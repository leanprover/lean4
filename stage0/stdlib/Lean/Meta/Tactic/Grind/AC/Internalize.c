// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.AC.Internalize
// Imports: public import Lean.Meta.Tactic.Grind.AC.Util import Lean.Meta.Tactic.Grind.AC.DenoteExpr
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
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Meta_Grind_AC_ACM_getStruct(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_outOfBounds___redArg(lean_object*);
lean_object* l_Lean_PersistentArray_get_x21___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
uint64_t lean_usize_to_uint64(size_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_AC_addTermOpId___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_AC_acExt;
lean_object* l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getConfig___redArg(lean_object*);
lean_object* l_Lean_Meta_Grind_AC_getOpId_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_AC_isOp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_AC_mkVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_AC_modifyStruct___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Internalize_0__Lean_Meta_Grind_AC_isParentSameOpApp___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Internalize_0__Lean_Meta_Grind_AC_isParentSameOpApp___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Internalize_0__Lean_Meta_Grind_AC_isParentSameOpApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Internalize_0__Lean_Meta_Grind_AC_isParentSameOpApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_reify(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_reify___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2_spec__4_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2_spec__5___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_internalize___lam__0(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_internalize___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Expr_denoteExpr___at___00Lean_Meta_Grind_AC_internalize_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Expr_denoteExpr___at___00Lean_Meta_Grind_AC_internalize_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_AC_internalize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "grind"};
static const lean_object* l_Lean_Meta_Grind_AC_internalize___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_AC_internalize___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_AC_internalize___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "ac"};
static const lean_object* l_Lean_Meta_Grind_AC_internalize___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_AC_internalize___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_AC_internalize___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "internalize"};
static const lean_object* l_Lean_Meta_Grind_AC_internalize___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_AC_internalize___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Grind_AC_internalize___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_AC_internalize___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_internalize___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_internalize___closed__3_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_AC_internalize___closed__1_value),LEAN_SCALAR_PTR_LITERAL(9, 156, 240, 157, 146, 53, 54, 12)}};
static const lean_ctor_object l_Lean_Meta_Grind_AC_internalize___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_AC_internalize___closed__3_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_AC_internalize___closed__2_value),LEAN_SCALAR_PTR_LITERAL(148, 182, 35, 4, 116, 197, 166, 64)}};
static const lean_object* l_Lean_Meta_Grind_AC_internalize___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_AC_internalize___closed__3_value;
static const lean_string_object l_Lean_Meta_Grind_AC_internalize___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Meta_Grind_AC_internalize___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_AC_internalize___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Grind_AC_internalize___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_AC_internalize___closed__4_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Meta_Grind_AC_internalize___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_AC_internalize___closed__5_value;
static lean_once_cell_t l_Lean_Meta_Grind_AC_internalize___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_AC_internalize___closed__6;
static const lean_string_object l_Lean_Meta_Grind_AC_internalize___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_Lean_Meta_Grind_AC_internalize___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_AC_internalize___closed__7_value;
static lean_once_cell_t l_Lean_Meta_Grind_AC_internalize___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_AC_internalize___closed__8;
static const lean_string_object l_Lean_Meta_Grind_AC_internalize___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "] "};
static const lean_object* l_Lean_Meta_Grind_AC_internalize___closed__9 = (const lean_object*)&l_Lean_Meta_Grind_AC_internalize___closed__9_value;
static lean_once_cell_t l_Lean_Meta_Grind_AC_internalize___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_AC_internalize___closed__10;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_internalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_internalize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2_spec__5(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2_spec__4_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Internalize_0__Lean_Meta_Grind_AC_isParentSameOpApp___redArg(lean_object* v_parent_x3f_1_, lean_object* v_op_2_){
_start:
{
if (lean_obj_tag(v_parent_x3f_1_) == 1)
{
lean_object* v_val_4_; lean_object* v___x_6_; uint8_t v_isShared_7_; uint8_t v_isSharedCheck_26_; 
v_val_4_ = lean_ctor_get(v_parent_x3f_1_, 0);
v_isSharedCheck_26_ = !lean_is_exclusive(v_parent_x3f_1_);
if (v_isSharedCheck_26_ == 0)
{
v___x_6_ = v_parent_x3f_1_;
v_isShared_7_ = v_isSharedCheck_26_;
goto v_resetjp_5_;
}
else
{
lean_inc(v_val_4_);
lean_dec(v_parent_x3f_1_);
v___x_6_ = lean_box(0);
v_isShared_7_ = v_isSharedCheck_26_;
goto v_resetjp_5_;
}
v_resetjp_5_:
{
uint8_t v___y_9_; uint8_t v___x_23_; 
v___x_23_ = l_Lean_Expr_isApp(v_val_4_);
if (v___x_23_ == 0)
{
v___y_9_ = v___x_23_;
goto v___jp_8_;
}
else
{
lean_object* v___x_24_; uint8_t v___x_25_; 
v___x_24_ = l_Lean_Expr_appFn_x21(v_val_4_);
v___x_25_ = l_Lean_Expr_isApp(v___x_24_);
lean_dec_ref(v___x_24_);
v___y_9_ = v___x_25_;
goto v___jp_8_;
}
v___jp_8_:
{
if (v___y_9_ == 0)
{
lean_object* v___x_10_; lean_object* v___x_12_; 
lean_dec(v_val_4_);
v___x_10_ = lean_box(v___y_9_);
if (v_isShared_7_ == 0)
{
lean_ctor_set_tag(v___x_6_, 0);
lean_ctor_set(v___x_6_, 0, v___x_10_);
v___x_12_ = v___x_6_;
goto v_reusejp_11_;
}
else
{
lean_object* v_reuseFailAlloc_13_; 
v_reuseFailAlloc_13_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_13_, 0, v___x_10_);
v___x_12_ = v_reuseFailAlloc_13_;
goto v_reusejp_11_;
}
v_reusejp_11_:
{
return v___x_12_;
}
}
else
{
lean_object* v___x_14_; lean_object* v___x_15_; size_t v___x_16_; size_t v___x_17_; uint8_t v___x_18_; lean_object* v___x_19_; lean_object* v___x_21_; 
v___x_14_ = l_Lean_Expr_appFn_x21(v_val_4_);
lean_dec(v_val_4_);
v___x_15_ = l_Lean_Expr_appFn_x21(v___x_14_);
lean_dec_ref(v___x_14_);
v___x_16_ = lean_ptr_addr(v___x_15_);
lean_dec_ref(v___x_15_);
v___x_17_ = lean_ptr_addr(v_op_2_);
v___x_18_ = lean_usize_dec_eq(v___x_16_, v___x_17_);
v___x_19_ = lean_box(v___x_18_);
if (v_isShared_7_ == 0)
{
lean_ctor_set_tag(v___x_6_, 0);
lean_ctor_set(v___x_6_, 0, v___x_19_);
v___x_21_ = v___x_6_;
goto v_reusejp_20_;
}
else
{
lean_object* v_reuseFailAlloc_22_; 
v_reuseFailAlloc_22_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_22_, 0, v___x_19_);
v___x_21_ = v_reuseFailAlloc_22_;
goto v_reusejp_20_;
}
v_reusejp_20_:
{
return v___x_21_;
}
}
}
}
}
else
{
uint8_t v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; 
lean_dec(v_parent_x3f_1_);
v___x_27_ = 0;
v___x_28_ = lean_box(v___x_27_);
v___x_29_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_29_, 0, v___x_28_);
return v___x_29_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Internalize_0__Lean_Meta_Grind_AC_isParentSameOpApp___redArg___boxed(lean_object* v_parent_x3f_30_, lean_object* v_op_31_, lean_object* v_a_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l___private_Lean_Meta_Tactic_Grind_AC_Internalize_0__Lean_Meta_Grind_AC_isParentSameOpApp___redArg(v_parent_x3f_30_, v_op_31_);
lean_dec_ref(v_op_31_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Internalize_0__Lean_Meta_Grind_AC_isParentSameOpApp(lean_object* v_parent_x3f_34_, lean_object* v_op_35_, lean_object* v_a_36_, lean_object* v_a_37_, lean_object* v_a_38_, lean_object* v_a_39_, lean_object* v_a_40_, lean_object* v_a_41_, lean_object* v_a_42_, lean_object* v_a_43_, lean_object* v_a_44_, lean_object* v_a_45_){
_start:
{
lean_object* v___x_47_; 
v___x_47_ = l___private_Lean_Meta_Tactic_Grind_AC_Internalize_0__Lean_Meta_Grind_AC_isParentSameOpApp___redArg(v_parent_x3f_34_, v_op_35_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Internalize_0__Lean_Meta_Grind_AC_isParentSameOpApp___boxed(lean_object* v_parent_x3f_48_, lean_object* v_op_49_, lean_object* v_a_50_, lean_object* v_a_51_, lean_object* v_a_52_, lean_object* v_a_53_, lean_object* v_a_54_, lean_object* v_a_55_, lean_object* v_a_56_, lean_object* v_a_57_, lean_object* v_a_58_, lean_object* v_a_59_, lean_object* v_a_60_){
_start:
{
lean_object* v_res_61_; 
v_res_61_ = l___private_Lean_Meta_Tactic_Grind_AC_Internalize_0__Lean_Meta_Grind_AC_isParentSameOpApp(v_parent_x3f_48_, v_op_49_, v_a_50_, v_a_51_, v_a_52_, v_a_53_, v_a_54_, v_a_55_, v_a_56_, v_a_57_, v_a_58_, v_a_59_);
lean_dec(v_a_59_);
lean_dec_ref(v_a_58_);
lean_dec(v_a_57_);
lean_dec_ref(v_a_56_);
lean_dec(v_a_55_);
lean_dec_ref(v_a_54_);
lean_dec(v_a_53_);
lean_dec_ref(v_a_52_);
lean_dec(v_a_51_);
lean_dec(v_a_50_);
lean_dec_ref(v_op_49_);
return v_res_61_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_reify(lean_object* v_e_62_, lean_object* v_a_63_, lean_object* v_a_64_, lean_object* v_a_65_, lean_object* v_a_66_, lean_object* v_a_67_, lean_object* v_a_68_, lean_object* v_a_69_, lean_object* v_a_70_, lean_object* v_a_71_, lean_object* v_a_72_, lean_object* v_a_73_){
_start:
{
lean_object* v___x_75_; 
v___x_75_ = l_Lean_Meta_Grind_AC_isOp_x3f(v_e_62_, v_a_63_, v_a_64_, v_a_65_, v_a_66_, v_a_67_, v_a_68_, v_a_69_, v_a_70_, v_a_71_, v_a_72_, v_a_73_);
if (lean_obj_tag(v___x_75_) == 0)
{
lean_object* v_a_76_; 
v_a_76_ = lean_ctor_get(v___x_75_, 0);
lean_inc(v_a_76_);
lean_dec_ref_known(v___x_75_, 1);
if (lean_obj_tag(v_a_76_) == 1)
{
lean_object* v_val_77_; lean_object* v_fst_78_; lean_object* v_snd_79_; lean_object* v___x_81_; uint8_t v_isShared_82_; uint8_t v_isSharedCheck_97_; 
lean_dec_ref(v_e_62_);
v_val_77_ = lean_ctor_get(v_a_76_, 0);
lean_inc(v_val_77_);
lean_dec_ref_known(v_a_76_, 1);
v_fst_78_ = lean_ctor_get(v_val_77_, 0);
v_snd_79_ = lean_ctor_get(v_val_77_, 1);
v_isSharedCheck_97_ = !lean_is_exclusive(v_val_77_);
if (v_isSharedCheck_97_ == 0)
{
v___x_81_ = v_val_77_;
v_isShared_82_ = v_isSharedCheck_97_;
goto v_resetjp_80_;
}
else
{
lean_inc(v_snd_79_);
lean_inc(v_fst_78_);
lean_dec(v_val_77_);
v___x_81_ = lean_box(0);
v_isShared_82_ = v_isSharedCheck_97_;
goto v_resetjp_80_;
}
v_resetjp_80_:
{
lean_object* v___x_83_; 
v___x_83_ = l_Lean_Meta_Grind_AC_reify(v_fst_78_, v_a_63_, v_a_64_, v_a_65_, v_a_66_, v_a_67_, v_a_68_, v_a_69_, v_a_70_, v_a_71_, v_a_72_, v_a_73_);
if (lean_obj_tag(v___x_83_) == 0)
{
lean_object* v_a_84_; lean_object* v___x_85_; 
v_a_84_ = lean_ctor_get(v___x_83_, 0);
lean_inc(v_a_84_);
lean_dec_ref_known(v___x_83_, 1);
v___x_85_ = l_Lean_Meta_Grind_AC_reify(v_snd_79_, v_a_63_, v_a_64_, v_a_65_, v_a_66_, v_a_67_, v_a_68_, v_a_69_, v_a_70_, v_a_71_, v_a_72_, v_a_73_);
if (lean_obj_tag(v___x_85_) == 0)
{
lean_object* v_a_86_; lean_object* v___x_88_; uint8_t v_isShared_89_; uint8_t v_isSharedCheck_96_; 
v_a_86_ = lean_ctor_get(v___x_85_, 0);
v_isSharedCheck_96_ = !lean_is_exclusive(v___x_85_);
if (v_isSharedCheck_96_ == 0)
{
v___x_88_ = v___x_85_;
v_isShared_89_ = v_isSharedCheck_96_;
goto v_resetjp_87_;
}
else
{
lean_inc(v_a_86_);
lean_dec(v___x_85_);
v___x_88_ = lean_box(0);
v_isShared_89_ = v_isSharedCheck_96_;
goto v_resetjp_87_;
}
v_resetjp_87_:
{
lean_object* v___x_91_; 
if (v_isShared_82_ == 0)
{
lean_ctor_set_tag(v___x_81_, 1);
lean_ctor_set(v___x_81_, 1, v_a_86_);
lean_ctor_set(v___x_81_, 0, v_a_84_);
v___x_91_ = v___x_81_;
goto v_reusejp_90_;
}
else
{
lean_object* v_reuseFailAlloc_95_; 
v_reuseFailAlloc_95_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_95_, 0, v_a_84_);
lean_ctor_set(v_reuseFailAlloc_95_, 1, v_a_86_);
v___x_91_ = v_reuseFailAlloc_95_;
goto v_reusejp_90_;
}
v_reusejp_90_:
{
lean_object* v___x_93_; 
if (v_isShared_89_ == 0)
{
lean_ctor_set(v___x_88_, 0, v___x_91_);
v___x_93_ = v___x_88_;
goto v_reusejp_92_;
}
else
{
lean_object* v_reuseFailAlloc_94_; 
v_reuseFailAlloc_94_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_94_, 0, v___x_91_);
v___x_93_ = v_reuseFailAlloc_94_;
goto v_reusejp_92_;
}
v_reusejp_92_:
{
return v___x_93_;
}
}
}
}
else
{
lean_dec(v_a_84_);
lean_del_object(v___x_81_);
return v___x_85_;
}
}
else
{
lean_del_object(v___x_81_);
lean_dec(v_snd_79_);
return v___x_83_;
}
}
}
else
{
lean_object* v___x_98_; 
lean_dec(v_a_76_);
v___x_98_ = l_Lean_Meta_Grind_AC_mkVar(v_e_62_, v_a_63_, v_a_64_, v_a_65_, v_a_66_, v_a_67_, v_a_68_, v_a_69_, v_a_70_, v_a_71_, v_a_72_, v_a_73_);
if (lean_obj_tag(v___x_98_) == 0)
{
lean_object* v_a_99_; lean_object* v___x_101_; uint8_t v_isShared_102_; uint8_t v_isSharedCheck_107_; 
v_a_99_ = lean_ctor_get(v___x_98_, 0);
v_isSharedCheck_107_ = !lean_is_exclusive(v___x_98_);
if (v_isSharedCheck_107_ == 0)
{
v___x_101_ = v___x_98_;
v_isShared_102_ = v_isSharedCheck_107_;
goto v_resetjp_100_;
}
else
{
lean_inc(v_a_99_);
lean_dec(v___x_98_);
v___x_101_ = lean_box(0);
v_isShared_102_ = v_isSharedCheck_107_;
goto v_resetjp_100_;
}
v_resetjp_100_:
{
lean_object* v___x_103_; lean_object* v___x_105_; 
v___x_103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_103_, 0, v_a_99_);
if (v_isShared_102_ == 0)
{
lean_ctor_set(v___x_101_, 0, v___x_103_);
v___x_105_ = v___x_101_;
goto v_reusejp_104_;
}
else
{
lean_object* v_reuseFailAlloc_106_; 
v_reuseFailAlloc_106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_106_, 0, v___x_103_);
v___x_105_ = v_reuseFailAlloc_106_;
goto v_reusejp_104_;
}
v_reusejp_104_:
{
return v___x_105_;
}
}
}
else
{
lean_object* v_a_108_; lean_object* v___x_110_; uint8_t v_isShared_111_; uint8_t v_isSharedCheck_115_; 
v_a_108_ = lean_ctor_get(v___x_98_, 0);
v_isSharedCheck_115_ = !lean_is_exclusive(v___x_98_);
if (v_isSharedCheck_115_ == 0)
{
v___x_110_ = v___x_98_;
v_isShared_111_ = v_isSharedCheck_115_;
goto v_resetjp_109_;
}
else
{
lean_inc(v_a_108_);
lean_dec(v___x_98_);
v___x_110_ = lean_box(0);
v_isShared_111_ = v_isSharedCheck_115_;
goto v_resetjp_109_;
}
v_resetjp_109_:
{
lean_object* v___x_113_; 
if (v_isShared_111_ == 0)
{
v___x_113_ = v___x_110_;
goto v_reusejp_112_;
}
else
{
lean_object* v_reuseFailAlloc_114_; 
v_reuseFailAlloc_114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_114_, 0, v_a_108_);
v___x_113_ = v_reuseFailAlloc_114_;
goto v_reusejp_112_;
}
v_reusejp_112_:
{
return v___x_113_;
}
}
}
}
}
else
{
lean_object* v_a_116_; lean_object* v___x_118_; uint8_t v_isShared_119_; uint8_t v_isSharedCheck_123_; 
lean_dec_ref(v_e_62_);
v_a_116_ = lean_ctor_get(v___x_75_, 0);
v_isSharedCheck_123_ = !lean_is_exclusive(v___x_75_);
if (v_isSharedCheck_123_ == 0)
{
v___x_118_ = v___x_75_;
v_isShared_119_ = v_isSharedCheck_123_;
goto v_resetjp_117_;
}
else
{
lean_inc(v_a_116_);
lean_dec(v___x_75_);
v___x_118_ = lean_box(0);
v_isShared_119_ = v_isSharedCheck_123_;
goto v_resetjp_117_;
}
v_resetjp_117_:
{
lean_object* v___x_121_; 
if (v_isShared_119_ == 0)
{
v___x_121_ = v___x_118_;
goto v_reusejp_120_;
}
else
{
lean_object* v_reuseFailAlloc_122_; 
v_reuseFailAlloc_122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_122_, 0, v_a_116_);
v___x_121_ = v_reuseFailAlloc_122_;
goto v_reusejp_120_;
}
v_reusejp_120_:
{
return v___x_121_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_reify___boxed(lean_object* v_e_124_, lean_object* v_a_125_, lean_object* v_a_126_, lean_object* v_a_127_, lean_object* v_a_128_, lean_object* v_a_129_, lean_object* v_a_130_, lean_object* v_a_131_, lean_object* v_a_132_, lean_object* v_a_133_, lean_object* v_a_134_, lean_object* v_a_135_, lean_object* v_a_136_){
_start:
{
lean_object* v_res_137_; 
v_res_137_ = l_Lean_Meta_Grind_AC_reify(v_e_124_, v_a_125_, v_a_126_, v_a_127_, v_a_128_, v_a_129_, v_a_130_, v_a_131_, v_a_132_, v_a_133_, v_a_134_, v_a_135_);
lean_dec(v_a_135_);
lean_dec_ref(v_a_134_);
lean_dec(v_a_133_);
lean_dec_ref(v_a_132_);
lean_dec(v_a_131_);
lean_dec_ref(v_a_130_);
lean_dec(v_a_129_);
lean_dec_ref(v_a_128_);
lean_dec(v_a_127_);
lean_dec(v_a_126_);
lean_dec(v_a_125_);
return v_res_137_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2_spec__4_spec__8___redArg(lean_object* v_x_138_, lean_object* v_x_139_, lean_object* v_x_140_, lean_object* v_x_141_){
_start:
{
lean_object* v_ks_142_; lean_object* v_vs_143_; lean_object* v___x_145_; uint8_t v_isShared_146_; uint8_t v_isSharedCheck_169_; 
v_ks_142_ = lean_ctor_get(v_x_138_, 0);
v_vs_143_ = lean_ctor_get(v_x_138_, 1);
v_isSharedCheck_169_ = !lean_is_exclusive(v_x_138_);
if (v_isSharedCheck_169_ == 0)
{
v___x_145_ = v_x_138_;
v_isShared_146_ = v_isSharedCheck_169_;
goto v_resetjp_144_;
}
else
{
lean_inc(v_vs_143_);
lean_inc(v_ks_142_);
lean_dec(v_x_138_);
v___x_145_ = lean_box(0);
v_isShared_146_ = v_isSharedCheck_169_;
goto v_resetjp_144_;
}
v_resetjp_144_:
{
lean_object* v___x_147_; uint8_t v___x_148_; 
v___x_147_ = lean_array_get_size(v_ks_142_);
v___x_148_ = lean_nat_dec_lt(v_x_139_, v___x_147_);
if (v___x_148_ == 0)
{
lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_152_; 
lean_dec(v_x_139_);
v___x_149_ = lean_array_push(v_ks_142_, v_x_140_);
v___x_150_ = lean_array_push(v_vs_143_, v_x_141_);
if (v_isShared_146_ == 0)
{
lean_ctor_set(v___x_145_, 1, v___x_150_);
lean_ctor_set(v___x_145_, 0, v___x_149_);
v___x_152_ = v___x_145_;
goto v_reusejp_151_;
}
else
{
lean_object* v_reuseFailAlloc_153_; 
v_reuseFailAlloc_153_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_153_, 0, v___x_149_);
lean_ctor_set(v_reuseFailAlloc_153_, 1, v___x_150_);
v___x_152_ = v_reuseFailAlloc_153_;
goto v_reusejp_151_;
}
v_reusejp_151_:
{
return v___x_152_;
}
}
else
{
lean_object* v_k_x27_154_; size_t v___x_155_; size_t v___x_156_; uint8_t v___x_157_; 
v_k_x27_154_ = lean_array_fget_borrowed(v_ks_142_, v_x_139_);
v___x_155_ = lean_ptr_addr(v_x_140_);
v___x_156_ = lean_ptr_addr(v_k_x27_154_);
v___x_157_ = lean_usize_dec_eq(v___x_155_, v___x_156_);
if (v___x_157_ == 0)
{
lean_object* v___x_159_; 
if (v_isShared_146_ == 0)
{
v___x_159_ = v___x_145_;
goto v_reusejp_158_;
}
else
{
lean_object* v_reuseFailAlloc_163_; 
v_reuseFailAlloc_163_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_163_, 0, v_ks_142_);
lean_ctor_set(v_reuseFailAlloc_163_, 1, v_vs_143_);
v___x_159_ = v_reuseFailAlloc_163_;
goto v_reusejp_158_;
}
v_reusejp_158_:
{
lean_object* v___x_160_; lean_object* v___x_161_; 
v___x_160_ = lean_unsigned_to_nat(1u);
v___x_161_ = lean_nat_add(v_x_139_, v___x_160_);
lean_dec(v_x_139_);
v_x_138_ = v___x_159_;
v_x_139_ = v___x_161_;
goto _start;
}
}
else
{
lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_167_; 
v___x_164_ = lean_array_fset(v_ks_142_, v_x_139_, v_x_140_);
v___x_165_ = lean_array_fset(v_vs_143_, v_x_139_, v_x_141_);
lean_dec(v_x_139_);
if (v_isShared_146_ == 0)
{
lean_ctor_set(v___x_145_, 1, v___x_165_);
lean_ctor_set(v___x_145_, 0, v___x_164_);
v___x_167_ = v___x_145_;
goto v_reusejp_166_;
}
else
{
lean_object* v_reuseFailAlloc_168_; 
v_reuseFailAlloc_168_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_168_, 0, v___x_164_);
lean_ctor_set(v_reuseFailAlloc_168_, 1, v___x_165_);
v___x_167_ = v_reuseFailAlloc_168_;
goto v_reusejp_166_;
}
v_reusejp_166_:
{
return v___x_167_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2_spec__4___redArg(lean_object* v_n_170_, lean_object* v_k_171_, lean_object* v_v_172_){
_start:
{
lean_object* v___x_173_; lean_object* v___x_174_; 
v___x_173_ = lean_unsigned_to_nat(0u);
v___x_174_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2_spec__4_spec__8___redArg(v_n_170_, v___x_173_, v_k_171_, v_v_172_);
return v___x_174_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_175_; 
v___x_175_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_175_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___redArg(lean_object* v_x_176_, size_t v_x_177_, size_t v_x_178_, lean_object* v_x_179_, lean_object* v_x_180_){
_start:
{
if (lean_obj_tag(v_x_176_) == 0)
{
lean_object* v_es_181_; size_t v___x_182_; size_t v___x_183_; lean_object* v_j_184_; lean_object* v___x_185_; uint8_t v___x_186_; 
v_es_181_ = lean_ctor_get(v_x_176_, 0);
v___x_182_ = ((size_t)31ULL);
v___x_183_ = lean_usize_land(v_x_177_, v___x_182_);
v_j_184_ = lean_usize_to_nat(v___x_183_);
v___x_185_ = lean_array_get_size(v_es_181_);
v___x_186_ = lean_nat_dec_lt(v_j_184_, v___x_185_);
if (v___x_186_ == 0)
{
lean_dec(v_j_184_);
lean_dec(v_x_180_);
lean_dec_ref(v_x_179_);
return v_x_176_;
}
else
{
lean_object* v___x_188_; uint8_t v_isShared_189_; uint8_t v_isSharedCheck_227_; 
lean_inc_ref(v_es_181_);
v_isSharedCheck_227_ = !lean_is_exclusive(v_x_176_);
if (v_isSharedCheck_227_ == 0)
{
lean_object* v_unused_228_; 
v_unused_228_ = lean_ctor_get(v_x_176_, 0);
lean_dec(v_unused_228_);
v___x_188_ = v_x_176_;
v_isShared_189_ = v_isSharedCheck_227_;
goto v_resetjp_187_;
}
else
{
lean_dec(v_x_176_);
v___x_188_ = lean_box(0);
v_isShared_189_ = v_isSharedCheck_227_;
goto v_resetjp_187_;
}
v_resetjp_187_:
{
lean_object* v_v_190_; lean_object* v___x_191_; lean_object* v_xs_x27_192_; lean_object* v___y_194_; 
v_v_190_ = lean_array_fget(v_es_181_, v_j_184_);
v___x_191_ = lean_box(0);
v_xs_x27_192_ = lean_array_fset(v_es_181_, v_j_184_, v___x_191_);
switch(lean_obj_tag(v_v_190_))
{
case 0:
{
lean_object* v_key_199_; lean_object* v_val_200_; lean_object* v___x_202_; uint8_t v_isShared_203_; uint8_t v_isSharedCheck_212_; 
v_key_199_ = lean_ctor_get(v_v_190_, 0);
v_val_200_ = lean_ctor_get(v_v_190_, 1);
v_isSharedCheck_212_ = !lean_is_exclusive(v_v_190_);
if (v_isSharedCheck_212_ == 0)
{
v___x_202_ = v_v_190_;
v_isShared_203_ = v_isSharedCheck_212_;
goto v_resetjp_201_;
}
else
{
lean_inc(v_val_200_);
lean_inc(v_key_199_);
lean_dec(v_v_190_);
v___x_202_ = lean_box(0);
v_isShared_203_ = v_isSharedCheck_212_;
goto v_resetjp_201_;
}
v_resetjp_201_:
{
size_t v___x_204_; size_t v___x_205_; uint8_t v___x_206_; 
v___x_204_ = lean_ptr_addr(v_x_179_);
v___x_205_ = lean_ptr_addr(v_key_199_);
v___x_206_ = lean_usize_dec_eq(v___x_204_, v___x_205_);
if (v___x_206_ == 0)
{
lean_object* v___x_207_; lean_object* v___x_208_; 
lean_del_object(v___x_202_);
v___x_207_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_199_, v_val_200_, v_x_179_, v_x_180_);
v___x_208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_208_, 0, v___x_207_);
v___y_194_ = v___x_208_;
goto v___jp_193_;
}
else
{
lean_object* v___x_210_; 
lean_dec(v_val_200_);
lean_dec(v_key_199_);
if (v_isShared_203_ == 0)
{
lean_ctor_set(v___x_202_, 1, v_x_180_);
lean_ctor_set(v___x_202_, 0, v_x_179_);
v___x_210_ = v___x_202_;
goto v_reusejp_209_;
}
else
{
lean_object* v_reuseFailAlloc_211_; 
v_reuseFailAlloc_211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_211_, 0, v_x_179_);
lean_ctor_set(v_reuseFailAlloc_211_, 1, v_x_180_);
v___x_210_ = v_reuseFailAlloc_211_;
goto v_reusejp_209_;
}
v_reusejp_209_:
{
v___y_194_ = v___x_210_;
goto v___jp_193_;
}
}
}
}
case 1:
{
lean_object* v_node_213_; lean_object* v___x_215_; uint8_t v_isShared_216_; uint8_t v_isSharedCheck_225_; 
v_node_213_ = lean_ctor_get(v_v_190_, 0);
v_isSharedCheck_225_ = !lean_is_exclusive(v_v_190_);
if (v_isSharedCheck_225_ == 0)
{
v___x_215_ = v_v_190_;
v_isShared_216_ = v_isSharedCheck_225_;
goto v_resetjp_214_;
}
else
{
lean_inc(v_node_213_);
lean_dec(v_v_190_);
v___x_215_ = lean_box(0);
v_isShared_216_ = v_isSharedCheck_225_;
goto v_resetjp_214_;
}
v_resetjp_214_:
{
size_t v___x_217_; size_t v___x_218_; size_t v___x_219_; size_t v___x_220_; lean_object* v___x_221_; lean_object* v___x_223_; 
v___x_217_ = ((size_t)5ULL);
v___x_218_ = lean_usize_shift_right(v_x_177_, v___x_217_);
v___x_219_ = ((size_t)1ULL);
v___x_220_ = lean_usize_add(v_x_178_, v___x_219_);
v___x_221_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___redArg(v_node_213_, v___x_218_, v___x_220_, v_x_179_, v_x_180_);
if (v_isShared_216_ == 0)
{
lean_ctor_set(v___x_215_, 0, v___x_221_);
v___x_223_ = v___x_215_;
goto v_reusejp_222_;
}
else
{
lean_object* v_reuseFailAlloc_224_; 
v_reuseFailAlloc_224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_224_, 0, v___x_221_);
v___x_223_ = v_reuseFailAlloc_224_;
goto v_reusejp_222_;
}
v_reusejp_222_:
{
v___y_194_ = v___x_223_;
goto v___jp_193_;
}
}
}
default: 
{
lean_object* v___x_226_; 
v___x_226_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_226_, 0, v_x_179_);
lean_ctor_set(v___x_226_, 1, v_x_180_);
v___y_194_ = v___x_226_;
goto v___jp_193_;
}
}
v___jp_193_:
{
lean_object* v___x_195_; lean_object* v___x_197_; 
v___x_195_ = lean_array_fset(v_xs_x27_192_, v_j_184_, v___y_194_);
lean_dec(v_j_184_);
if (v_isShared_189_ == 0)
{
lean_ctor_set(v___x_188_, 0, v___x_195_);
v___x_197_ = v___x_188_;
goto v_reusejp_196_;
}
else
{
lean_object* v_reuseFailAlloc_198_; 
v_reuseFailAlloc_198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_198_, 0, v___x_195_);
v___x_197_ = v_reuseFailAlloc_198_;
goto v_reusejp_196_;
}
v_reusejp_196_:
{
return v___x_197_;
}
}
}
}
}
else
{
lean_object* v_ks_229_; lean_object* v_vs_230_; lean_object* v___x_232_; uint8_t v_isShared_233_; uint8_t v_isSharedCheck_250_; 
v_ks_229_ = lean_ctor_get(v_x_176_, 0);
v_vs_230_ = lean_ctor_get(v_x_176_, 1);
v_isSharedCheck_250_ = !lean_is_exclusive(v_x_176_);
if (v_isSharedCheck_250_ == 0)
{
v___x_232_ = v_x_176_;
v_isShared_233_ = v_isSharedCheck_250_;
goto v_resetjp_231_;
}
else
{
lean_inc(v_vs_230_);
lean_inc(v_ks_229_);
lean_dec(v_x_176_);
v___x_232_ = lean_box(0);
v_isShared_233_ = v_isSharedCheck_250_;
goto v_resetjp_231_;
}
v_resetjp_231_:
{
lean_object* v___x_235_; 
if (v_isShared_233_ == 0)
{
v___x_235_ = v___x_232_;
goto v_reusejp_234_;
}
else
{
lean_object* v_reuseFailAlloc_249_; 
v_reuseFailAlloc_249_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_249_, 0, v_ks_229_);
lean_ctor_set(v_reuseFailAlloc_249_, 1, v_vs_230_);
v___x_235_ = v_reuseFailAlloc_249_;
goto v_reusejp_234_;
}
v_reusejp_234_:
{
lean_object* v_newNode_236_; uint8_t v___y_238_; size_t v___x_244_; uint8_t v___x_245_; 
v_newNode_236_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2_spec__4___redArg(v___x_235_, v_x_179_, v_x_180_);
v___x_244_ = ((size_t)7ULL);
v___x_245_ = lean_usize_dec_le(v___x_244_, v_x_178_);
if (v___x_245_ == 0)
{
lean_object* v___x_246_; lean_object* v___x_247_; uint8_t v___x_248_; 
v___x_246_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_236_);
v___x_247_ = lean_unsigned_to_nat(4u);
v___x_248_ = lean_nat_dec_lt(v___x_246_, v___x_247_);
lean_dec(v___x_246_);
v___y_238_ = v___x_248_;
goto v___jp_237_;
}
else
{
v___y_238_ = v___x_245_;
goto v___jp_237_;
}
v___jp_237_:
{
if (v___y_238_ == 0)
{
lean_object* v_ks_239_; lean_object* v_vs_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; 
v_ks_239_ = lean_ctor_get(v_newNode_236_, 0);
lean_inc_ref(v_ks_239_);
v_vs_240_ = lean_ctor_get(v_newNode_236_, 1);
lean_inc_ref(v_vs_240_);
lean_dec_ref(v_newNode_236_);
v___x_241_ = lean_unsigned_to_nat(0u);
v___x_242_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___redArg___closed__0);
v___x_243_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2_spec__5___redArg(v_x_178_, v_ks_239_, v_vs_240_, v___x_241_, v___x_242_);
lean_dec_ref(v_vs_240_);
lean_dec_ref(v_ks_239_);
return v___x_243_;
}
else
{
return v_newNode_236_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2_spec__5___redArg(size_t v_depth_251_, lean_object* v_keys_252_, lean_object* v_vals_253_, lean_object* v_i_254_, lean_object* v_entries_255_){
_start:
{
lean_object* v___x_256_; uint8_t v___x_257_; 
v___x_256_ = lean_array_get_size(v_keys_252_);
v___x_257_ = lean_nat_dec_lt(v_i_254_, v___x_256_);
if (v___x_257_ == 0)
{
lean_dec(v_i_254_);
return v_entries_255_;
}
else
{
lean_object* v_k_258_; lean_object* v_v_259_; size_t v___x_260_; size_t v___x_261_; size_t v___x_262_; uint64_t v___x_263_; size_t v_h_264_; size_t v___x_265_; lean_object* v___x_266_; size_t v___x_267_; size_t v___x_268_; size_t v___x_269_; size_t v_h_270_; lean_object* v___x_271_; lean_object* v___x_272_; 
v_k_258_ = lean_array_fget_borrowed(v_keys_252_, v_i_254_);
v_v_259_ = lean_array_fget_borrowed(v_vals_253_, v_i_254_);
v___x_260_ = lean_ptr_addr(v_k_258_);
v___x_261_ = ((size_t)3ULL);
v___x_262_ = lean_usize_shift_right(v___x_260_, v___x_261_);
v___x_263_ = lean_usize_to_uint64(v___x_262_);
v_h_264_ = lean_uint64_to_usize(v___x_263_);
v___x_265_ = ((size_t)5ULL);
v___x_266_ = lean_unsigned_to_nat(1u);
v___x_267_ = ((size_t)1ULL);
v___x_268_ = lean_usize_sub(v_depth_251_, v___x_267_);
v___x_269_ = lean_usize_mul(v___x_265_, v___x_268_);
v_h_270_ = lean_usize_shift_right(v_h_264_, v___x_269_);
v___x_271_ = lean_nat_add(v_i_254_, v___x_266_);
lean_dec(v_i_254_);
lean_inc(v_v_259_);
lean_inc(v_k_258_);
v___x_272_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___redArg(v_entries_255_, v_h_270_, v_depth_251_, v_k_258_, v_v_259_);
v_i_254_ = v___x_271_;
v_entries_255_ = v___x_272_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_depth_274_, lean_object* v_keys_275_, lean_object* v_vals_276_, lean_object* v_i_277_, lean_object* v_entries_278_){
_start:
{
size_t v_depth_boxed_279_; lean_object* v_res_280_; 
v_depth_boxed_279_ = lean_unbox_usize(v_depth_274_);
lean_dec(v_depth_274_);
v_res_280_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2_spec__5___redArg(v_depth_boxed_279_, v_keys_275_, v_vals_276_, v_i_277_, v_entries_278_);
lean_dec_ref(v_vals_276_);
lean_dec_ref(v_keys_275_);
return v_res_280_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___redArg___boxed(lean_object* v_x_281_, lean_object* v_x_282_, lean_object* v_x_283_, lean_object* v_x_284_, lean_object* v_x_285_){
_start:
{
size_t v_x_55768__boxed_286_; size_t v_x_55769__boxed_287_; lean_object* v_res_288_; 
v_x_55768__boxed_286_ = lean_unbox_usize(v_x_282_);
lean_dec(v_x_282_);
v_x_55769__boxed_287_ = lean_unbox_usize(v_x_283_);
lean_dec(v_x_283_);
v_res_288_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___redArg(v_x_281_, v_x_55768__boxed_286_, v_x_55769__boxed_287_, v_x_284_, v_x_285_);
return v_res_288_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1___redArg(lean_object* v_x_289_, lean_object* v_x_290_, lean_object* v_x_291_){
_start:
{
size_t v___x_292_; size_t v___x_293_; size_t v___x_294_; uint64_t v___x_295_; size_t v___x_296_; size_t v___x_297_; lean_object* v___x_298_; 
v___x_292_ = lean_ptr_addr(v_x_290_);
v___x_293_ = ((size_t)3ULL);
v___x_294_ = lean_usize_shift_right(v___x_292_, v___x_293_);
v___x_295_ = lean_usize_to_uint64(v___x_294_);
v___x_296_ = lean_uint64_to_usize(v___x_295_);
v___x_297_ = ((size_t)1ULL);
v___x_298_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___redArg(v_x_289_, v___x_296_, v___x_297_, v_x_290_, v_x_291_);
return v___x_298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_internalize___lam__0(lean_object* v_e_299_, lean_object* v_a_300_, uint8_t v_ac_301_, lean_object* v_s_302_){
_start:
{
lean_object* v_id_303_; lean_object* v_type_304_; lean_object* v_u_305_; lean_object* v_op_306_; lean_object* v_neutral_x3f_307_; lean_object* v_assocInst_308_; lean_object* v_idempotentInst_x3f_309_; lean_object* v_commInst_x3f_310_; lean_object* v_neutralInst_x3f_311_; lean_object* v_nextId_312_; lean_object* v_vars_313_; lean_object* v_varMap_314_; lean_object* v_denote_315_; lean_object* v_denoteEntries_316_; lean_object* v_queue_317_; lean_object* v_basis_318_; lean_object* v_diseqs_319_; lean_object* v___x_321_; uint8_t v_isShared_322_; uint8_t v_isSharedCheck_329_; 
v_id_303_ = lean_ctor_get(v_s_302_, 0);
v_type_304_ = lean_ctor_get(v_s_302_, 1);
v_u_305_ = lean_ctor_get(v_s_302_, 2);
v_op_306_ = lean_ctor_get(v_s_302_, 3);
v_neutral_x3f_307_ = lean_ctor_get(v_s_302_, 4);
v_assocInst_308_ = lean_ctor_get(v_s_302_, 5);
v_idempotentInst_x3f_309_ = lean_ctor_get(v_s_302_, 6);
v_commInst_x3f_310_ = lean_ctor_get(v_s_302_, 7);
v_neutralInst_x3f_311_ = lean_ctor_get(v_s_302_, 8);
v_nextId_312_ = lean_ctor_get(v_s_302_, 9);
v_vars_313_ = lean_ctor_get(v_s_302_, 10);
v_varMap_314_ = lean_ctor_get(v_s_302_, 11);
v_denote_315_ = lean_ctor_get(v_s_302_, 12);
v_denoteEntries_316_ = lean_ctor_get(v_s_302_, 13);
v_queue_317_ = lean_ctor_get(v_s_302_, 14);
v_basis_318_ = lean_ctor_get(v_s_302_, 15);
v_diseqs_319_ = lean_ctor_get(v_s_302_, 16);
v_isSharedCheck_329_ = !lean_is_exclusive(v_s_302_);
if (v_isSharedCheck_329_ == 0)
{
v___x_321_ = v_s_302_;
v_isShared_322_ = v_isSharedCheck_329_;
goto v_resetjp_320_;
}
else
{
lean_inc(v_diseqs_319_);
lean_inc(v_basis_318_);
lean_inc(v_queue_317_);
lean_inc(v_denoteEntries_316_);
lean_inc(v_denote_315_);
lean_inc(v_varMap_314_);
lean_inc(v_vars_313_);
lean_inc(v_nextId_312_);
lean_inc(v_neutralInst_x3f_311_);
lean_inc(v_commInst_x3f_310_);
lean_inc(v_idempotentInst_x3f_309_);
lean_inc(v_assocInst_308_);
lean_inc(v_neutral_x3f_307_);
lean_inc(v_op_306_);
lean_inc(v_u_305_);
lean_inc(v_type_304_);
lean_inc(v_id_303_);
lean_dec(v_s_302_);
v___x_321_ = lean_box(0);
v_isShared_322_ = v_isSharedCheck_329_;
goto v_resetjp_320_;
}
v_resetjp_320_:
{
lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_327_; 
lean_inc_ref(v_a_300_);
lean_inc_ref(v_e_299_);
v___x_323_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1___redArg(v_denote_315_, v_e_299_, v_a_300_);
v___x_324_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_324_, 0, v_e_299_);
lean_ctor_set(v___x_324_, 1, v_a_300_);
v___x_325_ = l_Lean_PersistentArray_push___redArg(v_denoteEntries_316_, v___x_324_);
if (v_isShared_322_ == 0)
{
lean_ctor_set(v___x_321_, 13, v___x_325_);
lean_ctor_set(v___x_321_, 12, v___x_323_);
v___x_327_ = v___x_321_;
goto v_reusejp_326_;
}
else
{
lean_object* v_reuseFailAlloc_328_; 
v_reuseFailAlloc_328_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_328_, 0, v_id_303_);
lean_ctor_set(v_reuseFailAlloc_328_, 1, v_type_304_);
lean_ctor_set(v_reuseFailAlloc_328_, 2, v_u_305_);
lean_ctor_set(v_reuseFailAlloc_328_, 3, v_op_306_);
lean_ctor_set(v_reuseFailAlloc_328_, 4, v_neutral_x3f_307_);
lean_ctor_set(v_reuseFailAlloc_328_, 5, v_assocInst_308_);
lean_ctor_set(v_reuseFailAlloc_328_, 6, v_idempotentInst_x3f_309_);
lean_ctor_set(v_reuseFailAlloc_328_, 7, v_commInst_x3f_310_);
lean_ctor_set(v_reuseFailAlloc_328_, 8, v_neutralInst_x3f_311_);
lean_ctor_set(v_reuseFailAlloc_328_, 9, v_nextId_312_);
lean_ctor_set(v_reuseFailAlloc_328_, 10, v_vars_313_);
lean_ctor_set(v_reuseFailAlloc_328_, 11, v_varMap_314_);
lean_ctor_set(v_reuseFailAlloc_328_, 12, v___x_323_);
lean_ctor_set(v_reuseFailAlloc_328_, 13, v___x_325_);
lean_ctor_set(v_reuseFailAlloc_328_, 14, v_queue_317_);
lean_ctor_set(v_reuseFailAlloc_328_, 15, v_basis_318_);
lean_ctor_set(v_reuseFailAlloc_328_, 16, v_diseqs_319_);
v___x_327_ = v_reuseFailAlloc_328_;
goto v_reusejp_326_;
}
v_reusejp_326_:
{
lean_ctor_set_uint8(v___x_327_, sizeof(void*)*17, v_ac_301_);
return v___x_327_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_internalize___lam__0___boxed(lean_object* v_e_330_, lean_object* v_a_331_, lean_object* v_ac_332_, lean_object* v_s_333_){
_start:
{
uint8_t v_ac_boxed_334_; lean_object* v_res_335_; 
v_ac_boxed_334_ = lean_unbox(v_ac_332_);
v_res_335_ = l_Lean_Meta_Grind_AC_internalize___lam__0(v_e_330_, v_a_331_, v_ac_boxed_334_, v_s_333_);
return v_res_335_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3_spec__5(lean_object* v_msgData_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_){
_start:
{
lean_object* v___x_342_; lean_object* v_env_343_; lean_object* v___x_344_; lean_object* v_mctx_345_; lean_object* v_lctx_346_; lean_object* v_options_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; 
v___x_342_ = lean_st_ref_get(v___y_340_);
v_env_343_ = lean_ctor_get(v___x_342_, 0);
lean_inc_ref(v_env_343_);
lean_dec(v___x_342_);
v___x_344_ = lean_st_ref_get(v___y_338_);
v_mctx_345_ = lean_ctor_get(v___x_344_, 0);
lean_inc_ref(v_mctx_345_);
lean_dec(v___x_344_);
v_lctx_346_ = lean_ctor_get(v___y_337_, 2);
v_options_347_ = lean_ctor_get(v___y_339_, 2);
lean_inc_ref(v_options_347_);
lean_inc_ref(v_lctx_346_);
v___x_348_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_348_, 0, v_env_343_);
lean_ctor_set(v___x_348_, 1, v_mctx_345_);
lean_ctor_set(v___x_348_, 2, v_lctx_346_);
lean_ctor_set(v___x_348_, 3, v_options_347_);
v___x_349_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_349_, 0, v___x_348_);
lean_ctor_set(v___x_349_, 1, v_msgData_336_);
v___x_350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_350_, 0, v___x_349_);
return v___x_350_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3_spec__5___boxed(lean_object* v_msgData_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_){
_start:
{
lean_object* v_res_357_; 
v_res_357_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3_spec__5(v_msgData_351_, v___y_352_, v___y_353_, v___y_354_, v___y_355_);
lean_dec(v___y_355_);
lean_dec_ref(v___y_354_);
lean_dec(v___y_353_);
lean_dec_ref(v___y_352_);
return v_res_357_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_358_; double v___x_359_; 
v___x_358_ = lean_unsigned_to_nat(0u);
v___x_359_ = lean_float_of_nat(v___x_358_);
return v___x_359_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3___redArg(lean_object* v_cls_363_, lean_object* v_msg_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_){
_start:
{
lean_object* v_ref_370_; lean_object* v___x_371_; lean_object* v_a_372_; lean_object* v___x_374_; uint8_t v_isShared_375_; uint8_t v_isSharedCheck_416_; 
v_ref_370_ = lean_ctor_get(v___y_367_, 5);
v___x_371_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3_spec__5(v_msg_364_, v___y_365_, v___y_366_, v___y_367_, v___y_368_);
v_a_372_ = lean_ctor_get(v___x_371_, 0);
v_isSharedCheck_416_ = !lean_is_exclusive(v___x_371_);
if (v_isSharedCheck_416_ == 0)
{
v___x_374_ = v___x_371_;
v_isShared_375_ = v_isSharedCheck_416_;
goto v_resetjp_373_;
}
else
{
lean_inc(v_a_372_);
lean_dec(v___x_371_);
v___x_374_ = lean_box(0);
v_isShared_375_ = v_isSharedCheck_416_;
goto v_resetjp_373_;
}
v_resetjp_373_:
{
lean_object* v___x_376_; lean_object* v_traceState_377_; lean_object* v_env_378_; lean_object* v_nextMacroScope_379_; lean_object* v_ngen_380_; lean_object* v_auxDeclNGen_381_; lean_object* v_cache_382_; lean_object* v_messages_383_; lean_object* v_infoState_384_; lean_object* v_snapshotTasks_385_; lean_object* v___x_387_; uint8_t v_isShared_388_; uint8_t v_isSharedCheck_415_; 
v___x_376_ = lean_st_ref_take(v___y_368_);
v_traceState_377_ = lean_ctor_get(v___x_376_, 4);
v_env_378_ = lean_ctor_get(v___x_376_, 0);
v_nextMacroScope_379_ = lean_ctor_get(v___x_376_, 1);
v_ngen_380_ = lean_ctor_get(v___x_376_, 2);
v_auxDeclNGen_381_ = lean_ctor_get(v___x_376_, 3);
v_cache_382_ = lean_ctor_get(v___x_376_, 5);
v_messages_383_ = lean_ctor_get(v___x_376_, 6);
v_infoState_384_ = lean_ctor_get(v___x_376_, 7);
v_snapshotTasks_385_ = lean_ctor_get(v___x_376_, 8);
v_isSharedCheck_415_ = !lean_is_exclusive(v___x_376_);
if (v_isSharedCheck_415_ == 0)
{
v___x_387_ = v___x_376_;
v_isShared_388_ = v_isSharedCheck_415_;
goto v_resetjp_386_;
}
else
{
lean_inc(v_snapshotTasks_385_);
lean_inc(v_infoState_384_);
lean_inc(v_messages_383_);
lean_inc(v_cache_382_);
lean_inc(v_traceState_377_);
lean_inc(v_auxDeclNGen_381_);
lean_inc(v_ngen_380_);
lean_inc(v_nextMacroScope_379_);
lean_inc(v_env_378_);
lean_dec(v___x_376_);
v___x_387_ = lean_box(0);
v_isShared_388_ = v_isSharedCheck_415_;
goto v_resetjp_386_;
}
v_resetjp_386_:
{
uint64_t v_tid_389_; lean_object* v_traces_390_; lean_object* v___x_392_; uint8_t v_isShared_393_; uint8_t v_isSharedCheck_414_; 
v_tid_389_ = lean_ctor_get_uint64(v_traceState_377_, sizeof(void*)*1);
v_traces_390_ = lean_ctor_get(v_traceState_377_, 0);
v_isSharedCheck_414_ = !lean_is_exclusive(v_traceState_377_);
if (v_isSharedCheck_414_ == 0)
{
v___x_392_ = v_traceState_377_;
v_isShared_393_ = v_isSharedCheck_414_;
goto v_resetjp_391_;
}
else
{
lean_inc(v_traces_390_);
lean_dec(v_traceState_377_);
v___x_392_ = lean_box(0);
v_isShared_393_ = v_isSharedCheck_414_;
goto v_resetjp_391_;
}
v_resetjp_391_:
{
lean_object* v___x_394_; double v___x_395_; uint8_t v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_404_; 
v___x_394_ = lean_box(0);
v___x_395_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3___redArg___closed__0);
v___x_396_ = 0;
v___x_397_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3___redArg___closed__1));
v___x_398_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_398_, 0, v_cls_363_);
lean_ctor_set(v___x_398_, 1, v___x_394_);
lean_ctor_set(v___x_398_, 2, v___x_397_);
lean_ctor_set_float(v___x_398_, sizeof(void*)*3, v___x_395_);
lean_ctor_set_float(v___x_398_, sizeof(void*)*3 + 8, v___x_395_);
lean_ctor_set_uint8(v___x_398_, sizeof(void*)*3 + 16, v___x_396_);
v___x_399_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3___redArg___closed__2));
v___x_400_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_400_, 0, v___x_398_);
lean_ctor_set(v___x_400_, 1, v_a_372_);
lean_ctor_set(v___x_400_, 2, v___x_399_);
lean_inc(v_ref_370_);
v___x_401_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_401_, 0, v_ref_370_);
lean_ctor_set(v___x_401_, 1, v___x_400_);
v___x_402_ = l_Lean_PersistentArray_push___redArg(v_traces_390_, v___x_401_);
if (v_isShared_393_ == 0)
{
lean_ctor_set(v___x_392_, 0, v___x_402_);
v___x_404_ = v___x_392_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_413_; 
v_reuseFailAlloc_413_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_413_, 0, v___x_402_);
lean_ctor_set_uint64(v_reuseFailAlloc_413_, sizeof(void*)*1, v_tid_389_);
v___x_404_ = v_reuseFailAlloc_413_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
lean_object* v___x_406_; 
if (v_isShared_388_ == 0)
{
lean_ctor_set(v___x_387_, 4, v___x_404_);
v___x_406_ = v___x_387_;
goto v_reusejp_405_;
}
else
{
lean_object* v_reuseFailAlloc_412_; 
v_reuseFailAlloc_412_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_412_, 0, v_env_378_);
lean_ctor_set(v_reuseFailAlloc_412_, 1, v_nextMacroScope_379_);
lean_ctor_set(v_reuseFailAlloc_412_, 2, v_ngen_380_);
lean_ctor_set(v_reuseFailAlloc_412_, 3, v_auxDeclNGen_381_);
lean_ctor_set(v_reuseFailAlloc_412_, 4, v___x_404_);
lean_ctor_set(v_reuseFailAlloc_412_, 5, v_cache_382_);
lean_ctor_set(v_reuseFailAlloc_412_, 6, v_messages_383_);
lean_ctor_set(v_reuseFailAlloc_412_, 7, v_infoState_384_);
lean_ctor_set(v_reuseFailAlloc_412_, 8, v_snapshotTasks_385_);
v___x_406_ = v_reuseFailAlloc_412_;
goto v_reusejp_405_;
}
v_reusejp_405_:
{
lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_410_; 
v___x_407_ = lean_st_ref_set(v___y_368_, v___x_406_);
v___x_408_ = lean_box(0);
if (v_isShared_375_ == 0)
{
lean_ctor_set(v___x_374_, 0, v___x_408_);
v___x_410_ = v___x_374_;
goto v_reusejp_409_;
}
else
{
lean_object* v_reuseFailAlloc_411_; 
v_reuseFailAlloc_411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_411_, 0, v___x_408_);
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
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3___redArg___boxed(lean_object* v_cls_417_, lean_object* v_msg_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_){
_start:
{
lean_object* v_res_424_; 
v_res_424_ = l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3___redArg(v_cls_417_, v_msg_418_, v___y_419_, v___y_420_, v___y_421_, v___y_422_);
lean_dec(v___y_422_);
lean_dec_ref(v___y_421_);
lean_dec(v___y_420_);
lean_dec_ref(v___y_419_);
return v_res_424_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_425_, lean_object* v_i_426_, lean_object* v_k_427_){
_start:
{
lean_object* v___x_428_; uint8_t v___x_429_; 
v___x_428_ = lean_array_get_size(v_keys_425_);
v___x_429_ = lean_nat_dec_lt(v_i_426_, v___x_428_);
if (v___x_429_ == 0)
{
lean_dec(v_i_426_);
return v___x_429_;
}
else
{
lean_object* v_k_x27_430_; size_t v___x_431_; size_t v___x_432_; uint8_t v___x_433_; 
v_k_x27_430_ = lean_array_fget_borrowed(v_keys_425_, v_i_426_);
v___x_431_ = lean_ptr_addr(v_k_427_);
v___x_432_ = lean_ptr_addr(v_k_x27_430_);
v___x_433_ = lean_usize_dec_eq(v___x_431_, v___x_432_);
if (v___x_433_ == 0)
{
lean_object* v___x_434_; lean_object* v___x_435_; 
v___x_434_ = lean_unsigned_to_nat(1u);
v___x_435_ = lean_nat_add(v_i_426_, v___x_434_);
lean_dec(v_i_426_);
v_i_426_ = v___x_435_;
goto _start;
}
else
{
lean_dec(v_i_426_);
return v___x_433_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_437_, lean_object* v_i_438_, lean_object* v_k_439_){
_start:
{
uint8_t v_res_440_; lean_object* v_r_441_; 
v_res_440_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0_spec__1___redArg(v_keys_437_, v_i_438_, v_k_439_);
lean_dec_ref(v_k_439_);
lean_dec_ref(v_keys_437_);
v_r_441_ = lean_box(v_res_440_);
return v_r_441_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0___redArg(lean_object* v_x_442_, size_t v_x_443_, lean_object* v_x_444_){
_start:
{
if (lean_obj_tag(v_x_442_) == 0)
{
lean_object* v_es_445_; lean_object* v___x_446_; size_t v___x_447_; size_t v___x_448_; lean_object* v_j_449_; lean_object* v___x_450_; 
v_es_445_ = lean_ctor_get(v_x_442_, 0);
v___x_446_ = lean_box(2);
v___x_447_ = ((size_t)31ULL);
v___x_448_ = lean_usize_land(v_x_443_, v___x_447_);
v_j_449_ = lean_usize_to_nat(v___x_448_);
v___x_450_ = lean_array_get_borrowed(v___x_446_, v_es_445_, v_j_449_);
lean_dec(v_j_449_);
switch(lean_obj_tag(v___x_450_))
{
case 0:
{
lean_object* v_key_451_; size_t v___x_452_; size_t v___x_453_; uint8_t v___x_454_; 
v_key_451_ = lean_ctor_get(v___x_450_, 0);
v___x_452_ = lean_ptr_addr(v_x_444_);
v___x_453_ = lean_ptr_addr(v_key_451_);
v___x_454_ = lean_usize_dec_eq(v___x_452_, v___x_453_);
return v___x_454_;
}
case 1:
{
lean_object* v_node_455_; size_t v___x_456_; size_t v___x_457_; 
v_node_455_ = lean_ctor_get(v___x_450_, 0);
v___x_456_ = ((size_t)5ULL);
v___x_457_ = lean_usize_shift_right(v_x_443_, v___x_456_);
v_x_442_ = v_node_455_;
v_x_443_ = v___x_457_;
goto _start;
}
default: 
{
uint8_t v___x_459_; 
v___x_459_ = 0;
return v___x_459_;
}
}
}
else
{
lean_object* v_ks_460_; lean_object* v___x_461_; uint8_t v___x_462_; 
v_ks_460_ = lean_ctor_get(v_x_442_, 0);
v___x_461_ = lean_unsigned_to_nat(0u);
v___x_462_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0_spec__1___redArg(v_ks_460_, v___x_461_, v_x_444_);
return v___x_462_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0___redArg___boxed(lean_object* v_x_463_, lean_object* v_x_464_, lean_object* v_x_465_){
_start:
{
size_t v_x_56116__boxed_466_; uint8_t v_res_467_; lean_object* v_r_468_; 
v_x_56116__boxed_466_ = lean_unbox_usize(v_x_464_);
lean_dec(v_x_464_);
v_res_467_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0___redArg(v_x_463_, v_x_56116__boxed_466_, v_x_465_);
lean_dec_ref(v_x_465_);
lean_dec_ref(v_x_463_);
v_r_468_ = lean_box(v_res_467_);
return v_r_468_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0___redArg(lean_object* v_x_469_, lean_object* v_x_470_){
_start:
{
size_t v___x_471_; size_t v___x_472_; size_t v___x_473_; uint64_t v___x_474_; size_t v___x_475_; uint8_t v___x_476_; 
v___x_471_ = lean_ptr_addr(v_x_470_);
v___x_472_ = ((size_t)3ULL);
v___x_473_ = lean_usize_shift_right(v___x_471_, v___x_472_);
v___x_474_ = lean_usize_to_uint64(v___x_473_);
v___x_475_ = lean_uint64_to_usize(v___x_474_);
v___x_476_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0___redArg(v_x_469_, v___x_475_, v_x_470_);
return v___x_476_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0___redArg___boxed(lean_object* v_x_477_, lean_object* v_x_478_){
_start:
{
uint8_t v_res_479_; lean_object* v_r_480_; 
v_res_479_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0___redArg(v_x_477_, v_x_478_);
lean_dec_ref(v_x_478_);
lean_dec_ref(v_x_477_);
v_r_480_ = lean_box(v_res_479_);
return v_r_480_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Expr_denoteExpr___at___00Lean_Meta_Grind_AC_internalize_spec__2(lean_object* v_e_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_){
_start:
{
if (lean_obj_tag(v_e_481_) == 0)
{
lean_object* v_x_494_; lean_object* v___x_495_; 
v_x_494_ = lean_ctor_get(v_e_481_, 0);
v___x_495_ = l_Lean_Meta_Grind_AC_ACM_getStruct(v___y_482_, v___y_483_, v___y_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_, v___y_489_, v___y_490_, v___y_491_, v___y_492_);
if (lean_obj_tag(v___x_495_) == 0)
{
lean_object* v_a_496_; lean_object* v___x_498_; uint8_t v_isShared_499_; uint8_t v_isSharedCheck_512_; 
v_a_496_ = lean_ctor_get(v___x_495_, 0);
v_isSharedCheck_512_ = !lean_is_exclusive(v___x_495_);
if (v_isSharedCheck_512_ == 0)
{
v___x_498_ = v___x_495_;
v_isShared_499_ = v_isSharedCheck_512_;
goto v_resetjp_497_;
}
else
{
lean_inc(v_a_496_);
lean_dec(v___x_495_);
v___x_498_ = lean_box(0);
v_isShared_499_ = v_isSharedCheck_512_;
goto v_resetjp_497_;
}
v_resetjp_497_:
{
lean_object* v_vars_500_; lean_object* v_size_501_; lean_object* v___x_502_; uint8_t v___x_503_; 
v_vars_500_ = lean_ctor_get(v_a_496_, 10);
lean_inc_ref(v_vars_500_);
lean_dec(v_a_496_);
v_size_501_ = lean_ctor_get(v_vars_500_, 2);
v___x_502_ = l_Lean_instInhabitedExpr;
v___x_503_ = lean_nat_dec_lt(v_x_494_, v_size_501_);
if (v___x_503_ == 0)
{
lean_object* v___x_504_; lean_object* v___x_506_; 
lean_dec_ref(v_vars_500_);
v___x_504_ = l_outOfBounds___redArg(v___x_502_);
if (v_isShared_499_ == 0)
{
lean_ctor_set(v___x_498_, 0, v___x_504_);
v___x_506_ = v___x_498_;
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
else
{
lean_object* v___x_508_; lean_object* v___x_510_; 
v___x_508_ = l_Lean_PersistentArray_get_x21___redArg(v___x_502_, v_vars_500_, v_x_494_);
lean_dec_ref(v_vars_500_);
if (v_isShared_499_ == 0)
{
lean_ctor_set(v___x_498_, 0, v___x_508_);
v___x_510_ = v___x_498_;
goto v_reusejp_509_;
}
else
{
lean_object* v_reuseFailAlloc_511_; 
v_reuseFailAlloc_511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_511_, 0, v___x_508_);
v___x_510_ = v_reuseFailAlloc_511_;
goto v_reusejp_509_;
}
v_reusejp_509_:
{
return v___x_510_;
}
}
}
}
else
{
lean_object* v_a_513_; lean_object* v___x_515_; uint8_t v_isShared_516_; uint8_t v_isSharedCheck_520_; 
v_a_513_ = lean_ctor_get(v___x_495_, 0);
v_isSharedCheck_520_ = !lean_is_exclusive(v___x_495_);
if (v_isSharedCheck_520_ == 0)
{
v___x_515_ = v___x_495_;
v_isShared_516_ = v_isSharedCheck_520_;
goto v_resetjp_514_;
}
else
{
lean_inc(v_a_513_);
lean_dec(v___x_495_);
v___x_515_ = lean_box(0);
v_isShared_516_ = v_isSharedCheck_520_;
goto v_resetjp_514_;
}
v_resetjp_514_:
{
lean_object* v___x_518_; 
if (v_isShared_516_ == 0)
{
v___x_518_ = v___x_515_;
goto v_reusejp_517_;
}
else
{
lean_object* v_reuseFailAlloc_519_; 
v_reuseFailAlloc_519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_519_, 0, v_a_513_);
v___x_518_ = v_reuseFailAlloc_519_;
goto v_reusejp_517_;
}
v_reusejp_517_:
{
return v___x_518_;
}
}
}
}
else
{
lean_object* v_lhs_521_; lean_object* v_rhs_522_; lean_object* v___x_523_; 
v_lhs_521_ = lean_ctor_get(v_e_481_, 0);
v_rhs_522_ = lean_ctor_get(v_e_481_, 1);
v___x_523_ = l_Lean_Meta_Grind_AC_ACM_getStruct(v___y_482_, v___y_483_, v___y_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_, v___y_489_, v___y_490_, v___y_491_, v___y_492_);
if (lean_obj_tag(v___x_523_) == 0)
{
lean_object* v_a_524_; lean_object* v___x_525_; 
v_a_524_ = lean_ctor_get(v___x_523_, 0);
lean_inc(v_a_524_);
lean_dec_ref_known(v___x_523_, 1);
v___x_525_ = l_Lean_Grind_AC_Expr_denoteExpr___at___00Lean_Meta_Grind_AC_internalize_spec__2(v_lhs_521_, v___y_482_, v___y_483_, v___y_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_, v___y_489_, v___y_490_, v___y_491_, v___y_492_);
if (lean_obj_tag(v___x_525_) == 0)
{
lean_object* v_a_526_; lean_object* v___x_527_; 
v_a_526_ = lean_ctor_get(v___x_525_, 0);
lean_inc(v_a_526_);
lean_dec_ref_known(v___x_525_, 1);
v___x_527_ = l_Lean_Grind_AC_Expr_denoteExpr___at___00Lean_Meta_Grind_AC_internalize_spec__2(v_rhs_522_, v___y_482_, v___y_483_, v___y_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_, v___y_489_, v___y_490_, v___y_491_, v___y_492_);
if (lean_obj_tag(v___x_527_) == 0)
{
lean_object* v_a_528_; lean_object* v___x_530_; uint8_t v_isShared_531_; uint8_t v_isSharedCheck_537_; 
v_a_528_ = lean_ctor_get(v___x_527_, 0);
v_isSharedCheck_537_ = !lean_is_exclusive(v___x_527_);
if (v_isSharedCheck_537_ == 0)
{
v___x_530_ = v___x_527_;
v_isShared_531_ = v_isSharedCheck_537_;
goto v_resetjp_529_;
}
else
{
lean_inc(v_a_528_);
lean_dec(v___x_527_);
v___x_530_ = lean_box(0);
v_isShared_531_ = v_isSharedCheck_537_;
goto v_resetjp_529_;
}
v_resetjp_529_:
{
lean_object* v_op_532_; lean_object* v___x_533_; lean_object* v___x_535_; 
v_op_532_ = lean_ctor_get(v_a_524_, 3);
lean_inc_ref(v_op_532_);
lean_dec(v_a_524_);
v___x_533_ = l_Lean_mkAppB(v_op_532_, v_a_526_, v_a_528_);
if (v_isShared_531_ == 0)
{
lean_ctor_set(v___x_530_, 0, v___x_533_);
v___x_535_ = v___x_530_;
goto v_reusejp_534_;
}
else
{
lean_object* v_reuseFailAlloc_536_; 
v_reuseFailAlloc_536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_536_, 0, v___x_533_);
v___x_535_ = v_reuseFailAlloc_536_;
goto v_reusejp_534_;
}
v_reusejp_534_:
{
return v___x_535_;
}
}
}
else
{
lean_dec(v_a_526_);
lean_dec(v_a_524_);
return v___x_527_;
}
}
else
{
lean_dec(v_a_524_);
return v___x_525_;
}
}
else
{
lean_object* v_a_538_; lean_object* v___x_540_; uint8_t v_isShared_541_; uint8_t v_isSharedCheck_545_; 
v_a_538_ = lean_ctor_get(v___x_523_, 0);
v_isSharedCheck_545_ = !lean_is_exclusive(v___x_523_);
if (v_isSharedCheck_545_ == 0)
{
v___x_540_ = v___x_523_;
v_isShared_541_ = v_isSharedCheck_545_;
goto v_resetjp_539_;
}
else
{
lean_inc(v_a_538_);
lean_dec(v___x_523_);
v___x_540_ = lean_box(0);
v_isShared_541_ = v_isSharedCheck_545_;
goto v_resetjp_539_;
}
v_resetjp_539_:
{
lean_object* v___x_543_; 
if (v_isShared_541_ == 0)
{
v___x_543_ = v___x_540_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_544_; 
v_reuseFailAlloc_544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_544_, 0, v_a_538_);
v___x_543_ = v_reuseFailAlloc_544_;
goto v_reusejp_542_;
}
v_reusejp_542_:
{
return v___x_543_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Expr_denoteExpr___at___00Lean_Meta_Grind_AC_internalize_spec__2___boxed(lean_object* v_e_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_){
_start:
{
lean_object* v_res_559_; 
v_res_559_ = l_Lean_Grind_AC_Expr_denoteExpr___at___00Lean_Meta_Grind_AC_internalize_spec__2(v_e_546_, v___y_547_, v___y_548_, v___y_549_, v___y_550_, v___y_551_, v___y_552_, v___y_553_, v___y_554_, v___y_555_, v___y_556_, v___y_557_);
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
lean_dec(v___y_547_);
lean_dec_ref(v_e_546_);
return v_res_559_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_AC_internalize___closed__6(void){
_start:
{
lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; 
v___x_570_ = ((lean_object*)(l_Lean_Meta_Grind_AC_internalize___closed__3));
v___x_571_ = ((lean_object*)(l_Lean_Meta_Grind_AC_internalize___closed__5));
v___x_572_ = l_Lean_Name_append(v___x_571_, v___x_570_);
return v___x_572_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_AC_internalize___closed__8(void){
_start:
{
lean_object* v___x_574_; lean_object* v___x_575_; 
v___x_574_ = ((lean_object*)(l_Lean_Meta_Grind_AC_internalize___closed__7));
v___x_575_ = l_Lean_stringToMessageData(v___x_574_);
return v___x_575_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_AC_internalize___closed__10(void){
_start:
{
lean_object* v___x_577_; lean_object* v___x_578_; 
v___x_577_ = ((lean_object*)(l_Lean_Meta_Grind_AC_internalize___closed__9));
v___x_578_ = l_Lean_stringToMessageData(v___x_577_);
return v___x_578_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_internalize(lean_object* v_e_579_, lean_object* v_parent_x3f_580_, lean_object* v_a_581_, lean_object* v_a_582_, lean_object* v_a_583_, lean_object* v_a_584_, lean_object* v_a_585_, lean_object* v_a_586_, lean_object* v_a_587_, lean_object* v_a_588_, lean_object* v_a_589_, lean_object* v_a_590_){
_start:
{
lean_object* v___y_593_; lean_object* v___y_594_; lean_object* v___y_595_; lean_object* v___y_596_; lean_object* v___y_597_; lean_object* v___y_598_; lean_object* v___y_599_; lean_object* v___y_600_; lean_object* v___y_601_; lean_object* v___y_602_; lean_object* v___y_603_; lean_object* v___x_607_; 
v___x_607_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_583_);
if (lean_obj_tag(v___x_607_) == 0)
{
lean_object* v_a_608_; lean_object* v___x_610_; uint8_t v_isShared_611_; uint8_t v_isSharedCheck_722_; 
v_a_608_ = lean_ctor_get(v___x_607_, 0);
v_isSharedCheck_722_ = !lean_is_exclusive(v___x_607_);
if (v_isSharedCheck_722_ == 0)
{
v___x_610_ = v___x_607_;
v_isShared_611_ = v_isSharedCheck_722_;
goto v_resetjp_609_;
}
else
{
lean_inc(v_a_608_);
lean_dec(v___x_607_);
v___x_610_ = lean_box(0);
v_isShared_611_ = v_isSharedCheck_722_;
goto v_resetjp_609_;
}
v_resetjp_609_:
{
uint8_t v_ac_612_; uint8_t v___y_614_; 
v_ac_612_ = lean_ctor_get_uint8(v_a_608_, sizeof(void*)*13 + 24);
lean_dec(v_a_608_);
if (v_ac_612_ == 0)
{
lean_object* v___x_717_; lean_object* v___x_718_; 
lean_del_object(v___x_610_);
lean_dec(v_parent_x3f_580_);
lean_dec_ref(v_e_579_);
v___x_717_ = lean_box(0);
v___x_718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_718_, 0, v___x_717_);
return v___x_718_;
}
else
{
uint8_t v___x_719_; 
v___x_719_ = l_Lean_Expr_isApp(v_e_579_);
if (v___x_719_ == 0)
{
v___y_614_ = v___x_719_;
goto v___jp_613_;
}
else
{
lean_object* v___x_720_; uint8_t v___x_721_; 
v___x_720_ = l_Lean_Expr_appFn_x21(v_e_579_);
v___x_721_ = l_Lean_Expr_isApp(v___x_720_);
lean_dec_ref(v___x_720_);
v___y_614_ = v___x_721_;
goto v___jp_613_;
}
}
v___jp_613_:
{
if (v___y_614_ == 0)
{
lean_object* v___x_615_; lean_object* v___x_617_; 
lean_dec(v_parent_x3f_580_);
lean_dec_ref(v_e_579_);
v___x_615_ = lean_box(0);
if (v_isShared_611_ == 0)
{
lean_ctor_set(v___x_610_, 0, v___x_615_);
v___x_617_ = v___x_610_;
goto v_reusejp_616_;
}
else
{
lean_object* v_reuseFailAlloc_618_; 
v_reuseFailAlloc_618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_618_, 0, v___x_615_);
v___x_617_ = v_reuseFailAlloc_618_;
goto v_reusejp_616_;
}
v_reusejp_616_:
{
return v___x_617_;
}
}
else
{
lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; 
lean_del_object(v___x_610_);
v___x_619_ = l_Lean_Expr_appFn_x21(v_e_579_);
v___x_620_ = l_Lean_Expr_appFn_x21(v___x_619_);
lean_dec_ref(v___x_619_);
lean_inc_ref(v___x_620_);
v___x_621_ = l_Lean_Meta_Grind_AC_getOpId_x3f(v___x_620_, v_a_581_, v_a_582_, v_a_583_, v_a_584_, v_a_585_, v_a_586_, v_a_587_, v_a_588_, v_a_589_, v_a_590_);
if (lean_obj_tag(v___x_621_) == 0)
{
lean_object* v_a_622_; lean_object* v___x_624_; uint8_t v_isShared_625_; uint8_t v_isSharedCheck_708_; 
v_a_622_ = lean_ctor_get(v___x_621_, 0);
v_isSharedCheck_708_ = !lean_is_exclusive(v___x_621_);
if (v_isSharedCheck_708_ == 0)
{
v___x_624_ = v___x_621_;
v_isShared_625_ = v_isSharedCheck_708_;
goto v_resetjp_623_;
}
else
{
lean_inc(v_a_622_);
lean_dec(v___x_621_);
v___x_624_ = lean_box(0);
v_isShared_625_ = v_isSharedCheck_708_;
goto v_resetjp_623_;
}
v_resetjp_623_:
{
if (lean_obj_tag(v_a_622_) == 1)
{
lean_object* v_val_626_; lean_object* v___x_627_; lean_object* v_a_628_; lean_object* v___x_630_; uint8_t v_isShared_631_; uint8_t v_isSharedCheck_703_; 
lean_del_object(v___x_624_);
v_val_626_ = lean_ctor_get(v_a_622_, 0);
lean_inc(v_val_626_);
lean_dec_ref_known(v_a_622_, 1);
v___x_627_ = l___private_Lean_Meta_Tactic_Grind_AC_Internalize_0__Lean_Meta_Grind_AC_isParentSameOpApp___redArg(v_parent_x3f_580_, v___x_620_);
lean_dec_ref(v___x_620_);
v_a_628_ = lean_ctor_get(v___x_627_, 0);
v_isSharedCheck_703_ = !lean_is_exclusive(v___x_627_);
if (v_isSharedCheck_703_ == 0)
{
v___x_630_ = v___x_627_;
v_isShared_631_ = v_isSharedCheck_703_;
goto v_resetjp_629_;
}
else
{
lean_inc(v_a_628_);
lean_dec(v___x_627_);
v___x_630_ = lean_box(0);
v_isShared_631_ = v_isSharedCheck_703_;
goto v_resetjp_629_;
}
v_resetjp_629_:
{
uint8_t v___x_632_; 
v___x_632_ = lean_unbox(v_a_628_);
lean_dec(v_a_628_);
if (v___x_632_ == 0)
{
lean_object* v___x_633_; 
lean_del_object(v___x_630_);
v___x_633_ = l_Lean_Meta_Grind_AC_ACM_getStruct(v_val_626_, v_a_581_, v_a_582_, v_a_583_, v_a_584_, v_a_585_, v_a_586_, v_a_587_, v_a_588_, v_a_589_, v_a_590_);
if (lean_obj_tag(v___x_633_) == 0)
{
lean_object* v_a_634_; lean_object* v___x_636_; uint8_t v_isShared_637_; uint8_t v_isSharedCheck_690_; 
v_a_634_ = lean_ctor_get(v___x_633_, 0);
v_isSharedCheck_690_ = !lean_is_exclusive(v___x_633_);
if (v_isSharedCheck_690_ == 0)
{
v___x_636_ = v___x_633_;
v_isShared_637_ = v_isSharedCheck_690_;
goto v_resetjp_635_;
}
else
{
lean_inc(v_a_634_);
lean_dec(v___x_633_);
v___x_636_ = lean_box(0);
v_isShared_637_ = v_isSharedCheck_690_;
goto v_resetjp_635_;
}
v_resetjp_635_:
{
lean_object* v_denote_638_; uint8_t v___x_639_; 
v_denote_638_ = lean_ctor_get(v_a_634_, 12);
lean_inc_ref(v_denote_638_);
lean_dec(v_a_634_);
v___x_639_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0___redArg(v_denote_638_, v_e_579_);
lean_dec_ref(v_denote_638_);
if (v___x_639_ == 0)
{
lean_object* v___x_640_; 
lean_del_object(v___x_636_);
lean_inc_ref(v_e_579_);
v___x_640_ = l_Lean_Meta_Grind_AC_reify(v_e_579_, v_val_626_, v_a_581_, v_a_582_, v_a_583_, v_a_584_, v_a_585_, v_a_586_, v_a_587_, v_a_588_, v_a_589_, v_a_590_);
if (lean_obj_tag(v___x_640_) == 0)
{
lean_object* v_a_641_; lean_object* v___x_642_; lean_object* v___f_643_; lean_object* v___x_644_; 
v_a_641_ = lean_ctor_get(v___x_640_, 0);
lean_inc_n(v_a_641_, 2);
lean_dec_ref_known(v___x_640_, 1);
v___x_642_ = lean_box(v_ac_612_);
lean_inc_ref(v_e_579_);
v___f_643_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_AC_internalize___lam__0___boxed), 4, 3);
lean_closure_set(v___f_643_, 0, v_e_579_);
lean_closure_set(v___f_643_, 1, v_a_641_);
lean_closure_set(v___f_643_, 2, v___x_642_);
v___x_644_ = l_Lean_Meta_Grind_AC_modifyStruct___redArg(v___f_643_, v_val_626_, v_a_581_);
if (lean_obj_tag(v___x_644_) == 0)
{
lean_object* v___x_646_; uint8_t v_isShared_647_; uint8_t v_isSharedCheck_676_; 
v_isSharedCheck_676_ = !lean_is_exclusive(v___x_644_);
if (v_isSharedCheck_676_ == 0)
{
lean_object* v_unused_677_; 
v_unused_677_ = lean_ctor_get(v___x_644_, 0);
lean_dec(v_unused_677_);
v___x_646_ = v___x_644_;
v_isShared_647_ = v_isSharedCheck_676_;
goto v_resetjp_645_;
}
else
{
lean_dec(v___x_644_);
v___x_646_ = lean_box(0);
v_isShared_647_ = v_isSharedCheck_676_;
goto v_resetjp_645_;
}
v_resetjp_645_:
{
lean_object* v_options_648_; uint8_t v_hasTrace_649_; 
v_options_648_ = lean_ctor_get(v_a_589_, 2);
v_hasTrace_649_ = lean_ctor_get_uint8(v_options_648_, sizeof(void*)*1);
if (v_hasTrace_649_ == 0)
{
lean_del_object(v___x_646_);
lean_dec(v_a_641_);
v___y_593_ = v_val_626_;
v___y_594_ = v_a_581_;
v___y_595_ = v_a_582_;
v___y_596_ = v_a_583_;
v___y_597_ = v_a_584_;
v___y_598_ = v_a_585_;
v___y_599_ = v_a_586_;
v___y_600_ = v_a_587_;
v___y_601_ = v_a_588_;
v___y_602_ = v_a_589_;
v___y_603_ = v_a_590_;
goto v___jp_592_;
}
else
{
lean_object* v_inheritedTraceOptions_650_; lean_object* v___x_651_; lean_object* v___x_652_; uint8_t v___x_653_; 
v_inheritedTraceOptions_650_ = lean_ctor_get(v_a_589_, 13);
v___x_651_ = ((lean_object*)(l_Lean_Meta_Grind_AC_internalize___closed__3));
v___x_652_ = lean_obj_once(&l_Lean_Meta_Grind_AC_internalize___closed__6, &l_Lean_Meta_Grind_AC_internalize___closed__6_once, _init_l_Lean_Meta_Grind_AC_internalize___closed__6);
v___x_653_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_650_, v_options_648_, v___x_652_);
if (v___x_653_ == 0)
{
lean_del_object(v___x_646_);
lean_dec(v_a_641_);
v___y_593_ = v_val_626_;
v___y_594_ = v_a_581_;
v___y_595_ = v_a_582_;
v___y_596_ = v_a_583_;
v___y_597_ = v_a_584_;
v___y_598_ = v_a_585_;
v___y_599_ = v_a_586_;
v___y_600_ = v_a_587_;
v___y_601_ = v_a_588_;
v___y_602_ = v_a_589_;
v___y_603_ = v_a_590_;
goto v___jp_592_;
}
else
{
lean_object* v___x_654_; 
v___x_654_ = l_Lean_Grind_AC_Expr_denoteExpr___at___00Lean_Meta_Grind_AC_internalize_spec__2(v_a_641_, v_val_626_, v_a_581_, v_a_582_, v_a_583_, v_a_584_, v_a_585_, v_a_586_, v_a_587_, v_a_588_, v_a_589_, v_a_590_);
lean_dec(v_a_641_);
if (lean_obj_tag(v___x_654_) == 0)
{
lean_object* v_a_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_659_; 
v_a_655_ = lean_ctor_get(v___x_654_, 0);
lean_inc(v_a_655_);
lean_dec_ref_known(v___x_654_, 1);
v___x_656_ = lean_obj_once(&l_Lean_Meta_Grind_AC_internalize___closed__8, &l_Lean_Meta_Grind_AC_internalize___closed__8_once, _init_l_Lean_Meta_Grind_AC_internalize___closed__8);
lean_inc(v_val_626_);
v___x_657_ = l_Nat_reprFast(v_val_626_);
if (v_isShared_647_ == 0)
{
lean_ctor_set_tag(v___x_646_, 3);
lean_ctor_set(v___x_646_, 0, v___x_657_);
v___x_659_ = v___x_646_;
goto v_reusejp_658_;
}
else
{
lean_object* v_reuseFailAlloc_667_; 
v_reuseFailAlloc_667_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_667_, 0, v___x_657_);
v___x_659_ = v_reuseFailAlloc_667_;
goto v_reusejp_658_;
}
v_reusejp_658_:
{
lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; 
v___x_660_ = l_Lean_MessageData_ofFormat(v___x_659_);
v___x_661_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_661_, 0, v___x_656_);
lean_ctor_set(v___x_661_, 1, v___x_660_);
v___x_662_ = lean_obj_once(&l_Lean_Meta_Grind_AC_internalize___closed__10, &l_Lean_Meta_Grind_AC_internalize___closed__10_once, _init_l_Lean_Meta_Grind_AC_internalize___closed__10);
v___x_663_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_663_, 0, v___x_661_);
lean_ctor_set(v___x_663_, 1, v___x_662_);
v___x_664_ = l_Lean_MessageData_ofExpr(v_a_655_);
v___x_665_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_665_, 0, v___x_663_);
lean_ctor_set(v___x_665_, 1, v___x_664_);
v___x_666_ = l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3___redArg(v___x_651_, v___x_665_, v_a_587_, v_a_588_, v_a_589_, v_a_590_);
if (lean_obj_tag(v___x_666_) == 0)
{
lean_dec_ref_known(v___x_666_, 1);
v___y_593_ = v_val_626_;
v___y_594_ = v_a_581_;
v___y_595_ = v_a_582_;
v___y_596_ = v_a_583_;
v___y_597_ = v_a_584_;
v___y_598_ = v_a_585_;
v___y_599_ = v_a_586_;
v___y_600_ = v_a_587_;
v___y_601_ = v_a_588_;
v___y_602_ = v_a_589_;
v___y_603_ = v_a_590_;
goto v___jp_592_;
}
else
{
lean_dec(v_val_626_);
lean_dec_ref(v_e_579_);
return v___x_666_;
}
}
}
else
{
lean_object* v_a_668_; lean_object* v___x_670_; uint8_t v_isShared_671_; uint8_t v_isSharedCheck_675_; 
lean_del_object(v___x_646_);
lean_dec(v_val_626_);
lean_dec_ref(v_e_579_);
v_a_668_ = lean_ctor_get(v___x_654_, 0);
v_isSharedCheck_675_ = !lean_is_exclusive(v___x_654_);
if (v_isSharedCheck_675_ == 0)
{
v___x_670_ = v___x_654_;
v_isShared_671_ = v_isSharedCheck_675_;
goto v_resetjp_669_;
}
else
{
lean_inc(v_a_668_);
lean_dec(v___x_654_);
v___x_670_ = lean_box(0);
v_isShared_671_ = v_isSharedCheck_675_;
goto v_resetjp_669_;
}
v_resetjp_669_:
{
lean_object* v___x_673_; 
if (v_isShared_671_ == 0)
{
v___x_673_ = v___x_670_;
goto v_reusejp_672_;
}
else
{
lean_object* v_reuseFailAlloc_674_; 
v_reuseFailAlloc_674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_674_, 0, v_a_668_);
v___x_673_ = v_reuseFailAlloc_674_;
goto v_reusejp_672_;
}
v_reusejp_672_:
{
return v___x_673_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_641_);
lean_dec(v_val_626_);
lean_dec_ref(v_e_579_);
return v___x_644_;
}
}
else
{
lean_object* v_a_678_; lean_object* v___x_680_; uint8_t v_isShared_681_; uint8_t v_isSharedCheck_685_; 
lean_dec(v_val_626_);
lean_dec_ref(v_e_579_);
v_a_678_ = lean_ctor_get(v___x_640_, 0);
v_isSharedCheck_685_ = !lean_is_exclusive(v___x_640_);
if (v_isSharedCheck_685_ == 0)
{
v___x_680_ = v___x_640_;
v_isShared_681_ = v_isSharedCheck_685_;
goto v_resetjp_679_;
}
else
{
lean_inc(v_a_678_);
lean_dec(v___x_640_);
v___x_680_ = lean_box(0);
v_isShared_681_ = v_isSharedCheck_685_;
goto v_resetjp_679_;
}
v_resetjp_679_:
{
lean_object* v___x_683_; 
if (v_isShared_681_ == 0)
{
v___x_683_ = v___x_680_;
goto v_reusejp_682_;
}
else
{
lean_object* v_reuseFailAlloc_684_; 
v_reuseFailAlloc_684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_684_, 0, v_a_678_);
v___x_683_ = v_reuseFailAlloc_684_;
goto v_reusejp_682_;
}
v_reusejp_682_:
{
return v___x_683_;
}
}
}
}
else
{
lean_object* v___x_686_; lean_object* v___x_688_; 
lean_dec(v_val_626_);
lean_dec_ref(v_e_579_);
v___x_686_ = lean_box(0);
if (v_isShared_637_ == 0)
{
lean_ctor_set(v___x_636_, 0, v___x_686_);
v___x_688_ = v___x_636_;
goto v_reusejp_687_;
}
else
{
lean_object* v_reuseFailAlloc_689_; 
v_reuseFailAlloc_689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_689_, 0, v___x_686_);
v___x_688_ = v_reuseFailAlloc_689_;
goto v_reusejp_687_;
}
v_reusejp_687_:
{
return v___x_688_;
}
}
}
}
else
{
lean_object* v_a_691_; lean_object* v___x_693_; uint8_t v_isShared_694_; uint8_t v_isSharedCheck_698_; 
lean_dec(v_val_626_);
lean_dec_ref(v_e_579_);
v_a_691_ = lean_ctor_get(v___x_633_, 0);
v_isSharedCheck_698_ = !lean_is_exclusive(v___x_633_);
if (v_isSharedCheck_698_ == 0)
{
v___x_693_ = v___x_633_;
v_isShared_694_ = v_isSharedCheck_698_;
goto v_resetjp_692_;
}
else
{
lean_inc(v_a_691_);
lean_dec(v___x_633_);
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
lean_object* v___x_699_; lean_object* v___x_701_; 
lean_dec(v_val_626_);
lean_dec_ref(v_e_579_);
v___x_699_ = lean_box(0);
if (v_isShared_631_ == 0)
{
lean_ctor_set(v___x_630_, 0, v___x_699_);
v___x_701_ = v___x_630_;
goto v_reusejp_700_;
}
else
{
lean_object* v_reuseFailAlloc_702_; 
v_reuseFailAlloc_702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_702_, 0, v___x_699_);
v___x_701_ = v_reuseFailAlloc_702_;
goto v_reusejp_700_;
}
v_reusejp_700_:
{
return v___x_701_;
}
}
}
}
else
{
lean_object* v___x_704_; lean_object* v___x_706_; 
lean_dec(v_a_622_);
lean_dec_ref(v___x_620_);
lean_dec(v_parent_x3f_580_);
lean_dec_ref(v_e_579_);
v___x_704_ = lean_box(0);
if (v_isShared_625_ == 0)
{
lean_ctor_set(v___x_624_, 0, v___x_704_);
v___x_706_ = v___x_624_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_707_; 
v_reuseFailAlloc_707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_707_, 0, v___x_704_);
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
lean_object* v_a_709_; lean_object* v___x_711_; uint8_t v_isShared_712_; uint8_t v_isSharedCheck_716_; 
lean_dec_ref(v___x_620_);
lean_dec(v_parent_x3f_580_);
lean_dec_ref(v_e_579_);
v_a_709_ = lean_ctor_get(v___x_621_, 0);
v_isSharedCheck_716_ = !lean_is_exclusive(v___x_621_);
if (v_isSharedCheck_716_ == 0)
{
v___x_711_ = v___x_621_;
v_isShared_712_ = v_isSharedCheck_716_;
goto v_resetjp_710_;
}
else
{
lean_inc(v_a_709_);
lean_dec(v___x_621_);
v___x_711_ = lean_box(0);
v_isShared_712_ = v_isSharedCheck_716_;
goto v_resetjp_710_;
}
v_resetjp_710_:
{
lean_object* v___x_714_; 
if (v_isShared_712_ == 0)
{
v___x_714_ = v___x_711_;
goto v_reusejp_713_;
}
else
{
lean_object* v_reuseFailAlloc_715_; 
v_reuseFailAlloc_715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_715_, 0, v_a_709_);
v___x_714_ = v_reuseFailAlloc_715_;
goto v_reusejp_713_;
}
v_reusejp_713_:
{
return v___x_714_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_723_; lean_object* v___x_725_; uint8_t v_isShared_726_; uint8_t v_isSharedCheck_730_; 
lean_dec(v_parent_x3f_580_);
lean_dec_ref(v_e_579_);
v_a_723_ = lean_ctor_get(v___x_607_, 0);
v_isSharedCheck_730_ = !lean_is_exclusive(v___x_607_);
if (v_isSharedCheck_730_ == 0)
{
v___x_725_ = v___x_607_;
v_isShared_726_ = v_isSharedCheck_730_;
goto v_resetjp_724_;
}
else
{
lean_inc(v_a_723_);
lean_dec(v___x_607_);
v___x_725_ = lean_box(0);
v_isShared_726_ = v_isSharedCheck_730_;
goto v_resetjp_724_;
}
v_resetjp_724_:
{
lean_object* v___x_728_; 
if (v_isShared_726_ == 0)
{
v___x_728_ = v___x_725_;
goto v_reusejp_727_;
}
else
{
lean_object* v_reuseFailAlloc_729_; 
v_reuseFailAlloc_729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_729_, 0, v_a_723_);
v___x_728_ = v_reuseFailAlloc_729_;
goto v_reusejp_727_;
}
v_reusejp_727_:
{
return v___x_728_;
}
}
}
v___jp_592_:
{
lean_object* v___x_604_; 
lean_inc_ref(v_e_579_);
v___x_604_ = l_Lean_Meta_Grind_AC_addTermOpId___redArg(v_e_579_, v___y_593_, v___y_594_);
lean_dec(v___y_593_);
if (lean_obj_tag(v___x_604_) == 0)
{
lean_object* v___x_605_; lean_object* v___x_606_; 
lean_dec_ref_known(v___x_604_, 1);
v___x_605_ = l_Lean_Meta_Grind_AC_acExt;
v___x_606_ = l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(v___x_605_, v_e_579_, v___y_594_, v___y_595_, v___y_596_, v___y_597_, v___y_598_, v___y_599_, v___y_600_, v___y_601_, v___y_602_, v___y_603_);
return v___x_606_;
}
else
{
lean_dec_ref(v_e_579_);
return v___x_604_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_internalize___boxed(lean_object* v_e_731_, lean_object* v_parent_x3f_732_, lean_object* v_a_733_, lean_object* v_a_734_, lean_object* v_a_735_, lean_object* v_a_736_, lean_object* v_a_737_, lean_object* v_a_738_, lean_object* v_a_739_, lean_object* v_a_740_, lean_object* v_a_741_, lean_object* v_a_742_, lean_object* v_a_743_){
_start:
{
lean_object* v_res_744_; 
v_res_744_ = l_Lean_Meta_Grind_AC_internalize(v_e_731_, v_parent_x3f_732_, v_a_733_, v_a_734_, v_a_735_, v_a_736_, v_a_737_, v_a_738_, v_a_739_, v_a_740_, v_a_741_, v_a_742_);
lean_dec(v_a_742_);
lean_dec_ref(v_a_741_);
lean_dec(v_a_740_);
lean_dec_ref(v_a_739_);
lean_dec(v_a_738_);
lean_dec_ref(v_a_737_);
lean_dec(v_a_736_);
lean_dec_ref(v_a_735_);
lean_dec(v_a_734_);
lean_dec(v_a_733_);
return v_res_744_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0(lean_object* v_00_u03b2_745_, lean_object* v_x_746_, lean_object* v_x_747_){
_start:
{
uint8_t v___x_748_; 
v___x_748_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0___redArg(v_x_746_, v_x_747_);
return v___x_748_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0___boxed(lean_object* v_00_u03b2_749_, lean_object* v_x_750_, lean_object* v_x_751_){
_start:
{
uint8_t v_res_752_; lean_object* v_r_753_; 
v_res_752_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0(v_00_u03b2_749_, v_x_750_, v_x_751_);
lean_dec_ref(v_x_751_);
lean_dec_ref(v_x_750_);
v_r_753_ = lean_box(v_res_752_);
return v_r_753_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1(lean_object* v_00_u03b2_754_, lean_object* v_x_755_, lean_object* v_x_756_, lean_object* v_x_757_){
_start:
{
lean_object* v___x_758_; 
v___x_758_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1___redArg(v_x_755_, v_x_756_, v_x_757_);
return v___x_758_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3(lean_object* v_cls_759_, lean_object* v_msg_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_){
_start:
{
lean_object* v___x_773_; 
v___x_773_ = l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3___redArg(v_cls_759_, v_msg_760_, v___y_768_, v___y_769_, v___y_770_, v___y_771_);
return v___x_773_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3___boxed(lean_object* v_cls_774_, lean_object* v_msg_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_){
_start:
{
lean_object* v_res_788_; 
v_res_788_ = l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3(v_cls_774_, v_msg_775_, v___y_776_, v___y_777_, v___y_778_, v___y_779_, v___y_780_, v___y_781_, v___y_782_, v___y_783_, v___y_784_, v___y_785_, v___y_786_);
lean_dec(v___y_786_);
lean_dec_ref(v___y_785_);
lean_dec(v___y_784_);
lean_dec_ref(v___y_783_);
lean_dec(v___y_782_);
lean_dec_ref(v___y_781_);
lean_dec(v___y_780_);
lean_dec_ref(v___y_779_);
lean_dec(v___y_778_);
lean_dec(v___y_777_);
lean_dec(v___y_776_);
return v_res_788_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0(lean_object* v_00_u03b2_789_, lean_object* v_x_790_, size_t v_x_791_, lean_object* v_x_792_){
_start:
{
uint8_t v___x_793_; 
v___x_793_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0___redArg(v_x_790_, v_x_791_, v_x_792_);
return v___x_793_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0___boxed(lean_object* v_00_u03b2_794_, lean_object* v_x_795_, lean_object* v_x_796_, lean_object* v_x_797_){
_start:
{
size_t v_x_56703__boxed_798_; uint8_t v_res_799_; lean_object* v_r_800_; 
v_x_56703__boxed_798_ = lean_unbox_usize(v_x_796_);
lean_dec(v_x_796_);
v_res_799_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0(v_00_u03b2_794_, v_x_795_, v_x_56703__boxed_798_, v_x_797_);
lean_dec_ref(v_x_797_);
lean_dec_ref(v_x_795_);
v_r_800_ = lean_box(v_res_799_);
return v_r_800_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2(lean_object* v_00_u03b2_801_, lean_object* v_x_802_, size_t v_x_803_, size_t v_x_804_, lean_object* v_x_805_, lean_object* v_x_806_){
_start:
{
lean_object* v___x_807_; 
v___x_807_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___redArg(v_x_802_, v_x_803_, v_x_804_, v_x_805_, v_x_806_);
return v___x_807_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___boxed(lean_object* v_00_u03b2_808_, lean_object* v_x_809_, lean_object* v_x_810_, lean_object* v_x_811_, lean_object* v_x_812_, lean_object* v_x_813_){
_start:
{
size_t v_x_56714__boxed_814_; size_t v_x_56715__boxed_815_; lean_object* v_res_816_; 
v_x_56714__boxed_814_ = lean_unbox_usize(v_x_810_);
lean_dec(v_x_810_);
v_x_56715__boxed_815_ = lean_unbox_usize(v_x_811_);
lean_dec(v_x_811_);
v_res_816_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2(v_00_u03b2_808_, v_x_809_, v_x_56714__boxed_814_, v_x_56715__boxed_815_, v_x_812_, v_x_813_);
return v_res_816_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_817_, lean_object* v_keys_818_, lean_object* v_vals_819_, lean_object* v_heq_820_, lean_object* v_i_821_, lean_object* v_k_822_){
_start:
{
uint8_t v___x_823_; 
v___x_823_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0_spec__1___redArg(v_keys_818_, v_i_821_, v_k_822_);
return v___x_823_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_824_, lean_object* v_keys_825_, lean_object* v_vals_826_, lean_object* v_heq_827_, lean_object* v_i_828_, lean_object* v_k_829_){
_start:
{
uint8_t v_res_830_; lean_object* v_r_831_; 
v_res_830_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0_spec__1(v_00_u03b2_824_, v_keys_825_, v_vals_826_, v_heq_827_, v_i_828_, v_k_829_);
lean_dec_ref(v_k_829_);
lean_dec_ref(v_vals_826_);
lean_dec_ref(v_keys_825_);
v_r_831_ = lean_box(v_res_830_);
return v_r_831_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_832_, lean_object* v_n_833_, lean_object* v_k_834_, lean_object* v_v_835_){
_start:
{
lean_object* v___x_836_; 
v___x_836_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2_spec__4___redArg(v_n_833_, v_k_834_, v_v_835_);
return v___x_836_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_837_, size_t v_depth_838_, lean_object* v_keys_839_, lean_object* v_vals_840_, lean_object* v_heq_841_, lean_object* v_i_842_, lean_object* v_entries_843_){
_start:
{
lean_object* v___x_844_; 
v___x_844_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2_spec__5___redArg(v_depth_838_, v_keys_839_, v_vals_840_, v_i_842_, v_entries_843_);
return v___x_844_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_845_, lean_object* v_depth_846_, lean_object* v_keys_847_, lean_object* v_vals_848_, lean_object* v_heq_849_, lean_object* v_i_850_, lean_object* v_entries_851_){
_start:
{
size_t v_depth_boxed_852_; lean_object* v_res_853_; 
v_depth_boxed_852_ = lean_unbox_usize(v_depth_846_);
lean_dec(v_depth_846_);
v_res_853_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2_spec__5(v_00_u03b2_845_, v_depth_boxed_852_, v_keys_847_, v_vals_848_, v_heq_849_, v_i_850_, v_entries_851_);
lean_dec_ref(v_vals_848_);
lean_dec_ref(v_keys_847_);
return v_res_853_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2_spec__4_spec__8(lean_object* v_00_u03b2_854_, lean_object* v_x_855_, lean_object* v_x_856_, lean_object* v_x_857_, lean_object* v_x_858_){
_start:
{
lean_object* v___x_859_; 
v___x_859_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2_spec__4_spec__8___redArg(v_x_855_, v_x_856_, v_x_857_, v_x_858_);
return v___x_859_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_AC_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_AC_DenoteExpr(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_AC_Internalize(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Grind_AC_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_AC_DenoteExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_AC_Internalize(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Grind_AC_Util(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_AC_DenoteExpr(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_AC_Internalize(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_AC_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_AC_DenoteExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_AC_Internalize(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_AC_Internalize(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_AC_Internalize(builtin);
}
#ifdef __cplusplus
}
#endif
