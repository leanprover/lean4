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
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
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
lean_object* v_ks_229_; lean_object* v_vs_230_; lean_object* v___x_232_; uint8_t v_isShared_233_; uint8_t v_isSharedCheck_248_; 
v_ks_229_ = lean_ctor_get(v_x_176_, 0);
v_vs_230_ = lean_ctor_get(v_x_176_, 1);
v_isSharedCheck_248_ = !lean_is_exclusive(v_x_176_);
if (v_isSharedCheck_248_ == 0)
{
v___x_232_ = v_x_176_;
v_isShared_233_ = v_isSharedCheck_248_;
goto v_resetjp_231_;
}
else
{
lean_inc(v_vs_230_);
lean_inc(v_ks_229_);
lean_dec(v_x_176_);
v___x_232_ = lean_box(0);
v_isShared_233_ = v_isSharedCheck_248_;
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
lean_object* v_reuseFailAlloc_247_; 
v_reuseFailAlloc_247_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_247_, 0, v_ks_229_);
lean_ctor_set(v_reuseFailAlloc_247_, 1, v_vs_230_);
v___x_235_ = v_reuseFailAlloc_247_;
goto v_reusejp_234_;
}
v_reusejp_234_:
{
lean_object* v_newNode_236_; size_t v___x_237_; uint8_t v___x_238_; 
v_newNode_236_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2_spec__4___redArg(v___x_235_, v_x_179_, v_x_180_);
v___x_237_ = ((size_t)7ULL);
v___x_238_ = lean_usize_dec_le(v___x_237_, v_x_178_);
if (v___x_238_ == 0)
{
lean_object* v___x_239_; lean_object* v___x_240_; uint8_t v___x_241_; 
v___x_239_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_236_);
v___x_240_ = lean_unsigned_to_nat(4u);
v___x_241_ = lean_nat_dec_lt(v___x_239_, v___x_240_);
lean_dec(v___x_239_);
if (v___x_241_ == 0)
{
lean_object* v_ks_242_; lean_object* v_vs_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; 
v_ks_242_ = lean_ctor_get(v_newNode_236_, 0);
lean_inc_ref(v_ks_242_);
v_vs_243_ = lean_ctor_get(v_newNode_236_, 1);
lean_inc_ref(v_vs_243_);
lean_dec_ref(v_newNode_236_);
v___x_244_ = lean_unsigned_to_nat(0u);
v___x_245_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___redArg___closed__0);
v___x_246_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2_spec__5___redArg(v_x_178_, v_ks_242_, v_vs_243_, v___x_244_, v___x_245_);
lean_dec_ref(v_vs_243_);
lean_dec_ref(v_ks_242_);
return v___x_246_;
}
else
{
return v_newNode_236_;
}
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
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2_spec__5___redArg(size_t v_depth_249_, lean_object* v_keys_250_, lean_object* v_vals_251_, lean_object* v_i_252_, lean_object* v_entries_253_){
_start:
{
lean_object* v___x_254_; uint8_t v___x_255_; 
v___x_254_ = lean_array_get_size(v_keys_250_);
v___x_255_ = lean_nat_dec_lt(v_i_252_, v___x_254_);
if (v___x_255_ == 0)
{
lean_dec(v_i_252_);
return v_entries_253_;
}
else
{
lean_object* v_k_256_; lean_object* v_v_257_; size_t v___x_258_; size_t v___x_259_; size_t v___x_260_; uint64_t v___x_261_; size_t v_h_262_; size_t v___x_263_; lean_object* v___x_264_; size_t v___x_265_; size_t v___x_266_; size_t v___x_267_; size_t v_h_268_; lean_object* v___x_269_; lean_object* v___x_270_; 
v_k_256_ = lean_array_fget_borrowed(v_keys_250_, v_i_252_);
v_v_257_ = lean_array_fget_borrowed(v_vals_251_, v_i_252_);
v___x_258_ = lean_ptr_addr(v_k_256_);
v___x_259_ = ((size_t)3ULL);
v___x_260_ = lean_usize_shift_right(v___x_258_, v___x_259_);
v___x_261_ = lean_usize_to_uint64(v___x_260_);
v_h_262_ = lean_uint64_to_usize(v___x_261_);
v___x_263_ = ((size_t)5ULL);
v___x_264_ = lean_unsigned_to_nat(1u);
v___x_265_ = ((size_t)1ULL);
v___x_266_ = lean_usize_sub(v_depth_249_, v___x_265_);
v___x_267_ = lean_usize_mul(v___x_263_, v___x_266_);
v_h_268_ = lean_usize_shift_right(v_h_262_, v___x_267_);
v___x_269_ = lean_nat_add(v_i_252_, v___x_264_);
lean_dec(v_i_252_);
lean_inc(v_v_257_);
lean_inc(v_k_256_);
v___x_270_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___redArg(v_entries_253_, v_h_268_, v_depth_249_, v_k_256_, v_v_257_);
v_i_252_ = v___x_269_;
v_entries_253_ = v___x_270_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_depth_272_, lean_object* v_keys_273_, lean_object* v_vals_274_, lean_object* v_i_275_, lean_object* v_entries_276_){
_start:
{
size_t v_depth_boxed_277_; lean_object* v_res_278_; 
v_depth_boxed_277_ = lean_unbox_usize(v_depth_272_);
lean_dec(v_depth_272_);
v_res_278_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2_spec__5___redArg(v_depth_boxed_277_, v_keys_273_, v_vals_274_, v_i_275_, v_entries_276_);
lean_dec_ref(v_vals_274_);
lean_dec_ref(v_keys_273_);
return v_res_278_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___redArg___boxed(lean_object* v_x_279_, lean_object* v_x_280_, lean_object* v_x_281_, lean_object* v_x_282_, lean_object* v_x_283_){
_start:
{
size_t v_x_38247__boxed_284_; size_t v_x_38248__boxed_285_; lean_object* v_res_286_; 
v_x_38247__boxed_284_ = lean_unbox_usize(v_x_280_);
lean_dec(v_x_280_);
v_x_38248__boxed_285_ = lean_unbox_usize(v_x_281_);
lean_dec(v_x_281_);
v_res_286_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___redArg(v_x_279_, v_x_38247__boxed_284_, v_x_38248__boxed_285_, v_x_282_, v_x_283_);
return v_res_286_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1___redArg(lean_object* v_x_287_, lean_object* v_x_288_, lean_object* v_x_289_){
_start:
{
size_t v___x_290_; size_t v___x_291_; size_t v___x_292_; uint64_t v___x_293_; size_t v___x_294_; size_t v___x_295_; lean_object* v___x_296_; 
v___x_290_ = lean_ptr_addr(v_x_288_);
v___x_291_ = ((size_t)3ULL);
v___x_292_ = lean_usize_shift_right(v___x_290_, v___x_291_);
v___x_293_ = lean_usize_to_uint64(v___x_292_);
v___x_294_ = lean_uint64_to_usize(v___x_293_);
v___x_295_ = ((size_t)1ULL);
v___x_296_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___redArg(v_x_287_, v___x_294_, v___x_295_, v_x_288_, v_x_289_);
return v___x_296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_internalize___lam__0(lean_object* v_e_297_, lean_object* v_a_298_, uint8_t v_ac_299_, lean_object* v_s_300_){
_start:
{
lean_object* v_id_301_; lean_object* v_type_302_; lean_object* v_u_303_; lean_object* v_op_304_; lean_object* v_neutral_x3f_305_; lean_object* v_assocInst_306_; lean_object* v_idempotentInst_x3f_307_; lean_object* v_commInst_x3f_308_; lean_object* v_neutralInst_x3f_309_; lean_object* v_nextId_310_; lean_object* v_vars_311_; lean_object* v_varMap_312_; lean_object* v_denote_313_; lean_object* v_denoteEntries_314_; lean_object* v_queue_315_; lean_object* v_basis_316_; lean_object* v_diseqs_317_; lean_object* v___x_319_; uint8_t v_isShared_320_; uint8_t v_isSharedCheck_327_; 
v_id_301_ = lean_ctor_get(v_s_300_, 0);
v_type_302_ = lean_ctor_get(v_s_300_, 1);
v_u_303_ = lean_ctor_get(v_s_300_, 2);
v_op_304_ = lean_ctor_get(v_s_300_, 3);
v_neutral_x3f_305_ = lean_ctor_get(v_s_300_, 4);
v_assocInst_306_ = lean_ctor_get(v_s_300_, 5);
v_idempotentInst_x3f_307_ = lean_ctor_get(v_s_300_, 6);
v_commInst_x3f_308_ = lean_ctor_get(v_s_300_, 7);
v_neutralInst_x3f_309_ = lean_ctor_get(v_s_300_, 8);
v_nextId_310_ = lean_ctor_get(v_s_300_, 9);
v_vars_311_ = lean_ctor_get(v_s_300_, 10);
v_varMap_312_ = lean_ctor_get(v_s_300_, 11);
v_denote_313_ = lean_ctor_get(v_s_300_, 12);
v_denoteEntries_314_ = lean_ctor_get(v_s_300_, 13);
v_queue_315_ = lean_ctor_get(v_s_300_, 14);
v_basis_316_ = lean_ctor_get(v_s_300_, 15);
v_diseqs_317_ = lean_ctor_get(v_s_300_, 16);
v_isSharedCheck_327_ = !lean_is_exclusive(v_s_300_);
if (v_isSharedCheck_327_ == 0)
{
v___x_319_ = v_s_300_;
v_isShared_320_ = v_isSharedCheck_327_;
goto v_resetjp_318_;
}
else
{
lean_inc(v_diseqs_317_);
lean_inc(v_basis_316_);
lean_inc(v_queue_315_);
lean_inc(v_denoteEntries_314_);
lean_inc(v_denote_313_);
lean_inc(v_varMap_312_);
lean_inc(v_vars_311_);
lean_inc(v_nextId_310_);
lean_inc(v_neutralInst_x3f_309_);
lean_inc(v_commInst_x3f_308_);
lean_inc(v_idempotentInst_x3f_307_);
lean_inc(v_assocInst_306_);
lean_inc(v_neutral_x3f_305_);
lean_inc(v_op_304_);
lean_inc(v_u_303_);
lean_inc(v_type_302_);
lean_inc(v_id_301_);
lean_dec(v_s_300_);
v___x_319_ = lean_box(0);
v_isShared_320_ = v_isSharedCheck_327_;
goto v_resetjp_318_;
}
v_resetjp_318_:
{
lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_325_; 
lean_inc_ref(v_a_298_);
lean_inc_ref(v_e_297_);
v___x_321_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1___redArg(v_denote_313_, v_e_297_, v_a_298_);
v___x_322_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_322_, 0, v_e_297_);
lean_ctor_set(v___x_322_, 1, v_a_298_);
v___x_323_ = l_Lean_PersistentArray_push___redArg(v_denoteEntries_314_, v___x_322_);
if (v_isShared_320_ == 0)
{
lean_ctor_set(v___x_319_, 13, v___x_323_);
lean_ctor_set(v___x_319_, 12, v___x_321_);
v___x_325_ = v___x_319_;
goto v_reusejp_324_;
}
else
{
lean_object* v_reuseFailAlloc_326_; 
v_reuseFailAlloc_326_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_326_, 0, v_id_301_);
lean_ctor_set(v_reuseFailAlloc_326_, 1, v_type_302_);
lean_ctor_set(v_reuseFailAlloc_326_, 2, v_u_303_);
lean_ctor_set(v_reuseFailAlloc_326_, 3, v_op_304_);
lean_ctor_set(v_reuseFailAlloc_326_, 4, v_neutral_x3f_305_);
lean_ctor_set(v_reuseFailAlloc_326_, 5, v_assocInst_306_);
lean_ctor_set(v_reuseFailAlloc_326_, 6, v_idempotentInst_x3f_307_);
lean_ctor_set(v_reuseFailAlloc_326_, 7, v_commInst_x3f_308_);
lean_ctor_set(v_reuseFailAlloc_326_, 8, v_neutralInst_x3f_309_);
lean_ctor_set(v_reuseFailAlloc_326_, 9, v_nextId_310_);
lean_ctor_set(v_reuseFailAlloc_326_, 10, v_vars_311_);
lean_ctor_set(v_reuseFailAlloc_326_, 11, v_varMap_312_);
lean_ctor_set(v_reuseFailAlloc_326_, 12, v___x_321_);
lean_ctor_set(v_reuseFailAlloc_326_, 13, v___x_323_);
lean_ctor_set(v_reuseFailAlloc_326_, 14, v_queue_315_);
lean_ctor_set(v_reuseFailAlloc_326_, 15, v_basis_316_);
lean_ctor_set(v_reuseFailAlloc_326_, 16, v_diseqs_317_);
v___x_325_ = v_reuseFailAlloc_326_;
goto v_reusejp_324_;
}
v_reusejp_324_:
{
lean_ctor_set_uint8(v___x_325_, sizeof(void*)*17, v_ac_299_);
return v___x_325_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_internalize___lam__0___boxed(lean_object* v_e_328_, lean_object* v_a_329_, lean_object* v_ac_330_, lean_object* v_s_331_){
_start:
{
uint8_t v_ac_boxed_332_; lean_object* v_res_333_; 
v_ac_boxed_332_ = lean_unbox(v_ac_330_);
v_res_333_ = l_Lean_Meta_Grind_AC_internalize___lam__0(v_e_328_, v_a_329_, v_ac_boxed_332_, v_s_331_);
return v_res_333_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3_spec__5(lean_object* v_msgData_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_){
_start:
{
lean_object* v___x_340_; lean_object* v_env_341_; lean_object* v___x_342_; lean_object* v_toCold_343_; lean_object* v_mctx_344_; lean_object* v_lctx_345_; lean_object* v_options_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; 
v___x_340_ = lean_st_ref_get(v___y_338_);
v_env_341_ = lean_ctor_get(v___x_340_, 0);
lean_inc_ref(v_env_341_);
lean_dec(v___x_340_);
v___x_342_ = lean_st_ref_get(v___y_336_);
v_toCold_343_ = lean_ctor_get(v___y_337_, 0);
v_mctx_344_ = lean_ctor_get(v___x_342_, 0);
lean_inc_ref(v_mctx_344_);
lean_dec(v___x_342_);
v_lctx_345_ = lean_ctor_get(v___y_335_, 2);
v_options_346_ = lean_ctor_get(v_toCold_343_, 2);
lean_inc_ref(v_options_346_);
lean_inc_ref(v_lctx_345_);
v___x_347_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_347_, 0, v_env_341_);
lean_ctor_set(v___x_347_, 1, v_mctx_344_);
lean_ctor_set(v___x_347_, 2, v_lctx_345_);
lean_ctor_set(v___x_347_, 3, v_options_346_);
v___x_348_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_348_, 0, v___x_347_);
lean_ctor_set(v___x_348_, 1, v_msgData_334_);
v___x_349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_349_, 0, v___x_348_);
return v___x_349_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3_spec__5___boxed(lean_object* v_msgData_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_){
_start:
{
lean_object* v_res_356_; 
v_res_356_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3_spec__5(v_msgData_350_, v___y_351_, v___y_352_, v___y_353_, v___y_354_);
lean_dec(v___y_354_);
lean_dec_ref(v___y_353_);
lean_dec(v___y_352_);
lean_dec_ref(v___y_351_);
return v_res_356_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_357_; double v___x_358_; 
v___x_357_ = lean_unsigned_to_nat(0u);
v___x_358_ = lean_float_of_nat(v___x_357_);
return v___x_358_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3___redArg(lean_object* v_cls_362_, lean_object* v_msg_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_){
_start:
{
lean_object* v_ref_369_; lean_object* v___x_370_; lean_object* v_a_371_; lean_object* v___x_373_; uint8_t v_isShared_374_; uint8_t v_isSharedCheck_415_; 
v_ref_369_ = lean_ctor_get(v___y_366_, 2);
v___x_370_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3_spec__5(v_msg_363_, v___y_364_, v___y_365_, v___y_366_, v___y_367_);
v_a_371_ = lean_ctor_get(v___x_370_, 0);
v_isSharedCheck_415_ = !lean_is_exclusive(v___x_370_);
if (v_isSharedCheck_415_ == 0)
{
v___x_373_ = v___x_370_;
v_isShared_374_ = v_isSharedCheck_415_;
goto v_resetjp_372_;
}
else
{
lean_inc(v_a_371_);
lean_dec(v___x_370_);
v___x_373_ = lean_box(0);
v_isShared_374_ = v_isSharedCheck_415_;
goto v_resetjp_372_;
}
v_resetjp_372_:
{
lean_object* v___x_375_; lean_object* v_traceState_376_; lean_object* v_env_377_; lean_object* v_nextMacroScope_378_; lean_object* v_ngen_379_; lean_object* v_auxDeclNGen_380_; lean_object* v_cache_381_; lean_object* v_messages_382_; lean_object* v_infoState_383_; lean_object* v_snapshotTasks_384_; lean_object* v___x_386_; uint8_t v_isShared_387_; uint8_t v_isSharedCheck_414_; 
v___x_375_ = lean_st_ref_take(v___y_367_);
v_traceState_376_ = lean_ctor_get(v___x_375_, 4);
v_env_377_ = lean_ctor_get(v___x_375_, 0);
v_nextMacroScope_378_ = lean_ctor_get(v___x_375_, 1);
v_ngen_379_ = lean_ctor_get(v___x_375_, 2);
v_auxDeclNGen_380_ = lean_ctor_get(v___x_375_, 3);
v_cache_381_ = lean_ctor_get(v___x_375_, 5);
v_messages_382_ = lean_ctor_get(v___x_375_, 6);
v_infoState_383_ = lean_ctor_get(v___x_375_, 7);
v_snapshotTasks_384_ = lean_ctor_get(v___x_375_, 8);
v_isSharedCheck_414_ = !lean_is_exclusive(v___x_375_);
if (v_isSharedCheck_414_ == 0)
{
v___x_386_ = v___x_375_;
v_isShared_387_ = v_isSharedCheck_414_;
goto v_resetjp_385_;
}
else
{
lean_inc(v_snapshotTasks_384_);
lean_inc(v_infoState_383_);
lean_inc(v_messages_382_);
lean_inc(v_cache_381_);
lean_inc(v_traceState_376_);
lean_inc(v_auxDeclNGen_380_);
lean_inc(v_ngen_379_);
lean_inc(v_nextMacroScope_378_);
lean_inc(v_env_377_);
lean_dec(v___x_375_);
v___x_386_ = lean_box(0);
v_isShared_387_ = v_isSharedCheck_414_;
goto v_resetjp_385_;
}
v_resetjp_385_:
{
uint64_t v_tid_388_; lean_object* v_traces_389_; lean_object* v___x_391_; uint8_t v_isShared_392_; uint8_t v_isSharedCheck_413_; 
v_tid_388_ = lean_ctor_get_uint64(v_traceState_376_, sizeof(void*)*1);
v_traces_389_ = lean_ctor_get(v_traceState_376_, 0);
v_isSharedCheck_413_ = !lean_is_exclusive(v_traceState_376_);
if (v_isSharedCheck_413_ == 0)
{
v___x_391_ = v_traceState_376_;
v_isShared_392_ = v_isSharedCheck_413_;
goto v_resetjp_390_;
}
else
{
lean_inc(v_traces_389_);
lean_dec(v_traceState_376_);
v___x_391_ = lean_box(0);
v_isShared_392_ = v_isSharedCheck_413_;
goto v_resetjp_390_;
}
v_resetjp_390_:
{
lean_object* v___x_393_; double v___x_394_; uint8_t v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_403_; 
v___x_393_ = lean_box(0);
v___x_394_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3___redArg___closed__0);
v___x_395_ = 0;
v___x_396_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3___redArg___closed__1));
v___x_397_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_397_, 0, v_cls_362_);
lean_ctor_set(v___x_397_, 1, v___x_393_);
lean_ctor_set(v___x_397_, 2, v___x_396_);
lean_ctor_set_float(v___x_397_, sizeof(void*)*3, v___x_394_);
lean_ctor_set_float(v___x_397_, sizeof(void*)*3 + 8, v___x_394_);
lean_ctor_set_uint8(v___x_397_, sizeof(void*)*3 + 16, v___x_395_);
v___x_398_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3___redArg___closed__2));
v___x_399_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_399_, 0, v___x_397_);
lean_ctor_set(v___x_399_, 1, v_a_371_);
lean_ctor_set(v___x_399_, 2, v___x_398_);
lean_inc(v_ref_369_);
v___x_400_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_400_, 0, v_ref_369_);
lean_ctor_set(v___x_400_, 1, v___x_399_);
v___x_401_ = l_Lean_PersistentArray_push___redArg(v_traces_389_, v___x_400_);
if (v_isShared_392_ == 0)
{
lean_ctor_set(v___x_391_, 0, v___x_401_);
v___x_403_ = v___x_391_;
goto v_reusejp_402_;
}
else
{
lean_object* v_reuseFailAlloc_412_; 
v_reuseFailAlloc_412_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_412_, 0, v___x_401_);
lean_ctor_set_uint64(v_reuseFailAlloc_412_, sizeof(void*)*1, v_tid_388_);
v___x_403_ = v_reuseFailAlloc_412_;
goto v_reusejp_402_;
}
v_reusejp_402_:
{
lean_object* v___x_405_; 
if (v_isShared_387_ == 0)
{
lean_ctor_set(v___x_386_, 4, v___x_403_);
v___x_405_ = v___x_386_;
goto v_reusejp_404_;
}
else
{
lean_object* v_reuseFailAlloc_411_; 
v_reuseFailAlloc_411_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_411_, 0, v_env_377_);
lean_ctor_set(v_reuseFailAlloc_411_, 1, v_nextMacroScope_378_);
lean_ctor_set(v_reuseFailAlloc_411_, 2, v_ngen_379_);
lean_ctor_set(v_reuseFailAlloc_411_, 3, v_auxDeclNGen_380_);
lean_ctor_set(v_reuseFailAlloc_411_, 4, v___x_403_);
lean_ctor_set(v_reuseFailAlloc_411_, 5, v_cache_381_);
lean_ctor_set(v_reuseFailAlloc_411_, 6, v_messages_382_);
lean_ctor_set(v_reuseFailAlloc_411_, 7, v_infoState_383_);
lean_ctor_set(v_reuseFailAlloc_411_, 8, v_snapshotTasks_384_);
v___x_405_ = v_reuseFailAlloc_411_;
goto v_reusejp_404_;
}
v_reusejp_404_:
{
lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_409_; 
v___x_406_ = lean_st_ref_put(v___y_367_, v___x_405_);
v___x_407_ = lean_box(0);
if (v_isShared_374_ == 0)
{
lean_ctor_set(v___x_373_, 0, v___x_407_);
v___x_409_ = v___x_373_;
goto v_reusejp_408_;
}
else
{
lean_object* v_reuseFailAlloc_410_; 
v_reuseFailAlloc_410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_410_, 0, v___x_407_);
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
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3___redArg___boxed(lean_object* v_cls_416_, lean_object* v_msg_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_){
_start:
{
lean_object* v_res_423_; 
v_res_423_ = l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3___redArg(v_cls_416_, v_msg_417_, v___y_418_, v___y_419_, v___y_420_, v___y_421_);
lean_dec(v___y_421_);
lean_dec_ref(v___y_420_);
lean_dec(v___y_419_);
lean_dec_ref(v___y_418_);
return v_res_423_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_424_, lean_object* v_i_425_, lean_object* v_k_426_){
_start:
{
lean_object* v___x_427_; uint8_t v___x_428_; 
v___x_427_ = lean_array_get_size(v_keys_424_);
v___x_428_ = lean_nat_dec_lt(v_i_425_, v___x_427_);
if (v___x_428_ == 0)
{
lean_dec(v_i_425_);
return v___x_428_;
}
else
{
lean_object* v_k_x27_429_; size_t v___x_430_; size_t v___x_431_; uint8_t v___x_432_; 
v_k_x27_429_ = lean_array_fget_borrowed(v_keys_424_, v_i_425_);
v___x_430_ = lean_ptr_addr(v_k_426_);
v___x_431_ = lean_ptr_addr(v_k_x27_429_);
v___x_432_ = lean_usize_dec_eq(v___x_430_, v___x_431_);
if (v___x_432_ == 0)
{
lean_object* v___x_433_; lean_object* v___x_434_; 
v___x_433_ = lean_unsigned_to_nat(1u);
v___x_434_ = lean_nat_add(v_i_425_, v___x_433_);
lean_dec(v_i_425_);
v_i_425_ = v___x_434_;
goto _start;
}
else
{
lean_dec(v_i_425_);
return v___x_428_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_436_, lean_object* v_i_437_, lean_object* v_k_438_){
_start:
{
uint8_t v_res_439_; lean_object* v_r_440_; 
v_res_439_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0_spec__1___redArg(v_keys_436_, v_i_437_, v_k_438_);
lean_dec_ref(v_k_438_);
lean_dec_ref(v_keys_436_);
v_r_440_ = lean_box(v_res_439_);
return v_r_440_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0___redArg(lean_object* v_x_441_, size_t v_x_442_, lean_object* v_x_443_){
_start:
{
if (lean_obj_tag(v_x_441_) == 0)
{
lean_object* v_es_444_; lean_object* v___x_445_; size_t v___x_446_; size_t v___x_447_; lean_object* v_j_448_; lean_object* v___x_449_; 
v_es_444_ = lean_ctor_get(v_x_441_, 0);
v___x_445_ = lean_box(2);
v___x_446_ = ((size_t)31ULL);
v___x_447_ = lean_usize_land(v_x_442_, v___x_446_);
v_j_448_ = lean_usize_to_nat(v___x_447_);
v___x_449_ = lean_array_get_borrowed(v___x_445_, v_es_444_, v_j_448_);
lean_dec(v_j_448_);
switch(lean_obj_tag(v___x_449_))
{
case 0:
{
lean_object* v_key_450_; size_t v___x_451_; size_t v___x_452_; uint8_t v___x_453_; 
v_key_450_ = lean_ctor_get(v___x_449_, 0);
v___x_451_ = lean_ptr_addr(v_x_443_);
v___x_452_ = lean_ptr_addr(v_key_450_);
v___x_453_ = lean_usize_dec_eq(v___x_451_, v___x_452_);
return v___x_453_;
}
case 1:
{
lean_object* v_node_454_; size_t v___x_455_; size_t v___x_456_; 
v_node_454_ = lean_ctor_get(v___x_449_, 0);
v___x_455_ = ((size_t)5ULL);
v___x_456_ = lean_usize_shift_right(v_x_442_, v___x_455_);
v_x_441_ = v_node_454_;
v_x_442_ = v___x_456_;
goto _start;
}
default: 
{
uint8_t v___x_458_; 
v___x_458_ = 0;
return v___x_458_;
}
}
}
else
{
lean_object* v_ks_459_; lean_object* v___x_460_; uint8_t v___x_461_; 
v_ks_459_ = lean_ctor_get(v_x_441_, 0);
v___x_460_ = lean_unsigned_to_nat(0u);
v___x_461_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0_spec__1___redArg(v_ks_459_, v___x_460_, v_x_443_);
return v___x_461_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0___redArg___boxed(lean_object* v_x_462_, lean_object* v_x_463_, lean_object* v_x_464_){
_start:
{
size_t v_x_38591__boxed_465_; uint8_t v_res_466_; lean_object* v_r_467_; 
v_x_38591__boxed_465_ = lean_unbox_usize(v_x_463_);
lean_dec(v_x_463_);
v_res_466_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0___redArg(v_x_462_, v_x_38591__boxed_465_, v_x_464_);
lean_dec_ref(v_x_464_);
lean_dec_ref(v_x_462_);
v_r_467_ = lean_box(v_res_466_);
return v_r_467_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0___redArg(lean_object* v_x_468_, lean_object* v_x_469_){
_start:
{
size_t v___x_470_; size_t v___x_471_; size_t v___x_472_; uint64_t v___x_473_; size_t v___x_474_; uint8_t v___x_475_; 
v___x_470_ = lean_ptr_addr(v_x_469_);
v___x_471_ = ((size_t)3ULL);
v___x_472_ = lean_usize_shift_right(v___x_470_, v___x_471_);
v___x_473_ = lean_usize_to_uint64(v___x_472_);
v___x_474_ = lean_uint64_to_usize(v___x_473_);
v___x_475_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0___redArg(v_x_468_, v___x_474_, v_x_469_);
return v___x_475_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0___redArg___boxed(lean_object* v_x_476_, lean_object* v_x_477_){
_start:
{
uint8_t v_res_478_; lean_object* v_r_479_; 
v_res_478_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0___redArg(v_x_476_, v_x_477_);
lean_dec_ref(v_x_477_);
lean_dec_ref(v_x_476_);
v_r_479_ = lean_box(v_res_478_);
return v_r_479_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Expr_denoteExpr___at___00Lean_Meta_Grind_AC_internalize_spec__2(lean_object* v_e_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_){
_start:
{
if (lean_obj_tag(v_e_480_) == 0)
{
lean_object* v_x_493_; lean_object* v___x_494_; 
v_x_493_ = lean_ctor_get(v_e_480_, 0);
v___x_494_ = l_Lean_Meta_Grind_AC_ACM_getStruct(v___y_481_, v___y_482_, v___y_483_, v___y_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_, v___y_489_, v___y_490_, v___y_491_);
if (lean_obj_tag(v___x_494_) == 0)
{
lean_object* v_a_495_; lean_object* v___x_497_; uint8_t v_isShared_498_; uint8_t v_isSharedCheck_511_; 
v_a_495_ = lean_ctor_get(v___x_494_, 0);
v_isSharedCheck_511_ = !lean_is_exclusive(v___x_494_);
if (v_isSharedCheck_511_ == 0)
{
v___x_497_ = v___x_494_;
v_isShared_498_ = v_isSharedCheck_511_;
goto v_resetjp_496_;
}
else
{
lean_inc(v_a_495_);
lean_dec(v___x_494_);
v___x_497_ = lean_box(0);
v_isShared_498_ = v_isSharedCheck_511_;
goto v_resetjp_496_;
}
v_resetjp_496_:
{
lean_object* v_vars_499_; lean_object* v_size_500_; lean_object* v___x_501_; uint8_t v___x_502_; 
v_vars_499_ = lean_ctor_get(v_a_495_, 10);
lean_inc_ref(v_vars_499_);
lean_dec(v_a_495_);
v_size_500_ = lean_ctor_get(v_vars_499_, 2);
v___x_501_ = l_Lean_instInhabitedExpr;
v___x_502_ = lean_nat_dec_lt(v_x_493_, v_size_500_);
if (v___x_502_ == 0)
{
lean_object* v___x_503_; lean_object* v___x_505_; 
lean_dec_ref(v_vars_499_);
v___x_503_ = l_outOfBounds___redArg(v___x_501_);
if (v_isShared_498_ == 0)
{
lean_ctor_set(v___x_497_, 0, v___x_503_);
v___x_505_ = v___x_497_;
goto v_reusejp_504_;
}
else
{
lean_object* v_reuseFailAlloc_506_; 
v_reuseFailAlloc_506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_506_, 0, v___x_503_);
v___x_505_ = v_reuseFailAlloc_506_;
goto v_reusejp_504_;
}
v_reusejp_504_:
{
return v___x_505_;
}
}
else
{
lean_object* v___x_507_; lean_object* v___x_509_; 
v___x_507_ = l_Lean_PersistentArray_get_x21___redArg(v___x_501_, v_vars_499_, v_x_493_);
lean_dec_ref(v_vars_499_);
if (v_isShared_498_ == 0)
{
lean_ctor_set(v___x_497_, 0, v___x_507_);
v___x_509_ = v___x_497_;
goto v_reusejp_508_;
}
else
{
lean_object* v_reuseFailAlloc_510_; 
v_reuseFailAlloc_510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_510_, 0, v___x_507_);
v___x_509_ = v_reuseFailAlloc_510_;
goto v_reusejp_508_;
}
v_reusejp_508_:
{
return v___x_509_;
}
}
}
}
else
{
lean_object* v_a_512_; lean_object* v___x_514_; uint8_t v_isShared_515_; uint8_t v_isSharedCheck_519_; 
v_a_512_ = lean_ctor_get(v___x_494_, 0);
v_isSharedCheck_519_ = !lean_is_exclusive(v___x_494_);
if (v_isSharedCheck_519_ == 0)
{
v___x_514_ = v___x_494_;
v_isShared_515_ = v_isSharedCheck_519_;
goto v_resetjp_513_;
}
else
{
lean_inc(v_a_512_);
lean_dec(v___x_494_);
v___x_514_ = lean_box(0);
v_isShared_515_ = v_isSharedCheck_519_;
goto v_resetjp_513_;
}
v_resetjp_513_:
{
lean_object* v___x_517_; 
if (v_isShared_515_ == 0)
{
v___x_517_ = v___x_514_;
goto v_reusejp_516_;
}
else
{
lean_object* v_reuseFailAlloc_518_; 
v_reuseFailAlloc_518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_518_, 0, v_a_512_);
v___x_517_ = v_reuseFailAlloc_518_;
goto v_reusejp_516_;
}
v_reusejp_516_:
{
return v___x_517_;
}
}
}
}
else
{
lean_object* v_lhs_520_; lean_object* v_rhs_521_; lean_object* v___x_522_; 
v_lhs_520_ = lean_ctor_get(v_e_480_, 0);
v_rhs_521_ = lean_ctor_get(v_e_480_, 1);
v___x_522_ = l_Lean_Meta_Grind_AC_ACM_getStruct(v___y_481_, v___y_482_, v___y_483_, v___y_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_, v___y_489_, v___y_490_, v___y_491_);
if (lean_obj_tag(v___x_522_) == 0)
{
lean_object* v_a_523_; lean_object* v___x_524_; 
v_a_523_ = lean_ctor_get(v___x_522_, 0);
lean_inc(v_a_523_);
lean_dec_ref_known(v___x_522_, 1);
v___x_524_ = l_Lean_Grind_AC_Expr_denoteExpr___at___00Lean_Meta_Grind_AC_internalize_spec__2(v_lhs_520_, v___y_481_, v___y_482_, v___y_483_, v___y_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_, v___y_489_, v___y_490_, v___y_491_);
if (lean_obj_tag(v___x_524_) == 0)
{
lean_object* v_a_525_; lean_object* v___x_526_; 
v_a_525_ = lean_ctor_get(v___x_524_, 0);
lean_inc(v_a_525_);
lean_dec_ref_known(v___x_524_, 1);
v___x_526_ = l_Lean_Grind_AC_Expr_denoteExpr___at___00Lean_Meta_Grind_AC_internalize_spec__2(v_rhs_521_, v___y_481_, v___y_482_, v___y_483_, v___y_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_, v___y_489_, v___y_490_, v___y_491_);
if (lean_obj_tag(v___x_526_) == 0)
{
lean_object* v_a_527_; lean_object* v___x_529_; uint8_t v_isShared_530_; uint8_t v_isSharedCheck_536_; 
v_a_527_ = lean_ctor_get(v___x_526_, 0);
v_isSharedCheck_536_ = !lean_is_exclusive(v___x_526_);
if (v_isSharedCheck_536_ == 0)
{
v___x_529_ = v___x_526_;
v_isShared_530_ = v_isSharedCheck_536_;
goto v_resetjp_528_;
}
else
{
lean_inc(v_a_527_);
lean_dec(v___x_526_);
v___x_529_ = lean_box(0);
v_isShared_530_ = v_isSharedCheck_536_;
goto v_resetjp_528_;
}
v_resetjp_528_:
{
lean_object* v_op_531_; lean_object* v___x_532_; lean_object* v___x_534_; 
v_op_531_ = lean_ctor_get(v_a_523_, 3);
lean_inc_ref(v_op_531_);
lean_dec(v_a_523_);
v___x_532_ = l_Lean_mkAppB(v_op_531_, v_a_525_, v_a_527_);
if (v_isShared_530_ == 0)
{
lean_ctor_set(v___x_529_, 0, v___x_532_);
v___x_534_ = v___x_529_;
goto v_reusejp_533_;
}
else
{
lean_object* v_reuseFailAlloc_535_; 
v_reuseFailAlloc_535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_535_, 0, v___x_532_);
v___x_534_ = v_reuseFailAlloc_535_;
goto v_reusejp_533_;
}
v_reusejp_533_:
{
return v___x_534_;
}
}
}
else
{
lean_dec(v_a_525_);
lean_dec(v_a_523_);
return v___x_526_;
}
}
else
{
lean_dec(v_a_523_);
return v___x_524_;
}
}
else
{
lean_object* v_a_537_; lean_object* v___x_539_; uint8_t v_isShared_540_; uint8_t v_isSharedCheck_544_; 
v_a_537_ = lean_ctor_get(v___x_522_, 0);
v_isSharedCheck_544_ = !lean_is_exclusive(v___x_522_);
if (v_isSharedCheck_544_ == 0)
{
v___x_539_ = v___x_522_;
v_isShared_540_ = v_isSharedCheck_544_;
goto v_resetjp_538_;
}
else
{
lean_inc(v_a_537_);
lean_dec(v___x_522_);
v___x_539_ = lean_box(0);
v_isShared_540_ = v_isSharedCheck_544_;
goto v_resetjp_538_;
}
v_resetjp_538_:
{
lean_object* v___x_542_; 
if (v_isShared_540_ == 0)
{
v___x_542_ = v___x_539_;
goto v_reusejp_541_;
}
else
{
lean_object* v_reuseFailAlloc_543_; 
v_reuseFailAlloc_543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_543_, 0, v_a_537_);
v___x_542_ = v_reuseFailAlloc_543_;
goto v_reusejp_541_;
}
v_reusejp_541_:
{
return v___x_542_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Expr_denoteExpr___at___00Lean_Meta_Grind_AC_internalize_spec__2___boxed(lean_object* v_e_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_){
_start:
{
lean_object* v_res_558_; 
v_res_558_ = l_Lean_Grind_AC_Expr_denoteExpr___at___00Lean_Meta_Grind_AC_internalize_spec__2(v_e_545_, v___y_546_, v___y_547_, v___y_548_, v___y_549_, v___y_550_, v___y_551_, v___y_552_, v___y_553_, v___y_554_, v___y_555_, v___y_556_);
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
lean_dec(v___y_546_);
lean_dec_ref(v_e_545_);
return v_res_558_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_AC_internalize___closed__6(void){
_start:
{
lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; 
v___x_569_ = ((lean_object*)(l_Lean_Meta_Grind_AC_internalize___closed__3));
v___x_570_ = ((lean_object*)(l_Lean_Meta_Grind_AC_internalize___closed__5));
v___x_571_ = l_Lean_Name_append(v___x_570_, v___x_569_);
return v___x_571_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_AC_internalize___closed__8(void){
_start:
{
lean_object* v___x_573_; lean_object* v___x_574_; 
v___x_573_ = ((lean_object*)(l_Lean_Meta_Grind_AC_internalize___closed__7));
v___x_574_ = l_Lean_stringToMessageData(v___x_573_);
return v___x_574_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_AC_internalize___closed__10(void){
_start:
{
lean_object* v___x_576_; lean_object* v___x_577_; 
v___x_576_ = ((lean_object*)(l_Lean_Meta_Grind_AC_internalize___closed__9));
v___x_577_ = l_Lean_stringToMessageData(v___x_576_);
return v___x_577_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_internalize(lean_object* v_e_578_, lean_object* v_parent_x3f_579_, lean_object* v_a_580_, lean_object* v_a_581_, lean_object* v_a_582_, lean_object* v_a_583_, lean_object* v_a_584_, lean_object* v_a_585_, lean_object* v_a_586_, lean_object* v_a_587_, lean_object* v_a_588_, lean_object* v_a_589_){
_start:
{
lean_object* v___y_592_; lean_object* v___y_593_; lean_object* v___y_594_; lean_object* v___y_595_; lean_object* v___y_596_; lean_object* v___y_597_; lean_object* v___y_598_; lean_object* v___y_599_; lean_object* v___y_600_; lean_object* v___y_601_; lean_object* v___y_602_; lean_object* v___x_606_; 
v___x_606_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_582_);
if (lean_obj_tag(v___x_606_) == 0)
{
lean_object* v_a_607_; lean_object* v___x_609_; uint8_t v_isShared_610_; uint8_t v_isSharedCheck_722_; 
v_a_607_ = lean_ctor_get(v___x_606_, 0);
v_isSharedCheck_722_ = !lean_is_exclusive(v___x_606_);
if (v_isSharedCheck_722_ == 0)
{
v___x_609_ = v___x_606_;
v_isShared_610_ = v_isSharedCheck_722_;
goto v_resetjp_608_;
}
else
{
lean_inc(v_a_607_);
lean_dec(v___x_606_);
v___x_609_ = lean_box(0);
v_isShared_610_ = v_isSharedCheck_722_;
goto v_resetjp_608_;
}
v_resetjp_608_:
{
uint8_t v_ac_611_; uint8_t v___y_613_; 
v_ac_611_ = lean_ctor_get_uint8(v_a_607_, sizeof(void*)*14 + 25);
lean_dec(v_a_607_);
if (v_ac_611_ == 0)
{
lean_object* v___x_717_; lean_object* v___x_718_; 
lean_del_object(v___x_609_);
lean_dec(v_parent_x3f_579_);
lean_dec_ref(v_e_578_);
v___x_717_ = lean_box(0);
v___x_718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_718_, 0, v___x_717_);
return v___x_718_;
}
else
{
uint8_t v___x_719_; 
v___x_719_ = l_Lean_Expr_isApp(v_e_578_);
if (v___x_719_ == 0)
{
v___y_613_ = v___x_719_;
goto v___jp_612_;
}
else
{
lean_object* v___x_720_; uint8_t v___x_721_; 
v___x_720_ = l_Lean_Expr_appFn_x21(v_e_578_);
v___x_721_ = l_Lean_Expr_isApp(v___x_720_);
lean_dec_ref(v___x_720_);
v___y_613_ = v___x_721_;
goto v___jp_612_;
}
}
v___jp_612_:
{
if (v___y_613_ == 0)
{
lean_object* v___x_614_; lean_object* v___x_616_; 
lean_dec(v_parent_x3f_579_);
lean_dec_ref(v_e_578_);
v___x_614_ = lean_box(0);
if (v_isShared_610_ == 0)
{
lean_ctor_set(v___x_609_, 0, v___x_614_);
v___x_616_ = v___x_609_;
goto v_reusejp_615_;
}
else
{
lean_object* v_reuseFailAlloc_617_; 
v_reuseFailAlloc_617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_617_, 0, v___x_614_);
v___x_616_ = v_reuseFailAlloc_617_;
goto v_reusejp_615_;
}
v_reusejp_615_:
{
return v___x_616_;
}
}
else
{
lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; 
lean_del_object(v___x_609_);
v___x_618_ = l_Lean_Expr_appFn_x21(v_e_578_);
v___x_619_ = l_Lean_Expr_appFn_x21(v___x_618_);
lean_dec_ref(v___x_618_);
lean_inc_ref(v___x_619_);
v___x_620_ = l_Lean_Meta_Grind_AC_getOpId_x3f(v___x_619_, v_a_580_, v_a_581_, v_a_582_, v_a_583_, v_a_584_, v_a_585_, v_a_586_, v_a_587_, v_a_588_, v_a_589_);
if (lean_obj_tag(v___x_620_) == 0)
{
lean_object* v_a_621_; lean_object* v___x_623_; uint8_t v_isShared_624_; uint8_t v_isSharedCheck_708_; 
v_a_621_ = lean_ctor_get(v___x_620_, 0);
v_isSharedCheck_708_ = !lean_is_exclusive(v___x_620_);
if (v_isSharedCheck_708_ == 0)
{
v___x_623_ = v___x_620_;
v_isShared_624_ = v_isSharedCheck_708_;
goto v_resetjp_622_;
}
else
{
lean_inc(v_a_621_);
lean_dec(v___x_620_);
v___x_623_ = lean_box(0);
v_isShared_624_ = v_isSharedCheck_708_;
goto v_resetjp_622_;
}
v_resetjp_622_:
{
if (lean_obj_tag(v_a_621_) == 1)
{
lean_object* v_val_625_; lean_object* v___x_626_; lean_object* v_a_627_; lean_object* v___x_629_; uint8_t v_isShared_630_; uint8_t v_isSharedCheck_703_; 
lean_del_object(v___x_623_);
v_val_625_ = lean_ctor_get(v_a_621_, 0);
lean_inc(v_val_625_);
lean_dec_ref_known(v_a_621_, 1);
v___x_626_ = l___private_Lean_Meta_Tactic_Grind_AC_Internalize_0__Lean_Meta_Grind_AC_isParentSameOpApp___redArg(v_parent_x3f_579_, v___x_619_);
lean_dec_ref(v___x_619_);
v_a_627_ = lean_ctor_get(v___x_626_, 0);
v_isSharedCheck_703_ = !lean_is_exclusive(v___x_626_);
if (v_isSharedCheck_703_ == 0)
{
v___x_629_ = v___x_626_;
v_isShared_630_ = v_isSharedCheck_703_;
goto v_resetjp_628_;
}
else
{
lean_inc(v_a_627_);
lean_dec(v___x_626_);
v___x_629_ = lean_box(0);
v_isShared_630_ = v_isSharedCheck_703_;
goto v_resetjp_628_;
}
v_resetjp_628_:
{
uint8_t v___x_631_; 
v___x_631_ = lean_unbox(v_a_627_);
lean_dec(v_a_627_);
if (v___x_631_ == 0)
{
lean_object* v___x_632_; 
lean_del_object(v___x_629_);
v___x_632_ = l_Lean_Meta_Grind_AC_ACM_getStruct(v_val_625_, v_a_580_, v_a_581_, v_a_582_, v_a_583_, v_a_584_, v_a_585_, v_a_586_, v_a_587_, v_a_588_, v_a_589_);
if (lean_obj_tag(v___x_632_) == 0)
{
lean_object* v_a_633_; lean_object* v___x_635_; uint8_t v_isShared_636_; uint8_t v_isSharedCheck_690_; 
v_a_633_ = lean_ctor_get(v___x_632_, 0);
v_isSharedCheck_690_ = !lean_is_exclusive(v___x_632_);
if (v_isSharedCheck_690_ == 0)
{
v___x_635_ = v___x_632_;
v_isShared_636_ = v_isSharedCheck_690_;
goto v_resetjp_634_;
}
else
{
lean_inc(v_a_633_);
lean_dec(v___x_632_);
v___x_635_ = lean_box(0);
v_isShared_636_ = v_isSharedCheck_690_;
goto v_resetjp_634_;
}
v_resetjp_634_:
{
lean_object* v_denote_637_; uint8_t v___x_638_; 
v_denote_637_ = lean_ctor_get(v_a_633_, 12);
lean_inc_ref(v_denote_637_);
lean_dec(v_a_633_);
v___x_638_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0___redArg(v_denote_637_, v_e_578_);
lean_dec_ref(v_denote_637_);
if (v___x_638_ == 0)
{
lean_object* v___x_639_; 
lean_del_object(v___x_635_);
lean_inc_ref(v_e_578_);
v___x_639_ = l_Lean_Meta_Grind_AC_reify(v_e_578_, v_val_625_, v_a_580_, v_a_581_, v_a_582_, v_a_583_, v_a_584_, v_a_585_, v_a_586_, v_a_587_, v_a_588_, v_a_589_);
if (lean_obj_tag(v___x_639_) == 0)
{
lean_object* v_a_640_; lean_object* v___x_641_; lean_object* v___f_642_; lean_object* v___x_643_; 
v_a_640_ = lean_ctor_get(v___x_639_, 0);
lean_inc_n(v_a_640_, 2);
lean_dec_ref_known(v___x_639_, 1);
v___x_641_ = lean_box(v_ac_611_);
lean_inc_ref(v_e_578_);
v___f_642_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_AC_internalize___lam__0___boxed), 4, 3);
lean_closure_set(v___f_642_, 0, v_e_578_);
lean_closure_set(v___f_642_, 1, v_a_640_);
lean_closure_set(v___f_642_, 2, v___x_641_);
v___x_643_ = l_Lean_Meta_Grind_AC_modifyStruct___redArg(v___f_642_, v_val_625_, v_a_580_);
if (lean_obj_tag(v___x_643_) == 0)
{
lean_object* v___x_645_; uint8_t v_isShared_646_; uint8_t v_isSharedCheck_676_; 
v_isSharedCheck_676_ = !lean_is_exclusive(v___x_643_);
if (v_isSharedCheck_676_ == 0)
{
lean_object* v_unused_677_; 
v_unused_677_ = lean_ctor_get(v___x_643_, 0);
lean_dec(v_unused_677_);
v___x_645_ = v___x_643_;
v_isShared_646_ = v_isSharedCheck_676_;
goto v_resetjp_644_;
}
else
{
lean_dec(v___x_643_);
v___x_645_ = lean_box(0);
v_isShared_646_ = v_isSharedCheck_676_;
goto v_resetjp_644_;
}
v_resetjp_644_:
{
lean_object* v_toCold_647_; lean_object* v_options_648_; uint8_t v_hasTrace_649_; 
v_toCold_647_ = lean_ctor_get(v_a_588_, 0);
v_options_648_ = lean_ctor_get(v_toCold_647_, 2);
v_hasTrace_649_ = lean_ctor_get_uint8(v_options_648_, sizeof(void*)*1);
if (v_hasTrace_649_ == 0)
{
lean_del_object(v___x_645_);
lean_dec(v_a_640_);
v___y_592_ = v_val_625_;
v___y_593_ = v_a_580_;
v___y_594_ = v_a_581_;
v___y_595_ = v_a_582_;
v___y_596_ = v_a_583_;
v___y_597_ = v_a_584_;
v___y_598_ = v_a_585_;
v___y_599_ = v_a_586_;
v___y_600_ = v_a_587_;
v___y_601_ = v_a_588_;
v___y_602_ = v_a_589_;
goto v___jp_591_;
}
else
{
lean_object* v_inheritedTraceOptions_650_; lean_object* v___x_651_; lean_object* v___x_652_; uint8_t v___x_653_; 
v_inheritedTraceOptions_650_ = lean_ctor_get(v_toCold_647_, 11);
v___x_651_ = ((lean_object*)(l_Lean_Meta_Grind_AC_internalize___closed__3));
v___x_652_ = lean_obj_once(&l_Lean_Meta_Grind_AC_internalize___closed__6, &l_Lean_Meta_Grind_AC_internalize___closed__6_once, _init_l_Lean_Meta_Grind_AC_internalize___closed__6);
v___x_653_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_650_, v_options_648_, v___x_652_);
if (v___x_653_ == 0)
{
lean_del_object(v___x_645_);
lean_dec(v_a_640_);
v___y_592_ = v_val_625_;
v___y_593_ = v_a_580_;
v___y_594_ = v_a_581_;
v___y_595_ = v_a_582_;
v___y_596_ = v_a_583_;
v___y_597_ = v_a_584_;
v___y_598_ = v_a_585_;
v___y_599_ = v_a_586_;
v___y_600_ = v_a_587_;
v___y_601_ = v_a_588_;
v___y_602_ = v_a_589_;
goto v___jp_591_;
}
else
{
lean_object* v___x_654_; 
v___x_654_ = l_Lean_Grind_AC_Expr_denoteExpr___at___00Lean_Meta_Grind_AC_internalize_spec__2(v_a_640_, v_val_625_, v_a_580_, v_a_581_, v_a_582_, v_a_583_, v_a_584_, v_a_585_, v_a_586_, v_a_587_, v_a_588_, v_a_589_);
lean_dec(v_a_640_);
if (lean_obj_tag(v___x_654_) == 0)
{
lean_object* v_a_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_659_; 
v_a_655_ = lean_ctor_get(v___x_654_, 0);
lean_inc(v_a_655_);
lean_dec_ref_known(v___x_654_, 1);
v___x_656_ = lean_obj_once(&l_Lean_Meta_Grind_AC_internalize___closed__8, &l_Lean_Meta_Grind_AC_internalize___closed__8_once, _init_l_Lean_Meta_Grind_AC_internalize___closed__8);
lean_inc(v_val_625_);
v___x_657_ = l_Nat_reprFast(v_val_625_);
if (v_isShared_646_ == 0)
{
lean_ctor_set_tag(v___x_645_, 3);
lean_ctor_set(v___x_645_, 0, v___x_657_);
v___x_659_ = v___x_645_;
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
v___x_666_ = l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3___redArg(v___x_651_, v___x_665_, v_a_586_, v_a_587_, v_a_588_, v_a_589_);
if (lean_obj_tag(v___x_666_) == 0)
{
lean_dec_ref_known(v___x_666_, 1);
v___y_592_ = v_val_625_;
v___y_593_ = v_a_580_;
v___y_594_ = v_a_581_;
v___y_595_ = v_a_582_;
v___y_596_ = v_a_583_;
v___y_597_ = v_a_584_;
v___y_598_ = v_a_585_;
v___y_599_ = v_a_586_;
v___y_600_ = v_a_587_;
v___y_601_ = v_a_588_;
v___y_602_ = v_a_589_;
goto v___jp_591_;
}
else
{
lean_dec(v_val_625_);
lean_dec_ref(v_e_578_);
return v___x_666_;
}
}
}
else
{
lean_object* v_a_668_; lean_object* v___x_670_; uint8_t v_isShared_671_; uint8_t v_isSharedCheck_675_; 
lean_del_object(v___x_645_);
lean_dec(v_val_625_);
lean_dec_ref(v_e_578_);
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
lean_dec(v_a_640_);
lean_dec(v_val_625_);
lean_dec_ref(v_e_578_);
return v___x_643_;
}
}
else
{
lean_object* v_a_678_; lean_object* v___x_680_; uint8_t v_isShared_681_; uint8_t v_isSharedCheck_685_; 
lean_dec(v_val_625_);
lean_dec_ref(v_e_578_);
v_a_678_ = lean_ctor_get(v___x_639_, 0);
v_isSharedCheck_685_ = !lean_is_exclusive(v___x_639_);
if (v_isSharedCheck_685_ == 0)
{
v___x_680_ = v___x_639_;
v_isShared_681_ = v_isSharedCheck_685_;
goto v_resetjp_679_;
}
else
{
lean_inc(v_a_678_);
lean_dec(v___x_639_);
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
lean_dec(v_val_625_);
lean_dec_ref(v_e_578_);
v___x_686_ = lean_box(0);
if (v_isShared_636_ == 0)
{
lean_ctor_set(v___x_635_, 0, v___x_686_);
v___x_688_ = v___x_635_;
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
lean_dec(v_val_625_);
lean_dec_ref(v_e_578_);
v_a_691_ = lean_ctor_get(v___x_632_, 0);
v_isSharedCheck_698_ = !lean_is_exclusive(v___x_632_);
if (v_isSharedCheck_698_ == 0)
{
v___x_693_ = v___x_632_;
v_isShared_694_ = v_isSharedCheck_698_;
goto v_resetjp_692_;
}
else
{
lean_inc(v_a_691_);
lean_dec(v___x_632_);
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
lean_dec(v_val_625_);
lean_dec_ref(v_e_578_);
v___x_699_ = lean_box(0);
if (v_isShared_630_ == 0)
{
lean_ctor_set(v___x_629_, 0, v___x_699_);
v___x_701_ = v___x_629_;
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
lean_dec(v_a_621_);
lean_dec_ref(v___x_619_);
lean_dec(v_parent_x3f_579_);
lean_dec_ref(v_e_578_);
v___x_704_ = lean_box(0);
if (v_isShared_624_ == 0)
{
lean_ctor_set(v___x_623_, 0, v___x_704_);
v___x_706_ = v___x_623_;
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
lean_dec_ref(v___x_619_);
lean_dec(v_parent_x3f_579_);
lean_dec_ref(v_e_578_);
v_a_709_ = lean_ctor_get(v___x_620_, 0);
v_isSharedCheck_716_ = !lean_is_exclusive(v___x_620_);
if (v_isSharedCheck_716_ == 0)
{
v___x_711_ = v___x_620_;
v_isShared_712_ = v_isSharedCheck_716_;
goto v_resetjp_710_;
}
else
{
lean_inc(v_a_709_);
lean_dec(v___x_620_);
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
lean_dec(v_parent_x3f_579_);
lean_dec_ref(v_e_578_);
v_a_723_ = lean_ctor_get(v___x_606_, 0);
v_isSharedCheck_730_ = !lean_is_exclusive(v___x_606_);
if (v_isSharedCheck_730_ == 0)
{
v___x_725_ = v___x_606_;
v_isShared_726_ = v_isSharedCheck_730_;
goto v_resetjp_724_;
}
else
{
lean_inc(v_a_723_);
lean_dec(v___x_606_);
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
v___jp_591_:
{
lean_object* v___x_603_; 
lean_inc_ref(v_e_578_);
v___x_603_ = l_Lean_Meta_Grind_AC_addTermOpId___redArg(v_e_578_, v___y_592_, v___y_593_);
lean_dec(v___y_592_);
if (lean_obj_tag(v___x_603_) == 0)
{
lean_object* v___x_604_; lean_object* v___x_605_; 
lean_dec_ref_known(v___x_603_, 1);
v___x_604_ = l_Lean_Meta_Grind_AC_acExt;
v___x_605_ = l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(v___x_604_, v_e_578_, v___y_593_, v___y_594_, v___y_595_, v___y_596_, v___y_597_, v___y_598_, v___y_599_, v___y_600_, v___y_601_, v___y_602_);
return v___x_605_;
}
else
{
lean_dec_ref(v_e_578_);
return v___x_603_;
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
size_t v_x_39178__boxed_798_; uint8_t v_res_799_; lean_object* v_r_800_; 
v_x_39178__boxed_798_ = lean_unbox_usize(v_x_796_);
lean_dec(v_x_796_);
v_res_799_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0(v_00_u03b2_794_, v_x_795_, v_x_39178__boxed_798_, v_x_797_);
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
size_t v_x_39189__boxed_814_; size_t v_x_39190__boxed_815_; lean_object* v_res_816_; 
v_x_39189__boxed_814_ = lean_unbox_usize(v_x_810_);
lean_dec(v_x_810_);
v_x_39190__boxed_815_ = lean_unbox_usize(v_x_811_);
lean_dec(v_x_811_);
v_res_816_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2(v_00_u03b2_808_, v_x_809_, v_x_39189__boxed_814_, v_x_39190__boxed_815_, v_x_812_, v_x_813_);
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
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_AC_Internalize(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
