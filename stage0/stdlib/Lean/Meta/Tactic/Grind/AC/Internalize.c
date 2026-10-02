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
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_Meta_Grind_AC_ACM_getStruct(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
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
v___x_175_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
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
size_t v_x_38386__boxed_284_; size_t v_x_38387__boxed_285_; lean_object* v_res_286_; 
v_x_38386__boxed_284_ = lean_unbox_usize(v_x_280_);
lean_dec(v_x_280_);
v_x_38387__boxed_285_ = lean_unbox_usize(v_x_281_);
lean_dec(v_x_281_);
v_res_286_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___redArg(v_x_279_, v_x_38386__boxed_284_, v_x_38387__boxed_285_, v_x_282_, v_x_283_);
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
lean_object* v_ref_369_; lean_object* v___x_370_; lean_object* v_a_371_; lean_object* v___x_373_; uint8_t v_isShared_374_; uint8_t v_isSharedCheck_416_; 
v_ref_369_ = lean_ctor_get(v___y_366_, 2);
v___x_370_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3_spec__5(v_msg_363_, v___y_364_, v___y_365_, v___y_366_, v___y_367_);
v_a_371_ = lean_ctor_get(v___x_370_, 0);
v_isSharedCheck_416_ = !lean_is_exclusive(v___x_370_);
if (v_isSharedCheck_416_ == 0)
{
v___x_373_ = v___x_370_;
v_isShared_374_ = v_isSharedCheck_416_;
goto v_resetjp_372_;
}
else
{
lean_inc(v_a_371_);
lean_dec(v___x_370_);
v___x_373_ = lean_box(0);
v_isShared_374_ = v_isSharedCheck_416_;
goto v_resetjp_372_;
}
v_resetjp_372_:
{
lean_object* v___x_375_; lean_object* v_traceState_376_; lean_object* v_env_377_; lean_object* v_nextMacroScope_378_; lean_object* v_ngen_379_; lean_object* v_auxDeclNGen_380_; lean_object* v_cache_381_; lean_object* v_recordedDeps_382_; lean_object* v_messages_383_; lean_object* v_infoState_384_; lean_object* v_snapshotTasks_385_; lean_object* v___x_387_; uint8_t v_isShared_388_; uint8_t v_isSharedCheck_415_; 
v___x_375_ = lean_st_ref_take(v___y_367_);
v_traceState_376_ = lean_ctor_get(v___x_375_, 4);
v_env_377_ = lean_ctor_get(v___x_375_, 0);
v_nextMacroScope_378_ = lean_ctor_get(v___x_375_, 1);
v_ngen_379_ = lean_ctor_get(v___x_375_, 2);
v_auxDeclNGen_380_ = lean_ctor_get(v___x_375_, 3);
v_cache_381_ = lean_ctor_get(v___x_375_, 5);
v_recordedDeps_382_ = lean_ctor_get(v___x_375_, 6);
v_messages_383_ = lean_ctor_get(v___x_375_, 7);
v_infoState_384_ = lean_ctor_get(v___x_375_, 8);
v_snapshotTasks_385_ = lean_ctor_get(v___x_375_, 9);
v_isSharedCheck_415_ = !lean_is_exclusive(v___x_375_);
if (v_isSharedCheck_415_ == 0)
{
v___x_387_ = v___x_375_;
v_isShared_388_ = v_isSharedCheck_415_;
goto v_resetjp_386_;
}
else
{
lean_inc(v_snapshotTasks_385_);
lean_inc(v_infoState_384_);
lean_inc(v_messages_383_);
lean_inc(v_recordedDeps_382_);
lean_inc(v_cache_381_);
lean_inc(v_traceState_376_);
lean_inc(v_auxDeclNGen_380_);
lean_inc(v_ngen_379_);
lean_inc(v_nextMacroScope_378_);
lean_inc(v_env_377_);
lean_dec(v___x_375_);
v___x_387_ = lean_box(0);
v_isShared_388_ = v_isSharedCheck_415_;
goto v_resetjp_386_;
}
v_resetjp_386_:
{
uint64_t v_tid_389_; lean_object* v_traces_390_; lean_object* v___x_392_; uint8_t v_isShared_393_; uint8_t v_isSharedCheck_414_; 
v_tid_389_ = lean_ctor_get_uint64(v_traceState_376_, sizeof(void*)*1);
v_traces_390_ = lean_ctor_get(v_traceState_376_, 0);
v_isSharedCheck_414_ = !lean_is_exclusive(v_traceState_376_);
if (v_isSharedCheck_414_ == 0)
{
v___x_392_ = v_traceState_376_;
v_isShared_393_ = v_isSharedCheck_414_;
goto v_resetjp_391_;
}
else
{
lean_inc(v_traces_390_);
lean_dec(v_traceState_376_);
v___x_392_ = lean_box(0);
v_isShared_393_ = v_isSharedCheck_414_;
goto v_resetjp_391_;
}
v_resetjp_391_:
{
lean_object* v___x_394_; lean_object* v___x_395_; double v___x_396_; uint8_t v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_405_; 
v___x_394_ = lean_box(0);
v___x_395_ = lean_box(0);
v___x_396_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3___redArg___closed__0);
v___x_397_ = 0;
v___x_398_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3___redArg___closed__1));
v___x_399_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_399_, 0, v_cls_362_);
lean_ctor_set(v___x_399_, 1, v___x_395_);
lean_ctor_set(v___x_399_, 2, v___x_398_);
lean_ctor_set_float(v___x_399_, sizeof(void*)*3, v___x_396_);
lean_ctor_set_float(v___x_399_, sizeof(void*)*3 + 8, v___x_396_);
lean_ctor_set_uint8(v___x_399_, sizeof(void*)*3 + 16, v___x_397_);
v___x_400_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3___redArg___closed__2));
v___x_401_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_401_, 0, v___x_399_);
lean_ctor_set(v___x_401_, 1, v_a_371_);
lean_ctor_set(v___x_401_, 2, v___x_400_);
lean_inc(v_ref_369_);
v___x_402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_402_, 0, v_ref_369_);
lean_ctor_set(v___x_402_, 1, v___x_401_);
v___x_403_ = l_Lean_PersistentArray_push___redArg(v_traces_390_, v___x_402_);
if (v_isShared_393_ == 0)
{
lean_ctor_set(v___x_392_, 0, v___x_403_);
v___x_405_ = v___x_392_;
goto v_reusejp_404_;
}
else
{
lean_object* v_reuseFailAlloc_413_; 
v_reuseFailAlloc_413_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_413_, 0, v___x_403_);
lean_ctor_set_uint64(v_reuseFailAlloc_413_, sizeof(void*)*1, v_tid_389_);
v___x_405_ = v_reuseFailAlloc_413_;
goto v_reusejp_404_;
}
v_reusejp_404_:
{
lean_object* v___x_407_; 
if (v_isShared_388_ == 0)
{
lean_ctor_set(v___x_387_, 4, v___x_405_);
v___x_407_ = v___x_387_;
goto v_reusejp_406_;
}
else
{
lean_object* v_reuseFailAlloc_412_; 
v_reuseFailAlloc_412_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_412_, 0, v_env_377_);
lean_ctor_set(v_reuseFailAlloc_412_, 1, v_nextMacroScope_378_);
lean_ctor_set(v_reuseFailAlloc_412_, 2, v_ngen_379_);
lean_ctor_set(v_reuseFailAlloc_412_, 3, v_auxDeclNGen_380_);
lean_ctor_set(v_reuseFailAlloc_412_, 4, v___x_405_);
lean_ctor_set(v_reuseFailAlloc_412_, 5, v_cache_381_);
lean_ctor_set(v_reuseFailAlloc_412_, 6, v_recordedDeps_382_);
lean_ctor_set(v_reuseFailAlloc_412_, 7, v_messages_383_);
lean_ctor_set(v_reuseFailAlloc_412_, 8, v_infoState_384_);
lean_ctor_set(v_reuseFailAlloc_412_, 9, v_snapshotTasks_385_);
v___x_407_ = v_reuseFailAlloc_412_;
goto v_reusejp_406_;
}
v_reusejp_406_:
{
lean_object* v___x_408_; lean_object* v___x_410_; 
v___x_408_ = lean_st_ref_put(v___y_367_, v___x_407_);
if (v_isShared_374_ == 0)
{
lean_ctor_set(v___x_373_, 0, v___x_394_);
v___x_410_ = v___x_373_;
goto v_reusejp_409_;
}
else
{
lean_object* v_reuseFailAlloc_411_; 
v_reuseFailAlloc_411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_411_, 0, v___x_394_);
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
return v___x_429_;
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
size_t v_x_38730__boxed_466_; uint8_t v_res_467_; lean_object* v_r_468_; 
v_x_38730__boxed_466_ = lean_unbox_usize(v_x_464_);
lean_dec(v_x_464_);
v_res_467_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0___redArg(v_x_463_, v_x_38730__boxed_466_, v_x_465_);
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
lean_object* v_x_494_; lean_object* v___x_495_; lean_object* v___x_496_; 
v_x_494_ = lean_ctor_get(v_e_481_, 0);
v___x_495_ = l_Lean_instInhabitedExpr;
v___x_496_ = l_Lean_Meta_Grind_AC_ACM_getStruct(v___y_482_, v___y_483_, v___y_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_, v___y_489_, v___y_490_, v___y_491_, v___y_492_);
if (lean_obj_tag(v___x_496_) == 0)
{
lean_object* v_a_497_; lean_object* v___x_499_; uint8_t v_isShared_500_; uint8_t v_isSharedCheck_512_; 
v_a_497_ = lean_ctor_get(v___x_496_, 0);
v_isSharedCheck_512_ = !lean_is_exclusive(v___x_496_);
if (v_isSharedCheck_512_ == 0)
{
v___x_499_ = v___x_496_;
v_isShared_500_ = v_isSharedCheck_512_;
goto v_resetjp_498_;
}
else
{
lean_inc(v_a_497_);
lean_dec(v___x_496_);
v___x_499_ = lean_box(0);
v_isShared_500_ = v_isSharedCheck_512_;
goto v_resetjp_498_;
}
v_resetjp_498_:
{
lean_object* v_vars_501_; lean_object* v_size_502_; uint8_t v___x_503_; 
v_vars_501_ = lean_ctor_get(v_a_497_, 10);
lean_inc_ref(v_vars_501_);
lean_dec(v_a_497_);
v_size_502_ = lean_ctor_get(v_vars_501_, 2);
v___x_503_ = lean_nat_dec_lt(v_x_494_, v_size_502_);
if (v___x_503_ == 0)
{
lean_object* v___x_504_; lean_object* v___x_506_; 
lean_dec_ref(v_vars_501_);
v___x_504_ = l_outOfBounds___redArg(v___x_495_);
if (v_isShared_500_ == 0)
{
lean_ctor_set(v___x_499_, 0, v___x_504_);
v___x_506_ = v___x_499_;
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
v___x_508_ = l_Lean_PersistentArray_get_x21___redArg(v___x_495_, v_vars_501_, v_x_494_);
lean_dec_ref(v_vars_501_);
if (v_isShared_500_ == 0)
{
lean_ctor_set(v___x_499_, 0, v___x_508_);
v___x_510_ = v___x_499_;
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
v_a_513_ = lean_ctor_get(v___x_496_, 0);
v_isSharedCheck_520_ = !lean_is_exclusive(v___x_496_);
if (v_isSharedCheck_520_ == 0)
{
v___x_515_ = v___x_496_;
v_isShared_516_ = v_isSharedCheck_520_;
goto v_resetjp_514_;
}
else
{
lean_inc(v_a_513_);
lean_dec(v___x_496_);
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
lean_object* v_a_608_; lean_object* v___x_610_; uint8_t v_isShared_611_; uint8_t v_isSharedCheck_723_; 
v_a_608_ = lean_ctor_get(v___x_607_, 0);
v_isSharedCheck_723_ = !lean_is_exclusive(v___x_607_);
if (v_isSharedCheck_723_ == 0)
{
v___x_610_ = v___x_607_;
v_isShared_611_ = v_isSharedCheck_723_;
goto v_resetjp_609_;
}
else
{
lean_inc(v_a_608_);
lean_dec(v___x_607_);
v___x_610_ = lean_box(0);
v_isShared_611_ = v_isSharedCheck_723_;
goto v_resetjp_609_;
}
v_resetjp_609_:
{
uint8_t v_ac_612_; uint8_t v___y_614_; 
v_ac_612_ = lean_ctor_get_uint8(v_a_608_, sizeof(void*)*14 + 25);
lean_dec(v_a_608_);
if (v_ac_612_ == 0)
{
lean_object* v___x_718_; lean_object* v___x_719_; 
lean_del_object(v___x_610_);
lean_dec(v_parent_x3f_580_);
lean_dec_ref(v_e_579_);
v___x_718_ = lean_box(0);
v___x_719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_719_, 0, v___x_718_);
return v___x_719_;
}
else
{
uint8_t v___x_720_; 
v___x_720_ = l_Lean_Expr_isApp(v_e_579_);
if (v___x_720_ == 0)
{
v___y_614_ = v___x_720_;
goto v___jp_613_;
}
else
{
lean_object* v___x_721_; uint8_t v___x_722_; 
v___x_721_ = l_Lean_Expr_appFn_x21(v_e_579_);
v___x_722_ = l_Lean_Expr_isApp(v___x_721_);
lean_dec_ref(v___x_721_);
v___y_614_ = v___x_722_;
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
lean_object* v_a_622_; lean_object* v___x_624_; uint8_t v_isShared_625_; uint8_t v_isSharedCheck_709_; 
v_a_622_ = lean_ctor_get(v___x_621_, 0);
v_isSharedCheck_709_ = !lean_is_exclusive(v___x_621_);
if (v_isSharedCheck_709_ == 0)
{
v___x_624_ = v___x_621_;
v_isShared_625_ = v_isSharedCheck_709_;
goto v_resetjp_623_;
}
else
{
lean_inc(v_a_622_);
lean_dec(v___x_621_);
v___x_624_ = lean_box(0);
v_isShared_625_ = v_isSharedCheck_709_;
goto v_resetjp_623_;
}
v_resetjp_623_:
{
if (lean_obj_tag(v_a_622_) == 1)
{
lean_object* v_val_626_; lean_object* v___x_627_; lean_object* v_a_628_; lean_object* v___x_630_; uint8_t v_isShared_631_; uint8_t v_isSharedCheck_704_; 
lean_del_object(v___x_624_);
v_val_626_ = lean_ctor_get(v_a_622_, 0);
lean_inc(v_val_626_);
lean_dec_ref_known(v_a_622_, 1);
v___x_627_ = l___private_Lean_Meta_Tactic_Grind_AC_Internalize_0__Lean_Meta_Grind_AC_isParentSameOpApp___redArg(v_parent_x3f_580_, v___x_620_);
lean_dec_ref(v___x_620_);
v_a_628_ = lean_ctor_get(v___x_627_, 0);
v_isSharedCheck_704_ = !lean_is_exclusive(v___x_627_);
if (v_isSharedCheck_704_ == 0)
{
v___x_630_ = v___x_627_;
v_isShared_631_ = v_isSharedCheck_704_;
goto v_resetjp_629_;
}
else
{
lean_inc(v_a_628_);
lean_dec(v___x_627_);
v___x_630_ = lean_box(0);
v_isShared_631_ = v_isSharedCheck_704_;
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
lean_object* v_a_634_; lean_object* v___x_636_; uint8_t v_isShared_637_; uint8_t v_isSharedCheck_691_; 
v_a_634_ = lean_ctor_get(v___x_633_, 0);
v_isSharedCheck_691_ = !lean_is_exclusive(v___x_633_);
if (v_isSharedCheck_691_ == 0)
{
v___x_636_ = v___x_633_;
v_isShared_637_ = v_isSharedCheck_691_;
goto v_resetjp_635_;
}
else
{
lean_inc(v_a_634_);
lean_dec(v___x_633_);
v___x_636_ = lean_box(0);
v_isShared_637_ = v_isSharedCheck_691_;
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
lean_object* v___x_646_; uint8_t v_isShared_647_; uint8_t v_isSharedCheck_677_; 
v_isSharedCheck_677_ = !lean_is_exclusive(v___x_644_);
if (v_isSharedCheck_677_ == 0)
{
lean_object* v_unused_678_; 
v_unused_678_ = lean_ctor_get(v___x_644_, 0);
lean_dec(v_unused_678_);
v___x_646_ = v___x_644_;
v_isShared_647_ = v_isSharedCheck_677_;
goto v_resetjp_645_;
}
else
{
lean_dec(v___x_644_);
v___x_646_ = lean_box(0);
v_isShared_647_ = v_isSharedCheck_677_;
goto v_resetjp_645_;
}
v_resetjp_645_:
{
lean_object* v_toCold_648_; lean_object* v_options_649_; uint8_t v_hasTrace_650_; 
v_toCold_648_ = lean_ctor_get(v_a_589_, 0);
v_options_649_ = lean_ctor_get(v_toCold_648_, 2);
v_hasTrace_650_ = lean_ctor_get_uint8(v_options_649_, sizeof(void*)*1);
if (v_hasTrace_650_ == 0)
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
lean_object* v_inheritedTraceOptions_651_; lean_object* v___x_652_; lean_object* v___x_653_; uint8_t v___x_654_; 
v_inheritedTraceOptions_651_ = lean_ctor_get(v_toCold_648_, 11);
v___x_652_ = ((lean_object*)(l_Lean_Meta_Grind_AC_internalize___closed__3));
v___x_653_ = lean_obj_once(&l_Lean_Meta_Grind_AC_internalize___closed__6, &l_Lean_Meta_Grind_AC_internalize___closed__6_once, _init_l_Lean_Meta_Grind_AC_internalize___closed__6);
v___x_654_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_651_, v_options_649_, v___x_653_);
if (v___x_654_ == 0)
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
lean_object* v___x_655_; 
v___x_655_ = l_Lean_Grind_AC_Expr_denoteExpr___at___00Lean_Meta_Grind_AC_internalize_spec__2(v_a_641_, v_val_626_, v_a_581_, v_a_582_, v_a_583_, v_a_584_, v_a_585_, v_a_586_, v_a_587_, v_a_588_, v_a_589_, v_a_590_);
lean_dec(v_a_641_);
if (lean_obj_tag(v___x_655_) == 0)
{
lean_object* v_a_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_660_; 
v_a_656_ = lean_ctor_get(v___x_655_, 0);
lean_inc(v_a_656_);
lean_dec_ref_known(v___x_655_, 1);
v___x_657_ = lean_obj_once(&l_Lean_Meta_Grind_AC_internalize___closed__8, &l_Lean_Meta_Grind_AC_internalize___closed__8_once, _init_l_Lean_Meta_Grind_AC_internalize___closed__8);
lean_inc(v_val_626_);
v___x_658_ = l_Nat_reprFast(v_val_626_);
if (v_isShared_647_ == 0)
{
lean_ctor_set_tag(v___x_646_, 3);
lean_ctor_set(v___x_646_, 0, v___x_658_);
v___x_660_ = v___x_646_;
goto v_reusejp_659_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v___x_658_);
v___x_660_ = v_reuseFailAlloc_668_;
goto v_reusejp_659_;
}
v_reusejp_659_:
{
lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; 
v___x_661_ = l_Lean_MessageData_ofFormat(v___x_660_);
v___x_662_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_662_, 0, v___x_657_);
lean_ctor_set(v___x_662_, 1, v___x_661_);
v___x_663_ = lean_obj_once(&l_Lean_Meta_Grind_AC_internalize___closed__10, &l_Lean_Meta_Grind_AC_internalize___closed__10_once, _init_l_Lean_Meta_Grind_AC_internalize___closed__10);
v___x_664_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_664_, 0, v___x_662_);
lean_ctor_set(v___x_664_, 1, v___x_663_);
v___x_665_ = l_Lean_MessageData_ofExpr(v_a_656_);
v___x_666_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_666_, 0, v___x_664_);
lean_ctor_set(v___x_666_, 1, v___x_665_);
v___x_667_ = l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3___redArg(v___x_652_, v___x_666_, v_a_587_, v_a_588_, v_a_589_, v_a_590_);
if (lean_obj_tag(v___x_667_) == 0)
{
lean_dec_ref_known(v___x_667_, 1);
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
return v___x_667_;
}
}
}
else
{
lean_object* v_a_669_; lean_object* v___x_671_; uint8_t v_isShared_672_; uint8_t v_isSharedCheck_676_; 
lean_del_object(v___x_646_);
lean_dec(v_val_626_);
lean_dec_ref(v_e_579_);
v_a_669_ = lean_ctor_get(v___x_655_, 0);
v_isSharedCheck_676_ = !lean_is_exclusive(v___x_655_);
if (v_isSharedCheck_676_ == 0)
{
v___x_671_ = v___x_655_;
v_isShared_672_ = v_isSharedCheck_676_;
goto v_resetjp_670_;
}
else
{
lean_inc(v_a_669_);
lean_dec(v___x_655_);
v___x_671_ = lean_box(0);
v_isShared_672_ = v_isSharedCheck_676_;
goto v_resetjp_670_;
}
v_resetjp_670_:
{
lean_object* v___x_674_; 
if (v_isShared_672_ == 0)
{
v___x_674_ = v___x_671_;
goto v_reusejp_673_;
}
else
{
lean_object* v_reuseFailAlloc_675_; 
v_reuseFailAlloc_675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_675_, 0, v_a_669_);
v___x_674_ = v_reuseFailAlloc_675_;
goto v_reusejp_673_;
}
v_reusejp_673_:
{
return v___x_674_;
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
lean_object* v_a_679_; lean_object* v___x_681_; uint8_t v_isShared_682_; uint8_t v_isSharedCheck_686_; 
lean_dec(v_val_626_);
lean_dec_ref(v_e_579_);
v_a_679_ = lean_ctor_get(v___x_640_, 0);
v_isSharedCheck_686_ = !lean_is_exclusive(v___x_640_);
if (v_isSharedCheck_686_ == 0)
{
v___x_681_ = v___x_640_;
v_isShared_682_ = v_isSharedCheck_686_;
goto v_resetjp_680_;
}
else
{
lean_inc(v_a_679_);
lean_dec(v___x_640_);
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
lean_object* v___x_687_; lean_object* v___x_689_; 
lean_dec(v_val_626_);
lean_dec_ref(v_e_579_);
v___x_687_ = lean_box(0);
if (v_isShared_637_ == 0)
{
lean_ctor_set(v___x_636_, 0, v___x_687_);
v___x_689_ = v___x_636_;
goto v_reusejp_688_;
}
else
{
lean_object* v_reuseFailAlloc_690_; 
v_reuseFailAlloc_690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_690_, 0, v___x_687_);
v___x_689_ = v_reuseFailAlloc_690_;
goto v_reusejp_688_;
}
v_reusejp_688_:
{
return v___x_689_;
}
}
}
}
else
{
lean_object* v_a_692_; lean_object* v___x_694_; uint8_t v_isShared_695_; uint8_t v_isSharedCheck_699_; 
lean_dec(v_val_626_);
lean_dec_ref(v_e_579_);
v_a_692_ = lean_ctor_get(v___x_633_, 0);
v_isSharedCheck_699_ = !lean_is_exclusive(v___x_633_);
if (v_isSharedCheck_699_ == 0)
{
v___x_694_ = v___x_633_;
v_isShared_695_ = v_isSharedCheck_699_;
goto v_resetjp_693_;
}
else
{
lean_inc(v_a_692_);
lean_dec(v___x_633_);
v___x_694_ = lean_box(0);
v_isShared_695_ = v_isSharedCheck_699_;
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
lean_object* v_reuseFailAlloc_698_; 
v_reuseFailAlloc_698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_698_, 0, v_a_692_);
v___x_697_ = v_reuseFailAlloc_698_;
goto v_reusejp_696_;
}
v_reusejp_696_:
{
return v___x_697_;
}
}
}
}
else
{
lean_object* v___x_700_; lean_object* v___x_702_; 
lean_dec(v_val_626_);
lean_dec_ref(v_e_579_);
v___x_700_ = lean_box(0);
if (v_isShared_631_ == 0)
{
lean_ctor_set(v___x_630_, 0, v___x_700_);
v___x_702_ = v___x_630_;
goto v_reusejp_701_;
}
else
{
lean_object* v_reuseFailAlloc_703_; 
v_reuseFailAlloc_703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_703_, 0, v___x_700_);
v___x_702_ = v_reuseFailAlloc_703_;
goto v_reusejp_701_;
}
v_reusejp_701_:
{
return v___x_702_;
}
}
}
}
else
{
lean_object* v___x_705_; lean_object* v___x_707_; 
lean_dec(v_a_622_);
lean_dec_ref(v___x_620_);
lean_dec(v_parent_x3f_580_);
lean_dec_ref(v_e_579_);
v___x_705_ = lean_box(0);
if (v_isShared_625_ == 0)
{
lean_ctor_set(v___x_624_, 0, v___x_705_);
v___x_707_ = v___x_624_;
goto v_reusejp_706_;
}
else
{
lean_object* v_reuseFailAlloc_708_; 
v_reuseFailAlloc_708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_708_, 0, v___x_705_);
v___x_707_ = v_reuseFailAlloc_708_;
goto v_reusejp_706_;
}
v_reusejp_706_:
{
return v___x_707_;
}
}
}
}
else
{
lean_object* v_a_710_; lean_object* v___x_712_; uint8_t v_isShared_713_; uint8_t v_isSharedCheck_717_; 
lean_dec_ref(v___x_620_);
lean_dec(v_parent_x3f_580_);
lean_dec_ref(v_e_579_);
v_a_710_ = lean_ctor_get(v___x_621_, 0);
v_isSharedCheck_717_ = !lean_is_exclusive(v___x_621_);
if (v_isSharedCheck_717_ == 0)
{
v___x_712_ = v___x_621_;
v_isShared_713_ = v_isSharedCheck_717_;
goto v_resetjp_711_;
}
else
{
lean_inc(v_a_710_);
lean_dec(v___x_621_);
v___x_712_ = lean_box(0);
v_isShared_713_ = v_isSharedCheck_717_;
goto v_resetjp_711_;
}
v_resetjp_711_:
{
lean_object* v___x_715_; 
if (v_isShared_713_ == 0)
{
v___x_715_ = v___x_712_;
goto v_reusejp_714_;
}
else
{
lean_object* v_reuseFailAlloc_716_; 
v_reuseFailAlloc_716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_716_, 0, v_a_710_);
v___x_715_ = v_reuseFailAlloc_716_;
goto v_reusejp_714_;
}
v_reusejp_714_:
{
return v___x_715_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_724_; lean_object* v___x_726_; uint8_t v_isShared_727_; uint8_t v_isSharedCheck_731_; 
lean_dec(v_parent_x3f_580_);
lean_dec_ref(v_e_579_);
v_a_724_ = lean_ctor_get(v___x_607_, 0);
v_isSharedCheck_731_ = !lean_is_exclusive(v___x_607_);
if (v_isSharedCheck_731_ == 0)
{
v___x_726_ = v___x_607_;
v_isShared_727_ = v_isSharedCheck_731_;
goto v_resetjp_725_;
}
else
{
lean_inc(v_a_724_);
lean_dec(v___x_607_);
v___x_726_ = lean_box(0);
v_isShared_727_ = v_isSharedCheck_731_;
goto v_resetjp_725_;
}
v_resetjp_725_:
{
lean_object* v___x_729_; 
if (v_isShared_727_ == 0)
{
v___x_729_ = v___x_726_;
goto v_reusejp_728_;
}
else
{
lean_object* v_reuseFailAlloc_730_; 
v_reuseFailAlloc_730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_730_, 0, v_a_724_);
v___x_729_ = v_reuseFailAlloc_730_;
goto v_reusejp_728_;
}
v_reusejp_728_:
{
return v___x_729_;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_internalize___boxed(lean_object* v_e_732_, lean_object* v_parent_x3f_733_, lean_object* v_a_734_, lean_object* v_a_735_, lean_object* v_a_736_, lean_object* v_a_737_, lean_object* v_a_738_, lean_object* v_a_739_, lean_object* v_a_740_, lean_object* v_a_741_, lean_object* v_a_742_, lean_object* v_a_743_, lean_object* v_a_744_){
_start:
{
lean_object* v_res_745_; 
v_res_745_ = l_Lean_Meta_Grind_AC_internalize(v_e_732_, v_parent_x3f_733_, v_a_734_, v_a_735_, v_a_736_, v_a_737_, v_a_738_, v_a_739_, v_a_740_, v_a_741_, v_a_742_, v_a_743_);
lean_dec(v_a_743_);
lean_dec_ref(v_a_742_);
lean_dec(v_a_741_);
lean_dec_ref(v_a_740_);
lean_dec(v_a_739_);
lean_dec_ref(v_a_738_);
lean_dec(v_a_737_);
lean_dec_ref(v_a_736_);
lean_dec(v_a_735_);
lean_dec(v_a_734_);
return v_res_745_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0(lean_object* v_00_u03b2_746_, lean_object* v_x_747_, lean_object* v_x_748_){
_start:
{
uint8_t v___x_749_; 
v___x_749_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0___redArg(v_x_747_, v_x_748_);
return v___x_749_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0___boxed(lean_object* v_00_u03b2_750_, lean_object* v_x_751_, lean_object* v_x_752_){
_start:
{
uint8_t v_res_753_; lean_object* v_r_754_; 
v_res_753_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0(v_00_u03b2_750_, v_x_751_, v_x_752_);
lean_dec_ref(v_x_752_);
lean_dec_ref(v_x_751_);
v_r_754_ = lean_box(v_res_753_);
return v_r_754_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1(lean_object* v_00_u03b2_755_, lean_object* v_x_756_, lean_object* v_x_757_, lean_object* v_x_758_){
_start:
{
lean_object* v___x_759_; 
v___x_759_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1___redArg(v_x_756_, v_x_757_, v_x_758_);
return v___x_759_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3(lean_object* v_cls_760_, lean_object* v_msg_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_){
_start:
{
lean_object* v___x_774_; 
v___x_774_ = l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3___redArg(v_cls_760_, v_msg_761_, v___y_769_, v___y_770_, v___y_771_, v___y_772_);
return v___x_774_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3___boxed(lean_object* v_cls_775_, lean_object* v_msg_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_){
_start:
{
lean_object* v_res_789_; 
v_res_789_ = l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3(v_cls_775_, v_msg_776_, v___y_777_, v___y_778_, v___y_779_, v___y_780_, v___y_781_, v___y_782_, v___y_783_, v___y_784_, v___y_785_, v___y_786_, v___y_787_);
lean_dec(v___y_787_);
lean_dec_ref(v___y_786_);
lean_dec(v___y_785_);
lean_dec_ref(v___y_784_);
lean_dec(v___y_783_);
lean_dec_ref(v___y_782_);
lean_dec(v___y_781_);
lean_dec_ref(v___y_780_);
lean_dec(v___y_779_);
lean_dec(v___y_778_);
lean_dec(v___y_777_);
return v_res_789_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0(lean_object* v_00_u03b2_790_, lean_object* v_x_791_, size_t v_x_792_, lean_object* v_x_793_){
_start:
{
uint8_t v___x_794_; 
v___x_794_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0___redArg(v_x_791_, v_x_792_, v_x_793_);
return v___x_794_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0___boxed(lean_object* v_00_u03b2_795_, lean_object* v_x_796_, lean_object* v_x_797_, lean_object* v_x_798_){
_start:
{
size_t v_x_39317__boxed_799_; uint8_t v_res_800_; lean_object* v_r_801_; 
v_x_39317__boxed_799_ = lean_unbox_usize(v_x_797_);
lean_dec(v_x_797_);
v_res_800_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0(v_00_u03b2_795_, v_x_796_, v_x_39317__boxed_799_, v_x_798_);
lean_dec_ref(v_x_798_);
lean_dec_ref(v_x_796_);
v_r_801_ = lean_box(v_res_800_);
return v_r_801_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2(lean_object* v_00_u03b2_802_, lean_object* v_x_803_, size_t v_x_804_, size_t v_x_805_, lean_object* v_x_806_, lean_object* v_x_807_){
_start:
{
lean_object* v___x_808_; 
v___x_808_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___redArg(v_x_803_, v_x_804_, v_x_805_, v_x_806_, v_x_807_);
return v___x_808_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___boxed(lean_object* v_00_u03b2_809_, lean_object* v_x_810_, lean_object* v_x_811_, lean_object* v_x_812_, lean_object* v_x_813_, lean_object* v_x_814_){
_start:
{
size_t v_x_39328__boxed_815_; size_t v_x_39329__boxed_816_; lean_object* v_res_817_; 
v_x_39328__boxed_815_ = lean_unbox_usize(v_x_811_);
lean_dec(v_x_811_);
v_x_39329__boxed_816_ = lean_unbox_usize(v_x_812_);
lean_dec(v_x_812_);
v_res_817_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2(v_00_u03b2_809_, v_x_810_, v_x_39328__boxed_815_, v_x_39329__boxed_816_, v_x_813_, v_x_814_);
return v_res_817_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_818_, lean_object* v_keys_819_, lean_object* v_vals_820_, lean_object* v_heq_821_, lean_object* v_i_822_, lean_object* v_k_823_){
_start:
{
uint8_t v___x_824_; 
v___x_824_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0_spec__1___redArg(v_keys_819_, v_i_822_, v_k_823_);
return v___x_824_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_825_, lean_object* v_keys_826_, lean_object* v_vals_827_, lean_object* v_heq_828_, lean_object* v_i_829_, lean_object* v_k_830_){
_start:
{
uint8_t v_res_831_; lean_object* v_r_832_; 
v_res_831_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0_spec__1(v_00_u03b2_825_, v_keys_826_, v_vals_827_, v_heq_828_, v_i_829_, v_k_830_);
lean_dec_ref(v_k_830_);
lean_dec_ref(v_vals_827_);
lean_dec_ref(v_keys_826_);
v_r_832_ = lean_box(v_res_831_);
return v_r_832_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_833_, lean_object* v_n_834_, lean_object* v_k_835_, lean_object* v_v_836_){
_start:
{
lean_object* v___x_837_; 
v___x_837_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2_spec__4___redArg(v_n_834_, v_k_835_, v_v_836_);
return v___x_837_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_838_, size_t v_depth_839_, lean_object* v_keys_840_, lean_object* v_vals_841_, lean_object* v_heq_842_, lean_object* v_i_843_, lean_object* v_entries_844_){
_start:
{
lean_object* v___x_845_; 
v___x_845_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2_spec__5___redArg(v_depth_839_, v_keys_840_, v_vals_841_, v_i_843_, v_entries_844_);
return v___x_845_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_846_, lean_object* v_depth_847_, lean_object* v_keys_848_, lean_object* v_vals_849_, lean_object* v_heq_850_, lean_object* v_i_851_, lean_object* v_entries_852_){
_start:
{
size_t v_depth_boxed_853_; lean_object* v_res_854_; 
v_depth_boxed_853_ = lean_unbox_usize(v_depth_847_);
lean_dec(v_depth_847_);
v_res_854_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2_spec__5(v_00_u03b2_846_, v_depth_boxed_853_, v_keys_848_, v_vals_849_, v_heq_850_, v_i_851_, v_entries_852_);
lean_dec_ref(v_vals_849_);
lean_dec_ref(v_keys_848_);
return v_res_854_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2_spec__4_spec__8(lean_object* v_00_u03b2_855_, lean_object* v_x_856_, lean_object* v_x_857_, lean_object* v_x_858_, lean_object* v_x_859_){
_start:
{
lean_object* v___x_860_; 
v___x_860_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2_spec__4_spec__8___redArg(v_x_856_, v_x_857_, v_x_858_, v_x_859_);
return v___x_860_;
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
