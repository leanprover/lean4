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
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
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
lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Internalize_0__Lean_Meta_Grind_AC_isParentSameOpApp___redArg(lean_object* v_parent_x3f_1_, lean_object* v_op_2_){
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
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_AC_Internalize_0__Lean_Meta_Grind_AC_isParentSameOpApp___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_parent_x3f_1_ = stack[0].m_obj;
lean_object* v_op_2_ = stack[1].m_obj;
lean_object* v_res_30_;
v_res_30_ = l___private_Lean_Meta_Tactic_Grind_AC_Internalize_0__Lean_Meta_Grind_AC_isParentSameOpApp___redArg(v_parent_x3f_1_, v_op_2_);
stack->m_obj
 = v_res_30_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Internalize_0__Lean_Meta_Grind_AC_isParentSameOpApp___redArg___boxed(lean_object* v_parent_x3f_31_, lean_object* v_op_32_, lean_object* v_a_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = l___private_Lean_Meta_Tactic_Grind_AC_Internalize_0__Lean_Meta_Grind_AC_isParentSameOpApp___redArg(v_parent_x3f_31_, v_op_32_);
lean_dec_ref(v_op_32_);
return v_res_34_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Internalize_0__Lean_Meta_Grind_AC_isParentSameOpApp(lean_object* v_parent_x3f_35_, lean_object* v_op_36_, lean_object* v_a_37_, lean_object* v_a_38_, lean_object* v_a_39_, lean_object* v_a_40_, lean_object* v_a_41_, lean_object* v_a_42_, lean_object* v_a_43_, lean_object* v_a_44_, lean_object* v_a_45_, lean_object* v_a_46_){
_start:
{
lean_object* v___x_48_; 
v___x_48_ = l___private_Lean_Meta_Tactic_Grind_AC_Internalize_0__Lean_Meta_Grind_AC_isParentSameOpApp___redArg(v_parent_x3f_35_, v_op_36_);
return v___x_48_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_AC_Internalize_0__Lean_Meta_Grind_AC_isParentSameOpApp_0interp(lean_interpreter_value* stack)
{
lean_object* v_parent_x3f_35_ = stack[0].m_obj;
lean_object* v_op_36_ = stack[1].m_obj;
lean_object* v_a_37_ = stack[2].m_obj;
lean_object* v_a_38_ = stack[3].m_obj;
lean_object* v_a_39_ = stack[4].m_obj;
lean_object* v_a_40_ = stack[5].m_obj;
lean_object* v_a_41_ = stack[6].m_obj;
lean_object* v_a_42_ = stack[7].m_obj;
lean_object* v_a_43_ = stack[8].m_obj;
lean_object* v_a_44_ = stack[9].m_obj;
lean_object* v_a_45_ = stack[10].m_obj;
lean_object* v_a_46_ = stack[11].m_obj;
lean_object* v_res_49_;
v_res_49_ = l___private_Lean_Meta_Tactic_Grind_AC_Internalize_0__Lean_Meta_Grind_AC_isParentSameOpApp(v_parent_x3f_35_, v_op_36_, v_a_37_, v_a_38_, v_a_39_, v_a_40_, v_a_41_, v_a_42_, v_a_43_, v_a_44_, v_a_45_, v_a_46_);
stack->m_obj
 = v_res_49_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Internalize_0__Lean_Meta_Grind_AC_isParentSameOpApp___boxed(lean_object* v_parent_x3f_50_, lean_object* v_op_51_, lean_object* v_a_52_, lean_object* v_a_53_, lean_object* v_a_54_, lean_object* v_a_55_, lean_object* v_a_56_, lean_object* v_a_57_, lean_object* v_a_58_, lean_object* v_a_59_, lean_object* v_a_60_, lean_object* v_a_61_, lean_object* v_a_62_){
_start:
{
lean_object* v_res_63_; 
v_res_63_ = l___private_Lean_Meta_Tactic_Grind_AC_Internalize_0__Lean_Meta_Grind_AC_isParentSameOpApp(v_parent_x3f_50_, v_op_51_, v_a_52_, v_a_53_, v_a_54_, v_a_55_, v_a_56_, v_a_57_, v_a_58_, v_a_59_, v_a_60_, v_a_61_);
lean_dec(v_a_61_);
lean_dec_ref(v_a_60_);
lean_dec(v_a_59_);
lean_dec_ref(v_a_58_);
lean_dec(v_a_57_);
lean_dec_ref(v_a_56_);
lean_dec(v_a_55_);
lean_dec_ref(v_a_54_);
lean_dec(v_a_53_);
lean_dec(v_a_52_);
lean_dec_ref(v_op_51_);
return v_res_63_;
}
}
lean_object* l_Lean_Meta_Grind_AC_reify(lean_object* v_e_64_, lean_object* v_a_65_, lean_object* v_a_66_, lean_object* v_a_67_, lean_object* v_a_68_, lean_object* v_a_69_, lean_object* v_a_70_, lean_object* v_a_71_, lean_object* v_a_72_, lean_object* v_a_73_, lean_object* v_a_74_, lean_object* v_a_75_){
_start:
{
lean_object* v___x_77_; 
v___x_77_ = l_Lean_Meta_Grind_AC_isOp_x3f(v_e_64_, v_a_65_, v_a_66_, v_a_67_, v_a_68_, v_a_69_, v_a_70_, v_a_71_, v_a_72_, v_a_73_, v_a_74_, v_a_75_);
if (lean_obj_tag(v___x_77_) == 0)
{
lean_object* v_a_78_; 
v_a_78_ = lean_ctor_get(v___x_77_, 0);
lean_inc(v_a_78_);
lean_dec_ref_known(v___x_77_, 1);
if (lean_obj_tag(v_a_78_) == 1)
{
lean_object* v_val_79_; lean_object* v_fst_80_; lean_object* v_snd_81_; lean_object* v___x_83_; uint8_t v_isShared_84_; uint8_t v_isSharedCheck_99_; 
lean_dec_ref(v_e_64_);
v_val_79_ = lean_ctor_get(v_a_78_, 0);
lean_inc(v_val_79_);
lean_dec_ref_known(v_a_78_, 1);
v_fst_80_ = lean_ctor_get(v_val_79_, 0);
v_snd_81_ = lean_ctor_get(v_val_79_, 1);
v_isSharedCheck_99_ = !lean_is_exclusive(v_val_79_);
if (v_isSharedCheck_99_ == 0)
{
v___x_83_ = v_val_79_;
v_isShared_84_ = v_isSharedCheck_99_;
goto v_resetjp_82_;
}
else
{
lean_inc(v_snd_81_);
lean_inc(v_fst_80_);
lean_dec(v_val_79_);
v___x_83_ = lean_box(0);
v_isShared_84_ = v_isSharedCheck_99_;
goto v_resetjp_82_;
}
v_resetjp_82_:
{
lean_object* v___x_85_; 
v___x_85_ = l_Lean_Meta_Grind_AC_reify(v_fst_80_, v_a_65_, v_a_66_, v_a_67_, v_a_68_, v_a_69_, v_a_70_, v_a_71_, v_a_72_, v_a_73_, v_a_74_, v_a_75_);
if (lean_obj_tag(v___x_85_) == 0)
{
lean_object* v_a_86_; lean_object* v___x_87_; 
v_a_86_ = lean_ctor_get(v___x_85_, 0);
lean_inc(v_a_86_);
lean_dec_ref_known(v___x_85_, 1);
v___x_87_ = l_Lean_Meta_Grind_AC_reify(v_snd_81_, v_a_65_, v_a_66_, v_a_67_, v_a_68_, v_a_69_, v_a_70_, v_a_71_, v_a_72_, v_a_73_, v_a_74_, v_a_75_);
if (lean_obj_tag(v___x_87_) == 0)
{
lean_object* v_a_88_; lean_object* v___x_90_; uint8_t v_isShared_91_; uint8_t v_isSharedCheck_98_; 
v_a_88_ = lean_ctor_get(v___x_87_, 0);
v_isSharedCheck_98_ = !lean_is_exclusive(v___x_87_);
if (v_isSharedCheck_98_ == 0)
{
v___x_90_ = v___x_87_;
v_isShared_91_ = v_isSharedCheck_98_;
goto v_resetjp_89_;
}
else
{
lean_inc(v_a_88_);
lean_dec(v___x_87_);
v___x_90_ = lean_box(0);
v_isShared_91_ = v_isSharedCheck_98_;
goto v_resetjp_89_;
}
v_resetjp_89_:
{
lean_object* v___x_93_; 
if (v_isShared_84_ == 0)
{
lean_ctor_set_tag(v___x_83_, 1);
lean_ctor_set(v___x_83_, 1, v_a_88_);
lean_ctor_set(v___x_83_, 0, v_a_86_);
v___x_93_ = v___x_83_;
goto v_reusejp_92_;
}
else
{
lean_object* v_reuseFailAlloc_97_; 
v_reuseFailAlloc_97_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_97_, 0, v_a_86_);
lean_ctor_set(v_reuseFailAlloc_97_, 1, v_a_88_);
v___x_93_ = v_reuseFailAlloc_97_;
goto v_reusejp_92_;
}
v_reusejp_92_:
{
lean_object* v___x_95_; 
if (v_isShared_91_ == 0)
{
lean_ctor_set(v___x_90_, 0, v___x_93_);
v___x_95_ = v___x_90_;
goto v_reusejp_94_;
}
else
{
lean_object* v_reuseFailAlloc_96_; 
v_reuseFailAlloc_96_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_96_, 0, v___x_93_);
v___x_95_ = v_reuseFailAlloc_96_;
goto v_reusejp_94_;
}
v_reusejp_94_:
{
return v___x_95_;
}
}
}
}
else
{
lean_dec(v_a_86_);
lean_del_object(v___x_83_);
return v___x_87_;
}
}
else
{
lean_del_object(v___x_83_);
lean_dec(v_snd_81_);
return v___x_85_;
}
}
}
else
{
lean_object* v___x_100_; 
lean_dec(v_a_78_);
v___x_100_ = l_Lean_Meta_Grind_AC_mkVar(v_e_64_, v_a_65_, v_a_66_, v_a_67_, v_a_68_, v_a_69_, v_a_70_, v_a_71_, v_a_72_, v_a_73_, v_a_74_, v_a_75_);
if (lean_obj_tag(v___x_100_) == 0)
{
lean_object* v_a_101_; lean_object* v___x_103_; uint8_t v_isShared_104_; uint8_t v_isSharedCheck_109_; 
v_a_101_ = lean_ctor_get(v___x_100_, 0);
v_isSharedCheck_109_ = !lean_is_exclusive(v___x_100_);
if (v_isSharedCheck_109_ == 0)
{
v___x_103_ = v___x_100_;
v_isShared_104_ = v_isSharedCheck_109_;
goto v_resetjp_102_;
}
else
{
lean_inc(v_a_101_);
lean_dec(v___x_100_);
v___x_103_ = lean_box(0);
v_isShared_104_ = v_isSharedCheck_109_;
goto v_resetjp_102_;
}
v_resetjp_102_:
{
lean_object* v___x_105_; lean_object* v___x_107_; 
v___x_105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_105_, 0, v_a_101_);
if (v_isShared_104_ == 0)
{
lean_ctor_set(v___x_103_, 0, v___x_105_);
v___x_107_ = v___x_103_;
goto v_reusejp_106_;
}
else
{
lean_object* v_reuseFailAlloc_108_; 
v_reuseFailAlloc_108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_108_, 0, v___x_105_);
v___x_107_ = v_reuseFailAlloc_108_;
goto v_reusejp_106_;
}
v_reusejp_106_:
{
return v___x_107_;
}
}
}
else
{
lean_object* v_a_110_; lean_object* v___x_112_; uint8_t v_isShared_113_; uint8_t v_isSharedCheck_117_; 
v_a_110_ = lean_ctor_get(v___x_100_, 0);
v_isSharedCheck_117_ = !lean_is_exclusive(v___x_100_);
if (v_isSharedCheck_117_ == 0)
{
v___x_112_ = v___x_100_;
v_isShared_113_ = v_isSharedCheck_117_;
goto v_resetjp_111_;
}
else
{
lean_inc(v_a_110_);
lean_dec(v___x_100_);
v___x_112_ = lean_box(0);
v_isShared_113_ = v_isSharedCheck_117_;
goto v_resetjp_111_;
}
v_resetjp_111_:
{
lean_object* v___x_115_; 
if (v_isShared_113_ == 0)
{
v___x_115_ = v___x_112_;
goto v_reusejp_114_;
}
else
{
lean_object* v_reuseFailAlloc_116_; 
v_reuseFailAlloc_116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_116_, 0, v_a_110_);
v___x_115_ = v_reuseFailAlloc_116_;
goto v_reusejp_114_;
}
v_reusejp_114_:
{
return v___x_115_;
}
}
}
}
}
else
{
lean_object* v_a_118_; lean_object* v___x_120_; uint8_t v_isShared_121_; uint8_t v_isSharedCheck_125_; 
lean_dec_ref(v_e_64_);
v_a_118_ = lean_ctor_get(v___x_77_, 0);
v_isSharedCheck_125_ = !lean_is_exclusive(v___x_77_);
if (v_isSharedCheck_125_ == 0)
{
v___x_120_ = v___x_77_;
v_isShared_121_ = v_isSharedCheck_125_;
goto v_resetjp_119_;
}
else
{
lean_inc(v_a_118_);
lean_dec(v___x_77_);
v___x_120_ = lean_box(0);
v_isShared_121_ = v_isSharedCheck_125_;
goto v_resetjp_119_;
}
v_resetjp_119_:
{
lean_object* v___x_123_; 
if (v_isShared_121_ == 0)
{
v___x_123_ = v___x_120_;
goto v_reusejp_122_;
}
else
{
lean_object* v_reuseFailAlloc_124_; 
v_reuseFailAlloc_124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_124_, 0, v_a_118_);
v___x_123_ = v_reuseFailAlloc_124_;
goto v_reusejp_122_;
}
v_reusejp_122_:
{
return v___x_123_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_AC_reify_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_64_ = stack[0].m_obj;
lean_object* v_a_65_ = stack[1].m_obj;
lean_object* v_a_66_ = stack[2].m_obj;
lean_object* v_a_67_ = stack[3].m_obj;
lean_object* v_a_68_ = stack[4].m_obj;
lean_object* v_a_69_ = stack[5].m_obj;
lean_object* v_a_70_ = stack[6].m_obj;
lean_object* v_a_71_ = stack[7].m_obj;
lean_object* v_a_72_ = stack[8].m_obj;
lean_object* v_a_73_ = stack[9].m_obj;
lean_object* v_a_74_ = stack[10].m_obj;
lean_object* v_a_75_ = stack[11].m_obj;
lean_object* v_res_126_;
v_res_126_ = l_Lean_Meta_Grind_AC_reify(v_e_64_, v_a_65_, v_a_66_, v_a_67_, v_a_68_, v_a_69_, v_a_70_, v_a_71_, v_a_72_, v_a_73_, v_a_74_, v_a_75_);
stack->m_obj
 = v_res_126_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_reify___boxed(lean_object* v_e_127_, lean_object* v_a_128_, lean_object* v_a_129_, lean_object* v_a_130_, lean_object* v_a_131_, lean_object* v_a_132_, lean_object* v_a_133_, lean_object* v_a_134_, lean_object* v_a_135_, lean_object* v_a_136_, lean_object* v_a_137_, lean_object* v_a_138_, lean_object* v_a_139_){
_start:
{
lean_object* v_res_140_; 
v_res_140_ = l_Lean_Meta_Grind_AC_reify(v_e_127_, v_a_128_, v_a_129_, v_a_130_, v_a_131_, v_a_132_, v_a_133_, v_a_134_, v_a_135_, v_a_136_, v_a_137_, v_a_138_);
lean_dec(v_a_138_);
lean_dec_ref(v_a_137_);
lean_dec(v_a_136_);
lean_dec_ref(v_a_135_);
lean_dec(v_a_134_);
lean_dec_ref(v_a_133_);
lean_dec(v_a_132_);
lean_dec_ref(v_a_131_);
lean_dec(v_a_130_);
lean_dec(v_a_129_);
lean_dec(v_a_128_);
return v_res_140_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2_spec__4_spec__8___redArg(lean_object* v_x_141_, lean_object* v_x_142_, lean_object* v_x_143_, lean_object* v_x_144_){
_start:
{
lean_object* v_ks_145_; lean_object* v_vs_146_; lean_object* v___x_148_; uint8_t v_isShared_149_; uint8_t v_isSharedCheck_172_; 
v_ks_145_ = lean_ctor_get(v_x_141_, 0);
v_vs_146_ = lean_ctor_get(v_x_141_, 1);
v_isSharedCheck_172_ = !lean_is_exclusive(v_x_141_);
if (v_isSharedCheck_172_ == 0)
{
v___x_148_ = v_x_141_;
v_isShared_149_ = v_isSharedCheck_172_;
goto v_resetjp_147_;
}
else
{
lean_inc(v_vs_146_);
lean_inc(v_ks_145_);
lean_dec(v_x_141_);
v___x_148_ = lean_box(0);
v_isShared_149_ = v_isSharedCheck_172_;
goto v_resetjp_147_;
}
v_resetjp_147_:
{
lean_object* v___x_150_; uint8_t v___x_151_; 
v___x_150_ = lean_array_get_size(v_ks_145_);
v___x_151_ = lean_nat_dec_lt(v_x_142_, v___x_150_);
if (v___x_151_ == 0)
{
lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_155_; 
lean_dec(v_x_142_);
v___x_152_ = lean_array_push(v_ks_145_, v_x_143_);
v___x_153_ = lean_array_push(v_vs_146_, v_x_144_);
if (v_isShared_149_ == 0)
{
lean_ctor_set(v___x_148_, 1, v___x_153_);
lean_ctor_set(v___x_148_, 0, v___x_152_);
v___x_155_ = v___x_148_;
goto v_reusejp_154_;
}
else
{
lean_object* v_reuseFailAlloc_156_; 
v_reuseFailAlloc_156_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_156_, 0, v___x_152_);
lean_ctor_set(v_reuseFailAlloc_156_, 1, v___x_153_);
v___x_155_ = v_reuseFailAlloc_156_;
goto v_reusejp_154_;
}
v_reusejp_154_:
{
return v___x_155_;
}
}
else
{
lean_object* v_k_x27_157_; size_t v___x_158_; size_t v___x_159_; uint8_t v___x_160_; 
v_k_x27_157_ = lean_array_fget_borrowed(v_ks_145_, v_x_142_);
v___x_158_ = lean_ptr_addr(v_x_143_);
v___x_159_ = lean_ptr_addr(v_k_x27_157_);
v___x_160_ = lean_usize_dec_eq(v___x_158_, v___x_159_);
if (v___x_160_ == 0)
{
lean_object* v___x_162_; 
if (v_isShared_149_ == 0)
{
v___x_162_ = v___x_148_;
goto v_reusejp_161_;
}
else
{
lean_object* v_reuseFailAlloc_166_; 
v_reuseFailAlloc_166_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_166_, 0, v_ks_145_);
lean_ctor_set(v_reuseFailAlloc_166_, 1, v_vs_146_);
v___x_162_ = v_reuseFailAlloc_166_;
goto v_reusejp_161_;
}
v_reusejp_161_:
{
lean_object* v___x_163_; lean_object* v___x_164_; 
v___x_163_ = lean_unsigned_to_nat(1u);
v___x_164_ = lean_nat_add(v_x_142_, v___x_163_);
lean_dec(v_x_142_);
v_x_141_ = v___x_162_;
v_x_142_ = v___x_164_;
goto _start;
}
}
else
{
lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_170_; 
v___x_167_ = lean_array_fset(v_ks_145_, v_x_142_, v_x_143_);
v___x_168_ = lean_array_fset(v_vs_146_, v_x_142_, v_x_144_);
lean_dec(v_x_142_);
if (v_isShared_149_ == 0)
{
lean_ctor_set(v___x_148_, 1, v___x_168_);
lean_ctor_set(v___x_148_, 0, v___x_167_);
v___x_170_ = v___x_148_;
goto v_reusejp_169_;
}
else
{
lean_object* v_reuseFailAlloc_171_; 
v_reuseFailAlloc_171_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_171_, 0, v___x_167_);
lean_ctor_set(v_reuseFailAlloc_171_, 1, v___x_168_);
v___x_170_ = v_reuseFailAlloc_171_;
goto v_reusejp_169_;
}
v_reusejp_169_:
{
return v___x_170_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2_spec__4___redArg(lean_object* v_n_173_, lean_object* v_k_174_, lean_object* v_v_175_){
_start:
{
lean_object* v___x_176_; lean_object* v___x_177_; 
v___x_176_ = lean_unsigned_to_nat(0u);
v___x_177_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2_spec__4_spec__8___redArg(v_n_173_, v___x_176_, v_k_174_, v_v_175_);
return v___x_177_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_178_; 
v___x_178_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_178_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___redArg(lean_object* v_x_179_, size_t v_x_180_, size_t v_x_181_, lean_object* v_x_182_, lean_object* v_x_183_){
_start:
{
if (lean_obj_tag(v_x_179_) == 0)
{
lean_object* v_es_184_; size_t v___x_185_; size_t v___x_186_; lean_object* v_j_187_; lean_object* v___x_188_; uint8_t v___x_189_; 
v_es_184_ = lean_ctor_get(v_x_179_, 0);
v___x_185_ = ((size_t)31ULL);
v___x_186_ = lean_usize_land(v_x_180_, v___x_185_);
v_j_187_ = lean_usize_to_nat(v___x_186_);
v___x_188_ = lean_array_get_size(v_es_184_);
v___x_189_ = lean_nat_dec_lt(v_j_187_, v___x_188_);
if (v___x_189_ == 0)
{
lean_dec(v_j_187_);
lean_dec(v_x_183_);
lean_dec_ref(v_x_182_);
return v_x_179_;
}
else
{
lean_object* v___x_191_; uint8_t v_isShared_192_; uint8_t v_isSharedCheck_230_; 
lean_inc_ref(v_es_184_);
v_isSharedCheck_230_ = !lean_is_exclusive(v_x_179_);
if (v_isSharedCheck_230_ == 0)
{
lean_object* v_unused_231_; 
v_unused_231_ = lean_ctor_get(v_x_179_, 0);
lean_dec(v_unused_231_);
v___x_191_ = v_x_179_;
v_isShared_192_ = v_isSharedCheck_230_;
goto v_resetjp_190_;
}
else
{
lean_dec(v_x_179_);
v___x_191_ = lean_box(0);
v_isShared_192_ = v_isSharedCheck_230_;
goto v_resetjp_190_;
}
v_resetjp_190_:
{
lean_object* v_v_193_; lean_object* v___x_194_; lean_object* v_xs_x27_195_; lean_object* v___y_197_; 
v_v_193_ = lean_array_fget(v_es_184_, v_j_187_);
v___x_194_ = lean_box(0);
v_xs_x27_195_ = lean_array_fset(v_es_184_, v_j_187_, v___x_194_);
switch(lean_obj_tag(v_v_193_))
{
case 0:
{
lean_object* v_key_202_; lean_object* v_val_203_; lean_object* v___x_205_; uint8_t v_isShared_206_; uint8_t v_isSharedCheck_215_; 
v_key_202_ = lean_ctor_get(v_v_193_, 0);
v_val_203_ = lean_ctor_get(v_v_193_, 1);
v_isSharedCheck_215_ = !lean_is_exclusive(v_v_193_);
if (v_isSharedCheck_215_ == 0)
{
v___x_205_ = v_v_193_;
v_isShared_206_ = v_isSharedCheck_215_;
goto v_resetjp_204_;
}
else
{
lean_inc(v_val_203_);
lean_inc(v_key_202_);
lean_dec(v_v_193_);
v___x_205_ = lean_box(0);
v_isShared_206_ = v_isSharedCheck_215_;
goto v_resetjp_204_;
}
v_resetjp_204_:
{
size_t v___x_207_; size_t v___x_208_; uint8_t v___x_209_; 
v___x_207_ = lean_ptr_addr(v_x_182_);
v___x_208_ = lean_ptr_addr(v_key_202_);
v___x_209_ = lean_usize_dec_eq(v___x_207_, v___x_208_);
if (v___x_209_ == 0)
{
lean_object* v___x_210_; lean_object* v___x_211_; 
lean_del_object(v___x_205_);
v___x_210_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_202_, v_val_203_, v_x_182_, v_x_183_);
v___x_211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_211_, 0, v___x_210_);
v___y_197_ = v___x_211_;
goto v___jp_196_;
}
else
{
lean_object* v___x_213_; 
lean_dec(v_val_203_);
lean_dec(v_key_202_);
if (v_isShared_206_ == 0)
{
lean_ctor_set(v___x_205_, 1, v_x_183_);
lean_ctor_set(v___x_205_, 0, v_x_182_);
v___x_213_ = v___x_205_;
goto v_reusejp_212_;
}
else
{
lean_object* v_reuseFailAlloc_214_; 
v_reuseFailAlloc_214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_214_, 0, v_x_182_);
lean_ctor_set(v_reuseFailAlloc_214_, 1, v_x_183_);
v___x_213_ = v_reuseFailAlloc_214_;
goto v_reusejp_212_;
}
v_reusejp_212_:
{
v___y_197_ = v___x_213_;
goto v___jp_196_;
}
}
}
}
case 1:
{
lean_object* v_node_216_; lean_object* v___x_218_; uint8_t v_isShared_219_; uint8_t v_isSharedCheck_228_; 
v_node_216_ = lean_ctor_get(v_v_193_, 0);
v_isSharedCheck_228_ = !lean_is_exclusive(v_v_193_);
if (v_isSharedCheck_228_ == 0)
{
v___x_218_ = v_v_193_;
v_isShared_219_ = v_isSharedCheck_228_;
goto v_resetjp_217_;
}
else
{
lean_inc(v_node_216_);
lean_dec(v_v_193_);
v___x_218_ = lean_box(0);
v_isShared_219_ = v_isSharedCheck_228_;
goto v_resetjp_217_;
}
v_resetjp_217_:
{
size_t v___x_220_; size_t v___x_221_; size_t v___x_222_; size_t v___x_223_; lean_object* v___x_224_; lean_object* v___x_226_; 
v___x_220_ = ((size_t)5ULL);
v___x_221_ = lean_usize_shift_right(v_x_180_, v___x_220_);
v___x_222_ = ((size_t)1ULL);
v___x_223_ = lean_usize_add(v_x_181_, v___x_222_);
v___x_224_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___redArg(v_node_216_, v___x_221_, v___x_223_, v_x_182_, v_x_183_);
if (v_isShared_219_ == 0)
{
lean_ctor_set(v___x_218_, 0, v___x_224_);
v___x_226_ = v___x_218_;
goto v_reusejp_225_;
}
else
{
lean_object* v_reuseFailAlloc_227_; 
v_reuseFailAlloc_227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_227_, 0, v___x_224_);
v___x_226_ = v_reuseFailAlloc_227_;
goto v_reusejp_225_;
}
v_reusejp_225_:
{
v___y_197_ = v___x_226_;
goto v___jp_196_;
}
}
}
default: 
{
lean_object* v___x_229_; 
v___x_229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_229_, 0, v_x_182_);
lean_ctor_set(v___x_229_, 1, v_x_183_);
v___y_197_ = v___x_229_;
goto v___jp_196_;
}
}
v___jp_196_:
{
lean_object* v___x_198_; lean_object* v___x_200_; 
v___x_198_ = lean_array_fset(v_xs_x27_195_, v_j_187_, v___y_197_);
lean_dec(v_j_187_);
if (v_isShared_192_ == 0)
{
lean_ctor_set(v___x_191_, 0, v___x_198_);
v___x_200_ = v___x_191_;
goto v_reusejp_199_;
}
else
{
lean_object* v_reuseFailAlloc_201_; 
v_reuseFailAlloc_201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_201_, 0, v___x_198_);
v___x_200_ = v_reuseFailAlloc_201_;
goto v_reusejp_199_;
}
v_reusejp_199_:
{
return v___x_200_;
}
}
}
}
}
else
{
lean_object* v_ks_232_; lean_object* v_vs_233_; lean_object* v___x_235_; uint8_t v_isShared_236_; uint8_t v_isSharedCheck_251_; 
v_ks_232_ = lean_ctor_get(v_x_179_, 0);
v_vs_233_ = lean_ctor_get(v_x_179_, 1);
v_isSharedCheck_251_ = !lean_is_exclusive(v_x_179_);
if (v_isSharedCheck_251_ == 0)
{
v___x_235_ = v_x_179_;
v_isShared_236_ = v_isSharedCheck_251_;
goto v_resetjp_234_;
}
else
{
lean_inc(v_vs_233_);
lean_inc(v_ks_232_);
lean_dec(v_x_179_);
v___x_235_ = lean_box(0);
v_isShared_236_ = v_isSharedCheck_251_;
goto v_resetjp_234_;
}
v_resetjp_234_:
{
lean_object* v___x_238_; 
if (v_isShared_236_ == 0)
{
v___x_238_ = v___x_235_;
goto v_reusejp_237_;
}
else
{
lean_object* v_reuseFailAlloc_250_; 
v_reuseFailAlloc_250_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_250_, 0, v_ks_232_);
lean_ctor_set(v_reuseFailAlloc_250_, 1, v_vs_233_);
v___x_238_ = v_reuseFailAlloc_250_;
goto v_reusejp_237_;
}
v_reusejp_237_:
{
lean_object* v_newNode_239_; size_t v___x_240_; uint8_t v___x_241_; 
v_newNode_239_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2_spec__4___redArg(v___x_238_, v_x_182_, v_x_183_);
v___x_240_ = ((size_t)7ULL);
v___x_241_ = lean_usize_dec_le(v___x_240_, v_x_181_);
if (v___x_241_ == 0)
{
lean_object* v___x_242_; lean_object* v___x_243_; uint8_t v___x_244_; 
v___x_242_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_239_);
v___x_243_ = lean_unsigned_to_nat(4u);
v___x_244_ = lean_nat_dec_lt(v___x_242_, v___x_243_);
lean_dec(v___x_242_);
if (v___x_244_ == 0)
{
lean_object* v_ks_245_; lean_object* v_vs_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; 
v_ks_245_ = lean_ctor_get(v_newNode_239_, 0);
lean_inc_ref(v_ks_245_);
v_vs_246_ = lean_ctor_get(v_newNode_239_, 1);
lean_inc_ref(v_vs_246_);
lean_dec_ref(v_newNode_239_);
v___x_247_ = lean_unsigned_to_nat(0u);
v___x_248_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___redArg___closed__0);
v___x_249_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2_spec__5___redArg(v_x_181_, v_ks_245_, v_vs_246_, v___x_247_, v___x_248_);
lean_dec_ref(v_vs_246_);
lean_dec_ref(v_ks_245_);
return v___x_249_;
}
else
{
return v_newNode_239_;
}
}
else
{
return v_newNode_239_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_179_ = stack[0].m_obj;
size_t v_x_180_ = stack[1].m_num;
size_t v_x_181_ = stack[2].m_num;
lean_object* v_x_182_ = stack[3].m_obj;
lean_object* v_x_183_ = stack[4].m_obj;
lean_object* v_res_252_;
v_res_252_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___redArg(v_x_179_, v_x_180_, v_x_181_, v_x_182_, v_x_183_);
stack->m_obj
 = v_res_252_;
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2_spec__5___redArg(size_t v_depth_253_, lean_object* v_keys_254_, lean_object* v_vals_255_, lean_object* v_i_256_, lean_object* v_entries_257_){
_start:
{
lean_object* v___x_258_; uint8_t v___x_259_; 
v___x_258_ = lean_array_get_size(v_keys_254_);
v___x_259_ = lean_nat_dec_lt(v_i_256_, v___x_258_);
if (v___x_259_ == 0)
{
lean_dec(v_i_256_);
return v_entries_257_;
}
else
{
lean_object* v_k_260_; lean_object* v_v_261_; size_t v___x_262_; size_t v___x_263_; size_t v___x_264_; uint64_t v___x_265_; size_t v_h_266_; size_t v___x_267_; lean_object* v___x_268_; size_t v___x_269_; size_t v___x_270_; size_t v___x_271_; size_t v_h_272_; lean_object* v___x_273_; lean_object* v___x_274_; 
v_k_260_ = lean_array_fget_borrowed(v_keys_254_, v_i_256_);
v_v_261_ = lean_array_fget_borrowed(v_vals_255_, v_i_256_);
v___x_262_ = lean_ptr_addr(v_k_260_);
v___x_263_ = ((size_t)3ULL);
v___x_264_ = lean_usize_shift_right(v___x_262_, v___x_263_);
v___x_265_ = lean_usize_to_uint64(v___x_264_);
v_h_266_ = lean_uint64_to_usize(v___x_265_);
v___x_267_ = ((size_t)5ULL);
v___x_268_ = lean_unsigned_to_nat(1u);
v___x_269_ = ((size_t)1ULL);
v___x_270_ = lean_usize_sub(v_depth_253_, v___x_269_);
v___x_271_ = lean_usize_mul(v___x_267_, v___x_270_);
v_h_272_ = lean_usize_shift_right(v_h_266_, v___x_271_);
v___x_273_ = lean_nat_add(v_i_256_, v___x_268_);
lean_dec(v_i_256_);
lean_inc(v_v_261_);
lean_inc(v_k_260_);
v___x_274_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___redArg(v_entries_257_, v_h_272_, v_depth_253_, v_k_260_, v_v_261_);
v_i_256_ = v___x_273_;
v_entries_257_ = v___x_274_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_depth_253_ = stack[0].m_num;
lean_object* v_keys_254_ = stack[1].m_obj;
lean_object* v_vals_255_ = stack[2].m_obj;
lean_object* v_i_256_ = stack[3].m_obj;
lean_object* v_entries_257_ = stack[4].m_obj;
lean_object* v_res_276_;
v_res_276_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2_spec__5___redArg(v_depth_253_, v_keys_254_, v_vals_255_, v_i_256_, v_entries_257_);
stack->m_obj
 = v_res_276_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_depth_277_, lean_object* v_keys_278_, lean_object* v_vals_279_, lean_object* v_i_280_, lean_object* v_entries_281_){
_start:
{
size_t v_depth_boxed_282_; lean_object* v_res_283_; 
v_depth_boxed_282_ = lean_unbox_usize(v_depth_277_);
lean_dec(v_depth_277_);
v_res_283_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2_spec__5___redArg(v_depth_boxed_282_, v_keys_278_, v_vals_279_, v_i_280_, v_entries_281_);
lean_dec_ref(v_vals_279_);
lean_dec_ref(v_keys_278_);
return v_res_283_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___redArg___boxed(lean_object* v_x_284_, lean_object* v_x_285_, lean_object* v_x_286_, lean_object* v_x_287_, lean_object* v_x_288_){
_start:
{
size_t v_x_38425__boxed_289_; size_t v_x_38426__boxed_290_; lean_object* v_res_291_; 
v_x_38425__boxed_289_ = lean_unbox_usize(v_x_285_);
lean_dec(v_x_285_);
v_x_38426__boxed_290_ = lean_unbox_usize(v_x_286_);
lean_dec(v_x_286_);
v_res_291_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___redArg(v_x_284_, v_x_38425__boxed_289_, v_x_38426__boxed_290_, v_x_287_, v_x_288_);
return v_res_291_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1___redArg(lean_object* v_x_292_, lean_object* v_x_293_, lean_object* v_x_294_){
_start:
{
size_t v___x_295_; size_t v___x_296_; size_t v___x_297_; uint64_t v___x_298_; size_t v___x_299_; size_t v___x_300_; lean_object* v___x_301_; 
v___x_295_ = lean_ptr_addr(v_x_293_);
v___x_296_ = ((size_t)3ULL);
v___x_297_ = lean_usize_shift_right(v___x_295_, v___x_296_);
v___x_298_ = lean_usize_to_uint64(v___x_297_);
v___x_299_ = lean_uint64_to_usize(v___x_298_);
v___x_300_ = ((size_t)1ULL);
v___x_301_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___redArg(v_x_292_, v___x_299_, v___x_300_, v_x_293_, v_x_294_);
return v___x_301_;
}
}
lean_object* l_Lean_Meta_Grind_AC_internalize___lam__0(lean_object* v_e_302_, lean_object* v_a_303_, uint8_t v_ac_304_, lean_object* v_s_305_){
_start:
{
lean_object* v_id_306_; lean_object* v_type_307_; lean_object* v_u_308_; lean_object* v_op_309_; lean_object* v_neutral_x3f_310_; lean_object* v_assocInst_311_; lean_object* v_idempotentInst_x3f_312_; lean_object* v_commInst_x3f_313_; lean_object* v_neutralInst_x3f_314_; lean_object* v_nextId_315_; lean_object* v_vars_316_; lean_object* v_varMap_317_; lean_object* v_denote_318_; lean_object* v_denoteEntries_319_; lean_object* v_queue_320_; lean_object* v_basis_321_; lean_object* v_diseqs_322_; lean_object* v___x_324_; uint8_t v_isShared_325_; uint8_t v_isSharedCheck_332_; 
v_id_306_ = lean_ctor_get(v_s_305_, 0);
v_type_307_ = lean_ctor_get(v_s_305_, 1);
v_u_308_ = lean_ctor_get(v_s_305_, 2);
v_op_309_ = lean_ctor_get(v_s_305_, 3);
v_neutral_x3f_310_ = lean_ctor_get(v_s_305_, 4);
v_assocInst_311_ = lean_ctor_get(v_s_305_, 5);
v_idempotentInst_x3f_312_ = lean_ctor_get(v_s_305_, 6);
v_commInst_x3f_313_ = lean_ctor_get(v_s_305_, 7);
v_neutralInst_x3f_314_ = lean_ctor_get(v_s_305_, 8);
v_nextId_315_ = lean_ctor_get(v_s_305_, 9);
v_vars_316_ = lean_ctor_get(v_s_305_, 10);
v_varMap_317_ = lean_ctor_get(v_s_305_, 11);
v_denote_318_ = lean_ctor_get(v_s_305_, 12);
v_denoteEntries_319_ = lean_ctor_get(v_s_305_, 13);
v_queue_320_ = lean_ctor_get(v_s_305_, 14);
v_basis_321_ = lean_ctor_get(v_s_305_, 15);
v_diseqs_322_ = lean_ctor_get(v_s_305_, 16);
v_isSharedCheck_332_ = !lean_is_exclusive(v_s_305_);
if (v_isSharedCheck_332_ == 0)
{
v___x_324_ = v_s_305_;
v_isShared_325_ = v_isSharedCheck_332_;
goto v_resetjp_323_;
}
else
{
lean_inc(v_diseqs_322_);
lean_inc(v_basis_321_);
lean_inc(v_queue_320_);
lean_inc(v_denoteEntries_319_);
lean_inc(v_denote_318_);
lean_inc(v_varMap_317_);
lean_inc(v_vars_316_);
lean_inc(v_nextId_315_);
lean_inc(v_neutralInst_x3f_314_);
lean_inc(v_commInst_x3f_313_);
lean_inc(v_idempotentInst_x3f_312_);
lean_inc(v_assocInst_311_);
lean_inc(v_neutral_x3f_310_);
lean_inc(v_op_309_);
lean_inc(v_u_308_);
lean_inc(v_type_307_);
lean_inc(v_id_306_);
lean_dec(v_s_305_);
v___x_324_ = lean_box(0);
v_isShared_325_ = v_isSharedCheck_332_;
goto v_resetjp_323_;
}
v_resetjp_323_:
{
lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_330_; 
lean_inc_ref(v_a_303_);
lean_inc_ref(v_e_302_);
v___x_326_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1___redArg(v_denote_318_, v_e_302_, v_a_303_);
v___x_327_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_327_, 0, v_e_302_);
lean_ctor_set(v___x_327_, 1, v_a_303_);
v___x_328_ = l_Lean_PersistentArray_push___redArg(v_denoteEntries_319_, v___x_327_);
if (v_isShared_325_ == 0)
{
lean_ctor_set(v___x_324_, 13, v___x_328_);
lean_ctor_set(v___x_324_, 12, v___x_326_);
v___x_330_ = v___x_324_;
goto v_reusejp_329_;
}
else
{
lean_object* v_reuseFailAlloc_331_; 
v_reuseFailAlloc_331_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_331_, 0, v_id_306_);
lean_ctor_set(v_reuseFailAlloc_331_, 1, v_type_307_);
lean_ctor_set(v_reuseFailAlloc_331_, 2, v_u_308_);
lean_ctor_set(v_reuseFailAlloc_331_, 3, v_op_309_);
lean_ctor_set(v_reuseFailAlloc_331_, 4, v_neutral_x3f_310_);
lean_ctor_set(v_reuseFailAlloc_331_, 5, v_assocInst_311_);
lean_ctor_set(v_reuseFailAlloc_331_, 6, v_idempotentInst_x3f_312_);
lean_ctor_set(v_reuseFailAlloc_331_, 7, v_commInst_x3f_313_);
lean_ctor_set(v_reuseFailAlloc_331_, 8, v_neutralInst_x3f_314_);
lean_ctor_set(v_reuseFailAlloc_331_, 9, v_nextId_315_);
lean_ctor_set(v_reuseFailAlloc_331_, 10, v_vars_316_);
lean_ctor_set(v_reuseFailAlloc_331_, 11, v_varMap_317_);
lean_ctor_set(v_reuseFailAlloc_331_, 12, v___x_326_);
lean_ctor_set(v_reuseFailAlloc_331_, 13, v___x_328_);
lean_ctor_set(v_reuseFailAlloc_331_, 14, v_queue_320_);
lean_ctor_set(v_reuseFailAlloc_331_, 15, v_basis_321_);
lean_ctor_set(v_reuseFailAlloc_331_, 16, v_diseqs_322_);
v___x_330_ = v_reuseFailAlloc_331_;
goto v_reusejp_329_;
}
v_reusejp_329_:
{
lean_ctor_set_uint8(v___x_330_, sizeof(void*)*17, v_ac_304_);
return v___x_330_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_AC_internalize___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_302_ = stack[0].m_obj;
lean_object* v_a_303_ = stack[1].m_obj;
uint8_t v_ac_304_ = stack[2].m_num;
lean_object* v_s_305_ = stack[3].m_obj;
lean_object* v_res_333_;
v_res_333_ = l_Lean_Meta_Grind_AC_internalize___lam__0(v_e_302_, v_a_303_, v_ac_304_, v_s_305_);
stack->m_obj
 = v_res_333_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_internalize___lam__0___boxed(lean_object* v_e_334_, lean_object* v_a_335_, lean_object* v_ac_336_, lean_object* v_s_337_){
_start:
{
uint8_t v_ac_boxed_338_; lean_object* v_res_339_; 
v_ac_boxed_338_ = lean_unbox(v_ac_336_);
v_res_339_ = l_Lean_Meta_Grind_AC_internalize___lam__0(v_e_334_, v_a_335_, v_ac_boxed_338_, v_s_337_);
return v_res_339_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3_spec__5(lean_object* v_msgData_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_){
_start:
{
lean_object* v___x_346_; lean_object* v_env_347_; uint8_t v___x_348_; lean_object* v_env_349_; lean_object* v___x_350_; lean_object* v_toCold_351_; lean_object* v_mctx_352_; lean_object* v_lctx_353_; lean_object* v_options_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; 
v___x_346_ = lean_st_ref_get(v___y_344_);
v_env_347_ = lean_ctor_get(v___x_346_, 0);
lean_inc_ref(v_env_347_);
lean_dec(v___x_346_);
v___x_348_ = 0;
v_env_349_ = l_Lean_Environment_setRecordingDeps(v_env_347_, v___x_348_);
v___x_350_ = lean_st_ref_get(v___y_342_);
v_toCold_351_ = lean_ctor_get(v___y_343_, 0);
v_mctx_352_ = lean_ctor_get(v___x_350_, 0);
lean_inc_ref(v_mctx_352_);
lean_dec(v___x_350_);
v_lctx_353_ = lean_ctor_get(v___y_341_, 2);
v_options_354_ = lean_ctor_get(v_toCold_351_, 2);
lean_inc_ref(v_options_354_);
lean_inc_ref(v_lctx_353_);
v___x_355_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_355_, 0, v_env_349_);
lean_ctor_set(v___x_355_, 1, v_mctx_352_);
lean_ctor_set(v___x_355_, 2, v_lctx_353_);
lean_ctor_set(v___x_355_, 3, v_options_354_);
v___x_356_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_356_, 0, v___x_355_);
lean_ctor_set(v___x_356_, 1, v_msgData_340_);
v___x_357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_357_, 0, v___x_356_);
return v___x_357_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_340_ = stack[0].m_obj;
lean_object* v___y_341_ = stack[1].m_obj;
lean_object* v___y_342_ = stack[2].m_obj;
lean_object* v___y_343_ = stack[3].m_obj;
lean_object* v___y_344_ = stack[4].m_obj;
lean_object* v_res_358_;
v_res_358_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3_spec__5(v_msgData_340_, v___y_341_, v___y_342_, v___y_343_, v___y_344_);
stack->m_obj
 = v_res_358_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3_spec__5___boxed(lean_object* v_msgData_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_){
_start:
{
lean_object* v_res_365_; 
v_res_365_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3_spec__5(v_msgData_359_, v___y_360_, v___y_361_, v___y_362_, v___y_363_);
lean_dec(v___y_363_);
lean_dec_ref(v___y_362_);
lean_dec(v___y_361_);
lean_dec_ref(v___y_360_);
return v_res_365_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_366_; double v___x_367_; 
v___x_366_ = lean_unsigned_to_nat(0u);
v___x_367_ = lean_float_of_nat(v___x_366_);
return v___x_367_;
}
}
lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3___redArg(lean_object* v_cls_371_, lean_object* v_msg_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_){
_start:
{
lean_object* v_ref_378_; lean_object* v___x_379_; lean_object* v_a_380_; lean_object* v___x_382_; uint8_t v_isShared_383_; uint8_t v_isSharedCheck_425_; 
v_ref_378_ = lean_ctor_get(v___y_375_, 2);
v___x_379_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3_spec__5(v_msg_372_, v___y_373_, v___y_374_, v___y_375_, v___y_376_);
v_a_380_ = lean_ctor_get(v___x_379_, 0);
v_isSharedCheck_425_ = !lean_is_exclusive(v___x_379_);
if (v_isSharedCheck_425_ == 0)
{
v___x_382_ = v___x_379_;
v_isShared_383_ = v_isSharedCheck_425_;
goto v_resetjp_381_;
}
else
{
lean_inc(v_a_380_);
lean_dec(v___x_379_);
v___x_382_ = lean_box(0);
v_isShared_383_ = v_isSharedCheck_425_;
goto v_resetjp_381_;
}
v_resetjp_381_:
{
lean_object* v___x_384_; lean_object* v_traceState_385_; lean_object* v_env_386_; lean_object* v_nextMacroScope_387_; lean_object* v_ngen_388_; lean_object* v_auxDeclNGen_389_; lean_object* v_cache_390_; lean_object* v_recordedDeps_391_; lean_object* v_messages_392_; lean_object* v_infoState_393_; lean_object* v_snapshotTasks_394_; lean_object* v___x_396_; uint8_t v_isShared_397_; uint8_t v_isSharedCheck_424_; 
v___x_384_ = lean_st_ref_take(v___y_376_);
v_traceState_385_ = lean_ctor_get(v___x_384_, 4);
v_env_386_ = lean_ctor_get(v___x_384_, 0);
v_nextMacroScope_387_ = lean_ctor_get(v___x_384_, 1);
v_ngen_388_ = lean_ctor_get(v___x_384_, 2);
v_auxDeclNGen_389_ = lean_ctor_get(v___x_384_, 3);
v_cache_390_ = lean_ctor_get(v___x_384_, 5);
v_recordedDeps_391_ = lean_ctor_get(v___x_384_, 6);
v_messages_392_ = lean_ctor_get(v___x_384_, 7);
v_infoState_393_ = lean_ctor_get(v___x_384_, 8);
v_snapshotTasks_394_ = lean_ctor_get(v___x_384_, 9);
v_isSharedCheck_424_ = !lean_is_exclusive(v___x_384_);
if (v_isSharedCheck_424_ == 0)
{
v___x_396_ = v___x_384_;
v_isShared_397_ = v_isSharedCheck_424_;
goto v_resetjp_395_;
}
else
{
lean_inc(v_snapshotTasks_394_);
lean_inc(v_infoState_393_);
lean_inc(v_messages_392_);
lean_inc(v_recordedDeps_391_);
lean_inc(v_cache_390_);
lean_inc(v_traceState_385_);
lean_inc(v_auxDeclNGen_389_);
lean_inc(v_ngen_388_);
lean_inc(v_nextMacroScope_387_);
lean_inc(v_env_386_);
lean_dec(v___x_384_);
v___x_396_ = lean_box(0);
v_isShared_397_ = v_isSharedCheck_424_;
goto v_resetjp_395_;
}
v_resetjp_395_:
{
uint64_t v_tid_398_; lean_object* v_traces_399_; lean_object* v___x_401_; uint8_t v_isShared_402_; uint8_t v_isSharedCheck_423_; 
v_tid_398_ = lean_ctor_get_uint64(v_traceState_385_, sizeof(void*)*1);
v_traces_399_ = lean_ctor_get(v_traceState_385_, 0);
v_isSharedCheck_423_ = !lean_is_exclusive(v_traceState_385_);
if (v_isSharedCheck_423_ == 0)
{
v___x_401_ = v_traceState_385_;
v_isShared_402_ = v_isSharedCheck_423_;
goto v_resetjp_400_;
}
else
{
lean_inc(v_traces_399_);
lean_dec(v_traceState_385_);
v___x_401_ = lean_box(0);
v_isShared_402_ = v_isSharedCheck_423_;
goto v_resetjp_400_;
}
v_resetjp_400_:
{
lean_object* v___x_403_; lean_object* v___x_404_; double v___x_405_; uint8_t v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_414_; 
v___x_403_ = lean_box(0);
v___x_404_ = lean_box(0);
v___x_405_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3___redArg___closed__0);
v___x_406_ = 0;
v___x_407_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3___redArg___closed__1));
v___x_408_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_408_, 0, v_cls_371_);
lean_ctor_set(v___x_408_, 1, v___x_404_);
lean_ctor_set(v___x_408_, 2, v___x_407_);
lean_ctor_set_float(v___x_408_, sizeof(void*)*3, v___x_405_);
lean_ctor_set_float(v___x_408_, sizeof(void*)*3 + 8, v___x_405_);
lean_ctor_set_uint8(v___x_408_, sizeof(void*)*3 + 16, v___x_406_);
v___x_409_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3___redArg___closed__2));
v___x_410_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_410_, 0, v___x_408_);
lean_ctor_set(v___x_410_, 1, v_a_380_);
lean_ctor_set(v___x_410_, 2, v___x_409_);
lean_inc(v_ref_378_);
v___x_411_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_411_, 0, v_ref_378_);
lean_ctor_set(v___x_411_, 1, v___x_410_);
v___x_412_ = l_Lean_PersistentArray_push___redArg(v_traces_399_, v___x_411_);
if (v_isShared_402_ == 0)
{
lean_ctor_set(v___x_401_, 0, v___x_412_);
v___x_414_ = v___x_401_;
goto v_reusejp_413_;
}
else
{
lean_object* v_reuseFailAlloc_422_; 
v_reuseFailAlloc_422_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_422_, 0, v___x_412_);
lean_ctor_set_uint64(v_reuseFailAlloc_422_, sizeof(void*)*1, v_tid_398_);
v___x_414_ = v_reuseFailAlloc_422_;
goto v_reusejp_413_;
}
v_reusejp_413_:
{
lean_object* v___x_416_; 
if (v_isShared_397_ == 0)
{
lean_ctor_set(v___x_396_, 4, v___x_414_);
v___x_416_ = v___x_396_;
goto v_reusejp_415_;
}
else
{
lean_object* v_reuseFailAlloc_421_; 
v_reuseFailAlloc_421_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_421_, 0, v_env_386_);
lean_ctor_set(v_reuseFailAlloc_421_, 1, v_nextMacroScope_387_);
lean_ctor_set(v_reuseFailAlloc_421_, 2, v_ngen_388_);
lean_ctor_set(v_reuseFailAlloc_421_, 3, v_auxDeclNGen_389_);
lean_ctor_set(v_reuseFailAlloc_421_, 4, v___x_414_);
lean_ctor_set(v_reuseFailAlloc_421_, 5, v_cache_390_);
lean_ctor_set(v_reuseFailAlloc_421_, 6, v_recordedDeps_391_);
lean_ctor_set(v_reuseFailAlloc_421_, 7, v_messages_392_);
lean_ctor_set(v_reuseFailAlloc_421_, 8, v_infoState_393_);
lean_ctor_set(v_reuseFailAlloc_421_, 9, v_snapshotTasks_394_);
v___x_416_ = v_reuseFailAlloc_421_;
goto v_reusejp_415_;
}
v_reusejp_415_:
{
lean_object* v___x_417_; lean_object* v___x_419_; 
v___x_417_ = lean_st_ref_put(v___y_376_, v___x_416_);
if (v_isShared_383_ == 0)
{
lean_ctor_set(v___x_382_, 0, v___x_403_);
v___x_419_ = v___x_382_;
goto v_reusejp_418_;
}
else
{
lean_object* v_reuseFailAlloc_420_; 
v_reuseFailAlloc_420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_420_, 0, v___x_403_);
v___x_419_ = v_reuseFailAlloc_420_;
goto v_reusejp_418_;
}
v_reusejp_418_:
{
return v___x_419_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_371_ = stack[0].m_obj;
lean_object* v_msg_372_ = stack[1].m_obj;
lean_object* v___y_373_ = stack[2].m_obj;
lean_object* v___y_374_ = stack[3].m_obj;
lean_object* v___y_375_ = stack[4].m_obj;
lean_object* v___y_376_ = stack[5].m_obj;
lean_object* v_res_426_;
v_res_426_ = l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3___redArg(v_cls_371_, v_msg_372_, v___y_373_, v___y_374_, v___y_375_, v___y_376_);
stack->m_obj
 = v_res_426_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3___redArg___boxed(lean_object* v_cls_427_, lean_object* v_msg_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_){
_start:
{
lean_object* v_res_434_; 
v_res_434_ = l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3___redArg(v_cls_427_, v_msg_428_, v___y_429_, v___y_430_, v___y_431_, v___y_432_);
lean_dec(v___y_432_);
lean_dec_ref(v___y_431_);
lean_dec(v___y_430_);
lean_dec_ref(v___y_429_);
return v_res_434_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_435_, lean_object* v_i_436_, lean_object* v_k_437_){
_start:
{
lean_object* v___x_438_; uint8_t v___x_439_; 
v___x_438_ = lean_array_get_size(v_keys_435_);
v___x_439_ = lean_nat_dec_lt(v_i_436_, v___x_438_);
if (v___x_439_ == 0)
{
lean_dec(v_i_436_);
return v___x_439_;
}
else
{
lean_object* v_k_x27_440_; size_t v___x_441_; size_t v___x_442_; uint8_t v___x_443_; 
v_k_x27_440_ = lean_array_fget_borrowed(v_keys_435_, v_i_436_);
v___x_441_ = lean_ptr_addr(v_k_437_);
v___x_442_ = lean_ptr_addr(v_k_x27_440_);
v___x_443_ = lean_usize_dec_eq(v___x_441_, v___x_442_);
if (v___x_443_ == 0)
{
lean_object* v___x_444_; lean_object* v___x_445_; 
v___x_444_ = lean_unsigned_to_nat(1u);
v___x_445_ = lean_nat_add(v_i_436_, v___x_444_);
lean_dec(v_i_436_);
v_i_436_ = v___x_445_;
goto _start;
}
else
{
lean_dec(v_i_436_);
return v___x_439_;
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_keys_435_ = stack[0].m_obj;
lean_object* v_i_436_ = stack[1].m_obj;
lean_object* v_k_437_ = stack[2].m_obj;
uint8_t v_res_447_;
v_res_447_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0_spec__1___redArg(v_keys_435_, v_i_436_, v_k_437_);
stack->m_num = v_res_447_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_448_, lean_object* v_i_449_, lean_object* v_k_450_){
_start:
{
uint8_t v_res_451_; lean_object* v_r_452_; 
v_res_451_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0_spec__1___redArg(v_keys_448_, v_i_449_, v_k_450_);
lean_dec_ref(v_k_450_);
lean_dec_ref(v_keys_448_);
v_r_452_ = lean_box(v_res_451_);
return v_r_452_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0___redArg(lean_object* v_x_453_, size_t v_x_454_, lean_object* v_x_455_){
_start:
{
if (lean_obj_tag(v_x_453_) == 0)
{
lean_object* v_es_456_; lean_object* v___x_457_; size_t v___x_458_; size_t v___x_459_; lean_object* v_j_460_; lean_object* v___x_461_; 
v_es_456_ = lean_ctor_get(v_x_453_, 0);
v___x_457_ = lean_box(2);
v___x_458_ = ((size_t)31ULL);
v___x_459_ = lean_usize_land(v_x_454_, v___x_458_);
v_j_460_ = lean_usize_to_nat(v___x_459_);
v___x_461_ = lean_array_get_borrowed(v___x_457_, v_es_456_, v_j_460_);
lean_dec(v_j_460_);
switch(lean_obj_tag(v___x_461_))
{
case 0:
{
lean_object* v_key_462_; size_t v___x_463_; size_t v___x_464_; uint8_t v___x_465_; 
v_key_462_ = lean_ctor_get(v___x_461_, 0);
v___x_463_ = lean_ptr_addr(v_x_455_);
v___x_464_ = lean_ptr_addr(v_key_462_);
v___x_465_ = lean_usize_dec_eq(v___x_463_, v___x_464_);
return v___x_465_;
}
case 1:
{
lean_object* v_node_466_; size_t v___x_467_; size_t v___x_468_; 
v_node_466_ = lean_ctor_get(v___x_461_, 0);
v___x_467_ = ((size_t)5ULL);
v___x_468_ = lean_usize_shift_right(v_x_454_, v___x_467_);
v_x_453_ = v_node_466_;
v_x_454_ = v___x_468_;
goto _start;
}
default: 
{
uint8_t v___x_470_; 
v___x_470_ = 0;
return v___x_470_;
}
}
}
else
{
lean_object* v_ks_471_; lean_object* v___x_472_; uint8_t v___x_473_; 
v_ks_471_ = lean_ctor_get(v_x_453_, 0);
v___x_472_ = lean_unsigned_to_nat(0u);
v___x_473_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0_spec__1___redArg(v_ks_471_, v___x_472_, v_x_455_);
return v___x_473_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_453_ = stack[0].m_obj;
size_t v_x_454_ = stack[1].m_num;
lean_object* v_x_455_ = stack[2].m_obj;
uint8_t v_res_474_;
v_res_474_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0___redArg(v_x_453_, v_x_454_, v_x_455_);
stack->m_num = v_res_474_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0___redArg___boxed(lean_object* v_x_475_, lean_object* v_x_476_, lean_object* v_x_477_){
_start:
{
size_t v_x_38956__boxed_478_; uint8_t v_res_479_; lean_object* v_r_480_; 
v_x_38956__boxed_478_ = lean_unbox_usize(v_x_476_);
lean_dec(v_x_476_);
v_res_479_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0___redArg(v_x_475_, v_x_38956__boxed_478_, v_x_477_);
lean_dec_ref(v_x_477_);
lean_dec_ref(v_x_475_);
v_r_480_ = lean_box(v_res_479_);
return v_r_480_;
}
}
uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0___redArg(lean_object* v_x_481_, lean_object* v_x_482_){
_start:
{
size_t v___x_483_; size_t v___x_484_; size_t v___x_485_; uint64_t v___x_486_; size_t v___x_487_; uint8_t v___x_488_; 
v___x_483_ = lean_ptr_addr(v_x_482_);
v___x_484_ = ((size_t)3ULL);
v___x_485_ = lean_usize_shift_right(v___x_483_, v___x_484_);
v___x_486_ = lean_usize_to_uint64(v___x_485_);
v___x_487_ = lean_uint64_to_usize(v___x_486_);
v___x_488_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0___redArg(v_x_481_, v___x_487_, v_x_482_);
return v___x_488_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_481_ = stack[0].m_obj;
lean_object* v_x_482_ = stack[1].m_obj;
uint8_t v_res_489_;
v_res_489_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0___redArg(v_x_481_, v_x_482_);
stack->m_num = v_res_489_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0___redArg___boxed(lean_object* v_x_490_, lean_object* v_x_491_){
_start:
{
uint8_t v_res_492_; lean_object* v_r_493_; 
v_res_492_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0___redArg(v_x_490_, v_x_491_);
lean_dec_ref(v_x_491_);
lean_dec_ref(v_x_490_);
v_r_493_ = lean_box(v_res_492_);
return v_r_493_;
}
}
lean_object* l_Lean_Grind_AC_Expr_denoteExpr___at___00Lean_Meta_Grind_AC_internalize_spec__2(lean_object* v_e_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_){
_start:
{
if (lean_obj_tag(v_e_494_) == 0)
{
lean_object* v_x_507_; lean_object* v___x_508_; lean_object* v___x_509_; 
v_x_507_ = lean_ctor_get(v_e_494_, 0);
v___x_508_ = l_Lean_instInhabitedExpr;
v___x_509_ = l_Lean_Meta_Grind_AC_ACM_getStruct(v___y_495_, v___y_496_, v___y_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_, v___y_504_, v___y_505_);
if (lean_obj_tag(v___x_509_) == 0)
{
lean_object* v_a_510_; lean_object* v___x_512_; uint8_t v_isShared_513_; uint8_t v_isSharedCheck_525_; 
v_a_510_ = lean_ctor_get(v___x_509_, 0);
v_isSharedCheck_525_ = !lean_is_exclusive(v___x_509_);
if (v_isSharedCheck_525_ == 0)
{
v___x_512_ = v___x_509_;
v_isShared_513_ = v_isSharedCheck_525_;
goto v_resetjp_511_;
}
else
{
lean_inc(v_a_510_);
lean_dec(v___x_509_);
v___x_512_ = lean_box(0);
v_isShared_513_ = v_isSharedCheck_525_;
goto v_resetjp_511_;
}
v_resetjp_511_:
{
lean_object* v_vars_514_; lean_object* v_size_515_; uint8_t v___x_516_; 
v_vars_514_ = lean_ctor_get(v_a_510_, 10);
lean_inc_ref(v_vars_514_);
lean_dec(v_a_510_);
v_size_515_ = lean_ctor_get(v_vars_514_, 2);
v___x_516_ = lean_nat_dec_lt(v_x_507_, v_size_515_);
if (v___x_516_ == 0)
{
lean_object* v___x_517_; lean_object* v___x_519_; 
lean_dec_ref(v_vars_514_);
v___x_517_ = l_outOfBounds___redArg(v___x_508_);
if (v_isShared_513_ == 0)
{
lean_ctor_set(v___x_512_, 0, v___x_517_);
v___x_519_ = v___x_512_;
goto v_reusejp_518_;
}
else
{
lean_object* v_reuseFailAlloc_520_; 
v_reuseFailAlloc_520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_520_, 0, v___x_517_);
v___x_519_ = v_reuseFailAlloc_520_;
goto v_reusejp_518_;
}
v_reusejp_518_:
{
return v___x_519_;
}
}
else
{
lean_object* v___x_521_; lean_object* v___x_523_; 
v___x_521_ = l_Lean_PersistentArray_get_x21___redArg(v___x_508_, v_vars_514_, v_x_507_);
lean_dec_ref(v_vars_514_);
if (v_isShared_513_ == 0)
{
lean_ctor_set(v___x_512_, 0, v___x_521_);
v___x_523_ = v___x_512_;
goto v_reusejp_522_;
}
else
{
lean_object* v_reuseFailAlloc_524_; 
v_reuseFailAlloc_524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_524_, 0, v___x_521_);
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
v_a_526_ = lean_ctor_get(v___x_509_, 0);
v_isSharedCheck_533_ = !lean_is_exclusive(v___x_509_);
if (v_isSharedCheck_533_ == 0)
{
v___x_528_ = v___x_509_;
v_isShared_529_ = v_isSharedCheck_533_;
goto v_resetjp_527_;
}
else
{
lean_inc(v_a_526_);
lean_dec(v___x_509_);
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
lean_object* v_lhs_534_; lean_object* v_rhs_535_; lean_object* v___x_536_; 
v_lhs_534_ = lean_ctor_get(v_e_494_, 0);
v_rhs_535_ = lean_ctor_get(v_e_494_, 1);
v___x_536_ = l_Lean_Meta_Grind_AC_ACM_getStruct(v___y_495_, v___y_496_, v___y_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_, v___y_504_, v___y_505_);
if (lean_obj_tag(v___x_536_) == 0)
{
lean_object* v_a_537_; lean_object* v___x_538_; 
v_a_537_ = lean_ctor_get(v___x_536_, 0);
lean_inc(v_a_537_);
lean_dec_ref_known(v___x_536_, 1);
v___x_538_ = l_Lean_Grind_AC_Expr_denoteExpr___at___00Lean_Meta_Grind_AC_internalize_spec__2(v_lhs_534_, v___y_495_, v___y_496_, v___y_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_, v___y_504_, v___y_505_);
if (lean_obj_tag(v___x_538_) == 0)
{
lean_object* v_a_539_; lean_object* v___x_540_; 
v_a_539_ = lean_ctor_get(v___x_538_, 0);
lean_inc(v_a_539_);
lean_dec_ref_known(v___x_538_, 1);
v___x_540_ = l_Lean_Grind_AC_Expr_denoteExpr___at___00Lean_Meta_Grind_AC_internalize_spec__2(v_rhs_535_, v___y_495_, v___y_496_, v___y_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_, v___y_504_, v___y_505_);
if (lean_obj_tag(v___x_540_) == 0)
{
lean_object* v_a_541_; lean_object* v___x_543_; uint8_t v_isShared_544_; uint8_t v_isSharedCheck_550_; 
v_a_541_ = lean_ctor_get(v___x_540_, 0);
v_isSharedCheck_550_ = !lean_is_exclusive(v___x_540_);
if (v_isSharedCheck_550_ == 0)
{
v___x_543_ = v___x_540_;
v_isShared_544_ = v_isSharedCheck_550_;
goto v_resetjp_542_;
}
else
{
lean_inc(v_a_541_);
lean_dec(v___x_540_);
v___x_543_ = lean_box(0);
v_isShared_544_ = v_isSharedCheck_550_;
goto v_resetjp_542_;
}
v_resetjp_542_:
{
lean_object* v_op_545_; lean_object* v___x_546_; lean_object* v___x_548_; 
v_op_545_ = lean_ctor_get(v_a_537_, 3);
lean_inc_ref(v_op_545_);
lean_dec(v_a_537_);
v___x_546_ = l_Lean_mkAppB(v_op_545_, v_a_539_, v_a_541_);
if (v_isShared_544_ == 0)
{
lean_ctor_set(v___x_543_, 0, v___x_546_);
v___x_548_ = v___x_543_;
goto v_reusejp_547_;
}
else
{
lean_object* v_reuseFailAlloc_549_; 
v_reuseFailAlloc_549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_549_, 0, v___x_546_);
v___x_548_ = v_reuseFailAlloc_549_;
goto v_reusejp_547_;
}
v_reusejp_547_:
{
return v___x_548_;
}
}
}
else
{
lean_dec(v_a_539_);
lean_dec(v_a_537_);
return v___x_540_;
}
}
else
{
lean_dec(v_a_537_);
return v___x_538_;
}
}
else
{
lean_object* v_a_551_; lean_object* v___x_553_; uint8_t v_isShared_554_; uint8_t v_isSharedCheck_558_; 
v_a_551_ = lean_ctor_get(v___x_536_, 0);
v_isSharedCheck_558_ = !lean_is_exclusive(v___x_536_);
if (v_isSharedCheck_558_ == 0)
{
v___x_553_ = v___x_536_;
v_isShared_554_ = v_isSharedCheck_558_;
goto v_resetjp_552_;
}
else
{
lean_inc(v_a_551_);
lean_dec(v___x_536_);
v___x_553_ = lean_box(0);
v_isShared_554_ = v_isSharedCheck_558_;
goto v_resetjp_552_;
}
v_resetjp_552_:
{
lean_object* v___x_556_; 
if (v_isShared_554_ == 0)
{
v___x_556_ = v___x_553_;
goto v_reusejp_555_;
}
else
{
lean_object* v_reuseFailAlloc_557_; 
v_reuseFailAlloc_557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_557_, 0, v_a_551_);
v___x_556_ = v_reuseFailAlloc_557_;
goto v_reusejp_555_;
}
v_reusejp_555_:
{
return v___x_556_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Grind_AC_Expr_denoteExpr___at___00Lean_Meta_Grind_AC_internalize_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_494_ = stack[0].m_obj;
lean_object* v___y_495_ = stack[1].m_obj;
lean_object* v___y_496_ = stack[2].m_obj;
lean_object* v___y_497_ = stack[3].m_obj;
lean_object* v___y_498_ = stack[4].m_obj;
lean_object* v___y_499_ = stack[5].m_obj;
lean_object* v___y_500_ = stack[6].m_obj;
lean_object* v___y_501_ = stack[7].m_obj;
lean_object* v___y_502_ = stack[8].m_obj;
lean_object* v___y_503_ = stack[9].m_obj;
lean_object* v___y_504_ = stack[10].m_obj;
lean_object* v___y_505_ = stack[11].m_obj;
lean_object* v_res_559_;
v_res_559_ = l_Lean_Grind_AC_Expr_denoteExpr___at___00Lean_Meta_Grind_AC_internalize_spec__2(v_e_494_, v___y_495_, v___y_496_, v___y_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_, v___y_504_, v___y_505_);
stack->m_obj
 = v_res_559_;
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Expr_denoteExpr___at___00Lean_Meta_Grind_AC_internalize_spec__2___boxed(lean_object* v_e_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_){
_start:
{
lean_object* v_res_573_; 
v_res_573_ = l_Lean_Grind_AC_Expr_denoteExpr___at___00Lean_Meta_Grind_AC_internalize_spec__2(v_e_560_, v___y_561_, v___y_562_, v___y_563_, v___y_564_, v___y_565_, v___y_566_, v___y_567_, v___y_568_, v___y_569_, v___y_570_, v___y_571_);
lean_dec(v___y_571_);
lean_dec_ref(v___y_570_);
lean_dec(v___y_569_);
lean_dec_ref(v___y_568_);
lean_dec(v___y_567_);
lean_dec_ref(v___y_566_);
lean_dec(v___y_565_);
lean_dec_ref(v___y_564_);
lean_dec(v___y_563_);
lean_dec(v___y_562_);
lean_dec(v___y_561_);
lean_dec_ref(v_e_560_);
return v_res_573_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_AC_internalize___closed__6(void){
_start:
{
lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; 
v___x_584_ = ((lean_object*)(l_Lean_Meta_Grind_AC_internalize___closed__3));
v___x_585_ = ((lean_object*)(l_Lean_Meta_Grind_AC_internalize___closed__5));
v___x_586_ = l_Lean_Name_append(v___x_585_, v___x_584_);
return v___x_586_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_AC_internalize___closed__8(void){
_start:
{
lean_object* v___x_588_; lean_object* v___x_589_; 
v___x_588_ = ((lean_object*)(l_Lean_Meta_Grind_AC_internalize___closed__7));
v___x_589_ = l_Lean_stringToMessageData(v___x_588_);
return v___x_589_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_AC_internalize___closed__10(void){
_start:
{
lean_object* v___x_591_; lean_object* v___x_592_; 
v___x_591_ = ((lean_object*)(l_Lean_Meta_Grind_AC_internalize___closed__9));
v___x_592_ = l_Lean_stringToMessageData(v___x_591_);
return v___x_592_;
}
}
lean_object* l_Lean_Meta_Grind_AC_internalize(lean_object* v_e_593_, lean_object* v_parent_x3f_594_, lean_object* v_a_595_, lean_object* v_a_596_, lean_object* v_a_597_, lean_object* v_a_598_, lean_object* v_a_599_, lean_object* v_a_600_, lean_object* v_a_601_, lean_object* v_a_602_, lean_object* v_a_603_, lean_object* v_a_604_){
_start:
{
lean_object* v___y_607_; lean_object* v___y_608_; lean_object* v___y_609_; lean_object* v___y_610_; lean_object* v___y_611_; lean_object* v___y_612_; lean_object* v___y_613_; lean_object* v___y_614_; lean_object* v___y_615_; lean_object* v___y_616_; lean_object* v___y_617_; lean_object* v___x_621_; 
v___x_621_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_597_);
if (lean_obj_tag(v___x_621_) == 0)
{
lean_object* v_a_622_; lean_object* v___x_624_; uint8_t v_isShared_625_; uint8_t v_isSharedCheck_737_; 
v_a_622_ = lean_ctor_get(v___x_621_, 0);
v_isSharedCheck_737_ = !lean_is_exclusive(v___x_621_);
if (v_isSharedCheck_737_ == 0)
{
v___x_624_ = v___x_621_;
v_isShared_625_ = v_isSharedCheck_737_;
goto v_resetjp_623_;
}
else
{
lean_inc(v_a_622_);
lean_dec(v___x_621_);
v___x_624_ = lean_box(0);
v_isShared_625_ = v_isSharedCheck_737_;
goto v_resetjp_623_;
}
v_resetjp_623_:
{
uint8_t v_ac_626_; uint8_t v___y_628_; 
v_ac_626_ = lean_ctor_get_uint8(v_a_622_, sizeof(void*)*14 + 25);
lean_dec(v_a_622_);
if (v_ac_626_ == 0)
{
lean_object* v___x_732_; lean_object* v___x_733_; 
lean_del_object(v___x_624_);
lean_dec(v_parent_x3f_594_);
lean_dec_ref(v_e_593_);
v___x_732_ = lean_box(0);
v___x_733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_733_, 0, v___x_732_);
return v___x_733_;
}
else
{
uint8_t v___x_734_; 
v___x_734_ = l_Lean_Expr_isApp(v_e_593_);
if (v___x_734_ == 0)
{
v___y_628_ = v___x_734_;
goto v___jp_627_;
}
else
{
lean_object* v___x_735_; uint8_t v___x_736_; 
v___x_735_ = l_Lean_Expr_appFn_x21(v_e_593_);
v___x_736_ = l_Lean_Expr_isApp(v___x_735_);
lean_dec_ref(v___x_735_);
v___y_628_ = v___x_736_;
goto v___jp_627_;
}
}
v___jp_627_:
{
if (v___y_628_ == 0)
{
lean_object* v___x_629_; lean_object* v___x_631_; 
lean_dec(v_parent_x3f_594_);
lean_dec_ref(v_e_593_);
v___x_629_ = lean_box(0);
if (v_isShared_625_ == 0)
{
lean_ctor_set(v___x_624_, 0, v___x_629_);
v___x_631_ = v___x_624_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_632_; 
v_reuseFailAlloc_632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_632_, 0, v___x_629_);
v___x_631_ = v_reuseFailAlloc_632_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
return v___x_631_;
}
}
else
{
lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; 
lean_del_object(v___x_624_);
v___x_633_ = l_Lean_Expr_appFn_x21(v_e_593_);
v___x_634_ = l_Lean_Expr_appFn_x21(v___x_633_);
lean_dec_ref(v___x_633_);
lean_inc_ref(v___x_634_);
v___x_635_ = l_Lean_Meta_Grind_AC_getOpId_x3f(v___x_634_, v_a_595_, v_a_596_, v_a_597_, v_a_598_, v_a_599_, v_a_600_, v_a_601_, v_a_602_, v_a_603_, v_a_604_);
if (lean_obj_tag(v___x_635_) == 0)
{
lean_object* v_a_636_; lean_object* v___x_638_; uint8_t v_isShared_639_; uint8_t v_isSharedCheck_723_; 
v_a_636_ = lean_ctor_get(v___x_635_, 0);
v_isSharedCheck_723_ = !lean_is_exclusive(v___x_635_);
if (v_isSharedCheck_723_ == 0)
{
v___x_638_ = v___x_635_;
v_isShared_639_ = v_isSharedCheck_723_;
goto v_resetjp_637_;
}
else
{
lean_inc(v_a_636_);
lean_dec(v___x_635_);
v___x_638_ = lean_box(0);
v_isShared_639_ = v_isSharedCheck_723_;
goto v_resetjp_637_;
}
v_resetjp_637_:
{
if (lean_obj_tag(v_a_636_) == 1)
{
lean_object* v_val_640_; lean_object* v___x_641_; lean_object* v_a_642_; lean_object* v___x_644_; uint8_t v_isShared_645_; uint8_t v_isSharedCheck_718_; 
lean_del_object(v___x_638_);
v_val_640_ = lean_ctor_get(v_a_636_, 0);
lean_inc(v_val_640_);
lean_dec_ref_known(v_a_636_, 1);
v___x_641_ = l___private_Lean_Meta_Tactic_Grind_AC_Internalize_0__Lean_Meta_Grind_AC_isParentSameOpApp___redArg(v_parent_x3f_594_, v___x_634_);
lean_dec_ref(v___x_634_);
v_a_642_ = lean_ctor_get(v___x_641_, 0);
v_isSharedCheck_718_ = !lean_is_exclusive(v___x_641_);
if (v_isSharedCheck_718_ == 0)
{
v___x_644_ = v___x_641_;
v_isShared_645_ = v_isSharedCheck_718_;
goto v_resetjp_643_;
}
else
{
lean_inc(v_a_642_);
lean_dec(v___x_641_);
v___x_644_ = lean_box(0);
v_isShared_645_ = v_isSharedCheck_718_;
goto v_resetjp_643_;
}
v_resetjp_643_:
{
uint8_t v___x_646_; 
v___x_646_ = lean_unbox(v_a_642_);
lean_dec(v_a_642_);
if (v___x_646_ == 0)
{
lean_object* v___x_647_; 
lean_del_object(v___x_644_);
v___x_647_ = l_Lean_Meta_Grind_AC_ACM_getStruct(v_val_640_, v_a_595_, v_a_596_, v_a_597_, v_a_598_, v_a_599_, v_a_600_, v_a_601_, v_a_602_, v_a_603_, v_a_604_);
if (lean_obj_tag(v___x_647_) == 0)
{
lean_object* v_a_648_; lean_object* v___x_650_; uint8_t v_isShared_651_; uint8_t v_isSharedCheck_705_; 
v_a_648_ = lean_ctor_get(v___x_647_, 0);
v_isSharedCheck_705_ = !lean_is_exclusive(v___x_647_);
if (v_isSharedCheck_705_ == 0)
{
v___x_650_ = v___x_647_;
v_isShared_651_ = v_isSharedCheck_705_;
goto v_resetjp_649_;
}
else
{
lean_inc(v_a_648_);
lean_dec(v___x_647_);
v___x_650_ = lean_box(0);
v_isShared_651_ = v_isSharedCheck_705_;
goto v_resetjp_649_;
}
v_resetjp_649_:
{
lean_object* v_denote_652_; uint8_t v___x_653_; 
v_denote_652_ = lean_ctor_get(v_a_648_, 12);
lean_inc_ref(v_denote_652_);
lean_dec(v_a_648_);
v___x_653_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0___redArg(v_denote_652_, v_e_593_);
lean_dec_ref(v_denote_652_);
if (v___x_653_ == 0)
{
lean_object* v___x_654_; 
lean_del_object(v___x_650_);
lean_inc_ref(v_e_593_);
v___x_654_ = l_Lean_Meta_Grind_AC_reify(v_e_593_, v_val_640_, v_a_595_, v_a_596_, v_a_597_, v_a_598_, v_a_599_, v_a_600_, v_a_601_, v_a_602_, v_a_603_, v_a_604_);
if (lean_obj_tag(v___x_654_) == 0)
{
lean_object* v_a_655_; lean_object* v___x_656_; lean_object* v___f_657_; lean_object* v___x_658_; 
v_a_655_ = lean_ctor_get(v___x_654_, 0);
lean_inc_n(v_a_655_, 2);
lean_dec_ref_known(v___x_654_, 1);
v___x_656_ = lean_box(v_ac_626_);
lean_inc_ref(v_e_593_);
v___f_657_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_AC_internalize___lam__0___boxed), 4, 3);
lean_closure_set(v___f_657_, 0, v_e_593_);
lean_closure_set(v___f_657_, 1, v_a_655_);
lean_closure_set(v___f_657_, 2, v___x_656_);
v___x_658_ = l_Lean_Meta_Grind_AC_modifyStruct___redArg(v___f_657_, v_val_640_, v_a_595_);
if (lean_obj_tag(v___x_658_) == 0)
{
lean_object* v___x_660_; uint8_t v_isShared_661_; uint8_t v_isSharedCheck_691_; 
v_isSharedCheck_691_ = !lean_is_exclusive(v___x_658_);
if (v_isSharedCheck_691_ == 0)
{
lean_object* v_unused_692_; 
v_unused_692_ = lean_ctor_get(v___x_658_, 0);
lean_dec(v_unused_692_);
v___x_660_ = v___x_658_;
v_isShared_661_ = v_isSharedCheck_691_;
goto v_resetjp_659_;
}
else
{
lean_dec(v___x_658_);
v___x_660_ = lean_box(0);
v_isShared_661_ = v_isSharedCheck_691_;
goto v_resetjp_659_;
}
v_resetjp_659_:
{
lean_object* v_toCold_662_; lean_object* v_options_663_; uint8_t v_hasTrace_664_; 
v_toCold_662_ = lean_ctor_get(v_a_603_, 0);
v_options_663_ = lean_ctor_get(v_toCold_662_, 2);
v_hasTrace_664_ = lean_ctor_get_uint8(v_options_663_, sizeof(void*)*1);
if (v_hasTrace_664_ == 0)
{
lean_del_object(v___x_660_);
lean_dec(v_a_655_);
v___y_607_ = v_val_640_;
v___y_608_ = v_a_595_;
v___y_609_ = v_a_596_;
v___y_610_ = v_a_597_;
v___y_611_ = v_a_598_;
v___y_612_ = v_a_599_;
v___y_613_ = v_a_600_;
v___y_614_ = v_a_601_;
v___y_615_ = v_a_602_;
v___y_616_ = v_a_603_;
v___y_617_ = v_a_604_;
goto v___jp_606_;
}
else
{
lean_object* v_inheritedTraceOptions_665_; lean_object* v___x_666_; lean_object* v___x_667_; uint8_t v___x_668_; 
v_inheritedTraceOptions_665_ = lean_ctor_get(v_toCold_662_, 11);
v___x_666_ = ((lean_object*)(l_Lean_Meta_Grind_AC_internalize___closed__3));
v___x_667_ = lean_obj_once(&l_Lean_Meta_Grind_AC_internalize___closed__6, &l_Lean_Meta_Grind_AC_internalize___closed__6_once, _init_l_Lean_Meta_Grind_AC_internalize___closed__6);
v___x_668_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_665_, v_options_663_, v___x_667_);
if (v___x_668_ == 0)
{
lean_del_object(v___x_660_);
lean_dec(v_a_655_);
v___y_607_ = v_val_640_;
v___y_608_ = v_a_595_;
v___y_609_ = v_a_596_;
v___y_610_ = v_a_597_;
v___y_611_ = v_a_598_;
v___y_612_ = v_a_599_;
v___y_613_ = v_a_600_;
v___y_614_ = v_a_601_;
v___y_615_ = v_a_602_;
v___y_616_ = v_a_603_;
v___y_617_ = v_a_604_;
goto v___jp_606_;
}
else
{
lean_object* v___x_669_; 
v___x_669_ = l_Lean_Grind_AC_Expr_denoteExpr___at___00Lean_Meta_Grind_AC_internalize_spec__2(v_a_655_, v_val_640_, v_a_595_, v_a_596_, v_a_597_, v_a_598_, v_a_599_, v_a_600_, v_a_601_, v_a_602_, v_a_603_, v_a_604_);
lean_dec(v_a_655_);
if (lean_obj_tag(v___x_669_) == 0)
{
lean_object* v_a_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_674_; 
v_a_670_ = lean_ctor_get(v___x_669_, 0);
lean_inc(v_a_670_);
lean_dec_ref_known(v___x_669_, 1);
v___x_671_ = lean_obj_once(&l_Lean_Meta_Grind_AC_internalize___closed__8, &l_Lean_Meta_Grind_AC_internalize___closed__8_once, _init_l_Lean_Meta_Grind_AC_internalize___closed__8);
lean_inc(v_val_640_);
v___x_672_ = l_Nat_reprFast(v_val_640_);
if (v_isShared_661_ == 0)
{
lean_ctor_set_tag(v___x_660_, 3);
lean_ctor_set(v___x_660_, 0, v___x_672_);
v___x_674_ = v___x_660_;
goto v_reusejp_673_;
}
else
{
lean_object* v_reuseFailAlloc_682_; 
v_reuseFailAlloc_682_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_682_, 0, v___x_672_);
v___x_674_ = v_reuseFailAlloc_682_;
goto v_reusejp_673_;
}
v_reusejp_673_:
{
lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; 
v___x_675_ = l_Lean_MessageData_ofFormat(v___x_674_);
v___x_676_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_676_, 0, v___x_671_);
lean_ctor_set(v___x_676_, 1, v___x_675_);
v___x_677_ = lean_obj_once(&l_Lean_Meta_Grind_AC_internalize___closed__10, &l_Lean_Meta_Grind_AC_internalize___closed__10_once, _init_l_Lean_Meta_Grind_AC_internalize___closed__10);
v___x_678_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_678_, 0, v___x_676_);
lean_ctor_set(v___x_678_, 1, v___x_677_);
v___x_679_ = l_Lean_MessageData_ofExpr(v_a_670_);
v___x_680_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_680_, 0, v___x_678_);
lean_ctor_set(v___x_680_, 1, v___x_679_);
v___x_681_ = l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3___redArg(v___x_666_, v___x_680_, v_a_601_, v_a_602_, v_a_603_, v_a_604_);
if (lean_obj_tag(v___x_681_) == 0)
{
lean_dec_ref_known(v___x_681_, 1);
v___y_607_ = v_val_640_;
v___y_608_ = v_a_595_;
v___y_609_ = v_a_596_;
v___y_610_ = v_a_597_;
v___y_611_ = v_a_598_;
v___y_612_ = v_a_599_;
v___y_613_ = v_a_600_;
v___y_614_ = v_a_601_;
v___y_615_ = v_a_602_;
v___y_616_ = v_a_603_;
v___y_617_ = v_a_604_;
goto v___jp_606_;
}
else
{
lean_dec(v_val_640_);
lean_dec_ref(v_e_593_);
return v___x_681_;
}
}
}
else
{
lean_object* v_a_683_; lean_object* v___x_685_; uint8_t v_isShared_686_; uint8_t v_isSharedCheck_690_; 
lean_del_object(v___x_660_);
lean_dec(v_val_640_);
lean_dec_ref(v_e_593_);
v_a_683_ = lean_ctor_get(v___x_669_, 0);
v_isSharedCheck_690_ = !lean_is_exclusive(v___x_669_);
if (v_isSharedCheck_690_ == 0)
{
v___x_685_ = v___x_669_;
v_isShared_686_ = v_isSharedCheck_690_;
goto v_resetjp_684_;
}
else
{
lean_inc(v_a_683_);
lean_dec(v___x_669_);
v___x_685_ = lean_box(0);
v_isShared_686_ = v_isSharedCheck_690_;
goto v_resetjp_684_;
}
v_resetjp_684_:
{
lean_object* v___x_688_; 
if (v_isShared_686_ == 0)
{
v___x_688_ = v___x_685_;
goto v_reusejp_687_;
}
else
{
lean_object* v_reuseFailAlloc_689_; 
v_reuseFailAlloc_689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_689_, 0, v_a_683_);
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
}
}
}
else
{
lean_dec(v_a_655_);
lean_dec(v_val_640_);
lean_dec_ref(v_e_593_);
return v___x_658_;
}
}
else
{
lean_object* v_a_693_; lean_object* v___x_695_; uint8_t v_isShared_696_; uint8_t v_isSharedCheck_700_; 
lean_dec(v_val_640_);
lean_dec_ref(v_e_593_);
v_a_693_ = lean_ctor_get(v___x_654_, 0);
v_isSharedCheck_700_ = !lean_is_exclusive(v___x_654_);
if (v_isSharedCheck_700_ == 0)
{
v___x_695_ = v___x_654_;
v_isShared_696_ = v_isSharedCheck_700_;
goto v_resetjp_694_;
}
else
{
lean_inc(v_a_693_);
lean_dec(v___x_654_);
v___x_695_ = lean_box(0);
v_isShared_696_ = v_isSharedCheck_700_;
goto v_resetjp_694_;
}
v_resetjp_694_:
{
lean_object* v___x_698_; 
if (v_isShared_696_ == 0)
{
v___x_698_ = v___x_695_;
goto v_reusejp_697_;
}
else
{
lean_object* v_reuseFailAlloc_699_; 
v_reuseFailAlloc_699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_699_, 0, v_a_693_);
v___x_698_ = v_reuseFailAlloc_699_;
goto v_reusejp_697_;
}
v_reusejp_697_:
{
return v___x_698_;
}
}
}
}
else
{
lean_object* v___x_701_; lean_object* v___x_703_; 
lean_dec(v_val_640_);
lean_dec_ref(v_e_593_);
v___x_701_ = lean_box(0);
if (v_isShared_651_ == 0)
{
lean_ctor_set(v___x_650_, 0, v___x_701_);
v___x_703_ = v___x_650_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v___x_701_);
v___x_703_ = v_reuseFailAlloc_704_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
return v___x_703_;
}
}
}
}
else
{
lean_object* v_a_706_; lean_object* v___x_708_; uint8_t v_isShared_709_; uint8_t v_isSharedCheck_713_; 
lean_dec(v_val_640_);
lean_dec_ref(v_e_593_);
v_a_706_ = lean_ctor_get(v___x_647_, 0);
v_isSharedCheck_713_ = !lean_is_exclusive(v___x_647_);
if (v_isSharedCheck_713_ == 0)
{
v___x_708_ = v___x_647_;
v_isShared_709_ = v_isSharedCheck_713_;
goto v_resetjp_707_;
}
else
{
lean_inc(v_a_706_);
lean_dec(v___x_647_);
v___x_708_ = lean_box(0);
v_isShared_709_ = v_isSharedCheck_713_;
goto v_resetjp_707_;
}
v_resetjp_707_:
{
lean_object* v___x_711_; 
if (v_isShared_709_ == 0)
{
v___x_711_ = v___x_708_;
goto v_reusejp_710_;
}
else
{
lean_object* v_reuseFailAlloc_712_; 
v_reuseFailAlloc_712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_712_, 0, v_a_706_);
v___x_711_ = v_reuseFailAlloc_712_;
goto v_reusejp_710_;
}
v_reusejp_710_:
{
return v___x_711_;
}
}
}
}
else
{
lean_object* v___x_714_; lean_object* v___x_716_; 
lean_dec(v_val_640_);
lean_dec_ref(v_e_593_);
v___x_714_ = lean_box(0);
if (v_isShared_645_ == 0)
{
lean_ctor_set(v___x_644_, 0, v___x_714_);
v___x_716_ = v___x_644_;
goto v_reusejp_715_;
}
else
{
lean_object* v_reuseFailAlloc_717_; 
v_reuseFailAlloc_717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_717_, 0, v___x_714_);
v___x_716_ = v_reuseFailAlloc_717_;
goto v_reusejp_715_;
}
v_reusejp_715_:
{
return v___x_716_;
}
}
}
}
else
{
lean_object* v___x_719_; lean_object* v___x_721_; 
lean_dec(v_a_636_);
lean_dec_ref(v___x_634_);
lean_dec(v_parent_x3f_594_);
lean_dec_ref(v_e_593_);
v___x_719_ = lean_box(0);
if (v_isShared_639_ == 0)
{
lean_ctor_set(v___x_638_, 0, v___x_719_);
v___x_721_ = v___x_638_;
goto v_reusejp_720_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v___x_719_);
v___x_721_ = v_reuseFailAlloc_722_;
goto v_reusejp_720_;
}
v_reusejp_720_:
{
return v___x_721_;
}
}
}
}
else
{
lean_object* v_a_724_; lean_object* v___x_726_; uint8_t v_isShared_727_; uint8_t v_isSharedCheck_731_; 
lean_dec_ref(v___x_634_);
lean_dec(v_parent_x3f_594_);
lean_dec_ref(v_e_593_);
v_a_724_ = lean_ctor_get(v___x_635_, 0);
v_isSharedCheck_731_ = !lean_is_exclusive(v___x_635_);
if (v_isSharedCheck_731_ == 0)
{
v___x_726_ = v___x_635_;
v_isShared_727_ = v_isSharedCheck_731_;
goto v_resetjp_725_;
}
else
{
lean_inc(v_a_724_);
lean_dec(v___x_635_);
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
}
}
}
}
else
{
lean_object* v_a_738_; lean_object* v___x_740_; uint8_t v_isShared_741_; uint8_t v_isSharedCheck_745_; 
lean_dec(v_parent_x3f_594_);
lean_dec_ref(v_e_593_);
v_a_738_ = lean_ctor_get(v___x_621_, 0);
v_isSharedCheck_745_ = !lean_is_exclusive(v___x_621_);
if (v_isSharedCheck_745_ == 0)
{
v___x_740_ = v___x_621_;
v_isShared_741_ = v_isSharedCheck_745_;
goto v_resetjp_739_;
}
else
{
lean_inc(v_a_738_);
lean_dec(v___x_621_);
v___x_740_ = lean_box(0);
v_isShared_741_ = v_isSharedCheck_745_;
goto v_resetjp_739_;
}
v_resetjp_739_:
{
lean_object* v___x_743_; 
if (v_isShared_741_ == 0)
{
v___x_743_ = v___x_740_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v_a_738_);
v___x_743_ = v_reuseFailAlloc_744_;
goto v_reusejp_742_;
}
v_reusejp_742_:
{
return v___x_743_;
}
}
}
v___jp_606_:
{
lean_object* v___x_618_; 
lean_inc_ref(v_e_593_);
v___x_618_ = l_Lean_Meta_Grind_AC_addTermOpId___redArg(v_e_593_, v___y_607_, v___y_608_);
lean_dec(v___y_607_);
if (lean_obj_tag(v___x_618_) == 0)
{
lean_object* v___x_619_; lean_object* v___x_620_; 
lean_dec_ref_known(v___x_618_, 1);
v___x_619_ = l_Lean_Meta_Grind_AC_acExt;
v___x_620_ = l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(v___x_619_, v_e_593_, v___y_608_, v___y_609_, v___y_610_, v___y_611_, v___y_612_, v___y_613_, v___y_614_, v___y_615_, v___y_616_, v___y_617_);
return v___x_620_;
}
else
{
lean_dec_ref(v_e_593_);
return v___x_618_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_AC_internalize_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_593_ = stack[0].m_obj;
lean_object* v_parent_x3f_594_ = stack[1].m_obj;
lean_object* v_a_595_ = stack[2].m_obj;
lean_object* v_a_596_ = stack[3].m_obj;
lean_object* v_a_597_ = stack[4].m_obj;
lean_object* v_a_598_ = stack[5].m_obj;
lean_object* v_a_599_ = stack[6].m_obj;
lean_object* v_a_600_ = stack[7].m_obj;
lean_object* v_a_601_ = stack[8].m_obj;
lean_object* v_a_602_ = stack[9].m_obj;
lean_object* v_a_603_ = stack[10].m_obj;
lean_object* v_a_604_ = stack[11].m_obj;
lean_object* v_res_746_;
v_res_746_ = l_Lean_Meta_Grind_AC_internalize(v_e_593_, v_parent_x3f_594_, v_a_595_, v_a_596_, v_a_597_, v_a_598_, v_a_599_, v_a_600_, v_a_601_, v_a_602_, v_a_603_, v_a_604_);
stack->m_obj
 = v_res_746_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_internalize___boxed(lean_object* v_e_747_, lean_object* v_parent_x3f_748_, lean_object* v_a_749_, lean_object* v_a_750_, lean_object* v_a_751_, lean_object* v_a_752_, lean_object* v_a_753_, lean_object* v_a_754_, lean_object* v_a_755_, lean_object* v_a_756_, lean_object* v_a_757_, lean_object* v_a_758_, lean_object* v_a_759_){
_start:
{
lean_object* v_res_760_; 
v_res_760_ = l_Lean_Meta_Grind_AC_internalize(v_e_747_, v_parent_x3f_748_, v_a_749_, v_a_750_, v_a_751_, v_a_752_, v_a_753_, v_a_754_, v_a_755_, v_a_756_, v_a_757_, v_a_758_);
lean_dec(v_a_758_);
lean_dec_ref(v_a_757_);
lean_dec(v_a_756_);
lean_dec_ref(v_a_755_);
lean_dec(v_a_754_);
lean_dec_ref(v_a_753_);
lean_dec(v_a_752_);
lean_dec_ref(v_a_751_);
lean_dec(v_a_750_);
lean_dec(v_a_749_);
return v_res_760_;
}
}
uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0(lean_object* v_00_u03b2_761_, lean_object* v_x_762_, lean_object* v_x_763_){
_start:
{
uint8_t v___x_764_; 
v___x_764_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0___redArg(v_x_762_, v_x_763_);
return v___x_764_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_762_ = stack[1].m_obj;
lean_object* v_x_763_ = stack[2].m_obj;
uint8_t v_res_765_;
v_res_765_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0(lean_box(0), v_x_762_, v_x_763_);
stack->m_num = v_res_765_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0___boxed(lean_object* v_00_u03b2_766_, lean_object* v_x_767_, lean_object* v_x_768_){
_start:
{
uint8_t v_res_769_; lean_object* v_r_770_; 
v_res_769_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0(v_00_u03b2_766_, v_x_767_, v_x_768_);
lean_dec_ref(v_x_768_);
lean_dec_ref(v_x_767_);
v_r_770_ = lean_box(v_res_769_);
return v_r_770_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1(lean_object* v_00_u03b2_771_, lean_object* v_x_772_, lean_object* v_x_773_, lean_object* v_x_774_){
_start:
{
lean_object* v___x_775_; 
v___x_775_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1___redArg(v_x_772_, v_x_773_, v_x_774_);
return v___x_775_;
}
}
lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3(lean_object* v_cls_776_, lean_object* v_msg_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_){
_start:
{
lean_object* v___x_790_; 
v___x_790_ = l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3___redArg(v_cls_776_, v_msg_777_, v___y_785_, v___y_786_, v___y_787_, v___y_788_);
return v___x_790_;
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_776_ = stack[0].m_obj;
lean_object* v_msg_777_ = stack[1].m_obj;
lean_object* v___y_778_ = stack[2].m_obj;
lean_object* v___y_779_ = stack[3].m_obj;
lean_object* v___y_780_ = stack[4].m_obj;
lean_object* v___y_781_ = stack[5].m_obj;
lean_object* v___y_782_ = stack[6].m_obj;
lean_object* v___y_783_ = stack[7].m_obj;
lean_object* v___y_784_ = stack[8].m_obj;
lean_object* v___y_785_ = stack[9].m_obj;
lean_object* v___y_786_ = stack[10].m_obj;
lean_object* v___y_787_ = stack[11].m_obj;
lean_object* v___y_788_ = stack[12].m_obj;
lean_object* v_res_791_;
v_res_791_ = l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3(v_cls_776_, v_msg_777_, v___y_778_, v___y_779_, v___y_780_, v___y_781_, v___y_782_, v___y_783_, v___y_784_, v___y_785_, v___y_786_, v___y_787_, v___y_788_);
stack->m_obj
 = v_res_791_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3___boxed(lean_object* v_cls_792_, lean_object* v_msg_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_){
_start:
{
lean_object* v_res_806_; 
v_res_806_ = l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3(v_cls_792_, v_msg_793_, v___y_794_, v___y_795_, v___y_796_, v___y_797_, v___y_798_, v___y_799_, v___y_800_, v___y_801_, v___y_802_, v___y_803_, v___y_804_);
lean_dec(v___y_804_);
lean_dec_ref(v___y_803_);
lean_dec(v___y_802_);
lean_dec_ref(v___y_801_);
lean_dec(v___y_800_);
lean_dec_ref(v___y_799_);
lean_dec(v___y_798_);
lean_dec_ref(v___y_797_);
lean_dec(v___y_796_);
lean_dec(v___y_795_);
lean_dec(v___y_794_);
return v_res_806_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0(lean_object* v_00_u03b2_807_, lean_object* v_x_808_, size_t v_x_809_, lean_object* v_x_810_){
_start:
{
uint8_t v___x_811_; 
v___x_811_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0___redArg(v_x_808_, v_x_809_, v_x_810_);
return v___x_811_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_808_ = stack[1].m_obj;
size_t v_x_809_ = stack[2].m_num;
lean_object* v_x_810_ = stack[3].m_obj;
uint8_t v_res_812_;
v_res_812_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0(lean_box(0), v_x_808_, v_x_809_, v_x_810_);
stack->m_num = v_res_812_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0___boxed(lean_object* v_00_u03b2_813_, lean_object* v_x_814_, lean_object* v_x_815_, lean_object* v_x_816_){
_start:
{
size_t v_x_39838__boxed_817_; uint8_t v_res_818_; lean_object* v_r_819_; 
v_x_39838__boxed_817_ = lean_unbox_usize(v_x_815_);
lean_dec(v_x_815_);
v_res_818_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0(v_00_u03b2_813_, v_x_814_, v_x_39838__boxed_817_, v_x_816_);
lean_dec_ref(v_x_816_);
lean_dec_ref(v_x_814_);
v_r_819_ = lean_box(v_res_818_);
return v_r_819_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2(lean_object* v_00_u03b2_820_, lean_object* v_x_821_, size_t v_x_822_, size_t v_x_823_, lean_object* v_x_824_, lean_object* v_x_825_){
_start:
{
lean_object* v___x_826_; 
v___x_826_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___redArg(v_x_821_, v_x_822_, v_x_823_, v_x_824_, v_x_825_);
return v___x_826_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_821_ = stack[1].m_obj;
size_t v_x_822_ = stack[2].m_num;
size_t v_x_823_ = stack[3].m_num;
lean_object* v_x_824_ = stack[4].m_obj;
lean_object* v_x_825_ = stack[5].m_obj;
lean_object* v_res_827_;
v_res_827_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2(lean_box(0), v_x_821_, v_x_822_, v_x_823_, v_x_824_, v_x_825_);
stack->m_obj
 = v_res_827_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___boxed(lean_object* v_00_u03b2_828_, lean_object* v_x_829_, lean_object* v_x_830_, lean_object* v_x_831_, lean_object* v_x_832_, lean_object* v_x_833_){
_start:
{
size_t v_x_39856__boxed_834_; size_t v_x_39857__boxed_835_; lean_object* v_res_836_; 
v_x_39856__boxed_834_ = lean_unbox_usize(v_x_830_);
lean_dec(v_x_830_);
v_x_39857__boxed_835_ = lean_unbox_usize(v_x_831_);
lean_dec(v_x_831_);
v_res_836_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2(v_00_u03b2_828_, v_x_829_, v_x_39856__boxed_834_, v_x_39857__boxed_835_, v_x_832_, v_x_833_);
return v_res_836_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_837_, lean_object* v_keys_838_, lean_object* v_vals_839_, lean_object* v_heq_840_, lean_object* v_i_841_, lean_object* v_k_842_){
_start:
{
uint8_t v___x_843_; 
v___x_843_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0_spec__1___redArg(v_keys_838_, v_i_841_, v_k_842_);
return v___x_843_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_keys_838_ = stack[1].m_obj;
lean_object* v_vals_839_ = stack[2].m_obj;
lean_object* v_i_841_ = stack[4].m_obj;
lean_object* v_k_842_ = stack[5].m_obj;
uint8_t v_res_844_;
v_res_844_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0_spec__1(lean_box(0), v_keys_838_, v_vals_839_, lean_box(0), v_i_841_, v_k_842_);
stack->m_num = v_res_844_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_845_, lean_object* v_keys_846_, lean_object* v_vals_847_, lean_object* v_heq_848_, lean_object* v_i_849_, lean_object* v_k_850_){
_start:
{
uint8_t v_res_851_; lean_object* v_r_852_; 
v_res_851_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0_spec__1(v_00_u03b2_845_, v_keys_846_, v_vals_847_, v_heq_848_, v_i_849_, v_k_850_);
lean_dec_ref(v_k_850_);
lean_dec_ref(v_vals_847_);
lean_dec_ref(v_keys_846_);
v_r_852_ = lean_box(v_res_851_);
return v_r_852_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_853_, lean_object* v_n_854_, lean_object* v_k_855_, lean_object* v_v_856_){
_start:
{
lean_object* v___x_857_; 
v___x_857_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2_spec__4___redArg(v_n_854_, v_k_855_, v_v_856_);
return v___x_857_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_858_, size_t v_depth_859_, lean_object* v_keys_860_, lean_object* v_vals_861_, lean_object* v_heq_862_, lean_object* v_i_863_, lean_object* v_entries_864_){
_start:
{
lean_object* v___x_865_; 
v___x_865_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2_spec__5___redArg(v_depth_859_, v_keys_860_, v_vals_861_, v_i_863_, v_entries_864_);
return v___x_865_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2_spec__5_0interp(lean_interpreter_value* stack)
{
size_t v_depth_859_ = stack[1].m_num;
lean_object* v_keys_860_ = stack[2].m_obj;
lean_object* v_vals_861_ = stack[3].m_obj;
lean_object* v_i_863_ = stack[5].m_obj;
lean_object* v_entries_864_ = stack[6].m_obj;
lean_object* v_res_866_;
v_res_866_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2_spec__5(lean_box(0), v_depth_859_, v_keys_860_, v_vals_861_, lean_box(0), v_i_863_, v_entries_864_);
stack->m_obj
 = v_res_866_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_867_, lean_object* v_depth_868_, lean_object* v_keys_869_, lean_object* v_vals_870_, lean_object* v_heq_871_, lean_object* v_i_872_, lean_object* v_entries_873_){
_start:
{
size_t v_depth_boxed_874_; lean_object* v_res_875_; 
v_depth_boxed_874_ = lean_unbox_usize(v_depth_868_);
lean_dec(v_depth_868_);
v_res_875_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2_spec__5(v_00_u03b2_867_, v_depth_boxed_874_, v_keys_869_, v_vals_870_, v_heq_871_, v_i_872_, v_entries_873_);
lean_dec_ref(v_vals_870_);
lean_dec_ref(v_keys_869_);
return v_res_875_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2_spec__4_spec__8(lean_object* v_00_u03b2_876_, lean_object* v_x_877_, lean_object* v_x_878_, lean_object* v_x_879_, lean_object* v_x_880_){
_start:
{
lean_object* v___x_881_; 
v___x_881_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2_spec__4_spec__8___redArg(v_x_877_, v_x_878_, v_x_879_, v_x_880_);
return v___x_881_;
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
