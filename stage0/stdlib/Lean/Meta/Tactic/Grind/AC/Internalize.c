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
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Internalize_0__Lean_Meta_Grind_AC_isParentSameOpApp___redArg(lean_object* v_parent_x3f_1_, lean_object* v_op_2_){
_start:
{
if (lean_obj_tag(v_parent_x3f_1_) == 1)
{
lean_object* v_val_4_; lean_object* v___x_6_; uint8_t v_isShared_7_; uint8_t v_isSharedCheck_27_; 
v_val_4_ = lean_ctor_get(v_parent_x3f_1_, 0);
v_isSharedCheck_27_ = !lean_is_exclusive(v_parent_x3f_1_);
if (v_isSharedCheck_27_ == 0)
{
v___x_6_ = v_parent_x3f_1_;
v_isShared_7_ = v_isSharedCheck_27_;
goto v_resetjp_5_;
}
else
{
lean_inc(v_val_4_);
lean_dec(v_parent_x3f_1_);
v___x_6_ = lean_box(0);
v_isShared_7_ = v_isSharedCheck_27_;
goto v_resetjp_5_;
}
v_resetjp_5_:
{
uint8_t v___x_8_; 
v___x_8_ = l_Lean_Expr_isApp(v_val_4_);
if (v___x_8_ == 0)
{
lean_object* v___x_9_; lean_object* v___x_11_; 
lean_dec(v_val_4_);
v___x_9_ = lean_box(v___x_8_);
if (v_isShared_7_ == 0)
{
lean_ctor_set_tag(v___x_6_, 0);
lean_ctor_set(v___x_6_, 0, v___x_9_);
v___x_11_ = v___x_6_;
goto v_reusejp_10_;
}
else
{
lean_object* v_reuseFailAlloc_12_; 
v_reuseFailAlloc_12_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_12_, 0, v___x_9_);
v___x_11_ = v_reuseFailAlloc_12_;
goto v_reusejp_10_;
}
v_reusejp_10_:
{
return v___x_11_;
}
}
else
{
lean_object* v___x_13_; uint8_t v___x_14_; 
v___x_13_ = l_Lean_Expr_appFn_x21(v_val_4_);
lean_dec(v_val_4_);
v___x_14_ = l_Lean_Expr_isApp(v___x_13_);
if (v___x_14_ == 0)
{
lean_object* v___x_15_; lean_object* v___x_17_; 
lean_dec_ref(v___x_13_);
v___x_15_ = lean_box(v___x_14_);
if (v_isShared_7_ == 0)
{
lean_ctor_set_tag(v___x_6_, 0);
lean_ctor_set(v___x_6_, 0, v___x_15_);
v___x_17_ = v___x_6_;
goto v_reusejp_16_;
}
else
{
lean_object* v_reuseFailAlloc_18_; 
v_reuseFailAlloc_18_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_18_, 0, v___x_15_);
v___x_17_ = v_reuseFailAlloc_18_;
goto v_reusejp_16_;
}
v_reusejp_16_:
{
return v___x_17_;
}
}
else
{
lean_object* v___x_19_; size_t v___x_20_; size_t v___x_21_; uint8_t v___x_22_; lean_object* v___x_23_; lean_object* v___x_25_; 
v___x_19_ = l_Lean_Expr_appFn_x21(v___x_13_);
lean_dec_ref(v___x_13_);
v___x_20_ = lean_ptr_addr(v___x_19_);
lean_dec_ref(v___x_19_);
v___x_21_ = lean_ptr_addr(v_op_2_);
v___x_22_ = lean_usize_dec_eq(v___x_20_, v___x_21_);
v___x_23_ = lean_box(v___x_22_);
if (v_isShared_7_ == 0)
{
lean_ctor_set_tag(v___x_6_, 0);
lean_ctor_set(v___x_6_, 0, v___x_23_);
v___x_25_ = v___x_6_;
goto v_reusejp_24_;
}
else
{
lean_object* v_reuseFailAlloc_26_; 
v_reuseFailAlloc_26_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_26_, 0, v___x_23_);
v___x_25_ = v_reuseFailAlloc_26_;
goto v_reusejp_24_;
}
v_reusejp_24_:
{
return v___x_25_;
}
}
}
}
}
else
{
uint8_t v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; 
lean_dec(v_parent_x3f_1_);
v___x_28_ = 0;
v___x_29_ = lean_box(v___x_28_);
v___x_30_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_30_, 0, v___x_29_);
return v___x_30_;
}
}
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Internalize_0__Lean_Meta_Grind_AC_isParentSameOpApp(lean_object* v_parent_x3f_35_, lean_object* v_op_36_, lean_object* v_a_37_, lean_object* v_a_38_, lean_object* v_a_39_, lean_object* v_a_40_, lean_object* v_a_41_, lean_object* v_a_42_, lean_object* v_a_43_, lean_object* v_a_44_, lean_object* v_a_45_, lean_object* v_a_46_){
_start:
{
lean_object* v___x_48_; 
v___x_48_ = l___private_Lean_Meta_Tactic_Grind_AC_Internalize_0__Lean_Meta_Grind_AC_isParentSameOpApp___redArg(v_parent_x3f_35_, v_op_36_);
return v___x_48_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Internalize_0__Lean_Meta_Grind_AC_isParentSameOpApp___boxed(lean_object* v_parent_x3f_49_, lean_object* v_op_50_, lean_object* v_a_51_, lean_object* v_a_52_, lean_object* v_a_53_, lean_object* v_a_54_, lean_object* v_a_55_, lean_object* v_a_56_, lean_object* v_a_57_, lean_object* v_a_58_, lean_object* v_a_59_, lean_object* v_a_60_, lean_object* v_a_61_){
_start:
{
lean_object* v_res_62_; 
v_res_62_ = l___private_Lean_Meta_Tactic_Grind_AC_Internalize_0__Lean_Meta_Grind_AC_isParentSameOpApp(v_parent_x3f_49_, v_op_50_, v_a_51_, v_a_52_, v_a_53_, v_a_54_, v_a_55_, v_a_56_, v_a_57_, v_a_58_, v_a_59_, v_a_60_);
lean_dec(v_a_60_);
lean_dec_ref(v_a_59_);
lean_dec(v_a_58_);
lean_dec_ref(v_a_57_);
lean_dec(v_a_56_);
lean_dec_ref(v_a_55_);
lean_dec(v_a_54_);
lean_dec_ref(v_a_53_);
lean_dec(v_a_52_);
lean_dec(v_a_51_);
lean_dec_ref(v_op_50_);
return v_res_62_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_reify(lean_object* v_e_63_, lean_object* v_a_64_, lean_object* v_a_65_, lean_object* v_a_66_, lean_object* v_a_67_, lean_object* v_a_68_, lean_object* v_a_69_, lean_object* v_a_70_, lean_object* v_a_71_, lean_object* v_a_72_, lean_object* v_a_73_, lean_object* v_a_74_){
_start:
{
lean_object* v___x_76_; 
v___x_76_ = l_Lean_Meta_Grind_AC_isOp_x3f(v_e_63_, v_a_64_, v_a_65_, v_a_66_, v_a_67_, v_a_68_, v_a_69_, v_a_70_, v_a_71_, v_a_72_, v_a_73_, v_a_74_);
if (lean_obj_tag(v___x_76_) == 0)
{
lean_object* v_a_77_; 
v_a_77_ = lean_ctor_get(v___x_76_, 0);
lean_inc(v_a_77_);
lean_dec_ref_known(v___x_76_, 1);
if (lean_obj_tag(v_a_77_) == 1)
{
lean_object* v_val_78_; lean_object* v_fst_79_; lean_object* v_snd_80_; lean_object* v___x_82_; uint8_t v_isShared_83_; uint8_t v_isSharedCheck_98_; 
lean_dec_ref(v_e_63_);
v_val_78_ = lean_ctor_get(v_a_77_, 0);
lean_inc(v_val_78_);
lean_dec_ref_known(v_a_77_, 1);
v_fst_79_ = lean_ctor_get(v_val_78_, 0);
v_snd_80_ = lean_ctor_get(v_val_78_, 1);
v_isSharedCheck_98_ = !lean_is_exclusive(v_val_78_);
if (v_isSharedCheck_98_ == 0)
{
v___x_82_ = v_val_78_;
v_isShared_83_ = v_isSharedCheck_98_;
goto v_resetjp_81_;
}
else
{
lean_inc(v_snd_80_);
lean_inc(v_fst_79_);
lean_dec(v_val_78_);
v___x_82_ = lean_box(0);
v_isShared_83_ = v_isSharedCheck_98_;
goto v_resetjp_81_;
}
v_resetjp_81_:
{
lean_object* v___x_84_; 
v___x_84_ = l_Lean_Meta_Grind_AC_reify(v_fst_79_, v_a_64_, v_a_65_, v_a_66_, v_a_67_, v_a_68_, v_a_69_, v_a_70_, v_a_71_, v_a_72_, v_a_73_, v_a_74_);
if (lean_obj_tag(v___x_84_) == 0)
{
lean_object* v_a_85_; lean_object* v___x_86_; 
v_a_85_ = lean_ctor_get(v___x_84_, 0);
lean_inc(v_a_85_);
lean_dec_ref_known(v___x_84_, 1);
v___x_86_ = l_Lean_Meta_Grind_AC_reify(v_snd_80_, v_a_64_, v_a_65_, v_a_66_, v_a_67_, v_a_68_, v_a_69_, v_a_70_, v_a_71_, v_a_72_, v_a_73_, v_a_74_);
if (lean_obj_tag(v___x_86_) == 0)
{
lean_object* v_a_87_; lean_object* v___x_89_; uint8_t v_isShared_90_; uint8_t v_isSharedCheck_97_; 
v_a_87_ = lean_ctor_get(v___x_86_, 0);
v_isSharedCheck_97_ = !lean_is_exclusive(v___x_86_);
if (v_isSharedCheck_97_ == 0)
{
v___x_89_ = v___x_86_;
v_isShared_90_ = v_isSharedCheck_97_;
goto v_resetjp_88_;
}
else
{
lean_inc(v_a_87_);
lean_dec(v___x_86_);
v___x_89_ = lean_box(0);
v_isShared_90_ = v_isSharedCheck_97_;
goto v_resetjp_88_;
}
v_resetjp_88_:
{
lean_object* v___x_92_; 
if (v_isShared_83_ == 0)
{
lean_ctor_set_tag(v___x_82_, 1);
lean_ctor_set(v___x_82_, 1, v_a_87_);
lean_ctor_set(v___x_82_, 0, v_a_85_);
v___x_92_ = v___x_82_;
goto v_reusejp_91_;
}
else
{
lean_object* v_reuseFailAlloc_96_; 
v_reuseFailAlloc_96_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_96_, 0, v_a_85_);
lean_ctor_set(v_reuseFailAlloc_96_, 1, v_a_87_);
v___x_92_ = v_reuseFailAlloc_96_;
goto v_reusejp_91_;
}
v_reusejp_91_:
{
lean_object* v___x_94_; 
if (v_isShared_90_ == 0)
{
lean_ctor_set(v___x_89_, 0, v___x_92_);
v___x_94_ = v___x_89_;
goto v_reusejp_93_;
}
else
{
lean_object* v_reuseFailAlloc_95_; 
v_reuseFailAlloc_95_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_95_, 0, v___x_92_);
v___x_94_ = v_reuseFailAlloc_95_;
goto v_reusejp_93_;
}
v_reusejp_93_:
{
return v___x_94_;
}
}
}
}
else
{
lean_dec(v_a_85_);
lean_del_object(v___x_82_);
return v___x_86_;
}
}
else
{
lean_del_object(v___x_82_);
lean_dec(v_snd_80_);
return v___x_84_;
}
}
}
else
{
lean_object* v___x_99_; 
lean_dec(v_a_77_);
v___x_99_ = l_Lean_Meta_Grind_AC_mkVar(v_e_63_, v_a_64_, v_a_65_, v_a_66_, v_a_67_, v_a_68_, v_a_69_, v_a_70_, v_a_71_, v_a_72_, v_a_73_, v_a_74_);
if (lean_obj_tag(v___x_99_) == 0)
{
lean_object* v_a_100_; lean_object* v___x_102_; uint8_t v_isShared_103_; uint8_t v_isSharedCheck_108_; 
v_a_100_ = lean_ctor_get(v___x_99_, 0);
v_isSharedCheck_108_ = !lean_is_exclusive(v___x_99_);
if (v_isSharedCheck_108_ == 0)
{
v___x_102_ = v___x_99_;
v_isShared_103_ = v_isSharedCheck_108_;
goto v_resetjp_101_;
}
else
{
lean_inc(v_a_100_);
lean_dec(v___x_99_);
v___x_102_ = lean_box(0);
v_isShared_103_ = v_isSharedCheck_108_;
goto v_resetjp_101_;
}
v_resetjp_101_:
{
lean_object* v___x_104_; lean_object* v___x_106_; 
v___x_104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_104_, 0, v_a_100_);
if (v_isShared_103_ == 0)
{
lean_ctor_set(v___x_102_, 0, v___x_104_);
v___x_106_ = v___x_102_;
goto v_reusejp_105_;
}
else
{
lean_object* v_reuseFailAlloc_107_; 
v_reuseFailAlloc_107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_107_, 0, v___x_104_);
v___x_106_ = v_reuseFailAlloc_107_;
goto v_reusejp_105_;
}
v_reusejp_105_:
{
return v___x_106_;
}
}
}
else
{
lean_object* v_a_109_; lean_object* v___x_111_; uint8_t v_isShared_112_; uint8_t v_isSharedCheck_116_; 
v_a_109_ = lean_ctor_get(v___x_99_, 0);
v_isSharedCheck_116_ = !lean_is_exclusive(v___x_99_);
if (v_isSharedCheck_116_ == 0)
{
v___x_111_ = v___x_99_;
v_isShared_112_ = v_isSharedCheck_116_;
goto v_resetjp_110_;
}
else
{
lean_inc(v_a_109_);
lean_dec(v___x_99_);
v___x_111_ = lean_box(0);
v_isShared_112_ = v_isSharedCheck_116_;
goto v_resetjp_110_;
}
v_resetjp_110_:
{
lean_object* v___x_114_; 
if (v_isShared_112_ == 0)
{
v___x_114_ = v___x_111_;
goto v_reusejp_113_;
}
else
{
lean_object* v_reuseFailAlloc_115_; 
v_reuseFailAlloc_115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_115_, 0, v_a_109_);
v___x_114_ = v_reuseFailAlloc_115_;
goto v_reusejp_113_;
}
v_reusejp_113_:
{
return v___x_114_;
}
}
}
}
}
else
{
lean_object* v_a_117_; lean_object* v___x_119_; uint8_t v_isShared_120_; uint8_t v_isSharedCheck_124_; 
lean_dec_ref(v_e_63_);
v_a_117_ = lean_ctor_get(v___x_76_, 0);
v_isSharedCheck_124_ = !lean_is_exclusive(v___x_76_);
if (v_isSharedCheck_124_ == 0)
{
v___x_119_ = v___x_76_;
v_isShared_120_ = v_isSharedCheck_124_;
goto v_resetjp_118_;
}
else
{
lean_inc(v_a_117_);
lean_dec(v___x_76_);
v___x_119_ = lean_box(0);
v_isShared_120_ = v_isSharedCheck_124_;
goto v_resetjp_118_;
}
v_resetjp_118_:
{
lean_object* v___x_122_; 
if (v_isShared_120_ == 0)
{
v___x_122_ = v___x_119_;
goto v_reusejp_121_;
}
else
{
lean_object* v_reuseFailAlloc_123_; 
v_reuseFailAlloc_123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_123_, 0, v_a_117_);
v___x_122_ = v_reuseFailAlloc_123_;
goto v_reusejp_121_;
}
v_reusejp_121_:
{
return v___x_122_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_reify___boxed(lean_object* v_e_125_, lean_object* v_a_126_, lean_object* v_a_127_, lean_object* v_a_128_, lean_object* v_a_129_, lean_object* v_a_130_, lean_object* v_a_131_, lean_object* v_a_132_, lean_object* v_a_133_, lean_object* v_a_134_, lean_object* v_a_135_, lean_object* v_a_136_, lean_object* v_a_137_){
_start:
{
lean_object* v_res_138_; 
v_res_138_ = l_Lean_Meta_Grind_AC_reify(v_e_125_, v_a_126_, v_a_127_, v_a_128_, v_a_129_, v_a_130_, v_a_131_, v_a_132_, v_a_133_, v_a_134_, v_a_135_, v_a_136_);
lean_dec(v_a_136_);
lean_dec_ref(v_a_135_);
lean_dec(v_a_134_);
lean_dec_ref(v_a_133_);
lean_dec(v_a_132_);
lean_dec_ref(v_a_131_);
lean_dec(v_a_130_);
lean_dec_ref(v_a_129_);
lean_dec(v_a_128_);
lean_dec(v_a_127_);
lean_dec(v_a_126_);
return v_res_138_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2_spec__4_spec__8___redArg(lean_object* v_x_139_, lean_object* v_x_140_, lean_object* v_x_141_, lean_object* v_x_142_){
_start:
{
lean_object* v_ks_143_; lean_object* v_vs_144_; lean_object* v___x_146_; uint8_t v_isShared_147_; uint8_t v_isSharedCheck_170_; 
v_ks_143_ = lean_ctor_get(v_x_139_, 0);
v_vs_144_ = lean_ctor_get(v_x_139_, 1);
v_isSharedCheck_170_ = !lean_is_exclusive(v_x_139_);
if (v_isSharedCheck_170_ == 0)
{
v___x_146_ = v_x_139_;
v_isShared_147_ = v_isSharedCheck_170_;
goto v_resetjp_145_;
}
else
{
lean_inc(v_vs_144_);
lean_inc(v_ks_143_);
lean_dec(v_x_139_);
v___x_146_ = lean_box(0);
v_isShared_147_ = v_isSharedCheck_170_;
goto v_resetjp_145_;
}
v_resetjp_145_:
{
lean_object* v___x_148_; uint8_t v___x_149_; 
v___x_148_ = lean_array_get_size(v_ks_143_);
v___x_149_ = lean_nat_dec_lt(v_x_140_, v___x_148_);
if (v___x_149_ == 0)
{
lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_153_; 
lean_dec(v_x_140_);
v___x_150_ = lean_array_push(v_ks_143_, v_x_141_);
v___x_151_ = lean_array_push(v_vs_144_, v_x_142_);
if (v_isShared_147_ == 0)
{
lean_ctor_set(v___x_146_, 1, v___x_151_);
lean_ctor_set(v___x_146_, 0, v___x_150_);
v___x_153_ = v___x_146_;
goto v_reusejp_152_;
}
else
{
lean_object* v_reuseFailAlloc_154_; 
v_reuseFailAlloc_154_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_154_, 0, v___x_150_);
lean_ctor_set(v_reuseFailAlloc_154_, 1, v___x_151_);
v___x_153_ = v_reuseFailAlloc_154_;
goto v_reusejp_152_;
}
v_reusejp_152_:
{
return v___x_153_;
}
}
else
{
lean_object* v_k_x27_155_; size_t v___x_156_; size_t v___x_157_; uint8_t v___x_158_; 
v_k_x27_155_ = lean_array_fget_borrowed(v_ks_143_, v_x_140_);
v___x_156_ = lean_ptr_addr(v_x_141_);
v___x_157_ = lean_ptr_addr(v_k_x27_155_);
v___x_158_ = lean_usize_dec_eq(v___x_156_, v___x_157_);
if (v___x_158_ == 0)
{
lean_object* v___x_160_; 
if (v_isShared_147_ == 0)
{
v___x_160_ = v___x_146_;
goto v_reusejp_159_;
}
else
{
lean_object* v_reuseFailAlloc_164_; 
v_reuseFailAlloc_164_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_164_, 0, v_ks_143_);
lean_ctor_set(v_reuseFailAlloc_164_, 1, v_vs_144_);
v___x_160_ = v_reuseFailAlloc_164_;
goto v_reusejp_159_;
}
v_reusejp_159_:
{
lean_object* v___x_161_; lean_object* v___x_162_; 
v___x_161_ = lean_unsigned_to_nat(1u);
v___x_162_ = lean_nat_add(v_x_140_, v___x_161_);
lean_dec(v_x_140_);
v_x_139_ = v___x_160_;
v_x_140_ = v___x_162_;
goto _start;
}
}
else
{
lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_168_; 
v___x_165_ = lean_array_fset(v_ks_143_, v_x_140_, v_x_141_);
v___x_166_ = lean_array_fset(v_vs_144_, v_x_140_, v_x_142_);
lean_dec(v_x_140_);
if (v_isShared_147_ == 0)
{
lean_ctor_set(v___x_146_, 1, v___x_166_);
lean_ctor_set(v___x_146_, 0, v___x_165_);
v___x_168_ = v___x_146_;
goto v_reusejp_167_;
}
else
{
lean_object* v_reuseFailAlloc_169_; 
v_reuseFailAlloc_169_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_169_, 0, v___x_165_);
lean_ctor_set(v_reuseFailAlloc_169_, 1, v___x_166_);
v___x_168_ = v_reuseFailAlloc_169_;
goto v_reusejp_167_;
}
v_reusejp_167_:
{
return v___x_168_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2_spec__4___redArg(lean_object* v_n_171_, lean_object* v_k_172_, lean_object* v_v_173_){
_start:
{
lean_object* v___x_174_; lean_object* v___x_175_; 
v___x_174_ = lean_unsigned_to_nat(0u);
v___x_175_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2_spec__4_spec__8___redArg(v_n_171_, v___x_174_, v_k_172_, v_v_173_);
return v___x_175_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_176_; 
v___x_176_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_176_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___redArg(lean_object* v_x_177_, size_t v_x_178_, size_t v_x_179_, lean_object* v_x_180_, lean_object* v_x_181_){
_start:
{
if (lean_obj_tag(v_x_177_) == 0)
{
lean_object* v_es_182_; size_t v___x_183_; size_t v___x_184_; lean_object* v_j_185_; lean_object* v___x_186_; uint8_t v___x_187_; 
v_es_182_ = lean_ctor_get(v_x_177_, 0);
v___x_183_ = ((size_t)31ULL);
v___x_184_ = lean_usize_land(v_x_178_, v___x_183_);
v_j_185_ = lean_usize_to_nat(v___x_184_);
v___x_186_ = lean_array_get_size(v_es_182_);
v___x_187_ = lean_nat_dec_lt(v_j_185_, v___x_186_);
if (v___x_187_ == 0)
{
lean_dec(v_j_185_);
lean_dec(v_x_181_);
lean_dec_ref(v_x_180_);
return v_x_177_;
}
else
{
lean_object* v___x_189_; uint8_t v_isShared_190_; uint8_t v_isSharedCheck_228_; 
lean_inc_ref(v_es_182_);
v_isSharedCheck_228_ = !lean_is_exclusive(v_x_177_);
if (v_isSharedCheck_228_ == 0)
{
lean_object* v_unused_229_; 
v_unused_229_ = lean_ctor_get(v_x_177_, 0);
lean_dec(v_unused_229_);
v___x_189_ = v_x_177_;
v_isShared_190_ = v_isSharedCheck_228_;
goto v_resetjp_188_;
}
else
{
lean_dec(v_x_177_);
v___x_189_ = lean_box(0);
v_isShared_190_ = v_isSharedCheck_228_;
goto v_resetjp_188_;
}
v_resetjp_188_:
{
lean_object* v_v_191_; lean_object* v___x_192_; lean_object* v_xs_x27_193_; lean_object* v___y_195_; 
v_v_191_ = lean_array_fget(v_es_182_, v_j_185_);
v___x_192_ = lean_box(0);
v_xs_x27_193_ = lean_array_fset(v_es_182_, v_j_185_, v___x_192_);
switch(lean_obj_tag(v_v_191_))
{
case 0:
{
lean_object* v_key_200_; lean_object* v_val_201_; lean_object* v___x_203_; uint8_t v_isShared_204_; uint8_t v_isSharedCheck_213_; 
v_key_200_ = lean_ctor_get(v_v_191_, 0);
v_val_201_ = lean_ctor_get(v_v_191_, 1);
v_isSharedCheck_213_ = !lean_is_exclusive(v_v_191_);
if (v_isSharedCheck_213_ == 0)
{
v___x_203_ = v_v_191_;
v_isShared_204_ = v_isSharedCheck_213_;
goto v_resetjp_202_;
}
else
{
lean_inc(v_val_201_);
lean_inc(v_key_200_);
lean_dec(v_v_191_);
v___x_203_ = lean_box(0);
v_isShared_204_ = v_isSharedCheck_213_;
goto v_resetjp_202_;
}
v_resetjp_202_:
{
size_t v___x_205_; size_t v___x_206_; uint8_t v___x_207_; 
v___x_205_ = lean_ptr_addr(v_x_180_);
v___x_206_ = lean_ptr_addr(v_key_200_);
v___x_207_ = lean_usize_dec_eq(v___x_205_, v___x_206_);
if (v___x_207_ == 0)
{
lean_object* v___x_208_; lean_object* v___x_209_; 
lean_del_object(v___x_203_);
v___x_208_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_200_, v_val_201_, v_x_180_, v_x_181_);
v___x_209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_209_, 0, v___x_208_);
v___y_195_ = v___x_209_;
goto v___jp_194_;
}
else
{
lean_object* v___x_211_; 
lean_dec(v_val_201_);
lean_dec(v_key_200_);
if (v_isShared_204_ == 0)
{
lean_ctor_set(v___x_203_, 1, v_x_181_);
lean_ctor_set(v___x_203_, 0, v_x_180_);
v___x_211_ = v___x_203_;
goto v_reusejp_210_;
}
else
{
lean_object* v_reuseFailAlloc_212_; 
v_reuseFailAlloc_212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_212_, 0, v_x_180_);
lean_ctor_set(v_reuseFailAlloc_212_, 1, v_x_181_);
v___x_211_ = v_reuseFailAlloc_212_;
goto v_reusejp_210_;
}
v_reusejp_210_:
{
v___y_195_ = v___x_211_;
goto v___jp_194_;
}
}
}
}
case 1:
{
lean_object* v_node_214_; lean_object* v___x_216_; uint8_t v_isShared_217_; uint8_t v_isSharedCheck_226_; 
v_node_214_ = lean_ctor_get(v_v_191_, 0);
v_isSharedCheck_226_ = !lean_is_exclusive(v_v_191_);
if (v_isSharedCheck_226_ == 0)
{
v___x_216_ = v_v_191_;
v_isShared_217_ = v_isSharedCheck_226_;
goto v_resetjp_215_;
}
else
{
lean_inc(v_node_214_);
lean_dec(v_v_191_);
v___x_216_ = lean_box(0);
v_isShared_217_ = v_isSharedCheck_226_;
goto v_resetjp_215_;
}
v_resetjp_215_:
{
size_t v___x_218_; size_t v___x_219_; size_t v___x_220_; size_t v___x_221_; lean_object* v___x_222_; lean_object* v___x_224_; 
v___x_218_ = ((size_t)5ULL);
v___x_219_ = lean_usize_shift_right(v_x_178_, v___x_218_);
v___x_220_ = ((size_t)1ULL);
v___x_221_ = lean_usize_add(v_x_179_, v___x_220_);
v___x_222_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___redArg(v_node_214_, v___x_219_, v___x_221_, v_x_180_, v_x_181_);
if (v_isShared_217_ == 0)
{
lean_ctor_set(v___x_216_, 0, v___x_222_);
v___x_224_ = v___x_216_;
goto v_reusejp_223_;
}
else
{
lean_object* v_reuseFailAlloc_225_; 
v_reuseFailAlloc_225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_225_, 0, v___x_222_);
v___x_224_ = v_reuseFailAlloc_225_;
goto v_reusejp_223_;
}
v_reusejp_223_:
{
v___y_195_ = v___x_224_;
goto v___jp_194_;
}
}
}
default: 
{
lean_object* v___x_227_; 
v___x_227_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_227_, 0, v_x_180_);
lean_ctor_set(v___x_227_, 1, v_x_181_);
v___y_195_ = v___x_227_;
goto v___jp_194_;
}
}
v___jp_194_:
{
lean_object* v___x_196_; lean_object* v___x_198_; 
v___x_196_ = lean_array_fset(v_xs_x27_193_, v_j_185_, v___y_195_);
lean_dec(v_j_185_);
if (v_isShared_190_ == 0)
{
lean_ctor_set(v___x_189_, 0, v___x_196_);
v___x_198_ = v___x_189_;
goto v_reusejp_197_;
}
else
{
lean_object* v_reuseFailAlloc_199_; 
v_reuseFailAlloc_199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_199_, 0, v___x_196_);
v___x_198_ = v_reuseFailAlloc_199_;
goto v_reusejp_197_;
}
v_reusejp_197_:
{
return v___x_198_;
}
}
}
}
}
else
{
lean_object* v_ks_230_; lean_object* v_vs_231_; lean_object* v___x_233_; uint8_t v_isShared_234_; uint8_t v_isSharedCheck_249_; 
v_ks_230_ = lean_ctor_get(v_x_177_, 0);
v_vs_231_ = lean_ctor_get(v_x_177_, 1);
v_isSharedCheck_249_ = !lean_is_exclusive(v_x_177_);
if (v_isSharedCheck_249_ == 0)
{
v___x_233_ = v_x_177_;
v_isShared_234_ = v_isSharedCheck_249_;
goto v_resetjp_232_;
}
else
{
lean_inc(v_vs_231_);
lean_inc(v_ks_230_);
lean_dec(v_x_177_);
v___x_233_ = lean_box(0);
v_isShared_234_ = v_isSharedCheck_249_;
goto v_resetjp_232_;
}
v_resetjp_232_:
{
lean_object* v___x_236_; 
if (v_isShared_234_ == 0)
{
v___x_236_ = v___x_233_;
goto v_reusejp_235_;
}
else
{
lean_object* v_reuseFailAlloc_248_; 
v_reuseFailAlloc_248_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_248_, 0, v_ks_230_);
lean_ctor_set(v_reuseFailAlloc_248_, 1, v_vs_231_);
v___x_236_ = v_reuseFailAlloc_248_;
goto v_reusejp_235_;
}
v_reusejp_235_:
{
lean_object* v_newNode_237_; size_t v___x_238_; uint8_t v___x_239_; 
v_newNode_237_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2_spec__4___redArg(v___x_236_, v_x_180_, v_x_181_);
v___x_238_ = ((size_t)7ULL);
v___x_239_ = lean_usize_dec_le(v___x_238_, v_x_179_);
if (v___x_239_ == 0)
{
lean_object* v___x_240_; lean_object* v___x_241_; uint8_t v___x_242_; 
v___x_240_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_237_);
v___x_241_ = lean_unsigned_to_nat(4u);
v___x_242_ = lean_nat_dec_lt(v___x_240_, v___x_241_);
lean_dec(v___x_240_);
if (v___x_242_ == 0)
{
lean_object* v_ks_243_; lean_object* v_vs_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; 
v_ks_243_ = lean_ctor_get(v_newNode_237_, 0);
lean_inc_ref(v_ks_243_);
v_vs_244_ = lean_ctor_get(v_newNode_237_, 1);
lean_inc_ref(v_vs_244_);
lean_dec_ref(v_newNode_237_);
v___x_245_ = lean_unsigned_to_nat(0u);
v___x_246_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___redArg___closed__0);
v___x_247_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2_spec__5___redArg(v_x_179_, v_ks_243_, v_vs_244_, v___x_245_, v___x_246_);
lean_dec_ref(v_vs_244_);
lean_dec_ref(v_ks_243_);
return v___x_247_;
}
else
{
return v_newNode_237_;
}
}
else
{
return v_newNode_237_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2_spec__5___redArg(size_t v_depth_250_, lean_object* v_keys_251_, lean_object* v_vals_252_, lean_object* v_i_253_, lean_object* v_entries_254_){
_start:
{
lean_object* v___x_255_; uint8_t v___x_256_; 
v___x_255_ = lean_array_get_size(v_keys_251_);
v___x_256_ = lean_nat_dec_lt(v_i_253_, v___x_255_);
if (v___x_256_ == 0)
{
lean_dec(v_i_253_);
return v_entries_254_;
}
else
{
lean_object* v_k_257_; lean_object* v_v_258_; size_t v___x_259_; size_t v___x_260_; size_t v___x_261_; uint64_t v___x_262_; size_t v_h_263_; size_t v___x_264_; lean_object* v___x_265_; size_t v___x_266_; size_t v___x_267_; size_t v___x_268_; size_t v_h_269_; lean_object* v___x_270_; lean_object* v___x_271_; 
v_k_257_ = lean_array_fget_borrowed(v_keys_251_, v_i_253_);
v_v_258_ = lean_array_fget_borrowed(v_vals_252_, v_i_253_);
v___x_259_ = lean_ptr_addr(v_k_257_);
v___x_260_ = ((size_t)3ULL);
v___x_261_ = lean_usize_shift_right(v___x_259_, v___x_260_);
v___x_262_ = lean_usize_to_uint64(v___x_261_);
v_h_263_ = lean_uint64_to_usize(v___x_262_);
v___x_264_ = ((size_t)5ULL);
v___x_265_ = lean_unsigned_to_nat(1u);
v___x_266_ = ((size_t)1ULL);
v___x_267_ = lean_usize_sub(v_depth_250_, v___x_266_);
v___x_268_ = lean_usize_mul(v___x_264_, v___x_267_);
v_h_269_ = lean_usize_shift_right(v_h_263_, v___x_268_);
v___x_270_ = lean_nat_add(v_i_253_, v___x_265_);
lean_dec(v_i_253_);
lean_inc(v_v_258_);
lean_inc(v_k_257_);
v___x_271_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___redArg(v_entries_254_, v_h_269_, v_depth_250_, v_k_257_, v_v_258_);
v_i_253_ = v___x_270_;
v_entries_254_ = v___x_271_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_depth_273_, lean_object* v_keys_274_, lean_object* v_vals_275_, lean_object* v_i_276_, lean_object* v_entries_277_){
_start:
{
size_t v_depth_boxed_278_; lean_object* v_res_279_; 
v_depth_boxed_278_ = lean_unbox_usize(v_depth_273_);
lean_dec(v_depth_273_);
v_res_279_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2_spec__5___redArg(v_depth_boxed_278_, v_keys_274_, v_vals_275_, v_i_276_, v_entries_277_);
lean_dec_ref(v_vals_275_);
lean_dec_ref(v_keys_274_);
return v_res_279_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___redArg___boxed(lean_object* v_x_280_, lean_object* v_x_281_, lean_object* v_x_282_, lean_object* v_x_283_, lean_object* v_x_284_){
_start:
{
size_t v_x_39227__boxed_285_; size_t v_x_39228__boxed_286_; lean_object* v_res_287_; 
v_x_39227__boxed_285_ = lean_unbox_usize(v_x_281_);
lean_dec(v_x_281_);
v_x_39228__boxed_286_ = lean_unbox_usize(v_x_282_);
lean_dec(v_x_282_);
v_res_287_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___redArg(v_x_280_, v_x_39227__boxed_285_, v_x_39228__boxed_286_, v_x_283_, v_x_284_);
return v_res_287_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1___redArg(lean_object* v_x_288_, lean_object* v_x_289_, lean_object* v_x_290_){
_start:
{
size_t v___x_291_; size_t v___x_292_; size_t v___x_293_; uint64_t v___x_294_; size_t v___x_295_; size_t v___x_296_; lean_object* v___x_297_; 
v___x_291_ = lean_ptr_addr(v_x_289_);
v___x_292_ = ((size_t)3ULL);
v___x_293_ = lean_usize_shift_right(v___x_291_, v___x_292_);
v___x_294_ = lean_usize_to_uint64(v___x_293_);
v___x_295_ = lean_uint64_to_usize(v___x_294_);
v___x_296_ = ((size_t)1ULL);
v___x_297_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___redArg(v_x_288_, v___x_295_, v___x_296_, v_x_289_, v_x_290_);
return v___x_297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_internalize___lam__0(lean_object* v_e_298_, lean_object* v_a_299_, uint8_t v___x_300_, lean_object* v_s_301_){
_start:
{
lean_object* v_id_302_; lean_object* v_type_303_; lean_object* v_u_304_; lean_object* v_op_305_; lean_object* v_neutral_x3f_306_; lean_object* v_assocInst_307_; lean_object* v_idempotentInst_x3f_308_; lean_object* v_commInst_x3f_309_; lean_object* v_neutralInst_x3f_310_; lean_object* v_nextId_311_; lean_object* v_vars_312_; lean_object* v_varMap_313_; lean_object* v_denote_314_; lean_object* v_denoteEntries_315_; lean_object* v_queue_316_; lean_object* v_basis_317_; lean_object* v_diseqs_318_; lean_object* v___x_320_; uint8_t v_isShared_321_; uint8_t v_isSharedCheck_328_; 
v_id_302_ = lean_ctor_get(v_s_301_, 0);
v_type_303_ = lean_ctor_get(v_s_301_, 1);
v_u_304_ = lean_ctor_get(v_s_301_, 2);
v_op_305_ = lean_ctor_get(v_s_301_, 3);
v_neutral_x3f_306_ = lean_ctor_get(v_s_301_, 4);
v_assocInst_307_ = lean_ctor_get(v_s_301_, 5);
v_idempotentInst_x3f_308_ = lean_ctor_get(v_s_301_, 6);
v_commInst_x3f_309_ = lean_ctor_get(v_s_301_, 7);
v_neutralInst_x3f_310_ = lean_ctor_get(v_s_301_, 8);
v_nextId_311_ = lean_ctor_get(v_s_301_, 9);
v_vars_312_ = lean_ctor_get(v_s_301_, 10);
v_varMap_313_ = lean_ctor_get(v_s_301_, 11);
v_denote_314_ = lean_ctor_get(v_s_301_, 12);
v_denoteEntries_315_ = lean_ctor_get(v_s_301_, 13);
v_queue_316_ = lean_ctor_get(v_s_301_, 14);
v_basis_317_ = lean_ctor_get(v_s_301_, 15);
v_diseqs_318_ = lean_ctor_get(v_s_301_, 16);
v_isSharedCheck_328_ = !lean_is_exclusive(v_s_301_);
if (v_isSharedCheck_328_ == 0)
{
v___x_320_ = v_s_301_;
v_isShared_321_ = v_isSharedCheck_328_;
goto v_resetjp_319_;
}
else
{
lean_inc(v_diseqs_318_);
lean_inc(v_basis_317_);
lean_inc(v_queue_316_);
lean_inc(v_denoteEntries_315_);
lean_inc(v_denote_314_);
lean_inc(v_varMap_313_);
lean_inc(v_vars_312_);
lean_inc(v_nextId_311_);
lean_inc(v_neutralInst_x3f_310_);
lean_inc(v_commInst_x3f_309_);
lean_inc(v_idempotentInst_x3f_308_);
lean_inc(v_assocInst_307_);
lean_inc(v_neutral_x3f_306_);
lean_inc(v_op_305_);
lean_inc(v_u_304_);
lean_inc(v_type_303_);
lean_inc(v_id_302_);
lean_dec(v_s_301_);
v___x_320_ = lean_box(0);
v_isShared_321_ = v_isSharedCheck_328_;
goto v_resetjp_319_;
}
v_resetjp_319_:
{
lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_326_; 
lean_inc_ref(v_a_299_);
lean_inc_ref(v_e_298_);
v___x_322_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1___redArg(v_denote_314_, v_e_298_, v_a_299_);
v___x_323_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_323_, 0, v_e_298_);
lean_ctor_set(v___x_323_, 1, v_a_299_);
v___x_324_ = l_Lean_PersistentArray_push___redArg(v_denoteEntries_315_, v___x_323_);
if (v_isShared_321_ == 0)
{
lean_ctor_set(v___x_320_, 13, v___x_324_);
lean_ctor_set(v___x_320_, 12, v___x_322_);
v___x_326_ = v___x_320_;
goto v_reusejp_325_;
}
else
{
lean_object* v_reuseFailAlloc_327_; 
v_reuseFailAlloc_327_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_327_, 0, v_id_302_);
lean_ctor_set(v_reuseFailAlloc_327_, 1, v_type_303_);
lean_ctor_set(v_reuseFailAlloc_327_, 2, v_u_304_);
lean_ctor_set(v_reuseFailAlloc_327_, 3, v_op_305_);
lean_ctor_set(v_reuseFailAlloc_327_, 4, v_neutral_x3f_306_);
lean_ctor_set(v_reuseFailAlloc_327_, 5, v_assocInst_307_);
lean_ctor_set(v_reuseFailAlloc_327_, 6, v_idempotentInst_x3f_308_);
lean_ctor_set(v_reuseFailAlloc_327_, 7, v_commInst_x3f_309_);
lean_ctor_set(v_reuseFailAlloc_327_, 8, v_neutralInst_x3f_310_);
lean_ctor_set(v_reuseFailAlloc_327_, 9, v_nextId_311_);
lean_ctor_set(v_reuseFailAlloc_327_, 10, v_vars_312_);
lean_ctor_set(v_reuseFailAlloc_327_, 11, v_varMap_313_);
lean_ctor_set(v_reuseFailAlloc_327_, 12, v___x_322_);
lean_ctor_set(v_reuseFailAlloc_327_, 13, v___x_324_);
lean_ctor_set(v_reuseFailAlloc_327_, 14, v_queue_316_);
lean_ctor_set(v_reuseFailAlloc_327_, 15, v_basis_317_);
lean_ctor_set(v_reuseFailAlloc_327_, 16, v_diseqs_318_);
v___x_326_ = v_reuseFailAlloc_327_;
goto v_reusejp_325_;
}
v_reusejp_325_:
{
lean_ctor_set_uint8(v___x_326_, sizeof(void*)*17, v___x_300_);
return v___x_326_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_internalize___lam__0___boxed(lean_object* v_e_329_, lean_object* v_a_330_, lean_object* v___x_331_, lean_object* v_s_332_){
_start:
{
uint8_t v___x_39406__boxed_333_; lean_object* v_res_334_; 
v___x_39406__boxed_333_ = lean_unbox(v___x_331_);
v_res_334_ = l_Lean_Meta_Grind_AC_internalize___lam__0(v_e_329_, v_a_330_, v___x_39406__boxed_333_, v_s_332_);
return v_res_334_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3_spec__5(lean_object* v_msgData_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_){
_start:
{
lean_object* v___x_341_; lean_object* v_env_342_; uint8_t v___x_343_; lean_object* v_env_344_; lean_object* v___x_345_; lean_object* v_toCold_346_; lean_object* v_mctx_347_; lean_object* v_lctx_348_; lean_object* v_options_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; 
v___x_341_ = lean_st_ref_get(v___y_339_);
v_env_342_ = lean_ctor_get(v___x_341_, 0);
lean_inc_ref(v_env_342_);
lean_dec(v___x_341_);
v___x_343_ = 0;
v_env_344_ = l_Lean_Environment_setRecordingDeps(v_env_342_, v___x_343_);
v___x_345_ = lean_st_ref_get(v___y_337_);
v_toCold_346_ = lean_ctor_get(v___y_338_, 0);
v_mctx_347_ = lean_ctor_get(v___x_345_, 0);
lean_inc_ref(v_mctx_347_);
lean_dec(v___x_345_);
v_lctx_348_ = lean_ctor_get(v___y_336_, 2);
v_options_349_ = lean_ctor_get(v_toCold_346_, 2);
lean_inc_ref(v_options_349_);
lean_inc_ref(v_lctx_348_);
v___x_350_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_350_, 0, v_env_344_);
lean_ctor_set(v___x_350_, 1, v_mctx_347_);
lean_ctor_set(v___x_350_, 2, v_lctx_348_);
lean_ctor_set(v___x_350_, 3, v_options_349_);
v___x_351_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_351_, 0, v___x_350_);
lean_ctor_set(v___x_351_, 1, v_msgData_335_);
v___x_352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_352_, 0, v___x_351_);
return v___x_352_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3_spec__5___boxed(lean_object* v_msgData_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_){
_start:
{
lean_object* v_res_359_; 
v_res_359_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3_spec__5(v_msgData_353_, v___y_354_, v___y_355_, v___y_356_, v___y_357_);
lean_dec(v___y_357_);
lean_dec_ref(v___y_356_);
lean_dec(v___y_355_);
lean_dec_ref(v___y_354_);
return v_res_359_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_360_; double v___x_361_; 
v___x_360_ = lean_unsigned_to_nat(0u);
v___x_361_ = lean_float_of_nat(v___x_360_);
return v___x_361_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3___redArg(lean_object* v_cls_365_, lean_object* v_msg_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_){
_start:
{
lean_object* v_ref_372_; lean_object* v___x_373_; lean_object* v_a_374_; lean_object* v___x_376_; uint8_t v_isShared_377_; uint8_t v_isSharedCheck_419_; 
v_ref_372_ = lean_ctor_get(v___y_369_, 2);
v___x_373_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3_spec__5(v_msg_366_, v___y_367_, v___y_368_, v___y_369_, v___y_370_);
v_a_374_ = lean_ctor_get(v___x_373_, 0);
v_isSharedCheck_419_ = !lean_is_exclusive(v___x_373_);
if (v_isSharedCheck_419_ == 0)
{
v___x_376_ = v___x_373_;
v_isShared_377_ = v_isSharedCheck_419_;
goto v_resetjp_375_;
}
else
{
lean_inc(v_a_374_);
lean_dec(v___x_373_);
v___x_376_ = lean_box(0);
v_isShared_377_ = v_isSharedCheck_419_;
goto v_resetjp_375_;
}
v_resetjp_375_:
{
lean_object* v___x_378_; lean_object* v_traceState_379_; lean_object* v_env_380_; lean_object* v_nextMacroScope_381_; lean_object* v_ngen_382_; lean_object* v_auxDeclNGen_383_; lean_object* v_cache_384_; lean_object* v_recordedDeps_385_; lean_object* v_messages_386_; lean_object* v_infoState_387_; lean_object* v_snapshotTasks_388_; lean_object* v___x_390_; uint8_t v_isShared_391_; uint8_t v_isSharedCheck_418_; 
v___x_378_ = lean_st_ref_take(v___y_370_);
v_traceState_379_ = lean_ctor_get(v___x_378_, 4);
v_env_380_ = lean_ctor_get(v___x_378_, 0);
v_nextMacroScope_381_ = lean_ctor_get(v___x_378_, 1);
v_ngen_382_ = lean_ctor_get(v___x_378_, 2);
v_auxDeclNGen_383_ = lean_ctor_get(v___x_378_, 3);
v_cache_384_ = lean_ctor_get(v___x_378_, 5);
v_recordedDeps_385_ = lean_ctor_get(v___x_378_, 6);
v_messages_386_ = lean_ctor_get(v___x_378_, 7);
v_infoState_387_ = lean_ctor_get(v___x_378_, 8);
v_snapshotTasks_388_ = lean_ctor_get(v___x_378_, 9);
v_isSharedCheck_418_ = !lean_is_exclusive(v___x_378_);
if (v_isSharedCheck_418_ == 0)
{
v___x_390_ = v___x_378_;
v_isShared_391_ = v_isSharedCheck_418_;
goto v_resetjp_389_;
}
else
{
lean_inc(v_snapshotTasks_388_);
lean_inc(v_infoState_387_);
lean_inc(v_messages_386_);
lean_inc(v_recordedDeps_385_);
lean_inc(v_cache_384_);
lean_inc(v_traceState_379_);
lean_inc(v_auxDeclNGen_383_);
lean_inc(v_ngen_382_);
lean_inc(v_nextMacroScope_381_);
lean_inc(v_env_380_);
lean_dec(v___x_378_);
v___x_390_ = lean_box(0);
v_isShared_391_ = v_isSharedCheck_418_;
goto v_resetjp_389_;
}
v_resetjp_389_:
{
uint64_t v_tid_392_; lean_object* v_traces_393_; lean_object* v___x_395_; uint8_t v_isShared_396_; uint8_t v_isSharedCheck_417_; 
v_tid_392_ = lean_ctor_get_uint64(v_traceState_379_, sizeof(void*)*1);
v_traces_393_ = lean_ctor_get(v_traceState_379_, 0);
v_isSharedCheck_417_ = !lean_is_exclusive(v_traceState_379_);
if (v_isSharedCheck_417_ == 0)
{
v___x_395_ = v_traceState_379_;
v_isShared_396_ = v_isSharedCheck_417_;
goto v_resetjp_394_;
}
else
{
lean_inc(v_traces_393_);
lean_dec(v_traceState_379_);
v___x_395_ = lean_box(0);
v_isShared_396_ = v_isSharedCheck_417_;
goto v_resetjp_394_;
}
v_resetjp_394_:
{
lean_object* v___x_397_; lean_object* v___x_398_; double v___x_399_; uint8_t v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_408_; 
v___x_397_ = lean_box(0);
v___x_398_ = lean_box(0);
v___x_399_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3___redArg___closed__0);
v___x_400_ = 0;
v___x_401_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3___redArg___closed__1));
v___x_402_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_402_, 0, v_cls_365_);
lean_ctor_set(v___x_402_, 1, v___x_398_);
lean_ctor_set(v___x_402_, 2, v___x_401_);
lean_ctor_set_float(v___x_402_, sizeof(void*)*3, v___x_399_);
lean_ctor_set_float(v___x_402_, sizeof(void*)*3 + 8, v___x_399_);
lean_ctor_set_uint8(v___x_402_, sizeof(void*)*3 + 16, v___x_400_);
v___x_403_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3___redArg___closed__2));
v___x_404_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_404_, 0, v___x_402_);
lean_ctor_set(v___x_404_, 1, v_a_374_);
lean_ctor_set(v___x_404_, 2, v___x_403_);
lean_inc(v_ref_372_);
v___x_405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_405_, 0, v_ref_372_);
lean_ctor_set(v___x_405_, 1, v___x_404_);
v___x_406_ = l_Lean_PersistentArray_push___redArg(v_traces_393_, v___x_405_);
if (v_isShared_396_ == 0)
{
lean_ctor_set(v___x_395_, 0, v___x_406_);
v___x_408_ = v___x_395_;
goto v_reusejp_407_;
}
else
{
lean_object* v_reuseFailAlloc_416_; 
v_reuseFailAlloc_416_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_416_, 0, v___x_406_);
lean_ctor_set_uint64(v_reuseFailAlloc_416_, sizeof(void*)*1, v_tid_392_);
v___x_408_ = v_reuseFailAlloc_416_;
goto v_reusejp_407_;
}
v_reusejp_407_:
{
lean_object* v___x_410_; 
if (v_isShared_391_ == 0)
{
lean_ctor_set(v___x_390_, 4, v___x_408_);
v___x_410_ = v___x_390_;
goto v_reusejp_409_;
}
else
{
lean_object* v_reuseFailAlloc_415_; 
v_reuseFailAlloc_415_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_415_, 0, v_env_380_);
lean_ctor_set(v_reuseFailAlloc_415_, 1, v_nextMacroScope_381_);
lean_ctor_set(v_reuseFailAlloc_415_, 2, v_ngen_382_);
lean_ctor_set(v_reuseFailAlloc_415_, 3, v_auxDeclNGen_383_);
lean_ctor_set(v_reuseFailAlloc_415_, 4, v___x_408_);
lean_ctor_set(v_reuseFailAlloc_415_, 5, v_cache_384_);
lean_ctor_set(v_reuseFailAlloc_415_, 6, v_recordedDeps_385_);
lean_ctor_set(v_reuseFailAlloc_415_, 7, v_messages_386_);
lean_ctor_set(v_reuseFailAlloc_415_, 8, v_infoState_387_);
lean_ctor_set(v_reuseFailAlloc_415_, 9, v_snapshotTasks_388_);
v___x_410_ = v_reuseFailAlloc_415_;
goto v_reusejp_409_;
}
v_reusejp_409_:
{
lean_object* v___x_411_; lean_object* v___x_413_; 
v___x_411_ = lean_st_ref_put(v___y_370_, v___x_410_);
if (v_isShared_377_ == 0)
{
lean_ctor_set(v___x_376_, 0, v___x_397_);
v___x_413_ = v___x_376_;
goto v_reusejp_412_;
}
else
{
lean_object* v_reuseFailAlloc_414_; 
v_reuseFailAlloc_414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_414_, 0, v___x_397_);
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
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3___redArg___boxed(lean_object* v_cls_420_, lean_object* v_msg_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_){
_start:
{
lean_object* v_res_427_; 
v_res_427_ = l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3___redArg(v_cls_420_, v_msg_421_, v___y_422_, v___y_423_, v___y_424_, v___y_425_);
lean_dec(v___y_425_);
lean_dec_ref(v___y_424_);
lean_dec(v___y_423_);
lean_dec_ref(v___y_422_);
return v_res_427_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_428_, lean_object* v_i_429_, lean_object* v_k_430_){
_start:
{
lean_object* v___x_431_; uint8_t v___x_432_; 
v___x_431_ = lean_array_get_size(v_keys_428_);
v___x_432_ = lean_nat_dec_lt(v_i_429_, v___x_431_);
if (v___x_432_ == 0)
{
lean_dec(v_i_429_);
return v___x_432_;
}
else
{
lean_object* v_k_x27_433_; size_t v___x_434_; size_t v___x_435_; uint8_t v___x_436_; 
v_k_x27_433_ = lean_array_fget_borrowed(v_keys_428_, v_i_429_);
v___x_434_ = lean_ptr_addr(v_k_430_);
v___x_435_ = lean_ptr_addr(v_k_x27_433_);
v___x_436_ = lean_usize_dec_eq(v___x_434_, v___x_435_);
if (v___x_436_ == 0)
{
lean_object* v___x_437_; lean_object* v___x_438_; 
v___x_437_ = lean_unsigned_to_nat(1u);
v___x_438_ = lean_nat_add(v_i_429_, v___x_437_);
lean_dec(v_i_429_);
v_i_429_ = v___x_438_;
goto _start;
}
else
{
lean_dec(v_i_429_);
return v___x_432_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_440_, lean_object* v_i_441_, lean_object* v_k_442_){
_start:
{
uint8_t v_res_443_; lean_object* v_r_444_; 
v_res_443_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0_spec__1___redArg(v_keys_440_, v_i_441_, v_k_442_);
lean_dec_ref(v_k_442_);
lean_dec_ref(v_keys_440_);
v_r_444_ = lean_box(v_res_443_);
return v_r_444_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0___redArg(lean_object* v_x_445_, size_t v_x_446_, lean_object* v_x_447_){
_start:
{
if (lean_obj_tag(v_x_445_) == 0)
{
lean_object* v_es_448_; lean_object* v___x_449_; size_t v___x_450_; size_t v___x_451_; lean_object* v_j_452_; lean_object* v___x_453_; 
v_es_448_ = lean_ctor_get(v_x_445_, 0);
v___x_449_ = lean_box(2);
v___x_450_ = ((size_t)31ULL);
v___x_451_ = lean_usize_land(v_x_446_, v___x_450_);
v_j_452_ = lean_usize_to_nat(v___x_451_);
v___x_453_ = lean_array_get_borrowed(v___x_449_, v_es_448_, v_j_452_);
lean_dec(v_j_452_);
switch(lean_obj_tag(v___x_453_))
{
case 0:
{
lean_object* v_key_454_; size_t v___x_455_; size_t v___x_456_; uint8_t v___x_457_; 
v_key_454_ = lean_ctor_get(v___x_453_, 0);
v___x_455_ = lean_ptr_addr(v_x_447_);
v___x_456_ = lean_ptr_addr(v_key_454_);
v___x_457_ = lean_usize_dec_eq(v___x_455_, v___x_456_);
return v___x_457_;
}
case 1:
{
lean_object* v_node_458_; size_t v___x_459_; size_t v___x_460_; 
v_node_458_ = lean_ctor_get(v___x_453_, 0);
v___x_459_ = ((size_t)5ULL);
v___x_460_ = lean_usize_shift_right(v_x_446_, v___x_459_);
v_x_445_ = v_node_458_;
v_x_446_ = v___x_460_;
goto _start;
}
default: 
{
uint8_t v___x_462_; 
v___x_462_ = 0;
return v___x_462_;
}
}
}
else
{
lean_object* v_ks_463_; lean_object* v___x_464_; uint8_t v___x_465_; 
v_ks_463_ = lean_ctor_get(v_x_445_, 0);
v___x_464_ = lean_unsigned_to_nat(0u);
v___x_465_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0_spec__1___redArg(v_ks_463_, v___x_464_, v_x_447_);
return v___x_465_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0___redArg___boxed(lean_object* v_x_466_, lean_object* v_x_467_, lean_object* v_x_468_){
_start:
{
size_t v_x_39576__boxed_469_; uint8_t v_res_470_; lean_object* v_r_471_; 
v_x_39576__boxed_469_ = lean_unbox_usize(v_x_467_);
lean_dec(v_x_467_);
v_res_470_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0___redArg(v_x_466_, v_x_39576__boxed_469_, v_x_468_);
lean_dec_ref(v_x_468_);
lean_dec_ref(v_x_466_);
v_r_471_ = lean_box(v_res_470_);
return v_r_471_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0___redArg(lean_object* v_x_472_, lean_object* v_x_473_){
_start:
{
size_t v___x_474_; size_t v___x_475_; size_t v___x_476_; uint64_t v___x_477_; size_t v___x_478_; uint8_t v___x_479_; 
v___x_474_ = lean_ptr_addr(v_x_473_);
v___x_475_ = ((size_t)3ULL);
v___x_476_ = lean_usize_shift_right(v___x_474_, v___x_475_);
v___x_477_ = lean_usize_to_uint64(v___x_476_);
v___x_478_ = lean_uint64_to_usize(v___x_477_);
v___x_479_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0___redArg(v_x_472_, v___x_478_, v_x_473_);
return v___x_479_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0___redArg___boxed(lean_object* v_x_480_, lean_object* v_x_481_){
_start:
{
uint8_t v_res_482_; lean_object* v_r_483_; 
v_res_482_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0___redArg(v_x_480_, v_x_481_);
lean_dec_ref(v_x_481_);
lean_dec_ref(v_x_480_);
v_r_483_ = lean_box(v_res_482_);
return v_r_483_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Expr_denoteExpr___at___00Lean_Meta_Grind_AC_internalize_spec__2(lean_object* v_e_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_){
_start:
{
if (lean_obj_tag(v_e_484_) == 0)
{
lean_object* v_x_497_; lean_object* v___x_498_; lean_object* v___x_499_; 
v_x_497_ = lean_ctor_get(v_e_484_, 0);
v___x_498_ = l_Lean_instInhabitedExpr;
v___x_499_ = l_Lean_Meta_Grind_AC_ACM_getStruct(v___y_485_, v___y_486_, v___y_487_, v___y_488_, v___y_489_, v___y_490_, v___y_491_, v___y_492_, v___y_493_, v___y_494_, v___y_495_);
if (lean_obj_tag(v___x_499_) == 0)
{
lean_object* v_a_500_; lean_object* v___x_502_; uint8_t v_isShared_503_; uint8_t v_isSharedCheck_515_; 
v_a_500_ = lean_ctor_get(v___x_499_, 0);
v_isSharedCheck_515_ = !lean_is_exclusive(v___x_499_);
if (v_isSharedCheck_515_ == 0)
{
v___x_502_ = v___x_499_;
v_isShared_503_ = v_isSharedCheck_515_;
goto v_resetjp_501_;
}
else
{
lean_inc(v_a_500_);
lean_dec(v___x_499_);
v___x_502_ = lean_box(0);
v_isShared_503_ = v_isSharedCheck_515_;
goto v_resetjp_501_;
}
v_resetjp_501_:
{
lean_object* v_vars_504_; lean_object* v_size_505_; uint8_t v___x_506_; 
v_vars_504_ = lean_ctor_get(v_a_500_, 10);
lean_inc_ref(v_vars_504_);
lean_dec(v_a_500_);
v_size_505_ = lean_ctor_get(v_vars_504_, 2);
v___x_506_ = lean_nat_dec_lt(v_x_497_, v_size_505_);
if (v___x_506_ == 0)
{
lean_object* v___x_507_; lean_object* v___x_509_; 
lean_dec_ref(v_vars_504_);
v___x_507_ = l_outOfBounds___redArg(v___x_498_);
if (v_isShared_503_ == 0)
{
lean_ctor_set(v___x_502_, 0, v___x_507_);
v___x_509_ = v___x_502_;
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
else
{
lean_object* v___x_511_; lean_object* v___x_513_; 
v___x_511_ = l_Lean_PersistentArray_get_x21___redArg(v___x_498_, v_vars_504_, v_x_497_);
lean_dec_ref(v_vars_504_);
if (v_isShared_503_ == 0)
{
lean_ctor_set(v___x_502_, 0, v___x_511_);
v___x_513_ = v___x_502_;
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
v_a_516_ = lean_ctor_get(v___x_499_, 0);
v_isSharedCheck_523_ = !lean_is_exclusive(v___x_499_);
if (v_isSharedCheck_523_ == 0)
{
v___x_518_ = v___x_499_;
v_isShared_519_ = v_isSharedCheck_523_;
goto v_resetjp_517_;
}
else
{
lean_inc(v_a_516_);
lean_dec(v___x_499_);
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
lean_object* v_lhs_524_; lean_object* v_rhs_525_; lean_object* v___x_526_; 
v_lhs_524_ = lean_ctor_get(v_e_484_, 0);
v_rhs_525_ = lean_ctor_get(v_e_484_, 1);
v___x_526_ = l_Lean_Meta_Grind_AC_ACM_getStruct(v___y_485_, v___y_486_, v___y_487_, v___y_488_, v___y_489_, v___y_490_, v___y_491_, v___y_492_, v___y_493_, v___y_494_, v___y_495_);
if (lean_obj_tag(v___x_526_) == 0)
{
lean_object* v_a_527_; lean_object* v___x_528_; 
v_a_527_ = lean_ctor_get(v___x_526_, 0);
lean_inc(v_a_527_);
lean_dec_ref_known(v___x_526_, 1);
v___x_528_ = l_Lean_Grind_AC_Expr_denoteExpr___at___00Lean_Meta_Grind_AC_internalize_spec__2(v_lhs_524_, v___y_485_, v___y_486_, v___y_487_, v___y_488_, v___y_489_, v___y_490_, v___y_491_, v___y_492_, v___y_493_, v___y_494_, v___y_495_);
if (lean_obj_tag(v___x_528_) == 0)
{
lean_object* v_a_529_; lean_object* v___x_530_; 
v_a_529_ = lean_ctor_get(v___x_528_, 0);
lean_inc(v_a_529_);
lean_dec_ref_known(v___x_528_, 1);
v___x_530_ = l_Lean_Grind_AC_Expr_denoteExpr___at___00Lean_Meta_Grind_AC_internalize_spec__2(v_rhs_525_, v___y_485_, v___y_486_, v___y_487_, v___y_488_, v___y_489_, v___y_490_, v___y_491_, v___y_492_, v___y_493_, v___y_494_, v___y_495_);
if (lean_obj_tag(v___x_530_) == 0)
{
lean_object* v_a_531_; lean_object* v___x_533_; uint8_t v_isShared_534_; uint8_t v_isSharedCheck_540_; 
v_a_531_ = lean_ctor_get(v___x_530_, 0);
v_isSharedCheck_540_ = !lean_is_exclusive(v___x_530_);
if (v_isSharedCheck_540_ == 0)
{
v___x_533_ = v___x_530_;
v_isShared_534_ = v_isSharedCheck_540_;
goto v_resetjp_532_;
}
else
{
lean_inc(v_a_531_);
lean_dec(v___x_530_);
v___x_533_ = lean_box(0);
v_isShared_534_ = v_isSharedCheck_540_;
goto v_resetjp_532_;
}
v_resetjp_532_:
{
lean_object* v_op_535_; lean_object* v___x_536_; lean_object* v___x_538_; 
v_op_535_ = lean_ctor_get(v_a_527_, 3);
lean_inc_ref(v_op_535_);
lean_dec(v_a_527_);
v___x_536_ = l_Lean_mkAppB(v_op_535_, v_a_529_, v_a_531_);
if (v_isShared_534_ == 0)
{
lean_ctor_set(v___x_533_, 0, v___x_536_);
v___x_538_ = v___x_533_;
goto v_reusejp_537_;
}
else
{
lean_object* v_reuseFailAlloc_539_; 
v_reuseFailAlloc_539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_539_, 0, v___x_536_);
v___x_538_ = v_reuseFailAlloc_539_;
goto v_reusejp_537_;
}
v_reusejp_537_:
{
return v___x_538_;
}
}
}
else
{
lean_dec(v_a_529_);
lean_dec(v_a_527_);
return v___x_530_;
}
}
else
{
lean_dec(v_a_527_);
return v___x_528_;
}
}
else
{
lean_object* v_a_541_; lean_object* v___x_543_; uint8_t v_isShared_544_; uint8_t v_isSharedCheck_548_; 
v_a_541_ = lean_ctor_get(v___x_526_, 0);
v_isSharedCheck_548_ = !lean_is_exclusive(v___x_526_);
if (v_isSharedCheck_548_ == 0)
{
v___x_543_ = v___x_526_;
v_isShared_544_ = v_isSharedCheck_548_;
goto v_resetjp_542_;
}
else
{
lean_inc(v_a_541_);
lean_dec(v___x_526_);
v___x_543_ = lean_box(0);
v_isShared_544_ = v_isSharedCheck_548_;
goto v_resetjp_542_;
}
v_resetjp_542_:
{
lean_object* v___x_546_; 
if (v_isShared_544_ == 0)
{
v___x_546_ = v___x_543_;
goto v_reusejp_545_;
}
else
{
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_547_, 0, v_a_541_);
v___x_546_ = v_reuseFailAlloc_547_;
goto v_reusejp_545_;
}
v_reusejp_545_:
{
return v___x_546_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Expr_denoteExpr___at___00Lean_Meta_Grind_AC_internalize_spec__2___boxed(lean_object* v_e_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_){
_start:
{
lean_object* v_res_562_; 
v_res_562_ = l_Lean_Grind_AC_Expr_denoteExpr___at___00Lean_Meta_Grind_AC_internalize_spec__2(v_e_549_, v___y_550_, v___y_551_, v___y_552_, v___y_553_, v___y_554_, v___y_555_, v___y_556_, v___y_557_, v___y_558_, v___y_559_, v___y_560_);
lean_dec(v___y_560_);
lean_dec_ref(v___y_559_);
lean_dec(v___y_558_);
lean_dec_ref(v___y_557_);
lean_dec(v___y_556_);
lean_dec_ref(v___y_555_);
lean_dec(v___y_554_);
lean_dec_ref(v___y_553_);
lean_dec(v___y_552_);
lean_dec(v___y_551_);
lean_dec(v___y_550_);
lean_dec_ref(v_e_549_);
return v_res_562_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_AC_internalize___closed__6(void){
_start:
{
lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; 
v___x_573_ = ((lean_object*)(l_Lean_Meta_Grind_AC_internalize___closed__3));
v___x_574_ = ((lean_object*)(l_Lean_Meta_Grind_AC_internalize___closed__5));
v___x_575_ = l_Lean_Name_append(v___x_574_, v___x_573_);
return v___x_575_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_AC_internalize___closed__8(void){
_start:
{
lean_object* v___x_577_; lean_object* v___x_578_; 
v___x_577_ = ((lean_object*)(l_Lean_Meta_Grind_AC_internalize___closed__7));
v___x_578_ = l_Lean_stringToMessageData(v___x_577_);
return v___x_578_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_AC_internalize___closed__10(void){
_start:
{
lean_object* v___x_580_; lean_object* v___x_581_; 
v___x_580_ = ((lean_object*)(l_Lean_Meta_Grind_AC_internalize___closed__9));
v___x_581_ = l_Lean_stringToMessageData(v___x_580_);
return v___x_581_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_internalize(lean_object* v_e_582_, lean_object* v_parent_x3f_583_, lean_object* v_a_584_, lean_object* v_a_585_, lean_object* v_a_586_, lean_object* v_a_587_, lean_object* v_a_588_, lean_object* v_a_589_, lean_object* v_a_590_, lean_object* v_a_591_, lean_object* v_a_592_, lean_object* v_a_593_){
_start:
{
lean_object* v___y_596_; lean_object* v___y_597_; lean_object* v___y_598_; lean_object* v___y_599_; lean_object* v___y_600_; lean_object* v___y_601_; lean_object* v___y_602_; lean_object* v___y_603_; lean_object* v___y_604_; lean_object* v___y_605_; lean_object* v___y_606_; lean_object* v___x_610_; 
v___x_610_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_586_);
if (lean_obj_tag(v___x_610_) == 0)
{
lean_object* v_a_611_; lean_object* v___x_613_; uint8_t v_isShared_614_; uint8_t v_isSharedCheck_724_; 
v_a_611_ = lean_ctor_get(v___x_610_, 0);
v_isSharedCheck_724_ = !lean_is_exclusive(v___x_610_);
if (v_isSharedCheck_724_ == 0)
{
v___x_613_ = v___x_610_;
v_isShared_614_ = v_isSharedCheck_724_;
goto v_resetjp_612_;
}
else
{
lean_inc(v_a_611_);
lean_dec(v___x_610_);
v___x_613_ = lean_box(0);
v_isShared_614_ = v_isSharedCheck_724_;
goto v_resetjp_612_;
}
v_resetjp_612_:
{
uint8_t v_ac_620_; 
v_ac_620_ = lean_ctor_get_uint8(v_a_611_, sizeof(void*)*14 + 26);
lean_dec(v_a_611_);
if (v_ac_620_ == 0)
{
lean_object* v___x_621_; lean_object* v___x_622_; 
lean_del_object(v___x_613_);
lean_dec(v_parent_x3f_583_);
lean_dec_ref(v_e_582_);
v___x_621_ = lean_box(0);
v___x_622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_622_, 0, v___x_621_);
return v___x_622_;
}
else
{
uint8_t v___x_623_; 
v___x_623_ = l_Lean_Expr_isApp(v_e_582_);
if (v___x_623_ == 0)
{
lean_dec(v_parent_x3f_583_);
lean_dec_ref(v_e_582_);
goto v___jp_615_;
}
else
{
lean_object* v___x_624_; uint8_t v___x_625_; 
v___x_624_ = l_Lean_Expr_appFn_x21(v_e_582_);
v___x_625_ = l_Lean_Expr_isApp(v___x_624_);
if (v___x_625_ == 0)
{
lean_dec_ref(v___x_624_);
lean_dec(v_parent_x3f_583_);
lean_dec_ref(v_e_582_);
goto v___jp_615_;
}
else
{
lean_object* v___x_626_; lean_object* v___x_627_; 
lean_del_object(v___x_613_);
v___x_626_ = l_Lean_Expr_appFn_x21(v___x_624_);
lean_dec_ref(v___x_624_);
lean_inc_ref(v___x_626_);
v___x_627_ = l_Lean_Meta_Grind_AC_getOpId_x3f(v___x_626_, v_a_584_, v_a_585_, v_a_586_, v_a_587_, v_a_588_, v_a_589_, v_a_590_, v_a_591_, v_a_592_, v_a_593_);
if (lean_obj_tag(v___x_627_) == 0)
{
lean_object* v_a_628_; lean_object* v___x_630_; uint8_t v_isShared_631_; uint8_t v_isSharedCheck_715_; 
v_a_628_ = lean_ctor_get(v___x_627_, 0);
v_isSharedCheck_715_ = !lean_is_exclusive(v___x_627_);
if (v_isSharedCheck_715_ == 0)
{
v___x_630_ = v___x_627_;
v_isShared_631_ = v_isSharedCheck_715_;
goto v_resetjp_629_;
}
else
{
lean_inc(v_a_628_);
lean_dec(v___x_627_);
v___x_630_ = lean_box(0);
v_isShared_631_ = v_isSharedCheck_715_;
goto v_resetjp_629_;
}
v_resetjp_629_:
{
if (lean_obj_tag(v_a_628_) == 1)
{
lean_object* v_val_632_; lean_object* v___x_633_; lean_object* v_a_634_; lean_object* v___x_636_; uint8_t v_isShared_637_; uint8_t v_isSharedCheck_710_; 
lean_del_object(v___x_630_);
v_val_632_ = lean_ctor_get(v_a_628_, 0);
lean_inc(v_val_632_);
lean_dec_ref_known(v_a_628_, 1);
v___x_633_ = l___private_Lean_Meta_Tactic_Grind_AC_Internalize_0__Lean_Meta_Grind_AC_isParentSameOpApp___redArg(v_parent_x3f_583_, v___x_626_);
lean_dec_ref(v___x_626_);
v_a_634_ = lean_ctor_get(v___x_633_, 0);
v_isSharedCheck_710_ = !lean_is_exclusive(v___x_633_);
if (v_isSharedCheck_710_ == 0)
{
v___x_636_ = v___x_633_;
v_isShared_637_ = v_isSharedCheck_710_;
goto v_resetjp_635_;
}
else
{
lean_inc(v_a_634_);
lean_dec(v___x_633_);
v___x_636_ = lean_box(0);
v_isShared_637_ = v_isSharedCheck_710_;
goto v_resetjp_635_;
}
v_resetjp_635_:
{
uint8_t v___x_638_; 
v___x_638_ = lean_unbox(v_a_634_);
lean_dec(v_a_634_);
if (v___x_638_ == 0)
{
lean_object* v___x_639_; 
lean_del_object(v___x_636_);
v___x_639_ = l_Lean_Meta_Grind_AC_ACM_getStruct(v_val_632_, v_a_584_, v_a_585_, v_a_586_, v_a_587_, v_a_588_, v_a_589_, v_a_590_, v_a_591_, v_a_592_, v_a_593_);
if (lean_obj_tag(v___x_639_) == 0)
{
lean_object* v_a_640_; lean_object* v___x_642_; uint8_t v_isShared_643_; uint8_t v_isSharedCheck_697_; 
v_a_640_ = lean_ctor_get(v___x_639_, 0);
v_isSharedCheck_697_ = !lean_is_exclusive(v___x_639_);
if (v_isSharedCheck_697_ == 0)
{
v___x_642_ = v___x_639_;
v_isShared_643_ = v_isSharedCheck_697_;
goto v_resetjp_641_;
}
else
{
lean_inc(v_a_640_);
lean_dec(v___x_639_);
v___x_642_ = lean_box(0);
v_isShared_643_ = v_isSharedCheck_697_;
goto v_resetjp_641_;
}
v_resetjp_641_:
{
lean_object* v_denote_644_; uint8_t v___x_645_; 
v_denote_644_ = lean_ctor_get(v_a_640_, 12);
lean_inc_ref(v_denote_644_);
lean_dec(v_a_640_);
v___x_645_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0___redArg(v_denote_644_, v_e_582_);
lean_dec_ref(v_denote_644_);
if (v___x_645_ == 0)
{
lean_object* v___x_646_; 
lean_del_object(v___x_642_);
lean_inc_ref(v_e_582_);
v___x_646_ = l_Lean_Meta_Grind_AC_reify(v_e_582_, v_val_632_, v_a_584_, v_a_585_, v_a_586_, v_a_587_, v_a_588_, v_a_589_, v_a_590_, v_a_591_, v_a_592_, v_a_593_);
if (lean_obj_tag(v___x_646_) == 0)
{
lean_object* v_a_647_; lean_object* v___x_648_; lean_object* v___f_649_; lean_object* v___x_650_; 
v_a_647_ = lean_ctor_get(v___x_646_, 0);
lean_inc_n(v_a_647_, 2);
lean_dec_ref_known(v___x_646_, 1);
v___x_648_ = lean_box(v___x_625_);
lean_inc_ref(v_e_582_);
v___f_649_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_AC_internalize___lam__0___boxed), 4, 3);
lean_closure_set(v___f_649_, 0, v_e_582_);
lean_closure_set(v___f_649_, 1, v_a_647_);
lean_closure_set(v___f_649_, 2, v___x_648_);
v___x_650_ = l_Lean_Meta_Grind_AC_modifyStruct___redArg(v___f_649_, v_val_632_, v_a_584_);
if (lean_obj_tag(v___x_650_) == 0)
{
lean_object* v___x_652_; uint8_t v_isShared_653_; uint8_t v_isSharedCheck_683_; 
v_isSharedCheck_683_ = !lean_is_exclusive(v___x_650_);
if (v_isSharedCheck_683_ == 0)
{
lean_object* v_unused_684_; 
v_unused_684_ = lean_ctor_get(v___x_650_, 0);
lean_dec(v_unused_684_);
v___x_652_ = v___x_650_;
v_isShared_653_ = v_isSharedCheck_683_;
goto v_resetjp_651_;
}
else
{
lean_dec(v___x_650_);
v___x_652_ = lean_box(0);
v_isShared_653_ = v_isSharedCheck_683_;
goto v_resetjp_651_;
}
v_resetjp_651_:
{
lean_object* v_toCold_654_; lean_object* v_options_655_; uint8_t v_hasTrace_656_; 
v_toCold_654_ = lean_ctor_get(v_a_592_, 0);
v_options_655_ = lean_ctor_get(v_toCold_654_, 2);
v_hasTrace_656_ = lean_ctor_get_uint8(v_options_655_, sizeof(void*)*1);
if (v_hasTrace_656_ == 0)
{
lean_del_object(v___x_652_);
lean_dec(v_a_647_);
v___y_596_ = v_val_632_;
v___y_597_ = v_a_584_;
v___y_598_ = v_a_585_;
v___y_599_ = v_a_586_;
v___y_600_ = v_a_587_;
v___y_601_ = v_a_588_;
v___y_602_ = v_a_589_;
v___y_603_ = v_a_590_;
v___y_604_ = v_a_591_;
v___y_605_ = v_a_592_;
v___y_606_ = v_a_593_;
goto v___jp_595_;
}
else
{
lean_object* v_inheritedTraceOptions_657_; lean_object* v___x_658_; lean_object* v___x_659_; uint8_t v___x_660_; 
v_inheritedTraceOptions_657_ = lean_ctor_get(v_toCold_654_, 11);
v___x_658_ = ((lean_object*)(l_Lean_Meta_Grind_AC_internalize___closed__3));
v___x_659_ = lean_obj_once(&l_Lean_Meta_Grind_AC_internalize___closed__6, &l_Lean_Meta_Grind_AC_internalize___closed__6_once, _init_l_Lean_Meta_Grind_AC_internalize___closed__6);
v___x_660_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_657_, v_options_655_, v___x_659_);
if (v___x_660_ == 0)
{
lean_del_object(v___x_652_);
lean_dec(v_a_647_);
v___y_596_ = v_val_632_;
v___y_597_ = v_a_584_;
v___y_598_ = v_a_585_;
v___y_599_ = v_a_586_;
v___y_600_ = v_a_587_;
v___y_601_ = v_a_588_;
v___y_602_ = v_a_589_;
v___y_603_ = v_a_590_;
v___y_604_ = v_a_591_;
v___y_605_ = v_a_592_;
v___y_606_ = v_a_593_;
goto v___jp_595_;
}
else
{
lean_object* v___x_661_; 
v___x_661_ = l_Lean_Grind_AC_Expr_denoteExpr___at___00Lean_Meta_Grind_AC_internalize_spec__2(v_a_647_, v_val_632_, v_a_584_, v_a_585_, v_a_586_, v_a_587_, v_a_588_, v_a_589_, v_a_590_, v_a_591_, v_a_592_, v_a_593_);
lean_dec(v_a_647_);
if (lean_obj_tag(v___x_661_) == 0)
{
lean_object* v_a_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_666_; 
v_a_662_ = lean_ctor_get(v___x_661_, 0);
lean_inc(v_a_662_);
lean_dec_ref_known(v___x_661_, 1);
v___x_663_ = lean_obj_once(&l_Lean_Meta_Grind_AC_internalize___closed__8, &l_Lean_Meta_Grind_AC_internalize___closed__8_once, _init_l_Lean_Meta_Grind_AC_internalize___closed__8);
lean_inc(v_val_632_);
v___x_664_ = l_Nat_reprFast(v_val_632_);
if (v_isShared_653_ == 0)
{
lean_ctor_set_tag(v___x_652_, 3);
lean_ctor_set(v___x_652_, 0, v___x_664_);
v___x_666_ = v___x_652_;
goto v_reusejp_665_;
}
else
{
lean_object* v_reuseFailAlloc_674_; 
v_reuseFailAlloc_674_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_674_, 0, v___x_664_);
v___x_666_ = v_reuseFailAlloc_674_;
goto v_reusejp_665_;
}
v_reusejp_665_:
{
lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; 
v___x_667_ = l_Lean_MessageData_ofFormat(v___x_666_);
v___x_668_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_668_, 0, v___x_663_);
lean_ctor_set(v___x_668_, 1, v___x_667_);
v___x_669_ = lean_obj_once(&l_Lean_Meta_Grind_AC_internalize___closed__10, &l_Lean_Meta_Grind_AC_internalize___closed__10_once, _init_l_Lean_Meta_Grind_AC_internalize___closed__10);
v___x_670_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_670_, 0, v___x_668_);
lean_ctor_set(v___x_670_, 1, v___x_669_);
v___x_671_ = l_Lean_MessageData_ofExpr(v_a_662_);
v___x_672_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_672_, 0, v___x_670_);
lean_ctor_set(v___x_672_, 1, v___x_671_);
v___x_673_ = l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3___redArg(v___x_658_, v___x_672_, v_a_590_, v_a_591_, v_a_592_, v_a_593_);
if (lean_obj_tag(v___x_673_) == 0)
{
lean_dec_ref_known(v___x_673_, 1);
v___y_596_ = v_val_632_;
v___y_597_ = v_a_584_;
v___y_598_ = v_a_585_;
v___y_599_ = v_a_586_;
v___y_600_ = v_a_587_;
v___y_601_ = v_a_588_;
v___y_602_ = v_a_589_;
v___y_603_ = v_a_590_;
v___y_604_ = v_a_591_;
v___y_605_ = v_a_592_;
v___y_606_ = v_a_593_;
goto v___jp_595_;
}
else
{
lean_dec(v_val_632_);
lean_dec_ref(v_e_582_);
return v___x_673_;
}
}
}
else
{
lean_object* v_a_675_; lean_object* v___x_677_; uint8_t v_isShared_678_; uint8_t v_isSharedCheck_682_; 
lean_del_object(v___x_652_);
lean_dec(v_val_632_);
lean_dec_ref(v_e_582_);
v_a_675_ = lean_ctor_get(v___x_661_, 0);
v_isSharedCheck_682_ = !lean_is_exclusive(v___x_661_);
if (v_isSharedCheck_682_ == 0)
{
v___x_677_ = v___x_661_;
v_isShared_678_ = v_isSharedCheck_682_;
goto v_resetjp_676_;
}
else
{
lean_inc(v_a_675_);
lean_dec(v___x_661_);
v___x_677_ = lean_box(0);
v_isShared_678_ = v_isSharedCheck_682_;
goto v_resetjp_676_;
}
v_resetjp_676_:
{
lean_object* v___x_680_; 
if (v_isShared_678_ == 0)
{
v___x_680_ = v___x_677_;
goto v_reusejp_679_;
}
else
{
lean_object* v_reuseFailAlloc_681_; 
v_reuseFailAlloc_681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_681_, 0, v_a_675_);
v___x_680_ = v_reuseFailAlloc_681_;
goto v_reusejp_679_;
}
v_reusejp_679_:
{
return v___x_680_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_647_);
lean_dec(v_val_632_);
lean_dec_ref(v_e_582_);
return v___x_650_;
}
}
else
{
lean_object* v_a_685_; lean_object* v___x_687_; uint8_t v_isShared_688_; uint8_t v_isSharedCheck_692_; 
lean_dec(v_val_632_);
lean_dec_ref(v_e_582_);
v_a_685_ = lean_ctor_get(v___x_646_, 0);
v_isSharedCheck_692_ = !lean_is_exclusive(v___x_646_);
if (v_isSharedCheck_692_ == 0)
{
v___x_687_ = v___x_646_;
v_isShared_688_ = v_isSharedCheck_692_;
goto v_resetjp_686_;
}
else
{
lean_inc(v_a_685_);
lean_dec(v___x_646_);
v___x_687_ = lean_box(0);
v_isShared_688_ = v_isSharedCheck_692_;
goto v_resetjp_686_;
}
v_resetjp_686_:
{
lean_object* v___x_690_; 
if (v_isShared_688_ == 0)
{
v___x_690_ = v___x_687_;
goto v_reusejp_689_;
}
else
{
lean_object* v_reuseFailAlloc_691_; 
v_reuseFailAlloc_691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_691_, 0, v_a_685_);
v___x_690_ = v_reuseFailAlloc_691_;
goto v_reusejp_689_;
}
v_reusejp_689_:
{
return v___x_690_;
}
}
}
}
else
{
lean_object* v___x_693_; lean_object* v___x_695_; 
lean_dec(v_val_632_);
lean_dec_ref(v_e_582_);
v___x_693_ = lean_box(0);
if (v_isShared_643_ == 0)
{
lean_ctor_set(v___x_642_, 0, v___x_693_);
v___x_695_ = v___x_642_;
goto v_reusejp_694_;
}
else
{
lean_object* v_reuseFailAlloc_696_; 
v_reuseFailAlloc_696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_696_, 0, v___x_693_);
v___x_695_ = v_reuseFailAlloc_696_;
goto v_reusejp_694_;
}
v_reusejp_694_:
{
return v___x_695_;
}
}
}
}
else
{
lean_object* v_a_698_; lean_object* v___x_700_; uint8_t v_isShared_701_; uint8_t v_isSharedCheck_705_; 
lean_dec(v_val_632_);
lean_dec_ref(v_e_582_);
v_a_698_ = lean_ctor_get(v___x_639_, 0);
v_isSharedCheck_705_ = !lean_is_exclusive(v___x_639_);
if (v_isSharedCheck_705_ == 0)
{
v___x_700_ = v___x_639_;
v_isShared_701_ = v_isSharedCheck_705_;
goto v_resetjp_699_;
}
else
{
lean_inc(v_a_698_);
lean_dec(v___x_639_);
v___x_700_ = lean_box(0);
v_isShared_701_ = v_isSharedCheck_705_;
goto v_resetjp_699_;
}
v_resetjp_699_:
{
lean_object* v___x_703_; 
if (v_isShared_701_ == 0)
{
v___x_703_ = v___x_700_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v_a_698_);
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
lean_object* v___x_706_; lean_object* v___x_708_; 
lean_dec(v_val_632_);
lean_dec_ref(v_e_582_);
v___x_706_ = lean_box(0);
if (v_isShared_637_ == 0)
{
lean_ctor_set(v___x_636_, 0, v___x_706_);
v___x_708_ = v___x_636_;
goto v_reusejp_707_;
}
else
{
lean_object* v_reuseFailAlloc_709_; 
v_reuseFailAlloc_709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_709_, 0, v___x_706_);
v___x_708_ = v_reuseFailAlloc_709_;
goto v_reusejp_707_;
}
v_reusejp_707_:
{
return v___x_708_;
}
}
}
}
else
{
lean_object* v___x_711_; lean_object* v___x_713_; 
lean_dec(v_a_628_);
lean_dec_ref(v___x_626_);
lean_dec(v_parent_x3f_583_);
lean_dec_ref(v_e_582_);
v___x_711_ = lean_box(0);
if (v_isShared_631_ == 0)
{
lean_ctor_set(v___x_630_, 0, v___x_711_);
v___x_713_ = v___x_630_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_714_; 
v_reuseFailAlloc_714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_714_, 0, v___x_711_);
v___x_713_ = v_reuseFailAlloc_714_;
goto v_reusejp_712_;
}
v_reusejp_712_:
{
return v___x_713_;
}
}
}
}
else
{
lean_object* v_a_716_; lean_object* v___x_718_; uint8_t v_isShared_719_; uint8_t v_isSharedCheck_723_; 
lean_dec_ref(v___x_626_);
lean_dec(v_parent_x3f_583_);
lean_dec_ref(v_e_582_);
v_a_716_ = lean_ctor_get(v___x_627_, 0);
v_isSharedCheck_723_ = !lean_is_exclusive(v___x_627_);
if (v_isSharedCheck_723_ == 0)
{
v___x_718_ = v___x_627_;
v_isShared_719_ = v_isSharedCheck_723_;
goto v_resetjp_717_;
}
else
{
lean_inc(v_a_716_);
lean_dec(v___x_627_);
v___x_718_ = lean_box(0);
v_isShared_719_ = v_isSharedCheck_723_;
goto v_resetjp_717_;
}
v_resetjp_717_:
{
lean_object* v___x_721_; 
if (v_isShared_719_ == 0)
{
v___x_721_ = v___x_718_;
goto v_reusejp_720_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v_a_716_);
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
}
}
v___jp_615_:
{
lean_object* v___x_616_; lean_object* v___x_618_; 
v___x_616_ = lean_box(0);
if (v_isShared_614_ == 0)
{
lean_ctor_set(v___x_613_, 0, v___x_616_);
v___x_618_ = v___x_613_;
goto v_reusejp_617_;
}
else
{
lean_object* v_reuseFailAlloc_619_; 
v_reuseFailAlloc_619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_619_, 0, v___x_616_);
v___x_618_ = v_reuseFailAlloc_619_;
goto v_reusejp_617_;
}
v_reusejp_617_:
{
return v___x_618_;
}
}
}
}
else
{
lean_object* v_a_725_; lean_object* v___x_727_; uint8_t v_isShared_728_; uint8_t v_isSharedCheck_732_; 
lean_dec(v_parent_x3f_583_);
lean_dec_ref(v_e_582_);
v_a_725_ = lean_ctor_get(v___x_610_, 0);
v_isSharedCheck_732_ = !lean_is_exclusive(v___x_610_);
if (v_isSharedCheck_732_ == 0)
{
v___x_727_ = v___x_610_;
v_isShared_728_ = v_isSharedCheck_732_;
goto v_resetjp_726_;
}
else
{
lean_inc(v_a_725_);
lean_dec(v___x_610_);
v___x_727_ = lean_box(0);
v_isShared_728_ = v_isSharedCheck_732_;
goto v_resetjp_726_;
}
v_resetjp_726_:
{
lean_object* v___x_730_; 
if (v_isShared_728_ == 0)
{
v___x_730_ = v___x_727_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v_a_725_);
v___x_730_ = v_reuseFailAlloc_731_;
goto v_reusejp_729_;
}
v_reusejp_729_:
{
return v___x_730_;
}
}
}
v___jp_595_:
{
lean_object* v___x_607_; 
lean_inc_ref(v_e_582_);
v___x_607_ = l_Lean_Meta_Grind_AC_addTermOpId___redArg(v_e_582_, v___y_596_, v___y_597_);
lean_dec(v___y_596_);
if (lean_obj_tag(v___x_607_) == 0)
{
lean_object* v___x_608_; lean_object* v___x_609_; 
lean_dec_ref_known(v___x_607_, 1);
v___x_608_ = l_Lean_Meta_Grind_AC_acExt;
v___x_609_ = l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(v___x_608_, v_e_582_, v___y_597_, v___y_598_, v___y_599_, v___y_600_, v___y_601_, v___y_602_, v___y_603_, v___y_604_, v___y_605_, v___y_606_);
return v___x_609_;
}
else
{
lean_dec_ref(v_e_582_);
return v___x_607_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_internalize___boxed(lean_object* v_e_733_, lean_object* v_parent_x3f_734_, lean_object* v_a_735_, lean_object* v_a_736_, lean_object* v_a_737_, lean_object* v_a_738_, lean_object* v_a_739_, lean_object* v_a_740_, lean_object* v_a_741_, lean_object* v_a_742_, lean_object* v_a_743_, lean_object* v_a_744_, lean_object* v_a_745_){
_start:
{
lean_object* v_res_746_; 
v_res_746_ = l_Lean_Meta_Grind_AC_internalize(v_e_733_, v_parent_x3f_734_, v_a_735_, v_a_736_, v_a_737_, v_a_738_, v_a_739_, v_a_740_, v_a_741_, v_a_742_, v_a_743_, v_a_744_);
lean_dec(v_a_744_);
lean_dec_ref(v_a_743_);
lean_dec(v_a_742_);
lean_dec_ref(v_a_741_);
lean_dec(v_a_740_);
lean_dec_ref(v_a_739_);
lean_dec(v_a_738_);
lean_dec_ref(v_a_737_);
lean_dec(v_a_736_);
lean_dec(v_a_735_);
return v_res_746_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0(lean_object* v_00_u03b2_747_, lean_object* v_x_748_, lean_object* v_x_749_){
_start:
{
uint8_t v___x_750_; 
v___x_750_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0___redArg(v_x_748_, v_x_749_);
return v___x_750_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0___boxed(lean_object* v_00_u03b2_751_, lean_object* v_x_752_, lean_object* v_x_753_){
_start:
{
uint8_t v_res_754_; lean_object* v_r_755_; 
v_res_754_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0(v_00_u03b2_751_, v_x_752_, v_x_753_);
lean_dec_ref(v_x_753_);
lean_dec_ref(v_x_752_);
v_r_755_ = lean_box(v_res_754_);
return v_r_755_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1(lean_object* v_00_u03b2_756_, lean_object* v_x_757_, lean_object* v_x_758_, lean_object* v_x_759_){
_start:
{
lean_object* v___x_760_; 
v___x_760_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1___redArg(v_x_757_, v_x_758_, v_x_759_);
return v___x_760_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3(lean_object* v_cls_761_, lean_object* v_msg_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_){
_start:
{
lean_object* v___x_775_; 
v___x_775_ = l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3___redArg(v_cls_761_, v_msg_762_, v___y_770_, v___y_771_, v___y_772_, v___y_773_);
return v___x_775_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3___boxed(lean_object* v_cls_776_, lean_object* v_msg_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_){
_start:
{
lean_object* v_res_790_; 
v_res_790_ = l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3(v_cls_776_, v_msg_777_, v___y_778_, v___y_779_, v___y_780_, v___y_781_, v___y_782_, v___y_783_, v___y_784_, v___y_785_, v___y_786_, v___y_787_, v___y_788_);
lean_dec(v___y_788_);
lean_dec_ref(v___y_787_);
lean_dec(v___y_786_);
lean_dec_ref(v___y_785_);
lean_dec(v___y_784_);
lean_dec_ref(v___y_783_);
lean_dec(v___y_782_);
lean_dec_ref(v___y_781_);
lean_dec(v___y_780_);
lean_dec(v___y_779_);
lean_dec(v___y_778_);
return v_res_790_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0(lean_object* v_00_u03b2_791_, lean_object* v_x_792_, size_t v_x_793_, lean_object* v_x_794_){
_start:
{
uint8_t v___x_795_; 
v___x_795_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0___redArg(v_x_792_, v_x_793_, v_x_794_);
return v___x_795_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0___boxed(lean_object* v_00_u03b2_796_, lean_object* v_x_797_, lean_object* v_x_798_, lean_object* v_x_799_){
_start:
{
size_t v_x_40159__boxed_800_; uint8_t v_res_801_; lean_object* v_r_802_; 
v_x_40159__boxed_800_ = lean_unbox_usize(v_x_798_);
lean_dec(v_x_798_);
v_res_801_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0(v_00_u03b2_796_, v_x_797_, v_x_40159__boxed_800_, v_x_799_);
lean_dec_ref(v_x_799_);
lean_dec_ref(v_x_797_);
v_r_802_ = lean_box(v_res_801_);
return v_r_802_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2(lean_object* v_00_u03b2_803_, lean_object* v_x_804_, size_t v_x_805_, size_t v_x_806_, lean_object* v_x_807_, lean_object* v_x_808_){
_start:
{
lean_object* v___x_809_; 
v___x_809_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___redArg(v_x_804_, v_x_805_, v_x_806_, v_x_807_, v_x_808_);
return v___x_809_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___boxed(lean_object* v_00_u03b2_810_, lean_object* v_x_811_, lean_object* v_x_812_, lean_object* v_x_813_, lean_object* v_x_814_, lean_object* v_x_815_){
_start:
{
size_t v_x_40170__boxed_816_; size_t v_x_40171__boxed_817_; lean_object* v_res_818_; 
v_x_40170__boxed_816_ = lean_unbox_usize(v_x_812_);
lean_dec(v_x_812_);
v_x_40171__boxed_817_ = lean_unbox_usize(v_x_813_);
lean_dec(v_x_813_);
v_res_818_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2(v_00_u03b2_810_, v_x_811_, v_x_40170__boxed_816_, v_x_40171__boxed_817_, v_x_814_, v_x_815_);
return v_res_818_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_819_, lean_object* v_keys_820_, lean_object* v_vals_821_, lean_object* v_heq_822_, lean_object* v_i_823_, lean_object* v_k_824_){
_start:
{
uint8_t v___x_825_; 
v___x_825_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0_spec__1___redArg(v_keys_820_, v_i_823_, v_k_824_);
return v___x_825_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_826_, lean_object* v_keys_827_, lean_object* v_vals_828_, lean_object* v_heq_829_, lean_object* v_i_830_, lean_object* v_k_831_){
_start:
{
uint8_t v_res_832_; lean_object* v_r_833_; 
v_res_832_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0_spec__1(v_00_u03b2_826_, v_keys_827_, v_vals_828_, v_heq_829_, v_i_830_, v_k_831_);
lean_dec_ref(v_k_831_);
lean_dec_ref(v_vals_828_);
lean_dec_ref(v_keys_827_);
v_r_833_ = lean_box(v_res_832_);
return v_r_833_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_834_, lean_object* v_n_835_, lean_object* v_k_836_, lean_object* v_v_837_){
_start:
{
lean_object* v___x_838_; 
v___x_838_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2_spec__4___redArg(v_n_835_, v_k_836_, v_v_837_);
return v___x_838_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_839_, size_t v_depth_840_, lean_object* v_keys_841_, lean_object* v_vals_842_, lean_object* v_heq_843_, lean_object* v_i_844_, lean_object* v_entries_845_){
_start:
{
lean_object* v___x_846_; 
v___x_846_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2_spec__5___redArg(v_depth_840_, v_keys_841_, v_vals_842_, v_i_844_, v_entries_845_);
return v___x_846_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_847_, lean_object* v_depth_848_, lean_object* v_keys_849_, lean_object* v_vals_850_, lean_object* v_heq_851_, lean_object* v_i_852_, lean_object* v_entries_853_){
_start:
{
size_t v_depth_boxed_854_; lean_object* v_res_855_; 
v_depth_boxed_854_ = lean_unbox_usize(v_depth_848_);
lean_dec(v_depth_848_);
v_res_855_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2_spec__5(v_00_u03b2_847_, v_depth_boxed_854_, v_keys_849_, v_vals_850_, v_heq_851_, v_i_852_, v_entries_853_);
lean_dec_ref(v_vals_850_);
lean_dec_ref(v_keys_849_);
return v_res_855_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2_spec__4_spec__8(lean_object* v_00_u03b2_856_, lean_object* v_x_857_, lean_object* v_x_858_, lean_object* v_x_859_, lean_object* v_x_860_){
_start:
{
lean_object* v___x_861_; 
v___x_861_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2_spec__4_spec__8___redArg(v_x_857_, v_x_858_, v_x_859_, v_x_860_);
return v___x_861_;
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
