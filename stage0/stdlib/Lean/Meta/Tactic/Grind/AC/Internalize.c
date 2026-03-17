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
uint8_t l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
uint64_t l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_AC_ACM_getStruct(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_outOfBounds___redArg(lean_object*);
lean_object* l_Lean_PersistentArray_get_x21___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_AC_addTermOpId___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_AC_acExt;
lean_object* l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getConfig___redArg(lean_object*);
lean_object* l_Lean_Meta_Grind_AC_getOpId_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_AC_isOp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_AC_mkVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_AC_modifyStruct___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Internalize_0__Lean_Meta_Grind_AC_isParentSameOpApp___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Internalize_0__Lean_Meta_Grind_AC_isParentSameOpApp___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Internalize_0__Lean_Meta_Grind_AC_isParentSameOpApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Internalize_0__Lean_Meta_Grind_AC_isParentSameOpApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_reify(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_reify___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_AC_internalize_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_AC_internalize_spec__2___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_AC_internalize_spec__2___redArg___closed__0_value;
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_AC_internalize_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_AC_internalize_spec__2___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_AC_internalize_spec__2___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_AC_internalize_spec__2___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_AC_internalize_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_AC_internalize_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_AC_internalize_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_AC_internalize_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2_spec__5_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2_spec__5___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2_spec__6___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_internalize___lam__0(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_internalize___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Expr_denoteExpr___at___00Lean_Meta_Grind_AC_internalize_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Expr_denoteExpr___at___00Lean_Meta_Grind_AC_internalize_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__4___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__4___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__4___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__4___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__4___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__4___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__4___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__4___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Meta_Grind_AC_internalize___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_Lean_Meta_Grind_AC_internalize___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_AC_internalize___closed__4_value;
static lean_once_cell_t l_Lean_Meta_Grind_AC_internalize___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_AC_internalize___closed__5;
static const lean_string_object l_Lean_Meta_Grind_AC_internalize___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "] "};
static const lean_object* l_Lean_Meta_Grind_AC_internalize___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_AC_internalize___closed__6_value;
static lean_once_cell_t l_Lean_Meta_Grind_AC_internalize___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_AC_internalize___closed__7;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_internalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_internalize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2_spec__6(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2_spec__5_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Internalize_0__Lean_Meta_Grind_AC_isParentSameOpApp___redArg(lean_object* v_parent_x3f_1_, lean_object* v_op_2_){
_start:
{
if (lean_obj_tag(v_parent_x3f_1_) == 1)
{
lean_object* v_val_4_; lean_object* v___x_6_; uint8_t v_isShared_7_; uint8_t v_isSharedCheck_24_; 
v_val_4_ = lean_ctor_get(v_parent_x3f_1_, 0);
v_isSharedCheck_24_ = !lean_is_exclusive(v_parent_x3f_1_);
if (v_isSharedCheck_24_ == 0)
{
v___x_6_ = v_parent_x3f_1_;
v_isShared_7_ = v_isSharedCheck_24_;
goto v_resetjp_5_;
}
else
{
lean_inc(v_val_4_);
lean_dec(v_parent_x3f_1_);
v___x_6_ = lean_box(0);
v_isShared_7_ = v_isSharedCheck_24_;
goto v_resetjp_5_;
}
v_resetjp_5_:
{
uint8_t v___y_9_; uint8_t v___x_21_; 
v___x_21_ = l_Lean_Expr_isApp(v_val_4_);
if (v___x_21_ == 0)
{
v___y_9_ = v___x_21_;
goto v___jp_8_;
}
else
{
lean_object* v___x_22_; uint8_t v___x_23_; 
v___x_22_ = l_Lean_Expr_appFn_x21(v_val_4_);
v___x_23_ = l_Lean_Expr_isApp(v___x_22_);
lean_dec_ref(v___x_22_);
v___y_9_ = v___x_23_;
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
lean_object* v___x_14_; lean_object* v___x_15_; uint8_t v___x_16_; lean_object* v___x_17_; lean_object* v___x_19_; 
v___x_14_ = l_Lean_Expr_appFn_x21(v_val_4_);
lean_dec(v_val_4_);
v___x_15_ = l_Lean_Expr_appFn_x21(v___x_14_);
lean_dec_ref(v___x_14_);
v___x_16_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_15_, v_op_2_);
lean_dec_ref(v___x_15_);
v___x_17_ = lean_box(v___x_16_);
if (v_isShared_7_ == 0)
{
lean_ctor_set_tag(v___x_6_, 0);
lean_ctor_set(v___x_6_, 0, v___x_17_);
v___x_19_ = v___x_6_;
goto v_reusejp_18_;
}
else
{
lean_object* v_reuseFailAlloc_20_; 
v_reuseFailAlloc_20_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_20_, 0, v___x_17_);
v___x_19_ = v_reuseFailAlloc_20_;
goto v_reusejp_18_;
}
v_reusejp_18_:
{
return v___x_19_;
}
}
}
}
}
else
{
uint8_t v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; 
lean_dec(v_parent_x3f_1_);
v___x_25_ = 0;
v___x_26_ = lean_box(v___x_25_);
v___x_27_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_27_, 0, v___x_26_);
return v___x_27_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Internalize_0__Lean_Meta_Grind_AC_isParentSameOpApp___redArg___boxed(lean_object* v_parent_x3f_28_, lean_object* v_op_29_, lean_object* v_a_30_){
_start:
{
lean_object* v_res_31_; 
v_res_31_ = l___private_Lean_Meta_Tactic_Grind_AC_Internalize_0__Lean_Meta_Grind_AC_isParentSameOpApp___redArg(v_parent_x3f_28_, v_op_29_);
lean_dec_ref(v_op_29_);
return v_res_31_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Internalize_0__Lean_Meta_Grind_AC_isParentSameOpApp(lean_object* v_parent_x3f_32_, lean_object* v_op_33_, lean_object* v_a_34_, lean_object* v_a_35_, lean_object* v_a_36_, lean_object* v_a_37_, lean_object* v_a_38_, lean_object* v_a_39_, lean_object* v_a_40_, lean_object* v_a_41_, lean_object* v_a_42_, lean_object* v_a_43_){
_start:
{
lean_object* v___x_45_; 
v___x_45_ = l___private_Lean_Meta_Tactic_Grind_AC_Internalize_0__Lean_Meta_Grind_AC_isParentSameOpApp___redArg(v_parent_x3f_32_, v_op_33_);
return v___x_45_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Internalize_0__Lean_Meta_Grind_AC_isParentSameOpApp___boxed(lean_object* v_parent_x3f_46_, lean_object* v_op_47_, lean_object* v_a_48_, lean_object* v_a_49_, lean_object* v_a_50_, lean_object* v_a_51_, lean_object* v_a_52_, lean_object* v_a_53_, lean_object* v_a_54_, lean_object* v_a_55_, lean_object* v_a_56_, lean_object* v_a_57_, lean_object* v_a_58_){
_start:
{
lean_object* v_res_59_; 
v_res_59_ = l___private_Lean_Meta_Tactic_Grind_AC_Internalize_0__Lean_Meta_Grind_AC_isParentSameOpApp(v_parent_x3f_46_, v_op_47_, v_a_48_, v_a_49_, v_a_50_, v_a_51_, v_a_52_, v_a_53_, v_a_54_, v_a_55_, v_a_56_, v_a_57_);
lean_dec(v_a_57_);
lean_dec_ref(v_a_56_);
lean_dec(v_a_55_);
lean_dec_ref(v_a_54_);
lean_dec(v_a_53_);
lean_dec_ref(v_a_52_);
lean_dec(v_a_51_);
lean_dec_ref(v_a_50_);
lean_dec(v_a_49_);
lean_dec(v_a_48_);
lean_dec_ref(v_op_47_);
return v_res_59_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_reify(lean_object* v_e_60_, lean_object* v_a_61_, lean_object* v_a_62_, lean_object* v_a_63_, lean_object* v_a_64_, lean_object* v_a_65_, lean_object* v_a_66_, lean_object* v_a_67_, lean_object* v_a_68_, lean_object* v_a_69_, lean_object* v_a_70_, lean_object* v_a_71_){
_start:
{
lean_object* v___x_73_; 
v___x_73_ = l_Lean_Meta_Grind_AC_isOp_x3f(v_e_60_, v_a_61_, v_a_62_, v_a_63_, v_a_64_, v_a_65_, v_a_66_, v_a_67_, v_a_68_, v_a_69_, v_a_70_, v_a_71_);
if (lean_obj_tag(v___x_73_) == 0)
{
lean_object* v_a_74_; 
v_a_74_ = lean_ctor_get(v___x_73_, 0);
lean_inc(v_a_74_);
lean_dec_ref(v___x_73_);
if (lean_obj_tag(v_a_74_) == 1)
{
lean_object* v_val_75_; lean_object* v_fst_76_; lean_object* v_snd_77_; lean_object* v___x_79_; uint8_t v_isShared_80_; uint8_t v_isSharedCheck_95_; 
lean_dec_ref(v_e_60_);
v_val_75_ = lean_ctor_get(v_a_74_, 0);
lean_inc(v_val_75_);
lean_dec_ref(v_a_74_);
v_fst_76_ = lean_ctor_get(v_val_75_, 0);
v_snd_77_ = lean_ctor_get(v_val_75_, 1);
v_isSharedCheck_95_ = !lean_is_exclusive(v_val_75_);
if (v_isSharedCheck_95_ == 0)
{
v___x_79_ = v_val_75_;
v_isShared_80_ = v_isSharedCheck_95_;
goto v_resetjp_78_;
}
else
{
lean_inc(v_snd_77_);
lean_inc(v_fst_76_);
lean_dec(v_val_75_);
v___x_79_ = lean_box(0);
v_isShared_80_ = v_isSharedCheck_95_;
goto v_resetjp_78_;
}
v_resetjp_78_:
{
lean_object* v___x_81_; 
lean_inc(v_a_71_);
lean_inc_ref(v_a_70_);
lean_inc(v_a_69_);
lean_inc_ref(v_a_68_);
lean_inc(v_a_67_);
lean_inc_ref(v_a_66_);
lean_inc(v_a_65_);
lean_inc_ref(v_a_64_);
lean_inc(v_a_63_);
lean_inc(v_a_62_);
lean_inc(v_a_61_);
v___x_81_ = l_Lean_Meta_Grind_AC_reify(v_fst_76_, v_a_61_, v_a_62_, v_a_63_, v_a_64_, v_a_65_, v_a_66_, v_a_67_, v_a_68_, v_a_69_, v_a_70_, v_a_71_);
if (lean_obj_tag(v___x_81_) == 0)
{
lean_object* v_a_82_; lean_object* v___x_83_; 
v_a_82_ = lean_ctor_get(v___x_81_, 0);
lean_inc(v_a_82_);
lean_dec_ref(v___x_81_);
v___x_83_ = l_Lean_Meta_Grind_AC_reify(v_snd_77_, v_a_61_, v_a_62_, v_a_63_, v_a_64_, v_a_65_, v_a_66_, v_a_67_, v_a_68_, v_a_69_, v_a_70_, v_a_71_);
if (lean_obj_tag(v___x_83_) == 0)
{
lean_object* v_a_84_; lean_object* v___x_86_; uint8_t v_isShared_87_; uint8_t v_isSharedCheck_94_; 
v_a_84_ = lean_ctor_get(v___x_83_, 0);
v_isSharedCheck_94_ = !lean_is_exclusive(v___x_83_);
if (v_isSharedCheck_94_ == 0)
{
v___x_86_ = v___x_83_;
v_isShared_87_ = v_isSharedCheck_94_;
goto v_resetjp_85_;
}
else
{
lean_inc(v_a_84_);
lean_dec(v___x_83_);
v___x_86_ = lean_box(0);
v_isShared_87_ = v_isSharedCheck_94_;
goto v_resetjp_85_;
}
v_resetjp_85_:
{
lean_object* v___x_89_; 
if (v_isShared_80_ == 0)
{
lean_ctor_set_tag(v___x_79_, 1);
lean_ctor_set(v___x_79_, 1, v_a_84_);
lean_ctor_set(v___x_79_, 0, v_a_82_);
v___x_89_ = v___x_79_;
goto v_reusejp_88_;
}
else
{
lean_object* v_reuseFailAlloc_93_; 
v_reuseFailAlloc_93_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_93_, 0, v_a_82_);
lean_ctor_set(v_reuseFailAlloc_93_, 1, v_a_84_);
v___x_89_ = v_reuseFailAlloc_93_;
goto v_reusejp_88_;
}
v_reusejp_88_:
{
lean_object* v___x_91_; 
if (v_isShared_87_ == 0)
{
lean_ctor_set(v___x_86_, 0, v___x_89_);
v___x_91_ = v___x_86_;
goto v_reusejp_90_;
}
else
{
lean_object* v_reuseFailAlloc_92_; 
v_reuseFailAlloc_92_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_92_, 0, v___x_89_);
v___x_91_ = v_reuseFailAlloc_92_;
goto v_reusejp_90_;
}
v_reusejp_90_:
{
return v___x_91_;
}
}
}
}
else
{
lean_dec(v_a_82_);
lean_del_object(v___x_79_);
return v___x_83_;
}
}
else
{
lean_del_object(v___x_79_);
lean_dec(v_snd_77_);
lean_dec(v_a_71_);
lean_dec_ref(v_a_70_);
lean_dec(v_a_69_);
lean_dec_ref(v_a_68_);
lean_dec(v_a_67_);
lean_dec_ref(v_a_66_);
lean_dec(v_a_65_);
lean_dec_ref(v_a_64_);
lean_dec(v_a_63_);
lean_dec(v_a_62_);
lean_dec(v_a_61_);
return v___x_81_;
}
}
}
else
{
lean_object* v___x_96_; 
lean_dec(v_a_74_);
v___x_96_ = l_Lean_Meta_Grind_AC_mkVar(v_e_60_, v_a_61_, v_a_62_, v_a_63_, v_a_64_, v_a_65_, v_a_66_, v_a_67_, v_a_68_, v_a_69_, v_a_70_, v_a_71_);
if (lean_obj_tag(v___x_96_) == 0)
{
lean_object* v_a_97_; lean_object* v___x_99_; uint8_t v_isShared_100_; uint8_t v_isSharedCheck_105_; 
v_a_97_ = lean_ctor_get(v___x_96_, 0);
v_isSharedCheck_105_ = !lean_is_exclusive(v___x_96_);
if (v_isSharedCheck_105_ == 0)
{
v___x_99_ = v___x_96_;
v_isShared_100_ = v_isSharedCheck_105_;
goto v_resetjp_98_;
}
else
{
lean_inc(v_a_97_);
lean_dec(v___x_96_);
v___x_99_ = lean_box(0);
v_isShared_100_ = v_isSharedCheck_105_;
goto v_resetjp_98_;
}
v_resetjp_98_:
{
lean_object* v___x_101_; lean_object* v___x_103_; 
v___x_101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_101_, 0, v_a_97_);
if (v_isShared_100_ == 0)
{
lean_ctor_set(v___x_99_, 0, v___x_101_);
v___x_103_ = v___x_99_;
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
else
{
lean_object* v_a_106_; lean_object* v___x_108_; uint8_t v_isShared_109_; uint8_t v_isSharedCheck_113_; 
v_a_106_ = lean_ctor_get(v___x_96_, 0);
v_isSharedCheck_113_ = !lean_is_exclusive(v___x_96_);
if (v_isSharedCheck_113_ == 0)
{
v___x_108_ = v___x_96_;
v_isShared_109_ = v_isSharedCheck_113_;
goto v_resetjp_107_;
}
else
{
lean_inc(v_a_106_);
lean_dec(v___x_96_);
v___x_108_ = lean_box(0);
v_isShared_109_ = v_isSharedCheck_113_;
goto v_resetjp_107_;
}
v_resetjp_107_:
{
lean_object* v___x_111_; 
if (v_isShared_109_ == 0)
{
v___x_111_ = v___x_108_;
goto v_reusejp_110_;
}
else
{
lean_object* v_reuseFailAlloc_112_; 
v_reuseFailAlloc_112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_112_, 0, v_a_106_);
v___x_111_ = v_reuseFailAlloc_112_;
goto v_reusejp_110_;
}
v_reusejp_110_:
{
return v___x_111_;
}
}
}
}
}
else
{
lean_object* v_a_114_; lean_object* v___x_116_; uint8_t v_isShared_117_; uint8_t v_isSharedCheck_121_; 
lean_dec(v_a_71_);
lean_dec_ref(v_a_70_);
lean_dec(v_a_69_);
lean_dec_ref(v_a_68_);
lean_dec(v_a_67_);
lean_dec_ref(v_a_66_);
lean_dec(v_a_65_);
lean_dec_ref(v_a_64_);
lean_dec(v_a_63_);
lean_dec(v_a_62_);
lean_dec(v_a_61_);
lean_dec_ref(v_e_60_);
v_a_114_ = lean_ctor_get(v___x_73_, 0);
v_isSharedCheck_121_ = !lean_is_exclusive(v___x_73_);
if (v_isSharedCheck_121_ == 0)
{
v___x_116_ = v___x_73_;
v_isShared_117_ = v_isSharedCheck_121_;
goto v_resetjp_115_;
}
else
{
lean_inc(v_a_114_);
lean_dec(v___x_73_);
v___x_116_ = lean_box(0);
v_isShared_117_ = v_isSharedCheck_121_;
goto v_resetjp_115_;
}
v_resetjp_115_:
{
lean_object* v___x_119_; 
if (v_isShared_117_ == 0)
{
v___x_119_ = v___x_116_;
goto v_reusejp_118_;
}
else
{
lean_object* v_reuseFailAlloc_120_; 
v_reuseFailAlloc_120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_120_, 0, v_a_114_);
v___x_119_ = v_reuseFailAlloc_120_;
goto v_reusejp_118_;
}
v_reusejp_118_:
{
return v___x_119_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_reify___boxed(lean_object* v_e_122_, lean_object* v_a_123_, lean_object* v_a_124_, lean_object* v_a_125_, lean_object* v_a_126_, lean_object* v_a_127_, lean_object* v_a_128_, lean_object* v_a_129_, lean_object* v_a_130_, lean_object* v_a_131_, lean_object* v_a_132_, lean_object* v_a_133_, lean_object* v_a_134_){
_start:
{
lean_object* v_res_135_; 
v_res_135_ = l_Lean_Meta_Grind_AC_reify(v_e_122_, v_a_123_, v_a_124_, v_a_125_, v_a_126_, v_a_127_, v_a_128_, v_a_129_, v_a_130_, v_a_131_, v_a_132_, v_a_133_);
return v_res_135_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_AC_internalize_spec__2___redArg(lean_object* v_cls_139_, lean_object* v___y_140_){
_start:
{
lean_object* v_options_142_; uint8_t v_hasTrace_143_; 
v_options_142_ = lean_ctor_get(v___y_140_, 2);
v_hasTrace_143_ = lean_ctor_get_uint8(v_options_142_, sizeof(void*)*1);
if (v_hasTrace_143_ == 0)
{
lean_object* v___x_144_; lean_object* v___x_145_; 
lean_dec(v_cls_139_);
v___x_144_ = lean_box(v_hasTrace_143_);
v___x_145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_145_, 0, v___x_144_);
return v___x_145_;
}
else
{
lean_object* v_inheritedTraceOptions_146_; lean_object* v___x_147_; lean_object* v___x_148_; uint8_t v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; 
v_inheritedTraceOptions_146_ = lean_ctor_get(v___y_140_, 13);
v___x_147_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_AC_internalize_spec__2___redArg___closed__1));
v___x_148_ = l_Lean_Name_append(v___x_147_, v_cls_139_);
v___x_149_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_146_, v_options_142_, v___x_148_);
lean_dec(v___x_148_);
v___x_150_ = lean_box(v___x_149_);
v___x_151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_151_, 0, v___x_150_);
return v___x_151_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_AC_internalize_spec__2___redArg___boxed(lean_object* v_cls_152_, lean_object* v___y_153_, lean_object* v___y_154_){
_start:
{
lean_object* v_res_155_; 
v_res_155_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_AC_internalize_spec__2___redArg(v_cls_152_, v___y_153_);
lean_dec_ref(v___y_153_);
return v_res_155_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_AC_internalize_spec__2(lean_object* v_cls_156_, lean_object* v___y_157_, lean_object* v___y_158_, lean_object* v___y_159_, lean_object* v___y_160_, lean_object* v___y_161_, lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_){
_start:
{
lean_object* v___x_169_; 
v___x_169_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_AC_internalize_spec__2___redArg(v_cls_156_, v___y_166_);
return v___x_169_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_AC_internalize_spec__2___boxed(lean_object* v_cls_170_, lean_object* v___y_171_, lean_object* v___y_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_, lean_object* v___y_180_, lean_object* v___y_181_, lean_object* v___y_182_){
_start:
{
lean_object* v_res_183_; 
v_res_183_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_AC_internalize_spec__2(v_cls_170_, v___y_171_, v___y_172_, v___y_173_, v___y_174_, v___y_175_, v___y_176_, v___y_177_, v___y_178_, v___y_179_, v___y_180_, v___y_181_);
lean_dec(v___y_181_);
lean_dec_ref(v___y_180_);
lean_dec(v___y_179_);
lean_dec_ref(v___y_178_);
lean_dec(v___y_177_);
lean_dec_ref(v___y_176_);
lean_dec(v___y_175_);
lean_dec_ref(v___y_174_);
lean_dec(v___y_173_);
lean_dec(v___y_172_);
lean_dec(v___y_171_);
return v_res_183_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2_spec__5_spec__9___redArg(lean_object* v_x_184_, lean_object* v_x_185_, lean_object* v_x_186_, lean_object* v_x_187_){
_start:
{
lean_object* v_ks_188_; lean_object* v_vs_189_; lean_object* v___x_191_; uint8_t v_isShared_192_; uint8_t v_isSharedCheck_213_; 
v_ks_188_ = lean_ctor_get(v_x_184_, 0);
v_vs_189_ = lean_ctor_get(v_x_184_, 1);
v_isSharedCheck_213_ = !lean_is_exclusive(v_x_184_);
if (v_isSharedCheck_213_ == 0)
{
v___x_191_ = v_x_184_;
v_isShared_192_ = v_isSharedCheck_213_;
goto v_resetjp_190_;
}
else
{
lean_inc(v_vs_189_);
lean_inc(v_ks_188_);
lean_dec(v_x_184_);
v___x_191_ = lean_box(0);
v_isShared_192_ = v_isSharedCheck_213_;
goto v_resetjp_190_;
}
v_resetjp_190_:
{
lean_object* v___x_193_; uint8_t v___x_194_; 
v___x_193_ = lean_array_get_size(v_ks_188_);
v___x_194_ = lean_nat_dec_lt(v_x_185_, v___x_193_);
if (v___x_194_ == 0)
{
lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_198_; 
lean_dec(v_x_185_);
v___x_195_ = lean_array_push(v_ks_188_, v_x_186_);
v___x_196_ = lean_array_push(v_vs_189_, v_x_187_);
if (v_isShared_192_ == 0)
{
lean_ctor_set(v___x_191_, 1, v___x_196_);
lean_ctor_set(v___x_191_, 0, v___x_195_);
v___x_198_ = v___x_191_;
goto v_reusejp_197_;
}
else
{
lean_object* v_reuseFailAlloc_199_; 
v_reuseFailAlloc_199_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_199_, 0, v___x_195_);
lean_ctor_set(v_reuseFailAlloc_199_, 1, v___x_196_);
v___x_198_ = v_reuseFailAlloc_199_;
goto v_reusejp_197_;
}
v_reusejp_197_:
{
return v___x_198_;
}
}
else
{
lean_object* v_k_x27_200_; uint8_t v___x_201_; 
v_k_x27_200_ = lean_array_fget_borrowed(v_ks_188_, v_x_185_);
v___x_201_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_186_, v_k_x27_200_);
if (v___x_201_ == 0)
{
lean_object* v___x_203_; 
if (v_isShared_192_ == 0)
{
v___x_203_ = v___x_191_;
goto v_reusejp_202_;
}
else
{
lean_object* v_reuseFailAlloc_207_; 
v_reuseFailAlloc_207_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_207_, 0, v_ks_188_);
lean_ctor_set(v_reuseFailAlloc_207_, 1, v_vs_189_);
v___x_203_ = v_reuseFailAlloc_207_;
goto v_reusejp_202_;
}
v_reusejp_202_:
{
lean_object* v___x_204_; lean_object* v___x_205_; 
v___x_204_ = lean_unsigned_to_nat(1u);
v___x_205_ = lean_nat_add(v_x_185_, v___x_204_);
lean_dec(v_x_185_);
v_x_184_ = v___x_203_;
v_x_185_ = v___x_205_;
goto _start;
}
}
else
{
lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_211_; 
v___x_208_ = lean_array_fset(v_ks_188_, v_x_185_, v_x_186_);
v___x_209_ = lean_array_fset(v_vs_189_, v_x_185_, v_x_187_);
lean_dec(v_x_185_);
if (v_isShared_192_ == 0)
{
lean_ctor_set(v___x_191_, 1, v___x_209_);
lean_ctor_set(v___x_191_, 0, v___x_208_);
v___x_211_ = v___x_191_;
goto v_reusejp_210_;
}
else
{
lean_object* v_reuseFailAlloc_212_; 
v_reuseFailAlloc_212_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_212_, 0, v___x_208_);
lean_ctor_set(v_reuseFailAlloc_212_, 1, v___x_209_);
v___x_211_ = v_reuseFailAlloc_212_;
goto v_reusejp_210_;
}
v_reusejp_210_:
{
return v___x_211_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2_spec__5___redArg(lean_object* v_n_214_, lean_object* v_k_215_, lean_object* v_v_216_){
_start:
{
lean_object* v___x_217_; lean_object* v___x_218_; 
v___x_217_ = lean_unsigned_to_nat(0u);
v___x_218_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2_spec__5_spec__9___redArg(v_n_214_, v___x_217_, v_k_215_, v_v_216_);
return v___x_218_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___redArg___closed__0(void){
_start:
{
size_t v___x_219_; size_t v___x_220_; size_t v___x_221_; 
v___x_219_ = ((size_t)5ULL);
v___x_220_ = ((size_t)1ULL);
v___x_221_ = lean_usize_shift_left(v___x_220_, v___x_219_);
return v___x_221_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___redArg___closed__1(void){
_start:
{
size_t v___x_222_; size_t v___x_223_; size_t v___x_224_; 
v___x_222_ = ((size_t)1ULL);
v___x_223_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___redArg___closed__0);
v___x_224_ = lean_usize_sub(v___x_223_, v___x_222_);
return v___x_224_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_225_; 
v___x_225_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_225_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___redArg(lean_object* v_x_226_, size_t v_x_227_, size_t v_x_228_, lean_object* v_x_229_, lean_object* v_x_230_){
_start:
{
if (lean_obj_tag(v_x_226_) == 0)
{
lean_object* v_es_231_; size_t v___x_232_; size_t v___x_233_; size_t v___x_234_; size_t v___x_235_; lean_object* v_j_236_; lean_object* v___x_237_; uint8_t v___x_238_; 
v_es_231_ = lean_ctor_get(v_x_226_, 0);
v___x_232_ = ((size_t)5ULL);
v___x_233_ = ((size_t)1ULL);
v___x_234_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___redArg___closed__1);
v___x_235_ = lean_usize_land(v_x_227_, v___x_234_);
v_j_236_ = lean_usize_to_nat(v___x_235_);
v___x_237_ = lean_array_get_size(v_es_231_);
v___x_238_ = lean_nat_dec_lt(v_j_236_, v___x_237_);
if (v___x_238_ == 0)
{
lean_dec(v_j_236_);
lean_dec(v_x_230_);
lean_dec_ref(v_x_229_);
return v_x_226_;
}
else
{
lean_object* v___x_240_; uint8_t v_isShared_241_; uint8_t v_isSharedCheck_275_; 
lean_inc_ref(v_es_231_);
v_isSharedCheck_275_ = !lean_is_exclusive(v_x_226_);
if (v_isSharedCheck_275_ == 0)
{
lean_object* v_unused_276_; 
v_unused_276_ = lean_ctor_get(v_x_226_, 0);
lean_dec(v_unused_276_);
v___x_240_ = v_x_226_;
v_isShared_241_ = v_isSharedCheck_275_;
goto v_resetjp_239_;
}
else
{
lean_dec(v_x_226_);
v___x_240_ = lean_box(0);
v_isShared_241_ = v_isSharedCheck_275_;
goto v_resetjp_239_;
}
v_resetjp_239_:
{
lean_object* v_v_242_; lean_object* v___x_243_; lean_object* v_xs_x27_244_; lean_object* v___y_246_; 
v_v_242_ = lean_array_fget(v_es_231_, v_j_236_);
v___x_243_ = lean_box(0);
v_xs_x27_244_ = lean_array_fset(v_es_231_, v_j_236_, v___x_243_);
switch(lean_obj_tag(v_v_242_))
{
case 0:
{
lean_object* v_key_251_; lean_object* v_val_252_; lean_object* v___x_254_; uint8_t v_isShared_255_; uint8_t v_isSharedCheck_262_; 
v_key_251_ = lean_ctor_get(v_v_242_, 0);
v_val_252_ = lean_ctor_get(v_v_242_, 1);
v_isSharedCheck_262_ = !lean_is_exclusive(v_v_242_);
if (v_isSharedCheck_262_ == 0)
{
v___x_254_ = v_v_242_;
v_isShared_255_ = v_isSharedCheck_262_;
goto v_resetjp_253_;
}
else
{
lean_inc(v_val_252_);
lean_inc(v_key_251_);
lean_dec(v_v_242_);
v___x_254_ = lean_box(0);
v_isShared_255_ = v_isSharedCheck_262_;
goto v_resetjp_253_;
}
v_resetjp_253_:
{
uint8_t v___x_256_; 
v___x_256_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_229_, v_key_251_);
if (v___x_256_ == 0)
{
lean_object* v___x_257_; lean_object* v___x_258_; 
lean_del_object(v___x_254_);
v___x_257_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_251_, v_val_252_, v_x_229_, v_x_230_);
v___x_258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_258_, 0, v___x_257_);
v___y_246_ = v___x_258_;
goto v___jp_245_;
}
else
{
lean_object* v___x_260_; 
lean_dec(v_val_252_);
lean_dec(v_key_251_);
if (v_isShared_255_ == 0)
{
lean_ctor_set(v___x_254_, 1, v_x_230_);
lean_ctor_set(v___x_254_, 0, v_x_229_);
v___x_260_ = v___x_254_;
goto v_reusejp_259_;
}
else
{
lean_object* v_reuseFailAlloc_261_; 
v_reuseFailAlloc_261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_261_, 0, v_x_229_);
lean_ctor_set(v_reuseFailAlloc_261_, 1, v_x_230_);
v___x_260_ = v_reuseFailAlloc_261_;
goto v_reusejp_259_;
}
v_reusejp_259_:
{
v___y_246_ = v___x_260_;
goto v___jp_245_;
}
}
}
}
case 1:
{
lean_object* v_node_263_; lean_object* v___x_265_; uint8_t v_isShared_266_; uint8_t v_isSharedCheck_273_; 
v_node_263_ = lean_ctor_get(v_v_242_, 0);
v_isSharedCheck_273_ = !lean_is_exclusive(v_v_242_);
if (v_isSharedCheck_273_ == 0)
{
v___x_265_ = v_v_242_;
v_isShared_266_ = v_isSharedCheck_273_;
goto v_resetjp_264_;
}
else
{
lean_inc(v_node_263_);
lean_dec(v_v_242_);
v___x_265_ = lean_box(0);
v_isShared_266_ = v_isSharedCheck_273_;
goto v_resetjp_264_;
}
v_resetjp_264_:
{
size_t v___x_267_; size_t v___x_268_; lean_object* v___x_269_; lean_object* v___x_271_; 
v___x_267_ = lean_usize_shift_right(v_x_227_, v___x_232_);
v___x_268_ = lean_usize_add(v_x_228_, v___x_233_);
v___x_269_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___redArg(v_node_263_, v___x_267_, v___x_268_, v_x_229_, v_x_230_);
if (v_isShared_266_ == 0)
{
lean_ctor_set(v___x_265_, 0, v___x_269_);
v___x_271_ = v___x_265_;
goto v_reusejp_270_;
}
else
{
lean_object* v_reuseFailAlloc_272_; 
v_reuseFailAlloc_272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_272_, 0, v___x_269_);
v___x_271_ = v_reuseFailAlloc_272_;
goto v_reusejp_270_;
}
v_reusejp_270_:
{
v___y_246_ = v___x_271_;
goto v___jp_245_;
}
}
}
default: 
{
lean_object* v___x_274_; 
v___x_274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_274_, 0, v_x_229_);
lean_ctor_set(v___x_274_, 1, v_x_230_);
v___y_246_ = v___x_274_;
goto v___jp_245_;
}
}
v___jp_245_:
{
lean_object* v___x_247_; lean_object* v___x_249_; 
v___x_247_ = lean_array_fset(v_xs_x27_244_, v_j_236_, v___y_246_);
lean_dec(v_j_236_);
if (v_isShared_241_ == 0)
{
lean_ctor_set(v___x_240_, 0, v___x_247_);
v___x_249_ = v___x_240_;
goto v_reusejp_248_;
}
else
{
lean_object* v_reuseFailAlloc_250_; 
v_reuseFailAlloc_250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_250_, 0, v___x_247_);
v___x_249_ = v_reuseFailAlloc_250_;
goto v_reusejp_248_;
}
v_reusejp_248_:
{
return v___x_249_;
}
}
}
}
}
else
{
lean_object* v_ks_277_; lean_object* v_vs_278_; lean_object* v___x_280_; uint8_t v_isShared_281_; uint8_t v_isSharedCheck_298_; 
v_ks_277_ = lean_ctor_get(v_x_226_, 0);
v_vs_278_ = lean_ctor_get(v_x_226_, 1);
v_isSharedCheck_298_ = !lean_is_exclusive(v_x_226_);
if (v_isSharedCheck_298_ == 0)
{
v___x_280_ = v_x_226_;
v_isShared_281_ = v_isSharedCheck_298_;
goto v_resetjp_279_;
}
else
{
lean_inc(v_vs_278_);
lean_inc(v_ks_277_);
lean_dec(v_x_226_);
v___x_280_ = lean_box(0);
v_isShared_281_ = v_isSharedCheck_298_;
goto v_resetjp_279_;
}
v_resetjp_279_:
{
lean_object* v___x_283_; 
if (v_isShared_281_ == 0)
{
v___x_283_ = v___x_280_;
goto v_reusejp_282_;
}
else
{
lean_object* v_reuseFailAlloc_297_; 
v_reuseFailAlloc_297_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_297_, 0, v_ks_277_);
lean_ctor_set(v_reuseFailAlloc_297_, 1, v_vs_278_);
v___x_283_ = v_reuseFailAlloc_297_;
goto v_reusejp_282_;
}
v_reusejp_282_:
{
lean_object* v_newNode_284_; uint8_t v___y_286_; size_t v___x_292_; uint8_t v___x_293_; 
v_newNode_284_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2_spec__5___redArg(v___x_283_, v_x_229_, v_x_230_);
v___x_292_ = ((size_t)7ULL);
v___x_293_ = lean_usize_dec_le(v___x_292_, v_x_228_);
if (v___x_293_ == 0)
{
lean_object* v___x_294_; lean_object* v___x_295_; uint8_t v___x_296_; 
v___x_294_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_284_);
v___x_295_ = lean_unsigned_to_nat(4u);
v___x_296_ = lean_nat_dec_lt(v___x_294_, v___x_295_);
lean_dec(v___x_294_);
v___y_286_ = v___x_296_;
goto v___jp_285_;
}
else
{
v___y_286_ = v___x_293_;
goto v___jp_285_;
}
v___jp_285_:
{
if (v___y_286_ == 0)
{
lean_object* v_ks_287_; lean_object* v_vs_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; 
v_ks_287_ = lean_ctor_get(v_newNode_284_, 0);
lean_inc_ref(v_ks_287_);
v_vs_288_ = lean_ctor_get(v_newNode_284_, 1);
lean_inc_ref(v_vs_288_);
lean_dec_ref(v_newNode_284_);
v___x_289_ = lean_unsigned_to_nat(0u);
v___x_290_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___redArg___closed__2);
v___x_291_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2_spec__6___redArg(v_x_228_, v_ks_287_, v_vs_288_, v___x_289_, v___x_290_);
lean_dec_ref(v_vs_288_);
lean_dec_ref(v_ks_287_);
return v___x_291_;
}
else
{
return v_newNode_284_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2_spec__6___redArg(size_t v_depth_299_, lean_object* v_keys_300_, lean_object* v_vals_301_, lean_object* v_i_302_, lean_object* v_entries_303_){
_start:
{
lean_object* v___x_304_; uint8_t v___x_305_; 
v___x_304_ = lean_array_get_size(v_keys_300_);
v___x_305_ = lean_nat_dec_lt(v_i_302_, v___x_304_);
if (v___x_305_ == 0)
{
lean_dec(v_i_302_);
return v_entries_303_;
}
else
{
lean_object* v_k_306_; lean_object* v_v_307_; uint64_t v___x_308_; size_t v_h_309_; size_t v___x_310_; lean_object* v___x_311_; size_t v___x_312_; size_t v___x_313_; size_t v___x_314_; size_t v_h_315_; lean_object* v___x_316_; lean_object* v___x_317_; 
v_k_306_ = lean_array_fget_borrowed(v_keys_300_, v_i_302_);
v_v_307_ = lean_array_fget_borrowed(v_vals_301_, v_i_302_);
v___x_308_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_k_306_);
v_h_309_ = lean_uint64_to_usize(v___x_308_);
v___x_310_ = ((size_t)5ULL);
v___x_311_ = lean_unsigned_to_nat(1u);
v___x_312_ = ((size_t)1ULL);
v___x_313_ = lean_usize_sub(v_depth_299_, v___x_312_);
v___x_314_ = lean_usize_mul(v___x_310_, v___x_313_);
v_h_315_ = lean_usize_shift_right(v_h_309_, v___x_314_);
v___x_316_ = lean_nat_add(v_i_302_, v___x_311_);
lean_dec(v_i_302_);
lean_inc(v_v_307_);
lean_inc(v_k_306_);
v___x_317_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___redArg(v_entries_303_, v_h_315_, v_depth_299_, v_k_306_, v_v_307_);
v_i_302_ = v___x_316_;
v_entries_303_ = v___x_317_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2_spec__6___redArg___boxed(lean_object* v_depth_319_, lean_object* v_keys_320_, lean_object* v_vals_321_, lean_object* v_i_322_, lean_object* v_entries_323_){
_start:
{
size_t v_depth_boxed_324_; lean_object* v_res_325_; 
v_depth_boxed_324_ = lean_unbox_usize(v_depth_319_);
lean_dec(v_depth_319_);
v_res_325_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2_spec__6___redArg(v_depth_boxed_324_, v_keys_320_, v_vals_321_, v_i_322_, v_entries_323_);
lean_dec_ref(v_vals_321_);
lean_dec_ref(v_keys_320_);
return v_res_325_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___redArg___boxed(lean_object* v_x_326_, lean_object* v_x_327_, lean_object* v_x_328_, lean_object* v_x_329_, lean_object* v_x_330_){
_start:
{
size_t v_x_54642__boxed_331_; size_t v_x_54643__boxed_332_; lean_object* v_res_333_; 
v_x_54642__boxed_331_ = lean_unbox_usize(v_x_327_);
lean_dec(v_x_327_);
v_x_54643__boxed_332_ = lean_unbox_usize(v_x_328_);
lean_dec(v_x_328_);
v_res_333_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___redArg(v_x_326_, v_x_54642__boxed_331_, v_x_54643__boxed_332_, v_x_329_, v_x_330_);
return v_res_333_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1___redArg(lean_object* v_x_334_, lean_object* v_x_335_, lean_object* v_x_336_){
_start:
{
uint64_t v___x_337_; size_t v___x_338_; size_t v___x_339_; lean_object* v___x_340_; 
v___x_337_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_335_);
v___x_338_ = lean_uint64_to_usize(v___x_337_);
v___x_339_ = ((size_t)1ULL);
v___x_340_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___redArg(v_x_334_, v___x_338_, v___x_339_, v_x_335_, v_x_336_);
return v___x_340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_internalize___lam__0(lean_object* v_e_341_, lean_object* v_a_342_, uint8_t v_ac_343_, lean_object* v_s_344_){
_start:
{
lean_object* v_id_345_; lean_object* v_type_346_; lean_object* v_u_347_; lean_object* v_op_348_; lean_object* v_neutral_x3f_349_; lean_object* v_assocInst_350_; lean_object* v_idempotentInst_x3f_351_; lean_object* v_commInst_x3f_352_; lean_object* v_neutralInst_x3f_353_; lean_object* v_nextId_354_; lean_object* v_vars_355_; lean_object* v_varMap_356_; lean_object* v_denote_357_; lean_object* v_denoteEntries_358_; lean_object* v_queue_359_; lean_object* v_basis_360_; lean_object* v_diseqs_361_; lean_object* v___x_363_; uint8_t v_isShared_364_; uint8_t v_isSharedCheck_371_; 
v_id_345_ = lean_ctor_get(v_s_344_, 0);
v_type_346_ = lean_ctor_get(v_s_344_, 1);
v_u_347_ = lean_ctor_get(v_s_344_, 2);
v_op_348_ = lean_ctor_get(v_s_344_, 3);
v_neutral_x3f_349_ = lean_ctor_get(v_s_344_, 4);
v_assocInst_350_ = lean_ctor_get(v_s_344_, 5);
v_idempotentInst_x3f_351_ = lean_ctor_get(v_s_344_, 6);
v_commInst_x3f_352_ = lean_ctor_get(v_s_344_, 7);
v_neutralInst_x3f_353_ = lean_ctor_get(v_s_344_, 8);
v_nextId_354_ = lean_ctor_get(v_s_344_, 9);
v_vars_355_ = lean_ctor_get(v_s_344_, 10);
v_varMap_356_ = lean_ctor_get(v_s_344_, 11);
v_denote_357_ = lean_ctor_get(v_s_344_, 12);
v_denoteEntries_358_ = lean_ctor_get(v_s_344_, 13);
v_queue_359_ = lean_ctor_get(v_s_344_, 14);
v_basis_360_ = lean_ctor_get(v_s_344_, 15);
v_diseqs_361_ = lean_ctor_get(v_s_344_, 16);
v_isSharedCheck_371_ = !lean_is_exclusive(v_s_344_);
if (v_isSharedCheck_371_ == 0)
{
v___x_363_ = v_s_344_;
v_isShared_364_ = v_isSharedCheck_371_;
goto v_resetjp_362_;
}
else
{
lean_inc(v_diseqs_361_);
lean_inc(v_basis_360_);
lean_inc(v_queue_359_);
lean_inc(v_denoteEntries_358_);
lean_inc(v_denote_357_);
lean_inc(v_varMap_356_);
lean_inc(v_vars_355_);
lean_inc(v_nextId_354_);
lean_inc(v_neutralInst_x3f_353_);
lean_inc(v_commInst_x3f_352_);
lean_inc(v_idempotentInst_x3f_351_);
lean_inc(v_assocInst_350_);
lean_inc(v_neutral_x3f_349_);
lean_inc(v_op_348_);
lean_inc(v_u_347_);
lean_inc(v_type_346_);
lean_inc(v_id_345_);
lean_dec(v_s_344_);
v___x_363_ = lean_box(0);
v_isShared_364_ = v_isSharedCheck_371_;
goto v_resetjp_362_;
}
v_resetjp_362_:
{
lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_369_; 
lean_inc_ref(v_a_342_);
lean_inc_ref(v_e_341_);
v___x_365_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1___redArg(v_denote_357_, v_e_341_, v_a_342_);
v___x_366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_366_, 0, v_e_341_);
lean_ctor_set(v___x_366_, 1, v_a_342_);
v___x_367_ = l_Lean_PersistentArray_push___redArg(v_denoteEntries_358_, v___x_366_);
if (v_isShared_364_ == 0)
{
lean_ctor_set(v___x_363_, 13, v___x_367_);
lean_ctor_set(v___x_363_, 12, v___x_365_);
v___x_369_ = v___x_363_;
goto v_reusejp_368_;
}
else
{
lean_object* v_reuseFailAlloc_370_; 
v_reuseFailAlloc_370_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_370_, 0, v_id_345_);
lean_ctor_set(v_reuseFailAlloc_370_, 1, v_type_346_);
lean_ctor_set(v_reuseFailAlloc_370_, 2, v_u_347_);
lean_ctor_set(v_reuseFailAlloc_370_, 3, v_op_348_);
lean_ctor_set(v_reuseFailAlloc_370_, 4, v_neutral_x3f_349_);
lean_ctor_set(v_reuseFailAlloc_370_, 5, v_assocInst_350_);
lean_ctor_set(v_reuseFailAlloc_370_, 6, v_idempotentInst_x3f_351_);
lean_ctor_set(v_reuseFailAlloc_370_, 7, v_commInst_x3f_352_);
lean_ctor_set(v_reuseFailAlloc_370_, 8, v_neutralInst_x3f_353_);
lean_ctor_set(v_reuseFailAlloc_370_, 9, v_nextId_354_);
lean_ctor_set(v_reuseFailAlloc_370_, 10, v_vars_355_);
lean_ctor_set(v_reuseFailAlloc_370_, 11, v_varMap_356_);
lean_ctor_set(v_reuseFailAlloc_370_, 12, v___x_365_);
lean_ctor_set(v_reuseFailAlloc_370_, 13, v___x_367_);
lean_ctor_set(v_reuseFailAlloc_370_, 14, v_queue_359_);
lean_ctor_set(v_reuseFailAlloc_370_, 15, v_basis_360_);
lean_ctor_set(v_reuseFailAlloc_370_, 16, v_diseqs_361_);
v___x_369_ = v_reuseFailAlloc_370_;
goto v_reusejp_368_;
}
v_reusejp_368_:
{
lean_ctor_set_uint8(v___x_369_, sizeof(void*)*17, v_ac_343_);
return v___x_369_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_internalize___lam__0___boxed(lean_object* v_e_372_, lean_object* v_a_373_, lean_object* v_ac_374_, lean_object* v_s_375_){
_start:
{
uint8_t v_ac_boxed_376_; lean_object* v_res_377_; 
v_ac_boxed_376_ = lean_unbox(v_ac_374_);
v_res_377_ = l_Lean_Meta_Grind_AC_internalize___lam__0(v_e_372_, v_a_373_, v_ac_boxed_376_, v_s_375_);
return v_res_377_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0_spec__2___redArg(lean_object* v_keys_378_, lean_object* v_i_379_, lean_object* v_k_380_){
_start:
{
lean_object* v___x_381_; uint8_t v___x_382_; 
v___x_381_ = lean_array_get_size(v_keys_378_);
v___x_382_ = lean_nat_dec_lt(v_i_379_, v___x_381_);
if (v___x_382_ == 0)
{
lean_dec(v_i_379_);
return v___x_382_;
}
else
{
lean_object* v_k_x27_383_; uint8_t v___x_384_; 
v_k_x27_383_ = lean_array_fget_borrowed(v_keys_378_, v_i_379_);
v___x_384_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_k_380_, v_k_x27_383_);
if (v___x_384_ == 0)
{
lean_object* v___x_385_; lean_object* v___x_386_; 
v___x_385_ = lean_unsigned_to_nat(1u);
v___x_386_ = lean_nat_add(v_i_379_, v___x_385_);
lean_dec(v_i_379_);
v_i_379_ = v___x_386_;
goto _start;
}
else
{
lean_dec(v_i_379_);
return v___x_384_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_keys_388_, lean_object* v_i_389_, lean_object* v_k_390_){
_start:
{
uint8_t v_res_391_; lean_object* v_r_392_; 
v_res_391_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0_spec__2___redArg(v_keys_388_, v_i_389_, v_k_390_);
lean_dec_ref(v_k_390_);
lean_dec_ref(v_keys_388_);
v_r_392_ = lean_box(v_res_391_);
return v_r_392_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0___redArg(lean_object* v_x_393_, size_t v_x_394_, lean_object* v_x_395_){
_start:
{
if (lean_obj_tag(v_x_393_) == 0)
{
lean_object* v_es_396_; lean_object* v___x_397_; size_t v___x_398_; size_t v___x_399_; size_t v___x_400_; lean_object* v_j_401_; lean_object* v___x_402_; 
v_es_396_ = lean_ctor_get(v_x_393_, 0);
lean_inc_ref(v_es_396_);
lean_dec_ref(v_x_393_);
v___x_397_ = lean_box(2);
v___x_398_ = ((size_t)5ULL);
v___x_399_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___redArg___closed__1);
v___x_400_ = lean_usize_land(v_x_394_, v___x_399_);
v_j_401_ = lean_usize_to_nat(v___x_400_);
v___x_402_ = lean_array_get(v___x_397_, v_es_396_, v_j_401_);
lean_dec(v_j_401_);
lean_dec_ref(v_es_396_);
switch(lean_obj_tag(v___x_402_))
{
case 0:
{
lean_object* v_key_403_; uint8_t v___x_404_; 
v_key_403_ = lean_ctor_get(v___x_402_, 0);
lean_inc(v_key_403_);
lean_dec_ref(v___x_402_);
v___x_404_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_395_, v_key_403_);
lean_dec(v_key_403_);
return v___x_404_;
}
case 1:
{
lean_object* v_node_405_; size_t v___x_406_; 
v_node_405_ = lean_ctor_get(v___x_402_, 0);
lean_inc(v_node_405_);
lean_dec_ref(v___x_402_);
v___x_406_ = lean_usize_shift_right(v_x_394_, v___x_398_);
v_x_393_ = v_node_405_;
v_x_394_ = v___x_406_;
goto _start;
}
default: 
{
uint8_t v___x_408_; 
v___x_408_ = 0;
return v___x_408_;
}
}
}
else
{
lean_object* v_ks_409_; lean_object* v___x_410_; uint8_t v___x_411_; 
v_ks_409_ = lean_ctor_get(v_x_393_, 0);
lean_inc_ref(v_ks_409_);
lean_dec_ref(v_x_393_);
v___x_410_ = lean_unsigned_to_nat(0u);
v___x_411_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0_spec__2___redArg(v_ks_409_, v___x_410_, v_x_395_);
lean_dec_ref(v_ks_409_);
return v___x_411_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0___redArg___boxed(lean_object* v_x_412_, lean_object* v_x_413_, lean_object* v_x_414_){
_start:
{
size_t v_x_54859__boxed_415_; uint8_t v_res_416_; lean_object* v_r_417_; 
v_x_54859__boxed_415_ = lean_unbox_usize(v_x_413_);
lean_dec(v_x_413_);
v_res_416_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0___redArg(v_x_412_, v_x_54859__boxed_415_, v_x_414_);
lean_dec_ref(v_x_414_);
v_r_417_ = lean_box(v_res_416_);
return v_r_417_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0___redArg(lean_object* v_x_418_, lean_object* v_x_419_){
_start:
{
uint64_t v___x_420_; size_t v___x_421_; uint8_t v___x_422_; 
v___x_420_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_419_);
v___x_421_ = lean_uint64_to_usize(v___x_420_);
v___x_422_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0___redArg(v_x_418_, v___x_421_, v_x_419_);
return v___x_422_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0___redArg___boxed(lean_object* v_x_423_, lean_object* v_x_424_){
_start:
{
uint8_t v_res_425_; lean_object* v_r_426_; 
v_res_425_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0___redArg(v_x_423_, v_x_424_);
lean_dec_ref(v_x_424_);
v_r_426_ = lean_box(v_res_425_);
return v_r_426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Expr_denoteExpr___at___00Lean_Meta_Grind_AC_internalize_spec__3(lean_object* v_e_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_){
_start:
{
if (lean_obj_tag(v_e_427_) == 0)
{
lean_object* v_x_440_; lean_object* v___x_441_; 
v_x_440_ = lean_ctor_get(v_e_427_, 0);
v___x_441_ = l_Lean_Meta_Grind_AC_ACM_getStruct(v___y_428_, v___y_429_, v___y_430_, v___y_431_, v___y_432_, v___y_433_, v___y_434_, v___y_435_, v___y_436_, v___y_437_, v___y_438_);
if (lean_obj_tag(v___x_441_) == 0)
{
lean_object* v_a_442_; lean_object* v___x_444_; uint8_t v_isShared_445_; uint8_t v_isSharedCheck_458_; 
v_a_442_ = lean_ctor_get(v___x_441_, 0);
v_isSharedCheck_458_ = !lean_is_exclusive(v___x_441_);
if (v_isSharedCheck_458_ == 0)
{
v___x_444_ = v___x_441_;
v_isShared_445_ = v_isSharedCheck_458_;
goto v_resetjp_443_;
}
else
{
lean_inc(v_a_442_);
lean_dec(v___x_441_);
v___x_444_ = lean_box(0);
v_isShared_445_ = v_isSharedCheck_458_;
goto v_resetjp_443_;
}
v_resetjp_443_:
{
lean_object* v_vars_446_; lean_object* v_size_447_; lean_object* v___x_448_; uint8_t v___x_449_; 
v_vars_446_ = lean_ctor_get(v_a_442_, 10);
lean_inc_ref(v_vars_446_);
lean_dec(v_a_442_);
v_size_447_ = lean_ctor_get(v_vars_446_, 2);
v___x_448_ = l_Lean_instInhabitedExpr;
v___x_449_ = lean_nat_dec_lt(v_x_440_, v_size_447_);
if (v___x_449_ == 0)
{
lean_object* v___x_450_; lean_object* v___x_452_; 
lean_dec_ref(v_vars_446_);
v___x_450_ = l_outOfBounds___redArg(v___x_448_);
if (v_isShared_445_ == 0)
{
lean_ctor_set(v___x_444_, 0, v___x_450_);
v___x_452_ = v___x_444_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v___x_450_);
v___x_452_ = v_reuseFailAlloc_453_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
return v___x_452_;
}
}
else
{
lean_object* v___x_454_; lean_object* v___x_456_; 
v___x_454_ = l_Lean_PersistentArray_get_x21___redArg(v___x_448_, v_vars_446_, v_x_440_);
if (v_isShared_445_ == 0)
{
lean_ctor_set(v___x_444_, 0, v___x_454_);
v___x_456_ = v___x_444_;
goto v_reusejp_455_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v___x_454_);
v___x_456_ = v_reuseFailAlloc_457_;
goto v_reusejp_455_;
}
v_reusejp_455_:
{
return v___x_456_;
}
}
}
}
else
{
lean_object* v_a_459_; lean_object* v___x_461_; uint8_t v_isShared_462_; uint8_t v_isSharedCheck_466_; 
v_a_459_ = lean_ctor_get(v___x_441_, 0);
v_isSharedCheck_466_ = !lean_is_exclusive(v___x_441_);
if (v_isSharedCheck_466_ == 0)
{
v___x_461_ = v___x_441_;
v_isShared_462_ = v_isSharedCheck_466_;
goto v_resetjp_460_;
}
else
{
lean_inc(v_a_459_);
lean_dec(v___x_441_);
v___x_461_ = lean_box(0);
v_isShared_462_ = v_isSharedCheck_466_;
goto v_resetjp_460_;
}
v_resetjp_460_:
{
lean_object* v___x_464_; 
if (v_isShared_462_ == 0)
{
v___x_464_ = v___x_461_;
goto v_reusejp_463_;
}
else
{
lean_object* v_reuseFailAlloc_465_; 
v_reuseFailAlloc_465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_465_, 0, v_a_459_);
v___x_464_ = v_reuseFailAlloc_465_;
goto v_reusejp_463_;
}
v_reusejp_463_:
{
return v___x_464_;
}
}
}
}
else
{
lean_object* v_lhs_467_; lean_object* v_rhs_468_; lean_object* v___x_469_; 
v_lhs_467_ = lean_ctor_get(v_e_427_, 0);
v_rhs_468_ = lean_ctor_get(v_e_427_, 1);
v___x_469_ = l_Lean_Meta_Grind_AC_ACM_getStruct(v___y_428_, v___y_429_, v___y_430_, v___y_431_, v___y_432_, v___y_433_, v___y_434_, v___y_435_, v___y_436_, v___y_437_, v___y_438_);
if (lean_obj_tag(v___x_469_) == 0)
{
lean_object* v_a_470_; lean_object* v___x_471_; 
v_a_470_ = lean_ctor_get(v___x_469_, 0);
lean_inc(v_a_470_);
lean_dec_ref(v___x_469_);
v___x_471_ = l_Lean_Grind_AC_Expr_denoteExpr___at___00Lean_Meta_Grind_AC_internalize_spec__3(v_lhs_467_, v___y_428_, v___y_429_, v___y_430_, v___y_431_, v___y_432_, v___y_433_, v___y_434_, v___y_435_, v___y_436_, v___y_437_, v___y_438_);
if (lean_obj_tag(v___x_471_) == 0)
{
lean_object* v_a_472_; lean_object* v___x_473_; 
v_a_472_ = lean_ctor_get(v___x_471_, 0);
lean_inc(v_a_472_);
lean_dec_ref(v___x_471_);
v___x_473_ = l_Lean_Grind_AC_Expr_denoteExpr___at___00Lean_Meta_Grind_AC_internalize_spec__3(v_rhs_468_, v___y_428_, v___y_429_, v___y_430_, v___y_431_, v___y_432_, v___y_433_, v___y_434_, v___y_435_, v___y_436_, v___y_437_, v___y_438_);
if (lean_obj_tag(v___x_473_) == 0)
{
lean_object* v_a_474_; lean_object* v___x_476_; uint8_t v_isShared_477_; uint8_t v_isSharedCheck_483_; 
v_a_474_ = lean_ctor_get(v___x_473_, 0);
v_isSharedCheck_483_ = !lean_is_exclusive(v___x_473_);
if (v_isSharedCheck_483_ == 0)
{
v___x_476_ = v___x_473_;
v_isShared_477_ = v_isSharedCheck_483_;
goto v_resetjp_475_;
}
else
{
lean_inc(v_a_474_);
lean_dec(v___x_473_);
v___x_476_ = lean_box(0);
v_isShared_477_ = v_isSharedCheck_483_;
goto v_resetjp_475_;
}
v_resetjp_475_:
{
lean_object* v_op_478_; lean_object* v___x_479_; lean_object* v___x_481_; 
v_op_478_ = lean_ctor_get(v_a_470_, 3);
lean_inc_ref(v_op_478_);
lean_dec(v_a_470_);
v___x_479_ = l_Lean_mkAppB(v_op_478_, v_a_472_, v_a_474_);
if (v_isShared_477_ == 0)
{
lean_ctor_set(v___x_476_, 0, v___x_479_);
v___x_481_ = v___x_476_;
goto v_reusejp_480_;
}
else
{
lean_object* v_reuseFailAlloc_482_; 
v_reuseFailAlloc_482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_482_, 0, v___x_479_);
v___x_481_ = v_reuseFailAlloc_482_;
goto v_reusejp_480_;
}
v_reusejp_480_:
{
return v___x_481_;
}
}
}
else
{
lean_dec(v_a_472_);
lean_dec(v_a_470_);
return v___x_473_;
}
}
else
{
lean_dec(v_a_470_);
return v___x_471_;
}
}
else
{
lean_object* v_a_484_; lean_object* v___x_486_; uint8_t v_isShared_487_; uint8_t v_isSharedCheck_491_; 
v_a_484_ = lean_ctor_get(v___x_469_, 0);
v_isSharedCheck_491_ = !lean_is_exclusive(v___x_469_);
if (v_isSharedCheck_491_ == 0)
{
v___x_486_ = v___x_469_;
v_isShared_487_ = v_isSharedCheck_491_;
goto v_resetjp_485_;
}
else
{
lean_inc(v_a_484_);
lean_dec(v___x_469_);
v___x_486_ = lean_box(0);
v_isShared_487_ = v_isSharedCheck_491_;
goto v_resetjp_485_;
}
v_resetjp_485_:
{
lean_object* v___x_489_; 
if (v_isShared_487_ == 0)
{
v___x_489_ = v___x_486_;
goto v_reusejp_488_;
}
else
{
lean_object* v_reuseFailAlloc_490_; 
v_reuseFailAlloc_490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_490_, 0, v_a_484_);
v___x_489_ = v_reuseFailAlloc_490_;
goto v_reusejp_488_;
}
v_reusejp_488_:
{
return v___x_489_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Expr_denoteExpr___at___00Lean_Meta_Grind_AC_internalize_spec__3___boxed(lean_object* v_e_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_){
_start:
{
lean_object* v_res_505_; 
v_res_505_ = l_Lean_Grind_AC_Expr_denoteExpr___at___00Lean_Meta_Grind_AC_internalize_spec__3(v_e_492_, v___y_493_, v___y_494_, v___y_495_, v___y_496_, v___y_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_);
lean_dec(v___y_503_);
lean_dec_ref(v___y_502_);
lean_dec(v___y_501_);
lean_dec_ref(v___y_500_);
lean_dec(v___y_499_);
lean_dec_ref(v___y_498_);
lean_dec(v___y_497_);
lean_dec_ref(v___y_496_);
lean_dec(v___y_495_);
lean_dec(v___y_494_);
lean_dec(v___y_493_);
lean_dec_ref(v_e_492_);
return v_res_505_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__4_spec__6(lean_object* v_msgData_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_){
_start:
{
lean_object* v___x_512_; lean_object* v_env_513_; lean_object* v___x_514_; lean_object* v_mctx_515_; lean_object* v_lctx_516_; lean_object* v_options_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; 
v___x_512_ = lean_st_ref_get(v___y_510_);
v_env_513_ = lean_ctor_get(v___x_512_, 0);
lean_inc_ref(v_env_513_);
lean_dec(v___x_512_);
v___x_514_ = lean_st_ref_get(v___y_508_);
v_mctx_515_ = lean_ctor_get(v___x_514_, 0);
lean_inc_ref(v_mctx_515_);
lean_dec(v___x_514_);
v_lctx_516_ = lean_ctor_get(v___y_507_, 2);
v_options_517_ = lean_ctor_get(v___y_509_, 2);
lean_inc_ref(v_options_517_);
lean_inc_ref(v_lctx_516_);
v___x_518_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_518_, 0, v_env_513_);
lean_ctor_set(v___x_518_, 1, v_mctx_515_);
lean_ctor_set(v___x_518_, 2, v_lctx_516_);
lean_ctor_set(v___x_518_, 3, v_options_517_);
v___x_519_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_519_, 0, v___x_518_);
lean_ctor_set(v___x_519_, 1, v_msgData_506_);
v___x_520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_520_, 0, v___x_519_);
return v___x_520_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__4_spec__6___boxed(lean_object* v_msgData_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_){
_start:
{
lean_object* v_res_527_; 
v_res_527_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__4_spec__6(v_msgData_521_, v___y_522_, v___y_523_, v___y_524_, v___y_525_);
lean_dec(v___y_525_);
lean_dec_ref(v___y_524_);
lean_dec(v___y_523_);
lean_dec_ref(v___y_522_);
return v_res_527_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_528_; double v___x_529_; 
v___x_528_ = lean_unsigned_to_nat(0u);
v___x_529_ = lean_float_of_nat(v___x_528_);
return v___x_529_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__4___redArg(lean_object* v_cls_533_, lean_object* v_msg_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_){
_start:
{
lean_object* v_ref_540_; lean_object* v___x_541_; lean_object* v_a_542_; lean_object* v___x_544_; uint8_t v_isShared_545_; uint8_t v_isSharedCheck_586_; 
v_ref_540_ = lean_ctor_get(v___y_537_, 5);
v___x_541_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__4_spec__6(v_msg_534_, v___y_535_, v___y_536_, v___y_537_, v___y_538_);
v_a_542_ = lean_ctor_get(v___x_541_, 0);
v_isSharedCheck_586_ = !lean_is_exclusive(v___x_541_);
if (v_isSharedCheck_586_ == 0)
{
v___x_544_ = v___x_541_;
v_isShared_545_ = v_isSharedCheck_586_;
goto v_resetjp_543_;
}
else
{
lean_inc(v_a_542_);
lean_dec(v___x_541_);
v___x_544_ = lean_box(0);
v_isShared_545_ = v_isSharedCheck_586_;
goto v_resetjp_543_;
}
v_resetjp_543_:
{
lean_object* v___x_546_; lean_object* v_traceState_547_; lean_object* v_env_548_; lean_object* v_nextMacroScope_549_; lean_object* v_ngen_550_; lean_object* v_auxDeclNGen_551_; lean_object* v_cache_552_; lean_object* v_messages_553_; lean_object* v_infoState_554_; lean_object* v_snapshotTasks_555_; lean_object* v___x_557_; uint8_t v_isShared_558_; uint8_t v_isSharedCheck_585_; 
v___x_546_ = lean_st_ref_take(v___y_538_);
v_traceState_547_ = lean_ctor_get(v___x_546_, 4);
v_env_548_ = lean_ctor_get(v___x_546_, 0);
v_nextMacroScope_549_ = lean_ctor_get(v___x_546_, 1);
v_ngen_550_ = lean_ctor_get(v___x_546_, 2);
v_auxDeclNGen_551_ = lean_ctor_get(v___x_546_, 3);
v_cache_552_ = lean_ctor_get(v___x_546_, 5);
v_messages_553_ = lean_ctor_get(v___x_546_, 6);
v_infoState_554_ = lean_ctor_get(v___x_546_, 7);
v_snapshotTasks_555_ = lean_ctor_get(v___x_546_, 8);
v_isSharedCheck_585_ = !lean_is_exclusive(v___x_546_);
if (v_isSharedCheck_585_ == 0)
{
v___x_557_ = v___x_546_;
v_isShared_558_ = v_isSharedCheck_585_;
goto v_resetjp_556_;
}
else
{
lean_inc(v_snapshotTasks_555_);
lean_inc(v_infoState_554_);
lean_inc(v_messages_553_);
lean_inc(v_cache_552_);
lean_inc(v_traceState_547_);
lean_inc(v_auxDeclNGen_551_);
lean_inc(v_ngen_550_);
lean_inc(v_nextMacroScope_549_);
lean_inc(v_env_548_);
lean_dec(v___x_546_);
v___x_557_ = lean_box(0);
v_isShared_558_ = v_isSharedCheck_585_;
goto v_resetjp_556_;
}
v_resetjp_556_:
{
uint64_t v_tid_559_; lean_object* v_traces_560_; lean_object* v___x_562_; uint8_t v_isShared_563_; uint8_t v_isSharedCheck_584_; 
v_tid_559_ = lean_ctor_get_uint64(v_traceState_547_, sizeof(void*)*1);
v_traces_560_ = lean_ctor_get(v_traceState_547_, 0);
v_isSharedCheck_584_ = !lean_is_exclusive(v_traceState_547_);
if (v_isSharedCheck_584_ == 0)
{
v___x_562_ = v_traceState_547_;
v_isShared_563_ = v_isSharedCheck_584_;
goto v_resetjp_561_;
}
else
{
lean_inc(v_traces_560_);
lean_dec(v_traceState_547_);
v___x_562_ = lean_box(0);
v_isShared_563_ = v_isSharedCheck_584_;
goto v_resetjp_561_;
}
v_resetjp_561_:
{
lean_object* v___x_564_; double v___x_565_; uint8_t v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_574_; 
v___x_564_ = lean_box(0);
v___x_565_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__4___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__4___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__4___redArg___closed__0);
v___x_566_ = 0;
v___x_567_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__4___redArg___closed__1));
v___x_568_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_568_, 0, v_cls_533_);
lean_ctor_set(v___x_568_, 1, v___x_564_);
lean_ctor_set(v___x_568_, 2, v___x_567_);
lean_ctor_set_float(v___x_568_, sizeof(void*)*3, v___x_565_);
lean_ctor_set_float(v___x_568_, sizeof(void*)*3 + 8, v___x_565_);
lean_ctor_set_uint8(v___x_568_, sizeof(void*)*3 + 16, v___x_566_);
v___x_569_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__4___redArg___closed__2));
v___x_570_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_570_, 0, v___x_568_);
lean_ctor_set(v___x_570_, 1, v_a_542_);
lean_ctor_set(v___x_570_, 2, v___x_569_);
lean_inc(v_ref_540_);
v___x_571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_571_, 0, v_ref_540_);
lean_ctor_set(v___x_571_, 1, v___x_570_);
v___x_572_ = l_Lean_PersistentArray_push___redArg(v_traces_560_, v___x_571_);
if (v_isShared_563_ == 0)
{
lean_ctor_set(v___x_562_, 0, v___x_572_);
v___x_574_ = v___x_562_;
goto v_reusejp_573_;
}
else
{
lean_object* v_reuseFailAlloc_583_; 
v_reuseFailAlloc_583_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_583_, 0, v___x_572_);
lean_ctor_set_uint64(v_reuseFailAlloc_583_, sizeof(void*)*1, v_tid_559_);
v___x_574_ = v_reuseFailAlloc_583_;
goto v_reusejp_573_;
}
v_reusejp_573_:
{
lean_object* v___x_576_; 
if (v_isShared_558_ == 0)
{
lean_ctor_set(v___x_557_, 4, v___x_574_);
v___x_576_ = v___x_557_;
goto v_reusejp_575_;
}
else
{
lean_object* v_reuseFailAlloc_582_; 
v_reuseFailAlloc_582_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_582_, 0, v_env_548_);
lean_ctor_set(v_reuseFailAlloc_582_, 1, v_nextMacroScope_549_);
lean_ctor_set(v_reuseFailAlloc_582_, 2, v_ngen_550_);
lean_ctor_set(v_reuseFailAlloc_582_, 3, v_auxDeclNGen_551_);
lean_ctor_set(v_reuseFailAlloc_582_, 4, v___x_574_);
lean_ctor_set(v_reuseFailAlloc_582_, 5, v_cache_552_);
lean_ctor_set(v_reuseFailAlloc_582_, 6, v_messages_553_);
lean_ctor_set(v_reuseFailAlloc_582_, 7, v_infoState_554_);
lean_ctor_set(v_reuseFailAlloc_582_, 8, v_snapshotTasks_555_);
v___x_576_ = v_reuseFailAlloc_582_;
goto v_reusejp_575_;
}
v_reusejp_575_:
{
lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_580_; 
v___x_577_ = lean_st_ref_set(v___y_538_, v___x_576_);
v___x_578_ = lean_box(0);
if (v_isShared_545_ == 0)
{
lean_ctor_set(v___x_544_, 0, v___x_578_);
v___x_580_ = v___x_544_;
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
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__4___redArg___boxed(lean_object* v_cls_587_, lean_object* v_msg_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_){
_start:
{
lean_object* v_res_594_; 
v_res_594_ = l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__4___redArg(v_cls_587_, v_msg_588_, v___y_589_, v___y_590_, v___y_591_, v___y_592_);
lean_dec(v___y_592_);
lean_dec_ref(v___y_591_);
lean_dec(v___y_590_);
lean_dec_ref(v___y_589_);
return v_res_594_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_AC_internalize___closed__5(void){
_start:
{
lean_object* v___x_603_; lean_object* v___x_604_; 
v___x_603_ = ((lean_object*)(l_Lean_Meta_Grind_AC_internalize___closed__4));
v___x_604_ = l_Lean_stringToMessageData(v___x_603_);
return v___x_604_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_AC_internalize___closed__7(void){
_start:
{
lean_object* v___x_606_; lean_object* v___x_607_; 
v___x_606_ = ((lean_object*)(l_Lean_Meta_Grind_AC_internalize___closed__6));
v___x_607_ = l_Lean_stringToMessageData(v___x_606_);
return v___x_607_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_internalize(lean_object* v_e_608_, lean_object* v_parent_x3f_609_, lean_object* v_a_610_, lean_object* v_a_611_, lean_object* v_a_612_, lean_object* v_a_613_, lean_object* v_a_614_, lean_object* v_a_615_, lean_object* v_a_616_, lean_object* v_a_617_, lean_object* v_a_618_, lean_object* v_a_619_){
_start:
{
lean_object* v___y_622_; lean_object* v___y_623_; lean_object* v___y_624_; lean_object* v___y_625_; lean_object* v___y_626_; lean_object* v___y_627_; lean_object* v___y_628_; lean_object* v___y_629_; lean_object* v___y_630_; lean_object* v___y_631_; lean_object* v___y_632_; lean_object* v___x_636_; 
v___x_636_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_612_);
if (lean_obj_tag(v___x_636_) == 0)
{
lean_object* v_a_637_; lean_object* v___x_639_; uint8_t v_isShared_640_; uint8_t v_isSharedCheck_748_; 
v_a_637_ = lean_ctor_get(v___x_636_, 0);
v_isSharedCheck_748_ = !lean_is_exclusive(v___x_636_);
if (v_isSharedCheck_748_ == 0)
{
v___x_639_ = v___x_636_;
v_isShared_640_ = v_isSharedCheck_748_;
goto v_resetjp_638_;
}
else
{
lean_inc(v_a_637_);
lean_dec(v___x_636_);
v___x_639_ = lean_box(0);
v_isShared_640_ = v_isSharedCheck_748_;
goto v_resetjp_638_;
}
v_resetjp_638_:
{
uint8_t v_ac_641_; uint8_t v___y_643_; 
v_ac_641_ = lean_ctor_get_uint8(v_a_637_, sizeof(void*)*11 + 24);
lean_dec(v_a_637_);
if (v_ac_641_ == 0)
{
lean_object* v___x_743_; lean_object* v___x_744_; 
lean_del_object(v___x_639_);
lean_dec(v_a_619_);
lean_dec_ref(v_a_618_);
lean_dec(v_a_617_);
lean_dec_ref(v_a_616_);
lean_dec(v_a_615_);
lean_dec_ref(v_a_614_);
lean_dec(v_a_613_);
lean_dec_ref(v_a_612_);
lean_dec(v_a_611_);
lean_dec(v_a_610_);
lean_dec(v_parent_x3f_609_);
lean_dec_ref(v_e_608_);
v___x_743_ = lean_box(0);
v___x_744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_744_, 0, v___x_743_);
return v___x_744_;
}
else
{
uint8_t v___x_745_; 
v___x_745_ = l_Lean_Expr_isApp(v_e_608_);
if (v___x_745_ == 0)
{
v___y_643_ = v___x_745_;
goto v___jp_642_;
}
else
{
lean_object* v___x_746_; uint8_t v___x_747_; 
v___x_746_ = l_Lean_Expr_appFn_x21(v_e_608_);
v___x_747_ = l_Lean_Expr_isApp(v___x_746_);
lean_dec_ref(v___x_746_);
v___y_643_ = v___x_747_;
goto v___jp_642_;
}
}
v___jp_642_:
{
if (v___y_643_ == 0)
{
lean_object* v___x_644_; lean_object* v___x_646_; 
lean_dec(v_a_619_);
lean_dec_ref(v_a_618_);
lean_dec(v_a_617_);
lean_dec_ref(v_a_616_);
lean_dec(v_a_615_);
lean_dec_ref(v_a_614_);
lean_dec(v_a_613_);
lean_dec_ref(v_a_612_);
lean_dec(v_a_611_);
lean_dec(v_a_610_);
lean_dec(v_parent_x3f_609_);
lean_dec_ref(v_e_608_);
v___x_644_ = lean_box(0);
if (v_isShared_640_ == 0)
{
lean_ctor_set(v___x_639_, 0, v___x_644_);
v___x_646_ = v___x_639_;
goto v_reusejp_645_;
}
else
{
lean_object* v_reuseFailAlloc_647_; 
v_reuseFailAlloc_647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_647_, 0, v___x_644_);
v___x_646_ = v_reuseFailAlloc_647_;
goto v_reusejp_645_;
}
v_reusejp_645_:
{
return v___x_646_;
}
}
else
{
lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; 
lean_del_object(v___x_639_);
v___x_648_ = l_Lean_Expr_appFn_x21(v_e_608_);
v___x_649_ = l_Lean_Expr_appFn_x21(v___x_648_);
lean_dec_ref(v___x_648_);
lean_inc(v_a_619_);
lean_inc_ref(v_a_618_);
lean_inc(v_a_617_);
lean_inc_ref(v_a_616_);
lean_inc(v_a_615_);
lean_inc_ref(v_a_614_);
lean_inc(v_a_613_);
lean_inc_ref(v_a_612_);
lean_inc(v_a_611_);
lean_inc(v_a_610_);
lean_inc_ref(v___x_649_);
v___x_650_ = l_Lean_Meta_Grind_AC_getOpId_x3f(v___x_649_, v_a_610_, v_a_611_, v_a_612_, v_a_613_, v_a_614_, v_a_615_, v_a_616_, v_a_617_, v_a_618_, v_a_619_);
if (lean_obj_tag(v___x_650_) == 0)
{
lean_object* v_a_651_; lean_object* v___x_653_; uint8_t v_isShared_654_; uint8_t v_isSharedCheck_734_; 
v_a_651_ = lean_ctor_get(v___x_650_, 0);
v_isSharedCheck_734_ = !lean_is_exclusive(v___x_650_);
if (v_isSharedCheck_734_ == 0)
{
v___x_653_ = v___x_650_;
v_isShared_654_ = v_isSharedCheck_734_;
goto v_resetjp_652_;
}
else
{
lean_inc(v_a_651_);
lean_dec(v___x_650_);
v___x_653_ = lean_box(0);
v_isShared_654_ = v_isSharedCheck_734_;
goto v_resetjp_652_;
}
v_resetjp_652_:
{
if (lean_obj_tag(v_a_651_) == 1)
{
lean_object* v_val_655_; lean_object* v___x_656_; lean_object* v_a_657_; lean_object* v___x_659_; uint8_t v_isShared_660_; uint8_t v_isSharedCheck_729_; 
lean_del_object(v___x_653_);
v_val_655_ = lean_ctor_get(v_a_651_, 0);
lean_inc(v_val_655_);
lean_dec_ref(v_a_651_);
v___x_656_ = l___private_Lean_Meta_Tactic_Grind_AC_Internalize_0__Lean_Meta_Grind_AC_isParentSameOpApp___redArg(v_parent_x3f_609_, v___x_649_);
lean_dec_ref(v___x_649_);
v_a_657_ = lean_ctor_get(v___x_656_, 0);
v_isSharedCheck_729_ = !lean_is_exclusive(v___x_656_);
if (v_isSharedCheck_729_ == 0)
{
v___x_659_ = v___x_656_;
v_isShared_660_ = v_isSharedCheck_729_;
goto v_resetjp_658_;
}
else
{
lean_inc(v_a_657_);
lean_dec(v___x_656_);
v___x_659_ = lean_box(0);
v_isShared_660_ = v_isSharedCheck_729_;
goto v_resetjp_658_;
}
v_resetjp_658_:
{
uint8_t v___x_661_; 
v___x_661_ = lean_unbox(v_a_657_);
lean_dec(v_a_657_);
if (v___x_661_ == 0)
{
lean_object* v___x_662_; 
lean_del_object(v___x_659_);
v___x_662_ = l_Lean_Meta_Grind_AC_ACM_getStruct(v_val_655_, v_a_610_, v_a_611_, v_a_612_, v_a_613_, v_a_614_, v_a_615_, v_a_616_, v_a_617_, v_a_618_, v_a_619_);
if (lean_obj_tag(v___x_662_) == 0)
{
lean_object* v_a_663_; lean_object* v___x_665_; uint8_t v_isShared_666_; uint8_t v_isSharedCheck_716_; 
v_a_663_ = lean_ctor_get(v___x_662_, 0);
v_isSharedCheck_716_ = !lean_is_exclusive(v___x_662_);
if (v_isSharedCheck_716_ == 0)
{
v___x_665_ = v___x_662_;
v_isShared_666_ = v_isSharedCheck_716_;
goto v_resetjp_664_;
}
else
{
lean_inc(v_a_663_);
lean_dec(v___x_662_);
v___x_665_ = lean_box(0);
v_isShared_666_ = v_isSharedCheck_716_;
goto v_resetjp_664_;
}
v_resetjp_664_:
{
lean_object* v_denote_667_; uint8_t v___x_668_; 
v_denote_667_ = lean_ctor_get(v_a_663_, 12);
lean_inc_ref(v_denote_667_);
lean_dec(v_a_663_);
v___x_668_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0___redArg(v_denote_667_, v_e_608_);
if (v___x_668_ == 0)
{
lean_object* v___x_669_; 
lean_del_object(v___x_665_);
lean_inc(v_a_619_);
lean_inc_ref(v_a_618_);
lean_inc(v_a_617_);
lean_inc_ref(v_a_616_);
lean_inc(v_a_615_);
lean_inc_ref(v_a_614_);
lean_inc(v_a_613_);
lean_inc_ref(v_a_612_);
lean_inc(v_a_611_);
lean_inc(v_a_610_);
lean_inc(v_val_655_);
lean_inc_ref(v_e_608_);
v___x_669_ = l_Lean_Meta_Grind_AC_reify(v_e_608_, v_val_655_, v_a_610_, v_a_611_, v_a_612_, v_a_613_, v_a_614_, v_a_615_, v_a_616_, v_a_617_, v_a_618_, v_a_619_);
if (lean_obj_tag(v___x_669_) == 0)
{
lean_object* v_a_670_; lean_object* v___x_671_; lean_object* v___f_672_; lean_object* v___x_673_; 
v_a_670_ = lean_ctor_get(v___x_669_, 0);
lean_inc(v_a_670_);
lean_dec_ref(v___x_669_);
v___x_671_ = lean_box(v_ac_641_);
lean_inc(v_a_670_);
lean_inc_ref(v_e_608_);
v___f_672_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_AC_internalize___lam__0___boxed), 4, 3);
lean_closure_set(v___f_672_, 0, v_e_608_);
lean_closure_set(v___f_672_, 1, v_a_670_);
lean_closure_set(v___f_672_, 2, v___x_671_);
lean_inc(v_val_655_);
v___x_673_ = l_Lean_Meta_Grind_AC_modifyStruct___redArg(v___f_672_, v_val_655_, v_a_610_);
if (lean_obj_tag(v___x_673_) == 0)
{
lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v_a_676_; lean_object* v___x_678_; uint8_t v_isShared_679_; uint8_t v_isSharedCheck_703_; 
lean_dec_ref(v___x_673_);
v___x_674_ = ((lean_object*)(l_Lean_Meta_Grind_AC_internalize___closed__3));
v___x_675_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_AC_internalize_spec__2___redArg(v___x_674_, v_a_618_);
v_a_676_ = lean_ctor_get(v___x_675_, 0);
v_isSharedCheck_703_ = !lean_is_exclusive(v___x_675_);
if (v_isSharedCheck_703_ == 0)
{
v___x_678_ = v___x_675_;
v_isShared_679_ = v_isSharedCheck_703_;
goto v_resetjp_677_;
}
else
{
lean_inc(v_a_676_);
lean_dec(v___x_675_);
v___x_678_ = lean_box(0);
v_isShared_679_ = v_isSharedCheck_703_;
goto v_resetjp_677_;
}
v_resetjp_677_:
{
uint8_t v___x_680_; 
v___x_680_ = lean_unbox(v_a_676_);
lean_dec(v_a_676_);
if (v___x_680_ == 0)
{
lean_del_object(v___x_678_);
lean_dec(v_a_670_);
v___y_622_ = v_val_655_;
v___y_623_ = v_a_610_;
v___y_624_ = v_a_611_;
v___y_625_ = v_a_612_;
v___y_626_ = v_a_613_;
v___y_627_ = v_a_614_;
v___y_628_ = v_a_615_;
v___y_629_ = v_a_616_;
v___y_630_ = v_a_617_;
v___y_631_ = v_a_618_;
v___y_632_ = v_a_619_;
goto v___jp_621_;
}
else
{
lean_object* v___x_681_; 
v___x_681_ = l_Lean_Grind_AC_Expr_denoteExpr___at___00Lean_Meta_Grind_AC_internalize_spec__3(v_a_670_, v_val_655_, v_a_610_, v_a_611_, v_a_612_, v_a_613_, v_a_614_, v_a_615_, v_a_616_, v_a_617_, v_a_618_, v_a_619_);
lean_dec(v_a_670_);
if (lean_obj_tag(v___x_681_) == 0)
{
lean_object* v_a_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_686_; 
v_a_682_ = lean_ctor_get(v___x_681_, 0);
lean_inc(v_a_682_);
lean_dec_ref(v___x_681_);
v___x_683_ = lean_obj_once(&l_Lean_Meta_Grind_AC_internalize___closed__5, &l_Lean_Meta_Grind_AC_internalize___closed__5_once, _init_l_Lean_Meta_Grind_AC_internalize___closed__5);
lean_inc(v_val_655_);
v___x_684_ = l_Nat_reprFast(v_val_655_);
if (v_isShared_679_ == 0)
{
lean_ctor_set_tag(v___x_678_, 3);
lean_ctor_set(v___x_678_, 0, v___x_684_);
v___x_686_ = v___x_678_;
goto v_reusejp_685_;
}
else
{
lean_object* v_reuseFailAlloc_694_; 
v_reuseFailAlloc_694_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_694_, 0, v___x_684_);
v___x_686_ = v_reuseFailAlloc_694_;
goto v_reusejp_685_;
}
v_reusejp_685_:
{
lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; 
v___x_687_ = l_Lean_MessageData_ofFormat(v___x_686_);
v___x_688_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_688_, 0, v___x_683_);
lean_ctor_set(v___x_688_, 1, v___x_687_);
v___x_689_ = lean_obj_once(&l_Lean_Meta_Grind_AC_internalize___closed__7, &l_Lean_Meta_Grind_AC_internalize___closed__7_once, _init_l_Lean_Meta_Grind_AC_internalize___closed__7);
v___x_690_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_690_, 0, v___x_688_);
lean_ctor_set(v___x_690_, 1, v___x_689_);
v___x_691_ = l_Lean_MessageData_ofExpr(v_a_682_);
v___x_692_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_692_, 0, v___x_690_);
lean_ctor_set(v___x_692_, 1, v___x_691_);
v___x_693_ = l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__4___redArg(v___x_674_, v___x_692_, v_a_616_, v_a_617_, v_a_618_, v_a_619_);
if (lean_obj_tag(v___x_693_) == 0)
{
lean_dec_ref(v___x_693_);
v___y_622_ = v_val_655_;
v___y_623_ = v_a_610_;
v___y_624_ = v_a_611_;
v___y_625_ = v_a_612_;
v___y_626_ = v_a_613_;
v___y_627_ = v_a_614_;
v___y_628_ = v_a_615_;
v___y_629_ = v_a_616_;
v___y_630_ = v_a_617_;
v___y_631_ = v_a_618_;
v___y_632_ = v_a_619_;
goto v___jp_621_;
}
else
{
lean_dec(v_val_655_);
lean_dec(v_a_619_);
lean_dec_ref(v_a_618_);
lean_dec(v_a_617_);
lean_dec_ref(v_a_616_);
lean_dec(v_a_615_);
lean_dec_ref(v_a_614_);
lean_dec(v_a_613_);
lean_dec_ref(v_a_612_);
lean_dec(v_a_611_);
lean_dec(v_a_610_);
lean_dec_ref(v_e_608_);
return v___x_693_;
}
}
}
else
{
lean_object* v_a_695_; lean_object* v___x_697_; uint8_t v_isShared_698_; uint8_t v_isSharedCheck_702_; 
lean_del_object(v___x_678_);
lean_dec(v_val_655_);
lean_dec(v_a_619_);
lean_dec_ref(v_a_618_);
lean_dec(v_a_617_);
lean_dec_ref(v_a_616_);
lean_dec(v_a_615_);
lean_dec_ref(v_a_614_);
lean_dec(v_a_613_);
lean_dec_ref(v_a_612_);
lean_dec(v_a_611_);
lean_dec(v_a_610_);
lean_dec_ref(v_e_608_);
v_a_695_ = lean_ctor_get(v___x_681_, 0);
v_isSharedCheck_702_ = !lean_is_exclusive(v___x_681_);
if (v_isSharedCheck_702_ == 0)
{
v___x_697_ = v___x_681_;
v_isShared_698_ = v_isSharedCheck_702_;
goto v_resetjp_696_;
}
else
{
lean_inc(v_a_695_);
lean_dec(v___x_681_);
v___x_697_ = lean_box(0);
v_isShared_698_ = v_isSharedCheck_702_;
goto v_resetjp_696_;
}
v_resetjp_696_:
{
lean_object* v___x_700_; 
if (v_isShared_698_ == 0)
{
v___x_700_ = v___x_697_;
goto v_reusejp_699_;
}
else
{
lean_object* v_reuseFailAlloc_701_; 
v_reuseFailAlloc_701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v_a_695_);
v___x_700_ = v_reuseFailAlloc_701_;
goto v_reusejp_699_;
}
v_reusejp_699_:
{
return v___x_700_;
}
}
}
}
}
}
else
{
lean_dec(v_a_670_);
lean_dec(v_val_655_);
lean_dec(v_a_619_);
lean_dec_ref(v_a_618_);
lean_dec(v_a_617_);
lean_dec_ref(v_a_616_);
lean_dec(v_a_615_);
lean_dec_ref(v_a_614_);
lean_dec(v_a_613_);
lean_dec_ref(v_a_612_);
lean_dec(v_a_611_);
lean_dec(v_a_610_);
lean_dec_ref(v_e_608_);
return v___x_673_;
}
}
else
{
lean_object* v_a_704_; lean_object* v___x_706_; uint8_t v_isShared_707_; uint8_t v_isSharedCheck_711_; 
lean_dec(v_val_655_);
lean_dec(v_a_619_);
lean_dec_ref(v_a_618_);
lean_dec(v_a_617_);
lean_dec_ref(v_a_616_);
lean_dec(v_a_615_);
lean_dec_ref(v_a_614_);
lean_dec(v_a_613_);
lean_dec_ref(v_a_612_);
lean_dec(v_a_611_);
lean_dec(v_a_610_);
lean_dec_ref(v_e_608_);
v_a_704_ = lean_ctor_get(v___x_669_, 0);
v_isSharedCheck_711_ = !lean_is_exclusive(v___x_669_);
if (v_isSharedCheck_711_ == 0)
{
v___x_706_ = v___x_669_;
v_isShared_707_ = v_isSharedCheck_711_;
goto v_resetjp_705_;
}
else
{
lean_inc(v_a_704_);
lean_dec(v___x_669_);
v___x_706_ = lean_box(0);
v_isShared_707_ = v_isSharedCheck_711_;
goto v_resetjp_705_;
}
v_resetjp_705_:
{
lean_object* v___x_709_; 
if (v_isShared_707_ == 0)
{
v___x_709_ = v___x_706_;
goto v_reusejp_708_;
}
else
{
lean_object* v_reuseFailAlloc_710_; 
v_reuseFailAlloc_710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_710_, 0, v_a_704_);
v___x_709_ = v_reuseFailAlloc_710_;
goto v_reusejp_708_;
}
v_reusejp_708_:
{
return v___x_709_;
}
}
}
}
else
{
lean_object* v___x_712_; lean_object* v___x_714_; 
lean_dec(v_val_655_);
lean_dec(v_a_619_);
lean_dec_ref(v_a_618_);
lean_dec(v_a_617_);
lean_dec_ref(v_a_616_);
lean_dec(v_a_615_);
lean_dec_ref(v_a_614_);
lean_dec(v_a_613_);
lean_dec_ref(v_a_612_);
lean_dec(v_a_611_);
lean_dec(v_a_610_);
lean_dec_ref(v_e_608_);
v___x_712_ = lean_box(0);
if (v_isShared_666_ == 0)
{
lean_ctor_set(v___x_665_, 0, v___x_712_);
v___x_714_ = v___x_665_;
goto v_reusejp_713_;
}
else
{
lean_object* v_reuseFailAlloc_715_; 
v_reuseFailAlloc_715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_715_, 0, v___x_712_);
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
else
{
lean_object* v_a_717_; lean_object* v___x_719_; uint8_t v_isShared_720_; uint8_t v_isSharedCheck_724_; 
lean_dec(v_val_655_);
lean_dec(v_a_619_);
lean_dec_ref(v_a_618_);
lean_dec(v_a_617_);
lean_dec_ref(v_a_616_);
lean_dec(v_a_615_);
lean_dec_ref(v_a_614_);
lean_dec(v_a_613_);
lean_dec_ref(v_a_612_);
lean_dec(v_a_611_);
lean_dec(v_a_610_);
lean_dec_ref(v_e_608_);
v_a_717_ = lean_ctor_get(v___x_662_, 0);
v_isSharedCheck_724_ = !lean_is_exclusive(v___x_662_);
if (v_isSharedCheck_724_ == 0)
{
v___x_719_ = v___x_662_;
v_isShared_720_ = v_isSharedCheck_724_;
goto v_resetjp_718_;
}
else
{
lean_inc(v_a_717_);
lean_dec(v___x_662_);
v___x_719_ = lean_box(0);
v_isShared_720_ = v_isSharedCheck_724_;
goto v_resetjp_718_;
}
v_resetjp_718_:
{
lean_object* v___x_722_; 
if (v_isShared_720_ == 0)
{
v___x_722_ = v___x_719_;
goto v_reusejp_721_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v_a_717_);
v___x_722_ = v_reuseFailAlloc_723_;
goto v_reusejp_721_;
}
v_reusejp_721_:
{
return v___x_722_;
}
}
}
}
else
{
lean_object* v___x_725_; lean_object* v___x_727_; 
lean_dec(v_val_655_);
lean_dec(v_a_619_);
lean_dec_ref(v_a_618_);
lean_dec(v_a_617_);
lean_dec_ref(v_a_616_);
lean_dec(v_a_615_);
lean_dec_ref(v_a_614_);
lean_dec(v_a_613_);
lean_dec_ref(v_a_612_);
lean_dec(v_a_611_);
lean_dec(v_a_610_);
lean_dec_ref(v_e_608_);
v___x_725_ = lean_box(0);
if (v_isShared_660_ == 0)
{
lean_ctor_set(v___x_659_, 0, v___x_725_);
v___x_727_ = v___x_659_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_728_; 
v_reuseFailAlloc_728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_728_, 0, v___x_725_);
v___x_727_ = v_reuseFailAlloc_728_;
goto v_reusejp_726_;
}
v_reusejp_726_:
{
return v___x_727_;
}
}
}
}
else
{
lean_object* v___x_730_; lean_object* v___x_732_; 
lean_dec(v_a_651_);
lean_dec_ref(v___x_649_);
lean_dec(v_a_619_);
lean_dec_ref(v_a_618_);
lean_dec(v_a_617_);
lean_dec_ref(v_a_616_);
lean_dec(v_a_615_);
lean_dec_ref(v_a_614_);
lean_dec(v_a_613_);
lean_dec_ref(v_a_612_);
lean_dec(v_a_611_);
lean_dec(v_a_610_);
lean_dec(v_parent_x3f_609_);
lean_dec_ref(v_e_608_);
v___x_730_ = lean_box(0);
if (v_isShared_654_ == 0)
{
lean_ctor_set(v___x_653_, 0, v___x_730_);
v___x_732_ = v___x_653_;
goto v_reusejp_731_;
}
else
{
lean_object* v_reuseFailAlloc_733_; 
v_reuseFailAlloc_733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_733_, 0, v___x_730_);
v___x_732_ = v_reuseFailAlloc_733_;
goto v_reusejp_731_;
}
v_reusejp_731_:
{
return v___x_732_;
}
}
}
}
else
{
lean_object* v_a_735_; lean_object* v___x_737_; uint8_t v_isShared_738_; uint8_t v_isSharedCheck_742_; 
lean_dec_ref(v___x_649_);
lean_dec(v_a_619_);
lean_dec_ref(v_a_618_);
lean_dec(v_a_617_);
lean_dec_ref(v_a_616_);
lean_dec(v_a_615_);
lean_dec_ref(v_a_614_);
lean_dec(v_a_613_);
lean_dec_ref(v_a_612_);
lean_dec(v_a_611_);
lean_dec(v_a_610_);
lean_dec(v_parent_x3f_609_);
lean_dec_ref(v_e_608_);
v_a_735_ = lean_ctor_get(v___x_650_, 0);
v_isSharedCheck_742_ = !lean_is_exclusive(v___x_650_);
if (v_isSharedCheck_742_ == 0)
{
v___x_737_ = v___x_650_;
v_isShared_738_ = v_isSharedCheck_742_;
goto v_resetjp_736_;
}
else
{
lean_inc(v_a_735_);
lean_dec(v___x_650_);
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
}
}
else
{
lean_object* v_a_749_; lean_object* v___x_751_; uint8_t v_isShared_752_; uint8_t v_isSharedCheck_756_; 
lean_dec(v_a_619_);
lean_dec_ref(v_a_618_);
lean_dec(v_a_617_);
lean_dec_ref(v_a_616_);
lean_dec(v_a_615_);
lean_dec_ref(v_a_614_);
lean_dec(v_a_613_);
lean_dec_ref(v_a_612_);
lean_dec(v_a_611_);
lean_dec(v_a_610_);
lean_dec(v_parent_x3f_609_);
lean_dec_ref(v_e_608_);
v_a_749_ = lean_ctor_get(v___x_636_, 0);
v_isSharedCheck_756_ = !lean_is_exclusive(v___x_636_);
if (v_isSharedCheck_756_ == 0)
{
v___x_751_ = v___x_636_;
v_isShared_752_ = v_isSharedCheck_756_;
goto v_resetjp_750_;
}
else
{
lean_inc(v_a_749_);
lean_dec(v___x_636_);
v___x_751_ = lean_box(0);
v_isShared_752_ = v_isSharedCheck_756_;
goto v_resetjp_750_;
}
v_resetjp_750_:
{
lean_object* v___x_754_; 
if (v_isShared_752_ == 0)
{
v___x_754_ = v___x_751_;
goto v_reusejp_753_;
}
else
{
lean_object* v_reuseFailAlloc_755_; 
v_reuseFailAlloc_755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_755_, 0, v_a_749_);
v___x_754_ = v_reuseFailAlloc_755_;
goto v_reusejp_753_;
}
v_reusejp_753_:
{
return v___x_754_;
}
}
}
v___jp_621_:
{
lean_object* v___x_633_; 
lean_inc_ref(v_e_608_);
v___x_633_ = l_Lean_Meta_Grind_AC_addTermOpId___redArg(v_e_608_, v___y_622_, v___y_623_);
if (lean_obj_tag(v___x_633_) == 0)
{
lean_object* v___x_634_; lean_object* v___x_635_; 
lean_dec_ref(v___x_633_);
v___x_634_ = l_Lean_Meta_Grind_AC_acExt;
v___x_635_ = l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(v___x_634_, v_e_608_, v___y_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_, v___y_630_, v___y_631_, v___y_632_);
return v___x_635_;
}
else
{
lean_dec(v___y_632_);
lean_dec_ref(v___y_631_);
lean_dec(v___y_630_);
lean_dec_ref(v___y_629_);
lean_dec(v___y_628_);
lean_dec_ref(v___y_627_);
lean_dec(v___y_626_);
lean_dec_ref(v___y_625_);
lean_dec(v___y_624_);
lean_dec(v___y_623_);
lean_dec_ref(v_e_608_);
return v___x_633_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_internalize___boxed(lean_object* v_e_757_, lean_object* v_parent_x3f_758_, lean_object* v_a_759_, lean_object* v_a_760_, lean_object* v_a_761_, lean_object* v_a_762_, lean_object* v_a_763_, lean_object* v_a_764_, lean_object* v_a_765_, lean_object* v_a_766_, lean_object* v_a_767_, lean_object* v_a_768_, lean_object* v_a_769_){
_start:
{
lean_object* v_res_770_; 
v_res_770_ = l_Lean_Meta_Grind_AC_internalize(v_e_757_, v_parent_x3f_758_, v_a_759_, v_a_760_, v_a_761_, v_a_762_, v_a_763_, v_a_764_, v_a_765_, v_a_766_, v_a_767_, v_a_768_);
return v_res_770_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0(lean_object* v_00_u03b2_771_, lean_object* v_x_772_, lean_object* v_x_773_){
_start:
{
uint8_t v___x_774_; 
v___x_774_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0___redArg(v_x_772_, v_x_773_);
return v___x_774_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0___boxed(lean_object* v_00_u03b2_775_, lean_object* v_x_776_, lean_object* v_x_777_){
_start:
{
uint8_t v_res_778_; lean_object* v_r_779_; 
v_res_778_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0(v_00_u03b2_775_, v_x_776_, v_x_777_);
lean_dec_ref(v_x_777_);
v_r_779_ = lean_box(v_res_778_);
return v_r_779_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1(lean_object* v_00_u03b2_780_, lean_object* v_x_781_, lean_object* v_x_782_, lean_object* v_x_783_){
_start:
{
lean_object* v___x_784_; 
v___x_784_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1___redArg(v_x_781_, v_x_782_, v_x_783_);
return v___x_784_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__4(lean_object* v_cls_785_, lean_object* v_msg_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_){
_start:
{
lean_object* v___x_799_; 
v___x_799_ = l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__4___redArg(v_cls_785_, v_msg_786_, v___y_794_, v___y_795_, v___y_796_, v___y_797_);
return v___x_799_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__4___boxed(lean_object* v_cls_800_, lean_object* v_msg_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_){
_start:
{
lean_object* v_res_814_; 
v_res_814_ = l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__4(v_cls_800_, v_msg_801_, v___y_802_, v___y_803_, v___y_804_, v___y_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_, v___y_812_);
lean_dec(v___y_812_);
lean_dec_ref(v___y_811_);
lean_dec(v___y_810_);
lean_dec_ref(v___y_809_);
lean_dec(v___y_808_);
lean_dec_ref(v___y_807_);
lean_dec(v___y_806_);
lean_dec_ref(v___y_805_);
lean_dec(v___y_804_);
lean_dec(v___y_803_);
lean_dec(v___y_802_);
return v_res_814_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0(lean_object* v_00_u03b2_815_, lean_object* v_x_816_, size_t v_x_817_, lean_object* v_x_818_){
_start:
{
uint8_t v___x_819_; 
v___x_819_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0___redArg(v_x_816_, v_x_817_, v_x_818_);
return v___x_819_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0___boxed(lean_object* v_00_u03b2_820_, lean_object* v_x_821_, lean_object* v_x_822_, lean_object* v_x_823_){
_start:
{
size_t v_x_55578__boxed_824_; uint8_t v_res_825_; lean_object* v_r_826_; 
v_x_55578__boxed_824_ = lean_unbox_usize(v_x_822_);
lean_dec(v_x_822_);
v_res_825_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0(v_00_u03b2_820_, v_x_821_, v_x_55578__boxed_824_, v_x_823_);
lean_dec_ref(v_x_823_);
v_r_826_ = lean_box(v_res_825_);
return v_r_826_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2(lean_object* v_00_u03b2_827_, lean_object* v_x_828_, size_t v_x_829_, size_t v_x_830_, lean_object* v_x_831_, lean_object* v_x_832_){
_start:
{
lean_object* v___x_833_; 
v___x_833_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___redArg(v_x_828_, v_x_829_, v_x_830_, v_x_831_, v_x_832_);
return v___x_833_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___boxed(lean_object* v_00_u03b2_834_, lean_object* v_x_835_, lean_object* v_x_836_, lean_object* v_x_837_, lean_object* v_x_838_, lean_object* v_x_839_){
_start:
{
size_t v_x_55589__boxed_840_; size_t v_x_55590__boxed_841_; lean_object* v_res_842_; 
v_x_55589__boxed_840_ = lean_unbox_usize(v_x_836_);
lean_dec(v_x_836_);
v_x_55590__boxed_841_ = lean_unbox_usize(v_x_837_);
lean_dec(v_x_837_);
v_res_842_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2(v_00_u03b2_834_, v_x_835_, v_x_55589__boxed_840_, v_x_55590__boxed_841_, v_x_838_, v_x_839_);
return v_res_842_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_843_, lean_object* v_keys_844_, lean_object* v_vals_845_, lean_object* v_heq_846_, lean_object* v_i_847_, lean_object* v_k_848_){
_start:
{
uint8_t v___x_849_; 
v___x_849_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0_spec__2___redArg(v_keys_844_, v_i_847_, v_k_848_);
return v___x_849_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_850_, lean_object* v_keys_851_, lean_object* v_vals_852_, lean_object* v_heq_853_, lean_object* v_i_854_, lean_object* v_k_855_){
_start:
{
uint8_t v_res_856_; lean_object* v_r_857_; 
v_res_856_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0_spec__2(v_00_u03b2_850_, v_keys_851_, v_vals_852_, v_heq_853_, v_i_854_, v_k_855_);
lean_dec_ref(v_k_855_);
lean_dec_ref(v_vals_852_);
lean_dec_ref(v_keys_851_);
v_r_857_ = lean_box(v_res_856_);
return v_r_857_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_858_, lean_object* v_n_859_, lean_object* v_k_860_, lean_object* v_v_861_){
_start:
{
lean_object* v___x_862_; 
v___x_862_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2_spec__5___redArg(v_n_859_, v_k_860_, v_v_861_);
return v___x_862_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2_spec__6(lean_object* v_00_u03b2_863_, size_t v_depth_864_, lean_object* v_keys_865_, lean_object* v_vals_866_, lean_object* v_heq_867_, lean_object* v_i_868_, lean_object* v_entries_869_){
_start:
{
lean_object* v___x_870_; 
v___x_870_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2_spec__6___redArg(v_depth_864_, v_keys_865_, v_vals_866_, v_i_868_, v_entries_869_);
return v___x_870_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2_spec__6___boxed(lean_object* v_00_u03b2_871_, lean_object* v_depth_872_, lean_object* v_keys_873_, lean_object* v_vals_874_, lean_object* v_heq_875_, lean_object* v_i_876_, lean_object* v_entries_877_){
_start:
{
size_t v_depth_boxed_878_; lean_object* v_res_879_; 
v_depth_boxed_878_ = lean_unbox_usize(v_depth_872_);
lean_dec(v_depth_872_);
v_res_879_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2_spec__6(v_00_u03b2_871_, v_depth_boxed_878_, v_keys_873_, v_vals_874_, v_heq_875_, v_i_876_, v_entries_877_);
lean_dec_ref(v_vals_874_);
lean_dec_ref(v_keys_873_);
return v_res_879_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2_spec__5_spec__9(lean_object* v_00_u03b2_880_, lean_object* v_x_881_, lean_object* v_x_882_, lean_object* v_x_883_, lean_object* v_x_884_){
_start:
{
lean_object* v___x_885_; 
v___x_885_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2_spec__5_spec__9___redArg(v_x_881_, v_x_882_, v_x_883_, v_x_884_);
return v___x_885_;
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
