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
lean_object* l_Lean_Meta_Grind_AC_ACM_getStruct(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_outOfBounds___redArg(lean_object*);
lean_object* l_Lean_PersistentArray_get_x21___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_size(lean_object*);
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
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___redArg___closed__2;
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
lean_dec(v_a_133_);
lean_dec_ref(v_a_132_);
lean_dec(v_a_131_);
lean_dec_ref(v_a_130_);
lean_dec(v_a_129_);
lean_dec_ref(v_a_128_);
lean_dec(v_a_127_);
lean_dec_ref(v_a_126_);
lean_dec(v_a_125_);
lean_dec(v_a_124_);
lean_dec(v_a_123_);
return v_res_135_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2_spec__4_spec__8___redArg(lean_object* v_x_136_, lean_object* v_x_137_, lean_object* v_x_138_, lean_object* v_x_139_){
_start:
{
lean_object* v_ks_140_; lean_object* v_vs_141_; lean_object* v___x_143_; uint8_t v_isShared_144_; uint8_t v_isSharedCheck_165_; 
v_ks_140_ = lean_ctor_get(v_x_136_, 0);
v_vs_141_ = lean_ctor_get(v_x_136_, 1);
v_isSharedCheck_165_ = !lean_is_exclusive(v_x_136_);
if (v_isSharedCheck_165_ == 0)
{
v___x_143_ = v_x_136_;
v_isShared_144_ = v_isSharedCheck_165_;
goto v_resetjp_142_;
}
else
{
lean_inc(v_vs_141_);
lean_inc(v_ks_140_);
lean_dec(v_x_136_);
v___x_143_ = lean_box(0);
v_isShared_144_ = v_isSharedCheck_165_;
goto v_resetjp_142_;
}
v_resetjp_142_:
{
lean_object* v___x_145_; uint8_t v___x_146_; 
v___x_145_ = lean_array_get_size(v_ks_140_);
v___x_146_ = lean_nat_dec_lt(v_x_137_, v___x_145_);
if (v___x_146_ == 0)
{
lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_150_; 
lean_dec(v_x_137_);
v___x_147_ = lean_array_push(v_ks_140_, v_x_138_);
v___x_148_ = lean_array_push(v_vs_141_, v_x_139_);
if (v_isShared_144_ == 0)
{
lean_ctor_set(v___x_143_, 1, v___x_148_);
lean_ctor_set(v___x_143_, 0, v___x_147_);
v___x_150_ = v___x_143_;
goto v_reusejp_149_;
}
else
{
lean_object* v_reuseFailAlloc_151_; 
v_reuseFailAlloc_151_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_151_, 0, v___x_147_);
lean_ctor_set(v_reuseFailAlloc_151_, 1, v___x_148_);
v___x_150_ = v_reuseFailAlloc_151_;
goto v_reusejp_149_;
}
v_reusejp_149_:
{
return v___x_150_;
}
}
else
{
lean_object* v_k_x27_152_; uint8_t v___x_153_; 
v_k_x27_152_ = lean_array_fget_borrowed(v_ks_140_, v_x_137_);
v___x_153_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_138_, v_k_x27_152_);
if (v___x_153_ == 0)
{
lean_object* v___x_155_; 
if (v_isShared_144_ == 0)
{
v___x_155_ = v___x_143_;
goto v_reusejp_154_;
}
else
{
lean_object* v_reuseFailAlloc_159_; 
v_reuseFailAlloc_159_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_159_, 0, v_ks_140_);
lean_ctor_set(v_reuseFailAlloc_159_, 1, v_vs_141_);
v___x_155_ = v_reuseFailAlloc_159_;
goto v_reusejp_154_;
}
v_reusejp_154_:
{
lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_156_ = lean_unsigned_to_nat(1u);
v___x_157_ = lean_nat_add(v_x_137_, v___x_156_);
lean_dec(v_x_137_);
v_x_136_ = v___x_155_;
v_x_137_ = v___x_157_;
goto _start;
}
}
else
{
lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_163_; 
v___x_160_ = lean_array_fset(v_ks_140_, v_x_137_, v_x_138_);
v___x_161_ = lean_array_fset(v_vs_141_, v_x_137_, v_x_139_);
lean_dec(v_x_137_);
if (v_isShared_144_ == 0)
{
lean_ctor_set(v___x_143_, 1, v___x_161_);
lean_ctor_set(v___x_143_, 0, v___x_160_);
v___x_163_ = v___x_143_;
goto v_reusejp_162_;
}
else
{
lean_object* v_reuseFailAlloc_164_; 
v_reuseFailAlloc_164_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_164_, 0, v___x_160_);
lean_ctor_set(v_reuseFailAlloc_164_, 1, v___x_161_);
v___x_163_ = v_reuseFailAlloc_164_;
goto v_reusejp_162_;
}
v_reusejp_162_:
{
return v___x_163_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2_spec__4___redArg(lean_object* v_n_166_, lean_object* v_k_167_, lean_object* v_v_168_){
_start:
{
lean_object* v___x_169_; lean_object* v___x_170_; 
v___x_169_ = lean_unsigned_to_nat(0u);
v___x_170_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2_spec__4_spec__8___redArg(v_n_166_, v___x_169_, v_k_167_, v_v_168_);
return v___x_170_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___redArg___closed__0(void){
_start:
{
size_t v___x_171_; size_t v___x_172_; size_t v___x_173_; 
v___x_171_ = ((size_t)5ULL);
v___x_172_ = ((size_t)1ULL);
v___x_173_ = lean_usize_shift_left(v___x_172_, v___x_171_);
return v___x_173_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___redArg___closed__1(void){
_start:
{
size_t v___x_174_; size_t v___x_175_; size_t v___x_176_; 
v___x_174_ = ((size_t)1ULL);
v___x_175_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___redArg___closed__0);
v___x_176_ = lean_usize_sub(v___x_175_, v___x_174_);
return v___x_176_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_177_; 
v___x_177_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_177_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___redArg(lean_object* v_x_178_, size_t v_x_179_, size_t v_x_180_, lean_object* v_x_181_, lean_object* v_x_182_){
_start:
{
if (lean_obj_tag(v_x_178_) == 0)
{
lean_object* v_es_183_; size_t v___x_184_; size_t v___x_185_; size_t v___x_186_; size_t v___x_187_; lean_object* v_j_188_; lean_object* v___x_189_; uint8_t v___x_190_; 
v_es_183_ = lean_ctor_get(v_x_178_, 0);
v___x_184_ = ((size_t)5ULL);
v___x_185_ = ((size_t)1ULL);
v___x_186_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___redArg___closed__1);
v___x_187_ = lean_usize_land(v_x_179_, v___x_186_);
v_j_188_ = lean_usize_to_nat(v___x_187_);
v___x_189_ = lean_array_get_size(v_es_183_);
v___x_190_ = lean_nat_dec_lt(v_j_188_, v___x_189_);
if (v___x_190_ == 0)
{
lean_dec(v_j_188_);
lean_dec(v_x_182_);
lean_dec_ref(v_x_181_);
return v_x_178_;
}
else
{
lean_object* v___x_192_; uint8_t v_isShared_193_; uint8_t v_isSharedCheck_227_; 
lean_inc_ref(v_es_183_);
v_isSharedCheck_227_ = !lean_is_exclusive(v_x_178_);
if (v_isSharedCheck_227_ == 0)
{
lean_object* v_unused_228_; 
v_unused_228_ = lean_ctor_get(v_x_178_, 0);
lean_dec(v_unused_228_);
v___x_192_ = v_x_178_;
v_isShared_193_ = v_isSharedCheck_227_;
goto v_resetjp_191_;
}
else
{
lean_dec(v_x_178_);
v___x_192_ = lean_box(0);
v_isShared_193_ = v_isSharedCheck_227_;
goto v_resetjp_191_;
}
v_resetjp_191_:
{
lean_object* v_v_194_; lean_object* v___x_195_; lean_object* v_xs_x27_196_; lean_object* v___y_198_; 
v_v_194_ = lean_array_fget(v_es_183_, v_j_188_);
v___x_195_ = lean_box(0);
v_xs_x27_196_ = lean_array_fset(v_es_183_, v_j_188_, v___x_195_);
switch(lean_obj_tag(v_v_194_))
{
case 0:
{
lean_object* v_key_203_; lean_object* v_val_204_; lean_object* v___x_206_; uint8_t v_isShared_207_; uint8_t v_isSharedCheck_214_; 
v_key_203_ = lean_ctor_get(v_v_194_, 0);
v_val_204_ = lean_ctor_get(v_v_194_, 1);
v_isSharedCheck_214_ = !lean_is_exclusive(v_v_194_);
if (v_isSharedCheck_214_ == 0)
{
v___x_206_ = v_v_194_;
v_isShared_207_ = v_isSharedCheck_214_;
goto v_resetjp_205_;
}
else
{
lean_inc(v_val_204_);
lean_inc(v_key_203_);
lean_dec(v_v_194_);
v___x_206_ = lean_box(0);
v_isShared_207_ = v_isSharedCheck_214_;
goto v_resetjp_205_;
}
v_resetjp_205_:
{
uint8_t v___x_208_; 
v___x_208_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_181_, v_key_203_);
if (v___x_208_ == 0)
{
lean_object* v___x_209_; lean_object* v___x_210_; 
lean_del_object(v___x_206_);
v___x_209_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_203_, v_val_204_, v_x_181_, v_x_182_);
v___x_210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_210_, 0, v___x_209_);
v___y_198_ = v___x_210_;
goto v___jp_197_;
}
else
{
lean_object* v___x_212_; 
lean_dec(v_val_204_);
lean_dec(v_key_203_);
if (v_isShared_207_ == 0)
{
lean_ctor_set(v___x_206_, 1, v_x_182_);
lean_ctor_set(v___x_206_, 0, v_x_181_);
v___x_212_ = v___x_206_;
goto v_reusejp_211_;
}
else
{
lean_object* v_reuseFailAlloc_213_; 
v_reuseFailAlloc_213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_213_, 0, v_x_181_);
lean_ctor_set(v_reuseFailAlloc_213_, 1, v_x_182_);
v___x_212_ = v_reuseFailAlloc_213_;
goto v_reusejp_211_;
}
v_reusejp_211_:
{
v___y_198_ = v___x_212_;
goto v___jp_197_;
}
}
}
}
case 1:
{
lean_object* v_node_215_; lean_object* v___x_217_; uint8_t v_isShared_218_; uint8_t v_isSharedCheck_225_; 
v_node_215_ = lean_ctor_get(v_v_194_, 0);
v_isSharedCheck_225_ = !lean_is_exclusive(v_v_194_);
if (v_isSharedCheck_225_ == 0)
{
v___x_217_ = v_v_194_;
v_isShared_218_ = v_isSharedCheck_225_;
goto v_resetjp_216_;
}
else
{
lean_inc(v_node_215_);
lean_dec(v_v_194_);
v___x_217_ = lean_box(0);
v_isShared_218_ = v_isSharedCheck_225_;
goto v_resetjp_216_;
}
v_resetjp_216_:
{
size_t v___x_219_; size_t v___x_220_; lean_object* v___x_221_; lean_object* v___x_223_; 
v___x_219_ = lean_usize_shift_right(v_x_179_, v___x_184_);
v___x_220_ = lean_usize_add(v_x_180_, v___x_185_);
v___x_221_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___redArg(v_node_215_, v___x_219_, v___x_220_, v_x_181_, v_x_182_);
if (v_isShared_218_ == 0)
{
lean_ctor_set(v___x_217_, 0, v___x_221_);
v___x_223_ = v___x_217_;
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
v___y_198_ = v___x_223_;
goto v___jp_197_;
}
}
}
default: 
{
lean_object* v___x_226_; 
v___x_226_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_226_, 0, v_x_181_);
lean_ctor_set(v___x_226_, 1, v_x_182_);
v___y_198_ = v___x_226_;
goto v___jp_197_;
}
}
v___jp_197_:
{
lean_object* v___x_199_; lean_object* v___x_201_; 
v___x_199_ = lean_array_fset(v_xs_x27_196_, v_j_188_, v___y_198_);
lean_dec(v_j_188_);
if (v_isShared_193_ == 0)
{
lean_ctor_set(v___x_192_, 0, v___x_199_);
v___x_201_ = v___x_192_;
goto v_reusejp_200_;
}
else
{
lean_object* v_reuseFailAlloc_202_; 
v_reuseFailAlloc_202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_202_, 0, v___x_199_);
v___x_201_ = v_reuseFailAlloc_202_;
goto v_reusejp_200_;
}
v_reusejp_200_:
{
return v___x_201_;
}
}
}
}
}
else
{
lean_object* v_ks_229_; lean_object* v_vs_230_; lean_object* v___x_232_; uint8_t v_isShared_233_; uint8_t v_isSharedCheck_250_; 
v_ks_229_ = lean_ctor_get(v_x_178_, 0);
v_vs_230_ = lean_ctor_get(v_x_178_, 1);
v_isSharedCheck_250_ = !lean_is_exclusive(v_x_178_);
if (v_isSharedCheck_250_ == 0)
{
v___x_232_ = v_x_178_;
v_isShared_233_ = v_isSharedCheck_250_;
goto v_resetjp_231_;
}
else
{
lean_inc(v_vs_230_);
lean_inc(v_ks_229_);
lean_dec(v_x_178_);
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
v_newNode_236_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2_spec__4___redArg(v___x_235_, v_x_181_, v_x_182_);
v___x_244_ = ((size_t)7ULL);
v___x_245_ = lean_usize_dec_le(v___x_244_, v_x_180_);
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
v___x_242_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___redArg___closed__2);
v___x_243_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2_spec__5___redArg(v_x_180_, v_ks_239_, v_vs_240_, v___x_241_, v___x_242_);
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
lean_object* v_k_258_; lean_object* v_v_259_; uint64_t v___x_260_; size_t v_h_261_; size_t v___x_262_; lean_object* v___x_263_; size_t v___x_264_; size_t v___x_265_; size_t v___x_266_; size_t v_h_267_; lean_object* v___x_268_; lean_object* v___x_269_; 
v_k_258_ = lean_array_fget_borrowed(v_keys_252_, v_i_254_);
v_v_259_ = lean_array_fget_borrowed(v_vals_253_, v_i_254_);
v___x_260_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_k_258_);
v_h_261_ = lean_uint64_to_usize(v___x_260_);
v___x_262_ = ((size_t)5ULL);
v___x_263_ = lean_unsigned_to_nat(1u);
v___x_264_ = ((size_t)1ULL);
v___x_265_ = lean_usize_sub(v_depth_251_, v___x_264_);
v___x_266_ = lean_usize_mul(v___x_262_, v___x_265_);
v_h_267_ = lean_usize_shift_right(v_h_261_, v___x_266_);
v___x_268_ = lean_nat_add(v_i_254_, v___x_263_);
lean_dec(v_i_254_);
lean_inc(v_v_259_);
lean_inc(v_k_258_);
v___x_269_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___redArg(v_entries_255_, v_h_267_, v_depth_251_, v_k_258_, v_v_259_);
v_i_254_ = v___x_268_;
v_entries_255_ = v___x_269_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_depth_271_, lean_object* v_keys_272_, lean_object* v_vals_273_, lean_object* v_i_274_, lean_object* v_entries_275_){
_start:
{
size_t v_depth_boxed_276_; lean_object* v_res_277_; 
v_depth_boxed_276_ = lean_unbox_usize(v_depth_271_);
lean_dec(v_depth_271_);
v_res_277_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2_spec__5___redArg(v_depth_boxed_276_, v_keys_272_, v_vals_273_, v_i_274_, v_entries_275_);
lean_dec_ref(v_vals_273_);
lean_dec_ref(v_keys_272_);
return v_res_277_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___redArg___boxed(lean_object* v_x_278_, lean_object* v_x_279_, lean_object* v_x_280_, lean_object* v_x_281_, lean_object* v_x_282_){
_start:
{
size_t v_x_55673__boxed_283_; size_t v_x_55674__boxed_284_; lean_object* v_res_285_; 
v_x_55673__boxed_283_ = lean_unbox_usize(v_x_279_);
lean_dec(v_x_279_);
v_x_55674__boxed_284_ = lean_unbox_usize(v_x_280_);
lean_dec(v_x_280_);
v_res_285_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___redArg(v_x_278_, v_x_55673__boxed_283_, v_x_55674__boxed_284_, v_x_281_, v_x_282_);
return v_res_285_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1___redArg(lean_object* v_x_286_, lean_object* v_x_287_, lean_object* v_x_288_){
_start:
{
uint64_t v___x_289_; size_t v___x_290_; size_t v___x_291_; lean_object* v___x_292_; 
v___x_289_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_287_);
v___x_290_ = lean_uint64_to_usize(v___x_289_);
v___x_291_ = ((size_t)1ULL);
v___x_292_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___redArg(v_x_286_, v___x_290_, v___x_291_, v_x_287_, v_x_288_);
return v___x_292_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_internalize___lam__0(lean_object* v_e_293_, lean_object* v_a_294_, uint8_t v_ac_295_, lean_object* v_s_296_){
_start:
{
lean_object* v_id_297_; lean_object* v_type_298_; lean_object* v_u_299_; lean_object* v_op_300_; lean_object* v_neutral_x3f_301_; lean_object* v_assocInst_302_; lean_object* v_idempotentInst_x3f_303_; lean_object* v_commInst_x3f_304_; lean_object* v_neutralInst_x3f_305_; lean_object* v_nextId_306_; lean_object* v_vars_307_; lean_object* v_varMap_308_; lean_object* v_denote_309_; lean_object* v_denoteEntries_310_; lean_object* v_queue_311_; lean_object* v_basis_312_; lean_object* v_diseqs_313_; lean_object* v___x_315_; uint8_t v_isShared_316_; uint8_t v_isSharedCheck_323_; 
v_id_297_ = lean_ctor_get(v_s_296_, 0);
v_type_298_ = lean_ctor_get(v_s_296_, 1);
v_u_299_ = lean_ctor_get(v_s_296_, 2);
v_op_300_ = lean_ctor_get(v_s_296_, 3);
v_neutral_x3f_301_ = lean_ctor_get(v_s_296_, 4);
v_assocInst_302_ = lean_ctor_get(v_s_296_, 5);
v_idempotentInst_x3f_303_ = lean_ctor_get(v_s_296_, 6);
v_commInst_x3f_304_ = lean_ctor_get(v_s_296_, 7);
v_neutralInst_x3f_305_ = lean_ctor_get(v_s_296_, 8);
v_nextId_306_ = lean_ctor_get(v_s_296_, 9);
v_vars_307_ = lean_ctor_get(v_s_296_, 10);
v_varMap_308_ = lean_ctor_get(v_s_296_, 11);
v_denote_309_ = lean_ctor_get(v_s_296_, 12);
v_denoteEntries_310_ = lean_ctor_get(v_s_296_, 13);
v_queue_311_ = lean_ctor_get(v_s_296_, 14);
v_basis_312_ = lean_ctor_get(v_s_296_, 15);
v_diseqs_313_ = lean_ctor_get(v_s_296_, 16);
v_isSharedCheck_323_ = !lean_is_exclusive(v_s_296_);
if (v_isSharedCheck_323_ == 0)
{
v___x_315_ = v_s_296_;
v_isShared_316_ = v_isSharedCheck_323_;
goto v_resetjp_314_;
}
else
{
lean_inc(v_diseqs_313_);
lean_inc(v_basis_312_);
lean_inc(v_queue_311_);
lean_inc(v_denoteEntries_310_);
lean_inc(v_denote_309_);
lean_inc(v_varMap_308_);
lean_inc(v_vars_307_);
lean_inc(v_nextId_306_);
lean_inc(v_neutralInst_x3f_305_);
lean_inc(v_commInst_x3f_304_);
lean_inc(v_idempotentInst_x3f_303_);
lean_inc(v_assocInst_302_);
lean_inc(v_neutral_x3f_301_);
lean_inc(v_op_300_);
lean_inc(v_u_299_);
lean_inc(v_type_298_);
lean_inc(v_id_297_);
lean_dec(v_s_296_);
v___x_315_ = lean_box(0);
v_isShared_316_ = v_isSharedCheck_323_;
goto v_resetjp_314_;
}
v_resetjp_314_:
{
lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_321_; 
lean_inc_ref(v_a_294_);
lean_inc_ref(v_e_293_);
v___x_317_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1___redArg(v_denote_309_, v_e_293_, v_a_294_);
v___x_318_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_318_, 0, v_e_293_);
lean_ctor_set(v___x_318_, 1, v_a_294_);
v___x_319_ = l_Lean_PersistentArray_push___redArg(v_denoteEntries_310_, v___x_318_);
if (v_isShared_316_ == 0)
{
lean_ctor_set(v___x_315_, 13, v___x_319_);
lean_ctor_set(v___x_315_, 12, v___x_317_);
v___x_321_ = v___x_315_;
goto v_reusejp_320_;
}
else
{
lean_object* v_reuseFailAlloc_322_; 
v_reuseFailAlloc_322_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_322_, 0, v_id_297_);
lean_ctor_set(v_reuseFailAlloc_322_, 1, v_type_298_);
lean_ctor_set(v_reuseFailAlloc_322_, 2, v_u_299_);
lean_ctor_set(v_reuseFailAlloc_322_, 3, v_op_300_);
lean_ctor_set(v_reuseFailAlloc_322_, 4, v_neutral_x3f_301_);
lean_ctor_set(v_reuseFailAlloc_322_, 5, v_assocInst_302_);
lean_ctor_set(v_reuseFailAlloc_322_, 6, v_idempotentInst_x3f_303_);
lean_ctor_set(v_reuseFailAlloc_322_, 7, v_commInst_x3f_304_);
lean_ctor_set(v_reuseFailAlloc_322_, 8, v_neutralInst_x3f_305_);
lean_ctor_set(v_reuseFailAlloc_322_, 9, v_nextId_306_);
lean_ctor_set(v_reuseFailAlloc_322_, 10, v_vars_307_);
lean_ctor_set(v_reuseFailAlloc_322_, 11, v_varMap_308_);
lean_ctor_set(v_reuseFailAlloc_322_, 12, v___x_317_);
lean_ctor_set(v_reuseFailAlloc_322_, 13, v___x_319_);
lean_ctor_set(v_reuseFailAlloc_322_, 14, v_queue_311_);
lean_ctor_set(v_reuseFailAlloc_322_, 15, v_basis_312_);
lean_ctor_set(v_reuseFailAlloc_322_, 16, v_diseqs_313_);
v___x_321_ = v_reuseFailAlloc_322_;
goto v_reusejp_320_;
}
v_reusejp_320_:
{
lean_ctor_set_uint8(v___x_321_, sizeof(void*)*17, v_ac_295_);
return v___x_321_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_internalize___lam__0___boxed(lean_object* v_e_324_, lean_object* v_a_325_, lean_object* v_ac_326_, lean_object* v_s_327_){
_start:
{
uint8_t v_ac_boxed_328_; lean_object* v_res_329_; 
v_ac_boxed_328_ = lean_unbox(v_ac_326_);
v_res_329_ = l_Lean_Meta_Grind_AC_internalize___lam__0(v_e_324_, v_a_325_, v_ac_boxed_328_, v_s_327_);
return v_res_329_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3_spec__5(lean_object* v_msgData_330_, lean_object* v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_){
_start:
{
lean_object* v___x_336_; lean_object* v_env_337_; lean_object* v___x_338_; lean_object* v_mctx_339_; lean_object* v_lctx_340_; lean_object* v_options_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; 
v___x_336_ = lean_st_ref_get(v___y_334_);
v_env_337_ = lean_ctor_get(v___x_336_, 0);
lean_inc_ref(v_env_337_);
lean_dec(v___x_336_);
v___x_338_ = lean_st_ref_get(v___y_332_);
v_mctx_339_ = lean_ctor_get(v___x_338_, 0);
lean_inc_ref(v_mctx_339_);
lean_dec(v___x_338_);
v_lctx_340_ = lean_ctor_get(v___y_331_, 2);
v_options_341_ = lean_ctor_get(v___y_333_, 2);
lean_inc_ref(v_options_341_);
lean_inc_ref(v_lctx_340_);
v___x_342_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_342_, 0, v_env_337_);
lean_ctor_set(v___x_342_, 1, v_mctx_339_);
lean_ctor_set(v___x_342_, 2, v_lctx_340_);
lean_ctor_set(v___x_342_, 3, v_options_341_);
v___x_343_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_343_, 0, v___x_342_);
lean_ctor_set(v___x_343_, 1, v_msgData_330_);
v___x_344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_344_, 0, v___x_343_);
return v___x_344_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3_spec__5___boxed(lean_object* v_msgData_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_){
_start:
{
lean_object* v_res_351_; 
v_res_351_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3_spec__5(v_msgData_345_, v___y_346_, v___y_347_, v___y_348_, v___y_349_);
lean_dec(v___y_349_);
lean_dec_ref(v___y_348_);
lean_dec(v___y_347_);
lean_dec_ref(v___y_346_);
return v_res_351_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_352_; double v___x_353_; 
v___x_352_ = lean_unsigned_to_nat(0u);
v___x_353_ = lean_float_of_nat(v___x_352_);
return v___x_353_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3___redArg(lean_object* v_cls_357_, lean_object* v_msg_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_){
_start:
{
lean_object* v_ref_364_; lean_object* v___x_365_; lean_object* v_a_366_; lean_object* v___x_368_; uint8_t v_isShared_369_; uint8_t v_isSharedCheck_410_; 
v_ref_364_ = lean_ctor_get(v___y_361_, 5);
v___x_365_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3_spec__5(v_msg_358_, v___y_359_, v___y_360_, v___y_361_, v___y_362_);
v_a_366_ = lean_ctor_get(v___x_365_, 0);
v_isSharedCheck_410_ = !lean_is_exclusive(v___x_365_);
if (v_isSharedCheck_410_ == 0)
{
v___x_368_ = v___x_365_;
v_isShared_369_ = v_isSharedCheck_410_;
goto v_resetjp_367_;
}
else
{
lean_inc(v_a_366_);
lean_dec(v___x_365_);
v___x_368_ = lean_box(0);
v_isShared_369_ = v_isSharedCheck_410_;
goto v_resetjp_367_;
}
v_resetjp_367_:
{
lean_object* v___x_370_; lean_object* v_traceState_371_; lean_object* v_env_372_; lean_object* v_nextMacroScope_373_; lean_object* v_ngen_374_; lean_object* v_auxDeclNGen_375_; lean_object* v_cache_376_; lean_object* v_messages_377_; lean_object* v_infoState_378_; lean_object* v_snapshotTasks_379_; lean_object* v___x_381_; uint8_t v_isShared_382_; uint8_t v_isSharedCheck_409_; 
v___x_370_ = lean_st_ref_take(v___y_362_);
v_traceState_371_ = lean_ctor_get(v___x_370_, 4);
v_env_372_ = lean_ctor_get(v___x_370_, 0);
v_nextMacroScope_373_ = lean_ctor_get(v___x_370_, 1);
v_ngen_374_ = lean_ctor_get(v___x_370_, 2);
v_auxDeclNGen_375_ = lean_ctor_get(v___x_370_, 3);
v_cache_376_ = lean_ctor_get(v___x_370_, 5);
v_messages_377_ = lean_ctor_get(v___x_370_, 6);
v_infoState_378_ = lean_ctor_get(v___x_370_, 7);
v_snapshotTasks_379_ = lean_ctor_get(v___x_370_, 8);
v_isSharedCheck_409_ = !lean_is_exclusive(v___x_370_);
if (v_isSharedCheck_409_ == 0)
{
v___x_381_ = v___x_370_;
v_isShared_382_ = v_isSharedCheck_409_;
goto v_resetjp_380_;
}
else
{
lean_inc(v_snapshotTasks_379_);
lean_inc(v_infoState_378_);
lean_inc(v_messages_377_);
lean_inc(v_cache_376_);
lean_inc(v_traceState_371_);
lean_inc(v_auxDeclNGen_375_);
lean_inc(v_ngen_374_);
lean_inc(v_nextMacroScope_373_);
lean_inc(v_env_372_);
lean_dec(v___x_370_);
v___x_381_ = lean_box(0);
v_isShared_382_ = v_isSharedCheck_409_;
goto v_resetjp_380_;
}
v_resetjp_380_:
{
uint64_t v_tid_383_; lean_object* v_traces_384_; lean_object* v___x_386_; uint8_t v_isShared_387_; uint8_t v_isSharedCheck_408_; 
v_tid_383_ = lean_ctor_get_uint64(v_traceState_371_, sizeof(void*)*1);
v_traces_384_ = lean_ctor_get(v_traceState_371_, 0);
v_isSharedCheck_408_ = !lean_is_exclusive(v_traceState_371_);
if (v_isSharedCheck_408_ == 0)
{
v___x_386_ = v_traceState_371_;
v_isShared_387_ = v_isSharedCheck_408_;
goto v_resetjp_385_;
}
else
{
lean_inc(v_traces_384_);
lean_dec(v_traceState_371_);
v___x_386_ = lean_box(0);
v_isShared_387_ = v_isSharedCheck_408_;
goto v_resetjp_385_;
}
v_resetjp_385_:
{
lean_object* v___x_388_; double v___x_389_; uint8_t v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_398_; 
v___x_388_ = lean_box(0);
v___x_389_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3___redArg___closed__0);
v___x_390_ = 0;
v___x_391_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3___redArg___closed__1));
v___x_392_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_392_, 0, v_cls_357_);
lean_ctor_set(v___x_392_, 1, v___x_388_);
lean_ctor_set(v___x_392_, 2, v___x_391_);
lean_ctor_set_float(v___x_392_, sizeof(void*)*3, v___x_389_);
lean_ctor_set_float(v___x_392_, sizeof(void*)*3 + 8, v___x_389_);
lean_ctor_set_uint8(v___x_392_, sizeof(void*)*3 + 16, v___x_390_);
v___x_393_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3___redArg___closed__2));
v___x_394_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_394_, 0, v___x_392_);
lean_ctor_set(v___x_394_, 1, v_a_366_);
lean_ctor_set(v___x_394_, 2, v___x_393_);
lean_inc(v_ref_364_);
v___x_395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_395_, 0, v_ref_364_);
lean_ctor_set(v___x_395_, 1, v___x_394_);
v___x_396_ = l_Lean_PersistentArray_push___redArg(v_traces_384_, v___x_395_);
if (v_isShared_387_ == 0)
{
lean_ctor_set(v___x_386_, 0, v___x_396_);
v___x_398_ = v___x_386_;
goto v_reusejp_397_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_407_, 0, v___x_396_);
lean_ctor_set_uint64(v_reuseFailAlloc_407_, sizeof(void*)*1, v_tid_383_);
v___x_398_ = v_reuseFailAlloc_407_;
goto v_reusejp_397_;
}
v_reusejp_397_:
{
lean_object* v___x_400_; 
if (v_isShared_382_ == 0)
{
lean_ctor_set(v___x_381_, 4, v___x_398_);
v___x_400_ = v___x_381_;
goto v_reusejp_399_;
}
else
{
lean_object* v_reuseFailAlloc_406_; 
v_reuseFailAlloc_406_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_406_, 0, v_env_372_);
lean_ctor_set(v_reuseFailAlloc_406_, 1, v_nextMacroScope_373_);
lean_ctor_set(v_reuseFailAlloc_406_, 2, v_ngen_374_);
lean_ctor_set(v_reuseFailAlloc_406_, 3, v_auxDeclNGen_375_);
lean_ctor_set(v_reuseFailAlloc_406_, 4, v___x_398_);
lean_ctor_set(v_reuseFailAlloc_406_, 5, v_cache_376_);
lean_ctor_set(v_reuseFailAlloc_406_, 6, v_messages_377_);
lean_ctor_set(v_reuseFailAlloc_406_, 7, v_infoState_378_);
lean_ctor_set(v_reuseFailAlloc_406_, 8, v_snapshotTasks_379_);
v___x_400_ = v_reuseFailAlloc_406_;
goto v_reusejp_399_;
}
v_reusejp_399_:
{
lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_404_; 
v___x_401_ = lean_st_ref_set(v___y_362_, v___x_400_);
v___x_402_ = lean_box(0);
if (v_isShared_369_ == 0)
{
lean_ctor_set(v___x_368_, 0, v___x_402_);
v___x_404_ = v___x_368_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v___x_402_);
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3___redArg___boxed(lean_object* v_cls_411_, lean_object* v_msg_412_, lean_object* v___y_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_){
_start:
{
lean_object* v_res_418_; 
v_res_418_ = l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3___redArg(v_cls_411_, v_msg_412_, v___y_413_, v___y_414_, v___y_415_, v___y_416_);
lean_dec(v___y_416_);
lean_dec_ref(v___y_415_);
lean_dec(v___y_414_);
lean_dec_ref(v___y_413_);
return v_res_418_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_419_, lean_object* v_i_420_, lean_object* v_k_421_){
_start:
{
lean_object* v___x_422_; uint8_t v___x_423_; 
v___x_422_ = lean_array_get_size(v_keys_419_);
v___x_423_ = lean_nat_dec_lt(v_i_420_, v___x_422_);
if (v___x_423_ == 0)
{
lean_dec(v_i_420_);
return v___x_423_;
}
else
{
lean_object* v_k_x27_424_; uint8_t v___x_425_; 
v_k_x27_424_ = lean_array_fget_borrowed(v_keys_419_, v_i_420_);
v___x_425_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_k_421_, v_k_x27_424_);
if (v___x_425_ == 0)
{
lean_object* v___x_426_; lean_object* v___x_427_; 
v___x_426_ = lean_unsigned_to_nat(1u);
v___x_427_ = lean_nat_add(v_i_420_, v___x_426_);
lean_dec(v_i_420_);
v_i_420_ = v___x_427_;
goto _start;
}
else
{
lean_dec(v_i_420_);
return v___x_425_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_429_, lean_object* v_i_430_, lean_object* v_k_431_){
_start:
{
uint8_t v_res_432_; lean_object* v_r_433_; 
v_res_432_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0_spec__1___redArg(v_keys_429_, v_i_430_, v_k_431_);
lean_dec_ref(v_k_431_);
lean_dec_ref(v_keys_429_);
v_r_433_ = lean_box(v_res_432_);
return v_r_433_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0___redArg(lean_object* v_x_434_, size_t v_x_435_, lean_object* v_x_436_){
_start:
{
if (lean_obj_tag(v_x_434_) == 0)
{
lean_object* v_es_437_; lean_object* v___x_438_; size_t v___x_439_; size_t v___x_440_; size_t v___x_441_; lean_object* v_j_442_; lean_object* v___x_443_; 
v_es_437_ = lean_ctor_get(v_x_434_, 0);
v___x_438_ = lean_box(2);
v___x_439_ = ((size_t)5ULL);
v___x_440_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___redArg___closed__1);
v___x_441_ = lean_usize_land(v_x_435_, v___x_440_);
v_j_442_ = lean_usize_to_nat(v___x_441_);
v___x_443_ = lean_array_get_borrowed(v___x_438_, v_es_437_, v_j_442_);
lean_dec(v_j_442_);
switch(lean_obj_tag(v___x_443_))
{
case 0:
{
lean_object* v_key_444_; uint8_t v___x_445_; 
v_key_444_ = lean_ctor_get(v___x_443_, 0);
v___x_445_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_436_, v_key_444_);
return v___x_445_;
}
case 1:
{
lean_object* v_node_446_; size_t v___x_447_; 
v_node_446_ = lean_ctor_get(v___x_443_, 0);
v___x_447_ = lean_usize_shift_right(v_x_435_, v___x_439_);
v_x_434_ = v_node_446_;
v_x_435_ = v___x_447_;
goto _start;
}
default: 
{
uint8_t v___x_449_; 
v___x_449_ = 0;
return v___x_449_;
}
}
}
else
{
lean_object* v_ks_450_; lean_object* v___x_451_; uint8_t v___x_452_; 
v_ks_450_ = lean_ctor_get(v_x_434_, 0);
v___x_451_ = lean_unsigned_to_nat(0u);
v___x_452_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0_spec__1___redArg(v_ks_450_, v___x_451_, v_x_436_);
return v___x_452_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0___redArg___boxed(lean_object* v_x_453_, lean_object* v_x_454_, lean_object* v_x_455_){
_start:
{
size_t v_x_56016__boxed_456_; uint8_t v_res_457_; lean_object* v_r_458_; 
v_x_56016__boxed_456_ = lean_unbox_usize(v_x_454_);
lean_dec(v_x_454_);
v_res_457_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0___redArg(v_x_453_, v_x_56016__boxed_456_, v_x_455_);
lean_dec_ref(v_x_455_);
lean_dec_ref(v_x_453_);
v_r_458_ = lean_box(v_res_457_);
return v_r_458_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0___redArg(lean_object* v_x_459_, lean_object* v_x_460_){
_start:
{
uint64_t v___x_461_; size_t v___x_462_; uint8_t v___x_463_; 
v___x_461_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_460_);
v___x_462_ = lean_uint64_to_usize(v___x_461_);
v___x_463_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0___redArg(v_x_459_, v___x_462_, v_x_460_);
return v___x_463_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0___redArg___boxed(lean_object* v_x_464_, lean_object* v_x_465_){
_start:
{
uint8_t v_res_466_; lean_object* v_r_467_; 
v_res_466_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0___redArg(v_x_464_, v_x_465_);
lean_dec_ref(v_x_465_);
lean_dec_ref(v_x_464_);
v_r_467_ = lean_box(v_res_466_);
return v_r_467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Expr_denoteExpr___at___00Lean_Meta_Grind_AC_internalize_spec__2(lean_object* v_e_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_){
_start:
{
if (lean_obj_tag(v_e_468_) == 0)
{
lean_object* v_x_481_; lean_object* v___x_482_; 
v_x_481_ = lean_ctor_get(v_e_468_, 0);
v___x_482_ = l_Lean_Meta_Grind_AC_ACM_getStruct(v___y_469_, v___y_470_, v___y_471_, v___y_472_, v___y_473_, v___y_474_, v___y_475_, v___y_476_, v___y_477_, v___y_478_, v___y_479_);
if (lean_obj_tag(v___x_482_) == 0)
{
lean_object* v_a_483_; lean_object* v___x_485_; uint8_t v_isShared_486_; uint8_t v_isSharedCheck_499_; 
v_a_483_ = lean_ctor_get(v___x_482_, 0);
v_isSharedCheck_499_ = !lean_is_exclusive(v___x_482_);
if (v_isSharedCheck_499_ == 0)
{
v___x_485_ = v___x_482_;
v_isShared_486_ = v_isSharedCheck_499_;
goto v_resetjp_484_;
}
else
{
lean_inc(v_a_483_);
lean_dec(v___x_482_);
v___x_485_ = lean_box(0);
v_isShared_486_ = v_isSharedCheck_499_;
goto v_resetjp_484_;
}
v_resetjp_484_:
{
lean_object* v_vars_487_; lean_object* v_size_488_; lean_object* v___x_489_; uint8_t v___x_490_; 
v_vars_487_ = lean_ctor_get(v_a_483_, 10);
lean_inc_ref(v_vars_487_);
lean_dec(v_a_483_);
v_size_488_ = lean_ctor_get(v_vars_487_, 2);
v___x_489_ = l_Lean_instInhabitedExpr;
v___x_490_ = lean_nat_dec_lt(v_x_481_, v_size_488_);
if (v___x_490_ == 0)
{
lean_object* v___x_491_; lean_object* v___x_493_; 
lean_dec_ref(v_vars_487_);
v___x_491_ = l_outOfBounds___redArg(v___x_489_);
if (v_isShared_486_ == 0)
{
lean_ctor_set(v___x_485_, 0, v___x_491_);
v___x_493_ = v___x_485_;
goto v_reusejp_492_;
}
else
{
lean_object* v_reuseFailAlloc_494_; 
v_reuseFailAlloc_494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_494_, 0, v___x_491_);
v___x_493_ = v_reuseFailAlloc_494_;
goto v_reusejp_492_;
}
v_reusejp_492_:
{
return v___x_493_;
}
}
else
{
lean_object* v___x_495_; lean_object* v___x_497_; 
v___x_495_ = l_Lean_PersistentArray_get_x21___redArg(v___x_489_, v_vars_487_, v_x_481_);
lean_dec_ref(v_vars_487_);
if (v_isShared_486_ == 0)
{
lean_ctor_set(v___x_485_, 0, v___x_495_);
v___x_497_ = v___x_485_;
goto v_reusejp_496_;
}
else
{
lean_object* v_reuseFailAlloc_498_; 
v_reuseFailAlloc_498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_498_, 0, v___x_495_);
v___x_497_ = v_reuseFailAlloc_498_;
goto v_reusejp_496_;
}
v_reusejp_496_:
{
return v___x_497_;
}
}
}
}
else
{
lean_object* v_a_500_; lean_object* v___x_502_; uint8_t v_isShared_503_; uint8_t v_isSharedCheck_507_; 
v_a_500_ = lean_ctor_get(v___x_482_, 0);
v_isSharedCheck_507_ = !lean_is_exclusive(v___x_482_);
if (v_isSharedCheck_507_ == 0)
{
v___x_502_ = v___x_482_;
v_isShared_503_ = v_isSharedCheck_507_;
goto v_resetjp_501_;
}
else
{
lean_inc(v_a_500_);
lean_dec(v___x_482_);
v___x_502_ = lean_box(0);
v_isShared_503_ = v_isSharedCheck_507_;
goto v_resetjp_501_;
}
v_resetjp_501_:
{
lean_object* v___x_505_; 
if (v_isShared_503_ == 0)
{
v___x_505_ = v___x_502_;
goto v_reusejp_504_;
}
else
{
lean_object* v_reuseFailAlloc_506_; 
v_reuseFailAlloc_506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_506_, 0, v_a_500_);
v___x_505_ = v_reuseFailAlloc_506_;
goto v_reusejp_504_;
}
v_reusejp_504_:
{
return v___x_505_;
}
}
}
}
else
{
lean_object* v_lhs_508_; lean_object* v_rhs_509_; lean_object* v___x_510_; 
v_lhs_508_ = lean_ctor_get(v_e_468_, 0);
v_rhs_509_ = lean_ctor_get(v_e_468_, 1);
v___x_510_ = l_Lean_Meta_Grind_AC_ACM_getStruct(v___y_469_, v___y_470_, v___y_471_, v___y_472_, v___y_473_, v___y_474_, v___y_475_, v___y_476_, v___y_477_, v___y_478_, v___y_479_);
if (lean_obj_tag(v___x_510_) == 0)
{
lean_object* v_a_511_; lean_object* v___x_512_; 
v_a_511_ = lean_ctor_get(v___x_510_, 0);
lean_inc(v_a_511_);
lean_dec_ref(v___x_510_);
v___x_512_ = l_Lean_Grind_AC_Expr_denoteExpr___at___00Lean_Meta_Grind_AC_internalize_spec__2(v_lhs_508_, v___y_469_, v___y_470_, v___y_471_, v___y_472_, v___y_473_, v___y_474_, v___y_475_, v___y_476_, v___y_477_, v___y_478_, v___y_479_);
if (lean_obj_tag(v___x_512_) == 0)
{
lean_object* v_a_513_; lean_object* v___x_514_; 
v_a_513_ = lean_ctor_get(v___x_512_, 0);
lean_inc(v_a_513_);
lean_dec_ref(v___x_512_);
v___x_514_ = l_Lean_Grind_AC_Expr_denoteExpr___at___00Lean_Meta_Grind_AC_internalize_spec__2(v_rhs_509_, v___y_469_, v___y_470_, v___y_471_, v___y_472_, v___y_473_, v___y_474_, v___y_475_, v___y_476_, v___y_477_, v___y_478_, v___y_479_);
if (lean_obj_tag(v___x_514_) == 0)
{
lean_object* v_a_515_; lean_object* v___x_517_; uint8_t v_isShared_518_; uint8_t v_isSharedCheck_524_; 
v_a_515_ = lean_ctor_get(v___x_514_, 0);
v_isSharedCheck_524_ = !lean_is_exclusive(v___x_514_);
if (v_isSharedCheck_524_ == 0)
{
v___x_517_ = v___x_514_;
v_isShared_518_ = v_isSharedCheck_524_;
goto v_resetjp_516_;
}
else
{
lean_inc(v_a_515_);
lean_dec(v___x_514_);
v___x_517_ = lean_box(0);
v_isShared_518_ = v_isSharedCheck_524_;
goto v_resetjp_516_;
}
v_resetjp_516_:
{
lean_object* v_op_519_; lean_object* v___x_520_; lean_object* v___x_522_; 
v_op_519_ = lean_ctor_get(v_a_511_, 3);
lean_inc_ref(v_op_519_);
lean_dec(v_a_511_);
v___x_520_ = l_Lean_mkAppB(v_op_519_, v_a_513_, v_a_515_);
if (v_isShared_518_ == 0)
{
lean_ctor_set(v___x_517_, 0, v___x_520_);
v___x_522_ = v___x_517_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_523_; 
v_reuseFailAlloc_523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_523_, 0, v___x_520_);
v___x_522_ = v_reuseFailAlloc_523_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
return v___x_522_;
}
}
}
else
{
lean_dec(v_a_513_);
lean_dec(v_a_511_);
return v___x_514_;
}
}
else
{
lean_dec(v_a_511_);
return v___x_512_;
}
}
else
{
lean_object* v_a_525_; lean_object* v___x_527_; uint8_t v_isShared_528_; uint8_t v_isSharedCheck_532_; 
v_a_525_ = lean_ctor_get(v___x_510_, 0);
v_isSharedCheck_532_ = !lean_is_exclusive(v___x_510_);
if (v_isSharedCheck_532_ == 0)
{
v___x_527_ = v___x_510_;
v_isShared_528_ = v_isSharedCheck_532_;
goto v_resetjp_526_;
}
else
{
lean_inc(v_a_525_);
lean_dec(v___x_510_);
v___x_527_ = lean_box(0);
v_isShared_528_ = v_isSharedCheck_532_;
goto v_resetjp_526_;
}
v_resetjp_526_:
{
lean_object* v___x_530_; 
if (v_isShared_528_ == 0)
{
v___x_530_ = v___x_527_;
goto v_reusejp_529_;
}
else
{
lean_object* v_reuseFailAlloc_531_; 
v_reuseFailAlloc_531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_531_, 0, v_a_525_);
v___x_530_ = v_reuseFailAlloc_531_;
goto v_reusejp_529_;
}
v_reusejp_529_:
{
return v___x_530_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Expr_denoteExpr___at___00Lean_Meta_Grind_AC_internalize_spec__2___boxed(lean_object* v_e_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_){
_start:
{
lean_object* v_res_546_; 
v_res_546_ = l_Lean_Grind_AC_Expr_denoteExpr___at___00Lean_Meta_Grind_AC_internalize_spec__2(v_e_533_, v___y_534_, v___y_535_, v___y_536_, v___y_537_, v___y_538_, v___y_539_, v___y_540_, v___y_541_, v___y_542_, v___y_543_, v___y_544_);
lean_dec(v___y_544_);
lean_dec_ref(v___y_543_);
lean_dec(v___y_542_);
lean_dec_ref(v___y_541_);
lean_dec(v___y_540_);
lean_dec_ref(v___y_539_);
lean_dec(v___y_538_);
lean_dec_ref(v___y_537_);
lean_dec(v___y_536_);
lean_dec(v___y_535_);
lean_dec(v___y_534_);
lean_dec_ref(v_e_533_);
return v_res_546_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_AC_internalize___closed__6(void){
_start:
{
lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; 
v___x_557_ = ((lean_object*)(l_Lean_Meta_Grind_AC_internalize___closed__3));
v___x_558_ = ((lean_object*)(l_Lean_Meta_Grind_AC_internalize___closed__5));
v___x_559_ = l_Lean_Name_append(v___x_558_, v___x_557_);
return v___x_559_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_AC_internalize___closed__8(void){
_start:
{
lean_object* v___x_561_; lean_object* v___x_562_; 
v___x_561_ = ((lean_object*)(l_Lean_Meta_Grind_AC_internalize___closed__7));
v___x_562_ = l_Lean_stringToMessageData(v___x_561_);
return v___x_562_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_AC_internalize___closed__10(void){
_start:
{
lean_object* v___x_564_; lean_object* v___x_565_; 
v___x_564_ = ((lean_object*)(l_Lean_Meta_Grind_AC_internalize___closed__9));
v___x_565_ = l_Lean_stringToMessageData(v___x_564_);
return v___x_565_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_internalize(lean_object* v_e_566_, lean_object* v_parent_x3f_567_, lean_object* v_a_568_, lean_object* v_a_569_, lean_object* v_a_570_, lean_object* v_a_571_, lean_object* v_a_572_, lean_object* v_a_573_, lean_object* v_a_574_, lean_object* v_a_575_, lean_object* v_a_576_, lean_object* v_a_577_){
_start:
{
lean_object* v___y_580_; lean_object* v___y_581_; lean_object* v___y_582_; lean_object* v___y_583_; lean_object* v___y_584_; lean_object* v___y_585_; lean_object* v___y_586_; lean_object* v___y_587_; lean_object* v___y_588_; lean_object* v___y_589_; lean_object* v___y_590_; lean_object* v___x_594_; 
v___x_594_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_570_);
if (lean_obj_tag(v___x_594_) == 0)
{
lean_object* v_a_595_; lean_object* v___x_597_; uint8_t v_isShared_598_; uint8_t v_isSharedCheck_709_; 
v_a_595_ = lean_ctor_get(v___x_594_, 0);
v_isSharedCheck_709_ = !lean_is_exclusive(v___x_594_);
if (v_isSharedCheck_709_ == 0)
{
v___x_597_ = v___x_594_;
v_isShared_598_ = v_isSharedCheck_709_;
goto v_resetjp_596_;
}
else
{
lean_inc(v_a_595_);
lean_dec(v___x_594_);
v___x_597_ = lean_box(0);
v_isShared_598_ = v_isSharedCheck_709_;
goto v_resetjp_596_;
}
v_resetjp_596_:
{
uint8_t v_ac_599_; uint8_t v___y_601_; 
v_ac_599_ = lean_ctor_get_uint8(v_a_595_, sizeof(void*)*12 + 24);
lean_dec(v_a_595_);
if (v_ac_599_ == 0)
{
lean_object* v___x_704_; lean_object* v___x_705_; 
lean_del_object(v___x_597_);
lean_dec(v_parent_x3f_567_);
lean_dec_ref(v_e_566_);
v___x_704_ = lean_box(0);
v___x_705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_705_, 0, v___x_704_);
return v___x_705_;
}
else
{
uint8_t v___x_706_; 
v___x_706_ = l_Lean_Expr_isApp(v_e_566_);
if (v___x_706_ == 0)
{
v___y_601_ = v___x_706_;
goto v___jp_600_;
}
else
{
lean_object* v___x_707_; uint8_t v___x_708_; 
v___x_707_ = l_Lean_Expr_appFn_x21(v_e_566_);
v___x_708_ = l_Lean_Expr_isApp(v___x_707_);
lean_dec_ref(v___x_707_);
v___y_601_ = v___x_708_;
goto v___jp_600_;
}
}
v___jp_600_:
{
if (v___y_601_ == 0)
{
lean_object* v___x_602_; lean_object* v___x_604_; 
lean_dec(v_parent_x3f_567_);
lean_dec_ref(v_e_566_);
v___x_602_ = lean_box(0);
if (v_isShared_598_ == 0)
{
lean_ctor_set(v___x_597_, 0, v___x_602_);
v___x_604_ = v___x_597_;
goto v_reusejp_603_;
}
else
{
lean_object* v_reuseFailAlloc_605_; 
v_reuseFailAlloc_605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_605_, 0, v___x_602_);
v___x_604_ = v_reuseFailAlloc_605_;
goto v_reusejp_603_;
}
v_reusejp_603_:
{
return v___x_604_;
}
}
else
{
lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; 
lean_del_object(v___x_597_);
v___x_606_ = l_Lean_Expr_appFn_x21(v_e_566_);
v___x_607_ = l_Lean_Expr_appFn_x21(v___x_606_);
lean_dec_ref(v___x_606_);
lean_inc_ref(v___x_607_);
v___x_608_ = l_Lean_Meta_Grind_AC_getOpId_x3f(v___x_607_, v_a_568_, v_a_569_, v_a_570_, v_a_571_, v_a_572_, v_a_573_, v_a_574_, v_a_575_, v_a_576_, v_a_577_);
if (lean_obj_tag(v___x_608_) == 0)
{
lean_object* v_a_609_; lean_object* v___x_611_; uint8_t v_isShared_612_; uint8_t v_isSharedCheck_695_; 
v_a_609_ = lean_ctor_get(v___x_608_, 0);
v_isSharedCheck_695_ = !lean_is_exclusive(v___x_608_);
if (v_isSharedCheck_695_ == 0)
{
v___x_611_ = v___x_608_;
v_isShared_612_ = v_isSharedCheck_695_;
goto v_resetjp_610_;
}
else
{
lean_inc(v_a_609_);
lean_dec(v___x_608_);
v___x_611_ = lean_box(0);
v_isShared_612_ = v_isSharedCheck_695_;
goto v_resetjp_610_;
}
v_resetjp_610_:
{
if (lean_obj_tag(v_a_609_) == 1)
{
lean_object* v_val_613_; lean_object* v___x_614_; lean_object* v_a_615_; lean_object* v___x_617_; uint8_t v_isShared_618_; uint8_t v_isSharedCheck_690_; 
lean_del_object(v___x_611_);
v_val_613_ = lean_ctor_get(v_a_609_, 0);
lean_inc(v_val_613_);
lean_dec_ref(v_a_609_);
v___x_614_ = l___private_Lean_Meta_Tactic_Grind_AC_Internalize_0__Lean_Meta_Grind_AC_isParentSameOpApp___redArg(v_parent_x3f_567_, v___x_607_);
lean_dec_ref(v___x_607_);
v_a_615_ = lean_ctor_get(v___x_614_, 0);
v_isSharedCheck_690_ = !lean_is_exclusive(v___x_614_);
if (v_isSharedCheck_690_ == 0)
{
v___x_617_ = v___x_614_;
v_isShared_618_ = v_isSharedCheck_690_;
goto v_resetjp_616_;
}
else
{
lean_inc(v_a_615_);
lean_dec(v___x_614_);
v___x_617_ = lean_box(0);
v_isShared_618_ = v_isSharedCheck_690_;
goto v_resetjp_616_;
}
v_resetjp_616_:
{
uint8_t v___x_619_; 
v___x_619_ = lean_unbox(v_a_615_);
lean_dec(v_a_615_);
if (v___x_619_ == 0)
{
lean_object* v___x_620_; 
lean_del_object(v___x_617_);
v___x_620_ = l_Lean_Meta_Grind_AC_ACM_getStruct(v_val_613_, v_a_568_, v_a_569_, v_a_570_, v_a_571_, v_a_572_, v_a_573_, v_a_574_, v_a_575_, v_a_576_, v_a_577_);
if (lean_obj_tag(v___x_620_) == 0)
{
lean_object* v_a_621_; lean_object* v___x_623_; uint8_t v_isShared_624_; uint8_t v_isSharedCheck_677_; 
v_a_621_ = lean_ctor_get(v___x_620_, 0);
v_isSharedCheck_677_ = !lean_is_exclusive(v___x_620_);
if (v_isSharedCheck_677_ == 0)
{
v___x_623_ = v___x_620_;
v_isShared_624_ = v_isSharedCheck_677_;
goto v_resetjp_622_;
}
else
{
lean_inc(v_a_621_);
lean_dec(v___x_620_);
v___x_623_ = lean_box(0);
v_isShared_624_ = v_isSharedCheck_677_;
goto v_resetjp_622_;
}
v_resetjp_622_:
{
lean_object* v_denote_625_; uint8_t v___x_626_; 
v_denote_625_ = lean_ctor_get(v_a_621_, 12);
lean_inc_ref(v_denote_625_);
lean_dec(v_a_621_);
v___x_626_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0___redArg(v_denote_625_, v_e_566_);
lean_dec_ref(v_denote_625_);
if (v___x_626_ == 0)
{
lean_object* v___x_627_; 
lean_del_object(v___x_623_);
lean_inc_ref(v_e_566_);
v___x_627_ = l_Lean_Meta_Grind_AC_reify(v_e_566_, v_val_613_, v_a_568_, v_a_569_, v_a_570_, v_a_571_, v_a_572_, v_a_573_, v_a_574_, v_a_575_, v_a_576_, v_a_577_);
if (lean_obj_tag(v___x_627_) == 0)
{
lean_object* v_a_628_; lean_object* v___x_629_; lean_object* v___f_630_; lean_object* v___x_631_; 
v_a_628_ = lean_ctor_get(v___x_627_, 0);
lean_inc_n(v_a_628_, 2);
lean_dec_ref(v___x_627_);
v___x_629_ = lean_box(v_ac_599_);
lean_inc_ref(v_e_566_);
v___f_630_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_AC_internalize___lam__0___boxed), 4, 3);
lean_closure_set(v___f_630_, 0, v_e_566_);
lean_closure_set(v___f_630_, 1, v_a_628_);
lean_closure_set(v___f_630_, 2, v___x_629_);
v___x_631_ = l_Lean_Meta_Grind_AC_modifyStruct___redArg(v___f_630_, v_val_613_, v_a_568_);
if (lean_obj_tag(v___x_631_) == 0)
{
lean_object* v___x_633_; uint8_t v_isShared_634_; uint8_t v_isSharedCheck_663_; 
v_isSharedCheck_663_ = !lean_is_exclusive(v___x_631_);
if (v_isSharedCheck_663_ == 0)
{
lean_object* v_unused_664_; 
v_unused_664_ = lean_ctor_get(v___x_631_, 0);
lean_dec(v_unused_664_);
v___x_633_ = v___x_631_;
v_isShared_634_ = v_isSharedCheck_663_;
goto v_resetjp_632_;
}
else
{
lean_dec(v___x_631_);
v___x_633_ = lean_box(0);
v_isShared_634_ = v_isSharedCheck_663_;
goto v_resetjp_632_;
}
v_resetjp_632_:
{
lean_object* v_options_635_; uint8_t v_hasTrace_636_; 
v_options_635_ = lean_ctor_get(v_a_576_, 2);
v_hasTrace_636_ = lean_ctor_get_uint8(v_options_635_, sizeof(void*)*1);
if (v_hasTrace_636_ == 0)
{
lean_del_object(v___x_633_);
lean_dec(v_a_628_);
v___y_580_ = v_val_613_;
v___y_581_ = v_a_568_;
v___y_582_ = v_a_569_;
v___y_583_ = v_a_570_;
v___y_584_ = v_a_571_;
v___y_585_ = v_a_572_;
v___y_586_ = v_a_573_;
v___y_587_ = v_a_574_;
v___y_588_ = v_a_575_;
v___y_589_ = v_a_576_;
v___y_590_ = v_a_577_;
goto v___jp_579_;
}
else
{
lean_object* v_inheritedTraceOptions_637_; lean_object* v___x_638_; lean_object* v___x_639_; uint8_t v___x_640_; 
v_inheritedTraceOptions_637_ = lean_ctor_get(v_a_576_, 13);
v___x_638_ = ((lean_object*)(l_Lean_Meta_Grind_AC_internalize___closed__3));
v___x_639_ = lean_obj_once(&l_Lean_Meta_Grind_AC_internalize___closed__6, &l_Lean_Meta_Grind_AC_internalize___closed__6_once, _init_l_Lean_Meta_Grind_AC_internalize___closed__6);
v___x_640_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_637_, v_options_635_, v___x_639_);
if (v___x_640_ == 0)
{
lean_del_object(v___x_633_);
lean_dec(v_a_628_);
v___y_580_ = v_val_613_;
v___y_581_ = v_a_568_;
v___y_582_ = v_a_569_;
v___y_583_ = v_a_570_;
v___y_584_ = v_a_571_;
v___y_585_ = v_a_572_;
v___y_586_ = v_a_573_;
v___y_587_ = v_a_574_;
v___y_588_ = v_a_575_;
v___y_589_ = v_a_576_;
v___y_590_ = v_a_577_;
goto v___jp_579_;
}
else
{
lean_object* v___x_641_; 
v___x_641_ = l_Lean_Grind_AC_Expr_denoteExpr___at___00Lean_Meta_Grind_AC_internalize_spec__2(v_a_628_, v_val_613_, v_a_568_, v_a_569_, v_a_570_, v_a_571_, v_a_572_, v_a_573_, v_a_574_, v_a_575_, v_a_576_, v_a_577_);
lean_dec(v_a_628_);
if (lean_obj_tag(v___x_641_) == 0)
{
lean_object* v_a_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_646_; 
v_a_642_ = lean_ctor_get(v___x_641_, 0);
lean_inc(v_a_642_);
lean_dec_ref(v___x_641_);
v___x_643_ = lean_obj_once(&l_Lean_Meta_Grind_AC_internalize___closed__8, &l_Lean_Meta_Grind_AC_internalize___closed__8_once, _init_l_Lean_Meta_Grind_AC_internalize___closed__8);
lean_inc(v_val_613_);
v___x_644_ = l_Nat_reprFast(v_val_613_);
if (v_isShared_634_ == 0)
{
lean_ctor_set_tag(v___x_633_, 3);
lean_ctor_set(v___x_633_, 0, v___x_644_);
v___x_646_ = v___x_633_;
goto v_reusejp_645_;
}
else
{
lean_object* v_reuseFailAlloc_654_; 
v_reuseFailAlloc_654_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_654_, 0, v___x_644_);
v___x_646_ = v_reuseFailAlloc_654_;
goto v_reusejp_645_;
}
v_reusejp_645_:
{
lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; 
v___x_647_ = l_Lean_MessageData_ofFormat(v___x_646_);
v___x_648_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_648_, 0, v___x_643_);
lean_ctor_set(v___x_648_, 1, v___x_647_);
v___x_649_ = lean_obj_once(&l_Lean_Meta_Grind_AC_internalize___closed__10, &l_Lean_Meta_Grind_AC_internalize___closed__10_once, _init_l_Lean_Meta_Grind_AC_internalize___closed__10);
v___x_650_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_650_, 0, v___x_648_);
lean_ctor_set(v___x_650_, 1, v___x_649_);
v___x_651_ = l_Lean_MessageData_ofExpr(v_a_642_);
v___x_652_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_652_, 0, v___x_650_);
lean_ctor_set(v___x_652_, 1, v___x_651_);
v___x_653_ = l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3___redArg(v___x_638_, v___x_652_, v_a_574_, v_a_575_, v_a_576_, v_a_577_);
if (lean_obj_tag(v___x_653_) == 0)
{
lean_dec_ref(v___x_653_);
v___y_580_ = v_val_613_;
v___y_581_ = v_a_568_;
v___y_582_ = v_a_569_;
v___y_583_ = v_a_570_;
v___y_584_ = v_a_571_;
v___y_585_ = v_a_572_;
v___y_586_ = v_a_573_;
v___y_587_ = v_a_574_;
v___y_588_ = v_a_575_;
v___y_589_ = v_a_576_;
v___y_590_ = v_a_577_;
goto v___jp_579_;
}
else
{
lean_dec(v_val_613_);
lean_dec_ref(v_e_566_);
return v___x_653_;
}
}
}
else
{
lean_object* v_a_655_; lean_object* v___x_657_; uint8_t v_isShared_658_; uint8_t v_isSharedCheck_662_; 
lean_del_object(v___x_633_);
lean_dec(v_val_613_);
lean_dec_ref(v_e_566_);
v_a_655_ = lean_ctor_get(v___x_641_, 0);
v_isSharedCheck_662_ = !lean_is_exclusive(v___x_641_);
if (v_isSharedCheck_662_ == 0)
{
v___x_657_ = v___x_641_;
v_isShared_658_ = v_isSharedCheck_662_;
goto v_resetjp_656_;
}
else
{
lean_inc(v_a_655_);
lean_dec(v___x_641_);
v___x_657_ = lean_box(0);
v_isShared_658_ = v_isSharedCheck_662_;
goto v_resetjp_656_;
}
v_resetjp_656_:
{
lean_object* v___x_660_; 
if (v_isShared_658_ == 0)
{
v___x_660_ = v___x_657_;
goto v_reusejp_659_;
}
else
{
lean_object* v_reuseFailAlloc_661_; 
v_reuseFailAlloc_661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_661_, 0, v_a_655_);
v___x_660_ = v_reuseFailAlloc_661_;
goto v_reusejp_659_;
}
v_reusejp_659_:
{
return v___x_660_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_628_);
lean_dec(v_val_613_);
lean_dec_ref(v_e_566_);
return v___x_631_;
}
}
else
{
lean_object* v_a_665_; lean_object* v___x_667_; uint8_t v_isShared_668_; uint8_t v_isSharedCheck_672_; 
lean_dec(v_val_613_);
lean_dec_ref(v_e_566_);
v_a_665_ = lean_ctor_get(v___x_627_, 0);
v_isSharedCheck_672_ = !lean_is_exclusive(v___x_627_);
if (v_isSharedCheck_672_ == 0)
{
v___x_667_ = v___x_627_;
v_isShared_668_ = v_isSharedCheck_672_;
goto v_resetjp_666_;
}
else
{
lean_inc(v_a_665_);
lean_dec(v___x_627_);
v___x_667_ = lean_box(0);
v_isShared_668_ = v_isSharedCheck_672_;
goto v_resetjp_666_;
}
v_resetjp_666_:
{
lean_object* v___x_670_; 
if (v_isShared_668_ == 0)
{
v___x_670_ = v___x_667_;
goto v_reusejp_669_;
}
else
{
lean_object* v_reuseFailAlloc_671_; 
v_reuseFailAlloc_671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_671_, 0, v_a_665_);
v___x_670_ = v_reuseFailAlloc_671_;
goto v_reusejp_669_;
}
v_reusejp_669_:
{
return v___x_670_;
}
}
}
}
else
{
lean_object* v___x_673_; lean_object* v___x_675_; 
lean_dec(v_val_613_);
lean_dec_ref(v_e_566_);
v___x_673_ = lean_box(0);
if (v_isShared_624_ == 0)
{
lean_ctor_set(v___x_623_, 0, v___x_673_);
v___x_675_ = v___x_623_;
goto v_reusejp_674_;
}
else
{
lean_object* v_reuseFailAlloc_676_; 
v_reuseFailAlloc_676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_676_, 0, v___x_673_);
v___x_675_ = v_reuseFailAlloc_676_;
goto v_reusejp_674_;
}
v_reusejp_674_:
{
return v___x_675_;
}
}
}
}
else
{
lean_object* v_a_678_; lean_object* v___x_680_; uint8_t v_isShared_681_; uint8_t v_isSharedCheck_685_; 
lean_dec(v_val_613_);
lean_dec_ref(v_e_566_);
v_a_678_ = lean_ctor_get(v___x_620_, 0);
v_isSharedCheck_685_ = !lean_is_exclusive(v___x_620_);
if (v_isSharedCheck_685_ == 0)
{
v___x_680_ = v___x_620_;
v_isShared_681_ = v_isSharedCheck_685_;
goto v_resetjp_679_;
}
else
{
lean_inc(v_a_678_);
lean_dec(v___x_620_);
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
lean_dec(v_val_613_);
lean_dec_ref(v_e_566_);
v___x_686_ = lean_box(0);
if (v_isShared_618_ == 0)
{
lean_ctor_set(v___x_617_, 0, v___x_686_);
v___x_688_ = v___x_617_;
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
lean_object* v___x_691_; lean_object* v___x_693_; 
lean_dec(v_a_609_);
lean_dec_ref(v___x_607_);
lean_dec(v_parent_x3f_567_);
lean_dec_ref(v_e_566_);
v___x_691_ = lean_box(0);
if (v_isShared_612_ == 0)
{
lean_ctor_set(v___x_611_, 0, v___x_691_);
v___x_693_ = v___x_611_;
goto v_reusejp_692_;
}
else
{
lean_object* v_reuseFailAlloc_694_; 
v_reuseFailAlloc_694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_694_, 0, v___x_691_);
v___x_693_ = v_reuseFailAlloc_694_;
goto v_reusejp_692_;
}
v_reusejp_692_:
{
return v___x_693_;
}
}
}
}
else
{
lean_object* v_a_696_; lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_703_; 
lean_dec_ref(v___x_607_);
lean_dec(v_parent_x3f_567_);
lean_dec_ref(v_e_566_);
v_a_696_ = lean_ctor_get(v___x_608_, 0);
v_isSharedCheck_703_ = !lean_is_exclusive(v___x_608_);
if (v_isSharedCheck_703_ == 0)
{
v___x_698_ = v___x_608_;
v_isShared_699_ = v_isSharedCheck_703_;
goto v_resetjp_697_;
}
else
{
lean_inc(v_a_696_);
lean_dec(v___x_608_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_703_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
lean_object* v___x_701_; 
if (v_isShared_699_ == 0)
{
v___x_701_ = v___x_698_;
goto v_reusejp_700_;
}
else
{
lean_object* v_reuseFailAlloc_702_; 
v_reuseFailAlloc_702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_702_, 0, v_a_696_);
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
}
}
}
else
{
lean_object* v_a_710_; lean_object* v___x_712_; uint8_t v_isShared_713_; uint8_t v_isSharedCheck_717_; 
lean_dec(v_parent_x3f_567_);
lean_dec_ref(v_e_566_);
v_a_710_ = lean_ctor_get(v___x_594_, 0);
v_isSharedCheck_717_ = !lean_is_exclusive(v___x_594_);
if (v_isSharedCheck_717_ == 0)
{
v___x_712_ = v___x_594_;
v_isShared_713_ = v_isSharedCheck_717_;
goto v_resetjp_711_;
}
else
{
lean_inc(v_a_710_);
lean_dec(v___x_594_);
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
v___jp_579_:
{
lean_object* v___x_591_; 
lean_inc_ref(v_e_566_);
v___x_591_ = l_Lean_Meta_Grind_AC_addTermOpId___redArg(v_e_566_, v___y_580_, v___y_581_);
lean_dec(v___y_580_);
if (lean_obj_tag(v___x_591_) == 0)
{
lean_object* v___x_592_; lean_object* v___x_593_; 
lean_dec_ref(v___x_591_);
v___x_592_ = l_Lean_Meta_Grind_AC_acExt;
v___x_593_ = l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(v___x_592_, v_e_566_, v___y_581_, v___y_582_, v___y_583_, v___y_584_, v___y_585_, v___y_586_, v___y_587_, v___y_588_, v___y_589_, v___y_590_);
return v___x_593_;
}
else
{
lean_dec_ref(v_e_566_);
return v___x_591_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_internalize___boxed(lean_object* v_e_718_, lean_object* v_parent_x3f_719_, lean_object* v_a_720_, lean_object* v_a_721_, lean_object* v_a_722_, lean_object* v_a_723_, lean_object* v_a_724_, lean_object* v_a_725_, lean_object* v_a_726_, lean_object* v_a_727_, lean_object* v_a_728_, lean_object* v_a_729_, lean_object* v_a_730_){
_start:
{
lean_object* v_res_731_; 
v_res_731_ = l_Lean_Meta_Grind_AC_internalize(v_e_718_, v_parent_x3f_719_, v_a_720_, v_a_721_, v_a_722_, v_a_723_, v_a_724_, v_a_725_, v_a_726_, v_a_727_, v_a_728_, v_a_729_);
lean_dec(v_a_729_);
lean_dec_ref(v_a_728_);
lean_dec(v_a_727_);
lean_dec_ref(v_a_726_);
lean_dec(v_a_725_);
lean_dec_ref(v_a_724_);
lean_dec(v_a_723_);
lean_dec_ref(v_a_722_);
lean_dec(v_a_721_);
lean_dec(v_a_720_);
return v_res_731_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0(lean_object* v_00_u03b2_732_, lean_object* v_x_733_, lean_object* v_x_734_){
_start:
{
uint8_t v___x_735_; 
v___x_735_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0___redArg(v_x_733_, v_x_734_);
return v___x_735_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0___boxed(lean_object* v_00_u03b2_736_, lean_object* v_x_737_, lean_object* v_x_738_){
_start:
{
uint8_t v_res_739_; lean_object* v_r_740_; 
v_res_739_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0(v_00_u03b2_736_, v_x_737_, v_x_738_);
lean_dec_ref(v_x_738_);
lean_dec_ref(v_x_737_);
v_r_740_ = lean_box(v_res_739_);
return v_r_740_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1(lean_object* v_00_u03b2_741_, lean_object* v_x_742_, lean_object* v_x_743_, lean_object* v_x_744_){
_start:
{
lean_object* v___x_745_; 
v___x_745_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1___redArg(v_x_742_, v_x_743_, v_x_744_);
return v___x_745_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3(lean_object* v_cls_746_, lean_object* v_msg_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_){
_start:
{
lean_object* v___x_760_; 
v___x_760_ = l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3___redArg(v_cls_746_, v_msg_747_, v___y_755_, v___y_756_, v___y_757_, v___y_758_);
return v___x_760_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3___boxed(lean_object* v_cls_761_, lean_object* v_msg_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_){
_start:
{
lean_object* v_res_775_; 
v_res_775_ = l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3(v_cls_761_, v_msg_762_, v___y_763_, v___y_764_, v___y_765_, v___y_766_, v___y_767_, v___y_768_, v___y_769_, v___y_770_, v___y_771_, v___y_772_, v___y_773_);
lean_dec(v___y_773_);
lean_dec_ref(v___y_772_);
lean_dec(v___y_771_);
lean_dec_ref(v___y_770_);
lean_dec(v___y_769_);
lean_dec_ref(v___y_768_);
lean_dec(v___y_767_);
lean_dec_ref(v___y_766_);
lean_dec(v___y_765_);
lean_dec(v___y_764_);
lean_dec(v___y_763_);
return v_res_775_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0(lean_object* v_00_u03b2_776_, lean_object* v_x_777_, size_t v_x_778_, lean_object* v_x_779_){
_start:
{
uint8_t v___x_780_; 
v___x_780_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0___redArg(v_x_777_, v_x_778_, v_x_779_);
return v___x_780_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0___boxed(lean_object* v_00_u03b2_781_, lean_object* v_x_782_, lean_object* v_x_783_, lean_object* v_x_784_){
_start:
{
size_t v_x_56595__boxed_785_; uint8_t v_res_786_; lean_object* v_r_787_; 
v_x_56595__boxed_785_ = lean_unbox_usize(v_x_783_);
lean_dec(v_x_783_);
v_res_786_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0(v_00_u03b2_781_, v_x_782_, v_x_56595__boxed_785_, v_x_784_);
lean_dec_ref(v_x_784_);
lean_dec_ref(v_x_782_);
v_r_787_ = lean_box(v_res_786_);
return v_r_787_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2(lean_object* v_00_u03b2_788_, lean_object* v_x_789_, size_t v_x_790_, size_t v_x_791_, lean_object* v_x_792_, lean_object* v_x_793_){
_start:
{
lean_object* v___x_794_; 
v___x_794_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___redArg(v_x_789_, v_x_790_, v_x_791_, v_x_792_, v_x_793_);
return v___x_794_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___boxed(lean_object* v_00_u03b2_795_, lean_object* v_x_796_, lean_object* v_x_797_, lean_object* v_x_798_, lean_object* v_x_799_, lean_object* v_x_800_){
_start:
{
size_t v_x_56606__boxed_801_; size_t v_x_56607__boxed_802_; lean_object* v_res_803_; 
v_x_56606__boxed_801_ = lean_unbox_usize(v_x_797_);
lean_dec(v_x_797_);
v_x_56607__boxed_802_ = lean_unbox_usize(v_x_798_);
lean_dec(v_x_798_);
v_res_803_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2(v_00_u03b2_795_, v_x_796_, v_x_56606__boxed_801_, v_x_56607__boxed_802_, v_x_799_, v_x_800_);
return v_res_803_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_804_, lean_object* v_keys_805_, lean_object* v_vals_806_, lean_object* v_heq_807_, lean_object* v_i_808_, lean_object* v_k_809_){
_start:
{
uint8_t v___x_810_; 
v___x_810_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0_spec__1___redArg(v_keys_805_, v_i_808_, v_k_809_);
return v___x_810_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_811_, lean_object* v_keys_812_, lean_object* v_vals_813_, lean_object* v_heq_814_, lean_object* v_i_815_, lean_object* v_k_816_){
_start:
{
uint8_t v_res_817_; lean_object* v_r_818_; 
v_res_817_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0_spec__1(v_00_u03b2_811_, v_keys_812_, v_vals_813_, v_heq_814_, v_i_815_, v_k_816_);
lean_dec_ref(v_k_816_);
lean_dec_ref(v_vals_813_);
lean_dec_ref(v_keys_812_);
v_r_818_ = lean_box(v_res_817_);
return v_r_818_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_819_, lean_object* v_n_820_, lean_object* v_k_821_, lean_object* v_v_822_){
_start:
{
lean_object* v___x_823_; 
v___x_823_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2_spec__4___redArg(v_n_820_, v_k_821_, v_v_822_);
return v___x_823_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_824_, size_t v_depth_825_, lean_object* v_keys_826_, lean_object* v_vals_827_, lean_object* v_heq_828_, lean_object* v_i_829_, lean_object* v_entries_830_){
_start:
{
lean_object* v___x_831_; 
v___x_831_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2_spec__5___redArg(v_depth_825_, v_keys_826_, v_vals_827_, v_i_829_, v_entries_830_);
return v___x_831_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_832_, lean_object* v_depth_833_, lean_object* v_keys_834_, lean_object* v_vals_835_, lean_object* v_heq_836_, lean_object* v_i_837_, lean_object* v_entries_838_){
_start:
{
size_t v_depth_boxed_839_; lean_object* v_res_840_; 
v_depth_boxed_839_ = lean_unbox_usize(v_depth_833_);
lean_dec(v_depth_833_);
v_res_840_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2_spec__5(v_00_u03b2_832_, v_depth_boxed_839_, v_keys_834_, v_vals_835_, v_heq_836_, v_i_837_, v_entries_838_);
lean_dec_ref(v_vals_835_);
lean_dec_ref(v_keys_834_);
return v_res_840_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2_spec__4_spec__8(lean_object* v_00_u03b2_841_, lean_object* v_x_842_, lean_object* v_x_843_, lean_object* v_x_844_, lean_object* v_x_845_){
_start:
{
lean_object* v___x_846_; 
v___x_846_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2_spec__4_spec__8___redArg(v_x_842_, v_x_843_, v_x_844_, v_x_845_);
return v___x_846_;
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
