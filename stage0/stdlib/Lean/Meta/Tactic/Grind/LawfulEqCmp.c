// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.LawfulEqCmp
// Imports: public import Lean.Meta.Tactic.Grind.Types import Lean.Meta.Tactic.Grind.Util import Lean.Meta.Tactic.Grind.SynthInstance
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
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_st_ref_get(lean_object*);
uint64_t l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_decLevel_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_synthInstanceMeta_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getBinOp(lean_object*);
lean_object* l_Lean_Meta_Sym_getOrderingEqExpr___redArg(lean_object*);
lean_object* l_Lean_Meta_Grind_isEqv___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* lean_grind_mk_eq_proof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_pushEqCore___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_LawfulEqCmp_0__Lean_Meta_Grind_getLawfulEqCmpThm_x3f_go_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_LawfulEqCmp_0__Lean_Meta_Grind_getLawfulEqCmpThm_x3f_go_x3f___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_LawfulEqCmp_0__Lean_Meta_Grind_getLawfulEqCmpThm_x3f_go_x3f___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_LawfulEqCmp_0__Lean_Meta_Grind_getLawfulEqCmpThm_x3f_go_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "LawfulEqCmp"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_LawfulEqCmp_0__Lean_Meta_Grind_getLawfulEqCmpThm_x3f_go_x3f___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_LawfulEqCmp_0__Lean_Meta_Grind_getLawfulEqCmpThm_x3f_go_x3f___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_LawfulEqCmp_0__Lean_Meta_Grind_getLawfulEqCmpThm_x3f_go_x3f___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_LawfulEqCmp_0__Lean_Meta_Grind_getLawfulEqCmpThm_x3f_go_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_LawfulEqCmp_0__Lean_Meta_Grind_getLawfulEqCmpThm_x3f_go_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_LawfulEqCmp_0__Lean_Meta_Grind_getLawfulEqCmpThm_x3f_go_x3f___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_LawfulEqCmp_0__Lean_Meta_Grind_getLawfulEqCmpThm_x3f_go_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(48, 91, 188, 155, 197, 176, 186, 149)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_LawfulEqCmp_0__Lean_Meta_Grind_getLawfulEqCmpThm_x3f_go_x3f___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_LawfulEqCmp_0__Lean_Meta_Grind_getLawfulEqCmpThm_x3f_go_x3f___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_LawfulEqCmp_0__Lean_Meta_Grind_getLawfulEqCmpThm_x3f_go_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Ordering"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_LawfulEqCmp_0__Lean_Meta_Grind_getLawfulEqCmpThm_x3f_go_x3f___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_LawfulEqCmp_0__Lean_Meta_Grind_getLawfulEqCmpThm_x3f_go_x3f___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_LawfulEqCmp_0__Lean_Meta_Grind_getLawfulEqCmpThm_x3f_go_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_LawfulEqCmp_0__Lean_Meta_Grind_getLawfulEqCmpThm_x3f_go_x3f___closed__3_value),LEAN_SCALAR_PTR_LITERAL(226, 44, 125, 228, 251, 150, 72, 72)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_LawfulEqCmp_0__Lean_Meta_Grind_getLawfulEqCmpThm_x3f_go_x3f___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_LawfulEqCmp_0__Lean_Meta_Grind_getLawfulEqCmpThm_x3f_go_x3f___closed__4_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_LawfulEqCmp_0__Lean_Meta_Grind_getLawfulEqCmpThm_x3f_go_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "eq_of_compare"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_LawfulEqCmp_0__Lean_Meta_Grind_getLawfulEqCmpThm_x3f_go_x3f___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_LawfulEqCmp_0__Lean_Meta_Grind_getLawfulEqCmpThm_x3f_go_x3f___closed__5_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_LawfulEqCmp_0__Lean_Meta_Grind_getLawfulEqCmpThm_x3f_go_x3f___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_LawfulEqCmp_0__Lean_Meta_Grind_getLawfulEqCmpThm_x3f_go_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_LawfulEqCmp_0__Lean_Meta_Grind_getLawfulEqCmpThm_x3f_go_x3f___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_LawfulEqCmp_0__Lean_Meta_Grind_getLawfulEqCmpThm_x3f_go_x3f___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_LawfulEqCmp_0__Lean_Meta_Grind_getLawfulEqCmpThm_x3f_go_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(48, 91, 188, 155, 197, 176, 186, 149)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_LawfulEqCmp_0__Lean_Meta_Grind_getLawfulEqCmpThm_x3f_go_x3f___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_LawfulEqCmp_0__Lean_Meta_Grind_getLawfulEqCmpThm_x3f_go_x3f___closed__6_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_LawfulEqCmp_0__Lean_Meta_Grind_getLawfulEqCmpThm_x3f_go_x3f___closed__5_value),LEAN_SCALAR_PTR_LITERAL(195, 195, 43, 68, 20, 25, 179, 199)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_LawfulEqCmp_0__Lean_Meta_Grind_getLawfulEqCmpThm_x3f_go_x3f___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_LawfulEqCmp_0__Lean_Meta_Grind_getLawfulEqCmpThm_x3f_go_x3f___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_LawfulEqCmp_0__Lean_Meta_Grind_getLawfulEqCmpThm_x3f_go_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_LawfulEqCmp_0__Lean_Meta_Grind_getLawfulEqCmpThm_x3f_go_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__0_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__0_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__0_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__1_spec__2_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__1_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__1_spec__2___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__1_spec__2___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__1_spec__2_spec__5___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__1_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getLawfulEqCmpThm_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getLawfulEqCmpThm_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getLawfulEqCmpThm_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getLawfulEqCmpThm_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__1_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__1_spec__2_spec__5(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__1_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__1_spec__2_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateLawfulEqCmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateLawfulEqCmp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_LawfulEqCmp_0__Lean_Meta_Grind_getLawfulEqCmpThm_x3f_go_x3f(lean_object* v_op_14_, lean_object* v_a_15_, lean_object* v_a_16_, lean_object* v_a_17_, lean_object* v_a_18_){
_start:
{
lean_object* v___x_20_; lean_object* v_env_21_; lean_object* v___x_22_; uint8_t v___x_23_; uint8_t v___x_24_; 
v___x_20_ = lean_st_ref_get(v_a_18_);
v_env_21_ = lean_ctor_get(v___x_20_, 0);
lean_inc_ref(v_env_21_);
lean_dec(v___x_20_);
v___x_22_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_LawfulEqCmp_0__Lean_Meta_Grind_getLawfulEqCmpThm_x3f_go_x3f___closed__2));
v___x_23_ = 1;
v___x_24_ = l_Lean_Environment_contains(v_env_21_, v___x_22_, v___x_23_);
if (v___x_24_ == 0)
{
lean_object* v___x_25_; lean_object* v___x_26_; 
lean_dec_ref(v_op_14_);
v___x_25_ = lean_box(0);
v___x_26_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_26_, 0, v___x_25_);
return v___x_26_;
}
else
{
lean_object* v___x_27_; 
lean_inc(v_a_18_);
lean_inc_ref(v_a_17_);
lean_inc(v_a_16_);
lean_inc_ref(v_a_15_);
lean_inc_ref(v_op_14_);
v___x_27_ = lean_infer_type(v_op_14_, v_a_15_, v_a_16_, v_a_17_, v_a_18_);
if (lean_obj_tag(v___x_27_) == 0)
{
lean_object* v_a_28_; lean_object* v___x_29_; 
v_a_28_ = lean_ctor_get(v___x_27_, 0);
lean_inc(v_a_28_);
lean_dec_ref(v___x_27_);
lean_inc(v_a_18_);
lean_inc_ref(v_a_17_);
lean_inc(v_a_16_);
lean_inc_ref(v_a_15_);
v___x_29_ = lean_whnf(v_a_28_, v_a_15_, v_a_16_, v_a_17_, v_a_18_);
if (lean_obj_tag(v___x_29_) == 0)
{
lean_object* v_a_30_; lean_object* v___x_32_; uint8_t v_isShared_33_; uint8_t v_isSharedCheck_147_; 
v_a_30_ = lean_ctor_get(v___x_29_, 0);
v_isSharedCheck_147_ = !lean_is_exclusive(v___x_29_);
if (v_isSharedCheck_147_ == 0)
{
v___x_32_ = v___x_29_;
v_isShared_33_ = v_isSharedCheck_147_;
goto v_resetjp_31_;
}
else
{
lean_inc(v_a_30_);
lean_dec(v___x_29_);
v___x_32_ = lean_box(0);
v_isShared_33_ = v_isSharedCheck_147_;
goto v_resetjp_31_;
}
v_resetjp_31_:
{
if (lean_obj_tag(v_a_30_) == 7)
{
lean_object* v_binderType_34_; lean_object* v_body_35_; uint8_t v___x_36_; 
v_binderType_34_ = lean_ctor_get(v_a_30_, 1);
lean_inc_ref(v_binderType_34_);
v_body_35_ = lean_ctor_get(v_a_30_, 2);
lean_inc_ref(v_body_35_);
lean_dec_ref(v_a_30_);
v___x_36_ = l_Lean_Expr_hasLooseBVars(v_body_35_);
if (v___x_36_ == 0)
{
lean_object* v___x_37_; 
lean_del_object(v___x_32_);
lean_inc(v_a_18_);
lean_inc_ref(v_a_17_);
lean_inc(v_a_16_);
lean_inc_ref(v_a_15_);
v___x_37_ = lean_whnf(v_body_35_, v_a_15_, v_a_16_, v_a_17_, v_a_18_);
if (lean_obj_tag(v___x_37_) == 0)
{
lean_object* v_a_38_; lean_object* v___x_40_; uint8_t v_isShared_41_; uint8_t v_isSharedCheck_130_; 
v_a_38_ = lean_ctor_get(v___x_37_, 0);
v_isSharedCheck_130_ = !lean_is_exclusive(v___x_37_);
if (v_isSharedCheck_130_ == 0)
{
v___x_40_ = v___x_37_;
v_isShared_41_ = v_isSharedCheck_130_;
goto v_resetjp_39_;
}
else
{
lean_inc(v_a_38_);
lean_dec(v___x_37_);
v___x_40_ = lean_box(0);
v_isShared_41_ = v_isSharedCheck_130_;
goto v_resetjp_39_;
}
v_resetjp_39_:
{
if (lean_obj_tag(v_a_38_) == 7)
{
lean_object* v_binderType_42_; lean_object* v_body_43_; lean_object* v___x_44_; uint8_t v___x_45_; 
v_binderType_42_ = lean_ctor_get(v_a_38_, 1);
lean_inc_ref(v_binderType_42_);
v_body_43_ = lean_ctor_get(v_a_38_, 2);
lean_inc_ref(v_body_43_);
lean_dec_ref(v_a_38_);
v___x_44_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_LawfulEqCmp_0__Lean_Meta_Grind_getLawfulEqCmpThm_x3f_go_x3f___closed__4));
v___x_45_ = l_Lean_Expr_isConstOf(v_body_43_, v___x_44_);
lean_dec_ref(v_body_43_);
if (v___x_45_ == 0)
{
lean_object* v___x_46_; lean_object* v___x_48_; 
lean_dec_ref(v_binderType_42_);
lean_dec_ref(v_binderType_34_);
lean_dec_ref(v_op_14_);
v___x_46_ = lean_box(0);
if (v_isShared_41_ == 0)
{
lean_ctor_set(v___x_40_, 0, v___x_46_);
v___x_48_ = v___x_40_;
goto v_reusejp_47_;
}
else
{
lean_object* v_reuseFailAlloc_49_; 
v_reuseFailAlloc_49_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_49_, 0, v___x_46_);
v___x_48_ = v_reuseFailAlloc_49_;
goto v_reusejp_47_;
}
v_reusejp_47_:
{
return v___x_48_;
}
}
else
{
lean_object* v___x_50_; 
lean_del_object(v___x_40_);
lean_inc_ref(v_binderType_34_);
v___x_50_ = l_Lean_Meta_isExprDefEq(v_binderType_34_, v_binderType_42_, v_a_15_, v_a_16_, v_a_17_, v_a_18_);
if (lean_obj_tag(v___x_50_) == 0)
{
lean_object* v_a_51_; lean_object* v___x_53_; uint8_t v_isShared_54_; uint8_t v_isSharedCheck_117_; 
v_a_51_ = lean_ctor_get(v___x_50_, 0);
v_isSharedCheck_117_ = !lean_is_exclusive(v___x_50_);
if (v_isSharedCheck_117_ == 0)
{
v___x_53_ = v___x_50_;
v_isShared_54_ = v_isSharedCheck_117_;
goto v_resetjp_52_;
}
else
{
lean_inc(v_a_51_);
lean_dec(v___x_50_);
v___x_53_ = lean_box(0);
v_isShared_54_ = v_isSharedCheck_117_;
goto v_resetjp_52_;
}
v_resetjp_52_:
{
uint8_t v___x_55_; 
v___x_55_ = lean_unbox(v_a_51_);
lean_dec(v_a_51_);
if (v___x_55_ == 0)
{
lean_object* v___x_56_; lean_object* v___x_58_; 
lean_dec_ref(v_binderType_34_);
lean_dec_ref(v_op_14_);
v___x_56_ = lean_box(0);
if (v_isShared_54_ == 0)
{
lean_ctor_set(v___x_53_, 0, v___x_56_);
v___x_58_ = v___x_53_;
goto v_reusejp_57_;
}
else
{
lean_object* v_reuseFailAlloc_59_; 
v_reuseFailAlloc_59_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_59_, 0, v___x_56_);
v___x_58_ = v_reuseFailAlloc_59_;
goto v_reusejp_57_;
}
v_reusejp_57_:
{
return v___x_58_;
}
}
else
{
lean_object* v___x_60_; 
lean_del_object(v___x_53_);
lean_inc_ref(v_binderType_34_);
v___x_60_ = l_Lean_Meta_getLevel(v_binderType_34_, v_a_15_, v_a_16_, v_a_17_, v_a_18_);
if (lean_obj_tag(v___x_60_) == 0)
{
lean_object* v_a_61_; lean_object* v___x_62_; 
v_a_61_ = lean_ctor_get(v___x_60_, 0);
lean_inc(v_a_61_);
lean_dec_ref(v___x_60_);
v___x_62_ = l_Lean_Meta_decLevel_x3f(v_a_61_, v_a_15_, v_a_16_, v_a_17_, v_a_18_);
if (lean_obj_tag(v___x_62_) == 0)
{
lean_object* v_a_63_; lean_object* v___x_65_; uint8_t v_isShared_66_; uint8_t v_isSharedCheck_100_; 
v_a_63_ = lean_ctor_get(v___x_62_, 0);
v_isSharedCheck_100_ = !lean_is_exclusive(v___x_62_);
if (v_isSharedCheck_100_ == 0)
{
v___x_65_ = v___x_62_;
v_isShared_66_ = v_isSharedCheck_100_;
goto v_resetjp_64_;
}
else
{
lean_inc(v_a_63_);
lean_dec(v___x_62_);
v___x_65_ = lean_box(0);
v_isShared_66_ = v_isSharedCheck_100_;
goto v_resetjp_64_;
}
v_resetjp_64_:
{
if (lean_obj_tag(v_a_63_) == 1)
{
lean_object* v_val_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; 
lean_del_object(v___x_65_);
v_val_67_ = lean_ctor_get(v_a_63_, 0);
lean_inc(v_val_67_);
lean_dec_ref(v_a_63_);
v___x_68_ = lean_box(0);
v___x_69_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_69_, 0, v_val_67_);
lean_ctor_set(v___x_69_, 1, v___x_68_);
lean_inc_ref(v___x_69_);
v___x_70_ = l_Lean_mkConst(v___x_22_, v___x_69_);
lean_inc_ref(v_op_14_);
lean_inc_ref(v_binderType_34_);
v___x_71_ = l_Lean_mkAppB(v___x_70_, v_binderType_34_, v_op_14_);
v___x_72_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(v___x_71_, v_a_15_, v_a_16_, v_a_17_, v_a_18_);
if (lean_obj_tag(v___x_72_) == 0)
{
lean_object* v_a_73_; lean_object* v___x_75_; uint8_t v_isShared_76_; uint8_t v_isSharedCheck_95_; 
v_a_73_ = lean_ctor_get(v___x_72_, 0);
v_isSharedCheck_95_ = !lean_is_exclusive(v___x_72_);
if (v_isSharedCheck_95_ == 0)
{
v___x_75_ = v___x_72_;
v_isShared_76_ = v_isSharedCheck_95_;
goto v_resetjp_74_;
}
else
{
lean_inc(v_a_73_);
lean_dec(v___x_72_);
v___x_75_ = lean_box(0);
v_isShared_76_ = v_isSharedCheck_95_;
goto v_resetjp_74_;
}
v_resetjp_74_:
{
if (lean_obj_tag(v_a_73_) == 1)
{
lean_object* v_val_77_; lean_object* v___x_79_; uint8_t v_isShared_80_; uint8_t v_isSharedCheck_90_; 
v_val_77_ = lean_ctor_get(v_a_73_, 0);
v_isSharedCheck_90_ = !lean_is_exclusive(v_a_73_);
if (v_isSharedCheck_90_ == 0)
{
v___x_79_ = v_a_73_;
v_isShared_80_ = v_isSharedCheck_90_;
goto v_resetjp_78_;
}
else
{
lean_inc(v_val_77_);
lean_dec(v_a_73_);
v___x_79_ = lean_box(0);
v_isShared_80_ = v_isSharedCheck_90_;
goto v_resetjp_78_;
}
v_resetjp_78_:
{
lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_85_; 
v___x_81_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_LawfulEqCmp_0__Lean_Meta_Grind_getLawfulEqCmpThm_x3f_go_x3f___closed__6));
v___x_82_ = l_Lean_mkConst(v___x_81_, v___x_69_);
v___x_83_ = l_Lean_mkApp3(v___x_82_, v_binderType_34_, v_op_14_, v_val_77_);
if (v_isShared_80_ == 0)
{
lean_ctor_set(v___x_79_, 0, v___x_83_);
v___x_85_ = v___x_79_;
goto v_reusejp_84_;
}
else
{
lean_object* v_reuseFailAlloc_89_; 
v_reuseFailAlloc_89_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_89_, 0, v___x_83_);
v___x_85_ = v_reuseFailAlloc_89_;
goto v_reusejp_84_;
}
v_reusejp_84_:
{
lean_object* v___x_87_; 
if (v_isShared_76_ == 0)
{
lean_ctor_set(v___x_75_, 0, v___x_85_);
v___x_87_ = v___x_75_;
goto v_reusejp_86_;
}
else
{
lean_object* v_reuseFailAlloc_88_; 
v_reuseFailAlloc_88_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_88_, 0, v___x_85_);
v___x_87_ = v_reuseFailAlloc_88_;
goto v_reusejp_86_;
}
v_reusejp_86_:
{
return v___x_87_;
}
}
}
}
else
{
lean_object* v___x_91_; lean_object* v___x_93_; 
lean_dec(v_a_73_);
lean_dec_ref(v___x_69_);
lean_dec_ref(v_binderType_34_);
lean_dec_ref(v_op_14_);
v___x_91_ = lean_box(0);
if (v_isShared_76_ == 0)
{
lean_ctor_set(v___x_75_, 0, v___x_91_);
v___x_93_ = v___x_75_;
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
lean_dec_ref(v___x_69_);
lean_dec_ref(v_binderType_34_);
lean_dec_ref(v_op_14_);
return v___x_72_;
}
}
else
{
lean_object* v___x_96_; lean_object* v___x_98_; 
lean_dec(v_a_63_);
lean_dec_ref(v_binderType_34_);
lean_dec_ref(v_op_14_);
v___x_96_ = lean_box(0);
if (v_isShared_66_ == 0)
{
lean_ctor_set(v___x_65_, 0, v___x_96_);
v___x_98_ = v___x_65_;
goto v_reusejp_97_;
}
else
{
lean_object* v_reuseFailAlloc_99_; 
v_reuseFailAlloc_99_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_99_, 0, v___x_96_);
v___x_98_ = v_reuseFailAlloc_99_;
goto v_reusejp_97_;
}
v_reusejp_97_:
{
return v___x_98_;
}
}
}
}
else
{
lean_object* v_a_101_; lean_object* v___x_103_; uint8_t v_isShared_104_; uint8_t v_isSharedCheck_108_; 
lean_dec_ref(v_binderType_34_);
lean_dec_ref(v_op_14_);
v_a_101_ = lean_ctor_get(v___x_62_, 0);
v_isSharedCheck_108_ = !lean_is_exclusive(v___x_62_);
if (v_isSharedCheck_108_ == 0)
{
v___x_103_ = v___x_62_;
v_isShared_104_ = v_isSharedCheck_108_;
goto v_resetjp_102_;
}
else
{
lean_inc(v_a_101_);
lean_dec(v___x_62_);
v___x_103_ = lean_box(0);
v_isShared_104_ = v_isSharedCheck_108_;
goto v_resetjp_102_;
}
v_resetjp_102_:
{
lean_object* v___x_106_; 
if (v_isShared_104_ == 0)
{
v___x_106_ = v___x_103_;
goto v_reusejp_105_;
}
else
{
lean_object* v_reuseFailAlloc_107_; 
v_reuseFailAlloc_107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_107_, 0, v_a_101_);
v___x_106_ = v_reuseFailAlloc_107_;
goto v_reusejp_105_;
}
v_reusejp_105_:
{
return v___x_106_;
}
}
}
}
else
{
lean_object* v_a_109_; lean_object* v___x_111_; uint8_t v_isShared_112_; uint8_t v_isSharedCheck_116_; 
lean_dec_ref(v_binderType_34_);
lean_dec_ref(v_op_14_);
v_a_109_ = lean_ctor_get(v___x_60_, 0);
v_isSharedCheck_116_ = !lean_is_exclusive(v___x_60_);
if (v_isSharedCheck_116_ == 0)
{
v___x_111_ = v___x_60_;
v_isShared_112_ = v_isSharedCheck_116_;
goto v_resetjp_110_;
}
else
{
lean_inc(v_a_109_);
lean_dec(v___x_60_);
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
}
else
{
lean_object* v_a_118_; lean_object* v___x_120_; uint8_t v_isShared_121_; uint8_t v_isSharedCheck_125_; 
lean_dec_ref(v_binderType_34_);
lean_dec_ref(v_op_14_);
v_a_118_ = lean_ctor_get(v___x_50_, 0);
v_isSharedCheck_125_ = !lean_is_exclusive(v___x_50_);
if (v_isSharedCheck_125_ == 0)
{
v___x_120_ = v___x_50_;
v_isShared_121_ = v_isSharedCheck_125_;
goto v_resetjp_119_;
}
else
{
lean_inc(v_a_118_);
lean_dec(v___x_50_);
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
else
{
lean_object* v___x_126_; lean_object* v___x_128_; 
lean_dec(v_a_38_);
lean_dec_ref(v_binderType_34_);
lean_dec_ref(v_op_14_);
v___x_126_ = lean_box(0);
if (v_isShared_41_ == 0)
{
lean_ctor_set(v___x_40_, 0, v___x_126_);
v___x_128_ = v___x_40_;
goto v_reusejp_127_;
}
else
{
lean_object* v_reuseFailAlloc_129_; 
v_reuseFailAlloc_129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_129_, 0, v___x_126_);
v___x_128_ = v_reuseFailAlloc_129_;
goto v_reusejp_127_;
}
v_reusejp_127_:
{
return v___x_128_;
}
}
}
}
else
{
lean_object* v_a_131_; lean_object* v___x_133_; uint8_t v_isShared_134_; uint8_t v_isSharedCheck_138_; 
lean_dec_ref(v_binderType_34_);
lean_dec_ref(v_op_14_);
v_a_131_ = lean_ctor_get(v___x_37_, 0);
v_isSharedCheck_138_ = !lean_is_exclusive(v___x_37_);
if (v_isSharedCheck_138_ == 0)
{
v___x_133_ = v___x_37_;
v_isShared_134_ = v_isSharedCheck_138_;
goto v_resetjp_132_;
}
else
{
lean_inc(v_a_131_);
lean_dec(v___x_37_);
v___x_133_ = lean_box(0);
v_isShared_134_ = v_isSharedCheck_138_;
goto v_resetjp_132_;
}
v_resetjp_132_:
{
lean_object* v___x_136_; 
if (v_isShared_134_ == 0)
{
v___x_136_ = v___x_133_;
goto v_reusejp_135_;
}
else
{
lean_object* v_reuseFailAlloc_137_; 
v_reuseFailAlloc_137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_137_, 0, v_a_131_);
v___x_136_ = v_reuseFailAlloc_137_;
goto v_reusejp_135_;
}
v_reusejp_135_:
{
return v___x_136_;
}
}
}
}
else
{
lean_object* v___x_139_; lean_object* v___x_141_; 
lean_dec_ref(v_body_35_);
lean_dec_ref(v_binderType_34_);
lean_dec_ref(v_op_14_);
v___x_139_ = lean_box(0);
if (v_isShared_33_ == 0)
{
lean_ctor_set(v___x_32_, 0, v___x_139_);
v___x_141_ = v___x_32_;
goto v_reusejp_140_;
}
else
{
lean_object* v_reuseFailAlloc_142_; 
v_reuseFailAlloc_142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_142_, 0, v___x_139_);
v___x_141_ = v_reuseFailAlloc_142_;
goto v_reusejp_140_;
}
v_reusejp_140_:
{
return v___x_141_;
}
}
}
else
{
lean_object* v___x_143_; lean_object* v___x_145_; 
lean_dec(v_a_30_);
lean_dec_ref(v_op_14_);
v___x_143_ = lean_box(0);
if (v_isShared_33_ == 0)
{
lean_ctor_set(v___x_32_, 0, v___x_143_);
v___x_145_ = v___x_32_;
goto v_reusejp_144_;
}
else
{
lean_object* v_reuseFailAlloc_146_; 
v_reuseFailAlloc_146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_146_, 0, v___x_143_);
v___x_145_ = v_reuseFailAlloc_146_;
goto v_reusejp_144_;
}
v_reusejp_144_:
{
return v___x_145_;
}
}
}
}
else
{
lean_object* v_a_148_; lean_object* v___x_150_; uint8_t v_isShared_151_; uint8_t v_isSharedCheck_155_; 
lean_dec_ref(v_op_14_);
v_a_148_ = lean_ctor_get(v___x_29_, 0);
v_isSharedCheck_155_ = !lean_is_exclusive(v___x_29_);
if (v_isSharedCheck_155_ == 0)
{
v___x_150_ = v___x_29_;
v_isShared_151_ = v_isSharedCheck_155_;
goto v_resetjp_149_;
}
else
{
lean_inc(v_a_148_);
lean_dec(v___x_29_);
v___x_150_ = lean_box(0);
v_isShared_151_ = v_isSharedCheck_155_;
goto v_resetjp_149_;
}
v_resetjp_149_:
{
lean_object* v___x_153_; 
if (v_isShared_151_ == 0)
{
v___x_153_ = v___x_150_;
goto v_reusejp_152_;
}
else
{
lean_object* v_reuseFailAlloc_154_; 
v_reuseFailAlloc_154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_154_, 0, v_a_148_);
v___x_153_ = v_reuseFailAlloc_154_;
goto v_reusejp_152_;
}
v_reusejp_152_:
{
return v___x_153_;
}
}
}
}
else
{
lean_object* v_a_156_; lean_object* v___x_158_; uint8_t v_isShared_159_; uint8_t v_isSharedCheck_163_; 
lean_dec_ref(v_op_14_);
v_a_156_ = lean_ctor_get(v___x_27_, 0);
v_isSharedCheck_163_ = !lean_is_exclusive(v___x_27_);
if (v_isSharedCheck_163_ == 0)
{
v___x_158_ = v___x_27_;
v_isShared_159_ = v_isSharedCheck_163_;
goto v_resetjp_157_;
}
else
{
lean_inc(v_a_156_);
lean_dec(v___x_27_);
v___x_158_ = lean_box(0);
v_isShared_159_ = v_isSharedCheck_163_;
goto v_resetjp_157_;
}
v_resetjp_157_:
{
lean_object* v___x_161_; 
if (v_isShared_159_ == 0)
{
v___x_161_ = v___x_158_;
goto v_reusejp_160_;
}
else
{
lean_object* v_reuseFailAlloc_162_; 
v_reuseFailAlloc_162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_162_, 0, v_a_156_);
v___x_161_ = v_reuseFailAlloc_162_;
goto v_reusejp_160_;
}
v_reusejp_160_:
{
return v___x_161_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_LawfulEqCmp_0__Lean_Meta_Grind_getLawfulEqCmpThm_x3f_go_x3f___boxed(lean_object* v_op_164_, lean_object* v_a_165_, lean_object* v_a_166_, lean_object* v_a_167_, lean_object* v_a_168_, lean_object* v_a_169_){
_start:
{
lean_object* v_res_170_; 
v_res_170_ = l___private_Lean_Meta_Tactic_Grind_LawfulEqCmp_0__Lean_Meta_Grind_getLawfulEqCmpThm_x3f_go_x3f(v_op_164_, v_a_165_, v_a_166_, v_a_167_, v_a_168_);
lean_dec(v_a_168_);
lean_dec_ref(v_a_167_);
lean_dec(v_a_166_);
lean_dec_ref(v_a_165_);
return v_res_170_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_171_, lean_object* v_vals_172_, lean_object* v_i_173_, lean_object* v_k_174_){
_start:
{
lean_object* v___x_175_; uint8_t v___x_176_; 
v___x_175_ = lean_array_get_size(v_keys_171_);
v___x_176_ = lean_nat_dec_lt(v_i_173_, v___x_175_);
if (v___x_176_ == 0)
{
lean_object* v___x_177_; 
lean_dec(v_i_173_);
v___x_177_ = lean_box(0);
return v___x_177_;
}
else
{
lean_object* v_k_x27_178_; uint8_t v___x_179_; 
v_k_x27_178_ = lean_array_fget_borrowed(v_keys_171_, v_i_173_);
v___x_179_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_k_174_, v_k_x27_178_);
if (v___x_179_ == 0)
{
lean_object* v___x_180_; lean_object* v___x_181_; 
v___x_180_ = lean_unsigned_to_nat(1u);
v___x_181_ = lean_nat_add(v_i_173_, v___x_180_);
lean_dec(v_i_173_);
v_i_173_ = v___x_181_;
goto _start;
}
else
{
lean_object* v___x_183_; lean_object* v___x_184_; 
v___x_183_ = lean_array_fget_borrowed(v_vals_172_, v_i_173_);
lean_dec(v_i_173_);
lean_inc(v___x_183_);
v___x_184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_184_, 0, v___x_183_);
return v___x_184_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_185_, lean_object* v_vals_186_, lean_object* v_i_187_, lean_object* v_k_188_){
_start:
{
lean_object* v_res_189_; 
v_res_189_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__0_spec__0_spec__1___redArg(v_keys_185_, v_vals_186_, v_i_187_, v_k_188_);
lean_dec_ref(v_k_188_);
lean_dec_ref(v_vals_186_);
lean_dec_ref(v_keys_185_);
return v_res_189_;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__0_spec__0___redArg___closed__0(void){
_start:
{
size_t v___x_190_; size_t v___x_191_; size_t v___x_192_; 
v___x_190_ = ((size_t)5ULL);
v___x_191_ = ((size_t)1ULL);
v___x_192_ = lean_usize_shift_left(v___x_191_, v___x_190_);
return v___x_192_;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__0_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_193_; size_t v___x_194_; size_t v___x_195_; 
v___x_193_ = ((size_t)1ULL);
v___x_194_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__0_spec__0___redArg___closed__0);
v___x_195_ = lean_usize_sub(v___x_194_, v___x_193_);
return v___x_195_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__0_spec__0___redArg(lean_object* v_x_196_, size_t v_x_197_, lean_object* v_x_198_){
_start:
{
if (lean_obj_tag(v_x_196_) == 0)
{
lean_object* v_es_199_; lean_object* v___x_200_; size_t v___x_201_; size_t v___x_202_; size_t v___x_203_; lean_object* v_j_204_; lean_object* v___x_205_; 
v_es_199_ = lean_ctor_get(v_x_196_, 0);
v___x_200_ = lean_box(2);
v___x_201_ = ((size_t)5ULL);
v___x_202_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__0_spec__0___redArg___closed__1);
v___x_203_ = lean_usize_land(v_x_197_, v___x_202_);
v_j_204_ = lean_usize_to_nat(v___x_203_);
v___x_205_ = lean_array_get_borrowed(v___x_200_, v_es_199_, v_j_204_);
lean_dec(v_j_204_);
switch(lean_obj_tag(v___x_205_))
{
case 0:
{
lean_object* v_key_206_; lean_object* v_val_207_; uint8_t v___x_208_; 
v_key_206_ = lean_ctor_get(v___x_205_, 0);
v_val_207_ = lean_ctor_get(v___x_205_, 1);
v___x_208_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_198_, v_key_206_);
if (v___x_208_ == 0)
{
lean_object* v___x_209_; 
v___x_209_ = lean_box(0);
return v___x_209_;
}
else
{
lean_object* v___x_210_; 
lean_inc(v_val_207_);
v___x_210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_210_, 0, v_val_207_);
return v___x_210_;
}
}
case 1:
{
lean_object* v_node_211_; size_t v___x_212_; 
v_node_211_ = lean_ctor_get(v___x_205_, 0);
v___x_212_ = lean_usize_shift_right(v_x_197_, v___x_201_);
v_x_196_ = v_node_211_;
v_x_197_ = v___x_212_;
goto _start;
}
default: 
{
lean_object* v___x_214_; 
v___x_214_ = lean_box(0);
return v___x_214_;
}
}
}
else
{
lean_object* v_ks_215_; lean_object* v_vs_216_; lean_object* v___x_217_; lean_object* v___x_218_; 
v_ks_215_ = lean_ctor_get(v_x_196_, 0);
v_vs_216_ = lean_ctor_get(v_x_196_, 1);
v___x_217_ = lean_unsigned_to_nat(0u);
v___x_218_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__0_spec__0_spec__1___redArg(v_ks_215_, v_vs_216_, v___x_217_, v_x_198_);
return v___x_218_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_219_, lean_object* v_x_220_, lean_object* v_x_221_){
_start:
{
size_t v_x_4394__boxed_222_; lean_object* v_res_223_; 
v_x_4394__boxed_222_ = lean_unbox_usize(v_x_220_);
lean_dec(v_x_220_);
v_res_223_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__0_spec__0___redArg(v_x_219_, v_x_4394__boxed_222_, v_x_221_);
lean_dec_ref(v_x_221_);
lean_dec_ref(v_x_219_);
return v_res_223_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__0___redArg(lean_object* v_x_224_, lean_object* v_x_225_){
_start:
{
uint64_t v___x_226_; size_t v___x_227_; lean_object* v___x_228_; 
v___x_226_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_225_);
v___x_227_ = lean_uint64_to_usize(v___x_226_);
v___x_228_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__0_spec__0___redArg(v_x_224_, v___x_227_, v_x_225_);
return v___x_228_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__0___redArg___boxed(lean_object* v_x_229_, lean_object* v_x_230_){
_start:
{
lean_object* v_res_231_; 
v_res_231_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__0___redArg(v_x_229_, v_x_230_);
lean_dec_ref(v_x_230_);
lean_dec_ref(v_x_229_);
return v_res_231_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__1_spec__2_spec__4_spec__5___redArg(lean_object* v_x_232_, lean_object* v_x_233_, lean_object* v_x_234_, lean_object* v_x_235_){
_start:
{
lean_object* v_ks_236_; lean_object* v_vs_237_; lean_object* v___x_239_; uint8_t v_isShared_240_; uint8_t v_isSharedCheck_261_; 
v_ks_236_ = lean_ctor_get(v_x_232_, 0);
v_vs_237_ = lean_ctor_get(v_x_232_, 1);
v_isSharedCheck_261_ = !lean_is_exclusive(v_x_232_);
if (v_isSharedCheck_261_ == 0)
{
v___x_239_ = v_x_232_;
v_isShared_240_ = v_isSharedCheck_261_;
goto v_resetjp_238_;
}
else
{
lean_inc(v_vs_237_);
lean_inc(v_ks_236_);
lean_dec(v_x_232_);
v___x_239_ = lean_box(0);
v_isShared_240_ = v_isSharedCheck_261_;
goto v_resetjp_238_;
}
v_resetjp_238_:
{
lean_object* v___x_241_; uint8_t v___x_242_; 
v___x_241_ = lean_array_get_size(v_ks_236_);
v___x_242_ = lean_nat_dec_lt(v_x_233_, v___x_241_);
if (v___x_242_ == 0)
{
lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_246_; 
lean_dec(v_x_233_);
v___x_243_ = lean_array_push(v_ks_236_, v_x_234_);
v___x_244_ = lean_array_push(v_vs_237_, v_x_235_);
if (v_isShared_240_ == 0)
{
lean_ctor_set(v___x_239_, 1, v___x_244_);
lean_ctor_set(v___x_239_, 0, v___x_243_);
v___x_246_ = v___x_239_;
goto v_reusejp_245_;
}
else
{
lean_object* v_reuseFailAlloc_247_; 
v_reuseFailAlloc_247_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_247_, 0, v___x_243_);
lean_ctor_set(v_reuseFailAlloc_247_, 1, v___x_244_);
v___x_246_ = v_reuseFailAlloc_247_;
goto v_reusejp_245_;
}
v_reusejp_245_:
{
return v___x_246_;
}
}
else
{
lean_object* v_k_x27_248_; uint8_t v___x_249_; 
v_k_x27_248_ = lean_array_fget_borrowed(v_ks_236_, v_x_233_);
v___x_249_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_234_, v_k_x27_248_);
if (v___x_249_ == 0)
{
lean_object* v___x_251_; 
if (v_isShared_240_ == 0)
{
v___x_251_ = v___x_239_;
goto v_reusejp_250_;
}
else
{
lean_object* v_reuseFailAlloc_255_; 
v_reuseFailAlloc_255_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_255_, 0, v_ks_236_);
lean_ctor_set(v_reuseFailAlloc_255_, 1, v_vs_237_);
v___x_251_ = v_reuseFailAlloc_255_;
goto v_reusejp_250_;
}
v_reusejp_250_:
{
lean_object* v___x_252_; lean_object* v___x_253_; 
v___x_252_ = lean_unsigned_to_nat(1u);
v___x_253_ = lean_nat_add(v_x_233_, v___x_252_);
lean_dec(v_x_233_);
v_x_232_ = v___x_251_;
v_x_233_ = v___x_253_;
goto _start;
}
}
else
{
lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_259_; 
v___x_256_ = lean_array_fset(v_ks_236_, v_x_233_, v_x_234_);
v___x_257_ = lean_array_fset(v_vs_237_, v_x_233_, v_x_235_);
lean_dec(v_x_233_);
if (v_isShared_240_ == 0)
{
lean_ctor_set(v___x_239_, 1, v___x_257_);
lean_ctor_set(v___x_239_, 0, v___x_256_);
v___x_259_ = v___x_239_;
goto v_reusejp_258_;
}
else
{
lean_object* v_reuseFailAlloc_260_; 
v_reuseFailAlloc_260_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_260_, 0, v___x_256_);
lean_ctor_set(v_reuseFailAlloc_260_, 1, v___x_257_);
v___x_259_ = v_reuseFailAlloc_260_;
goto v_reusejp_258_;
}
v_reusejp_258_:
{
return v___x_259_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__1_spec__2_spec__4___redArg(lean_object* v_n_262_, lean_object* v_k_263_, lean_object* v_v_264_){
_start:
{
lean_object* v___x_265_; lean_object* v___x_266_; 
v___x_265_ = lean_unsigned_to_nat(0u);
v___x_266_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__1_spec__2_spec__4_spec__5___redArg(v_n_262_, v___x_265_, v_k_263_, v_v_264_);
return v___x_266_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_267_; 
v___x_267_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_267_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__1_spec__2___redArg(lean_object* v_x_268_, size_t v_x_269_, size_t v_x_270_, lean_object* v_x_271_, lean_object* v_x_272_){
_start:
{
if (lean_obj_tag(v_x_268_) == 0)
{
lean_object* v_es_273_; size_t v___x_274_; size_t v___x_275_; size_t v___x_276_; size_t v___x_277_; lean_object* v_j_278_; lean_object* v___x_279_; uint8_t v___x_280_; 
v_es_273_ = lean_ctor_get(v_x_268_, 0);
v___x_274_ = ((size_t)5ULL);
v___x_275_ = ((size_t)1ULL);
v___x_276_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__0_spec__0___redArg___closed__1);
v___x_277_ = lean_usize_land(v_x_269_, v___x_276_);
v_j_278_ = lean_usize_to_nat(v___x_277_);
v___x_279_ = lean_array_get_size(v_es_273_);
v___x_280_ = lean_nat_dec_lt(v_j_278_, v___x_279_);
if (v___x_280_ == 0)
{
lean_dec(v_j_278_);
lean_dec(v_x_272_);
lean_dec_ref(v_x_271_);
return v_x_268_;
}
else
{
lean_object* v___x_282_; uint8_t v_isShared_283_; uint8_t v_isSharedCheck_317_; 
lean_inc_ref(v_es_273_);
v_isSharedCheck_317_ = !lean_is_exclusive(v_x_268_);
if (v_isSharedCheck_317_ == 0)
{
lean_object* v_unused_318_; 
v_unused_318_ = lean_ctor_get(v_x_268_, 0);
lean_dec(v_unused_318_);
v___x_282_ = v_x_268_;
v_isShared_283_ = v_isSharedCheck_317_;
goto v_resetjp_281_;
}
else
{
lean_dec(v_x_268_);
v___x_282_ = lean_box(0);
v_isShared_283_ = v_isSharedCheck_317_;
goto v_resetjp_281_;
}
v_resetjp_281_:
{
lean_object* v_v_284_; lean_object* v___x_285_; lean_object* v_xs_x27_286_; lean_object* v___y_288_; 
v_v_284_ = lean_array_fget(v_es_273_, v_j_278_);
v___x_285_ = lean_box(0);
v_xs_x27_286_ = lean_array_fset(v_es_273_, v_j_278_, v___x_285_);
switch(lean_obj_tag(v_v_284_))
{
case 0:
{
lean_object* v_key_293_; lean_object* v_val_294_; lean_object* v___x_296_; uint8_t v_isShared_297_; uint8_t v_isSharedCheck_304_; 
v_key_293_ = lean_ctor_get(v_v_284_, 0);
v_val_294_ = lean_ctor_get(v_v_284_, 1);
v_isSharedCheck_304_ = !lean_is_exclusive(v_v_284_);
if (v_isSharedCheck_304_ == 0)
{
v___x_296_ = v_v_284_;
v_isShared_297_ = v_isSharedCheck_304_;
goto v_resetjp_295_;
}
else
{
lean_inc(v_val_294_);
lean_inc(v_key_293_);
lean_dec(v_v_284_);
v___x_296_ = lean_box(0);
v_isShared_297_ = v_isSharedCheck_304_;
goto v_resetjp_295_;
}
v_resetjp_295_:
{
uint8_t v___x_298_; 
v___x_298_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_271_, v_key_293_);
if (v___x_298_ == 0)
{
lean_object* v___x_299_; lean_object* v___x_300_; 
lean_del_object(v___x_296_);
v___x_299_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_293_, v_val_294_, v_x_271_, v_x_272_);
v___x_300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_300_, 0, v___x_299_);
v___y_288_ = v___x_300_;
goto v___jp_287_;
}
else
{
lean_object* v___x_302_; 
lean_dec(v_val_294_);
lean_dec(v_key_293_);
if (v_isShared_297_ == 0)
{
lean_ctor_set(v___x_296_, 1, v_x_272_);
lean_ctor_set(v___x_296_, 0, v_x_271_);
v___x_302_ = v___x_296_;
goto v_reusejp_301_;
}
else
{
lean_object* v_reuseFailAlloc_303_; 
v_reuseFailAlloc_303_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_303_, 0, v_x_271_);
lean_ctor_set(v_reuseFailAlloc_303_, 1, v_x_272_);
v___x_302_ = v_reuseFailAlloc_303_;
goto v_reusejp_301_;
}
v_reusejp_301_:
{
v___y_288_ = v___x_302_;
goto v___jp_287_;
}
}
}
}
case 1:
{
lean_object* v_node_305_; lean_object* v___x_307_; uint8_t v_isShared_308_; uint8_t v_isSharedCheck_315_; 
v_node_305_ = lean_ctor_get(v_v_284_, 0);
v_isSharedCheck_315_ = !lean_is_exclusive(v_v_284_);
if (v_isSharedCheck_315_ == 0)
{
v___x_307_ = v_v_284_;
v_isShared_308_ = v_isSharedCheck_315_;
goto v_resetjp_306_;
}
else
{
lean_inc(v_node_305_);
lean_dec(v_v_284_);
v___x_307_ = lean_box(0);
v_isShared_308_ = v_isSharedCheck_315_;
goto v_resetjp_306_;
}
v_resetjp_306_:
{
size_t v___x_309_; size_t v___x_310_; lean_object* v___x_311_; lean_object* v___x_313_; 
v___x_309_ = lean_usize_shift_right(v_x_269_, v___x_274_);
v___x_310_ = lean_usize_add(v_x_270_, v___x_275_);
v___x_311_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__1_spec__2___redArg(v_node_305_, v___x_309_, v___x_310_, v_x_271_, v_x_272_);
if (v_isShared_308_ == 0)
{
lean_ctor_set(v___x_307_, 0, v___x_311_);
v___x_313_ = v___x_307_;
goto v_reusejp_312_;
}
else
{
lean_object* v_reuseFailAlloc_314_; 
v_reuseFailAlloc_314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_314_, 0, v___x_311_);
v___x_313_ = v_reuseFailAlloc_314_;
goto v_reusejp_312_;
}
v_reusejp_312_:
{
v___y_288_ = v___x_313_;
goto v___jp_287_;
}
}
}
default: 
{
lean_object* v___x_316_; 
v___x_316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_316_, 0, v_x_271_);
lean_ctor_set(v___x_316_, 1, v_x_272_);
v___y_288_ = v___x_316_;
goto v___jp_287_;
}
}
v___jp_287_:
{
lean_object* v___x_289_; lean_object* v___x_291_; 
v___x_289_ = lean_array_fset(v_xs_x27_286_, v_j_278_, v___y_288_);
lean_dec(v_j_278_);
if (v_isShared_283_ == 0)
{
lean_ctor_set(v___x_282_, 0, v___x_289_);
v___x_291_ = v___x_282_;
goto v_reusejp_290_;
}
else
{
lean_object* v_reuseFailAlloc_292_; 
v_reuseFailAlloc_292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_292_, 0, v___x_289_);
v___x_291_ = v_reuseFailAlloc_292_;
goto v_reusejp_290_;
}
v_reusejp_290_:
{
return v___x_291_;
}
}
}
}
}
else
{
lean_object* v_ks_319_; lean_object* v_vs_320_; lean_object* v___x_322_; uint8_t v_isShared_323_; uint8_t v_isSharedCheck_340_; 
v_ks_319_ = lean_ctor_get(v_x_268_, 0);
v_vs_320_ = lean_ctor_get(v_x_268_, 1);
v_isSharedCheck_340_ = !lean_is_exclusive(v_x_268_);
if (v_isSharedCheck_340_ == 0)
{
v___x_322_ = v_x_268_;
v_isShared_323_ = v_isSharedCheck_340_;
goto v_resetjp_321_;
}
else
{
lean_inc(v_vs_320_);
lean_inc(v_ks_319_);
lean_dec(v_x_268_);
v___x_322_ = lean_box(0);
v_isShared_323_ = v_isSharedCheck_340_;
goto v_resetjp_321_;
}
v_resetjp_321_:
{
lean_object* v___x_325_; 
if (v_isShared_323_ == 0)
{
v___x_325_ = v___x_322_;
goto v_reusejp_324_;
}
else
{
lean_object* v_reuseFailAlloc_339_; 
v_reuseFailAlloc_339_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_339_, 0, v_ks_319_);
lean_ctor_set(v_reuseFailAlloc_339_, 1, v_vs_320_);
v___x_325_ = v_reuseFailAlloc_339_;
goto v_reusejp_324_;
}
v_reusejp_324_:
{
lean_object* v_newNode_326_; uint8_t v___y_328_; size_t v___x_334_; uint8_t v___x_335_; 
v_newNode_326_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__1_spec__2_spec__4___redArg(v___x_325_, v_x_271_, v_x_272_);
v___x_334_ = ((size_t)7ULL);
v___x_335_ = lean_usize_dec_le(v___x_334_, v_x_270_);
if (v___x_335_ == 0)
{
lean_object* v___x_336_; lean_object* v___x_337_; uint8_t v___x_338_; 
v___x_336_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_326_);
v___x_337_ = lean_unsigned_to_nat(4u);
v___x_338_ = lean_nat_dec_lt(v___x_336_, v___x_337_);
lean_dec(v___x_336_);
v___y_328_ = v___x_338_;
goto v___jp_327_;
}
else
{
v___y_328_ = v___x_335_;
goto v___jp_327_;
}
v___jp_327_:
{
if (v___y_328_ == 0)
{
lean_object* v_ks_329_; lean_object* v_vs_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; 
v_ks_329_ = lean_ctor_get(v_newNode_326_, 0);
lean_inc_ref(v_ks_329_);
v_vs_330_ = lean_ctor_get(v_newNode_326_, 1);
lean_inc_ref(v_vs_330_);
lean_dec_ref(v_newNode_326_);
v___x_331_ = lean_unsigned_to_nat(0u);
v___x_332_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__1_spec__2___redArg___closed__0);
v___x_333_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__1_spec__2_spec__5___redArg(v_x_270_, v_ks_329_, v_vs_330_, v___x_331_, v___x_332_);
lean_dec_ref(v_vs_330_);
lean_dec_ref(v_ks_329_);
return v___x_333_;
}
else
{
return v_newNode_326_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__1_spec__2_spec__5___redArg(size_t v_depth_341_, lean_object* v_keys_342_, lean_object* v_vals_343_, lean_object* v_i_344_, lean_object* v_entries_345_){
_start:
{
lean_object* v___x_346_; uint8_t v___x_347_; 
v___x_346_ = lean_array_get_size(v_keys_342_);
v___x_347_ = lean_nat_dec_lt(v_i_344_, v___x_346_);
if (v___x_347_ == 0)
{
lean_dec(v_i_344_);
return v_entries_345_;
}
else
{
lean_object* v_k_348_; lean_object* v_v_349_; uint64_t v___x_350_; size_t v_h_351_; size_t v___x_352_; lean_object* v___x_353_; size_t v___x_354_; size_t v___x_355_; size_t v___x_356_; size_t v_h_357_; lean_object* v___x_358_; lean_object* v___x_359_; 
v_k_348_ = lean_array_fget_borrowed(v_keys_342_, v_i_344_);
v_v_349_ = lean_array_fget_borrowed(v_vals_343_, v_i_344_);
v___x_350_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_k_348_);
v_h_351_ = lean_uint64_to_usize(v___x_350_);
v___x_352_ = ((size_t)5ULL);
v___x_353_ = lean_unsigned_to_nat(1u);
v___x_354_ = ((size_t)1ULL);
v___x_355_ = lean_usize_sub(v_depth_341_, v___x_354_);
v___x_356_ = lean_usize_mul(v___x_352_, v___x_355_);
v_h_357_ = lean_usize_shift_right(v_h_351_, v___x_356_);
v___x_358_ = lean_nat_add(v_i_344_, v___x_353_);
lean_dec(v_i_344_);
lean_inc(v_v_349_);
lean_inc(v_k_348_);
v___x_359_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__1_spec__2___redArg(v_entries_345_, v_h_357_, v_depth_341_, v_k_348_, v_v_349_);
v_i_344_ = v___x_358_;
v_entries_345_ = v___x_359_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_depth_361_, lean_object* v_keys_362_, lean_object* v_vals_363_, lean_object* v_i_364_, lean_object* v_entries_365_){
_start:
{
size_t v_depth_boxed_366_; lean_object* v_res_367_; 
v_depth_boxed_366_ = lean_unbox_usize(v_depth_361_);
lean_dec(v_depth_361_);
v_res_367_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__1_spec__2_spec__5___redArg(v_depth_boxed_366_, v_keys_362_, v_vals_363_, v_i_364_, v_entries_365_);
lean_dec_ref(v_vals_363_);
lean_dec_ref(v_keys_362_);
return v_res_367_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__1_spec__2___redArg___boxed(lean_object* v_x_368_, lean_object* v_x_369_, lean_object* v_x_370_, lean_object* v_x_371_, lean_object* v_x_372_){
_start:
{
size_t v_x_4541__boxed_373_; size_t v_x_4542__boxed_374_; lean_object* v_res_375_; 
v_x_4541__boxed_373_ = lean_unbox_usize(v_x_369_);
lean_dec(v_x_369_);
v_x_4542__boxed_374_ = lean_unbox_usize(v_x_370_);
lean_dec(v_x_370_);
v_res_375_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__1_spec__2___redArg(v_x_368_, v_x_4541__boxed_373_, v_x_4542__boxed_374_, v_x_371_, v_x_372_);
return v_res_375_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__1___redArg(lean_object* v_x_376_, lean_object* v_x_377_, lean_object* v_x_378_){
_start:
{
uint64_t v___x_379_; size_t v___x_380_; size_t v___x_381_; lean_object* v___x_382_; 
v___x_379_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_377_);
v___x_380_ = lean_uint64_to_usize(v___x_379_);
v___x_381_ = ((size_t)1ULL);
v___x_382_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__1_spec__2___redArg(v_x_376_, v___x_380_, v___x_381_, v_x_377_, v_x_378_);
return v___x_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getLawfulEqCmpThm_x3f___redArg(lean_object* v_op_383_, lean_object* v_a_384_, lean_object* v_a_385_, lean_object* v_a_386_, lean_object* v_a_387_, lean_object* v_a_388_){
_start:
{
lean_object* v___x_390_; lean_object* v_lawfulEqCmpMap_391_; lean_object* v___x_392_; 
v___x_390_ = lean_st_ref_get(v_a_384_);
v_lawfulEqCmpMap_391_ = lean_ctor_get(v___x_390_, 6);
lean_inc_ref(v_lawfulEqCmpMap_391_);
lean_dec(v___x_390_);
v___x_392_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__0___redArg(v_lawfulEqCmpMap_391_, v_op_383_);
lean_dec_ref(v_lawfulEqCmpMap_391_);
if (lean_obj_tag(v___x_392_) == 1)
{
lean_object* v_val_393_; lean_object* v___x_395_; uint8_t v_isShared_396_; uint8_t v_isSharedCheck_400_; 
lean_dec_ref(v_op_383_);
v_val_393_ = lean_ctor_get(v___x_392_, 0);
v_isSharedCheck_400_ = !lean_is_exclusive(v___x_392_);
if (v_isSharedCheck_400_ == 0)
{
v___x_395_ = v___x_392_;
v_isShared_396_ = v_isSharedCheck_400_;
goto v_resetjp_394_;
}
else
{
lean_inc(v_val_393_);
lean_dec(v___x_392_);
v___x_395_ = lean_box(0);
v_isShared_396_ = v_isSharedCheck_400_;
goto v_resetjp_394_;
}
v_resetjp_394_:
{
lean_object* v___x_398_; 
if (v_isShared_396_ == 0)
{
lean_ctor_set_tag(v___x_395_, 0);
v___x_398_ = v___x_395_;
goto v_reusejp_397_;
}
else
{
lean_object* v_reuseFailAlloc_399_; 
v_reuseFailAlloc_399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_399_, 0, v_val_393_);
v___x_398_ = v_reuseFailAlloc_399_;
goto v_reusejp_397_;
}
v_reusejp_397_:
{
return v___x_398_;
}
}
}
else
{
lean_object* v___x_401_; 
lean_dec(v___x_392_);
lean_inc_ref(v_op_383_);
v___x_401_ = l___private_Lean_Meta_Tactic_Grind_LawfulEqCmp_0__Lean_Meta_Grind_getLawfulEqCmpThm_x3f_go_x3f(v_op_383_, v_a_385_, v_a_386_, v_a_387_, v_a_388_);
if (lean_obj_tag(v___x_401_) == 0)
{
lean_object* v_a_402_; lean_object* v___x_404_; uint8_t v_isShared_405_; uint8_t v_isSharedCheck_429_; 
v_a_402_ = lean_ctor_get(v___x_401_, 0);
v_isSharedCheck_429_ = !lean_is_exclusive(v___x_401_);
if (v_isSharedCheck_429_ == 0)
{
v___x_404_ = v___x_401_;
v_isShared_405_ = v_isSharedCheck_429_;
goto v_resetjp_403_;
}
else
{
lean_inc(v_a_402_);
lean_dec(v___x_401_);
v___x_404_ = lean_box(0);
v_isShared_405_ = v_isSharedCheck_429_;
goto v_resetjp_403_;
}
v_resetjp_403_:
{
lean_object* v___x_406_; lean_object* v_congrThms_407_; lean_object* v_simp_408_; lean_object* v_lastTag_409_; lean_object* v_counters_410_; lean_object* v_splitDiags_411_; lean_object* v_ematchDiags_412_; lean_object* v_lawfulEqCmpMap_413_; lean_object* v_reflCmpMap_414_; lean_object* v_anchors_415_; lean_object* v_instanceMap_416_; lean_object* v___x_418_; uint8_t v_isShared_419_; uint8_t v_isSharedCheck_428_; 
v___x_406_ = lean_st_ref_take(v_a_384_);
v_congrThms_407_ = lean_ctor_get(v___x_406_, 0);
v_simp_408_ = lean_ctor_get(v___x_406_, 1);
v_lastTag_409_ = lean_ctor_get(v___x_406_, 2);
v_counters_410_ = lean_ctor_get(v___x_406_, 3);
v_splitDiags_411_ = lean_ctor_get(v___x_406_, 4);
v_ematchDiags_412_ = lean_ctor_get(v___x_406_, 5);
v_lawfulEqCmpMap_413_ = lean_ctor_get(v___x_406_, 6);
v_reflCmpMap_414_ = lean_ctor_get(v___x_406_, 7);
v_anchors_415_ = lean_ctor_get(v___x_406_, 8);
v_instanceMap_416_ = lean_ctor_get(v___x_406_, 9);
v_isSharedCheck_428_ = !lean_is_exclusive(v___x_406_);
if (v_isSharedCheck_428_ == 0)
{
v___x_418_ = v___x_406_;
v_isShared_419_ = v_isSharedCheck_428_;
goto v_resetjp_417_;
}
else
{
lean_inc(v_instanceMap_416_);
lean_inc(v_anchors_415_);
lean_inc(v_reflCmpMap_414_);
lean_inc(v_lawfulEqCmpMap_413_);
lean_inc(v_ematchDiags_412_);
lean_inc(v_splitDiags_411_);
lean_inc(v_counters_410_);
lean_inc(v_lastTag_409_);
lean_inc(v_simp_408_);
lean_inc(v_congrThms_407_);
lean_dec(v___x_406_);
v___x_418_ = lean_box(0);
v_isShared_419_ = v_isSharedCheck_428_;
goto v_resetjp_417_;
}
v_resetjp_417_:
{
lean_object* v___x_420_; lean_object* v___x_422_; 
lean_inc(v_a_402_);
v___x_420_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__1___redArg(v_lawfulEqCmpMap_413_, v_op_383_, v_a_402_);
if (v_isShared_419_ == 0)
{
lean_ctor_set(v___x_418_, 6, v___x_420_);
v___x_422_ = v___x_418_;
goto v_reusejp_421_;
}
else
{
lean_object* v_reuseFailAlloc_427_; 
v_reuseFailAlloc_427_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_427_, 0, v_congrThms_407_);
lean_ctor_set(v_reuseFailAlloc_427_, 1, v_simp_408_);
lean_ctor_set(v_reuseFailAlloc_427_, 2, v_lastTag_409_);
lean_ctor_set(v_reuseFailAlloc_427_, 3, v_counters_410_);
lean_ctor_set(v_reuseFailAlloc_427_, 4, v_splitDiags_411_);
lean_ctor_set(v_reuseFailAlloc_427_, 5, v_ematchDiags_412_);
lean_ctor_set(v_reuseFailAlloc_427_, 6, v___x_420_);
lean_ctor_set(v_reuseFailAlloc_427_, 7, v_reflCmpMap_414_);
lean_ctor_set(v_reuseFailAlloc_427_, 8, v_anchors_415_);
lean_ctor_set(v_reuseFailAlloc_427_, 9, v_instanceMap_416_);
v___x_422_ = v_reuseFailAlloc_427_;
goto v_reusejp_421_;
}
v_reusejp_421_:
{
lean_object* v___x_423_; lean_object* v___x_425_; 
v___x_423_ = lean_st_ref_set(v_a_384_, v___x_422_);
if (v_isShared_405_ == 0)
{
v___x_425_ = v___x_404_;
goto v_reusejp_424_;
}
else
{
lean_object* v_reuseFailAlloc_426_; 
v_reuseFailAlloc_426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_426_, 0, v_a_402_);
v___x_425_ = v_reuseFailAlloc_426_;
goto v_reusejp_424_;
}
v_reusejp_424_:
{
return v___x_425_;
}
}
}
}
}
else
{
lean_dec_ref(v_op_383_);
return v___x_401_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getLawfulEqCmpThm_x3f___redArg___boxed(lean_object* v_op_430_, lean_object* v_a_431_, lean_object* v_a_432_, lean_object* v_a_433_, lean_object* v_a_434_, lean_object* v_a_435_, lean_object* v_a_436_){
_start:
{
lean_object* v_res_437_; 
v_res_437_ = l_Lean_Meta_Grind_getLawfulEqCmpThm_x3f___redArg(v_op_430_, v_a_431_, v_a_432_, v_a_433_, v_a_434_, v_a_435_);
lean_dec(v_a_435_);
lean_dec_ref(v_a_434_);
lean_dec(v_a_433_);
lean_dec_ref(v_a_432_);
lean_dec(v_a_431_);
return v_res_437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getLawfulEqCmpThm_x3f(lean_object* v_op_438_, lean_object* v_a_439_, lean_object* v_a_440_, lean_object* v_a_441_, lean_object* v_a_442_, lean_object* v_a_443_, lean_object* v_a_444_, lean_object* v_a_445_, lean_object* v_a_446_, lean_object* v_a_447_){
_start:
{
lean_object* v___x_449_; 
v___x_449_ = l_Lean_Meta_Grind_getLawfulEqCmpThm_x3f___redArg(v_op_438_, v_a_441_, v_a_444_, v_a_445_, v_a_446_, v_a_447_);
return v___x_449_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getLawfulEqCmpThm_x3f___boxed(lean_object* v_op_450_, lean_object* v_a_451_, lean_object* v_a_452_, lean_object* v_a_453_, lean_object* v_a_454_, lean_object* v_a_455_, lean_object* v_a_456_, lean_object* v_a_457_, lean_object* v_a_458_, lean_object* v_a_459_, lean_object* v_a_460_){
_start:
{
lean_object* v_res_461_; 
v_res_461_ = l_Lean_Meta_Grind_getLawfulEqCmpThm_x3f(v_op_450_, v_a_451_, v_a_452_, v_a_453_, v_a_454_, v_a_455_, v_a_456_, v_a_457_, v_a_458_, v_a_459_);
lean_dec(v_a_459_);
lean_dec_ref(v_a_458_);
lean_dec(v_a_457_);
lean_dec_ref(v_a_456_);
lean_dec(v_a_455_);
lean_dec_ref(v_a_454_);
lean_dec(v_a_453_);
lean_dec_ref(v_a_452_);
lean_dec(v_a_451_);
return v_res_461_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__0(lean_object* v_00_u03b2_462_, lean_object* v_x_463_, lean_object* v_x_464_){
_start:
{
lean_object* v___x_465_; 
v___x_465_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__0___redArg(v_x_463_, v_x_464_);
return v___x_465_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__0___boxed(lean_object* v_00_u03b2_466_, lean_object* v_x_467_, lean_object* v_x_468_){
_start:
{
lean_object* v_res_469_; 
v_res_469_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__0(v_00_u03b2_466_, v_x_467_, v_x_468_);
lean_dec_ref(v_x_468_);
lean_dec_ref(v_x_467_);
return v_res_469_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__1(lean_object* v_00_u03b2_470_, lean_object* v_x_471_, lean_object* v_x_472_, lean_object* v_x_473_){
_start:
{
lean_object* v___x_474_; 
v___x_474_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__1___redArg(v_x_471_, v_x_472_, v_x_473_);
return v___x_474_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__0_spec__0(lean_object* v_00_u03b2_475_, lean_object* v_x_476_, size_t v_x_477_, lean_object* v_x_478_){
_start:
{
lean_object* v___x_479_; 
v___x_479_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__0_spec__0___redArg(v_x_476_, v_x_477_, v_x_478_);
return v___x_479_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_480_, lean_object* v_x_481_, lean_object* v_x_482_, lean_object* v_x_483_){
_start:
{
size_t v_x_4794__boxed_484_; lean_object* v_res_485_; 
v_x_4794__boxed_484_ = lean_unbox_usize(v_x_482_);
lean_dec(v_x_482_);
v_res_485_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__0_spec__0(v_00_u03b2_480_, v_x_481_, v_x_4794__boxed_484_, v_x_483_);
lean_dec_ref(v_x_483_);
lean_dec_ref(v_x_481_);
return v_res_485_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__1_spec__2(lean_object* v_00_u03b2_486_, lean_object* v_x_487_, size_t v_x_488_, size_t v_x_489_, lean_object* v_x_490_, lean_object* v_x_491_){
_start:
{
lean_object* v___x_492_; 
v___x_492_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__1_spec__2___redArg(v_x_487_, v_x_488_, v_x_489_, v_x_490_, v_x_491_);
return v___x_492_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__1_spec__2___boxed(lean_object* v_00_u03b2_493_, lean_object* v_x_494_, lean_object* v_x_495_, lean_object* v_x_496_, lean_object* v_x_497_, lean_object* v_x_498_){
_start:
{
size_t v_x_4805__boxed_499_; size_t v_x_4806__boxed_500_; lean_object* v_res_501_; 
v_x_4805__boxed_499_ = lean_unbox_usize(v_x_495_);
lean_dec(v_x_495_);
v_x_4806__boxed_500_ = lean_unbox_usize(v_x_496_);
lean_dec(v_x_496_);
v_res_501_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__1_spec__2(v_00_u03b2_493_, v_x_494_, v_x_4805__boxed_499_, v_x_4806__boxed_500_, v_x_497_, v_x_498_);
return v_res_501_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_502_, lean_object* v_keys_503_, lean_object* v_vals_504_, lean_object* v_heq_505_, lean_object* v_i_506_, lean_object* v_k_507_){
_start:
{
lean_object* v___x_508_; 
v___x_508_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__0_spec__0_spec__1___redArg(v_keys_503_, v_vals_504_, v_i_506_, v_k_507_);
return v___x_508_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_509_, lean_object* v_keys_510_, lean_object* v_vals_511_, lean_object* v_heq_512_, lean_object* v_i_513_, lean_object* v_k_514_){
_start:
{
lean_object* v_res_515_; 
v_res_515_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__0_spec__0_spec__1(v_00_u03b2_509_, v_keys_510_, v_vals_511_, v_heq_512_, v_i_513_, v_k_514_);
lean_dec_ref(v_k_514_);
lean_dec_ref(v_vals_511_);
lean_dec_ref(v_keys_510_);
return v_res_515_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_516_, lean_object* v_n_517_, lean_object* v_k_518_, lean_object* v_v_519_){
_start:
{
lean_object* v___x_520_; 
v___x_520_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__1_spec__2_spec__4___redArg(v_n_517_, v_k_518_, v_v_519_);
return v___x_520_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_521_, size_t v_depth_522_, lean_object* v_keys_523_, lean_object* v_vals_524_, lean_object* v_heq_525_, lean_object* v_i_526_, lean_object* v_entries_527_){
_start:
{
lean_object* v___x_528_; 
v___x_528_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__1_spec__2_spec__5___redArg(v_depth_522_, v_keys_523_, v_vals_524_, v_i_526_, v_entries_527_);
return v___x_528_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_529_, lean_object* v_depth_530_, lean_object* v_keys_531_, lean_object* v_vals_532_, lean_object* v_heq_533_, lean_object* v_i_534_, lean_object* v_entries_535_){
_start:
{
size_t v_depth_boxed_536_; lean_object* v_res_537_; 
v_depth_boxed_536_ = lean_unbox_usize(v_depth_530_);
lean_dec(v_depth_530_);
v_res_537_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__1_spec__2_spec__5(v_00_u03b2_529_, v_depth_boxed_536_, v_keys_531_, v_vals_532_, v_heq_533_, v_i_534_, v_entries_535_);
lean_dec_ref(v_vals_532_);
lean_dec_ref(v_keys_531_);
return v_res_537_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__1_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_538_, lean_object* v_x_539_, lean_object* v_x_540_, lean_object* v_x_541_, lean_object* v_x_542_){
_start:
{
lean_object* v___x_543_; 
v___x_543_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__1_spec__2_spec__4_spec__5___redArg(v_x_539_, v_x_540_, v_x_541_, v_x_542_);
return v___x_543_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateLawfulEqCmp(lean_object* v_e_544_, lean_object* v_a_545_, lean_object* v_a_546_, lean_object* v_a_547_, lean_object* v_a_548_, lean_object* v_a_549_, lean_object* v_a_550_, lean_object* v_a_551_, lean_object* v_a_552_, lean_object* v_a_553_, lean_object* v_a_554_){
_start:
{
lean_object* v___x_556_; 
v___x_556_ = l_Lean_Meta_Grind_getBinOp(v_e_544_);
if (lean_obj_tag(v___x_556_) == 1)
{
lean_object* v_val_557_; lean_object* v___x_558_; 
v_val_557_ = lean_ctor_get(v___x_556_, 0);
lean_inc(v_val_557_);
lean_dec_ref(v___x_556_);
v___x_558_ = l_Lean_Meta_Grind_getLawfulEqCmpThm_x3f___redArg(v_val_557_, v_a_548_, v_a_551_, v_a_552_, v_a_553_, v_a_554_);
if (lean_obj_tag(v___x_558_) == 0)
{
lean_object* v_a_559_; lean_object* v___x_561_; uint8_t v_isShared_562_; uint8_t v_isSharedCheck_613_; 
v_a_559_ = lean_ctor_get(v___x_558_, 0);
v_isSharedCheck_613_ = !lean_is_exclusive(v___x_558_);
if (v_isSharedCheck_613_ == 0)
{
v___x_561_ = v___x_558_;
v_isShared_562_ = v_isSharedCheck_613_;
goto v_resetjp_560_;
}
else
{
lean_inc(v_a_559_);
lean_dec(v___x_558_);
v___x_561_ = lean_box(0);
v_isShared_562_ = v_isSharedCheck_613_;
goto v_resetjp_560_;
}
v_resetjp_560_:
{
if (lean_obj_tag(v_a_559_) == 1)
{
lean_object* v_val_563_; lean_object* v___x_564_; 
lean_del_object(v___x_561_);
v_val_563_ = lean_ctor_get(v_a_559_, 0);
lean_inc(v_val_563_);
lean_dec_ref(v_a_559_);
v___x_564_ = l_Lean_Meta_Sym_getOrderingEqExpr___redArg(v_a_549_);
if (lean_obj_tag(v___x_564_) == 0)
{
lean_object* v_a_565_; lean_object* v___x_566_; 
v_a_565_ = lean_ctor_get(v___x_564_, 0);
lean_inc(v_a_565_);
lean_dec_ref(v___x_564_);
v___x_566_ = l_Lean_Meta_Grind_isEqv___redArg(v_e_544_, v_a_565_, v_a_545_);
if (lean_obj_tag(v___x_566_) == 0)
{
lean_object* v_a_567_; lean_object* v___x_569_; uint8_t v_isShared_570_; uint8_t v_isSharedCheck_592_; 
v_a_567_ = lean_ctor_get(v___x_566_, 0);
v_isSharedCheck_592_ = !lean_is_exclusive(v___x_566_);
if (v_isSharedCheck_592_ == 0)
{
v___x_569_ = v___x_566_;
v_isShared_570_ = v_isSharedCheck_592_;
goto v_resetjp_568_;
}
else
{
lean_inc(v_a_567_);
lean_dec(v___x_566_);
v___x_569_ = lean_box(0);
v_isShared_570_ = v_isSharedCheck_592_;
goto v_resetjp_568_;
}
v_resetjp_568_:
{
uint8_t v___x_571_; 
v___x_571_ = lean_unbox(v_a_567_);
lean_dec(v_a_567_);
if (v___x_571_ == 0)
{
lean_object* v___x_572_; lean_object* v___x_574_; 
lean_dec(v_a_565_);
lean_dec(v_val_563_);
lean_dec_ref(v_e_544_);
v___x_572_ = lean_box(0);
if (v_isShared_570_ == 0)
{
lean_ctor_set(v___x_569_, 0, v___x_572_);
v___x_574_ = v___x_569_;
goto v_reusejp_573_;
}
else
{
lean_object* v_reuseFailAlloc_575_; 
v_reuseFailAlloc_575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_575_, 0, v___x_572_);
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
lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; 
lean_del_object(v___x_569_);
v___x_576_ = l_Lean_Expr_appFn_x21(v_e_544_);
v___x_577_ = l_Lean_Expr_appArg_x21(v_e_544_);
lean_inc(v_a_554_);
lean_inc_ref(v_a_553_);
lean_inc(v_a_552_);
lean_inc_ref(v_a_551_);
lean_inc(v_a_550_);
lean_inc_ref(v_a_549_);
lean_inc(v_a_548_);
lean_inc_ref(v_a_547_);
lean_inc(v_a_546_);
lean_inc(v_a_545_);
v___x_578_ = lean_grind_mk_eq_proof(v_e_544_, v_a_565_, v_a_545_, v_a_546_, v_a_547_, v_a_548_, v_a_549_, v_a_550_, v_a_551_, v_a_552_, v_a_553_, v_a_554_);
if (lean_obj_tag(v___x_578_) == 0)
{
lean_object* v_a_579_; lean_object* v___x_580_; lean_object* v___x_581_; uint8_t v___x_582_; lean_object* v___x_583_; 
v_a_579_ = lean_ctor_get(v___x_578_, 0);
lean_inc(v_a_579_);
lean_dec_ref(v___x_578_);
v___x_580_ = l_Lean_Expr_appArg_x21(v___x_576_);
lean_dec_ref(v___x_576_);
lean_inc_ref(v___x_577_);
lean_inc_ref(v___x_580_);
v___x_581_ = l_Lean_mkApp3(v_val_563_, v___x_580_, v___x_577_, v_a_579_);
v___x_582_ = 0;
v___x_583_ = l_Lean_Meta_Grind_pushEqCore___redArg(v___x_580_, v___x_577_, v___x_581_, v___x_582_, v_a_545_, v_a_547_, v_a_551_, v_a_552_, v_a_553_, v_a_554_);
return v___x_583_;
}
else
{
lean_object* v_a_584_; lean_object* v___x_586_; uint8_t v_isShared_587_; uint8_t v_isSharedCheck_591_; 
lean_dec_ref(v___x_577_);
lean_dec_ref(v___x_576_);
lean_dec(v_val_563_);
v_a_584_ = lean_ctor_get(v___x_578_, 0);
v_isSharedCheck_591_ = !lean_is_exclusive(v___x_578_);
if (v_isSharedCheck_591_ == 0)
{
v___x_586_ = v___x_578_;
v_isShared_587_ = v_isSharedCheck_591_;
goto v_resetjp_585_;
}
else
{
lean_inc(v_a_584_);
lean_dec(v___x_578_);
v___x_586_ = lean_box(0);
v_isShared_587_ = v_isSharedCheck_591_;
goto v_resetjp_585_;
}
v_resetjp_585_:
{
lean_object* v___x_589_; 
if (v_isShared_587_ == 0)
{
v___x_589_ = v___x_586_;
goto v_reusejp_588_;
}
else
{
lean_object* v_reuseFailAlloc_590_; 
v_reuseFailAlloc_590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_590_, 0, v_a_584_);
v___x_589_ = v_reuseFailAlloc_590_;
goto v_reusejp_588_;
}
v_reusejp_588_:
{
return v___x_589_;
}
}
}
}
}
}
else
{
lean_object* v_a_593_; lean_object* v___x_595_; uint8_t v_isShared_596_; uint8_t v_isSharedCheck_600_; 
lean_dec(v_a_565_);
lean_dec(v_val_563_);
lean_dec_ref(v_e_544_);
v_a_593_ = lean_ctor_get(v___x_566_, 0);
v_isSharedCheck_600_ = !lean_is_exclusive(v___x_566_);
if (v_isSharedCheck_600_ == 0)
{
v___x_595_ = v___x_566_;
v_isShared_596_ = v_isSharedCheck_600_;
goto v_resetjp_594_;
}
else
{
lean_inc(v_a_593_);
lean_dec(v___x_566_);
v___x_595_ = lean_box(0);
v_isShared_596_ = v_isSharedCheck_600_;
goto v_resetjp_594_;
}
v_resetjp_594_:
{
lean_object* v___x_598_; 
if (v_isShared_596_ == 0)
{
v___x_598_ = v___x_595_;
goto v_reusejp_597_;
}
else
{
lean_object* v_reuseFailAlloc_599_; 
v_reuseFailAlloc_599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_599_, 0, v_a_593_);
v___x_598_ = v_reuseFailAlloc_599_;
goto v_reusejp_597_;
}
v_reusejp_597_:
{
return v___x_598_;
}
}
}
}
else
{
lean_object* v_a_601_; lean_object* v___x_603_; uint8_t v_isShared_604_; uint8_t v_isSharedCheck_608_; 
lean_dec(v_val_563_);
lean_dec_ref(v_e_544_);
v_a_601_ = lean_ctor_get(v___x_564_, 0);
v_isSharedCheck_608_ = !lean_is_exclusive(v___x_564_);
if (v_isSharedCheck_608_ == 0)
{
v___x_603_ = v___x_564_;
v_isShared_604_ = v_isSharedCheck_608_;
goto v_resetjp_602_;
}
else
{
lean_inc(v_a_601_);
lean_dec(v___x_564_);
v___x_603_ = lean_box(0);
v_isShared_604_ = v_isSharedCheck_608_;
goto v_resetjp_602_;
}
v_resetjp_602_:
{
lean_object* v___x_606_; 
if (v_isShared_604_ == 0)
{
v___x_606_ = v___x_603_;
goto v_reusejp_605_;
}
else
{
lean_object* v_reuseFailAlloc_607_; 
v_reuseFailAlloc_607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_607_, 0, v_a_601_);
v___x_606_ = v_reuseFailAlloc_607_;
goto v_reusejp_605_;
}
v_reusejp_605_:
{
return v___x_606_;
}
}
}
}
else
{
lean_object* v___x_609_; lean_object* v___x_611_; 
lean_dec(v_a_559_);
lean_dec_ref(v_e_544_);
v___x_609_ = lean_box(0);
if (v_isShared_562_ == 0)
{
lean_ctor_set(v___x_561_, 0, v___x_609_);
v___x_611_ = v___x_561_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v___x_609_);
v___x_611_ = v_reuseFailAlloc_612_;
goto v_reusejp_610_;
}
v_reusejp_610_:
{
return v___x_611_;
}
}
}
}
else
{
lean_object* v_a_614_; lean_object* v___x_616_; uint8_t v_isShared_617_; uint8_t v_isSharedCheck_621_; 
lean_dec_ref(v_e_544_);
v_a_614_ = lean_ctor_get(v___x_558_, 0);
v_isSharedCheck_621_ = !lean_is_exclusive(v___x_558_);
if (v_isSharedCheck_621_ == 0)
{
v___x_616_ = v___x_558_;
v_isShared_617_ = v_isSharedCheck_621_;
goto v_resetjp_615_;
}
else
{
lean_inc(v_a_614_);
lean_dec(v___x_558_);
v___x_616_ = lean_box(0);
v_isShared_617_ = v_isSharedCheck_621_;
goto v_resetjp_615_;
}
v_resetjp_615_:
{
lean_object* v___x_619_; 
if (v_isShared_617_ == 0)
{
v___x_619_ = v___x_616_;
goto v_reusejp_618_;
}
else
{
lean_object* v_reuseFailAlloc_620_; 
v_reuseFailAlloc_620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_620_, 0, v_a_614_);
v___x_619_ = v_reuseFailAlloc_620_;
goto v_reusejp_618_;
}
v_reusejp_618_:
{
return v___x_619_;
}
}
}
}
else
{
lean_object* v___x_622_; lean_object* v___x_623_; 
lean_dec(v___x_556_);
lean_dec_ref(v_e_544_);
v___x_622_ = lean_box(0);
v___x_623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_623_, 0, v___x_622_);
return v___x_623_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateLawfulEqCmp___boxed(lean_object* v_e_624_, lean_object* v_a_625_, lean_object* v_a_626_, lean_object* v_a_627_, lean_object* v_a_628_, lean_object* v_a_629_, lean_object* v_a_630_, lean_object* v_a_631_, lean_object* v_a_632_, lean_object* v_a_633_, lean_object* v_a_634_, lean_object* v_a_635_){
_start:
{
lean_object* v_res_636_; 
v_res_636_ = l_Lean_Meta_Grind_propagateLawfulEqCmp(v_e_624_, v_a_625_, v_a_626_, v_a_627_, v_a_628_, v_a_629_, v_a_630_, v_a_631_, v_a_632_, v_a_633_, v_a_634_);
lean_dec(v_a_634_);
lean_dec_ref(v_a_633_);
lean_dec(v_a_632_);
lean_dec_ref(v_a_631_);
lean_dec(v_a_630_);
lean_dec_ref(v_a_629_);
lean_dec(v_a_628_);
lean_dec_ref(v_a_627_);
lean_dec(v_a_626_);
lean_dec(v_a_625_);
return v_res_636_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_SynthInstance(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_LawfulEqCmp(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Grind_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_SynthInstance(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_LawfulEqCmp(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Util(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_SynthInstance(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_LawfulEqCmp(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_SynthInstance(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_LawfulEqCmp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_LawfulEqCmp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_LawfulEqCmp(builtin);
}
#ifdef __cplusplus
}
#endif
