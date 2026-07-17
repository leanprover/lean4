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
lean_object* lean_st_ref_get(lean_object*);
size_t lean_ptr_addr(lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
uint64_t lean_usize_to_uint64(size_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
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
size_t lean_usize_sub(size_t, size_t);
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
lean_dec_ref_known(v___x_27_, 1);
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
lean_dec_ref_known(v_a_30_, 3);
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
lean_dec_ref_known(v_a_38_, 3);
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
lean_dec_ref_known(v___x_60_, 1);
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
lean_dec_ref_known(v_a_63_, 1);
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
lean_dec_ref_known(v___x_69_, 2);
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
lean_dec_ref_known(v___x_69_, 2);
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
lean_object* v_k_x27_178_; size_t v___x_179_; size_t v___x_180_; uint8_t v___x_181_; 
v_k_x27_178_ = lean_array_fget_borrowed(v_keys_171_, v_i_173_);
v___x_179_ = lean_ptr_addr(v_k_174_);
v___x_180_ = lean_ptr_addr(v_k_x27_178_);
v___x_181_ = lean_usize_dec_eq(v___x_179_, v___x_180_);
if (v___x_181_ == 0)
{
lean_object* v___x_182_; lean_object* v___x_183_; 
v___x_182_ = lean_unsigned_to_nat(1u);
v___x_183_ = lean_nat_add(v_i_173_, v___x_182_);
lean_dec(v_i_173_);
v_i_173_ = v___x_183_;
goto _start;
}
else
{
lean_object* v___x_185_; lean_object* v___x_186_; 
v___x_185_ = lean_array_fget_borrowed(v_vals_172_, v_i_173_);
lean_dec(v_i_173_);
lean_inc(v___x_185_);
v___x_186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_186_, 0, v___x_185_);
return v___x_186_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_187_, lean_object* v_vals_188_, lean_object* v_i_189_, lean_object* v_k_190_){
_start:
{
lean_object* v_res_191_; 
v_res_191_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__0_spec__0_spec__1___redArg(v_keys_187_, v_vals_188_, v_i_189_, v_k_190_);
lean_dec_ref(v_k_190_);
lean_dec_ref(v_vals_188_);
lean_dec_ref(v_keys_187_);
return v_res_191_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__0_spec__0___redArg(lean_object* v_x_192_, size_t v_x_193_, lean_object* v_x_194_){
_start:
{
if (lean_obj_tag(v_x_192_) == 0)
{
lean_object* v_es_195_; lean_object* v___x_196_; size_t v___x_197_; size_t v___x_198_; lean_object* v_j_199_; lean_object* v___x_200_; 
v_es_195_ = lean_ctor_get(v_x_192_, 0);
v___x_196_ = lean_box(2);
v___x_197_ = ((size_t)31ULL);
v___x_198_ = lean_usize_land(v_x_193_, v___x_197_);
v_j_199_ = lean_usize_to_nat(v___x_198_);
v___x_200_ = lean_array_get_borrowed(v___x_196_, v_es_195_, v_j_199_);
lean_dec(v_j_199_);
switch(lean_obj_tag(v___x_200_))
{
case 0:
{
lean_object* v_key_201_; lean_object* v_val_202_; size_t v___x_203_; size_t v___x_204_; uint8_t v___x_205_; 
v_key_201_ = lean_ctor_get(v___x_200_, 0);
v_val_202_ = lean_ctor_get(v___x_200_, 1);
v___x_203_ = lean_ptr_addr(v_x_194_);
v___x_204_ = lean_ptr_addr(v_key_201_);
v___x_205_ = lean_usize_dec_eq(v___x_203_, v___x_204_);
if (v___x_205_ == 0)
{
lean_object* v___x_206_; 
v___x_206_ = lean_box(0);
return v___x_206_;
}
else
{
lean_object* v___x_207_; 
lean_inc(v_val_202_);
v___x_207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_207_, 0, v_val_202_);
return v___x_207_;
}
}
case 1:
{
lean_object* v_node_208_; size_t v___x_209_; size_t v___x_210_; 
v_node_208_ = lean_ctor_get(v___x_200_, 0);
v___x_209_ = ((size_t)5ULL);
v___x_210_ = lean_usize_shift_right(v_x_193_, v___x_209_);
v_x_192_ = v_node_208_;
v_x_193_ = v___x_210_;
goto _start;
}
default: 
{
lean_object* v___x_212_; 
v___x_212_ = lean_box(0);
return v___x_212_;
}
}
}
else
{
lean_object* v_ks_213_; lean_object* v_vs_214_; lean_object* v___x_215_; lean_object* v___x_216_; 
v_ks_213_ = lean_ctor_get(v_x_192_, 0);
v_vs_214_ = lean_ctor_get(v_x_192_, 1);
v___x_215_ = lean_unsigned_to_nat(0u);
v___x_216_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__0_spec__0_spec__1___redArg(v_ks_213_, v_vs_214_, v___x_215_, v_x_194_);
return v___x_216_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_217_, lean_object* v_x_218_, lean_object* v_x_219_){
_start:
{
size_t v_x_4426__boxed_220_; lean_object* v_res_221_; 
v_x_4426__boxed_220_ = lean_unbox_usize(v_x_218_);
lean_dec(v_x_218_);
v_res_221_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__0_spec__0___redArg(v_x_217_, v_x_4426__boxed_220_, v_x_219_);
lean_dec_ref(v_x_219_);
lean_dec_ref(v_x_217_);
return v_res_221_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__0___redArg(lean_object* v_x_222_, lean_object* v_x_223_){
_start:
{
size_t v___x_224_; size_t v___x_225_; size_t v___x_226_; uint64_t v___x_227_; size_t v___x_228_; lean_object* v___x_229_; 
v___x_224_ = lean_ptr_addr(v_x_223_);
v___x_225_ = ((size_t)3ULL);
v___x_226_ = lean_usize_shift_right(v___x_224_, v___x_225_);
v___x_227_ = lean_usize_to_uint64(v___x_226_);
v___x_228_ = lean_uint64_to_usize(v___x_227_);
v___x_229_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__0_spec__0___redArg(v_x_222_, v___x_228_, v_x_223_);
return v___x_229_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__0___redArg___boxed(lean_object* v_x_230_, lean_object* v_x_231_){
_start:
{
lean_object* v_res_232_; 
v_res_232_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__0___redArg(v_x_230_, v_x_231_);
lean_dec_ref(v_x_231_);
lean_dec_ref(v_x_230_);
return v_res_232_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__1_spec__2_spec__4_spec__5___redArg(lean_object* v_x_233_, lean_object* v_x_234_, lean_object* v_x_235_, lean_object* v_x_236_){
_start:
{
lean_object* v_ks_237_; lean_object* v_vs_238_; lean_object* v___x_240_; uint8_t v_isShared_241_; uint8_t v_isSharedCheck_264_; 
v_ks_237_ = lean_ctor_get(v_x_233_, 0);
v_vs_238_ = lean_ctor_get(v_x_233_, 1);
v_isSharedCheck_264_ = !lean_is_exclusive(v_x_233_);
if (v_isSharedCheck_264_ == 0)
{
v___x_240_ = v_x_233_;
v_isShared_241_ = v_isSharedCheck_264_;
goto v_resetjp_239_;
}
else
{
lean_inc(v_vs_238_);
lean_inc(v_ks_237_);
lean_dec(v_x_233_);
v___x_240_ = lean_box(0);
v_isShared_241_ = v_isSharedCheck_264_;
goto v_resetjp_239_;
}
v_resetjp_239_:
{
lean_object* v___x_242_; uint8_t v___x_243_; 
v___x_242_ = lean_array_get_size(v_ks_237_);
v___x_243_ = lean_nat_dec_lt(v_x_234_, v___x_242_);
if (v___x_243_ == 0)
{
lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_247_; 
lean_dec(v_x_234_);
v___x_244_ = lean_array_push(v_ks_237_, v_x_235_);
v___x_245_ = lean_array_push(v_vs_238_, v_x_236_);
if (v_isShared_241_ == 0)
{
lean_ctor_set(v___x_240_, 1, v___x_245_);
lean_ctor_set(v___x_240_, 0, v___x_244_);
v___x_247_ = v___x_240_;
goto v_reusejp_246_;
}
else
{
lean_object* v_reuseFailAlloc_248_; 
v_reuseFailAlloc_248_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_248_, 0, v___x_244_);
lean_ctor_set(v_reuseFailAlloc_248_, 1, v___x_245_);
v___x_247_ = v_reuseFailAlloc_248_;
goto v_reusejp_246_;
}
v_reusejp_246_:
{
return v___x_247_;
}
}
else
{
lean_object* v_k_x27_249_; size_t v___x_250_; size_t v___x_251_; uint8_t v___x_252_; 
v_k_x27_249_ = lean_array_fget_borrowed(v_ks_237_, v_x_234_);
v___x_250_ = lean_ptr_addr(v_x_235_);
v___x_251_ = lean_ptr_addr(v_k_x27_249_);
v___x_252_ = lean_usize_dec_eq(v___x_250_, v___x_251_);
if (v___x_252_ == 0)
{
lean_object* v___x_254_; 
if (v_isShared_241_ == 0)
{
v___x_254_ = v___x_240_;
goto v_reusejp_253_;
}
else
{
lean_object* v_reuseFailAlloc_258_; 
v_reuseFailAlloc_258_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_258_, 0, v_ks_237_);
lean_ctor_set(v_reuseFailAlloc_258_, 1, v_vs_238_);
v___x_254_ = v_reuseFailAlloc_258_;
goto v_reusejp_253_;
}
v_reusejp_253_:
{
lean_object* v___x_255_; lean_object* v___x_256_; 
v___x_255_ = lean_unsigned_to_nat(1u);
v___x_256_ = lean_nat_add(v_x_234_, v___x_255_);
lean_dec(v_x_234_);
v_x_233_ = v___x_254_;
v_x_234_ = v___x_256_;
goto _start;
}
}
else
{
lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_262_; 
v___x_259_ = lean_array_fset(v_ks_237_, v_x_234_, v_x_235_);
v___x_260_ = lean_array_fset(v_vs_238_, v_x_234_, v_x_236_);
lean_dec(v_x_234_);
if (v_isShared_241_ == 0)
{
lean_ctor_set(v___x_240_, 1, v___x_260_);
lean_ctor_set(v___x_240_, 0, v___x_259_);
v___x_262_ = v___x_240_;
goto v_reusejp_261_;
}
else
{
lean_object* v_reuseFailAlloc_263_; 
v_reuseFailAlloc_263_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_263_, 0, v___x_259_);
lean_ctor_set(v_reuseFailAlloc_263_, 1, v___x_260_);
v___x_262_ = v_reuseFailAlloc_263_;
goto v_reusejp_261_;
}
v_reusejp_261_:
{
return v___x_262_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__1_spec__2_spec__4___redArg(lean_object* v_n_265_, lean_object* v_k_266_, lean_object* v_v_267_){
_start:
{
lean_object* v___x_268_; lean_object* v___x_269_; 
v___x_268_ = lean_unsigned_to_nat(0u);
v___x_269_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__1_spec__2_spec__4_spec__5___redArg(v_n_265_, v___x_268_, v_k_266_, v_v_267_);
return v___x_269_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_270_; 
v___x_270_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_270_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__1_spec__2___redArg(lean_object* v_x_271_, size_t v_x_272_, size_t v_x_273_, lean_object* v_x_274_, lean_object* v_x_275_){
_start:
{
if (lean_obj_tag(v_x_271_) == 0)
{
lean_object* v_es_276_; size_t v___x_277_; size_t v___x_278_; lean_object* v_j_279_; lean_object* v___x_280_; uint8_t v___x_281_; 
v_es_276_ = lean_ctor_get(v_x_271_, 0);
v___x_277_ = ((size_t)31ULL);
v___x_278_ = lean_usize_land(v_x_272_, v___x_277_);
v_j_279_ = lean_usize_to_nat(v___x_278_);
v___x_280_ = lean_array_get_size(v_es_276_);
v___x_281_ = lean_nat_dec_lt(v_j_279_, v___x_280_);
if (v___x_281_ == 0)
{
lean_dec(v_j_279_);
lean_dec(v_x_275_);
lean_dec_ref(v_x_274_);
return v_x_271_;
}
else
{
lean_object* v___x_283_; uint8_t v_isShared_284_; uint8_t v_isSharedCheck_322_; 
lean_inc_ref(v_es_276_);
v_isSharedCheck_322_ = !lean_is_exclusive(v_x_271_);
if (v_isSharedCheck_322_ == 0)
{
lean_object* v_unused_323_; 
v_unused_323_ = lean_ctor_get(v_x_271_, 0);
lean_dec(v_unused_323_);
v___x_283_ = v_x_271_;
v_isShared_284_ = v_isSharedCheck_322_;
goto v_resetjp_282_;
}
else
{
lean_dec(v_x_271_);
v___x_283_ = lean_box(0);
v_isShared_284_ = v_isSharedCheck_322_;
goto v_resetjp_282_;
}
v_resetjp_282_:
{
lean_object* v_v_285_; lean_object* v___x_286_; lean_object* v_xs_x27_287_; lean_object* v___y_289_; 
v_v_285_ = lean_array_fget(v_es_276_, v_j_279_);
v___x_286_ = lean_box(0);
v_xs_x27_287_ = lean_array_fset(v_es_276_, v_j_279_, v___x_286_);
switch(lean_obj_tag(v_v_285_))
{
case 0:
{
lean_object* v_key_294_; lean_object* v_val_295_; lean_object* v___x_297_; uint8_t v_isShared_298_; uint8_t v_isSharedCheck_307_; 
v_key_294_ = lean_ctor_get(v_v_285_, 0);
v_val_295_ = lean_ctor_get(v_v_285_, 1);
v_isSharedCheck_307_ = !lean_is_exclusive(v_v_285_);
if (v_isSharedCheck_307_ == 0)
{
v___x_297_ = v_v_285_;
v_isShared_298_ = v_isSharedCheck_307_;
goto v_resetjp_296_;
}
else
{
lean_inc(v_val_295_);
lean_inc(v_key_294_);
lean_dec(v_v_285_);
v___x_297_ = lean_box(0);
v_isShared_298_ = v_isSharedCheck_307_;
goto v_resetjp_296_;
}
v_resetjp_296_:
{
size_t v___x_299_; size_t v___x_300_; uint8_t v___x_301_; 
v___x_299_ = lean_ptr_addr(v_x_274_);
v___x_300_ = lean_ptr_addr(v_key_294_);
v___x_301_ = lean_usize_dec_eq(v___x_299_, v___x_300_);
if (v___x_301_ == 0)
{
lean_object* v___x_302_; lean_object* v___x_303_; 
lean_del_object(v___x_297_);
v___x_302_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_294_, v_val_295_, v_x_274_, v_x_275_);
v___x_303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_303_, 0, v___x_302_);
v___y_289_ = v___x_303_;
goto v___jp_288_;
}
else
{
lean_object* v___x_305_; 
lean_dec(v_val_295_);
lean_dec(v_key_294_);
if (v_isShared_298_ == 0)
{
lean_ctor_set(v___x_297_, 1, v_x_275_);
lean_ctor_set(v___x_297_, 0, v_x_274_);
v___x_305_ = v___x_297_;
goto v_reusejp_304_;
}
else
{
lean_object* v_reuseFailAlloc_306_; 
v_reuseFailAlloc_306_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_306_, 0, v_x_274_);
lean_ctor_set(v_reuseFailAlloc_306_, 1, v_x_275_);
v___x_305_ = v_reuseFailAlloc_306_;
goto v_reusejp_304_;
}
v_reusejp_304_:
{
v___y_289_ = v___x_305_;
goto v___jp_288_;
}
}
}
}
case 1:
{
lean_object* v_node_308_; lean_object* v___x_310_; uint8_t v_isShared_311_; uint8_t v_isSharedCheck_320_; 
v_node_308_ = lean_ctor_get(v_v_285_, 0);
v_isSharedCheck_320_ = !lean_is_exclusive(v_v_285_);
if (v_isSharedCheck_320_ == 0)
{
v___x_310_ = v_v_285_;
v_isShared_311_ = v_isSharedCheck_320_;
goto v_resetjp_309_;
}
else
{
lean_inc(v_node_308_);
lean_dec(v_v_285_);
v___x_310_ = lean_box(0);
v_isShared_311_ = v_isSharedCheck_320_;
goto v_resetjp_309_;
}
v_resetjp_309_:
{
size_t v___x_312_; size_t v___x_313_; size_t v___x_314_; size_t v___x_315_; lean_object* v___x_316_; lean_object* v___x_318_; 
v___x_312_ = ((size_t)5ULL);
v___x_313_ = lean_usize_shift_right(v_x_272_, v___x_312_);
v___x_314_ = ((size_t)1ULL);
v___x_315_ = lean_usize_add(v_x_273_, v___x_314_);
v___x_316_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__1_spec__2___redArg(v_node_308_, v___x_313_, v___x_315_, v_x_274_, v_x_275_);
if (v_isShared_311_ == 0)
{
lean_ctor_set(v___x_310_, 0, v___x_316_);
v___x_318_ = v___x_310_;
goto v_reusejp_317_;
}
else
{
lean_object* v_reuseFailAlloc_319_; 
v_reuseFailAlloc_319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_319_, 0, v___x_316_);
v___x_318_ = v_reuseFailAlloc_319_;
goto v_reusejp_317_;
}
v_reusejp_317_:
{
v___y_289_ = v___x_318_;
goto v___jp_288_;
}
}
}
default: 
{
lean_object* v___x_321_; 
v___x_321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_321_, 0, v_x_274_);
lean_ctor_set(v___x_321_, 1, v_x_275_);
v___y_289_ = v___x_321_;
goto v___jp_288_;
}
}
v___jp_288_:
{
lean_object* v___x_290_; lean_object* v___x_292_; 
v___x_290_ = lean_array_fset(v_xs_x27_287_, v_j_279_, v___y_289_);
lean_dec(v_j_279_);
if (v_isShared_284_ == 0)
{
lean_ctor_set(v___x_283_, 0, v___x_290_);
v___x_292_ = v___x_283_;
goto v_reusejp_291_;
}
else
{
lean_object* v_reuseFailAlloc_293_; 
v_reuseFailAlloc_293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_293_, 0, v___x_290_);
v___x_292_ = v_reuseFailAlloc_293_;
goto v_reusejp_291_;
}
v_reusejp_291_:
{
return v___x_292_;
}
}
}
}
}
else
{
lean_object* v_ks_324_; lean_object* v_vs_325_; lean_object* v___x_327_; uint8_t v_isShared_328_; uint8_t v_isSharedCheck_345_; 
v_ks_324_ = lean_ctor_get(v_x_271_, 0);
v_vs_325_ = lean_ctor_get(v_x_271_, 1);
v_isSharedCheck_345_ = !lean_is_exclusive(v_x_271_);
if (v_isSharedCheck_345_ == 0)
{
v___x_327_ = v_x_271_;
v_isShared_328_ = v_isSharedCheck_345_;
goto v_resetjp_326_;
}
else
{
lean_inc(v_vs_325_);
lean_inc(v_ks_324_);
lean_dec(v_x_271_);
v___x_327_ = lean_box(0);
v_isShared_328_ = v_isSharedCheck_345_;
goto v_resetjp_326_;
}
v_resetjp_326_:
{
lean_object* v___x_330_; 
if (v_isShared_328_ == 0)
{
v___x_330_ = v___x_327_;
goto v_reusejp_329_;
}
else
{
lean_object* v_reuseFailAlloc_344_; 
v_reuseFailAlloc_344_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_344_, 0, v_ks_324_);
lean_ctor_set(v_reuseFailAlloc_344_, 1, v_vs_325_);
v___x_330_ = v_reuseFailAlloc_344_;
goto v_reusejp_329_;
}
v_reusejp_329_:
{
lean_object* v_newNode_331_; uint8_t v___y_333_; size_t v___x_339_; uint8_t v___x_340_; 
v_newNode_331_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__1_spec__2_spec__4___redArg(v___x_330_, v_x_274_, v_x_275_);
v___x_339_ = ((size_t)7ULL);
v___x_340_ = lean_usize_dec_le(v___x_339_, v_x_273_);
if (v___x_340_ == 0)
{
lean_object* v___x_341_; lean_object* v___x_342_; uint8_t v___x_343_; 
v___x_341_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_331_);
v___x_342_ = lean_unsigned_to_nat(4u);
v___x_343_ = lean_nat_dec_lt(v___x_341_, v___x_342_);
lean_dec(v___x_341_);
v___y_333_ = v___x_343_;
goto v___jp_332_;
}
else
{
v___y_333_ = v___x_340_;
goto v___jp_332_;
}
v___jp_332_:
{
if (v___y_333_ == 0)
{
lean_object* v_ks_334_; lean_object* v_vs_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; 
v_ks_334_ = lean_ctor_get(v_newNode_331_, 0);
lean_inc_ref(v_ks_334_);
v_vs_335_ = lean_ctor_get(v_newNode_331_, 1);
lean_inc_ref(v_vs_335_);
lean_dec_ref(v_newNode_331_);
v___x_336_ = lean_unsigned_to_nat(0u);
v___x_337_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__1_spec__2___redArg___closed__0);
v___x_338_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__1_spec__2_spec__5___redArg(v_x_273_, v_ks_334_, v_vs_335_, v___x_336_, v___x_337_);
lean_dec_ref(v_vs_335_);
lean_dec_ref(v_ks_334_);
return v___x_338_;
}
else
{
return v_newNode_331_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__1_spec__2_spec__5___redArg(size_t v_depth_346_, lean_object* v_keys_347_, lean_object* v_vals_348_, lean_object* v_i_349_, lean_object* v_entries_350_){
_start:
{
lean_object* v___x_351_; uint8_t v___x_352_; 
v___x_351_ = lean_array_get_size(v_keys_347_);
v___x_352_ = lean_nat_dec_lt(v_i_349_, v___x_351_);
if (v___x_352_ == 0)
{
lean_dec(v_i_349_);
return v_entries_350_;
}
else
{
lean_object* v_k_353_; lean_object* v_v_354_; size_t v___x_355_; size_t v___x_356_; size_t v___x_357_; uint64_t v___x_358_; size_t v_h_359_; size_t v___x_360_; lean_object* v___x_361_; size_t v___x_362_; size_t v___x_363_; size_t v___x_364_; size_t v_h_365_; lean_object* v___x_366_; lean_object* v___x_367_; 
v_k_353_ = lean_array_fget_borrowed(v_keys_347_, v_i_349_);
v_v_354_ = lean_array_fget_borrowed(v_vals_348_, v_i_349_);
v___x_355_ = lean_ptr_addr(v_k_353_);
v___x_356_ = ((size_t)3ULL);
v___x_357_ = lean_usize_shift_right(v___x_355_, v___x_356_);
v___x_358_ = lean_usize_to_uint64(v___x_357_);
v_h_359_ = lean_uint64_to_usize(v___x_358_);
v___x_360_ = ((size_t)5ULL);
v___x_361_ = lean_unsigned_to_nat(1u);
v___x_362_ = ((size_t)1ULL);
v___x_363_ = lean_usize_sub(v_depth_346_, v___x_362_);
v___x_364_ = lean_usize_mul(v___x_360_, v___x_363_);
v_h_365_ = lean_usize_shift_right(v_h_359_, v___x_364_);
v___x_366_ = lean_nat_add(v_i_349_, v___x_361_);
lean_dec(v_i_349_);
lean_inc(v_v_354_);
lean_inc(v_k_353_);
v___x_367_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__1_spec__2___redArg(v_entries_350_, v_h_365_, v_depth_346_, v_k_353_, v_v_354_);
v_i_349_ = v___x_366_;
v_entries_350_ = v___x_367_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_depth_369_, lean_object* v_keys_370_, lean_object* v_vals_371_, lean_object* v_i_372_, lean_object* v_entries_373_){
_start:
{
size_t v_depth_boxed_374_; lean_object* v_res_375_; 
v_depth_boxed_374_ = lean_unbox_usize(v_depth_369_);
lean_dec(v_depth_369_);
v_res_375_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__1_spec__2_spec__5___redArg(v_depth_boxed_374_, v_keys_370_, v_vals_371_, v_i_372_, v_entries_373_);
lean_dec_ref(v_vals_371_);
lean_dec_ref(v_keys_370_);
return v_res_375_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__1_spec__2___redArg___boxed(lean_object* v_x_376_, lean_object* v_x_377_, lean_object* v_x_378_, lean_object* v_x_379_, lean_object* v_x_380_){
_start:
{
size_t v_x_4578__boxed_381_; size_t v_x_4579__boxed_382_; lean_object* v_res_383_; 
v_x_4578__boxed_381_ = lean_unbox_usize(v_x_377_);
lean_dec(v_x_377_);
v_x_4579__boxed_382_ = lean_unbox_usize(v_x_378_);
lean_dec(v_x_378_);
v_res_383_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__1_spec__2___redArg(v_x_376_, v_x_4578__boxed_381_, v_x_4579__boxed_382_, v_x_379_, v_x_380_);
return v_res_383_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__1___redArg(lean_object* v_x_384_, lean_object* v_x_385_, lean_object* v_x_386_){
_start:
{
size_t v___x_387_; size_t v___x_388_; size_t v___x_389_; uint64_t v___x_390_; size_t v___x_391_; size_t v___x_392_; lean_object* v___x_393_; 
v___x_387_ = lean_ptr_addr(v_x_385_);
v___x_388_ = ((size_t)3ULL);
v___x_389_ = lean_usize_shift_right(v___x_387_, v___x_388_);
v___x_390_ = lean_usize_to_uint64(v___x_389_);
v___x_391_ = lean_uint64_to_usize(v___x_390_);
v___x_392_ = ((size_t)1ULL);
v___x_393_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__1_spec__2___redArg(v_x_384_, v___x_391_, v___x_392_, v_x_385_, v_x_386_);
return v___x_393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getLawfulEqCmpThm_x3f___redArg(lean_object* v_op_394_, lean_object* v_a_395_, lean_object* v_a_396_, lean_object* v_a_397_, lean_object* v_a_398_, lean_object* v_a_399_){
_start:
{
lean_object* v___x_401_; lean_object* v_lawfulEqCmpMap_402_; lean_object* v___x_403_; 
v___x_401_ = lean_st_ref_get(v_a_395_);
v_lawfulEqCmpMap_402_ = lean_ctor_get(v___x_401_, 6);
lean_inc_ref(v_lawfulEqCmpMap_402_);
lean_dec(v___x_401_);
v___x_403_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__0___redArg(v_lawfulEqCmpMap_402_, v_op_394_);
lean_dec_ref(v_lawfulEqCmpMap_402_);
if (lean_obj_tag(v___x_403_) == 1)
{
lean_object* v_val_404_; lean_object* v___x_406_; uint8_t v_isShared_407_; uint8_t v_isSharedCheck_411_; 
lean_dec_ref(v_op_394_);
v_val_404_ = lean_ctor_get(v___x_403_, 0);
v_isSharedCheck_411_ = !lean_is_exclusive(v___x_403_);
if (v_isSharedCheck_411_ == 0)
{
v___x_406_ = v___x_403_;
v_isShared_407_ = v_isSharedCheck_411_;
goto v_resetjp_405_;
}
else
{
lean_inc(v_val_404_);
lean_dec(v___x_403_);
v___x_406_ = lean_box(0);
v_isShared_407_ = v_isSharedCheck_411_;
goto v_resetjp_405_;
}
v_resetjp_405_:
{
lean_object* v___x_409_; 
if (v_isShared_407_ == 0)
{
lean_ctor_set_tag(v___x_406_, 0);
v___x_409_ = v___x_406_;
goto v_reusejp_408_;
}
else
{
lean_object* v_reuseFailAlloc_410_; 
v_reuseFailAlloc_410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_410_, 0, v_val_404_);
v___x_409_ = v_reuseFailAlloc_410_;
goto v_reusejp_408_;
}
v_reusejp_408_:
{
return v___x_409_;
}
}
}
else
{
lean_object* v___x_412_; 
lean_dec(v___x_403_);
lean_inc_ref(v_op_394_);
v___x_412_ = l___private_Lean_Meta_Tactic_Grind_LawfulEqCmp_0__Lean_Meta_Grind_getLawfulEqCmpThm_x3f_go_x3f(v_op_394_, v_a_396_, v_a_397_, v_a_398_, v_a_399_);
if (lean_obj_tag(v___x_412_) == 0)
{
lean_object* v_a_413_; lean_object* v___x_415_; uint8_t v_isShared_416_; uint8_t v_isSharedCheck_440_; 
v_a_413_ = lean_ctor_get(v___x_412_, 0);
v_isSharedCheck_440_ = !lean_is_exclusive(v___x_412_);
if (v_isSharedCheck_440_ == 0)
{
v___x_415_ = v___x_412_;
v_isShared_416_ = v_isSharedCheck_440_;
goto v_resetjp_414_;
}
else
{
lean_inc(v_a_413_);
lean_dec(v___x_412_);
v___x_415_ = lean_box(0);
v_isShared_416_ = v_isSharedCheck_440_;
goto v_resetjp_414_;
}
v_resetjp_414_:
{
lean_object* v___x_417_; lean_object* v_congrThms_418_; lean_object* v_simp_419_; lean_object* v_lastTag_420_; lean_object* v_counters_421_; lean_object* v_splitDiags_422_; lean_object* v_ematchDiags_423_; lean_object* v_lawfulEqCmpMap_424_; lean_object* v_reflCmpMap_425_; lean_object* v_anchors_426_; lean_object* v_instanceMap_427_; lean_object* v___x_429_; uint8_t v_isShared_430_; uint8_t v_isSharedCheck_439_; 
v___x_417_ = lean_st_ref_take(v_a_395_);
v_congrThms_418_ = lean_ctor_get(v___x_417_, 0);
v_simp_419_ = lean_ctor_get(v___x_417_, 1);
v_lastTag_420_ = lean_ctor_get(v___x_417_, 2);
v_counters_421_ = lean_ctor_get(v___x_417_, 3);
v_splitDiags_422_ = lean_ctor_get(v___x_417_, 4);
v_ematchDiags_423_ = lean_ctor_get(v___x_417_, 5);
v_lawfulEqCmpMap_424_ = lean_ctor_get(v___x_417_, 6);
v_reflCmpMap_425_ = lean_ctor_get(v___x_417_, 7);
v_anchors_426_ = lean_ctor_get(v___x_417_, 8);
v_instanceMap_427_ = lean_ctor_get(v___x_417_, 9);
v_isSharedCheck_439_ = !lean_is_exclusive(v___x_417_);
if (v_isSharedCheck_439_ == 0)
{
v___x_429_ = v___x_417_;
v_isShared_430_ = v_isSharedCheck_439_;
goto v_resetjp_428_;
}
else
{
lean_inc(v_instanceMap_427_);
lean_inc(v_anchors_426_);
lean_inc(v_reflCmpMap_425_);
lean_inc(v_lawfulEqCmpMap_424_);
lean_inc(v_ematchDiags_423_);
lean_inc(v_splitDiags_422_);
lean_inc(v_counters_421_);
lean_inc(v_lastTag_420_);
lean_inc(v_simp_419_);
lean_inc(v_congrThms_418_);
lean_dec(v___x_417_);
v___x_429_ = lean_box(0);
v_isShared_430_ = v_isSharedCheck_439_;
goto v_resetjp_428_;
}
v_resetjp_428_:
{
lean_object* v___x_431_; lean_object* v___x_433_; 
lean_inc(v_a_413_);
v___x_431_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__1___redArg(v_lawfulEqCmpMap_424_, v_op_394_, v_a_413_);
if (v_isShared_430_ == 0)
{
lean_ctor_set(v___x_429_, 6, v___x_431_);
v___x_433_ = v___x_429_;
goto v_reusejp_432_;
}
else
{
lean_object* v_reuseFailAlloc_438_; 
v_reuseFailAlloc_438_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_438_, 0, v_congrThms_418_);
lean_ctor_set(v_reuseFailAlloc_438_, 1, v_simp_419_);
lean_ctor_set(v_reuseFailAlloc_438_, 2, v_lastTag_420_);
lean_ctor_set(v_reuseFailAlloc_438_, 3, v_counters_421_);
lean_ctor_set(v_reuseFailAlloc_438_, 4, v_splitDiags_422_);
lean_ctor_set(v_reuseFailAlloc_438_, 5, v_ematchDiags_423_);
lean_ctor_set(v_reuseFailAlloc_438_, 6, v___x_431_);
lean_ctor_set(v_reuseFailAlloc_438_, 7, v_reflCmpMap_425_);
lean_ctor_set(v_reuseFailAlloc_438_, 8, v_anchors_426_);
lean_ctor_set(v_reuseFailAlloc_438_, 9, v_instanceMap_427_);
v___x_433_ = v_reuseFailAlloc_438_;
goto v_reusejp_432_;
}
v_reusejp_432_:
{
lean_object* v___x_434_; lean_object* v___x_436_; 
v___x_434_ = lean_st_ref_set(v_a_395_, v___x_433_);
if (v_isShared_416_ == 0)
{
v___x_436_ = v___x_415_;
goto v_reusejp_435_;
}
else
{
lean_object* v_reuseFailAlloc_437_; 
v_reuseFailAlloc_437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_437_, 0, v_a_413_);
v___x_436_ = v_reuseFailAlloc_437_;
goto v_reusejp_435_;
}
v_reusejp_435_:
{
return v___x_436_;
}
}
}
}
}
else
{
lean_dec_ref(v_op_394_);
return v___x_412_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getLawfulEqCmpThm_x3f___redArg___boxed(lean_object* v_op_441_, lean_object* v_a_442_, lean_object* v_a_443_, lean_object* v_a_444_, lean_object* v_a_445_, lean_object* v_a_446_, lean_object* v_a_447_){
_start:
{
lean_object* v_res_448_; 
v_res_448_ = l_Lean_Meta_Grind_getLawfulEqCmpThm_x3f___redArg(v_op_441_, v_a_442_, v_a_443_, v_a_444_, v_a_445_, v_a_446_);
lean_dec(v_a_446_);
lean_dec_ref(v_a_445_);
lean_dec(v_a_444_);
lean_dec_ref(v_a_443_);
lean_dec(v_a_442_);
return v_res_448_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getLawfulEqCmpThm_x3f(lean_object* v_op_449_, lean_object* v_a_450_, lean_object* v_a_451_, lean_object* v_a_452_, lean_object* v_a_453_, lean_object* v_a_454_, lean_object* v_a_455_, lean_object* v_a_456_, lean_object* v_a_457_, lean_object* v_a_458_){
_start:
{
lean_object* v___x_460_; 
v___x_460_ = l_Lean_Meta_Grind_getLawfulEqCmpThm_x3f___redArg(v_op_449_, v_a_452_, v_a_455_, v_a_456_, v_a_457_, v_a_458_);
return v___x_460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getLawfulEqCmpThm_x3f___boxed(lean_object* v_op_461_, lean_object* v_a_462_, lean_object* v_a_463_, lean_object* v_a_464_, lean_object* v_a_465_, lean_object* v_a_466_, lean_object* v_a_467_, lean_object* v_a_468_, lean_object* v_a_469_, lean_object* v_a_470_, lean_object* v_a_471_){
_start:
{
lean_object* v_res_472_; 
v_res_472_ = l_Lean_Meta_Grind_getLawfulEqCmpThm_x3f(v_op_461_, v_a_462_, v_a_463_, v_a_464_, v_a_465_, v_a_466_, v_a_467_, v_a_468_, v_a_469_, v_a_470_);
lean_dec(v_a_470_);
lean_dec_ref(v_a_469_);
lean_dec(v_a_468_);
lean_dec_ref(v_a_467_);
lean_dec(v_a_466_);
lean_dec_ref(v_a_465_);
lean_dec(v_a_464_);
lean_dec_ref(v_a_463_);
lean_dec(v_a_462_);
return v_res_472_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__0(lean_object* v_00_u03b2_473_, lean_object* v_x_474_, lean_object* v_x_475_){
_start:
{
lean_object* v___x_476_; 
v___x_476_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__0___redArg(v_x_474_, v_x_475_);
return v___x_476_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__0___boxed(lean_object* v_00_u03b2_477_, lean_object* v_x_478_, lean_object* v_x_479_){
_start:
{
lean_object* v_res_480_; 
v_res_480_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__0(v_00_u03b2_477_, v_x_478_, v_x_479_);
lean_dec_ref(v_x_479_);
lean_dec_ref(v_x_478_);
return v_res_480_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__1(lean_object* v_00_u03b2_481_, lean_object* v_x_482_, lean_object* v_x_483_, lean_object* v_x_484_){
_start:
{
lean_object* v___x_485_; 
v___x_485_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__1___redArg(v_x_482_, v_x_483_, v_x_484_);
return v___x_485_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__0_spec__0(lean_object* v_00_u03b2_486_, lean_object* v_x_487_, size_t v_x_488_, lean_object* v_x_489_){
_start:
{
lean_object* v___x_490_; 
v___x_490_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__0_spec__0___redArg(v_x_487_, v_x_488_, v_x_489_);
return v___x_490_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_491_, lean_object* v_x_492_, lean_object* v_x_493_, lean_object* v_x_494_){
_start:
{
size_t v_x_4844__boxed_495_; lean_object* v_res_496_; 
v_x_4844__boxed_495_ = lean_unbox_usize(v_x_493_);
lean_dec(v_x_493_);
v_res_496_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__0_spec__0(v_00_u03b2_491_, v_x_492_, v_x_4844__boxed_495_, v_x_494_);
lean_dec_ref(v_x_494_);
lean_dec_ref(v_x_492_);
return v_res_496_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__1_spec__2(lean_object* v_00_u03b2_497_, lean_object* v_x_498_, size_t v_x_499_, size_t v_x_500_, lean_object* v_x_501_, lean_object* v_x_502_){
_start:
{
lean_object* v___x_503_; 
v___x_503_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__1_spec__2___redArg(v_x_498_, v_x_499_, v_x_500_, v_x_501_, v_x_502_);
return v___x_503_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__1_spec__2___boxed(lean_object* v_00_u03b2_504_, lean_object* v_x_505_, lean_object* v_x_506_, lean_object* v_x_507_, lean_object* v_x_508_, lean_object* v_x_509_){
_start:
{
size_t v_x_4855__boxed_510_; size_t v_x_4856__boxed_511_; lean_object* v_res_512_; 
v_x_4855__boxed_510_ = lean_unbox_usize(v_x_506_);
lean_dec(v_x_506_);
v_x_4856__boxed_511_ = lean_unbox_usize(v_x_507_);
lean_dec(v_x_507_);
v_res_512_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__1_spec__2(v_00_u03b2_504_, v_x_505_, v_x_4855__boxed_510_, v_x_4856__boxed_511_, v_x_508_, v_x_509_);
return v_res_512_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_513_, lean_object* v_keys_514_, lean_object* v_vals_515_, lean_object* v_heq_516_, lean_object* v_i_517_, lean_object* v_k_518_){
_start:
{
lean_object* v___x_519_; 
v___x_519_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__0_spec__0_spec__1___redArg(v_keys_514_, v_vals_515_, v_i_517_, v_k_518_);
return v___x_519_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_520_, lean_object* v_keys_521_, lean_object* v_vals_522_, lean_object* v_heq_523_, lean_object* v_i_524_, lean_object* v_k_525_){
_start:
{
lean_object* v_res_526_; 
v_res_526_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__0_spec__0_spec__1(v_00_u03b2_520_, v_keys_521_, v_vals_522_, v_heq_523_, v_i_524_, v_k_525_);
lean_dec_ref(v_k_525_);
lean_dec_ref(v_vals_522_);
lean_dec_ref(v_keys_521_);
return v_res_526_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_527_, lean_object* v_n_528_, lean_object* v_k_529_, lean_object* v_v_530_){
_start:
{
lean_object* v___x_531_; 
v___x_531_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__1_spec__2_spec__4___redArg(v_n_528_, v_k_529_, v_v_530_);
return v___x_531_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_532_, size_t v_depth_533_, lean_object* v_keys_534_, lean_object* v_vals_535_, lean_object* v_heq_536_, lean_object* v_i_537_, lean_object* v_entries_538_){
_start:
{
lean_object* v___x_539_; 
v___x_539_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__1_spec__2_spec__5___redArg(v_depth_533_, v_keys_534_, v_vals_535_, v_i_537_, v_entries_538_);
return v___x_539_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_540_, lean_object* v_depth_541_, lean_object* v_keys_542_, lean_object* v_vals_543_, lean_object* v_heq_544_, lean_object* v_i_545_, lean_object* v_entries_546_){
_start:
{
size_t v_depth_boxed_547_; lean_object* v_res_548_; 
v_depth_boxed_547_ = lean_unbox_usize(v_depth_541_);
lean_dec(v_depth_541_);
v_res_548_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__1_spec__2_spec__5(v_00_u03b2_540_, v_depth_boxed_547_, v_keys_542_, v_vals_543_, v_heq_544_, v_i_545_, v_entries_546_);
lean_dec_ref(v_vals_543_);
lean_dec_ref(v_keys_542_);
return v_res_548_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__1_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_549_, lean_object* v_x_550_, lean_object* v_x_551_, lean_object* v_x_552_, lean_object* v_x_553_){
_start:
{
lean_object* v___x_554_; 
v___x_554_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__1_spec__2_spec__4_spec__5___redArg(v_x_550_, v_x_551_, v_x_552_, v_x_553_);
return v___x_554_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateLawfulEqCmp(lean_object* v_e_555_, lean_object* v_a_556_, lean_object* v_a_557_, lean_object* v_a_558_, lean_object* v_a_559_, lean_object* v_a_560_, lean_object* v_a_561_, lean_object* v_a_562_, lean_object* v_a_563_, lean_object* v_a_564_, lean_object* v_a_565_){
_start:
{
lean_object* v___x_567_; 
v___x_567_ = l_Lean_Meta_Grind_getBinOp(v_e_555_);
if (lean_obj_tag(v___x_567_) == 1)
{
lean_object* v_val_568_; lean_object* v___x_569_; 
v_val_568_ = lean_ctor_get(v___x_567_, 0);
lean_inc(v_val_568_);
lean_dec_ref_known(v___x_567_, 1);
v___x_569_ = l_Lean_Meta_Grind_getLawfulEqCmpThm_x3f___redArg(v_val_568_, v_a_559_, v_a_562_, v_a_563_, v_a_564_, v_a_565_);
if (lean_obj_tag(v___x_569_) == 0)
{
lean_object* v_a_570_; lean_object* v___x_572_; uint8_t v_isShared_573_; uint8_t v_isSharedCheck_624_; 
v_a_570_ = lean_ctor_get(v___x_569_, 0);
v_isSharedCheck_624_ = !lean_is_exclusive(v___x_569_);
if (v_isSharedCheck_624_ == 0)
{
v___x_572_ = v___x_569_;
v_isShared_573_ = v_isSharedCheck_624_;
goto v_resetjp_571_;
}
else
{
lean_inc(v_a_570_);
lean_dec(v___x_569_);
v___x_572_ = lean_box(0);
v_isShared_573_ = v_isSharedCheck_624_;
goto v_resetjp_571_;
}
v_resetjp_571_:
{
if (lean_obj_tag(v_a_570_) == 1)
{
lean_object* v_val_574_; lean_object* v___x_575_; 
lean_del_object(v___x_572_);
v_val_574_ = lean_ctor_get(v_a_570_, 0);
lean_inc(v_val_574_);
lean_dec_ref_known(v_a_570_, 1);
v___x_575_ = l_Lean_Meta_Sym_getOrderingEqExpr___redArg(v_a_560_);
if (lean_obj_tag(v___x_575_) == 0)
{
lean_object* v_a_576_; lean_object* v___x_577_; 
v_a_576_ = lean_ctor_get(v___x_575_, 0);
lean_inc(v_a_576_);
lean_dec_ref_known(v___x_575_, 1);
v___x_577_ = l_Lean_Meta_Grind_isEqv___redArg(v_e_555_, v_a_576_, v_a_556_);
if (lean_obj_tag(v___x_577_) == 0)
{
lean_object* v_a_578_; lean_object* v___x_580_; uint8_t v_isShared_581_; uint8_t v_isSharedCheck_603_; 
v_a_578_ = lean_ctor_get(v___x_577_, 0);
v_isSharedCheck_603_ = !lean_is_exclusive(v___x_577_);
if (v_isSharedCheck_603_ == 0)
{
v___x_580_ = v___x_577_;
v_isShared_581_ = v_isSharedCheck_603_;
goto v_resetjp_579_;
}
else
{
lean_inc(v_a_578_);
lean_dec(v___x_577_);
v___x_580_ = lean_box(0);
v_isShared_581_ = v_isSharedCheck_603_;
goto v_resetjp_579_;
}
v_resetjp_579_:
{
uint8_t v___x_582_; 
v___x_582_ = lean_unbox(v_a_578_);
lean_dec(v_a_578_);
if (v___x_582_ == 0)
{
lean_object* v___x_583_; lean_object* v___x_585_; 
lean_dec(v_a_576_);
lean_dec(v_val_574_);
lean_dec_ref(v_e_555_);
v___x_583_ = lean_box(0);
if (v_isShared_581_ == 0)
{
lean_ctor_set(v___x_580_, 0, v___x_583_);
v___x_585_ = v___x_580_;
goto v_reusejp_584_;
}
else
{
lean_object* v_reuseFailAlloc_586_; 
v_reuseFailAlloc_586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_586_, 0, v___x_583_);
v___x_585_ = v_reuseFailAlloc_586_;
goto v_reusejp_584_;
}
v_reusejp_584_:
{
return v___x_585_;
}
}
else
{
lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; 
lean_del_object(v___x_580_);
v___x_587_ = l_Lean_Expr_appFn_x21(v_e_555_);
v___x_588_ = l_Lean_Expr_appArg_x21(v_e_555_);
lean_inc(v_a_565_);
lean_inc_ref(v_a_564_);
lean_inc(v_a_563_);
lean_inc_ref(v_a_562_);
lean_inc(v_a_561_);
lean_inc_ref(v_a_560_);
lean_inc(v_a_559_);
lean_inc_ref(v_a_558_);
lean_inc(v_a_557_);
lean_inc(v_a_556_);
v___x_589_ = lean_grind_mk_eq_proof(v_e_555_, v_a_576_, v_a_556_, v_a_557_, v_a_558_, v_a_559_, v_a_560_, v_a_561_, v_a_562_, v_a_563_, v_a_564_, v_a_565_);
if (lean_obj_tag(v___x_589_) == 0)
{
lean_object* v_a_590_; lean_object* v___x_591_; lean_object* v___x_592_; uint8_t v___x_593_; lean_object* v___x_594_; 
v_a_590_ = lean_ctor_get(v___x_589_, 0);
lean_inc(v_a_590_);
lean_dec_ref_known(v___x_589_, 1);
v___x_591_ = l_Lean_Expr_appArg_x21(v___x_587_);
lean_dec_ref(v___x_587_);
lean_inc_ref(v___x_588_);
lean_inc_ref(v___x_591_);
v___x_592_ = l_Lean_mkApp3(v_val_574_, v___x_591_, v___x_588_, v_a_590_);
v___x_593_ = 0;
v___x_594_ = l_Lean_Meta_Grind_pushEqCore___redArg(v___x_591_, v___x_588_, v___x_592_, v___x_593_, v_a_556_, v_a_558_, v_a_562_, v_a_563_, v_a_564_, v_a_565_);
return v___x_594_;
}
else
{
lean_object* v_a_595_; lean_object* v___x_597_; uint8_t v_isShared_598_; uint8_t v_isSharedCheck_602_; 
lean_dec_ref(v___x_588_);
lean_dec_ref(v___x_587_);
lean_dec(v_val_574_);
v_a_595_ = lean_ctor_get(v___x_589_, 0);
v_isSharedCheck_602_ = !lean_is_exclusive(v___x_589_);
if (v_isSharedCheck_602_ == 0)
{
v___x_597_ = v___x_589_;
v_isShared_598_ = v_isSharedCheck_602_;
goto v_resetjp_596_;
}
else
{
lean_inc(v_a_595_);
lean_dec(v___x_589_);
v___x_597_ = lean_box(0);
v_isShared_598_ = v_isSharedCheck_602_;
goto v_resetjp_596_;
}
v_resetjp_596_:
{
lean_object* v___x_600_; 
if (v_isShared_598_ == 0)
{
v___x_600_ = v___x_597_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_601_; 
v_reuseFailAlloc_601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_601_, 0, v_a_595_);
v___x_600_ = v_reuseFailAlloc_601_;
goto v_reusejp_599_;
}
v_reusejp_599_:
{
return v___x_600_;
}
}
}
}
}
}
else
{
lean_object* v_a_604_; lean_object* v___x_606_; uint8_t v_isShared_607_; uint8_t v_isSharedCheck_611_; 
lean_dec(v_a_576_);
lean_dec(v_val_574_);
lean_dec_ref(v_e_555_);
v_a_604_ = lean_ctor_get(v___x_577_, 0);
v_isSharedCheck_611_ = !lean_is_exclusive(v___x_577_);
if (v_isSharedCheck_611_ == 0)
{
v___x_606_ = v___x_577_;
v_isShared_607_ = v_isSharedCheck_611_;
goto v_resetjp_605_;
}
else
{
lean_inc(v_a_604_);
lean_dec(v___x_577_);
v___x_606_ = lean_box(0);
v_isShared_607_ = v_isSharedCheck_611_;
goto v_resetjp_605_;
}
v_resetjp_605_:
{
lean_object* v___x_609_; 
if (v_isShared_607_ == 0)
{
v___x_609_ = v___x_606_;
goto v_reusejp_608_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v_a_604_);
v___x_609_ = v_reuseFailAlloc_610_;
goto v_reusejp_608_;
}
v_reusejp_608_:
{
return v___x_609_;
}
}
}
}
else
{
lean_object* v_a_612_; lean_object* v___x_614_; uint8_t v_isShared_615_; uint8_t v_isSharedCheck_619_; 
lean_dec(v_val_574_);
lean_dec_ref(v_e_555_);
v_a_612_ = lean_ctor_get(v___x_575_, 0);
v_isSharedCheck_619_ = !lean_is_exclusive(v___x_575_);
if (v_isSharedCheck_619_ == 0)
{
v___x_614_ = v___x_575_;
v_isShared_615_ = v_isSharedCheck_619_;
goto v_resetjp_613_;
}
else
{
lean_inc(v_a_612_);
lean_dec(v___x_575_);
v___x_614_ = lean_box(0);
v_isShared_615_ = v_isSharedCheck_619_;
goto v_resetjp_613_;
}
v_resetjp_613_:
{
lean_object* v___x_617_; 
if (v_isShared_615_ == 0)
{
v___x_617_ = v___x_614_;
goto v_reusejp_616_;
}
else
{
lean_object* v_reuseFailAlloc_618_; 
v_reuseFailAlloc_618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_618_, 0, v_a_612_);
v___x_617_ = v_reuseFailAlloc_618_;
goto v_reusejp_616_;
}
v_reusejp_616_:
{
return v___x_617_;
}
}
}
}
else
{
lean_object* v___x_620_; lean_object* v___x_622_; 
lean_dec(v_a_570_);
lean_dec_ref(v_e_555_);
v___x_620_ = lean_box(0);
if (v_isShared_573_ == 0)
{
lean_ctor_set(v___x_572_, 0, v___x_620_);
v___x_622_ = v___x_572_;
goto v_reusejp_621_;
}
else
{
lean_object* v_reuseFailAlloc_623_; 
v_reuseFailAlloc_623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_623_, 0, v___x_620_);
v___x_622_ = v_reuseFailAlloc_623_;
goto v_reusejp_621_;
}
v_reusejp_621_:
{
return v___x_622_;
}
}
}
}
else
{
lean_object* v_a_625_; lean_object* v___x_627_; uint8_t v_isShared_628_; uint8_t v_isSharedCheck_632_; 
lean_dec_ref(v_e_555_);
v_a_625_ = lean_ctor_get(v___x_569_, 0);
v_isSharedCheck_632_ = !lean_is_exclusive(v___x_569_);
if (v_isSharedCheck_632_ == 0)
{
v___x_627_ = v___x_569_;
v_isShared_628_ = v_isSharedCheck_632_;
goto v_resetjp_626_;
}
else
{
lean_inc(v_a_625_);
lean_dec(v___x_569_);
v___x_627_ = lean_box(0);
v_isShared_628_ = v_isSharedCheck_632_;
goto v_resetjp_626_;
}
v_resetjp_626_:
{
lean_object* v___x_630_; 
if (v_isShared_628_ == 0)
{
v___x_630_ = v___x_627_;
goto v_reusejp_629_;
}
else
{
lean_object* v_reuseFailAlloc_631_; 
v_reuseFailAlloc_631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_631_, 0, v_a_625_);
v___x_630_ = v_reuseFailAlloc_631_;
goto v_reusejp_629_;
}
v_reusejp_629_:
{
return v___x_630_;
}
}
}
}
else
{
lean_object* v___x_633_; lean_object* v___x_634_; 
lean_dec(v___x_567_);
lean_dec_ref(v_e_555_);
v___x_633_ = lean_box(0);
v___x_634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_634_, 0, v___x_633_);
return v___x_634_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateLawfulEqCmp___boxed(lean_object* v_e_635_, lean_object* v_a_636_, lean_object* v_a_637_, lean_object* v_a_638_, lean_object* v_a_639_, lean_object* v_a_640_, lean_object* v_a_641_, lean_object* v_a_642_, lean_object* v_a_643_, lean_object* v_a_644_, lean_object* v_a_645_, lean_object* v_a_646_){
_start:
{
lean_object* v_res_647_; 
v_res_647_ = l_Lean_Meta_Grind_propagateLawfulEqCmp(v_e_635_, v_a_636_, v_a_637_, v_a_638_, v_a_639_, v_a_640_, v_a_641_, v_a_642_, v_a_643_, v_a_644_, v_a_645_);
lean_dec(v_a_645_);
lean_dec_ref(v_a_644_);
lean_dec(v_a_643_);
lean_dec_ref(v_a_642_);
lean_dec(v_a_641_);
lean_dec_ref(v_a_640_);
lean_dec(v_a_639_);
lean_dec_ref(v_a_638_);
lean_dec(v_a_637_);
lean_dec(v_a_636_);
return v_res_647_;
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
