// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.PropagateInj
// Imports: public import Lean.Meta.Tactic.Grind.Types import Init.Grind.Propagator import Init.Grind.Injective import Lean.Meta.Tactic.Grind.PropagatorAttr import Lean.Meta.Tactic.Grind.Simp
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
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_HeadIndex_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
uint8_t l_Lean_instBEqHeadIndex_beq(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
uint64_t l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_instInhabitedGoalM(lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_preprocessLight(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getGeneration___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_pushEqCore___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_grind_internalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Expr_toHeadIndex(lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Meta_Grind_mkEqTrueProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
lean_object* l_Lean_Meta_mkOfEqTrueCore(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isEqTrue___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_eta(lean_object*);
lean_object* l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__0___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3_spec__5_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3_spec__5___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3_spec__6___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2___redArg(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "Lean.Meta.Tactic.Grind.PropagateInj"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 74, .m_capacity = 74, .m_length = 73, .m_data = "_private.Lean.Meta.Tactic.Grind.PropagateInj.0.Lean.Meta.Grind.getInvFor\?"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__3;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Nonempty"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__4_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "intro"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__5_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(142, 191, 110, 220, 210, 100, 152, 183)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__5_value),LEAN_SCALAR_PTR_LITERAL(113, 209, 180, 93, 84, 117, 67, 110)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__6_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__7_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__8_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "leftInv"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__9_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__7_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__10_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__8_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__10_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__9_value),LEAN_SCALAR_PTR_LITERAL(125, 193, 128, 144, 122, 197, 27, 63)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__10_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__11;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "leftInv_eq"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__12_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__7_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__13_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__8_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__13_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__12_value),LEAN_SCALAR_PTR_LITERAL(247, 98, 181, 128, 57, 3, 90, 161)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__13_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3_spec__6(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_mkInjEq_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_mkInjEq_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_mkInjEq_spec__0___redArg___closed__0_value;
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_mkInjEq_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_mkInjEq_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_mkInjEq_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_mkInjEq_spec__0___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_mkInjEq_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_mkInjEq_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_mkInjEq_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_mkInjEq_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__1___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__1___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__1___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__1___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_mkInjEq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "grind"};
static const lean_object* l_Lean_Meta_Grind_mkInjEq___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_mkInjEq___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_mkInjEq___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "inj"};
static const lean_object* l_Lean_Meta_Grind_mkInjEq___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_mkInjEq___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_mkInjEq___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "assert"};
static const lean_object* l_Lean_Meta_Grind_mkInjEq___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_mkInjEq___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Grind_mkInjEq___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_mkInjEq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l_Lean_Meta_Grind_mkInjEq___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_mkInjEq___closed__3_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_mkInjEq___closed__1_value),LEAN_SCALAR_PTR_LITERAL(178, 139, 26, 158, 27, 86, 65, 26)}};
static const lean_ctor_object l_Lean_Meta_Grind_mkInjEq___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_mkInjEq___closed__3_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_mkInjEq___closed__2_value),LEAN_SCALAR_PTR_LITERAL(212, 213, 49, 65, 20, 205, 188, 235)}};
static const lean_object* l_Lean_Meta_Grind_mkInjEq___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_mkInjEq___closed__3_value;
static const lean_string_object l_Lean_Meta_Grind_mkInjEq___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l_Lean_Meta_Grind_mkInjEq___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_mkInjEq___closed__4_value;
static lean_once_cell_t l_Lean_Meta_Grind_mkInjEq___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_mkInjEq___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkInjEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkInjEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Function"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Injective"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj___closed__0_value),LEAN_SCALAR_PTR_LITERAL(225, 8, 186, 189, 152, 89, 197, 12)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj___closed__1_value),LEAN_SCALAR_PTR_LITERAL(52, 162, 25, 76, 92, 227, 14, 201)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj___regBuiltin___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj_declare__1_00___x40_Lean_Meta_Tactic_Grind_PropagateInj_3930705876____hygCtx___hyg_8_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj___regBuiltin___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj_declare__1_00___x40_Lean_Meta_Tactic_Grind_PropagateInj_3930705876____hygCtx___hyg_8____boxed(lean_object*);
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = l_Lean_Meta_Grind_instInhabitedGoalM(lean_box(0));
return v___x_1_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__0(lean_object* v_msg_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_, lean_object* v___y_7_, lean_object* v___y_8_, lean_object* v___y_9_, lean_object* v___y_10_, lean_object* v___y_11_, lean_object* v___y_12_){
_start:
{
lean_object* v___x_14_; lean_object* v___x_9850__overap_15_; lean_object* v___x_16_; 
v___x_14_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__0___closed__0, &l_panic___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__0___closed__0);
v___x_9850__overap_15_ = lean_panic_fn(v___x_14_, v_msg_2_);
v___x_16_ = lean_apply_11(v___x_9850__overap_15_, v___y_3_, v___y_4_, v___y_5_, v___y_6_, v___y_7_, v___y_8_, v___y_9_, v___y_10_, v___y_11_, v___y_12_, lean_box(0));
return v___x_16_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__0___boxed(lean_object* v_msg_17_, lean_object* v___y_18_, lean_object* v___y_19_, lean_object* v___y_20_, lean_object* v___y_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_, lean_object* v___y_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__0(v_msg_17_, v___y_18_, v___y_19_, v___y_20_, v___y_21_, v___y_22_, v___y_23_, v___y_24_, v___y_25_, v___y_26_, v___y_27_);
return v_res_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1_spec__2___redArg(lean_object* v_keys_30_, lean_object* v_vals_31_, lean_object* v_i_32_, lean_object* v_k_33_){
_start:
{
lean_object* v___x_34_; uint8_t v___x_35_; 
v___x_34_ = lean_array_get_size(v_keys_30_);
v___x_35_ = lean_nat_dec_lt(v_i_32_, v___x_34_);
if (v___x_35_ == 0)
{
lean_object* v___x_36_; 
lean_dec(v_i_32_);
v___x_36_ = lean_box(0);
return v___x_36_;
}
else
{
lean_object* v_k_x27_37_; uint8_t v___x_38_; 
v_k_x27_37_ = lean_array_fget_borrowed(v_keys_30_, v_i_32_);
v___x_38_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_k_33_, v_k_x27_37_);
if (v___x_38_ == 0)
{
lean_object* v___x_39_; lean_object* v___x_40_; 
v___x_39_ = lean_unsigned_to_nat(1u);
v___x_40_ = lean_nat_add(v_i_32_, v___x_39_);
lean_dec(v_i_32_);
v_i_32_ = v___x_40_;
goto _start;
}
else
{
lean_object* v___x_42_; lean_object* v___x_43_; 
v___x_42_ = lean_array_fget_borrowed(v_vals_31_, v_i_32_);
lean_dec(v_i_32_);
lean_inc(v___x_42_);
v___x_43_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_43_, 0, v___x_42_);
return v___x_43_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_keys_44_, lean_object* v_vals_45_, lean_object* v_i_46_, lean_object* v_k_47_){
_start:
{
lean_object* v_res_48_; 
v_res_48_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1_spec__2___redArg(v_keys_44_, v_vals_45_, v_i_46_, v_k_47_);
lean_dec_ref(v_k_47_);
lean_dec_ref(v_vals_45_);
lean_dec_ref(v_keys_44_);
return v_res_48_;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1___redArg___closed__0(void){
_start:
{
size_t v___x_49_; size_t v___x_50_; size_t v___x_51_; 
v___x_49_ = ((size_t)5ULL);
v___x_50_ = ((size_t)1ULL);
v___x_51_ = lean_usize_shift_left(v___x_50_, v___x_49_);
return v___x_51_;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_52_; size_t v___x_53_; size_t v___x_54_; 
v___x_52_ = ((size_t)1ULL);
v___x_53_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1___redArg___closed__0);
v___x_54_ = lean_usize_sub(v___x_53_, v___x_52_);
return v___x_54_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1___redArg(lean_object* v_x_55_, size_t v_x_56_, lean_object* v_x_57_){
_start:
{
if (lean_obj_tag(v_x_55_) == 0)
{
lean_object* v_es_58_; lean_object* v___x_60_; uint8_t v_isShared_61_; uint8_t v_isSharedCheck_79_; 
v_es_58_ = lean_ctor_get(v_x_55_, 0);
v_isSharedCheck_79_ = !lean_is_exclusive(v_x_55_);
if (v_isSharedCheck_79_ == 0)
{
v___x_60_ = v_x_55_;
v_isShared_61_ = v_isSharedCheck_79_;
goto v_resetjp_59_;
}
else
{
lean_inc(v_es_58_);
lean_dec(v_x_55_);
v___x_60_ = lean_box(0);
v_isShared_61_ = v_isSharedCheck_79_;
goto v_resetjp_59_;
}
v_resetjp_59_:
{
lean_object* v___x_62_; size_t v___x_63_; size_t v___x_64_; size_t v___x_65_; lean_object* v_j_66_; lean_object* v___x_67_; 
v___x_62_ = lean_box(2);
v___x_63_ = ((size_t)5ULL);
v___x_64_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1___redArg___closed__1);
v___x_65_ = lean_usize_land(v_x_56_, v___x_64_);
v_j_66_ = lean_usize_to_nat(v___x_65_);
v___x_67_ = lean_array_get(v___x_62_, v_es_58_, v_j_66_);
lean_dec(v_j_66_);
lean_dec_ref(v_es_58_);
switch(lean_obj_tag(v___x_67_))
{
case 0:
{
lean_object* v_key_68_; lean_object* v_val_69_; uint8_t v___x_70_; 
v_key_68_ = lean_ctor_get(v___x_67_, 0);
lean_inc(v_key_68_);
v_val_69_ = lean_ctor_get(v___x_67_, 1);
lean_inc(v_val_69_);
lean_dec_ref(v___x_67_);
v___x_70_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_57_, v_key_68_);
lean_dec(v_key_68_);
if (v___x_70_ == 0)
{
lean_object* v___x_71_; 
lean_dec(v_val_69_);
lean_del_object(v___x_60_);
v___x_71_ = lean_box(0);
return v___x_71_;
}
else
{
lean_object* v___x_73_; 
if (v_isShared_61_ == 0)
{
lean_ctor_set_tag(v___x_60_, 1);
lean_ctor_set(v___x_60_, 0, v_val_69_);
v___x_73_ = v___x_60_;
goto v_reusejp_72_;
}
else
{
lean_object* v_reuseFailAlloc_74_; 
v_reuseFailAlloc_74_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_74_, 0, v_val_69_);
v___x_73_ = v_reuseFailAlloc_74_;
goto v_reusejp_72_;
}
v_reusejp_72_:
{
return v___x_73_;
}
}
}
case 1:
{
lean_object* v_node_75_; size_t v___x_76_; 
lean_del_object(v___x_60_);
v_node_75_ = lean_ctor_get(v___x_67_, 0);
lean_inc(v_node_75_);
lean_dec_ref(v___x_67_);
v___x_76_ = lean_usize_shift_right(v_x_56_, v___x_63_);
v_x_55_ = v_node_75_;
v_x_56_ = v___x_76_;
goto _start;
}
default: 
{
lean_object* v___x_78_; 
lean_del_object(v___x_60_);
v___x_78_ = lean_box(0);
return v___x_78_;
}
}
}
}
else
{
lean_object* v_ks_80_; lean_object* v_vs_81_; lean_object* v___x_82_; lean_object* v___x_83_; 
v_ks_80_ = lean_ctor_get(v_x_55_, 0);
lean_inc_ref(v_ks_80_);
v_vs_81_ = lean_ctor_get(v_x_55_, 1);
lean_inc_ref(v_vs_81_);
lean_dec_ref(v_x_55_);
v___x_82_ = lean_unsigned_to_nat(0u);
v___x_83_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1_spec__2___redArg(v_ks_80_, v_vs_81_, v___x_82_, v_x_57_);
lean_dec_ref(v_vs_81_);
lean_dec_ref(v_ks_80_);
return v___x_83_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1___redArg___boxed(lean_object* v_x_84_, lean_object* v_x_85_, lean_object* v_x_86_){
_start:
{
size_t v_x_10332__boxed_87_; lean_object* v_res_88_; 
v_x_10332__boxed_87_ = lean_unbox_usize(v_x_85_);
lean_dec(v_x_85_);
v_res_88_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1___redArg(v_x_84_, v_x_10332__boxed_87_, v_x_86_);
lean_dec_ref(v_x_86_);
return v_res_88_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1___redArg(lean_object* v_x_89_, lean_object* v_x_90_){
_start:
{
uint64_t v___x_91_; size_t v___x_92_; lean_object* v___x_93_; 
v___x_91_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_90_);
v___x_92_ = lean_uint64_to_usize(v___x_91_);
v___x_93_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1___redArg(v_x_89_, v___x_92_, v_x_90_);
return v___x_93_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1___redArg___boxed(lean_object* v_x_94_, lean_object* v_x_95_){
_start:
{
lean_object* v_res_96_; 
v_res_96_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1___redArg(v_x_94_, v_x_95_);
lean_dec_ref(v_x_95_);
return v_res_96_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3_spec__5_spec__6___redArg(lean_object* v_x_97_, lean_object* v_x_98_, lean_object* v_x_99_, lean_object* v_x_100_){
_start:
{
lean_object* v_ks_101_; lean_object* v_vs_102_; lean_object* v___x_104_; uint8_t v_isShared_105_; uint8_t v_isSharedCheck_126_; 
v_ks_101_ = lean_ctor_get(v_x_97_, 0);
v_vs_102_ = lean_ctor_get(v_x_97_, 1);
v_isSharedCheck_126_ = !lean_is_exclusive(v_x_97_);
if (v_isSharedCheck_126_ == 0)
{
v___x_104_ = v_x_97_;
v_isShared_105_ = v_isSharedCheck_126_;
goto v_resetjp_103_;
}
else
{
lean_inc(v_vs_102_);
lean_inc(v_ks_101_);
lean_dec(v_x_97_);
v___x_104_ = lean_box(0);
v_isShared_105_ = v_isSharedCheck_126_;
goto v_resetjp_103_;
}
v_resetjp_103_:
{
lean_object* v___x_106_; uint8_t v___x_107_; 
v___x_106_ = lean_array_get_size(v_ks_101_);
v___x_107_ = lean_nat_dec_lt(v_x_98_, v___x_106_);
if (v___x_107_ == 0)
{
lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_111_; 
lean_dec(v_x_98_);
v___x_108_ = lean_array_push(v_ks_101_, v_x_99_);
v___x_109_ = lean_array_push(v_vs_102_, v_x_100_);
if (v_isShared_105_ == 0)
{
lean_ctor_set(v___x_104_, 1, v___x_109_);
lean_ctor_set(v___x_104_, 0, v___x_108_);
v___x_111_ = v___x_104_;
goto v_reusejp_110_;
}
else
{
lean_object* v_reuseFailAlloc_112_; 
v_reuseFailAlloc_112_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_112_, 0, v___x_108_);
lean_ctor_set(v_reuseFailAlloc_112_, 1, v___x_109_);
v___x_111_ = v_reuseFailAlloc_112_;
goto v_reusejp_110_;
}
v_reusejp_110_:
{
return v___x_111_;
}
}
else
{
lean_object* v_k_x27_113_; uint8_t v___x_114_; 
v_k_x27_113_ = lean_array_fget_borrowed(v_ks_101_, v_x_98_);
v___x_114_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_99_, v_k_x27_113_);
if (v___x_114_ == 0)
{
lean_object* v___x_116_; 
if (v_isShared_105_ == 0)
{
v___x_116_ = v___x_104_;
goto v_reusejp_115_;
}
else
{
lean_object* v_reuseFailAlloc_120_; 
v_reuseFailAlloc_120_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_120_, 0, v_ks_101_);
lean_ctor_set(v_reuseFailAlloc_120_, 1, v_vs_102_);
v___x_116_ = v_reuseFailAlloc_120_;
goto v_reusejp_115_;
}
v_reusejp_115_:
{
lean_object* v___x_117_; lean_object* v___x_118_; 
v___x_117_ = lean_unsigned_to_nat(1u);
v___x_118_ = lean_nat_add(v_x_98_, v___x_117_);
lean_dec(v_x_98_);
v_x_97_ = v___x_116_;
v_x_98_ = v___x_118_;
goto _start;
}
}
else
{
lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_124_; 
v___x_121_ = lean_array_fset(v_ks_101_, v_x_98_, v_x_99_);
v___x_122_ = lean_array_fset(v_vs_102_, v_x_98_, v_x_100_);
lean_dec(v_x_98_);
if (v_isShared_105_ == 0)
{
lean_ctor_set(v___x_104_, 1, v___x_122_);
lean_ctor_set(v___x_104_, 0, v___x_121_);
v___x_124_ = v___x_104_;
goto v_reusejp_123_;
}
else
{
lean_object* v_reuseFailAlloc_125_; 
v_reuseFailAlloc_125_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_125_, 0, v___x_121_);
lean_ctor_set(v_reuseFailAlloc_125_, 1, v___x_122_);
v___x_124_ = v_reuseFailAlloc_125_;
goto v_reusejp_123_;
}
v_reusejp_123_:
{
return v___x_124_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3_spec__5___redArg(lean_object* v_n_127_, lean_object* v_k_128_, lean_object* v_v_129_){
_start:
{
lean_object* v___x_130_; lean_object* v___x_131_; 
v___x_130_ = lean_unsigned_to_nat(0u);
v___x_131_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3_spec__5_spec__6___redArg(v_n_127_, v___x_130_, v_k_128_, v_v_129_);
return v___x_131_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_132_; 
v___x_132_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_132_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3___redArg(lean_object* v_x_133_, size_t v_x_134_, size_t v_x_135_, lean_object* v_x_136_, lean_object* v_x_137_){
_start:
{
if (lean_obj_tag(v_x_133_) == 0)
{
lean_object* v_es_138_; size_t v___x_139_; size_t v___x_140_; size_t v___x_141_; size_t v___x_142_; lean_object* v_j_143_; lean_object* v___x_144_; uint8_t v___x_145_; 
v_es_138_ = lean_ctor_get(v_x_133_, 0);
v___x_139_ = ((size_t)5ULL);
v___x_140_ = ((size_t)1ULL);
v___x_141_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1___redArg___closed__1);
v___x_142_ = lean_usize_land(v_x_134_, v___x_141_);
v_j_143_ = lean_usize_to_nat(v___x_142_);
v___x_144_ = lean_array_get_size(v_es_138_);
v___x_145_ = lean_nat_dec_lt(v_j_143_, v___x_144_);
if (v___x_145_ == 0)
{
lean_dec(v_j_143_);
lean_dec(v_x_137_);
lean_dec_ref(v_x_136_);
return v_x_133_;
}
else
{
lean_object* v___x_147_; uint8_t v_isShared_148_; uint8_t v_isSharedCheck_182_; 
lean_inc_ref(v_es_138_);
v_isSharedCheck_182_ = !lean_is_exclusive(v_x_133_);
if (v_isSharedCheck_182_ == 0)
{
lean_object* v_unused_183_; 
v_unused_183_ = lean_ctor_get(v_x_133_, 0);
lean_dec(v_unused_183_);
v___x_147_ = v_x_133_;
v_isShared_148_ = v_isSharedCheck_182_;
goto v_resetjp_146_;
}
else
{
lean_dec(v_x_133_);
v___x_147_ = lean_box(0);
v_isShared_148_ = v_isSharedCheck_182_;
goto v_resetjp_146_;
}
v_resetjp_146_:
{
lean_object* v_v_149_; lean_object* v___x_150_; lean_object* v_xs_x27_151_; lean_object* v___y_153_; 
v_v_149_ = lean_array_fget(v_es_138_, v_j_143_);
v___x_150_ = lean_box(0);
v_xs_x27_151_ = lean_array_fset(v_es_138_, v_j_143_, v___x_150_);
switch(lean_obj_tag(v_v_149_))
{
case 0:
{
lean_object* v_key_158_; lean_object* v_val_159_; lean_object* v___x_161_; uint8_t v_isShared_162_; uint8_t v_isSharedCheck_169_; 
v_key_158_ = lean_ctor_get(v_v_149_, 0);
v_val_159_ = lean_ctor_get(v_v_149_, 1);
v_isSharedCheck_169_ = !lean_is_exclusive(v_v_149_);
if (v_isSharedCheck_169_ == 0)
{
v___x_161_ = v_v_149_;
v_isShared_162_ = v_isSharedCheck_169_;
goto v_resetjp_160_;
}
else
{
lean_inc(v_val_159_);
lean_inc(v_key_158_);
lean_dec(v_v_149_);
v___x_161_ = lean_box(0);
v_isShared_162_ = v_isSharedCheck_169_;
goto v_resetjp_160_;
}
v_resetjp_160_:
{
uint8_t v___x_163_; 
v___x_163_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_136_, v_key_158_);
if (v___x_163_ == 0)
{
lean_object* v___x_164_; lean_object* v___x_165_; 
lean_del_object(v___x_161_);
v___x_164_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_158_, v_val_159_, v_x_136_, v_x_137_);
v___x_165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_165_, 0, v___x_164_);
v___y_153_ = v___x_165_;
goto v___jp_152_;
}
else
{
lean_object* v___x_167_; 
lean_dec(v_val_159_);
lean_dec(v_key_158_);
if (v_isShared_162_ == 0)
{
lean_ctor_set(v___x_161_, 1, v_x_137_);
lean_ctor_set(v___x_161_, 0, v_x_136_);
v___x_167_ = v___x_161_;
goto v_reusejp_166_;
}
else
{
lean_object* v_reuseFailAlloc_168_; 
v_reuseFailAlloc_168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_168_, 0, v_x_136_);
lean_ctor_set(v_reuseFailAlloc_168_, 1, v_x_137_);
v___x_167_ = v_reuseFailAlloc_168_;
goto v_reusejp_166_;
}
v_reusejp_166_:
{
v___y_153_ = v___x_167_;
goto v___jp_152_;
}
}
}
}
case 1:
{
lean_object* v_node_170_; lean_object* v___x_172_; uint8_t v_isShared_173_; uint8_t v_isSharedCheck_180_; 
v_node_170_ = lean_ctor_get(v_v_149_, 0);
v_isSharedCheck_180_ = !lean_is_exclusive(v_v_149_);
if (v_isSharedCheck_180_ == 0)
{
v___x_172_ = v_v_149_;
v_isShared_173_ = v_isSharedCheck_180_;
goto v_resetjp_171_;
}
else
{
lean_inc(v_node_170_);
lean_dec(v_v_149_);
v___x_172_ = lean_box(0);
v_isShared_173_ = v_isSharedCheck_180_;
goto v_resetjp_171_;
}
v_resetjp_171_:
{
size_t v___x_174_; size_t v___x_175_; lean_object* v___x_176_; lean_object* v___x_178_; 
v___x_174_ = lean_usize_shift_right(v_x_134_, v___x_139_);
v___x_175_ = lean_usize_add(v_x_135_, v___x_140_);
v___x_176_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3___redArg(v_node_170_, v___x_174_, v___x_175_, v_x_136_, v_x_137_);
if (v_isShared_173_ == 0)
{
lean_ctor_set(v___x_172_, 0, v___x_176_);
v___x_178_ = v___x_172_;
goto v_reusejp_177_;
}
else
{
lean_object* v_reuseFailAlloc_179_; 
v_reuseFailAlloc_179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_179_, 0, v___x_176_);
v___x_178_ = v_reuseFailAlloc_179_;
goto v_reusejp_177_;
}
v_reusejp_177_:
{
v___y_153_ = v___x_178_;
goto v___jp_152_;
}
}
}
default: 
{
lean_object* v___x_181_; 
v___x_181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_181_, 0, v_x_136_);
lean_ctor_set(v___x_181_, 1, v_x_137_);
v___y_153_ = v___x_181_;
goto v___jp_152_;
}
}
v___jp_152_:
{
lean_object* v___x_154_; lean_object* v___x_156_; 
v___x_154_ = lean_array_fset(v_xs_x27_151_, v_j_143_, v___y_153_);
lean_dec(v_j_143_);
if (v_isShared_148_ == 0)
{
lean_ctor_set(v___x_147_, 0, v___x_154_);
v___x_156_ = v___x_147_;
goto v_reusejp_155_;
}
else
{
lean_object* v_reuseFailAlloc_157_; 
v_reuseFailAlloc_157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_157_, 0, v___x_154_);
v___x_156_ = v_reuseFailAlloc_157_;
goto v_reusejp_155_;
}
v_reusejp_155_:
{
return v___x_156_;
}
}
}
}
}
else
{
lean_object* v_ks_184_; lean_object* v_vs_185_; lean_object* v___x_187_; uint8_t v_isShared_188_; uint8_t v_isSharedCheck_205_; 
v_ks_184_ = lean_ctor_get(v_x_133_, 0);
v_vs_185_ = lean_ctor_get(v_x_133_, 1);
v_isSharedCheck_205_ = !lean_is_exclusive(v_x_133_);
if (v_isSharedCheck_205_ == 0)
{
v___x_187_ = v_x_133_;
v_isShared_188_ = v_isSharedCheck_205_;
goto v_resetjp_186_;
}
else
{
lean_inc(v_vs_185_);
lean_inc(v_ks_184_);
lean_dec(v_x_133_);
v___x_187_ = lean_box(0);
v_isShared_188_ = v_isSharedCheck_205_;
goto v_resetjp_186_;
}
v_resetjp_186_:
{
lean_object* v___x_190_; 
if (v_isShared_188_ == 0)
{
v___x_190_ = v___x_187_;
goto v_reusejp_189_;
}
else
{
lean_object* v_reuseFailAlloc_204_; 
v_reuseFailAlloc_204_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_204_, 0, v_ks_184_);
lean_ctor_set(v_reuseFailAlloc_204_, 1, v_vs_185_);
v___x_190_ = v_reuseFailAlloc_204_;
goto v_reusejp_189_;
}
v_reusejp_189_:
{
lean_object* v_newNode_191_; uint8_t v___y_193_; size_t v___x_199_; uint8_t v___x_200_; 
v_newNode_191_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3_spec__5___redArg(v___x_190_, v_x_136_, v_x_137_);
v___x_199_ = ((size_t)7ULL);
v___x_200_ = lean_usize_dec_le(v___x_199_, v_x_135_);
if (v___x_200_ == 0)
{
lean_object* v___x_201_; lean_object* v___x_202_; uint8_t v___x_203_; 
v___x_201_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_191_);
v___x_202_ = lean_unsigned_to_nat(4u);
v___x_203_ = lean_nat_dec_lt(v___x_201_, v___x_202_);
lean_dec(v___x_201_);
v___y_193_ = v___x_203_;
goto v___jp_192_;
}
else
{
v___y_193_ = v___x_200_;
goto v___jp_192_;
}
v___jp_192_:
{
if (v___y_193_ == 0)
{
lean_object* v_ks_194_; lean_object* v_vs_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; 
v_ks_194_ = lean_ctor_get(v_newNode_191_, 0);
lean_inc_ref(v_ks_194_);
v_vs_195_ = lean_ctor_get(v_newNode_191_, 1);
lean_inc_ref(v_vs_195_);
lean_dec_ref(v_newNode_191_);
v___x_196_ = lean_unsigned_to_nat(0u);
v___x_197_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3___redArg___closed__0);
v___x_198_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3_spec__6___redArg(v_x_135_, v_ks_194_, v_vs_195_, v___x_196_, v___x_197_);
lean_dec_ref(v_vs_195_);
lean_dec_ref(v_ks_194_);
return v___x_198_;
}
else
{
return v_newNode_191_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3_spec__6___redArg(size_t v_depth_206_, lean_object* v_keys_207_, lean_object* v_vals_208_, lean_object* v_i_209_, lean_object* v_entries_210_){
_start:
{
lean_object* v___x_211_; uint8_t v___x_212_; 
v___x_211_ = lean_array_get_size(v_keys_207_);
v___x_212_ = lean_nat_dec_lt(v_i_209_, v___x_211_);
if (v___x_212_ == 0)
{
lean_dec(v_i_209_);
return v_entries_210_;
}
else
{
lean_object* v_k_213_; lean_object* v_v_214_; uint64_t v___x_215_; size_t v_h_216_; size_t v___x_217_; lean_object* v___x_218_; size_t v___x_219_; size_t v___x_220_; size_t v___x_221_; size_t v_h_222_; lean_object* v___x_223_; lean_object* v___x_224_; 
v_k_213_ = lean_array_fget_borrowed(v_keys_207_, v_i_209_);
v_v_214_ = lean_array_fget_borrowed(v_vals_208_, v_i_209_);
v___x_215_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_k_213_);
v_h_216_ = lean_uint64_to_usize(v___x_215_);
v___x_217_ = ((size_t)5ULL);
v___x_218_ = lean_unsigned_to_nat(1u);
v___x_219_ = ((size_t)1ULL);
v___x_220_ = lean_usize_sub(v_depth_206_, v___x_219_);
v___x_221_ = lean_usize_mul(v___x_217_, v___x_220_);
v_h_222_ = lean_usize_shift_right(v_h_216_, v___x_221_);
v___x_223_ = lean_nat_add(v_i_209_, v___x_218_);
lean_dec(v_i_209_);
lean_inc(v_v_214_);
lean_inc(v_k_213_);
v___x_224_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3___redArg(v_entries_210_, v_h_222_, v_depth_206_, v_k_213_, v_v_214_);
v_i_209_ = v___x_223_;
v_entries_210_ = v___x_224_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3_spec__6___redArg___boxed(lean_object* v_depth_226_, lean_object* v_keys_227_, lean_object* v_vals_228_, lean_object* v_i_229_, lean_object* v_entries_230_){
_start:
{
size_t v_depth_boxed_231_; lean_object* v_res_232_; 
v_depth_boxed_231_ = lean_unbox_usize(v_depth_226_);
lean_dec(v_depth_226_);
v_res_232_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3_spec__6___redArg(v_depth_boxed_231_, v_keys_227_, v_vals_228_, v_i_229_, v_entries_230_);
lean_dec_ref(v_vals_228_);
lean_dec_ref(v_keys_227_);
return v_res_232_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3___redArg___boxed(lean_object* v_x_233_, lean_object* v_x_234_, lean_object* v_x_235_, lean_object* v_x_236_, lean_object* v_x_237_){
_start:
{
size_t v_x_10491__boxed_238_; size_t v_x_10492__boxed_239_; lean_object* v_res_240_; 
v_x_10491__boxed_238_ = lean_unbox_usize(v_x_234_);
lean_dec(v_x_234_);
v_x_10492__boxed_239_ = lean_unbox_usize(v_x_235_);
lean_dec(v_x_235_);
v_res_240_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3___redArg(v_x_233_, v_x_10491__boxed_238_, v_x_10492__boxed_239_, v_x_236_, v_x_237_);
return v_res_240_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2___redArg(lean_object* v_x_241_, lean_object* v_x_242_, lean_object* v_x_243_){
_start:
{
uint64_t v___x_244_; size_t v___x_245_; size_t v___x_246_; lean_object* v___x_247_; 
v___x_244_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_242_);
v___x_245_ = lean_uint64_to_usize(v___x_244_);
v___x_246_ = ((size_t)1ULL);
v___x_247_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3___redArg(v_x_241_, v___x_245_, v___x_246_, v_x_242_, v_x_243_);
return v___x_247_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__3(void){
_start:
{
lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; 
v___x_251_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__2));
v___x_252_ = lean_unsigned_to_nat(26u);
v___x_253_ = lean_unsigned_to_nat(19u);
v___x_254_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__1));
v___x_255_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__0));
v___x_256_ = l_mkPanicMessageWithDecl(v___x_255_, v___x_254_, v___x_253_, v___x_252_, v___x_251_);
return v___x_256_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__11(void){
_start:
{
lean_object* v___x_269_; lean_object* v_dummy_270_; 
v___x_269_ = lean_box(0);
v_dummy_270_ = l_Lean_Expr_sort___override(v___x_269_);
return v_dummy_270_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f(lean_object* v_f_276_, lean_object* v_a_277_, lean_object* v_a_278_, lean_object* v_a_279_, lean_object* v_a_280_, lean_object* v_a_281_, lean_object* v_a_282_, lean_object* v_a_283_, lean_object* v_a_284_, lean_object* v_a_285_, lean_object* v_a_286_, lean_object* v_a_287_){
_start:
{
lean_object* v___y_290_; lean_object* v___y_291_; lean_object* v___y_292_; lean_object* v___y_293_; lean_object* v___y_294_; lean_object* v___y_295_; lean_object* v___y_296_; lean_object* v___y_297_; lean_object* v___y_298_; lean_object* v___y_299_; lean_object* v___x_302_; lean_object* v_toGoalState_303_; lean_object* v_inj_304_; lean_object* v_fns_305_; lean_object* v___x_307_; uint8_t v_isShared_308_; uint8_t v_isSharedCheck_430_; 
v___x_302_ = lean_st_ref_get(v_a_278_);
v_toGoalState_303_ = lean_ctor_get(v___x_302_, 0);
lean_inc_ref(v_toGoalState_303_);
lean_dec(v___x_302_);
v_inj_304_ = lean_ctor_get(v_toGoalState_303_, 14);
lean_inc_ref(v_inj_304_);
lean_dec_ref(v_toGoalState_303_);
v_fns_305_ = lean_ctor_get(v_inj_304_, 1);
v_isSharedCheck_430_ = !lean_is_exclusive(v_inj_304_);
if (v_isSharedCheck_430_ == 0)
{
lean_object* v_unused_431_; 
v_unused_431_ = lean_ctor_get(v_inj_304_, 0);
lean_dec(v_unused_431_);
v___x_307_ = v_inj_304_;
v_isShared_308_ = v_isSharedCheck_430_;
goto v_resetjp_306_;
}
else
{
lean_inc(v_fns_305_);
lean_dec(v_inj_304_);
v___x_307_ = lean_box(0);
v_isShared_308_ = v_isSharedCheck_430_;
goto v_resetjp_306_;
}
v___jp_289_:
{
lean_object* v___x_300_; lean_object* v___x_301_; 
v___x_300_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__3, &l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__3);
v___x_301_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__0(v___x_300_, v___y_290_, v___y_291_, v___y_292_, v___y_293_, v___y_294_, v___y_295_, v___y_296_, v___y_297_, v___y_298_, v___y_299_);
return v___x_301_;
}
v_resetjp_306_:
{
lean_object* v___x_309_; 
v___x_309_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1___redArg(v_fns_305_, v_f_276_);
if (lean_obj_tag(v___x_309_) == 1)
{
lean_object* v_val_310_; lean_object* v___x_312_; uint8_t v_isShared_313_; uint8_t v_isSharedCheck_427_; 
v_val_310_ = lean_ctor_get(v___x_309_, 0);
v_isSharedCheck_427_ = !lean_is_exclusive(v___x_309_);
if (v_isSharedCheck_427_ == 0)
{
v___x_312_ = v___x_309_;
v_isShared_313_ = v_isSharedCheck_427_;
goto v_resetjp_311_;
}
else
{
lean_inc(v_val_310_);
lean_dec(v___x_309_);
v___x_312_ = lean_box(0);
v_isShared_313_ = v_isSharedCheck_427_;
goto v_resetjp_311_;
}
v_resetjp_311_:
{
lean_object* v_inv_x3f_314_; 
v_inv_x3f_314_ = lean_ctor_get(v_val_310_, 4);
if (lean_obj_tag(v_inv_x3f_314_) == 1)
{
lean_object* v___x_315_; 
lean_inc_ref(v_inv_x3f_314_);
lean_del_object(v___x_312_);
lean_dec(v_val_310_);
lean_del_object(v___x_307_);
lean_dec(v_a_287_);
lean_dec_ref(v_a_286_);
lean_dec(v_a_285_);
lean_dec_ref(v_a_284_);
lean_dec(v_a_283_);
lean_dec_ref(v_a_282_);
lean_dec(v_a_281_);
lean_dec_ref(v_a_280_);
lean_dec(v_a_279_);
lean_dec(v_a_278_);
lean_dec_ref(v_a_277_);
lean_dec_ref(v_f_276_);
v___x_315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_315_, 0, v_inv_x3f_314_);
return v___x_315_;
}
else
{
lean_object* v_us_316_; 
v_us_316_ = lean_ctor_get(v_val_310_, 0);
lean_inc(v_us_316_);
if (lean_obj_tag(v_us_316_) == 1)
{
lean_object* v_tail_317_; 
v_tail_317_ = lean_ctor_get(v_us_316_, 1);
lean_inc(v_tail_317_);
if (lean_obj_tag(v_tail_317_) == 1)
{
lean_object* v_tail_318_; lean_object* v___x_320_; uint8_t v_isShared_321_; uint8_t v_isSharedCheck_425_; 
v_tail_318_ = lean_ctor_get(v_tail_317_, 1);
v_isSharedCheck_425_ = !lean_is_exclusive(v_tail_317_);
if (v_isSharedCheck_425_ == 0)
{
lean_object* v_unused_426_; 
v_unused_426_ = lean_ctor_get(v_tail_317_, 0);
lean_dec(v_unused_426_);
v___x_320_ = v_tail_317_;
v_isShared_321_ = v_isSharedCheck_425_;
goto v_resetjp_319_;
}
else
{
lean_inc(v_tail_318_);
lean_dec(v_tail_317_);
v___x_320_ = lean_box(0);
v_isShared_321_ = v_isSharedCheck_425_;
goto v_resetjp_319_;
}
v_resetjp_319_:
{
if (lean_obj_tag(v_tail_318_) == 0)
{
lean_object* v_00_u03b1_322_; lean_object* v_00_u03b2_323_; lean_object* v_h_324_; lean_object* v___x_326_; uint8_t v_isShared_327_; uint8_t v_isSharedCheck_422_; 
v_00_u03b1_322_ = lean_ctor_get(v_val_310_, 1);
v_00_u03b2_323_ = lean_ctor_get(v_val_310_, 2);
v_h_324_ = lean_ctor_get(v_val_310_, 3);
v_isSharedCheck_422_ = !lean_is_exclusive(v_val_310_);
if (v_isSharedCheck_422_ == 0)
{
lean_object* v_unused_423_; lean_object* v_unused_424_; 
v_unused_423_ = lean_ctor_get(v_val_310_, 4);
lean_dec(v_unused_423_);
v_unused_424_ = lean_ctor_get(v_val_310_, 0);
lean_dec(v_unused_424_);
v___x_326_ = v_val_310_;
v_isShared_327_ = v_isSharedCheck_422_;
goto v_resetjp_325_;
}
else
{
lean_inc(v_h_324_);
lean_inc(v_00_u03b2_323_);
lean_inc(v_00_u03b1_322_);
lean_dec(v_val_310_);
v___x_326_ = lean_box(0);
v_isShared_327_ = v_isSharedCheck_422_;
goto v_resetjp_325_;
}
v_resetjp_325_:
{
lean_object* v_head_328_; lean_object* v___x_329_; lean_object* v___x_331_; 
v_head_328_ = lean_ctor_get(v_us_316_, 0);
v___x_329_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__6));
lean_inc(v_head_328_);
if (v_isShared_321_ == 0)
{
lean_ctor_set(v___x_320_, 0, v_head_328_);
v___x_331_ = v___x_320_;
goto v_reusejp_330_;
}
else
{
lean_object* v_reuseFailAlloc_421_; 
v_reuseFailAlloc_421_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_421_, 0, v_head_328_);
lean_ctor_set(v_reuseFailAlloc_421_, 1, v_tail_318_);
v___x_331_ = v_reuseFailAlloc_421_;
goto v_reusejp_330_;
}
v_reusejp_330_:
{
lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; 
v___x_332_ = l_Lean_mkConst(v___x_329_, v___x_331_);
lean_inc_ref(v_00_u03b1_322_);
v___x_333_ = l_Lean_mkAppB(v___x_332_, v_00_u03b1_322_, v_a_277_);
v___x_334_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__10));
lean_inc_ref(v_us_316_);
v___x_335_ = l_Lean_mkConst(v___x_334_, v_us_316_);
lean_inc_ref(v_h_324_);
lean_inc_ref(v_f_276_);
lean_inc_ref(v_00_u03b2_323_);
lean_inc_ref(v_00_u03b1_322_);
v___x_336_ = l_Lean_mkApp5(v___x_335_, v_00_u03b1_322_, v_00_u03b2_323_, v_f_276_, v_h_324_, v___x_333_);
lean_inc(v_a_278_);
v___x_337_ = l_Lean_Meta_Grind_preprocessLight(v___x_336_, v_a_278_, v_a_279_, v_a_280_, v_a_281_, v_a_282_, v_a_283_, v_a_284_, v_a_285_, v_a_286_, v_a_287_);
if (lean_obj_tag(v___x_337_) == 0)
{
lean_object* v_a_338_; lean_object* v___x_340_; uint8_t v_isShared_341_; uint8_t v_isSharedCheck_412_; 
v_a_338_ = lean_ctor_get(v___x_337_, 0);
v_isSharedCheck_412_ = !lean_is_exclusive(v___x_337_);
if (v_isSharedCheck_412_ == 0)
{
v___x_340_ = v___x_337_;
v_isShared_341_ = v_isSharedCheck_412_;
goto v_resetjp_339_;
}
else
{
lean_inc(v_a_338_);
lean_dec(v___x_337_);
v___x_340_ = lean_box(0);
v_isShared_341_ = v_isSharedCheck_412_;
goto v_resetjp_339_;
}
v_resetjp_339_:
{
lean_object* v___x_342_; lean_object* v_nargs_343_; lean_object* v_toGoalState_344_; lean_object* v_inj_345_; lean_object* v_mvarId_346_; lean_object* v___x_348_; uint8_t v_isShared_349_; uint8_t v_isSharedCheck_410_; 
v___x_342_ = lean_st_ref_take(v_a_278_);
v_nargs_343_ = l_Lean_Expr_getAppNumArgs(v_a_338_);
v_toGoalState_344_ = lean_ctor_get(v___x_342_, 0);
lean_inc_ref(v_toGoalState_344_);
v_inj_345_ = lean_ctor_get(v_toGoalState_344_, 14);
lean_inc_ref(v_inj_345_);
v_mvarId_346_ = lean_ctor_get(v___x_342_, 1);
v_isSharedCheck_410_ = !lean_is_exclusive(v___x_342_);
if (v_isSharedCheck_410_ == 0)
{
lean_object* v_unused_411_; 
v_unused_411_ = lean_ctor_get(v___x_342_, 0);
lean_dec(v_unused_411_);
v___x_348_ = v___x_342_;
v_isShared_349_ = v_isSharedCheck_410_;
goto v_resetjp_347_;
}
else
{
lean_inc(v_mvarId_346_);
lean_dec(v___x_342_);
v___x_348_ = lean_box(0);
v_isShared_349_ = v_isSharedCheck_410_;
goto v_resetjp_347_;
}
v_resetjp_347_:
{
lean_object* v_nextDeclIdx_350_; lean_object* v_canon_351_; lean_object* v_enodeMap_352_; lean_object* v_exprs_353_; lean_object* v_parents_354_; lean_object* v_congrTable_355_; lean_object* v_appMap_356_; lean_object* v_indicesFound_357_; lean_object* v_newFacts_358_; uint8_t v_inconsistent_359_; lean_object* v_nextIdx_360_; lean_object* v_newRawFacts_361_; lean_object* v_facts_362_; lean_object* v_extThms_363_; lean_object* v_ematch_364_; lean_object* v_split_365_; lean_object* v_clean_366_; lean_object* v_sstates_367_; lean_object* v___x_369_; uint8_t v_isShared_370_; uint8_t v_isSharedCheck_408_; 
v_nextDeclIdx_350_ = lean_ctor_get(v_toGoalState_344_, 0);
v_canon_351_ = lean_ctor_get(v_toGoalState_344_, 1);
v_enodeMap_352_ = lean_ctor_get(v_toGoalState_344_, 2);
v_exprs_353_ = lean_ctor_get(v_toGoalState_344_, 3);
v_parents_354_ = lean_ctor_get(v_toGoalState_344_, 4);
v_congrTable_355_ = lean_ctor_get(v_toGoalState_344_, 5);
v_appMap_356_ = lean_ctor_get(v_toGoalState_344_, 6);
v_indicesFound_357_ = lean_ctor_get(v_toGoalState_344_, 7);
v_newFacts_358_ = lean_ctor_get(v_toGoalState_344_, 8);
v_inconsistent_359_ = lean_ctor_get_uint8(v_toGoalState_344_, sizeof(void*)*18);
v_nextIdx_360_ = lean_ctor_get(v_toGoalState_344_, 9);
v_newRawFacts_361_ = lean_ctor_get(v_toGoalState_344_, 10);
v_facts_362_ = lean_ctor_get(v_toGoalState_344_, 11);
v_extThms_363_ = lean_ctor_get(v_toGoalState_344_, 12);
v_ematch_364_ = lean_ctor_get(v_toGoalState_344_, 13);
v_split_365_ = lean_ctor_get(v_toGoalState_344_, 15);
v_clean_366_ = lean_ctor_get(v_toGoalState_344_, 16);
v_sstates_367_ = lean_ctor_get(v_toGoalState_344_, 17);
v_isSharedCheck_408_ = !lean_is_exclusive(v_toGoalState_344_);
if (v_isSharedCheck_408_ == 0)
{
lean_object* v_unused_409_; 
v_unused_409_ = lean_ctor_get(v_toGoalState_344_, 14);
lean_dec(v_unused_409_);
v___x_369_ = v_toGoalState_344_;
v_isShared_370_ = v_isSharedCheck_408_;
goto v_resetjp_368_;
}
else
{
lean_inc(v_sstates_367_);
lean_inc(v_clean_366_);
lean_inc(v_split_365_);
lean_inc(v_ematch_364_);
lean_inc(v_extThms_363_);
lean_inc(v_facts_362_);
lean_inc(v_newRawFacts_361_);
lean_inc(v_nextIdx_360_);
lean_inc(v_newFacts_358_);
lean_inc(v_indicesFound_357_);
lean_inc(v_appMap_356_);
lean_inc(v_congrTable_355_);
lean_inc(v_parents_354_);
lean_inc(v_exprs_353_);
lean_inc(v_enodeMap_352_);
lean_inc(v_canon_351_);
lean_inc(v_nextDeclIdx_350_);
lean_dec(v_toGoalState_344_);
v___x_369_ = lean_box(0);
v_isShared_370_ = v_isSharedCheck_408_;
goto v_resetjp_368_;
}
v_resetjp_368_:
{
lean_object* v_thms_371_; lean_object* v_fns_372_; lean_object* v___x_374_; uint8_t v_isShared_375_; uint8_t v_isSharedCheck_407_; 
v_thms_371_ = lean_ctor_get(v_inj_345_, 0);
v_fns_372_ = lean_ctor_get(v_inj_345_, 1);
v_isSharedCheck_407_ = !lean_is_exclusive(v_inj_345_);
if (v_isSharedCheck_407_ == 0)
{
v___x_374_ = v_inj_345_;
v_isShared_375_ = v_isSharedCheck_407_;
goto v_resetjp_373_;
}
else
{
lean_inc(v_fns_372_);
lean_inc(v_thms_371_);
lean_dec(v_inj_345_);
v___x_374_ = lean_box(0);
v_isShared_375_ = v_isSharedCheck_407_;
goto v_resetjp_373_;
}
v_resetjp_373_:
{
lean_object* v_dummy_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_385_; 
v_dummy_376_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__11, &l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__11_once, _init_l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__11);
lean_inc(v_nargs_343_);
v___x_377_ = lean_mk_array(v_nargs_343_, v_dummy_376_);
v___x_378_ = lean_unsigned_to_nat(1u);
v___x_379_ = lean_nat_sub(v_nargs_343_, v___x_378_);
lean_dec(v_nargs_343_);
lean_inc(v_a_338_);
v___x_380_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_338_, v___x_377_, v___x_379_);
v___x_381_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__13));
lean_inc_ref(v_us_316_);
v___x_382_ = l_Lean_mkConst(v___x_381_, v_us_316_);
v___x_383_ = l_Lean_mkAppN(v___x_382_, v___x_380_);
lean_dec_ref(v___x_380_);
if (v_isShared_308_ == 0)
{
lean_ctor_set(v___x_307_, 1, v___x_383_);
lean_ctor_set(v___x_307_, 0, v_a_338_);
v___x_385_ = v___x_307_;
goto v_reusejp_384_;
}
else
{
lean_object* v_reuseFailAlloc_406_; 
v_reuseFailAlloc_406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_406_, 0, v_a_338_);
lean_ctor_set(v_reuseFailAlloc_406_, 1, v___x_383_);
v___x_385_ = v_reuseFailAlloc_406_;
goto v_reusejp_384_;
}
v_reusejp_384_:
{
lean_object* v___x_387_; 
if (v_isShared_313_ == 0)
{
lean_ctor_set(v___x_312_, 0, v___x_385_);
v___x_387_ = v___x_312_;
goto v_reusejp_386_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v___x_385_);
v___x_387_ = v_reuseFailAlloc_405_;
goto v_reusejp_386_;
}
v_reusejp_386_:
{
lean_object* v___x_389_; 
lean_inc_ref(v___x_387_);
if (v_isShared_327_ == 0)
{
lean_ctor_set(v___x_326_, 4, v___x_387_);
v___x_389_ = v___x_326_;
goto v_reusejp_388_;
}
else
{
lean_object* v_reuseFailAlloc_404_; 
v_reuseFailAlloc_404_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_404_, 0, v_us_316_);
lean_ctor_set(v_reuseFailAlloc_404_, 1, v_00_u03b1_322_);
lean_ctor_set(v_reuseFailAlloc_404_, 2, v_00_u03b2_323_);
lean_ctor_set(v_reuseFailAlloc_404_, 3, v_h_324_);
lean_ctor_set(v_reuseFailAlloc_404_, 4, v___x_387_);
v___x_389_ = v_reuseFailAlloc_404_;
goto v_reusejp_388_;
}
v_reusejp_388_:
{
lean_object* v___x_390_; lean_object* v___x_392_; 
v___x_390_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2___redArg(v_fns_372_, v_f_276_, v___x_389_);
if (v_isShared_375_ == 0)
{
lean_ctor_set(v___x_374_, 1, v___x_390_);
v___x_392_ = v___x_374_;
goto v_reusejp_391_;
}
else
{
lean_object* v_reuseFailAlloc_403_; 
v_reuseFailAlloc_403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_403_, 0, v_thms_371_);
lean_ctor_set(v_reuseFailAlloc_403_, 1, v___x_390_);
v___x_392_ = v_reuseFailAlloc_403_;
goto v_reusejp_391_;
}
v_reusejp_391_:
{
lean_object* v___x_394_; 
if (v_isShared_370_ == 0)
{
lean_ctor_set(v___x_369_, 14, v___x_392_);
v___x_394_ = v___x_369_;
goto v_reusejp_393_;
}
else
{
lean_object* v_reuseFailAlloc_402_; 
v_reuseFailAlloc_402_ = lean_alloc_ctor(0, 18, 1);
lean_ctor_set(v_reuseFailAlloc_402_, 0, v_nextDeclIdx_350_);
lean_ctor_set(v_reuseFailAlloc_402_, 1, v_canon_351_);
lean_ctor_set(v_reuseFailAlloc_402_, 2, v_enodeMap_352_);
lean_ctor_set(v_reuseFailAlloc_402_, 3, v_exprs_353_);
lean_ctor_set(v_reuseFailAlloc_402_, 4, v_parents_354_);
lean_ctor_set(v_reuseFailAlloc_402_, 5, v_congrTable_355_);
lean_ctor_set(v_reuseFailAlloc_402_, 6, v_appMap_356_);
lean_ctor_set(v_reuseFailAlloc_402_, 7, v_indicesFound_357_);
lean_ctor_set(v_reuseFailAlloc_402_, 8, v_newFacts_358_);
lean_ctor_set(v_reuseFailAlloc_402_, 9, v_nextIdx_360_);
lean_ctor_set(v_reuseFailAlloc_402_, 10, v_newRawFacts_361_);
lean_ctor_set(v_reuseFailAlloc_402_, 11, v_facts_362_);
lean_ctor_set(v_reuseFailAlloc_402_, 12, v_extThms_363_);
lean_ctor_set(v_reuseFailAlloc_402_, 13, v_ematch_364_);
lean_ctor_set(v_reuseFailAlloc_402_, 14, v___x_392_);
lean_ctor_set(v_reuseFailAlloc_402_, 15, v_split_365_);
lean_ctor_set(v_reuseFailAlloc_402_, 16, v_clean_366_);
lean_ctor_set(v_reuseFailAlloc_402_, 17, v_sstates_367_);
lean_ctor_set_uint8(v_reuseFailAlloc_402_, sizeof(void*)*18, v_inconsistent_359_);
v___x_394_ = v_reuseFailAlloc_402_;
goto v_reusejp_393_;
}
v_reusejp_393_:
{
lean_object* v___x_396_; 
if (v_isShared_349_ == 0)
{
lean_ctor_set(v___x_348_, 0, v___x_394_);
v___x_396_ = v___x_348_;
goto v_reusejp_395_;
}
else
{
lean_object* v_reuseFailAlloc_401_; 
v_reuseFailAlloc_401_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_401_, 0, v___x_394_);
lean_ctor_set(v_reuseFailAlloc_401_, 1, v_mvarId_346_);
v___x_396_ = v_reuseFailAlloc_401_;
goto v_reusejp_395_;
}
v_reusejp_395_:
{
lean_object* v___x_397_; lean_object* v___x_399_; 
v___x_397_ = lean_st_ref_set(v_a_278_, v___x_396_);
lean_dec(v_a_278_);
if (v_isShared_341_ == 0)
{
lean_ctor_set(v___x_340_, 0, v___x_387_);
v___x_399_ = v___x_340_;
goto v_reusejp_398_;
}
else
{
lean_object* v_reuseFailAlloc_400_; 
v_reuseFailAlloc_400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_400_, 0, v___x_387_);
v___x_399_ = v_reuseFailAlloc_400_;
goto v_reusejp_398_;
}
v_reusejp_398_:
{
return v___x_399_;
}
}
}
}
}
}
}
}
}
}
}
}
else
{
lean_object* v_a_413_; lean_object* v___x_415_; uint8_t v_isShared_416_; uint8_t v_isSharedCheck_420_; 
lean_del_object(v___x_326_);
lean_dec_ref(v_h_324_);
lean_dec_ref(v_00_u03b2_323_);
lean_dec_ref(v_00_u03b1_322_);
lean_dec_ref(v_us_316_);
lean_del_object(v___x_312_);
lean_del_object(v___x_307_);
lean_dec(v_a_278_);
lean_dec_ref(v_f_276_);
v_a_413_ = lean_ctor_get(v___x_337_, 0);
v_isSharedCheck_420_ = !lean_is_exclusive(v___x_337_);
if (v_isSharedCheck_420_ == 0)
{
v___x_415_ = v___x_337_;
v_isShared_416_ = v_isSharedCheck_420_;
goto v_resetjp_414_;
}
else
{
lean_inc(v_a_413_);
lean_dec(v___x_337_);
v___x_415_ = lean_box(0);
v_isShared_416_ = v_isSharedCheck_420_;
goto v_resetjp_414_;
}
v_resetjp_414_:
{
lean_object* v___x_418_; 
if (v_isShared_416_ == 0)
{
v___x_418_ = v___x_415_;
goto v_reusejp_417_;
}
else
{
lean_object* v_reuseFailAlloc_419_; 
v_reuseFailAlloc_419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_419_, 0, v_a_413_);
v___x_418_ = v_reuseFailAlloc_419_;
goto v_reusejp_417_;
}
v_reusejp_417_:
{
return v___x_418_;
}
}
}
}
}
}
else
{
lean_del_object(v___x_320_);
lean_dec(v_tail_318_);
lean_dec_ref(v_us_316_);
lean_del_object(v___x_312_);
lean_dec(v_val_310_);
lean_del_object(v___x_307_);
lean_dec_ref(v_a_277_);
lean_dec_ref(v_f_276_);
v___y_290_ = v_a_278_;
v___y_291_ = v_a_279_;
v___y_292_ = v_a_280_;
v___y_293_ = v_a_281_;
v___y_294_ = v_a_282_;
v___y_295_ = v_a_283_;
v___y_296_ = v_a_284_;
v___y_297_ = v_a_285_;
v___y_298_ = v_a_286_;
v___y_299_ = v_a_287_;
goto v___jp_289_;
}
}
}
else
{
lean_dec(v_tail_317_);
lean_dec_ref(v_us_316_);
lean_del_object(v___x_312_);
lean_dec(v_val_310_);
lean_del_object(v___x_307_);
lean_dec_ref(v_a_277_);
lean_dec_ref(v_f_276_);
v___y_290_ = v_a_278_;
v___y_291_ = v_a_279_;
v___y_292_ = v_a_280_;
v___y_293_ = v_a_281_;
v___y_294_ = v_a_282_;
v___y_295_ = v_a_283_;
v___y_296_ = v_a_284_;
v___y_297_ = v_a_285_;
v___y_298_ = v_a_286_;
v___y_299_ = v_a_287_;
goto v___jp_289_;
}
}
else
{
lean_dec(v_us_316_);
lean_del_object(v___x_312_);
lean_dec(v_val_310_);
lean_del_object(v___x_307_);
lean_dec_ref(v_a_277_);
lean_dec_ref(v_f_276_);
v___y_290_ = v_a_278_;
v___y_291_ = v_a_279_;
v___y_292_ = v_a_280_;
v___y_293_ = v_a_281_;
v___y_294_ = v_a_282_;
v___y_295_ = v_a_283_;
v___y_296_ = v_a_284_;
v___y_297_ = v_a_285_;
v___y_298_ = v_a_286_;
v___y_299_ = v_a_287_;
goto v___jp_289_;
}
}
}
}
else
{
lean_object* v___x_428_; lean_object* v___x_429_; 
lean_dec(v___x_309_);
lean_del_object(v___x_307_);
lean_dec(v_a_287_);
lean_dec_ref(v_a_286_);
lean_dec(v_a_285_);
lean_dec_ref(v_a_284_);
lean_dec(v_a_283_);
lean_dec_ref(v_a_282_);
lean_dec(v_a_281_);
lean_dec_ref(v_a_280_);
lean_dec(v_a_279_);
lean_dec(v_a_278_);
lean_dec_ref(v_a_277_);
lean_dec_ref(v_f_276_);
v___x_428_ = lean_box(0);
v___x_429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_429_, 0, v___x_428_);
return v___x_429_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___boxed(lean_object* v_f_432_, lean_object* v_a_433_, lean_object* v_a_434_, lean_object* v_a_435_, lean_object* v_a_436_, lean_object* v_a_437_, lean_object* v_a_438_, lean_object* v_a_439_, lean_object* v_a_440_, lean_object* v_a_441_, lean_object* v_a_442_, lean_object* v_a_443_, lean_object* v_a_444_){
_start:
{
lean_object* v_res_445_; 
v_res_445_ = l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f(v_f_432_, v_a_433_, v_a_434_, v_a_435_, v_a_436_, v_a_437_, v_a_438_, v_a_439_, v_a_440_, v_a_441_, v_a_442_, v_a_443_);
return v_res_445_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1(lean_object* v_00_u03b2_446_, lean_object* v_x_447_, lean_object* v_x_448_){
_start:
{
lean_object* v___x_449_; 
v___x_449_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1___redArg(v_x_447_, v_x_448_);
return v___x_449_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1___boxed(lean_object* v_00_u03b2_450_, lean_object* v_x_451_, lean_object* v_x_452_){
_start:
{
lean_object* v_res_453_; 
v_res_453_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1(v_00_u03b2_450_, v_x_451_, v_x_452_);
lean_dec_ref(v_x_452_);
return v_res_453_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2(lean_object* v_00_u03b2_454_, lean_object* v_x_455_, lean_object* v_x_456_, lean_object* v_x_457_){
_start:
{
lean_object* v___x_458_; 
v___x_458_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2___redArg(v_x_455_, v_x_456_, v_x_457_);
return v___x_458_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1(lean_object* v_00_u03b2_459_, lean_object* v_x_460_, size_t v_x_461_, lean_object* v_x_462_){
_start:
{
lean_object* v___x_463_; 
v___x_463_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1___redArg(v_x_460_, v_x_461_, v_x_462_);
return v___x_463_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1___boxed(lean_object* v_00_u03b2_464_, lean_object* v_x_465_, lean_object* v_x_466_, lean_object* v_x_467_){
_start:
{
size_t v_x_11012__boxed_468_; lean_object* v_res_469_; 
v_x_11012__boxed_468_ = lean_unbox_usize(v_x_466_);
lean_dec(v_x_466_);
v_res_469_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1(v_00_u03b2_464_, v_x_465_, v_x_11012__boxed_468_, v_x_467_);
lean_dec_ref(v_x_467_);
return v_res_469_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3(lean_object* v_00_u03b2_470_, lean_object* v_x_471_, size_t v_x_472_, size_t v_x_473_, lean_object* v_x_474_, lean_object* v_x_475_){
_start:
{
lean_object* v___x_476_; 
v___x_476_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3___redArg(v_x_471_, v_x_472_, v_x_473_, v_x_474_, v_x_475_);
return v___x_476_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3___boxed(lean_object* v_00_u03b2_477_, lean_object* v_x_478_, lean_object* v_x_479_, lean_object* v_x_480_, lean_object* v_x_481_, lean_object* v_x_482_){
_start:
{
size_t v_x_11023__boxed_483_; size_t v_x_11024__boxed_484_; lean_object* v_res_485_; 
v_x_11023__boxed_483_ = lean_unbox_usize(v_x_479_);
lean_dec(v_x_479_);
v_x_11024__boxed_484_ = lean_unbox_usize(v_x_480_);
lean_dec(v_x_480_);
v_res_485_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3(v_00_u03b2_477_, v_x_478_, v_x_11023__boxed_483_, v_x_11024__boxed_484_, v_x_481_, v_x_482_);
return v_res_485_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_486_, lean_object* v_keys_487_, lean_object* v_vals_488_, lean_object* v_heq_489_, lean_object* v_i_490_, lean_object* v_k_491_){
_start:
{
lean_object* v___x_492_; 
v___x_492_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1_spec__2___redArg(v_keys_487_, v_vals_488_, v_i_490_, v_k_491_);
return v___x_492_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03b2_493_, lean_object* v_keys_494_, lean_object* v_vals_495_, lean_object* v_heq_496_, lean_object* v_i_497_, lean_object* v_k_498_){
_start:
{
lean_object* v_res_499_; 
v_res_499_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1_spec__2(v_00_u03b2_493_, v_keys_494_, v_vals_495_, v_heq_496_, v_i_497_, v_k_498_);
lean_dec_ref(v_k_498_);
lean_dec_ref(v_vals_495_);
lean_dec_ref(v_keys_494_);
return v_res_499_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3_spec__5(lean_object* v_00_u03b2_500_, lean_object* v_n_501_, lean_object* v_k_502_, lean_object* v_v_503_){
_start:
{
lean_object* v___x_504_; 
v___x_504_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3_spec__5___redArg(v_n_501_, v_k_502_, v_v_503_);
return v___x_504_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3_spec__6(lean_object* v_00_u03b2_505_, size_t v_depth_506_, lean_object* v_keys_507_, lean_object* v_vals_508_, lean_object* v_heq_509_, lean_object* v_i_510_, lean_object* v_entries_511_){
_start:
{
lean_object* v___x_512_; 
v___x_512_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3_spec__6___redArg(v_depth_506_, v_keys_507_, v_vals_508_, v_i_510_, v_entries_511_);
return v___x_512_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3_spec__6___boxed(lean_object* v_00_u03b2_513_, lean_object* v_depth_514_, lean_object* v_keys_515_, lean_object* v_vals_516_, lean_object* v_heq_517_, lean_object* v_i_518_, lean_object* v_entries_519_){
_start:
{
size_t v_depth_boxed_520_; lean_object* v_res_521_; 
v_depth_boxed_520_ = lean_unbox_usize(v_depth_514_);
lean_dec(v_depth_514_);
v_res_521_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3_spec__6(v_00_u03b2_513_, v_depth_boxed_520_, v_keys_515_, v_vals_516_, v_heq_517_, v_i_518_, v_entries_519_);
lean_dec_ref(v_vals_516_);
lean_dec_ref(v_keys_515_);
return v_res_521_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3_spec__5_spec__6(lean_object* v_00_u03b2_522_, lean_object* v_x_523_, lean_object* v_x_524_, lean_object* v_x_525_, lean_object* v_x_526_){
_start:
{
lean_object* v___x_527_; 
v___x_527_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3_spec__5_spec__6___redArg(v_x_523_, v_x_524_, v_x_525_, v_x_526_);
return v___x_527_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_mkInjEq_spec__0___redArg(lean_object* v_cls_531_, lean_object* v___y_532_){
_start:
{
lean_object* v_options_534_; uint8_t v_hasTrace_535_; 
v_options_534_ = lean_ctor_get(v___y_532_, 2);
v_hasTrace_535_ = lean_ctor_get_uint8(v_options_534_, sizeof(void*)*1);
if (v_hasTrace_535_ == 0)
{
lean_object* v___x_536_; lean_object* v___x_537_; 
lean_dec(v_cls_531_);
v___x_536_ = lean_box(v_hasTrace_535_);
v___x_537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_537_, 0, v___x_536_);
return v___x_537_;
}
else
{
lean_object* v_inheritedTraceOptions_538_; lean_object* v___x_539_; lean_object* v___x_540_; uint8_t v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; 
v_inheritedTraceOptions_538_ = lean_ctor_get(v___y_532_, 13);
v___x_539_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_mkInjEq_spec__0___redArg___closed__1));
v___x_540_ = l_Lean_Name_append(v___x_539_, v_cls_531_);
v___x_541_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_538_, v_options_534_, v___x_540_);
lean_dec(v___x_540_);
v___x_542_ = lean_box(v___x_541_);
v___x_543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_543_, 0, v___x_542_);
return v___x_543_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_mkInjEq_spec__0___redArg___boxed(lean_object* v_cls_544_, lean_object* v___y_545_, lean_object* v___y_546_){
_start:
{
lean_object* v_res_547_; 
v_res_547_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_mkInjEq_spec__0___redArg(v_cls_544_, v___y_545_);
lean_dec_ref(v___y_545_);
return v_res_547_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_mkInjEq_spec__0(lean_object* v_cls_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_){
_start:
{
lean_object* v___x_560_; 
v___x_560_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_mkInjEq_spec__0___redArg(v_cls_548_, v___y_557_);
return v___x_560_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_mkInjEq_spec__0___boxed(lean_object* v_cls_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_){
_start:
{
lean_object* v_res_573_; 
v_res_573_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_mkInjEq_spec__0(v_cls_561_, v___y_562_, v___y_563_, v___y_564_, v___y_565_, v___y_566_, v___y_567_, v___y_568_, v___y_569_, v___y_570_, v___y_571_);
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
return v_res_573_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__1_spec__1(lean_object* v_msgData_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_){
_start:
{
lean_object* v___x_580_; lean_object* v_env_581_; lean_object* v___x_582_; lean_object* v_mctx_583_; lean_object* v_lctx_584_; lean_object* v_options_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; 
v___x_580_ = lean_st_ref_get(v___y_578_);
v_env_581_ = lean_ctor_get(v___x_580_, 0);
lean_inc_ref(v_env_581_);
lean_dec(v___x_580_);
v___x_582_ = lean_st_ref_get(v___y_576_);
v_mctx_583_ = lean_ctor_get(v___x_582_, 0);
lean_inc_ref(v_mctx_583_);
lean_dec(v___x_582_);
v_lctx_584_ = lean_ctor_get(v___y_575_, 2);
v_options_585_ = lean_ctor_get(v___y_577_, 2);
lean_inc_ref(v_options_585_);
lean_inc_ref(v_lctx_584_);
v___x_586_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_586_, 0, v_env_581_);
lean_ctor_set(v___x_586_, 1, v_mctx_583_);
lean_ctor_set(v___x_586_, 2, v_lctx_584_);
lean_ctor_set(v___x_586_, 3, v_options_585_);
v___x_587_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_587_, 0, v___x_586_);
lean_ctor_set(v___x_587_, 1, v_msgData_574_);
v___x_588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_588_, 0, v___x_587_);
return v___x_588_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__1_spec__1___boxed(lean_object* v_msgData_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_){
_start:
{
lean_object* v_res_595_; 
v_res_595_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__1_spec__1(v_msgData_589_, v___y_590_, v___y_591_, v___y_592_, v___y_593_);
lean_dec(v___y_593_);
lean_dec_ref(v___y_592_);
lean_dec(v___y_591_);
lean_dec_ref(v___y_590_);
return v_res_595_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_596_; double v___x_597_; 
v___x_596_ = lean_unsigned_to_nat(0u);
v___x_597_ = lean_float_of_nat(v___x_596_);
return v___x_597_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__1___redArg(lean_object* v_cls_601_, lean_object* v_msg_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_){
_start:
{
lean_object* v_ref_608_; lean_object* v___x_609_; lean_object* v_a_610_; lean_object* v___x_612_; uint8_t v_isShared_613_; uint8_t v_isSharedCheck_654_; 
v_ref_608_ = lean_ctor_get(v___y_605_, 5);
v___x_609_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__1_spec__1(v_msg_602_, v___y_603_, v___y_604_, v___y_605_, v___y_606_);
v_a_610_ = lean_ctor_get(v___x_609_, 0);
v_isSharedCheck_654_ = !lean_is_exclusive(v___x_609_);
if (v_isSharedCheck_654_ == 0)
{
v___x_612_ = v___x_609_;
v_isShared_613_ = v_isSharedCheck_654_;
goto v_resetjp_611_;
}
else
{
lean_inc(v_a_610_);
lean_dec(v___x_609_);
v___x_612_ = lean_box(0);
v_isShared_613_ = v_isSharedCheck_654_;
goto v_resetjp_611_;
}
v_resetjp_611_:
{
lean_object* v___x_614_; lean_object* v_traceState_615_; lean_object* v_env_616_; lean_object* v_nextMacroScope_617_; lean_object* v_ngen_618_; lean_object* v_auxDeclNGen_619_; lean_object* v_cache_620_; lean_object* v_messages_621_; lean_object* v_infoState_622_; lean_object* v_snapshotTasks_623_; lean_object* v___x_625_; uint8_t v_isShared_626_; uint8_t v_isSharedCheck_653_; 
v___x_614_ = lean_st_ref_take(v___y_606_);
v_traceState_615_ = lean_ctor_get(v___x_614_, 4);
v_env_616_ = lean_ctor_get(v___x_614_, 0);
v_nextMacroScope_617_ = lean_ctor_get(v___x_614_, 1);
v_ngen_618_ = lean_ctor_get(v___x_614_, 2);
v_auxDeclNGen_619_ = lean_ctor_get(v___x_614_, 3);
v_cache_620_ = lean_ctor_get(v___x_614_, 5);
v_messages_621_ = lean_ctor_get(v___x_614_, 6);
v_infoState_622_ = lean_ctor_get(v___x_614_, 7);
v_snapshotTasks_623_ = lean_ctor_get(v___x_614_, 8);
v_isSharedCheck_653_ = !lean_is_exclusive(v___x_614_);
if (v_isSharedCheck_653_ == 0)
{
v___x_625_ = v___x_614_;
v_isShared_626_ = v_isSharedCheck_653_;
goto v_resetjp_624_;
}
else
{
lean_inc(v_snapshotTasks_623_);
lean_inc(v_infoState_622_);
lean_inc(v_messages_621_);
lean_inc(v_cache_620_);
lean_inc(v_traceState_615_);
lean_inc(v_auxDeclNGen_619_);
lean_inc(v_ngen_618_);
lean_inc(v_nextMacroScope_617_);
lean_inc(v_env_616_);
lean_dec(v___x_614_);
v___x_625_ = lean_box(0);
v_isShared_626_ = v_isSharedCheck_653_;
goto v_resetjp_624_;
}
v_resetjp_624_:
{
uint64_t v_tid_627_; lean_object* v_traces_628_; lean_object* v___x_630_; uint8_t v_isShared_631_; uint8_t v_isSharedCheck_652_; 
v_tid_627_ = lean_ctor_get_uint64(v_traceState_615_, sizeof(void*)*1);
v_traces_628_ = lean_ctor_get(v_traceState_615_, 0);
v_isSharedCheck_652_ = !lean_is_exclusive(v_traceState_615_);
if (v_isSharedCheck_652_ == 0)
{
v___x_630_ = v_traceState_615_;
v_isShared_631_ = v_isSharedCheck_652_;
goto v_resetjp_629_;
}
else
{
lean_inc(v_traces_628_);
lean_dec(v_traceState_615_);
v___x_630_ = lean_box(0);
v_isShared_631_ = v_isSharedCheck_652_;
goto v_resetjp_629_;
}
v_resetjp_629_:
{
lean_object* v___x_632_; double v___x_633_; uint8_t v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_642_; 
v___x_632_ = lean_box(0);
v___x_633_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__1___redArg___closed__0);
v___x_634_ = 0;
v___x_635_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__1___redArg___closed__1));
v___x_636_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_636_, 0, v_cls_601_);
lean_ctor_set(v___x_636_, 1, v___x_632_);
lean_ctor_set(v___x_636_, 2, v___x_635_);
lean_ctor_set_float(v___x_636_, sizeof(void*)*3, v___x_633_);
lean_ctor_set_float(v___x_636_, sizeof(void*)*3 + 8, v___x_633_);
lean_ctor_set_uint8(v___x_636_, sizeof(void*)*3 + 16, v___x_634_);
v___x_637_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__1___redArg___closed__2));
v___x_638_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_638_, 0, v___x_636_);
lean_ctor_set(v___x_638_, 1, v_a_610_);
lean_ctor_set(v___x_638_, 2, v___x_637_);
lean_inc(v_ref_608_);
v___x_639_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_639_, 0, v_ref_608_);
lean_ctor_set(v___x_639_, 1, v___x_638_);
v___x_640_ = l_Lean_PersistentArray_push___redArg(v_traces_628_, v___x_639_);
if (v_isShared_631_ == 0)
{
lean_ctor_set(v___x_630_, 0, v___x_640_);
v___x_642_ = v___x_630_;
goto v_reusejp_641_;
}
else
{
lean_object* v_reuseFailAlloc_651_; 
v_reuseFailAlloc_651_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_651_, 0, v___x_640_);
lean_ctor_set_uint64(v_reuseFailAlloc_651_, sizeof(void*)*1, v_tid_627_);
v___x_642_ = v_reuseFailAlloc_651_;
goto v_reusejp_641_;
}
v_reusejp_641_:
{
lean_object* v___x_644_; 
if (v_isShared_626_ == 0)
{
lean_ctor_set(v___x_625_, 4, v___x_642_);
v___x_644_ = v___x_625_;
goto v_reusejp_643_;
}
else
{
lean_object* v_reuseFailAlloc_650_; 
v_reuseFailAlloc_650_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_650_, 0, v_env_616_);
lean_ctor_set(v_reuseFailAlloc_650_, 1, v_nextMacroScope_617_);
lean_ctor_set(v_reuseFailAlloc_650_, 2, v_ngen_618_);
lean_ctor_set(v_reuseFailAlloc_650_, 3, v_auxDeclNGen_619_);
lean_ctor_set(v_reuseFailAlloc_650_, 4, v___x_642_);
lean_ctor_set(v_reuseFailAlloc_650_, 5, v_cache_620_);
lean_ctor_set(v_reuseFailAlloc_650_, 6, v_messages_621_);
lean_ctor_set(v_reuseFailAlloc_650_, 7, v_infoState_622_);
lean_ctor_set(v_reuseFailAlloc_650_, 8, v_snapshotTasks_623_);
v___x_644_ = v_reuseFailAlloc_650_;
goto v_reusejp_643_;
}
v_reusejp_643_:
{
lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_648_; 
v___x_645_ = lean_st_ref_set(v___y_606_, v___x_644_);
v___x_646_ = lean_box(0);
if (v_isShared_613_ == 0)
{
lean_ctor_set(v___x_612_, 0, v___x_646_);
v___x_648_ = v___x_612_;
goto v_reusejp_647_;
}
else
{
lean_object* v_reuseFailAlloc_649_; 
v_reuseFailAlloc_649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_649_, 0, v___x_646_);
v___x_648_ = v_reuseFailAlloc_649_;
goto v_reusejp_647_;
}
v_reusejp_647_:
{
return v___x_648_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__1___redArg___boxed(lean_object* v_cls_655_, lean_object* v_msg_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_){
_start:
{
lean_object* v_res_662_; 
v_res_662_ = l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__1___redArg(v_cls_655_, v_msg_656_, v___y_657_, v___y_658_, v___y_659_, v___y_660_);
lean_dec(v___y_660_);
lean_dec_ref(v___y_659_);
lean_dec(v___y_658_);
lean_dec_ref(v___y_657_);
return v_res_662_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkInjEq___closed__5(void){
_start:
{
lean_object* v___x_671_; lean_object* v___x_672_; 
v___x_671_ = ((lean_object*)(l_Lean_Meta_Grind_mkInjEq___closed__4));
v___x_672_ = l_Lean_stringToMessageData(v___x_671_);
return v___x_672_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkInjEq(lean_object* v_e_673_, lean_object* v_a_674_, lean_object* v_a_675_, lean_object* v_a_676_, lean_object* v_a_677_, lean_object* v_a_678_, lean_object* v_a_679_, lean_object* v_a_680_, lean_object* v_a_681_, lean_object* v_a_682_, lean_object* v_a_683_){
_start:
{
if (lean_obj_tag(v_e_673_) == 5)
{
lean_object* v_fn_685_; lean_object* v_arg_686_; lean_object* v___x_687_; 
v_fn_685_ = lean_ctor_get(v_e_673_, 0);
v_arg_686_ = lean_ctor_get(v_e_673_, 1);
lean_inc_ref(v_arg_686_);
lean_inc(v_a_683_);
lean_inc_ref(v_a_682_);
lean_inc(v_a_681_);
lean_inc_ref(v_a_680_);
lean_inc(v_a_679_);
lean_inc_ref(v_a_678_);
lean_inc(v_a_677_);
lean_inc_ref(v_a_676_);
lean_inc(v_a_675_);
lean_inc(v_a_674_);
lean_inc_ref(v_arg_686_);
lean_inc_ref(v_fn_685_);
v___x_687_ = l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f(v_fn_685_, v_arg_686_, v_a_674_, v_a_675_, v_a_676_, v_a_677_, v_a_678_, v_a_679_, v_a_680_, v_a_681_, v_a_682_, v_a_683_);
if (lean_obj_tag(v___x_687_) == 0)
{
lean_object* v_a_688_; lean_object* v___x_690_; uint8_t v_isShared_691_; uint8_t v_isSharedCheck_738_; 
v_a_688_ = lean_ctor_get(v___x_687_, 0);
v_isSharedCheck_738_ = !lean_is_exclusive(v___x_687_);
if (v_isSharedCheck_738_ == 0)
{
v___x_690_ = v___x_687_;
v_isShared_691_ = v_isSharedCheck_738_;
goto v_resetjp_689_;
}
else
{
lean_inc(v_a_688_);
lean_dec(v___x_687_);
v___x_690_ = lean_box(0);
v_isShared_691_ = v_isSharedCheck_738_;
goto v_resetjp_689_;
}
v_resetjp_689_:
{
if (lean_obj_tag(v_a_688_) == 1)
{
lean_object* v_val_692_; lean_object* v_fst_693_; lean_object* v_snd_694_; lean_object* v___x_696_; uint8_t v_isShared_697_; uint8_t v_isSharedCheck_733_; 
lean_del_object(v___x_690_);
v_val_692_ = lean_ctor_get(v_a_688_, 0);
lean_inc(v_val_692_);
lean_dec_ref(v_a_688_);
v_fst_693_ = lean_ctor_get(v_val_692_, 0);
v_snd_694_ = lean_ctor_get(v_val_692_, 1);
v_isSharedCheck_733_ = !lean_is_exclusive(v_val_692_);
if (v_isSharedCheck_733_ == 0)
{
v___x_696_ = v_val_692_;
v_isShared_697_ = v_isSharedCheck_733_;
goto v_resetjp_695_;
}
else
{
lean_inc(v_snd_694_);
lean_inc(v_fst_693_);
lean_dec(v_val_692_);
v___x_696_ = lean_box(0);
v_isShared_697_ = v_isSharedCheck_733_;
goto v_resetjp_695_;
}
v_resetjp_695_:
{
lean_object* v___x_698_; 
v___x_698_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_673_, v_a_674_);
if (lean_obj_tag(v___x_698_) == 0)
{
lean_object* v_a_699_; lean_object* v___x_700_; lean_object* v___y_702_; lean_object* v___y_703_; lean_object* v___y_704_; lean_object* v___y_705_; lean_object* v___y_706_; lean_object* v___y_707_; lean_object* v___x_711_; lean_object* v___x_712_; 
v_a_699_ = lean_ctor_get(v___x_698_, 0);
lean_inc(v_a_699_);
lean_dec_ref(v___x_698_);
v___x_700_ = l_Lean_Expr_app___override(v_fst_693_, v_e_673_);
v___x_711_ = lean_box(0);
lean_inc(v_a_683_);
lean_inc_ref(v_a_682_);
lean_inc(v_a_681_);
lean_inc_ref(v_a_680_);
lean_inc_ref(v_a_676_);
lean_inc(v_a_674_);
lean_inc_ref(v___x_700_);
v___x_712_ = lean_grind_internalize(v___x_700_, v_a_699_, v___x_711_, v_a_674_, v_a_675_, v_a_676_, v_a_677_, v_a_678_, v_a_679_, v_a_680_, v_a_681_, v_a_682_, v_a_683_);
if (lean_obj_tag(v___x_712_) == 0)
{
lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v_a_715_; uint8_t v___x_716_; 
lean_dec_ref(v___x_712_);
v___x_713_ = ((lean_object*)(l_Lean_Meta_Grind_mkInjEq___closed__3));
v___x_714_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_mkInjEq_spec__0___redArg(v___x_713_, v_a_682_);
v_a_715_ = lean_ctor_get(v___x_714_, 0);
lean_inc(v_a_715_);
lean_dec_ref(v___x_714_);
v___x_716_ = lean_unbox(v_a_715_);
lean_dec(v_a_715_);
if (v___x_716_ == 0)
{
lean_del_object(v___x_696_);
v___y_702_ = v_a_674_;
v___y_703_ = v_a_676_;
v___y_704_ = v_a_680_;
v___y_705_ = v_a_681_;
v___y_706_ = v_a_682_;
v___y_707_ = v_a_683_;
goto v___jp_701_;
}
else
{
lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_720_; 
lean_inc_ref(v___x_700_);
v___x_717_ = l_Lean_MessageData_ofExpr(v___x_700_);
v___x_718_ = lean_obj_once(&l_Lean_Meta_Grind_mkInjEq___closed__5, &l_Lean_Meta_Grind_mkInjEq___closed__5_once, _init_l_Lean_Meta_Grind_mkInjEq___closed__5);
if (v_isShared_697_ == 0)
{
lean_ctor_set_tag(v___x_696_, 7);
lean_ctor_set(v___x_696_, 1, v___x_718_);
lean_ctor_set(v___x_696_, 0, v___x_717_);
v___x_720_ = v___x_696_;
goto v_reusejp_719_;
}
else
{
lean_object* v_reuseFailAlloc_724_; 
v_reuseFailAlloc_724_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_724_, 0, v___x_717_);
lean_ctor_set(v_reuseFailAlloc_724_, 1, v___x_718_);
v___x_720_ = v_reuseFailAlloc_724_;
goto v_reusejp_719_;
}
v_reusejp_719_:
{
lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; 
lean_inc_ref(v_arg_686_);
v___x_721_ = l_Lean_MessageData_ofExpr(v_arg_686_);
v___x_722_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_722_, 0, v___x_720_);
lean_ctor_set(v___x_722_, 1, v___x_721_);
v___x_723_ = l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__1___redArg(v___x_713_, v___x_722_, v_a_680_, v_a_681_, v_a_682_, v_a_683_);
if (lean_obj_tag(v___x_723_) == 0)
{
lean_dec_ref(v___x_723_);
v___y_702_ = v_a_674_;
v___y_703_ = v_a_676_;
v___y_704_ = v_a_680_;
v___y_705_ = v_a_681_;
v___y_706_ = v_a_682_;
v___y_707_ = v_a_683_;
goto v___jp_701_;
}
else
{
lean_dec_ref(v___x_700_);
lean_dec(v_snd_694_);
lean_dec_ref(v_arg_686_);
lean_dec(v_a_683_);
lean_dec_ref(v_a_682_);
lean_dec(v_a_681_);
lean_dec_ref(v_a_680_);
lean_dec_ref(v_a_676_);
lean_dec(v_a_674_);
return v___x_723_;
}
}
}
}
else
{
lean_dec_ref(v___x_700_);
lean_del_object(v___x_696_);
lean_dec(v_snd_694_);
lean_dec_ref(v_arg_686_);
lean_dec(v_a_683_);
lean_dec_ref(v_a_682_);
lean_dec(v_a_681_);
lean_dec_ref(v_a_680_);
lean_dec_ref(v_a_676_);
lean_dec(v_a_674_);
return v___x_712_;
}
v___jp_701_:
{
lean_object* v___x_708_; uint8_t v___x_709_; lean_object* v___x_710_; 
lean_inc_ref(v_arg_686_);
v___x_708_ = l_Lean_Expr_app___override(v_snd_694_, v_arg_686_);
v___x_709_ = 0;
v___x_710_ = l_Lean_Meta_Grind_pushEqCore___redArg(v___x_700_, v_arg_686_, v___x_708_, v___x_709_, v___y_702_, v___y_703_, v___y_704_, v___y_705_, v___y_706_, v___y_707_);
lean_dec_ref(v___y_703_);
lean_dec(v___y_702_);
return v___x_710_;
}
}
else
{
lean_object* v_a_725_; lean_object* v___x_727_; uint8_t v_isShared_728_; uint8_t v_isSharedCheck_732_; 
lean_del_object(v___x_696_);
lean_dec(v_snd_694_);
lean_dec(v_fst_693_);
lean_dec_ref(v_arg_686_);
lean_dec_ref(v_e_673_);
lean_dec(v_a_683_);
lean_dec_ref(v_a_682_);
lean_dec(v_a_681_);
lean_dec_ref(v_a_680_);
lean_dec(v_a_679_);
lean_dec_ref(v_a_678_);
lean_dec(v_a_677_);
lean_dec_ref(v_a_676_);
lean_dec(v_a_675_);
lean_dec(v_a_674_);
v_a_725_ = lean_ctor_get(v___x_698_, 0);
v_isSharedCheck_732_ = !lean_is_exclusive(v___x_698_);
if (v_isSharedCheck_732_ == 0)
{
v___x_727_ = v___x_698_;
v_isShared_728_ = v_isSharedCheck_732_;
goto v_resetjp_726_;
}
else
{
lean_inc(v_a_725_);
lean_dec(v___x_698_);
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
}
}
else
{
lean_object* v___x_734_; lean_object* v___x_736_; 
lean_dec(v_a_688_);
lean_dec_ref(v_arg_686_);
lean_dec_ref(v_e_673_);
lean_dec(v_a_683_);
lean_dec_ref(v_a_682_);
lean_dec(v_a_681_);
lean_dec_ref(v_a_680_);
lean_dec(v_a_679_);
lean_dec_ref(v_a_678_);
lean_dec(v_a_677_);
lean_dec_ref(v_a_676_);
lean_dec(v_a_675_);
lean_dec(v_a_674_);
v___x_734_ = lean_box(0);
if (v_isShared_691_ == 0)
{
lean_ctor_set(v___x_690_, 0, v___x_734_);
v___x_736_ = v___x_690_;
goto v_reusejp_735_;
}
else
{
lean_object* v_reuseFailAlloc_737_; 
v_reuseFailAlloc_737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_737_, 0, v___x_734_);
v___x_736_ = v_reuseFailAlloc_737_;
goto v_reusejp_735_;
}
v_reusejp_735_:
{
return v___x_736_;
}
}
}
}
else
{
lean_object* v_a_739_; lean_object* v___x_741_; uint8_t v_isShared_742_; uint8_t v_isSharedCheck_746_; 
lean_dec_ref(v_arg_686_);
lean_dec_ref(v_e_673_);
lean_dec(v_a_683_);
lean_dec_ref(v_a_682_);
lean_dec(v_a_681_);
lean_dec_ref(v_a_680_);
lean_dec(v_a_679_);
lean_dec_ref(v_a_678_);
lean_dec(v_a_677_);
lean_dec_ref(v_a_676_);
lean_dec(v_a_675_);
lean_dec(v_a_674_);
v_a_739_ = lean_ctor_get(v___x_687_, 0);
v_isSharedCheck_746_ = !lean_is_exclusive(v___x_687_);
if (v_isSharedCheck_746_ == 0)
{
v___x_741_ = v___x_687_;
v_isShared_742_ = v_isSharedCheck_746_;
goto v_resetjp_740_;
}
else
{
lean_inc(v_a_739_);
lean_dec(v___x_687_);
v___x_741_ = lean_box(0);
v_isShared_742_ = v_isSharedCheck_746_;
goto v_resetjp_740_;
}
v_resetjp_740_:
{
lean_object* v___x_744_; 
if (v_isShared_742_ == 0)
{
v___x_744_ = v___x_741_;
goto v_reusejp_743_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v_a_739_);
v___x_744_ = v_reuseFailAlloc_745_;
goto v_reusejp_743_;
}
v_reusejp_743_:
{
return v___x_744_;
}
}
}
}
else
{
lean_object* v___x_747_; lean_object* v___x_748_; 
lean_dec(v_a_683_);
lean_dec_ref(v_a_682_);
lean_dec(v_a_681_);
lean_dec_ref(v_a_680_);
lean_dec(v_a_679_);
lean_dec_ref(v_a_678_);
lean_dec(v_a_677_);
lean_dec_ref(v_a_676_);
lean_dec(v_a_675_);
lean_dec(v_a_674_);
lean_dec_ref(v_e_673_);
v___x_747_ = lean_box(0);
v___x_748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_748_, 0, v___x_747_);
return v___x_748_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkInjEq___boxed(lean_object* v_e_749_, lean_object* v_a_750_, lean_object* v_a_751_, lean_object* v_a_752_, lean_object* v_a_753_, lean_object* v_a_754_, lean_object* v_a_755_, lean_object* v_a_756_, lean_object* v_a_757_, lean_object* v_a_758_, lean_object* v_a_759_, lean_object* v_a_760_){
_start:
{
lean_object* v_res_761_; 
v_res_761_ = l_Lean_Meta_Grind_mkInjEq(v_e_749_, v_a_750_, v_a_751_, v_a_752_, v_a_753_, v_a_754_, v_a_755_, v_a_756_, v_a_757_, v_a_758_, v_a_759_);
return v_res_761_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__1(lean_object* v_cls_762_, lean_object* v_msg_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_){
_start:
{
lean_object* v___x_775_; 
v___x_775_ = l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__1___redArg(v_cls_762_, v_msg_763_, v___y_770_, v___y_771_, v___y_772_, v___y_773_);
return v___x_775_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__1___boxed(lean_object* v_cls_776_, lean_object* v_msg_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_){
_start:
{
lean_object* v_res_789_; 
v_res_789_ = l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__1(v_cls_776_, v_msg_777_, v___y_778_, v___y_779_, v___y_780_, v___y_781_, v___y_782_, v___y_783_, v___y_784_, v___y_785_, v___y_786_, v___y_787_);
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
return v_res_789_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1_spec__2___redArg(lean_object* v_keys_790_, lean_object* v_vals_791_, lean_object* v_i_792_, lean_object* v_k_793_){
_start:
{
lean_object* v___x_794_; uint8_t v___x_795_; 
v___x_794_ = lean_array_get_size(v_keys_790_);
v___x_795_ = lean_nat_dec_lt(v_i_792_, v___x_794_);
if (v___x_795_ == 0)
{
lean_object* v___x_796_; 
lean_dec(v_i_792_);
v___x_796_ = lean_box(0);
return v___x_796_;
}
else
{
lean_object* v_k_x27_797_; uint8_t v___x_798_; 
v_k_x27_797_ = lean_array_fget_borrowed(v_keys_790_, v_i_792_);
v___x_798_ = l_Lean_instBEqHeadIndex_beq(v_k_793_, v_k_x27_797_);
if (v___x_798_ == 0)
{
lean_object* v___x_799_; lean_object* v___x_800_; 
v___x_799_ = lean_unsigned_to_nat(1u);
v___x_800_ = lean_nat_add(v_i_792_, v___x_799_);
lean_dec(v_i_792_);
v_i_792_ = v___x_800_;
goto _start;
}
else
{
lean_object* v___x_802_; lean_object* v___x_803_; 
v___x_802_ = lean_array_fget_borrowed(v_vals_791_, v_i_792_);
lean_dec(v_i_792_);
lean_inc(v___x_802_);
v___x_803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_803_, 0, v___x_802_);
return v___x_803_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_keys_804_, lean_object* v_vals_805_, lean_object* v_i_806_, lean_object* v_k_807_){
_start:
{
lean_object* v_res_808_; 
v_res_808_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1_spec__2___redArg(v_keys_804_, v_vals_805_, v_i_806_, v_k_807_);
lean_dec(v_k_807_);
lean_dec_ref(v_vals_805_);
lean_dec_ref(v_keys_804_);
return v_res_808_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1___redArg(lean_object* v_x_809_, size_t v_x_810_, lean_object* v_x_811_){
_start:
{
if (lean_obj_tag(v_x_809_) == 0)
{
lean_object* v_es_812_; lean_object* v___x_814_; uint8_t v_isShared_815_; uint8_t v_isSharedCheck_833_; 
v_es_812_ = lean_ctor_get(v_x_809_, 0);
v_isSharedCheck_833_ = !lean_is_exclusive(v_x_809_);
if (v_isSharedCheck_833_ == 0)
{
v___x_814_ = v_x_809_;
v_isShared_815_ = v_isSharedCheck_833_;
goto v_resetjp_813_;
}
else
{
lean_inc(v_es_812_);
lean_dec(v_x_809_);
v___x_814_ = lean_box(0);
v_isShared_815_ = v_isSharedCheck_833_;
goto v_resetjp_813_;
}
v_resetjp_813_:
{
lean_object* v___x_816_; size_t v___x_817_; size_t v___x_818_; size_t v___x_819_; lean_object* v_j_820_; lean_object* v___x_821_; 
v___x_816_ = lean_box(2);
v___x_817_ = ((size_t)5ULL);
v___x_818_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1___redArg___closed__1);
v___x_819_ = lean_usize_land(v_x_810_, v___x_818_);
v_j_820_ = lean_usize_to_nat(v___x_819_);
v___x_821_ = lean_array_get(v___x_816_, v_es_812_, v_j_820_);
lean_dec(v_j_820_);
lean_dec_ref(v_es_812_);
switch(lean_obj_tag(v___x_821_))
{
case 0:
{
lean_object* v_key_822_; lean_object* v_val_823_; uint8_t v___x_824_; 
v_key_822_ = lean_ctor_get(v___x_821_, 0);
lean_inc(v_key_822_);
v_val_823_ = lean_ctor_get(v___x_821_, 1);
lean_inc(v_val_823_);
lean_dec_ref(v___x_821_);
v___x_824_ = l_Lean_instBEqHeadIndex_beq(v_x_811_, v_key_822_);
lean_dec(v_key_822_);
if (v___x_824_ == 0)
{
lean_object* v___x_825_; 
lean_dec(v_val_823_);
lean_del_object(v___x_814_);
v___x_825_ = lean_box(0);
return v___x_825_;
}
else
{
lean_object* v___x_827_; 
if (v_isShared_815_ == 0)
{
lean_ctor_set_tag(v___x_814_, 1);
lean_ctor_set(v___x_814_, 0, v_val_823_);
v___x_827_ = v___x_814_;
goto v_reusejp_826_;
}
else
{
lean_object* v_reuseFailAlloc_828_; 
v_reuseFailAlloc_828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_828_, 0, v_val_823_);
v___x_827_ = v_reuseFailAlloc_828_;
goto v_reusejp_826_;
}
v_reusejp_826_:
{
return v___x_827_;
}
}
}
case 1:
{
lean_object* v_node_829_; size_t v___x_830_; 
lean_del_object(v___x_814_);
v_node_829_ = lean_ctor_get(v___x_821_, 0);
lean_inc(v_node_829_);
lean_dec_ref(v___x_821_);
v___x_830_ = lean_usize_shift_right(v_x_810_, v___x_817_);
v_x_809_ = v_node_829_;
v_x_810_ = v___x_830_;
goto _start;
}
default: 
{
lean_object* v___x_832_; 
lean_del_object(v___x_814_);
v___x_832_ = lean_box(0);
return v___x_832_;
}
}
}
}
else
{
lean_object* v_ks_834_; lean_object* v_vs_835_; lean_object* v___x_836_; lean_object* v___x_837_; 
v_ks_834_ = lean_ctor_get(v_x_809_, 0);
lean_inc_ref(v_ks_834_);
v_vs_835_ = lean_ctor_get(v_x_809_, 1);
lean_inc_ref(v_vs_835_);
lean_dec_ref(v_x_809_);
v___x_836_ = lean_unsigned_to_nat(0u);
v___x_837_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1_spec__2___redArg(v_ks_834_, v_vs_835_, v___x_836_, v_x_811_);
lean_dec_ref(v_vs_835_);
lean_dec_ref(v_ks_834_);
return v___x_837_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1___redArg___boxed(lean_object* v_x_838_, lean_object* v_x_839_, lean_object* v_x_840_){
_start:
{
size_t v_x_10101__boxed_841_; lean_object* v_res_842_; 
v_x_10101__boxed_841_ = lean_unbox_usize(v_x_839_);
lean_dec(v_x_839_);
v_res_842_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1___redArg(v_x_838_, v_x_10101__boxed_841_, v_x_840_);
lean_dec(v_x_840_);
return v_res_842_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1___redArg(lean_object* v_x_843_, lean_object* v_x_844_){
_start:
{
uint64_t v___x_845_; size_t v___x_846_; lean_object* v___x_847_; 
v___x_845_ = l_Lean_HeadIndex_hash(v_x_844_);
v___x_846_ = lean_uint64_to_usize(v___x_845_);
v___x_847_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1___redArg(v_x_843_, v___x_846_, v_x_844_);
return v___x_847_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1___redArg___boxed(lean_object* v_x_848_, lean_object* v_x_849_){
_start:
{
lean_object* v_res_850_; 
v_res_850_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1___redArg(v_x_848_, v_x_849_);
lean_dec(v_x_849_);
return v_res_850_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__0___redArg(lean_object* v_f_851_, lean_object* v_as_x27_852_, lean_object* v_b_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_){
_start:
{
if (lean_obj_tag(v_as_x27_852_) == 0)
{
lean_object* v___x_865_; 
lean_dec(v___y_863_);
lean_dec_ref(v___y_862_);
lean_dec(v___y_861_);
lean_dec_ref(v___y_860_);
lean_dec(v___y_859_);
lean_dec_ref(v___y_858_);
lean_dec(v___y_857_);
lean_dec_ref(v___y_856_);
lean_dec(v___y_855_);
lean_dec(v___y_854_);
v___x_865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_865_, 0, v_b_853_);
return v___x_865_;
}
else
{
lean_object* v_head_866_; lean_object* v_tail_867_; lean_object* v___x_868_; uint8_t v___y_870_; uint8_t v___x_874_; 
v_head_866_ = lean_ctor_get(v_as_x27_852_, 0);
lean_inc(v_head_866_);
v_tail_867_ = lean_ctor_get(v_as_x27_852_, 1);
lean_inc(v_tail_867_);
lean_dec_ref(v_as_x27_852_);
v___x_868_ = lean_box(0);
v___x_874_ = l_Lean_Expr_isApp(v_head_866_);
if (v___x_874_ == 0)
{
v___y_870_ = v___x_874_;
goto v___jp_869_;
}
else
{
lean_object* v___x_875_; uint8_t v___x_876_; 
v___x_875_ = l_Lean_Expr_appFn_x21(v_head_866_);
v___x_876_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_875_, v_f_851_);
lean_dec_ref(v___x_875_);
v___y_870_ = v___x_876_;
goto v___jp_869_;
}
v___jp_869_:
{
if (v___y_870_ == 0)
{
lean_dec(v_head_866_);
v_as_x27_852_ = v_tail_867_;
v_b_853_ = v___x_868_;
goto _start;
}
else
{
lean_object* v___x_872_; 
lean_inc(v___y_863_);
lean_inc_ref(v___y_862_);
lean_inc(v___y_861_);
lean_inc_ref(v___y_860_);
lean_inc(v___y_859_);
lean_inc_ref(v___y_858_);
lean_inc(v___y_857_);
lean_inc_ref(v___y_856_);
lean_inc(v___y_855_);
lean_inc(v___y_854_);
v___x_872_ = l_Lean_Meta_Grind_mkInjEq(v_head_866_, v___y_854_, v___y_855_, v___y_856_, v___y_857_, v___y_858_, v___y_859_, v___y_860_, v___y_861_, v___y_862_, v___y_863_);
if (lean_obj_tag(v___x_872_) == 0)
{
lean_dec_ref(v___x_872_);
v_as_x27_852_ = v_tail_867_;
v_b_853_ = v___x_868_;
goto _start;
}
else
{
lean_dec(v_tail_867_);
lean_dec(v___y_863_);
lean_dec_ref(v___y_862_);
lean_dec(v___y_861_);
lean_dec_ref(v___y_860_);
lean_dec(v___y_859_);
lean_dec_ref(v___y_858_);
lean_dec(v___y_857_);
lean_dec_ref(v___y_856_);
lean_dec(v___y_855_);
lean_dec(v___y_854_);
return v___x_872_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__0___redArg___boxed(lean_object* v_f_877_, lean_object* v_as_x27_878_, lean_object* v_b_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_){
_start:
{
lean_object* v_res_891_; 
v_res_891_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__0___redArg(v_f_877_, v_as_x27_878_, v_b_879_, v___y_880_, v___y_881_, v___y_882_, v___y_883_, v___y_884_, v___y_885_, v___y_886_, v___y_887_, v___y_888_, v___y_889_);
lean_dec_ref(v_f_877_);
return v_res_891_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn(lean_object* v_us_892_, lean_object* v_00_u03b1_893_, lean_object* v_00_u03b2_894_, lean_object* v_f_895_, lean_object* v_h_896_, lean_object* v_a_897_, lean_object* v_a_898_, lean_object* v_a_899_, lean_object* v_a_900_, lean_object* v_a_901_, lean_object* v_a_902_, lean_object* v_a_903_, lean_object* v_a_904_, lean_object* v_a_905_, lean_object* v_a_906_){
_start:
{
lean_object* v___x_908_; lean_object* v_toGoalState_909_; lean_object* v_inj_910_; lean_object* v_mvarId_911_; lean_object* v___x_913_; uint8_t v_isShared_914_; uint8_t v_isSharedCheck_976_; 
v___x_908_ = lean_st_ref_take(v_a_897_);
v_toGoalState_909_ = lean_ctor_get(v___x_908_, 0);
lean_inc_ref(v_toGoalState_909_);
v_inj_910_ = lean_ctor_get(v_toGoalState_909_, 14);
lean_inc_ref(v_inj_910_);
v_mvarId_911_ = lean_ctor_get(v___x_908_, 1);
v_isSharedCheck_976_ = !lean_is_exclusive(v___x_908_);
if (v_isSharedCheck_976_ == 0)
{
lean_object* v_unused_977_; 
v_unused_977_ = lean_ctor_get(v___x_908_, 0);
lean_dec(v_unused_977_);
v___x_913_ = v___x_908_;
v_isShared_914_ = v_isSharedCheck_976_;
goto v_resetjp_912_;
}
else
{
lean_inc(v_mvarId_911_);
lean_dec(v___x_908_);
v___x_913_ = lean_box(0);
v_isShared_914_ = v_isSharedCheck_976_;
goto v_resetjp_912_;
}
v_resetjp_912_:
{
lean_object* v_nextDeclIdx_915_; lean_object* v_canon_916_; lean_object* v_enodeMap_917_; lean_object* v_exprs_918_; lean_object* v_parents_919_; lean_object* v_congrTable_920_; lean_object* v_appMap_921_; lean_object* v_indicesFound_922_; lean_object* v_newFacts_923_; uint8_t v_inconsistent_924_; lean_object* v_nextIdx_925_; lean_object* v_newRawFacts_926_; lean_object* v_facts_927_; lean_object* v_extThms_928_; lean_object* v_ematch_929_; lean_object* v_split_930_; lean_object* v_clean_931_; lean_object* v_sstates_932_; lean_object* v___x_934_; uint8_t v_isShared_935_; uint8_t v_isSharedCheck_974_; 
v_nextDeclIdx_915_ = lean_ctor_get(v_toGoalState_909_, 0);
v_canon_916_ = lean_ctor_get(v_toGoalState_909_, 1);
v_enodeMap_917_ = lean_ctor_get(v_toGoalState_909_, 2);
v_exprs_918_ = lean_ctor_get(v_toGoalState_909_, 3);
v_parents_919_ = lean_ctor_get(v_toGoalState_909_, 4);
v_congrTable_920_ = lean_ctor_get(v_toGoalState_909_, 5);
v_appMap_921_ = lean_ctor_get(v_toGoalState_909_, 6);
v_indicesFound_922_ = lean_ctor_get(v_toGoalState_909_, 7);
v_newFacts_923_ = lean_ctor_get(v_toGoalState_909_, 8);
v_inconsistent_924_ = lean_ctor_get_uint8(v_toGoalState_909_, sizeof(void*)*18);
v_nextIdx_925_ = lean_ctor_get(v_toGoalState_909_, 9);
v_newRawFacts_926_ = lean_ctor_get(v_toGoalState_909_, 10);
v_facts_927_ = lean_ctor_get(v_toGoalState_909_, 11);
v_extThms_928_ = lean_ctor_get(v_toGoalState_909_, 12);
v_ematch_929_ = lean_ctor_get(v_toGoalState_909_, 13);
v_split_930_ = lean_ctor_get(v_toGoalState_909_, 15);
v_clean_931_ = lean_ctor_get(v_toGoalState_909_, 16);
v_sstates_932_ = lean_ctor_get(v_toGoalState_909_, 17);
v_isSharedCheck_974_ = !lean_is_exclusive(v_toGoalState_909_);
if (v_isSharedCheck_974_ == 0)
{
lean_object* v_unused_975_; 
v_unused_975_ = lean_ctor_get(v_toGoalState_909_, 14);
lean_dec(v_unused_975_);
v___x_934_ = v_toGoalState_909_;
v_isShared_935_ = v_isSharedCheck_974_;
goto v_resetjp_933_;
}
else
{
lean_inc(v_sstates_932_);
lean_inc(v_clean_931_);
lean_inc(v_split_930_);
lean_inc(v_ematch_929_);
lean_inc(v_extThms_928_);
lean_inc(v_facts_927_);
lean_inc(v_newRawFacts_926_);
lean_inc(v_nextIdx_925_);
lean_inc(v_newFacts_923_);
lean_inc(v_indicesFound_922_);
lean_inc(v_appMap_921_);
lean_inc(v_congrTable_920_);
lean_inc(v_parents_919_);
lean_inc(v_exprs_918_);
lean_inc(v_enodeMap_917_);
lean_inc(v_canon_916_);
lean_inc(v_nextDeclIdx_915_);
lean_dec(v_toGoalState_909_);
v___x_934_ = lean_box(0);
v_isShared_935_ = v_isSharedCheck_974_;
goto v_resetjp_933_;
}
v_resetjp_933_:
{
lean_object* v_thms_936_; lean_object* v_fns_937_; lean_object* v___x_939_; uint8_t v_isShared_940_; uint8_t v_isSharedCheck_973_; 
v_thms_936_ = lean_ctor_get(v_inj_910_, 0);
v_fns_937_ = lean_ctor_get(v_inj_910_, 1);
v_isSharedCheck_973_ = !lean_is_exclusive(v_inj_910_);
if (v_isSharedCheck_973_ == 0)
{
v___x_939_ = v_inj_910_;
v_isShared_940_ = v_isSharedCheck_973_;
goto v_resetjp_938_;
}
else
{
lean_inc(v_fns_937_);
lean_inc(v_thms_936_);
lean_dec(v_inj_910_);
v___x_939_ = lean_box(0);
v_isShared_940_ = v_isSharedCheck_973_;
goto v_resetjp_938_;
}
v_resetjp_938_:
{
lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_945_; 
v___x_941_ = lean_box(0);
v___x_942_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_942_, 0, v_us_892_);
lean_ctor_set(v___x_942_, 1, v_00_u03b1_893_);
lean_ctor_set(v___x_942_, 2, v_00_u03b2_894_);
lean_ctor_set(v___x_942_, 3, v_h_896_);
lean_ctor_set(v___x_942_, 4, v___x_941_);
lean_inc_ref(v_f_895_);
v___x_943_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2___redArg(v_fns_937_, v_f_895_, v___x_942_);
if (v_isShared_940_ == 0)
{
lean_ctor_set(v___x_939_, 1, v___x_943_);
v___x_945_ = v___x_939_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_972_; 
v_reuseFailAlloc_972_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_972_, 0, v_thms_936_);
lean_ctor_set(v_reuseFailAlloc_972_, 1, v___x_943_);
v___x_945_ = v_reuseFailAlloc_972_;
goto v_reusejp_944_;
}
v_reusejp_944_:
{
lean_object* v___x_947_; 
if (v_isShared_935_ == 0)
{
lean_ctor_set(v___x_934_, 14, v___x_945_);
v___x_947_ = v___x_934_;
goto v_reusejp_946_;
}
else
{
lean_object* v_reuseFailAlloc_971_; 
v_reuseFailAlloc_971_ = lean_alloc_ctor(0, 18, 1);
lean_ctor_set(v_reuseFailAlloc_971_, 0, v_nextDeclIdx_915_);
lean_ctor_set(v_reuseFailAlloc_971_, 1, v_canon_916_);
lean_ctor_set(v_reuseFailAlloc_971_, 2, v_enodeMap_917_);
lean_ctor_set(v_reuseFailAlloc_971_, 3, v_exprs_918_);
lean_ctor_set(v_reuseFailAlloc_971_, 4, v_parents_919_);
lean_ctor_set(v_reuseFailAlloc_971_, 5, v_congrTable_920_);
lean_ctor_set(v_reuseFailAlloc_971_, 6, v_appMap_921_);
lean_ctor_set(v_reuseFailAlloc_971_, 7, v_indicesFound_922_);
lean_ctor_set(v_reuseFailAlloc_971_, 8, v_newFacts_923_);
lean_ctor_set(v_reuseFailAlloc_971_, 9, v_nextIdx_925_);
lean_ctor_set(v_reuseFailAlloc_971_, 10, v_newRawFacts_926_);
lean_ctor_set(v_reuseFailAlloc_971_, 11, v_facts_927_);
lean_ctor_set(v_reuseFailAlloc_971_, 12, v_extThms_928_);
lean_ctor_set(v_reuseFailAlloc_971_, 13, v_ematch_929_);
lean_ctor_set(v_reuseFailAlloc_971_, 14, v___x_945_);
lean_ctor_set(v_reuseFailAlloc_971_, 15, v_split_930_);
lean_ctor_set(v_reuseFailAlloc_971_, 16, v_clean_931_);
lean_ctor_set(v_reuseFailAlloc_971_, 17, v_sstates_932_);
lean_ctor_set_uint8(v_reuseFailAlloc_971_, sizeof(void*)*18, v_inconsistent_924_);
v___x_947_ = v_reuseFailAlloc_971_;
goto v_reusejp_946_;
}
v_reusejp_946_:
{
lean_object* v___x_949_; 
if (v_isShared_914_ == 0)
{
lean_ctor_set(v___x_913_, 0, v___x_947_);
v___x_949_ = v___x_913_;
goto v_reusejp_948_;
}
else
{
lean_object* v_reuseFailAlloc_970_; 
v_reuseFailAlloc_970_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_970_, 0, v___x_947_);
lean_ctor_set(v_reuseFailAlloc_970_, 1, v_mvarId_911_);
v___x_949_ = v_reuseFailAlloc_970_;
goto v_reusejp_948_;
}
v_reusejp_948_:
{
lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___y_953_; lean_object* v_toGoalState_964_; lean_object* v_appMap_965_; lean_object* v___x_966_; lean_object* v___x_967_; 
v___x_950_ = lean_st_ref_set(v_a_897_, v___x_949_);
v___x_951_ = lean_st_ref_get(v_a_897_);
v_toGoalState_964_ = lean_ctor_get(v___x_951_, 0);
lean_inc_ref(v_toGoalState_964_);
lean_dec(v___x_951_);
v_appMap_965_ = lean_ctor_get(v_toGoalState_964_, 6);
lean_inc_ref(v_appMap_965_);
lean_dec_ref(v_toGoalState_964_);
lean_inc_ref(v_f_895_);
v___x_966_ = l_Lean_Expr_toHeadIndex(v_f_895_);
v___x_967_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1___redArg(v_appMap_965_, v___x_966_);
lean_dec(v___x_966_);
if (lean_obj_tag(v___x_967_) == 0)
{
lean_object* v___x_968_; 
v___x_968_ = lean_box(0);
v___y_953_ = v___x_968_;
goto v___jp_952_;
}
else
{
lean_object* v_val_969_; 
v_val_969_ = lean_ctor_get(v___x_967_, 0);
lean_inc(v_val_969_);
lean_dec_ref(v___x_967_);
v___y_953_ = v_val_969_;
goto v___jp_952_;
}
v___jp_952_:
{
lean_object* v___x_954_; lean_object* v___x_955_; 
v___x_954_ = lean_box(0);
v___x_955_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__0___redArg(v_f_895_, v___y_953_, v___x_954_, v_a_897_, v_a_898_, v_a_899_, v_a_900_, v_a_901_, v_a_902_, v_a_903_, v_a_904_, v_a_905_, v_a_906_);
lean_dec_ref(v_f_895_);
if (lean_obj_tag(v___x_955_) == 0)
{
lean_object* v___x_957_; uint8_t v_isShared_958_; uint8_t v_isSharedCheck_962_; 
v_isSharedCheck_962_ = !lean_is_exclusive(v___x_955_);
if (v_isSharedCheck_962_ == 0)
{
lean_object* v_unused_963_; 
v_unused_963_ = lean_ctor_get(v___x_955_, 0);
lean_dec(v_unused_963_);
v___x_957_ = v___x_955_;
v_isShared_958_ = v_isSharedCheck_962_;
goto v_resetjp_956_;
}
else
{
lean_dec(v___x_955_);
v___x_957_ = lean_box(0);
v_isShared_958_ = v_isSharedCheck_962_;
goto v_resetjp_956_;
}
v_resetjp_956_:
{
lean_object* v___x_960_; 
if (v_isShared_958_ == 0)
{
lean_ctor_set(v___x_957_, 0, v___x_954_);
v___x_960_ = v___x_957_;
goto v_reusejp_959_;
}
else
{
lean_object* v_reuseFailAlloc_961_; 
v_reuseFailAlloc_961_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_961_, 0, v___x_954_);
v___x_960_ = v_reuseFailAlloc_961_;
goto v_reusejp_959_;
}
v_reusejp_959_:
{
return v___x_960_;
}
}
}
else
{
return v___x_955_;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn___boxed(lean_object* v_us_978_, lean_object* v_00_u03b1_979_, lean_object* v_00_u03b2_980_, lean_object* v_f_981_, lean_object* v_h_982_, lean_object* v_a_983_, lean_object* v_a_984_, lean_object* v_a_985_, lean_object* v_a_986_, lean_object* v_a_987_, lean_object* v_a_988_, lean_object* v_a_989_, lean_object* v_a_990_, lean_object* v_a_991_, lean_object* v_a_992_, lean_object* v_a_993_){
_start:
{
lean_object* v_res_994_; 
v_res_994_ = l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn(v_us_978_, v_00_u03b1_979_, v_00_u03b2_980_, v_f_981_, v_h_982_, v_a_983_, v_a_984_, v_a_985_, v_a_986_, v_a_987_, v_a_988_, v_a_989_, v_a_990_, v_a_991_, v_a_992_);
return v_res_994_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__0(lean_object* v_f_995_, lean_object* v_as_996_, lean_object* v_as_x27_997_, lean_object* v_b_998_, lean_object* v_a_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_){
_start:
{
lean_object* v___x_1011_; 
v___x_1011_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__0___redArg(v_f_995_, v_as_x27_997_, v_b_998_, v___y_1000_, v___y_1001_, v___y_1002_, v___y_1003_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_, v___y_1008_, v___y_1009_);
return v___x_1011_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__0___boxed(lean_object* v_f_1012_, lean_object* v_as_1013_, lean_object* v_as_x27_1014_, lean_object* v_b_1015_, lean_object* v_a_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_){
_start:
{
lean_object* v_res_1028_; 
v_res_1028_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__0(v_f_1012_, v_as_1013_, v_as_x27_1014_, v_b_1015_, v_a_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_, v___y_1023_, v___y_1024_, v___y_1025_, v___y_1026_);
lean_dec(v_as_1013_);
lean_dec_ref(v_f_1012_);
return v_res_1028_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1(lean_object* v_00_u03b2_1029_, lean_object* v_x_1030_, lean_object* v_x_1031_){
_start:
{
lean_object* v___x_1032_; 
v___x_1032_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1___redArg(v_x_1030_, v_x_1031_);
return v___x_1032_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1___boxed(lean_object* v_00_u03b2_1033_, lean_object* v_x_1034_, lean_object* v_x_1035_){
_start:
{
lean_object* v_res_1036_; 
v_res_1036_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1(v_00_u03b2_1033_, v_x_1034_, v_x_1035_);
lean_dec(v_x_1035_);
return v_res_1036_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1(lean_object* v_00_u03b2_1037_, lean_object* v_x_1038_, size_t v_x_1039_, lean_object* v_x_1040_){
_start:
{
lean_object* v___x_1041_; 
v___x_1041_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1___redArg(v_x_1038_, v_x_1039_, v_x_1040_);
return v___x_1041_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1___boxed(lean_object* v_00_u03b2_1042_, lean_object* v_x_1043_, lean_object* v_x_1044_, lean_object* v_x_1045_){
_start:
{
size_t v_x_10404__boxed_1046_; lean_object* v_res_1047_; 
v_x_10404__boxed_1046_ = lean_unbox_usize(v_x_1044_);
lean_dec(v_x_1044_);
v_res_1047_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1(v_00_u03b2_1042_, v_x_1043_, v_x_10404__boxed_1046_, v_x_1045_);
lean_dec(v_x_1045_);
return v_res_1047_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_1048_, lean_object* v_keys_1049_, lean_object* v_vals_1050_, lean_object* v_heq_1051_, lean_object* v_i_1052_, lean_object* v_k_1053_){
_start:
{
lean_object* v___x_1054_; 
v___x_1054_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1_spec__2___redArg(v_keys_1049_, v_vals_1050_, v_i_1052_, v_k_1053_);
return v___x_1054_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1055_, lean_object* v_keys_1056_, lean_object* v_vals_1057_, lean_object* v_heq_1058_, lean_object* v_i_1059_, lean_object* v_k_1060_){
_start:
{
lean_object* v_res_1061_; 
v_res_1061_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1_spec__2(v_00_u03b2_1055_, v_keys_1056_, v_vals_1057_, v_heq_1058_, v_i_1059_, v_k_1060_);
lean_dec(v_k_1060_);
lean_dec_ref(v_vals_1057_);
lean_dec_ref(v_keys_1056_);
return v_res_1061_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj(lean_object* v_e_1067_, lean_object* v_a_1068_, lean_object* v_a_1069_, lean_object* v_a_1070_, lean_object* v_a_1071_, lean_object* v_a_1072_, lean_object* v_a_1073_, lean_object* v_a_1074_, lean_object* v_a_1075_, lean_object* v_a_1076_, lean_object* v_a_1077_){
_start:
{
lean_object* v___x_1082_; uint8_t v___x_1083_; 
lean_inc_ref(v_e_1067_);
v___x_1082_ = l_Lean_Expr_cleanupAnnotations(v_e_1067_);
v___x_1083_ = l_Lean_Expr_isApp(v___x_1082_);
if (v___x_1083_ == 0)
{
lean_dec_ref(v___x_1082_);
lean_dec(v_a_1077_);
lean_dec_ref(v_a_1076_);
lean_dec(v_a_1075_);
lean_dec_ref(v_a_1074_);
lean_dec(v_a_1073_);
lean_dec_ref(v_a_1072_);
lean_dec(v_a_1071_);
lean_dec_ref(v_a_1070_);
lean_dec(v_a_1069_);
lean_dec(v_a_1068_);
lean_dec_ref(v_e_1067_);
goto v___jp_1079_;
}
else
{
lean_object* v_arg_1084_; lean_object* v___x_1085_; uint8_t v___x_1086_; 
v_arg_1084_ = lean_ctor_get(v___x_1082_, 1);
lean_inc_ref(v_arg_1084_);
v___x_1085_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1082_);
v___x_1086_ = l_Lean_Expr_isApp(v___x_1085_);
if (v___x_1086_ == 0)
{
lean_dec_ref(v___x_1085_);
lean_dec_ref(v_arg_1084_);
lean_dec(v_a_1077_);
lean_dec_ref(v_a_1076_);
lean_dec(v_a_1075_);
lean_dec_ref(v_a_1074_);
lean_dec(v_a_1073_);
lean_dec_ref(v_a_1072_);
lean_dec(v_a_1071_);
lean_dec_ref(v_a_1070_);
lean_dec(v_a_1069_);
lean_dec(v_a_1068_);
lean_dec_ref(v_e_1067_);
goto v___jp_1079_;
}
else
{
lean_object* v_arg_1087_; lean_object* v___x_1088_; uint8_t v___x_1089_; 
v_arg_1087_ = lean_ctor_get(v___x_1085_, 1);
lean_inc_ref(v_arg_1087_);
v___x_1088_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1085_);
v___x_1089_ = l_Lean_Expr_isApp(v___x_1088_);
if (v___x_1089_ == 0)
{
lean_dec_ref(v___x_1088_);
lean_dec_ref(v_arg_1087_);
lean_dec_ref(v_arg_1084_);
lean_dec(v_a_1077_);
lean_dec_ref(v_a_1076_);
lean_dec(v_a_1075_);
lean_dec_ref(v_a_1074_);
lean_dec(v_a_1073_);
lean_dec_ref(v_a_1072_);
lean_dec(v_a_1071_);
lean_dec_ref(v_a_1070_);
lean_dec(v_a_1069_);
lean_dec(v_a_1068_);
lean_dec_ref(v_e_1067_);
goto v___jp_1079_;
}
else
{
lean_object* v_arg_1090_; lean_object* v___x_1091_; lean_object* v_f_1093_; lean_object* v___y_1094_; lean_object* v___y_1095_; lean_object* v___y_1096_; lean_object* v___y_1097_; lean_object* v___y_1098_; lean_object* v___y_1099_; lean_object* v___y_1100_; lean_object* v___y_1101_; lean_object* v___y_1102_; lean_object* v___y_1103_; lean_object* v___x_1117_; uint8_t v___x_1118_; 
v_arg_1090_ = lean_ctor_get(v___x_1088_, 1);
lean_inc_ref(v_arg_1090_);
v___x_1091_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1088_);
v___x_1117_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj___closed__2));
v___x_1118_ = l_Lean_Expr_isConstOf(v___x_1091_, v___x_1117_);
if (v___x_1118_ == 0)
{
lean_dec_ref(v___x_1091_);
lean_dec_ref(v_arg_1090_);
lean_dec_ref(v_arg_1087_);
lean_dec_ref(v_arg_1084_);
lean_dec(v_a_1077_);
lean_dec_ref(v_a_1076_);
lean_dec(v_a_1075_);
lean_dec_ref(v_a_1074_);
lean_dec(v_a_1073_);
lean_dec_ref(v_a_1072_);
lean_dec(v_a_1071_);
lean_dec_ref(v_a_1070_);
lean_dec(v_a_1069_);
lean_dec(v_a_1068_);
lean_dec_ref(v_e_1067_);
goto v___jp_1079_;
}
else
{
lean_object* v___x_1119_; 
lean_inc_ref(v_e_1067_);
v___x_1119_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_e_1067_, v_a_1068_, v_a_1072_, v_a_1074_, v_a_1075_, v_a_1076_, v_a_1077_);
if (lean_obj_tag(v___x_1119_) == 0)
{
lean_object* v_a_1120_; lean_object* v___x_1122_; uint8_t v_isShared_1123_; uint8_t v_isSharedCheck_1153_; 
v_a_1120_ = lean_ctor_get(v___x_1119_, 0);
v_isSharedCheck_1153_ = !lean_is_exclusive(v___x_1119_);
if (v_isSharedCheck_1153_ == 0)
{
v___x_1122_ = v___x_1119_;
v_isShared_1123_ = v_isSharedCheck_1153_;
goto v_resetjp_1121_;
}
else
{
lean_inc(v_a_1120_);
lean_dec(v___x_1119_);
v___x_1122_ = lean_box(0);
v_isShared_1123_ = v_isSharedCheck_1153_;
goto v_resetjp_1121_;
}
v_resetjp_1121_:
{
uint8_t v___x_1124_; 
v___x_1124_ = lean_unbox(v_a_1120_);
lean_dec(v_a_1120_);
if (v___x_1124_ == 0)
{
lean_object* v___x_1125_; lean_object* v___x_1127_; 
lean_dec_ref(v___x_1091_);
lean_dec_ref(v_arg_1090_);
lean_dec_ref(v_arg_1087_);
lean_dec_ref(v_arg_1084_);
lean_dec(v_a_1077_);
lean_dec_ref(v_a_1076_);
lean_dec(v_a_1075_);
lean_dec_ref(v_a_1074_);
lean_dec(v_a_1073_);
lean_dec_ref(v_a_1072_);
lean_dec(v_a_1071_);
lean_dec_ref(v_a_1070_);
lean_dec(v_a_1069_);
lean_dec(v_a_1068_);
lean_dec_ref(v_e_1067_);
v___x_1125_ = lean_box(0);
if (v_isShared_1123_ == 0)
{
lean_ctor_set(v___x_1122_, 0, v___x_1125_);
v___x_1127_ = v___x_1122_;
goto v_reusejp_1126_;
}
else
{
lean_object* v_reuseFailAlloc_1128_; 
v_reuseFailAlloc_1128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1128_, 0, v___x_1125_);
v___x_1127_ = v_reuseFailAlloc_1128_;
goto v_reusejp_1126_;
}
v_reusejp_1126_:
{
return v___x_1127_;
}
}
else
{
lean_object* v___x_1129_; uint8_t v___x_1130_; 
lean_del_object(v___x_1122_);
lean_inc_ref(v_arg_1084_);
v___x_1129_ = l_Lean_Expr_eta(v_arg_1084_);
v___x_1130_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_arg_1084_, v___x_1129_);
if (v___x_1130_ == 0)
{
lean_object* v___x_1131_; 
lean_dec_ref(v_arg_1084_);
lean_inc(v_a_1077_);
lean_inc_ref(v_a_1076_);
lean_inc(v_a_1075_);
lean_inc_ref(v_a_1074_);
lean_inc(v_a_1073_);
lean_inc_ref(v_a_1072_);
lean_inc(v_a_1071_);
lean_inc_ref(v_a_1070_);
lean_inc(v_a_1069_);
lean_inc(v_a_1068_);
v___x_1131_ = l_Lean_Meta_Grind_preprocessLight(v___x_1129_, v_a_1068_, v_a_1069_, v_a_1070_, v_a_1071_, v_a_1072_, v_a_1073_, v_a_1074_, v_a_1075_, v_a_1076_, v_a_1077_);
if (lean_obj_tag(v___x_1131_) == 0)
{
lean_object* v_a_1132_; lean_object* v___x_1133_; 
v_a_1132_ = lean_ctor_get(v___x_1131_, 0);
lean_inc(v_a_1132_);
lean_dec_ref(v___x_1131_);
v___x_1133_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_1067_, v_a_1068_);
if (lean_obj_tag(v___x_1133_) == 0)
{
lean_object* v_a_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; 
v_a_1134_ = lean_ctor_get(v___x_1133_, 0);
lean_inc(v_a_1134_);
lean_dec_ref(v___x_1133_);
v___x_1135_ = lean_box(0);
lean_inc(v_a_1077_);
lean_inc_ref(v_a_1076_);
lean_inc(v_a_1075_);
lean_inc_ref(v_a_1074_);
lean_inc(v_a_1073_);
lean_inc_ref(v_a_1072_);
lean_inc(v_a_1071_);
lean_inc_ref(v_a_1070_);
lean_inc(v_a_1069_);
lean_inc(v_a_1068_);
lean_inc(v_a_1132_);
v___x_1136_ = lean_grind_internalize(v_a_1132_, v_a_1134_, v___x_1135_, v_a_1068_, v_a_1069_, v_a_1070_, v_a_1071_, v_a_1072_, v_a_1073_, v_a_1074_, v_a_1075_, v_a_1076_, v_a_1077_);
if (lean_obj_tag(v___x_1136_) == 0)
{
lean_dec_ref(v___x_1136_);
v_f_1093_ = v_a_1132_;
v___y_1094_ = v_a_1068_;
v___y_1095_ = v_a_1069_;
v___y_1096_ = v_a_1070_;
v___y_1097_ = v_a_1071_;
v___y_1098_ = v_a_1072_;
v___y_1099_ = v_a_1073_;
v___y_1100_ = v_a_1074_;
v___y_1101_ = v_a_1075_;
v___y_1102_ = v_a_1076_;
v___y_1103_ = v_a_1077_;
goto v___jp_1092_;
}
else
{
lean_dec(v_a_1132_);
lean_dec_ref(v___x_1091_);
lean_dec_ref(v_arg_1090_);
lean_dec_ref(v_arg_1087_);
lean_dec(v_a_1077_);
lean_dec_ref(v_a_1076_);
lean_dec(v_a_1075_);
lean_dec_ref(v_a_1074_);
lean_dec(v_a_1073_);
lean_dec_ref(v_a_1072_);
lean_dec(v_a_1071_);
lean_dec_ref(v_a_1070_);
lean_dec(v_a_1069_);
lean_dec(v_a_1068_);
lean_dec_ref(v_e_1067_);
return v___x_1136_;
}
}
else
{
lean_object* v_a_1137_; lean_object* v___x_1139_; uint8_t v_isShared_1140_; uint8_t v_isSharedCheck_1144_; 
lean_dec(v_a_1132_);
lean_dec_ref(v___x_1091_);
lean_dec_ref(v_arg_1090_);
lean_dec_ref(v_arg_1087_);
lean_dec(v_a_1077_);
lean_dec_ref(v_a_1076_);
lean_dec(v_a_1075_);
lean_dec_ref(v_a_1074_);
lean_dec(v_a_1073_);
lean_dec_ref(v_a_1072_);
lean_dec(v_a_1071_);
lean_dec_ref(v_a_1070_);
lean_dec(v_a_1069_);
lean_dec(v_a_1068_);
lean_dec_ref(v_e_1067_);
v_a_1137_ = lean_ctor_get(v___x_1133_, 0);
v_isSharedCheck_1144_ = !lean_is_exclusive(v___x_1133_);
if (v_isSharedCheck_1144_ == 0)
{
v___x_1139_ = v___x_1133_;
v_isShared_1140_ = v_isSharedCheck_1144_;
goto v_resetjp_1138_;
}
else
{
lean_inc(v_a_1137_);
lean_dec(v___x_1133_);
v___x_1139_ = lean_box(0);
v_isShared_1140_ = v_isSharedCheck_1144_;
goto v_resetjp_1138_;
}
v_resetjp_1138_:
{
lean_object* v___x_1142_; 
if (v_isShared_1140_ == 0)
{
v___x_1142_ = v___x_1139_;
goto v_reusejp_1141_;
}
else
{
lean_object* v_reuseFailAlloc_1143_; 
v_reuseFailAlloc_1143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1143_, 0, v_a_1137_);
v___x_1142_ = v_reuseFailAlloc_1143_;
goto v_reusejp_1141_;
}
v_reusejp_1141_:
{
return v___x_1142_;
}
}
}
}
else
{
lean_object* v_a_1145_; lean_object* v___x_1147_; uint8_t v_isShared_1148_; uint8_t v_isSharedCheck_1152_; 
lean_dec_ref(v___x_1091_);
lean_dec_ref(v_arg_1090_);
lean_dec_ref(v_arg_1087_);
lean_dec(v_a_1077_);
lean_dec_ref(v_a_1076_);
lean_dec(v_a_1075_);
lean_dec_ref(v_a_1074_);
lean_dec(v_a_1073_);
lean_dec_ref(v_a_1072_);
lean_dec(v_a_1071_);
lean_dec_ref(v_a_1070_);
lean_dec(v_a_1069_);
lean_dec(v_a_1068_);
lean_dec_ref(v_e_1067_);
v_a_1145_ = lean_ctor_get(v___x_1131_, 0);
v_isSharedCheck_1152_ = !lean_is_exclusive(v___x_1131_);
if (v_isSharedCheck_1152_ == 0)
{
v___x_1147_ = v___x_1131_;
v_isShared_1148_ = v_isSharedCheck_1152_;
goto v_resetjp_1146_;
}
else
{
lean_inc(v_a_1145_);
lean_dec(v___x_1131_);
v___x_1147_ = lean_box(0);
v_isShared_1148_ = v_isSharedCheck_1152_;
goto v_resetjp_1146_;
}
v_resetjp_1146_:
{
lean_object* v___x_1150_; 
if (v_isShared_1148_ == 0)
{
v___x_1150_ = v___x_1147_;
goto v_reusejp_1149_;
}
else
{
lean_object* v_reuseFailAlloc_1151_; 
v_reuseFailAlloc_1151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1151_, 0, v_a_1145_);
v___x_1150_ = v_reuseFailAlloc_1151_;
goto v_reusejp_1149_;
}
v_reusejp_1149_:
{
return v___x_1150_;
}
}
}
}
else
{
lean_dec_ref(v___x_1129_);
v_f_1093_ = v_arg_1084_;
v___y_1094_ = v_a_1068_;
v___y_1095_ = v_a_1069_;
v___y_1096_ = v_a_1070_;
v___y_1097_ = v_a_1071_;
v___y_1098_ = v_a_1072_;
v___y_1099_ = v_a_1073_;
v___y_1100_ = v_a_1074_;
v___y_1101_ = v_a_1075_;
v___y_1102_ = v_a_1076_;
v___y_1103_ = v_a_1077_;
goto v___jp_1092_;
}
}
}
}
else
{
lean_object* v_a_1154_; lean_object* v___x_1156_; uint8_t v_isShared_1157_; uint8_t v_isSharedCheck_1161_; 
lean_dec_ref(v___x_1091_);
lean_dec_ref(v_arg_1090_);
lean_dec_ref(v_arg_1087_);
lean_dec_ref(v_arg_1084_);
lean_dec(v_a_1077_);
lean_dec_ref(v_a_1076_);
lean_dec(v_a_1075_);
lean_dec_ref(v_a_1074_);
lean_dec(v_a_1073_);
lean_dec_ref(v_a_1072_);
lean_dec(v_a_1071_);
lean_dec_ref(v_a_1070_);
lean_dec(v_a_1069_);
lean_dec(v_a_1068_);
lean_dec_ref(v_e_1067_);
v_a_1154_ = lean_ctor_get(v___x_1119_, 0);
v_isSharedCheck_1161_ = !lean_is_exclusive(v___x_1119_);
if (v_isSharedCheck_1161_ == 0)
{
v___x_1156_ = v___x_1119_;
v_isShared_1157_ = v_isSharedCheck_1161_;
goto v_resetjp_1155_;
}
else
{
lean_inc(v_a_1154_);
lean_dec(v___x_1119_);
v___x_1156_ = lean_box(0);
v_isShared_1157_ = v_isSharedCheck_1161_;
goto v_resetjp_1155_;
}
v_resetjp_1155_:
{
lean_object* v___x_1159_; 
if (v_isShared_1157_ == 0)
{
v___x_1159_ = v___x_1156_;
goto v_reusejp_1158_;
}
else
{
lean_object* v_reuseFailAlloc_1160_; 
v_reuseFailAlloc_1160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1160_, 0, v_a_1154_);
v___x_1159_ = v_reuseFailAlloc_1160_;
goto v_reusejp_1158_;
}
v_reusejp_1158_:
{
return v___x_1159_;
}
}
}
}
v___jp_1092_:
{
lean_object* v___x_1104_; 
lean_inc(v___y_1103_);
lean_inc_ref(v___y_1102_);
lean_inc(v___y_1101_);
lean_inc_ref(v___y_1100_);
lean_inc(v___y_1099_);
lean_inc_ref(v___y_1098_);
lean_inc(v___y_1097_);
lean_inc_ref(v___y_1096_);
lean_inc(v___y_1095_);
lean_inc(v___y_1094_);
lean_inc_ref(v_e_1067_);
v___x_1104_ = l_Lean_Meta_Grind_mkEqTrueProof(v_e_1067_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_, v___y_1103_);
if (lean_obj_tag(v___x_1104_) == 0)
{
lean_object* v_a_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; 
v_a_1105_ = lean_ctor_get(v___x_1104_, 0);
lean_inc(v_a_1105_);
lean_dec_ref(v___x_1104_);
v___x_1106_ = l_Lean_Expr_constLevels_x21(v___x_1091_);
lean_dec_ref(v___x_1091_);
v___x_1107_ = l_Lean_Meta_mkOfEqTrueCore(v_e_1067_, v_a_1105_);
v___x_1108_ = l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn(v___x_1106_, v_arg_1090_, v_arg_1087_, v_f_1093_, v___x_1107_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_, v___y_1103_);
return v___x_1108_;
}
else
{
lean_object* v_a_1109_; lean_object* v___x_1111_; uint8_t v_isShared_1112_; uint8_t v_isSharedCheck_1116_; 
lean_dec(v___y_1103_);
lean_dec_ref(v___y_1102_);
lean_dec(v___y_1101_);
lean_dec_ref(v___y_1100_);
lean_dec(v___y_1099_);
lean_dec_ref(v___y_1098_);
lean_dec(v___y_1097_);
lean_dec_ref(v___y_1096_);
lean_dec(v___y_1095_);
lean_dec(v___y_1094_);
lean_dec_ref(v_f_1093_);
lean_dec_ref(v___x_1091_);
lean_dec_ref(v_arg_1090_);
lean_dec_ref(v_arg_1087_);
lean_dec_ref(v_e_1067_);
v_a_1109_ = lean_ctor_get(v___x_1104_, 0);
v_isSharedCheck_1116_ = !lean_is_exclusive(v___x_1104_);
if (v_isSharedCheck_1116_ == 0)
{
v___x_1111_ = v___x_1104_;
v_isShared_1112_ = v_isSharedCheck_1116_;
goto v_resetjp_1110_;
}
else
{
lean_inc(v_a_1109_);
lean_dec(v___x_1104_);
v___x_1111_ = lean_box(0);
v_isShared_1112_ = v_isSharedCheck_1116_;
goto v_resetjp_1110_;
}
v_resetjp_1110_:
{
lean_object* v___x_1114_; 
if (v_isShared_1112_ == 0)
{
v___x_1114_ = v___x_1111_;
goto v_reusejp_1113_;
}
else
{
lean_object* v_reuseFailAlloc_1115_; 
v_reuseFailAlloc_1115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1115_, 0, v_a_1109_);
v___x_1114_ = v_reuseFailAlloc_1115_;
goto v_reusejp_1113_;
}
v_reusejp_1113_:
{
return v___x_1114_;
}
}
}
}
}
}
}
v___jp_1079_:
{
lean_object* v___x_1080_; lean_object* v___x_1081_; 
v___x_1080_ = lean_box(0);
v___x_1081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1081_, 0, v___x_1080_);
return v___x_1081_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj___boxed(lean_object* v_e_1162_, lean_object* v_a_1163_, lean_object* v_a_1164_, lean_object* v_a_1165_, lean_object* v_a_1166_, lean_object* v_a_1167_, lean_object* v_a_1168_, lean_object* v_a_1169_, lean_object* v_a_1170_, lean_object* v_a_1171_, lean_object* v_a_1172_, lean_object* v_a_1173_){
_start:
{
lean_object* v_res_1174_; 
v_res_1174_ = l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj(v_e_1162_, v_a_1163_, v_a_1164_, v_a_1165_, v_a_1166_, v_a_1167_, v_a_1168_, v_a_1169_, v_a_1170_, v_a_1171_, v_a_1172_);
return v_res_1174_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj___regBuiltin___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj_declare__1_00___x40_Lean_Meta_Tactic_Grind_PropagateInj_3930705876____hygCtx___hyg_8_(){
_start:
{
lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; 
v___x_1176_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj___closed__2));
v___x_1177_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj___boxed), 12, 0);
v___x_1178_ = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(v___x_1176_, v___x_1177_);
return v___x_1178_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj___regBuiltin___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj_declare__1_00___x40_Lean_Meta_Tactic_Grind_PropagateInj_3930705876____hygCtx___hyg_8____boxed(lean_object* v_a_1179_){
_start:
{
lean_object* v_res_1180_; 
v_res_1180_ = l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj___regBuiltin___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj_declare__1_00___x40_Lean_Meta_Tactic_Grind_PropagateInj_3930705876____hygCtx___hyg_8_();
return v_res_1180_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Propagator(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Injective(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_PropagatorAttr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Simp(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_PropagateInj(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Grind_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Propagator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Injective(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_PropagatorAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Simp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj___regBuiltin___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj_declare__1_00___x40_Lean_Meta_Tactic_Grind_PropagateInj_3930705876____hygCtx___hyg_8_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_PropagateInj(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
lean_object* initialize_Init_Grind_Propagator(uint8_t builtin);
lean_object* initialize_Init_Grind_Injective(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_PropagatorAttr(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Simp(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_PropagateInj(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Propagator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Injective(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_PropagatorAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Simp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_PropagateInj(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_PropagateInj(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_PropagateInj(builtin);
}
#ifdef __cplusplus
}
#endif
