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
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
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
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_preprocessLight___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Meta_Grind_mkInjEq___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Meta_Grind_mkInjEq___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_mkInjEq___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Grind_mkInjEq___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_mkInjEq___closed__4_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Meta_Grind_mkInjEq___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_mkInjEq___closed__5_value;
static lean_once_cell_t l_Lean_Meta_Grind_mkInjEq___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_mkInjEq___closed__6;
static const lean_string_object l_Lean_Meta_Grind_mkInjEq___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l_Lean_Meta_Grind_mkInjEq___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_mkInjEq___closed__7_value;
static lean_once_cell_t l_Lean_Meta_Grind_mkInjEq___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_mkInjEq___closed__8;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkInjEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkInjEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v___x_14_; lean_object* v___x_9023__overap_15_; lean_object* v___x_16_; 
v___x_14_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__0___closed__0, &l_panic___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__0___closed__0);
v___x_9023__overap_15_ = lean_panic_fn_borrowed(v___x_14_, v_msg_2_);
lean_inc(v___y_12_);
lean_inc_ref(v___y_11_);
lean_inc(v___y_10_);
lean_inc_ref(v___y_9_);
lean_inc(v___y_8_);
lean_inc_ref(v___y_7_);
lean_inc(v___y_6_);
lean_inc_ref(v___y_5_);
lean_inc(v___y_4_);
lean_inc(v___y_3_);
v___x_16_ = lean_apply_11(v___x_9023__overap_15_, v___y_3_, v___y_4_, v___y_5_, v___y_6_, v___y_7_, v___y_8_, v___y_9_, v___y_10_, v___y_11_, v___y_12_, lean_box(0));
return v___x_16_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__0___boxed(lean_object* v_msg_17_, lean_object* v___y_18_, lean_object* v___y_19_, lean_object* v___y_20_, lean_object* v___y_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_, lean_object* v___y_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__0(v_msg_17_, v___y_18_, v___y_19_, v___y_20_, v___y_21_, v___y_22_, v___y_23_, v___y_24_, v___y_25_, v___y_26_, v___y_27_);
lean_dec(v___y_27_);
lean_dec_ref(v___y_26_);
lean_dec(v___y_25_);
lean_dec_ref(v___y_24_);
lean_dec(v___y_23_);
lean_dec_ref(v___y_22_);
lean_dec(v___y_21_);
lean_dec_ref(v___y_20_);
lean_dec(v___y_19_);
lean_dec(v___y_18_);
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
lean_object* v_es_58_; lean_object* v___x_59_; size_t v___x_60_; size_t v___x_61_; size_t v___x_62_; lean_object* v_j_63_; lean_object* v___x_64_; 
v_es_58_ = lean_ctor_get(v_x_55_, 0);
v___x_59_ = lean_box(2);
v___x_60_ = ((size_t)5ULL);
v___x_61_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1___redArg___closed__1);
v___x_62_ = lean_usize_land(v_x_56_, v___x_61_);
v_j_63_ = lean_usize_to_nat(v___x_62_);
v___x_64_ = lean_array_get_borrowed(v___x_59_, v_es_58_, v_j_63_);
lean_dec(v_j_63_);
switch(lean_obj_tag(v___x_64_))
{
case 0:
{
lean_object* v_key_65_; lean_object* v_val_66_; uint8_t v___x_67_; 
v_key_65_ = lean_ctor_get(v___x_64_, 0);
v_val_66_ = lean_ctor_get(v___x_64_, 1);
v___x_67_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_57_, v_key_65_);
if (v___x_67_ == 0)
{
lean_object* v___x_68_; 
v___x_68_ = lean_box(0);
return v___x_68_;
}
else
{
lean_object* v___x_69_; 
lean_inc(v_val_66_);
v___x_69_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_69_, 0, v_val_66_);
return v___x_69_;
}
}
case 1:
{
lean_object* v_node_70_; size_t v___x_71_; 
v_node_70_ = lean_ctor_get(v___x_64_, 0);
v___x_71_ = lean_usize_shift_right(v_x_56_, v___x_60_);
v_x_55_ = v_node_70_;
v_x_56_ = v___x_71_;
goto _start;
}
default: 
{
lean_object* v___x_73_; 
v___x_73_ = lean_box(0);
return v___x_73_;
}
}
}
else
{
lean_object* v_ks_74_; lean_object* v_vs_75_; lean_object* v___x_76_; lean_object* v___x_77_; 
v_ks_74_ = lean_ctor_get(v_x_55_, 0);
v_vs_75_ = lean_ctor_get(v_x_55_, 1);
v___x_76_ = lean_unsigned_to_nat(0u);
v___x_77_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1_spec__2___redArg(v_ks_74_, v_vs_75_, v___x_76_, v_x_57_);
return v___x_77_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1___redArg___boxed(lean_object* v_x_78_, lean_object* v_x_79_, lean_object* v_x_80_){
_start:
{
size_t v_x_9505__boxed_81_; lean_object* v_res_82_; 
v_x_9505__boxed_81_ = lean_unbox_usize(v_x_79_);
lean_dec(v_x_79_);
v_res_82_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1___redArg(v_x_78_, v_x_9505__boxed_81_, v_x_80_);
lean_dec_ref(v_x_80_);
lean_dec_ref(v_x_78_);
return v_res_82_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1___redArg(lean_object* v_x_83_, lean_object* v_x_84_){
_start:
{
uint64_t v___x_85_; size_t v___x_86_; lean_object* v___x_87_; 
v___x_85_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_84_);
v___x_86_ = lean_uint64_to_usize(v___x_85_);
v___x_87_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1___redArg(v_x_83_, v___x_86_, v_x_84_);
return v___x_87_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1___redArg___boxed(lean_object* v_x_88_, lean_object* v_x_89_){
_start:
{
lean_object* v_res_90_; 
v_res_90_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1___redArg(v_x_88_, v_x_89_);
lean_dec_ref(v_x_89_);
lean_dec_ref(v_x_88_);
return v_res_90_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3_spec__5_spec__6___redArg(lean_object* v_x_91_, lean_object* v_x_92_, lean_object* v_x_93_, lean_object* v_x_94_){
_start:
{
lean_object* v_ks_95_; lean_object* v_vs_96_; lean_object* v___x_98_; uint8_t v_isShared_99_; uint8_t v_isSharedCheck_120_; 
v_ks_95_ = lean_ctor_get(v_x_91_, 0);
v_vs_96_ = lean_ctor_get(v_x_91_, 1);
v_isSharedCheck_120_ = !lean_is_exclusive(v_x_91_);
if (v_isSharedCheck_120_ == 0)
{
v___x_98_ = v_x_91_;
v_isShared_99_ = v_isSharedCheck_120_;
goto v_resetjp_97_;
}
else
{
lean_inc(v_vs_96_);
lean_inc(v_ks_95_);
lean_dec(v_x_91_);
v___x_98_ = lean_box(0);
v_isShared_99_ = v_isSharedCheck_120_;
goto v_resetjp_97_;
}
v_resetjp_97_:
{
lean_object* v___x_100_; uint8_t v___x_101_; 
v___x_100_ = lean_array_get_size(v_ks_95_);
v___x_101_ = lean_nat_dec_lt(v_x_92_, v___x_100_);
if (v___x_101_ == 0)
{
lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_105_; 
lean_dec(v_x_92_);
v___x_102_ = lean_array_push(v_ks_95_, v_x_93_);
v___x_103_ = lean_array_push(v_vs_96_, v_x_94_);
if (v_isShared_99_ == 0)
{
lean_ctor_set(v___x_98_, 1, v___x_103_);
lean_ctor_set(v___x_98_, 0, v___x_102_);
v___x_105_ = v___x_98_;
goto v_reusejp_104_;
}
else
{
lean_object* v_reuseFailAlloc_106_; 
v_reuseFailAlloc_106_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_106_, 0, v___x_102_);
lean_ctor_set(v_reuseFailAlloc_106_, 1, v___x_103_);
v___x_105_ = v_reuseFailAlloc_106_;
goto v_reusejp_104_;
}
v_reusejp_104_:
{
return v___x_105_;
}
}
else
{
lean_object* v_k_x27_107_; uint8_t v___x_108_; 
v_k_x27_107_ = lean_array_fget_borrowed(v_ks_95_, v_x_92_);
v___x_108_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_93_, v_k_x27_107_);
if (v___x_108_ == 0)
{
lean_object* v___x_110_; 
if (v_isShared_99_ == 0)
{
v___x_110_ = v___x_98_;
goto v_reusejp_109_;
}
else
{
lean_object* v_reuseFailAlloc_114_; 
v_reuseFailAlloc_114_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_114_, 0, v_ks_95_);
lean_ctor_set(v_reuseFailAlloc_114_, 1, v_vs_96_);
v___x_110_ = v_reuseFailAlloc_114_;
goto v_reusejp_109_;
}
v_reusejp_109_:
{
lean_object* v___x_111_; lean_object* v___x_112_; 
v___x_111_ = lean_unsigned_to_nat(1u);
v___x_112_ = lean_nat_add(v_x_92_, v___x_111_);
lean_dec(v_x_92_);
v_x_91_ = v___x_110_;
v_x_92_ = v___x_112_;
goto _start;
}
}
else
{
lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_118_; 
v___x_115_ = lean_array_fset(v_ks_95_, v_x_92_, v_x_93_);
v___x_116_ = lean_array_fset(v_vs_96_, v_x_92_, v_x_94_);
lean_dec(v_x_92_);
if (v_isShared_99_ == 0)
{
lean_ctor_set(v___x_98_, 1, v___x_116_);
lean_ctor_set(v___x_98_, 0, v___x_115_);
v___x_118_ = v___x_98_;
goto v_reusejp_117_;
}
else
{
lean_object* v_reuseFailAlloc_119_; 
v_reuseFailAlloc_119_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_119_, 0, v___x_115_);
lean_ctor_set(v_reuseFailAlloc_119_, 1, v___x_116_);
v___x_118_ = v_reuseFailAlloc_119_;
goto v_reusejp_117_;
}
v_reusejp_117_:
{
return v___x_118_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3_spec__5___redArg(lean_object* v_n_121_, lean_object* v_k_122_, lean_object* v_v_123_){
_start:
{
lean_object* v___x_124_; lean_object* v___x_125_; 
v___x_124_ = lean_unsigned_to_nat(0u);
v___x_125_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3_spec__5_spec__6___redArg(v_n_121_, v___x_124_, v_k_122_, v_v_123_);
return v___x_125_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_126_; 
v___x_126_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_126_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3___redArg(lean_object* v_x_127_, size_t v_x_128_, size_t v_x_129_, lean_object* v_x_130_, lean_object* v_x_131_){
_start:
{
if (lean_obj_tag(v_x_127_) == 0)
{
lean_object* v_es_132_; size_t v___x_133_; size_t v___x_134_; size_t v___x_135_; size_t v___x_136_; lean_object* v_j_137_; lean_object* v___x_138_; uint8_t v___x_139_; 
v_es_132_ = lean_ctor_get(v_x_127_, 0);
v___x_133_ = ((size_t)5ULL);
v___x_134_ = ((size_t)1ULL);
v___x_135_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1___redArg___closed__1);
v___x_136_ = lean_usize_land(v_x_128_, v___x_135_);
v_j_137_ = lean_usize_to_nat(v___x_136_);
v___x_138_ = lean_array_get_size(v_es_132_);
v___x_139_ = lean_nat_dec_lt(v_j_137_, v___x_138_);
if (v___x_139_ == 0)
{
lean_dec(v_j_137_);
lean_dec(v_x_131_);
lean_dec_ref(v_x_130_);
return v_x_127_;
}
else
{
lean_object* v___x_141_; uint8_t v_isShared_142_; uint8_t v_isSharedCheck_176_; 
lean_inc_ref(v_es_132_);
v_isSharedCheck_176_ = !lean_is_exclusive(v_x_127_);
if (v_isSharedCheck_176_ == 0)
{
lean_object* v_unused_177_; 
v_unused_177_ = lean_ctor_get(v_x_127_, 0);
lean_dec(v_unused_177_);
v___x_141_ = v_x_127_;
v_isShared_142_ = v_isSharedCheck_176_;
goto v_resetjp_140_;
}
else
{
lean_dec(v_x_127_);
v___x_141_ = lean_box(0);
v_isShared_142_ = v_isSharedCheck_176_;
goto v_resetjp_140_;
}
v_resetjp_140_:
{
lean_object* v_v_143_; lean_object* v___x_144_; lean_object* v_xs_x27_145_; lean_object* v___y_147_; 
v_v_143_ = lean_array_fget(v_es_132_, v_j_137_);
v___x_144_ = lean_box(0);
v_xs_x27_145_ = lean_array_fset(v_es_132_, v_j_137_, v___x_144_);
switch(lean_obj_tag(v_v_143_))
{
case 0:
{
lean_object* v_key_152_; lean_object* v_val_153_; lean_object* v___x_155_; uint8_t v_isShared_156_; uint8_t v_isSharedCheck_163_; 
v_key_152_ = lean_ctor_get(v_v_143_, 0);
v_val_153_ = lean_ctor_get(v_v_143_, 1);
v_isSharedCheck_163_ = !lean_is_exclusive(v_v_143_);
if (v_isSharedCheck_163_ == 0)
{
v___x_155_ = v_v_143_;
v_isShared_156_ = v_isSharedCheck_163_;
goto v_resetjp_154_;
}
else
{
lean_inc(v_val_153_);
lean_inc(v_key_152_);
lean_dec(v_v_143_);
v___x_155_ = lean_box(0);
v_isShared_156_ = v_isSharedCheck_163_;
goto v_resetjp_154_;
}
v_resetjp_154_:
{
uint8_t v___x_157_; 
v___x_157_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_130_, v_key_152_);
if (v___x_157_ == 0)
{
lean_object* v___x_158_; lean_object* v___x_159_; 
lean_del_object(v___x_155_);
v___x_158_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_152_, v_val_153_, v_x_130_, v_x_131_);
v___x_159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_159_, 0, v___x_158_);
v___y_147_ = v___x_159_;
goto v___jp_146_;
}
else
{
lean_object* v___x_161_; 
lean_dec(v_val_153_);
lean_dec(v_key_152_);
if (v_isShared_156_ == 0)
{
lean_ctor_set(v___x_155_, 1, v_x_131_);
lean_ctor_set(v___x_155_, 0, v_x_130_);
v___x_161_ = v___x_155_;
goto v_reusejp_160_;
}
else
{
lean_object* v_reuseFailAlloc_162_; 
v_reuseFailAlloc_162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_162_, 0, v_x_130_);
lean_ctor_set(v_reuseFailAlloc_162_, 1, v_x_131_);
v___x_161_ = v_reuseFailAlloc_162_;
goto v_reusejp_160_;
}
v_reusejp_160_:
{
v___y_147_ = v___x_161_;
goto v___jp_146_;
}
}
}
}
case 1:
{
lean_object* v_node_164_; lean_object* v___x_166_; uint8_t v_isShared_167_; uint8_t v_isSharedCheck_174_; 
v_node_164_ = lean_ctor_get(v_v_143_, 0);
v_isSharedCheck_174_ = !lean_is_exclusive(v_v_143_);
if (v_isSharedCheck_174_ == 0)
{
v___x_166_ = v_v_143_;
v_isShared_167_ = v_isSharedCheck_174_;
goto v_resetjp_165_;
}
else
{
lean_inc(v_node_164_);
lean_dec(v_v_143_);
v___x_166_ = lean_box(0);
v_isShared_167_ = v_isSharedCheck_174_;
goto v_resetjp_165_;
}
v_resetjp_165_:
{
size_t v___x_168_; size_t v___x_169_; lean_object* v___x_170_; lean_object* v___x_172_; 
v___x_168_ = lean_usize_shift_right(v_x_128_, v___x_133_);
v___x_169_ = lean_usize_add(v_x_129_, v___x_134_);
v___x_170_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3___redArg(v_node_164_, v___x_168_, v___x_169_, v_x_130_, v_x_131_);
if (v_isShared_167_ == 0)
{
lean_ctor_set(v___x_166_, 0, v___x_170_);
v___x_172_ = v___x_166_;
goto v_reusejp_171_;
}
else
{
lean_object* v_reuseFailAlloc_173_; 
v_reuseFailAlloc_173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_173_, 0, v___x_170_);
v___x_172_ = v_reuseFailAlloc_173_;
goto v_reusejp_171_;
}
v_reusejp_171_:
{
v___y_147_ = v___x_172_;
goto v___jp_146_;
}
}
}
default: 
{
lean_object* v___x_175_; 
v___x_175_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_175_, 0, v_x_130_);
lean_ctor_set(v___x_175_, 1, v_x_131_);
v___y_147_ = v___x_175_;
goto v___jp_146_;
}
}
v___jp_146_:
{
lean_object* v___x_148_; lean_object* v___x_150_; 
v___x_148_ = lean_array_fset(v_xs_x27_145_, v_j_137_, v___y_147_);
lean_dec(v_j_137_);
if (v_isShared_142_ == 0)
{
lean_ctor_set(v___x_141_, 0, v___x_148_);
v___x_150_ = v___x_141_;
goto v_reusejp_149_;
}
else
{
lean_object* v_reuseFailAlloc_151_; 
v_reuseFailAlloc_151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_151_, 0, v___x_148_);
v___x_150_ = v_reuseFailAlloc_151_;
goto v_reusejp_149_;
}
v_reusejp_149_:
{
return v___x_150_;
}
}
}
}
}
else
{
lean_object* v_ks_178_; lean_object* v_vs_179_; lean_object* v___x_181_; uint8_t v_isShared_182_; uint8_t v_isSharedCheck_199_; 
v_ks_178_ = lean_ctor_get(v_x_127_, 0);
v_vs_179_ = lean_ctor_get(v_x_127_, 1);
v_isSharedCheck_199_ = !lean_is_exclusive(v_x_127_);
if (v_isSharedCheck_199_ == 0)
{
v___x_181_ = v_x_127_;
v_isShared_182_ = v_isSharedCheck_199_;
goto v_resetjp_180_;
}
else
{
lean_inc(v_vs_179_);
lean_inc(v_ks_178_);
lean_dec(v_x_127_);
v___x_181_ = lean_box(0);
v_isShared_182_ = v_isSharedCheck_199_;
goto v_resetjp_180_;
}
v_resetjp_180_:
{
lean_object* v___x_184_; 
if (v_isShared_182_ == 0)
{
v___x_184_ = v___x_181_;
goto v_reusejp_183_;
}
else
{
lean_object* v_reuseFailAlloc_198_; 
v_reuseFailAlloc_198_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_198_, 0, v_ks_178_);
lean_ctor_set(v_reuseFailAlloc_198_, 1, v_vs_179_);
v___x_184_ = v_reuseFailAlloc_198_;
goto v_reusejp_183_;
}
v_reusejp_183_:
{
lean_object* v_newNode_185_; uint8_t v___y_187_; size_t v___x_193_; uint8_t v___x_194_; 
v_newNode_185_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3_spec__5___redArg(v___x_184_, v_x_130_, v_x_131_);
v___x_193_ = ((size_t)7ULL);
v___x_194_ = lean_usize_dec_le(v___x_193_, v_x_129_);
if (v___x_194_ == 0)
{
lean_object* v___x_195_; lean_object* v___x_196_; uint8_t v___x_197_; 
v___x_195_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_185_);
v___x_196_ = lean_unsigned_to_nat(4u);
v___x_197_ = lean_nat_dec_lt(v___x_195_, v___x_196_);
lean_dec(v___x_195_);
v___y_187_ = v___x_197_;
goto v___jp_186_;
}
else
{
v___y_187_ = v___x_194_;
goto v___jp_186_;
}
v___jp_186_:
{
if (v___y_187_ == 0)
{
lean_object* v_ks_188_; lean_object* v_vs_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; 
v_ks_188_ = lean_ctor_get(v_newNode_185_, 0);
lean_inc_ref(v_ks_188_);
v_vs_189_ = lean_ctor_get(v_newNode_185_, 1);
lean_inc_ref(v_vs_189_);
lean_dec_ref(v_newNode_185_);
v___x_190_ = lean_unsigned_to_nat(0u);
v___x_191_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3___redArg___closed__0);
v___x_192_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3_spec__6___redArg(v_x_129_, v_ks_188_, v_vs_189_, v___x_190_, v___x_191_);
lean_dec_ref(v_vs_189_);
lean_dec_ref(v_ks_188_);
return v___x_192_;
}
else
{
return v_newNode_185_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3_spec__6___redArg(size_t v_depth_200_, lean_object* v_keys_201_, lean_object* v_vals_202_, lean_object* v_i_203_, lean_object* v_entries_204_){
_start:
{
lean_object* v___x_205_; uint8_t v___x_206_; 
v___x_205_ = lean_array_get_size(v_keys_201_);
v___x_206_ = lean_nat_dec_lt(v_i_203_, v___x_205_);
if (v___x_206_ == 0)
{
lean_dec(v_i_203_);
return v_entries_204_;
}
else
{
lean_object* v_k_207_; lean_object* v_v_208_; uint64_t v___x_209_; size_t v_h_210_; size_t v___x_211_; lean_object* v___x_212_; size_t v___x_213_; size_t v___x_214_; size_t v___x_215_; size_t v_h_216_; lean_object* v___x_217_; lean_object* v___x_218_; 
v_k_207_ = lean_array_fget_borrowed(v_keys_201_, v_i_203_);
v_v_208_ = lean_array_fget_borrowed(v_vals_202_, v_i_203_);
v___x_209_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_k_207_);
v_h_210_ = lean_uint64_to_usize(v___x_209_);
v___x_211_ = ((size_t)5ULL);
v___x_212_ = lean_unsigned_to_nat(1u);
v___x_213_ = ((size_t)1ULL);
v___x_214_ = lean_usize_sub(v_depth_200_, v___x_213_);
v___x_215_ = lean_usize_mul(v___x_211_, v___x_214_);
v_h_216_ = lean_usize_shift_right(v_h_210_, v___x_215_);
v___x_217_ = lean_nat_add(v_i_203_, v___x_212_);
lean_dec(v_i_203_);
lean_inc(v_v_208_);
lean_inc(v_k_207_);
v___x_218_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3___redArg(v_entries_204_, v_h_216_, v_depth_200_, v_k_207_, v_v_208_);
v_i_203_ = v___x_217_;
v_entries_204_ = v___x_218_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3_spec__6___redArg___boxed(lean_object* v_depth_220_, lean_object* v_keys_221_, lean_object* v_vals_222_, lean_object* v_i_223_, lean_object* v_entries_224_){
_start:
{
size_t v_depth_boxed_225_; lean_object* v_res_226_; 
v_depth_boxed_225_ = lean_unbox_usize(v_depth_220_);
lean_dec(v_depth_220_);
v_res_226_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3_spec__6___redArg(v_depth_boxed_225_, v_keys_221_, v_vals_222_, v_i_223_, v_entries_224_);
lean_dec_ref(v_vals_222_);
lean_dec_ref(v_keys_221_);
return v_res_226_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3___redArg___boxed(lean_object* v_x_227_, lean_object* v_x_228_, lean_object* v_x_229_, lean_object* v_x_230_, lean_object* v_x_231_){
_start:
{
size_t v_x_9652__boxed_232_; size_t v_x_9653__boxed_233_; lean_object* v_res_234_; 
v_x_9652__boxed_232_ = lean_unbox_usize(v_x_228_);
lean_dec(v_x_228_);
v_x_9653__boxed_233_ = lean_unbox_usize(v_x_229_);
lean_dec(v_x_229_);
v_res_234_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3___redArg(v_x_227_, v_x_9652__boxed_232_, v_x_9653__boxed_233_, v_x_230_, v_x_231_);
return v_res_234_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2___redArg(lean_object* v_x_235_, lean_object* v_x_236_, lean_object* v_x_237_){
_start:
{
uint64_t v___x_238_; size_t v___x_239_; size_t v___x_240_; lean_object* v___x_241_; 
v___x_238_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_236_);
v___x_239_ = lean_uint64_to_usize(v___x_238_);
v___x_240_ = ((size_t)1ULL);
v___x_241_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3___redArg(v_x_235_, v___x_239_, v___x_240_, v_x_236_, v_x_237_);
return v___x_241_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__3(void){
_start:
{
lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; 
v___x_245_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__2));
v___x_246_ = lean_unsigned_to_nat(26u);
v___x_247_ = lean_unsigned_to_nat(19u);
v___x_248_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__1));
v___x_249_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__0));
v___x_250_ = l_mkPanicMessageWithDecl(v___x_249_, v___x_248_, v___x_247_, v___x_246_, v___x_245_);
return v___x_250_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__11(void){
_start:
{
lean_object* v___x_263_; lean_object* v_dummy_264_; 
v___x_263_ = lean_box(0);
v_dummy_264_ = l_Lean_Expr_sort___override(v___x_263_);
return v_dummy_264_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f(lean_object* v_f_270_, lean_object* v_a_271_, lean_object* v_a_272_, lean_object* v_a_273_, lean_object* v_a_274_, lean_object* v_a_275_, lean_object* v_a_276_, lean_object* v_a_277_, lean_object* v_a_278_, lean_object* v_a_279_, lean_object* v_a_280_, lean_object* v_a_281_){
_start:
{
lean_object* v___y_284_; lean_object* v___y_285_; lean_object* v___y_286_; lean_object* v___y_287_; lean_object* v___y_288_; lean_object* v___y_289_; lean_object* v___y_290_; lean_object* v___y_291_; lean_object* v___y_292_; lean_object* v___y_293_; lean_object* v___x_296_; lean_object* v_toGoalState_297_; lean_object* v_inj_298_; lean_object* v_fns_299_; lean_object* v___x_301_; uint8_t v_isShared_302_; uint8_t v_isSharedCheck_423_; 
v___x_296_ = lean_st_ref_get(v_a_272_);
v_toGoalState_297_ = lean_ctor_get(v___x_296_, 0);
lean_inc_ref(v_toGoalState_297_);
lean_dec(v___x_296_);
v_inj_298_ = lean_ctor_get(v_toGoalState_297_, 13);
lean_inc_ref(v_inj_298_);
lean_dec_ref(v_toGoalState_297_);
v_fns_299_ = lean_ctor_get(v_inj_298_, 1);
v_isSharedCheck_423_ = !lean_is_exclusive(v_inj_298_);
if (v_isSharedCheck_423_ == 0)
{
lean_object* v_unused_424_; 
v_unused_424_ = lean_ctor_get(v_inj_298_, 0);
lean_dec(v_unused_424_);
v___x_301_ = v_inj_298_;
v_isShared_302_ = v_isSharedCheck_423_;
goto v_resetjp_300_;
}
else
{
lean_inc(v_fns_299_);
lean_dec(v_inj_298_);
v___x_301_ = lean_box(0);
v_isShared_302_ = v_isSharedCheck_423_;
goto v_resetjp_300_;
}
v___jp_283_:
{
lean_object* v___x_294_; lean_object* v___x_295_; 
v___x_294_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__3, &l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__3);
v___x_295_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__0(v___x_294_, v___y_284_, v___y_285_, v___y_286_, v___y_287_, v___y_288_, v___y_289_, v___y_290_, v___y_291_, v___y_292_, v___y_293_);
return v___x_295_;
}
v_resetjp_300_:
{
lean_object* v___x_303_; 
v___x_303_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1___redArg(v_fns_299_, v_f_270_);
lean_dec_ref(v_fns_299_);
if (lean_obj_tag(v___x_303_) == 1)
{
lean_object* v_val_304_; lean_object* v___x_306_; uint8_t v_isShared_307_; uint8_t v_isSharedCheck_420_; 
v_val_304_ = lean_ctor_get(v___x_303_, 0);
v_isSharedCheck_420_ = !lean_is_exclusive(v___x_303_);
if (v_isSharedCheck_420_ == 0)
{
v___x_306_ = v___x_303_;
v_isShared_307_ = v_isSharedCheck_420_;
goto v_resetjp_305_;
}
else
{
lean_inc(v_val_304_);
lean_dec(v___x_303_);
v___x_306_ = lean_box(0);
v_isShared_307_ = v_isSharedCheck_420_;
goto v_resetjp_305_;
}
v_resetjp_305_:
{
lean_object* v_inv_x3f_308_; 
v_inv_x3f_308_ = lean_ctor_get(v_val_304_, 4);
if (lean_obj_tag(v_inv_x3f_308_) == 1)
{
lean_object* v___x_309_; 
lean_inc_ref(v_inv_x3f_308_);
lean_del_object(v___x_306_);
lean_dec(v_val_304_);
lean_del_object(v___x_301_);
lean_dec_ref(v_a_271_);
lean_dec_ref(v_f_270_);
v___x_309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_309_, 0, v_inv_x3f_308_);
return v___x_309_;
}
else
{
lean_object* v_us_310_; 
v_us_310_ = lean_ctor_get(v_val_304_, 0);
lean_inc(v_us_310_);
if (lean_obj_tag(v_us_310_) == 1)
{
lean_object* v_tail_311_; 
v_tail_311_ = lean_ctor_get(v_us_310_, 1);
lean_inc(v_tail_311_);
if (lean_obj_tag(v_tail_311_) == 1)
{
lean_object* v_tail_312_; lean_object* v___x_314_; uint8_t v_isShared_315_; uint8_t v_isSharedCheck_418_; 
v_tail_312_ = lean_ctor_get(v_tail_311_, 1);
v_isSharedCheck_418_ = !lean_is_exclusive(v_tail_311_);
if (v_isSharedCheck_418_ == 0)
{
lean_object* v_unused_419_; 
v_unused_419_ = lean_ctor_get(v_tail_311_, 0);
lean_dec(v_unused_419_);
v___x_314_ = v_tail_311_;
v_isShared_315_ = v_isSharedCheck_418_;
goto v_resetjp_313_;
}
else
{
lean_inc(v_tail_312_);
lean_dec(v_tail_311_);
v___x_314_ = lean_box(0);
v_isShared_315_ = v_isSharedCheck_418_;
goto v_resetjp_313_;
}
v_resetjp_313_:
{
if (lean_obj_tag(v_tail_312_) == 0)
{
lean_object* v_00_u03b1_316_; lean_object* v_00_u03b2_317_; lean_object* v_h_318_; lean_object* v___x_320_; uint8_t v_isShared_321_; uint8_t v_isSharedCheck_415_; 
v_00_u03b1_316_ = lean_ctor_get(v_val_304_, 1);
v_00_u03b2_317_ = lean_ctor_get(v_val_304_, 2);
v_h_318_ = lean_ctor_get(v_val_304_, 3);
v_isSharedCheck_415_ = !lean_is_exclusive(v_val_304_);
if (v_isSharedCheck_415_ == 0)
{
lean_object* v_unused_416_; lean_object* v_unused_417_; 
v_unused_416_ = lean_ctor_get(v_val_304_, 4);
lean_dec(v_unused_416_);
v_unused_417_ = lean_ctor_get(v_val_304_, 0);
lean_dec(v_unused_417_);
v___x_320_ = v_val_304_;
v_isShared_321_ = v_isSharedCheck_415_;
goto v_resetjp_319_;
}
else
{
lean_inc(v_h_318_);
lean_inc(v_00_u03b2_317_);
lean_inc(v_00_u03b1_316_);
lean_dec(v_val_304_);
v___x_320_ = lean_box(0);
v_isShared_321_ = v_isSharedCheck_415_;
goto v_resetjp_319_;
}
v_resetjp_319_:
{
lean_object* v_head_322_; lean_object* v___x_323_; lean_object* v___x_325_; 
v_head_322_ = lean_ctor_get(v_us_310_, 0);
v___x_323_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__6));
lean_inc(v_head_322_);
if (v_isShared_315_ == 0)
{
lean_ctor_set(v___x_314_, 0, v_head_322_);
v___x_325_ = v___x_314_;
goto v_reusejp_324_;
}
else
{
lean_object* v_reuseFailAlloc_414_; 
v_reuseFailAlloc_414_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_414_, 0, v_head_322_);
lean_ctor_set(v_reuseFailAlloc_414_, 1, v_tail_312_);
v___x_325_ = v_reuseFailAlloc_414_;
goto v_reusejp_324_;
}
v_reusejp_324_:
{
lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; 
v___x_326_ = l_Lean_mkConst(v___x_323_, v___x_325_);
lean_inc_ref_n(v_00_u03b1_316_, 2);
v___x_327_ = l_Lean_mkAppB(v___x_326_, v_00_u03b1_316_, v_a_271_);
v___x_328_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__10));
lean_inc_ref(v_us_310_);
v___x_329_ = l_Lean_mkConst(v___x_328_, v_us_310_);
lean_inc_ref(v_h_318_);
lean_inc_ref(v_f_270_);
lean_inc_ref(v_00_u03b2_317_);
v___x_330_ = l_Lean_mkApp5(v___x_329_, v_00_u03b1_316_, v_00_u03b2_317_, v_f_270_, v_h_318_, v___x_327_);
v___x_331_ = l_Lean_Meta_Grind_preprocessLight___redArg(v___x_330_, v_a_273_, v_a_274_, v_a_275_, v_a_276_, v_a_277_, v_a_278_, v_a_279_, v_a_280_, v_a_281_);
if (lean_obj_tag(v___x_331_) == 0)
{
lean_object* v_a_332_; lean_object* v___x_334_; uint8_t v_isShared_335_; uint8_t v_isSharedCheck_405_; 
v_a_332_ = lean_ctor_get(v___x_331_, 0);
v_isSharedCheck_405_ = !lean_is_exclusive(v___x_331_);
if (v_isSharedCheck_405_ == 0)
{
v___x_334_ = v___x_331_;
v_isShared_335_ = v_isSharedCheck_405_;
goto v_resetjp_333_;
}
else
{
lean_inc(v_a_332_);
lean_dec(v___x_331_);
v___x_334_ = lean_box(0);
v_isShared_335_ = v_isSharedCheck_405_;
goto v_resetjp_333_;
}
v_resetjp_333_:
{
lean_object* v___x_336_; lean_object* v_nargs_337_; lean_object* v_toGoalState_338_; lean_object* v_inj_339_; lean_object* v_mvarId_340_; lean_object* v___x_342_; uint8_t v_isShared_343_; uint8_t v_isSharedCheck_403_; 
v___x_336_ = lean_st_ref_take(v_a_272_);
v_nargs_337_ = l_Lean_Expr_getAppNumArgs(v_a_332_);
v_toGoalState_338_ = lean_ctor_get(v___x_336_, 0);
lean_inc_ref(v_toGoalState_338_);
v_inj_339_ = lean_ctor_get(v_toGoalState_338_, 13);
lean_inc_ref(v_inj_339_);
v_mvarId_340_ = lean_ctor_get(v___x_336_, 1);
v_isSharedCheck_403_ = !lean_is_exclusive(v___x_336_);
if (v_isSharedCheck_403_ == 0)
{
lean_object* v_unused_404_; 
v_unused_404_ = lean_ctor_get(v___x_336_, 0);
lean_dec(v_unused_404_);
v___x_342_ = v___x_336_;
v_isShared_343_ = v_isSharedCheck_403_;
goto v_resetjp_341_;
}
else
{
lean_inc(v_mvarId_340_);
lean_dec(v___x_336_);
v___x_342_ = lean_box(0);
v_isShared_343_ = v_isSharedCheck_403_;
goto v_resetjp_341_;
}
v_resetjp_341_:
{
lean_object* v_nextDeclIdx_344_; lean_object* v_enodeMap_345_; lean_object* v_exprs_346_; lean_object* v_parents_347_; lean_object* v_congrTable_348_; lean_object* v_appMap_349_; lean_object* v_indicesFound_350_; lean_object* v_newFacts_351_; uint8_t v_inconsistent_352_; lean_object* v_nextIdx_353_; lean_object* v_newRawFacts_354_; lean_object* v_facts_355_; lean_object* v_extThms_356_; lean_object* v_ematch_357_; lean_object* v_split_358_; lean_object* v_clean_359_; lean_object* v_sstates_360_; lean_object* v___x_362_; uint8_t v_isShared_363_; uint8_t v_isSharedCheck_401_; 
v_nextDeclIdx_344_ = lean_ctor_get(v_toGoalState_338_, 0);
v_enodeMap_345_ = lean_ctor_get(v_toGoalState_338_, 1);
v_exprs_346_ = lean_ctor_get(v_toGoalState_338_, 2);
v_parents_347_ = lean_ctor_get(v_toGoalState_338_, 3);
v_congrTable_348_ = lean_ctor_get(v_toGoalState_338_, 4);
v_appMap_349_ = lean_ctor_get(v_toGoalState_338_, 5);
v_indicesFound_350_ = lean_ctor_get(v_toGoalState_338_, 6);
v_newFacts_351_ = lean_ctor_get(v_toGoalState_338_, 7);
v_inconsistent_352_ = lean_ctor_get_uint8(v_toGoalState_338_, sizeof(void*)*17);
v_nextIdx_353_ = lean_ctor_get(v_toGoalState_338_, 8);
v_newRawFacts_354_ = lean_ctor_get(v_toGoalState_338_, 9);
v_facts_355_ = lean_ctor_get(v_toGoalState_338_, 10);
v_extThms_356_ = lean_ctor_get(v_toGoalState_338_, 11);
v_ematch_357_ = lean_ctor_get(v_toGoalState_338_, 12);
v_split_358_ = lean_ctor_get(v_toGoalState_338_, 14);
v_clean_359_ = lean_ctor_get(v_toGoalState_338_, 15);
v_sstates_360_ = lean_ctor_get(v_toGoalState_338_, 16);
v_isSharedCheck_401_ = !lean_is_exclusive(v_toGoalState_338_);
if (v_isSharedCheck_401_ == 0)
{
lean_object* v_unused_402_; 
v_unused_402_ = lean_ctor_get(v_toGoalState_338_, 13);
lean_dec(v_unused_402_);
v___x_362_ = v_toGoalState_338_;
v_isShared_363_ = v_isSharedCheck_401_;
goto v_resetjp_361_;
}
else
{
lean_inc(v_sstates_360_);
lean_inc(v_clean_359_);
lean_inc(v_split_358_);
lean_inc(v_ematch_357_);
lean_inc(v_extThms_356_);
lean_inc(v_facts_355_);
lean_inc(v_newRawFacts_354_);
lean_inc(v_nextIdx_353_);
lean_inc(v_newFacts_351_);
lean_inc(v_indicesFound_350_);
lean_inc(v_appMap_349_);
lean_inc(v_congrTable_348_);
lean_inc(v_parents_347_);
lean_inc(v_exprs_346_);
lean_inc(v_enodeMap_345_);
lean_inc(v_nextDeclIdx_344_);
lean_dec(v_toGoalState_338_);
v___x_362_ = lean_box(0);
v_isShared_363_ = v_isSharedCheck_401_;
goto v_resetjp_361_;
}
v_resetjp_361_:
{
lean_object* v_thms_364_; lean_object* v_fns_365_; lean_object* v___x_367_; uint8_t v_isShared_368_; uint8_t v_isSharedCheck_400_; 
v_thms_364_ = lean_ctor_get(v_inj_339_, 0);
v_fns_365_ = lean_ctor_get(v_inj_339_, 1);
v_isSharedCheck_400_ = !lean_is_exclusive(v_inj_339_);
if (v_isSharedCheck_400_ == 0)
{
v___x_367_ = v_inj_339_;
v_isShared_368_ = v_isSharedCheck_400_;
goto v_resetjp_366_;
}
else
{
lean_inc(v_fns_365_);
lean_inc(v_thms_364_);
lean_dec(v_inj_339_);
v___x_367_ = lean_box(0);
v_isShared_368_ = v_isSharedCheck_400_;
goto v_resetjp_366_;
}
v_resetjp_366_:
{
lean_object* v_dummy_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_378_; 
v_dummy_369_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__11, &l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__11_once, _init_l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__11);
lean_inc(v_nargs_337_);
v___x_370_ = lean_mk_array(v_nargs_337_, v_dummy_369_);
v___x_371_ = lean_unsigned_to_nat(1u);
v___x_372_ = lean_nat_sub(v_nargs_337_, v___x_371_);
lean_dec(v_nargs_337_);
lean_inc(v_a_332_);
v___x_373_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_332_, v___x_370_, v___x_372_);
v___x_374_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__13));
lean_inc_ref(v_us_310_);
v___x_375_ = l_Lean_mkConst(v___x_374_, v_us_310_);
v___x_376_ = l_Lean_mkAppN(v___x_375_, v___x_373_);
lean_dec_ref(v___x_373_);
if (v_isShared_302_ == 0)
{
lean_ctor_set(v___x_301_, 1, v___x_376_);
lean_ctor_set(v___x_301_, 0, v_a_332_);
v___x_378_ = v___x_301_;
goto v_reusejp_377_;
}
else
{
lean_object* v_reuseFailAlloc_399_; 
v_reuseFailAlloc_399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_399_, 0, v_a_332_);
lean_ctor_set(v_reuseFailAlloc_399_, 1, v___x_376_);
v___x_378_ = v_reuseFailAlloc_399_;
goto v_reusejp_377_;
}
v_reusejp_377_:
{
lean_object* v___x_380_; 
if (v_isShared_307_ == 0)
{
lean_ctor_set(v___x_306_, 0, v___x_378_);
v___x_380_ = v___x_306_;
goto v_reusejp_379_;
}
else
{
lean_object* v_reuseFailAlloc_398_; 
v_reuseFailAlloc_398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_398_, 0, v___x_378_);
v___x_380_ = v_reuseFailAlloc_398_;
goto v_reusejp_379_;
}
v_reusejp_379_:
{
lean_object* v___x_382_; 
lean_inc_ref(v___x_380_);
if (v_isShared_321_ == 0)
{
lean_ctor_set(v___x_320_, 4, v___x_380_);
v___x_382_ = v___x_320_;
goto v_reusejp_381_;
}
else
{
lean_object* v_reuseFailAlloc_397_; 
v_reuseFailAlloc_397_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_397_, 0, v_us_310_);
lean_ctor_set(v_reuseFailAlloc_397_, 1, v_00_u03b1_316_);
lean_ctor_set(v_reuseFailAlloc_397_, 2, v_00_u03b2_317_);
lean_ctor_set(v_reuseFailAlloc_397_, 3, v_h_318_);
lean_ctor_set(v_reuseFailAlloc_397_, 4, v___x_380_);
v___x_382_ = v_reuseFailAlloc_397_;
goto v_reusejp_381_;
}
v_reusejp_381_:
{
lean_object* v___x_383_; lean_object* v___x_385_; 
v___x_383_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2___redArg(v_fns_365_, v_f_270_, v___x_382_);
if (v_isShared_368_ == 0)
{
lean_ctor_set(v___x_367_, 1, v___x_383_);
v___x_385_ = v___x_367_;
goto v_reusejp_384_;
}
else
{
lean_object* v_reuseFailAlloc_396_; 
v_reuseFailAlloc_396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_396_, 0, v_thms_364_);
lean_ctor_set(v_reuseFailAlloc_396_, 1, v___x_383_);
v___x_385_ = v_reuseFailAlloc_396_;
goto v_reusejp_384_;
}
v_reusejp_384_:
{
lean_object* v___x_387_; 
if (v_isShared_363_ == 0)
{
lean_ctor_set(v___x_362_, 13, v___x_385_);
v___x_387_ = v___x_362_;
goto v_reusejp_386_;
}
else
{
lean_object* v_reuseFailAlloc_395_; 
v_reuseFailAlloc_395_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_395_, 0, v_nextDeclIdx_344_);
lean_ctor_set(v_reuseFailAlloc_395_, 1, v_enodeMap_345_);
lean_ctor_set(v_reuseFailAlloc_395_, 2, v_exprs_346_);
lean_ctor_set(v_reuseFailAlloc_395_, 3, v_parents_347_);
lean_ctor_set(v_reuseFailAlloc_395_, 4, v_congrTable_348_);
lean_ctor_set(v_reuseFailAlloc_395_, 5, v_appMap_349_);
lean_ctor_set(v_reuseFailAlloc_395_, 6, v_indicesFound_350_);
lean_ctor_set(v_reuseFailAlloc_395_, 7, v_newFacts_351_);
lean_ctor_set(v_reuseFailAlloc_395_, 8, v_nextIdx_353_);
lean_ctor_set(v_reuseFailAlloc_395_, 9, v_newRawFacts_354_);
lean_ctor_set(v_reuseFailAlloc_395_, 10, v_facts_355_);
lean_ctor_set(v_reuseFailAlloc_395_, 11, v_extThms_356_);
lean_ctor_set(v_reuseFailAlloc_395_, 12, v_ematch_357_);
lean_ctor_set(v_reuseFailAlloc_395_, 13, v___x_385_);
lean_ctor_set(v_reuseFailAlloc_395_, 14, v_split_358_);
lean_ctor_set(v_reuseFailAlloc_395_, 15, v_clean_359_);
lean_ctor_set(v_reuseFailAlloc_395_, 16, v_sstates_360_);
lean_ctor_set_uint8(v_reuseFailAlloc_395_, sizeof(void*)*17, v_inconsistent_352_);
v___x_387_ = v_reuseFailAlloc_395_;
goto v_reusejp_386_;
}
v_reusejp_386_:
{
lean_object* v___x_389_; 
if (v_isShared_343_ == 0)
{
lean_ctor_set(v___x_342_, 0, v___x_387_);
v___x_389_ = v___x_342_;
goto v_reusejp_388_;
}
else
{
lean_object* v_reuseFailAlloc_394_; 
v_reuseFailAlloc_394_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_394_, 0, v___x_387_);
lean_ctor_set(v_reuseFailAlloc_394_, 1, v_mvarId_340_);
v___x_389_ = v_reuseFailAlloc_394_;
goto v_reusejp_388_;
}
v_reusejp_388_:
{
lean_object* v___x_390_; lean_object* v___x_392_; 
v___x_390_ = lean_st_ref_set(v_a_272_, v___x_389_);
if (v_isShared_335_ == 0)
{
lean_ctor_set(v___x_334_, 0, v___x_380_);
v___x_392_ = v___x_334_;
goto v_reusejp_391_;
}
else
{
lean_object* v_reuseFailAlloc_393_; 
v_reuseFailAlloc_393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_393_, 0, v___x_380_);
v___x_392_ = v_reuseFailAlloc_393_;
goto v_reusejp_391_;
}
v_reusejp_391_:
{
return v___x_392_;
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
lean_object* v_a_406_; lean_object* v___x_408_; uint8_t v_isShared_409_; uint8_t v_isSharedCheck_413_; 
lean_del_object(v___x_320_);
lean_dec_ref(v_h_318_);
lean_dec_ref(v_00_u03b2_317_);
lean_dec_ref(v_00_u03b1_316_);
lean_dec_ref(v_us_310_);
lean_del_object(v___x_306_);
lean_del_object(v___x_301_);
lean_dec_ref(v_f_270_);
v_a_406_ = lean_ctor_get(v___x_331_, 0);
v_isSharedCheck_413_ = !lean_is_exclusive(v___x_331_);
if (v_isSharedCheck_413_ == 0)
{
v___x_408_ = v___x_331_;
v_isShared_409_ = v_isSharedCheck_413_;
goto v_resetjp_407_;
}
else
{
lean_inc(v_a_406_);
lean_dec(v___x_331_);
v___x_408_ = lean_box(0);
v_isShared_409_ = v_isSharedCheck_413_;
goto v_resetjp_407_;
}
v_resetjp_407_:
{
lean_object* v___x_411_; 
if (v_isShared_409_ == 0)
{
v___x_411_ = v___x_408_;
goto v_reusejp_410_;
}
else
{
lean_object* v_reuseFailAlloc_412_; 
v_reuseFailAlloc_412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_412_, 0, v_a_406_);
v___x_411_ = v_reuseFailAlloc_412_;
goto v_reusejp_410_;
}
v_reusejp_410_:
{
return v___x_411_;
}
}
}
}
}
}
else
{
lean_del_object(v___x_314_);
lean_dec(v_tail_312_);
lean_dec_ref(v_us_310_);
lean_del_object(v___x_306_);
lean_dec(v_val_304_);
lean_del_object(v___x_301_);
lean_dec_ref(v_a_271_);
lean_dec_ref(v_f_270_);
v___y_284_ = v_a_272_;
v___y_285_ = v_a_273_;
v___y_286_ = v_a_274_;
v___y_287_ = v_a_275_;
v___y_288_ = v_a_276_;
v___y_289_ = v_a_277_;
v___y_290_ = v_a_278_;
v___y_291_ = v_a_279_;
v___y_292_ = v_a_280_;
v___y_293_ = v_a_281_;
goto v___jp_283_;
}
}
}
else
{
lean_dec(v_tail_311_);
lean_dec_ref(v_us_310_);
lean_del_object(v___x_306_);
lean_dec(v_val_304_);
lean_del_object(v___x_301_);
lean_dec_ref(v_a_271_);
lean_dec_ref(v_f_270_);
v___y_284_ = v_a_272_;
v___y_285_ = v_a_273_;
v___y_286_ = v_a_274_;
v___y_287_ = v_a_275_;
v___y_288_ = v_a_276_;
v___y_289_ = v_a_277_;
v___y_290_ = v_a_278_;
v___y_291_ = v_a_279_;
v___y_292_ = v_a_280_;
v___y_293_ = v_a_281_;
goto v___jp_283_;
}
}
else
{
lean_dec(v_us_310_);
lean_del_object(v___x_306_);
lean_dec(v_val_304_);
lean_del_object(v___x_301_);
lean_dec_ref(v_a_271_);
lean_dec_ref(v_f_270_);
v___y_284_ = v_a_272_;
v___y_285_ = v_a_273_;
v___y_286_ = v_a_274_;
v___y_287_ = v_a_275_;
v___y_288_ = v_a_276_;
v___y_289_ = v_a_277_;
v___y_290_ = v_a_278_;
v___y_291_ = v_a_279_;
v___y_292_ = v_a_280_;
v___y_293_ = v_a_281_;
goto v___jp_283_;
}
}
}
}
else
{
lean_object* v___x_421_; lean_object* v___x_422_; 
lean_dec(v___x_303_);
lean_del_object(v___x_301_);
lean_dec_ref(v_a_271_);
lean_dec_ref(v_f_270_);
v___x_421_ = lean_box(0);
v___x_422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_422_, 0, v___x_421_);
return v___x_422_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___boxed(lean_object* v_f_425_, lean_object* v_a_426_, lean_object* v_a_427_, lean_object* v_a_428_, lean_object* v_a_429_, lean_object* v_a_430_, lean_object* v_a_431_, lean_object* v_a_432_, lean_object* v_a_433_, lean_object* v_a_434_, lean_object* v_a_435_, lean_object* v_a_436_, lean_object* v_a_437_){
_start:
{
lean_object* v_res_438_; 
v_res_438_ = l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f(v_f_425_, v_a_426_, v_a_427_, v_a_428_, v_a_429_, v_a_430_, v_a_431_, v_a_432_, v_a_433_, v_a_434_, v_a_435_, v_a_436_);
lean_dec(v_a_436_);
lean_dec_ref(v_a_435_);
lean_dec(v_a_434_);
lean_dec_ref(v_a_433_);
lean_dec(v_a_432_);
lean_dec_ref(v_a_431_);
lean_dec(v_a_430_);
lean_dec_ref(v_a_429_);
lean_dec(v_a_428_);
lean_dec(v_a_427_);
return v_res_438_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1(lean_object* v_00_u03b2_439_, lean_object* v_x_440_, lean_object* v_x_441_){
_start:
{
lean_object* v___x_442_; 
v___x_442_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1___redArg(v_x_440_, v_x_441_);
return v___x_442_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1___boxed(lean_object* v_00_u03b2_443_, lean_object* v_x_444_, lean_object* v_x_445_){
_start:
{
lean_object* v_res_446_; 
v_res_446_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1(v_00_u03b2_443_, v_x_444_, v_x_445_);
lean_dec_ref(v_x_445_);
lean_dec_ref(v_x_444_);
return v_res_446_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2(lean_object* v_00_u03b2_447_, lean_object* v_x_448_, lean_object* v_x_449_, lean_object* v_x_450_){
_start:
{
lean_object* v___x_451_; 
v___x_451_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2___redArg(v_x_448_, v_x_449_, v_x_450_);
return v___x_451_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1(lean_object* v_00_u03b2_452_, lean_object* v_x_453_, size_t v_x_454_, lean_object* v_x_455_){
_start:
{
lean_object* v___x_456_; 
v___x_456_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1___redArg(v_x_453_, v_x_454_, v_x_455_);
return v___x_456_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1___boxed(lean_object* v_00_u03b2_457_, lean_object* v_x_458_, lean_object* v_x_459_, lean_object* v_x_460_){
_start:
{
size_t v_x_10143__boxed_461_; lean_object* v_res_462_; 
v_x_10143__boxed_461_ = lean_unbox_usize(v_x_459_);
lean_dec(v_x_459_);
v_res_462_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1(v_00_u03b2_457_, v_x_458_, v_x_10143__boxed_461_, v_x_460_);
lean_dec_ref(v_x_460_);
lean_dec_ref(v_x_458_);
return v_res_462_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3(lean_object* v_00_u03b2_463_, lean_object* v_x_464_, size_t v_x_465_, size_t v_x_466_, lean_object* v_x_467_, lean_object* v_x_468_){
_start:
{
lean_object* v___x_469_; 
v___x_469_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3___redArg(v_x_464_, v_x_465_, v_x_466_, v_x_467_, v_x_468_);
return v___x_469_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3___boxed(lean_object* v_00_u03b2_470_, lean_object* v_x_471_, lean_object* v_x_472_, lean_object* v_x_473_, lean_object* v_x_474_, lean_object* v_x_475_){
_start:
{
size_t v_x_10154__boxed_476_; size_t v_x_10155__boxed_477_; lean_object* v_res_478_; 
v_x_10154__boxed_476_ = lean_unbox_usize(v_x_472_);
lean_dec(v_x_472_);
v_x_10155__boxed_477_ = lean_unbox_usize(v_x_473_);
lean_dec(v_x_473_);
v_res_478_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3(v_00_u03b2_470_, v_x_471_, v_x_10154__boxed_476_, v_x_10155__boxed_477_, v_x_474_, v_x_475_);
return v_res_478_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_479_, lean_object* v_keys_480_, lean_object* v_vals_481_, lean_object* v_heq_482_, lean_object* v_i_483_, lean_object* v_k_484_){
_start:
{
lean_object* v___x_485_; 
v___x_485_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1_spec__2___redArg(v_keys_480_, v_vals_481_, v_i_483_, v_k_484_);
return v___x_485_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03b2_486_, lean_object* v_keys_487_, lean_object* v_vals_488_, lean_object* v_heq_489_, lean_object* v_i_490_, lean_object* v_k_491_){
_start:
{
lean_object* v_res_492_; 
v_res_492_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1_spec__2(v_00_u03b2_486_, v_keys_487_, v_vals_488_, v_heq_489_, v_i_490_, v_k_491_);
lean_dec_ref(v_k_491_);
lean_dec_ref(v_vals_488_);
lean_dec_ref(v_keys_487_);
return v_res_492_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3_spec__5(lean_object* v_00_u03b2_493_, lean_object* v_n_494_, lean_object* v_k_495_, lean_object* v_v_496_){
_start:
{
lean_object* v___x_497_; 
v___x_497_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3_spec__5___redArg(v_n_494_, v_k_495_, v_v_496_);
return v___x_497_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3_spec__6(lean_object* v_00_u03b2_498_, size_t v_depth_499_, lean_object* v_keys_500_, lean_object* v_vals_501_, lean_object* v_heq_502_, lean_object* v_i_503_, lean_object* v_entries_504_){
_start:
{
lean_object* v___x_505_; 
v___x_505_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3_spec__6___redArg(v_depth_499_, v_keys_500_, v_vals_501_, v_i_503_, v_entries_504_);
return v___x_505_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3_spec__6___boxed(lean_object* v_00_u03b2_506_, lean_object* v_depth_507_, lean_object* v_keys_508_, lean_object* v_vals_509_, lean_object* v_heq_510_, lean_object* v_i_511_, lean_object* v_entries_512_){
_start:
{
size_t v_depth_boxed_513_; lean_object* v_res_514_; 
v_depth_boxed_513_ = lean_unbox_usize(v_depth_507_);
lean_dec(v_depth_507_);
v_res_514_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3_spec__6(v_00_u03b2_506_, v_depth_boxed_513_, v_keys_508_, v_vals_509_, v_heq_510_, v_i_511_, v_entries_512_);
lean_dec_ref(v_vals_509_);
lean_dec_ref(v_keys_508_);
return v_res_514_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3_spec__5_spec__6(lean_object* v_00_u03b2_515_, lean_object* v_x_516_, lean_object* v_x_517_, lean_object* v_x_518_, lean_object* v_x_519_){
_start:
{
lean_object* v___x_520_; 
v___x_520_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3_spec__5_spec__6___redArg(v_x_516_, v_x_517_, v_x_518_, v_x_519_);
return v___x_520_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0_spec__0(lean_object* v_msgData_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_){
_start:
{
lean_object* v___x_527_; lean_object* v_env_528_; lean_object* v___x_529_; lean_object* v_mctx_530_; lean_object* v_lctx_531_; lean_object* v_options_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; 
v___x_527_ = lean_st_ref_get(v___y_525_);
v_env_528_ = lean_ctor_get(v___x_527_, 0);
lean_inc_ref(v_env_528_);
lean_dec(v___x_527_);
v___x_529_ = lean_st_ref_get(v___y_523_);
v_mctx_530_ = lean_ctor_get(v___x_529_, 0);
lean_inc_ref(v_mctx_530_);
lean_dec(v___x_529_);
v_lctx_531_ = lean_ctor_get(v___y_522_, 2);
v_options_532_ = lean_ctor_get(v___y_524_, 2);
lean_inc_ref(v_options_532_);
lean_inc_ref(v_lctx_531_);
v___x_533_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_533_, 0, v_env_528_);
lean_ctor_set(v___x_533_, 1, v_mctx_530_);
lean_ctor_set(v___x_533_, 2, v_lctx_531_);
lean_ctor_set(v___x_533_, 3, v_options_532_);
v___x_534_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_534_, 0, v___x_533_);
lean_ctor_set(v___x_534_, 1, v_msgData_521_);
v___x_535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_535_, 0, v___x_534_);
return v___x_535_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0_spec__0___boxed(lean_object* v_msgData_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_){
_start:
{
lean_object* v_res_542_; 
v_res_542_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0_spec__0(v_msgData_536_, v___y_537_, v___y_538_, v___y_539_, v___y_540_);
lean_dec(v___y_540_);
lean_dec_ref(v___y_539_);
lean_dec(v___y_538_);
lean_dec_ref(v___y_537_);
return v_res_542_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_543_; double v___x_544_; 
v___x_543_ = lean_unsigned_to_nat(0u);
v___x_544_ = lean_float_of_nat(v___x_543_);
return v___x_544_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0___redArg(lean_object* v_cls_548_, lean_object* v_msg_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_){
_start:
{
lean_object* v_ref_555_; lean_object* v___x_556_; lean_object* v_a_557_; lean_object* v___x_559_; uint8_t v_isShared_560_; uint8_t v_isSharedCheck_601_; 
v_ref_555_ = lean_ctor_get(v___y_552_, 5);
v___x_556_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0_spec__0(v_msg_549_, v___y_550_, v___y_551_, v___y_552_, v___y_553_);
v_a_557_ = lean_ctor_get(v___x_556_, 0);
v_isSharedCheck_601_ = !lean_is_exclusive(v___x_556_);
if (v_isSharedCheck_601_ == 0)
{
v___x_559_ = v___x_556_;
v_isShared_560_ = v_isSharedCheck_601_;
goto v_resetjp_558_;
}
else
{
lean_inc(v_a_557_);
lean_dec(v___x_556_);
v___x_559_ = lean_box(0);
v_isShared_560_ = v_isSharedCheck_601_;
goto v_resetjp_558_;
}
v_resetjp_558_:
{
lean_object* v___x_561_; lean_object* v_traceState_562_; lean_object* v_env_563_; lean_object* v_nextMacroScope_564_; lean_object* v_ngen_565_; lean_object* v_auxDeclNGen_566_; lean_object* v_cache_567_; lean_object* v_messages_568_; lean_object* v_infoState_569_; lean_object* v_snapshotTasks_570_; lean_object* v___x_572_; uint8_t v_isShared_573_; uint8_t v_isSharedCheck_600_; 
v___x_561_ = lean_st_ref_take(v___y_553_);
v_traceState_562_ = lean_ctor_get(v___x_561_, 4);
v_env_563_ = lean_ctor_get(v___x_561_, 0);
v_nextMacroScope_564_ = lean_ctor_get(v___x_561_, 1);
v_ngen_565_ = lean_ctor_get(v___x_561_, 2);
v_auxDeclNGen_566_ = lean_ctor_get(v___x_561_, 3);
v_cache_567_ = lean_ctor_get(v___x_561_, 5);
v_messages_568_ = lean_ctor_get(v___x_561_, 6);
v_infoState_569_ = lean_ctor_get(v___x_561_, 7);
v_snapshotTasks_570_ = lean_ctor_get(v___x_561_, 8);
v_isSharedCheck_600_ = !lean_is_exclusive(v___x_561_);
if (v_isSharedCheck_600_ == 0)
{
v___x_572_ = v___x_561_;
v_isShared_573_ = v_isSharedCheck_600_;
goto v_resetjp_571_;
}
else
{
lean_inc(v_snapshotTasks_570_);
lean_inc(v_infoState_569_);
lean_inc(v_messages_568_);
lean_inc(v_cache_567_);
lean_inc(v_traceState_562_);
lean_inc(v_auxDeclNGen_566_);
lean_inc(v_ngen_565_);
lean_inc(v_nextMacroScope_564_);
lean_inc(v_env_563_);
lean_dec(v___x_561_);
v___x_572_ = lean_box(0);
v_isShared_573_ = v_isSharedCheck_600_;
goto v_resetjp_571_;
}
v_resetjp_571_:
{
uint64_t v_tid_574_; lean_object* v_traces_575_; lean_object* v___x_577_; uint8_t v_isShared_578_; uint8_t v_isSharedCheck_599_; 
v_tid_574_ = lean_ctor_get_uint64(v_traceState_562_, sizeof(void*)*1);
v_traces_575_ = lean_ctor_get(v_traceState_562_, 0);
v_isSharedCheck_599_ = !lean_is_exclusive(v_traceState_562_);
if (v_isSharedCheck_599_ == 0)
{
v___x_577_ = v_traceState_562_;
v_isShared_578_ = v_isSharedCheck_599_;
goto v_resetjp_576_;
}
else
{
lean_inc(v_traces_575_);
lean_dec(v_traceState_562_);
v___x_577_ = lean_box(0);
v_isShared_578_ = v_isSharedCheck_599_;
goto v_resetjp_576_;
}
v_resetjp_576_:
{
lean_object* v___x_579_; double v___x_580_; uint8_t v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_589_; 
v___x_579_ = lean_box(0);
v___x_580_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0___redArg___closed__0);
v___x_581_ = 0;
v___x_582_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0___redArg___closed__1));
v___x_583_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_583_, 0, v_cls_548_);
lean_ctor_set(v___x_583_, 1, v___x_579_);
lean_ctor_set(v___x_583_, 2, v___x_582_);
lean_ctor_set_float(v___x_583_, sizeof(void*)*3, v___x_580_);
lean_ctor_set_float(v___x_583_, sizeof(void*)*3 + 8, v___x_580_);
lean_ctor_set_uint8(v___x_583_, sizeof(void*)*3 + 16, v___x_581_);
v___x_584_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0___redArg___closed__2));
v___x_585_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_585_, 0, v___x_583_);
lean_ctor_set(v___x_585_, 1, v_a_557_);
lean_ctor_set(v___x_585_, 2, v___x_584_);
lean_inc(v_ref_555_);
v___x_586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_586_, 0, v_ref_555_);
lean_ctor_set(v___x_586_, 1, v___x_585_);
v___x_587_ = l_Lean_PersistentArray_push___redArg(v_traces_575_, v___x_586_);
if (v_isShared_578_ == 0)
{
lean_ctor_set(v___x_577_, 0, v___x_587_);
v___x_589_ = v___x_577_;
goto v_reusejp_588_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v___x_587_);
lean_ctor_set_uint64(v_reuseFailAlloc_598_, sizeof(void*)*1, v_tid_574_);
v___x_589_ = v_reuseFailAlloc_598_;
goto v_reusejp_588_;
}
v_reusejp_588_:
{
lean_object* v___x_591_; 
if (v_isShared_573_ == 0)
{
lean_ctor_set(v___x_572_, 4, v___x_589_);
v___x_591_ = v___x_572_;
goto v_reusejp_590_;
}
else
{
lean_object* v_reuseFailAlloc_597_; 
v_reuseFailAlloc_597_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_597_, 0, v_env_563_);
lean_ctor_set(v_reuseFailAlloc_597_, 1, v_nextMacroScope_564_);
lean_ctor_set(v_reuseFailAlloc_597_, 2, v_ngen_565_);
lean_ctor_set(v_reuseFailAlloc_597_, 3, v_auxDeclNGen_566_);
lean_ctor_set(v_reuseFailAlloc_597_, 4, v___x_589_);
lean_ctor_set(v_reuseFailAlloc_597_, 5, v_cache_567_);
lean_ctor_set(v_reuseFailAlloc_597_, 6, v_messages_568_);
lean_ctor_set(v_reuseFailAlloc_597_, 7, v_infoState_569_);
lean_ctor_set(v_reuseFailAlloc_597_, 8, v_snapshotTasks_570_);
v___x_591_ = v_reuseFailAlloc_597_;
goto v_reusejp_590_;
}
v_reusejp_590_:
{
lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_595_; 
v___x_592_ = lean_st_ref_set(v___y_553_, v___x_591_);
v___x_593_ = lean_box(0);
if (v_isShared_560_ == 0)
{
lean_ctor_set(v___x_559_, 0, v___x_593_);
v___x_595_ = v___x_559_;
goto v_reusejp_594_;
}
else
{
lean_object* v_reuseFailAlloc_596_; 
v_reuseFailAlloc_596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_596_, 0, v___x_593_);
v___x_595_ = v_reuseFailAlloc_596_;
goto v_reusejp_594_;
}
v_reusejp_594_:
{
return v___x_595_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0___redArg___boxed(lean_object* v_cls_602_, lean_object* v_msg_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_){
_start:
{
lean_object* v_res_609_; 
v_res_609_ = l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0___redArg(v_cls_602_, v_msg_603_, v___y_604_, v___y_605_, v___y_606_, v___y_607_);
lean_dec(v___y_607_);
lean_dec_ref(v___y_606_);
lean_dec(v___y_605_);
lean_dec_ref(v___y_604_);
return v_res_609_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkInjEq___closed__6(void){
_start:
{
lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; 
v___x_620_ = ((lean_object*)(l_Lean_Meta_Grind_mkInjEq___closed__3));
v___x_621_ = ((lean_object*)(l_Lean_Meta_Grind_mkInjEq___closed__5));
v___x_622_ = l_Lean_Name_append(v___x_621_, v___x_620_);
return v___x_622_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkInjEq___closed__8(void){
_start:
{
lean_object* v___x_624_; lean_object* v___x_625_; 
v___x_624_ = ((lean_object*)(l_Lean_Meta_Grind_mkInjEq___closed__7));
v___x_625_ = l_Lean_stringToMessageData(v___x_624_);
return v___x_625_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkInjEq(lean_object* v_e_626_, lean_object* v_a_627_, lean_object* v_a_628_, lean_object* v_a_629_, lean_object* v_a_630_, lean_object* v_a_631_, lean_object* v_a_632_, lean_object* v_a_633_, lean_object* v_a_634_, lean_object* v_a_635_, lean_object* v_a_636_){
_start:
{
if (lean_obj_tag(v_e_626_) == 5)
{
lean_object* v_fn_638_; lean_object* v_arg_639_; lean_object* v___x_640_; 
v_fn_638_ = lean_ctor_get(v_e_626_, 0);
v_arg_639_ = lean_ctor_get(v_e_626_, 1);
lean_inc_ref_n(v_arg_639_, 2);
lean_inc_ref(v_fn_638_);
v___x_640_ = l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f(v_fn_638_, v_arg_639_, v_a_627_, v_a_628_, v_a_629_, v_a_630_, v_a_631_, v_a_632_, v_a_633_, v_a_634_, v_a_635_, v_a_636_);
if (lean_obj_tag(v___x_640_) == 0)
{
lean_object* v_a_641_; lean_object* v___x_643_; uint8_t v_isShared_644_; uint8_t v_isSharedCheck_693_; 
v_a_641_ = lean_ctor_get(v___x_640_, 0);
v_isSharedCheck_693_ = !lean_is_exclusive(v___x_640_);
if (v_isSharedCheck_693_ == 0)
{
v___x_643_ = v___x_640_;
v_isShared_644_ = v_isSharedCheck_693_;
goto v_resetjp_642_;
}
else
{
lean_inc(v_a_641_);
lean_dec(v___x_640_);
v___x_643_ = lean_box(0);
v_isShared_644_ = v_isSharedCheck_693_;
goto v_resetjp_642_;
}
v_resetjp_642_:
{
if (lean_obj_tag(v_a_641_) == 1)
{
lean_object* v_val_645_; lean_object* v_fst_646_; lean_object* v_snd_647_; lean_object* v___x_649_; uint8_t v_isShared_650_; uint8_t v_isSharedCheck_688_; 
lean_del_object(v___x_643_);
v_val_645_ = lean_ctor_get(v_a_641_, 0);
lean_inc(v_val_645_);
lean_dec_ref(v_a_641_);
v_fst_646_ = lean_ctor_get(v_val_645_, 0);
v_snd_647_ = lean_ctor_get(v_val_645_, 1);
v_isSharedCheck_688_ = !lean_is_exclusive(v_val_645_);
if (v_isSharedCheck_688_ == 0)
{
v___x_649_ = v_val_645_;
v_isShared_650_ = v_isSharedCheck_688_;
goto v_resetjp_648_;
}
else
{
lean_inc(v_snd_647_);
lean_inc(v_fst_646_);
lean_dec(v_val_645_);
v___x_649_ = lean_box(0);
v_isShared_650_ = v_isSharedCheck_688_;
goto v_resetjp_648_;
}
v_resetjp_648_:
{
lean_object* v___x_651_; 
v___x_651_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_626_, v_a_627_);
if (lean_obj_tag(v___x_651_) == 0)
{
lean_object* v_a_652_; lean_object* v___x_653_; lean_object* v___y_655_; lean_object* v___y_656_; lean_object* v___y_657_; lean_object* v___y_658_; lean_object* v___y_659_; lean_object* v___y_660_; lean_object* v___x_664_; lean_object* v___x_665_; 
v_a_652_ = lean_ctor_get(v___x_651_, 0);
lean_inc(v_a_652_);
lean_dec_ref(v___x_651_);
v___x_653_ = l_Lean_Expr_app___override(v_fst_646_, v_e_626_);
v___x_664_ = lean_box(0);
lean_inc(v_a_636_);
lean_inc_ref(v_a_635_);
lean_inc(v_a_634_);
lean_inc_ref(v_a_633_);
lean_inc(v_a_632_);
lean_inc_ref(v_a_631_);
lean_inc(v_a_630_);
lean_inc_ref(v_a_629_);
lean_inc(v_a_628_);
lean_inc(v_a_627_);
lean_inc_ref(v___x_653_);
v___x_665_ = lean_grind_internalize(v___x_653_, v_a_652_, v___x_664_, v_a_627_, v_a_628_, v_a_629_, v_a_630_, v_a_631_, v_a_632_, v_a_633_, v_a_634_, v_a_635_, v_a_636_);
if (lean_obj_tag(v___x_665_) == 0)
{
lean_object* v_options_666_; uint8_t v_hasTrace_667_; 
lean_dec_ref(v___x_665_);
v_options_666_ = lean_ctor_get(v_a_635_, 2);
v_hasTrace_667_ = lean_ctor_get_uint8(v_options_666_, sizeof(void*)*1);
if (v_hasTrace_667_ == 0)
{
lean_del_object(v___x_649_);
v___y_655_ = v_a_627_;
v___y_656_ = v_a_629_;
v___y_657_ = v_a_633_;
v___y_658_ = v_a_634_;
v___y_659_ = v_a_635_;
v___y_660_ = v_a_636_;
goto v___jp_654_;
}
else
{
lean_object* v_inheritedTraceOptions_668_; lean_object* v___x_669_; lean_object* v___x_670_; uint8_t v___x_671_; 
v_inheritedTraceOptions_668_ = lean_ctor_get(v_a_635_, 13);
v___x_669_ = ((lean_object*)(l_Lean_Meta_Grind_mkInjEq___closed__3));
v___x_670_ = lean_obj_once(&l_Lean_Meta_Grind_mkInjEq___closed__6, &l_Lean_Meta_Grind_mkInjEq___closed__6_once, _init_l_Lean_Meta_Grind_mkInjEq___closed__6);
v___x_671_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_668_, v_options_666_, v___x_670_);
if (v___x_671_ == 0)
{
lean_del_object(v___x_649_);
v___y_655_ = v_a_627_;
v___y_656_ = v_a_629_;
v___y_657_ = v_a_633_;
v___y_658_ = v_a_634_;
v___y_659_ = v_a_635_;
v___y_660_ = v_a_636_;
goto v___jp_654_;
}
else
{
lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_675_; 
lean_inc_ref(v___x_653_);
v___x_672_ = l_Lean_MessageData_ofExpr(v___x_653_);
v___x_673_ = lean_obj_once(&l_Lean_Meta_Grind_mkInjEq___closed__8, &l_Lean_Meta_Grind_mkInjEq___closed__8_once, _init_l_Lean_Meta_Grind_mkInjEq___closed__8);
if (v_isShared_650_ == 0)
{
lean_ctor_set_tag(v___x_649_, 7);
lean_ctor_set(v___x_649_, 1, v___x_673_);
lean_ctor_set(v___x_649_, 0, v___x_672_);
v___x_675_ = v___x_649_;
goto v_reusejp_674_;
}
else
{
lean_object* v_reuseFailAlloc_679_; 
v_reuseFailAlloc_679_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_679_, 0, v___x_672_);
lean_ctor_set(v_reuseFailAlloc_679_, 1, v___x_673_);
v___x_675_ = v_reuseFailAlloc_679_;
goto v_reusejp_674_;
}
v_reusejp_674_:
{
lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; 
lean_inc_ref(v_arg_639_);
v___x_676_ = l_Lean_MessageData_ofExpr(v_arg_639_);
v___x_677_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_677_, 0, v___x_675_);
lean_ctor_set(v___x_677_, 1, v___x_676_);
v___x_678_ = l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0___redArg(v___x_669_, v___x_677_, v_a_633_, v_a_634_, v_a_635_, v_a_636_);
if (lean_obj_tag(v___x_678_) == 0)
{
lean_dec_ref(v___x_678_);
v___y_655_ = v_a_627_;
v___y_656_ = v_a_629_;
v___y_657_ = v_a_633_;
v___y_658_ = v_a_634_;
v___y_659_ = v_a_635_;
v___y_660_ = v_a_636_;
goto v___jp_654_;
}
else
{
lean_dec_ref(v___x_653_);
lean_dec(v_snd_647_);
lean_dec_ref(v_arg_639_);
return v___x_678_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_653_);
lean_del_object(v___x_649_);
lean_dec(v_snd_647_);
lean_dec_ref(v_arg_639_);
return v___x_665_;
}
v___jp_654_:
{
lean_object* v___x_661_; uint8_t v___x_662_; lean_object* v___x_663_; 
lean_inc_ref(v_arg_639_);
v___x_661_ = l_Lean_Expr_app___override(v_snd_647_, v_arg_639_);
v___x_662_ = 0;
v___x_663_ = l_Lean_Meta_Grind_pushEqCore___redArg(v___x_653_, v_arg_639_, v___x_661_, v___x_662_, v___y_655_, v___y_656_, v___y_657_, v___y_658_, v___y_659_, v___y_660_);
return v___x_663_;
}
}
else
{
lean_object* v_a_680_; lean_object* v___x_682_; uint8_t v_isShared_683_; uint8_t v_isSharedCheck_687_; 
lean_del_object(v___x_649_);
lean_dec(v_snd_647_);
lean_dec(v_fst_646_);
lean_dec_ref(v_arg_639_);
lean_dec_ref(v_e_626_);
v_a_680_ = lean_ctor_get(v___x_651_, 0);
v_isSharedCheck_687_ = !lean_is_exclusive(v___x_651_);
if (v_isSharedCheck_687_ == 0)
{
v___x_682_ = v___x_651_;
v_isShared_683_ = v_isSharedCheck_687_;
goto v_resetjp_681_;
}
else
{
lean_inc(v_a_680_);
lean_dec(v___x_651_);
v___x_682_ = lean_box(0);
v_isShared_683_ = v_isSharedCheck_687_;
goto v_resetjp_681_;
}
v_resetjp_681_:
{
lean_object* v___x_685_; 
if (v_isShared_683_ == 0)
{
v___x_685_ = v___x_682_;
goto v_reusejp_684_;
}
else
{
lean_object* v_reuseFailAlloc_686_; 
v_reuseFailAlloc_686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_686_, 0, v_a_680_);
v___x_685_ = v_reuseFailAlloc_686_;
goto v_reusejp_684_;
}
v_reusejp_684_:
{
return v___x_685_;
}
}
}
}
}
else
{
lean_object* v___x_689_; lean_object* v___x_691_; 
lean_dec(v_a_641_);
lean_dec_ref(v_arg_639_);
lean_dec_ref(v_e_626_);
v___x_689_ = lean_box(0);
if (v_isShared_644_ == 0)
{
lean_ctor_set(v___x_643_, 0, v___x_689_);
v___x_691_ = v___x_643_;
goto v_reusejp_690_;
}
else
{
lean_object* v_reuseFailAlloc_692_; 
v_reuseFailAlloc_692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_692_, 0, v___x_689_);
v___x_691_ = v_reuseFailAlloc_692_;
goto v_reusejp_690_;
}
v_reusejp_690_:
{
return v___x_691_;
}
}
}
}
else
{
lean_object* v_a_694_; lean_object* v___x_696_; uint8_t v_isShared_697_; uint8_t v_isSharedCheck_701_; 
lean_dec_ref(v_arg_639_);
lean_dec_ref(v_e_626_);
v_a_694_ = lean_ctor_get(v___x_640_, 0);
v_isSharedCheck_701_ = !lean_is_exclusive(v___x_640_);
if (v_isSharedCheck_701_ == 0)
{
v___x_696_ = v___x_640_;
v_isShared_697_ = v_isSharedCheck_701_;
goto v_resetjp_695_;
}
else
{
lean_inc(v_a_694_);
lean_dec(v___x_640_);
v___x_696_ = lean_box(0);
v_isShared_697_ = v_isSharedCheck_701_;
goto v_resetjp_695_;
}
v_resetjp_695_:
{
lean_object* v___x_699_; 
if (v_isShared_697_ == 0)
{
v___x_699_ = v___x_696_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v_a_694_);
v___x_699_ = v_reuseFailAlloc_700_;
goto v_reusejp_698_;
}
v_reusejp_698_:
{
return v___x_699_;
}
}
}
}
else
{
lean_object* v___x_702_; lean_object* v___x_703_; 
lean_dec_ref(v_e_626_);
v___x_702_ = lean_box(0);
v___x_703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_703_, 0, v___x_702_);
return v___x_703_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkInjEq___boxed(lean_object* v_e_704_, lean_object* v_a_705_, lean_object* v_a_706_, lean_object* v_a_707_, lean_object* v_a_708_, lean_object* v_a_709_, lean_object* v_a_710_, lean_object* v_a_711_, lean_object* v_a_712_, lean_object* v_a_713_, lean_object* v_a_714_, lean_object* v_a_715_){
_start:
{
lean_object* v_res_716_; 
v_res_716_ = l_Lean_Meta_Grind_mkInjEq(v_e_704_, v_a_705_, v_a_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_);
lean_dec(v_a_714_);
lean_dec_ref(v_a_713_);
lean_dec(v_a_712_);
lean_dec_ref(v_a_711_);
lean_dec(v_a_710_);
lean_dec_ref(v_a_709_);
lean_dec(v_a_708_);
lean_dec_ref(v_a_707_);
lean_dec(v_a_706_);
lean_dec(v_a_705_);
return v_res_716_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0(lean_object* v_cls_717_, lean_object* v_msg_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_){
_start:
{
lean_object* v___x_730_; 
v___x_730_ = l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0___redArg(v_cls_717_, v_msg_718_, v___y_725_, v___y_726_, v___y_727_, v___y_728_);
return v___x_730_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0___boxed(lean_object* v_cls_731_, lean_object* v_msg_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_){
_start:
{
lean_object* v_res_744_; 
v_res_744_ = l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0(v_cls_731_, v_msg_732_, v___y_733_, v___y_734_, v___y_735_, v___y_736_, v___y_737_, v___y_738_, v___y_739_, v___y_740_, v___y_741_, v___y_742_);
lean_dec(v___y_742_);
lean_dec_ref(v___y_741_);
lean_dec(v___y_740_);
lean_dec_ref(v___y_739_);
lean_dec(v___y_738_);
lean_dec_ref(v___y_737_);
lean_dec(v___y_736_);
lean_dec_ref(v___y_735_);
lean_dec(v___y_734_);
lean_dec(v___y_733_);
return v_res_744_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1_spec__2___redArg(lean_object* v_keys_745_, lean_object* v_vals_746_, lean_object* v_i_747_, lean_object* v_k_748_){
_start:
{
lean_object* v___x_749_; uint8_t v___x_750_; 
v___x_749_ = lean_array_get_size(v_keys_745_);
v___x_750_ = lean_nat_dec_lt(v_i_747_, v___x_749_);
if (v___x_750_ == 0)
{
lean_object* v___x_751_; 
lean_dec(v_i_747_);
v___x_751_ = lean_box(0);
return v___x_751_;
}
else
{
lean_object* v_k_x27_752_; uint8_t v___x_753_; 
v_k_x27_752_ = lean_array_fget_borrowed(v_keys_745_, v_i_747_);
v___x_753_ = l_Lean_instBEqHeadIndex_beq(v_k_748_, v_k_x27_752_);
if (v___x_753_ == 0)
{
lean_object* v___x_754_; lean_object* v___x_755_; 
v___x_754_ = lean_unsigned_to_nat(1u);
v___x_755_ = lean_nat_add(v_i_747_, v___x_754_);
lean_dec(v_i_747_);
v_i_747_ = v___x_755_;
goto _start;
}
else
{
lean_object* v___x_757_; lean_object* v___x_758_; 
v___x_757_ = lean_array_fget_borrowed(v_vals_746_, v_i_747_);
lean_dec(v_i_747_);
lean_inc(v___x_757_);
v___x_758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_758_, 0, v___x_757_);
return v___x_758_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_keys_759_, lean_object* v_vals_760_, lean_object* v_i_761_, lean_object* v_k_762_){
_start:
{
lean_object* v_res_763_; 
v_res_763_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1_spec__2___redArg(v_keys_759_, v_vals_760_, v_i_761_, v_k_762_);
lean_dec(v_k_762_);
lean_dec_ref(v_vals_760_);
lean_dec_ref(v_keys_759_);
return v_res_763_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1___redArg(lean_object* v_x_764_, size_t v_x_765_, lean_object* v_x_766_){
_start:
{
if (lean_obj_tag(v_x_764_) == 0)
{
lean_object* v_es_767_; lean_object* v___x_768_; size_t v___x_769_; size_t v___x_770_; size_t v___x_771_; lean_object* v_j_772_; lean_object* v___x_773_; 
v_es_767_ = lean_ctor_get(v_x_764_, 0);
v___x_768_ = lean_box(2);
v___x_769_ = ((size_t)5ULL);
v___x_770_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1___redArg___closed__1);
v___x_771_ = lean_usize_land(v_x_765_, v___x_770_);
v_j_772_ = lean_usize_to_nat(v___x_771_);
v___x_773_ = lean_array_get_borrowed(v___x_768_, v_es_767_, v_j_772_);
lean_dec(v_j_772_);
switch(lean_obj_tag(v___x_773_))
{
case 0:
{
lean_object* v_key_774_; lean_object* v_val_775_; uint8_t v___x_776_; 
v_key_774_ = lean_ctor_get(v___x_773_, 0);
v_val_775_ = lean_ctor_get(v___x_773_, 1);
v___x_776_ = l_Lean_instBEqHeadIndex_beq(v_x_766_, v_key_774_);
if (v___x_776_ == 0)
{
lean_object* v___x_777_; 
v___x_777_ = lean_box(0);
return v___x_777_;
}
else
{
lean_object* v___x_778_; 
lean_inc(v_val_775_);
v___x_778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_778_, 0, v_val_775_);
return v___x_778_;
}
}
case 1:
{
lean_object* v_node_779_; size_t v___x_780_; 
v_node_779_ = lean_ctor_get(v___x_773_, 0);
v___x_780_ = lean_usize_shift_right(v_x_765_, v___x_769_);
v_x_764_ = v_node_779_;
v_x_765_ = v___x_780_;
goto _start;
}
default: 
{
lean_object* v___x_782_; 
v___x_782_ = lean_box(0);
return v___x_782_;
}
}
}
else
{
lean_object* v_ks_783_; lean_object* v_vs_784_; lean_object* v___x_785_; lean_object* v___x_786_; 
v_ks_783_ = lean_ctor_get(v_x_764_, 0);
v_vs_784_ = lean_ctor_get(v_x_764_, 1);
v___x_785_ = lean_unsigned_to_nat(0u);
v___x_786_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1_spec__2___redArg(v_ks_783_, v_vs_784_, v___x_785_, v_x_766_);
return v___x_786_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1___redArg___boxed(lean_object* v_x_787_, lean_object* v_x_788_, lean_object* v_x_789_){
_start:
{
size_t v_x_9714__boxed_790_; lean_object* v_res_791_; 
v_x_9714__boxed_790_ = lean_unbox_usize(v_x_788_);
lean_dec(v_x_788_);
v_res_791_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1___redArg(v_x_787_, v_x_9714__boxed_790_, v_x_789_);
lean_dec(v_x_789_);
lean_dec_ref(v_x_787_);
return v_res_791_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1___redArg(lean_object* v_x_792_, lean_object* v_x_793_){
_start:
{
uint64_t v___x_794_; size_t v___x_795_; lean_object* v___x_796_; 
v___x_794_ = l_Lean_HeadIndex_hash(v_x_793_);
v___x_795_ = lean_uint64_to_usize(v___x_794_);
v___x_796_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1___redArg(v_x_792_, v___x_795_, v_x_793_);
return v___x_796_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1___redArg___boxed(lean_object* v_x_797_, lean_object* v_x_798_){
_start:
{
lean_object* v_res_799_; 
v_res_799_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1___redArg(v_x_797_, v_x_798_);
lean_dec(v_x_798_);
lean_dec_ref(v_x_797_);
return v_res_799_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__0___redArg(lean_object* v_f_800_, lean_object* v_as_x27_801_, lean_object* v_b_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_){
_start:
{
if (lean_obj_tag(v_as_x27_801_) == 0)
{
lean_object* v___x_814_; 
v___x_814_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_814_, 0, v_b_802_);
return v___x_814_;
}
else
{
lean_object* v_head_815_; lean_object* v_tail_816_; lean_object* v___x_817_; uint8_t v___y_819_; uint8_t v___x_823_; 
v_head_815_ = lean_ctor_get(v_as_x27_801_, 0);
v_tail_816_ = lean_ctor_get(v_as_x27_801_, 1);
v___x_817_ = lean_box(0);
v___x_823_ = l_Lean_Expr_isApp(v_head_815_);
if (v___x_823_ == 0)
{
v___y_819_ = v___x_823_;
goto v___jp_818_;
}
else
{
lean_object* v___x_824_; uint8_t v___x_825_; 
v___x_824_ = l_Lean_Expr_appFn_x21(v_head_815_);
v___x_825_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_824_, v_f_800_);
lean_dec_ref(v___x_824_);
v___y_819_ = v___x_825_;
goto v___jp_818_;
}
v___jp_818_:
{
if (v___y_819_ == 0)
{
v_as_x27_801_ = v_tail_816_;
v_b_802_ = v___x_817_;
goto _start;
}
else
{
lean_object* v___x_821_; 
lean_inc(v_head_815_);
v___x_821_ = l_Lean_Meta_Grind_mkInjEq(v_head_815_, v___y_803_, v___y_804_, v___y_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_, v___y_812_);
if (lean_obj_tag(v___x_821_) == 0)
{
lean_dec_ref(v___x_821_);
v_as_x27_801_ = v_tail_816_;
v_b_802_ = v___x_817_;
goto _start;
}
else
{
return v___x_821_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__0___redArg___boxed(lean_object* v_f_826_, lean_object* v_as_x27_827_, lean_object* v_b_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_){
_start:
{
lean_object* v_res_840_; 
v_res_840_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__0___redArg(v_f_826_, v_as_x27_827_, v_b_828_, v___y_829_, v___y_830_, v___y_831_, v___y_832_, v___y_833_, v___y_834_, v___y_835_, v___y_836_, v___y_837_, v___y_838_);
lean_dec(v___y_838_);
lean_dec_ref(v___y_837_);
lean_dec(v___y_836_);
lean_dec_ref(v___y_835_);
lean_dec(v___y_834_);
lean_dec_ref(v___y_833_);
lean_dec(v___y_832_);
lean_dec_ref(v___y_831_);
lean_dec(v___y_830_);
lean_dec(v___y_829_);
lean_dec(v_as_x27_827_);
lean_dec_ref(v_f_826_);
return v_res_840_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn(lean_object* v_us_841_, lean_object* v_00_u03b1_842_, lean_object* v_00_u03b2_843_, lean_object* v_f_844_, lean_object* v_h_845_, lean_object* v_a_846_, lean_object* v_a_847_, lean_object* v_a_848_, lean_object* v_a_849_, lean_object* v_a_850_, lean_object* v_a_851_, lean_object* v_a_852_, lean_object* v_a_853_, lean_object* v_a_854_, lean_object* v_a_855_){
_start:
{
lean_object* v___x_857_; lean_object* v_toGoalState_858_; lean_object* v_inj_859_; lean_object* v_mvarId_860_; lean_object* v___x_862_; uint8_t v_isShared_863_; uint8_t v_isSharedCheck_924_; 
v___x_857_ = lean_st_ref_take(v_a_846_);
v_toGoalState_858_ = lean_ctor_get(v___x_857_, 0);
lean_inc_ref(v_toGoalState_858_);
v_inj_859_ = lean_ctor_get(v_toGoalState_858_, 13);
lean_inc_ref(v_inj_859_);
v_mvarId_860_ = lean_ctor_get(v___x_857_, 1);
v_isSharedCheck_924_ = !lean_is_exclusive(v___x_857_);
if (v_isSharedCheck_924_ == 0)
{
lean_object* v_unused_925_; 
v_unused_925_ = lean_ctor_get(v___x_857_, 0);
lean_dec(v_unused_925_);
v___x_862_ = v___x_857_;
v_isShared_863_ = v_isSharedCheck_924_;
goto v_resetjp_861_;
}
else
{
lean_inc(v_mvarId_860_);
lean_dec(v___x_857_);
v___x_862_ = lean_box(0);
v_isShared_863_ = v_isSharedCheck_924_;
goto v_resetjp_861_;
}
v_resetjp_861_:
{
lean_object* v_nextDeclIdx_864_; lean_object* v_enodeMap_865_; lean_object* v_exprs_866_; lean_object* v_parents_867_; lean_object* v_congrTable_868_; lean_object* v_appMap_869_; lean_object* v_indicesFound_870_; lean_object* v_newFacts_871_; uint8_t v_inconsistent_872_; lean_object* v_nextIdx_873_; lean_object* v_newRawFacts_874_; lean_object* v_facts_875_; lean_object* v_extThms_876_; lean_object* v_ematch_877_; lean_object* v_split_878_; lean_object* v_clean_879_; lean_object* v_sstates_880_; lean_object* v___x_882_; uint8_t v_isShared_883_; uint8_t v_isSharedCheck_922_; 
v_nextDeclIdx_864_ = lean_ctor_get(v_toGoalState_858_, 0);
v_enodeMap_865_ = lean_ctor_get(v_toGoalState_858_, 1);
v_exprs_866_ = lean_ctor_get(v_toGoalState_858_, 2);
v_parents_867_ = lean_ctor_get(v_toGoalState_858_, 3);
v_congrTable_868_ = lean_ctor_get(v_toGoalState_858_, 4);
v_appMap_869_ = lean_ctor_get(v_toGoalState_858_, 5);
v_indicesFound_870_ = lean_ctor_get(v_toGoalState_858_, 6);
v_newFacts_871_ = lean_ctor_get(v_toGoalState_858_, 7);
v_inconsistent_872_ = lean_ctor_get_uint8(v_toGoalState_858_, sizeof(void*)*17);
v_nextIdx_873_ = lean_ctor_get(v_toGoalState_858_, 8);
v_newRawFacts_874_ = lean_ctor_get(v_toGoalState_858_, 9);
v_facts_875_ = lean_ctor_get(v_toGoalState_858_, 10);
v_extThms_876_ = lean_ctor_get(v_toGoalState_858_, 11);
v_ematch_877_ = lean_ctor_get(v_toGoalState_858_, 12);
v_split_878_ = lean_ctor_get(v_toGoalState_858_, 14);
v_clean_879_ = lean_ctor_get(v_toGoalState_858_, 15);
v_sstates_880_ = lean_ctor_get(v_toGoalState_858_, 16);
v_isSharedCheck_922_ = !lean_is_exclusive(v_toGoalState_858_);
if (v_isSharedCheck_922_ == 0)
{
lean_object* v_unused_923_; 
v_unused_923_ = lean_ctor_get(v_toGoalState_858_, 13);
lean_dec(v_unused_923_);
v___x_882_ = v_toGoalState_858_;
v_isShared_883_ = v_isSharedCheck_922_;
goto v_resetjp_881_;
}
else
{
lean_inc(v_sstates_880_);
lean_inc(v_clean_879_);
lean_inc(v_split_878_);
lean_inc(v_ematch_877_);
lean_inc(v_extThms_876_);
lean_inc(v_facts_875_);
lean_inc(v_newRawFacts_874_);
lean_inc(v_nextIdx_873_);
lean_inc(v_newFacts_871_);
lean_inc(v_indicesFound_870_);
lean_inc(v_appMap_869_);
lean_inc(v_congrTable_868_);
lean_inc(v_parents_867_);
lean_inc(v_exprs_866_);
lean_inc(v_enodeMap_865_);
lean_inc(v_nextDeclIdx_864_);
lean_dec(v_toGoalState_858_);
v___x_882_ = lean_box(0);
v_isShared_883_ = v_isSharedCheck_922_;
goto v_resetjp_881_;
}
v_resetjp_881_:
{
lean_object* v_thms_884_; lean_object* v_fns_885_; lean_object* v___x_887_; uint8_t v_isShared_888_; uint8_t v_isSharedCheck_921_; 
v_thms_884_ = lean_ctor_get(v_inj_859_, 0);
v_fns_885_ = lean_ctor_get(v_inj_859_, 1);
v_isSharedCheck_921_ = !lean_is_exclusive(v_inj_859_);
if (v_isSharedCheck_921_ == 0)
{
v___x_887_ = v_inj_859_;
v_isShared_888_ = v_isSharedCheck_921_;
goto v_resetjp_886_;
}
else
{
lean_inc(v_fns_885_);
lean_inc(v_thms_884_);
lean_dec(v_inj_859_);
v___x_887_ = lean_box(0);
v_isShared_888_ = v_isSharedCheck_921_;
goto v_resetjp_886_;
}
v_resetjp_886_:
{
lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_893_; 
v___x_889_ = lean_box(0);
v___x_890_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_890_, 0, v_us_841_);
lean_ctor_set(v___x_890_, 1, v_00_u03b1_842_);
lean_ctor_set(v___x_890_, 2, v_00_u03b2_843_);
lean_ctor_set(v___x_890_, 3, v_h_845_);
lean_ctor_set(v___x_890_, 4, v___x_889_);
lean_inc_ref(v_f_844_);
v___x_891_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2___redArg(v_fns_885_, v_f_844_, v___x_890_);
if (v_isShared_888_ == 0)
{
lean_ctor_set(v___x_887_, 1, v___x_891_);
v___x_893_ = v___x_887_;
goto v_reusejp_892_;
}
else
{
lean_object* v_reuseFailAlloc_920_; 
v_reuseFailAlloc_920_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_920_, 0, v_thms_884_);
lean_ctor_set(v_reuseFailAlloc_920_, 1, v___x_891_);
v___x_893_ = v_reuseFailAlloc_920_;
goto v_reusejp_892_;
}
v_reusejp_892_:
{
lean_object* v___x_895_; 
if (v_isShared_883_ == 0)
{
lean_ctor_set(v___x_882_, 13, v___x_893_);
v___x_895_ = v___x_882_;
goto v_reusejp_894_;
}
else
{
lean_object* v_reuseFailAlloc_919_; 
v_reuseFailAlloc_919_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_919_, 0, v_nextDeclIdx_864_);
lean_ctor_set(v_reuseFailAlloc_919_, 1, v_enodeMap_865_);
lean_ctor_set(v_reuseFailAlloc_919_, 2, v_exprs_866_);
lean_ctor_set(v_reuseFailAlloc_919_, 3, v_parents_867_);
lean_ctor_set(v_reuseFailAlloc_919_, 4, v_congrTable_868_);
lean_ctor_set(v_reuseFailAlloc_919_, 5, v_appMap_869_);
lean_ctor_set(v_reuseFailAlloc_919_, 6, v_indicesFound_870_);
lean_ctor_set(v_reuseFailAlloc_919_, 7, v_newFacts_871_);
lean_ctor_set(v_reuseFailAlloc_919_, 8, v_nextIdx_873_);
lean_ctor_set(v_reuseFailAlloc_919_, 9, v_newRawFacts_874_);
lean_ctor_set(v_reuseFailAlloc_919_, 10, v_facts_875_);
lean_ctor_set(v_reuseFailAlloc_919_, 11, v_extThms_876_);
lean_ctor_set(v_reuseFailAlloc_919_, 12, v_ematch_877_);
lean_ctor_set(v_reuseFailAlloc_919_, 13, v___x_893_);
lean_ctor_set(v_reuseFailAlloc_919_, 14, v_split_878_);
lean_ctor_set(v_reuseFailAlloc_919_, 15, v_clean_879_);
lean_ctor_set(v_reuseFailAlloc_919_, 16, v_sstates_880_);
lean_ctor_set_uint8(v_reuseFailAlloc_919_, sizeof(void*)*17, v_inconsistent_872_);
v___x_895_ = v_reuseFailAlloc_919_;
goto v_reusejp_894_;
}
v_reusejp_894_:
{
lean_object* v___x_897_; 
if (v_isShared_863_ == 0)
{
lean_ctor_set(v___x_862_, 0, v___x_895_);
v___x_897_ = v___x_862_;
goto v_reusejp_896_;
}
else
{
lean_object* v_reuseFailAlloc_918_; 
v_reuseFailAlloc_918_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_918_, 0, v___x_895_);
lean_ctor_set(v_reuseFailAlloc_918_, 1, v_mvarId_860_);
v___x_897_ = v_reuseFailAlloc_918_;
goto v_reusejp_896_;
}
v_reusejp_896_:
{
lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___y_901_; lean_object* v_toGoalState_912_; lean_object* v_appMap_913_; lean_object* v___x_914_; lean_object* v___x_915_; 
v___x_898_ = lean_st_ref_set(v_a_846_, v___x_897_);
v___x_899_ = lean_st_ref_get(v_a_846_);
v_toGoalState_912_ = lean_ctor_get(v___x_899_, 0);
lean_inc_ref(v_toGoalState_912_);
lean_dec(v___x_899_);
v_appMap_913_ = lean_ctor_get(v_toGoalState_912_, 5);
lean_inc_ref(v_appMap_913_);
lean_dec_ref(v_toGoalState_912_);
lean_inc_ref(v_f_844_);
v___x_914_ = l_Lean_Expr_toHeadIndex(v_f_844_);
v___x_915_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1___redArg(v_appMap_913_, v___x_914_);
lean_dec(v___x_914_);
lean_dec_ref(v_appMap_913_);
if (lean_obj_tag(v___x_915_) == 0)
{
lean_object* v___x_916_; 
v___x_916_ = lean_box(0);
v___y_901_ = v___x_916_;
goto v___jp_900_;
}
else
{
lean_object* v_val_917_; 
v_val_917_ = lean_ctor_get(v___x_915_, 0);
lean_inc(v_val_917_);
lean_dec_ref(v___x_915_);
v___y_901_ = v_val_917_;
goto v___jp_900_;
}
v___jp_900_:
{
lean_object* v___x_902_; lean_object* v___x_903_; 
v___x_902_ = lean_box(0);
v___x_903_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__0___redArg(v_f_844_, v___y_901_, v___x_902_, v_a_846_, v_a_847_, v_a_848_, v_a_849_, v_a_850_, v_a_851_, v_a_852_, v_a_853_, v_a_854_, v_a_855_);
lean_dec(v___y_901_);
lean_dec_ref(v_f_844_);
if (lean_obj_tag(v___x_903_) == 0)
{
lean_object* v___x_905_; uint8_t v_isShared_906_; uint8_t v_isSharedCheck_910_; 
v_isSharedCheck_910_ = !lean_is_exclusive(v___x_903_);
if (v_isSharedCheck_910_ == 0)
{
lean_object* v_unused_911_; 
v_unused_911_ = lean_ctor_get(v___x_903_, 0);
lean_dec(v_unused_911_);
v___x_905_ = v___x_903_;
v_isShared_906_ = v_isSharedCheck_910_;
goto v_resetjp_904_;
}
else
{
lean_dec(v___x_903_);
v___x_905_ = lean_box(0);
v_isShared_906_ = v_isSharedCheck_910_;
goto v_resetjp_904_;
}
v_resetjp_904_:
{
lean_object* v___x_908_; 
if (v_isShared_906_ == 0)
{
lean_ctor_set(v___x_905_, 0, v___x_902_);
v___x_908_ = v___x_905_;
goto v_reusejp_907_;
}
else
{
lean_object* v_reuseFailAlloc_909_; 
v_reuseFailAlloc_909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_909_, 0, v___x_902_);
v___x_908_ = v_reuseFailAlloc_909_;
goto v_reusejp_907_;
}
v_reusejp_907_:
{
return v___x_908_;
}
}
}
else
{
return v___x_903_;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn___boxed(lean_object* v_us_926_, lean_object* v_00_u03b1_927_, lean_object* v_00_u03b2_928_, lean_object* v_f_929_, lean_object* v_h_930_, lean_object* v_a_931_, lean_object* v_a_932_, lean_object* v_a_933_, lean_object* v_a_934_, lean_object* v_a_935_, lean_object* v_a_936_, lean_object* v_a_937_, lean_object* v_a_938_, lean_object* v_a_939_, lean_object* v_a_940_, lean_object* v_a_941_){
_start:
{
lean_object* v_res_942_; 
v_res_942_ = l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn(v_us_926_, v_00_u03b1_927_, v_00_u03b2_928_, v_f_929_, v_h_930_, v_a_931_, v_a_932_, v_a_933_, v_a_934_, v_a_935_, v_a_936_, v_a_937_, v_a_938_, v_a_939_, v_a_940_);
lean_dec(v_a_940_);
lean_dec_ref(v_a_939_);
lean_dec(v_a_938_);
lean_dec_ref(v_a_937_);
lean_dec(v_a_936_);
lean_dec_ref(v_a_935_);
lean_dec(v_a_934_);
lean_dec_ref(v_a_933_);
lean_dec(v_a_932_);
lean_dec(v_a_931_);
return v_res_942_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__0(lean_object* v_f_943_, lean_object* v_as_944_, lean_object* v_as_x27_945_, lean_object* v_b_946_, lean_object* v_a_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_){
_start:
{
lean_object* v___x_959_; 
v___x_959_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__0___redArg(v_f_943_, v_as_x27_945_, v_b_946_, v___y_948_, v___y_949_, v___y_950_, v___y_951_, v___y_952_, v___y_953_, v___y_954_, v___y_955_, v___y_956_, v___y_957_);
return v___x_959_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__0___boxed(lean_object* v_f_960_, lean_object* v_as_961_, lean_object* v_as_x27_962_, lean_object* v_b_963_, lean_object* v_a_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_){
_start:
{
lean_object* v_res_976_; 
v_res_976_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__0(v_f_960_, v_as_961_, v_as_x27_962_, v_b_963_, v_a_964_, v___y_965_, v___y_966_, v___y_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_, v___y_974_);
lean_dec(v___y_974_);
lean_dec_ref(v___y_973_);
lean_dec(v___y_972_);
lean_dec_ref(v___y_971_);
lean_dec(v___y_970_);
lean_dec_ref(v___y_969_);
lean_dec(v___y_968_);
lean_dec_ref(v___y_967_);
lean_dec(v___y_966_);
lean_dec(v___y_965_);
lean_dec(v_as_x27_962_);
lean_dec(v_as_961_);
lean_dec_ref(v_f_960_);
return v_res_976_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1(lean_object* v_00_u03b2_977_, lean_object* v_x_978_, lean_object* v_x_979_){
_start:
{
lean_object* v___x_980_; 
v___x_980_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1___redArg(v_x_978_, v_x_979_);
return v___x_980_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1___boxed(lean_object* v_00_u03b2_981_, lean_object* v_x_982_, lean_object* v_x_983_){
_start:
{
lean_object* v_res_984_; 
v_res_984_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1(v_00_u03b2_981_, v_x_982_, v_x_983_);
lean_dec(v_x_983_);
lean_dec_ref(v_x_982_);
return v_res_984_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1(lean_object* v_00_u03b2_985_, lean_object* v_x_986_, size_t v_x_987_, lean_object* v_x_988_){
_start:
{
lean_object* v___x_989_; 
v___x_989_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1___redArg(v_x_986_, v_x_987_, v_x_988_);
return v___x_989_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1___boxed(lean_object* v_00_u03b2_990_, lean_object* v_x_991_, lean_object* v_x_992_, lean_object* v_x_993_){
_start:
{
size_t v_x_9975__boxed_994_; lean_object* v_res_995_; 
v_x_9975__boxed_994_ = lean_unbox_usize(v_x_992_);
lean_dec(v_x_992_);
v_res_995_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1(v_00_u03b2_990_, v_x_991_, v_x_9975__boxed_994_, v_x_993_);
lean_dec(v_x_993_);
lean_dec_ref(v_x_991_);
return v_res_995_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_996_, lean_object* v_keys_997_, lean_object* v_vals_998_, lean_object* v_heq_999_, lean_object* v_i_1000_, lean_object* v_k_1001_){
_start:
{
lean_object* v___x_1002_; 
v___x_1002_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1_spec__2___redArg(v_keys_997_, v_vals_998_, v_i_1000_, v_k_1001_);
return v___x_1002_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1003_, lean_object* v_keys_1004_, lean_object* v_vals_1005_, lean_object* v_heq_1006_, lean_object* v_i_1007_, lean_object* v_k_1008_){
_start:
{
lean_object* v_res_1009_; 
v_res_1009_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1_spec__2(v_00_u03b2_1003_, v_keys_1004_, v_vals_1005_, v_heq_1006_, v_i_1007_, v_k_1008_);
lean_dec(v_k_1008_);
lean_dec_ref(v_vals_1005_);
lean_dec_ref(v_keys_1004_);
return v_res_1009_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj(lean_object* v_e_1015_, lean_object* v_a_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_, lean_object* v_a_1023_, lean_object* v_a_1024_, lean_object* v_a_1025_){
_start:
{
lean_object* v___x_1030_; uint8_t v___x_1031_; 
lean_inc_ref(v_e_1015_);
v___x_1030_ = l_Lean_Expr_cleanupAnnotations(v_e_1015_);
v___x_1031_ = l_Lean_Expr_isApp(v___x_1030_);
if (v___x_1031_ == 0)
{
lean_dec_ref(v___x_1030_);
lean_dec_ref(v_e_1015_);
goto v___jp_1027_;
}
else
{
lean_object* v_arg_1032_; lean_object* v___x_1033_; uint8_t v___x_1034_; 
v_arg_1032_ = lean_ctor_get(v___x_1030_, 1);
lean_inc_ref(v_arg_1032_);
v___x_1033_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1030_);
v___x_1034_ = l_Lean_Expr_isApp(v___x_1033_);
if (v___x_1034_ == 0)
{
lean_dec_ref(v___x_1033_);
lean_dec_ref(v_arg_1032_);
lean_dec_ref(v_e_1015_);
goto v___jp_1027_;
}
else
{
lean_object* v_arg_1035_; lean_object* v___x_1036_; uint8_t v___x_1037_; 
v_arg_1035_ = lean_ctor_get(v___x_1033_, 1);
lean_inc_ref(v_arg_1035_);
v___x_1036_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1033_);
v___x_1037_ = l_Lean_Expr_isApp(v___x_1036_);
if (v___x_1037_ == 0)
{
lean_dec_ref(v___x_1036_);
lean_dec_ref(v_arg_1035_);
lean_dec_ref(v_arg_1032_);
lean_dec_ref(v_e_1015_);
goto v___jp_1027_;
}
else
{
lean_object* v_arg_1038_; lean_object* v___x_1039_; lean_object* v_f_1041_; lean_object* v___y_1042_; lean_object* v___y_1043_; lean_object* v___y_1044_; lean_object* v___y_1045_; lean_object* v___y_1046_; lean_object* v___y_1047_; lean_object* v___y_1048_; lean_object* v___y_1049_; lean_object* v___y_1050_; lean_object* v___y_1051_; lean_object* v___x_1065_; uint8_t v___x_1066_; 
v_arg_1038_ = lean_ctor_get(v___x_1036_, 1);
lean_inc_ref(v_arg_1038_);
v___x_1039_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1036_);
v___x_1065_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj___closed__2));
v___x_1066_ = l_Lean_Expr_isConstOf(v___x_1039_, v___x_1065_);
if (v___x_1066_ == 0)
{
lean_dec_ref(v___x_1039_);
lean_dec_ref(v_arg_1038_);
lean_dec_ref(v_arg_1035_);
lean_dec_ref(v_arg_1032_);
lean_dec_ref(v_e_1015_);
goto v___jp_1027_;
}
else
{
lean_object* v___x_1067_; 
lean_inc_ref(v_e_1015_);
v___x_1067_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_e_1015_, v_a_1016_, v_a_1020_, v_a_1022_, v_a_1023_, v_a_1024_, v_a_1025_);
if (lean_obj_tag(v___x_1067_) == 0)
{
lean_object* v_a_1068_; lean_object* v___x_1070_; uint8_t v_isShared_1071_; uint8_t v_isSharedCheck_1101_; 
v_a_1068_ = lean_ctor_get(v___x_1067_, 0);
v_isSharedCheck_1101_ = !lean_is_exclusive(v___x_1067_);
if (v_isSharedCheck_1101_ == 0)
{
v___x_1070_ = v___x_1067_;
v_isShared_1071_ = v_isSharedCheck_1101_;
goto v_resetjp_1069_;
}
else
{
lean_inc(v_a_1068_);
lean_dec(v___x_1067_);
v___x_1070_ = lean_box(0);
v_isShared_1071_ = v_isSharedCheck_1101_;
goto v_resetjp_1069_;
}
v_resetjp_1069_:
{
uint8_t v___x_1072_; 
v___x_1072_ = lean_unbox(v_a_1068_);
lean_dec(v_a_1068_);
if (v___x_1072_ == 0)
{
lean_object* v___x_1073_; lean_object* v___x_1075_; 
lean_dec_ref(v___x_1039_);
lean_dec_ref(v_arg_1038_);
lean_dec_ref(v_arg_1035_);
lean_dec_ref(v_arg_1032_);
lean_dec_ref(v_e_1015_);
v___x_1073_ = lean_box(0);
if (v_isShared_1071_ == 0)
{
lean_ctor_set(v___x_1070_, 0, v___x_1073_);
v___x_1075_ = v___x_1070_;
goto v_reusejp_1074_;
}
else
{
lean_object* v_reuseFailAlloc_1076_; 
v_reuseFailAlloc_1076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1076_, 0, v___x_1073_);
v___x_1075_ = v_reuseFailAlloc_1076_;
goto v_reusejp_1074_;
}
v_reusejp_1074_:
{
return v___x_1075_;
}
}
else
{
lean_object* v___x_1077_; uint8_t v___x_1078_; 
lean_del_object(v___x_1070_);
lean_inc_ref(v_arg_1032_);
v___x_1077_ = l_Lean_Expr_eta(v_arg_1032_);
v___x_1078_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_arg_1032_, v___x_1077_);
if (v___x_1078_ == 0)
{
lean_object* v___x_1079_; 
lean_dec_ref(v_arg_1032_);
v___x_1079_ = l_Lean_Meta_Grind_preprocessLight___redArg(v___x_1077_, v_a_1017_, v_a_1018_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_, v_a_1023_, v_a_1024_, v_a_1025_);
if (lean_obj_tag(v___x_1079_) == 0)
{
lean_object* v_a_1080_; lean_object* v___x_1081_; 
v_a_1080_ = lean_ctor_get(v___x_1079_, 0);
lean_inc(v_a_1080_);
lean_dec_ref(v___x_1079_);
v___x_1081_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_1015_, v_a_1016_);
if (lean_obj_tag(v___x_1081_) == 0)
{
lean_object* v_a_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; 
v_a_1082_ = lean_ctor_get(v___x_1081_, 0);
lean_inc(v_a_1082_);
lean_dec_ref(v___x_1081_);
v___x_1083_ = lean_box(0);
lean_inc(v_a_1025_);
lean_inc_ref(v_a_1024_);
lean_inc(v_a_1023_);
lean_inc_ref(v_a_1022_);
lean_inc(v_a_1021_);
lean_inc_ref(v_a_1020_);
lean_inc(v_a_1019_);
lean_inc_ref(v_a_1018_);
lean_inc(v_a_1017_);
lean_inc(v_a_1016_);
lean_inc(v_a_1080_);
v___x_1084_ = lean_grind_internalize(v_a_1080_, v_a_1082_, v___x_1083_, v_a_1016_, v_a_1017_, v_a_1018_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_, v_a_1023_, v_a_1024_, v_a_1025_);
if (lean_obj_tag(v___x_1084_) == 0)
{
lean_dec_ref(v___x_1084_);
v_f_1041_ = v_a_1080_;
v___y_1042_ = v_a_1016_;
v___y_1043_ = v_a_1017_;
v___y_1044_ = v_a_1018_;
v___y_1045_ = v_a_1019_;
v___y_1046_ = v_a_1020_;
v___y_1047_ = v_a_1021_;
v___y_1048_ = v_a_1022_;
v___y_1049_ = v_a_1023_;
v___y_1050_ = v_a_1024_;
v___y_1051_ = v_a_1025_;
goto v___jp_1040_;
}
else
{
lean_dec(v_a_1080_);
lean_dec_ref(v___x_1039_);
lean_dec_ref(v_arg_1038_);
lean_dec_ref(v_arg_1035_);
lean_dec_ref(v_e_1015_);
return v___x_1084_;
}
}
else
{
lean_object* v_a_1085_; lean_object* v___x_1087_; uint8_t v_isShared_1088_; uint8_t v_isSharedCheck_1092_; 
lean_dec(v_a_1080_);
lean_dec_ref(v___x_1039_);
lean_dec_ref(v_arg_1038_);
lean_dec_ref(v_arg_1035_);
lean_dec_ref(v_e_1015_);
v_a_1085_ = lean_ctor_get(v___x_1081_, 0);
v_isSharedCheck_1092_ = !lean_is_exclusive(v___x_1081_);
if (v_isSharedCheck_1092_ == 0)
{
v___x_1087_ = v___x_1081_;
v_isShared_1088_ = v_isSharedCheck_1092_;
goto v_resetjp_1086_;
}
else
{
lean_inc(v_a_1085_);
lean_dec(v___x_1081_);
v___x_1087_ = lean_box(0);
v_isShared_1088_ = v_isSharedCheck_1092_;
goto v_resetjp_1086_;
}
v_resetjp_1086_:
{
lean_object* v___x_1090_; 
if (v_isShared_1088_ == 0)
{
v___x_1090_ = v___x_1087_;
goto v_reusejp_1089_;
}
else
{
lean_object* v_reuseFailAlloc_1091_; 
v_reuseFailAlloc_1091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1091_, 0, v_a_1085_);
v___x_1090_ = v_reuseFailAlloc_1091_;
goto v_reusejp_1089_;
}
v_reusejp_1089_:
{
return v___x_1090_;
}
}
}
}
else
{
lean_object* v_a_1093_; lean_object* v___x_1095_; uint8_t v_isShared_1096_; uint8_t v_isSharedCheck_1100_; 
lean_dec_ref(v___x_1039_);
lean_dec_ref(v_arg_1038_);
lean_dec_ref(v_arg_1035_);
lean_dec_ref(v_e_1015_);
v_a_1093_ = lean_ctor_get(v___x_1079_, 0);
v_isSharedCheck_1100_ = !lean_is_exclusive(v___x_1079_);
if (v_isSharedCheck_1100_ == 0)
{
v___x_1095_ = v___x_1079_;
v_isShared_1096_ = v_isSharedCheck_1100_;
goto v_resetjp_1094_;
}
else
{
lean_inc(v_a_1093_);
lean_dec(v___x_1079_);
v___x_1095_ = lean_box(0);
v_isShared_1096_ = v_isSharedCheck_1100_;
goto v_resetjp_1094_;
}
v_resetjp_1094_:
{
lean_object* v___x_1098_; 
if (v_isShared_1096_ == 0)
{
v___x_1098_ = v___x_1095_;
goto v_reusejp_1097_;
}
else
{
lean_object* v_reuseFailAlloc_1099_; 
v_reuseFailAlloc_1099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1099_, 0, v_a_1093_);
v___x_1098_ = v_reuseFailAlloc_1099_;
goto v_reusejp_1097_;
}
v_reusejp_1097_:
{
return v___x_1098_;
}
}
}
}
else
{
lean_dec_ref(v___x_1077_);
v_f_1041_ = v_arg_1032_;
v___y_1042_ = v_a_1016_;
v___y_1043_ = v_a_1017_;
v___y_1044_ = v_a_1018_;
v___y_1045_ = v_a_1019_;
v___y_1046_ = v_a_1020_;
v___y_1047_ = v_a_1021_;
v___y_1048_ = v_a_1022_;
v___y_1049_ = v_a_1023_;
v___y_1050_ = v_a_1024_;
v___y_1051_ = v_a_1025_;
goto v___jp_1040_;
}
}
}
}
else
{
lean_object* v_a_1102_; lean_object* v___x_1104_; uint8_t v_isShared_1105_; uint8_t v_isSharedCheck_1109_; 
lean_dec_ref(v___x_1039_);
lean_dec_ref(v_arg_1038_);
lean_dec_ref(v_arg_1035_);
lean_dec_ref(v_arg_1032_);
lean_dec_ref(v_e_1015_);
v_a_1102_ = lean_ctor_get(v___x_1067_, 0);
v_isSharedCheck_1109_ = !lean_is_exclusive(v___x_1067_);
if (v_isSharedCheck_1109_ == 0)
{
v___x_1104_ = v___x_1067_;
v_isShared_1105_ = v_isSharedCheck_1109_;
goto v_resetjp_1103_;
}
else
{
lean_inc(v_a_1102_);
lean_dec(v___x_1067_);
v___x_1104_ = lean_box(0);
v_isShared_1105_ = v_isSharedCheck_1109_;
goto v_resetjp_1103_;
}
v_resetjp_1103_:
{
lean_object* v___x_1107_; 
if (v_isShared_1105_ == 0)
{
v___x_1107_ = v___x_1104_;
goto v_reusejp_1106_;
}
else
{
lean_object* v_reuseFailAlloc_1108_; 
v_reuseFailAlloc_1108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1108_, 0, v_a_1102_);
v___x_1107_ = v_reuseFailAlloc_1108_;
goto v_reusejp_1106_;
}
v_reusejp_1106_:
{
return v___x_1107_;
}
}
}
}
v___jp_1040_:
{
lean_object* v___x_1052_; 
lean_inc_ref(v_e_1015_);
v___x_1052_ = l_Lean_Meta_Grind_mkEqTrueProof(v_e_1015_, v___y_1042_, v___y_1043_, v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_);
if (lean_obj_tag(v___x_1052_) == 0)
{
lean_object* v_a_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; 
v_a_1053_ = lean_ctor_get(v___x_1052_, 0);
lean_inc(v_a_1053_);
lean_dec_ref(v___x_1052_);
v___x_1054_ = l_Lean_Expr_constLevels_x21(v___x_1039_);
lean_dec_ref(v___x_1039_);
v___x_1055_ = l_Lean_Meta_mkOfEqTrueCore(v_e_1015_, v_a_1053_);
v___x_1056_ = l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn(v___x_1054_, v_arg_1038_, v_arg_1035_, v_f_1041_, v___x_1055_, v___y_1042_, v___y_1043_, v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_);
return v___x_1056_;
}
else
{
lean_object* v_a_1057_; lean_object* v___x_1059_; uint8_t v_isShared_1060_; uint8_t v_isSharedCheck_1064_; 
lean_dec_ref(v_f_1041_);
lean_dec_ref(v___x_1039_);
lean_dec_ref(v_arg_1038_);
lean_dec_ref(v_arg_1035_);
lean_dec_ref(v_e_1015_);
v_a_1057_ = lean_ctor_get(v___x_1052_, 0);
v_isSharedCheck_1064_ = !lean_is_exclusive(v___x_1052_);
if (v_isSharedCheck_1064_ == 0)
{
v___x_1059_ = v___x_1052_;
v_isShared_1060_ = v_isSharedCheck_1064_;
goto v_resetjp_1058_;
}
else
{
lean_inc(v_a_1057_);
lean_dec(v___x_1052_);
v___x_1059_ = lean_box(0);
v_isShared_1060_ = v_isSharedCheck_1064_;
goto v_resetjp_1058_;
}
v_resetjp_1058_:
{
lean_object* v___x_1062_; 
if (v_isShared_1060_ == 0)
{
v___x_1062_ = v___x_1059_;
goto v_reusejp_1061_;
}
else
{
lean_object* v_reuseFailAlloc_1063_; 
v_reuseFailAlloc_1063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1063_, 0, v_a_1057_);
v___x_1062_ = v_reuseFailAlloc_1063_;
goto v_reusejp_1061_;
}
v_reusejp_1061_:
{
return v___x_1062_;
}
}
}
}
}
}
}
v___jp_1027_:
{
lean_object* v___x_1028_; lean_object* v___x_1029_; 
v___x_1028_ = lean_box(0);
v___x_1029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1029_, 0, v___x_1028_);
return v___x_1029_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj___boxed(lean_object* v_e_1110_, lean_object* v_a_1111_, lean_object* v_a_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_, lean_object* v_a_1117_, lean_object* v_a_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_, lean_object* v_a_1121_){
_start:
{
lean_object* v_res_1122_; 
v_res_1122_ = l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj(v_e_1110_, v_a_1111_, v_a_1112_, v_a_1113_, v_a_1114_, v_a_1115_, v_a_1116_, v_a_1117_, v_a_1118_, v_a_1119_, v_a_1120_);
lean_dec(v_a_1120_);
lean_dec_ref(v_a_1119_);
lean_dec(v_a_1118_);
lean_dec_ref(v_a_1117_);
lean_dec(v_a_1116_);
lean_dec_ref(v_a_1115_);
lean_dec(v_a_1114_);
lean_dec_ref(v_a_1113_);
lean_dec(v_a_1112_);
lean_dec(v_a_1111_);
return v_res_1122_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj___regBuiltin___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj_declare__1_00___x40_Lean_Meta_Tactic_Grind_PropagateInj_3930705876____hygCtx___hyg_8_(){
_start:
{
lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; 
v___x_1124_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj___closed__2));
v___x_1125_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj___boxed), 12, 0);
v___x_1126_ = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(v___x_1124_, v___x_1125_);
return v___x_1126_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj___regBuiltin___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj_declare__1_00___x40_Lean_Meta_Tactic_Grind_PropagateInj_3930705876____hygCtx___hyg_8____boxed(lean_object* v_a_1127_){
_start:
{
lean_object* v_res_1128_; 
v_res_1128_ = l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj___regBuiltin___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj_declare__1_00___x40_Lean_Meta_Tactic_Grind_PropagateInj_3930705876____hygCtx___hyg_8_();
return v_res_1128_;
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
