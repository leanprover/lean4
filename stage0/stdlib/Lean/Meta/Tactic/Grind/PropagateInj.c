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
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
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
uint64_t lean_usize_to_uint64(size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
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
lean_object* v___x_14_; lean_object* v___x_9068__overap_15_; lean_object* v___x_16_; 
v___x_14_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__0___closed__0, &l_panic___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__0___closed__0);
v___x_9068__overap_15_ = lean_panic_fn_borrowed(v___x_14_, v_msg_2_);
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
v___x_16_ = lean_apply_11(v___x_9068__overap_15_, v___y_3_, v___y_4_, v___y_5_, v___y_6_, v___y_7_, v___y_8_, v___y_9_, v___y_10_, v___y_11_, v___y_12_, lean_box(0));
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
lean_object* v_k_x27_37_; size_t v___x_38_; size_t v___x_39_; uint8_t v___x_40_; 
v_k_x27_37_ = lean_array_fget_borrowed(v_keys_30_, v_i_32_);
v___x_38_ = lean_ptr_addr(v_k_33_);
v___x_39_ = lean_ptr_addr(v_k_x27_37_);
v___x_40_ = lean_usize_dec_eq(v___x_38_, v___x_39_);
if (v___x_40_ == 0)
{
lean_object* v___x_41_; lean_object* v___x_42_; 
v___x_41_ = lean_unsigned_to_nat(1u);
v___x_42_ = lean_nat_add(v_i_32_, v___x_41_);
lean_dec(v_i_32_);
v_i_32_ = v___x_42_;
goto _start;
}
else
{
lean_object* v___x_44_; lean_object* v___x_45_; 
v___x_44_ = lean_array_fget_borrowed(v_vals_31_, v_i_32_);
lean_dec(v_i_32_);
lean_inc(v___x_44_);
v___x_45_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_45_, 0, v___x_44_);
return v___x_45_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_keys_46_, lean_object* v_vals_47_, lean_object* v_i_48_, lean_object* v_k_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1_spec__2___redArg(v_keys_46_, v_vals_47_, v_i_48_, v_k_49_);
lean_dec_ref(v_k_49_);
lean_dec_ref(v_vals_47_);
lean_dec_ref(v_keys_46_);
return v_res_50_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1___redArg(lean_object* v_x_51_, size_t v_x_52_, lean_object* v_x_53_){
_start:
{
if (lean_obj_tag(v_x_51_) == 0)
{
lean_object* v_es_54_; lean_object* v___x_55_; size_t v___x_56_; size_t v___x_57_; lean_object* v_j_58_; lean_object* v___x_59_; 
v_es_54_ = lean_ctor_get(v_x_51_, 0);
v___x_55_ = lean_box(2);
v___x_56_ = ((size_t)31ULL);
v___x_57_ = lean_usize_land(v_x_52_, v___x_56_);
v_j_58_ = lean_usize_to_nat(v___x_57_);
v___x_59_ = lean_array_get_borrowed(v___x_55_, v_es_54_, v_j_58_);
lean_dec(v_j_58_);
switch(lean_obj_tag(v___x_59_))
{
case 0:
{
lean_object* v_key_60_; lean_object* v_val_61_; size_t v___x_62_; size_t v___x_63_; uint8_t v___x_64_; 
v_key_60_ = lean_ctor_get(v___x_59_, 0);
v_val_61_ = lean_ctor_get(v___x_59_, 1);
v___x_62_ = lean_ptr_addr(v_x_53_);
v___x_63_ = lean_ptr_addr(v_key_60_);
v___x_64_ = lean_usize_dec_eq(v___x_62_, v___x_63_);
if (v___x_64_ == 0)
{
lean_object* v___x_65_; 
v___x_65_ = lean_box(0);
return v___x_65_;
}
else
{
lean_object* v___x_66_; 
lean_inc(v_val_61_);
v___x_66_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_66_, 0, v_val_61_);
return v___x_66_;
}
}
case 1:
{
lean_object* v_node_67_; size_t v___x_68_; size_t v___x_69_; 
v_node_67_ = lean_ctor_get(v___x_59_, 0);
v___x_68_ = ((size_t)5ULL);
v___x_69_ = lean_usize_shift_right(v_x_52_, v___x_68_);
v_x_51_ = v_node_67_;
v_x_52_ = v___x_69_;
goto _start;
}
default: 
{
lean_object* v___x_71_; 
v___x_71_ = lean_box(0);
return v___x_71_;
}
}
}
else
{
lean_object* v_ks_72_; lean_object* v_vs_73_; lean_object* v___x_74_; lean_object* v___x_75_; 
v_ks_72_ = lean_ctor_get(v_x_51_, 0);
v_vs_73_ = lean_ctor_get(v_x_51_, 1);
v___x_74_ = lean_unsigned_to_nat(0u);
v___x_75_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1_spec__2___redArg(v_ks_72_, v_vs_73_, v___x_74_, v_x_53_);
return v___x_75_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1___redArg___boxed(lean_object* v_x_76_, lean_object* v_x_77_, lean_object* v_x_78_){
_start:
{
size_t v_x_9582__boxed_79_; lean_object* v_res_80_; 
v_x_9582__boxed_79_ = lean_unbox_usize(v_x_77_);
lean_dec(v_x_77_);
v_res_80_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1___redArg(v_x_76_, v_x_9582__boxed_79_, v_x_78_);
lean_dec_ref(v_x_78_);
lean_dec_ref(v_x_76_);
return v_res_80_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1___redArg(lean_object* v_x_81_, lean_object* v_x_82_){
_start:
{
size_t v___x_83_; size_t v___x_84_; size_t v___x_85_; uint64_t v___x_86_; size_t v___x_87_; lean_object* v___x_88_; 
v___x_83_ = lean_ptr_addr(v_x_82_);
v___x_84_ = ((size_t)3ULL);
v___x_85_ = lean_usize_shift_right(v___x_83_, v___x_84_);
v___x_86_ = lean_usize_to_uint64(v___x_85_);
v___x_87_ = lean_uint64_to_usize(v___x_86_);
v___x_88_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1___redArg(v_x_81_, v___x_87_, v_x_82_);
return v___x_88_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1___redArg___boxed(lean_object* v_x_89_, lean_object* v_x_90_){
_start:
{
lean_object* v_res_91_; 
v_res_91_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1___redArg(v_x_89_, v_x_90_);
lean_dec_ref(v_x_90_);
lean_dec_ref(v_x_89_);
return v_res_91_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3_spec__5_spec__6___redArg(lean_object* v_x_92_, lean_object* v_x_93_, lean_object* v_x_94_, lean_object* v_x_95_){
_start:
{
lean_object* v_ks_96_; lean_object* v_vs_97_; lean_object* v___x_99_; uint8_t v_isShared_100_; uint8_t v_isSharedCheck_123_; 
v_ks_96_ = lean_ctor_get(v_x_92_, 0);
v_vs_97_ = lean_ctor_get(v_x_92_, 1);
v_isSharedCheck_123_ = !lean_is_exclusive(v_x_92_);
if (v_isSharedCheck_123_ == 0)
{
v___x_99_ = v_x_92_;
v_isShared_100_ = v_isSharedCheck_123_;
goto v_resetjp_98_;
}
else
{
lean_inc(v_vs_97_);
lean_inc(v_ks_96_);
lean_dec(v_x_92_);
v___x_99_ = lean_box(0);
v_isShared_100_ = v_isSharedCheck_123_;
goto v_resetjp_98_;
}
v_resetjp_98_:
{
lean_object* v___x_101_; uint8_t v___x_102_; 
v___x_101_ = lean_array_get_size(v_ks_96_);
v___x_102_ = lean_nat_dec_lt(v_x_93_, v___x_101_);
if (v___x_102_ == 0)
{
lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_106_; 
lean_dec(v_x_93_);
v___x_103_ = lean_array_push(v_ks_96_, v_x_94_);
v___x_104_ = lean_array_push(v_vs_97_, v_x_95_);
if (v_isShared_100_ == 0)
{
lean_ctor_set(v___x_99_, 1, v___x_104_);
lean_ctor_set(v___x_99_, 0, v___x_103_);
v___x_106_ = v___x_99_;
goto v_reusejp_105_;
}
else
{
lean_object* v_reuseFailAlloc_107_; 
v_reuseFailAlloc_107_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_107_, 0, v___x_103_);
lean_ctor_set(v_reuseFailAlloc_107_, 1, v___x_104_);
v___x_106_ = v_reuseFailAlloc_107_;
goto v_reusejp_105_;
}
v_reusejp_105_:
{
return v___x_106_;
}
}
else
{
lean_object* v_k_x27_108_; size_t v___x_109_; size_t v___x_110_; uint8_t v___x_111_; 
v_k_x27_108_ = lean_array_fget_borrowed(v_ks_96_, v_x_93_);
v___x_109_ = lean_ptr_addr(v_x_94_);
v___x_110_ = lean_ptr_addr(v_k_x27_108_);
v___x_111_ = lean_usize_dec_eq(v___x_109_, v___x_110_);
if (v___x_111_ == 0)
{
lean_object* v___x_113_; 
if (v_isShared_100_ == 0)
{
v___x_113_ = v___x_99_;
goto v_reusejp_112_;
}
else
{
lean_object* v_reuseFailAlloc_117_; 
v_reuseFailAlloc_117_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_117_, 0, v_ks_96_);
lean_ctor_set(v_reuseFailAlloc_117_, 1, v_vs_97_);
v___x_113_ = v_reuseFailAlloc_117_;
goto v_reusejp_112_;
}
v_reusejp_112_:
{
lean_object* v___x_114_; lean_object* v___x_115_; 
v___x_114_ = lean_unsigned_to_nat(1u);
v___x_115_ = lean_nat_add(v_x_93_, v___x_114_);
lean_dec(v_x_93_);
v_x_92_ = v___x_113_;
v_x_93_ = v___x_115_;
goto _start;
}
}
else
{
lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_121_; 
v___x_118_ = lean_array_fset(v_ks_96_, v_x_93_, v_x_94_);
v___x_119_ = lean_array_fset(v_vs_97_, v_x_93_, v_x_95_);
lean_dec(v_x_93_);
if (v_isShared_100_ == 0)
{
lean_ctor_set(v___x_99_, 1, v___x_119_);
lean_ctor_set(v___x_99_, 0, v___x_118_);
v___x_121_ = v___x_99_;
goto v_reusejp_120_;
}
else
{
lean_object* v_reuseFailAlloc_122_; 
v_reuseFailAlloc_122_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_122_, 0, v___x_118_);
lean_ctor_set(v_reuseFailAlloc_122_, 1, v___x_119_);
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
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3_spec__5___redArg(lean_object* v_n_124_, lean_object* v_k_125_, lean_object* v_v_126_){
_start:
{
lean_object* v___x_127_; lean_object* v___x_128_; 
v___x_127_ = lean_unsigned_to_nat(0u);
v___x_128_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3_spec__5_spec__6___redArg(v_n_124_, v___x_127_, v_k_125_, v_v_126_);
return v___x_128_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_129_; 
v___x_129_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_129_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3___redArg(lean_object* v_x_130_, size_t v_x_131_, size_t v_x_132_, lean_object* v_x_133_, lean_object* v_x_134_){
_start:
{
if (lean_obj_tag(v_x_130_) == 0)
{
lean_object* v_es_135_; size_t v___x_136_; size_t v___x_137_; lean_object* v_j_138_; lean_object* v___x_139_; uint8_t v___x_140_; 
v_es_135_ = lean_ctor_get(v_x_130_, 0);
v___x_136_ = ((size_t)31ULL);
v___x_137_ = lean_usize_land(v_x_131_, v___x_136_);
v_j_138_ = lean_usize_to_nat(v___x_137_);
v___x_139_ = lean_array_get_size(v_es_135_);
v___x_140_ = lean_nat_dec_lt(v_j_138_, v___x_139_);
if (v___x_140_ == 0)
{
lean_dec(v_j_138_);
lean_dec(v_x_134_);
lean_dec_ref(v_x_133_);
return v_x_130_;
}
else
{
lean_object* v___x_142_; uint8_t v_isShared_143_; uint8_t v_isSharedCheck_181_; 
lean_inc_ref(v_es_135_);
v_isSharedCheck_181_ = !lean_is_exclusive(v_x_130_);
if (v_isSharedCheck_181_ == 0)
{
lean_object* v_unused_182_; 
v_unused_182_ = lean_ctor_get(v_x_130_, 0);
lean_dec(v_unused_182_);
v___x_142_ = v_x_130_;
v_isShared_143_ = v_isSharedCheck_181_;
goto v_resetjp_141_;
}
else
{
lean_dec(v_x_130_);
v___x_142_ = lean_box(0);
v_isShared_143_ = v_isSharedCheck_181_;
goto v_resetjp_141_;
}
v_resetjp_141_:
{
lean_object* v_v_144_; lean_object* v___x_145_; lean_object* v_xs_x27_146_; lean_object* v___y_148_; 
v_v_144_ = lean_array_fget(v_es_135_, v_j_138_);
v___x_145_ = lean_box(0);
v_xs_x27_146_ = lean_array_fset(v_es_135_, v_j_138_, v___x_145_);
switch(lean_obj_tag(v_v_144_))
{
case 0:
{
lean_object* v_key_153_; lean_object* v_val_154_; lean_object* v___x_156_; uint8_t v_isShared_157_; uint8_t v_isSharedCheck_166_; 
v_key_153_ = lean_ctor_get(v_v_144_, 0);
v_val_154_ = lean_ctor_get(v_v_144_, 1);
v_isSharedCheck_166_ = !lean_is_exclusive(v_v_144_);
if (v_isSharedCheck_166_ == 0)
{
v___x_156_ = v_v_144_;
v_isShared_157_ = v_isSharedCheck_166_;
goto v_resetjp_155_;
}
else
{
lean_inc(v_val_154_);
lean_inc(v_key_153_);
lean_dec(v_v_144_);
v___x_156_ = lean_box(0);
v_isShared_157_ = v_isSharedCheck_166_;
goto v_resetjp_155_;
}
v_resetjp_155_:
{
size_t v___x_158_; size_t v___x_159_; uint8_t v___x_160_; 
v___x_158_ = lean_ptr_addr(v_x_133_);
v___x_159_ = lean_ptr_addr(v_key_153_);
v___x_160_ = lean_usize_dec_eq(v___x_158_, v___x_159_);
if (v___x_160_ == 0)
{
lean_object* v___x_161_; lean_object* v___x_162_; 
lean_del_object(v___x_156_);
v___x_161_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_153_, v_val_154_, v_x_133_, v_x_134_);
v___x_162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_162_, 0, v___x_161_);
v___y_148_ = v___x_162_;
goto v___jp_147_;
}
else
{
lean_object* v___x_164_; 
lean_dec(v_val_154_);
lean_dec(v_key_153_);
if (v_isShared_157_ == 0)
{
lean_ctor_set(v___x_156_, 1, v_x_134_);
lean_ctor_set(v___x_156_, 0, v_x_133_);
v___x_164_ = v___x_156_;
goto v_reusejp_163_;
}
else
{
lean_object* v_reuseFailAlloc_165_; 
v_reuseFailAlloc_165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_165_, 0, v_x_133_);
lean_ctor_set(v_reuseFailAlloc_165_, 1, v_x_134_);
v___x_164_ = v_reuseFailAlloc_165_;
goto v_reusejp_163_;
}
v_reusejp_163_:
{
v___y_148_ = v___x_164_;
goto v___jp_147_;
}
}
}
}
case 1:
{
lean_object* v_node_167_; lean_object* v___x_169_; uint8_t v_isShared_170_; uint8_t v_isSharedCheck_179_; 
v_node_167_ = lean_ctor_get(v_v_144_, 0);
v_isSharedCheck_179_ = !lean_is_exclusive(v_v_144_);
if (v_isSharedCheck_179_ == 0)
{
v___x_169_ = v_v_144_;
v_isShared_170_ = v_isSharedCheck_179_;
goto v_resetjp_168_;
}
else
{
lean_inc(v_node_167_);
lean_dec(v_v_144_);
v___x_169_ = lean_box(0);
v_isShared_170_ = v_isSharedCheck_179_;
goto v_resetjp_168_;
}
v_resetjp_168_:
{
size_t v___x_171_; size_t v___x_172_; size_t v___x_173_; size_t v___x_174_; lean_object* v___x_175_; lean_object* v___x_177_; 
v___x_171_ = ((size_t)5ULL);
v___x_172_ = lean_usize_shift_right(v_x_131_, v___x_171_);
v___x_173_ = ((size_t)1ULL);
v___x_174_ = lean_usize_add(v_x_132_, v___x_173_);
v___x_175_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3___redArg(v_node_167_, v___x_172_, v___x_174_, v_x_133_, v_x_134_);
if (v_isShared_170_ == 0)
{
lean_ctor_set(v___x_169_, 0, v___x_175_);
v___x_177_ = v___x_169_;
goto v_reusejp_176_;
}
else
{
lean_object* v_reuseFailAlloc_178_; 
v_reuseFailAlloc_178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_178_, 0, v___x_175_);
v___x_177_ = v_reuseFailAlloc_178_;
goto v_reusejp_176_;
}
v_reusejp_176_:
{
v___y_148_ = v___x_177_;
goto v___jp_147_;
}
}
}
default: 
{
lean_object* v___x_180_; 
v___x_180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_180_, 0, v_x_133_);
lean_ctor_set(v___x_180_, 1, v_x_134_);
v___y_148_ = v___x_180_;
goto v___jp_147_;
}
}
v___jp_147_:
{
lean_object* v___x_149_; lean_object* v___x_151_; 
v___x_149_ = lean_array_fset(v_xs_x27_146_, v_j_138_, v___y_148_);
lean_dec(v_j_138_);
if (v_isShared_143_ == 0)
{
lean_ctor_set(v___x_142_, 0, v___x_149_);
v___x_151_ = v___x_142_;
goto v_reusejp_150_;
}
else
{
lean_object* v_reuseFailAlloc_152_; 
v_reuseFailAlloc_152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_152_, 0, v___x_149_);
v___x_151_ = v_reuseFailAlloc_152_;
goto v_reusejp_150_;
}
v_reusejp_150_:
{
return v___x_151_;
}
}
}
}
}
else
{
lean_object* v_ks_183_; lean_object* v_vs_184_; lean_object* v___x_186_; uint8_t v_isShared_187_; uint8_t v_isSharedCheck_204_; 
v_ks_183_ = lean_ctor_get(v_x_130_, 0);
v_vs_184_ = lean_ctor_get(v_x_130_, 1);
v_isSharedCheck_204_ = !lean_is_exclusive(v_x_130_);
if (v_isSharedCheck_204_ == 0)
{
v___x_186_ = v_x_130_;
v_isShared_187_ = v_isSharedCheck_204_;
goto v_resetjp_185_;
}
else
{
lean_inc(v_vs_184_);
lean_inc(v_ks_183_);
lean_dec(v_x_130_);
v___x_186_ = lean_box(0);
v_isShared_187_ = v_isSharedCheck_204_;
goto v_resetjp_185_;
}
v_resetjp_185_:
{
lean_object* v___x_189_; 
if (v_isShared_187_ == 0)
{
v___x_189_ = v___x_186_;
goto v_reusejp_188_;
}
else
{
lean_object* v_reuseFailAlloc_203_; 
v_reuseFailAlloc_203_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_203_, 0, v_ks_183_);
lean_ctor_set(v_reuseFailAlloc_203_, 1, v_vs_184_);
v___x_189_ = v_reuseFailAlloc_203_;
goto v_reusejp_188_;
}
v_reusejp_188_:
{
lean_object* v_newNode_190_; uint8_t v___y_192_; size_t v___x_198_; uint8_t v___x_199_; 
v_newNode_190_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3_spec__5___redArg(v___x_189_, v_x_133_, v_x_134_);
v___x_198_ = ((size_t)7ULL);
v___x_199_ = lean_usize_dec_le(v___x_198_, v_x_132_);
if (v___x_199_ == 0)
{
lean_object* v___x_200_; lean_object* v___x_201_; uint8_t v___x_202_; 
v___x_200_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_190_);
v___x_201_ = lean_unsigned_to_nat(4u);
v___x_202_ = lean_nat_dec_lt(v___x_200_, v___x_201_);
lean_dec(v___x_200_);
v___y_192_ = v___x_202_;
goto v___jp_191_;
}
else
{
v___y_192_ = v___x_199_;
goto v___jp_191_;
}
v___jp_191_:
{
if (v___y_192_ == 0)
{
lean_object* v_ks_193_; lean_object* v_vs_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; 
v_ks_193_ = lean_ctor_get(v_newNode_190_, 0);
lean_inc_ref(v_ks_193_);
v_vs_194_ = lean_ctor_get(v_newNode_190_, 1);
lean_inc_ref(v_vs_194_);
lean_dec_ref(v_newNode_190_);
v___x_195_ = lean_unsigned_to_nat(0u);
v___x_196_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3___redArg___closed__0);
v___x_197_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3_spec__6___redArg(v_x_132_, v_ks_193_, v_vs_194_, v___x_195_, v___x_196_);
lean_dec_ref(v_vs_194_);
lean_dec_ref(v_ks_193_);
return v___x_197_;
}
else
{
return v_newNode_190_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3_spec__6___redArg(size_t v_depth_205_, lean_object* v_keys_206_, lean_object* v_vals_207_, lean_object* v_i_208_, lean_object* v_entries_209_){
_start:
{
lean_object* v___x_210_; uint8_t v___x_211_; 
v___x_210_ = lean_array_get_size(v_keys_206_);
v___x_211_ = lean_nat_dec_lt(v_i_208_, v___x_210_);
if (v___x_211_ == 0)
{
lean_dec(v_i_208_);
return v_entries_209_;
}
else
{
lean_object* v_k_212_; lean_object* v_v_213_; size_t v___x_214_; size_t v___x_215_; size_t v___x_216_; uint64_t v___x_217_; size_t v_h_218_; size_t v___x_219_; lean_object* v___x_220_; size_t v___x_221_; size_t v___x_222_; size_t v___x_223_; size_t v_h_224_; lean_object* v___x_225_; lean_object* v___x_226_; 
v_k_212_ = lean_array_fget_borrowed(v_keys_206_, v_i_208_);
v_v_213_ = lean_array_fget_borrowed(v_vals_207_, v_i_208_);
v___x_214_ = lean_ptr_addr(v_k_212_);
v___x_215_ = ((size_t)3ULL);
v___x_216_ = lean_usize_shift_right(v___x_214_, v___x_215_);
v___x_217_ = lean_usize_to_uint64(v___x_216_);
v_h_218_ = lean_uint64_to_usize(v___x_217_);
v___x_219_ = ((size_t)5ULL);
v___x_220_ = lean_unsigned_to_nat(1u);
v___x_221_ = ((size_t)1ULL);
v___x_222_ = lean_usize_sub(v_depth_205_, v___x_221_);
v___x_223_ = lean_usize_mul(v___x_219_, v___x_222_);
v_h_224_ = lean_usize_shift_right(v_h_218_, v___x_223_);
v___x_225_ = lean_nat_add(v_i_208_, v___x_220_);
lean_dec(v_i_208_);
lean_inc(v_v_213_);
lean_inc(v_k_212_);
v___x_226_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3___redArg(v_entries_209_, v_h_224_, v_depth_205_, v_k_212_, v_v_213_);
v_i_208_ = v___x_225_;
v_entries_209_ = v___x_226_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3_spec__6___redArg___boxed(lean_object* v_depth_228_, lean_object* v_keys_229_, lean_object* v_vals_230_, lean_object* v_i_231_, lean_object* v_entries_232_){
_start:
{
size_t v_depth_boxed_233_; lean_object* v_res_234_; 
v_depth_boxed_233_ = lean_unbox_usize(v_depth_228_);
lean_dec(v_depth_228_);
v_res_234_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3_spec__6___redArg(v_depth_boxed_233_, v_keys_229_, v_vals_230_, v_i_231_, v_entries_232_);
lean_dec_ref(v_vals_230_);
lean_dec_ref(v_keys_229_);
return v_res_234_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3___redArg___boxed(lean_object* v_x_235_, lean_object* v_x_236_, lean_object* v_x_237_, lean_object* v_x_238_, lean_object* v_x_239_){
_start:
{
size_t v_x_9734__boxed_240_; size_t v_x_9735__boxed_241_; lean_object* v_res_242_; 
v_x_9734__boxed_240_ = lean_unbox_usize(v_x_236_);
lean_dec(v_x_236_);
v_x_9735__boxed_241_ = lean_unbox_usize(v_x_237_);
lean_dec(v_x_237_);
v_res_242_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3___redArg(v_x_235_, v_x_9734__boxed_240_, v_x_9735__boxed_241_, v_x_238_, v_x_239_);
return v_res_242_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2___redArg(lean_object* v_x_243_, lean_object* v_x_244_, lean_object* v_x_245_){
_start:
{
size_t v___x_246_; size_t v___x_247_; size_t v___x_248_; uint64_t v___x_249_; size_t v___x_250_; size_t v___x_251_; lean_object* v___x_252_; 
v___x_246_ = lean_ptr_addr(v_x_244_);
v___x_247_ = ((size_t)3ULL);
v___x_248_ = lean_usize_shift_right(v___x_246_, v___x_247_);
v___x_249_ = lean_usize_to_uint64(v___x_248_);
v___x_250_ = lean_uint64_to_usize(v___x_249_);
v___x_251_ = ((size_t)1ULL);
v___x_252_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3___redArg(v_x_243_, v___x_250_, v___x_251_, v_x_244_, v_x_245_);
return v___x_252_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__3(void){
_start:
{
lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; 
v___x_256_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__2));
v___x_257_ = lean_unsigned_to_nat(26u);
v___x_258_ = lean_unsigned_to_nat(19u);
v___x_259_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__1));
v___x_260_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__0));
v___x_261_ = l_mkPanicMessageWithDecl(v___x_260_, v___x_259_, v___x_258_, v___x_257_, v___x_256_);
return v___x_261_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__11(void){
_start:
{
lean_object* v___x_274_; lean_object* v_dummy_275_; 
v___x_274_ = lean_box(0);
v_dummy_275_ = l_Lean_Expr_sort___override(v___x_274_);
return v_dummy_275_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f(lean_object* v_f_281_, lean_object* v_a_282_, lean_object* v_a_283_, lean_object* v_a_284_, lean_object* v_a_285_, lean_object* v_a_286_, lean_object* v_a_287_, lean_object* v_a_288_, lean_object* v_a_289_, lean_object* v_a_290_, lean_object* v_a_291_, lean_object* v_a_292_){
_start:
{
lean_object* v___y_295_; lean_object* v___y_296_; lean_object* v___y_297_; lean_object* v___y_298_; lean_object* v___y_299_; lean_object* v___y_300_; lean_object* v___y_301_; lean_object* v___y_302_; lean_object* v___y_303_; lean_object* v___y_304_; lean_object* v___x_307_; lean_object* v_toGoalState_308_; lean_object* v_inj_309_; lean_object* v_fns_310_; lean_object* v___x_312_; uint8_t v_isShared_313_; uint8_t v_isSharedCheck_434_; 
v___x_307_ = lean_st_ref_get(v_a_283_);
v_toGoalState_308_ = lean_ctor_get(v___x_307_, 0);
lean_inc_ref(v_toGoalState_308_);
lean_dec(v___x_307_);
v_inj_309_ = lean_ctor_get(v_toGoalState_308_, 13);
lean_inc_ref(v_inj_309_);
lean_dec_ref(v_toGoalState_308_);
v_fns_310_ = lean_ctor_get(v_inj_309_, 1);
v_isSharedCheck_434_ = !lean_is_exclusive(v_inj_309_);
if (v_isSharedCheck_434_ == 0)
{
lean_object* v_unused_435_; 
v_unused_435_ = lean_ctor_get(v_inj_309_, 0);
lean_dec(v_unused_435_);
v___x_312_ = v_inj_309_;
v_isShared_313_ = v_isSharedCheck_434_;
goto v_resetjp_311_;
}
else
{
lean_inc(v_fns_310_);
lean_dec(v_inj_309_);
v___x_312_ = lean_box(0);
v_isShared_313_ = v_isSharedCheck_434_;
goto v_resetjp_311_;
}
v___jp_294_:
{
lean_object* v___x_305_; lean_object* v___x_306_; 
v___x_305_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__3, &l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__3);
v___x_306_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__0(v___x_305_, v___y_295_, v___y_296_, v___y_297_, v___y_298_, v___y_299_, v___y_300_, v___y_301_, v___y_302_, v___y_303_, v___y_304_);
return v___x_306_;
}
v_resetjp_311_:
{
lean_object* v___x_314_; 
v___x_314_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1___redArg(v_fns_310_, v_f_281_);
lean_dec_ref(v_fns_310_);
if (lean_obj_tag(v___x_314_) == 1)
{
lean_object* v_val_315_; lean_object* v___x_317_; uint8_t v_isShared_318_; uint8_t v_isSharedCheck_431_; 
v_val_315_ = lean_ctor_get(v___x_314_, 0);
v_isSharedCheck_431_ = !lean_is_exclusive(v___x_314_);
if (v_isSharedCheck_431_ == 0)
{
v___x_317_ = v___x_314_;
v_isShared_318_ = v_isSharedCheck_431_;
goto v_resetjp_316_;
}
else
{
lean_inc(v_val_315_);
lean_dec(v___x_314_);
v___x_317_ = lean_box(0);
v_isShared_318_ = v_isSharedCheck_431_;
goto v_resetjp_316_;
}
v_resetjp_316_:
{
lean_object* v_inv_x3f_319_; 
v_inv_x3f_319_ = lean_ctor_get(v_val_315_, 4);
if (lean_obj_tag(v_inv_x3f_319_) == 1)
{
lean_object* v___x_320_; 
lean_inc_ref(v_inv_x3f_319_);
lean_del_object(v___x_317_);
lean_dec(v_val_315_);
lean_del_object(v___x_312_);
lean_dec_ref(v_a_282_);
lean_dec_ref(v_f_281_);
v___x_320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_320_, 0, v_inv_x3f_319_);
return v___x_320_;
}
else
{
lean_object* v_us_321_; 
v_us_321_ = lean_ctor_get(v_val_315_, 0);
lean_inc(v_us_321_);
if (lean_obj_tag(v_us_321_) == 1)
{
lean_object* v_tail_322_; 
v_tail_322_ = lean_ctor_get(v_us_321_, 1);
lean_inc(v_tail_322_);
if (lean_obj_tag(v_tail_322_) == 1)
{
lean_object* v_tail_323_; lean_object* v___x_325_; uint8_t v_isShared_326_; uint8_t v_isSharedCheck_429_; 
v_tail_323_ = lean_ctor_get(v_tail_322_, 1);
v_isSharedCheck_429_ = !lean_is_exclusive(v_tail_322_);
if (v_isSharedCheck_429_ == 0)
{
lean_object* v_unused_430_; 
v_unused_430_ = lean_ctor_get(v_tail_322_, 0);
lean_dec(v_unused_430_);
v___x_325_ = v_tail_322_;
v_isShared_326_ = v_isSharedCheck_429_;
goto v_resetjp_324_;
}
else
{
lean_inc(v_tail_323_);
lean_dec(v_tail_322_);
v___x_325_ = lean_box(0);
v_isShared_326_ = v_isSharedCheck_429_;
goto v_resetjp_324_;
}
v_resetjp_324_:
{
if (lean_obj_tag(v_tail_323_) == 0)
{
lean_object* v_00_u03b1_327_; lean_object* v_00_u03b2_328_; lean_object* v_h_329_; lean_object* v___x_331_; uint8_t v_isShared_332_; uint8_t v_isSharedCheck_426_; 
v_00_u03b1_327_ = lean_ctor_get(v_val_315_, 1);
v_00_u03b2_328_ = lean_ctor_get(v_val_315_, 2);
v_h_329_ = lean_ctor_get(v_val_315_, 3);
v_isSharedCheck_426_ = !lean_is_exclusive(v_val_315_);
if (v_isSharedCheck_426_ == 0)
{
lean_object* v_unused_427_; lean_object* v_unused_428_; 
v_unused_427_ = lean_ctor_get(v_val_315_, 4);
lean_dec(v_unused_427_);
v_unused_428_ = lean_ctor_get(v_val_315_, 0);
lean_dec(v_unused_428_);
v___x_331_ = v_val_315_;
v_isShared_332_ = v_isSharedCheck_426_;
goto v_resetjp_330_;
}
else
{
lean_inc(v_h_329_);
lean_inc(v_00_u03b2_328_);
lean_inc(v_00_u03b1_327_);
lean_dec(v_val_315_);
v___x_331_ = lean_box(0);
v_isShared_332_ = v_isSharedCheck_426_;
goto v_resetjp_330_;
}
v_resetjp_330_:
{
lean_object* v_head_333_; lean_object* v___x_334_; lean_object* v___x_336_; 
v_head_333_ = lean_ctor_get(v_us_321_, 0);
v___x_334_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__6));
lean_inc(v_head_333_);
if (v_isShared_326_ == 0)
{
lean_ctor_set(v___x_325_, 0, v_head_333_);
v___x_336_ = v___x_325_;
goto v_reusejp_335_;
}
else
{
lean_object* v_reuseFailAlloc_425_; 
v_reuseFailAlloc_425_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_425_, 0, v_head_333_);
lean_ctor_set(v_reuseFailAlloc_425_, 1, v_tail_323_);
v___x_336_ = v_reuseFailAlloc_425_;
goto v_reusejp_335_;
}
v_reusejp_335_:
{
lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; 
v___x_337_ = l_Lean_mkConst(v___x_334_, v___x_336_);
lean_inc_ref_n(v_00_u03b1_327_, 2);
v___x_338_ = l_Lean_mkAppB(v___x_337_, v_00_u03b1_327_, v_a_282_);
v___x_339_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__10));
lean_inc_ref(v_us_321_);
v___x_340_ = l_Lean_mkConst(v___x_339_, v_us_321_);
lean_inc_ref(v_h_329_);
lean_inc_ref(v_f_281_);
lean_inc_ref(v_00_u03b2_328_);
v___x_341_ = l_Lean_mkApp5(v___x_340_, v_00_u03b1_327_, v_00_u03b2_328_, v_f_281_, v_h_329_, v___x_338_);
v___x_342_ = l_Lean_Meta_Grind_preprocessLight___redArg(v___x_341_, v_a_284_, v_a_285_, v_a_286_, v_a_287_, v_a_288_, v_a_289_, v_a_290_, v_a_291_, v_a_292_);
if (lean_obj_tag(v___x_342_) == 0)
{
lean_object* v_a_343_; lean_object* v___x_345_; uint8_t v_isShared_346_; uint8_t v_isSharedCheck_416_; 
v_a_343_ = lean_ctor_get(v___x_342_, 0);
v_isSharedCheck_416_ = !lean_is_exclusive(v___x_342_);
if (v_isSharedCheck_416_ == 0)
{
v___x_345_ = v___x_342_;
v_isShared_346_ = v_isSharedCheck_416_;
goto v_resetjp_344_;
}
else
{
lean_inc(v_a_343_);
lean_dec(v___x_342_);
v___x_345_ = lean_box(0);
v_isShared_346_ = v_isSharedCheck_416_;
goto v_resetjp_344_;
}
v_resetjp_344_:
{
lean_object* v___x_347_; lean_object* v_nargs_348_; lean_object* v_toGoalState_349_; lean_object* v_inj_350_; lean_object* v_mvarId_351_; lean_object* v___x_353_; uint8_t v_isShared_354_; uint8_t v_isSharedCheck_414_; 
v___x_347_ = lean_st_ref_take(v_a_283_);
v_nargs_348_ = l_Lean_Expr_getAppNumArgs(v_a_343_);
v_toGoalState_349_ = lean_ctor_get(v___x_347_, 0);
lean_inc_ref(v_toGoalState_349_);
v_inj_350_ = lean_ctor_get(v_toGoalState_349_, 13);
lean_inc_ref(v_inj_350_);
v_mvarId_351_ = lean_ctor_get(v___x_347_, 1);
v_isSharedCheck_414_ = !lean_is_exclusive(v___x_347_);
if (v_isSharedCheck_414_ == 0)
{
lean_object* v_unused_415_; 
v_unused_415_ = lean_ctor_get(v___x_347_, 0);
lean_dec(v_unused_415_);
v___x_353_ = v___x_347_;
v_isShared_354_ = v_isSharedCheck_414_;
goto v_resetjp_352_;
}
else
{
lean_inc(v_mvarId_351_);
lean_dec(v___x_347_);
v___x_353_ = lean_box(0);
v_isShared_354_ = v_isSharedCheck_414_;
goto v_resetjp_352_;
}
v_resetjp_352_:
{
lean_object* v_nextDeclIdx_355_; lean_object* v_enodeMap_356_; lean_object* v_exprs_357_; lean_object* v_parents_358_; lean_object* v_congrTable_359_; lean_object* v_appMap_360_; lean_object* v_indicesFound_361_; lean_object* v_newFacts_362_; uint8_t v_inconsistent_363_; lean_object* v_nextIdx_364_; lean_object* v_newRawFacts_365_; lean_object* v_facts_366_; lean_object* v_extThms_367_; lean_object* v_ematch_368_; lean_object* v_split_369_; lean_object* v_clean_370_; lean_object* v_sstates_371_; lean_object* v___x_373_; uint8_t v_isShared_374_; uint8_t v_isSharedCheck_412_; 
v_nextDeclIdx_355_ = lean_ctor_get(v_toGoalState_349_, 0);
v_enodeMap_356_ = lean_ctor_get(v_toGoalState_349_, 1);
v_exprs_357_ = lean_ctor_get(v_toGoalState_349_, 2);
v_parents_358_ = lean_ctor_get(v_toGoalState_349_, 3);
v_congrTable_359_ = lean_ctor_get(v_toGoalState_349_, 4);
v_appMap_360_ = lean_ctor_get(v_toGoalState_349_, 5);
v_indicesFound_361_ = lean_ctor_get(v_toGoalState_349_, 6);
v_newFacts_362_ = lean_ctor_get(v_toGoalState_349_, 7);
v_inconsistent_363_ = lean_ctor_get_uint8(v_toGoalState_349_, sizeof(void*)*17);
v_nextIdx_364_ = lean_ctor_get(v_toGoalState_349_, 8);
v_newRawFacts_365_ = lean_ctor_get(v_toGoalState_349_, 9);
v_facts_366_ = lean_ctor_get(v_toGoalState_349_, 10);
v_extThms_367_ = lean_ctor_get(v_toGoalState_349_, 11);
v_ematch_368_ = lean_ctor_get(v_toGoalState_349_, 12);
v_split_369_ = lean_ctor_get(v_toGoalState_349_, 14);
v_clean_370_ = lean_ctor_get(v_toGoalState_349_, 15);
v_sstates_371_ = lean_ctor_get(v_toGoalState_349_, 16);
v_isSharedCheck_412_ = !lean_is_exclusive(v_toGoalState_349_);
if (v_isSharedCheck_412_ == 0)
{
lean_object* v_unused_413_; 
v_unused_413_ = lean_ctor_get(v_toGoalState_349_, 13);
lean_dec(v_unused_413_);
v___x_373_ = v_toGoalState_349_;
v_isShared_374_ = v_isSharedCheck_412_;
goto v_resetjp_372_;
}
else
{
lean_inc(v_sstates_371_);
lean_inc(v_clean_370_);
lean_inc(v_split_369_);
lean_inc(v_ematch_368_);
lean_inc(v_extThms_367_);
lean_inc(v_facts_366_);
lean_inc(v_newRawFacts_365_);
lean_inc(v_nextIdx_364_);
lean_inc(v_newFacts_362_);
lean_inc(v_indicesFound_361_);
lean_inc(v_appMap_360_);
lean_inc(v_congrTable_359_);
lean_inc(v_parents_358_);
lean_inc(v_exprs_357_);
lean_inc(v_enodeMap_356_);
lean_inc(v_nextDeclIdx_355_);
lean_dec(v_toGoalState_349_);
v___x_373_ = lean_box(0);
v_isShared_374_ = v_isSharedCheck_412_;
goto v_resetjp_372_;
}
v_resetjp_372_:
{
lean_object* v_thms_375_; lean_object* v_fns_376_; lean_object* v___x_378_; uint8_t v_isShared_379_; uint8_t v_isSharedCheck_411_; 
v_thms_375_ = lean_ctor_get(v_inj_350_, 0);
v_fns_376_ = lean_ctor_get(v_inj_350_, 1);
v_isSharedCheck_411_ = !lean_is_exclusive(v_inj_350_);
if (v_isSharedCheck_411_ == 0)
{
v___x_378_ = v_inj_350_;
v_isShared_379_ = v_isSharedCheck_411_;
goto v_resetjp_377_;
}
else
{
lean_inc(v_fns_376_);
lean_inc(v_thms_375_);
lean_dec(v_inj_350_);
v___x_378_ = lean_box(0);
v_isShared_379_ = v_isSharedCheck_411_;
goto v_resetjp_377_;
}
v_resetjp_377_:
{
lean_object* v_dummy_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_389_; 
v_dummy_380_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__11, &l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__11_once, _init_l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__11);
lean_inc(v_nargs_348_);
v___x_381_ = lean_mk_array(v_nargs_348_, v_dummy_380_);
v___x_382_ = lean_unsigned_to_nat(1u);
v___x_383_ = lean_nat_sub(v_nargs_348_, v___x_382_);
lean_dec(v_nargs_348_);
lean_inc(v_a_343_);
v___x_384_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_343_, v___x_381_, v___x_383_);
v___x_385_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__13));
lean_inc_ref(v_us_321_);
v___x_386_ = l_Lean_mkConst(v___x_385_, v_us_321_);
v___x_387_ = l_Lean_mkAppN(v___x_386_, v___x_384_);
lean_dec_ref(v___x_384_);
if (v_isShared_313_ == 0)
{
lean_ctor_set(v___x_312_, 1, v___x_387_);
lean_ctor_set(v___x_312_, 0, v_a_343_);
v___x_389_ = v___x_312_;
goto v_reusejp_388_;
}
else
{
lean_object* v_reuseFailAlloc_410_; 
v_reuseFailAlloc_410_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_410_, 0, v_a_343_);
lean_ctor_set(v_reuseFailAlloc_410_, 1, v___x_387_);
v___x_389_ = v_reuseFailAlloc_410_;
goto v_reusejp_388_;
}
v_reusejp_388_:
{
lean_object* v___x_391_; 
if (v_isShared_318_ == 0)
{
lean_ctor_set(v___x_317_, 0, v___x_389_);
v___x_391_ = v___x_317_;
goto v_reusejp_390_;
}
else
{
lean_object* v_reuseFailAlloc_409_; 
v_reuseFailAlloc_409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_409_, 0, v___x_389_);
v___x_391_ = v_reuseFailAlloc_409_;
goto v_reusejp_390_;
}
v_reusejp_390_:
{
lean_object* v___x_393_; 
lean_inc_ref(v___x_391_);
if (v_isShared_332_ == 0)
{
lean_ctor_set(v___x_331_, 4, v___x_391_);
v___x_393_ = v___x_331_;
goto v_reusejp_392_;
}
else
{
lean_object* v_reuseFailAlloc_408_; 
v_reuseFailAlloc_408_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_408_, 0, v_us_321_);
lean_ctor_set(v_reuseFailAlloc_408_, 1, v_00_u03b1_327_);
lean_ctor_set(v_reuseFailAlloc_408_, 2, v_00_u03b2_328_);
lean_ctor_set(v_reuseFailAlloc_408_, 3, v_h_329_);
lean_ctor_set(v_reuseFailAlloc_408_, 4, v___x_391_);
v___x_393_ = v_reuseFailAlloc_408_;
goto v_reusejp_392_;
}
v_reusejp_392_:
{
lean_object* v___x_394_; lean_object* v___x_396_; 
v___x_394_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2___redArg(v_fns_376_, v_f_281_, v___x_393_);
if (v_isShared_379_ == 0)
{
lean_ctor_set(v___x_378_, 1, v___x_394_);
v___x_396_ = v___x_378_;
goto v_reusejp_395_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_407_, 0, v_thms_375_);
lean_ctor_set(v_reuseFailAlloc_407_, 1, v___x_394_);
v___x_396_ = v_reuseFailAlloc_407_;
goto v_reusejp_395_;
}
v_reusejp_395_:
{
lean_object* v___x_398_; 
if (v_isShared_374_ == 0)
{
lean_ctor_set(v___x_373_, 13, v___x_396_);
v___x_398_ = v___x_373_;
goto v_reusejp_397_;
}
else
{
lean_object* v_reuseFailAlloc_406_; 
v_reuseFailAlloc_406_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_406_, 0, v_nextDeclIdx_355_);
lean_ctor_set(v_reuseFailAlloc_406_, 1, v_enodeMap_356_);
lean_ctor_set(v_reuseFailAlloc_406_, 2, v_exprs_357_);
lean_ctor_set(v_reuseFailAlloc_406_, 3, v_parents_358_);
lean_ctor_set(v_reuseFailAlloc_406_, 4, v_congrTable_359_);
lean_ctor_set(v_reuseFailAlloc_406_, 5, v_appMap_360_);
lean_ctor_set(v_reuseFailAlloc_406_, 6, v_indicesFound_361_);
lean_ctor_set(v_reuseFailAlloc_406_, 7, v_newFacts_362_);
lean_ctor_set(v_reuseFailAlloc_406_, 8, v_nextIdx_364_);
lean_ctor_set(v_reuseFailAlloc_406_, 9, v_newRawFacts_365_);
lean_ctor_set(v_reuseFailAlloc_406_, 10, v_facts_366_);
lean_ctor_set(v_reuseFailAlloc_406_, 11, v_extThms_367_);
lean_ctor_set(v_reuseFailAlloc_406_, 12, v_ematch_368_);
lean_ctor_set(v_reuseFailAlloc_406_, 13, v___x_396_);
lean_ctor_set(v_reuseFailAlloc_406_, 14, v_split_369_);
lean_ctor_set(v_reuseFailAlloc_406_, 15, v_clean_370_);
lean_ctor_set(v_reuseFailAlloc_406_, 16, v_sstates_371_);
lean_ctor_set_uint8(v_reuseFailAlloc_406_, sizeof(void*)*17, v_inconsistent_363_);
v___x_398_ = v_reuseFailAlloc_406_;
goto v_reusejp_397_;
}
v_reusejp_397_:
{
lean_object* v___x_400_; 
if (v_isShared_354_ == 0)
{
lean_ctor_set(v___x_353_, 0, v___x_398_);
v___x_400_ = v___x_353_;
goto v_reusejp_399_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v___x_398_);
lean_ctor_set(v_reuseFailAlloc_405_, 1, v_mvarId_351_);
v___x_400_ = v_reuseFailAlloc_405_;
goto v_reusejp_399_;
}
v_reusejp_399_:
{
lean_object* v___x_401_; lean_object* v___x_403_; 
v___x_401_ = lean_st_ref_set(v_a_283_, v___x_400_);
if (v_isShared_346_ == 0)
{
lean_ctor_set(v___x_345_, 0, v___x_391_);
v___x_403_ = v___x_345_;
goto v_reusejp_402_;
}
else
{
lean_object* v_reuseFailAlloc_404_; 
v_reuseFailAlloc_404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_404_, 0, v___x_391_);
v___x_403_ = v_reuseFailAlloc_404_;
goto v_reusejp_402_;
}
v_reusejp_402_:
{
return v___x_403_;
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
lean_object* v_a_417_; lean_object* v___x_419_; uint8_t v_isShared_420_; uint8_t v_isSharedCheck_424_; 
lean_del_object(v___x_331_);
lean_dec_ref(v_h_329_);
lean_dec_ref(v_00_u03b2_328_);
lean_dec_ref(v_00_u03b1_327_);
lean_dec_ref_known(v_us_321_, 2);
lean_del_object(v___x_317_);
lean_del_object(v___x_312_);
lean_dec_ref(v_f_281_);
v_a_417_ = lean_ctor_get(v___x_342_, 0);
v_isSharedCheck_424_ = !lean_is_exclusive(v___x_342_);
if (v_isSharedCheck_424_ == 0)
{
v___x_419_ = v___x_342_;
v_isShared_420_ = v_isSharedCheck_424_;
goto v_resetjp_418_;
}
else
{
lean_inc(v_a_417_);
lean_dec(v___x_342_);
v___x_419_ = lean_box(0);
v_isShared_420_ = v_isSharedCheck_424_;
goto v_resetjp_418_;
}
v_resetjp_418_:
{
lean_object* v___x_422_; 
if (v_isShared_420_ == 0)
{
v___x_422_ = v___x_419_;
goto v_reusejp_421_;
}
else
{
lean_object* v_reuseFailAlloc_423_; 
v_reuseFailAlloc_423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_423_, 0, v_a_417_);
v___x_422_ = v_reuseFailAlloc_423_;
goto v_reusejp_421_;
}
v_reusejp_421_:
{
return v___x_422_;
}
}
}
}
}
}
else
{
lean_del_object(v___x_325_);
lean_dec(v_tail_323_);
lean_dec_ref_known(v_us_321_, 2);
lean_del_object(v___x_317_);
lean_dec(v_val_315_);
lean_del_object(v___x_312_);
lean_dec_ref(v_a_282_);
lean_dec_ref(v_f_281_);
v___y_295_ = v_a_283_;
v___y_296_ = v_a_284_;
v___y_297_ = v_a_285_;
v___y_298_ = v_a_286_;
v___y_299_ = v_a_287_;
v___y_300_ = v_a_288_;
v___y_301_ = v_a_289_;
v___y_302_ = v_a_290_;
v___y_303_ = v_a_291_;
v___y_304_ = v_a_292_;
goto v___jp_294_;
}
}
}
else
{
lean_dec(v_tail_322_);
lean_dec_ref_known(v_us_321_, 2);
lean_del_object(v___x_317_);
lean_dec(v_val_315_);
lean_del_object(v___x_312_);
lean_dec_ref(v_a_282_);
lean_dec_ref(v_f_281_);
v___y_295_ = v_a_283_;
v___y_296_ = v_a_284_;
v___y_297_ = v_a_285_;
v___y_298_ = v_a_286_;
v___y_299_ = v_a_287_;
v___y_300_ = v_a_288_;
v___y_301_ = v_a_289_;
v___y_302_ = v_a_290_;
v___y_303_ = v_a_291_;
v___y_304_ = v_a_292_;
goto v___jp_294_;
}
}
else
{
lean_dec(v_us_321_);
lean_del_object(v___x_317_);
lean_dec(v_val_315_);
lean_del_object(v___x_312_);
lean_dec_ref(v_a_282_);
lean_dec_ref(v_f_281_);
v___y_295_ = v_a_283_;
v___y_296_ = v_a_284_;
v___y_297_ = v_a_285_;
v___y_298_ = v_a_286_;
v___y_299_ = v_a_287_;
v___y_300_ = v_a_288_;
v___y_301_ = v_a_289_;
v___y_302_ = v_a_290_;
v___y_303_ = v_a_291_;
v___y_304_ = v_a_292_;
goto v___jp_294_;
}
}
}
}
else
{
lean_object* v___x_432_; lean_object* v___x_433_; 
lean_dec(v___x_314_);
lean_del_object(v___x_312_);
lean_dec_ref(v_a_282_);
lean_dec_ref(v_f_281_);
v___x_432_ = lean_box(0);
v___x_433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_433_, 0, v___x_432_);
return v___x_433_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___boxed(lean_object* v_f_436_, lean_object* v_a_437_, lean_object* v_a_438_, lean_object* v_a_439_, lean_object* v_a_440_, lean_object* v_a_441_, lean_object* v_a_442_, lean_object* v_a_443_, lean_object* v_a_444_, lean_object* v_a_445_, lean_object* v_a_446_, lean_object* v_a_447_, lean_object* v_a_448_){
_start:
{
lean_object* v_res_449_; 
v_res_449_ = l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f(v_f_436_, v_a_437_, v_a_438_, v_a_439_, v_a_440_, v_a_441_, v_a_442_, v_a_443_, v_a_444_, v_a_445_, v_a_446_, v_a_447_);
lean_dec(v_a_447_);
lean_dec_ref(v_a_446_);
lean_dec(v_a_445_);
lean_dec_ref(v_a_444_);
lean_dec(v_a_443_);
lean_dec_ref(v_a_442_);
lean_dec(v_a_441_);
lean_dec_ref(v_a_440_);
lean_dec(v_a_439_);
lean_dec(v_a_438_);
return v_res_449_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1(lean_object* v_00_u03b2_450_, lean_object* v_x_451_, lean_object* v_x_452_){
_start:
{
lean_object* v___x_453_; 
v___x_453_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1___redArg(v_x_451_, v_x_452_);
return v___x_453_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1___boxed(lean_object* v_00_u03b2_454_, lean_object* v_x_455_, lean_object* v_x_456_){
_start:
{
lean_object* v_res_457_; 
v_res_457_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1(v_00_u03b2_454_, v_x_455_, v_x_456_);
lean_dec_ref(v_x_456_);
lean_dec_ref(v_x_455_);
return v_res_457_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2(lean_object* v_00_u03b2_458_, lean_object* v_x_459_, lean_object* v_x_460_, lean_object* v_x_461_){
_start:
{
lean_object* v___x_462_; 
v___x_462_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2___redArg(v_x_459_, v_x_460_, v_x_461_);
return v___x_462_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1(lean_object* v_00_u03b2_463_, lean_object* v_x_464_, size_t v_x_465_, lean_object* v_x_466_){
_start:
{
lean_object* v___x_467_; 
v___x_467_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1___redArg(v_x_464_, v_x_465_, v_x_466_);
return v___x_467_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1___boxed(lean_object* v_00_u03b2_468_, lean_object* v_x_469_, lean_object* v_x_470_, lean_object* v_x_471_){
_start:
{
size_t v_x_10238__boxed_472_; lean_object* v_res_473_; 
v_x_10238__boxed_472_ = lean_unbox_usize(v_x_470_);
lean_dec(v_x_470_);
v_res_473_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1(v_00_u03b2_468_, v_x_469_, v_x_10238__boxed_472_, v_x_471_);
lean_dec_ref(v_x_471_);
lean_dec_ref(v_x_469_);
return v_res_473_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3(lean_object* v_00_u03b2_474_, lean_object* v_x_475_, size_t v_x_476_, size_t v_x_477_, lean_object* v_x_478_, lean_object* v_x_479_){
_start:
{
lean_object* v___x_480_; 
v___x_480_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3___redArg(v_x_475_, v_x_476_, v_x_477_, v_x_478_, v_x_479_);
return v___x_480_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3___boxed(lean_object* v_00_u03b2_481_, lean_object* v_x_482_, lean_object* v_x_483_, lean_object* v_x_484_, lean_object* v_x_485_, lean_object* v_x_486_){
_start:
{
size_t v_x_10249__boxed_487_; size_t v_x_10250__boxed_488_; lean_object* v_res_489_; 
v_x_10249__boxed_487_ = lean_unbox_usize(v_x_483_);
lean_dec(v_x_483_);
v_x_10250__boxed_488_ = lean_unbox_usize(v_x_484_);
lean_dec(v_x_484_);
v_res_489_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3(v_00_u03b2_481_, v_x_482_, v_x_10249__boxed_487_, v_x_10250__boxed_488_, v_x_485_, v_x_486_);
return v_res_489_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_490_, lean_object* v_keys_491_, lean_object* v_vals_492_, lean_object* v_heq_493_, lean_object* v_i_494_, lean_object* v_k_495_){
_start:
{
lean_object* v___x_496_; 
v___x_496_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1_spec__2___redArg(v_keys_491_, v_vals_492_, v_i_494_, v_k_495_);
return v___x_496_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03b2_497_, lean_object* v_keys_498_, lean_object* v_vals_499_, lean_object* v_heq_500_, lean_object* v_i_501_, lean_object* v_k_502_){
_start:
{
lean_object* v_res_503_; 
v_res_503_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1_spec__2(v_00_u03b2_497_, v_keys_498_, v_vals_499_, v_heq_500_, v_i_501_, v_k_502_);
lean_dec_ref(v_k_502_);
lean_dec_ref(v_vals_499_);
lean_dec_ref(v_keys_498_);
return v_res_503_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3_spec__5(lean_object* v_00_u03b2_504_, lean_object* v_n_505_, lean_object* v_k_506_, lean_object* v_v_507_){
_start:
{
lean_object* v___x_508_; 
v___x_508_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3_spec__5___redArg(v_n_505_, v_k_506_, v_v_507_);
return v___x_508_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3_spec__6(lean_object* v_00_u03b2_509_, size_t v_depth_510_, lean_object* v_keys_511_, lean_object* v_vals_512_, lean_object* v_heq_513_, lean_object* v_i_514_, lean_object* v_entries_515_){
_start:
{
lean_object* v___x_516_; 
v___x_516_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3_spec__6___redArg(v_depth_510_, v_keys_511_, v_vals_512_, v_i_514_, v_entries_515_);
return v___x_516_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3_spec__6___boxed(lean_object* v_00_u03b2_517_, lean_object* v_depth_518_, lean_object* v_keys_519_, lean_object* v_vals_520_, lean_object* v_heq_521_, lean_object* v_i_522_, lean_object* v_entries_523_){
_start:
{
size_t v_depth_boxed_524_; lean_object* v_res_525_; 
v_depth_boxed_524_ = lean_unbox_usize(v_depth_518_);
lean_dec(v_depth_518_);
v_res_525_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3_spec__6(v_00_u03b2_517_, v_depth_boxed_524_, v_keys_519_, v_vals_520_, v_heq_521_, v_i_522_, v_entries_523_);
lean_dec_ref(v_vals_520_);
lean_dec_ref(v_keys_519_);
return v_res_525_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3_spec__5_spec__6(lean_object* v_00_u03b2_526_, lean_object* v_x_527_, lean_object* v_x_528_, lean_object* v_x_529_, lean_object* v_x_530_){
_start:
{
lean_object* v___x_531_; 
v___x_531_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3_spec__5_spec__6___redArg(v_x_527_, v_x_528_, v_x_529_, v_x_530_);
return v___x_531_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0_spec__0(lean_object* v_msgData_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_){
_start:
{
lean_object* v___x_538_; lean_object* v_env_539_; lean_object* v___x_540_; lean_object* v_mctx_541_; lean_object* v_lctx_542_; lean_object* v_options_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; 
v___x_538_ = lean_st_ref_get(v___y_536_);
v_env_539_ = lean_ctor_get(v___x_538_, 0);
lean_inc_ref(v_env_539_);
lean_dec(v___x_538_);
v___x_540_ = lean_st_ref_get(v___y_534_);
v_mctx_541_ = lean_ctor_get(v___x_540_, 0);
lean_inc_ref(v_mctx_541_);
lean_dec(v___x_540_);
v_lctx_542_ = lean_ctor_get(v___y_533_, 2);
v_options_543_ = lean_ctor_get(v___y_535_, 2);
lean_inc_ref(v_options_543_);
lean_inc_ref(v_lctx_542_);
v___x_544_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_544_, 0, v_env_539_);
lean_ctor_set(v___x_544_, 1, v_mctx_541_);
lean_ctor_set(v___x_544_, 2, v_lctx_542_);
lean_ctor_set(v___x_544_, 3, v_options_543_);
v___x_545_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_545_, 0, v___x_544_);
lean_ctor_set(v___x_545_, 1, v_msgData_532_);
v___x_546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_546_, 0, v___x_545_);
return v___x_546_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0_spec__0___boxed(lean_object* v_msgData_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_){
_start:
{
lean_object* v_res_553_; 
v_res_553_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0_spec__0(v_msgData_547_, v___y_548_, v___y_549_, v___y_550_, v___y_551_);
lean_dec(v___y_551_);
lean_dec_ref(v___y_550_);
lean_dec(v___y_549_);
lean_dec_ref(v___y_548_);
return v_res_553_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_554_; double v___x_555_; 
v___x_554_ = lean_unsigned_to_nat(0u);
v___x_555_ = lean_float_of_nat(v___x_554_);
return v___x_555_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0___redArg(lean_object* v_cls_559_, lean_object* v_msg_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_){
_start:
{
lean_object* v_ref_566_; lean_object* v___x_567_; lean_object* v_a_568_; lean_object* v___x_570_; uint8_t v_isShared_571_; uint8_t v_isSharedCheck_612_; 
v_ref_566_ = lean_ctor_get(v___y_563_, 5);
v___x_567_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0_spec__0(v_msg_560_, v___y_561_, v___y_562_, v___y_563_, v___y_564_);
v_a_568_ = lean_ctor_get(v___x_567_, 0);
v_isSharedCheck_612_ = !lean_is_exclusive(v___x_567_);
if (v_isSharedCheck_612_ == 0)
{
v___x_570_ = v___x_567_;
v_isShared_571_ = v_isSharedCheck_612_;
goto v_resetjp_569_;
}
else
{
lean_inc(v_a_568_);
lean_dec(v___x_567_);
v___x_570_ = lean_box(0);
v_isShared_571_ = v_isSharedCheck_612_;
goto v_resetjp_569_;
}
v_resetjp_569_:
{
lean_object* v___x_572_; lean_object* v_traceState_573_; lean_object* v_env_574_; lean_object* v_nextMacroScope_575_; lean_object* v_ngen_576_; lean_object* v_auxDeclNGen_577_; lean_object* v_cache_578_; lean_object* v_messages_579_; lean_object* v_infoState_580_; lean_object* v_snapshotTasks_581_; lean_object* v___x_583_; uint8_t v_isShared_584_; uint8_t v_isSharedCheck_611_; 
v___x_572_ = lean_st_ref_take(v___y_564_);
v_traceState_573_ = lean_ctor_get(v___x_572_, 4);
v_env_574_ = lean_ctor_get(v___x_572_, 0);
v_nextMacroScope_575_ = lean_ctor_get(v___x_572_, 1);
v_ngen_576_ = lean_ctor_get(v___x_572_, 2);
v_auxDeclNGen_577_ = lean_ctor_get(v___x_572_, 3);
v_cache_578_ = lean_ctor_get(v___x_572_, 5);
v_messages_579_ = lean_ctor_get(v___x_572_, 6);
v_infoState_580_ = lean_ctor_get(v___x_572_, 7);
v_snapshotTasks_581_ = lean_ctor_get(v___x_572_, 8);
v_isSharedCheck_611_ = !lean_is_exclusive(v___x_572_);
if (v_isSharedCheck_611_ == 0)
{
v___x_583_ = v___x_572_;
v_isShared_584_ = v_isSharedCheck_611_;
goto v_resetjp_582_;
}
else
{
lean_inc(v_snapshotTasks_581_);
lean_inc(v_infoState_580_);
lean_inc(v_messages_579_);
lean_inc(v_cache_578_);
lean_inc(v_traceState_573_);
lean_inc(v_auxDeclNGen_577_);
lean_inc(v_ngen_576_);
lean_inc(v_nextMacroScope_575_);
lean_inc(v_env_574_);
lean_dec(v___x_572_);
v___x_583_ = lean_box(0);
v_isShared_584_ = v_isSharedCheck_611_;
goto v_resetjp_582_;
}
v_resetjp_582_:
{
uint64_t v_tid_585_; lean_object* v_traces_586_; lean_object* v___x_588_; uint8_t v_isShared_589_; uint8_t v_isSharedCheck_610_; 
v_tid_585_ = lean_ctor_get_uint64(v_traceState_573_, sizeof(void*)*1);
v_traces_586_ = lean_ctor_get(v_traceState_573_, 0);
v_isSharedCheck_610_ = !lean_is_exclusive(v_traceState_573_);
if (v_isSharedCheck_610_ == 0)
{
v___x_588_ = v_traceState_573_;
v_isShared_589_ = v_isSharedCheck_610_;
goto v_resetjp_587_;
}
else
{
lean_inc(v_traces_586_);
lean_dec(v_traceState_573_);
v___x_588_ = lean_box(0);
v_isShared_589_ = v_isSharedCheck_610_;
goto v_resetjp_587_;
}
v_resetjp_587_:
{
lean_object* v___x_590_; double v___x_591_; uint8_t v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_600_; 
v___x_590_ = lean_box(0);
v___x_591_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0___redArg___closed__0);
v___x_592_ = 0;
v___x_593_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0___redArg___closed__1));
v___x_594_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_594_, 0, v_cls_559_);
lean_ctor_set(v___x_594_, 1, v___x_590_);
lean_ctor_set(v___x_594_, 2, v___x_593_);
lean_ctor_set_float(v___x_594_, sizeof(void*)*3, v___x_591_);
lean_ctor_set_float(v___x_594_, sizeof(void*)*3 + 8, v___x_591_);
lean_ctor_set_uint8(v___x_594_, sizeof(void*)*3 + 16, v___x_592_);
v___x_595_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0___redArg___closed__2));
v___x_596_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_596_, 0, v___x_594_);
lean_ctor_set(v___x_596_, 1, v_a_568_);
lean_ctor_set(v___x_596_, 2, v___x_595_);
lean_inc(v_ref_566_);
v___x_597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_597_, 0, v_ref_566_);
lean_ctor_set(v___x_597_, 1, v___x_596_);
v___x_598_ = l_Lean_PersistentArray_push___redArg(v_traces_586_, v___x_597_);
if (v_isShared_589_ == 0)
{
lean_ctor_set(v___x_588_, 0, v___x_598_);
v___x_600_ = v___x_588_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_609_; 
v_reuseFailAlloc_609_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v___x_598_);
lean_ctor_set_uint64(v_reuseFailAlloc_609_, sizeof(void*)*1, v_tid_585_);
v___x_600_ = v_reuseFailAlloc_609_;
goto v_reusejp_599_;
}
v_reusejp_599_:
{
lean_object* v___x_602_; 
if (v_isShared_584_ == 0)
{
lean_ctor_set(v___x_583_, 4, v___x_600_);
v___x_602_ = v___x_583_;
goto v_reusejp_601_;
}
else
{
lean_object* v_reuseFailAlloc_608_; 
v_reuseFailAlloc_608_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_608_, 0, v_env_574_);
lean_ctor_set(v_reuseFailAlloc_608_, 1, v_nextMacroScope_575_);
lean_ctor_set(v_reuseFailAlloc_608_, 2, v_ngen_576_);
lean_ctor_set(v_reuseFailAlloc_608_, 3, v_auxDeclNGen_577_);
lean_ctor_set(v_reuseFailAlloc_608_, 4, v___x_600_);
lean_ctor_set(v_reuseFailAlloc_608_, 5, v_cache_578_);
lean_ctor_set(v_reuseFailAlloc_608_, 6, v_messages_579_);
lean_ctor_set(v_reuseFailAlloc_608_, 7, v_infoState_580_);
lean_ctor_set(v_reuseFailAlloc_608_, 8, v_snapshotTasks_581_);
v___x_602_ = v_reuseFailAlloc_608_;
goto v_reusejp_601_;
}
v_reusejp_601_:
{
lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_606_; 
v___x_603_ = lean_st_ref_set(v___y_564_, v___x_602_);
v___x_604_ = lean_box(0);
if (v_isShared_571_ == 0)
{
lean_ctor_set(v___x_570_, 0, v___x_604_);
v___x_606_ = v___x_570_;
goto v_reusejp_605_;
}
else
{
lean_object* v_reuseFailAlloc_607_; 
v_reuseFailAlloc_607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_607_, 0, v___x_604_);
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
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0___redArg___boxed(lean_object* v_cls_613_, lean_object* v_msg_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_){
_start:
{
lean_object* v_res_620_; 
v_res_620_ = l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0___redArg(v_cls_613_, v_msg_614_, v___y_615_, v___y_616_, v___y_617_, v___y_618_);
lean_dec(v___y_618_);
lean_dec_ref(v___y_617_);
lean_dec(v___y_616_);
lean_dec_ref(v___y_615_);
return v_res_620_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkInjEq___closed__6(void){
_start:
{
lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; 
v___x_631_ = ((lean_object*)(l_Lean_Meta_Grind_mkInjEq___closed__3));
v___x_632_ = ((lean_object*)(l_Lean_Meta_Grind_mkInjEq___closed__5));
v___x_633_ = l_Lean_Name_append(v___x_632_, v___x_631_);
return v___x_633_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkInjEq___closed__8(void){
_start:
{
lean_object* v___x_635_; lean_object* v___x_636_; 
v___x_635_ = ((lean_object*)(l_Lean_Meta_Grind_mkInjEq___closed__7));
v___x_636_ = l_Lean_stringToMessageData(v___x_635_);
return v___x_636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkInjEq(lean_object* v_e_637_, lean_object* v_a_638_, lean_object* v_a_639_, lean_object* v_a_640_, lean_object* v_a_641_, lean_object* v_a_642_, lean_object* v_a_643_, lean_object* v_a_644_, lean_object* v_a_645_, lean_object* v_a_646_, lean_object* v_a_647_){
_start:
{
if (lean_obj_tag(v_e_637_) == 5)
{
lean_object* v_fn_649_; lean_object* v_arg_650_; lean_object* v___x_651_; 
v_fn_649_ = lean_ctor_get(v_e_637_, 0);
v_arg_650_ = lean_ctor_get(v_e_637_, 1);
lean_inc_ref_n(v_arg_650_, 2);
lean_inc_ref(v_fn_649_);
v___x_651_ = l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f(v_fn_649_, v_arg_650_, v_a_638_, v_a_639_, v_a_640_, v_a_641_, v_a_642_, v_a_643_, v_a_644_, v_a_645_, v_a_646_, v_a_647_);
if (lean_obj_tag(v___x_651_) == 0)
{
lean_object* v_a_652_; lean_object* v___x_654_; uint8_t v_isShared_655_; uint8_t v_isSharedCheck_704_; 
v_a_652_ = lean_ctor_get(v___x_651_, 0);
v_isSharedCheck_704_ = !lean_is_exclusive(v___x_651_);
if (v_isSharedCheck_704_ == 0)
{
v___x_654_ = v___x_651_;
v_isShared_655_ = v_isSharedCheck_704_;
goto v_resetjp_653_;
}
else
{
lean_inc(v_a_652_);
lean_dec(v___x_651_);
v___x_654_ = lean_box(0);
v_isShared_655_ = v_isSharedCheck_704_;
goto v_resetjp_653_;
}
v_resetjp_653_:
{
if (lean_obj_tag(v_a_652_) == 1)
{
lean_object* v_val_656_; lean_object* v_fst_657_; lean_object* v_snd_658_; lean_object* v___x_660_; uint8_t v_isShared_661_; uint8_t v_isSharedCheck_699_; 
lean_del_object(v___x_654_);
v_val_656_ = lean_ctor_get(v_a_652_, 0);
lean_inc(v_val_656_);
lean_dec_ref_known(v_a_652_, 1);
v_fst_657_ = lean_ctor_get(v_val_656_, 0);
v_snd_658_ = lean_ctor_get(v_val_656_, 1);
v_isSharedCheck_699_ = !lean_is_exclusive(v_val_656_);
if (v_isSharedCheck_699_ == 0)
{
v___x_660_ = v_val_656_;
v_isShared_661_ = v_isSharedCheck_699_;
goto v_resetjp_659_;
}
else
{
lean_inc(v_snd_658_);
lean_inc(v_fst_657_);
lean_dec(v_val_656_);
v___x_660_ = lean_box(0);
v_isShared_661_ = v_isSharedCheck_699_;
goto v_resetjp_659_;
}
v_resetjp_659_:
{
lean_object* v___x_662_; 
v___x_662_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_637_, v_a_638_);
if (lean_obj_tag(v___x_662_) == 0)
{
lean_object* v_a_663_; lean_object* v___x_664_; lean_object* v___y_666_; lean_object* v___y_667_; lean_object* v___y_668_; lean_object* v___y_669_; lean_object* v___y_670_; lean_object* v___y_671_; lean_object* v___x_675_; lean_object* v___x_676_; 
v_a_663_ = lean_ctor_get(v___x_662_, 0);
lean_inc(v_a_663_);
lean_dec_ref_known(v___x_662_, 1);
v___x_664_ = l_Lean_Expr_app___override(v_fst_657_, v_e_637_);
v___x_675_ = lean_box(0);
lean_inc(v_a_647_);
lean_inc_ref(v_a_646_);
lean_inc(v_a_645_);
lean_inc_ref(v_a_644_);
lean_inc(v_a_643_);
lean_inc_ref(v_a_642_);
lean_inc(v_a_641_);
lean_inc_ref(v_a_640_);
lean_inc(v_a_639_);
lean_inc(v_a_638_);
lean_inc_ref(v___x_664_);
v___x_676_ = lean_grind_internalize(v___x_664_, v_a_663_, v___x_675_, v_a_638_, v_a_639_, v_a_640_, v_a_641_, v_a_642_, v_a_643_, v_a_644_, v_a_645_, v_a_646_, v_a_647_);
if (lean_obj_tag(v___x_676_) == 0)
{
lean_object* v_options_677_; uint8_t v_hasTrace_678_; 
lean_dec_ref_known(v___x_676_, 1);
v_options_677_ = lean_ctor_get(v_a_646_, 2);
v_hasTrace_678_ = lean_ctor_get_uint8(v_options_677_, sizeof(void*)*1);
if (v_hasTrace_678_ == 0)
{
lean_del_object(v___x_660_);
v___y_666_ = v_a_638_;
v___y_667_ = v_a_640_;
v___y_668_ = v_a_644_;
v___y_669_ = v_a_645_;
v___y_670_ = v_a_646_;
v___y_671_ = v_a_647_;
goto v___jp_665_;
}
else
{
lean_object* v_inheritedTraceOptions_679_; lean_object* v___x_680_; lean_object* v___x_681_; uint8_t v___x_682_; 
v_inheritedTraceOptions_679_ = lean_ctor_get(v_a_646_, 13);
v___x_680_ = ((lean_object*)(l_Lean_Meta_Grind_mkInjEq___closed__3));
v___x_681_ = lean_obj_once(&l_Lean_Meta_Grind_mkInjEq___closed__6, &l_Lean_Meta_Grind_mkInjEq___closed__6_once, _init_l_Lean_Meta_Grind_mkInjEq___closed__6);
v___x_682_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_679_, v_options_677_, v___x_681_);
if (v___x_682_ == 0)
{
lean_del_object(v___x_660_);
v___y_666_ = v_a_638_;
v___y_667_ = v_a_640_;
v___y_668_ = v_a_644_;
v___y_669_ = v_a_645_;
v___y_670_ = v_a_646_;
v___y_671_ = v_a_647_;
goto v___jp_665_;
}
else
{
lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_686_; 
lean_inc_ref(v___x_664_);
v___x_683_ = l_Lean_MessageData_ofExpr(v___x_664_);
v___x_684_ = lean_obj_once(&l_Lean_Meta_Grind_mkInjEq___closed__8, &l_Lean_Meta_Grind_mkInjEq___closed__8_once, _init_l_Lean_Meta_Grind_mkInjEq___closed__8);
if (v_isShared_661_ == 0)
{
lean_ctor_set_tag(v___x_660_, 7);
lean_ctor_set(v___x_660_, 1, v___x_684_);
lean_ctor_set(v___x_660_, 0, v___x_683_);
v___x_686_ = v___x_660_;
goto v_reusejp_685_;
}
else
{
lean_object* v_reuseFailAlloc_690_; 
v_reuseFailAlloc_690_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_690_, 0, v___x_683_);
lean_ctor_set(v_reuseFailAlloc_690_, 1, v___x_684_);
v___x_686_ = v_reuseFailAlloc_690_;
goto v_reusejp_685_;
}
v_reusejp_685_:
{
lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; 
lean_inc_ref(v_arg_650_);
v___x_687_ = l_Lean_MessageData_ofExpr(v_arg_650_);
v___x_688_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_688_, 0, v___x_686_);
lean_ctor_set(v___x_688_, 1, v___x_687_);
v___x_689_ = l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0___redArg(v___x_680_, v___x_688_, v_a_644_, v_a_645_, v_a_646_, v_a_647_);
if (lean_obj_tag(v___x_689_) == 0)
{
lean_dec_ref_known(v___x_689_, 1);
v___y_666_ = v_a_638_;
v___y_667_ = v_a_640_;
v___y_668_ = v_a_644_;
v___y_669_ = v_a_645_;
v___y_670_ = v_a_646_;
v___y_671_ = v_a_647_;
goto v___jp_665_;
}
else
{
lean_dec_ref(v___x_664_);
lean_dec(v_snd_658_);
lean_dec_ref(v_arg_650_);
return v___x_689_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_664_);
lean_del_object(v___x_660_);
lean_dec(v_snd_658_);
lean_dec_ref(v_arg_650_);
return v___x_676_;
}
v___jp_665_:
{
lean_object* v___x_672_; uint8_t v___x_673_; lean_object* v___x_674_; 
lean_inc_ref(v_arg_650_);
v___x_672_ = l_Lean_Expr_app___override(v_snd_658_, v_arg_650_);
v___x_673_ = 0;
v___x_674_ = l_Lean_Meta_Grind_pushEqCore___redArg(v___x_664_, v_arg_650_, v___x_672_, v___x_673_, v___y_666_, v___y_667_, v___y_668_, v___y_669_, v___y_670_, v___y_671_);
return v___x_674_;
}
}
else
{
lean_object* v_a_691_; lean_object* v___x_693_; uint8_t v_isShared_694_; uint8_t v_isSharedCheck_698_; 
lean_del_object(v___x_660_);
lean_dec(v_snd_658_);
lean_dec(v_fst_657_);
lean_dec_ref(v_arg_650_);
lean_dec_ref_known(v_e_637_, 2);
v_a_691_ = lean_ctor_get(v___x_662_, 0);
v_isSharedCheck_698_ = !lean_is_exclusive(v___x_662_);
if (v_isSharedCheck_698_ == 0)
{
v___x_693_ = v___x_662_;
v_isShared_694_ = v_isSharedCheck_698_;
goto v_resetjp_692_;
}
else
{
lean_inc(v_a_691_);
lean_dec(v___x_662_);
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
}
else
{
lean_object* v___x_700_; lean_object* v___x_702_; 
lean_dec(v_a_652_);
lean_dec_ref(v_arg_650_);
lean_dec_ref_known(v_e_637_, 2);
v___x_700_ = lean_box(0);
if (v_isShared_655_ == 0)
{
lean_ctor_set(v___x_654_, 0, v___x_700_);
v___x_702_ = v___x_654_;
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
lean_object* v_a_705_; lean_object* v___x_707_; uint8_t v_isShared_708_; uint8_t v_isSharedCheck_712_; 
lean_dec_ref(v_arg_650_);
lean_dec_ref_known(v_e_637_, 2);
v_a_705_ = lean_ctor_get(v___x_651_, 0);
v_isSharedCheck_712_ = !lean_is_exclusive(v___x_651_);
if (v_isSharedCheck_712_ == 0)
{
v___x_707_ = v___x_651_;
v_isShared_708_ = v_isSharedCheck_712_;
goto v_resetjp_706_;
}
else
{
lean_inc(v_a_705_);
lean_dec(v___x_651_);
v___x_707_ = lean_box(0);
v_isShared_708_ = v_isSharedCheck_712_;
goto v_resetjp_706_;
}
v_resetjp_706_:
{
lean_object* v___x_710_; 
if (v_isShared_708_ == 0)
{
v___x_710_ = v___x_707_;
goto v_reusejp_709_;
}
else
{
lean_object* v_reuseFailAlloc_711_; 
v_reuseFailAlloc_711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_711_, 0, v_a_705_);
v___x_710_ = v_reuseFailAlloc_711_;
goto v_reusejp_709_;
}
v_reusejp_709_:
{
return v___x_710_;
}
}
}
}
else
{
lean_object* v___x_713_; lean_object* v___x_714_; 
lean_dec_ref(v_e_637_);
v___x_713_ = lean_box(0);
v___x_714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_714_, 0, v___x_713_);
return v___x_714_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkInjEq___boxed(lean_object* v_e_715_, lean_object* v_a_716_, lean_object* v_a_717_, lean_object* v_a_718_, lean_object* v_a_719_, lean_object* v_a_720_, lean_object* v_a_721_, lean_object* v_a_722_, lean_object* v_a_723_, lean_object* v_a_724_, lean_object* v_a_725_, lean_object* v_a_726_){
_start:
{
lean_object* v_res_727_; 
v_res_727_ = l_Lean_Meta_Grind_mkInjEq(v_e_715_, v_a_716_, v_a_717_, v_a_718_, v_a_719_, v_a_720_, v_a_721_, v_a_722_, v_a_723_, v_a_724_, v_a_725_);
lean_dec(v_a_725_);
lean_dec_ref(v_a_724_);
lean_dec(v_a_723_);
lean_dec_ref(v_a_722_);
lean_dec(v_a_721_);
lean_dec_ref(v_a_720_);
lean_dec(v_a_719_);
lean_dec_ref(v_a_718_);
lean_dec(v_a_717_);
lean_dec(v_a_716_);
return v_res_727_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0(lean_object* v_cls_728_, lean_object* v_msg_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_){
_start:
{
lean_object* v___x_741_; 
v___x_741_ = l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0___redArg(v_cls_728_, v_msg_729_, v___y_736_, v___y_737_, v___y_738_, v___y_739_);
return v___x_741_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0___boxed(lean_object* v_cls_742_, lean_object* v_msg_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_){
_start:
{
lean_object* v_res_755_; 
v_res_755_ = l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0(v_cls_742_, v_msg_743_, v___y_744_, v___y_745_, v___y_746_, v___y_747_, v___y_748_, v___y_749_, v___y_750_, v___y_751_, v___y_752_, v___y_753_);
lean_dec(v___y_753_);
lean_dec_ref(v___y_752_);
lean_dec(v___y_751_);
lean_dec_ref(v___y_750_);
lean_dec(v___y_749_);
lean_dec_ref(v___y_748_);
lean_dec(v___y_747_);
lean_dec_ref(v___y_746_);
lean_dec(v___y_745_);
lean_dec(v___y_744_);
return v_res_755_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1_spec__2___redArg(lean_object* v_keys_756_, lean_object* v_vals_757_, lean_object* v_i_758_, lean_object* v_k_759_){
_start:
{
lean_object* v___x_760_; uint8_t v___x_761_; 
v___x_760_ = lean_array_get_size(v_keys_756_);
v___x_761_ = lean_nat_dec_lt(v_i_758_, v___x_760_);
if (v___x_761_ == 0)
{
lean_object* v___x_762_; 
lean_dec(v_i_758_);
v___x_762_ = lean_box(0);
return v___x_762_;
}
else
{
lean_object* v_k_x27_763_; uint8_t v___x_764_; 
v_k_x27_763_ = lean_array_fget_borrowed(v_keys_756_, v_i_758_);
v___x_764_ = l_Lean_instBEqHeadIndex_beq(v_k_759_, v_k_x27_763_);
if (v___x_764_ == 0)
{
lean_object* v___x_765_; lean_object* v___x_766_; 
v___x_765_ = lean_unsigned_to_nat(1u);
v___x_766_ = lean_nat_add(v_i_758_, v___x_765_);
lean_dec(v_i_758_);
v_i_758_ = v___x_766_;
goto _start;
}
else
{
lean_object* v___x_768_; lean_object* v___x_769_; 
v___x_768_ = lean_array_fget_borrowed(v_vals_757_, v_i_758_);
lean_dec(v_i_758_);
lean_inc(v___x_768_);
v___x_769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_769_, 0, v___x_768_);
return v___x_769_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_keys_770_, lean_object* v_vals_771_, lean_object* v_i_772_, lean_object* v_k_773_){
_start:
{
lean_object* v_res_774_; 
v_res_774_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1_spec__2___redArg(v_keys_770_, v_vals_771_, v_i_772_, v_k_773_);
lean_dec(v_k_773_);
lean_dec_ref(v_vals_771_);
lean_dec_ref(v_keys_770_);
return v_res_774_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1___redArg(lean_object* v_x_775_, size_t v_x_776_, lean_object* v_x_777_){
_start:
{
if (lean_obj_tag(v_x_775_) == 0)
{
lean_object* v_es_778_; lean_object* v___x_779_; size_t v___x_780_; size_t v___x_781_; lean_object* v_j_782_; lean_object* v___x_783_; 
v_es_778_ = lean_ctor_get(v_x_775_, 0);
v___x_779_ = lean_box(2);
v___x_780_ = ((size_t)31ULL);
v___x_781_ = lean_usize_land(v_x_776_, v___x_780_);
v_j_782_ = lean_usize_to_nat(v___x_781_);
v___x_783_ = lean_array_get_borrowed(v___x_779_, v_es_778_, v_j_782_);
lean_dec(v_j_782_);
switch(lean_obj_tag(v___x_783_))
{
case 0:
{
lean_object* v_key_784_; lean_object* v_val_785_; uint8_t v___x_786_; 
v_key_784_ = lean_ctor_get(v___x_783_, 0);
v_val_785_ = lean_ctor_get(v___x_783_, 1);
v___x_786_ = l_Lean_instBEqHeadIndex_beq(v_x_777_, v_key_784_);
if (v___x_786_ == 0)
{
lean_object* v___x_787_; 
v___x_787_ = lean_box(0);
return v___x_787_;
}
else
{
lean_object* v___x_788_; 
lean_inc(v_val_785_);
v___x_788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_788_, 0, v_val_785_);
return v___x_788_;
}
}
case 1:
{
lean_object* v_node_789_; size_t v___x_790_; size_t v___x_791_; 
v_node_789_ = lean_ctor_get(v___x_783_, 0);
v___x_790_ = ((size_t)5ULL);
v___x_791_ = lean_usize_shift_right(v_x_776_, v___x_790_);
v_x_775_ = v_node_789_;
v_x_776_ = v___x_791_;
goto _start;
}
default: 
{
lean_object* v___x_793_; 
v___x_793_ = lean_box(0);
return v___x_793_;
}
}
}
else
{
lean_object* v_ks_794_; lean_object* v_vs_795_; lean_object* v___x_796_; lean_object* v___x_797_; 
v_ks_794_ = lean_ctor_get(v_x_775_, 0);
v_vs_795_ = lean_ctor_get(v_x_775_, 1);
v___x_796_ = lean_unsigned_to_nat(0u);
v___x_797_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1_spec__2___redArg(v_ks_794_, v_vs_795_, v___x_796_, v_x_777_);
return v___x_797_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1___redArg___boxed(lean_object* v_x_798_, lean_object* v_x_799_, lean_object* v_x_800_){
_start:
{
size_t v_x_9897__boxed_801_; lean_object* v_res_802_; 
v_x_9897__boxed_801_ = lean_unbox_usize(v_x_799_);
lean_dec(v_x_799_);
v_res_802_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1___redArg(v_x_798_, v_x_9897__boxed_801_, v_x_800_);
lean_dec(v_x_800_);
lean_dec_ref(v_x_798_);
return v_res_802_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1___redArg(lean_object* v_x_803_, lean_object* v_x_804_){
_start:
{
uint64_t v___x_805_; size_t v___x_806_; lean_object* v___x_807_; 
v___x_805_ = l_Lean_HeadIndex_hash(v_x_804_);
v___x_806_ = lean_uint64_to_usize(v___x_805_);
v___x_807_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1___redArg(v_x_803_, v___x_806_, v_x_804_);
return v___x_807_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1___redArg___boxed(lean_object* v_x_808_, lean_object* v_x_809_){
_start:
{
lean_object* v_res_810_; 
v_res_810_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1___redArg(v_x_808_, v_x_809_);
lean_dec(v_x_809_);
lean_dec_ref(v_x_808_);
return v_res_810_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__0___redArg(lean_object* v_f_811_, lean_object* v_as_x27_812_, lean_object* v_b_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_){
_start:
{
if (lean_obj_tag(v_as_x27_812_) == 0)
{
lean_object* v___x_825_; 
v___x_825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_825_, 0, v_b_813_);
return v___x_825_;
}
else
{
lean_object* v_head_826_; lean_object* v_tail_827_; lean_object* v___x_828_; uint8_t v___y_830_; uint8_t v___x_834_; 
v_head_826_ = lean_ctor_get(v_as_x27_812_, 0);
v_tail_827_ = lean_ctor_get(v_as_x27_812_, 1);
v___x_828_ = lean_box(0);
v___x_834_ = l_Lean_Expr_isApp(v_head_826_);
if (v___x_834_ == 0)
{
v___y_830_ = v___x_834_;
goto v___jp_829_;
}
else
{
lean_object* v___x_835_; size_t v___x_836_; size_t v___x_837_; uint8_t v___x_838_; 
v___x_835_ = l_Lean_Expr_appFn_x21(v_head_826_);
v___x_836_ = lean_ptr_addr(v___x_835_);
lean_dec_ref(v___x_835_);
v___x_837_ = lean_ptr_addr(v_f_811_);
v___x_838_ = lean_usize_dec_eq(v___x_836_, v___x_837_);
v___y_830_ = v___x_838_;
goto v___jp_829_;
}
v___jp_829_:
{
if (v___y_830_ == 0)
{
v_as_x27_812_ = v_tail_827_;
v_b_813_ = v___x_828_;
goto _start;
}
else
{
lean_object* v___x_832_; 
lean_inc(v_head_826_);
v___x_832_ = l_Lean_Meta_Grind_mkInjEq(v_head_826_, v___y_814_, v___y_815_, v___y_816_, v___y_817_, v___y_818_, v___y_819_, v___y_820_, v___y_821_, v___y_822_, v___y_823_);
if (lean_obj_tag(v___x_832_) == 0)
{
lean_dec_ref_known(v___x_832_, 1);
v_as_x27_812_ = v_tail_827_;
v_b_813_ = v___x_828_;
goto _start;
}
else
{
return v___x_832_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__0___redArg___boxed(lean_object* v_f_839_, lean_object* v_as_x27_840_, lean_object* v_b_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_){
_start:
{
lean_object* v_res_853_; 
v_res_853_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__0___redArg(v_f_839_, v_as_x27_840_, v_b_841_, v___y_842_, v___y_843_, v___y_844_, v___y_845_, v___y_846_, v___y_847_, v___y_848_, v___y_849_, v___y_850_, v___y_851_);
lean_dec(v___y_851_);
lean_dec_ref(v___y_850_);
lean_dec(v___y_849_);
lean_dec_ref(v___y_848_);
lean_dec(v___y_847_);
lean_dec_ref(v___y_846_);
lean_dec(v___y_845_);
lean_dec_ref(v___y_844_);
lean_dec(v___y_843_);
lean_dec(v___y_842_);
lean_dec(v_as_x27_840_);
lean_dec_ref(v_f_839_);
return v_res_853_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn(lean_object* v_us_854_, lean_object* v_00_u03b1_855_, lean_object* v_00_u03b2_856_, lean_object* v_f_857_, lean_object* v_h_858_, lean_object* v_a_859_, lean_object* v_a_860_, lean_object* v_a_861_, lean_object* v_a_862_, lean_object* v_a_863_, lean_object* v_a_864_, lean_object* v_a_865_, lean_object* v_a_866_, lean_object* v_a_867_, lean_object* v_a_868_){
_start:
{
lean_object* v___x_870_; lean_object* v_toGoalState_871_; lean_object* v_inj_872_; lean_object* v_mvarId_873_; lean_object* v___x_875_; uint8_t v_isShared_876_; uint8_t v_isSharedCheck_937_; 
v___x_870_ = lean_st_ref_take(v_a_859_);
v_toGoalState_871_ = lean_ctor_get(v___x_870_, 0);
lean_inc_ref(v_toGoalState_871_);
v_inj_872_ = lean_ctor_get(v_toGoalState_871_, 13);
lean_inc_ref(v_inj_872_);
v_mvarId_873_ = lean_ctor_get(v___x_870_, 1);
v_isSharedCheck_937_ = !lean_is_exclusive(v___x_870_);
if (v_isSharedCheck_937_ == 0)
{
lean_object* v_unused_938_; 
v_unused_938_ = lean_ctor_get(v___x_870_, 0);
lean_dec(v_unused_938_);
v___x_875_ = v___x_870_;
v_isShared_876_ = v_isSharedCheck_937_;
goto v_resetjp_874_;
}
else
{
lean_inc(v_mvarId_873_);
lean_dec(v___x_870_);
v___x_875_ = lean_box(0);
v_isShared_876_ = v_isSharedCheck_937_;
goto v_resetjp_874_;
}
v_resetjp_874_:
{
lean_object* v_nextDeclIdx_877_; lean_object* v_enodeMap_878_; lean_object* v_exprs_879_; lean_object* v_parents_880_; lean_object* v_congrTable_881_; lean_object* v_appMap_882_; lean_object* v_indicesFound_883_; lean_object* v_newFacts_884_; uint8_t v_inconsistent_885_; lean_object* v_nextIdx_886_; lean_object* v_newRawFacts_887_; lean_object* v_facts_888_; lean_object* v_extThms_889_; lean_object* v_ematch_890_; lean_object* v_split_891_; lean_object* v_clean_892_; lean_object* v_sstates_893_; lean_object* v___x_895_; uint8_t v_isShared_896_; uint8_t v_isSharedCheck_935_; 
v_nextDeclIdx_877_ = lean_ctor_get(v_toGoalState_871_, 0);
v_enodeMap_878_ = lean_ctor_get(v_toGoalState_871_, 1);
v_exprs_879_ = lean_ctor_get(v_toGoalState_871_, 2);
v_parents_880_ = lean_ctor_get(v_toGoalState_871_, 3);
v_congrTable_881_ = lean_ctor_get(v_toGoalState_871_, 4);
v_appMap_882_ = lean_ctor_get(v_toGoalState_871_, 5);
v_indicesFound_883_ = lean_ctor_get(v_toGoalState_871_, 6);
v_newFacts_884_ = lean_ctor_get(v_toGoalState_871_, 7);
v_inconsistent_885_ = lean_ctor_get_uint8(v_toGoalState_871_, sizeof(void*)*17);
v_nextIdx_886_ = lean_ctor_get(v_toGoalState_871_, 8);
v_newRawFacts_887_ = lean_ctor_get(v_toGoalState_871_, 9);
v_facts_888_ = lean_ctor_get(v_toGoalState_871_, 10);
v_extThms_889_ = lean_ctor_get(v_toGoalState_871_, 11);
v_ematch_890_ = lean_ctor_get(v_toGoalState_871_, 12);
v_split_891_ = lean_ctor_get(v_toGoalState_871_, 14);
v_clean_892_ = lean_ctor_get(v_toGoalState_871_, 15);
v_sstates_893_ = lean_ctor_get(v_toGoalState_871_, 16);
v_isSharedCheck_935_ = !lean_is_exclusive(v_toGoalState_871_);
if (v_isSharedCheck_935_ == 0)
{
lean_object* v_unused_936_; 
v_unused_936_ = lean_ctor_get(v_toGoalState_871_, 13);
lean_dec(v_unused_936_);
v___x_895_ = v_toGoalState_871_;
v_isShared_896_ = v_isSharedCheck_935_;
goto v_resetjp_894_;
}
else
{
lean_inc(v_sstates_893_);
lean_inc(v_clean_892_);
lean_inc(v_split_891_);
lean_inc(v_ematch_890_);
lean_inc(v_extThms_889_);
lean_inc(v_facts_888_);
lean_inc(v_newRawFacts_887_);
lean_inc(v_nextIdx_886_);
lean_inc(v_newFacts_884_);
lean_inc(v_indicesFound_883_);
lean_inc(v_appMap_882_);
lean_inc(v_congrTable_881_);
lean_inc(v_parents_880_);
lean_inc(v_exprs_879_);
lean_inc(v_enodeMap_878_);
lean_inc(v_nextDeclIdx_877_);
lean_dec(v_toGoalState_871_);
v___x_895_ = lean_box(0);
v_isShared_896_ = v_isSharedCheck_935_;
goto v_resetjp_894_;
}
v_resetjp_894_:
{
lean_object* v_thms_897_; lean_object* v_fns_898_; lean_object* v___x_900_; uint8_t v_isShared_901_; uint8_t v_isSharedCheck_934_; 
v_thms_897_ = lean_ctor_get(v_inj_872_, 0);
v_fns_898_ = lean_ctor_get(v_inj_872_, 1);
v_isSharedCheck_934_ = !lean_is_exclusive(v_inj_872_);
if (v_isSharedCheck_934_ == 0)
{
v___x_900_ = v_inj_872_;
v_isShared_901_ = v_isSharedCheck_934_;
goto v_resetjp_899_;
}
else
{
lean_inc(v_fns_898_);
lean_inc(v_thms_897_);
lean_dec(v_inj_872_);
v___x_900_ = lean_box(0);
v_isShared_901_ = v_isSharedCheck_934_;
goto v_resetjp_899_;
}
v_resetjp_899_:
{
lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_906_; 
v___x_902_ = lean_box(0);
v___x_903_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_903_, 0, v_us_854_);
lean_ctor_set(v___x_903_, 1, v_00_u03b1_855_);
lean_ctor_set(v___x_903_, 2, v_00_u03b2_856_);
lean_ctor_set(v___x_903_, 3, v_h_858_);
lean_ctor_set(v___x_903_, 4, v___x_902_);
lean_inc_ref(v_f_857_);
v___x_904_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2___redArg(v_fns_898_, v_f_857_, v___x_903_);
if (v_isShared_901_ == 0)
{
lean_ctor_set(v___x_900_, 1, v___x_904_);
v___x_906_ = v___x_900_;
goto v_reusejp_905_;
}
else
{
lean_object* v_reuseFailAlloc_933_; 
v_reuseFailAlloc_933_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_933_, 0, v_thms_897_);
lean_ctor_set(v_reuseFailAlloc_933_, 1, v___x_904_);
v___x_906_ = v_reuseFailAlloc_933_;
goto v_reusejp_905_;
}
v_reusejp_905_:
{
lean_object* v___x_908_; 
if (v_isShared_896_ == 0)
{
lean_ctor_set(v___x_895_, 13, v___x_906_);
v___x_908_ = v___x_895_;
goto v_reusejp_907_;
}
else
{
lean_object* v_reuseFailAlloc_932_; 
v_reuseFailAlloc_932_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_932_, 0, v_nextDeclIdx_877_);
lean_ctor_set(v_reuseFailAlloc_932_, 1, v_enodeMap_878_);
lean_ctor_set(v_reuseFailAlloc_932_, 2, v_exprs_879_);
lean_ctor_set(v_reuseFailAlloc_932_, 3, v_parents_880_);
lean_ctor_set(v_reuseFailAlloc_932_, 4, v_congrTable_881_);
lean_ctor_set(v_reuseFailAlloc_932_, 5, v_appMap_882_);
lean_ctor_set(v_reuseFailAlloc_932_, 6, v_indicesFound_883_);
lean_ctor_set(v_reuseFailAlloc_932_, 7, v_newFacts_884_);
lean_ctor_set(v_reuseFailAlloc_932_, 8, v_nextIdx_886_);
lean_ctor_set(v_reuseFailAlloc_932_, 9, v_newRawFacts_887_);
lean_ctor_set(v_reuseFailAlloc_932_, 10, v_facts_888_);
lean_ctor_set(v_reuseFailAlloc_932_, 11, v_extThms_889_);
lean_ctor_set(v_reuseFailAlloc_932_, 12, v_ematch_890_);
lean_ctor_set(v_reuseFailAlloc_932_, 13, v___x_906_);
lean_ctor_set(v_reuseFailAlloc_932_, 14, v_split_891_);
lean_ctor_set(v_reuseFailAlloc_932_, 15, v_clean_892_);
lean_ctor_set(v_reuseFailAlloc_932_, 16, v_sstates_893_);
lean_ctor_set_uint8(v_reuseFailAlloc_932_, sizeof(void*)*17, v_inconsistent_885_);
v___x_908_ = v_reuseFailAlloc_932_;
goto v_reusejp_907_;
}
v_reusejp_907_:
{
lean_object* v___x_910_; 
if (v_isShared_876_ == 0)
{
lean_ctor_set(v___x_875_, 0, v___x_908_);
v___x_910_ = v___x_875_;
goto v_reusejp_909_;
}
else
{
lean_object* v_reuseFailAlloc_931_; 
v_reuseFailAlloc_931_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_931_, 0, v___x_908_);
lean_ctor_set(v_reuseFailAlloc_931_, 1, v_mvarId_873_);
v___x_910_ = v_reuseFailAlloc_931_;
goto v_reusejp_909_;
}
v_reusejp_909_:
{
lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___y_914_; lean_object* v_toGoalState_925_; lean_object* v_appMap_926_; lean_object* v___x_927_; lean_object* v___x_928_; 
v___x_911_ = lean_st_ref_set(v_a_859_, v___x_910_);
v___x_912_ = lean_st_ref_get(v_a_859_);
v_toGoalState_925_ = lean_ctor_get(v___x_912_, 0);
lean_inc_ref(v_toGoalState_925_);
lean_dec(v___x_912_);
v_appMap_926_ = lean_ctor_get(v_toGoalState_925_, 5);
lean_inc_ref(v_appMap_926_);
lean_dec_ref(v_toGoalState_925_);
lean_inc_ref(v_f_857_);
v___x_927_ = l_Lean_Expr_toHeadIndex(v_f_857_);
v___x_928_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1___redArg(v_appMap_926_, v___x_927_);
lean_dec(v___x_927_);
lean_dec_ref(v_appMap_926_);
if (lean_obj_tag(v___x_928_) == 0)
{
lean_object* v___x_929_; 
v___x_929_ = lean_box(0);
v___y_914_ = v___x_929_;
goto v___jp_913_;
}
else
{
lean_object* v_val_930_; 
v_val_930_ = lean_ctor_get(v___x_928_, 0);
lean_inc(v_val_930_);
lean_dec_ref_known(v___x_928_, 1);
v___y_914_ = v_val_930_;
goto v___jp_913_;
}
v___jp_913_:
{
lean_object* v___x_915_; lean_object* v___x_916_; 
v___x_915_ = lean_box(0);
v___x_916_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__0___redArg(v_f_857_, v___y_914_, v___x_915_, v_a_859_, v_a_860_, v_a_861_, v_a_862_, v_a_863_, v_a_864_, v_a_865_, v_a_866_, v_a_867_, v_a_868_);
lean_dec(v___y_914_);
lean_dec_ref(v_f_857_);
if (lean_obj_tag(v___x_916_) == 0)
{
lean_object* v___x_918_; uint8_t v_isShared_919_; uint8_t v_isSharedCheck_923_; 
v_isSharedCheck_923_ = !lean_is_exclusive(v___x_916_);
if (v_isSharedCheck_923_ == 0)
{
lean_object* v_unused_924_; 
v_unused_924_ = lean_ctor_get(v___x_916_, 0);
lean_dec(v_unused_924_);
v___x_918_ = v___x_916_;
v_isShared_919_ = v_isSharedCheck_923_;
goto v_resetjp_917_;
}
else
{
lean_dec(v___x_916_);
v___x_918_ = lean_box(0);
v_isShared_919_ = v_isSharedCheck_923_;
goto v_resetjp_917_;
}
v_resetjp_917_:
{
lean_object* v___x_921_; 
if (v_isShared_919_ == 0)
{
lean_ctor_set(v___x_918_, 0, v___x_915_);
v___x_921_ = v___x_918_;
goto v_reusejp_920_;
}
else
{
lean_object* v_reuseFailAlloc_922_; 
v_reuseFailAlloc_922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_922_, 0, v___x_915_);
v___x_921_ = v_reuseFailAlloc_922_;
goto v_reusejp_920_;
}
v_reusejp_920_:
{
return v___x_921_;
}
}
}
else
{
return v___x_916_;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn___boxed(lean_object* v_us_939_, lean_object* v_00_u03b1_940_, lean_object* v_00_u03b2_941_, lean_object* v_f_942_, lean_object* v_h_943_, lean_object* v_a_944_, lean_object* v_a_945_, lean_object* v_a_946_, lean_object* v_a_947_, lean_object* v_a_948_, lean_object* v_a_949_, lean_object* v_a_950_, lean_object* v_a_951_, lean_object* v_a_952_, lean_object* v_a_953_, lean_object* v_a_954_){
_start:
{
lean_object* v_res_955_; 
v_res_955_ = l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn(v_us_939_, v_00_u03b1_940_, v_00_u03b2_941_, v_f_942_, v_h_943_, v_a_944_, v_a_945_, v_a_946_, v_a_947_, v_a_948_, v_a_949_, v_a_950_, v_a_951_, v_a_952_, v_a_953_);
lean_dec(v_a_953_);
lean_dec_ref(v_a_952_);
lean_dec(v_a_951_);
lean_dec_ref(v_a_950_);
lean_dec(v_a_949_);
lean_dec_ref(v_a_948_);
lean_dec(v_a_947_);
lean_dec_ref(v_a_946_);
lean_dec(v_a_945_);
lean_dec(v_a_944_);
return v_res_955_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__0(lean_object* v_f_956_, lean_object* v_as_957_, lean_object* v_as_x27_958_, lean_object* v_b_959_, lean_object* v_a_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_){
_start:
{
lean_object* v___x_972_; 
v___x_972_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__0___redArg(v_f_956_, v_as_x27_958_, v_b_959_, v___y_961_, v___y_962_, v___y_963_, v___y_964_, v___y_965_, v___y_966_, v___y_967_, v___y_968_, v___y_969_, v___y_970_);
return v___x_972_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__0___boxed(lean_object* v_f_973_, lean_object* v_as_974_, lean_object* v_as_x27_975_, lean_object* v_b_976_, lean_object* v_a_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_){
_start:
{
lean_object* v_res_989_; 
v_res_989_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__0(v_f_973_, v_as_974_, v_as_x27_975_, v_b_976_, v_a_977_, v___y_978_, v___y_979_, v___y_980_, v___y_981_, v___y_982_, v___y_983_, v___y_984_, v___y_985_, v___y_986_, v___y_987_);
lean_dec(v___y_987_);
lean_dec_ref(v___y_986_);
lean_dec(v___y_985_);
lean_dec_ref(v___y_984_);
lean_dec(v___y_983_);
lean_dec_ref(v___y_982_);
lean_dec(v___y_981_);
lean_dec_ref(v___y_980_);
lean_dec(v___y_979_);
lean_dec(v___y_978_);
lean_dec(v_as_x27_975_);
lean_dec(v_as_974_);
lean_dec_ref(v_f_973_);
return v_res_989_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1(lean_object* v_00_u03b2_990_, lean_object* v_x_991_, lean_object* v_x_992_){
_start:
{
lean_object* v___x_993_; 
v___x_993_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1___redArg(v_x_991_, v_x_992_);
return v___x_993_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1___boxed(lean_object* v_00_u03b2_994_, lean_object* v_x_995_, lean_object* v_x_996_){
_start:
{
lean_object* v_res_997_; 
v_res_997_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1(v_00_u03b2_994_, v_x_995_, v_x_996_);
lean_dec(v_x_996_);
lean_dec_ref(v_x_995_);
return v_res_997_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1(lean_object* v_00_u03b2_998_, lean_object* v_x_999_, size_t v_x_1000_, lean_object* v_x_1001_){
_start:
{
lean_object* v___x_1002_; 
v___x_1002_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1___redArg(v_x_999_, v_x_1000_, v_x_1001_);
return v___x_1002_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1___boxed(lean_object* v_00_u03b2_1003_, lean_object* v_x_1004_, lean_object* v_x_1005_, lean_object* v_x_1006_){
_start:
{
size_t v_x_10160__boxed_1007_; lean_object* v_res_1008_; 
v_x_10160__boxed_1007_ = lean_unbox_usize(v_x_1005_);
lean_dec(v_x_1005_);
v_res_1008_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1(v_00_u03b2_1003_, v_x_1004_, v_x_10160__boxed_1007_, v_x_1006_);
lean_dec(v_x_1006_);
lean_dec_ref(v_x_1004_);
return v_res_1008_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_1009_, lean_object* v_keys_1010_, lean_object* v_vals_1011_, lean_object* v_heq_1012_, lean_object* v_i_1013_, lean_object* v_k_1014_){
_start:
{
lean_object* v___x_1015_; 
v___x_1015_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1_spec__2___redArg(v_keys_1010_, v_vals_1011_, v_i_1013_, v_k_1014_);
return v___x_1015_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1016_, lean_object* v_keys_1017_, lean_object* v_vals_1018_, lean_object* v_heq_1019_, lean_object* v_i_1020_, lean_object* v_k_1021_){
_start:
{
lean_object* v_res_1022_; 
v_res_1022_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1_spec__2(v_00_u03b2_1016_, v_keys_1017_, v_vals_1018_, v_heq_1019_, v_i_1020_, v_k_1021_);
lean_dec(v_k_1021_);
lean_dec_ref(v_vals_1018_);
lean_dec_ref(v_keys_1017_);
return v_res_1022_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj(lean_object* v_e_1028_, lean_object* v_a_1029_, lean_object* v_a_1030_, lean_object* v_a_1031_, lean_object* v_a_1032_, lean_object* v_a_1033_, lean_object* v_a_1034_, lean_object* v_a_1035_, lean_object* v_a_1036_, lean_object* v_a_1037_, lean_object* v_a_1038_){
_start:
{
lean_object* v___x_1043_; uint8_t v___x_1044_; 
lean_inc_ref(v_e_1028_);
v___x_1043_ = l_Lean_Expr_cleanupAnnotations(v_e_1028_);
v___x_1044_ = l_Lean_Expr_isApp(v___x_1043_);
if (v___x_1044_ == 0)
{
lean_dec_ref(v___x_1043_);
lean_dec_ref(v_e_1028_);
goto v___jp_1040_;
}
else
{
lean_object* v_arg_1045_; lean_object* v___x_1046_; uint8_t v___x_1047_; 
v_arg_1045_ = lean_ctor_get(v___x_1043_, 1);
lean_inc_ref(v_arg_1045_);
v___x_1046_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1043_);
v___x_1047_ = l_Lean_Expr_isApp(v___x_1046_);
if (v___x_1047_ == 0)
{
lean_dec_ref(v___x_1046_);
lean_dec_ref(v_arg_1045_);
lean_dec_ref(v_e_1028_);
goto v___jp_1040_;
}
else
{
lean_object* v_arg_1048_; lean_object* v___x_1049_; uint8_t v___x_1050_; 
v_arg_1048_ = lean_ctor_get(v___x_1046_, 1);
lean_inc_ref(v_arg_1048_);
v___x_1049_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1046_);
v___x_1050_ = l_Lean_Expr_isApp(v___x_1049_);
if (v___x_1050_ == 0)
{
lean_dec_ref(v___x_1049_);
lean_dec_ref(v_arg_1048_);
lean_dec_ref(v_arg_1045_);
lean_dec_ref(v_e_1028_);
goto v___jp_1040_;
}
else
{
lean_object* v_arg_1051_; lean_object* v___x_1052_; lean_object* v_f_1054_; lean_object* v___y_1055_; lean_object* v___y_1056_; lean_object* v___y_1057_; lean_object* v___y_1058_; lean_object* v___y_1059_; lean_object* v___y_1060_; lean_object* v___y_1061_; lean_object* v___y_1062_; lean_object* v___y_1063_; lean_object* v___y_1064_; lean_object* v___x_1078_; uint8_t v___x_1079_; 
v_arg_1051_ = lean_ctor_get(v___x_1049_, 1);
lean_inc_ref(v_arg_1051_);
v___x_1052_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1049_);
v___x_1078_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj___closed__2));
v___x_1079_ = l_Lean_Expr_isConstOf(v___x_1052_, v___x_1078_);
if (v___x_1079_ == 0)
{
lean_dec_ref(v___x_1052_);
lean_dec_ref(v_arg_1051_);
lean_dec_ref(v_arg_1048_);
lean_dec_ref(v_arg_1045_);
lean_dec_ref(v_e_1028_);
goto v___jp_1040_;
}
else
{
lean_object* v___x_1080_; 
lean_inc_ref(v_e_1028_);
v___x_1080_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_e_1028_, v_a_1029_, v_a_1033_, v_a_1035_, v_a_1036_, v_a_1037_, v_a_1038_);
if (lean_obj_tag(v___x_1080_) == 0)
{
lean_object* v_a_1081_; lean_object* v___x_1083_; uint8_t v_isShared_1084_; uint8_t v_isSharedCheck_1116_; 
v_a_1081_ = lean_ctor_get(v___x_1080_, 0);
v_isSharedCheck_1116_ = !lean_is_exclusive(v___x_1080_);
if (v_isSharedCheck_1116_ == 0)
{
v___x_1083_ = v___x_1080_;
v_isShared_1084_ = v_isSharedCheck_1116_;
goto v_resetjp_1082_;
}
else
{
lean_inc(v_a_1081_);
lean_dec(v___x_1080_);
v___x_1083_ = lean_box(0);
v_isShared_1084_ = v_isSharedCheck_1116_;
goto v_resetjp_1082_;
}
v_resetjp_1082_:
{
uint8_t v___x_1085_; 
v___x_1085_ = lean_unbox(v_a_1081_);
lean_dec(v_a_1081_);
if (v___x_1085_ == 0)
{
lean_object* v___x_1086_; lean_object* v___x_1088_; 
lean_dec_ref(v___x_1052_);
lean_dec_ref(v_arg_1051_);
lean_dec_ref(v_arg_1048_);
lean_dec_ref(v_arg_1045_);
lean_dec_ref(v_e_1028_);
v___x_1086_ = lean_box(0);
if (v_isShared_1084_ == 0)
{
lean_ctor_set(v___x_1083_, 0, v___x_1086_);
v___x_1088_ = v___x_1083_;
goto v_reusejp_1087_;
}
else
{
lean_object* v_reuseFailAlloc_1089_; 
v_reuseFailAlloc_1089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1089_, 0, v___x_1086_);
v___x_1088_ = v_reuseFailAlloc_1089_;
goto v_reusejp_1087_;
}
v_reusejp_1087_:
{
return v___x_1088_;
}
}
else
{
lean_object* v___x_1090_; size_t v___x_1091_; size_t v___x_1092_; uint8_t v___x_1093_; 
lean_del_object(v___x_1083_);
lean_inc_ref(v_arg_1045_);
v___x_1090_ = l_Lean_Expr_eta(v_arg_1045_);
v___x_1091_ = lean_ptr_addr(v_arg_1045_);
v___x_1092_ = lean_ptr_addr(v___x_1090_);
v___x_1093_ = lean_usize_dec_eq(v___x_1091_, v___x_1092_);
if (v___x_1093_ == 0)
{
lean_object* v___x_1094_; 
lean_dec_ref(v_arg_1045_);
v___x_1094_ = l_Lean_Meta_Grind_preprocessLight___redArg(v___x_1090_, v_a_1030_, v_a_1031_, v_a_1032_, v_a_1033_, v_a_1034_, v_a_1035_, v_a_1036_, v_a_1037_, v_a_1038_);
if (lean_obj_tag(v___x_1094_) == 0)
{
lean_object* v_a_1095_; lean_object* v___x_1096_; 
v_a_1095_ = lean_ctor_get(v___x_1094_, 0);
lean_inc(v_a_1095_);
lean_dec_ref_known(v___x_1094_, 1);
v___x_1096_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_1028_, v_a_1029_);
if (lean_obj_tag(v___x_1096_) == 0)
{
lean_object* v_a_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; 
v_a_1097_ = lean_ctor_get(v___x_1096_, 0);
lean_inc(v_a_1097_);
lean_dec_ref_known(v___x_1096_, 1);
v___x_1098_ = lean_box(0);
lean_inc(v_a_1038_);
lean_inc_ref(v_a_1037_);
lean_inc(v_a_1036_);
lean_inc_ref(v_a_1035_);
lean_inc(v_a_1034_);
lean_inc_ref(v_a_1033_);
lean_inc(v_a_1032_);
lean_inc_ref(v_a_1031_);
lean_inc(v_a_1030_);
lean_inc(v_a_1029_);
lean_inc(v_a_1095_);
v___x_1099_ = lean_grind_internalize(v_a_1095_, v_a_1097_, v___x_1098_, v_a_1029_, v_a_1030_, v_a_1031_, v_a_1032_, v_a_1033_, v_a_1034_, v_a_1035_, v_a_1036_, v_a_1037_, v_a_1038_);
if (lean_obj_tag(v___x_1099_) == 0)
{
lean_dec_ref_known(v___x_1099_, 1);
v_f_1054_ = v_a_1095_;
v___y_1055_ = v_a_1029_;
v___y_1056_ = v_a_1030_;
v___y_1057_ = v_a_1031_;
v___y_1058_ = v_a_1032_;
v___y_1059_ = v_a_1033_;
v___y_1060_ = v_a_1034_;
v___y_1061_ = v_a_1035_;
v___y_1062_ = v_a_1036_;
v___y_1063_ = v_a_1037_;
v___y_1064_ = v_a_1038_;
goto v___jp_1053_;
}
else
{
lean_dec(v_a_1095_);
lean_dec_ref(v___x_1052_);
lean_dec_ref(v_arg_1051_);
lean_dec_ref(v_arg_1048_);
lean_dec_ref(v_e_1028_);
return v___x_1099_;
}
}
else
{
lean_object* v_a_1100_; lean_object* v___x_1102_; uint8_t v_isShared_1103_; uint8_t v_isSharedCheck_1107_; 
lean_dec(v_a_1095_);
lean_dec_ref(v___x_1052_);
lean_dec_ref(v_arg_1051_);
lean_dec_ref(v_arg_1048_);
lean_dec_ref(v_e_1028_);
v_a_1100_ = lean_ctor_get(v___x_1096_, 0);
v_isSharedCheck_1107_ = !lean_is_exclusive(v___x_1096_);
if (v_isSharedCheck_1107_ == 0)
{
v___x_1102_ = v___x_1096_;
v_isShared_1103_ = v_isSharedCheck_1107_;
goto v_resetjp_1101_;
}
else
{
lean_inc(v_a_1100_);
lean_dec(v___x_1096_);
v___x_1102_ = lean_box(0);
v_isShared_1103_ = v_isSharedCheck_1107_;
goto v_resetjp_1101_;
}
v_resetjp_1101_:
{
lean_object* v___x_1105_; 
if (v_isShared_1103_ == 0)
{
v___x_1105_ = v___x_1102_;
goto v_reusejp_1104_;
}
else
{
lean_object* v_reuseFailAlloc_1106_; 
v_reuseFailAlloc_1106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1106_, 0, v_a_1100_);
v___x_1105_ = v_reuseFailAlloc_1106_;
goto v_reusejp_1104_;
}
v_reusejp_1104_:
{
return v___x_1105_;
}
}
}
}
else
{
lean_object* v_a_1108_; lean_object* v___x_1110_; uint8_t v_isShared_1111_; uint8_t v_isSharedCheck_1115_; 
lean_dec_ref(v___x_1052_);
lean_dec_ref(v_arg_1051_);
lean_dec_ref(v_arg_1048_);
lean_dec_ref(v_e_1028_);
v_a_1108_ = lean_ctor_get(v___x_1094_, 0);
v_isSharedCheck_1115_ = !lean_is_exclusive(v___x_1094_);
if (v_isSharedCheck_1115_ == 0)
{
v___x_1110_ = v___x_1094_;
v_isShared_1111_ = v_isSharedCheck_1115_;
goto v_resetjp_1109_;
}
else
{
lean_inc(v_a_1108_);
lean_dec(v___x_1094_);
v___x_1110_ = lean_box(0);
v_isShared_1111_ = v_isSharedCheck_1115_;
goto v_resetjp_1109_;
}
v_resetjp_1109_:
{
lean_object* v___x_1113_; 
if (v_isShared_1111_ == 0)
{
v___x_1113_ = v___x_1110_;
goto v_reusejp_1112_;
}
else
{
lean_object* v_reuseFailAlloc_1114_; 
v_reuseFailAlloc_1114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1114_, 0, v_a_1108_);
v___x_1113_ = v_reuseFailAlloc_1114_;
goto v_reusejp_1112_;
}
v_reusejp_1112_:
{
return v___x_1113_;
}
}
}
}
else
{
lean_dec_ref(v___x_1090_);
v_f_1054_ = v_arg_1045_;
v___y_1055_ = v_a_1029_;
v___y_1056_ = v_a_1030_;
v___y_1057_ = v_a_1031_;
v___y_1058_ = v_a_1032_;
v___y_1059_ = v_a_1033_;
v___y_1060_ = v_a_1034_;
v___y_1061_ = v_a_1035_;
v___y_1062_ = v_a_1036_;
v___y_1063_ = v_a_1037_;
v___y_1064_ = v_a_1038_;
goto v___jp_1053_;
}
}
}
}
else
{
lean_object* v_a_1117_; lean_object* v___x_1119_; uint8_t v_isShared_1120_; uint8_t v_isSharedCheck_1124_; 
lean_dec_ref(v___x_1052_);
lean_dec_ref(v_arg_1051_);
lean_dec_ref(v_arg_1048_);
lean_dec_ref(v_arg_1045_);
lean_dec_ref(v_e_1028_);
v_a_1117_ = lean_ctor_get(v___x_1080_, 0);
v_isSharedCheck_1124_ = !lean_is_exclusive(v___x_1080_);
if (v_isSharedCheck_1124_ == 0)
{
v___x_1119_ = v___x_1080_;
v_isShared_1120_ = v_isSharedCheck_1124_;
goto v_resetjp_1118_;
}
else
{
lean_inc(v_a_1117_);
lean_dec(v___x_1080_);
v___x_1119_ = lean_box(0);
v_isShared_1120_ = v_isSharedCheck_1124_;
goto v_resetjp_1118_;
}
v_resetjp_1118_:
{
lean_object* v___x_1122_; 
if (v_isShared_1120_ == 0)
{
v___x_1122_ = v___x_1119_;
goto v_reusejp_1121_;
}
else
{
lean_object* v_reuseFailAlloc_1123_; 
v_reuseFailAlloc_1123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1123_, 0, v_a_1117_);
v___x_1122_ = v_reuseFailAlloc_1123_;
goto v_reusejp_1121_;
}
v_reusejp_1121_:
{
return v___x_1122_;
}
}
}
}
v___jp_1053_:
{
lean_object* v___x_1065_; 
lean_inc_ref(v_e_1028_);
v___x_1065_ = l_Lean_Meta_Grind_mkEqTrueProof(v_e_1028_, v___y_1055_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_);
if (lean_obj_tag(v___x_1065_) == 0)
{
lean_object* v_a_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; 
v_a_1066_ = lean_ctor_get(v___x_1065_, 0);
lean_inc(v_a_1066_);
lean_dec_ref_known(v___x_1065_, 1);
v___x_1067_ = l_Lean_Expr_constLevels_x21(v___x_1052_);
lean_dec_ref(v___x_1052_);
v___x_1068_ = l_Lean_Meta_mkOfEqTrueCore(v_e_1028_, v_a_1066_);
v___x_1069_ = l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn(v___x_1067_, v_arg_1051_, v_arg_1048_, v_f_1054_, v___x_1068_, v___y_1055_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_);
return v___x_1069_;
}
else
{
lean_object* v_a_1070_; lean_object* v___x_1072_; uint8_t v_isShared_1073_; uint8_t v_isSharedCheck_1077_; 
lean_dec_ref(v_f_1054_);
lean_dec_ref(v___x_1052_);
lean_dec_ref(v_arg_1051_);
lean_dec_ref(v_arg_1048_);
lean_dec_ref(v_e_1028_);
v_a_1070_ = lean_ctor_get(v___x_1065_, 0);
v_isSharedCheck_1077_ = !lean_is_exclusive(v___x_1065_);
if (v_isSharedCheck_1077_ == 0)
{
v___x_1072_ = v___x_1065_;
v_isShared_1073_ = v_isSharedCheck_1077_;
goto v_resetjp_1071_;
}
else
{
lean_inc(v_a_1070_);
lean_dec(v___x_1065_);
v___x_1072_ = lean_box(0);
v_isShared_1073_ = v_isSharedCheck_1077_;
goto v_resetjp_1071_;
}
v_resetjp_1071_:
{
lean_object* v___x_1075_; 
if (v_isShared_1073_ == 0)
{
v___x_1075_ = v___x_1072_;
goto v_reusejp_1074_;
}
else
{
lean_object* v_reuseFailAlloc_1076_; 
v_reuseFailAlloc_1076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1076_, 0, v_a_1070_);
v___x_1075_ = v_reuseFailAlloc_1076_;
goto v_reusejp_1074_;
}
v_reusejp_1074_:
{
return v___x_1075_;
}
}
}
}
}
}
}
v___jp_1040_:
{
lean_object* v___x_1041_; lean_object* v___x_1042_; 
v___x_1041_ = lean_box(0);
v___x_1042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1042_, 0, v___x_1041_);
return v___x_1042_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj___boxed(lean_object* v_e_1125_, lean_object* v_a_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_, lean_object* v_a_1131_, lean_object* v_a_1132_, lean_object* v_a_1133_, lean_object* v_a_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_){
_start:
{
lean_object* v_res_1137_; 
v_res_1137_ = l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj(v_e_1125_, v_a_1126_, v_a_1127_, v_a_1128_, v_a_1129_, v_a_1130_, v_a_1131_, v_a_1132_, v_a_1133_, v_a_1134_, v_a_1135_);
lean_dec(v_a_1135_);
lean_dec_ref(v_a_1134_);
lean_dec(v_a_1133_);
lean_dec_ref(v_a_1132_);
lean_dec(v_a_1131_);
lean_dec_ref(v_a_1130_);
lean_dec(v_a_1129_);
lean_dec_ref(v_a_1128_);
lean_dec(v_a_1127_);
lean_dec(v_a_1126_);
return v_res_1137_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj___regBuiltin___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj_declare__1_00___x40_Lean_Meta_Tactic_Grind_PropagateInj_3930705876____hygCtx___hyg_8_(){
_start:
{
lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; 
v___x_1139_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj___closed__2));
v___x_1140_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj___boxed), 12, 0);
v___x_1141_ = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(v___x_1139_, v___x_1140_);
return v___x_1141_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj___regBuiltin___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj_declare__1_00___x40_Lean_Meta_Tactic_Grind_PropagateInj_3930705876____hygCtx___hyg_8____boxed(lean_object* v_a_1142_){
_start:
{
lean_object* v_res_1143_; 
v_res_1143_ = l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj___regBuiltin___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj_declare__1_00___x40_Lean_Meta_Tactic_Grind_PropagateInj_3930705876____hygCtx___hyg_8_();
return v_res_1143_;
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
