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
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Expr_toHeadIndex(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_instInhabitedGoalM___redArg();
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_preprocessLight___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_pushEqCore___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getGeneration___redArg(lean_object*, lean_object*);
lean_object* lean_grind_internalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj___regBuiltin___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj_declare__1_00___x40_Lean_Meta_Tactic_Grind_PropagateInj_3930705876____hygCtx___hyg_9_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj___regBuiltin___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj_declare__1_00___x40_Lean_Meta_Tactic_Grind_PropagateInj_3930705876____hygCtx___hyg_9____boxed(lean_object*);
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = l_Lean_Meta_Grind_instInhabitedGoalM___redArg();
return v___x_1_;
}
}
lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__0(lean_object* v_msg_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_, lean_object* v___y_7_, lean_object* v___y_8_, lean_object* v___y_9_, lean_object* v___y_10_, lean_object* v___y_11_, lean_object* v___y_12_){
_start:
{
lean_object* v___x_14_; lean_object* v___x_9232__overap_15_; lean_object* v___x_16_; 
v___x_14_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__0___closed__0, &l_panic___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__0___closed__0);
v___x_9232__overap_15_ = lean_panic_fn_borrowed(v___x_14_, v_msg_2_);
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
v___x_16_ = lean_apply_11(v___x_9232__overap_15_, v___y_3_, v___y_4_, v___y_5_, v___y_6_, v___y_7_, v___y_8_, v___y_9_, v___y_10_, v___y_11_, v___y_12_, lean_box(0));
return v___x_16_;
}
}
LEAN_EXPORT void l_panic___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2_ = stack[0].m_obj;
lean_object* v___y_3_ = stack[1].m_obj;
lean_object* v___y_4_ = stack[2].m_obj;
lean_object* v___y_5_ = stack[3].m_obj;
lean_object* v___y_6_ = stack[4].m_obj;
lean_object* v___y_7_ = stack[5].m_obj;
lean_object* v___y_8_ = stack[6].m_obj;
lean_object* v___y_9_ = stack[7].m_obj;
lean_object* v___y_10_ = stack[8].m_obj;
lean_object* v___y_11_ = stack[9].m_obj;
lean_object* v___y_12_ = stack[10].m_obj;
lean_object* v_res_17_;
v_res_17_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__0(v_msg_2_, v___y_3_, v___y_4_, v___y_5_, v___y_6_, v___y_7_, v___y_8_, v___y_9_, v___y_10_, v___y_11_, v___y_12_);
stack->m_obj
 = v_res_17_;
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__0___boxed(lean_object* v_msg_18_, lean_object* v___y_19_, lean_object* v___y_20_, lean_object* v___y_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_, lean_object* v___y_28_, lean_object* v___y_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__0(v_msg_18_, v___y_19_, v___y_20_, v___y_21_, v___y_22_, v___y_23_, v___y_24_, v___y_25_, v___y_26_, v___y_27_, v___y_28_);
lean_dec(v___y_28_);
lean_dec_ref(v___y_27_);
lean_dec(v___y_26_);
lean_dec_ref(v___y_25_);
lean_dec(v___y_24_);
lean_dec_ref(v___y_23_);
lean_dec(v___y_22_);
lean_dec_ref(v___y_21_);
lean_dec(v___y_20_);
lean_dec(v___y_19_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1_spec__2___redArg(lean_object* v_keys_31_, lean_object* v_vals_32_, lean_object* v_i_33_, lean_object* v_k_34_){
_start:
{
lean_object* v___x_35_; uint8_t v___x_36_; 
v___x_35_ = lean_array_get_size(v_keys_31_);
v___x_36_ = lean_nat_dec_lt(v_i_33_, v___x_35_);
if (v___x_36_ == 0)
{
lean_object* v___x_37_; 
lean_dec(v_i_33_);
v___x_37_ = lean_box(0);
return v___x_37_;
}
else
{
lean_object* v_k_x27_38_; size_t v___x_39_; size_t v___x_40_; uint8_t v___x_41_; 
v_k_x27_38_ = lean_array_fget_borrowed(v_keys_31_, v_i_33_);
v___x_39_ = lean_ptr_addr(v_k_34_);
v___x_40_ = lean_ptr_addr(v_k_x27_38_);
v___x_41_ = lean_usize_dec_eq(v___x_39_, v___x_40_);
if (v___x_41_ == 0)
{
lean_object* v___x_42_; lean_object* v___x_43_; 
v___x_42_ = lean_unsigned_to_nat(1u);
v___x_43_ = lean_nat_add(v_i_33_, v___x_42_);
lean_dec(v_i_33_);
v_i_33_ = v___x_43_;
goto _start;
}
else
{
lean_object* v___x_45_; lean_object* v___x_46_; 
v___x_45_ = lean_array_fget_borrowed(v_vals_32_, v_i_33_);
lean_dec(v_i_33_);
lean_inc(v___x_45_);
v___x_46_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_46_, 0, v___x_45_);
return v___x_46_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_keys_47_, lean_object* v_vals_48_, lean_object* v_i_49_, lean_object* v_k_50_){
_start:
{
lean_object* v_res_51_; 
v_res_51_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1_spec__2___redArg(v_keys_47_, v_vals_48_, v_i_49_, v_k_50_);
lean_dec_ref(v_k_50_);
lean_dec_ref(v_vals_48_);
lean_dec_ref(v_keys_47_);
return v_res_51_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1___redArg(lean_object* v_x_52_, size_t v_x_53_, lean_object* v_x_54_){
_start:
{
if (lean_obj_tag(v_x_52_) == 0)
{
lean_object* v_es_55_; lean_object* v___x_56_; size_t v___x_57_; size_t v___x_58_; lean_object* v_j_59_; lean_object* v___x_60_; 
v_es_55_ = lean_ctor_get(v_x_52_, 0);
v___x_56_ = lean_box(2);
v___x_57_ = ((size_t)31ULL);
v___x_58_ = lean_usize_land(v_x_53_, v___x_57_);
v_j_59_ = lean_usize_to_nat(v___x_58_);
v___x_60_ = lean_array_get_borrowed(v___x_56_, v_es_55_, v_j_59_);
lean_dec(v_j_59_);
switch(lean_obj_tag(v___x_60_))
{
case 0:
{
lean_object* v_key_61_; lean_object* v_val_62_; size_t v___x_63_; size_t v___x_64_; uint8_t v___x_65_; 
v_key_61_ = lean_ctor_get(v___x_60_, 0);
v_val_62_ = lean_ctor_get(v___x_60_, 1);
v___x_63_ = lean_ptr_addr(v_x_54_);
v___x_64_ = lean_ptr_addr(v_key_61_);
v___x_65_ = lean_usize_dec_eq(v___x_63_, v___x_64_);
if (v___x_65_ == 0)
{
lean_object* v___x_66_; 
v___x_66_ = lean_box(0);
return v___x_66_;
}
else
{
lean_object* v___x_67_; 
lean_inc(v_val_62_);
v___x_67_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_67_, 0, v_val_62_);
return v___x_67_;
}
}
case 1:
{
lean_object* v_node_68_; size_t v___x_69_; size_t v___x_70_; 
v_node_68_ = lean_ctor_get(v___x_60_, 0);
v___x_69_ = ((size_t)5ULL);
v___x_70_ = lean_usize_shift_right(v_x_53_, v___x_69_);
v_x_52_ = v_node_68_;
v_x_53_ = v___x_70_;
goto _start;
}
default: 
{
lean_object* v___x_72_; 
v___x_72_ = lean_box(0);
return v___x_72_;
}
}
}
else
{
lean_object* v_ks_73_; lean_object* v_vs_74_; lean_object* v___x_75_; lean_object* v___x_76_; 
v_ks_73_ = lean_ctor_get(v_x_52_, 0);
v_vs_74_ = lean_ctor_get(v_x_52_, 1);
v___x_75_ = lean_unsigned_to_nat(0u);
v___x_76_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1_spec__2___redArg(v_ks_73_, v_vs_74_, v___x_75_, v_x_54_);
return v___x_76_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_52_ = stack[0].m_obj;
size_t v_x_53_ = stack[1].m_num;
lean_object* v_x_54_ = stack[2].m_obj;
lean_object* v_res_77_;
v_res_77_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1___redArg(v_x_52_, v_x_53_, v_x_54_);
stack->m_obj
 = v_res_77_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1___redArg___boxed(lean_object* v_x_78_, lean_object* v_x_79_, lean_object* v_x_80_){
_start:
{
size_t v_x_9817__boxed_81_; lean_object* v_res_82_; 
v_x_9817__boxed_81_ = lean_unbox_usize(v_x_79_);
lean_dec(v_x_79_);
v_res_82_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1___redArg(v_x_78_, v_x_9817__boxed_81_, v_x_80_);
lean_dec_ref(v_x_80_);
lean_dec_ref(v_x_78_);
return v_res_82_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1___redArg(lean_object* v_x_83_, lean_object* v_x_84_){
_start:
{
size_t v___x_85_; size_t v___x_86_; size_t v___x_87_; uint64_t v___x_88_; size_t v___x_89_; lean_object* v___x_90_; 
v___x_85_ = lean_ptr_addr(v_x_84_);
v___x_86_ = ((size_t)3ULL);
v___x_87_ = lean_usize_shift_right(v___x_85_, v___x_86_);
v___x_88_ = lean_usize_to_uint64(v___x_87_);
v___x_89_ = lean_uint64_to_usize(v___x_88_);
v___x_90_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1___redArg(v_x_83_, v___x_89_, v_x_84_);
return v___x_90_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1___redArg___boxed(lean_object* v_x_91_, lean_object* v_x_92_){
_start:
{
lean_object* v_res_93_; 
v_res_93_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1___redArg(v_x_91_, v_x_92_);
lean_dec_ref(v_x_92_);
lean_dec_ref(v_x_91_);
return v_res_93_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3_spec__5_spec__6___redArg(lean_object* v_x_94_, lean_object* v_x_95_, lean_object* v_x_96_, lean_object* v_x_97_){
_start:
{
lean_object* v_ks_98_; lean_object* v_vs_99_; lean_object* v___x_101_; uint8_t v_isShared_102_; uint8_t v_isSharedCheck_125_; 
v_ks_98_ = lean_ctor_get(v_x_94_, 0);
v_vs_99_ = lean_ctor_get(v_x_94_, 1);
v_isSharedCheck_125_ = !lean_is_exclusive(v_x_94_);
if (v_isSharedCheck_125_ == 0)
{
v___x_101_ = v_x_94_;
v_isShared_102_ = v_isSharedCheck_125_;
goto v_resetjp_100_;
}
else
{
lean_inc(v_vs_99_);
lean_inc(v_ks_98_);
lean_dec(v_x_94_);
v___x_101_ = lean_box(0);
v_isShared_102_ = v_isSharedCheck_125_;
goto v_resetjp_100_;
}
v_resetjp_100_:
{
lean_object* v___x_103_; uint8_t v___x_104_; 
v___x_103_ = lean_array_get_size(v_ks_98_);
v___x_104_ = lean_nat_dec_lt(v_x_95_, v___x_103_);
if (v___x_104_ == 0)
{
lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_108_; 
lean_dec(v_x_95_);
v___x_105_ = lean_array_push(v_ks_98_, v_x_96_);
v___x_106_ = lean_array_push(v_vs_99_, v_x_97_);
if (v_isShared_102_ == 0)
{
lean_ctor_set(v___x_101_, 1, v___x_106_);
lean_ctor_set(v___x_101_, 0, v___x_105_);
v___x_108_ = v___x_101_;
goto v_reusejp_107_;
}
else
{
lean_object* v_reuseFailAlloc_109_; 
v_reuseFailAlloc_109_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_109_, 0, v___x_105_);
lean_ctor_set(v_reuseFailAlloc_109_, 1, v___x_106_);
v___x_108_ = v_reuseFailAlloc_109_;
goto v_reusejp_107_;
}
v_reusejp_107_:
{
return v___x_108_;
}
}
else
{
lean_object* v_k_x27_110_; size_t v___x_111_; size_t v___x_112_; uint8_t v___x_113_; 
v_k_x27_110_ = lean_array_fget_borrowed(v_ks_98_, v_x_95_);
v___x_111_ = lean_ptr_addr(v_x_96_);
v___x_112_ = lean_ptr_addr(v_k_x27_110_);
v___x_113_ = lean_usize_dec_eq(v___x_111_, v___x_112_);
if (v___x_113_ == 0)
{
lean_object* v___x_115_; 
if (v_isShared_102_ == 0)
{
v___x_115_ = v___x_101_;
goto v_reusejp_114_;
}
else
{
lean_object* v_reuseFailAlloc_119_; 
v_reuseFailAlloc_119_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_119_, 0, v_ks_98_);
lean_ctor_set(v_reuseFailAlloc_119_, 1, v_vs_99_);
v___x_115_ = v_reuseFailAlloc_119_;
goto v_reusejp_114_;
}
v_reusejp_114_:
{
lean_object* v___x_116_; lean_object* v___x_117_; 
v___x_116_ = lean_unsigned_to_nat(1u);
v___x_117_ = lean_nat_add(v_x_95_, v___x_116_);
lean_dec(v_x_95_);
v_x_94_ = v___x_115_;
v_x_95_ = v___x_117_;
goto _start;
}
}
else
{
lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_123_; 
v___x_120_ = lean_array_fset(v_ks_98_, v_x_95_, v_x_96_);
v___x_121_ = lean_array_fset(v_vs_99_, v_x_95_, v_x_97_);
lean_dec(v_x_95_);
if (v_isShared_102_ == 0)
{
lean_ctor_set(v___x_101_, 1, v___x_121_);
lean_ctor_set(v___x_101_, 0, v___x_120_);
v___x_123_ = v___x_101_;
goto v_reusejp_122_;
}
else
{
lean_object* v_reuseFailAlloc_124_; 
v_reuseFailAlloc_124_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_124_, 0, v___x_120_);
lean_ctor_set(v_reuseFailAlloc_124_, 1, v___x_121_);
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
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3_spec__5___redArg(lean_object* v_n_126_, lean_object* v_k_127_, lean_object* v_v_128_){
_start:
{
lean_object* v___x_129_; lean_object* v___x_130_; 
v___x_129_ = lean_unsigned_to_nat(0u);
v___x_130_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3_spec__5_spec__6___redArg(v_n_126_, v___x_129_, v_k_127_, v_v_128_);
return v___x_130_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_131_; 
v___x_131_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_131_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3___redArg(lean_object* v_x_132_, size_t v_x_133_, size_t v_x_134_, lean_object* v_x_135_, lean_object* v_x_136_){
_start:
{
if (lean_obj_tag(v_x_132_) == 0)
{
lean_object* v_es_137_; size_t v___x_138_; size_t v___x_139_; lean_object* v_j_140_; lean_object* v___x_141_; uint8_t v___x_142_; 
v_es_137_ = lean_ctor_get(v_x_132_, 0);
v___x_138_ = ((size_t)31ULL);
v___x_139_ = lean_usize_land(v_x_133_, v___x_138_);
v_j_140_ = lean_usize_to_nat(v___x_139_);
v___x_141_ = lean_array_get_size(v_es_137_);
v___x_142_ = lean_nat_dec_lt(v_j_140_, v___x_141_);
if (v___x_142_ == 0)
{
lean_dec(v_j_140_);
lean_dec(v_x_136_);
lean_dec_ref(v_x_135_);
return v_x_132_;
}
else
{
lean_object* v___x_144_; uint8_t v_isShared_145_; uint8_t v_isSharedCheck_183_; 
lean_inc_ref(v_es_137_);
v_isSharedCheck_183_ = !lean_is_exclusive(v_x_132_);
if (v_isSharedCheck_183_ == 0)
{
lean_object* v_unused_184_; 
v_unused_184_ = lean_ctor_get(v_x_132_, 0);
lean_dec(v_unused_184_);
v___x_144_ = v_x_132_;
v_isShared_145_ = v_isSharedCheck_183_;
goto v_resetjp_143_;
}
else
{
lean_dec(v_x_132_);
v___x_144_ = lean_box(0);
v_isShared_145_ = v_isSharedCheck_183_;
goto v_resetjp_143_;
}
v_resetjp_143_:
{
lean_object* v_v_146_; lean_object* v___x_147_; lean_object* v_xs_x27_148_; lean_object* v___y_150_; 
v_v_146_ = lean_array_fget(v_es_137_, v_j_140_);
v___x_147_ = lean_box(0);
v_xs_x27_148_ = lean_array_fset(v_es_137_, v_j_140_, v___x_147_);
switch(lean_obj_tag(v_v_146_))
{
case 0:
{
lean_object* v_key_155_; lean_object* v_val_156_; lean_object* v___x_158_; uint8_t v_isShared_159_; uint8_t v_isSharedCheck_168_; 
v_key_155_ = lean_ctor_get(v_v_146_, 0);
v_val_156_ = lean_ctor_get(v_v_146_, 1);
v_isSharedCheck_168_ = !lean_is_exclusive(v_v_146_);
if (v_isSharedCheck_168_ == 0)
{
v___x_158_ = v_v_146_;
v_isShared_159_ = v_isSharedCheck_168_;
goto v_resetjp_157_;
}
else
{
lean_inc(v_val_156_);
lean_inc(v_key_155_);
lean_dec(v_v_146_);
v___x_158_ = lean_box(0);
v_isShared_159_ = v_isSharedCheck_168_;
goto v_resetjp_157_;
}
v_resetjp_157_:
{
size_t v___x_160_; size_t v___x_161_; uint8_t v___x_162_; 
v___x_160_ = lean_ptr_addr(v_x_135_);
v___x_161_ = lean_ptr_addr(v_key_155_);
v___x_162_ = lean_usize_dec_eq(v___x_160_, v___x_161_);
if (v___x_162_ == 0)
{
lean_object* v___x_163_; lean_object* v___x_164_; 
lean_del_object(v___x_158_);
v___x_163_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_155_, v_val_156_, v_x_135_, v_x_136_);
v___x_164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_164_, 0, v___x_163_);
v___y_150_ = v___x_164_;
goto v___jp_149_;
}
else
{
lean_object* v___x_166_; 
lean_dec(v_val_156_);
lean_dec(v_key_155_);
if (v_isShared_159_ == 0)
{
lean_ctor_set(v___x_158_, 1, v_x_136_);
lean_ctor_set(v___x_158_, 0, v_x_135_);
v___x_166_ = v___x_158_;
goto v_reusejp_165_;
}
else
{
lean_object* v_reuseFailAlloc_167_; 
v_reuseFailAlloc_167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_167_, 0, v_x_135_);
lean_ctor_set(v_reuseFailAlloc_167_, 1, v_x_136_);
v___x_166_ = v_reuseFailAlloc_167_;
goto v_reusejp_165_;
}
v_reusejp_165_:
{
v___y_150_ = v___x_166_;
goto v___jp_149_;
}
}
}
}
case 1:
{
lean_object* v_node_169_; lean_object* v___x_171_; uint8_t v_isShared_172_; uint8_t v_isSharedCheck_181_; 
v_node_169_ = lean_ctor_get(v_v_146_, 0);
v_isSharedCheck_181_ = !lean_is_exclusive(v_v_146_);
if (v_isSharedCheck_181_ == 0)
{
v___x_171_ = v_v_146_;
v_isShared_172_ = v_isSharedCheck_181_;
goto v_resetjp_170_;
}
else
{
lean_inc(v_node_169_);
lean_dec(v_v_146_);
v___x_171_ = lean_box(0);
v_isShared_172_ = v_isSharedCheck_181_;
goto v_resetjp_170_;
}
v_resetjp_170_:
{
size_t v___x_173_; size_t v___x_174_; size_t v___x_175_; size_t v___x_176_; lean_object* v___x_177_; lean_object* v___x_179_; 
v___x_173_ = ((size_t)5ULL);
v___x_174_ = lean_usize_shift_right(v_x_133_, v___x_173_);
v___x_175_ = ((size_t)1ULL);
v___x_176_ = lean_usize_add(v_x_134_, v___x_175_);
v___x_177_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3___redArg(v_node_169_, v___x_174_, v___x_176_, v_x_135_, v_x_136_);
if (v_isShared_172_ == 0)
{
lean_ctor_set(v___x_171_, 0, v___x_177_);
v___x_179_ = v___x_171_;
goto v_reusejp_178_;
}
else
{
lean_object* v_reuseFailAlloc_180_; 
v_reuseFailAlloc_180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_180_, 0, v___x_177_);
v___x_179_ = v_reuseFailAlloc_180_;
goto v_reusejp_178_;
}
v_reusejp_178_:
{
v___y_150_ = v___x_179_;
goto v___jp_149_;
}
}
}
default: 
{
lean_object* v___x_182_; 
v___x_182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_182_, 0, v_x_135_);
lean_ctor_set(v___x_182_, 1, v_x_136_);
v___y_150_ = v___x_182_;
goto v___jp_149_;
}
}
v___jp_149_:
{
lean_object* v___x_151_; lean_object* v___x_153_; 
v___x_151_ = lean_array_fset(v_xs_x27_148_, v_j_140_, v___y_150_);
lean_dec(v_j_140_);
if (v_isShared_145_ == 0)
{
lean_ctor_set(v___x_144_, 0, v___x_151_);
v___x_153_ = v___x_144_;
goto v_reusejp_152_;
}
else
{
lean_object* v_reuseFailAlloc_154_; 
v_reuseFailAlloc_154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_154_, 0, v___x_151_);
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
}
else
{
lean_object* v_ks_185_; lean_object* v_vs_186_; lean_object* v___x_188_; uint8_t v_isShared_189_; uint8_t v_isSharedCheck_204_; 
v_ks_185_ = lean_ctor_get(v_x_132_, 0);
v_vs_186_ = lean_ctor_get(v_x_132_, 1);
v_isSharedCheck_204_ = !lean_is_exclusive(v_x_132_);
if (v_isSharedCheck_204_ == 0)
{
v___x_188_ = v_x_132_;
v_isShared_189_ = v_isSharedCheck_204_;
goto v_resetjp_187_;
}
else
{
lean_inc(v_vs_186_);
lean_inc(v_ks_185_);
lean_dec(v_x_132_);
v___x_188_ = lean_box(0);
v_isShared_189_ = v_isSharedCheck_204_;
goto v_resetjp_187_;
}
v_resetjp_187_:
{
lean_object* v___x_191_; 
if (v_isShared_189_ == 0)
{
v___x_191_ = v___x_188_;
goto v_reusejp_190_;
}
else
{
lean_object* v_reuseFailAlloc_203_; 
v_reuseFailAlloc_203_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_203_, 0, v_ks_185_);
lean_ctor_set(v_reuseFailAlloc_203_, 1, v_vs_186_);
v___x_191_ = v_reuseFailAlloc_203_;
goto v_reusejp_190_;
}
v_reusejp_190_:
{
lean_object* v_newNode_192_; size_t v___x_193_; uint8_t v___x_194_; 
v_newNode_192_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3_spec__5___redArg(v___x_191_, v_x_135_, v_x_136_);
v___x_193_ = ((size_t)7ULL);
v___x_194_ = lean_usize_dec_le(v___x_193_, v_x_134_);
if (v___x_194_ == 0)
{
lean_object* v___x_195_; lean_object* v___x_196_; uint8_t v___x_197_; 
v___x_195_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_192_);
v___x_196_ = lean_unsigned_to_nat(4u);
v___x_197_ = lean_nat_dec_lt(v___x_195_, v___x_196_);
lean_dec(v___x_195_);
if (v___x_197_ == 0)
{
lean_object* v_ks_198_; lean_object* v_vs_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; 
v_ks_198_ = lean_ctor_get(v_newNode_192_, 0);
lean_inc_ref(v_ks_198_);
v_vs_199_ = lean_ctor_get(v_newNode_192_, 1);
lean_inc_ref(v_vs_199_);
lean_dec_ref(v_newNode_192_);
v___x_200_ = lean_unsigned_to_nat(0u);
v___x_201_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3___redArg___closed__0);
v___x_202_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3_spec__6___redArg(v_x_134_, v_ks_198_, v_vs_199_, v___x_200_, v___x_201_);
lean_dec_ref(v_vs_199_);
lean_dec_ref(v_ks_198_);
return v___x_202_;
}
else
{
return v_newNode_192_;
}
}
else
{
return v_newNode_192_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_132_ = stack[0].m_obj;
size_t v_x_133_ = stack[1].m_num;
size_t v_x_134_ = stack[2].m_num;
lean_object* v_x_135_ = stack[3].m_obj;
lean_object* v_x_136_ = stack[4].m_obj;
lean_object* v_res_205_;
v_res_205_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3___redArg(v_x_132_, v_x_133_, v_x_134_, v_x_135_, v_x_136_);
stack->m_obj
 = v_res_205_;
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3_spec__6___redArg(size_t v_depth_206_, lean_object* v_keys_207_, lean_object* v_vals_208_, lean_object* v_i_209_, lean_object* v_entries_210_){
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
lean_object* v_k_213_; lean_object* v_v_214_; size_t v___x_215_; size_t v___x_216_; size_t v___x_217_; uint64_t v___x_218_; size_t v_h_219_; size_t v___x_220_; lean_object* v___x_221_; size_t v___x_222_; size_t v___x_223_; size_t v___x_224_; size_t v_h_225_; lean_object* v___x_226_; lean_object* v___x_227_; 
v_k_213_ = lean_array_fget_borrowed(v_keys_207_, v_i_209_);
v_v_214_ = lean_array_fget_borrowed(v_vals_208_, v_i_209_);
v___x_215_ = lean_ptr_addr(v_k_213_);
v___x_216_ = ((size_t)3ULL);
v___x_217_ = lean_usize_shift_right(v___x_215_, v___x_216_);
v___x_218_ = lean_usize_to_uint64(v___x_217_);
v_h_219_ = lean_uint64_to_usize(v___x_218_);
v___x_220_ = ((size_t)5ULL);
v___x_221_ = lean_unsigned_to_nat(1u);
v___x_222_ = ((size_t)1ULL);
v___x_223_ = lean_usize_sub(v_depth_206_, v___x_222_);
v___x_224_ = lean_usize_mul(v___x_220_, v___x_223_);
v_h_225_ = lean_usize_shift_right(v_h_219_, v___x_224_);
v___x_226_ = lean_nat_add(v_i_209_, v___x_221_);
lean_dec(v_i_209_);
lean_inc(v_v_214_);
lean_inc(v_k_213_);
v___x_227_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3___redArg(v_entries_210_, v_h_225_, v_depth_206_, v_k_213_, v_v_214_);
v_i_209_ = v___x_226_;
v_entries_210_ = v___x_227_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_depth_206_ = stack[0].m_num;
lean_object* v_keys_207_ = stack[1].m_obj;
lean_object* v_vals_208_ = stack[2].m_obj;
lean_object* v_i_209_ = stack[3].m_obj;
lean_object* v_entries_210_ = stack[4].m_obj;
lean_object* v_res_229_;
v_res_229_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3_spec__6___redArg(v_depth_206_, v_keys_207_, v_vals_208_, v_i_209_, v_entries_210_);
stack->m_obj
 = v_res_229_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3_spec__6___redArg___boxed(lean_object* v_depth_230_, lean_object* v_keys_231_, lean_object* v_vals_232_, lean_object* v_i_233_, lean_object* v_entries_234_){
_start:
{
size_t v_depth_boxed_235_; lean_object* v_res_236_; 
v_depth_boxed_235_ = lean_unbox_usize(v_depth_230_);
lean_dec(v_depth_230_);
v_res_236_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3_spec__6___redArg(v_depth_boxed_235_, v_keys_231_, v_vals_232_, v_i_233_, v_entries_234_);
lean_dec_ref(v_vals_232_);
lean_dec_ref(v_keys_231_);
return v_res_236_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3___redArg___boxed(lean_object* v_x_237_, lean_object* v_x_238_, lean_object* v_x_239_, lean_object* v_x_240_, lean_object* v_x_241_){
_start:
{
size_t v_x_10039__boxed_242_; size_t v_x_10040__boxed_243_; lean_object* v_res_244_; 
v_x_10039__boxed_242_ = lean_unbox_usize(v_x_238_);
lean_dec(v_x_238_);
v_x_10040__boxed_243_ = lean_unbox_usize(v_x_239_);
lean_dec(v_x_239_);
v_res_244_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3___redArg(v_x_237_, v_x_10039__boxed_242_, v_x_10040__boxed_243_, v_x_240_, v_x_241_);
return v_res_244_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2___redArg(lean_object* v_x_245_, lean_object* v_x_246_, lean_object* v_x_247_){
_start:
{
size_t v___x_248_; size_t v___x_249_; size_t v___x_250_; uint64_t v___x_251_; size_t v___x_252_; size_t v___x_253_; lean_object* v___x_254_; 
v___x_248_ = lean_ptr_addr(v_x_246_);
v___x_249_ = ((size_t)3ULL);
v___x_250_ = lean_usize_shift_right(v___x_248_, v___x_249_);
v___x_251_ = lean_usize_to_uint64(v___x_250_);
v___x_252_ = lean_uint64_to_usize(v___x_251_);
v___x_253_ = ((size_t)1ULL);
v___x_254_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3___redArg(v_x_245_, v___x_252_, v___x_253_, v_x_246_, v_x_247_);
return v___x_254_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__3(void){
_start:
{
lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; 
v___x_258_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__2));
v___x_259_ = lean_unsigned_to_nat(26u);
v___x_260_ = lean_unsigned_to_nat(19u);
v___x_261_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__1));
v___x_262_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__0));
v___x_263_ = l_mkPanicMessageWithDecl(v___x_262_, v___x_261_, v___x_260_, v___x_259_, v___x_258_);
return v___x_263_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__11(void){
_start:
{
lean_object* v___x_276_; lean_object* v_dummy_277_; 
v___x_276_ = lean_box(0);
v_dummy_277_ = l_Lean_Expr_sort___override(v___x_276_);
return v_dummy_277_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f(lean_object* v_f_283_, lean_object* v_a_284_, lean_object* v_a_285_, lean_object* v_a_286_, lean_object* v_a_287_, lean_object* v_a_288_, lean_object* v_a_289_, lean_object* v_a_290_, lean_object* v_a_291_, lean_object* v_a_292_, lean_object* v_a_293_, lean_object* v_a_294_){
_start:
{
lean_object* v___y_297_; lean_object* v___y_298_; lean_object* v___y_299_; lean_object* v___y_300_; lean_object* v___y_301_; lean_object* v___y_302_; lean_object* v___y_303_; lean_object* v___y_304_; lean_object* v___y_305_; lean_object* v___y_306_; lean_object* v___x_309_; lean_object* v_toGoalState_310_; lean_object* v_inj_311_; lean_object* v_fns_312_; lean_object* v___x_314_; uint8_t v_isShared_315_; uint8_t v_isSharedCheck_436_; 
v___x_309_ = lean_st_ref_get(v_a_285_);
v_toGoalState_310_ = lean_ctor_get(v___x_309_, 0);
lean_inc_ref(v_toGoalState_310_);
lean_dec(v___x_309_);
v_inj_311_ = lean_ctor_get(v_toGoalState_310_, 13);
lean_inc_ref(v_inj_311_);
lean_dec_ref(v_toGoalState_310_);
v_fns_312_ = lean_ctor_get(v_inj_311_, 1);
v_isSharedCheck_436_ = !lean_is_exclusive(v_inj_311_);
if (v_isSharedCheck_436_ == 0)
{
lean_object* v_unused_437_; 
v_unused_437_ = lean_ctor_get(v_inj_311_, 0);
lean_dec(v_unused_437_);
v___x_314_ = v_inj_311_;
v_isShared_315_ = v_isSharedCheck_436_;
goto v_resetjp_313_;
}
else
{
lean_inc(v_fns_312_);
lean_dec(v_inj_311_);
v___x_314_ = lean_box(0);
v_isShared_315_ = v_isSharedCheck_436_;
goto v_resetjp_313_;
}
v___jp_296_:
{
lean_object* v___x_307_; lean_object* v___x_308_; 
v___x_307_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__3, &l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__3);
v___x_308_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__0(v___x_307_, v___y_297_, v___y_298_, v___y_299_, v___y_300_, v___y_301_, v___y_302_, v___y_303_, v___y_304_, v___y_305_, v___y_306_);
return v___x_308_;
}
v_resetjp_313_:
{
lean_object* v___x_316_; 
v___x_316_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1___redArg(v_fns_312_, v_f_283_);
lean_dec_ref(v_fns_312_);
if (lean_obj_tag(v___x_316_) == 1)
{
lean_object* v_val_317_; lean_object* v___x_319_; uint8_t v_isShared_320_; uint8_t v_isSharedCheck_433_; 
v_val_317_ = lean_ctor_get(v___x_316_, 0);
v_isSharedCheck_433_ = !lean_is_exclusive(v___x_316_);
if (v_isSharedCheck_433_ == 0)
{
v___x_319_ = v___x_316_;
v_isShared_320_ = v_isSharedCheck_433_;
goto v_resetjp_318_;
}
else
{
lean_inc(v_val_317_);
lean_dec(v___x_316_);
v___x_319_ = lean_box(0);
v_isShared_320_ = v_isSharedCheck_433_;
goto v_resetjp_318_;
}
v_resetjp_318_:
{
lean_object* v_inv_x3f_321_; 
v_inv_x3f_321_ = lean_ctor_get(v_val_317_, 4);
if (lean_obj_tag(v_inv_x3f_321_) == 1)
{
lean_object* v___x_322_; 
lean_inc_ref(v_inv_x3f_321_);
lean_del_object(v___x_319_);
lean_dec(v_val_317_);
lean_del_object(v___x_314_);
lean_dec_ref(v_a_284_);
lean_dec_ref(v_f_283_);
v___x_322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_322_, 0, v_inv_x3f_321_);
return v___x_322_;
}
else
{
lean_object* v_us_323_; 
v_us_323_ = lean_ctor_get(v_val_317_, 0);
lean_inc(v_us_323_);
if (lean_obj_tag(v_us_323_) == 1)
{
lean_object* v_tail_324_; 
v_tail_324_ = lean_ctor_get(v_us_323_, 1);
lean_inc(v_tail_324_);
if (lean_obj_tag(v_tail_324_) == 1)
{
lean_object* v_tail_325_; lean_object* v___x_327_; uint8_t v_isShared_328_; uint8_t v_isSharedCheck_431_; 
v_tail_325_ = lean_ctor_get(v_tail_324_, 1);
v_isSharedCheck_431_ = !lean_is_exclusive(v_tail_324_);
if (v_isSharedCheck_431_ == 0)
{
lean_object* v_unused_432_; 
v_unused_432_ = lean_ctor_get(v_tail_324_, 0);
lean_dec(v_unused_432_);
v___x_327_ = v_tail_324_;
v_isShared_328_ = v_isSharedCheck_431_;
goto v_resetjp_326_;
}
else
{
lean_inc(v_tail_325_);
lean_dec(v_tail_324_);
v___x_327_ = lean_box(0);
v_isShared_328_ = v_isSharedCheck_431_;
goto v_resetjp_326_;
}
v_resetjp_326_:
{
if (lean_obj_tag(v_tail_325_) == 0)
{
lean_object* v_00_u03b1_329_; lean_object* v_00_u03b2_330_; lean_object* v_h_331_; lean_object* v___x_333_; uint8_t v_isShared_334_; uint8_t v_isSharedCheck_428_; 
v_00_u03b1_329_ = lean_ctor_get(v_val_317_, 1);
v_00_u03b2_330_ = lean_ctor_get(v_val_317_, 2);
v_h_331_ = lean_ctor_get(v_val_317_, 3);
v_isSharedCheck_428_ = !lean_is_exclusive(v_val_317_);
if (v_isSharedCheck_428_ == 0)
{
lean_object* v_unused_429_; lean_object* v_unused_430_; 
v_unused_429_ = lean_ctor_get(v_val_317_, 4);
lean_dec(v_unused_429_);
v_unused_430_ = lean_ctor_get(v_val_317_, 0);
lean_dec(v_unused_430_);
v___x_333_ = v_val_317_;
v_isShared_334_ = v_isSharedCheck_428_;
goto v_resetjp_332_;
}
else
{
lean_inc(v_h_331_);
lean_inc(v_00_u03b2_330_);
lean_inc(v_00_u03b1_329_);
lean_dec(v_val_317_);
v___x_333_ = lean_box(0);
v_isShared_334_ = v_isSharedCheck_428_;
goto v_resetjp_332_;
}
v_resetjp_332_:
{
lean_object* v_head_335_; lean_object* v___x_336_; lean_object* v___x_338_; 
v_head_335_ = lean_ctor_get(v_us_323_, 0);
v___x_336_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__6));
lean_inc(v_head_335_);
if (v_isShared_328_ == 0)
{
lean_ctor_set(v___x_327_, 0, v_head_335_);
v___x_338_ = v___x_327_;
goto v_reusejp_337_;
}
else
{
lean_object* v_reuseFailAlloc_427_; 
v_reuseFailAlloc_427_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_427_, 0, v_head_335_);
lean_ctor_set(v_reuseFailAlloc_427_, 1, v_tail_325_);
v___x_338_ = v_reuseFailAlloc_427_;
goto v_reusejp_337_;
}
v_reusejp_337_:
{
lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; 
v___x_339_ = l_Lean_mkConst(v___x_336_, v___x_338_);
lean_inc_ref_n(v_00_u03b1_329_, 2);
v___x_340_ = l_Lean_mkAppB(v___x_339_, v_00_u03b1_329_, v_a_284_);
v___x_341_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__10));
lean_inc_ref(v_us_323_);
v___x_342_ = l_Lean_mkConst(v___x_341_, v_us_323_);
lean_inc_ref(v_h_331_);
lean_inc_ref(v_f_283_);
lean_inc_ref(v_00_u03b2_330_);
v___x_343_ = l_Lean_mkApp5(v___x_342_, v_00_u03b1_329_, v_00_u03b2_330_, v_f_283_, v_h_331_, v___x_340_);
v___x_344_ = l_Lean_Meta_Grind_preprocessLight___redArg(v___x_343_, v_a_286_, v_a_287_, v_a_288_, v_a_289_, v_a_290_, v_a_291_, v_a_292_, v_a_293_, v_a_294_);
if (lean_obj_tag(v___x_344_) == 0)
{
lean_object* v_a_345_; lean_object* v___x_347_; uint8_t v_isShared_348_; uint8_t v_isSharedCheck_418_; 
v_a_345_ = lean_ctor_get(v___x_344_, 0);
v_isSharedCheck_418_ = !lean_is_exclusive(v___x_344_);
if (v_isSharedCheck_418_ == 0)
{
v___x_347_ = v___x_344_;
v_isShared_348_ = v_isSharedCheck_418_;
goto v_resetjp_346_;
}
else
{
lean_inc(v_a_345_);
lean_dec(v___x_344_);
v___x_347_ = lean_box(0);
v_isShared_348_ = v_isSharedCheck_418_;
goto v_resetjp_346_;
}
v_resetjp_346_:
{
lean_object* v_dummy_349_; lean_object* v_nargs_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_359_; 
v_dummy_349_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__11, &l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__11_once, _init_l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__11);
v_nargs_350_ = l_Lean_Expr_getAppNumArgs(v_a_345_);
lean_inc(v_nargs_350_);
v___x_351_ = lean_mk_array(v_nargs_350_, v_dummy_349_);
v___x_352_ = lean_unsigned_to_nat(1u);
v___x_353_ = lean_nat_sub(v_nargs_350_, v___x_352_);
lean_dec(v_nargs_350_);
lean_inc(v_a_345_);
v___x_354_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_345_, v___x_351_, v___x_353_);
v___x_355_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__13));
lean_inc_ref(v_us_323_);
v___x_356_ = l_Lean_mkConst(v___x_355_, v_us_323_);
v___x_357_ = l_Lean_mkAppN(v___x_356_, v___x_354_);
lean_dec_ref(v___x_354_);
if (v_isShared_315_ == 0)
{
lean_ctor_set(v___x_314_, 1, v___x_357_);
lean_ctor_set(v___x_314_, 0, v_a_345_);
v___x_359_ = v___x_314_;
goto v_reusejp_358_;
}
else
{
lean_object* v_reuseFailAlloc_417_; 
v_reuseFailAlloc_417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_417_, 0, v_a_345_);
lean_ctor_set(v_reuseFailAlloc_417_, 1, v___x_357_);
v___x_359_ = v_reuseFailAlloc_417_;
goto v_reusejp_358_;
}
v_reusejp_358_:
{
lean_object* v___x_361_; 
if (v_isShared_320_ == 0)
{
lean_ctor_set(v___x_319_, 0, v___x_359_);
v___x_361_ = v___x_319_;
goto v_reusejp_360_;
}
else
{
lean_object* v_reuseFailAlloc_416_; 
v_reuseFailAlloc_416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_416_, 0, v___x_359_);
v___x_361_ = v_reuseFailAlloc_416_;
goto v_reusejp_360_;
}
v_reusejp_360_:
{
lean_object* v___x_363_; 
lean_inc_ref(v___x_361_);
if (v_isShared_334_ == 0)
{
lean_ctor_set(v___x_333_, 4, v___x_361_);
v___x_363_ = v___x_333_;
goto v_reusejp_362_;
}
else
{
lean_object* v_reuseFailAlloc_415_; 
v_reuseFailAlloc_415_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_415_, 0, v_us_323_);
lean_ctor_set(v_reuseFailAlloc_415_, 1, v_00_u03b1_329_);
lean_ctor_set(v_reuseFailAlloc_415_, 2, v_00_u03b2_330_);
lean_ctor_set(v_reuseFailAlloc_415_, 3, v_h_331_);
lean_ctor_set(v_reuseFailAlloc_415_, 4, v___x_361_);
v___x_363_ = v_reuseFailAlloc_415_;
goto v_reusejp_362_;
}
v_reusejp_362_:
{
lean_object* v___x_364_; lean_object* v_toGoalState_365_; lean_object* v_inj_366_; lean_object* v_mvarId_367_; lean_object* v___x_369_; uint8_t v_isShared_370_; uint8_t v_isSharedCheck_413_; 
v___x_364_ = lean_st_ref_take(v_a_285_);
v_toGoalState_365_ = lean_ctor_get(v___x_364_, 0);
lean_inc_ref(v_toGoalState_365_);
v_inj_366_ = lean_ctor_get(v_toGoalState_365_, 13);
lean_inc_ref(v_inj_366_);
v_mvarId_367_ = lean_ctor_get(v___x_364_, 1);
v_isSharedCheck_413_ = !lean_is_exclusive(v___x_364_);
if (v_isSharedCheck_413_ == 0)
{
lean_object* v_unused_414_; 
v_unused_414_ = lean_ctor_get(v___x_364_, 0);
lean_dec(v_unused_414_);
v___x_369_ = v___x_364_;
v_isShared_370_ = v_isSharedCheck_413_;
goto v_resetjp_368_;
}
else
{
lean_inc(v_mvarId_367_);
lean_dec(v___x_364_);
v___x_369_ = lean_box(0);
v_isShared_370_ = v_isSharedCheck_413_;
goto v_resetjp_368_;
}
v_resetjp_368_:
{
lean_object* v_nextDeclIdx_371_; lean_object* v_enodeMap_372_; lean_object* v_exprs_373_; lean_object* v_parents_374_; lean_object* v_congrTable_375_; lean_object* v_appMap_376_; lean_object* v_indicesFound_377_; lean_object* v_toProcess_378_; uint8_t v_inconsistent_379_; lean_object* v_nextIdx_380_; lean_object* v_newRawFacts_381_; lean_object* v_facts_382_; lean_object* v_extThms_383_; lean_object* v_ematch_384_; lean_object* v_split_385_; lean_object* v_clean_386_; lean_object* v_sstates_387_; lean_object* v___x_389_; uint8_t v_isShared_390_; uint8_t v_isSharedCheck_411_; 
v_nextDeclIdx_371_ = lean_ctor_get(v_toGoalState_365_, 0);
v_enodeMap_372_ = lean_ctor_get(v_toGoalState_365_, 1);
v_exprs_373_ = lean_ctor_get(v_toGoalState_365_, 2);
v_parents_374_ = lean_ctor_get(v_toGoalState_365_, 3);
v_congrTable_375_ = lean_ctor_get(v_toGoalState_365_, 4);
v_appMap_376_ = lean_ctor_get(v_toGoalState_365_, 5);
v_indicesFound_377_ = lean_ctor_get(v_toGoalState_365_, 6);
v_toProcess_378_ = lean_ctor_get(v_toGoalState_365_, 7);
v_inconsistent_379_ = lean_ctor_get_uint8(v_toGoalState_365_, sizeof(void*)*17);
v_nextIdx_380_ = lean_ctor_get(v_toGoalState_365_, 8);
v_newRawFacts_381_ = lean_ctor_get(v_toGoalState_365_, 9);
v_facts_382_ = lean_ctor_get(v_toGoalState_365_, 10);
v_extThms_383_ = lean_ctor_get(v_toGoalState_365_, 11);
v_ematch_384_ = lean_ctor_get(v_toGoalState_365_, 12);
v_split_385_ = lean_ctor_get(v_toGoalState_365_, 14);
v_clean_386_ = lean_ctor_get(v_toGoalState_365_, 15);
v_sstates_387_ = lean_ctor_get(v_toGoalState_365_, 16);
v_isSharedCheck_411_ = !lean_is_exclusive(v_toGoalState_365_);
if (v_isSharedCheck_411_ == 0)
{
lean_object* v_unused_412_; 
v_unused_412_ = lean_ctor_get(v_toGoalState_365_, 13);
lean_dec(v_unused_412_);
v___x_389_ = v_toGoalState_365_;
v_isShared_390_ = v_isSharedCheck_411_;
goto v_resetjp_388_;
}
else
{
lean_inc(v_sstates_387_);
lean_inc(v_clean_386_);
lean_inc(v_split_385_);
lean_inc(v_ematch_384_);
lean_inc(v_extThms_383_);
lean_inc(v_facts_382_);
lean_inc(v_newRawFacts_381_);
lean_inc(v_nextIdx_380_);
lean_inc(v_toProcess_378_);
lean_inc(v_indicesFound_377_);
lean_inc(v_appMap_376_);
lean_inc(v_congrTable_375_);
lean_inc(v_parents_374_);
lean_inc(v_exprs_373_);
lean_inc(v_enodeMap_372_);
lean_inc(v_nextDeclIdx_371_);
lean_dec(v_toGoalState_365_);
v___x_389_ = lean_box(0);
v_isShared_390_ = v_isSharedCheck_411_;
goto v_resetjp_388_;
}
v_resetjp_388_:
{
lean_object* v_thms_391_; lean_object* v_fns_392_; lean_object* v___x_394_; uint8_t v_isShared_395_; uint8_t v_isSharedCheck_410_; 
v_thms_391_ = lean_ctor_get(v_inj_366_, 0);
v_fns_392_ = lean_ctor_get(v_inj_366_, 1);
v_isSharedCheck_410_ = !lean_is_exclusive(v_inj_366_);
if (v_isSharedCheck_410_ == 0)
{
v___x_394_ = v_inj_366_;
v_isShared_395_ = v_isSharedCheck_410_;
goto v_resetjp_393_;
}
else
{
lean_inc(v_fns_392_);
lean_inc(v_thms_391_);
lean_dec(v_inj_366_);
v___x_394_ = lean_box(0);
v_isShared_395_ = v_isSharedCheck_410_;
goto v_resetjp_393_;
}
v_resetjp_393_:
{
lean_object* v___x_396_; lean_object* v___x_398_; 
v___x_396_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2___redArg(v_fns_392_, v_f_283_, v___x_363_);
if (v_isShared_395_ == 0)
{
lean_ctor_set(v___x_394_, 1, v___x_396_);
v___x_398_ = v___x_394_;
goto v_reusejp_397_;
}
else
{
lean_object* v_reuseFailAlloc_409_; 
v_reuseFailAlloc_409_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_409_, 0, v_thms_391_);
lean_ctor_set(v_reuseFailAlloc_409_, 1, v___x_396_);
v___x_398_ = v_reuseFailAlloc_409_;
goto v_reusejp_397_;
}
v_reusejp_397_:
{
lean_object* v___x_400_; 
if (v_isShared_390_ == 0)
{
lean_ctor_set(v___x_389_, 13, v___x_398_);
v___x_400_ = v___x_389_;
goto v_reusejp_399_;
}
else
{
lean_object* v_reuseFailAlloc_408_; 
v_reuseFailAlloc_408_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_408_, 0, v_nextDeclIdx_371_);
lean_ctor_set(v_reuseFailAlloc_408_, 1, v_enodeMap_372_);
lean_ctor_set(v_reuseFailAlloc_408_, 2, v_exprs_373_);
lean_ctor_set(v_reuseFailAlloc_408_, 3, v_parents_374_);
lean_ctor_set(v_reuseFailAlloc_408_, 4, v_congrTable_375_);
lean_ctor_set(v_reuseFailAlloc_408_, 5, v_appMap_376_);
lean_ctor_set(v_reuseFailAlloc_408_, 6, v_indicesFound_377_);
lean_ctor_set(v_reuseFailAlloc_408_, 7, v_toProcess_378_);
lean_ctor_set(v_reuseFailAlloc_408_, 8, v_nextIdx_380_);
lean_ctor_set(v_reuseFailAlloc_408_, 9, v_newRawFacts_381_);
lean_ctor_set(v_reuseFailAlloc_408_, 10, v_facts_382_);
lean_ctor_set(v_reuseFailAlloc_408_, 11, v_extThms_383_);
lean_ctor_set(v_reuseFailAlloc_408_, 12, v_ematch_384_);
lean_ctor_set(v_reuseFailAlloc_408_, 13, v___x_398_);
lean_ctor_set(v_reuseFailAlloc_408_, 14, v_split_385_);
lean_ctor_set(v_reuseFailAlloc_408_, 15, v_clean_386_);
lean_ctor_set(v_reuseFailAlloc_408_, 16, v_sstates_387_);
lean_ctor_set_uint8(v_reuseFailAlloc_408_, sizeof(void*)*17, v_inconsistent_379_);
v___x_400_ = v_reuseFailAlloc_408_;
goto v_reusejp_399_;
}
v_reusejp_399_:
{
lean_object* v___x_402_; 
if (v_isShared_370_ == 0)
{
lean_ctor_set(v___x_369_, 0, v___x_400_);
v___x_402_ = v___x_369_;
goto v_reusejp_401_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_407_, 0, v___x_400_);
lean_ctor_set(v_reuseFailAlloc_407_, 1, v_mvarId_367_);
v___x_402_ = v_reuseFailAlloc_407_;
goto v_reusejp_401_;
}
v_reusejp_401_:
{
lean_object* v___x_403_; lean_object* v___x_405_; 
v___x_403_ = lean_st_ref_put(v_a_285_, v___x_402_);
if (v_isShared_348_ == 0)
{
lean_ctor_set(v___x_347_, 0, v___x_361_);
v___x_405_ = v___x_347_;
goto v_reusejp_404_;
}
else
{
lean_object* v_reuseFailAlloc_406_; 
v_reuseFailAlloc_406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_406_, 0, v___x_361_);
v___x_405_ = v_reuseFailAlloc_406_;
goto v_reusejp_404_;
}
v_reusejp_404_:
{
return v___x_405_;
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
lean_object* v_a_419_; lean_object* v___x_421_; uint8_t v_isShared_422_; uint8_t v_isSharedCheck_426_; 
lean_del_object(v___x_333_);
lean_dec_ref(v_h_331_);
lean_dec_ref(v_00_u03b2_330_);
lean_dec_ref(v_00_u03b1_329_);
lean_dec_ref_known(v_us_323_, 2);
lean_del_object(v___x_319_);
lean_del_object(v___x_314_);
lean_dec_ref(v_f_283_);
v_a_419_ = lean_ctor_get(v___x_344_, 0);
v_isSharedCheck_426_ = !lean_is_exclusive(v___x_344_);
if (v_isSharedCheck_426_ == 0)
{
v___x_421_ = v___x_344_;
v_isShared_422_ = v_isSharedCheck_426_;
goto v_resetjp_420_;
}
else
{
lean_inc(v_a_419_);
lean_dec(v___x_344_);
v___x_421_ = lean_box(0);
v_isShared_422_ = v_isSharedCheck_426_;
goto v_resetjp_420_;
}
v_resetjp_420_:
{
lean_object* v___x_424_; 
if (v_isShared_422_ == 0)
{
v___x_424_ = v___x_421_;
goto v_reusejp_423_;
}
else
{
lean_object* v_reuseFailAlloc_425_; 
v_reuseFailAlloc_425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_425_, 0, v_a_419_);
v___x_424_ = v_reuseFailAlloc_425_;
goto v_reusejp_423_;
}
v_reusejp_423_:
{
return v___x_424_;
}
}
}
}
}
}
else
{
lean_del_object(v___x_327_);
lean_dec(v_tail_325_);
lean_dec_ref_known(v_us_323_, 2);
lean_del_object(v___x_319_);
lean_dec(v_val_317_);
lean_del_object(v___x_314_);
lean_dec_ref(v_a_284_);
lean_dec_ref(v_f_283_);
v___y_297_ = v_a_285_;
v___y_298_ = v_a_286_;
v___y_299_ = v_a_287_;
v___y_300_ = v_a_288_;
v___y_301_ = v_a_289_;
v___y_302_ = v_a_290_;
v___y_303_ = v_a_291_;
v___y_304_ = v_a_292_;
v___y_305_ = v_a_293_;
v___y_306_ = v_a_294_;
goto v___jp_296_;
}
}
}
else
{
lean_dec_ref_known(v_us_323_, 2);
lean_dec(v_tail_324_);
lean_del_object(v___x_319_);
lean_dec(v_val_317_);
lean_del_object(v___x_314_);
lean_dec_ref(v_a_284_);
lean_dec_ref(v_f_283_);
v___y_297_ = v_a_285_;
v___y_298_ = v_a_286_;
v___y_299_ = v_a_287_;
v___y_300_ = v_a_288_;
v___y_301_ = v_a_289_;
v___y_302_ = v_a_290_;
v___y_303_ = v_a_291_;
v___y_304_ = v_a_292_;
v___y_305_ = v_a_293_;
v___y_306_ = v_a_294_;
goto v___jp_296_;
}
}
else
{
lean_dec(v_us_323_);
lean_del_object(v___x_319_);
lean_dec(v_val_317_);
lean_del_object(v___x_314_);
lean_dec_ref(v_a_284_);
lean_dec_ref(v_f_283_);
v___y_297_ = v_a_285_;
v___y_298_ = v_a_286_;
v___y_299_ = v_a_287_;
v___y_300_ = v_a_288_;
v___y_301_ = v_a_289_;
v___y_302_ = v_a_290_;
v___y_303_ = v_a_291_;
v___y_304_ = v_a_292_;
v___y_305_ = v_a_293_;
v___y_306_ = v_a_294_;
goto v___jp_296_;
}
}
}
}
else
{
lean_object* v___x_434_; lean_object* v___x_435_; 
lean_dec(v___x_316_);
lean_del_object(v___x_314_);
lean_dec_ref(v_a_284_);
lean_dec_ref(v_f_283_);
v___x_434_ = lean_box(0);
v___x_435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_435_, 0, v___x_434_);
return v___x_435_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_283_ = stack[0].m_obj;
lean_object* v_a_284_ = stack[1].m_obj;
lean_object* v_a_285_ = stack[2].m_obj;
lean_object* v_a_286_ = stack[3].m_obj;
lean_object* v_a_287_ = stack[4].m_obj;
lean_object* v_a_288_ = stack[5].m_obj;
lean_object* v_a_289_ = stack[6].m_obj;
lean_object* v_a_290_ = stack[7].m_obj;
lean_object* v_a_291_ = stack[8].m_obj;
lean_object* v_a_292_ = stack[9].m_obj;
lean_object* v_a_293_ = stack[10].m_obj;
lean_object* v_a_294_ = stack[11].m_obj;
lean_object* v_res_438_;
v_res_438_ = l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f(v_f_283_, v_a_284_, v_a_285_, v_a_286_, v_a_287_, v_a_288_, v_a_289_, v_a_290_, v_a_291_, v_a_292_, v_a_293_, v_a_294_);
stack->m_obj
 = v_res_438_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___boxed(lean_object* v_f_439_, lean_object* v_a_440_, lean_object* v_a_441_, lean_object* v_a_442_, lean_object* v_a_443_, lean_object* v_a_444_, lean_object* v_a_445_, lean_object* v_a_446_, lean_object* v_a_447_, lean_object* v_a_448_, lean_object* v_a_449_, lean_object* v_a_450_, lean_object* v_a_451_){
_start:
{
lean_object* v_res_452_; 
v_res_452_ = l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f(v_f_439_, v_a_440_, v_a_441_, v_a_442_, v_a_443_, v_a_444_, v_a_445_, v_a_446_, v_a_447_, v_a_448_, v_a_449_, v_a_450_);
lean_dec(v_a_450_);
lean_dec_ref(v_a_449_);
lean_dec(v_a_448_);
lean_dec_ref(v_a_447_);
lean_dec(v_a_446_);
lean_dec_ref(v_a_445_);
lean_dec(v_a_444_);
lean_dec_ref(v_a_443_);
lean_dec(v_a_442_);
lean_dec(v_a_441_);
return v_res_452_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1(lean_object* v_00_u03b2_453_, lean_object* v_x_454_, lean_object* v_x_455_){
_start:
{
lean_object* v___x_456_; 
v___x_456_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1___redArg(v_x_454_, v_x_455_);
return v___x_456_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1___boxed(lean_object* v_00_u03b2_457_, lean_object* v_x_458_, lean_object* v_x_459_){
_start:
{
lean_object* v_res_460_; 
v_res_460_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1(v_00_u03b2_457_, v_x_458_, v_x_459_);
lean_dec_ref(v_x_459_);
lean_dec_ref(v_x_458_);
return v_res_460_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2(lean_object* v_00_u03b2_461_, lean_object* v_x_462_, lean_object* v_x_463_, lean_object* v_x_464_){
_start:
{
lean_object* v___x_465_; 
v___x_465_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2___redArg(v_x_462_, v_x_463_, v_x_464_);
return v___x_465_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1(lean_object* v_00_u03b2_466_, lean_object* v_x_467_, size_t v_x_468_, lean_object* v_x_469_){
_start:
{
lean_object* v___x_470_; 
v___x_470_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1___redArg(v_x_467_, v_x_468_, v_x_469_);
return v___x_470_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_467_ = stack[1].m_obj;
size_t v_x_468_ = stack[2].m_num;
lean_object* v_x_469_ = stack[3].m_obj;
lean_object* v_res_471_;
v_res_471_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1(lean_box(0), v_x_467_, v_x_468_, v_x_469_);
stack->m_obj
 = v_res_471_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1___boxed(lean_object* v_00_u03b2_472_, lean_object* v_x_473_, lean_object* v_x_474_, lean_object* v_x_475_){
_start:
{
size_t v_x_10786__boxed_476_; lean_object* v_res_477_; 
v_x_10786__boxed_476_ = lean_unbox_usize(v_x_474_);
lean_dec(v_x_474_);
v_res_477_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1(v_00_u03b2_472_, v_x_473_, v_x_10786__boxed_476_, v_x_475_);
lean_dec_ref(v_x_475_);
lean_dec_ref(v_x_473_);
return v_res_477_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3(lean_object* v_00_u03b2_478_, lean_object* v_x_479_, size_t v_x_480_, size_t v_x_481_, lean_object* v_x_482_, lean_object* v_x_483_){
_start:
{
lean_object* v___x_484_; 
v___x_484_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3___redArg(v_x_479_, v_x_480_, v_x_481_, v_x_482_, v_x_483_);
return v___x_484_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_479_ = stack[1].m_obj;
size_t v_x_480_ = stack[2].m_num;
size_t v_x_481_ = stack[3].m_num;
lean_object* v_x_482_ = stack[4].m_obj;
lean_object* v_x_483_ = stack[5].m_obj;
lean_object* v_res_485_;
v_res_485_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3(lean_box(0), v_x_479_, v_x_480_, v_x_481_, v_x_482_, v_x_483_);
stack->m_obj
 = v_res_485_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3___boxed(lean_object* v_00_u03b2_486_, lean_object* v_x_487_, lean_object* v_x_488_, lean_object* v_x_489_, lean_object* v_x_490_, lean_object* v_x_491_){
_start:
{
size_t v_x_10804__boxed_492_; size_t v_x_10805__boxed_493_; lean_object* v_res_494_; 
v_x_10804__boxed_492_ = lean_unbox_usize(v_x_488_);
lean_dec(v_x_488_);
v_x_10805__boxed_493_ = lean_unbox_usize(v_x_489_);
lean_dec(v_x_489_);
v_res_494_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3(v_00_u03b2_486_, v_x_487_, v_x_10804__boxed_492_, v_x_10805__boxed_493_, v_x_490_, v_x_491_);
return v_res_494_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_495_, lean_object* v_keys_496_, lean_object* v_vals_497_, lean_object* v_heq_498_, lean_object* v_i_499_, lean_object* v_k_500_){
_start:
{
lean_object* v___x_501_; 
v___x_501_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1_spec__2___redArg(v_keys_496_, v_vals_497_, v_i_499_, v_k_500_);
return v___x_501_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03b2_502_, lean_object* v_keys_503_, lean_object* v_vals_504_, lean_object* v_heq_505_, lean_object* v_i_506_, lean_object* v_k_507_){
_start:
{
lean_object* v_res_508_; 
v_res_508_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1_spec__2(v_00_u03b2_502_, v_keys_503_, v_vals_504_, v_heq_505_, v_i_506_, v_k_507_);
lean_dec_ref(v_k_507_);
lean_dec_ref(v_vals_504_);
lean_dec_ref(v_keys_503_);
return v_res_508_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3_spec__5(lean_object* v_00_u03b2_509_, lean_object* v_n_510_, lean_object* v_k_511_, lean_object* v_v_512_){
_start:
{
lean_object* v___x_513_; 
v___x_513_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3_spec__5___redArg(v_n_510_, v_k_511_, v_v_512_);
return v___x_513_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3_spec__6(lean_object* v_00_u03b2_514_, size_t v_depth_515_, lean_object* v_keys_516_, lean_object* v_vals_517_, lean_object* v_heq_518_, lean_object* v_i_519_, lean_object* v_entries_520_){
_start:
{
lean_object* v___x_521_; 
v___x_521_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3_spec__6___redArg(v_depth_515_, v_keys_516_, v_vals_517_, v_i_519_, v_entries_520_);
return v___x_521_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3_spec__6_0interp(lean_interpreter_value* stack)
{
size_t v_depth_515_ = stack[1].m_num;
lean_object* v_keys_516_ = stack[2].m_obj;
lean_object* v_vals_517_ = stack[3].m_obj;
lean_object* v_i_519_ = stack[5].m_obj;
lean_object* v_entries_520_ = stack[6].m_obj;
lean_object* v_res_522_;
v_res_522_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3_spec__6(lean_box(0), v_depth_515_, v_keys_516_, v_vals_517_, lean_box(0), v_i_519_, v_entries_520_);
stack->m_obj
 = v_res_522_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3_spec__6___boxed(lean_object* v_00_u03b2_523_, lean_object* v_depth_524_, lean_object* v_keys_525_, lean_object* v_vals_526_, lean_object* v_heq_527_, lean_object* v_i_528_, lean_object* v_entries_529_){
_start:
{
size_t v_depth_boxed_530_; lean_object* v_res_531_; 
v_depth_boxed_530_ = lean_unbox_usize(v_depth_524_);
lean_dec(v_depth_524_);
v_res_531_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3_spec__6(v_00_u03b2_523_, v_depth_boxed_530_, v_keys_525_, v_vals_526_, v_heq_527_, v_i_528_, v_entries_529_);
lean_dec_ref(v_vals_526_);
lean_dec_ref(v_keys_525_);
return v_res_531_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3_spec__5_spec__6(lean_object* v_00_u03b2_532_, lean_object* v_x_533_, lean_object* v_x_534_, lean_object* v_x_535_, lean_object* v_x_536_){
_start:
{
lean_object* v___x_537_; 
v___x_537_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3_spec__5_spec__6___redArg(v_x_533_, v_x_534_, v_x_535_, v_x_536_);
return v___x_537_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0_spec__0(lean_object* v_msgData_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_){
_start:
{
lean_object* v___x_544_; lean_object* v_env_545_; uint8_t v___x_546_; lean_object* v_env_547_; lean_object* v___x_548_; lean_object* v_toCold_549_; lean_object* v_mctx_550_; lean_object* v_lctx_551_; lean_object* v_options_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; 
v___x_544_ = lean_st_ref_get(v___y_542_);
v_env_545_ = lean_ctor_get(v___x_544_, 0);
lean_inc_ref(v_env_545_);
lean_dec(v___x_544_);
v___x_546_ = 0;
v_env_547_ = l_Lean_Environment_setRecordingDeps(v_env_545_, v___x_546_);
v___x_548_ = lean_st_ref_get(v___y_540_);
v_toCold_549_ = lean_ctor_get(v___y_541_, 0);
v_mctx_550_ = lean_ctor_get(v___x_548_, 0);
lean_inc_ref(v_mctx_550_);
lean_dec(v___x_548_);
v_lctx_551_ = lean_ctor_get(v___y_539_, 2);
v_options_552_ = lean_ctor_get(v_toCold_549_, 2);
lean_inc_ref(v_options_552_);
lean_inc_ref(v_lctx_551_);
v___x_553_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_553_, 0, v_env_547_);
lean_ctor_set(v___x_553_, 1, v_mctx_550_);
lean_ctor_set(v___x_553_, 2, v_lctx_551_);
lean_ctor_set(v___x_553_, 3, v_options_552_);
v___x_554_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_554_, 0, v___x_553_);
lean_ctor_set(v___x_554_, 1, v_msgData_538_);
v___x_555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_555_, 0, v___x_554_);
return v___x_555_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_538_ = stack[0].m_obj;
lean_object* v___y_539_ = stack[1].m_obj;
lean_object* v___y_540_ = stack[2].m_obj;
lean_object* v___y_541_ = stack[3].m_obj;
lean_object* v___y_542_ = stack[4].m_obj;
lean_object* v_res_556_;
v_res_556_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0_spec__0(v_msgData_538_, v___y_539_, v___y_540_, v___y_541_, v___y_542_);
stack->m_obj
 = v_res_556_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0_spec__0___boxed(lean_object* v_msgData_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_){
_start:
{
lean_object* v_res_563_; 
v_res_563_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0_spec__0(v_msgData_557_, v___y_558_, v___y_559_, v___y_560_, v___y_561_);
lean_dec(v___y_561_);
lean_dec_ref(v___y_560_);
lean_dec(v___y_559_);
lean_dec_ref(v___y_558_);
return v_res_563_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_564_; double v___x_565_; 
v___x_564_ = lean_unsigned_to_nat(0u);
v___x_565_ = lean_float_of_nat(v___x_564_);
return v___x_565_;
}
}
lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0___redArg(lean_object* v_cls_569_, lean_object* v_msg_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_){
_start:
{
lean_object* v_ref_576_; lean_object* v___x_577_; lean_object* v_a_578_; lean_object* v___x_580_; uint8_t v_isShared_581_; uint8_t v_isSharedCheck_623_; 
v_ref_576_ = lean_ctor_get(v___y_573_, 2);
v___x_577_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0_spec__0(v_msg_570_, v___y_571_, v___y_572_, v___y_573_, v___y_574_);
v_a_578_ = lean_ctor_get(v___x_577_, 0);
v_isSharedCheck_623_ = !lean_is_exclusive(v___x_577_);
if (v_isSharedCheck_623_ == 0)
{
v___x_580_ = v___x_577_;
v_isShared_581_ = v_isSharedCheck_623_;
goto v_resetjp_579_;
}
else
{
lean_inc(v_a_578_);
lean_dec(v___x_577_);
v___x_580_ = lean_box(0);
v_isShared_581_ = v_isSharedCheck_623_;
goto v_resetjp_579_;
}
v_resetjp_579_:
{
lean_object* v___x_582_; lean_object* v_traceState_583_; lean_object* v_env_584_; lean_object* v_nextMacroScope_585_; lean_object* v_ngen_586_; lean_object* v_auxDeclNGen_587_; lean_object* v_cache_588_; lean_object* v_recordedDeps_589_; lean_object* v_messages_590_; lean_object* v_infoState_591_; lean_object* v_snapshotTasks_592_; lean_object* v___x_594_; uint8_t v_isShared_595_; uint8_t v_isSharedCheck_622_; 
v___x_582_ = lean_st_ref_take(v___y_574_);
v_traceState_583_ = lean_ctor_get(v___x_582_, 4);
v_env_584_ = lean_ctor_get(v___x_582_, 0);
v_nextMacroScope_585_ = lean_ctor_get(v___x_582_, 1);
v_ngen_586_ = lean_ctor_get(v___x_582_, 2);
v_auxDeclNGen_587_ = lean_ctor_get(v___x_582_, 3);
v_cache_588_ = lean_ctor_get(v___x_582_, 5);
v_recordedDeps_589_ = lean_ctor_get(v___x_582_, 6);
v_messages_590_ = lean_ctor_get(v___x_582_, 7);
v_infoState_591_ = lean_ctor_get(v___x_582_, 8);
v_snapshotTasks_592_ = lean_ctor_get(v___x_582_, 9);
v_isSharedCheck_622_ = !lean_is_exclusive(v___x_582_);
if (v_isSharedCheck_622_ == 0)
{
v___x_594_ = v___x_582_;
v_isShared_595_ = v_isSharedCheck_622_;
goto v_resetjp_593_;
}
else
{
lean_inc(v_snapshotTasks_592_);
lean_inc(v_infoState_591_);
lean_inc(v_messages_590_);
lean_inc(v_recordedDeps_589_);
lean_inc(v_cache_588_);
lean_inc(v_traceState_583_);
lean_inc(v_auxDeclNGen_587_);
lean_inc(v_ngen_586_);
lean_inc(v_nextMacroScope_585_);
lean_inc(v_env_584_);
lean_dec(v___x_582_);
v___x_594_ = lean_box(0);
v_isShared_595_ = v_isSharedCheck_622_;
goto v_resetjp_593_;
}
v_resetjp_593_:
{
uint64_t v_tid_596_; lean_object* v_traces_597_; lean_object* v___x_599_; uint8_t v_isShared_600_; uint8_t v_isSharedCheck_621_; 
v_tid_596_ = lean_ctor_get_uint64(v_traceState_583_, sizeof(void*)*1);
v_traces_597_ = lean_ctor_get(v_traceState_583_, 0);
v_isSharedCheck_621_ = !lean_is_exclusive(v_traceState_583_);
if (v_isSharedCheck_621_ == 0)
{
v___x_599_ = v_traceState_583_;
v_isShared_600_ = v_isSharedCheck_621_;
goto v_resetjp_598_;
}
else
{
lean_inc(v_traces_597_);
lean_dec(v_traceState_583_);
v___x_599_ = lean_box(0);
v_isShared_600_ = v_isSharedCheck_621_;
goto v_resetjp_598_;
}
v_resetjp_598_:
{
lean_object* v___x_601_; lean_object* v___x_602_; double v___x_603_; uint8_t v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_612_; 
v___x_601_ = lean_box(0);
v___x_602_ = lean_box(0);
v___x_603_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0___redArg___closed__0);
v___x_604_ = 0;
v___x_605_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0___redArg___closed__1));
v___x_606_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_606_, 0, v_cls_569_);
lean_ctor_set(v___x_606_, 1, v___x_602_);
lean_ctor_set(v___x_606_, 2, v___x_605_);
lean_ctor_set_float(v___x_606_, sizeof(void*)*3, v___x_603_);
lean_ctor_set_float(v___x_606_, sizeof(void*)*3 + 8, v___x_603_);
lean_ctor_set_uint8(v___x_606_, sizeof(void*)*3 + 16, v___x_604_);
v___x_607_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0___redArg___closed__2));
v___x_608_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_608_, 0, v___x_606_);
lean_ctor_set(v___x_608_, 1, v_a_578_);
lean_ctor_set(v___x_608_, 2, v___x_607_);
lean_inc(v_ref_576_);
v___x_609_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_609_, 0, v_ref_576_);
lean_ctor_set(v___x_609_, 1, v___x_608_);
v___x_610_ = l_Lean_PersistentArray_push___redArg(v_traces_597_, v___x_609_);
if (v_isShared_600_ == 0)
{
lean_ctor_set(v___x_599_, 0, v___x_610_);
v___x_612_ = v___x_599_;
goto v_reusejp_611_;
}
else
{
lean_object* v_reuseFailAlloc_620_; 
v_reuseFailAlloc_620_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_620_, 0, v___x_610_);
lean_ctor_set_uint64(v_reuseFailAlloc_620_, sizeof(void*)*1, v_tid_596_);
v___x_612_ = v_reuseFailAlloc_620_;
goto v_reusejp_611_;
}
v_reusejp_611_:
{
lean_object* v___x_614_; 
if (v_isShared_595_ == 0)
{
lean_ctor_set(v___x_594_, 4, v___x_612_);
v___x_614_ = v___x_594_;
goto v_reusejp_613_;
}
else
{
lean_object* v_reuseFailAlloc_619_; 
v_reuseFailAlloc_619_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_619_, 0, v_env_584_);
lean_ctor_set(v_reuseFailAlloc_619_, 1, v_nextMacroScope_585_);
lean_ctor_set(v_reuseFailAlloc_619_, 2, v_ngen_586_);
lean_ctor_set(v_reuseFailAlloc_619_, 3, v_auxDeclNGen_587_);
lean_ctor_set(v_reuseFailAlloc_619_, 4, v___x_612_);
lean_ctor_set(v_reuseFailAlloc_619_, 5, v_cache_588_);
lean_ctor_set(v_reuseFailAlloc_619_, 6, v_recordedDeps_589_);
lean_ctor_set(v_reuseFailAlloc_619_, 7, v_messages_590_);
lean_ctor_set(v_reuseFailAlloc_619_, 8, v_infoState_591_);
lean_ctor_set(v_reuseFailAlloc_619_, 9, v_snapshotTasks_592_);
v___x_614_ = v_reuseFailAlloc_619_;
goto v_reusejp_613_;
}
v_reusejp_613_:
{
lean_object* v___x_615_; lean_object* v___x_617_; 
v___x_615_ = lean_st_ref_put(v___y_574_, v___x_614_);
if (v_isShared_581_ == 0)
{
lean_ctor_set(v___x_580_, 0, v___x_601_);
v___x_617_ = v___x_580_;
goto v_reusejp_616_;
}
else
{
lean_object* v_reuseFailAlloc_618_; 
v_reuseFailAlloc_618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_618_, 0, v___x_601_);
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
}
}
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_569_ = stack[0].m_obj;
lean_object* v_msg_570_ = stack[1].m_obj;
lean_object* v___y_571_ = stack[2].m_obj;
lean_object* v___y_572_ = stack[3].m_obj;
lean_object* v___y_573_ = stack[4].m_obj;
lean_object* v___y_574_ = stack[5].m_obj;
lean_object* v_res_624_;
v_res_624_ = l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0___redArg(v_cls_569_, v_msg_570_, v___y_571_, v___y_572_, v___y_573_, v___y_574_);
stack->m_obj
 = v_res_624_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0___redArg___boxed(lean_object* v_cls_625_, lean_object* v_msg_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_){
_start:
{
lean_object* v_res_632_; 
v_res_632_ = l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0___redArg(v_cls_625_, v_msg_626_, v___y_627_, v___y_628_, v___y_629_, v___y_630_);
lean_dec(v___y_630_);
lean_dec_ref(v___y_629_);
lean_dec(v___y_628_);
lean_dec_ref(v___y_627_);
return v_res_632_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkInjEq___closed__6(void){
_start:
{
lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; 
v___x_643_ = ((lean_object*)(l_Lean_Meta_Grind_mkInjEq___closed__3));
v___x_644_ = ((lean_object*)(l_Lean_Meta_Grind_mkInjEq___closed__5));
v___x_645_ = l_Lean_Name_append(v___x_644_, v___x_643_);
return v___x_645_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkInjEq___closed__8(void){
_start:
{
lean_object* v___x_647_; lean_object* v___x_648_; 
v___x_647_ = ((lean_object*)(l_Lean_Meta_Grind_mkInjEq___closed__7));
v___x_648_ = l_Lean_stringToMessageData(v___x_647_);
return v___x_648_;
}
}
lean_object* l_Lean_Meta_Grind_mkInjEq(lean_object* v_e_649_, lean_object* v_a_650_, lean_object* v_a_651_, lean_object* v_a_652_, lean_object* v_a_653_, lean_object* v_a_654_, lean_object* v_a_655_, lean_object* v_a_656_, lean_object* v_a_657_, lean_object* v_a_658_, lean_object* v_a_659_){
_start:
{
if (lean_obj_tag(v_e_649_) == 5)
{
lean_object* v_fn_661_; lean_object* v_arg_662_; lean_object* v___x_663_; 
v_fn_661_ = lean_ctor_get(v_e_649_, 0);
v_arg_662_ = lean_ctor_get(v_e_649_, 1);
lean_inc_ref_n(v_arg_662_, 2);
lean_inc_ref(v_fn_661_);
v___x_663_ = l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f(v_fn_661_, v_arg_662_, v_a_650_, v_a_651_, v_a_652_, v_a_653_, v_a_654_, v_a_655_, v_a_656_, v_a_657_, v_a_658_, v_a_659_);
if (lean_obj_tag(v___x_663_) == 0)
{
lean_object* v_a_664_; lean_object* v___x_666_; uint8_t v_isShared_667_; uint8_t v_isSharedCheck_717_; 
v_a_664_ = lean_ctor_get(v___x_663_, 0);
v_isSharedCheck_717_ = !lean_is_exclusive(v___x_663_);
if (v_isSharedCheck_717_ == 0)
{
v___x_666_ = v___x_663_;
v_isShared_667_ = v_isSharedCheck_717_;
goto v_resetjp_665_;
}
else
{
lean_inc(v_a_664_);
lean_dec(v___x_663_);
v___x_666_ = lean_box(0);
v_isShared_667_ = v_isSharedCheck_717_;
goto v_resetjp_665_;
}
v_resetjp_665_:
{
if (lean_obj_tag(v_a_664_) == 1)
{
lean_object* v_val_668_; lean_object* v_fst_669_; lean_object* v_snd_670_; lean_object* v___x_672_; uint8_t v_isShared_673_; uint8_t v_isSharedCheck_712_; 
lean_del_object(v___x_666_);
v_val_668_ = lean_ctor_get(v_a_664_, 0);
lean_inc(v_val_668_);
lean_dec_ref_known(v_a_664_, 1);
v_fst_669_ = lean_ctor_get(v_val_668_, 0);
v_snd_670_ = lean_ctor_get(v_val_668_, 1);
v_isSharedCheck_712_ = !lean_is_exclusive(v_val_668_);
if (v_isSharedCheck_712_ == 0)
{
v___x_672_ = v_val_668_;
v_isShared_673_ = v_isSharedCheck_712_;
goto v_resetjp_671_;
}
else
{
lean_inc(v_snd_670_);
lean_inc(v_fst_669_);
lean_dec(v_val_668_);
v___x_672_ = lean_box(0);
v_isShared_673_ = v_isSharedCheck_712_;
goto v_resetjp_671_;
}
v_resetjp_671_:
{
lean_object* v___x_674_; lean_object* v___y_676_; lean_object* v___y_677_; lean_object* v___y_678_; lean_object* v___y_679_; lean_object* v___y_680_; lean_object* v___y_681_; lean_object* v___x_685_; 
lean_inc_ref(v_e_649_);
v___x_674_ = l_Lean_Expr_app___override(v_fst_669_, v_e_649_);
v___x_685_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_649_, v_a_650_);
lean_dec_ref_known(v_e_649_, 2);
if (lean_obj_tag(v___x_685_) == 0)
{
lean_object* v_a_686_; lean_object* v___x_687_; lean_object* v___x_688_; 
v_a_686_ = lean_ctor_get(v___x_685_, 0);
lean_inc(v_a_686_);
lean_dec_ref_known(v___x_685_, 1);
v___x_687_ = lean_box(0);
lean_inc(v_a_659_);
lean_inc_ref(v_a_658_);
lean_inc(v_a_657_);
lean_inc_ref(v_a_656_);
lean_inc(v_a_655_);
lean_inc_ref(v_a_654_);
lean_inc(v_a_653_);
lean_inc_ref(v_a_652_);
lean_inc(v_a_651_);
lean_inc(v_a_650_);
lean_inc_ref(v___x_674_);
v___x_688_ = lean_grind_internalize(v___x_674_, v_a_686_, v___x_687_, v_a_650_, v_a_651_, v_a_652_, v_a_653_, v_a_654_, v_a_655_, v_a_656_, v_a_657_, v_a_658_, v_a_659_);
if (lean_obj_tag(v___x_688_) == 0)
{
lean_object* v_toCold_689_; lean_object* v_options_690_; uint8_t v_hasTrace_691_; 
lean_dec_ref_known(v___x_688_, 1);
v_toCold_689_ = lean_ctor_get(v_a_658_, 0);
v_options_690_ = lean_ctor_get(v_toCold_689_, 2);
v_hasTrace_691_ = lean_ctor_get_uint8(v_options_690_, sizeof(void*)*1);
if (v_hasTrace_691_ == 0)
{
lean_del_object(v___x_672_);
v___y_676_ = v_a_650_;
v___y_677_ = v_a_652_;
v___y_678_ = v_a_656_;
v___y_679_ = v_a_657_;
v___y_680_ = v_a_658_;
v___y_681_ = v_a_659_;
goto v___jp_675_;
}
else
{
lean_object* v_inheritedTraceOptions_692_; lean_object* v___x_693_; lean_object* v___x_694_; uint8_t v___x_695_; 
v_inheritedTraceOptions_692_ = lean_ctor_get(v_toCold_689_, 11);
v___x_693_ = ((lean_object*)(l_Lean_Meta_Grind_mkInjEq___closed__3));
v___x_694_ = lean_obj_once(&l_Lean_Meta_Grind_mkInjEq___closed__6, &l_Lean_Meta_Grind_mkInjEq___closed__6_once, _init_l_Lean_Meta_Grind_mkInjEq___closed__6);
v___x_695_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_692_, v_options_690_, v___x_694_);
if (v___x_695_ == 0)
{
lean_del_object(v___x_672_);
v___y_676_ = v_a_650_;
v___y_677_ = v_a_652_;
v___y_678_ = v_a_656_;
v___y_679_ = v_a_657_;
v___y_680_ = v_a_658_;
v___y_681_ = v_a_659_;
goto v___jp_675_;
}
else
{
lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_699_; 
lean_inc_ref(v___x_674_);
v___x_696_ = l_Lean_MessageData_ofExpr(v___x_674_);
v___x_697_ = lean_obj_once(&l_Lean_Meta_Grind_mkInjEq___closed__8, &l_Lean_Meta_Grind_mkInjEq___closed__8_once, _init_l_Lean_Meta_Grind_mkInjEq___closed__8);
if (v_isShared_673_ == 0)
{
lean_ctor_set_tag(v___x_672_, 7);
lean_ctor_set(v___x_672_, 1, v___x_697_);
lean_ctor_set(v___x_672_, 0, v___x_696_);
v___x_699_ = v___x_672_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_703_; 
v_reuseFailAlloc_703_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_703_, 0, v___x_696_);
lean_ctor_set(v_reuseFailAlloc_703_, 1, v___x_697_);
v___x_699_ = v_reuseFailAlloc_703_;
goto v_reusejp_698_;
}
v_reusejp_698_:
{
lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; 
lean_inc_ref(v_arg_662_);
v___x_700_ = l_Lean_MessageData_ofExpr(v_arg_662_);
v___x_701_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_701_, 0, v___x_699_);
lean_ctor_set(v___x_701_, 1, v___x_700_);
v___x_702_ = l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0___redArg(v___x_693_, v___x_701_, v_a_656_, v_a_657_, v_a_658_, v_a_659_);
if (lean_obj_tag(v___x_702_) == 0)
{
lean_dec_ref_known(v___x_702_, 1);
v___y_676_ = v_a_650_;
v___y_677_ = v_a_652_;
v___y_678_ = v_a_656_;
v___y_679_ = v_a_657_;
v___y_680_ = v_a_658_;
v___y_681_ = v_a_659_;
goto v___jp_675_;
}
else
{
lean_dec_ref(v___x_674_);
lean_dec(v_snd_670_);
lean_dec_ref(v_arg_662_);
return v___x_702_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_674_);
lean_del_object(v___x_672_);
lean_dec(v_snd_670_);
lean_dec_ref(v_arg_662_);
return v___x_688_;
}
}
else
{
lean_object* v_a_704_; lean_object* v___x_706_; uint8_t v_isShared_707_; uint8_t v_isSharedCheck_711_; 
lean_dec_ref(v___x_674_);
lean_del_object(v___x_672_);
lean_dec(v_snd_670_);
lean_dec_ref(v_arg_662_);
v_a_704_ = lean_ctor_get(v___x_685_, 0);
v_isSharedCheck_711_ = !lean_is_exclusive(v___x_685_);
if (v_isSharedCheck_711_ == 0)
{
v___x_706_ = v___x_685_;
v_isShared_707_ = v_isSharedCheck_711_;
goto v_resetjp_705_;
}
else
{
lean_inc(v_a_704_);
lean_dec(v___x_685_);
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
v___jp_675_:
{
lean_object* v___x_682_; uint8_t v___x_683_; lean_object* v___x_684_; 
lean_inc_ref(v_arg_662_);
v___x_682_ = l_Lean_Expr_app___override(v_snd_670_, v_arg_662_);
v___x_683_ = 0;
v___x_684_ = l_Lean_Meta_Grind_pushEqCore___redArg(v___x_674_, v_arg_662_, v___x_682_, v___x_683_, v___y_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_);
return v___x_684_;
}
}
}
else
{
lean_object* v___x_713_; lean_object* v___x_715_; 
lean_dec(v_a_664_);
lean_dec_ref(v_arg_662_);
lean_dec_ref_known(v_e_649_, 2);
v___x_713_ = lean_box(0);
if (v_isShared_667_ == 0)
{
lean_ctor_set(v___x_666_, 0, v___x_713_);
v___x_715_ = v___x_666_;
goto v_reusejp_714_;
}
else
{
lean_object* v_reuseFailAlloc_716_; 
v_reuseFailAlloc_716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_716_, 0, v___x_713_);
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
else
{
lean_object* v_a_718_; lean_object* v___x_720_; uint8_t v_isShared_721_; uint8_t v_isSharedCheck_725_; 
lean_dec_ref(v_arg_662_);
lean_dec_ref_known(v_e_649_, 2);
v_a_718_ = lean_ctor_get(v___x_663_, 0);
v_isSharedCheck_725_ = !lean_is_exclusive(v___x_663_);
if (v_isSharedCheck_725_ == 0)
{
v___x_720_ = v___x_663_;
v_isShared_721_ = v_isSharedCheck_725_;
goto v_resetjp_719_;
}
else
{
lean_inc(v_a_718_);
lean_dec(v___x_663_);
v___x_720_ = lean_box(0);
v_isShared_721_ = v_isSharedCheck_725_;
goto v_resetjp_719_;
}
v_resetjp_719_:
{
lean_object* v___x_723_; 
if (v_isShared_721_ == 0)
{
v___x_723_ = v___x_720_;
goto v_reusejp_722_;
}
else
{
lean_object* v_reuseFailAlloc_724_; 
v_reuseFailAlloc_724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_724_, 0, v_a_718_);
v___x_723_ = v_reuseFailAlloc_724_;
goto v_reusejp_722_;
}
v_reusejp_722_:
{
return v___x_723_;
}
}
}
}
else
{
lean_object* v___x_726_; lean_object* v___x_727_; 
lean_dec_ref(v_e_649_);
v___x_726_ = lean_box(0);
v___x_727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_727_, 0, v___x_726_);
return v___x_727_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_mkInjEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_649_ = stack[0].m_obj;
lean_object* v_a_650_ = stack[1].m_obj;
lean_object* v_a_651_ = stack[2].m_obj;
lean_object* v_a_652_ = stack[3].m_obj;
lean_object* v_a_653_ = stack[4].m_obj;
lean_object* v_a_654_ = stack[5].m_obj;
lean_object* v_a_655_ = stack[6].m_obj;
lean_object* v_a_656_ = stack[7].m_obj;
lean_object* v_a_657_ = stack[8].m_obj;
lean_object* v_a_658_ = stack[9].m_obj;
lean_object* v_a_659_ = stack[10].m_obj;
lean_object* v_res_728_;
v_res_728_ = l_Lean_Meta_Grind_mkInjEq(v_e_649_, v_a_650_, v_a_651_, v_a_652_, v_a_653_, v_a_654_, v_a_655_, v_a_656_, v_a_657_, v_a_658_, v_a_659_);
stack->m_obj
 = v_res_728_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkInjEq___boxed(lean_object* v_e_729_, lean_object* v_a_730_, lean_object* v_a_731_, lean_object* v_a_732_, lean_object* v_a_733_, lean_object* v_a_734_, lean_object* v_a_735_, lean_object* v_a_736_, lean_object* v_a_737_, lean_object* v_a_738_, lean_object* v_a_739_, lean_object* v_a_740_){
_start:
{
lean_object* v_res_741_; 
v_res_741_ = l_Lean_Meta_Grind_mkInjEq(v_e_729_, v_a_730_, v_a_731_, v_a_732_, v_a_733_, v_a_734_, v_a_735_, v_a_736_, v_a_737_, v_a_738_, v_a_739_);
lean_dec(v_a_739_);
lean_dec_ref(v_a_738_);
lean_dec(v_a_737_);
lean_dec_ref(v_a_736_);
lean_dec(v_a_735_);
lean_dec_ref(v_a_734_);
lean_dec(v_a_733_);
lean_dec_ref(v_a_732_);
lean_dec(v_a_731_);
lean_dec(v_a_730_);
return v_res_741_;
}
}
lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0(lean_object* v_cls_742_, lean_object* v_msg_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_){
_start:
{
lean_object* v___x_755_; 
v___x_755_ = l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0___redArg(v_cls_742_, v_msg_743_, v___y_750_, v___y_751_, v___y_752_, v___y_753_);
return v___x_755_;
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_742_ = stack[0].m_obj;
lean_object* v_msg_743_ = stack[1].m_obj;
lean_object* v___y_744_ = stack[2].m_obj;
lean_object* v___y_745_ = stack[3].m_obj;
lean_object* v___y_746_ = stack[4].m_obj;
lean_object* v___y_747_ = stack[5].m_obj;
lean_object* v___y_748_ = stack[6].m_obj;
lean_object* v___y_749_ = stack[7].m_obj;
lean_object* v___y_750_ = stack[8].m_obj;
lean_object* v___y_751_ = stack[9].m_obj;
lean_object* v___y_752_ = stack[10].m_obj;
lean_object* v___y_753_ = stack[11].m_obj;
lean_object* v_res_756_;
v_res_756_ = l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0(v_cls_742_, v_msg_743_, v___y_744_, v___y_745_, v___y_746_, v___y_747_, v___y_748_, v___y_749_, v___y_750_, v___y_751_, v___y_752_, v___y_753_);
stack->m_obj
 = v_res_756_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0___boxed(lean_object* v_cls_757_, lean_object* v_msg_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_){
_start:
{
lean_object* v_res_770_; 
v_res_770_ = l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0(v_cls_757_, v_msg_758_, v___y_759_, v___y_760_, v___y_761_, v___y_762_, v___y_763_, v___y_764_, v___y_765_, v___y_766_, v___y_767_, v___y_768_);
lean_dec(v___y_768_);
lean_dec_ref(v___y_767_);
lean_dec(v___y_766_);
lean_dec_ref(v___y_765_);
lean_dec(v___y_764_);
lean_dec_ref(v___y_763_);
lean_dec(v___y_762_);
lean_dec_ref(v___y_761_);
lean_dec(v___y_760_);
lean_dec(v___y_759_);
return v_res_770_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1_spec__2___redArg(lean_object* v_keys_771_, lean_object* v_vals_772_, lean_object* v_i_773_, lean_object* v_k_774_){
_start:
{
lean_object* v___x_775_; uint8_t v___x_776_; 
v___x_775_ = lean_array_get_size(v_keys_771_);
v___x_776_ = lean_nat_dec_lt(v_i_773_, v___x_775_);
if (v___x_776_ == 0)
{
lean_object* v___x_777_; 
lean_dec(v_i_773_);
v___x_777_ = lean_box(0);
return v___x_777_;
}
else
{
lean_object* v_k_x27_778_; uint8_t v___x_779_; 
v_k_x27_778_ = lean_array_fget_borrowed(v_keys_771_, v_i_773_);
v___x_779_ = l_Lean_instBEqHeadIndex_beq(v_k_774_, v_k_x27_778_);
if (v___x_779_ == 0)
{
lean_object* v___x_780_; lean_object* v___x_781_; 
v___x_780_ = lean_unsigned_to_nat(1u);
v___x_781_ = lean_nat_add(v_i_773_, v___x_780_);
lean_dec(v_i_773_);
v_i_773_ = v___x_781_;
goto _start;
}
else
{
lean_object* v___x_783_; lean_object* v___x_784_; 
v___x_783_ = lean_array_fget_borrowed(v_vals_772_, v_i_773_);
lean_dec(v_i_773_);
lean_inc(v___x_783_);
v___x_784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_784_, 0, v___x_783_);
return v___x_784_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_keys_785_, lean_object* v_vals_786_, lean_object* v_i_787_, lean_object* v_k_788_){
_start:
{
lean_object* v_res_789_; 
v_res_789_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1_spec__2___redArg(v_keys_785_, v_vals_786_, v_i_787_, v_k_788_);
lean_dec(v_k_788_);
lean_dec_ref(v_vals_786_);
lean_dec_ref(v_keys_785_);
return v_res_789_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1___redArg(lean_object* v_x_790_, size_t v_x_791_, lean_object* v_x_792_){
_start:
{
if (lean_obj_tag(v_x_790_) == 0)
{
lean_object* v_es_793_; lean_object* v___x_794_; size_t v___x_795_; size_t v___x_796_; lean_object* v_j_797_; lean_object* v___x_798_; 
v_es_793_ = lean_ctor_get(v_x_790_, 0);
v___x_794_ = lean_box(2);
v___x_795_ = ((size_t)31ULL);
v___x_796_ = lean_usize_land(v_x_791_, v___x_795_);
v_j_797_ = lean_usize_to_nat(v___x_796_);
v___x_798_ = lean_array_get_borrowed(v___x_794_, v_es_793_, v_j_797_);
lean_dec(v_j_797_);
switch(lean_obj_tag(v___x_798_))
{
case 0:
{
lean_object* v_key_799_; lean_object* v_val_800_; uint8_t v___x_801_; 
v_key_799_ = lean_ctor_get(v___x_798_, 0);
v_val_800_ = lean_ctor_get(v___x_798_, 1);
v___x_801_ = l_Lean_instBEqHeadIndex_beq(v_x_792_, v_key_799_);
if (v___x_801_ == 0)
{
lean_object* v___x_802_; 
v___x_802_ = lean_box(0);
return v___x_802_;
}
else
{
lean_object* v___x_803_; 
lean_inc(v_val_800_);
v___x_803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_803_, 0, v_val_800_);
return v___x_803_;
}
}
case 1:
{
lean_object* v_node_804_; size_t v___x_805_; size_t v___x_806_; 
v_node_804_ = lean_ctor_get(v___x_798_, 0);
v___x_805_ = ((size_t)5ULL);
v___x_806_ = lean_usize_shift_right(v_x_791_, v___x_805_);
v_x_790_ = v_node_804_;
v_x_791_ = v___x_806_;
goto _start;
}
default: 
{
lean_object* v___x_808_; 
v___x_808_ = lean_box(0);
return v___x_808_;
}
}
}
else
{
lean_object* v_ks_809_; lean_object* v_vs_810_; lean_object* v___x_811_; lean_object* v___x_812_; 
v_ks_809_ = lean_ctor_get(v_x_790_, 0);
v_vs_810_ = lean_ctor_get(v_x_790_, 1);
v___x_811_ = lean_unsigned_to_nat(0u);
v___x_812_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1_spec__2___redArg(v_ks_809_, v_vs_810_, v___x_811_, v_x_792_);
return v___x_812_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_790_ = stack[0].m_obj;
size_t v_x_791_ = stack[1].m_num;
lean_object* v_x_792_ = stack[2].m_obj;
lean_object* v_res_813_;
v_res_813_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1___redArg(v_x_790_, v_x_791_, v_x_792_);
stack->m_obj
 = v_res_813_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1___redArg___boxed(lean_object* v_x_814_, lean_object* v_x_815_, lean_object* v_x_816_){
_start:
{
size_t v_x_9572__boxed_817_; lean_object* v_res_818_; 
v_x_9572__boxed_817_ = lean_unbox_usize(v_x_815_);
lean_dec(v_x_815_);
v_res_818_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1___redArg(v_x_814_, v_x_9572__boxed_817_, v_x_816_);
lean_dec(v_x_816_);
lean_dec_ref(v_x_814_);
return v_res_818_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1___redArg(lean_object* v_x_819_, lean_object* v_x_820_){
_start:
{
uint64_t v___x_821_; size_t v___x_822_; lean_object* v___x_823_; 
v___x_821_ = l_Lean_HeadIndex_hash(v_x_820_);
v___x_822_ = lean_uint64_to_usize(v___x_821_);
v___x_823_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1___redArg(v_x_819_, v___x_822_, v_x_820_);
return v___x_823_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1___redArg___boxed(lean_object* v_x_824_, lean_object* v_x_825_){
_start:
{
lean_object* v_res_826_; 
v_res_826_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1___redArg(v_x_824_, v_x_825_);
lean_dec(v_x_825_);
lean_dec_ref(v_x_824_);
return v_res_826_;
}
}
lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__0___redArg(lean_object* v_f_827_, lean_object* v_as_x27_828_, lean_object* v_b_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_){
_start:
{
if (lean_obj_tag(v_as_x27_828_) == 0)
{
lean_object* v___x_841_; 
v___x_841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_841_, 0, v_b_829_);
return v___x_841_;
}
else
{
lean_object* v_head_842_; lean_object* v_tail_843_; lean_object* v___x_844_; uint8_t v___y_846_; uint8_t v___x_850_; 
v_head_842_ = lean_ctor_get(v_as_x27_828_, 0);
v_tail_843_ = lean_ctor_get(v_as_x27_828_, 1);
v___x_844_ = lean_box(0);
v___x_850_ = l_Lean_Expr_isApp(v_head_842_);
if (v___x_850_ == 0)
{
v___y_846_ = v___x_850_;
goto v___jp_845_;
}
else
{
lean_object* v___x_851_; size_t v___x_852_; size_t v___x_853_; uint8_t v___x_854_; 
v___x_851_ = l_Lean_Expr_appFn_x21(v_head_842_);
v___x_852_ = lean_ptr_addr(v___x_851_);
lean_dec_ref(v___x_851_);
v___x_853_ = lean_ptr_addr(v_f_827_);
v___x_854_ = lean_usize_dec_eq(v___x_852_, v___x_853_);
v___y_846_ = v___x_854_;
goto v___jp_845_;
}
v___jp_845_:
{
if (v___y_846_ == 0)
{
v_as_x27_828_ = v_tail_843_;
v_b_829_ = v___x_844_;
goto _start;
}
else
{
lean_object* v___x_848_; 
lean_inc(v_head_842_);
v___x_848_ = l_Lean_Meta_Grind_mkInjEq(v_head_842_, v___y_830_, v___y_831_, v___y_832_, v___y_833_, v___y_834_, v___y_835_, v___y_836_, v___y_837_, v___y_838_, v___y_839_);
if (lean_obj_tag(v___x_848_) == 0)
{
lean_dec_ref_known(v___x_848_, 1);
v_as_x27_828_ = v_tail_843_;
v_b_829_ = v___x_844_;
goto _start;
}
else
{
return v___x_848_;
}
}
}
}
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_827_ = stack[0].m_obj;
lean_object* v_as_x27_828_ = stack[1].m_obj;
lean_object* v_b_829_ = stack[2].m_obj;
lean_object* v___y_830_ = stack[3].m_obj;
lean_object* v___y_831_ = stack[4].m_obj;
lean_object* v___y_832_ = stack[5].m_obj;
lean_object* v___y_833_ = stack[6].m_obj;
lean_object* v___y_834_ = stack[7].m_obj;
lean_object* v___y_835_ = stack[8].m_obj;
lean_object* v___y_836_ = stack[9].m_obj;
lean_object* v___y_837_ = stack[10].m_obj;
lean_object* v___y_838_ = stack[11].m_obj;
lean_object* v___y_839_ = stack[12].m_obj;
lean_object* v_res_855_;
v_res_855_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__0___redArg(v_f_827_, v_as_x27_828_, v_b_829_, v___y_830_, v___y_831_, v___y_832_, v___y_833_, v___y_834_, v___y_835_, v___y_836_, v___y_837_, v___y_838_, v___y_839_);
stack->m_obj
 = v_res_855_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__0___redArg___boxed(lean_object* v_f_856_, lean_object* v_as_x27_857_, lean_object* v_b_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_){
_start:
{
lean_object* v_res_870_; 
v_res_870_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__0___redArg(v_f_856_, v_as_x27_857_, v_b_858_, v___y_859_, v___y_860_, v___y_861_, v___y_862_, v___y_863_, v___y_864_, v___y_865_, v___y_866_, v___y_867_, v___y_868_);
lean_dec(v___y_868_);
lean_dec_ref(v___y_867_);
lean_dec(v___y_866_);
lean_dec_ref(v___y_865_);
lean_dec(v___y_864_);
lean_dec_ref(v___y_863_);
lean_dec(v___y_862_);
lean_dec_ref(v___y_861_);
lean_dec(v___y_860_);
lean_dec(v___y_859_);
lean_dec(v_as_x27_857_);
lean_dec_ref(v_f_856_);
return v_res_870_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn(lean_object* v_us_871_, lean_object* v_00_u03b1_872_, lean_object* v_00_u03b2_873_, lean_object* v_f_874_, lean_object* v_h_875_, lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_a_879_, lean_object* v_a_880_, lean_object* v_a_881_, lean_object* v_a_882_, lean_object* v_a_883_, lean_object* v_a_884_, lean_object* v_a_885_){
_start:
{
lean_object* v___x_887_; lean_object* v_toGoalState_888_; lean_object* v_inj_889_; lean_object* v_mvarId_890_; lean_object* v___x_892_; uint8_t v_isShared_893_; uint8_t v_isSharedCheck_954_; 
v___x_887_ = lean_st_ref_take(v_a_876_);
v_toGoalState_888_ = lean_ctor_get(v___x_887_, 0);
lean_inc_ref(v_toGoalState_888_);
v_inj_889_ = lean_ctor_get(v_toGoalState_888_, 13);
lean_inc_ref(v_inj_889_);
v_mvarId_890_ = lean_ctor_get(v___x_887_, 1);
v_isSharedCheck_954_ = !lean_is_exclusive(v___x_887_);
if (v_isSharedCheck_954_ == 0)
{
lean_object* v_unused_955_; 
v_unused_955_ = lean_ctor_get(v___x_887_, 0);
lean_dec(v_unused_955_);
v___x_892_ = v___x_887_;
v_isShared_893_ = v_isSharedCheck_954_;
goto v_resetjp_891_;
}
else
{
lean_inc(v_mvarId_890_);
lean_dec(v___x_887_);
v___x_892_ = lean_box(0);
v_isShared_893_ = v_isSharedCheck_954_;
goto v_resetjp_891_;
}
v_resetjp_891_:
{
lean_object* v_nextDeclIdx_894_; lean_object* v_enodeMap_895_; lean_object* v_exprs_896_; lean_object* v_parents_897_; lean_object* v_congrTable_898_; lean_object* v_appMap_899_; lean_object* v_indicesFound_900_; lean_object* v_toProcess_901_; uint8_t v_inconsistent_902_; lean_object* v_nextIdx_903_; lean_object* v_newRawFacts_904_; lean_object* v_facts_905_; lean_object* v_extThms_906_; lean_object* v_ematch_907_; lean_object* v_split_908_; lean_object* v_clean_909_; lean_object* v_sstates_910_; lean_object* v___x_912_; uint8_t v_isShared_913_; uint8_t v_isSharedCheck_952_; 
v_nextDeclIdx_894_ = lean_ctor_get(v_toGoalState_888_, 0);
v_enodeMap_895_ = lean_ctor_get(v_toGoalState_888_, 1);
v_exprs_896_ = lean_ctor_get(v_toGoalState_888_, 2);
v_parents_897_ = lean_ctor_get(v_toGoalState_888_, 3);
v_congrTable_898_ = lean_ctor_get(v_toGoalState_888_, 4);
v_appMap_899_ = lean_ctor_get(v_toGoalState_888_, 5);
v_indicesFound_900_ = lean_ctor_get(v_toGoalState_888_, 6);
v_toProcess_901_ = lean_ctor_get(v_toGoalState_888_, 7);
v_inconsistent_902_ = lean_ctor_get_uint8(v_toGoalState_888_, sizeof(void*)*17);
v_nextIdx_903_ = lean_ctor_get(v_toGoalState_888_, 8);
v_newRawFacts_904_ = lean_ctor_get(v_toGoalState_888_, 9);
v_facts_905_ = lean_ctor_get(v_toGoalState_888_, 10);
v_extThms_906_ = lean_ctor_get(v_toGoalState_888_, 11);
v_ematch_907_ = lean_ctor_get(v_toGoalState_888_, 12);
v_split_908_ = lean_ctor_get(v_toGoalState_888_, 14);
v_clean_909_ = lean_ctor_get(v_toGoalState_888_, 15);
v_sstates_910_ = lean_ctor_get(v_toGoalState_888_, 16);
v_isSharedCheck_952_ = !lean_is_exclusive(v_toGoalState_888_);
if (v_isSharedCheck_952_ == 0)
{
lean_object* v_unused_953_; 
v_unused_953_ = lean_ctor_get(v_toGoalState_888_, 13);
lean_dec(v_unused_953_);
v___x_912_ = v_toGoalState_888_;
v_isShared_913_ = v_isSharedCheck_952_;
goto v_resetjp_911_;
}
else
{
lean_inc(v_sstates_910_);
lean_inc(v_clean_909_);
lean_inc(v_split_908_);
lean_inc(v_ematch_907_);
lean_inc(v_extThms_906_);
lean_inc(v_facts_905_);
lean_inc(v_newRawFacts_904_);
lean_inc(v_nextIdx_903_);
lean_inc(v_toProcess_901_);
lean_inc(v_indicesFound_900_);
lean_inc(v_appMap_899_);
lean_inc(v_congrTable_898_);
lean_inc(v_parents_897_);
lean_inc(v_exprs_896_);
lean_inc(v_enodeMap_895_);
lean_inc(v_nextDeclIdx_894_);
lean_dec(v_toGoalState_888_);
v___x_912_ = lean_box(0);
v_isShared_913_ = v_isSharedCheck_952_;
goto v_resetjp_911_;
}
v_resetjp_911_:
{
lean_object* v_thms_914_; lean_object* v_fns_915_; lean_object* v___x_917_; uint8_t v_isShared_918_; uint8_t v_isSharedCheck_951_; 
v_thms_914_ = lean_ctor_get(v_inj_889_, 0);
v_fns_915_ = lean_ctor_get(v_inj_889_, 1);
v_isSharedCheck_951_ = !lean_is_exclusive(v_inj_889_);
if (v_isSharedCheck_951_ == 0)
{
v___x_917_ = v_inj_889_;
v_isShared_918_ = v_isSharedCheck_951_;
goto v_resetjp_916_;
}
else
{
lean_inc(v_fns_915_);
lean_inc(v_thms_914_);
lean_dec(v_inj_889_);
v___x_917_ = lean_box(0);
v_isShared_918_ = v_isSharedCheck_951_;
goto v_resetjp_916_;
}
v_resetjp_916_:
{
lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_923_; 
v___x_919_ = lean_box(0);
v___x_920_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_920_, 0, v_us_871_);
lean_ctor_set(v___x_920_, 1, v_00_u03b1_872_);
lean_ctor_set(v___x_920_, 2, v_00_u03b2_873_);
lean_ctor_set(v___x_920_, 3, v_h_875_);
lean_ctor_set(v___x_920_, 4, v___x_919_);
lean_inc_ref(v_f_874_);
v___x_921_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2___redArg(v_fns_915_, v_f_874_, v___x_920_);
if (v_isShared_918_ == 0)
{
lean_ctor_set(v___x_917_, 1, v___x_921_);
v___x_923_ = v___x_917_;
goto v_reusejp_922_;
}
else
{
lean_object* v_reuseFailAlloc_950_; 
v_reuseFailAlloc_950_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_950_, 0, v_thms_914_);
lean_ctor_set(v_reuseFailAlloc_950_, 1, v___x_921_);
v___x_923_ = v_reuseFailAlloc_950_;
goto v_reusejp_922_;
}
v_reusejp_922_:
{
lean_object* v___x_925_; 
if (v_isShared_913_ == 0)
{
lean_ctor_set(v___x_912_, 13, v___x_923_);
v___x_925_ = v___x_912_;
goto v_reusejp_924_;
}
else
{
lean_object* v_reuseFailAlloc_949_; 
v_reuseFailAlloc_949_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_949_, 0, v_nextDeclIdx_894_);
lean_ctor_set(v_reuseFailAlloc_949_, 1, v_enodeMap_895_);
lean_ctor_set(v_reuseFailAlloc_949_, 2, v_exprs_896_);
lean_ctor_set(v_reuseFailAlloc_949_, 3, v_parents_897_);
lean_ctor_set(v_reuseFailAlloc_949_, 4, v_congrTable_898_);
lean_ctor_set(v_reuseFailAlloc_949_, 5, v_appMap_899_);
lean_ctor_set(v_reuseFailAlloc_949_, 6, v_indicesFound_900_);
lean_ctor_set(v_reuseFailAlloc_949_, 7, v_toProcess_901_);
lean_ctor_set(v_reuseFailAlloc_949_, 8, v_nextIdx_903_);
lean_ctor_set(v_reuseFailAlloc_949_, 9, v_newRawFacts_904_);
lean_ctor_set(v_reuseFailAlloc_949_, 10, v_facts_905_);
lean_ctor_set(v_reuseFailAlloc_949_, 11, v_extThms_906_);
lean_ctor_set(v_reuseFailAlloc_949_, 12, v_ematch_907_);
lean_ctor_set(v_reuseFailAlloc_949_, 13, v___x_923_);
lean_ctor_set(v_reuseFailAlloc_949_, 14, v_split_908_);
lean_ctor_set(v_reuseFailAlloc_949_, 15, v_clean_909_);
lean_ctor_set(v_reuseFailAlloc_949_, 16, v_sstates_910_);
lean_ctor_set_uint8(v_reuseFailAlloc_949_, sizeof(void*)*17, v_inconsistent_902_);
v___x_925_ = v_reuseFailAlloc_949_;
goto v_reusejp_924_;
}
v_reusejp_924_:
{
lean_object* v___x_927_; 
if (v_isShared_893_ == 0)
{
lean_ctor_set(v___x_892_, 0, v___x_925_);
v___x_927_ = v___x_892_;
goto v_reusejp_926_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v___x_925_);
lean_ctor_set(v_reuseFailAlloc_948_, 1, v_mvarId_890_);
v___x_927_ = v_reuseFailAlloc_948_;
goto v_reusejp_926_;
}
v_reusejp_926_:
{
lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___y_932_; lean_object* v_toGoalState_943_; lean_object* v_appMap_944_; lean_object* v___x_945_; 
v___x_928_ = lean_st_ref_put(v_a_876_, v___x_927_);
lean_inc_ref(v_f_874_);
v___x_929_ = l_Lean_Expr_toHeadIndex(v_f_874_);
v___x_930_ = lean_st_ref_get(v_a_876_);
v_toGoalState_943_ = lean_ctor_get(v___x_930_, 0);
lean_inc_ref(v_toGoalState_943_);
lean_dec(v___x_930_);
v_appMap_944_ = lean_ctor_get(v_toGoalState_943_, 5);
lean_inc_ref(v_appMap_944_);
lean_dec_ref(v_toGoalState_943_);
v___x_945_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1___redArg(v_appMap_944_, v___x_929_);
lean_dec(v___x_929_);
lean_dec_ref(v_appMap_944_);
if (lean_obj_tag(v___x_945_) == 0)
{
lean_object* v___x_946_; 
v___x_946_ = lean_box(0);
v___y_932_ = v___x_946_;
goto v___jp_931_;
}
else
{
lean_object* v_val_947_; 
v_val_947_ = lean_ctor_get(v___x_945_, 0);
lean_inc(v_val_947_);
lean_dec_ref_known(v___x_945_, 1);
v___y_932_ = v_val_947_;
goto v___jp_931_;
}
v___jp_931_:
{
lean_object* v___x_933_; lean_object* v___x_934_; 
v___x_933_ = lean_box(0);
v___x_934_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__0___redArg(v_f_874_, v___y_932_, v___x_933_, v_a_876_, v_a_877_, v_a_878_, v_a_879_, v_a_880_, v_a_881_, v_a_882_, v_a_883_, v_a_884_, v_a_885_);
lean_dec(v___y_932_);
lean_dec_ref(v_f_874_);
if (lean_obj_tag(v___x_934_) == 0)
{
lean_object* v___x_936_; uint8_t v_isShared_937_; uint8_t v_isSharedCheck_941_; 
v_isSharedCheck_941_ = !lean_is_exclusive(v___x_934_);
if (v_isSharedCheck_941_ == 0)
{
lean_object* v_unused_942_; 
v_unused_942_ = lean_ctor_get(v___x_934_, 0);
lean_dec(v_unused_942_);
v___x_936_ = v___x_934_;
v_isShared_937_ = v_isSharedCheck_941_;
goto v_resetjp_935_;
}
else
{
lean_dec(v___x_934_);
v___x_936_ = lean_box(0);
v_isShared_937_ = v_isSharedCheck_941_;
goto v_resetjp_935_;
}
v_resetjp_935_:
{
lean_object* v___x_939_; 
if (v_isShared_937_ == 0)
{
lean_ctor_set(v___x_936_, 0, v___x_933_);
v___x_939_ = v___x_936_;
goto v_reusejp_938_;
}
else
{
lean_object* v_reuseFailAlloc_940_; 
v_reuseFailAlloc_940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_940_, 0, v___x_933_);
v___x_939_ = v_reuseFailAlloc_940_;
goto v_reusejp_938_;
}
v_reusejp_938_:
{
return v___x_939_;
}
}
}
else
{
return v___x_934_;
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
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_0interp(lean_interpreter_value* stack)
{
lean_object* v_us_871_ = stack[0].m_obj;
lean_object* v_00_u03b1_872_ = stack[1].m_obj;
lean_object* v_00_u03b2_873_ = stack[2].m_obj;
lean_object* v_f_874_ = stack[3].m_obj;
lean_object* v_h_875_ = stack[4].m_obj;
lean_object* v_a_876_ = stack[5].m_obj;
lean_object* v_a_877_ = stack[6].m_obj;
lean_object* v_a_878_ = stack[7].m_obj;
lean_object* v_a_879_ = stack[8].m_obj;
lean_object* v_a_880_ = stack[9].m_obj;
lean_object* v_a_881_ = stack[10].m_obj;
lean_object* v_a_882_ = stack[11].m_obj;
lean_object* v_a_883_ = stack[12].m_obj;
lean_object* v_a_884_ = stack[13].m_obj;
lean_object* v_a_885_ = stack[14].m_obj;
lean_object* v_res_956_;
v_res_956_ = l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn(v_us_871_, v_00_u03b1_872_, v_00_u03b2_873_, v_f_874_, v_h_875_, v_a_876_, v_a_877_, v_a_878_, v_a_879_, v_a_880_, v_a_881_, v_a_882_, v_a_883_, v_a_884_, v_a_885_);
stack->m_obj
 = v_res_956_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn___boxed(lean_object* v_us_957_, lean_object* v_00_u03b1_958_, lean_object* v_00_u03b2_959_, lean_object* v_f_960_, lean_object* v_h_961_, lean_object* v_a_962_, lean_object* v_a_963_, lean_object* v_a_964_, lean_object* v_a_965_, lean_object* v_a_966_, lean_object* v_a_967_, lean_object* v_a_968_, lean_object* v_a_969_, lean_object* v_a_970_, lean_object* v_a_971_, lean_object* v_a_972_){
_start:
{
lean_object* v_res_973_; 
v_res_973_ = l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn(v_us_957_, v_00_u03b1_958_, v_00_u03b2_959_, v_f_960_, v_h_961_, v_a_962_, v_a_963_, v_a_964_, v_a_965_, v_a_966_, v_a_967_, v_a_968_, v_a_969_, v_a_970_, v_a_971_);
lean_dec(v_a_971_);
lean_dec_ref(v_a_970_);
lean_dec(v_a_969_);
lean_dec_ref(v_a_968_);
lean_dec(v_a_967_);
lean_dec_ref(v_a_966_);
lean_dec(v_a_965_);
lean_dec_ref(v_a_964_);
lean_dec(v_a_963_);
lean_dec(v_a_962_);
return v_res_973_;
}
}
lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__0(lean_object* v_f_974_, lean_object* v_as_975_, lean_object* v_as_x27_976_, lean_object* v_b_977_, lean_object* v_a_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_){
_start:
{
lean_object* v___x_990_; 
v___x_990_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__0___redArg(v_f_974_, v_as_x27_976_, v_b_977_, v___y_979_, v___y_980_, v___y_981_, v___y_982_, v___y_983_, v___y_984_, v___y_985_, v___y_986_, v___y_987_, v___y_988_);
return v___x_990_;
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_974_ = stack[0].m_obj;
lean_object* v_as_975_ = stack[1].m_obj;
lean_object* v_as_x27_976_ = stack[2].m_obj;
lean_object* v_b_977_ = stack[3].m_obj;
lean_object* v___y_979_ = stack[5].m_obj;
lean_object* v___y_980_ = stack[6].m_obj;
lean_object* v___y_981_ = stack[7].m_obj;
lean_object* v___y_982_ = stack[8].m_obj;
lean_object* v___y_983_ = stack[9].m_obj;
lean_object* v___y_984_ = stack[10].m_obj;
lean_object* v___y_985_ = stack[11].m_obj;
lean_object* v___y_986_ = stack[12].m_obj;
lean_object* v___y_987_ = stack[13].m_obj;
lean_object* v___y_988_ = stack[14].m_obj;
lean_object* v_res_991_;
v_res_991_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__0(v_f_974_, v_as_975_, v_as_x27_976_, v_b_977_, lean_box(0), v___y_979_, v___y_980_, v___y_981_, v___y_982_, v___y_983_, v___y_984_, v___y_985_, v___y_986_, v___y_987_, v___y_988_);
stack->m_obj
 = v_res_991_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__0___boxed(lean_object* v_f_992_, lean_object* v_as_993_, lean_object* v_as_x27_994_, lean_object* v_b_995_, lean_object* v_a_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_){
_start:
{
lean_object* v_res_1008_; 
v_res_1008_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__0(v_f_992_, v_as_993_, v_as_x27_994_, v_b_995_, v_a_996_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_, v___y_1001_, v___y_1002_, v___y_1003_, v___y_1004_, v___y_1005_, v___y_1006_);
lean_dec(v___y_1006_);
lean_dec_ref(v___y_1005_);
lean_dec(v___y_1004_);
lean_dec_ref(v___y_1003_);
lean_dec(v___y_1002_);
lean_dec_ref(v___y_1001_);
lean_dec(v___y_1000_);
lean_dec_ref(v___y_999_);
lean_dec(v___y_998_);
lean_dec(v___y_997_);
lean_dec(v_as_x27_994_);
lean_dec(v_as_993_);
lean_dec_ref(v_f_992_);
return v_res_1008_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1(lean_object* v_00_u03b2_1009_, lean_object* v_x_1010_, lean_object* v_x_1011_){
_start:
{
lean_object* v___x_1012_; 
v___x_1012_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1___redArg(v_x_1010_, v_x_1011_);
return v___x_1012_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1___boxed(lean_object* v_00_u03b2_1013_, lean_object* v_x_1014_, lean_object* v_x_1015_){
_start:
{
lean_object* v_res_1016_; 
v_res_1016_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1(v_00_u03b2_1013_, v_x_1014_, v_x_1015_);
lean_dec(v_x_1015_);
lean_dec_ref(v_x_1014_);
return v_res_1016_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1(lean_object* v_00_u03b2_1017_, lean_object* v_x_1018_, size_t v_x_1019_, lean_object* v_x_1020_){
_start:
{
lean_object* v___x_1021_; 
v___x_1021_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1___redArg(v_x_1018_, v_x_1019_, v_x_1020_);
return v___x_1021_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1018_ = stack[1].m_obj;
size_t v_x_1019_ = stack[2].m_num;
lean_object* v_x_1020_ = stack[3].m_obj;
lean_object* v_res_1022_;
v_res_1022_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1(lean_box(0), v_x_1018_, v_x_1019_, v_x_1020_);
stack->m_obj
 = v_res_1022_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1___boxed(lean_object* v_00_u03b2_1023_, lean_object* v_x_1024_, lean_object* v_x_1025_, lean_object* v_x_1026_){
_start:
{
size_t v_x_9980__boxed_1027_; lean_object* v_res_1028_; 
v_x_9980__boxed_1027_ = lean_unbox_usize(v_x_1025_);
lean_dec(v_x_1025_);
v_res_1028_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1(v_00_u03b2_1023_, v_x_1024_, v_x_9980__boxed_1027_, v_x_1026_);
lean_dec(v_x_1026_);
lean_dec_ref(v_x_1024_);
return v_res_1028_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_1029_, lean_object* v_keys_1030_, lean_object* v_vals_1031_, lean_object* v_heq_1032_, lean_object* v_i_1033_, lean_object* v_k_1034_){
_start:
{
lean_object* v___x_1035_; 
v___x_1035_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1_spec__2___redArg(v_keys_1030_, v_vals_1031_, v_i_1033_, v_k_1034_);
return v___x_1035_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1036_, lean_object* v_keys_1037_, lean_object* v_vals_1038_, lean_object* v_heq_1039_, lean_object* v_i_1040_, lean_object* v_k_1041_){
_start:
{
lean_object* v_res_1042_; 
v_res_1042_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1_spec__2(v_00_u03b2_1036_, v_keys_1037_, v_vals_1038_, v_heq_1039_, v_i_1040_, v_k_1041_);
lean_dec(v_k_1041_);
lean_dec_ref(v_vals_1038_);
lean_dec_ref(v_keys_1037_);
return v_res_1042_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj(lean_object* v_e_1048_, lean_object* v_a_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_, lean_object* v_a_1057_, lean_object* v_a_1058_){
_start:
{
lean_object* v___x_1063_; uint8_t v___x_1064_; 
lean_inc_ref(v_e_1048_);
v___x_1063_ = l_Lean_Expr_cleanupAnnotations(v_e_1048_);
v___x_1064_ = l_Lean_Expr_isApp(v___x_1063_);
if (v___x_1064_ == 0)
{
lean_dec_ref(v___x_1063_);
lean_dec_ref(v_e_1048_);
goto v___jp_1060_;
}
else
{
lean_object* v_arg_1065_; lean_object* v___x_1066_; uint8_t v___x_1067_; 
v_arg_1065_ = lean_ctor_get(v___x_1063_, 1);
lean_inc_ref(v_arg_1065_);
v___x_1066_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1063_);
v___x_1067_ = l_Lean_Expr_isApp(v___x_1066_);
if (v___x_1067_ == 0)
{
lean_dec_ref(v___x_1066_);
lean_dec_ref(v_arg_1065_);
lean_dec_ref(v_e_1048_);
goto v___jp_1060_;
}
else
{
lean_object* v_arg_1068_; lean_object* v___x_1069_; uint8_t v___x_1070_; 
v_arg_1068_ = lean_ctor_get(v___x_1066_, 1);
lean_inc_ref(v_arg_1068_);
v___x_1069_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1066_);
v___x_1070_ = l_Lean_Expr_isApp(v___x_1069_);
if (v___x_1070_ == 0)
{
lean_dec_ref(v___x_1069_);
lean_dec_ref(v_arg_1068_);
lean_dec_ref(v_arg_1065_);
lean_dec_ref(v_e_1048_);
goto v___jp_1060_;
}
else
{
lean_object* v_arg_1071_; lean_object* v___x_1072_; lean_object* v_f_1074_; lean_object* v___y_1075_; lean_object* v___y_1076_; lean_object* v___y_1077_; lean_object* v___y_1078_; lean_object* v___y_1079_; lean_object* v___y_1080_; lean_object* v___y_1081_; lean_object* v___y_1082_; lean_object* v___y_1083_; lean_object* v___y_1084_; lean_object* v___x_1098_; uint8_t v___x_1099_; 
v_arg_1071_ = lean_ctor_get(v___x_1069_, 1);
lean_inc_ref(v_arg_1071_);
v___x_1072_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1069_);
v___x_1098_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj___closed__2));
v___x_1099_ = l_Lean_Expr_isConstOf(v___x_1072_, v___x_1098_);
if (v___x_1099_ == 0)
{
lean_dec_ref(v___x_1072_);
lean_dec_ref(v_arg_1071_);
lean_dec_ref(v_arg_1068_);
lean_dec_ref(v_arg_1065_);
lean_dec_ref(v_e_1048_);
goto v___jp_1060_;
}
else
{
lean_object* v___x_1100_; 
lean_inc_ref(v_e_1048_);
v___x_1100_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_e_1048_, v_a_1049_, v_a_1053_, v_a_1055_, v_a_1056_, v_a_1057_, v_a_1058_);
if (lean_obj_tag(v___x_1100_) == 0)
{
lean_object* v_a_1101_; lean_object* v___x_1103_; uint8_t v_isShared_1104_; uint8_t v_isSharedCheck_1136_; 
v_a_1101_ = lean_ctor_get(v___x_1100_, 0);
v_isSharedCheck_1136_ = !lean_is_exclusive(v___x_1100_);
if (v_isSharedCheck_1136_ == 0)
{
v___x_1103_ = v___x_1100_;
v_isShared_1104_ = v_isSharedCheck_1136_;
goto v_resetjp_1102_;
}
else
{
lean_inc(v_a_1101_);
lean_dec(v___x_1100_);
v___x_1103_ = lean_box(0);
v_isShared_1104_ = v_isSharedCheck_1136_;
goto v_resetjp_1102_;
}
v_resetjp_1102_:
{
uint8_t v___x_1105_; 
v___x_1105_ = lean_unbox(v_a_1101_);
lean_dec(v_a_1101_);
if (v___x_1105_ == 0)
{
lean_object* v___x_1106_; lean_object* v___x_1108_; 
lean_dec_ref(v___x_1072_);
lean_dec_ref(v_arg_1071_);
lean_dec_ref(v_arg_1068_);
lean_dec_ref(v_arg_1065_);
lean_dec_ref(v_e_1048_);
v___x_1106_ = lean_box(0);
if (v_isShared_1104_ == 0)
{
lean_ctor_set(v___x_1103_, 0, v___x_1106_);
v___x_1108_ = v___x_1103_;
goto v_reusejp_1107_;
}
else
{
lean_object* v_reuseFailAlloc_1109_; 
v_reuseFailAlloc_1109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1109_, 0, v___x_1106_);
v___x_1108_ = v_reuseFailAlloc_1109_;
goto v_reusejp_1107_;
}
v_reusejp_1107_:
{
return v___x_1108_;
}
}
else
{
lean_object* v___x_1110_; size_t v___x_1111_; size_t v___x_1112_; uint8_t v___x_1113_; 
lean_del_object(v___x_1103_);
lean_inc_ref(v_arg_1065_);
v___x_1110_ = l_Lean_Expr_eta(v_arg_1065_);
v___x_1111_ = lean_ptr_addr(v_arg_1065_);
v___x_1112_ = lean_ptr_addr(v___x_1110_);
v___x_1113_ = lean_usize_dec_eq(v___x_1111_, v___x_1112_);
if (v___x_1113_ == 0)
{
lean_object* v___x_1114_; 
lean_dec_ref(v_arg_1065_);
v___x_1114_ = l_Lean_Meta_Grind_preprocessLight___redArg(v___x_1110_, v_a_1050_, v_a_1051_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_, v_a_1056_, v_a_1057_, v_a_1058_);
if (lean_obj_tag(v___x_1114_) == 0)
{
lean_object* v_a_1115_; lean_object* v___x_1116_; 
v_a_1115_ = lean_ctor_get(v___x_1114_, 0);
lean_inc(v_a_1115_);
lean_dec_ref_known(v___x_1114_, 1);
v___x_1116_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_1048_, v_a_1049_);
if (lean_obj_tag(v___x_1116_) == 0)
{
lean_object* v_a_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; 
v_a_1117_ = lean_ctor_get(v___x_1116_, 0);
lean_inc(v_a_1117_);
lean_dec_ref_known(v___x_1116_, 1);
v___x_1118_ = lean_box(0);
lean_inc(v_a_1058_);
lean_inc_ref(v_a_1057_);
lean_inc(v_a_1056_);
lean_inc_ref(v_a_1055_);
lean_inc(v_a_1054_);
lean_inc_ref(v_a_1053_);
lean_inc(v_a_1052_);
lean_inc_ref(v_a_1051_);
lean_inc(v_a_1050_);
lean_inc(v_a_1049_);
lean_inc(v_a_1115_);
v___x_1119_ = lean_grind_internalize(v_a_1115_, v_a_1117_, v___x_1118_, v_a_1049_, v_a_1050_, v_a_1051_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_, v_a_1056_, v_a_1057_, v_a_1058_);
if (lean_obj_tag(v___x_1119_) == 0)
{
lean_dec_ref_known(v___x_1119_, 1);
v_f_1074_ = v_a_1115_;
v___y_1075_ = v_a_1049_;
v___y_1076_ = v_a_1050_;
v___y_1077_ = v_a_1051_;
v___y_1078_ = v_a_1052_;
v___y_1079_ = v_a_1053_;
v___y_1080_ = v_a_1054_;
v___y_1081_ = v_a_1055_;
v___y_1082_ = v_a_1056_;
v___y_1083_ = v_a_1057_;
v___y_1084_ = v_a_1058_;
goto v___jp_1073_;
}
else
{
lean_dec(v_a_1115_);
lean_dec_ref(v___x_1072_);
lean_dec_ref(v_arg_1071_);
lean_dec_ref(v_arg_1068_);
lean_dec_ref(v_e_1048_);
return v___x_1119_;
}
}
else
{
lean_object* v_a_1120_; lean_object* v___x_1122_; uint8_t v_isShared_1123_; uint8_t v_isSharedCheck_1127_; 
lean_dec(v_a_1115_);
lean_dec_ref(v___x_1072_);
lean_dec_ref(v_arg_1071_);
lean_dec_ref(v_arg_1068_);
lean_dec_ref(v_e_1048_);
v_a_1120_ = lean_ctor_get(v___x_1116_, 0);
v_isSharedCheck_1127_ = !lean_is_exclusive(v___x_1116_);
if (v_isSharedCheck_1127_ == 0)
{
v___x_1122_ = v___x_1116_;
v_isShared_1123_ = v_isSharedCheck_1127_;
goto v_resetjp_1121_;
}
else
{
lean_inc(v_a_1120_);
lean_dec(v___x_1116_);
v___x_1122_ = lean_box(0);
v_isShared_1123_ = v_isSharedCheck_1127_;
goto v_resetjp_1121_;
}
v_resetjp_1121_:
{
lean_object* v___x_1125_; 
if (v_isShared_1123_ == 0)
{
v___x_1125_ = v___x_1122_;
goto v_reusejp_1124_;
}
else
{
lean_object* v_reuseFailAlloc_1126_; 
v_reuseFailAlloc_1126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1126_, 0, v_a_1120_);
v___x_1125_ = v_reuseFailAlloc_1126_;
goto v_reusejp_1124_;
}
v_reusejp_1124_:
{
return v___x_1125_;
}
}
}
}
else
{
lean_object* v_a_1128_; lean_object* v___x_1130_; uint8_t v_isShared_1131_; uint8_t v_isSharedCheck_1135_; 
lean_dec_ref(v___x_1072_);
lean_dec_ref(v_arg_1071_);
lean_dec_ref(v_arg_1068_);
lean_dec_ref(v_e_1048_);
v_a_1128_ = lean_ctor_get(v___x_1114_, 0);
v_isSharedCheck_1135_ = !lean_is_exclusive(v___x_1114_);
if (v_isSharedCheck_1135_ == 0)
{
v___x_1130_ = v___x_1114_;
v_isShared_1131_ = v_isSharedCheck_1135_;
goto v_resetjp_1129_;
}
else
{
lean_inc(v_a_1128_);
lean_dec(v___x_1114_);
v___x_1130_ = lean_box(0);
v_isShared_1131_ = v_isSharedCheck_1135_;
goto v_resetjp_1129_;
}
v_resetjp_1129_:
{
lean_object* v___x_1133_; 
if (v_isShared_1131_ == 0)
{
v___x_1133_ = v___x_1130_;
goto v_reusejp_1132_;
}
else
{
lean_object* v_reuseFailAlloc_1134_; 
v_reuseFailAlloc_1134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1134_, 0, v_a_1128_);
v___x_1133_ = v_reuseFailAlloc_1134_;
goto v_reusejp_1132_;
}
v_reusejp_1132_:
{
return v___x_1133_;
}
}
}
}
else
{
lean_dec_ref(v___x_1110_);
v_f_1074_ = v_arg_1065_;
v___y_1075_ = v_a_1049_;
v___y_1076_ = v_a_1050_;
v___y_1077_ = v_a_1051_;
v___y_1078_ = v_a_1052_;
v___y_1079_ = v_a_1053_;
v___y_1080_ = v_a_1054_;
v___y_1081_ = v_a_1055_;
v___y_1082_ = v_a_1056_;
v___y_1083_ = v_a_1057_;
v___y_1084_ = v_a_1058_;
goto v___jp_1073_;
}
}
}
}
else
{
lean_object* v_a_1137_; lean_object* v___x_1139_; uint8_t v_isShared_1140_; uint8_t v_isSharedCheck_1144_; 
lean_dec_ref(v___x_1072_);
lean_dec_ref(v_arg_1071_);
lean_dec_ref(v_arg_1068_);
lean_dec_ref(v_arg_1065_);
lean_dec_ref(v_e_1048_);
v_a_1137_ = lean_ctor_get(v___x_1100_, 0);
v_isSharedCheck_1144_ = !lean_is_exclusive(v___x_1100_);
if (v_isSharedCheck_1144_ == 0)
{
v___x_1139_ = v___x_1100_;
v_isShared_1140_ = v_isSharedCheck_1144_;
goto v_resetjp_1138_;
}
else
{
lean_inc(v_a_1137_);
lean_dec(v___x_1100_);
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
v___jp_1073_:
{
lean_object* v___x_1085_; 
lean_inc_ref(v_e_1048_);
v___x_1085_ = l_Lean_Meta_Grind_mkEqTrueProof(v_e_1048_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_);
if (lean_obj_tag(v___x_1085_) == 0)
{
lean_object* v_a_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; 
v_a_1086_ = lean_ctor_get(v___x_1085_, 0);
lean_inc(v_a_1086_);
lean_dec_ref_known(v___x_1085_, 1);
v___x_1087_ = l_Lean_Expr_constLevels_x21(v___x_1072_);
lean_dec_ref(v___x_1072_);
v___x_1088_ = l_Lean_Meta_mkOfEqTrueCore(v_e_1048_, v_a_1086_);
v___x_1089_ = l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn(v___x_1087_, v_arg_1071_, v_arg_1068_, v_f_1074_, v___x_1088_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_);
return v___x_1089_;
}
else
{
lean_object* v_a_1090_; lean_object* v___x_1092_; uint8_t v_isShared_1093_; uint8_t v_isSharedCheck_1097_; 
lean_dec_ref(v_f_1074_);
lean_dec_ref(v___x_1072_);
lean_dec_ref(v_arg_1071_);
lean_dec_ref(v_arg_1068_);
lean_dec_ref(v_e_1048_);
v_a_1090_ = lean_ctor_get(v___x_1085_, 0);
v_isSharedCheck_1097_ = !lean_is_exclusive(v___x_1085_);
if (v_isSharedCheck_1097_ == 0)
{
v___x_1092_ = v___x_1085_;
v_isShared_1093_ = v_isSharedCheck_1097_;
goto v_resetjp_1091_;
}
else
{
lean_inc(v_a_1090_);
lean_dec(v___x_1085_);
v___x_1092_ = lean_box(0);
v_isShared_1093_ = v_isSharedCheck_1097_;
goto v_resetjp_1091_;
}
v_resetjp_1091_:
{
lean_object* v___x_1095_; 
if (v_isShared_1093_ == 0)
{
v___x_1095_ = v___x_1092_;
goto v_reusejp_1094_;
}
else
{
lean_object* v_reuseFailAlloc_1096_; 
v_reuseFailAlloc_1096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1096_, 0, v_a_1090_);
v___x_1095_ = v_reuseFailAlloc_1096_;
goto v_reusejp_1094_;
}
v_reusejp_1094_:
{
return v___x_1095_;
}
}
}
}
}
}
}
v___jp_1060_:
{
lean_object* v___x_1061_; lean_object* v___x_1062_; 
v___x_1061_ = lean_box(0);
v___x_1062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1062_, 0, v___x_1061_);
return v___x_1062_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1048_ = stack[0].m_obj;
lean_object* v_a_1049_ = stack[1].m_obj;
lean_object* v_a_1050_ = stack[2].m_obj;
lean_object* v_a_1051_ = stack[3].m_obj;
lean_object* v_a_1052_ = stack[4].m_obj;
lean_object* v_a_1053_ = stack[5].m_obj;
lean_object* v_a_1054_ = stack[6].m_obj;
lean_object* v_a_1055_ = stack[7].m_obj;
lean_object* v_a_1056_ = stack[8].m_obj;
lean_object* v_a_1057_ = stack[9].m_obj;
lean_object* v_a_1058_ = stack[10].m_obj;
lean_object* v_res_1145_;
v_res_1145_ = l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj(v_e_1048_, v_a_1049_, v_a_1050_, v_a_1051_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_, v_a_1056_, v_a_1057_, v_a_1058_);
stack->m_obj
 = v_res_1145_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj___boxed(lean_object* v_e_1146_, lean_object* v_a_1147_, lean_object* v_a_1148_, lean_object* v_a_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_, lean_object* v_a_1157_){
_start:
{
lean_object* v_res_1158_; 
v_res_1158_ = l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj(v_e_1146_, v_a_1147_, v_a_1148_, v_a_1149_, v_a_1150_, v_a_1151_, v_a_1152_, v_a_1153_, v_a_1154_, v_a_1155_, v_a_1156_);
lean_dec(v_a_1156_);
lean_dec_ref(v_a_1155_);
lean_dec(v_a_1154_);
lean_dec_ref(v_a_1153_);
lean_dec(v_a_1152_);
lean_dec_ref(v_a_1151_);
lean_dec(v_a_1150_);
lean_dec_ref(v_a_1149_);
lean_dec(v_a_1148_);
lean_dec(v_a_1147_);
return v_res_1158_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj___regBuiltin___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj_declare__1_00___x40_Lean_Meta_Tactic_Grind_PropagateInj_3930705876____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; 
v___x_1160_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj___closed__2));
v___x_1161_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj___boxed), 12, 0);
v___x_1162_ = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(v___x_1160_, v___x_1161_);
return v___x_1162_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj___regBuiltin___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj_declare__1_00___x40_Lean_Meta_Tactic_Grind_PropagateInj_3930705876____hygCtx___hyg_9__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1163_;
v_res_1163_ = l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj___regBuiltin___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj_declare__1_00___x40_Lean_Meta_Tactic_Grind_PropagateInj_3930705876____hygCtx___hyg_9_();
stack->m_obj
 = v_res_1163_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj___regBuiltin___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj_declare__1_00___x40_Lean_Meta_Tactic_Grind_PropagateInj_3930705876____hygCtx___hyg_9____boxed(lean_object* v_a_1164_){
_start:
{
lean_object* v_res_1165_; 
v_res_1165_ = l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj___regBuiltin___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj_declare__1_00___x40_Lean_Meta_Tactic_Grind_PropagateInj_3930705876____hygCtx___hyg_9_();
return v_res_1165_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Propagator(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Injective(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_PropagatorAttr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Simp(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_PropagateInj(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
res = l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj___regBuiltin___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj_declare__1_00___x40_Lean_Meta_Tactic_Grind_PropagateInj_3930705876____hygCtx___hyg_9_();
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
