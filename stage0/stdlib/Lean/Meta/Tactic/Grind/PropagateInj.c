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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1___redArg(lean_object* v_x_49_, size_t v_x_50_, lean_object* v_x_51_){
_start:
{
if (lean_obj_tag(v_x_49_) == 0)
{
lean_object* v_es_52_; lean_object* v___x_53_; size_t v___x_54_; size_t v___x_55_; lean_object* v_j_56_; lean_object* v___x_57_; 
v_es_52_ = lean_ctor_get(v_x_49_, 0);
v___x_53_ = lean_box(2);
v___x_54_ = ((size_t)31ULL);
v___x_55_ = lean_usize_land(v_x_50_, v___x_54_);
v_j_56_ = lean_usize_to_nat(v___x_55_);
v___x_57_ = lean_array_get_borrowed(v___x_53_, v_es_52_, v_j_56_);
lean_dec(v_j_56_);
switch(lean_obj_tag(v___x_57_))
{
case 0:
{
lean_object* v_key_58_; lean_object* v_val_59_; uint8_t v___x_60_; 
v_key_58_ = lean_ctor_get(v___x_57_, 0);
v_val_59_ = lean_ctor_get(v___x_57_, 1);
v___x_60_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_51_, v_key_58_);
if (v___x_60_ == 0)
{
lean_object* v___x_61_; 
v___x_61_ = lean_box(0);
return v___x_61_;
}
else
{
lean_object* v___x_62_; 
lean_inc(v_val_59_);
v___x_62_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_62_, 0, v_val_59_);
return v___x_62_;
}
}
case 1:
{
lean_object* v_node_63_; size_t v___x_64_; size_t v___x_65_; 
v_node_63_ = lean_ctor_get(v___x_57_, 0);
v___x_64_ = ((size_t)5ULL);
v___x_65_ = lean_usize_shift_right(v_x_50_, v___x_64_);
v_x_49_ = v_node_63_;
v_x_50_ = v___x_65_;
goto _start;
}
default: 
{
lean_object* v___x_67_; 
v___x_67_ = lean_box(0);
return v___x_67_;
}
}
}
else
{
lean_object* v_ks_68_; lean_object* v_vs_69_; lean_object* v___x_70_; lean_object* v___x_71_; 
v_ks_68_ = lean_ctor_get(v_x_49_, 0);
v_vs_69_ = lean_ctor_get(v_x_49_, 1);
v___x_70_ = lean_unsigned_to_nat(0u);
v___x_71_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1_spec__2___redArg(v_ks_68_, v_vs_69_, v___x_70_, v_x_51_);
return v___x_71_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1___redArg___boxed(lean_object* v_x_72_, lean_object* v_x_73_, lean_object* v_x_74_){
_start:
{
size_t v_x_9487__boxed_75_; lean_object* v_res_76_; 
v_x_9487__boxed_75_ = lean_unbox_usize(v_x_73_);
lean_dec(v_x_73_);
v_res_76_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1___redArg(v_x_72_, v_x_9487__boxed_75_, v_x_74_);
lean_dec_ref(v_x_74_);
lean_dec_ref(v_x_72_);
return v_res_76_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1___redArg(lean_object* v_x_77_, lean_object* v_x_78_){
_start:
{
uint64_t v___x_79_; size_t v___x_80_; lean_object* v___x_81_; 
v___x_79_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_78_);
v___x_80_ = lean_uint64_to_usize(v___x_79_);
v___x_81_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1___redArg(v_x_77_, v___x_80_, v_x_78_);
return v___x_81_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1___redArg___boxed(lean_object* v_x_82_, lean_object* v_x_83_){
_start:
{
lean_object* v_res_84_; 
v_res_84_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1___redArg(v_x_82_, v_x_83_);
lean_dec_ref(v_x_83_);
lean_dec_ref(v_x_82_);
return v_res_84_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3_spec__5_spec__6___redArg(lean_object* v_x_85_, lean_object* v_x_86_, lean_object* v_x_87_, lean_object* v_x_88_){
_start:
{
lean_object* v_ks_89_; lean_object* v_vs_90_; lean_object* v___x_92_; uint8_t v_isShared_93_; uint8_t v_isSharedCheck_114_; 
v_ks_89_ = lean_ctor_get(v_x_85_, 0);
v_vs_90_ = lean_ctor_get(v_x_85_, 1);
v_isSharedCheck_114_ = !lean_is_exclusive(v_x_85_);
if (v_isSharedCheck_114_ == 0)
{
v___x_92_ = v_x_85_;
v_isShared_93_ = v_isSharedCheck_114_;
goto v_resetjp_91_;
}
else
{
lean_inc(v_vs_90_);
lean_inc(v_ks_89_);
lean_dec(v_x_85_);
v___x_92_ = lean_box(0);
v_isShared_93_ = v_isSharedCheck_114_;
goto v_resetjp_91_;
}
v_resetjp_91_:
{
lean_object* v___x_94_; uint8_t v___x_95_; 
v___x_94_ = lean_array_get_size(v_ks_89_);
v___x_95_ = lean_nat_dec_lt(v_x_86_, v___x_94_);
if (v___x_95_ == 0)
{
lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_99_; 
lean_dec(v_x_86_);
v___x_96_ = lean_array_push(v_ks_89_, v_x_87_);
v___x_97_ = lean_array_push(v_vs_90_, v_x_88_);
if (v_isShared_93_ == 0)
{
lean_ctor_set(v___x_92_, 1, v___x_97_);
lean_ctor_set(v___x_92_, 0, v___x_96_);
v___x_99_ = v___x_92_;
goto v_reusejp_98_;
}
else
{
lean_object* v_reuseFailAlloc_100_; 
v_reuseFailAlloc_100_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_100_, 0, v___x_96_);
lean_ctor_set(v_reuseFailAlloc_100_, 1, v___x_97_);
v___x_99_ = v_reuseFailAlloc_100_;
goto v_reusejp_98_;
}
v_reusejp_98_:
{
return v___x_99_;
}
}
else
{
lean_object* v_k_x27_101_; uint8_t v___x_102_; 
v_k_x27_101_ = lean_array_fget_borrowed(v_ks_89_, v_x_86_);
v___x_102_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_87_, v_k_x27_101_);
if (v___x_102_ == 0)
{
lean_object* v___x_104_; 
if (v_isShared_93_ == 0)
{
v___x_104_ = v___x_92_;
goto v_reusejp_103_;
}
else
{
lean_object* v_reuseFailAlloc_108_; 
v_reuseFailAlloc_108_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_108_, 0, v_ks_89_);
lean_ctor_set(v_reuseFailAlloc_108_, 1, v_vs_90_);
v___x_104_ = v_reuseFailAlloc_108_;
goto v_reusejp_103_;
}
v_reusejp_103_:
{
lean_object* v___x_105_; lean_object* v___x_106_; 
v___x_105_ = lean_unsigned_to_nat(1u);
v___x_106_ = lean_nat_add(v_x_86_, v___x_105_);
lean_dec(v_x_86_);
v_x_85_ = v___x_104_;
v_x_86_ = v___x_106_;
goto _start;
}
}
else
{
lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_112_; 
v___x_109_ = lean_array_fset(v_ks_89_, v_x_86_, v_x_87_);
v___x_110_ = lean_array_fset(v_vs_90_, v_x_86_, v_x_88_);
lean_dec(v_x_86_);
if (v_isShared_93_ == 0)
{
lean_ctor_set(v___x_92_, 1, v___x_110_);
lean_ctor_set(v___x_92_, 0, v___x_109_);
v___x_112_ = v___x_92_;
goto v_reusejp_111_;
}
else
{
lean_object* v_reuseFailAlloc_113_; 
v_reuseFailAlloc_113_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_113_, 0, v___x_109_);
lean_ctor_set(v_reuseFailAlloc_113_, 1, v___x_110_);
v___x_112_ = v_reuseFailAlloc_113_;
goto v_reusejp_111_;
}
v_reusejp_111_:
{
return v___x_112_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3_spec__5___redArg(lean_object* v_n_115_, lean_object* v_k_116_, lean_object* v_v_117_){
_start:
{
lean_object* v___x_118_; lean_object* v___x_119_; 
v___x_118_ = lean_unsigned_to_nat(0u);
v___x_119_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3_spec__5_spec__6___redArg(v_n_115_, v___x_118_, v_k_116_, v_v_117_);
return v___x_119_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_120_; 
v___x_120_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_120_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3___redArg(lean_object* v_x_121_, size_t v_x_122_, size_t v_x_123_, lean_object* v_x_124_, lean_object* v_x_125_){
_start:
{
if (lean_obj_tag(v_x_121_) == 0)
{
lean_object* v_es_126_; size_t v___x_127_; size_t v___x_128_; lean_object* v_j_129_; lean_object* v___x_130_; uint8_t v___x_131_; 
v_es_126_ = lean_ctor_get(v_x_121_, 0);
v___x_127_ = ((size_t)31ULL);
v___x_128_ = lean_usize_land(v_x_122_, v___x_127_);
v_j_129_ = lean_usize_to_nat(v___x_128_);
v___x_130_ = lean_array_get_size(v_es_126_);
v___x_131_ = lean_nat_dec_lt(v_j_129_, v___x_130_);
if (v___x_131_ == 0)
{
lean_dec(v_j_129_);
lean_dec(v_x_125_);
lean_dec_ref(v_x_124_);
return v_x_121_;
}
else
{
lean_object* v___x_133_; uint8_t v_isShared_134_; uint8_t v_isSharedCheck_170_; 
lean_inc_ref(v_es_126_);
v_isSharedCheck_170_ = !lean_is_exclusive(v_x_121_);
if (v_isSharedCheck_170_ == 0)
{
lean_object* v_unused_171_; 
v_unused_171_ = lean_ctor_get(v_x_121_, 0);
lean_dec(v_unused_171_);
v___x_133_ = v_x_121_;
v_isShared_134_ = v_isSharedCheck_170_;
goto v_resetjp_132_;
}
else
{
lean_dec(v_x_121_);
v___x_133_ = lean_box(0);
v_isShared_134_ = v_isSharedCheck_170_;
goto v_resetjp_132_;
}
v_resetjp_132_:
{
lean_object* v_v_135_; lean_object* v___x_136_; lean_object* v_xs_x27_137_; lean_object* v___y_139_; 
v_v_135_ = lean_array_fget(v_es_126_, v_j_129_);
v___x_136_ = lean_box(0);
v_xs_x27_137_ = lean_array_fset(v_es_126_, v_j_129_, v___x_136_);
switch(lean_obj_tag(v_v_135_))
{
case 0:
{
lean_object* v_key_144_; lean_object* v_val_145_; lean_object* v___x_147_; uint8_t v_isShared_148_; uint8_t v_isSharedCheck_155_; 
v_key_144_ = lean_ctor_get(v_v_135_, 0);
v_val_145_ = lean_ctor_get(v_v_135_, 1);
v_isSharedCheck_155_ = !lean_is_exclusive(v_v_135_);
if (v_isSharedCheck_155_ == 0)
{
v___x_147_ = v_v_135_;
v_isShared_148_ = v_isSharedCheck_155_;
goto v_resetjp_146_;
}
else
{
lean_inc(v_val_145_);
lean_inc(v_key_144_);
lean_dec(v_v_135_);
v___x_147_ = lean_box(0);
v_isShared_148_ = v_isSharedCheck_155_;
goto v_resetjp_146_;
}
v_resetjp_146_:
{
uint8_t v___x_149_; 
v___x_149_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_124_, v_key_144_);
if (v___x_149_ == 0)
{
lean_object* v___x_150_; lean_object* v___x_151_; 
lean_del_object(v___x_147_);
v___x_150_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_144_, v_val_145_, v_x_124_, v_x_125_);
v___x_151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_151_, 0, v___x_150_);
v___y_139_ = v___x_151_;
goto v___jp_138_;
}
else
{
lean_object* v___x_153_; 
lean_dec(v_val_145_);
lean_dec(v_key_144_);
if (v_isShared_148_ == 0)
{
lean_ctor_set(v___x_147_, 1, v_x_125_);
lean_ctor_set(v___x_147_, 0, v_x_124_);
v___x_153_ = v___x_147_;
goto v_reusejp_152_;
}
else
{
lean_object* v_reuseFailAlloc_154_; 
v_reuseFailAlloc_154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_154_, 0, v_x_124_);
lean_ctor_set(v_reuseFailAlloc_154_, 1, v_x_125_);
v___x_153_ = v_reuseFailAlloc_154_;
goto v_reusejp_152_;
}
v_reusejp_152_:
{
v___y_139_ = v___x_153_;
goto v___jp_138_;
}
}
}
}
case 1:
{
lean_object* v_node_156_; lean_object* v___x_158_; uint8_t v_isShared_159_; uint8_t v_isSharedCheck_168_; 
v_node_156_ = lean_ctor_get(v_v_135_, 0);
v_isSharedCheck_168_ = !lean_is_exclusive(v_v_135_);
if (v_isSharedCheck_168_ == 0)
{
v___x_158_ = v_v_135_;
v_isShared_159_ = v_isSharedCheck_168_;
goto v_resetjp_157_;
}
else
{
lean_inc(v_node_156_);
lean_dec(v_v_135_);
v___x_158_ = lean_box(0);
v_isShared_159_ = v_isSharedCheck_168_;
goto v_resetjp_157_;
}
v_resetjp_157_:
{
size_t v___x_160_; size_t v___x_161_; size_t v___x_162_; size_t v___x_163_; lean_object* v___x_164_; lean_object* v___x_166_; 
v___x_160_ = ((size_t)5ULL);
v___x_161_ = lean_usize_shift_right(v_x_122_, v___x_160_);
v___x_162_ = ((size_t)1ULL);
v___x_163_ = lean_usize_add(v_x_123_, v___x_162_);
v___x_164_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3___redArg(v_node_156_, v___x_161_, v___x_163_, v_x_124_, v_x_125_);
if (v_isShared_159_ == 0)
{
lean_ctor_set(v___x_158_, 0, v___x_164_);
v___x_166_ = v___x_158_;
goto v_reusejp_165_;
}
else
{
lean_object* v_reuseFailAlloc_167_; 
v_reuseFailAlloc_167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_167_, 0, v___x_164_);
v___x_166_ = v_reuseFailAlloc_167_;
goto v_reusejp_165_;
}
v_reusejp_165_:
{
v___y_139_ = v___x_166_;
goto v___jp_138_;
}
}
}
default: 
{
lean_object* v___x_169_; 
v___x_169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_169_, 0, v_x_124_);
lean_ctor_set(v___x_169_, 1, v_x_125_);
v___y_139_ = v___x_169_;
goto v___jp_138_;
}
}
v___jp_138_:
{
lean_object* v___x_140_; lean_object* v___x_142_; 
v___x_140_ = lean_array_fset(v_xs_x27_137_, v_j_129_, v___y_139_);
lean_dec(v_j_129_);
if (v_isShared_134_ == 0)
{
lean_ctor_set(v___x_133_, 0, v___x_140_);
v___x_142_ = v___x_133_;
goto v_reusejp_141_;
}
else
{
lean_object* v_reuseFailAlloc_143_; 
v_reuseFailAlloc_143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_143_, 0, v___x_140_);
v___x_142_ = v_reuseFailAlloc_143_;
goto v_reusejp_141_;
}
v_reusejp_141_:
{
return v___x_142_;
}
}
}
}
}
else
{
lean_object* v_ks_172_; lean_object* v_vs_173_; lean_object* v___x_175_; uint8_t v_isShared_176_; uint8_t v_isSharedCheck_193_; 
v_ks_172_ = lean_ctor_get(v_x_121_, 0);
v_vs_173_ = lean_ctor_get(v_x_121_, 1);
v_isSharedCheck_193_ = !lean_is_exclusive(v_x_121_);
if (v_isSharedCheck_193_ == 0)
{
v___x_175_ = v_x_121_;
v_isShared_176_ = v_isSharedCheck_193_;
goto v_resetjp_174_;
}
else
{
lean_inc(v_vs_173_);
lean_inc(v_ks_172_);
lean_dec(v_x_121_);
v___x_175_ = lean_box(0);
v_isShared_176_ = v_isSharedCheck_193_;
goto v_resetjp_174_;
}
v_resetjp_174_:
{
lean_object* v___x_178_; 
if (v_isShared_176_ == 0)
{
v___x_178_ = v___x_175_;
goto v_reusejp_177_;
}
else
{
lean_object* v_reuseFailAlloc_192_; 
v_reuseFailAlloc_192_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_192_, 0, v_ks_172_);
lean_ctor_set(v_reuseFailAlloc_192_, 1, v_vs_173_);
v___x_178_ = v_reuseFailAlloc_192_;
goto v_reusejp_177_;
}
v_reusejp_177_:
{
lean_object* v_newNode_179_; uint8_t v___y_181_; size_t v___x_187_; uint8_t v___x_188_; 
v_newNode_179_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3_spec__5___redArg(v___x_178_, v_x_124_, v_x_125_);
v___x_187_ = ((size_t)7ULL);
v___x_188_ = lean_usize_dec_le(v___x_187_, v_x_123_);
if (v___x_188_ == 0)
{
lean_object* v___x_189_; lean_object* v___x_190_; uint8_t v___x_191_; 
v___x_189_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_179_);
v___x_190_ = lean_unsigned_to_nat(4u);
v___x_191_ = lean_nat_dec_lt(v___x_189_, v___x_190_);
lean_dec(v___x_189_);
v___y_181_ = v___x_191_;
goto v___jp_180_;
}
else
{
v___y_181_ = v___x_188_;
goto v___jp_180_;
}
v___jp_180_:
{
if (v___y_181_ == 0)
{
lean_object* v_ks_182_; lean_object* v_vs_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; 
v_ks_182_ = lean_ctor_get(v_newNode_179_, 0);
lean_inc_ref(v_ks_182_);
v_vs_183_ = lean_ctor_get(v_newNode_179_, 1);
lean_inc_ref(v_vs_183_);
lean_dec_ref(v_newNode_179_);
v___x_184_ = lean_unsigned_to_nat(0u);
v___x_185_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3___redArg___closed__0);
v___x_186_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3_spec__6___redArg(v_x_123_, v_ks_182_, v_vs_183_, v___x_184_, v___x_185_);
lean_dec_ref(v_vs_183_);
lean_dec_ref(v_ks_182_);
return v___x_186_;
}
else
{
return v_newNode_179_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3_spec__6___redArg(size_t v_depth_194_, lean_object* v_keys_195_, lean_object* v_vals_196_, lean_object* v_i_197_, lean_object* v_entries_198_){
_start:
{
lean_object* v___x_199_; uint8_t v___x_200_; 
v___x_199_ = lean_array_get_size(v_keys_195_);
v___x_200_ = lean_nat_dec_lt(v_i_197_, v___x_199_);
if (v___x_200_ == 0)
{
lean_dec(v_i_197_);
return v_entries_198_;
}
else
{
lean_object* v_k_201_; lean_object* v_v_202_; uint64_t v___x_203_; size_t v_h_204_; size_t v___x_205_; lean_object* v___x_206_; size_t v___x_207_; size_t v___x_208_; size_t v___x_209_; size_t v_h_210_; lean_object* v___x_211_; lean_object* v___x_212_; 
v_k_201_ = lean_array_fget_borrowed(v_keys_195_, v_i_197_);
v_v_202_ = lean_array_fget_borrowed(v_vals_196_, v_i_197_);
v___x_203_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_k_201_);
v_h_204_ = lean_uint64_to_usize(v___x_203_);
v___x_205_ = ((size_t)5ULL);
v___x_206_ = lean_unsigned_to_nat(1u);
v___x_207_ = ((size_t)1ULL);
v___x_208_ = lean_usize_sub(v_depth_194_, v___x_207_);
v___x_209_ = lean_usize_mul(v___x_205_, v___x_208_);
v_h_210_ = lean_usize_shift_right(v_h_204_, v___x_209_);
v___x_211_ = lean_nat_add(v_i_197_, v___x_206_);
lean_dec(v_i_197_);
lean_inc(v_v_202_);
lean_inc(v_k_201_);
v___x_212_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3___redArg(v_entries_198_, v_h_210_, v_depth_194_, v_k_201_, v_v_202_);
v_i_197_ = v___x_211_;
v_entries_198_ = v___x_212_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3_spec__6___redArg___boxed(lean_object* v_depth_214_, lean_object* v_keys_215_, lean_object* v_vals_216_, lean_object* v_i_217_, lean_object* v_entries_218_){
_start:
{
size_t v_depth_boxed_219_; lean_object* v_res_220_; 
v_depth_boxed_219_ = lean_unbox_usize(v_depth_214_);
lean_dec(v_depth_214_);
v_res_220_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3_spec__6___redArg(v_depth_boxed_219_, v_keys_215_, v_vals_216_, v_i_217_, v_entries_218_);
lean_dec_ref(v_vals_216_);
lean_dec_ref(v_keys_215_);
return v_res_220_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3___redArg___boxed(lean_object* v_x_221_, lean_object* v_x_222_, lean_object* v_x_223_, lean_object* v_x_224_, lean_object* v_x_225_){
_start:
{
size_t v_x_9622__boxed_226_; size_t v_x_9623__boxed_227_; lean_object* v_res_228_; 
v_x_9622__boxed_226_ = lean_unbox_usize(v_x_222_);
lean_dec(v_x_222_);
v_x_9623__boxed_227_ = lean_unbox_usize(v_x_223_);
lean_dec(v_x_223_);
v_res_228_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3___redArg(v_x_221_, v_x_9622__boxed_226_, v_x_9623__boxed_227_, v_x_224_, v_x_225_);
return v_res_228_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2___redArg(lean_object* v_x_229_, lean_object* v_x_230_, lean_object* v_x_231_){
_start:
{
uint64_t v___x_232_; size_t v___x_233_; size_t v___x_234_; lean_object* v___x_235_; 
v___x_232_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_230_);
v___x_233_ = lean_uint64_to_usize(v___x_232_);
v___x_234_ = ((size_t)1ULL);
v___x_235_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3___redArg(v_x_229_, v___x_233_, v___x_234_, v_x_230_, v_x_231_);
return v___x_235_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__3(void){
_start:
{
lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; 
v___x_239_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__2));
v___x_240_ = lean_unsigned_to_nat(26u);
v___x_241_ = lean_unsigned_to_nat(19u);
v___x_242_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__1));
v___x_243_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__0));
v___x_244_ = l_mkPanicMessageWithDecl(v___x_243_, v___x_242_, v___x_241_, v___x_240_, v___x_239_);
return v___x_244_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__11(void){
_start:
{
lean_object* v___x_257_; lean_object* v_dummy_258_; 
v___x_257_ = lean_box(0);
v_dummy_258_ = l_Lean_Expr_sort___override(v___x_257_);
return v_dummy_258_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f(lean_object* v_f_264_, lean_object* v_a_265_, lean_object* v_a_266_, lean_object* v_a_267_, lean_object* v_a_268_, lean_object* v_a_269_, lean_object* v_a_270_, lean_object* v_a_271_, lean_object* v_a_272_, lean_object* v_a_273_, lean_object* v_a_274_, lean_object* v_a_275_){
_start:
{
lean_object* v___y_278_; lean_object* v___y_279_; lean_object* v___y_280_; lean_object* v___y_281_; lean_object* v___y_282_; lean_object* v___y_283_; lean_object* v___y_284_; lean_object* v___y_285_; lean_object* v___y_286_; lean_object* v___y_287_; lean_object* v___x_290_; lean_object* v_toGoalState_291_; lean_object* v_inj_292_; lean_object* v_fns_293_; lean_object* v___x_295_; uint8_t v_isShared_296_; uint8_t v_isSharedCheck_417_; 
v___x_290_ = lean_st_ref_get(v_a_266_);
v_toGoalState_291_ = lean_ctor_get(v___x_290_, 0);
lean_inc_ref(v_toGoalState_291_);
lean_dec(v___x_290_);
v_inj_292_ = lean_ctor_get(v_toGoalState_291_, 13);
lean_inc_ref(v_inj_292_);
lean_dec_ref(v_toGoalState_291_);
v_fns_293_ = lean_ctor_get(v_inj_292_, 1);
v_isSharedCheck_417_ = !lean_is_exclusive(v_inj_292_);
if (v_isSharedCheck_417_ == 0)
{
lean_object* v_unused_418_; 
v_unused_418_ = lean_ctor_get(v_inj_292_, 0);
lean_dec(v_unused_418_);
v___x_295_ = v_inj_292_;
v_isShared_296_ = v_isSharedCheck_417_;
goto v_resetjp_294_;
}
else
{
lean_inc(v_fns_293_);
lean_dec(v_inj_292_);
v___x_295_ = lean_box(0);
v_isShared_296_ = v_isSharedCheck_417_;
goto v_resetjp_294_;
}
v___jp_277_:
{
lean_object* v___x_288_; lean_object* v___x_289_; 
v___x_288_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__3, &l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__3);
v___x_289_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__0(v___x_288_, v___y_278_, v___y_279_, v___y_280_, v___y_281_, v___y_282_, v___y_283_, v___y_284_, v___y_285_, v___y_286_, v___y_287_);
return v___x_289_;
}
v_resetjp_294_:
{
lean_object* v___x_297_; 
v___x_297_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1___redArg(v_fns_293_, v_f_264_);
lean_dec_ref(v_fns_293_);
if (lean_obj_tag(v___x_297_) == 1)
{
lean_object* v_val_298_; lean_object* v___x_300_; uint8_t v_isShared_301_; uint8_t v_isSharedCheck_414_; 
v_val_298_ = lean_ctor_get(v___x_297_, 0);
v_isSharedCheck_414_ = !lean_is_exclusive(v___x_297_);
if (v_isSharedCheck_414_ == 0)
{
v___x_300_ = v___x_297_;
v_isShared_301_ = v_isSharedCheck_414_;
goto v_resetjp_299_;
}
else
{
lean_inc(v_val_298_);
lean_dec(v___x_297_);
v___x_300_ = lean_box(0);
v_isShared_301_ = v_isSharedCheck_414_;
goto v_resetjp_299_;
}
v_resetjp_299_:
{
lean_object* v_inv_x3f_302_; 
v_inv_x3f_302_ = lean_ctor_get(v_val_298_, 4);
if (lean_obj_tag(v_inv_x3f_302_) == 1)
{
lean_object* v___x_303_; 
lean_inc_ref(v_inv_x3f_302_);
lean_del_object(v___x_300_);
lean_dec(v_val_298_);
lean_del_object(v___x_295_);
lean_dec_ref(v_a_265_);
lean_dec_ref(v_f_264_);
v___x_303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_303_, 0, v_inv_x3f_302_);
return v___x_303_;
}
else
{
lean_object* v_us_304_; 
v_us_304_ = lean_ctor_get(v_val_298_, 0);
lean_inc(v_us_304_);
if (lean_obj_tag(v_us_304_) == 1)
{
lean_object* v_tail_305_; 
v_tail_305_ = lean_ctor_get(v_us_304_, 1);
lean_inc(v_tail_305_);
if (lean_obj_tag(v_tail_305_) == 1)
{
lean_object* v_tail_306_; lean_object* v___x_308_; uint8_t v_isShared_309_; uint8_t v_isSharedCheck_412_; 
v_tail_306_ = lean_ctor_get(v_tail_305_, 1);
v_isSharedCheck_412_ = !lean_is_exclusive(v_tail_305_);
if (v_isSharedCheck_412_ == 0)
{
lean_object* v_unused_413_; 
v_unused_413_ = lean_ctor_get(v_tail_305_, 0);
lean_dec(v_unused_413_);
v___x_308_ = v_tail_305_;
v_isShared_309_ = v_isSharedCheck_412_;
goto v_resetjp_307_;
}
else
{
lean_inc(v_tail_306_);
lean_dec(v_tail_305_);
v___x_308_ = lean_box(0);
v_isShared_309_ = v_isSharedCheck_412_;
goto v_resetjp_307_;
}
v_resetjp_307_:
{
if (lean_obj_tag(v_tail_306_) == 0)
{
lean_object* v_00_u03b1_310_; lean_object* v_00_u03b2_311_; lean_object* v_h_312_; lean_object* v___x_314_; uint8_t v_isShared_315_; uint8_t v_isSharedCheck_409_; 
v_00_u03b1_310_ = lean_ctor_get(v_val_298_, 1);
v_00_u03b2_311_ = lean_ctor_get(v_val_298_, 2);
v_h_312_ = lean_ctor_get(v_val_298_, 3);
v_isSharedCheck_409_ = !lean_is_exclusive(v_val_298_);
if (v_isSharedCheck_409_ == 0)
{
lean_object* v_unused_410_; lean_object* v_unused_411_; 
v_unused_410_ = lean_ctor_get(v_val_298_, 4);
lean_dec(v_unused_410_);
v_unused_411_ = lean_ctor_get(v_val_298_, 0);
lean_dec(v_unused_411_);
v___x_314_ = v_val_298_;
v_isShared_315_ = v_isSharedCheck_409_;
goto v_resetjp_313_;
}
else
{
lean_inc(v_h_312_);
lean_inc(v_00_u03b2_311_);
lean_inc(v_00_u03b1_310_);
lean_dec(v_val_298_);
v___x_314_ = lean_box(0);
v_isShared_315_ = v_isSharedCheck_409_;
goto v_resetjp_313_;
}
v_resetjp_313_:
{
lean_object* v_head_316_; lean_object* v___x_317_; lean_object* v___x_319_; 
v_head_316_ = lean_ctor_get(v_us_304_, 0);
v___x_317_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__6));
lean_inc(v_head_316_);
if (v_isShared_309_ == 0)
{
lean_ctor_set(v___x_308_, 0, v_head_316_);
v___x_319_ = v___x_308_;
goto v_reusejp_318_;
}
else
{
lean_object* v_reuseFailAlloc_408_; 
v_reuseFailAlloc_408_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_408_, 0, v_head_316_);
lean_ctor_set(v_reuseFailAlloc_408_, 1, v_tail_306_);
v___x_319_ = v_reuseFailAlloc_408_;
goto v_reusejp_318_;
}
v_reusejp_318_:
{
lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; 
v___x_320_ = l_Lean_mkConst(v___x_317_, v___x_319_);
lean_inc_ref_n(v_00_u03b1_310_, 2);
v___x_321_ = l_Lean_mkAppB(v___x_320_, v_00_u03b1_310_, v_a_265_);
v___x_322_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__10));
lean_inc_ref(v_us_304_);
v___x_323_ = l_Lean_mkConst(v___x_322_, v_us_304_);
lean_inc_ref(v_h_312_);
lean_inc_ref(v_f_264_);
lean_inc_ref(v_00_u03b2_311_);
v___x_324_ = l_Lean_mkApp5(v___x_323_, v_00_u03b1_310_, v_00_u03b2_311_, v_f_264_, v_h_312_, v___x_321_);
v___x_325_ = l_Lean_Meta_Grind_preprocessLight___redArg(v___x_324_, v_a_267_, v_a_268_, v_a_269_, v_a_270_, v_a_271_, v_a_272_, v_a_273_, v_a_274_, v_a_275_);
if (lean_obj_tag(v___x_325_) == 0)
{
lean_object* v_a_326_; lean_object* v___x_328_; uint8_t v_isShared_329_; uint8_t v_isSharedCheck_399_; 
v_a_326_ = lean_ctor_get(v___x_325_, 0);
v_isSharedCheck_399_ = !lean_is_exclusive(v___x_325_);
if (v_isSharedCheck_399_ == 0)
{
v___x_328_ = v___x_325_;
v_isShared_329_ = v_isSharedCheck_399_;
goto v_resetjp_327_;
}
else
{
lean_inc(v_a_326_);
lean_dec(v___x_325_);
v___x_328_ = lean_box(0);
v_isShared_329_ = v_isSharedCheck_399_;
goto v_resetjp_327_;
}
v_resetjp_327_:
{
lean_object* v___x_330_; lean_object* v_nargs_331_; lean_object* v_toGoalState_332_; lean_object* v_inj_333_; lean_object* v_mvarId_334_; lean_object* v___x_336_; uint8_t v_isShared_337_; uint8_t v_isSharedCheck_397_; 
v___x_330_ = lean_st_ref_take(v_a_266_);
v_nargs_331_ = l_Lean_Expr_getAppNumArgs(v_a_326_);
v_toGoalState_332_ = lean_ctor_get(v___x_330_, 0);
lean_inc_ref(v_toGoalState_332_);
v_inj_333_ = lean_ctor_get(v_toGoalState_332_, 13);
lean_inc_ref(v_inj_333_);
v_mvarId_334_ = lean_ctor_get(v___x_330_, 1);
v_isSharedCheck_397_ = !lean_is_exclusive(v___x_330_);
if (v_isSharedCheck_397_ == 0)
{
lean_object* v_unused_398_; 
v_unused_398_ = lean_ctor_get(v___x_330_, 0);
lean_dec(v_unused_398_);
v___x_336_ = v___x_330_;
v_isShared_337_ = v_isSharedCheck_397_;
goto v_resetjp_335_;
}
else
{
lean_inc(v_mvarId_334_);
lean_dec(v___x_330_);
v___x_336_ = lean_box(0);
v_isShared_337_ = v_isSharedCheck_397_;
goto v_resetjp_335_;
}
v_resetjp_335_:
{
lean_object* v_nextDeclIdx_338_; lean_object* v_enodeMap_339_; lean_object* v_exprs_340_; lean_object* v_parents_341_; lean_object* v_congrTable_342_; lean_object* v_appMap_343_; lean_object* v_indicesFound_344_; lean_object* v_newFacts_345_; uint8_t v_inconsistent_346_; lean_object* v_nextIdx_347_; lean_object* v_newRawFacts_348_; lean_object* v_facts_349_; lean_object* v_extThms_350_; lean_object* v_ematch_351_; lean_object* v_split_352_; lean_object* v_clean_353_; lean_object* v_sstates_354_; lean_object* v___x_356_; uint8_t v_isShared_357_; uint8_t v_isSharedCheck_395_; 
v_nextDeclIdx_338_ = lean_ctor_get(v_toGoalState_332_, 0);
v_enodeMap_339_ = lean_ctor_get(v_toGoalState_332_, 1);
v_exprs_340_ = lean_ctor_get(v_toGoalState_332_, 2);
v_parents_341_ = lean_ctor_get(v_toGoalState_332_, 3);
v_congrTable_342_ = lean_ctor_get(v_toGoalState_332_, 4);
v_appMap_343_ = lean_ctor_get(v_toGoalState_332_, 5);
v_indicesFound_344_ = lean_ctor_get(v_toGoalState_332_, 6);
v_newFacts_345_ = lean_ctor_get(v_toGoalState_332_, 7);
v_inconsistent_346_ = lean_ctor_get_uint8(v_toGoalState_332_, sizeof(void*)*17);
v_nextIdx_347_ = lean_ctor_get(v_toGoalState_332_, 8);
v_newRawFacts_348_ = lean_ctor_get(v_toGoalState_332_, 9);
v_facts_349_ = lean_ctor_get(v_toGoalState_332_, 10);
v_extThms_350_ = lean_ctor_get(v_toGoalState_332_, 11);
v_ematch_351_ = lean_ctor_get(v_toGoalState_332_, 12);
v_split_352_ = lean_ctor_get(v_toGoalState_332_, 14);
v_clean_353_ = lean_ctor_get(v_toGoalState_332_, 15);
v_sstates_354_ = lean_ctor_get(v_toGoalState_332_, 16);
v_isSharedCheck_395_ = !lean_is_exclusive(v_toGoalState_332_);
if (v_isSharedCheck_395_ == 0)
{
lean_object* v_unused_396_; 
v_unused_396_ = lean_ctor_get(v_toGoalState_332_, 13);
lean_dec(v_unused_396_);
v___x_356_ = v_toGoalState_332_;
v_isShared_357_ = v_isSharedCheck_395_;
goto v_resetjp_355_;
}
else
{
lean_inc(v_sstates_354_);
lean_inc(v_clean_353_);
lean_inc(v_split_352_);
lean_inc(v_ematch_351_);
lean_inc(v_extThms_350_);
lean_inc(v_facts_349_);
lean_inc(v_newRawFacts_348_);
lean_inc(v_nextIdx_347_);
lean_inc(v_newFacts_345_);
lean_inc(v_indicesFound_344_);
lean_inc(v_appMap_343_);
lean_inc(v_congrTable_342_);
lean_inc(v_parents_341_);
lean_inc(v_exprs_340_);
lean_inc(v_enodeMap_339_);
lean_inc(v_nextDeclIdx_338_);
lean_dec(v_toGoalState_332_);
v___x_356_ = lean_box(0);
v_isShared_357_ = v_isSharedCheck_395_;
goto v_resetjp_355_;
}
v_resetjp_355_:
{
lean_object* v_thms_358_; lean_object* v_fns_359_; lean_object* v___x_361_; uint8_t v_isShared_362_; uint8_t v_isSharedCheck_394_; 
v_thms_358_ = lean_ctor_get(v_inj_333_, 0);
v_fns_359_ = lean_ctor_get(v_inj_333_, 1);
v_isSharedCheck_394_ = !lean_is_exclusive(v_inj_333_);
if (v_isSharedCheck_394_ == 0)
{
v___x_361_ = v_inj_333_;
v_isShared_362_ = v_isSharedCheck_394_;
goto v_resetjp_360_;
}
else
{
lean_inc(v_fns_359_);
lean_inc(v_thms_358_);
lean_dec(v_inj_333_);
v___x_361_ = lean_box(0);
v_isShared_362_ = v_isSharedCheck_394_;
goto v_resetjp_360_;
}
v_resetjp_360_:
{
lean_object* v_dummy_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_372_; 
v_dummy_363_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__11, &l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__11_once, _init_l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__11);
lean_inc(v_nargs_331_);
v___x_364_ = lean_mk_array(v_nargs_331_, v_dummy_363_);
v___x_365_ = lean_unsigned_to_nat(1u);
v___x_366_ = lean_nat_sub(v_nargs_331_, v___x_365_);
lean_dec(v_nargs_331_);
lean_inc(v_a_326_);
v___x_367_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_326_, v___x_364_, v___x_366_);
v___x_368_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__13));
lean_inc_ref(v_us_304_);
v___x_369_ = l_Lean_mkConst(v___x_368_, v_us_304_);
v___x_370_ = l_Lean_mkAppN(v___x_369_, v___x_367_);
lean_dec_ref(v___x_367_);
if (v_isShared_296_ == 0)
{
lean_ctor_set(v___x_295_, 1, v___x_370_);
lean_ctor_set(v___x_295_, 0, v_a_326_);
v___x_372_ = v___x_295_;
goto v_reusejp_371_;
}
else
{
lean_object* v_reuseFailAlloc_393_; 
v_reuseFailAlloc_393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_393_, 0, v_a_326_);
lean_ctor_set(v_reuseFailAlloc_393_, 1, v___x_370_);
v___x_372_ = v_reuseFailAlloc_393_;
goto v_reusejp_371_;
}
v_reusejp_371_:
{
lean_object* v___x_374_; 
if (v_isShared_301_ == 0)
{
lean_ctor_set(v___x_300_, 0, v___x_372_);
v___x_374_ = v___x_300_;
goto v_reusejp_373_;
}
else
{
lean_object* v_reuseFailAlloc_392_; 
v_reuseFailAlloc_392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_392_, 0, v___x_372_);
v___x_374_ = v_reuseFailAlloc_392_;
goto v_reusejp_373_;
}
v_reusejp_373_:
{
lean_object* v___x_376_; 
lean_inc_ref(v___x_374_);
if (v_isShared_315_ == 0)
{
lean_ctor_set(v___x_314_, 4, v___x_374_);
v___x_376_ = v___x_314_;
goto v_reusejp_375_;
}
else
{
lean_object* v_reuseFailAlloc_391_; 
v_reuseFailAlloc_391_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_391_, 0, v_us_304_);
lean_ctor_set(v_reuseFailAlloc_391_, 1, v_00_u03b1_310_);
lean_ctor_set(v_reuseFailAlloc_391_, 2, v_00_u03b2_311_);
lean_ctor_set(v_reuseFailAlloc_391_, 3, v_h_312_);
lean_ctor_set(v_reuseFailAlloc_391_, 4, v___x_374_);
v___x_376_ = v_reuseFailAlloc_391_;
goto v_reusejp_375_;
}
v_reusejp_375_:
{
lean_object* v___x_377_; lean_object* v___x_379_; 
v___x_377_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2___redArg(v_fns_359_, v_f_264_, v___x_376_);
if (v_isShared_362_ == 0)
{
lean_ctor_set(v___x_361_, 1, v___x_377_);
v___x_379_ = v___x_361_;
goto v_reusejp_378_;
}
else
{
lean_object* v_reuseFailAlloc_390_; 
v_reuseFailAlloc_390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_390_, 0, v_thms_358_);
lean_ctor_set(v_reuseFailAlloc_390_, 1, v___x_377_);
v___x_379_ = v_reuseFailAlloc_390_;
goto v_reusejp_378_;
}
v_reusejp_378_:
{
lean_object* v___x_381_; 
if (v_isShared_357_ == 0)
{
lean_ctor_set(v___x_356_, 13, v___x_379_);
v___x_381_ = v___x_356_;
goto v_reusejp_380_;
}
else
{
lean_object* v_reuseFailAlloc_389_; 
v_reuseFailAlloc_389_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_389_, 0, v_nextDeclIdx_338_);
lean_ctor_set(v_reuseFailAlloc_389_, 1, v_enodeMap_339_);
lean_ctor_set(v_reuseFailAlloc_389_, 2, v_exprs_340_);
lean_ctor_set(v_reuseFailAlloc_389_, 3, v_parents_341_);
lean_ctor_set(v_reuseFailAlloc_389_, 4, v_congrTable_342_);
lean_ctor_set(v_reuseFailAlloc_389_, 5, v_appMap_343_);
lean_ctor_set(v_reuseFailAlloc_389_, 6, v_indicesFound_344_);
lean_ctor_set(v_reuseFailAlloc_389_, 7, v_newFacts_345_);
lean_ctor_set(v_reuseFailAlloc_389_, 8, v_nextIdx_347_);
lean_ctor_set(v_reuseFailAlloc_389_, 9, v_newRawFacts_348_);
lean_ctor_set(v_reuseFailAlloc_389_, 10, v_facts_349_);
lean_ctor_set(v_reuseFailAlloc_389_, 11, v_extThms_350_);
lean_ctor_set(v_reuseFailAlloc_389_, 12, v_ematch_351_);
lean_ctor_set(v_reuseFailAlloc_389_, 13, v___x_379_);
lean_ctor_set(v_reuseFailAlloc_389_, 14, v_split_352_);
lean_ctor_set(v_reuseFailAlloc_389_, 15, v_clean_353_);
lean_ctor_set(v_reuseFailAlloc_389_, 16, v_sstates_354_);
lean_ctor_set_uint8(v_reuseFailAlloc_389_, sizeof(void*)*17, v_inconsistent_346_);
v___x_381_ = v_reuseFailAlloc_389_;
goto v_reusejp_380_;
}
v_reusejp_380_:
{
lean_object* v___x_383_; 
if (v_isShared_337_ == 0)
{
lean_ctor_set(v___x_336_, 0, v___x_381_);
v___x_383_ = v___x_336_;
goto v_reusejp_382_;
}
else
{
lean_object* v_reuseFailAlloc_388_; 
v_reuseFailAlloc_388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_388_, 0, v___x_381_);
lean_ctor_set(v_reuseFailAlloc_388_, 1, v_mvarId_334_);
v___x_383_ = v_reuseFailAlloc_388_;
goto v_reusejp_382_;
}
v_reusejp_382_:
{
lean_object* v___x_384_; lean_object* v___x_386_; 
v___x_384_ = lean_st_ref_set(v_a_266_, v___x_383_);
if (v_isShared_329_ == 0)
{
lean_ctor_set(v___x_328_, 0, v___x_374_);
v___x_386_ = v___x_328_;
goto v_reusejp_385_;
}
else
{
lean_object* v_reuseFailAlloc_387_; 
v_reuseFailAlloc_387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_387_, 0, v___x_374_);
v___x_386_ = v_reuseFailAlloc_387_;
goto v_reusejp_385_;
}
v_reusejp_385_:
{
return v___x_386_;
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
lean_object* v_a_400_; lean_object* v___x_402_; uint8_t v_isShared_403_; uint8_t v_isSharedCheck_407_; 
lean_del_object(v___x_314_);
lean_dec_ref(v_h_312_);
lean_dec_ref(v_00_u03b2_311_);
lean_dec_ref(v_00_u03b1_310_);
lean_dec_ref_known(v_us_304_, 2);
lean_del_object(v___x_300_);
lean_del_object(v___x_295_);
lean_dec_ref(v_f_264_);
v_a_400_ = lean_ctor_get(v___x_325_, 0);
v_isSharedCheck_407_ = !lean_is_exclusive(v___x_325_);
if (v_isSharedCheck_407_ == 0)
{
v___x_402_ = v___x_325_;
v_isShared_403_ = v_isSharedCheck_407_;
goto v_resetjp_401_;
}
else
{
lean_inc(v_a_400_);
lean_dec(v___x_325_);
v___x_402_ = lean_box(0);
v_isShared_403_ = v_isSharedCheck_407_;
goto v_resetjp_401_;
}
v_resetjp_401_:
{
lean_object* v___x_405_; 
if (v_isShared_403_ == 0)
{
v___x_405_ = v___x_402_;
goto v_reusejp_404_;
}
else
{
lean_object* v_reuseFailAlloc_406_; 
v_reuseFailAlloc_406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_406_, 0, v_a_400_);
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
else
{
lean_del_object(v___x_308_);
lean_dec(v_tail_306_);
lean_dec_ref_known(v_us_304_, 2);
lean_del_object(v___x_300_);
lean_dec(v_val_298_);
lean_del_object(v___x_295_);
lean_dec_ref(v_a_265_);
lean_dec_ref(v_f_264_);
v___y_278_ = v_a_266_;
v___y_279_ = v_a_267_;
v___y_280_ = v_a_268_;
v___y_281_ = v_a_269_;
v___y_282_ = v_a_270_;
v___y_283_ = v_a_271_;
v___y_284_ = v_a_272_;
v___y_285_ = v_a_273_;
v___y_286_ = v_a_274_;
v___y_287_ = v_a_275_;
goto v___jp_277_;
}
}
}
else
{
lean_dec(v_tail_305_);
lean_dec_ref_known(v_us_304_, 2);
lean_del_object(v___x_300_);
lean_dec(v_val_298_);
lean_del_object(v___x_295_);
lean_dec_ref(v_a_265_);
lean_dec_ref(v_f_264_);
v___y_278_ = v_a_266_;
v___y_279_ = v_a_267_;
v___y_280_ = v_a_268_;
v___y_281_ = v_a_269_;
v___y_282_ = v_a_270_;
v___y_283_ = v_a_271_;
v___y_284_ = v_a_272_;
v___y_285_ = v_a_273_;
v___y_286_ = v_a_274_;
v___y_287_ = v_a_275_;
goto v___jp_277_;
}
}
else
{
lean_dec(v_us_304_);
lean_del_object(v___x_300_);
lean_dec(v_val_298_);
lean_del_object(v___x_295_);
lean_dec_ref(v_a_265_);
lean_dec_ref(v_f_264_);
v___y_278_ = v_a_266_;
v___y_279_ = v_a_267_;
v___y_280_ = v_a_268_;
v___y_281_ = v_a_269_;
v___y_282_ = v_a_270_;
v___y_283_ = v_a_271_;
v___y_284_ = v_a_272_;
v___y_285_ = v_a_273_;
v___y_286_ = v_a_274_;
v___y_287_ = v_a_275_;
goto v___jp_277_;
}
}
}
}
else
{
lean_object* v___x_415_; lean_object* v___x_416_; 
lean_dec(v___x_297_);
lean_del_object(v___x_295_);
lean_dec_ref(v_a_265_);
lean_dec_ref(v_f_264_);
v___x_415_ = lean_box(0);
v___x_416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_416_, 0, v___x_415_);
return v___x_416_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___boxed(lean_object* v_f_419_, lean_object* v_a_420_, lean_object* v_a_421_, lean_object* v_a_422_, lean_object* v_a_423_, lean_object* v_a_424_, lean_object* v_a_425_, lean_object* v_a_426_, lean_object* v_a_427_, lean_object* v_a_428_, lean_object* v_a_429_, lean_object* v_a_430_, lean_object* v_a_431_){
_start:
{
lean_object* v_res_432_; 
v_res_432_ = l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f(v_f_419_, v_a_420_, v_a_421_, v_a_422_, v_a_423_, v_a_424_, v_a_425_, v_a_426_, v_a_427_, v_a_428_, v_a_429_, v_a_430_);
lean_dec(v_a_430_);
lean_dec_ref(v_a_429_);
lean_dec(v_a_428_);
lean_dec_ref(v_a_427_);
lean_dec(v_a_426_);
lean_dec_ref(v_a_425_);
lean_dec(v_a_424_);
lean_dec_ref(v_a_423_);
lean_dec(v_a_422_);
lean_dec(v_a_421_);
return v_res_432_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1(lean_object* v_00_u03b2_433_, lean_object* v_x_434_, lean_object* v_x_435_){
_start:
{
lean_object* v___x_436_; 
v___x_436_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1___redArg(v_x_434_, v_x_435_);
return v___x_436_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1___boxed(lean_object* v_00_u03b2_437_, lean_object* v_x_438_, lean_object* v_x_439_){
_start:
{
lean_object* v_res_440_; 
v_res_440_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1(v_00_u03b2_437_, v_x_438_, v_x_439_);
lean_dec_ref(v_x_439_);
lean_dec_ref(v_x_438_);
return v_res_440_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2(lean_object* v_00_u03b2_441_, lean_object* v_x_442_, lean_object* v_x_443_, lean_object* v_x_444_){
_start:
{
lean_object* v___x_445_; 
v___x_445_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2___redArg(v_x_442_, v_x_443_, v_x_444_);
return v___x_445_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1(lean_object* v_00_u03b2_446_, lean_object* v_x_447_, size_t v_x_448_, lean_object* v_x_449_){
_start:
{
lean_object* v___x_450_; 
v___x_450_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1___redArg(v_x_447_, v_x_448_, v_x_449_);
return v___x_450_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1___boxed(lean_object* v_00_u03b2_451_, lean_object* v_x_452_, lean_object* v_x_453_, lean_object* v_x_454_){
_start:
{
size_t v_x_10113__boxed_455_; lean_object* v_res_456_; 
v_x_10113__boxed_455_ = lean_unbox_usize(v_x_453_);
lean_dec(v_x_453_);
v_res_456_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1(v_00_u03b2_451_, v_x_452_, v_x_10113__boxed_455_, v_x_454_);
lean_dec_ref(v_x_454_);
lean_dec_ref(v_x_452_);
return v_res_456_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3(lean_object* v_00_u03b2_457_, lean_object* v_x_458_, size_t v_x_459_, size_t v_x_460_, lean_object* v_x_461_, lean_object* v_x_462_){
_start:
{
lean_object* v___x_463_; 
v___x_463_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3___redArg(v_x_458_, v_x_459_, v_x_460_, v_x_461_, v_x_462_);
return v___x_463_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3___boxed(lean_object* v_00_u03b2_464_, lean_object* v_x_465_, lean_object* v_x_466_, lean_object* v_x_467_, lean_object* v_x_468_, lean_object* v_x_469_){
_start:
{
size_t v_x_10124__boxed_470_; size_t v_x_10125__boxed_471_; lean_object* v_res_472_; 
v_x_10124__boxed_470_ = lean_unbox_usize(v_x_466_);
lean_dec(v_x_466_);
v_x_10125__boxed_471_ = lean_unbox_usize(v_x_467_);
lean_dec(v_x_467_);
v_res_472_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3(v_00_u03b2_464_, v_x_465_, v_x_10124__boxed_470_, v_x_10125__boxed_471_, v_x_468_, v_x_469_);
return v_res_472_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_473_, lean_object* v_keys_474_, lean_object* v_vals_475_, lean_object* v_heq_476_, lean_object* v_i_477_, lean_object* v_k_478_){
_start:
{
lean_object* v___x_479_; 
v___x_479_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1_spec__2___redArg(v_keys_474_, v_vals_475_, v_i_477_, v_k_478_);
return v___x_479_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03b2_480_, lean_object* v_keys_481_, lean_object* v_vals_482_, lean_object* v_heq_483_, lean_object* v_i_484_, lean_object* v_k_485_){
_start:
{
lean_object* v_res_486_; 
v_res_486_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1_spec__2(v_00_u03b2_480_, v_keys_481_, v_vals_482_, v_heq_483_, v_i_484_, v_k_485_);
lean_dec_ref(v_k_485_);
lean_dec_ref(v_vals_482_);
lean_dec_ref(v_keys_481_);
return v_res_486_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3_spec__5(lean_object* v_00_u03b2_487_, lean_object* v_n_488_, lean_object* v_k_489_, lean_object* v_v_490_){
_start:
{
lean_object* v___x_491_; 
v___x_491_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3_spec__5___redArg(v_n_488_, v_k_489_, v_v_490_);
return v___x_491_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3_spec__6(lean_object* v_00_u03b2_492_, size_t v_depth_493_, lean_object* v_keys_494_, lean_object* v_vals_495_, lean_object* v_heq_496_, lean_object* v_i_497_, lean_object* v_entries_498_){
_start:
{
lean_object* v___x_499_; 
v___x_499_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3_spec__6___redArg(v_depth_493_, v_keys_494_, v_vals_495_, v_i_497_, v_entries_498_);
return v___x_499_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3_spec__6___boxed(lean_object* v_00_u03b2_500_, lean_object* v_depth_501_, lean_object* v_keys_502_, lean_object* v_vals_503_, lean_object* v_heq_504_, lean_object* v_i_505_, lean_object* v_entries_506_){
_start:
{
size_t v_depth_boxed_507_; lean_object* v_res_508_; 
v_depth_boxed_507_ = lean_unbox_usize(v_depth_501_);
lean_dec(v_depth_501_);
v_res_508_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3_spec__6(v_00_u03b2_500_, v_depth_boxed_507_, v_keys_502_, v_vals_503_, v_heq_504_, v_i_505_, v_entries_506_);
lean_dec_ref(v_vals_503_);
lean_dec_ref(v_keys_502_);
return v_res_508_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3_spec__5_spec__6(lean_object* v_00_u03b2_509_, lean_object* v_x_510_, lean_object* v_x_511_, lean_object* v_x_512_, lean_object* v_x_513_){
_start:
{
lean_object* v___x_514_; 
v___x_514_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3_spec__5_spec__6___redArg(v_x_510_, v_x_511_, v_x_512_, v_x_513_);
return v___x_514_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0_spec__0(lean_object* v_msgData_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_){
_start:
{
lean_object* v___x_521_; lean_object* v_env_522_; lean_object* v___x_523_; lean_object* v_mctx_524_; lean_object* v_lctx_525_; lean_object* v_options_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; 
v___x_521_ = lean_st_ref_get(v___y_519_);
v_env_522_ = lean_ctor_get(v___x_521_, 0);
lean_inc_ref(v_env_522_);
lean_dec(v___x_521_);
v___x_523_ = lean_st_ref_get(v___y_517_);
v_mctx_524_ = lean_ctor_get(v___x_523_, 0);
lean_inc_ref(v_mctx_524_);
lean_dec(v___x_523_);
v_lctx_525_ = lean_ctor_get(v___y_516_, 2);
v_options_526_ = lean_ctor_get(v___y_518_, 2);
lean_inc_ref(v_options_526_);
lean_inc_ref(v_lctx_525_);
v___x_527_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_527_, 0, v_env_522_);
lean_ctor_set(v___x_527_, 1, v_mctx_524_);
lean_ctor_set(v___x_527_, 2, v_lctx_525_);
lean_ctor_set(v___x_527_, 3, v_options_526_);
v___x_528_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_528_, 0, v___x_527_);
lean_ctor_set(v___x_528_, 1, v_msgData_515_);
v___x_529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_529_, 0, v___x_528_);
return v___x_529_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0_spec__0___boxed(lean_object* v_msgData_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_){
_start:
{
lean_object* v_res_536_; 
v_res_536_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0_spec__0(v_msgData_530_, v___y_531_, v___y_532_, v___y_533_, v___y_534_);
lean_dec(v___y_534_);
lean_dec_ref(v___y_533_);
lean_dec(v___y_532_);
lean_dec_ref(v___y_531_);
return v_res_536_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_537_; double v___x_538_; 
v___x_537_ = lean_unsigned_to_nat(0u);
v___x_538_ = lean_float_of_nat(v___x_537_);
return v___x_538_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0___redArg(lean_object* v_cls_542_, lean_object* v_msg_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_){
_start:
{
lean_object* v_ref_549_; lean_object* v___x_550_; lean_object* v_a_551_; lean_object* v___x_553_; uint8_t v_isShared_554_; uint8_t v_isSharedCheck_595_; 
v_ref_549_ = lean_ctor_get(v___y_546_, 5);
v___x_550_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0_spec__0(v_msg_543_, v___y_544_, v___y_545_, v___y_546_, v___y_547_);
v_a_551_ = lean_ctor_get(v___x_550_, 0);
v_isSharedCheck_595_ = !lean_is_exclusive(v___x_550_);
if (v_isSharedCheck_595_ == 0)
{
v___x_553_ = v___x_550_;
v_isShared_554_ = v_isSharedCheck_595_;
goto v_resetjp_552_;
}
else
{
lean_inc(v_a_551_);
lean_dec(v___x_550_);
v___x_553_ = lean_box(0);
v_isShared_554_ = v_isSharedCheck_595_;
goto v_resetjp_552_;
}
v_resetjp_552_:
{
lean_object* v___x_555_; lean_object* v_traceState_556_; lean_object* v_env_557_; lean_object* v_nextMacroScope_558_; lean_object* v_ngen_559_; lean_object* v_auxDeclNGen_560_; lean_object* v_cache_561_; lean_object* v_messages_562_; lean_object* v_infoState_563_; lean_object* v_snapshotTasks_564_; lean_object* v___x_566_; uint8_t v_isShared_567_; uint8_t v_isSharedCheck_594_; 
v___x_555_ = lean_st_ref_take(v___y_547_);
v_traceState_556_ = lean_ctor_get(v___x_555_, 4);
v_env_557_ = lean_ctor_get(v___x_555_, 0);
v_nextMacroScope_558_ = lean_ctor_get(v___x_555_, 1);
v_ngen_559_ = lean_ctor_get(v___x_555_, 2);
v_auxDeclNGen_560_ = lean_ctor_get(v___x_555_, 3);
v_cache_561_ = lean_ctor_get(v___x_555_, 5);
v_messages_562_ = lean_ctor_get(v___x_555_, 6);
v_infoState_563_ = lean_ctor_get(v___x_555_, 7);
v_snapshotTasks_564_ = lean_ctor_get(v___x_555_, 8);
v_isSharedCheck_594_ = !lean_is_exclusive(v___x_555_);
if (v_isSharedCheck_594_ == 0)
{
v___x_566_ = v___x_555_;
v_isShared_567_ = v_isSharedCheck_594_;
goto v_resetjp_565_;
}
else
{
lean_inc(v_snapshotTasks_564_);
lean_inc(v_infoState_563_);
lean_inc(v_messages_562_);
lean_inc(v_cache_561_);
lean_inc(v_traceState_556_);
lean_inc(v_auxDeclNGen_560_);
lean_inc(v_ngen_559_);
lean_inc(v_nextMacroScope_558_);
lean_inc(v_env_557_);
lean_dec(v___x_555_);
v___x_566_ = lean_box(0);
v_isShared_567_ = v_isSharedCheck_594_;
goto v_resetjp_565_;
}
v_resetjp_565_:
{
uint64_t v_tid_568_; lean_object* v_traces_569_; lean_object* v___x_571_; uint8_t v_isShared_572_; uint8_t v_isSharedCheck_593_; 
v_tid_568_ = lean_ctor_get_uint64(v_traceState_556_, sizeof(void*)*1);
v_traces_569_ = lean_ctor_get(v_traceState_556_, 0);
v_isSharedCheck_593_ = !lean_is_exclusive(v_traceState_556_);
if (v_isSharedCheck_593_ == 0)
{
v___x_571_ = v_traceState_556_;
v_isShared_572_ = v_isSharedCheck_593_;
goto v_resetjp_570_;
}
else
{
lean_inc(v_traces_569_);
lean_dec(v_traceState_556_);
v___x_571_ = lean_box(0);
v_isShared_572_ = v_isSharedCheck_593_;
goto v_resetjp_570_;
}
v_resetjp_570_:
{
lean_object* v___x_573_; double v___x_574_; uint8_t v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_583_; 
v___x_573_ = lean_box(0);
v___x_574_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0___redArg___closed__0);
v___x_575_ = 0;
v___x_576_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0___redArg___closed__1));
v___x_577_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_577_, 0, v_cls_542_);
lean_ctor_set(v___x_577_, 1, v___x_573_);
lean_ctor_set(v___x_577_, 2, v___x_576_);
lean_ctor_set_float(v___x_577_, sizeof(void*)*3, v___x_574_);
lean_ctor_set_float(v___x_577_, sizeof(void*)*3 + 8, v___x_574_);
lean_ctor_set_uint8(v___x_577_, sizeof(void*)*3 + 16, v___x_575_);
v___x_578_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0___redArg___closed__2));
v___x_579_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_579_, 0, v___x_577_);
lean_ctor_set(v___x_579_, 1, v_a_551_);
lean_ctor_set(v___x_579_, 2, v___x_578_);
lean_inc(v_ref_549_);
v___x_580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_580_, 0, v_ref_549_);
lean_ctor_set(v___x_580_, 1, v___x_579_);
v___x_581_ = l_Lean_PersistentArray_push___redArg(v_traces_569_, v___x_580_);
if (v_isShared_572_ == 0)
{
lean_ctor_set(v___x_571_, 0, v___x_581_);
v___x_583_ = v___x_571_;
goto v_reusejp_582_;
}
else
{
lean_object* v_reuseFailAlloc_592_; 
v_reuseFailAlloc_592_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_592_, 0, v___x_581_);
lean_ctor_set_uint64(v_reuseFailAlloc_592_, sizeof(void*)*1, v_tid_568_);
v___x_583_ = v_reuseFailAlloc_592_;
goto v_reusejp_582_;
}
v_reusejp_582_:
{
lean_object* v___x_585_; 
if (v_isShared_567_ == 0)
{
lean_ctor_set(v___x_566_, 4, v___x_583_);
v___x_585_ = v___x_566_;
goto v_reusejp_584_;
}
else
{
lean_object* v_reuseFailAlloc_591_; 
v_reuseFailAlloc_591_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_591_, 0, v_env_557_);
lean_ctor_set(v_reuseFailAlloc_591_, 1, v_nextMacroScope_558_);
lean_ctor_set(v_reuseFailAlloc_591_, 2, v_ngen_559_);
lean_ctor_set(v_reuseFailAlloc_591_, 3, v_auxDeclNGen_560_);
lean_ctor_set(v_reuseFailAlloc_591_, 4, v___x_583_);
lean_ctor_set(v_reuseFailAlloc_591_, 5, v_cache_561_);
lean_ctor_set(v_reuseFailAlloc_591_, 6, v_messages_562_);
lean_ctor_set(v_reuseFailAlloc_591_, 7, v_infoState_563_);
lean_ctor_set(v_reuseFailAlloc_591_, 8, v_snapshotTasks_564_);
v___x_585_ = v_reuseFailAlloc_591_;
goto v_reusejp_584_;
}
v_reusejp_584_:
{
lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_589_; 
v___x_586_ = lean_st_ref_set(v___y_547_, v___x_585_);
v___x_587_ = lean_box(0);
if (v_isShared_554_ == 0)
{
lean_ctor_set(v___x_553_, 0, v___x_587_);
v___x_589_ = v___x_553_;
goto v_reusejp_588_;
}
else
{
lean_object* v_reuseFailAlloc_590_; 
v_reuseFailAlloc_590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_590_, 0, v___x_587_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0___redArg___boxed(lean_object* v_cls_596_, lean_object* v_msg_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_){
_start:
{
lean_object* v_res_603_; 
v_res_603_ = l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0___redArg(v_cls_596_, v_msg_597_, v___y_598_, v___y_599_, v___y_600_, v___y_601_);
lean_dec(v___y_601_);
lean_dec_ref(v___y_600_);
lean_dec(v___y_599_);
lean_dec_ref(v___y_598_);
return v_res_603_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkInjEq___closed__6(void){
_start:
{
lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; 
v___x_614_ = ((lean_object*)(l_Lean_Meta_Grind_mkInjEq___closed__3));
v___x_615_ = ((lean_object*)(l_Lean_Meta_Grind_mkInjEq___closed__5));
v___x_616_ = l_Lean_Name_append(v___x_615_, v___x_614_);
return v___x_616_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkInjEq___closed__8(void){
_start:
{
lean_object* v___x_618_; lean_object* v___x_619_; 
v___x_618_ = ((lean_object*)(l_Lean_Meta_Grind_mkInjEq___closed__7));
v___x_619_ = l_Lean_stringToMessageData(v___x_618_);
return v___x_619_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkInjEq(lean_object* v_e_620_, lean_object* v_a_621_, lean_object* v_a_622_, lean_object* v_a_623_, lean_object* v_a_624_, lean_object* v_a_625_, lean_object* v_a_626_, lean_object* v_a_627_, lean_object* v_a_628_, lean_object* v_a_629_, lean_object* v_a_630_){
_start:
{
if (lean_obj_tag(v_e_620_) == 5)
{
lean_object* v_fn_632_; lean_object* v_arg_633_; lean_object* v___x_634_; 
v_fn_632_ = lean_ctor_get(v_e_620_, 0);
v_arg_633_ = lean_ctor_get(v_e_620_, 1);
lean_inc_ref_n(v_arg_633_, 2);
lean_inc_ref(v_fn_632_);
v___x_634_ = l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f(v_fn_632_, v_arg_633_, v_a_621_, v_a_622_, v_a_623_, v_a_624_, v_a_625_, v_a_626_, v_a_627_, v_a_628_, v_a_629_, v_a_630_);
if (lean_obj_tag(v___x_634_) == 0)
{
lean_object* v_a_635_; lean_object* v___x_637_; uint8_t v_isShared_638_; uint8_t v_isSharedCheck_687_; 
v_a_635_ = lean_ctor_get(v___x_634_, 0);
v_isSharedCheck_687_ = !lean_is_exclusive(v___x_634_);
if (v_isSharedCheck_687_ == 0)
{
v___x_637_ = v___x_634_;
v_isShared_638_ = v_isSharedCheck_687_;
goto v_resetjp_636_;
}
else
{
lean_inc(v_a_635_);
lean_dec(v___x_634_);
v___x_637_ = lean_box(0);
v_isShared_638_ = v_isSharedCheck_687_;
goto v_resetjp_636_;
}
v_resetjp_636_:
{
if (lean_obj_tag(v_a_635_) == 1)
{
lean_object* v_val_639_; lean_object* v_fst_640_; lean_object* v_snd_641_; lean_object* v___x_643_; uint8_t v_isShared_644_; uint8_t v_isSharedCheck_682_; 
lean_del_object(v___x_637_);
v_val_639_ = lean_ctor_get(v_a_635_, 0);
lean_inc(v_val_639_);
lean_dec_ref_known(v_a_635_, 1);
v_fst_640_ = lean_ctor_get(v_val_639_, 0);
v_snd_641_ = lean_ctor_get(v_val_639_, 1);
v_isSharedCheck_682_ = !lean_is_exclusive(v_val_639_);
if (v_isSharedCheck_682_ == 0)
{
v___x_643_ = v_val_639_;
v_isShared_644_ = v_isSharedCheck_682_;
goto v_resetjp_642_;
}
else
{
lean_inc(v_snd_641_);
lean_inc(v_fst_640_);
lean_dec(v_val_639_);
v___x_643_ = lean_box(0);
v_isShared_644_ = v_isSharedCheck_682_;
goto v_resetjp_642_;
}
v_resetjp_642_:
{
lean_object* v___x_645_; 
v___x_645_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_620_, v_a_621_);
if (lean_obj_tag(v___x_645_) == 0)
{
lean_object* v_a_646_; lean_object* v___x_647_; lean_object* v___y_649_; lean_object* v___y_650_; lean_object* v___y_651_; lean_object* v___y_652_; lean_object* v___y_653_; lean_object* v___y_654_; lean_object* v___x_658_; lean_object* v___x_659_; 
v_a_646_ = lean_ctor_get(v___x_645_, 0);
lean_inc(v_a_646_);
lean_dec_ref_known(v___x_645_, 1);
v___x_647_ = l_Lean_Expr_app___override(v_fst_640_, v_e_620_);
v___x_658_ = lean_box(0);
lean_inc(v_a_630_);
lean_inc_ref(v_a_629_);
lean_inc(v_a_628_);
lean_inc_ref(v_a_627_);
lean_inc(v_a_626_);
lean_inc_ref(v_a_625_);
lean_inc(v_a_624_);
lean_inc_ref(v_a_623_);
lean_inc(v_a_622_);
lean_inc(v_a_621_);
lean_inc_ref(v___x_647_);
v___x_659_ = lean_grind_internalize(v___x_647_, v_a_646_, v___x_658_, v_a_621_, v_a_622_, v_a_623_, v_a_624_, v_a_625_, v_a_626_, v_a_627_, v_a_628_, v_a_629_, v_a_630_);
if (lean_obj_tag(v___x_659_) == 0)
{
lean_object* v_options_660_; uint8_t v_hasTrace_661_; 
lean_dec_ref_known(v___x_659_, 1);
v_options_660_ = lean_ctor_get(v_a_629_, 2);
v_hasTrace_661_ = lean_ctor_get_uint8(v_options_660_, sizeof(void*)*1);
if (v_hasTrace_661_ == 0)
{
lean_del_object(v___x_643_);
v___y_649_ = v_a_621_;
v___y_650_ = v_a_623_;
v___y_651_ = v_a_627_;
v___y_652_ = v_a_628_;
v___y_653_ = v_a_629_;
v___y_654_ = v_a_630_;
goto v___jp_648_;
}
else
{
lean_object* v_inheritedTraceOptions_662_; lean_object* v___x_663_; lean_object* v___x_664_; uint8_t v___x_665_; 
v_inheritedTraceOptions_662_ = lean_ctor_get(v_a_629_, 13);
v___x_663_ = ((lean_object*)(l_Lean_Meta_Grind_mkInjEq___closed__3));
v___x_664_ = lean_obj_once(&l_Lean_Meta_Grind_mkInjEq___closed__6, &l_Lean_Meta_Grind_mkInjEq___closed__6_once, _init_l_Lean_Meta_Grind_mkInjEq___closed__6);
v___x_665_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_662_, v_options_660_, v___x_664_);
if (v___x_665_ == 0)
{
lean_del_object(v___x_643_);
v___y_649_ = v_a_621_;
v___y_650_ = v_a_623_;
v___y_651_ = v_a_627_;
v___y_652_ = v_a_628_;
v___y_653_ = v_a_629_;
v___y_654_ = v_a_630_;
goto v___jp_648_;
}
else
{
lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_669_; 
lean_inc_ref(v___x_647_);
v___x_666_ = l_Lean_MessageData_ofExpr(v___x_647_);
v___x_667_ = lean_obj_once(&l_Lean_Meta_Grind_mkInjEq___closed__8, &l_Lean_Meta_Grind_mkInjEq___closed__8_once, _init_l_Lean_Meta_Grind_mkInjEq___closed__8);
if (v_isShared_644_ == 0)
{
lean_ctor_set_tag(v___x_643_, 7);
lean_ctor_set(v___x_643_, 1, v___x_667_);
lean_ctor_set(v___x_643_, 0, v___x_666_);
v___x_669_ = v___x_643_;
goto v_reusejp_668_;
}
else
{
lean_object* v_reuseFailAlloc_673_; 
v_reuseFailAlloc_673_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_673_, 0, v___x_666_);
lean_ctor_set(v_reuseFailAlloc_673_, 1, v___x_667_);
v___x_669_ = v_reuseFailAlloc_673_;
goto v_reusejp_668_;
}
v_reusejp_668_:
{
lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; 
lean_inc_ref(v_arg_633_);
v___x_670_ = l_Lean_MessageData_ofExpr(v_arg_633_);
v___x_671_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_671_, 0, v___x_669_);
lean_ctor_set(v___x_671_, 1, v___x_670_);
v___x_672_ = l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0___redArg(v___x_663_, v___x_671_, v_a_627_, v_a_628_, v_a_629_, v_a_630_);
if (lean_obj_tag(v___x_672_) == 0)
{
lean_dec_ref_known(v___x_672_, 1);
v___y_649_ = v_a_621_;
v___y_650_ = v_a_623_;
v___y_651_ = v_a_627_;
v___y_652_ = v_a_628_;
v___y_653_ = v_a_629_;
v___y_654_ = v_a_630_;
goto v___jp_648_;
}
else
{
lean_dec_ref(v___x_647_);
lean_dec(v_snd_641_);
lean_dec_ref(v_arg_633_);
return v___x_672_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_647_);
lean_del_object(v___x_643_);
lean_dec(v_snd_641_);
lean_dec_ref(v_arg_633_);
return v___x_659_;
}
v___jp_648_:
{
lean_object* v___x_655_; uint8_t v___x_656_; lean_object* v___x_657_; 
lean_inc_ref(v_arg_633_);
v___x_655_ = l_Lean_Expr_app___override(v_snd_641_, v_arg_633_);
v___x_656_ = 0;
v___x_657_ = l_Lean_Meta_Grind_pushEqCore___redArg(v___x_647_, v_arg_633_, v___x_655_, v___x_656_, v___y_649_, v___y_650_, v___y_651_, v___y_652_, v___y_653_, v___y_654_);
return v___x_657_;
}
}
else
{
lean_object* v_a_674_; lean_object* v___x_676_; uint8_t v_isShared_677_; uint8_t v_isSharedCheck_681_; 
lean_del_object(v___x_643_);
lean_dec(v_snd_641_);
lean_dec(v_fst_640_);
lean_dec_ref(v_arg_633_);
lean_dec_ref_known(v_e_620_, 2);
v_a_674_ = lean_ctor_get(v___x_645_, 0);
v_isSharedCheck_681_ = !lean_is_exclusive(v___x_645_);
if (v_isSharedCheck_681_ == 0)
{
v___x_676_ = v___x_645_;
v_isShared_677_ = v_isSharedCheck_681_;
goto v_resetjp_675_;
}
else
{
lean_inc(v_a_674_);
lean_dec(v___x_645_);
v___x_676_ = lean_box(0);
v_isShared_677_ = v_isSharedCheck_681_;
goto v_resetjp_675_;
}
v_resetjp_675_:
{
lean_object* v___x_679_; 
if (v_isShared_677_ == 0)
{
v___x_679_ = v___x_676_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_680_; 
v_reuseFailAlloc_680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_680_, 0, v_a_674_);
v___x_679_ = v_reuseFailAlloc_680_;
goto v_reusejp_678_;
}
v_reusejp_678_:
{
return v___x_679_;
}
}
}
}
}
else
{
lean_object* v___x_683_; lean_object* v___x_685_; 
lean_dec(v_a_635_);
lean_dec_ref(v_arg_633_);
lean_dec_ref_known(v_e_620_, 2);
v___x_683_ = lean_box(0);
if (v_isShared_638_ == 0)
{
lean_ctor_set(v___x_637_, 0, v___x_683_);
v___x_685_ = v___x_637_;
goto v_reusejp_684_;
}
else
{
lean_object* v_reuseFailAlloc_686_; 
v_reuseFailAlloc_686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_686_, 0, v___x_683_);
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
else
{
lean_object* v_a_688_; lean_object* v___x_690_; uint8_t v_isShared_691_; uint8_t v_isSharedCheck_695_; 
lean_dec_ref(v_arg_633_);
lean_dec_ref_known(v_e_620_, 2);
v_a_688_ = lean_ctor_get(v___x_634_, 0);
v_isSharedCheck_695_ = !lean_is_exclusive(v___x_634_);
if (v_isSharedCheck_695_ == 0)
{
v___x_690_ = v___x_634_;
v_isShared_691_ = v_isSharedCheck_695_;
goto v_resetjp_689_;
}
else
{
lean_inc(v_a_688_);
lean_dec(v___x_634_);
v___x_690_ = lean_box(0);
v_isShared_691_ = v_isSharedCheck_695_;
goto v_resetjp_689_;
}
v_resetjp_689_:
{
lean_object* v___x_693_; 
if (v_isShared_691_ == 0)
{
v___x_693_ = v___x_690_;
goto v_reusejp_692_;
}
else
{
lean_object* v_reuseFailAlloc_694_; 
v_reuseFailAlloc_694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_694_, 0, v_a_688_);
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
lean_object* v___x_696_; lean_object* v___x_697_; 
lean_dec_ref(v_e_620_);
v___x_696_ = lean_box(0);
v___x_697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_697_, 0, v___x_696_);
return v___x_697_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkInjEq___boxed(lean_object* v_e_698_, lean_object* v_a_699_, lean_object* v_a_700_, lean_object* v_a_701_, lean_object* v_a_702_, lean_object* v_a_703_, lean_object* v_a_704_, lean_object* v_a_705_, lean_object* v_a_706_, lean_object* v_a_707_, lean_object* v_a_708_, lean_object* v_a_709_){
_start:
{
lean_object* v_res_710_; 
v_res_710_ = l_Lean_Meta_Grind_mkInjEq(v_e_698_, v_a_699_, v_a_700_, v_a_701_, v_a_702_, v_a_703_, v_a_704_, v_a_705_, v_a_706_, v_a_707_, v_a_708_);
lean_dec(v_a_708_);
lean_dec_ref(v_a_707_);
lean_dec(v_a_706_);
lean_dec_ref(v_a_705_);
lean_dec(v_a_704_);
lean_dec_ref(v_a_703_);
lean_dec(v_a_702_);
lean_dec_ref(v_a_701_);
lean_dec(v_a_700_);
lean_dec(v_a_699_);
return v_res_710_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0(lean_object* v_cls_711_, lean_object* v_msg_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_){
_start:
{
lean_object* v___x_724_; 
v___x_724_ = l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0___redArg(v_cls_711_, v_msg_712_, v___y_719_, v___y_720_, v___y_721_, v___y_722_);
return v___x_724_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0___boxed(lean_object* v_cls_725_, lean_object* v_msg_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_){
_start:
{
lean_object* v_res_738_; 
v_res_738_ = l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0(v_cls_725_, v_msg_726_, v___y_727_, v___y_728_, v___y_729_, v___y_730_, v___y_731_, v___y_732_, v___y_733_, v___y_734_, v___y_735_, v___y_736_);
lean_dec(v___y_736_);
lean_dec_ref(v___y_735_);
lean_dec(v___y_734_);
lean_dec_ref(v___y_733_);
lean_dec(v___y_732_);
lean_dec_ref(v___y_731_);
lean_dec(v___y_730_);
lean_dec_ref(v___y_729_);
lean_dec(v___y_728_);
lean_dec(v___y_727_);
return v_res_738_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1_spec__2___redArg(lean_object* v_keys_739_, lean_object* v_vals_740_, lean_object* v_i_741_, lean_object* v_k_742_){
_start:
{
lean_object* v___x_743_; uint8_t v___x_744_; 
v___x_743_ = lean_array_get_size(v_keys_739_);
v___x_744_ = lean_nat_dec_lt(v_i_741_, v___x_743_);
if (v___x_744_ == 0)
{
lean_object* v___x_745_; 
lean_dec(v_i_741_);
v___x_745_ = lean_box(0);
return v___x_745_;
}
else
{
lean_object* v_k_x27_746_; uint8_t v___x_747_; 
v_k_x27_746_ = lean_array_fget_borrowed(v_keys_739_, v_i_741_);
v___x_747_ = l_Lean_instBEqHeadIndex_beq(v_k_742_, v_k_x27_746_);
if (v___x_747_ == 0)
{
lean_object* v___x_748_; lean_object* v___x_749_; 
v___x_748_ = lean_unsigned_to_nat(1u);
v___x_749_ = lean_nat_add(v_i_741_, v___x_748_);
lean_dec(v_i_741_);
v_i_741_ = v___x_749_;
goto _start;
}
else
{
lean_object* v___x_751_; lean_object* v___x_752_; 
v___x_751_ = lean_array_fget_borrowed(v_vals_740_, v_i_741_);
lean_dec(v_i_741_);
lean_inc(v___x_751_);
v___x_752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_752_, 0, v___x_751_);
return v___x_752_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_keys_753_, lean_object* v_vals_754_, lean_object* v_i_755_, lean_object* v_k_756_){
_start:
{
lean_object* v_res_757_; 
v_res_757_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1_spec__2___redArg(v_keys_753_, v_vals_754_, v_i_755_, v_k_756_);
lean_dec(v_k_756_);
lean_dec_ref(v_vals_754_);
lean_dec_ref(v_keys_753_);
return v_res_757_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1___redArg(lean_object* v_x_758_, size_t v_x_759_, lean_object* v_x_760_){
_start:
{
if (lean_obj_tag(v_x_758_) == 0)
{
lean_object* v_es_761_; lean_object* v___x_762_; size_t v___x_763_; size_t v___x_764_; lean_object* v_j_765_; lean_object* v___x_766_; 
v_es_761_ = lean_ctor_get(v_x_758_, 0);
v___x_762_ = lean_box(2);
v___x_763_ = ((size_t)31ULL);
v___x_764_ = lean_usize_land(v_x_759_, v___x_763_);
v_j_765_ = lean_usize_to_nat(v___x_764_);
v___x_766_ = lean_array_get_borrowed(v___x_762_, v_es_761_, v_j_765_);
lean_dec(v_j_765_);
switch(lean_obj_tag(v___x_766_))
{
case 0:
{
lean_object* v_key_767_; lean_object* v_val_768_; uint8_t v___x_769_; 
v_key_767_ = lean_ctor_get(v___x_766_, 0);
v_val_768_ = lean_ctor_get(v___x_766_, 1);
v___x_769_ = l_Lean_instBEqHeadIndex_beq(v_x_760_, v_key_767_);
if (v___x_769_ == 0)
{
lean_object* v___x_770_; 
v___x_770_ = lean_box(0);
return v___x_770_;
}
else
{
lean_object* v___x_771_; 
lean_inc(v_val_768_);
v___x_771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_771_, 0, v_val_768_);
return v___x_771_;
}
}
case 1:
{
lean_object* v_node_772_; size_t v___x_773_; size_t v___x_774_; 
v_node_772_ = lean_ctor_get(v___x_766_, 0);
v___x_773_ = ((size_t)5ULL);
v___x_774_ = lean_usize_shift_right(v_x_759_, v___x_773_);
v_x_758_ = v_node_772_;
v_x_759_ = v___x_774_;
goto _start;
}
default: 
{
lean_object* v___x_776_; 
v___x_776_ = lean_box(0);
return v___x_776_;
}
}
}
else
{
lean_object* v_ks_777_; lean_object* v_vs_778_; lean_object* v___x_779_; lean_object* v___x_780_; 
v_ks_777_ = lean_ctor_get(v_x_758_, 0);
v_vs_778_ = lean_ctor_get(v_x_758_, 1);
v___x_779_ = lean_unsigned_to_nat(0u);
v___x_780_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1_spec__2___redArg(v_ks_777_, v_vs_778_, v___x_779_, v_x_760_);
return v___x_780_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1___redArg___boxed(lean_object* v_x_781_, lean_object* v_x_782_, lean_object* v_x_783_){
_start:
{
size_t v_x_9704__boxed_784_; lean_object* v_res_785_; 
v_x_9704__boxed_784_ = lean_unbox_usize(v_x_782_);
lean_dec(v_x_782_);
v_res_785_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1___redArg(v_x_781_, v_x_9704__boxed_784_, v_x_783_);
lean_dec(v_x_783_);
lean_dec_ref(v_x_781_);
return v_res_785_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1___redArg(lean_object* v_x_786_, lean_object* v_x_787_){
_start:
{
uint64_t v___x_788_; size_t v___x_789_; lean_object* v___x_790_; 
v___x_788_ = l_Lean_HeadIndex_hash(v_x_787_);
v___x_789_ = lean_uint64_to_usize(v___x_788_);
v___x_790_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1___redArg(v_x_786_, v___x_789_, v_x_787_);
return v___x_790_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1___redArg___boxed(lean_object* v_x_791_, lean_object* v_x_792_){
_start:
{
lean_object* v_res_793_; 
v_res_793_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1___redArg(v_x_791_, v_x_792_);
lean_dec(v_x_792_);
lean_dec_ref(v_x_791_);
return v_res_793_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__0___redArg(lean_object* v_f_794_, lean_object* v_as_x27_795_, lean_object* v_b_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_){
_start:
{
if (lean_obj_tag(v_as_x27_795_) == 0)
{
lean_object* v___x_808_; 
v___x_808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_808_, 0, v_b_796_);
return v___x_808_;
}
else
{
lean_object* v_head_809_; lean_object* v_tail_810_; lean_object* v___x_811_; uint8_t v___y_813_; uint8_t v___x_817_; 
v_head_809_ = lean_ctor_get(v_as_x27_795_, 0);
v_tail_810_ = lean_ctor_get(v_as_x27_795_, 1);
v___x_811_ = lean_box(0);
v___x_817_ = l_Lean_Expr_isApp(v_head_809_);
if (v___x_817_ == 0)
{
v___y_813_ = v___x_817_;
goto v___jp_812_;
}
else
{
lean_object* v___x_818_; uint8_t v___x_819_; 
v___x_818_ = l_Lean_Expr_appFn_x21(v_head_809_);
v___x_819_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_818_, v_f_794_);
lean_dec_ref(v___x_818_);
v___y_813_ = v___x_819_;
goto v___jp_812_;
}
v___jp_812_:
{
if (v___y_813_ == 0)
{
v_as_x27_795_ = v_tail_810_;
v_b_796_ = v___x_811_;
goto _start;
}
else
{
lean_object* v___x_815_; 
lean_inc(v_head_809_);
v___x_815_ = l_Lean_Meta_Grind_mkInjEq(v_head_809_, v___y_797_, v___y_798_, v___y_799_, v___y_800_, v___y_801_, v___y_802_, v___y_803_, v___y_804_, v___y_805_, v___y_806_);
if (lean_obj_tag(v___x_815_) == 0)
{
lean_dec_ref_known(v___x_815_, 1);
v_as_x27_795_ = v_tail_810_;
v_b_796_ = v___x_811_;
goto _start;
}
else
{
return v___x_815_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__0___redArg___boxed(lean_object* v_f_820_, lean_object* v_as_x27_821_, lean_object* v_b_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_){
_start:
{
lean_object* v_res_834_; 
v_res_834_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__0___redArg(v_f_820_, v_as_x27_821_, v_b_822_, v___y_823_, v___y_824_, v___y_825_, v___y_826_, v___y_827_, v___y_828_, v___y_829_, v___y_830_, v___y_831_, v___y_832_);
lean_dec(v___y_832_);
lean_dec_ref(v___y_831_);
lean_dec(v___y_830_);
lean_dec_ref(v___y_829_);
lean_dec(v___y_828_);
lean_dec_ref(v___y_827_);
lean_dec(v___y_826_);
lean_dec_ref(v___y_825_);
lean_dec(v___y_824_);
lean_dec(v___y_823_);
lean_dec(v_as_x27_821_);
lean_dec_ref(v_f_820_);
return v_res_834_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn(lean_object* v_us_835_, lean_object* v_00_u03b1_836_, lean_object* v_00_u03b2_837_, lean_object* v_f_838_, lean_object* v_h_839_, lean_object* v_a_840_, lean_object* v_a_841_, lean_object* v_a_842_, lean_object* v_a_843_, lean_object* v_a_844_, lean_object* v_a_845_, lean_object* v_a_846_, lean_object* v_a_847_, lean_object* v_a_848_, lean_object* v_a_849_){
_start:
{
lean_object* v___x_851_; lean_object* v_toGoalState_852_; lean_object* v_inj_853_; lean_object* v_mvarId_854_; lean_object* v___x_856_; uint8_t v_isShared_857_; uint8_t v_isSharedCheck_918_; 
v___x_851_ = lean_st_ref_take(v_a_840_);
v_toGoalState_852_ = lean_ctor_get(v___x_851_, 0);
lean_inc_ref(v_toGoalState_852_);
v_inj_853_ = lean_ctor_get(v_toGoalState_852_, 13);
lean_inc_ref(v_inj_853_);
v_mvarId_854_ = lean_ctor_get(v___x_851_, 1);
v_isSharedCheck_918_ = !lean_is_exclusive(v___x_851_);
if (v_isSharedCheck_918_ == 0)
{
lean_object* v_unused_919_; 
v_unused_919_ = lean_ctor_get(v___x_851_, 0);
lean_dec(v_unused_919_);
v___x_856_ = v___x_851_;
v_isShared_857_ = v_isSharedCheck_918_;
goto v_resetjp_855_;
}
else
{
lean_inc(v_mvarId_854_);
lean_dec(v___x_851_);
v___x_856_ = lean_box(0);
v_isShared_857_ = v_isSharedCheck_918_;
goto v_resetjp_855_;
}
v_resetjp_855_:
{
lean_object* v_nextDeclIdx_858_; lean_object* v_enodeMap_859_; lean_object* v_exprs_860_; lean_object* v_parents_861_; lean_object* v_congrTable_862_; lean_object* v_appMap_863_; lean_object* v_indicesFound_864_; lean_object* v_newFacts_865_; uint8_t v_inconsistent_866_; lean_object* v_nextIdx_867_; lean_object* v_newRawFacts_868_; lean_object* v_facts_869_; lean_object* v_extThms_870_; lean_object* v_ematch_871_; lean_object* v_split_872_; lean_object* v_clean_873_; lean_object* v_sstates_874_; lean_object* v___x_876_; uint8_t v_isShared_877_; uint8_t v_isSharedCheck_916_; 
v_nextDeclIdx_858_ = lean_ctor_get(v_toGoalState_852_, 0);
v_enodeMap_859_ = lean_ctor_get(v_toGoalState_852_, 1);
v_exprs_860_ = lean_ctor_get(v_toGoalState_852_, 2);
v_parents_861_ = lean_ctor_get(v_toGoalState_852_, 3);
v_congrTable_862_ = lean_ctor_get(v_toGoalState_852_, 4);
v_appMap_863_ = lean_ctor_get(v_toGoalState_852_, 5);
v_indicesFound_864_ = lean_ctor_get(v_toGoalState_852_, 6);
v_newFacts_865_ = lean_ctor_get(v_toGoalState_852_, 7);
v_inconsistent_866_ = lean_ctor_get_uint8(v_toGoalState_852_, sizeof(void*)*17);
v_nextIdx_867_ = lean_ctor_get(v_toGoalState_852_, 8);
v_newRawFacts_868_ = lean_ctor_get(v_toGoalState_852_, 9);
v_facts_869_ = lean_ctor_get(v_toGoalState_852_, 10);
v_extThms_870_ = lean_ctor_get(v_toGoalState_852_, 11);
v_ematch_871_ = lean_ctor_get(v_toGoalState_852_, 12);
v_split_872_ = lean_ctor_get(v_toGoalState_852_, 14);
v_clean_873_ = lean_ctor_get(v_toGoalState_852_, 15);
v_sstates_874_ = lean_ctor_get(v_toGoalState_852_, 16);
v_isSharedCheck_916_ = !lean_is_exclusive(v_toGoalState_852_);
if (v_isSharedCheck_916_ == 0)
{
lean_object* v_unused_917_; 
v_unused_917_ = lean_ctor_get(v_toGoalState_852_, 13);
lean_dec(v_unused_917_);
v___x_876_ = v_toGoalState_852_;
v_isShared_877_ = v_isSharedCheck_916_;
goto v_resetjp_875_;
}
else
{
lean_inc(v_sstates_874_);
lean_inc(v_clean_873_);
lean_inc(v_split_872_);
lean_inc(v_ematch_871_);
lean_inc(v_extThms_870_);
lean_inc(v_facts_869_);
lean_inc(v_newRawFacts_868_);
lean_inc(v_nextIdx_867_);
lean_inc(v_newFacts_865_);
lean_inc(v_indicesFound_864_);
lean_inc(v_appMap_863_);
lean_inc(v_congrTable_862_);
lean_inc(v_parents_861_);
lean_inc(v_exprs_860_);
lean_inc(v_enodeMap_859_);
lean_inc(v_nextDeclIdx_858_);
lean_dec(v_toGoalState_852_);
v___x_876_ = lean_box(0);
v_isShared_877_ = v_isSharedCheck_916_;
goto v_resetjp_875_;
}
v_resetjp_875_:
{
lean_object* v_thms_878_; lean_object* v_fns_879_; lean_object* v___x_881_; uint8_t v_isShared_882_; uint8_t v_isSharedCheck_915_; 
v_thms_878_ = lean_ctor_get(v_inj_853_, 0);
v_fns_879_ = lean_ctor_get(v_inj_853_, 1);
v_isSharedCheck_915_ = !lean_is_exclusive(v_inj_853_);
if (v_isSharedCheck_915_ == 0)
{
v___x_881_ = v_inj_853_;
v_isShared_882_ = v_isSharedCheck_915_;
goto v_resetjp_880_;
}
else
{
lean_inc(v_fns_879_);
lean_inc(v_thms_878_);
lean_dec(v_inj_853_);
v___x_881_ = lean_box(0);
v_isShared_882_ = v_isSharedCheck_915_;
goto v_resetjp_880_;
}
v_resetjp_880_:
{
lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_887_; 
v___x_883_ = lean_box(0);
v___x_884_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_884_, 0, v_us_835_);
lean_ctor_set(v___x_884_, 1, v_00_u03b1_836_);
lean_ctor_set(v___x_884_, 2, v_00_u03b2_837_);
lean_ctor_set(v___x_884_, 3, v_h_839_);
lean_ctor_set(v___x_884_, 4, v___x_883_);
lean_inc_ref(v_f_838_);
v___x_885_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2___redArg(v_fns_879_, v_f_838_, v___x_884_);
if (v_isShared_882_ == 0)
{
lean_ctor_set(v___x_881_, 1, v___x_885_);
v___x_887_ = v___x_881_;
goto v_reusejp_886_;
}
else
{
lean_object* v_reuseFailAlloc_914_; 
v_reuseFailAlloc_914_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_914_, 0, v_thms_878_);
lean_ctor_set(v_reuseFailAlloc_914_, 1, v___x_885_);
v___x_887_ = v_reuseFailAlloc_914_;
goto v_reusejp_886_;
}
v_reusejp_886_:
{
lean_object* v___x_889_; 
if (v_isShared_877_ == 0)
{
lean_ctor_set(v___x_876_, 13, v___x_887_);
v___x_889_ = v___x_876_;
goto v_reusejp_888_;
}
else
{
lean_object* v_reuseFailAlloc_913_; 
v_reuseFailAlloc_913_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_913_, 0, v_nextDeclIdx_858_);
lean_ctor_set(v_reuseFailAlloc_913_, 1, v_enodeMap_859_);
lean_ctor_set(v_reuseFailAlloc_913_, 2, v_exprs_860_);
lean_ctor_set(v_reuseFailAlloc_913_, 3, v_parents_861_);
lean_ctor_set(v_reuseFailAlloc_913_, 4, v_congrTable_862_);
lean_ctor_set(v_reuseFailAlloc_913_, 5, v_appMap_863_);
lean_ctor_set(v_reuseFailAlloc_913_, 6, v_indicesFound_864_);
lean_ctor_set(v_reuseFailAlloc_913_, 7, v_newFacts_865_);
lean_ctor_set(v_reuseFailAlloc_913_, 8, v_nextIdx_867_);
lean_ctor_set(v_reuseFailAlloc_913_, 9, v_newRawFacts_868_);
lean_ctor_set(v_reuseFailAlloc_913_, 10, v_facts_869_);
lean_ctor_set(v_reuseFailAlloc_913_, 11, v_extThms_870_);
lean_ctor_set(v_reuseFailAlloc_913_, 12, v_ematch_871_);
lean_ctor_set(v_reuseFailAlloc_913_, 13, v___x_887_);
lean_ctor_set(v_reuseFailAlloc_913_, 14, v_split_872_);
lean_ctor_set(v_reuseFailAlloc_913_, 15, v_clean_873_);
lean_ctor_set(v_reuseFailAlloc_913_, 16, v_sstates_874_);
lean_ctor_set_uint8(v_reuseFailAlloc_913_, sizeof(void*)*17, v_inconsistent_866_);
v___x_889_ = v_reuseFailAlloc_913_;
goto v_reusejp_888_;
}
v_reusejp_888_:
{
lean_object* v___x_891_; 
if (v_isShared_857_ == 0)
{
lean_ctor_set(v___x_856_, 0, v___x_889_);
v___x_891_ = v___x_856_;
goto v_reusejp_890_;
}
else
{
lean_object* v_reuseFailAlloc_912_; 
v_reuseFailAlloc_912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_912_, 0, v___x_889_);
lean_ctor_set(v_reuseFailAlloc_912_, 1, v_mvarId_854_);
v___x_891_ = v_reuseFailAlloc_912_;
goto v_reusejp_890_;
}
v_reusejp_890_:
{
lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___y_895_; lean_object* v_toGoalState_906_; lean_object* v_appMap_907_; lean_object* v___x_908_; lean_object* v___x_909_; 
v___x_892_ = lean_st_ref_set(v_a_840_, v___x_891_);
v___x_893_ = lean_st_ref_get(v_a_840_);
v_toGoalState_906_ = lean_ctor_get(v___x_893_, 0);
lean_inc_ref(v_toGoalState_906_);
lean_dec(v___x_893_);
v_appMap_907_ = lean_ctor_get(v_toGoalState_906_, 5);
lean_inc_ref(v_appMap_907_);
lean_dec_ref(v_toGoalState_906_);
lean_inc_ref(v_f_838_);
v___x_908_ = l_Lean_Expr_toHeadIndex(v_f_838_);
v___x_909_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1___redArg(v_appMap_907_, v___x_908_);
lean_dec(v___x_908_);
lean_dec_ref(v_appMap_907_);
if (lean_obj_tag(v___x_909_) == 0)
{
lean_object* v___x_910_; 
v___x_910_ = lean_box(0);
v___y_895_ = v___x_910_;
goto v___jp_894_;
}
else
{
lean_object* v_val_911_; 
v_val_911_ = lean_ctor_get(v___x_909_, 0);
lean_inc(v_val_911_);
lean_dec_ref_known(v___x_909_, 1);
v___y_895_ = v_val_911_;
goto v___jp_894_;
}
v___jp_894_:
{
lean_object* v___x_896_; lean_object* v___x_897_; 
v___x_896_ = lean_box(0);
v___x_897_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__0___redArg(v_f_838_, v___y_895_, v___x_896_, v_a_840_, v_a_841_, v_a_842_, v_a_843_, v_a_844_, v_a_845_, v_a_846_, v_a_847_, v_a_848_, v_a_849_);
lean_dec(v___y_895_);
lean_dec_ref(v_f_838_);
if (lean_obj_tag(v___x_897_) == 0)
{
lean_object* v___x_899_; uint8_t v_isShared_900_; uint8_t v_isSharedCheck_904_; 
v_isSharedCheck_904_ = !lean_is_exclusive(v___x_897_);
if (v_isSharedCheck_904_ == 0)
{
lean_object* v_unused_905_; 
v_unused_905_ = lean_ctor_get(v___x_897_, 0);
lean_dec(v_unused_905_);
v___x_899_ = v___x_897_;
v_isShared_900_ = v_isSharedCheck_904_;
goto v_resetjp_898_;
}
else
{
lean_dec(v___x_897_);
v___x_899_ = lean_box(0);
v_isShared_900_ = v_isSharedCheck_904_;
goto v_resetjp_898_;
}
v_resetjp_898_:
{
lean_object* v___x_902_; 
if (v_isShared_900_ == 0)
{
lean_ctor_set(v___x_899_, 0, v___x_896_);
v___x_902_ = v___x_899_;
goto v_reusejp_901_;
}
else
{
lean_object* v_reuseFailAlloc_903_; 
v_reuseFailAlloc_903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_903_, 0, v___x_896_);
v___x_902_ = v_reuseFailAlloc_903_;
goto v_reusejp_901_;
}
v_reusejp_901_:
{
return v___x_902_;
}
}
}
else
{
return v___x_897_;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn___boxed(lean_object* v_us_920_, lean_object* v_00_u03b1_921_, lean_object* v_00_u03b2_922_, lean_object* v_f_923_, lean_object* v_h_924_, lean_object* v_a_925_, lean_object* v_a_926_, lean_object* v_a_927_, lean_object* v_a_928_, lean_object* v_a_929_, lean_object* v_a_930_, lean_object* v_a_931_, lean_object* v_a_932_, lean_object* v_a_933_, lean_object* v_a_934_, lean_object* v_a_935_){
_start:
{
lean_object* v_res_936_; 
v_res_936_ = l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn(v_us_920_, v_00_u03b1_921_, v_00_u03b2_922_, v_f_923_, v_h_924_, v_a_925_, v_a_926_, v_a_927_, v_a_928_, v_a_929_, v_a_930_, v_a_931_, v_a_932_, v_a_933_, v_a_934_);
lean_dec(v_a_934_);
lean_dec_ref(v_a_933_);
lean_dec(v_a_932_);
lean_dec_ref(v_a_931_);
lean_dec(v_a_930_);
lean_dec_ref(v_a_929_);
lean_dec(v_a_928_);
lean_dec_ref(v_a_927_);
lean_dec(v_a_926_);
lean_dec(v_a_925_);
return v_res_936_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__0(lean_object* v_f_937_, lean_object* v_as_938_, lean_object* v_as_x27_939_, lean_object* v_b_940_, lean_object* v_a_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_){
_start:
{
lean_object* v___x_953_; 
v___x_953_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__0___redArg(v_f_937_, v_as_x27_939_, v_b_940_, v___y_942_, v___y_943_, v___y_944_, v___y_945_, v___y_946_, v___y_947_, v___y_948_, v___y_949_, v___y_950_, v___y_951_);
return v___x_953_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__0___boxed(lean_object* v_f_954_, lean_object* v_as_955_, lean_object* v_as_x27_956_, lean_object* v_b_957_, lean_object* v_a_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_){
_start:
{
lean_object* v_res_970_; 
v_res_970_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__0(v_f_954_, v_as_955_, v_as_x27_956_, v_b_957_, v_a_958_, v___y_959_, v___y_960_, v___y_961_, v___y_962_, v___y_963_, v___y_964_, v___y_965_, v___y_966_, v___y_967_, v___y_968_);
lean_dec(v___y_968_);
lean_dec_ref(v___y_967_);
lean_dec(v___y_966_);
lean_dec_ref(v___y_965_);
lean_dec(v___y_964_);
lean_dec_ref(v___y_963_);
lean_dec(v___y_962_);
lean_dec_ref(v___y_961_);
lean_dec(v___y_960_);
lean_dec(v___y_959_);
lean_dec(v_as_x27_956_);
lean_dec(v_as_955_);
lean_dec_ref(v_f_954_);
return v_res_970_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1(lean_object* v_00_u03b2_971_, lean_object* v_x_972_, lean_object* v_x_973_){
_start:
{
lean_object* v___x_974_; 
v___x_974_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1___redArg(v_x_972_, v_x_973_);
return v___x_974_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1___boxed(lean_object* v_00_u03b2_975_, lean_object* v_x_976_, lean_object* v_x_977_){
_start:
{
lean_object* v_res_978_; 
v_res_978_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1(v_00_u03b2_975_, v_x_976_, v_x_977_);
lean_dec(v_x_977_);
lean_dec_ref(v_x_976_);
return v_res_978_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1(lean_object* v_00_u03b2_979_, lean_object* v_x_980_, size_t v_x_981_, lean_object* v_x_982_){
_start:
{
lean_object* v___x_983_; 
v___x_983_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1___redArg(v_x_980_, v_x_981_, v_x_982_);
return v___x_983_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1___boxed(lean_object* v_00_u03b2_984_, lean_object* v_x_985_, lean_object* v_x_986_, lean_object* v_x_987_){
_start:
{
size_t v_x_9963__boxed_988_; lean_object* v_res_989_; 
v_x_9963__boxed_988_ = lean_unbox_usize(v_x_986_);
lean_dec(v_x_986_);
v_res_989_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1(v_00_u03b2_984_, v_x_985_, v_x_9963__boxed_988_, v_x_987_);
lean_dec(v_x_987_);
lean_dec_ref(v_x_985_);
return v_res_989_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_990_, lean_object* v_keys_991_, lean_object* v_vals_992_, lean_object* v_heq_993_, lean_object* v_i_994_, lean_object* v_k_995_){
_start:
{
lean_object* v___x_996_; 
v___x_996_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1_spec__2___redArg(v_keys_991_, v_vals_992_, v_i_994_, v_k_995_);
return v___x_996_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03b2_997_, lean_object* v_keys_998_, lean_object* v_vals_999_, lean_object* v_heq_1000_, lean_object* v_i_1001_, lean_object* v_k_1002_){
_start:
{
lean_object* v_res_1003_; 
v_res_1003_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1_spec__2(v_00_u03b2_997_, v_keys_998_, v_vals_999_, v_heq_1000_, v_i_1001_, v_k_1002_);
lean_dec(v_k_1002_);
lean_dec_ref(v_vals_999_);
lean_dec_ref(v_keys_998_);
return v_res_1003_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj(lean_object* v_e_1009_, lean_object* v_a_1010_, lean_object* v_a_1011_, lean_object* v_a_1012_, lean_object* v_a_1013_, lean_object* v_a_1014_, lean_object* v_a_1015_, lean_object* v_a_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_){
_start:
{
lean_object* v___x_1024_; uint8_t v___x_1025_; 
lean_inc_ref(v_e_1009_);
v___x_1024_ = l_Lean_Expr_cleanupAnnotations(v_e_1009_);
v___x_1025_ = l_Lean_Expr_isApp(v___x_1024_);
if (v___x_1025_ == 0)
{
lean_dec_ref(v___x_1024_);
lean_dec_ref(v_e_1009_);
goto v___jp_1021_;
}
else
{
lean_object* v_arg_1026_; lean_object* v___x_1027_; uint8_t v___x_1028_; 
v_arg_1026_ = lean_ctor_get(v___x_1024_, 1);
lean_inc_ref(v_arg_1026_);
v___x_1027_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1024_);
v___x_1028_ = l_Lean_Expr_isApp(v___x_1027_);
if (v___x_1028_ == 0)
{
lean_dec_ref(v___x_1027_);
lean_dec_ref(v_arg_1026_);
lean_dec_ref(v_e_1009_);
goto v___jp_1021_;
}
else
{
lean_object* v_arg_1029_; lean_object* v___x_1030_; uint8_t v___x_1031_; 
v_arg_1029_ = lean_ctor_get(v___x_1027_, 1);
lean_inc_ref(v_arg_1029_);
v___x_1030_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1027_);
v___x_1031_ = l_Lean_Expr_isApp(v___x_1030_);
if (v___x_1031_ == 0)
{
lean_dec_ref(v___x_1030_);
lean_dec_ref(v_arg_1029_);
lean_dec_ref(v_arg_1026_);
lean_dec_ref(v_e_1009_);
goto v___jp_1021_;
}
else
{
lean_object* v_arg_1032_; lean_object* v___x_1033_; lean_object* v_f_1035_; lean_object* v___y_1036_; lean_object* v___y_1037_; lean_object* v___y_1038_; lean_object* v___y_1039_; lean_object* v___y_1040_; lean_object* v___y_1041_; lean_object* v___y_1042_; lean_object* v___y_1043_; lean_object* v___y_1044_; lean_object* v___y_1045_; lean_object* v___x_1059_; uint8_t v___x_1060_; 
v_arg_1032_ = lean_ctor_get(v___x_1030_, 1);
lean_inc_ref(v_arg_1032_);
v___x_1033_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1030_);
v___x_1059_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj___closed__2));
v___x_1060_ = l_Lean_Expr_isConstOf(v___x_1033_, v___x_1059_);
if (v___x_1060_ == 0)
{
lean_dec_ref(v___x_1033_);
lean_dec_ref(v_arg_1032_);
lean_dec_ref(v_arg_1029_);
lean_dec_ref(v_arg_1026_);
lean_dec_ref(v_e_1009_);
goto v___jp_1021_;
}
else
{
lean_object* v___x_1061_; 
lean_inc_ref(v_e_1009_);
v___x_1061_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_e_1009_, v_a_1010_, v_a_1014_, v_a_1016_, v_a_1017_, v_a_1018_, v_a_1019_);
if (lean_obj_tag(v___x_1061_) == 0)
{
lean_object* v_a_1062_; lean_object* v___x_1064_; uint8_t v_isShared_1065_; uint8_t v_isSharedCheck_1095_; 
v_a_1062_ = lean_ctor_get(v___x_1061_, 0);
v_isSharedCheck_1095_ = !lean_is_exclusive(v___x_1061_);
if (v_isSharedCheck_1095_ == 0)
{
v___x_1064_ = v___x_1061_;
v_isShared_1065_ = v_isSharedCheck_1095_;
goto v_resetjp_1063_;
}
else
{
lean_inc(v_a_1062_);
lean_dec(v___x_1061_);
v___x_1064_ = lean_box(0);
v_isShared_1065_ = v_isSharedCheck_1095_;
goto v_resetjp_1063_;
}
v_resetjp_1063_:
{
uint8_t v___x_1066_; 
v___x_1066_ = lean_unbox(v_a_1062_);
lean_dec(v_a_1062_);
if (v___x_1066_ == 0)
{
lean_object* v___x_1067_; lean_object* v___x_1069_; 
lean_dec_ref(v___x_1033_);
lean_dec_ref(v_arg_1032_);
lean_dec_ref(v_arg_1029_);
lean_dec_ref(v_arg_1026_);
lean_dec_ref(v_e_1009_);
v___x_1067_ = lean_box(0);
if (v_isShared_1065_ == 0)
{
lean_ctor_set(v___x_1064_, 0, v___x_1067_);
v___x_1069_ = v___x_1064_;
goto v_reusejp_1068_;
}
else
{
lean_object* v_reuseFailAlloc_1070_; 
v_reuseFailAlloc_1070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1070_, 0, v___x_1067_);
v___x_1069_ = v_reuseFailAlloc_1070_;
goto v_reusejp_1068_;
}
v_reusejp_1068_:
{
return v___x_1069_;
}
}
else
{
lean_object* v___x_1071_; uint8_t v___x_1072_; 
lean_del_object(v___x_1064_);
lean_inc_ref(v_arg_1026_);
v___x_1071_ = l_Lean_Expr_eta(v_arg_1026_);
v___x_1072_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_arg_1026_, v___x_1071_);
if (v___x_1072_ == 0)
{
lean_object* v___x_1073_; 
lean_dec_ref(v_arg_1026_);
v___x_1073_ = l_Lean_Meta_Grind_preprocessLight___redArg(v___x_1071_, v_a_1011_, v_a_1012_, v_a_1013_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_, v_a_1019_);
if (lean_obj_tag(v___x_1073_) == 0)
{
lean_object* v_a_1074_; lean_object* v___x_1075_; 
v_a_1074_ = lean_ctor_get(v___x_1073_, 0);
lean_inc(v_a_1074_);
lean_dec_ref_known(v___x_1073_, 1);
v___x_1075_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_1009_, v_a_1010_);
if (lean_obj_tag(v___x_1075_) == 0)
{
lean_object* v_a_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; 
v_a_1076_ = lean_ctor_get(v___x_1075_, 0);
lean_inc(v_a_1076_);
lean_dec_ref_known(v___x_1075_, 1);
v___x_1077_ = lean_box(0);
lean_inc(v_a_1019_);
lean_inc_ref(v_a_1018_);
lean_inc(v_a_1017_);
lean_inc_ref(v_a_1016_);
lean_inc(v_a_1015_);
lean_inc_ref(v_a_1014_);
lean_inc(v_a_1013_);
lean_inc_ref(v_a_1012_);
lean_inc(v_a_1011_);
lean_inc(v_a_1010_);
lean_inc(v_a_1074_);
v___x_1078_ = lean_grind_internalize(v_a_1074_, v_a_1076_, v___x_1077_, v_a_1010_, v_a_1011_, v_a_1012_, v_a_1013_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_, v_a_1019_);
if (lean_obj_tag(v___x_1078_) == 0)
{
lean_dec_ref_known(v___x_1078_, 1);
v_f_1035_ = v_a_1074_;
v___y_1036_ = v_a_1010_;
v___y_1037_ = v_a_1011_;
v___y_1038_ = v_a_1012_;
v___y_1039_ = v_a_1013_;
v___y_1040_ = v_a_1014_;
v___y_1041_ = v_a_1015_;
v___y_1042_ = v_a_1016_;
v___y_1043_ = v_a_1017_;
v___y_1044_ = v_a_1018_;
v___y_1045_ = v_a_1019_;
goto v___jp_1034_;
}
else
{
lean_dec(v_a_1074_);
lean_dec_ref(v___x_1033_);
lean_dec_ref(v_arg_1032_);
lean_dec_ref(v_arg_1029_);
lean_dec_ref(v_e_1009_);
return v___x_1078_;
}
}
else
{
lean_object* v_a_1079_; lean_object* v___x_1081_; uint8_t v_isShared_1082_; uint8_t v_isSharedCheck_1086_; 
lean_dec(v_a_1074_);
lean_dec_ref(v___x_1033_);
lean_dec_ref(v_arg_1032_);
lean_dec_ref(v_arg_1029_);
lean_dec_ref(v_e_1009_);
v_a_1079_ = lean_ctor_get(v___x_1075_, 0);
v_isSharedCheck_1086_ = !lean_is_exclusive(v___x_1075_);
if (v_isSharedCheck_1086_ == 0)
{
v___x_1081_ = v___x_1075_;
v_isShared_1082_ = v_isSharedCheck_1086_;
goto v_resetjp_1080_;
}
else
{
lean_inc(v_a_1079_);
lean_dec(v___x_1075_);
v___x_1081_ = lean_box(0);
v_isShared_1082_ = v_isSharedCheck_1086_;
goto v_resetjp_1080_;
}
v_resetjp_1080_:
{
lean_object* v___x_1084_; 
if (v_isShared_1082_ == 0)
{
v___x_1084_ = v___x_1081_;
goto v_reusejp_1083_;
}
else
{
lean_object* v_reuseFailAlloc_1085_; 
v_reuseFailAlloc_1085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1085_, 0, v_a_1079_);
v___x_1084_ = v_reuseFailAlloc_1085_;
goto v_reusejp_1083_;
}
v_reusejp_1083_:
{
return v___x_1084_;
}
}
}
}
else
{
lean_object* v_a_1087_; lean_object* v___x_1089_; uint8_t v_isShared_1090_; uint8_t v_isSharedCheck_1094_; 
lean_dec_ref(v___x_1033_);
lean_dec_ref(v_arg_1032_);
lean_dec_ref(v_arg_1029_);
lean_dec_ref(v_e_1009_);
v_a_1087_ = lean_ctor_get(v___x_1073_, 0);
v_isSharedCheck_1094_ = !lean_is_exclusive(v___x_1073_);
if (v_isSharedCheck_1094_ == 0)
{
v___x_1089_ = v___x_1073_;
v_isShared_1090_ = v_isSharedCheck_1094_;
goto v_resetjp_1088_;
}
else
{
lean_inc(v_a_1087_);
lean_dec(v___x_1073_);
v___x_1089_ = lean_box(0);
v_isShared_1090_ = v_isSharedCheck_1094_;
goto v_resetjp_1088_;
}
v_resetjp_1088_:
{
lean_object* v___x_1092_; 
if (v_isShared_1090_ == 0)
{
v___x_1092_ = v___x_1089_;
goto v_reusejp_1091_;
}
else
{
lean_object* v_reuseFailAlloc_1093_; 
v_reuseFailAlloc_1093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1093_, 0, v_a_1087_);
v___x_1092_ = v_reuseFailAlloc_1093_;
goto v_reusejp_1091_;
}
v_reusejp_1091_:
{
return v___x_1092_;
}
}
}
}
else
{
lean_dec_ref(v___x_1071_);
v_f_1035_ = v_arg_1026_;
v___y_1036_ = v_a_1010_;
v___y_1037_ = v_a_1011_;
v___y_1038_ = v_a_1012_;
v___y_1039_ = v_a_1013_;
v___y_1040_ = v_a_1014_;
v___y_1041_ = v_a_1015_;
v___y_1042_ = v_a_1016_;
v___y_1043_ = v_a_1017_;
v___y_1044_ = v_a_1018_;
v___y_1045_ = v_a_1019_;
goto v___jp_1034_;
}
}
}
}
else
{
lean_object* v_a_1096_; lean_object* v___x_1098_; uint8_t v_isShared_1099_; uint8_t v_isSharedCheck_1103_; 
lean_dec_ref(v___x_1033_);
lean_dec_ref(v_arg_1032_);
lean_dec_ref(v_arg_1029_);
lean_dec_ref(v_arg_1026_);
lean_dec_ref(v_e_1009_);
v_a_1096_ = lean_ctor_get(v___x_1061_, 0);
v_isSharedCheck_1103_ = !lean_is_exclusive(v___x_1061_);
if (v_isSharedCheck_1103_ == 0)
{
v___x_1098_ = v___x_1061_;
v_isShared_1099_ = v_isSharedCheck_1103_;
goto v_resetjp_1097_;
}
else
{
lean_inc(v_a_1096_);
lean_dec(v___x_1061_);
v___x_1098_ = lean_box(0);
v_isShared_1099_ = v_isSharedCheck_1103_;
goto v_resetjp_1097_;
}
v_resetjp_1097_:
{
lean_object* v___x_1101_; 
if (v_isShared_1099_ == 0)
{
v___x_1101_ = v___x_1098_;
goto v_reusejp_1100_;
}
else
{
lean_object* v_reuseFailAlloc_1102_; 
v_reuseFailAlloc_1102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1102_, 0, v_a_1096_);
v___x_1101_ = v_reuseFailAlloc_1102_;
goto v_reusejp_1100_;
}
v_reusejp_1100_:
{
return v___x_1101_;
}
}
}
}
v___jp_1034_:
{
lean_object* v___x_1046_; 
lean_inc_ref(v_e_1009_);
v___x_1046_ = l_Lean_Meta_Grind_mkEqTrueProof(v_e_1009_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_, v___y_1040_, v___y_1041_, v___y_1042_, v___y_1043_, v___y_1044_, v___y_1045_);
if (lean_obj_tag(v___x_1046_) == 0)
{
lean_object* v_a_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; 
v_a_1047_ = lean_ctor_get(v___x_1046_, 0);
lean_inc(v_a_1047_);
lean_dec_ref_known(v___x_1046_, 1);
v___x_1048_ = l_Lean_Expr_constLevels_x21(v___x_1033_);
lean_dec_ref(v___x_1033_);
v___x_1049_ = l_Lean_Meta_mkOfEqTrueCore(v_e_1009_, v_a_1047_);
v___x_1050_ = l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn(v___x_1048_, v_arg_1032_, v_arg_1029_, v_f_1035_, v___x_1049_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_, v___y_1040_, v___y_1041_, v___y_1042_, v___y_1043_, v___y_1044_, v___y_1045_);
return v___x_1050_;
}
else
{
lean_object* v_a_1051_; lean_object* v___x_1053_; uint8_t v_isShared_1054_; uint8_t v_isSharedCheck_1058_; 
lean_dec_ref(v_f_1035_);
lean_dec_ref(v___x_1033_);
lean_dec_ref(v_arg_1032_);
lean_dec_ref(v_arg_1029_);
lean_dec_ref(v_e_1009_);
v_a_1051_ = lean_ctor_get(v___x_1046_, 0);
v_isSharedCheck_1058_ = !lean_is_exclusive(v___x_1046_);
if (v_isSharedCheck_1058_ == 0)
{
v___x_1053_ = v___x_1046_;
v_isShared_1054_ = v_isSharedCheck_1058_;
goto v_resetjp_1052_;
}
else
{
lean_inc(v_a_1051_);
lean_dec(v___x_1046_);
v___x_1053_ = lean_box(0);
v_isShared_1054_ = v_isSharedCheck_1058_;
goto v_resetjp_1052_;
}
v_resetjp_1052_:
{
lean_object* v___x_1056_; 
if (v_isShared_1054_ == 0)
{
v___x_1056_ = v___x_1053_;
goto v_reusejp_1055_;
}
else
{
lean_object* v_reuseFailAlloc_1057_; 
v_reuseFailAlloc_1057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1057_, 0, v_a_1051_);
v___x_1056_ = v_reuseFailAlloc_1057_;
goto v_reusejp_1055_;
}
v_reusejp_1055_:
{
return v___x_1056_;
}
}
}
}
}
}
}
v___jp_1021_:
{
lean_object* v___x_1022_; lean_object* v___x_1023_; 
v___x_1022_ = lean_box(0);
v___x_1023_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1023_, 0, v___x_1022_);
return v___x_1023_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj___boxed(lean_object* v_e_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_, lean_object* v_a_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_){
_start:
{
lean_object* v_res_1116_; 
v_res_1116_ = l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj(v_e_1104_, v_a_1105_, v_a_1106_, v_a_1107_, v_a_1108_, v_a_1109_, v_a_1110_, v_a_1111_, v_a_1112_, v_a_1113_, v_a_1114_);
lean_dec(v_a_1114_);
lean_dec_ref(v_a_1113_);
lean_dec(v_a_1112_);
lean_dec_ref(v_a_1111_);
lean_dec(v_a_1110_);
lean_dec_ref(v_a_1109_);
lean_dec(v_a_1108_);
lean_dec_ref(v_a_1107_);
lean_dec(v_a_1106_);
lean_dec(v_a_1105_);
return v_res_1116_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj___regBuiltin___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj_declare__1_00___x40_Lean_Meta_Tactic_Grind_PropagateInj_3930705876____hygCtx___hyg_8_(){
_start:
{
lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; 
v___x_1118_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj___closed__2));
v___x_1119_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj___boxed), 12, 0);
v___x_1120_ = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(v___x_1118_, v___x_1119_);
return v___x_1120_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj___regBuiltin___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj_declare__1_00___x40_Lean_Meta_Tactic_Grind_PropagateInj_3930705876____hygCtx___hyg_8____boxed(lean_object* v_a_1121_){
_start:
{
lean_object* v_res_1122_; 
v_res_1122_ = l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj___regBuiltin___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj_declare__1_00___x40_Lean_Meta_Tactic_Grind_PropagateInj_3930705876____hygCtx___hyg_8_();
return v_res_1122_;
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
