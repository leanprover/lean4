// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Inv
// Imports: public import Lean.Meta.Tactic.Grind.Types import Init.Grind.Util import Lean.Meta.Tactic.Grind.Util
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
lean_object* l_Lean_Meta_Grind_getExprs___redArg(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_get_x21___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(lean_object*, lean_object*);
uint8_t lean_expr_equal(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_instInhabitedGoalM(lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Meta_Grind_Goal_getEqcs(lean_object*, uint8_t);
lean_object* l_Lean_Meta_Grind_mkEqHEqProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_check(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_updateLastTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Meta_Grind_Goal_getENode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_useFunCC___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isRoot___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getParents___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_ParentSet_isEmpty(lean_object*);
lean_object* l_Lean_Meta_Grind_ParentSet_elems(lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Goal_getRoot_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
uint8_t l_Lean_Meta_Grind_isMatchCond(lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
uint8_t l_Lean_Meta_Grind_ENode_isRoot(lean_object*);
lean_object* l_Lean_Meta_Grind_Goal_getRoot(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Goal_getTarget_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Goal_getNext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_hasSameType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Meta_Grind_instHashableCongrKey___private__1(lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_instBEqCongrKey___private__1(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isCongrRoot___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getCongrRoot___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
extern lean_object* l_Lean_Meta_Grind_grind_debug_proofs;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Solvers_checkInvariants(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__0___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__4___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__4___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2___redArg(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "Lean.Meta.Tactic.Grind.Inv"};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___closed__0 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___closed__0_value;
static const lean_string_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 63, .m_capacity = 63, .m_length = 62, .m_data = "_private.Lean.Meta.Tactic.Grind.Inv.0.Lean.Meta.Grind.checkEqc"};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___closed__1 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___closed__1_value;
static const lean_string_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 148, .m_capacity = 148, .m_length = 147, .m_data = "assertion violation: isSameExpr ( __do_lift._@.Lean.Meta.Tactic.Grind.Inv.684779629._hygCtx._hyg.50.0 ) root.self\n    -- Check congruence root\n    "};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___closed__2 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___closed__2_value;
static lean_once_cell_t l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___closed__3;
static const lean_string_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 75, .m_capacity = 75, .m_length = 74, .m_data = "assertion violation: isSameExpr n root.self\n    -- Go to next element\n    "};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___closed__4 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___closed__4_value;
static lean_once_cell_t l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___closed__5;
static const lean_string_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 173, .m_capacity = 173, .m_length = 172, .m_data = "assertion violation: ( __do_lift._@.Lean.Meta.Tactic.Grind.Inv.684779629._hygCtx._hyg.286.0 )\n    -- Starting at `curr`, following the `target\?` field leads to `root`.\n    "};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___closed__6 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___closed__6_value;
static lean_once_cell_t l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___closed__7;
static const lean_string_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 202, .m_capacity = 202, .m_length = 201, .m_data = "assertion violation: ( __do_lift._@.Lean.Meta.Tactic.Grind.Inv.684779629._hygCtx._hyg.219.0 )\n    -- If the equivalence class does not have HEq proofs, then the types must be definitionally equal.\n    "};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___closed__8 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___closed__8_value;
static lean_once_cell_t l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___closed__9;
static const lean_string_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 114, .m_capacity = 114, .m_length = 113, .m_data = "assertion violation: isSameExpr e ( __do_lift._@.Lean.Meta.Tactic.Grind.Inv.684779629._hygCtx._hyg.170.0 )\n      "};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___closed__10 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___closed__10_value;
static lean_once_cell_t l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___closed__11;
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "assertion violation: root.size == size\n\n"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2(lean_object*, lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkChild___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkChild___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkChild(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkChild___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___closed__0 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___closed__0_value;
static const lean_ctor_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___closed__1 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___closed__1_value;
static const lean_string_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "HEq"};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___closed__2 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___closed__2_value;
static const lean_ctor_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(67, 180, 169, 191, 74, 196, 152, 188)}};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___closed__3 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___closed__3_value;
static const lean_ctor_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___closed__4 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___closed__4_value;
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "MatchCond"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent___closed__2_value),LEAN_SCALAR_PTR_LITERAL(109, 233, 187, 249, 156, 65, 204, 232)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__0___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__2___redArg(lean_object*, uint8_t, lean_object*, size_t, size_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 67, .m_capacity = 67, .m_length = 66, .m_data = "_private.Lean.Meta.Tactic.Grind.Inv.0.Lean.Meta.Grind.checkParents"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__0_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 104, .m_capacity = 104, .m_length = 103, .m_data = "assertion violation: ( __do_lift._@.Lean.Meta.Tactic.Grind.Inv.3145645808._hygCtx._hyg.185.0 )\n        "};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__1 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__1_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__2;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 100, .m_capacity = 100, .m_length = 99, .m_data = "assertion violation: ( __do_lift._@.Lean.Meta.Tactic.Grind.Inv.3145645808._hygCtx._hyg.495.0 )\n    "};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__3 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__3_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__4;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "e: "};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__5 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__5_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__6;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = ", parent: "};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__7 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__7_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__8;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__9;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 105, .m_capacity = 105, .m_length = 104, .m_data = "assertion violation: ( __do_lift._@.Lean.Meta.Tactic.Grind.Inv.3145645808._hygCtx._hyg.538.0 ).isEmpty\n\n"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__2(lean_object*, uint8_t, lean_object*, size_t, size_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___boxed(lean_object**);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 80, .m_capacity = 80, .m_length = 79, .m_data = "_private.Lean.Meta.Tactic.Grind.Inv.0.Lean.Meta.Grind.checkPtrEqImpliesStructEq"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg___closed__0_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 40, .m_data = "assertion violation: !Expr.equal e₁ e₂\n\n"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg___closed__1_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg___closed__2;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 114, .m_capacity = 114, .m_length = 109, .m_data = "assertion violation: !isSameExpr e₁ e₂\n      -- and the two expressions must not be structurally equal\n      "};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg___closed__3 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg___closed__3_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg___closed__4;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__1___boxed(lean_object**);
static const lean_string_object l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__0___redArg___closed__0_value;
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__0___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "grind"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__2___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__2___redArg___closed__0_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "debug"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__2___redArg___closed__1 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__2___redArg___closed__1_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__2___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "proofs"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__2___redArg___closed__2 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__2___redArg___closed__2_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__2___redArg___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__2___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__2___redArg___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__2___redArg___closed__3_value_aux_0),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__2___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(92, 174, 15, 22, 76, 124, 59, 78)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__2___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__2___redArg___closed__3_value_aux_1),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__2___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(25, 245, 48, 218, 201, 55, 112, 25)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__2___redArg___closed__3 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__2___redArg___closed__3_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__2___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "checked: "};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__2___redArg___closed__4 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__2___redArg___closed__4_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__2___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__2___redArg___closed__5;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__2___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " = "};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__2___redArg___closed__6 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__2___redArg___closed__6_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__2___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__2___redArg___closed__7;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_Grind_checkInvariants_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Grind_checkInvariants_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__2_spec__5(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__2___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__2___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__1_spec__3_spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__1_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__1_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__1_spec__3___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__1_spec__3___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__1_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__1_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_checkInvariants(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_checkInvariants___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Goal_checkInvariants_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Goal_checkInvariants_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Goal_checkInvariants_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Goal_checkInvariants_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Goal_checkInvariants_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Goal_checkInvariants_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Goal_checkInvariants___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Goal_checkInvariants___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Goal_checkInvariants(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Goal_checkInvariants___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = l_Lean_Meta_Grind_instInhabitedGoalM(lean_box(0));
return v___x_1_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__0(lean_object* v_msg_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_, lean_object* v___y_7_, lean_object* v___y_8_, lean_object* v___y_9_, lean_object* v___y_10_, lean_object* v___y_11_, lean_object* v___y_12_){
_start:
{
lean_object* v___x_14_; lean_object* v___x_25157__overap_15_; lean_object* v___x_16_; 
v___x_14_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__0___closed__0, &l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__0___closed__0);
v___x_25157__overap_15_ = lean_panic_fn(v___x_14_, v_msg_2_);
v___x_16_ = lean_apply_11(v___x_25157__overap_15_, v___y_3_, v___y_4_, v___y_5_, v___y_6_, v___y_7_, v___y_8_, v___y_9_, v___y_10_, v___y_11_, v___y_12_, lean_box(0));
return v___x_16_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__0___boxed(lean_object* v_msg_17_, lean_object* v___y_18_, lean_object* v___y_19_, lean_object* v___y_20_, lean_object* v___y_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_, lean_object* v___y_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__0(v_msg_17_, v___y_18_, v___y_19_, v___y_20_, v___y_21_, v___y_22_, v___y_23_, v___y_24_, v___y_25_, v___y_26_, v___y_27_);
return v_res_29_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__4___closed__0(void){
_start:
{
lean_object* v___x_30_; 
v___x_30_ = l_Lean_Meta_Grind_instInhabitedGoalM(lean_box(0));
return v___x_30_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__4(lean_object* v_msg_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_, lean_object* v___y_36_, lean_object* v___y_37_, lean_object* v___y_38_, lean_object* v___y_39_, lean_object* v___y_40_, lean_object* v___y_41_){
_start:
{
lean_object* v___x_43_; lean_object* v___x_26937__overap_44_; lean_object* v___x_45_; 
v___x_43_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__4___closed__0, &l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__4___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__4___closed__0);
v___x_26937__overap_44_ = lean_panic_fn(v___x_43_, v_msg_31_);
v___x_45_ = lean_apply_11(v___x_26937__overap_44_, v___y_32_, v___y_33_, v___y_34_, v___y_35_, v___y_36_, v___y_37_, v___y_38_, v___y_39_, v___y_40_, v___y_41_, lean_box(0));
return v___x_45_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__4___boxed(lean_object* v_msg_46_, lean_object* v___y_47_, lean_object* v___y_48_, lean_object* v___y_49_, lean_object* v___y_50_, lean_object* v___y_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_, lean_object* v___y_56_, lean_object* v___y_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__4(v_msg_46_, v___y_47_, v___y_48_, v___y_49_, v___y_50_, v___y_51_, v___y_52_, v___y_53_, v___y_54_, v___y_55_, v___y_56_);
return v_res_58_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2_spec__4___redArg(lean_object* v___x_59_, lean_object* v_keys_60_, lean_object* v_vals_61_, lean_object* v_i_62_, lean_object* v_k_63_){
_start:
{
lean_object* v___x_64_; uint8_t v___x_65_; 
v___x_64_ = lean_array_get_size(v_keys_60_);
v___x_65_ = lean_nat_dec_lt(v_i_62_, v___x_64_);
if (v___x_65_ == 0)
{
lean_object* v___x_66_; 
lean_dec_ref(v_k_63_);
lean_dec(v_i_62_);
lean_dec_ref(v___x_59_);
v___x_66_ = lean_box(0);
return v___x_66_;
}
else
{
lean_object* v_k_x27_67_; uint8_t v___x_68_; 
v_k_x27_67_ = lean_array_fget_borrowed(v_keys_60_, v_i_62_);
lean_inc(v_k_x27_67_);
lean_inc_ref(v_k_63_);
lean_inc_ref(v___x_59_);
v___x_68_ = l_Lean_Meta_Grind_instBEqCongrKey___private__1(v___x_59_, v_k_63_, v_k_x27_67_);
if (v___x_68_ == 0)
{
lean_object* v___x_69_; lean_object* v___x_70_; 
v___x_69_ = lean_unsigned_to_nat(1u);
v___x_70_ = lean_nat_add(v_i_62_, v___x_69_);
lean_dec(v_i_62_);
v_i_62_ = v___x_70_;
goto _start;
}
else
{
lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; 
lean_dec_ref(v_k_63_);
lean_dec_ref(v___x_59_);
v___x_72_ = lean_array_fget_borrowed(v_vals_61_, v_i_62_);
lean_dec(v_i_62_);
lean_inc(v___x_72_);
lean_inc(v_k_x27_67_);
v___x_73_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_73_, 0, v_k_x27_67_);
lean_ctor_set(v___x_73_, 1, v___x_72_);
v___x_74_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_74_, 0, v___x_73_);
return v___x_74_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2_spec__4___redArg___boxed(lean_object* v___x_75_, lean_object* v_keys_76_, lean_object* v_vals_77_, lean_object* v_i_78_, lean_object* v_k_79_){
_start:
{
lean_object* v_res_80_; 
v_res_80_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2_spec__4___redArg(v___x_75_, v_keys_76_, v_vals_77_, v_i_78_, v_k_79_);
lean_dec_ref(v_vals_77_);
lean_dec_ref(v_keys_76_);
return v_res_80_;
}
}
static size_t _init_l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2___redArg___closed__0(void){
_start:
{
size_t v___x_81_; size_t v___x_82_; size_t v___x_83_; 
v___x_81_ = ((size_t)5ULL);
v___x_82_ = ((size_t)1ULL);
v___x_83_ = lean_usize_shift_left(v___x_82_, v___x_81_);
return v___x_83_;
}
}
static size_t _init_l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2___redArg___closed__1(void){
_start:
{
size_t v___x_84_; size_t v___x_85_; size_t v___x_86_; 
v___x_84_ = ((size_t)1ULL);
v___x_85_ = lean_usize_once(&l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2___redArg___closed__0);
v___x_86_ = lean_usize_sub(v___x_85_, v___x_84_);
return v___x_86_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2___redArg(lean_object* v___x_87_, lean_object* v_x_88_, size_t v_x_89_, lean_object* v_x_90_){
_start:
{
if (lean_obj_tag(v_x_88_) == 0)
{
lean_object* v_es_91_; lean_object* v___x_93_; uint8_t v_isShared_94_; uint8_t v_isSharedCheck_119_; 
v_es_91_ = lean_ctor_get(v_x_88_, 0);
v_isSharedCheck_119_ = !lean_is_exclusive(v_x_88_);
if (v_isSharedCheck_119_ == 0)
{
v___x_93_ = v_x_88_;
v_isShared_94_ = v_isSharedCheck_119_;
goto v_resetjp_92_;
}
else
{
lean_inc(v_es_91_);
lean_dec(v_x_88_);
v___x_93_ = lean_box(0);
v_isShared_94_ = v_isSharedCheck_119_;
goto v_resetjp_92_;
}
v_resetjp_92_:
{
lean_object* v___x_95_; size_t v___x_96_; size_t v___x_97_; size_t v___x_98_; lean_object* v_j_99_; lean_object* v___x_100_; 
v___x_95_ = lean_box(2);
v___x_96_ = ((size_t)5ULL);
v___x_97_ = lean_usize_once(&l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2___redArg___closed__1, &l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2___redArg___closed__1);
v___x_98_ = lean_usize_land(v_x_89_, v___x_97_);
v_j_99_ = lean_usize_to_nat(v___x_98_);
v___x_100_ = lean_array_get(v___x_95_, v_es_91_, v_j_99_);
lean_dec(v_j_99_);
lean_dec_ref(v_es_91_);
switch(lean_obj_tag(v___x_100_))
{
case 0:
{
lean_object* v_key_101_; lean_object* v_val_102_; lean_object* v___x_104_; uint8_t v_isShared_105_; uint8_t v_isSharedCheck_114_; 
v_key_101_ = lean_ctor_get(v___x_100_, 0);
v_val_102_ = lean_ctor_get(v___x_100_, 1);
v_isSharedCheck_114_ = !lean_is_exclusive(v___x_100_);
if (v_isSharedCheck_114_ == 0)
{
v___x_104_ = v___x_100_;
v_isShared_105_ = v_isSharedCheck_114_;
goto v_resetjp_103_;
}
else
{
lean_inc(v_val_102_);
lean_inc(v_key_101_);
lean_dec(v___x_100_);
v___x_104_ = lean_box(0);
v_isShared_105_ = v_isSharedCheck_114_;
goto v_resetjp_103_;
}
v_resetjp_103_:
{
uint8_t v___x_106_; 
lean_inc(v_key_101_);
v___x_106_ = l_Lean_Meta_Grind_instBEqCongrKey___private__1(v___x_87_, v_x_90_, v_key_101_);
if (v___x_106_ == 0)
{
lean_object* v___x_107_; 
lean_del_object(v___x_104_);
lean_dec(v_val_102_);
lean_dec(v_key_101_);
lean_del_object(v___x_93_);
v___x_107_ = lean_box(0);
return v___x_107_;
}
else
{
lean_object* v___x_109_; 
if (v_isShared_105_ == 0)
{
v___x_109_ = v___x_104_;
goto v_reusejp_108_;
}
else
{
lean_object* v_reuseFailAlloc_113_; 
v_reuseFailAlloc_113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_113_, 0, v_key_101_);
lean_ctor_set(v_reuseFailAlloc_113_, 1, v_val_102_);
v___x_109_ = v_reuseFailAlloc_113_;
goto v_reusejp_108_;
}
v_reusejp_108_:
{
lean_object* v___x_111_; 
if (v_isShared_94_ == 0)
{
lean_ctor_set_tag(v___x_93_, 1);
lean_ctor_set(v___x_93_, 0, v___x_109_);
v___x_111_ = v___x_93_;
goto v_reusejp_110_;
}
else
{
lean_object* v_reuseFailAlloc_112_; 
v_reuseFailAlloc_112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_112_, 0, v___x_109_);
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
case 1:
{
lean_object* v_node_115_; size_t v___x_116_; 
lean_del_object(v___x_93_);
v_node_115_ = lean_ctor_get(v___x_100_, 0);
lean_inc(v_node_115_);
lean_dec_ref(v___x_100_);
v___x_116_ = lean_usize_shift_right(v_x_89_, v___x_96_);
v_x_88_ = v_node_115_;
v_x_89_ = v___x_116_;
goto _start;
}
default: 
{
lean_object* v___x_118_; 
lean_del_object(v___x_93_);
lean_dec_ref(v_x_90_);
lean_dec_ref(v___x_87_);
v___x_118_ = lean_box(0);
return v___x_118_;
}
}
}
}
else
{
lean_object* v_ks_120_; lean_object* v_vs_121_; lean_object* v___x_122_; lean_object* v___x_123_; 
v_ks_120_ = lean_ctor_get(v_x_88_, 0);
lean_inc_ref(v_ks_120_);
v_vs_121_ = lean_ctor_get(v_x_88_, 1);
lean_inc_ref(v_vs_121_);
lean_dec_ref(v_x_88_);
v___x_122_ = lean_unsigned_to_nat(0u);
v___x_123_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2_spec__4___redArg(v___x_87_, v_ks_120_, v_vs_121_, v___x_122_, v_x_90_);
lean_dec_ref(v_vs_121_);
lean_dec_ref(v_ks_120_);
return v___x_123_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2___redArg___boxed(lean_object* v___x_124_, lean_object* v_x_125_, lean_object* v_x_126_, lean_object* v_x_127_){
_start:
{
size_t v_x_27374__boxed_128_; lean_object* v_res_129_; 
v_x_27374__boxed_128_ = lean_unbox_usize(v_x_126_);
lean_dec(v_x_126_);
v_res_129_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2___redArg(v___x_124_, v_x_125_, v_x_27374__boxed_128_, v_x_127_);
return v_res_129_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2___redArg(lean_object* v___x_130_, lean_object* v_x_131_, lean_object* v_x_132_){
_start:
{
uint64_t v___x_133_; size_t v___x_134_; lean_object* v___x_135_; 
lean_inc_ref(v_x_132_);
lean_inc_ref(v___x_130_);
v___x_133_ = l_Lean_Meta_Grind_instHashableCongrKey___private__1(v___x_130_, v_x_132_);
v___x_134_ = lean_uint64_to_usize(v___x_133_);
v___x_135_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2___redArg(v___x_130_, v_x_131_, v___x_134_, v_x_132_);
return v___x_135_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__1___redArg(lean_object* v_b_136_, lean_object* v___y_137_){
_start:
{
lean_object* v___x_139_; lean_object* v___x_140_; 
v___x_139_ = lean_st_ref_get(v___y_137_);
v___x_140_ = l_Lean_Meta_Grind_Goal_getTarget_x3f(v___x_139_, v_b_136_);
if (lean_obj_tag(v___x_140_) == 1)
{
lean_object* v_val_141_; 
lean_dec_ref(v_b_136_);
v_val_141_ = lean_ctor_get(v___x_140_, 0);
lean_inc(v_val_141_);
lean_dec_ref(v___x_140_);
v_b_136_ = v_val_141_;
goto _start;
}
else
{
lean_object* v___x_143_; 
lean_dec(v___x_140_);
v___x_143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_143_, 0, v_b_136_);
return v___x_143_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__1___redArg___boxed(lean_object* v_b_144_, lean_object* v___y_145_, lean_object* v___y_146_){
_start:
{
lean_object* v_res_147_; 
v_res_147_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__1___redArg(v_b_144_, v___y_145_);
lean_dec(v___y_145_);
return v_res_147_;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___closed__3(void){
_start:
{
lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; 
v___x_151_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___closed__2));
v___x_152_ = lean_unsigned_to_nat(4u);
v___x_153_ = lean_unsigned_to_nat(22u);
v___x_154_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___closed__1));
v___x_155_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___closed__0));
v___x_156_ = l_mkPanicMessageWithDecl(v___x_155_, v___x_154_, v___x_153_, v___x_152_, v___x_151_);
return v___x_156_;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___closed__5(void){
_start:
{
lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; 
v___x_158_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___closed__4));
v___x_159_ = lean_unsigned_to_nat(4u);
v___x_160_ = lean_unsigned_to_nat(40u);
v___x_161_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___closed__1));
v___x_162_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___closed__0));
v___x_163_ = l_mkPanicMessageWithDecl(v___x_162_, v___x_161_, v___x_160_, v___x_159_, v___x_158_);
return v___x_163_;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___closed__7(void){
_start:
{
lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; 
v___x_165_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___closed__6));
v___x_166_ = lean_unsigned_to_nat(6u);
v___x_167_ = lean_unsigned_to_nat(32u);
v___x_168_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___closed__1));
v___x_169_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___closed__0));
v___x_170_ = l_mkPanicMessageWithDecl(v___x_169_, v___x_168_, v___x_167_, v___x_166_, v___x_165_);
return v___x_170_;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___closed__9(void){
_start:
{
lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; 
v___x_172_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___closed__8));
v___x_173_ = lean_unsigned_to_nat(8u);
v___x_174_ = lean_unsigned_to_nat(29u);
v___x_175_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___closed__1));
v___x_176_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___closed__0));
v___x_177_ = l_mkPanicMessageWithDecl(v___x_176_, v___x_175_, v___x_174_, v___x_173_, v___x_172_);
return v___x_177_;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___closed__11(void){
_start:
{
lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; 
v___x_179_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___closed__10));
v___x_180_ = lean_unsigned_to_nat(10u);
v___x_181_ = lean_unsigned_to_nat(27u);
v___x_182_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___closed__1));
v___x_183_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___closed__0));
v___x_184_ = l_mkPanicMessageWithDecl(v___x_183_, v___x_182_, v___x_181_, v___x_180_, v___x_179_);
return v___x_184_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3(lean_object* v_curr_185_, lean_object* v_root_186_, lean_object* v_b_187_, lean_object* v___y_188_, lean_object* v___y_189_, lean_object* v___y_190_, lean_object* v___y_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_){
_start:
{
lean_object* v___y_200_; lean_object* v___x_220_; lean_object* v_fst_221_; lean_object* v_snd_222_; lean_object* v___x_224_; uint8_t v_isShared_225_; uint8_t v_isSharedCheck_363_; 
v___x_220_ = lean_st_ref_get(v___y_188_);
v_fst_221_ = lean_ctor_get(v_b_187_, 0);
v_snd_222_ = lean_ctor_get(v_b_187_, 1);
v_isSharedCheck_363_ = !lean_is_exclusive(v_b_187_);
if (v_isSharedCheck_363_ == 0)
{
v___x_224_ = v_b_187_;
v_isShared_225_ = v_isSharedCheck_363_;
goto v_resetjp_223_;
}
else
{
lean_inc(v_snd_222_);
lean_inc(v_fst_221_);
lean_dec(v_b_187_);
v___x_224_ = lean_box(0);
v_isShared_225_ = v_isSharedCheck_363_;
goto v_resetjp_223_;
}
v___jp_199_:
{
if (lean_obj_tag(v___y_200_) == 0)
{
lean_object* v_a_201_; lean_object* v___x_203_; uint8_t v_isShared_204_; uint8_t v_isSharedCheck_211_; 
v_a_201_ = lean_ctor_get(v___y_200_, 0);
v_isSharedCheck_211_ = !lean_is_exclusive(v___y_200_);
if (v_isSharedCheck_211_ == 0)
{
v___x_203_ = v___y_200_;
v_isShared_204_ = v_isSharedCheck_211_;
goto v_resetjp_202_;
}
else
{
lean_inc(v_a_201_);
lean_dec(v___y_200_);
v___x_203_ = lean_box(0);
v_isShared_204_ = v_isSharedCheck_211_;
goto v_resetjp_202_;
}
v_resetjp_202_:
{
if (lean_obj_tag(v_a_201_) == 0)
{
lean_object* v_a_205_; lean_object* v___x_207_; 
lean_dec(v___y_197_);
lean_dec_ref(v___y_196_);
lean_dec(v___y_195_);
lean_dec_ref(v___y_194_);
lean_dec(v___y_193_);
lean_dec_ref(v___y_192_);
lean_dec(v___y_191_);
lean_dec_ref(v___y_190_);
lean_dec(v___y_189_);
lean_dec(v___y_188_);
lean_dec_ref(v_curr_185_);
v_a_205_ = lean_ctor_get(v_a_201_, 0);
lean_inc(v_a_205_);
lean_dec_ref(v_a_201_);
if (v_isShared_204_ == 0)
{
lean_ctor_set(v___x_203_, 0, v_a_205_);
v___x_207_ = v___x_203_;
goto v_reusejp_206_;
}
else
{
lean_object* v_reuseFailAlloc_208_; 
v_reuseFailAlloc_208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_208_, 0, v_a_205_);
v___x_207_ = v_reuseFailAlloc_208_;
goto v_reusejp_206_;
}
v_reusejp_206_:
{
return v___x_207_;
}
}
else
{
lean_object* v_a_209_; 
lean_del_object(v___x_203_);
v_a_209_ = lean_ctor_get(v_a_201_, 0);
lean_inc(v_a_209_);
lean_dec_ref(v_a_201_);
v_b_187_ = v_a_209_;
goto _start;
}
}
}
else
{
lean_object* v_a_212_; lean_object* v___x_214_; uint8_t v_isShared_215_; uint8_t v_isSharedCheck_219_; 
lean_dec(v___y_197_);
lean_dec_ref(v___y_196_);
lean_dec(v___y_195_);
lean_dec_ref(v___y_194_);
lean_dec(v___y_193_);
lean_dec_ref(v___y_192_);
lean_dec(v___y_191_);
lean_dec_ref(v___y_190_);
lean_dec(v___y_189_);
lean_dec(v___y_188_);
lean_dec_ref(v_curr_185_);
v_a_212_ = lean_ctor_get(v___y_200_, 0);
v_isSharedCheck_219_ = !lean_is_exclusive(v___y_200_);
if (v_isSharedCheck_219_ == 0)
{
v___x_214_ = v___y_200_;
v_isShared_215_ = v_isSharedCheck_219_;
goto v_resetjp_213_;
}
else
{
lean_inc(v_a_212_);
lean_dec(v___y_200_);
v___x_214_ = lean_box(0);
v_isShared_215_ = v_isSharedCheck_219_;
goto v_resetjp_213_;
}
v_resetjp_213_:
{
lean_object* v___x_217_; 
if (v_isShared_215_ == 0)
{
v___x_217_ = v___x_214_;
goto v_reusejp_216_;
}
else
{
lean_object* v_reuseFailAlloc_218_; 
v_reuseFailAlloc_218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_218_, 0, v_a_212_);
v___x_217_ = v_reuseFailAlloc_218_;
goto v_reusejp_216_;
}
v_reusejp_216_:
{
return v___x_217_;
}
}
}
}
v_resetjp_223_:
{
lean_object* v___x_226_; 
lean_inc(v_snd_222_);
v___x_226_ = l_Lean_Meta_Grind_Goal_getRoot(v___x_220_, v_snd_222_, v___y_194_, v___y_195_, v___y_196_, v___y_197_);
if (lean_obj_tag(v___x_226_) == 0)
{
lean_object* v_a_227_; uint8_t v___x_228_; 
v_a_227_ = lean_ctor_get(v___x_226_, 0);
lean_inc(v_a_227_);
lean_dec_ref(v___x_226_);
v___x_228_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_a_227_, v_curr_185_);
lean_dec(v_a_227_);
if (v___x_228_ == 0)
{
lean_object* v___x_229_; lean_object* v___x_230_; 
lean_del_object(v___x_224_);
lean_dec(v_snd_222_);
lean_dec(v_fst_221_);
v___x_229_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___closed__3, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___closed__3_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___closed__3);
lean_inc(v___y_197_);
lean_inc_ref(v___y_196_);
lean_inc(v___y_195_);
lean_inc_ref(v___y_194_);
lean_inc(v___y_193_);
lean_inc_ref(v___y_192_);
lean_inc(v___y_191_);
lean_inc_ref(v___y_190_);
lean_inc(v___y_189_);
lean_inc(v___y_188_);
v___x_230_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__0(v___x_229_, v___y_188_, v___y_189_, v___y_190_, v___y_191_, v___y_192_, v___y_193_, v___y_194_, v___y_195_, v___y_196_, v___y_197_);
v___y_200_ = v___x_230_;
goto v___jp_199_;
}
else
{
lean_object* v___x_231_; lean_object* v_size_232_; lean_object* v___y_234_; lean_object* v___y_235_; lean_object* v___y_236_; lean_object* v___y_237_; lean_object* v___y_238_; lean_object* v___y_239_; lean_object* v___y_240_; lean_object* v___y_241_; lean_object* v___y_242_; lean_object* v___y_243_; lean_object* v___y_284_; lean_object* v___y_285_; lean_object* v___y_286_; lean_object* v___y_287_; lean_object* v___y_288_; lean_object* v___y_289_; lean_object* v___y_290_; lean_object* v___y_291_; lean_object* v___y_292_; lean_object* v___y_293_; uint8_t v___x_308_; 
v___x_231_ = lean_unsigned_to_nat(1u);
v_size_232_ = lean_nat_add(v_fst_221_, v___x_231_);
lean_dec(v_fst_221_);
v___x_308_ = l_Lean_Expr_isApp(v_snd_222_);
if (v___x_308_ == 0)
{
lean_inc(v___y_197_);
lean_inc_ref(v___y_196_);
lean_inc(v___y_195_);
lean_inc_ref(v___y_194_);
lean_inc(v___y_193_);
lean_inc_ref(v___y_192_);
lean_inc(v___y_191_);
lean_inc_ref(v___y_190_);
lean_inc(v___y_189_);
lean_inc(v___y_188_);
v___y_284_ = v___y_188_;
v___y_285_ = v___y_189_;
v___y_286_ = v___y_190_;
v___y_287_ = v___y_191_;
v___y_288_ = v___y_192_;
v___y_289_ = v___y_193_;
v___y_290_ = v___y_194_;
v___y_291_ = v___y_195_;
v___y_292_ = v___y_196_;
v___y_293_ = v___y_197_;
goto v___jp_283_;
}
else
{
lean_object* v___x_309_; lean_object* v_toGoalState_310_; lean_object* v_enodeMap_311_; lean_object* v_congrTable_312_; lean_object* v___x_313_; 
v___x_309_ = lean_st_ref_get(v___y_188_);
v_toGoalState_310_ = lean_ctor_get(v___x_309_, 0);
lean_inc_ref(v_toGoalState_310_);
lean_dec(v___x_309_);
v_enodeMap_311_ = lean_ctor_get(v_toGoalState_310_, 2);
lean_inc_ref(v_enodeMap_311_);
v_congrTable_312_ = lean_ctor_get(v_toGoalState_310_, 5);
lean_inc_ref(v_congrTable_312_);
lean_dec_ref(v_toGoalState_310_);
lean_inc(v_snd_222_);
v___x_313_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2___redArg(v_enodeMap_311_, v_congrTable_312_, v_snd_222_);
if (lean_obj_tag(v___x_313_) == 0)
{
lean_object* v___x_314_; 
lean_inc(v_snd_222_);
v___x_314_ = l_Lean_Meta_Grind_isCongrRoot___redArg(v_snd_222_, v___y_188_, v___y_194_, v___y_195_, v___y_196_, v___y_197_);
if (lean_obj_tag(v___x_314_) == 0)
{
lean_object* v_a_315_; uint8_t v___x_316_; 
v_a_315_ = lean_ctor_get(v___x_314_, 0);
lean_inc(v_a_315_);
lean_dec_ref(v___x_314_);
v___x_316_ = lean_unbox(v_a_315_);
lean_dec(v_a_315_);
if (v___x_316_ == 0)
{
lean_object* v___x_317_; lean_object* v___x_318_; 
lean_dec(v_size_232_);
lean_del_object(v___x_224_);
lean_dec(v_snd_222_);
v___x_317_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___closed__9, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___closed__9_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___closed__9);
lean_inc(v___y_197_);
lean_inc_ref(v___y_196_);
lean_inc(v___y_195_);
lean_inc_ref(v___y_194_);
lean_inc(v___y_193_);
lean_inc_ref(v___y_192_);
lean_inc(v___y_191_);
lean_inc_ref(v___y_190_);
lean_inc(v___y_189_);
lean_inc(v___y_188_);
v___x_318_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__0(v___x_317_, v___y_188_, v___y_189_, v___y_190_, v___y_191_, v___y_192_, v___y_193_, v___y_194_, v___y_195_, v___y_196_, v___y_197_);
v___y_200_ = v___x_318_;
goto v___jp_199_;
}
else
{
lean_inc(v___y_197_);
lean_inc_ref(v___y_196_);
lean_inc(v___y_195_);
lean_inc_ref(v___y_194_);
lean_inc(v___y_193_);
lean_inc_ref(v___y_192_);
lean_inc(v___y_191_);
lean_inc_ref(v___y_190_);
lean_inc(v___y_189_);
lean_inc(v___y_188_);
v___y_284_ = v___y_188_;
v___y_285_ = v___y_189_;
v___y_286_ = v___y_190_;
v___y_287_ = v___y_191_;
v___y_288_ = v___y_192_;
v___y_289_ = v___y_193_;
v___y_290_ = v___y_194_;
v___y_291_ = v___y_195_;
v___y_292_ = v___y_196_;
v___y_293_ = v___y_197_;
goto v___jp_283_;
}
}
else
{
lean_object* v_a_319_; lean_object* v___x_321_; uint8_t v_isShared_322_; uint8_t v_isSharedCheck_326_; 
lean_dec(v_size_232_);
lean_del_object(v___x_224_);
lean_dec(v_snd_222_);
lean_dec(v___y_197_);
lean_dec_ref(v___y_196_);
lean_dec(v___y_195_);
lean_dec_ref(v___y_194_);
lean_dec(v___y_193_);
lean_dec_ref(v___y_192_);
lean_dec(v___y_191_);
lean_dec_ref(v___y_190_);
lean_dec(v___y_189_);
lean_dec(v___y_188_);
lean_dec_ref(v_curr_185_);
v_a_319_ = lean_ctor_get(v___x_314_, 0);
v_isSharedCheck_326_ = !lean_is_exclusive(v___x_314_);
if (v_isSharedCheck_326_ == 0)
{
v___x_321_ = v___x_314_;
v_isShared_322_ = v_isSharedCheck_326_;
goto v_resetjp_320_;
}
else
{
lean_inc(v_a_319_);
lean_dec(v___x_314_);
v___x_321_ = lean_box(0);
v_isShared_322_ = v_isSharedCheck_326_;
goto v_resetjp_320_;
}
v_resetjp_320_:
{
lean_object* v___x_324_; 
if (v_isShared_322_ == 0)
{
v___x_324_ = v___x_321_;
goto v_reusejp_323_;
}
else
{
lean_object* v_reuseFailAlloc_325_; 
v_reuseFailAlloc_325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_325_, 0, v_a_319_);
v___x_324_ = v_reuseFailAlloc_325_;
goto v_reusejp_323_;
}
v_reusejp_323_:
{
return v___x_324_;
}
}
}
}
else
{
lean_object* v_val_327_; lean_object* v_fst_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; 
v_val_327_ = lean_ctor_get(v___x_313_, 0);
lean_inc(v_val_327_);
lean_dec_ref(v___x_313_);
v_fst_328_ = lean_ctor_get(v_val_327_, 0);
lean_inc(v_fst_328_);
lean_dec(v_val_327_);
v___x_329_ = l_Lean_Expr_getAppFn(v_fst_328_);
v___x_330_ = l_Lean_Expr_getAppFn(v_snd_222_);
lean_inc(v___y_197_);
lean_inc_ref(v___y_196_);
lean_inc(v___y_195_);
lean_inc_ref(v___y_194_);
v___x_331_ = l_Lean_Meta_Grind_hasSameType(v___x_329_, v___x_330_, v___y_194_, v___y_195_, v___y_196_, v___y_197_);
if (lean_obj_tag(v___x_331_) == 0)
{
lean_object* v_a_332_; uint8_t v___x_333_; 
v_a_332_ = lean_ctor_get(v___x_331_, 0);
lean_inc(v_a_332_);
lean_dec_ref(v___x_331_);
v___x_333_ = lean_unbox(v_a_332_);
lean_dec(v_a_332_);
if (v___x_333_ == 0)
{
lean_dec(v_fst_328_);
lean_inc(v___y_197_);
lean_inc_ref(v___y_196_);
lean_inc(v___y_195_);
lean_inc_ref(v___y_194_);
lean_inc(v___y_193_);
lean_inc_ref(v___y_192_);
lean_inc(v___y_191_);
lean_inc_ref(v___y_190_);
lean_inc(v___y_189_);
lean_inc(v___y_188_);
v___y_284_ = v___y_188_;
v___y_285_ = v___y_189_;
v___y_286_ = v___y_190_;
v___y_287_ = v___y_191_;
v___y_288_ = v___y_192_;
v___y_289_ = v___y_193_;
v___y_290_ = v___y_194_;
v___y_291_ = v___y_195_;
v___y_292_ = v___y_196_;
v___y_293_ = v___y_197_;
goto v___jp_283_;
}
else
{
lean_object* v___x_334_; 
lean_inc(v_snd_222_);
v___x_334_ = l_Lean_Meta_Grind_getCongrRoot___redArg(v_snd_222_, v___y_188_, v___y_194_, v___y_195_, v___y_196_, v___y_197_);
if (lean_obj_tag(v___x_334_) == 0)
{
lean_object* v_a_335_; uint8_t v___x_336_; 
v_a_335_ = lean_ctor_get(v___x_334_, 0);
lean_inc(v_a_335_);
lean_dec_ref(v___x_334_);
v___x_336_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_fst_328_, v_a_335_);
lean_dec(v_a_335_);
lean_dec(v_fst_328_);
if (v___x_336_ == 0)
{
lean_object* v___x_337_; lean_object* v___x_338_; 
lean_dec(v_size_232_);
lean_del_object(v___x_224_);
lean_dec(v_snd_222_);
v___x_337_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___closed__11, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___closed__11_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___closed__11);
lean_inc(v___y_197_);
lean_inc_ref(v___y_196_);
lean_inc(v___y_195_);
lean_inc_ref(v___y_194_);
lean_inc(v___y_193_);
lean_inc_ref(v___y_192_);
lean_inc(v___y_191_);
lean_inc_ref(v___y_190_);
lean_inc(v___y_189_);
lean_inc(v___y_188_);
v___x_338_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__0(v___x_337_, v___y_188_, v___y_189_, v___y_190_, v___y_191_, v___y_192_, v___y_193_, v___y_194_, v___y_195_, v___y_196_, v___y_197_);
v___y_200_ = v___x_338_;
goto v___jp_199_;
}
else
{
lean_inc(v___y_197_);
lean_inc_ref(v___y_196_);
lean_inc(v___y_195_);
lean_inc_ref(v___y_194_);
lean_inc(v___y_193_);
lean_inc_ref(v___y_192_);
lean_inc(v___y_191_);
lean_inc_ref(v___y_190_);
lean_inc(v___y_189_);
lean_inc(v___y_188_);
v___y_284_ = v___y_188_;
v___y_285_ = v___y_189_;
v___y_286_ = v___y_190_;
v___y_287_ = v___y_191_;
v___y_288_ = v___y_192_;
v___y_289_ = v___y_193_;
v___y_290_ = v___y_194_;
v___y_291_ = v___y_195_;
v___y_292_ = v___y_196_;
v___y_293_ = v___y_197_;
goto v___jp_283_;
}
}
else
{
lean_object* v_a_339_; lean_object* v___x_341_; uint8_t v_isShared_342_; uint8_t v_isSharedCheck_346_; 
lean_dec(v_fst_328_);
lean_dec(v_size_232_);
lean_del_object(v___x_224_);
lean_dec(v_snd_222_);
lean_dec(v___y_197_);
lean_dec_ref(v___y_196_);
lean_dec(v___y_195_);
lean_dec_ref(v___y_194_);
lean_dec(v___y_193_);
lean_dec_ref(v___y_192_);
lean_dec(v___y_191_);
lean_dec_ref(v___y_190_);
lean_dec(v___y_189_);
lean_dec(v___y_188_);
lean_dec_ref(v_curr_185_);
v_a_339_ = lean_ctor_get(v___x_334_, 0);
v_isSharedCheck_346_ = !lean_is_exclusive(v___x_334_);
if (v_isSharedCheck_346_ == 0)
{
v___x_341_ = v___x_334_;
v_isShared_342_ = v_isSharedCheck_346_;
goto v_resetjp_340_;
}
else
{
lean_inc(v_a_339_);
lean_dec(v___x_334_);
v___x_341_ = lean_box(0);
v_isShared_342_ = v_isSharedCheck_346_;
goto v_resetjp_340_;
}
v_resetjp_340_:
{
lean_object* v___x_344_; 
if (v_isShared_342_ == 0)
{
v___x_344_ = v___x_341_;
goto v_reusejp_343_;
}
else
{
lean_object* v_reuseFailAlloc_345_; 
v_reuseFailAlloc_345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_345_, 0, v_a_339_);
v___x_344_ = v_reuseFailAlloc_345_;
goto v_reusejp_343_;
}
v_reusejp_343_:
{
return v___x_344_;
}
}
}
}
}
else
{
lean_object* v_a_347_; lean_object* v___x_349_; uint8_t v_isShared_350_; uint8_t v_isSharedCheck_354_; 
lean_dec(v_fst_328_);
lean_dec(v_size_232_);
lean_del_object(v___x_224_);
lean_dec(v_snd_222_);
lean_dec(v___y_197_);
lean_dec_ref(v___y_196_);
lean_dec(v___y_195_);
lean_dec_ref(v___y_194_);
lean_dec(v___y_193_);
lean_dec_ref(v___y_192_);
lean_dec(v___y_191_);
lean_dec_ref(v___y_190_);
lean_dec(v___y_189_);
lean_dec(v___y_188_);
lean_dec_ref(v_curr_185_);
v_a_347_ = lean_ctor_get(v___x_331_, 0);
v_isSharedCheck_354_ = !lean_is_exclusive(v___x_331_);
if (v_isSharedCheck_354_ == 0)
{
v___x_349_ = v___x_331_;
v_isShared_350_ = v_isSharedCheck_354_;
goto v_resetjp_348_;
}
else
{
lean_inc(v_a_347_);
lean_dec(v___x_331_);
v___x_349_ = lean_box(0);
v_isShared_350_ = v_isSharedCheck_354_;
goto v_resetjp_348_;
}
v_resetjp_348_:
{
lean_object* v___x_352_; 
if (v_isShared_350_ == 0)
{
v___x_352_ = v___x_349_;
goto v_reusejp_351_;
}
else
{
lean_object* v_reuseFailAlloc_353_; 
v_reuseFailAlloc_353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_353_, 0, v_a_347_);
v___x_352_ = v_reuseFailAlloc_353_;
goto v_reusejp_351_;
}
v_reusejp_351_:
{
return v___x_352_;
}
}
}
}
}
v___jp_233_:
{
lean_object* v___x_244_; 
lean_inc(v_snd_222_);
v___x_244_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__1___redArg(v_snd_222_, v___y_234_);
if (lean_obj_tag(v___x_244_) == 0)
{
lean_object* v_a_245_; uint8_t v___x_246_; 
v_a_245_ = lean_ctor_get(v___x_244_, 0);
lean_inc(v_a_245_);
lean_dec_ref(v___x_244_);
v___x_246_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_a_245_, v_curr_185_);
lean_dec(v_a_245_);
if (v___x_246_ == 0)
{
lean_object* v___x_247_; lean_object* v___x_248_; 
lean_dec(v_size_232_);
lean_del_object(v___x_224_);
lean_dec(v_snd_222_);
v___x_247_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___closed__5, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___closed__5_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___closed__5);
v___x_248_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__0(v___x_247_, v___y_234_, v___y_235_, v___y_236_, v___y_237_, v___y_238_, v___y_239_, v___y_240_, v___y_241_, v___y_242_, v___y_243_);
v___y_200_ = v___x_248_;
goto v___jp_199_;
}
else
{
lean_object* v___x_249_; lean_object* v___x_250_; 
lean_dec(v___y_239_);
lean_dec_ref(v___y_238_);
lean_dec(v___y_237_);
lean_dec_ref(v___y_236_);
lean_dec(v___y_235_);
v___x_249_ = lean_st_ref_get(v___y_234_);
lean_dec(v___y_234_);
v___x_250_ = l_Lean_Meta_Grind_Goal_getNext(v___x_249_, v_snd_222_, v___y_240_, v___y_241_, v___y_242_, v___y_243_);
lean_dec(v___y_243_);
lean_dec_ref(v___y_242_);
lean_dec(v___y_241_);
lean_dec_ref(v___y_240_);
if (lean_obj_tag(v___x_250_) == 0)
{
lean_object* v_a_251_; lean_object* v___x_253_; uint8_t v_isShared_254_; uint8_t v_isSharedCheck_266_; 
v_a_251_ = lean_ctor_get(v___x_250_, 0);
v_isSharedCheck_266_ = !lean_is_exclusive(v___x_250_);
if (v_isSharedCheck_266_ == 0)
{
v___x_253_ = v___x_250_;
v_isShared_254_ = v_isSharedCheck_266_;
goto v_resetjp_252_;
}
else
{
lean_inc(v_a_251_);
lean_dec(v___x_250_);
v___x_253_ = lean_box(0);
v_isShared_254_ = v_isSharedCheck_266_;
goto v_resetjp_252_;
}
v_resetjp_252_:
{
uint8_t v___x_255_; 
v___x_255_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_curr_185_, v_a_251_);
if (v___x_255_ == 0)
{
lean_object* v___x_257_; 
lean_del_object(v___x_253_);
if (v_isShared_225_ == 0)
{
lean_ctor_set(v___x_224_, 1, v_a_251_);
lean_ctor_set(v___x_224_, 0, v_size_232_);
v___x_257_ = v___x_224_;
goto v_reusejp_256_;
}
else
{
lean_object* v_reuseFailAlloc_259_; 
v_reuseFailAlloc_259_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_259_, 0, v_size_232_);
lean_ctor_set(v_reuseFailAlloc_259_, 1, v_a_251_);
v___x_257_ = v_reuseFailAlloc_259_;
goto v_reusejp_256_;
}
v_reusejp_256_:
{
v_b_187_ = v___x_257_;
goto _start;
}
}
else
{
lean_object* v___x_261_; 
lean_dec(v___y_197_);
lean_dec_ref(v___y_196_);
lean_dec(v___y_195_);
lean_dec_ref(v___y_194_);
lean_dec(v___y_193_);
lean_dec_ref(v___y_192_);
lean_dec(v___y_191_);
lean_dec_ref(v___y_190_);
lean_dec(v___y_189_);
lean_dec(v___y_188_);
lean_dec_ref(v_curr_185_);
if (v_isShared_225_ == 0)
{
lean_ctor_set(v___x_224_, 1, v_a_251_);
lean_ctor_set(v___x_224_, 0, v_size_232_);
v___x_261_ = v___x_224_;
goto v_reusejp_260_;
}
else
{
lean_object* v_reuseFailAlloc_265_; 
v_reuseFailAlloc_265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_265_, 0, v_size_232_);
lean_ctor_set(v_reuseFailAlloc_265_, 1, v_a_251_);
v___x_261_ = v_reuseFailAlloc_265_;
goto v_reusejp_260_;
}
v_reusejp_260_:
{
lean_object* v___x_263_; 
if (v_isShared_254_ == 0)
{
lean_ctor_set(v___x_253_, 0, v___x_261_);
v___x_263_ = v___x_253_;
goto v_reusejp_262_;
}
else
{
lean_object* v_reuseFailAlloc_264_; 
v_reuseFailAlloc_264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_264_, 0, v___x_261_);
v___x_263_ = v_reuseFailAlloc_264_;
goto v_reusejp_262_;
}
v_reusejp_262_:
{
return v___x_263_;
}
}
}
}
}
else
{
lean_object* v_a_267_; lean_object* v___x_269_; uint8_t v_isShared_270_; uint8_t v_isSharedCheck_274_; 
lean_dec(v_size_232_);
lean_del_object(v___x_224_);
lean_dec(v___y_197_);
lean_dec_ref(v___y_196_);
lean_dec(v___y_195_);
lean_dec_ref(v___y_194_);
lean_dec(v___y_193_);
lean_dec_ref(v___y_192_);
lean_dec(v___y_191_);
lean_dec_ref(v___y_190_);
lean_dec(v___y_189_);
lean_dec(v___y_188_);
lean_dec_ref(v_curr_185_);
v_a_267_ = lean_ctor_get(v___x_250_, 0);
v_isSharedCheck_274_ = !lean_is_exclusive(v___x_250_);
if (v_isSharedCheck_274_ == 0)
{
v___x_269_ = v___x_250_;
v_isShared_270_ = v_isSharedCheck_274_;
goto v_resetjp_268_;
}
else
{
lean_inc(v_a_267_);
lean_dec(v___x_250_);
v___x_269_ = lean_box(0);
v_isShared_270_ = v_isSharedCheck_274_;
goto v_resetjp_268_;
}
v_resetjp_268_:
{
lean_object* v___x_272_; 
if (v_isShared_270_ == 0)
{
v___x_272_ = v___x_269_;
goto v_reusejp_271_;
}
else
{
lean_object* v_reuseFailAlloc_273_; 
v_reuseFailAlloc_273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_273_, 0, v_a_267_);
v___x_272_ = v_reuseFailAlloc_273_;
goto v_reusejp_271_;
}
v_reusejp_271_:
{
return v___x_272_;
}
}
}
}
}
else
{
lean_object* v_a_275_; lean_object* v___x_277_; uint8_t v_isShared_278_; uint8_t v_isSharedCheck_282_; 
lean_dec(v___y_243_);
lean_dec_ref(v___y_242_);
lean_dec(v___y_241_);
lean_dec_ref(v___y_240_);
lean_dec(v___y_239_);
lean_dec_ref(v___y_238_);
lean_dec(v___y_237_);
lean_dec_ref(v___y_236_);
lean_dec(v___y_235_);
lean_dec(v___y_234_);
lean_dec(v_size_232_);
lean_del_object(v___x_224_);
lean_dec(v_snd_222_);
lean_dec(v___y_197_);
lean_dec_ref(v___y_196_);
lean_dec(v___y_195_);
lean_dec_ref(v___y_194_);
lean_dec(v___y_193_);
lean_dec_ref(v___y_192_);
lean_dec(v___y_191_);
lean_dec_ref(v___y_190_);
lean_dec(v___y_189_);
lean_dec(v___y_188_);
lean_dec_ref(v_curr_185_);
v_a_275_ = lean_ctor_get(v___x_244_, 0);
v_isSharedCheck_282_ = !lean_is_exclusive(v___x_244_);
if (v_isSharedCheck_282_ == 0)
{
v___x_277_ = v___x_244_;
v_isShared_278_ = v_isSharedCheck_282_;
goto v_resetjp_276_;
}
else
{
lean_inc(v_a_275_);
lean_dec(v___x_244_);
v___x_277_ = lean_box(0);
v_isShared_278_ = v_isSharedCheck_282_;
goto v_resetjp_276_;
}
v_resetjp_276_:
{
lean_object* v___x_280_; 
if (v_isShared_278_ == 0)
{
v___x_280_ = v___x_277_;
goto v_reusejp_279_;
}
else
{
lean_object* v_reuseFailAlloc_281_; 
v_reuseFailAlloc_281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_281_, 0, v_a_275_);
v___x_280_ = v_reuseFailAlloc_281_;
goto v_reusejp_279_;
}
v_reusejp_279_:
{
return v___x_280_;
}
}
}
}
v___jp_283_:
{
uint8_t v_heqProofs_294_; 
v_heqProofs_294_ = lean_ctor_get_uint8(v_root_186_, sizeof(void*)*11 + 4);
if (v_heqProofs_294_ == 0)
{
lean_object* v___x_295_; 
lean_inc(v___y_293_);
lean_inc_ref(v___y_292_);
lean_inc(v___y_291_);
lean_inc_ref(v___y_290_);
lean_inc_ref(v_curr_185_);
lean_inc(v_snd_222_);
v___x_295_ = l_Lean_Meta_Grind_hasSameType(v_snd_222_, v_curr_185_, v___y_290_, v___y_291_, v___y_292_, v___y_293_);
if (lean_obj_tag(v___x_295_) == 0)
{
lean_object* v_a_296_; uint8_t v___x_297_; 
v_a_296_ = lean_ctor_get(v___x_295_, 0);
lean_inc(v_a_296_);
lean_dec_ref(v___x_295_);
v___x_297_ = lean_unbox(v_a_296_);
lean_dec(v_a_296_);
if (v___x_297_ == 0)
{
lean_object* v___x_298_; lean_object* v___x_299_; 
lean_dec(v_size_232_);
lean_del_object(v___x_224_);
lean_dec(v_snd_222_);
v___x_298_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___closed__7, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___closed__7_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___closed__7);
v___x_299_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__0(v___x_298_, v___y_284_, v___y_285_, v___y_286_, v___y_287_, v___y_288_, v___y_289_, v___y_290_, v___y_291_, v___y_292_, v___y_293_);
v___y_200_ = v___x_299_;
goto v___jp_199_;
}
else
{
v___y_234_ = v___y_284_;
v___y_235_ = v___y_285_;
v___y_236_ = v___y_286_;
v___y_237_ = v___y_287_;
v___y_238_ = v___y_288_;
v___y_239_ = v___y_289_;
v___y_240_ = v___y_290_;
v___y_241_ = v___y_291_;
v___y_242_ = v___y_292_;
v___y_243_ = v___y_293_;
goto v___jp_233_;
}
}
else
{
lean_object* v_a_300_; lean_object* v___x_302_; uint8_t v_isShared_303_; uint8_t v_isSharedCheck_307_; 
lean_dec(v___y_293_);
lean_dec_ref(v___y_292_);
lean_dec(v___y_291_);
lean_dec_ref(v___y_290_);
lean_dec(v___y_289_);
lean_dec_ref(v___y_288_);
lean_dec(v___y_287_);
lean_dec_ref(v___y_286_);
lean_dec(v___y_285_);
lean_dec(v___y_284_);
lean_dec(v_size_232_);
lean_del_object(v___x_224_);
lean_dec(v_snd_222_);
lean_dec(v___y_197_);
lean_dec_ref(v___y_196_);
lean_dec(v___y_195_);
lean_dec_ref(v___y_194_);
lean_dec(v___y_193_);
lean_dec_ref(v___y_192_);
lean_dec(v___y_191_);
lean_dec_ref(v___y_190_);
lean_dec(v___y_189_);
lean_dec(v___y_188_);
lean_dec_ref(v_curr_185_);
v_a_300_ = lean_ctor_get(v___x_295_, 0);
v_isSharedCheck_307_ = !lean_is_exclusive(v___x_295_);
if (v_isSharedCheck_307_ == 0)
{
v___x_302_ = v___x_295_;
v_isShared_303_ = v_isSharedCheck_307_;
goto v_resetjp_301_;
}
else
{
lean_inc(v_a_300_);
lean_dec(v___x_295_);
v___x_302_ = lean_box(0);
v_isShared_303_ = v_isSharedCheck_307_;
goto v_resetjp_301_;
}
v_resetjp_301_:
{
lean_object* v___x_305_; 
if (v_isShared_303_ == 0)
{
v___x_305_ = v___x_302_;
goto v_reusejp_304_;
}
else
{
lean_object* v_reuseFailAlloc_306_; 
v_reuseFailAlloc_306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_306_, 0, v_a_300_);
v___x_305_ = v_reuseFailAlloc_306_;
goto v_reusejp_304_;
}
v_reusejp_304_:
{
return v___x_305_;
}
}
}
}
else
{
v___y_234_ = v___y_284_;
v___y_235_ = v___y_285_;
v___y_236_ = v___y_286_;
v___y_237_ = v___y_287_;
v___y_238_ = v___y_288_;
v___y_239_ = v___y_289_;
v___y_240_ = v___y_290_;
v___y_241_ = v___y_291_;
v___y_242_ = v___y_292_;
v___y_243_ = v___y_293_;
goto v___jp_233_;
}
}
}
}
else
{
lean_object* v_a_355_; lean_object* v___x_357_; uint8_t v_isShared_358_; uint8_t v_isSharedCheck_362_; 
lean_del_object(v___x_224_);
lean_dec(v_snd_222_);
lean_dec(v_fst_221_);
lean_dec(v___y_197_);
lean_dec_ref(v___y_196_);
lean_dec(v___y_195_);
lean_dec_ref(v___y_194_);
lean_dec(v___y_193_);
lean_dec_ref(v___y_192_);
lean_dec(v___y_191_);
lean_dec_ref(v___y_190_);
lean_dec(v___y_189_);
lean_dec(v___y_188_);
lean_dec_ref(v_curr_185_);
v_a_355_ = lean_ctor_get(v___x_226_, 0);
v_isSharedCheck_362_ = !lean_is_exclusive(v___x_226_);
if (v_isSharedCheck_362_ == 0)
{
v___x_357_ = v___x_226_;
v_isShared_358_ = v_isSharedCheck_362_;
goto v_resetjp_356_;
}
else
{
lean_inc(v_a_355_);
lean_dec(v___x_226_);
v___x_357_ = lean_box(0);
v_isShared_358_ = v_isSharedCheck_362_;
goto v_resetjp_356_;
}
v_resetjp_356_:
{
lean_object* v___x_360_; 
if (v_isShared_358_ == 0)
{
v___x_360_ = v___x_357_;
goto v_reusejp_359_;
}
else
{
lean_object* v_reuseFailAlloc_361_; 
v_reuseFailAlloc_361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_361_, 0, v_a_355_);
v___x_360_ = v_reuseFailAlloc_361_;
goto v_reusejp_359_;
}
v_reusejp_359_:
{
return v___x_360_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___boxed(lean_object* v_curr_364_, lean_object* v_root_365_, lean_object* v_b_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_){
_start:
{
lean_object* v_res_378_; 
v_res_378_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3(v_curr_364_, v_root_365_, v_b_366_, v___y_367_, v___y_368_, v___y_369_, v___y_370_, v___y_371_, v___y_372_, v___y_373_, v___y_374_, v___y_375_, v___y_376_);
lean_dec_ref(v_root_365_);
return v_res_378_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc___closed__1(void){
_start:
{
lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; 
v___x_380_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc___closed__0));
v___x_381_ = lean_unsigned_to_nat(2u);
v___x_382_ = lean_unsigned_to_nat(46u);
v___x_383_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___closed__1));
v___x_384_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___closed__0));
v___x_385_ = l_mkPanicMessageWithDecl(v___x_384_, v___x_383_, v___x_382_, v___x_381_, v___x_380_);
return v___x_385_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc(lean_object* v_root_386_, lean_object* v_a_387_, lean_object* v_a_388_, lean_object* v_a_389_, lean_object* v_a_390_, lean_object* v_a_391_, lean_object* v_a_392_, lean_object* v_a_393_, lean_object* v_a_394_, lean_object* v_a_395_, lean_object* v_a_396_){
_start:
{
lean_object* v_self_398_; lean_object* v_size_399_; lean_object* v_size_400_; lean_object* v___x_401_; lean_object* v___x_402_; 
v_self_398_ = lean_ctor_get(v_root_386_, 0);
lean_inc_ref(v_self_398_);
v_size_399_ = lean_ctor_get(v_root_386_, 6);
lean_inc(v_size_399_);
v_size_400_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_self_398_);
v___x_401_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_401_, 0, v_size_400_);
lean_ctor_set(v___x_401_, 1, v_self_398_);
lean_inc(v_a_396_);
lean_inc_ref(v_a_395_);
lean_inc(v_a_394_);
lean_inc_ref(v_a_393_);
lean_inc(v_a_392_);
lean_inc_ref(v_a_391_);
lean_inc(v_a_390_);
lean_inc_ref(v_a_389_);
lean_inc(v_a_388_);
lean_inc(v_a_387_);
v___x_402_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3(v_self_398_, v_root_386_, v___x_401_, v_a_387_, v_a_388_, v_a_389_, v_a_390_, v_a_391_, v_a_392_, v_a_393_, v_a_394_, v_a_395_, v_a_396_);
lean_dec_ref(v_root_386_);
if (lean_obj_tag(v___x_402_) == 0)
{
lean_object* v_a_403_; lean_object* v___x_405_; uint8_t v_isShared_406_; uint8_t v_isSharedCheck_415_; 
v_a_403_ = lean_ctor_get(v___x_402_, 0);
v_isSharedCheck_415_ = !lean_is_exclusive(v___x_402_);
if (v_isSharedCheck_415_ == 0)
{
v___x_405_ = v___x_402_;
v_isShared_406_ = v_isSharedCheck_415_;
goto v_resetjp_404_;
}
else
{
lean_inc(v_a_403_);
lean_dec(v___x_402_);
v___x_405_ = lean_box(0);
v_isShared_406_ = v_isSharedCheck_415_;
goto v_resetjp_404_;
}
v_resetjp_404_:
{
lean_object* v_fst_407_; uint8_t v___x_408_; 
v_fst_407_ = lean_ctor_get(v_a_403_, 0);
lean_inc(v_fst_407_);
lean_dec(v_a_403_);
v___x_408_ = lean_nat_dec_eq(v_size_399_, v_fst_407_);
lean_dec(v_fst_407_);
lean_dec(v_size_399_);
if (v___x_408_ == 0)
{
lean_object* v___x_409_; lean_object* v___x_410_; 
lean_del_object(v___x_405_);
v___x_409_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc___closed__1, &l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc___closed__1);
v___x_410_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__4(v___x_409_, v_a_387_, v_a_388_, v_a_389_, v_a_390_, v_a_391_, v_a_392_, v_a_393_, v_a_394_, v_a_395_, v_a_396_);
return v___x_410_;
}
else
{
lean_object* v___x_411_; lean_object* v___x_413_; 
lean_dec(v_a_396_);
lean_dec_ref(v_a_395_);
lean_dec(v_a_394_);
lean_dec_ref(v_a_393_);
lean_dec(v_a_392_);
lean_dec_ref(v_a_391_);
lean_dec(v_a_390_);
lean_dec_ref(v_a_389_);
lean_dec(v_a_388_);
lean_dec(v_a_387_);
v___x_411_ = lean_box(0);
if (v_isShared_406_ == 0)
{
lean_ctor_set(v___x_405_, 0, v___x_411_);
v___x_413_ = v___x_405_;
goto v_reusejp_412_;
}
else
{
lean_object* v_reuseFailAlloc_414_; 
v_reuseFailAlloc_414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_414_, 0, v___x_411_);
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
else
{
lean_object* v_a_416_; lean_object* v___x_418_; uint8_t v_isShared_419_; uint8_t v_isSharedCheck_423_; 
lean_dec(v_size_399_);
lean_dec(v_a_396_);
lean_dec_ref(v_a_395_);
lean_dec(v_a_394_);
lean_dec_ref(v_a_393_);
lean_dec(v_a_392_);
lean_dec_ref(v_a_391_);
lean_dec(v_a_390_);
lean_dec_ref(v_a_389_);
lean_dec(v_a_388_);
lean_dec(v_a_387_);
v_a_416_ = lean_ctor_get(v___x_402_, 0);
v_isSharedCheck_423_ = !lean_is_exclusive(v___x_402_);
if (v_isSharedCheck_423_ == 0)
{
v___x_418_ = v___x_402_;
v_isShared_419_ = v_isSharedCheck_423_;
goto v_resetjp_417_;
}
else
{
lean_inc(v_a_416_);
lean_dec(v___x_402_);
v___x_418_ = lean_box(0);
v_isShared_419_ = v_isSharedCheck_423_;
goto v_resetjp_417_;
}
v_resetjp_417_:
{
lean_object* v___x_421_; 
if (v_isShared_419_ == 0)
{
v___x_421_ = v___x_418_;
goto v_reusejp_420_;
}
else
{
lean_object* v_reuseFailAlloc_422_; 
v_reuseFailAlloc_422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_422_, 0, v_a_416_);
v___x_421_ = v_reuseFailAlloc_422_;
goto v_reusejp_420_;
}
v_reusejp_420_:
{
return v___x_421_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc___boxed(lean_object* v_root_424_, lean_object* v_a_425_, lean_object* v_a_426_, lean_object* v_a_427_, lean_object* v_a_428_, lean_object* v_a_429_, lean_object* v_a_430_, lean_object* v_a_431_, lean_object* v_a_432_, lean_object* v_a_433_, lean_object* v_a_434_, lean_object* v_a_435_){
_start:
{
lean_object* v_res_436_; 
v_res_436_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc(v_root_424_, v_a_425_, v_a_426_, v_a_427_, v_a_428_, v_a_429_, v_a_430_, v_a_431_, v_a_432_, v_a_433_, v_a_434_);
return v_res_436_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__1(lean_object* v_b_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_){
_start:
{
lean_object* v___x_449_; 
v___x_449_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__1___redArg(v_b_437_, v___y_438_);
return v___x_449_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__1___boxed(lean_object* v_b_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_){
_start:
{
lean_object* v_res_462_; 
v_res_462_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__1(v_b_450_, v___y_451_, v___y_452_, v___y_453_, v___y_454_, v___y_455_, v___y_456_, v___y_457_, v___y_458_, v___y_459_, v___y_460_);
lean_dec(v___y_460_);
lean_dec_ref(v___y_459_);
lean_dec(v___y_458_);
lean_dec_ref(v___y_457_);
lean_dec(v___y_456_);
lean_dec_ref(v___y_455_);
lean_dec(v___y_454_);
lean_dec_ref(v___y_453_);
lean_dec(v___y_452_);
lean_dec(v___y_451_);
return v_res_462_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2(lean_object* v___x_463_, lean_object* v_00_u03b2_464_, lean_object* v_x_465_, lean_object* v_x_466_){
_start:
{
lean_object* v___x_467_; 
v___x_467_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2___redArg(v___x_463_, v_x_465_, v_x_466_);
return v___x_467_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2(lean_object* v___x_468_, lean_object* v_00_u03b2_469_, lean_object* v_x_470_, size_t v_x_471_, lean_object* v_x_472_){
_start:
{
lean_object* v___x_473_; 
v___x_473_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2___redArg(v___x_468_, v_x_470_, v_x_471_, v_x_472_);
return v___x_473_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2___boxed(lean_object* v___x_474_, lean_object* v_00_u03b2_475_, lean_object* v_x_476_, lean_object* v_x_477_, lean_object* v_x_478_){
_start:
{
size_t v_x_28096__boxed_479_; lean_object* v_res_480_; 
v_x_28096__boxed_479_ = lean_unbox_usize(v_x_477_);
lean_dec(v_x_477_);
v_res_480_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2(v___x_474_, v_00_u03b2_475_, v_x_476_, v_x_28096__boxed_479_, v_x_478_);
return v_res_480_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2_spec__4(lean_object* v___x_481_, lean_object* v_00_u03b2_482_, lean_object* v_keys_483_, lean_object* v_vals_484_, lean_object* v_heq_485_, lean_object* v_i_486_, lean_object* v_k_487_){
_start:
{
lean_object* v___x_488_; 
v___x_488_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2_spec__4___redArg(v___x_481_, v_keys_483_, v_vals_484_, v_i_486_, v_k_487_);
return v___x_488_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2_spec__4___boxed(lean_object* v___x_489_, lean_object* v_00_u03b2_490_, lean_object* v_keys_491_, lean_object* v_vals_492_, lean_object* v_heq_493_, lean_object* v_i_494_, lean_object* v_k_495_){
_start:
{
lean_object* v_res_496_; 
v_res_496_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2_spec__4(v___x_489_, v_00_u03b2_490_, v_keys_491_, v_vals_492_, v_heq_493_, v_i_494_, v_k_495_);
lean_dec_ref(v_vals_492_);
lean_dec_ref(v_keys_491_);
return v_res_496_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkChild___redArg(lean_object* v_e_497_, lean_object* v_child_498_, lean_object* v_a_499_){
_start:
{
lean_object* v___x_501_; lean_object* v___x_502_; 
v___x_501_ = lean_st_ref_get(v_a_499_);
v___x_502_ = l_Lean_Meta_Grind_Goal_getRoot_x3f(v___x_501_, v_child_498_);
if (lean_obj_tag(v___x_502_) == 1)
{
lean_object* v_val_503_; lean_object* v___x_505_; uint8_t v_isShared_506_; uint8_t v_isSharedCheck_512_; 
v_val_503_ = lean_ctor_get(v___x_502_, 0);
v_isSharedCheck_512_ = !lean_is_exclusive(v___x_502_);
if (v_isSharedCheck_512_ == 0)
{
v___x_505_ = v___x_502_;
v_isShared_506_ = v_isSharedCheck_512_;
goto v_resetjp_504_;
}
else
{
lean_inc(v_val_503_);
lean_dec(v___x_502_);
v___x_505_ = lean_box(0);
v_isShared_506_ = v_isSharedCheck_512_;
goto v_resetjp_504_;
}
v_resetjp_504_:
{
uint8_t v___x_507_; lean_object* v___x_508_; lean_object* v___x_510_; 
v___x_507_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_val_503_, v_e_497_);
lean_dec(v_val_503_);
v___x_508_ = lean_box(v___x_507_);
if (v_isShared_506_ == 0)
{
lean_ctor_set_tag(v___x_505_, 0);
lean_ctor_set(v___x_505_, 0, v___x_508_);
v___x_510_ = v___x_505_;
goto v_reusejp_509_;
}
else
{
lean_object* v_reuseFailAlloc_511_; 
v_reuseFailAlloc_511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_511_, 0, v___x_508_);
v___x_510_ = v_reuseFailAlloc_511_;
goto v_reusejp_509_;
}
v_reusejp_509_:
{
return v___x_510_;
}
}
}
else
{
uint8_t v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; 
lean_dec(v___x_502_);
v___x_513_ = 0;
v___x_514_ = lean_box(v___x_513_);
v___x_515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_515_, 0, v___x_514_);
return v___x_515_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkChild___redArg___boxed(lean_object* v_e_516_, lean_object* v_child_517_, lean_object* v_a_518_, lean_object* v_a_519_){
_start:
{
lean_object* v_res_520_; 
v_res_520_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkChild___redArg(v_e_516_, v_child_517_, v_a_518_);
lean_dec(v_a_518_);
lean_dec_ref(v_child_517_);
lean_dec_ref(v_e_516_);
return v_res_520_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkChild(lean_object* v_e_521_, lean_object* v_child_522_, lean_object* v_a_523_, lean_object* v_a_524_, lean_object* v_a_525_, lean_object* v_a_526_, lean_object* v_a_527_, lean_object* v_a_528_, lean_object* v_a_529_, lean_object* v_a_530_, lean_object* v_a_531_, lean_object* v_a_532_){
_start:
{
lean_object* v___x_534_; 
v___x_534_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkChild___redArg(v_e_521_, v_child_522_, v_a_523_);
return v___x_534_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkChild___boxed(lean_object* v_e_535_, lean_object* v_child_536_, lean_object* v_a_537_, lean_object* v_a_538_, lean_object* v_a_539_, lean_object* v_a_540_, lean_object* v_a_541_, lean_object* v_a_542_, lean_object* v_a_543_, lean_object* v_a_544_, lean_object* v_a_545_, lean_object* v_a_546_, lean_object* v_a_547_){
_start:
{
lean_object* v_res_548_; 
v_res_548_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkChild(v_e_535_, v_child_536_, v_a_537_, v_a_538_, v_a_539_, v_a_540_, v_a_541_, v_a_542_, v_a_543_, v_a_544_, v_a_545_, v_a_546_);
lean_dec(v_a_546_);
lean_dec_ref(v_a_545_);
lean_dec(v_a_544_);
lean_dec_ref(v_a_543_);
lean_dec(v_a_542_);
lean_dec_ref(v_a_541_);
lean_dec(v_a_540_);
lean_dec_ref(v_a_539_);
lean_dec(v_a_538_);
lean_dec(v_a_537_);
lean_dec_ref(v_child_536_);
lean_dec_ref(v_e_535_);
return v_res_548_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg(lean_object* v_e_558_, lean_object* v_b_559_, lean_object* v___y_560_, lean_object* v___y_561_){
_start:
{
lean_object* v_snd_563_; lean_object* v___x_565_; uint8_t v_isShared_566_; uint8_t v_isSharedCheck_653_; 
v_snd_563_ = lean_ctor_get(v_b_559_, 1);
v_isSharedCheck_653_ = !lean_is_exclusive(v_b_559_);
if (v_isSharedCheck_653_ == 0)
{
lean_object* v_unused_654_; 
v_unused_654_ = lean_ctor_get(v_b_559_, 0);
lean_dec(v_unused_654_);
v___x_565_ = v_b_559_;
v_isShared_566_ = v_isSharedCheck_653_;
goto v_resetjp_564_;
}
else
{
lean_inc(v_snd_563_);
lean_dec(v_b_559_);
v___x_565_ = lean_box(0);
v_isShared_566_ = v_isSharedCheck_653_;
goto v_resetjp_564_;
}
v_resetjp_564_:
{
if (lean_obj_tag(v_snd_563_) == 7)
{
lean_object* v_binderType_567_; lean_object* v_body_568_; lean_object* v___x_569_; 
v_binderType_567_ = lean_ctor_get(v_snd_563_, 1);
v_body_568_ = lean_ctor_get(v_snd_563_, 2);
lean_inc_ref(v_binderType_567_);
v___x_569_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_binderType_567_, v___y_561_);
if (lean_obj_tag(v___x_569_) == 0)
{
lean_object* v_a_570_; lean_object* v___x_571_; lean_object* v___x_577_; uint8_t v___x_578_; 
v_a_570_ = lean_ctor_get(v___x_569_, 0);
lean_inc(v_a_570_);
lean_dec_ref(v___x_569_);
v___x_571_ = lean_box(0);
v___x_577_ = l_Lean_Expr_cleanupAnnotations(v_a_570_);
v___x_578_ = l_Lean_Expr_isApp(v___x_577_);
if (v___x_578_ == 0)
{
lean_inc_ref(v_body_568_);
lean_dec_ref(v___x_577_);
lean_dec_ref(v_snd_563_);
goto v___jp_572_;
}
else
{
lean_object* v___x_579_; uint8_t v___x_580_; 
v___x_579_ = l_Lean_Expr_appFnCleanup___redArg(v___x_577_);
v___x_580_ = l_Lean_Expr_isApp(v___x_579_);
if (v___x_580_ == 0)
{
lean_inc_ref(v_body_568_);
lean_dec_ref(v___x_579_);
lean_dec_ref(v_snd_563_);
goto v___jp_572_;
}
else
{
lean_object* v_arg_581_; lean_object* v___x_582_; uint8_t v___x_583_; 
v_arg_581_ = lean_ctor_get(v___x_579_, 1);
lean_inc_ref(v_arg_581_);
v___x_582_ = l_Lean_Expr_appFnCleanup___redArg(v___x_579_);
v___x_583_ = l_Lean_Expr_isApp(v___x_582_);
if (v___x_583_ == 0)
{
lean_inc_ref(v_body_568_);
lean_dec_ref(v___x_582_);
lean_dec_ref(v_arg_581_);
lean_dec_ref(v_snd_563_);
goto v___jp_572_;
}
else
{
lean_object* v_arg_584_; lean_object* v___x_585_; lean_object* v___x_586_; uint8_t v___x_587_; 
v_arg_584_ = lean_ctor_get(v___x_582_, 1);
lean_inc_ref(v_arg_584_);
v___x_585_ = l_Lean_Expr_appFnCleanup___redArg(v___x_582_);
v___x_586_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___closed__1));
v___x_587_ = l_Lean_Expr_isConstOf(v___x_585_, v___x_586_);
if (v___x_587_ == 0)
{
uint8_t v___x_588_; 
lean_dec_ref(v_arg_581_);
v___x_588_ = l_Lean_Expr_isApp(v___x_585_);
if (v___x_588_ == 0)
{
lean_inc_ref(v_body_568_);
lean_dec_ref(v___x_585_);
lean_dec_ref(v_arg_584_);
lean_dec_ref(v_snd_563_);
goto v___jp_572_;
}
else
{
lean_object* v_arg_589_; lean_object* v___x_590_; lean_object* v___x_591_; uint8_t v___x_592_; lean_object* v___y_594_; 
v_arg_589_ = lean_ctor_get(v___x_585_, 1);
lean_inc_ref(v_arg_589_);
v___x_590_ = l_Lean_Expr_appFnCleanup___redArg(v___x_585_);
v___x_591_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___closed__3));
v___x_592_ = l_Lean_Expr_isConstOf(v___x_590_, v___x_591_);
lean_dec_ref(v___x_590_);
if (v___x_592_ == 0)
{
lean_inc_ref(v_body_568_);
lean_dec_ref(v_arg_589_);
lean_dec_ref(v_arg_584_);
lean_dec_ref(v_snd_563_);
goto v___jp_572_;
}
else
{
lean_object* v___x_615_; 
v___x_615_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkChild___redArg(v_e_558_, v_arg_589_, v___y_560_);
lean_dec_ref(v_arg_589_);
if (lean_obj_tag(v___x_615_) == 0)
{
lean_object* v_a_616_; uint8_t v___x_617_; 
v_a_616_ = lean_ctor_get(v___x_615_, 0);
lean_inc(v_a_616_);
v___x_617_ = lean_unbox(v_a_616_);
lean_dec(v_a_616_);
if (v___x_617_ == 0)
{
lean_object* v___x_618_; 
lean_dec_ref(v___x_615_);
v___x_618_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkChild___redArg(v_e_558_, v_arg_584_, v___y_560_);
lean_dec_ref(v_arg_584_);
v___y_594_ = v___x_618_;
goto v___jp_593_;
}
else
{
lean_dec_ref(v_arg_584_);
v___y_594_ = v___x_615_;
goto v___jp_593_;
}
}
else
{
lean_dec_ref(v_arg_584_);
v___y_594_ = v___x_615_;
goto v___jp_593_;
}
}
v___jp_593_:
{
if (lean_obj_tag(v___y_594_) == 0)
{
lean_object* v_a_595_; lean_object* v___x_597_; uint8_t v_isShared_598_; uint8_t v_isSharedCheck_606_; 
v_a_595_ = lean_ctor_get(v___y_594_, 0);
v_isSharedCheck_606_ = !lean_is_exclusive(v___y_594_);
if (v_isSharedCheck_606_ == 0)
{
v___x_597_ = v___y_594_;
v_isShared_598_ = v_isSharedCheck_606_;
goto v_resetjp_596_;
}
else
{
lean_inc(v_a_595_);
lean_dec(v___y_594_);
v___x_597_ = lean_box(0);
v_isShared_598_ = v_isSharedCheck_606_;
goto v_resetjp_596_;
}
v_resetjp_596_:
{
uint8_t v___x_599_; 
v___x_599_ = lean_unbox(v_a_595_);
lean_dec(v_a_595_);
if (v___x_599_ == 0)
{
lean_inc_ref(v_body_568_);
lean_del_object(v___x_597_);
lean_dec_ref(v_snd_563_);
goto v___jp_572_;
}
else
{
lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_604_; 
lean_del_object(v___x_565_);
v___x_600_ = lean_box(v___x_592_);
v___x_601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_601_, 0, v___x_600_);
v___x_602_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_602_, 0, v___x_601_);
lean_ctor_set(v___x_602_, 1, v_snd_563_);
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
}
}
else
{
lean_object* v_a_607_; lean_object* v___x_609_; uint8_t v_isShared_610_; uint8_t v_isSharedCheck_614_; 
lean_dec_ref(v_snd_563_);
lean_del_object(v___x_565_);
v_a_607_ = lean_ctor_get(v___y_594_, 0);
v_isSharedCheck_614_ = !lean_is_exclusive(v___y_594_);
if (v_isSharedCheck_614_ == 0)
{
v___x_609_ = v___y_594_;
v_isShared_610_ = v_isSharedCheck_614_;
goto v_resetjp_608_;
}
else
{
lean_inc(v_a_607_);
lean_dec(v___y_594_);
v___x_609_ = lean_box(0);
v_isShared_610_ = v_isSharedCheck_614_;
goto v_resetjp_608_;
}
v_resetjp_608_:
{
lean_object* v___x_612_; 
if (v_isShared_610_ == 0)
{
v___x_612_ = v___x_609_;
goto v_reusejp_611_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v_a_607_);
v___x_612_ = v_reuseFailAlloc_613_;
goto v_reusejp_611_;
}
v_reusejp_611_:
{
return v___x_612_;
}
}
}
}
}
}
else
{
lean_object* v___x_619_; 
lean_dec_ref(v___x_585_);
lean_dec_ref(v_arg_584_);
v___x_619_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkChild___redArg(v_e_558_, v_arg_581_, v___y_560_);
lean_dec_ref(v_arg_581_);
if (lean_obj_tag(v___x_619_) == 0)
{
lean_object* v_a_620_; lean_object* v___x_622_; uint8_t v_isShared_623_; uint8_t v_isSharedCheck_631_; 
v_a_620_ = lean_ctor_get(v___x_619_, 0);
v_isSharedCheck_631_ = !lean_is_exclusive(v___x_619_);
if (v_isSharedCheck_631_ == 0)
{
v___x_622_ = v___x_619_;
v_isShared_623_ = v_isSharedCheck_631_;
goto v_resetjp_621_;
}
else
{
lean_inc(v_a_620_);
lean_dec(v___x_619_);
v___x_622_ = lean_box(0);
v_isShared_623_ = v_isSharedCheck_631_;
goto v_resetjp_621_;
}
v_resetjp_621_:
{
uint8_t v___x_624_; 
v___x_624_ = lean_unbox(v_a_620_);
lean_dec(v_a_620_);
if (v___x_624_ == 0)
{
lean_inc_ref(v_body_568_);
lean_del_object(v___x_622_);
lean_dec_ref(v_snd_563_);
goto v___jp_572_;
}
else
{
lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_629_; 
lean_del_object(v___x_565_);
v___x_625_ = lean_box(v___x_587_);
v___x_626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_626_, 0, v___x_625_);
v___x_627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_627_, 0, v___x_626_);
lean_ctor_set(v___x_627_, 1, v_snd_563_);
if (v_isShared_623_ == 0)
{
lean_ctor_set(v___x_622_, 0, v___x_627_);
v___x_629_ = v___x_622_;
goto v_reusejp_628_;
}
else
{
lean_object* v_reuseFailAlloc_630_; 
v_reuseFailAlloc_630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_630_, 0, v___x_627_);
v___x_629_ = v_reuseFailAlloc_630_;
goto v_reusejp_628_;
}
v_reusejp_628_:
{
return v___x_629_;
}
}
}
}
else
{
lean_object* v_a_632_; lean_object* v___x_634_; uint8_t v_isShared_635_; uint8_t v_isSharedCheck_639_; 
lean_dec_ref(v_snd_563_);
lean_del_object(v___x_565_);
v_a_632_ = lean_ctor_get(v___x_619_, 0);
v_isSharedCheck_639_ = !lean_is_exclusive(v___x_619_);
if (v_isSharedCheck_639_ == 0)
{
v___x_634_ = v___x_619_;
v_isShared_635_ = v_isSharedCheck_639_;
goto v_resetjp_633_;
}
else
{
lean_inc(v_a_632_);
lean_dec(v___x_619_);
v___x_634_ = lean_box(0);
v_isShared_635_ = v_isSharedCheck_639_;
goto v_resetjp_633_;
}
v_resetjp_633_:
{
lean_object* v___x_637_; 
if (v_isShared_635_ == 0)
{
v___x_637_ = v___x_634_;
goto v_reusejp_636_;
}
else
{
lean_object* v_reuseFailAlloc_638_; 
v_reuseFailAlloc_638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_638_, 0, v_a_632_);
v___x_637_ = v_reuseFailAlloc_638_;
goto v_reusejp_636_;
}
v_reusejp_636_:
{
return v___x_637_;
}
}
}
}
}
}
}
v___jp_572_:
{
lean_object* v___x_574_; 
if (v_isShared_566_ == 0)
{
lean_ctor_set(v___x_565_, 1, v_body_568_);
lean_ctor_set(v___x_565_, 0, v___x_571_);
v___x_574_ = v___x_565_;
goto v_reusejp_573_;
}
else
{
lean_object* v_reuseFailAlloc_576_; 
v_reuseFailAlloc_576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_576_, 0, v___x_571_);
lean_ctor_set(v_reuseFailAlloc_576_, 1, v_body_568_);
v___x_574_ = v_reuseFailAlloc_576_;
goto v_reusejp_573_;
}
v_reusejp_573_:
{
v_b_559_ = v___x_574_;
goto _start;
}
}
}
else
{
lean_object* v_a_640_; lean_object* v___x_642_; uint8_t v_isShared_643_; uint8_t v_isSharedCheck_647_; 
lean_dec_ref(v_snd_563_);
lean_del_object(v___x_565_);
v_a_640_ = lean_ctor_get(v___x_569_, 0);
v_isSharedCheck_647_ = !lean_is_exclusive(v___x_569_);
if (v_isSharedCheck_647_ == 0)
{
v___x_642_ = v___x_569_;
v_isShared_643_ = v_isSharedCheck_647_;
goto v_resetjp_641_;
}
else
{
lean_inc(v_a_640_);
lean_dec(v___x_569_);
v___x_642_ = lean_box(0);
v_isShared_643_ = v_isSharedCheck_647_;
goto v_resetjp_641_;
}
v_resetjp_641_:
{
lean_object* v___x_645_; 
if (v_isShared_643_ == 0)
{
v___x_645_ = v___x_642_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v_a_640_);
v___x_645_ = v_reuseFailAlloc_646_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
return v___x_645_;
}
}
}
}
else
{
lean_object* v___x_648_; lean_object* v___x_650_; 
v___x_648_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___closed__4));
if (v_isShared_566_ == 0)
{
lean_ctor_set(v___x_565_, 0, v___x_648_);
v___x_650_ = v___x_565_;
goto v_reusejp_649_;
}
else
{
lean_object* v_reuseFailAlloc_652_; 
v_reuseFailAlloc_652_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_652_, 0, v___x_648_);
lean_ctor_set(v_reuseFailAlloc_652_, 1, v_snd_563_);
v___x_650_ = v_reuseFailAlloc_652_;
goto v_reusejp_649_;
}
v_reusejp_649_:
{
lean_object* v___x_651_; 
v___x_651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_651_, 0, v___x_650_);
return v___x_651_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___boxed(lean_object* v_e_655_, lean_object* v_b_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_){
_start:
{
lean_object* v_res_660_; 
v_res_660_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg(v_e_655_, v_b_656_, v___y_657_, v___y_658_);
lean_dec(v___y_658_);
lean_dec(v___y_657_);
lean_dec_ref(v_e_655_);
return v_res_660_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent(lean_object* v_e_668_, lean_object* v_parent_669_, lean_object* v_a_670_, lean_object* v_a_671_, lean_object* v_a_672_, lean_object* v_a_673_, lean_object* v_a_674_, lean_object* v_a_675_, lean_object* v_a_676_, lean_object* v_a_677_, lean_object* v_a_678_, lean_object* v_a_679_){
_start:
{
lean_object* v___x_681_; 
v___x_681_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_parent_669_, v_a_677_);
if (lean_obj_tag(v___x_681_) == 0)
{
lean_object* v_a_682_; lean_object* v___x_684_; uint8_t v_isShared_685_; uint8_t v_isSharedCheck_724_; 
v_a_682_ = lean_ctor_get(v___x_681_, 0);
v_isSharedCheck_724_ = !lean_is_exclusive(v___x_681_);
if (v_isSharedCheck_724_ == 0)
{
v___x_684_ = v___x_681_;
v_isShared_685_ = v_isSharedCheck_724_;
goto v_resetjp_683_;
}
else
{
lean_inc(v_a_682_);
lean_dec(v___x_681_);
v___x_684_ = lean_box(0);
v_isShared_685_ = v_isSharedCheck_724_;
goto v_resetjp_683_;
}
v_resetjp_683_:
{
lean_object* v___x_692_; uint8_t v___x_693_; 
v___x_692_ = l_Lean_Expr_cleanupAnnotations(v_a_682_);
v___x_693_ = l_Lean_Expr_isApp(v___x_692_);
if (v___x_693_ == 0)
{
lean_dec_ref(v___x_692_);
goto v___jp_686_;
}
else
{
lean_object* v_arg_694_; lean_object* v___x_695_; lean_object* v___x_696_; uint8_t v___x_697_; 
v_arg_694_ = lean_ctor_get(v___x_692_, 1);
lean_inc_ref(v_arg_694_);
v___x_695_ = l_Lean_Expr_appFnCleanup___redArg(v___x_692_);
v___x_696_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent___closed__3));
v___x_697_ = l_Lean_Expr_isConstOf(v___x_695_, v___x_696_);
lean_dec_ref(v___x_695_);
if (v___x_697_ == 0)
{
lean_dec_ref(v_arg_694_);
goto v___jp_686_;
}
else
{
lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; 
lean_del_object(v___x_684_);
v___x_698_ = lean_box(0);
v___x_699_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_699_, 0, v___x_698_);
lean_ctor_set(v___x_699_, 1, v_arg_694_);
v___x_700_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg(v_e_668_, v___x_699_, v_a_670_, v_a_677_);
if (lean_obj_tag(v___x_700_) == 0)
{
lean_object* v_a_701_; lean_object* v___x_703_; uint8_t v_isShared_704_; uint8_t v_isSharedCheck_715_; 
v_a_701_ = lean_ctor_get(v___x_700_, 0);
v_isSharedCheck_715_ = !lean_is_exclusive(v___x_700_);
if (v_isSharedCheck_715_ == 0)
{
v___x_703_ = v___x_700_;
v_isShared_704_ = v_isSharedCheck_715_;
goto v_resetjp_702_;
}
else
{
lean_inc(v_a_701_);
lean_dec(v___x_700_);
v___x_703_ = lean_box(0);
v_isShared_704_ = v_isSharedCheck_715_;
goto v_resetjp_702_;
}
v_resetjp_702_:
{
lean_object* v_fst_705_; 
v_fst_705_ = lean_ctor_get(v_a_701_, 0);
lean_inc(v_fst_705_);
lean_dec(v_a_701_);
if (lean_obj_tag(v_fst_705_) == 0)
{
uint8_t v___x_706_; lean_object* v___x_707_; lean_object* v___x_709_; 
v___x_706_ = 0;
v___x_707_ = lean_box(v___x_706_);
if (v_isShared_704_ == 0)
{
lean_ctor_set(v___x_703_, 0, v___x_707_);
v___x_709_ = v___x_703_;
goto v_reusejp_708_;
}
else
{
lean_object* v_reuseFailAlloc_710_; 
v_reuseFailAlloc_710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_710_, 0, v___x_707_);
v___x_709_ = v_reuseFailAlloc_710_;
goto v_reusejp_708_;
}
v_reusejp_708_:
{
return v___x_709_;
}
}
else
{
lean_object* v_val_711_; lean_object* v___x_713_; 
v_val_711_ = lean_ctor_get(v_fst_705_, 0);
lean_inc(v_val_711_);
lean_dec_ref(v_fst_705_);
if (v_isShared_704_ == 0)
{
lean_ctor_set(v___x_703_, 0, v_val_711_);
v___x_713_ = v___x_703_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_714_; 
v_reuseFailAlloc_714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_714_, 0, v_val_711_);
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
v_a_716_ = lean_ctor_get(v___x_700_, 0);
v_isSharedCheck_723_ = !lean_is_exclusive(v___x_700_);
if (v_isSharedCheck_723_ == 0)
{
v___x_718_ = v___x_700_;
v_isShared_719_ = v_isSharedCheck_723_;
goto v_resetjp_717_;
}
else
{
lean_inc(v_a_716_);
lean_dec(v___x_700_);
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
v___jp_686_:
{
uint8_t v___x_687_; lean_object* v___x_688_; lean_object* v___x_690_; 
v___x_687_ = 0;
v___x_688_ = lean_box(v___x_687_);
if (v_isShared_685_ == 0)
{
lean_ctor_set(v___x_684_, 0, v___x_688_);
v___x_690_ = v___x_684_;
goto v_reusejp_689_;
}
else
{
lean_object* v_reuseFailAlloc_691_; 
v_reuseFailAlloc_691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_691_, 0, v___x_688_);
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
lean_object* v_a_725_; lean_object* v___x_727_; uint8_t v_isShared_728_; uint8_t v_isSharedCheck_732_; 
v_a_725_ = lean_ctor_get(v___x_681_, 0);
v_isSharedCheck_732_ = !lean_is_exclusive(v___x_681_);
if (v_isSharedCheck_732_ == 0)
{
v___x_727_ = v___x_681_;
v_isShared_728_ = v_isSharedCheck_732_;
goto v_resetjp_726_;
}
else
{
lean_inc(v_a_725_);
lean_dec(v___x_681_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent___boxed(lean_object* v_e_733_, lean_object* v_parent_734_, lean_object* v_a_735_, lean_object* v_a_736_, lean_object* v_a_737_, lean_object* v_a_738_, lean_object* v_a_739_, lean_object* v_a_740_, lean_object* v_a_741_, lean_object* v_a_742_, lean_object* v_a_743_, lean_object* v_a_744_, lean_object* v_a_745_){
_start:
{
lean_object* v_res_746_; 
v_res_746_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent(v_e_733_, v_parent_734_, v_a_735_, v_a_736_, v_a_737_, v_a_738_, v_a_739_, v_a_740_, v_a_741_, v_a_742_, v_a_743_, v_a_744_);
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
lean_dec_ref(v_e_733_);
return v_res_746_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0(lean_object* v_e_747_, lean_object* v_b_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_){
_start:
{
lean_object* v___x_760_; 
v___x_760_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg(v_e_747_, v_b_748_, v___y_749_, v___y_756_);
return v___x_760_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___boxed(lean_object* v_e_761_, lean_object* v_b_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_){
_start:
{
lean_object* v_res_774_; 
v_res_774_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0(v_e_761_, v_b_762_, v___y_763_, v___y_764_, v___y_765_, v___y_766_, v___y_767_, v___y_768_, v___y_769_, v___y_770_, v___y_771_, v___y_772_);
lean_dec(v___y_772_);
lean_dec_ref(v___y_771_);
lean_dec(v___y_770_);
lean_dec_ref(v___y_769_);
lean_dec(v___y_768_);
lean_dec_ref(v___y_767_);
lean_dec(v___y_766_);
lean_dec_ref(v___y_765_);
lean_dec(v___y_764_);
lean_dec(v___y_763_);
lean_dec_ref(v_e_761_);
return v_res_774_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__0___closed__0(void){
_start:
{
lean_object* v___x_775_; 
v___x_775_ = l_Lean_Meta_Grind_instInhabitedGoalM(lean_box(0));
return v___x_775_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__0(lean_object* v_msg_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_){
_start:
{
lean_object* v___x_788_; lean_object* v___x_60568__overap_789_; lean_object* v___x_790_; 
v___x_788_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__0___closed__0, &l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__0___closed__0);
v___x_60568__overap_789_ = lean_panic_fn(v___x_788_, v_msg_776_);
v___x_790_ = lean_apply_11(v___x_60568__overap_789_, v___y_777_, v___y_778_, v___y_779_, v___y_780_, v___y_781_, v___y_782_, v___y_783_, v___y_784_, v___y_785_, v___y_786_, lean_box(0));
return v___x_790_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__0___boxed(lean_object* v_msg_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_){
_start:
{
lean_object* v_res_803_; 
v_res_803_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__0(v_msg_791_, v___y_792_, v___y_793_, v___y_794_, v___y_795_, v___y_796_, v___y_797_, v___y_798_, v___y_799_, v___y_800_, v___y_801_);
return v_res_803_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__1_spec__1(lean_object* v_msgData_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_){
_start:
{
lean_object* v___x_810_; lean_object* v_env_811_; lean_object* v___x_812_; lean_object* v_mctx_813_; lean_object* v_lctx_814_; lean_object* v_options_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; 
v___x_810_ = lean_st_ref_get(v___y_808_);
v_env_811_ = lean_ctor_get(v___x_810_, 0);
lean_inc_ref(v_env_811_);
lean_dec(v___x_810_);
v___x_812_ = lean_st_ref_get(v___y_806_);
v_mctx_813_ = lean_ctor_get(v___x_812_, 0);
lean_inc_ref(v_mctx_813_);
lean_dec(v___x_812_);
v_lctx_814_ = lean_ctor_get(v___y_805_, 2);
v_options_815_ = lean_ctor_get(v___y_807_, 2);
lean_inc_ref(v_options_815_);
lean_inc_ref(v_lctx_814_);
v___x_816_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_816_, 0, v_env_811_);
lean_ctor_set(v___x_816_, 1, v_mctx_813_);
lean_ctor_set(v___x_816_, 2, v_lctx_814_);
lean_ctor_set(v___x_816_, 3, v_options_815_);
v___x_817_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_817_, 0, v___x_816_);
lean_ctor_set(v___x_817_, 1, v_msgData_804_);
v___x_818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_818_, 0, v___x_817_);
return v___x_818_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__1_spec__1___boxed(lean_object* v_msgData_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_){
_start:
{
lean_object* v_res_825_; 
v_res_825_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__1_spec__1(v_msgData_819_, v___y_820_, v___y_821_, v___y_822_, v___y_823_);
lean_dec(v___y_823_);
lean_dec_ref(v___y_822_);
lean_dec(v___y_821_);
lean_dec_ref(v___y_820_);
return v_res_825_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__1___redArg(lean_object* v_msg_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_){
_start:
{
lean_object* v_ref_832_; lean_object* v___x_833_; lean_object* v_a_834_; lean_object* v___x_836_; uint8_t v_isShared_837_; uint8_t v_isSharedCheck_842_; 
v_ref_832_ = lean_ctor_get(v___y_829_, 5);
v___x_833_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__1_spec__1(v_msg_826_, v___y_827_, v___y_828_, v___y_829_, v___y_830_);
v_a_834_ = lean_ctor_get(v___x_833_, 0);
v_isSharedCheck_842_ = !lean_is_exclusive(v___x_833_);
if (v_isSharedCheck_842_ == 0)
{
v___x_836_ = v___x_833_;
v_isShared_837_ = v_isSharedCheck_842_;
goto v_resetjp_835_;
}
else
{
lean_inc(v_a_834_);
lean_dec(v___x_833_);
v___x_836_ = lean_box(0);
v_isShared_837_ = v_isSharedCheck_842_;
goto v_resetjp_835_;
}
v_resetjp_835_:
{
lean_object* v___x_838_; lean_object* v___x_840_; 
lean_inc(v_ref_832_);
v___x_838_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_838_, 0, v_ref_832_);
lean_ctor_set(v___x_838_, 1, v_a_834_);
if (v_isShared_837_ == 0)
{
lean_ctor_set_tag(v___x_836_, 1);
lean_ctor_set(v___x_836_, 0, v___x_838_);
v___x_840_ = v___x_836_;
goto v_reusejp_839_;
}
else
{
lean_object* v_reuseFailAlloc_841_; 
v_reuseFailAlloc_841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_841_, 0, v___x_838_);
v___x_840_ = v_reuseFailAlloc_841_;
goto v_reusejp_839_;
}
v_reusejp_839_:
{
return v___x_840_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__1___redArg___boxed(lean_object* v_msg_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_){
_start:
{
lean_object* v_res_849_; 
v_res_849_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__1___redArg(v_msg_843_, v___y_844_, v___y_845_, v___y_846_, v___y_847_);
lean_dec(v___y_847_);
lean_dec_ref(v___y_846_);
lean_dec(v___y_845_);
lean_dec_ref(v___y_844_);
return v_res_849_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__2___redArg(lean_object* v_e_850_, uint8_t v_a_851_, lean_object* v_as_852_, size_t v_sz_853_, size_t v_i_854_, uint8_t v_b_855_, lean_object* v___y_856_){
_start:
{
uint8_t v___x_858_; 
v___x_858_ = lean_usize_dec_lt(v_i_854_, v_sz_853_);
if (v___x_858_ == 0)
{
lean_object* v___x_859_; lean_object* v___x_860_; 
v___x_859_ = lean_box(v_b_855_);
v___x_860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_860_, 0, v___x_859_);
return v___x_860_;
}
else
{
lean_object* v_a_861_; lean_object* v___x_862_; 
v_a_861_ = lean_array_uget_borrowed(v_as_852_, v_i_854_);
v___x_862_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkChild___redArg(v_e_850_, v_a_861_, v___y_856_);
if (lean_obj_tag(v___x_862_) == 0)
{
lean_object* v_a_863_; lean_object* v___x_865_; uint8_t v_isShared_866_; uint8_t v_isSharedCheck_875_; 
v_a_863_ = lean_ctor_get(v___x_862_, 0);
v_isSharedCheck_875_ = !lean_is_exclusive(v___x_862_);
if (v_isSharedCheck_875_ == 0)
{
v___x_865_ = v___x_862_;
v_isShared_866_ = v_isSharedCheck_875_;
goto v_resetjp_864_;
}
else
{
lean_inc(v_a_863_);
lean_dec(v___x_862_);
v___x_865_ = lean_box(0);
v_isShared_866_ = v_isSharedCheck_875_;
goto v_resetjp_864_;
}
v_resetjp_864_:
{
uint8_t v___x_867_; 
v___x_867_ = lean_unbox(v_a_863_);
lean_dec(v_a_863_);
if (v___x_867_ == 0)
{
size_t v___x_868_; size_t v___x_869_; 
lean_del_object(v___x_865_);
v___x_868_ = ((size_t)1ULL);
v___x_869_ = lean_usize_add(v_i_854_, v___x_868_);
v_i_854_ = v___x_869_;
goto _start;
}
else
{
lean_object* v___x_871_; lean_object* v___x_873_; 
v___x_871_ = lean_box(v_a_851_);
if (v_isShared_866_ == 0)
{
lean_ctor_set(v___x_865_, 0, v___x_871_);
v___x_873_ = v___x_865_;
goto v_reusejp_872_;
}
else
{
lean_object* v_reuseFailAlloc_874_; 
v_reuseFailAlloc_874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_874_, 0, v___x_871_);
v___x_873_ = v_reuseFailAlloc_874_;
goto v_reusejp_872_;
}
v_reusejp_872_:
{
return v___x_873_;
}
}
}
}
else
{
return v___x_862_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__2___redArg___boxed(lean_object* v_e_876_, lean_object* v_a_877_, lean_object* v_as_878_, lean_object* v_sz_879_, lean_object* v_i_880_, lean_object* v_b_881_, lean_object* v___y_882_, lean_object* v___y_883_){
_start:
{
uint8_t v_a_67300__boxed_884_; size_t v_sz_boxed_885_; size_t v_i_boxed_886_; uint8_t v_b_boxed_887_; lean_object* v_res_888_; 
v_a_67300__boxed_884_ = lean_unbox(v_a_877_);
v_sz_boxed_885_ = lean_unbox_usize(v_sz_879_);
lean_dec(v_sz_879_);
v_i_boxed_886_ = lean_unbox_usize(v_i_880_);
lean_dec(v_i_880_);
v_b_boxed_887_ = lean_unbox(v_b_881_);
v_res_888_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__2___redArg(v_e_876_, v_a_67300__boxed_884_, v_as_878_, v_sz_boxed_885_, v_i_boxed_886_, v_b_boxed_887_, v___y_882_);
lean_dec(v___y_882_);
lean_dec_ref(v_as_878_);
lean_dec_ref(v_e_876_);
return v_res_888_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__2(void){
_start:
{
lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; 
v___x_891_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__1));
v___x_892_ = lean_unsigned_to_nat(10u);
v___x_893_ = lean_unsigned_to_nat(73u);
v___x_894_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__0));
v___x_895_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___closed__0));
v___x_896_ = l_mkPanicMessageWithDecl(v___x_895_, v___x_894_, v___x_893_, v___x_892_, v___x_891_);
return v___x_896_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__4(void){
_start:
{
lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; 
v___x_898_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__3));
v___x_899_ = lean_unsigned_to_nat(12u);
v___x_900_ = lean_unsigned_to_nat(91u);
v___x_901_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__0));
v___x_902_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___closed__0));
v___x_903_ = l_mkPanicMessageWithDecl(v___x_902_, v___x_901_, v___x_900_, v___x_899_, v___x_898_);
return v___x_903_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__6(void){
_start:
{
lean_object* v___x_905_; lean_object* v___x_906_; 
v___x_905_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__5));
v___x_906_ = l_Lean_stringToMessageData(v___x_905_);
return v___x_906_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__8(void){
_start:
{
lean_object* v___x_908_; lean_object* v___x_909_; 
v___x_908_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__7));
v___x_909_ = l_Lean_stringToMessageData(v___x_908_);
return v___x_909_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__9(void){
_start:
{
lean_object* v___x_910_; lean_object* v_dummy_911_; 
v___x_910_ = lean_box(0);
v_dummy_911_ = l_Lean_Expr_sort___override(v___x_910_);
return v_dummy_911_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg(lean_object* v_e_912_, uint8_t v_a_913_, lean_object* v_as_x27_914_, lean_object* v_b_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_){
_start:
{
if (lean_obj_tag(v_as_x27_914_) == 0)
{
lean_object* v___x_927_; 
lean_dec(v___y_925_);
lean_dec_ref(v___y_924_);
lean_dec(v___y_923_);
lean_dec_ref(v___y_922_);
lean_dec(v___y_921_);
lean_dec_ref(v___y_920_);
lean_dec(v___y_919_);
lean_dec_ref(v___y_918_);
lean_dec(v___y_917_);
lean_dec(v___y_916_);
lean_dec_ref(v_e_912_);
v___x_927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_927_, 0, v_b_915_);
return v___x_927_;
}
else
{
lean_object* v_head_928_; lean_object* v_tail_929_; lean_object* v___x_931_; uint8_t v_isShared_932_; uint8_t v_isSharedCheck_1088_; 
v_head_928_ = lean_ctor_get(v_as_x27_914_, 0);
v_tail_929_ = lean_ctor_get(v_as_x27_914_, 1);
v_isSharedCheck_1088_ = !lean_is_exclusive(v_as_x27_914_);
if (v_isSharedCheck_1088_ == 0)
{
v___x_931_ = v_as_x27_914_;
v_isShared_932_ = v_isSharedCheck_1088_;
goto v_resetjp_930_;
}
else
{
lean_inc(v_tail_929_);
lean_inc(v_head_928_);
lean_dec(v_as_x27_914_);
v___x_931_ = lean_box(0);
v_isShared_932_ = v_isSharedCheck_1088_;
goto v_resetjp_930_;
}
v_resetjp_930_:
{
lean_object* v___y_934_; lean_object* v___x_954_; lean_object* v___y_956_; lean_object* v___y_957_; lean_object* v___y_958_; lean_object* v___y_959_; lean_object* v___y_960_; lean_object* v___y_961_; lean_object* v___y_962_; lean_object* v___y_963_; lean_object* v___y_964_; lean_object* v___y_965_; lean_object* v___y_981_; lean_object* v___y_982_; lean_object* v___y_983_; lean_object* v___y_984_; lean_object* v___y_985_; lean_object* v___y_986_; lean_object* v___y_987_; lean_object* v___y_988_; lean_object* v___y_989_; lean_object* v___y_990_; lean_object* v___y_991_; uint8_t v_found_999_; lean_object* v___y_1000_; lean_object* v___y_1001_; lean_object* v___y_1002_; lean_object* v___y_1003_; lean_object* v___y_1004_; lean_object* v___y_1005_; lean_object* v___y_1006_; lean_object* v___y_1007_; lean_object* v___y_1008_; lean_object* v___y_1009_; uint8_t v___x_1025_; 
v___x_954_ = lean_box(0);
v___x_1025_ = l_Lean_Meta_Grind_isMatchCond(v_head_928_);
if (v___x_1025_ == 0)
{
lean_object* v_dummy_1026_; lean_object* v_nargs_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; size_t v_sz_1032_; size_t v___x_1033_; lean_object* v___x_1034_; 
v_dummy_1026_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__9, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__9_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__9);
v_nargs_1027_ = l_Lean_Expr_getAppNumArgs(v_head_928_);
lean_inc(v_nargs_1027_);
v___x_1028_ = lean_mk_array(v_nargs_1027_, v_dummy_1026_);
v___x_1029_ = lean_unsigned_to_nat(1u);
v___x_1030_ = lean_nat_sub(v_nargs_1027_, v___x_1029_);
lean_dec(v_nargs_1027_);
lean_inc(v_head_928_);
v___x_1031_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_head_928_, v___x_1028_, v___x_1030_);
v_sz_1032_ = lean_array_size(v___x_1031_);
v___x_1033_ = ((size_t)0ULL);
v___x_1034_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__2___redArg(v_e_912_, v_a_913_, v___x_1031_, v_sz_1032_, v___x_1033_, v___x_1025_, v___y_916_);
lean_dec_ref(v___x_1031_);
if (lean_obj_tag(v___x_1034_) == 0)
{
if (lean_obj_tag(v_head_928_) == 7)
{
lean_object* v_a_1035_; lean_object* v_binderType_1036_; lean_object* v_body_1037_; lean_object* v___x_1038_; lean_object* v_a_1039_; uint8_t v_found_1041_; lean_object* v___y_1042_; lean_object* v___y_1043_; lean_object* v___y_1044_; lean_object* v___y_1045_; lean_object* v___y_1046_; lean_object* v___y_1047_; lean_object* v___y_1048_; lean_object* v___y_1049_; lean_object* v___y_1050_; lean_object* v___y_1051_; uint8_t v___x_1057_; 
v_a_1035_ = lean_ctor_get(v___x_1034_, 0);
lean_inc(v_a_1035_);
lean_dec_ref(v___x_1034_);
v_binderType_1036_ = lean_ctor_get(v_head_928_, 1);
v_body_1037_ = lean_ctor_get(v_head_928_, 2);
v___x_1038_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkChild___redArg(v_e_912_, v_binderType_1036_, v___y_916_);
v_a_1039_ = lean_ctor_get(v___x_1038_, 0);
lean_inc(v_a_1039_);
lean_dec_ref(v___x_1038_);
v___x_1057_ = lean_unbox(v_a_1039_);
lean_dec(v_a_1039_);
if (v___x_1057_ == 0)
{
uint8_t v___x_1058_; 
v___x_1058_ = lean_unbox(v_a_1035_);
lean_dec(v_a_1035_);
lean_inc(v___y_925_);
lean_inc_ref(v___y_924_);
lean_inc(v___y_923_);
lean_inc_ref(v___y_922_);
lean_inc(v___y_921_);
lean_inc_ref(v___y_920_);
lean_inc(v___y_919_);
lean_inc_ref(v___y_918_);
lean_inc(v___y_917_);
lean_inc(v___y_916_);
v_found_1041_ = v___x_1058_;
v___y_1042_ = v___y_916_;
v___y_1043_ = v___y_917_;
v___y_1044_ = v___y_918_;
v___y_1045_ = v___y_919_;
v___y_1046_ = v___y_920_;
v___y_1047_ = v___y_921_;
v___y_1048_ = v___y_922_;
v___y_1049_ = v___y_923_;
v___y_1050_ = v___y_924_;
v___y_1051_ = v___y_925_;
goto v___jp_1040_;
}
else
{
lean_dec(v_a_1035_);
lean_inc(v___y_925_);
lean_inc_ref(v___y_924_);
lean_inc(v___y_923_);
lean_inc_ref(v___y_922_);
lean_inc(v___y_921_);
lean_inc_ref(v___y_920_);
lean_inc(v___y_919_);
lean_inc_ref(v___y_918_);
lean_inc(v___y_917_);
lean_inc(v___y_916_);
v_found_1041_ = v_a_913_;
v___y_1042_ = v___y_916_;
v___y_1043_ = v___y_917_;
v___y_1044_ = v___y_918_;
v___y_1045_ = v___y_919_;
v___y_1046_ = v___y_920_;
v___y_1047_ = v___y_921_;
v___y_1048_ = v___y_922_;
v___y_1049_ = v___y_923_;
v___y_1050_ = v___y_924_;
v___y_1051_ = v___y_925_;
goto v___jp_1040_;
}
v___jp_1040_:
{
uint8_t v___x_1052_; 
v___x_1052_ = l_Lean_Expr_hasLooseBVars(v_body_1037_);
if (v___x_1052_ == 0)
{
lean_object* v___x_1053_; lean_object* v_a_1054_; uint8_t v___x_1055_; 
v___x_1053_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkChild___redArg(v_e_912_, v_body_1037_, v___y_1042_);
v_a_1054_ = lean_ctor_get(v___x_1053_, 0);
lean_inc(v_a_1054_);
lean_dec_ref(v___x_1053_);
v___x_1055_ = lean_unbox(v_a_1054_);
lean_dec(v_a_1054_);
if (v___x_1055_ == 0)
{
v_found_999_ = v_found_1041_;
v___y_1000_ = v___y_1042_;
v___y_1001_ = v___y_1043_;
v___y_1002_ = v___y_1044_;
v___y_1003_ = v___y_1045_;
v___y_1004_ = v___y_1046_;
v___y_1005_ = v___y_1047_;
v___y_1006_ = v___y_1048_;
v___y_1007_ = v___y_1049_;
v___y_1008_ = v___y_1050_;
v___y_1009_ = v___y_1051_;
goto v___jp_998_;
}
else
{
lean_dec(v___y_1051_);
lean_dec_ref(v___y_1050_);
lean_dec(v___y_1049_);
lean_dec_ref(v___y_1048_);
lean_dec(v___y_1047_);
lean_dec_ref(v___y_1046_);
lean_dec(v___y_1045_);
lean_dec_ref(v___y_1044_);
lean_dec(v___y_1043_);
lean_dec(v___y_1042_);
lean_dec_ref(v_head_928_);
lean_del_object(v___x_931_);
v_as_x27_914_ = v_tail_929_;
v_b_915_ = v___x_954_;
goto _start;
}
}
else
{
v_found_999_ = v_found_1041_;
v___y_1000_ = v___y_1042_;
v___y_1001_ = v___y_1043_;
v___y_1002_ = v___y_1044_;
v___y_1003_ = v___y_1045_;
v___y_1004_ = v___y_1046_;
v___y_1005_ = v___y_1047_;
v___y_1006_ = v___y_1048_;
v___y_1007_ = v___y_1049_;
v___y_1008_ = v___y_1050_;
v___y_1009_ = v___y_1051_;
goto v___jp_998_;
}
}
}
else
{
lean_object* v_a_1059_; uint8_t v___x_1060_; 
v_a_1059_ = lean_ctor_get(v___x_1034_, 0);
lean_inc(v_a_1059_);
lean_dec_ref(v___x_1034_);
v___x_1060_ = lean_unbox(v_a_1059_);
lean_dec(v_a_1059_);
lean_inc(v___y_925_);
lean_inc_ref(v___y_924_);
lean_inc(v___y_923_);
lean_inc_ref(v___y_922_);
lean_inc(v___y_921_);
lean_inc_ref(v___y_920_);
lean_inc(v___y_919_);
lean_inc_ref(v___y_918_);
lean_inc(v___y_917_);
lean_inc(v___y_916_);
v_found_999_ = v___x_1060_;
v___y_1000_ = v___y_916_;
v___y_1001_ = v___y_917_;
v___y_1002_ = v___y_918_;
v___y_1003_ = v___y_919_;
v___y_1004_ = v___y_920_;
v___y_1005_ = v___y_921_;
v___y_1006_ = v___y_922_;
v___y_1007_ = v___y_923_;
v___y_1008_ = v___y_924_;
v___y_1009_ = v___y_925_;
goto v___jp_998_;
}
}
else
{
lean_object* v_a_1061_; lean_object* v___x_1063_; uint8_t v_isShared_1064_; uint8_t v_isSharedCheck_1068_; 
lean_del_object(v___x_931_);
lean_dec(v_tail_929_);
lean_dec(v_head_928_);
lean_dec(v___y_925_);
lean_dec_ref(v___y_924_);
lean_dec(v___y_923_);
lean_dec_ref(v___y_922_);
lean_dec(v___y_921_);
lean_dec_ref(v___y_920_);
lean_dec(v___y_919_);
lean_dec_ref(v___y_918_);
lean_dec(v___y_917_);
lean_dec(v___y_916_);
lean_dec_ref(v_e_912_);
v_a_1061_ = lean_ctor_get(v___x_1034_, 0);
v_isSharedCheck_1068_ = !lean_is_exclusive(v___x_1034_);
if (v_isSharedCheck_1068_ == 0)
{
v___x_1063_ = v___x_1034_;
v_isShared_1064_ = v_isSharedCheck_1068_;
goto v_resetjp_1062_;
}
else
{
lean_inc(v_a_1061_);
lean_dec(v___x_1034_);
v___x_1063_ = lean_box(0);
v_isShared_1064_ = v_isSharedCheck_1068_;
goto v_resetjp_1062_;
}
v_resetjp_1062_:
{
lean_object* v___x_1066_; 
if (v_isShared_1064_ == 0)
{
v___x_1066_ = v___x_1063_;
goto v_reusejp_1065_;
}
else
{
lean_object* v_reuseFailAlloc_1067_; 
v_reuseFailAlloc_1067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1067_, 0, v_a_1061_);
v___x_1066_ = v_reuseFailAlloc_1067_;
goto v_reusejp_1065_;
}
v_reusejp_1065_:
{
return v___x_1066_;
}
}
}
}
else
{
lean_object* v___x_1069_; 
lean_del_object(v___x_931_);
lean_inc(v_head_928_);
v___x_1069_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent(v_e_912_, v_head_928_, v___y_916_, v___y_917_, v___y_918_, v___y_919_, v___y_920_, v___y_921_, v___y_922_, v___y_923_, v___y_924_, v___y_925_);
if (lean_obj_tag(v___x_1069_) == 0)
{
lean_object* v_a_1070_; uint8_t v___x_1071_; 
v_a_1070_ = lean_ctor_get(v___x_1069_, 0);
lean_inc(v_a_1070_);
lean_dec_ref(v___x_1069_);
v___x_1071_ = lean_unbox(v_a_1070_);
lean_dec(v_a_1070_);
if (v___x_1071_ == 0)
{
lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; 
lean_dec(v_tail_929_);
lean_dec(v___y_921_);
lean_dec_ref(v___y_920_);
lean_dec(v___y_919_);
lean_dec_ref(v___y_918_);
lean_dec(v___y_917_);
lean_dec(v___y_916_);
v___x_1072_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__6, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__6_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__6);
v___x_1073_ = l_Lean_MessageData_ofExpr(v_e_912_);
v___x_1074_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1074_, 0, v___x_1072_);
lean_ctor_set(v___x_1074_, 1, v___x_1073_);
v___x_1075_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__8, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__8_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__8);
v___x_1076_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1076_, 0, v___x_1074_);
lean_ctor_set(v___x_1076_, 1, v___x_1075_);
v___x_1077_ = l_Lean_MessageData_ofExpr(v_head_928_);
v___x_1078_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1078_, 0, v___x_1076_);
lean_ctor_set(v___x_1078_, 1, v___x_1077_);
v___x_1079_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__1___redArg(v___x_1078_, v___y_922_, v___y_923_, v___y_924_, v___y_925_);
lean_dec(v___y_925_);
lean_dec_ref(v___y_924_);
lean_dec(v___y_923_);
lean_dec_ref(v___y_922_);
return v___x_1079_;
}
else
{
lean_inc(v___y_925_);
lean_inc_ref(v___y_924_);
lean_inc(v___y_923_);
lean_inc_ref(v___y_922_);
lean_inc(v___y_921_);
lean_inc_ref(v___y_920_);
lean_inc(v___y_919_);
lean_inc_ref(v___y_918_);
lean_inc(v___y_917_);
lean_inc(v___y_916_);
v___y_956_ = v___y_916_;
v___y_957_ = v___y_917_;
v___y_958_ = v___y_918_;
v___y_959_ = v___y_919_;
v___y_960_ = v___y_920_;
v___y_961_ = v___y_921_;
v___y_962_ = v___y_922_;
v___y_963_ = v___y_923_;
v___y_964_ = v___y_924_;
v___y_965_ = v___y_925_;
goto v___jp_955_;
}
}
else
{
lean_object* v_a_1080_; lean_object* v___x_1082_; uint8_t v_isShared_1083_; uint8_t v_isSharedCheck_1087_; 
lean_dec(v_tail_929_);
lean_dec(v_head_928_);
lean_dec(v___y_925_);
lean_dec_ref(v___y_924_);
lean_dec(v___y_923_);
lean_dec_ref(v___y_922_);
lean_dec(v___y_921_);
lean_dec_ref(v___y_920_);
lean_dec(v___y_919_);
lean_dec_ref(v___y_918_);
lean_dec(v___y_917_);
lean_dec(v___y_916_);
lean_dec_ref(v_e_912_);
v_a_1080_ = lean_ctor_get(v___x_1069_, 0);
v_isSharedCheck_1087_ = !lean_is_exclusive(v___x_1069_);
if (v_isSharedCheck_1087_ == 0)
{
v___x_1082_ = v___x_1069_;
v_isShared_1083_ = v_isSharedCheck_1087_;
goto v_resetjp_1081_;
}
else
{
lean_inc(v_a_1080_);
lean_dec(v___x_1069_);
v___x_1082_ = lean_box(0);
v_isShared_1083_ = v_isSharedCheck_1087_;
goto v_resetjp_1081_;
}
v_resetjp_1081_:
{
lean_object* v___x_1085_; 
if (v_isShared_1083_ == 0)
{
v___x_1085_ = v___x_1082_;
goto v_reusejp_1084_;
}
else
{
lean_object* v_reuseFailAlloc_1086_; 
v_reuseFailAlloc_1086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1086_, 0, v_a_1080_);
v___x_1085_ = v_reuseFailAlloc_1086_;
goto v_reusejp_1084_;
}
v_reusejp_1084_:
{
return v___x_1085_;
}
}
}
}
v___jp_933_:
{
if (lean_obj_tag(v___y_934_) == 0)
{
lean_object* v_a_935_; lean_object* v___x_937_; uint8_t v_isShared_938_; uint8_t v_isSharedCheck_945_; 
v_a_935_ = lean_ctor_get(v___y_934_, 0);
v_isSharedCheck_945_ = !lean_is_exclusive(v___y_934_);
if (v_isSharedCheck_945_ == 0)
{
v___x_937_ = v___y_934_;
v_isShared_938_ = v_isSharedCheck_945_;
goto v_resetjp_936_;
}
else
{
lean_inc(v_a_935_);
lean_dec(v___y_934_);
v___x_937_ = lean_box(0);
v_isShared_938_ = v_isSharedCheck_945_;
goto v_resetjp_936_;
}
v_resetjp_936_:
{
if (lean_obj_tag(v_a_935_) == 0)
{
lean_object* v_a_939_; lean_object* v___x_941_; 
lean_dec(v_tail_929_);
lean_dec(v___y_925_);
lean_dec_ref(v___y_924_);
lean_dec(v___y_923_);
lean_dec_ref(v___y_922_);
lean_dec(v___y_921_);
lean_dec_ref(v___y_920_);
lean_dec(v___y_919_);
lean_dec_ref(v___y_918_);
lean_dec(v___y_917_);
lean_dec(v___y_916_);
lean_dec_ref(v_e_912_);
v_a_939_ = lean_ctor_get(v_a_935_, 0);
lean_inc(v_a_939_);
lean_dec_ref(v_a_935_);
if (v_isShared_938_ == 0)
{
lean_ctor_set(v___x_937_, 0, v_a_939_);
v___x_941_ = v___x_937_;
goto v_reusejp_940_;
}
else
{
lean_object* v_reuseFailAlloc_942_; 
v_reuseFailAlloc_942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_942_, 0, v_a_939_);
v___x_941_ = v_reuseFailAlloc_942_;
goto v_reusejp_940_;
}
v_reusejp_940_:
{
return v___x_941_;
}
}
else
{
lean_object* v_a_943_; 
lean_del_object(v___x_937_);
v_a_943_ = lean_ctor_get(v_a_935_, 0);
lean_inc(v_a_943_);
lean_dec_ref(v_a_935_);
v_as_x27_914_ = v_tail_929_;
v_b_915_ = v_a_943_;
goto _start;
}
}
}
else
{
lean_object* v_a_946_; lean_object* v___x_948_; uint8_t v_isShared_949_; uint8_t v_isSharedCheck_953_; 
lean_dec(v_tail_929_);
lean_dec(v___y_925_);
lean_dec_ref(v___y_924_);
lean_dec(v___y_923_);
lean_dec_ref(v___y_922_);
lean_dec(v___y_921_);
lean_dec_ref(v___y_920_);
lean_dec(v___y_919_);
lean_dec_ref(v___y_918_);
lean_dec(v___y_917_);
lean_dec(v___y_916_);
lean_dec_ref(v_e_912_);
v_a_946_ = lean_ctor_get(v___y_934_, 0);
v_isSharedCheck_953_ = !lean_is_exclusive(v___y_934_);
if (v_isSharedCheck_953_ == 0)
{
v___x_948_ = v___y_934_;
v_isShared_949_ = v_isSharedCheck_953_;
goto v_resetjp_947_;
}
else
{
lean_inc(v_a_946_);
lean_dec(v___y_934_);
v___x_948_ = lean_box(0);
v_isShared_949_ = v_isSharedCheck_953_;
goto v_resetjp_947_;
}
v_resetjp_947_:
{
lean_object* v___x_951_; 
if (v_isShared_949_ == 0)
{
v___x_951_ = v___x_948_;
goto v_reusejp_950_;
}
else
{
lean_object* v_reuseFailAlloc_952_; 
v_reuseFailAlloc_952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_952_, 0, v_a_946_);
v___x_951_ = v_reuseFailAlloc_952_;
goto v_reusejp_950_;
}
v_reusejp_950_:
{
return v___x_951_;
}
}
}
}
v___jp_955_:
{
lean_object* v___x_966_; 
v___x_966_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent(v_e_912_, v_head_928_, v___y_956_, v___y_957_, v___y_958_, v___y_959_, v___y_960_, v___y_961_, v___y_962_, v___y_963_, v___y_964_, v___y_965_);
if (lean_obj_tag(v___x_966_) == 0)
{
lean_object* v_a_967_; uint8_t v___x_968_; 
v_a_967_ = lean_ctor_get(v___x_966_, 0);
lean_inc(v_a_967_);
lean_dec_ref(v___x_966_);
v___x_968_ = lean_unbox(v_a_967_);
lean_dec(v_a_967_);
if (v___x_968_ == 0)
{
lean_object* v___x_969_; lean_object* v___x_970_; 
v___x_969_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__2, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__2_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__2);
v___x_970_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__0(v___x_969_, v___y_956_, v___y_957_, v___y_958_, v___y_959_, v___y_960_, v___y_961_, v___y_962_, v___y_963_, v___y_964_, v___y_965_);
v___y_934_ = v___x_970_;
goto v___jp_933_;
}
else
{
lean_dec(v___y_965_);
lean_dec_ref(v___y_964_);
lean_dec(v___y_963_);
lean_dec_ref(v___y_962_);
lean_dec(v___y_961_);
lean_dec_ref(v___y_960_);
lean_dec(v___y_959_);
lean_dec_ref(v___y_958_);
lean_dec(v___y_957_);
lean_dec(v___y_956_);
v_as_x27_914_ = v_tail_929_;
v_b_915_ = v___x_954_;
goto _start;
}
}
else
{
lean_object* v_a_972_; lean_object* v___x_974_; uint8_t v_isShared_975_; uint8_t v_isSharedCheck_979_; 
lean_dec(v___y_965_);
lean_dec_ref(v___y_964_);
lean_dec(v___y_963_);
lean_dec_ref(v___y_962_);
lean_dec(v___y_961_);
lean_dec_ref(v___y_960_);
lean_dec(v___y_959_);
lean_dec_ref(v___y_958_);
lean_dec(v___y_957_);
lean_dec(v___y_956_);
lean_dec(v_tail_929_);
lean_dec(v___y_925_);
lean_dec_ref(v___y_924_);
lean_dec(v___y_923_);
lean_dec_ref(v___y_922_);
lean_dec(v___y_921_);
lean_dec_ref(v___y_920_);
lean_dec(v___y_919_);
lean_dec_ref(v___y_918_);
lean_dec(v___y_917_);
lean_dec(v___y_916_);
lean_dec_ref(v_e_912_);
v_a_972_ = lean_ctor_get(v___x_966_, 0);
v_isSharedCheck_979_ = !lean_is_exclusive(v___x_966_);
if (v_isSharedCheck_979_ == 0)
{
v___x_974_ = v___x_966_;
v_isShared_975_ = v_isSharedCheck_979_;
goto v_resetjp_973_;
}
else
{
lean_inc(v_a_972_);
lean_dec(v___x_966_);
v___x_974_ = lean_box(0);
v_isShared_975_ = v_isSharedCheck_979_;
goto v_resetjp_973_;
}
v_resetjp_973_:
{
lean_object* v___x_977_; 
if (v_isShared_975_ == 0)
{
v___x_977_ = v___x_974_;
goto v_reusejp_976_;
}
else
{
lean_object* v_reuseFailAlloc_978_; 
v_reuseFailAlloc_978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_978_, 0, v_a_972_);
v___x_977_ = v_reuseFailAlloc_978_;
goto v_reusejp_976_;
}
v_reusejp_976_:
{
return v___x_977_;
}
}
}
}
v___jp_980_:
{
lean_object* v___x_992_; lean_object* v_a_993_; uint8_t v___x_994_; 
v___x_992_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkChild___redArg(v_e_912_, v___y_981_, v___y_982_);
lean_dec_ref(v___y_981_);
v_a_993_ = lean_ctor_get(v___x_992_, 0);
lean_inc(v_a_993_);
lean_dec_ref(v___x_992_);
v___x_994_ = lean_unbox(v_a_993_);
lean_dec(v_a_993_);
if (v___x_994_ == 0)
{
lean_object* v___x_995_; lean_object* v___x_996_; 
v___x_995_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__4, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__4);
v___x_996_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__0(v___x_995_, v___y_982_, v___y_983_, v___y_984_, v___y_985_, v___y_986_, v___y_987_, v___y_988_, v___y_989_, v___y_990_, v___y_991_);
v___y_934_ = v___x_996_;
goto v___jp_933_;
}
else
{
lean_dec(v___y_991_);
lean_dec_ref(v___y_990_);
lean_dec(v___y_989_);
lean_dec_ref(v___y_988_);
lean_dec(v___y_987_);
lean_dec_ref(v___y_986_);
lean_dec(v___y_985_);
lean_dec_ref(v___y_984_);
lean_dec(v___y_983_);
lean_dec(v___y_982_);
v_as_x27_914_ = v_tail_929_;
v_b_915_ = v___x_954_;
goto _start;
}
}
v___jp_998_:
{
if (v_found_999_ == 0)
{
lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v_a_1012_; uint8_t v___x_1013_; 
v___x_1010_ = l_Lean_Expr_getAppFn(v_head_928_);
v___x_1011_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkChild___redArg(v_e_912_, v___x_1010_, v___y_1000_);
v_a_1012_ = lean_ctor_get(v___x_1011_, 0);
lean_inc(v_a_1012_);
lean_dec_ref(v___x_1011_);
v___x_1013_ = lean_unbox(v_a_1012_);
lean_dec(v_a_1012_);
if (v___x_1013_ == 0)
{
lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1017_; 
lean_dec_ref(v___x_1010_);
lean_dec(v___y_1005_);
lean_dec_ref(v___y_1004_);
lean_dec(v___y_1003_);
lean_dec_ref(v___y_1002_);
lean_dec(v___y_1001_);
lean_dec(v___y_1000_);
lean_dec(v_tail_929_);
lean_dec(v___y_925_);
lean_dec_ref(v___y_924_);
lean_dec(v___y_923_);
lean_dec_ref(v___y_922_);
lean_dec(v___y_921_);
lean_dec_ref(v___y_920_);
lean_dec(v___y_919_);
lean_dec_ref(v___y_918_);
lean_dec(v___y_917_);
lean_dec(v___y_916_);
v___x_1014_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__6, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__6_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__6);
v___x_1015_ = l_Lean_MessageData_ofExpr(v_e_912_);
if (v_isShared_932_ == 0)
{
lean_ctor_set_tag(v___x_931_, 7);
lean_ctor_set(v___x_931_, 1, v___x_1015_);
lean_ctor_set(v___x_931_, 0, v___x_1014_);
v___x_1017_ = v___x_931_;
goto v_reusejp_1016_;
}
else
{
lean_object* v_reuseFailAlloc_1023_; 
v_reuseFailAlloc_1023_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1023_, 0, v___x_1014_);
lean_ctor_set(v_reuseFailAlloc_1023_, 1, v___x_1015_);
v___x_1017_ = v_reuseFailAlloc_1023_;
goto v_reusejp_1016_;
}
v_reusejp_1016_:
{
lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; 
v___x_1018_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__8, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__8_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__8);
v___x_1019_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1019_, 0, v___x_1017_);
lean_ctor_set(v___x_1019_, 1, v___x_1018_);
v___x_1020_ = l_Lean_MessageData_ofExpr(v_head_928_);
v___x_1021_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1021_, 0, v___x_1019_);
lean_ctor_set(v___x_1021_, 1, v___x_1020_);
v___x_1022_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__1___redArg(v___x_1021_, v___y_1006_, v___y_1007_, v___y_1008_, v___y_1009_);
lean_dec(v___y_1009_);
lean_dec_ref(v___y_1008_);
lean_dec(v___y_1007_);
lean_dec_ref(v___y_1006_);
return v___x_1022_;
}
}
else
{
lean_del_object(v___x_931_);
lean_dec(v_head_928_);
v___y_981_ = v___x_1010_;
v___y_982_ = v___y_1000_;
v___y_983_ = v___y_1001_;
v___y_984_ = v___y_1002_;
v___y_985_ = v___y_1003_;
v___y_986_ = v___y_1004_;
v___y_987_ = v___y_1005_;
v___y_988_ = v___y_1006_;
v___y_989_ = v___y_1007_;
v___y_990_ = v___y_1008_;
v___y_991_ = v___y_1009_;
goto v___jp_980_;
}
}
else
{
lean_dec(v___y_1009_);
lean_dec_ref(v___y_1008_);
lean_dec(v___y_1007_);
lean_dec_ref(v___y_1006_);
lean_dec(v___y_1005_);
lean_dec_ref(v___y_1004_);
lean_dec(v___y_1003_);
lean_dec_ref(v___y_1002_);
lean_dec(v___y_1001_);
lean_dec(v___y_1000_);
lean_del_object(v___x_931_);
lean_dec(v_head_928_);
v_as_x27_914_ = v_tail_929_;
v_b_915_ = v___x_954_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___boxed(lean_object* v_e_1089_, lean_object* v_a_1090_, lean_object* v_as_x27_1091_, lean_object* v_b_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_){
_start:
{
uint8_t v_a_67397__boxed_1104_; lean_object* v_res_1105_; 
v_a_67397__boxed_1104_ = lean_unbox(v_a_1090_);
v_res_1105_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg(v_e_1089_, v_a_67397__boxed_1104_, v_as_x27_1091_, v_b_1092_, v___y_1093_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_);
return v_res_1105_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents___closed__1(void){
_start:
{
lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; 
v___x_1107_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents___closed__0));
v___x_1108_ = lean_unsigned_to_nat(6u);
v___x_1109_ = lean_unsigned_to_nat(94u);
v___x_1110_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__0));
v___x_1111_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___closed__0));
v___x_1112_ = l_mkPanicMessageWithDecl(v___x_1111_, v___x_1110_, v___x_1109_, v___x_1108_, v___x_1107_);
return v___x_1112_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents(lean_object* v_e_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_, lean_object* v_a_1117_, lean_object* v_a_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_, lean_object* v_a_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_){
_start:
{
lean_object* v___x_1125_; 
lean_inc_ref(v_e_1113_);
v___x_1125_ = l_Lean_Meta_Grind_useFunCC___redArg(v_e_1113_, v_a_1114_, v_a_1120_, v_a_1121_, v_a_1122_, v_a_1123_);
if (lean_obj_tag(v___x_1125_) == 0)
{
lean_object* v_a_1126_; lean_object* v___x_1128_; uint8_t v_isShared_1129_; uint8_t v_isSharedCheck_1189_; 
v_a_1126_ = lean_ctor_get(v___x_1125_, 0);
v_isSharedCheck_1189_ = !lean_is_exclusive(v___x_1125_);
if (v_isSharedCheck_1189_ == 0)
{
v___x_1128_ = v___x_1125_;
v_isShared_1129_ = v_isSharedCheck_1189_;
goto v_resetjp_1127_;
}
else
{
lean_inc(v_a_1126_);
lean_dec(v___x_1125_);
v___x_1128_ = lean_box(0);
v_isShared_1129_ = v_isSharedCheck_1189_;
goto v_resetjp_1127_;
}
v_resetjp_1127_:
{
uint8_t v___x_1130_; 
v___x_1130_ = lean_unbox(v_a_1126_);
lean_dec(v_a_1126_);
if (v___x_1130_ == 0)
{
lean_object* v___x_1131_; 
lean_del_object(v___x_1128_);
v___x_1131_ = l_Lean_Meta_Grind_isRoot___redArg(v_e_1113_, v_a_1114_);
if (lean_obj_tag(v___x_1131_) == 0)
{
lean_object* v_a_1132_; uint8_t v___x_1133_; 
v_a_1132_ = lean_ctor_get(v___x_1131_, 0);
lean_inc(v_a_1132_);
lean_dec_ref(v___x_1131_);
v___x_1133_ = lean_unbox(v_a_1132_);
if (v___x_1133_ == 0)
{
lean_object* v___x_1134_; 
lean_dec(v_a_1132_);
v___x_1134_ = l_Lean_Meta_Grind_getParents___redArg(v_e_1113_, v_a_1114_);
lean_dec_ref(v_e_1113_);
if (lean_obj_tag(v___x_1134_) == 0)
{
lean_object* v_a_1135_; lean_object* v___x_1137_; uint8_t v_isShared_1138_; uint8_t v_isSharedCheck_1146_; 
v_a_1135_ = lean_ctor_get(v___x_1134_, 0);
v_isSharedCheck_1146_ = !lean_is_exclusive(v___x_1134_);
if (v_isSharedCheck_1146_ == 0)
{
v___x_1137_ = v___x_1134_;
v_isShared_1138_ = v_isSharedCheck_1146_;
goto v_resetjp_1136_;
}
else
{
lean_inc(v_a_1135_);
lean_dec(v___x_1134_);
v___x_1137_ = lean_box(0);
v_isShared_1138_ = v_isSharedCheck_1146_;
goto v_resetjp_1136_;
}
v_resetjp_1136_:
{
uint8_t v___x_1139_; 
v___x_1139_ = l_Lean_Meta_Grind_ParentSet_isEmpty(v_a_1135_);
lean_dec(v_a_1135_);
if (v___x_1139_ == 0)
{
lean_object* v___x_1140_; lean_object* v___x_1141_; 
lean_del_object(v___x_1137_);
v___x_1140_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents___closed__1, &l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents___closed__1);
v___x_1141_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__4(v___x_1140_, v_a_1114_, v_a_1115_, v_a_1116_, v_a_1117_, v_a_1118_, v_a_1119_, v_a_1120_, v_a_1121_, v_a_1122_, v_a_1123_);
return v___x_1141_;
}
else
{
lean_object* v___x_1142_; lean_object* v___x_1144_; 
lean_dec(v_a_1123_);
lean_dec_ref(v_a_1122_);
lean_dec(v_a_1121_);
lean_dec_ref(v_a_1120_);
lean_dec(v_a_1119_);
lean_dec_ref(v_a_1118_);
lean_dec(v_a_1117_);
lean_dec_ref(v_a_1116_);
lean_dec(v_a_1115_);
lean_dec(v_a_1114_);
v___x_1142_ = lean_box(0);
if (v_isShared_1138_ == 0)
{
lean_ctor_set(v___x_1137_, 0, v___x_1142_);
v___x_1144_ = v___x_1137_;
goto v_reusejp_1143_;
}
else
{
lean_object* v_reuseFailAlloc_1145_; 
v_reuseFailAlloc_1145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1145_, 0, v___x_1142_);
v___x_1144_ = v_reuseFailAlloc_1145_;
goto v_reusejp_1143_;
}
v_reusejp_1143_:
{
return v___x_1144_;
}
}
}
}
else
{
lean_object* v_a_1147_; lean_object* v___x_1149_; uint8_t v_isShared_1150_; uint8_t v_isSharedCheck_1154_; 
lean_dec(v_a_1123_);
lean_dec_ref(v_a_1122_);
lean_dec(v_a_1121_);
lean_dec_ref(v_a_1120_);
lean_dec(v_a_1119_);
lean_dec_ref(v_a_1118_);
lean_dec(v_a_1117_);
lean_dec_ref(v_a_1116_);
lean_dec(v_a_1115_);
lean_dec(v_a_1114_);
v_a_1147_ = lean_ctor_get(v___x_1134_, 0);
v_isSharedCheck_1154_ = !lean_is_exclusive(v___x_1134_);
if (v_isSharedCheck_1154_ == 0)
{
v___x_1149_ = v___x_1134_;
v_isShared_1150_ = v_isSharedCheck_1154_;
goto v_resetjp_1148_;
}
else
{
lean_inc(v_a_1147_);
lean_dec(v___x_1134_);
v___x_1149_ = lean_box(0);
v_isShared_1150_ = v_isSharedCheck_1154_;
goto v_resetjp_1148_;
}
v_resetjp_1148_:
{
lean_object* v___x_1152_; 
if (v_isShared_1150_ == 0)
{
v___x_1152_ = v___x_1149_;
goto v_reusejp_1151_;
}
else
{
lean_object* v_reuseFailAlloc_1153_; 
v_reuseFailAlloc_1153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1153_, 0, v_a_1147_);
v___x_1152_ = v_reuseFailAlloc_1153_;
goto v_reusejp_1151_;
}
v_reusejp_1151_:
{
return v___x_1152_;
}
}
}
}
else
{
lean_object* v___x_1155_; 
v___x_1155_ = l_Lean_Meta_Grind_getParents___redArg(v_e_1113_, v_a_1114_);
if (lean_obj_tag(v___x_1155_) == 0)
{
lean_object* v_a_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; uint8_t v___x_1159_; lean_object* v___x_1160_; 
v_a_1156_ = lean_ctor_get(v___x_1155_, 0);
lean_inc(v_a_1156_);
lean_dec_ref(v___x_1155_);
v___x_1157_ = l_Lean_Meta_Grind_ParentSet_elems(v_a_1156_);
lean_dec(v_a_1156_);
v___x_1158_ = lean_box(0);
v___x_1159_ = lean_unbox(v_a_1132_);
lean_dec(v_a_1132_);
v___x_1160_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg(v_e_1113_, v___x_1159_, v___x_1157_, v___x_1158_, v_a_1114_, v_a_1115_, v_a_1116_, v_a_1117_, v_a_1118_, v_a_1119_, v_a_1120_, v_a_1121_, v_a_1122_, v_a_1123_);
if (lean_obj_tag(v___x_1160_) == 0)
{
lean_object* v___x_1162_; uint8_t v_isShared_1163_; uint8_t v_isSharedCheck_1167_; 
v_isSharedCheck_1167_ = !lean_is_exclusive(v___x_1160_);
if (v_isSharedCheck_1167_ == 0)
{
lean_object* v_unused_1168_; 
v_unused_1168_ = lean_ctor_get(v___x_1160_, 0);
lean_dec(v_unused_1168_);
v___x_1162_ = v___x_1160_;
v_isShared_1163_ = v_isSharedCheck_1167_;
goto v_resetjp_1161_;
}
else
{
lean_dec(v___x_1160_);
v___x_1162_ = lean_box(0);
v_isShared_1163_ = v_isSharedCheck_1167_;
goto v_resetjp_1161_;
}
v_resetjp_1161_:
{
lean_object* v___x_1165_; 
if (v_isShared_1163_ == 0)
{
lean_ctor_set(v___x_1162_, 0, v___x_1158_);
v___x_1165_ = v___x_1162_;
goto v_reusejp_1164_;
}
else
{
lean_object* v_reuseFailAlloc_1166_; 
v_reuseFailAlloc_1166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1166_, 0, v___x_1158_);
v___x_1165_ = v_reuseFailAlloc_1166_;
goto v_reusejp_1164_;
}
v_reusejp_1164_:
{
return v___x_1165_;
}
}
}
else
{
return v___x_1160_;
}
}
else
{
lean_object* v_a_1169_; lean_object* v___x_1171_; uint8_t v_isShared_1172_; uint8_t v_isSharedCheck_1176_; 
lean_dec(v_a_1132_);
lean_dec(v_a_1123_);
lean_dec_ref(v_a_1122_);
lean_dec(v_a_1121_);
lean_dec_ref(v_a_1120_);
lean_dec(v_a_1119_);
lean_dec_ref(v_a_1118_);
lean_dec(v_a_1117_);
lean_dec_ref(v_a_1116_);
lean_dec(v_a_1115_);
lean_dec(v_a_1114_);
lean_dec_ref(v_e_1113_);
v_a_1169_ = lean_ctor_get(v___x_1155_, 0);
v_isSharedCheck_1176_ = !lean_is_exclusive(v___x_1155_);
if (v_isSharedCheck_1176_ == 0)
{
v___x_1171_ = v___x_1155_;
v_isShared_1172_ = v_isSharedCheck_1176_;
goto v_resetjp_1170_;
}
else
{
lean_inc(v_a_1169_);
lean_dec(v___x_1155_);
v___x_1171_ = lean_box(0);
v_isShared_1172_ = v_isSharedCheck_1176_;
goto v_resetjp_1170_;
}
v_resetjp_1170_:
{
lean_object* v___x_1174_; 
if (v_isShared_1172_ == 0)
{
v___x_1174_ = v___x_1171_;
goto v_reusejp_1173_;
}
else
{
lean_object* v_reuseFailAlloc_1175_; 
v_reuseFailAlloc_1175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1175_, 0, v_a_1169_);
v___x_1174_ = v_reuseFailAlloc_1175_;
goto v_reusejp_1173_;
}
v_reusejp_1173_:
{
return v___x_1174_;
}
}
}
}
}
else
{
lean_object* v_a_1177_; lean_object* v___x_1179_; uint8_t v_isShared_1180_; uint8_t v_isSharedCheck_1184_; 
lean_dec(v_a_1123_);
lean_dec_ref(v_a_1122_);
lean_dec(v_a_1121_);
lean_dec_ref(v_a_1120_);
lean_dec(v_a_1119_);
lean_dec_ref(v_a_1118_);
lean_dec(v_a_1117_);
lean_dec_ref(v_a_1116_);
lean_dec(v_a_1115_);
lean_dec(v_a_1114_);
lean_dec_ref(v_e_1113_);
v_a_1177_ = lean_ctor_get(v___x_1131_, 0);
v_isSharedCheck_1184_ = !lean_is_exclusive(v___x_1131_);
if (v_isSharedCheck_1184_ == 0)
{
v___x_1179_ = v___x_1131_;
v_isShared_1180_ = v_isSharedCheck_1184_;
goto v_resetjp_1178_;
}
else
{
lean_inc(v_a_1177_);
lean_dec(v___x_1131_);
v___x_1179_ = lean_box(0);
v_isShared_1180_ = v_isSharedCheck_1184_;
goto v_resetjp_1178_;
}
v_resetjp_1178_:
{
lean_object* v___x_1182_; 
if (v_isShared_1180_ == 0)
{
v___x_1182_ = v___x_1179_;
goto v_reusejp_1181_;
}
else
{
lean_object* v_reuseFailAlloc_1183_; 
v_reuseFailAlloc_1183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1183_, 0, v_a_1177_);
v___x_1182_ = v_reuseFailAlloc_1183_;
goto v_reusejp_1181_;
}
v_reusejp_1181_:
{
return v___x_1182_;
}
}
}
}
else
{
lean_object* v___x_1185_; lean_object* v___x_1187_; 
lean_dec(v_a_1123_);
lean_dec_ref(v_a_1122_);
lean_dec(v_a_1121_);
lean_dec_ref(v_a_1120_);
lean_dec(v_a_1119_);
lean_dec_ref(v_a_1118_);
lean_dec(v_a_1117_);
lean_dec_ref(v_a_1116_);
lean_dec(v_a_1115_);
lean_dec(v_a_1114_);
lean_dec_ref(v_e_1113_);
v___x_1185_ = lean_box(0);
if (v_isShared_1129_ == 0)
{
lean_ctor_set(v___x_1128_, 0, v___x_1185_);
v___x_1187_ = v___x_1128_;
goto v_reusejp_1186_;
}
else
{
lean_object* v_reuseFailAlloc_1188_; 
v_reuseFailAlloc_1188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1188_, 0, v___x_1185_);
v___x_1187_ = v_reuseFailAlloc_1188_;
goto v_reusejp_1186_;
}
v_reusejp_1186_:
{
return v___x_1187_;
}
}
}
}
else
{
lean_object* v_a_1190_; lean_object* v___x_1192_; uint8_t v_isShared_1193_; uint8_t v_isSharedCheck_1197_; 
lean_dec(v_a_1123_);
lean_dec_ref(v_a_1122_);
lean_dec(v_a_1121_);
lean_dec_ref(v_a_1120_);
lean_dec(v_a_1119_);
lean_dec_ref(v_a_1118_);
lean_dec(v_a_1117_);
lean_dec_ref(v_a_1116_);
lean_dec(v_a_1115_);
lean_dec(v_a_1114_);
lean_dec_ref(v_e_1113_);
v_a_1190_ = lean_ctor_get(v___x_1125_, 0);
v_isSharedCheck_1197_ = !lean_is_exclusive(v___x_1125_);
if (v_isSharedCheck_1197_ == 0)
{
v___x_1192_ = v___x_1125_;
v_isShared_1193_ = v_isSharedCheck_1197_;
goto v_resetjp_1191_;
}
else
{
lean_inc(v_a_1190_);
lean_dec(v___x_1125_);
v___x_1192_ = lean_box(0);
v_isShared_1193_ = v_isSharedCheck_1197_;
goto v_resetjp_1191_;
}
v_resetjp_1191_:
{
lean_object* v___x_1195_; 
if (v_isShared_1193_ == 0)
{
v___x_1195_ = v___x_1192_;
goto v_reusejp_1194_;
}
else
{
lean_object* v_reuseFailAlloc_1196_; 
v_reuseFailAlloc_1196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1196_, 0, v_a_1190_);
v___x_1195_ = v_reuseFailAlloc_1196_;
goto v_reusejp_1194_;
}
v_reusejp_1194_:
{
return v___x_1195_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents___boxed(lean_object* v_e_1198_, lean_object* v_a_1199_, lean_object* v_a_1200_, lean_object* v_a_1201_, lean_object* v_a_1202_, lean_object* v_a_1203_, lean_object* v_a_1204_, lean_object* v_a_1205_, lean_object* v_a_1206_, lean_object* v_a_1207_, lean_object* v_a_1208_, lean_object* v_a_1209_){
_start:
{
lean_object* v_res_1210_; 
v_res_1210_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents(v_e_1198_, v_a_1199_, v_a_1200_, v_a_1201_, v_a_1202_, v_a_1203_, v_a_1204_, v_a_1205_, v_a_1206_, v_a_1207_, v_a_1208_);
return v_res_1210_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__1(lean_object* v_00_u03b1_1211_, lean_object* v_msg_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_){
_start:
{
lean_object* v___x_1224_; 
v___x_1224_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__1___redArg(v_msg_1212_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_);
return v___x_1224_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__1___boxed(lean_object* v_00_u03b1_1225_, lean_object* v_msg_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_){
_start:
{
lean_object* v_res_1238_; 
v_res_1238_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__1(v_00_u03b1_1225_, v_msg_1226_, v___y_1227_, v___y_1228_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_, v___y_1235_, v___y_1236_);
lean_dec(v___y_1236_);
lean_dec_ref(v___y_1235_);
lean_dec(v___y_1234_);
lean_dec_ref(v___y_1233_);
lean_dec(v___y_1232_);
lean_dec_ref(v___y_1231_);
lean_dec(v___y_1230_);
lean_dec_ref(v___y_1229_);
lean_dec(v___y_1228_);
lean_dec(v___y_1227_);
return v_res_1238_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__2(lean_object* v_e_1239_, uint8_t v_a_1240_, lean_object* v_as_1241_, size_t v_sz_1242_, size_t v_i_1243_, uint8_t v_b_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_){
_start:
{
lean_object* v___x_1256_; 
v___x_1256_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__2___redArg(v_e_1239_, v_a_1240_, v_as_1241_, v_sz_1242_, v_i_1243_, v_b_1244_, v___y_1245_);
return v___x_1256_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__2___boxed(lean_object** _args){
lean_object* v_e_1257_ = _args[0];
lean_object* v_a_1258_ = _args[1];
lean_object* v_as_1259_ = _args[2];
lean_object* v_sz_1260_ = _args[3];
lean_object* v_i_1261_ = _args[4];
lean_object* v_b_1262_ = _args[5];
lean_object* v___y_1263_ = _args[6];
lean_object* v___y_1264_ = _args[7];
lean_object* v___y_1265_ = _args[8];
lean_object* v___y_1266_ = _args[9];
lean_object* v___y_1267_ = _args[10];
lean_object* v___y_1268_ = _args[11];
lean_object* v___y_1269_ = _args[12];
lean_object* v___y_1270_ = _args[13];
lean_object* v___y_1271_ = _args[14];
lean_object* v___y_1272_ = _args[15];
lean_object* v___y_1273_ = _args[16];
_start:
{
uint8_t v_a_68018__boxed_1274_; size_t v_sz_boxed_1275_; size_t v_i_boxed_1276_; uint8_t v_b_boxed_1277_; lean_object* v_res_1278_; 
v_a_68018__boxed_1274_ = lean_unbox(v_a_1258_);
v_sz_boxed_1275_ = lean_unbox_usize(v_sz_1260_);
lean_dec(v_sz_1260_);
v_i_boxed_1276_ = lean_unbox_usize(v_i_1261_);
lean_dec(v_i_1261_);
v_b_boxed_1277_ = lean_unbox(v_b_1262_);
v_res_1278_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__2(v_e_1257_, v_a_68018__boxed_1274_, v_as_1259_, v_sz_boxed_1275_, v_i_boxed_1276_, v_b_boxed_1277_, v___y_1263_, v___y_1264_, v___y_1265_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_, v___y_1272_);
lean_dec(v___y_1272_);
lean_dec_ref(v___y_1271_);
lean_dec(v___y_1270_);
lean_dec_ref(v___y_1269_);
lean_dec(v___y_1268_);
lean_dec_ref(v___y_1267_);
lean_dec(v___y_1266_);
lean_dec_ref(v___y_1265_);
lean_dec(v___y_1264_);
lean_dec(v___y_1263_);
lean_dec_ref(v_as_1259_);
lean_dec_ref(v_e_1257_);
return v_res_1278_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3(lean_object* v_e_1279_, uint8_t v_a_1280_, lean_object* v_as_1281_, lean_object* v_as_x27_1282_, lean_object* v_b_1283_, lean_object* v_a_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_){
_start:
{
lean_object* v___x_1296_; 
v___x_1296_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg(v_e_1279_, v_a_1280_, v_as_x27_1282_, v_b_1283_, v___y_1285_, v___y_1286_, v___y_1287_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_, v___y_1294_);
return v___x_1296_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___boxed(lean_object** _args){
lean_object* v_e_1297_ = _args[0];
lean_object* v_a_1298_ = _args[1];
lean_object* v_as_1299_ = _args[2];
lean_object* v_as_x27_1300_ = _args[3];
lean_object* v_b_1301_ = _args[4];
lean_object* v_a_1302_ = _args[5];
lean_object* v___y_1303_ = _args[6];
lean_object* v___y_1304_ = _args[7];
lean_object* v___y_1305_ = _args[8];
lean_object* v___y_1306_ = _args[9];
lean_object* v___y_1307_ = _args[10];
lean_object* v___y_1308_ = _args[11];
lean_object* v___y_1309_ = _args[12];
lean_object* v___y_1310_ = _args[13];
lean_object* v___y_1311_ = _args[14];
lean_object* v___y_1312_ = _args[15];
lean_object* v___y_1313_ = _args[16];
_start:
{
uint8_t v_a_68056__boxed_1314_; lean_object* v_res_1315_; 
v_a_68056__boxed_1314_ = lean_unbox(v_a_1298_);
v_res_1315_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3(v_e_1297_, v_a_68056__boxed_1314_, v_as_1299_, v_as_x27_1300_, v_b_1301_, v_a_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_, v___y_1310_, v___y_1311_, v___y_1312_);
lean_dec(v_as_1299_);
return v_res_1315_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; 
v___x_1318_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg___closed__1));
v___x_1319_ = lean_unsigned_to_nat(6u);
v___x_1320_ = lean_unsigned_to_nat(105u);
v___x_1321_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg___closed__0));
v___x_1322_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___closed__0));
v___x_1323_ = l_mkPanicMessageWithDecl(v___x_1322_, v___x_1321_, v___x_1320_, v___x_1319_, v___x_1318_);
return v___x_1323_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; 
v___x_1325_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg___closed__3));
v___x_1326_ = lean_unsigned_to_nat(6u);
v___x_1327_ = lean_unsigned_to_nat(103u);
v___x_1328_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg___closed__0));
v___x_1329_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___closed__0));
v___x_1330_ = l_mkPanicMessageWithDecl(v___x_1329_, v___x_1328_, v___x_1327_, v___x_1326_, v___x_1325_);
return v___x_1330_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg(lean_object* v_upperBound_1331_, lean_object* v_a_1332_, lean_object* v___x_1333_, lean_object* v_a_1334_, lean_object* v_b_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_){
_start:
{
lean_object* v_a_1348_; lean_object* v___y_1353_; uint8_t v___x_1372_; 
v___x_1372_ = lean_nat_dec_lt(v_a_1334_, v_upperBound_1331_);
if (v___x_1372_ == 0)
{
lean_object* v___x_1373_; 
lean_dec(v___y_1345_);
lean_dec_ref(v___y_1344_);
lean_dec(v___y_1343_);
lean_dec_ref(v___y_1342_);
lean_dec(v___y_1341_);
lean_dec_ref(v___y_1340_);
lean_dec(v___y_1339_);
lean_dec_ref(v___y_1338_);
lean_dec(v___y_1337_);
lean_dec(v___y_1336_);
lean_dec(v_a_1334_);
lean_dec_ref(v_a_1332_);
v___x_1373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1373_, 0, v_b_1335_);
return v___x_1373_;
}
else
{
lean_object* v___x_1374_; lean_object* v___x_1375_; uint8_t v___x_1376_; 
v___x_1374_ = l_Lean_instInhabitedExpr;
lean_inc_ref(v_a_1332_);
v___x_1375_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1374_, v_a_1332_, v_a_1334_);
v___x_1376_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_1333_, v___x_1375_);
if (v___x_1376_ == 0)
{
uint8_t v___x_1377_; 
v___x_1377_ = lean_expr_equal(v___x_1333_, v___x_1375_);
lean_dec(v___x_1375_);
if (v___x_1377_ == 0)
{
lean_object* v___x_1378_; 
v___x_1378_ = lean_box(0);
v_a_1348_ = v___x_1378_;
goto v___jp_1347_;
}
else
{
lean_object* v___x_1379_; lean_object* v___x_1380_; 
v___x_1379_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg___closed__2, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg___closed__2_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg___closed__2);
lean_inc(v___y_1345_);
lean_inc_ref(v___y_1344_);
lean_inc(v___y_1343_);
lean_inc_ref(v___y_1342_);
lean_inc(v___y_1341_);
lean_inc_ref(v___y_1340_);
lean_inc(v___y_1339_);
lean_inc_ref(v___y_1338_);
lean_inc(v___y_1337_);
lean_inc(v___y_1336_);
v___x_1380_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__0(v___x_1379_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_);
v___y_1353_ = v___x_1380_;
goto v___jp_1352_;
}
}
else
{
lean_object* v___x_1381_; lean_object* v___x_1382_; 
lean_dec(v___x_1375_);
v___x_1381_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg___closed__4, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg___closed__4_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg___closed__4);
lean_inc(v___y_1345_);
lean_inc_ref(v___y_1344_);
lean_inc(v___y_1343_);
lean_inc_ref(v___y_1342_);
lean_inc(v___y_1341_);
lean_inc_ref(v___y_1340_);
lean_inc(v___y_1339_);
lean_inc_ref(v___y_1338_);
lean_inc(v___y_1337_);
lean_inc(v___y_1336_);
v___x_1382_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__0(v___x_1381_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_);
v___y_1353_ = v___x_1382_;
goto v___jp_1352_;
}
}
v___jp_1347_:
{
lean_object* v___x_1349_; lean_object* v___x_1350_; 
v___x_1349_ = lean_unsigned_to_nat(1u);
v___x_1350_ = lean_nat_add(v_a_1334_, v___x_1349_);
lean_dec(v_a_1334_);
v_a_1334_ = v___x_1350_;
v_b_1335_ = v_a_1348_;
goto _start;
}
v___jp_1352_:
{
if (lean_obj_tag(v___y_1353_) == 0)
{
lean_object* v_a_1354_; lean_object* v___x_1356_; uint8_t v_isShared_1357_; uint8_t v_isSharedCheck_1363_; 
v_a_1354_ = lean_ctor_get(v___y_1353_, 0);
v_isSharedCheck_1363_ = !lean_is_exclusive(v___y_1353_);
if (v_isSharedCheck_1363_ == 0)
{
v___x_1356_ = v___y_1353_;
v_isShared_1357_ = v_isSharedCheck_1363_;
goto v_resetjp_1355_;
}
else
{
lean_inc(v_a_1354_);
lean_dec(v___y_1353_);
v___x_1356_ = lean_box(0);
v_isShared_1357_ = v_isSharedCheck_1363_;
goto v_resetjp_1355_;
}
v_resetjp_1355_:
{
if (lean_obj_tag(v_a_1354_) == 0)
{
lean_object* v_a_1358_; lean_object* v___x_1360_; 
lean_dec(v___y_1345_);
lean_dec_ref(v___y_1344_);
lean_dec(v___y_1343_);
lean_dec_ref(v___y_1342_);
lean_dec(v___y_1341_);
lean_dec_ref(v___y_1340_);
lean_dec(v___y_1339_);
lean_dec_ref(v___y_1338_);
lean_dec(v___y_1337_);
lean_dec(v___y_1336_);
lean_dec(v_a_1334_);
lean_dec_ref(v_a_1332_);
v_a_1358_ = lean_ctor_get(v_a_1354_, 0);
lean_inc(v_a_1358_);
lean_dec_ref(v_a_1354_);
if (v_isShared_1357_ == 0)
{
lean_ctor_set(v___x_1356_, 0, v_a_1358_);
v___x_1360_ = v___x_1356_;
goto v_reusejp_1359_;
}
else
{
lean_object* v_reuseFailAlloc_1361_; 
v_reuseFailAlloc_1361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1361_, 0, v_a_1358_);
v___x_1360_ = v_reuseFailAlloc_1361_;
goto v_reusejp_1359_;
}
v_reusejp_1359_:
{
return v___x_1360_;
}
}
else
{
lean_object* v_a_1362_; 
lean_del_object(v___x_1356_);
v_a_1362_ = lean_ctor_get(v_a_1354_, 0);
lean_inc(v_a_1362_);
lean_dec_ref(v_a_1354_);
v_a_1348_ = v_a_1362_;
goto v___jp_1347_;
}
}
}
else
{
lean_object* v_a_1364_; lean_object* v___x_1366_; uint8_t v_isShared_1367_; uint8_t v_isSharedCheck_1371_; 
lean_dec(v___y_1345_);
lean_dec_ref(v___y_1344_);
lean_dec(v___y_1343_);
lean_dec_ref(v___y_1342_);
lean_dec(v___y_1341_);
lean_dec_ref(v___y_1340_);
lean_dec(v___y_1339_);
lean_dec_ref(v___y_1338_);
lean_dec(v___y_1337_);
lean_dec(v___y_1336_);
lean_dec(v_a_1334_);
lean_dec_ref(v_a_1332_);
v_a_1364_ = lean_ctor_get(v___y_1353_, 0);
v_isSharedCheck_1371_ = !lean_is_exclusive(v___y_1353_);
if (v_isSharedCheck_1371_ == 0)
{
v___x_1366_ = v___y_1353_;
v_isShared_1367_ = v_isSharedCheck_1371_;
goto v_resetjp_1365_;
}
else
{
lean_inc(v_a_1364_);
lean_dec(v___y_1353_);
v___x_1366_ = lean_box(0);
v_isShared_1367_ = v_isSharedCheck_1371_;
goto v_resetjp_1365_;
}
v_resetjp_1365_:
{
lean_object* v___x_1369_; 
if (v_isShared_1367_ == 0)
{
v___x_1369_ = v___x_1366_;
goto v_reusejp_1368_;
}
else
{
lean_object* v_reuseFailAlloc_1370_; 
v_reuseFailAlloc_1370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1370_, 0, v_a_1364_);
v___x_1369_ = v_reuseFailAlloc_1370_;
goto v_reusejp_1368_;
}
v_reusejp_1368_:
{
return v___x_1369_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg___boxed(lean_object* v_upperBound_1383_, lean_object* v_a_1384_, lean_object* v___x_1385_, lean_object* v_a_1386_, lean_object* v_b_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_){
_start:
{
lean_object* v_res_1399_; 
v_res_1399_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg(v_upperBound_1383_, v_a_1384_, v___x_1385_, v_a_1386_, v_b_1387_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_, v___y_1396_, v___y_1397_);
lean_dec_ref(v___x_1385_);
lean_dec(v_upperBound_1383_);
return v_res_1399_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__1___redArg(lean_object* v_upperBound_1400_, lean_object* v___x_1401_, lean_object* v_a_1402_, lean_object* v_a_1403_, lean_object* v_b_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_){
_start:
{
uint8_t v___x_1416_; 
v___x_1416_ = lean_nat_dec_lt(v_a_1403_, v_upperBound_1400_);
if (v___x_1416_ == 0)
{
lean_object* v___x_1417_; 
lean_dec(v___y_1414_);
lean_dec_ref(v___y_1413_);
lean_dec(v___y_1412_);
lean_dec_ref(v___y_1411_);
lean_dec(v___y_1410_);
lean_dec_ref(v___y_1409_);
lean_dec(v___y_1408_);
lean_dec_ref(v___y_1407_);
lean_dec(v___y_1406_);
lean_dec(v___y_1405_);
lean_dec(v_a_1403_);
lean_dec_ref(v_a_1402_);
v___x_1417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1417_, 0, v_b_1404_);
return v___x_1417_;
}
else
{
lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; 
v___x_1418_ = lean_box(0);
v___x_1419_ = l_Lean_instInhabitedExpr;
v___x_1420_ = lean_unsigned_to_nat(1u);
v___x_1421_ = lean_nat_add(v_a_1403_, v___x_1420_);
lean_inc_ref(v_a_1402_);
v___x_1422_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1419_, v_a_1402_, v_a_1403_);
lean_dec(v_a_1403_);
lean_inc(v___y_1414_);
lean_inc_ref(v___y_1413_);
lean_inc(v___y_1412_);
lean_inc_ref(v___y_1411_);
lean_inc(v___y_1410_);
lean_inc_ref(v___y_1409_);
lean_inc(v___y_1408_);
lean_inc_ref(v___y_1407_);
lean_inc(v___y_1406_);
lean_inc(v___y_1405_);
lean_inc(v___x_1421_);
lean_inc_ref(v_a_1402_);
v___x_1423_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg(v___x_1401_, v_a_1402_, v___x_1422_, v___x_1421_, v___x_1418_, v___y_1405_, v___y_1406_, v___y_1407_, v___y_1408_, v___y_1409_, v___y_1410_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_);
lean_dec(v___x_1422_);
if (lean_obj_tag(v___x_1423_) == 0)
{
lean_dec_ref(v___x_1423_);
v_a_1403_ = v___x_1421_;
v_b_1404_ = v___x_1418_;
goto _start;
}
else
{
lean_dec(v___x_1421_);
lean_dec(v___y_1414_);
lean_dec_ref(v___y_1413_);
lean_dec(v___y_1412_);
lean_dec_ref(v___y_1411_);
lean_dec(v___y_1410_);
lean_dec_ref(v___y_1409_);
lean_dec(v___y_1408_);
lean_dec_ref(v___y_1407_);
lean_dec(v___y_1406_);
lean_dec(v___y_1405_);
lean_dec_ref(v_a_1402_);
return v___x_1423_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__1___redArg___boxed(lean_object* v_upperBound_1425_, lean_object* v___x_1426_, lean_object* v_a_1427_, lean_object* v_a_1428_, lean_object* v_b_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_){
_start:
{
lean_object* v_res_1441_; 
v_res_1441_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__1___redArg(v_upperBound_1425_, v___x_1426_, v_a_1427_, v_a_1428_, v_b_1429_, v___y_1430_, v___y_1431_, v___y_1432_, v___y_1433_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_);
lean_dec(v___x_1426_);
lean_dec(v_upperBound_1425_);
return v_res_1441_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq(lean_object* v_a_1442_, lean_object* v_a_1443_, lean_object* v_a_1444_, lean_object* v_a_1445_, lean_object* v_a_1446_, lean_object* v_a_1447_, lean_object* v_a_1448_, lean_object* v_a_1449_, lean_object* v_a_1450_, lean_object* v_a_1451_){
_start:
{
lean_object* v___x_1453_; 
v___x_1453_ = l_Lean_Meta_Grind_getExprs___redArg(v_a_1442_);
if (lean_obj_tag(v___x_1453_) == 0)
{
lean_object* v_a_1454_; lean_object* v_size_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; 
v_a_1454_ = lean_ctor_get(v___x_1453_, 0);
lean_inc(v_a_1454_);
lean_dec_ref(v___x_1453_);
v_size_1455_ = lean_ctor_get(v_a_1454_, 2);
lean_inc(v_size_1455_);
v___x_1456_ = lean_unsigned_to_nat(0u);
v___x_1457_ = lean_box(0);
v___x_1458_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__1___redArg(v_size_1455_, v_size_1455_, v_a_1454_, v___x_1456_, v___x_1457_, v_a_1442_, v_a_1443_, v_a_1444_, v_a_1445_, v_a_1446_, v_a_1447_, v_a_1448_, v_a_1449_, v_a_1450_, v_a_1451_);
lean_dec(v_size_1455_);
if (lean_obj_tag(v___x_1458_) == 0)
{
lean_object* v___x_1460_; uint8_t v_isShared_1461_; uint8_t v_isSharedCheck_1465_; 
v_isSharedCheck_1465_ = !lean_is_exclusive(v___x_1458_);
if (v_isSharedCheck_1465_ == 0)
{
lean_object* v_unused_1466_; 
v_unused_1466_ = lean_ctor_get(v___x_1458_, 0);
lean_dec(v_unused_1466_);
v___x_1460_ = v___x_1458_;
v_isShared_1461_ = v_isSharedCheck_1465_;
goto v_resetjp_1459_;
}
else
{
lean_dec(v___x_1458_);
v___x_1460_ = lean_box(0);
v_isShared_1461_ = v_isSharedCheck_1465_;
goto v_resetjp_1459_;
}
v_resetjp_1459_:
{
lean_object* v___x_1463_; 
if (v_isShared_1461_ == 0)
{
lean_ctor_set(v___x_1460_, 0, v___x_1457_);
v___x_1463_ = v___x_1460_;
goto v_reusejp_1462_;
}
else
{
lean_object* v_reuseFailAlloc_1464_; 
v_reuseFailAlloc_1464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1464_, 0, v___x_1457_);
v___x_1463_ = v_reuseFailAlloc_1464_;
goto v_reusejp_1462_;
}
v_reusejp_1462_:
{
return v___x_1463_;
}
}
}
else
{
return v___x_1458_;
}
}
else
{
lean_object* v_a_1467_; lean_object* v___x_1469_; uint8_t v_isShared_1470_; uint8_t v_isSharedCheck_1474_; 
lean_dec(v_a_1451_);
lean_dec_ref(v_a_1450_);
lean_dec(v_a_1449_);
lean_dec_ref(v_a_1448_);
lean_dec(v_a_1447_);
lean_dec_ref(v_a_1446_);
lean_dec(v_a_1445_);
lean_dec_ref(v_a_1444_);
lean_dec(v_a_1443_);
lean_dec(v_a_1442_);
v_a_1467_ = lean_ctor_get(v___x_1453_, 0);
v_isSharedCheck_1474_ = !lean_is_exclusive(v___x_1453_);
if (v_isSharedCheck_1474_ == 0)
{
v___x_1469_ = v___x_1453_;
v_isShared_1470_ = v_isSharedCheck_1474_;
goto v_resetjp_1468_;
}
else
{
lean_inc(v_a_1467_);
lean_dec(v___x_1453_);
v___x_1469_ = lean_box(0);
v_isShared_1470_ = v_isSharedCheck_1474_;
goto v_resetjp_1468_;
}
v_resetjp_1468_:
{
lean_object* v___x_1472_; 
if (v_isShared_1470_ == 0)
{
v___x_1472_ = v___x_1469_;
goto v_reusejp_1471_;
}
else
{
lean_object* v_reuseFailAlloc_1473_; 
v_reuseFailAlloc_1473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1473_, 0, v_a_1467_);
v___x_1472_ = v_reuseFailAlloc_1473_;
goto v_reusejp_1471_;
}
v_reusejp_1471_:
{
return v___x_1472_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq___boxed(lean_object* v_a_1475_, lean_object* v_a_1476_, lean_object* v_a_1477_, lean_object* v_a_1478_, lean_object* v_a_1479_, lean_object* v_a_1480_, lean_object* v_a_1481_, lean_object* v_a_1482_, lean_object* v_a_1483_, lean_object* v_a_1484_, lean_object* v_a_1485_){
_start:
{
lean_object* v_res_1486_; 
v_res_1486_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq(v_a_1475_, v_a_1476_, v_a_1477_, v_a_1478_, v_a_1479_, v_a_1480_, v_a_1481_, v_a_1482_, v_a_1483_, v_a_1484_);
return v_res_1486_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0(lean_object* v_upperBound_1487_, lean_object* v_a_1488_, lean_object* v___x_1489_, lean_object* v_inst_1490_, lean_object* v_R_1491_, lean_object* v_a_1492_, lean_object* v_b_1493_, lean_object* v_c_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_){
_start:
{
lean_object* v___x_1506_; 
v___x_1506_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg(v_upperBound_1487_, v_a_1488_, v___x_1489_, v_a_1492_, v_b_1493_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_, v___y_1500_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_);
return v___x_1506_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___boxed(lean_object** _args){
lean_object* v_upperBound_1507_ = _args[0];
lean_object* v_a_1508_ = _args[1];
lean_object* v___x_1509_ = _args[2];
lean_object* v_inst_1510_ = _args[3];
lean_object* v_R_1511_ = _args[4];
lean_object* v_a_1512_ = _args[5];
lean_object* v_b_1513_ = _args[6];
lean_object* v_c_1514_ = _args[7];
lean_object* v___y_1515_ = _args[8];
lean_object* v___y_1516_ = _args[9];
lean_object* v___y_1517_ = _args[10];
lean_object* v___y_1518_ = _args[11];
lean_object* v___y_1519_ = _args[12];
lean_object* v___y_1520_ = _args[13];
lean_object* v___y_1521_ = _args[14];
lean_object* v___y_1522_ = _args[15];
lean_object* v___y_1523_ = _args[16];
lean_object* v___y_1524_ = _args[17];
lean_object* v___y_1525_ = _args[18];
_start:
{
lean_object* v_res_1526_; 
v_res_1526_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0(v_upperBound_1507_, v_a_1508_, v___x_1509_, v_inst_1510_, v_R_1511_, v_a_1512_, v_b_1513_, v_c_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_);
lean_dec_ref(v___x_1509_);
lean_dec(v_upperBound_1507_);
return v_res_1526_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__1(lean_object* v_upperBound_1527_, lean_object* v___x_1528_, lean_object* v_a_1529_, lean_object* v_inst_1530_, lean_object* v_R_1531_, lean_object* v_a_1532_, lean_object* v_b_1533_, lean_object* v_c_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_){
_start:
{
lean_object* v___x_1546_; 
v___x_1546_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__1___redArg(v_upperBound_1527_, v___x_1528_, v_a_1529_, v_a_1532_, v_b_1533_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_);
return v___x_1546_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__1___boxed(lean_object** _args){
lean_object* v_upperBound_1547_ = _args[0];
lean_object* v___x_1548_ = _args[1];
lean_object* v_a_1549_ = _args[2];
lean_object* v_inst_1550_ = _args[3];
lean_object* v_R_1551_ = _args[4];
lean_object* v_a_1552_ = _args[5];
lean_object* v_b_1553_ = _args[6];
lean_object* v_c_1554_ = _args[7];
lean_object* v___y_1555_ = _args[8];
lean_object* v___y_1556_ = _args[9];
lean_object* v___y_1557_ = _args[10];
lean_object* v___y_1558_ = _args[11];
lean_object* v___y_1559_ = _args[12];
lean_object* v___y_1560_ = _args[13];
lean_object* v___y_1561_ = _args[14];
lean_object* v___y_1562_ = _args[15];
lean_object* v___y_1563_ = _args[16];
lean_object* v___y_1564_ = _args[17];
lean_object* v___y_1565_ = _args[18];
_start:
{
lean_object* v_res_1566_; 
v_res_1566_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__1(v_upperBound_1547_, v___x_1548_, v_a_1549_, v_inst_1550_, v_R_1551_, v_a_1552_, v_b_1553_, v_c_1554_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_, v___y_1562_, v___y_1563_, v___y_1564_);
lean_dec(v___x_1548_);
lean_dec(v_upperBound_1547_);
return v_res_1566_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__0___redArg(lean_object* v_cls_1570_, lean_object* v___y_1571_){
_start:
{
lean_object* v_options_1573_; uint8_t v_hasTrace_1574_; 
v_options_1573_ = lean_ctor_get(v___y_1571_, 2);
v_hasTrace_1574_ = lean_ctor_get_uint8(v_options_1573_, sizeof(void*)*1);
if (v_hasTrace_1574_ == 0)
{
lean_object* v___x_1575_; lean_object* v___x_1576_; 
lean_dec(v_cls_1570_);
v___x_1575_ = lean_box(v_hasTrace_1574_);
v___x_1576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1576_, 0, v___x_1575_);
return v___x_1576_;
}
else
{
lean_object* v_inheritedTraceOptions_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; uint8_t v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; 
v_inheritedTraceOptions_1577_ = lean_ctor_get(v___y_1571_, 13);
v___x_1578_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__0___redArg___closed__1));
v___x_1579_ = l_Lean_Name_append(v___x_1578_, v_cls_1570_);
v___x_1580_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1577_, v_options_1573_, v___x_1579_);
lean_dec(v___x_1579_);
v___x_1581_ = lean_box(v___x_1580_);
v___x_1582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1582_, 0, v___x_1581_);
return v___x_1582_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__0___redArg___boxed(lean_object* v_cls_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_){
_start:
{
lean_object* v_res_1586_; 
v_res_1586_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__0___redArg(v_cls_1583_, v___y_1584_);
lean_dec_ref(v___y_1584_);
return v_res_1586_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__0(lean_object* v_cls_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_){
_start:
{
lean_object* v___x_1599_; 
v___x_1599_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__0___redArg(v_cls_1587_, v___y_1596_);
return v___x_1599_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__0___boxed(lean_object* v_cls_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_){
_start:
{
lean_object* v_res_1612_; 
v_res_1612_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__0(v_cls_1600_, v___y_1601_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_, v___y_1606_, v___y_1607_, v___y_1608_, v___y_1609_, v___y_1610_);
lean_dec(v___y_1610_);
lean_dec_ref(v___y_1609_);
lean_dec(v___y_1608_);
lean_dec_ref(v___y_1607_);
lean_dec(v___y_1606_);
lean_dec_ref(v___y_1605_);
lean_dec(v___y_1604_);
lean_dec_ref(v___y_1603_);
lean_dec(v___y_1602_);
lean_dec(v___y_1601_);
return v_res_1612_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1613_; double v___x_1614_; 
v___x_1613_ = lean_unsigned_to_nat(0u);
v___x_1614_ = lean_float_of_nat(v___x_1613_);
return v___x_1614_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg(lean_object* v_cls_1618_, lean_object* v_msg_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_){
_start:
{
lean_object* v_ref_1625_; lean_object* v___x_1626_; lean_object* v_a_1627_; lean_object* v___x_1629_; uint8_t v_isShared_1630_; uint8_t v_isSharedCheck_1671_; 
v_ref_1625_ = lean_ctor_get(v___y_1622_, 5);
v___x_1626_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__1_spec__1(v_msg_1619_, v___y_1620_, v___y_1621_, v___y_1622_, v___y_1623_);
v_a_1627_ = lean_ctor_get(v___x_1626_, 0);
v_isSharedCheck_1671_ = !lean_is_exclusive(v___x_1626_);
if (v_isSharedCheck_1671_ == 0)
{
v___x_1629_ = v___x_1626_;
v_isShared_1630_ = v_isSharedCheck_1671_;
goto v_resetjp_1628_;
}
else
{
lean_inc(v_a_1627_);
lean_dec(v___x_1626_);
v___x_1629_ = lean_box(0);
v_isShared_1630_ = v_isSharedCheck_1671_;
goto v_resetjp_1628_;
}
v_resetjp_1628_:
{
lean_object* v___x_1631_; lean_object* v_traceState_1632_; lean_object* v_env_1633_; lean_object* v_nextMacroScope_1634_; lean_object* v_ngen_1635_; lean_object* v_auxDeclNGen_1636_; lean_object* v_cache_1637_; lean_object* v_messages_1638_; lean_object* v_infoState_1639_; lean_object* v_snapshotTasks_1640_; lean_object* v___x_1642_; uint8_t v_isShared_1643_; uint8_t v_isSharedCheck_1670_; 
v___x_1631_ = lean_st_ref_take(v___y_1623_);
v_traceState_1632_ = lean_ctor_get(v___x_1631_, 4);
v_env_1633_ = lean_ctor_get(v___x_1631_, 0);
v_nextMacroScope_1634_ = lean_ctor_get(v___x_1631_, 1);
v_ngen_1635_ = lean_ctor_get(v___x_1631_, 2);
v_auxDeclNGen_1636_ = lean_ctor_get(v___x_1631_, 3);
v_cache_1637_ = lean_ctor_get(v___x_1631_, 5);
v_messages_1638_ = lean_ctor_get(v___x_1631_, 6);
v_infoState_1639_ = lean_ctor_get(v___x_1631_, 7);
v_snapshotTasks_1640_ = lean_ctor_get(v___x_1631_, 8);
v_isSharedCheck_1670_ = !lean_is_exclusive(v___x_1631_);
if (v_isSharedCheck_1670_ == 0)
{
v___x_1642_ = v___x_1631_;
v_isShared_1643_ = v_isSharedCheck_1670_;
goto v_resetjp_1641_;
}
else
{
lean_inc(v_snapshotTasks_1640_);
lean_inc(v_infoState_1639_);
lean_inc(v_messages_1638_);
lean_inc(v_cache_1637_);
lean_inc(v_traceState_1632_);
lean_inc(v_auxDeclNGen_1636_);
lean_inc(v_ngen_1635_);
lean_inc(v_nextMacroScope_1634_);
lean_inc(v_env_1633_);
lean_dec(v___x_1631_);
v___x_1642_ = lean_box(0);
v_isShared_1643_ = v_isSharedCheck_1670_;
goto v_resetjp_1641_;
}
v_resetjp_1641_:
{
uint64_t v_tid_1644_; lean_object* v_traces_1645_; lean_object* v___x_1647_; uint8_t v_isShared_1648_; uint8_t v_isSharedCheck_1669_; 
v_tid_1644_ = lean_ctor_get_uint64(v_traceState_1632_, sizeof(void*)*1);
v_traces_1645_ = lean_ctor_get(v_traceState_1632_, 0);
v_isSharedCheck_1669_ = !lean_is_exclusive(v_traceState_1632_);
if (v_isSharedCheck_1669_ == 0)
{
v___x_1647_ = v_traceState_1632_;
v_isShared_1648_ = v_isSharedCheck_1669_;
goto v_resetjp_1646_;
}
else
{
lean_inc(v_traces_1645_);
lean_dec(v_traceState_1632_);
v___x_1647_ = lean_box(0);
v_isShared_1648_ = v_isSharedCheck_1669_;
goto v_resetjp_1646_;
}
v_resetjp_1646_:
{
lean_object* v___x_1649_; double v___x_1650_; uint8_t v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1659_; 
v___x_1649_ = lean_box(0);
v___x_1650_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__0);
v___x_1651_ = 0;
v___x_1652_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__1));
v___x_1653_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1653_, 0, v_cls_1618_);
lean_ctor_set(v___x_1653_, 1, v___x_1649_);
lean_ctor_set(v___x_1653_, 2, v___x_1652_);
lean_ctor_set_float(v___x_1653_, sizeof(void*)*3, v___x_1650_);
lean_ctor_set_float(v___x_1653_, sizeof(void*)*3 + 8, v___x_1650_);
lean_ctor_set_uint8(v___x_1653_, sizeof(void*)*3 + 16, v___x_1651_);
v___x_1654_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__2));
v___x_1655_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1655_, 0, v___x_1653_);
lean_ctor_set(v___x_1655_, 1, v_a_1627_);
lean_ctor_set(v___x_1655_, 2, v___x_1654_);
lean_inc(v_ref_1625_);
v___x_1656_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1656_, 0, v_ref_1625_);
lean_ctor_set(v___x_1656_, 1, v___x_1655_);
v___x_1657_ = l_Lean_PersistentArray_push___redArg(v_traces_1645_, v___x_1656_);
if (v_isShared_1648_ == 0)
{
lean_ctor_set(v___x_1647_, 0, v___x_1657_);
v___x_1659_ = v___x_1647_;
goto v_reusejp_1658_;
}
else
{
lean_object* v_reuseFailAlloc_1668_; 
v_reuseFailAlloc_1668_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1668_, 0, v___x_1657_);
lean_ctor_set_uint64(v_reuseFailAlloc_1668_, sizeof(void*)*1, v_tid_1644_);
v___x_1659_ = v_reuseFailAlloc_1668_;
goto v_reusejp_1658_;
}
v_reusejp_1658_:
{
lean_object* v___x_1661_; 
if (v_isShared_1643_ == 0)
{
lean_ctor_set(v___x_1642_, 4, v___x_1659_);
v___x_1661_ = v___x_1642_;
goto v_reusejp_1660_;
}
else
{
lean_object* v_reuseFailAlloc_1667_; 
v_reuseFailAlloc_1667_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1667_, 0, v_env_1633_);
lean_ctor_set(v_reuseFailAlloc_1667_, 1, v_nextMacroScope_1634_);
lean_ctor_set(v_reuseFailAlloc_1667_, 2, v_ngen_1635_);
lean_ctor_set(v_reuseFailAlloc_1667_, 3, v_auxDeclNGen_1636_);
lean_ctor_set(v_reuseFailAlloc_1667_, 4, v___x_1659_);
lean_ctor_set(v_reuseFailAlloc_1667_, 5, v_cache_1637_);
lean_ctor_set(v_reuseFailAlloc_1667_, 6, v_messages_1638_);
lean_ctor_set(v_reuseFailAlloc_1667_, 7, v_infoState_1639_);
lean_ctor_set(v_reuseFailAlloc_1667_, 8, v_snapshotTasks_1640_);
v___x_1661_ = v_reuseFailAlloc_1667_;
goto v_reusejp_1660_;
}
v_reusejp_1660_:
{
lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1665_; 
v___x_1662_ = lean_st_ref_set(v___y_1623_, v___x_1661_);
v___x_1663_ = lean_box(0);
if (v_isShared_1630_ == 0)
{
lean_ctor_set(v___x_1629_, 0, v___x_1663_);
v___x_1665_ = v___x_1629_;
goto v_reusejp_1664_;
}
else
{
lean_object* v_reuseFailAlloc_1666_; 
v_reuseFailAlloc_1666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1666_, 0, v___x_1663_);
v___x_1665_ = v_reuseFailAlloc_1666_;
goto v_reusejp_1664_;
}
v_reusejp_1664_:
{
return v___x_1665_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___boxed(lean_object* v_cls_1672_, lean_object* v_msg_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_){
_start:
{
lean_object* v_res_1679_; 
v_res_1679_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg(v_cls_1672_, v_msg_1673_, v___y_1674_, v___y_1675_, v___y_1676_, v___y_1677_);
lean_dec(v___y_1677_);
lean_dec_ref(v___y_1676_);
lean_dec(v___y_1675_);
lean_dec_ref(v___y_1674_);
return v_res_1679_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__2___redArg___closed__5(void){
_start:
{
lean_object* v___x_1688_; lean_object* v___x_1689_; 
v___x_1688_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__2___redArg___closed__4));
v___x_1689_ = l_Lean_stringToMessageData(v___x_1688_);
return v___x_1689_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__2___redArg___closed__7(void){
_start:
{
lean_object* v___x_1691_; lean_object* v___x_1692_; 
v___x_1691_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__2___redArg___closed__6));
v___x_1692_ = l_Lean_stringToMessageData(v___x_1691_);
return v___x_1692_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__2___redArg(lean_object* v_a_1693_, lean_object* v_as_x27_1694_, lean_object* v_b_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_){
_start:
{
if (lean_obj_tag(v_as_x27_1694_) == 0)
{
lean_object* v___x_1707_; 
lean_dec(v___y_1705_);
lean_dec_ref(v___y_1704_);
lean_dec(v___y_1703_);
lean_dec_ref(v___y_1702_);
lean_dec(v___y_1701_);
lean_dec_ref(v___y_1700_);
lean_dec(v___y_1699_);
lean_dec_ref(v___y_1698_);
lean_dec(v___y_1697_);
lean_dec(v___y_1696_);
lean_dec_ref(v_a_1693_);
v___x_1707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1707_, 0, v_b_1695_);
return v___x_1707_;
}
else
{
lean_object* v_head_1708_; lean_object* v_tail_1709_; lean_object* v___x_1711_; uint8_t v_isShared_1712_; uint8_t v_isSharedCheck_1771_; 
v_head_1708_ = lean_ctor_get(v_as_x27_1694_, 0);
v_tail_1709_ = lean_ctor_get(v_as_x27_1694_, 1);
v_isSharedCheck_1771_ = !lean_is_exclusive(v_as_x27_1694_);
if (v_isSharedCheck_1771_ == 0)
{
v___x_1711_ = v_as_x27_1694_;
v_isShared_1712_ = v_isSharedCheck_1771_;
goto v_resetjp_1710_;
}
else
{
lean_inc(v_tail_1709_);
lean_inc(v_head_1708_);
lean_dec(v_as_x27_1694_);
v___x_1711_ = lean_box(0);
v_isShared_1712_ = v_isSharedCheck_1771_;
goto v_resetjp_1710_;
}
v_resetjp_1710_:
{
lean_object* v___x_1713_; uint8_t v___x_1714_; 
v___x_1713_ = lean_box(0);
v___x_1714_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_a_1693_, v_head_1708_);
if (v___x_1714_ == 0)
{
lean_object* v___x_1715_; 
lean_inc(v___y_1705_);
lean_inc_ref(v___y_1704_);
lean_inc(v___y_1703_);
lean_inc_ref(v___y_1702_);
lean_inc(v___y_1701_);
lean_inc_ref(v___y_1700_);
lean_inc(v___y_1699_);
lean_inc_ref(v___y_1698_);
lean_inc(v___y_1697_);
lean_inc(v___y_1696_);
lean_inc(v_head_1708_);
lean_inc_ref(v_a_1693_);
v___x_1715_ = l_Lean_Meta_Grind_mkEqHEqProof(v_a_1693_, v_head_1708_, v___y_1696_, v___y_1697_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_);
if (lean_obj_tag(v___x_1715_) == 0)
{
lean_object* v_a_1716_; lean_object* v___x_1717_; lean_object* v___y_1719_; lean_object* v___y_1720_; lean_object* v___y_1721_; lean_object* v___y_1722_; lean_object* v___y_1723_; lean_object* v___y_1724_; lean_object* v___y_1725_; lean_object* v___y_1726_; lean_object* v___y_1727_; lean_object* v___y_1728_; lean_object* v___x_1752_; lean_object* v_a_1753_; uint8_t v___x_1754_; 
v_a_1716_ = lean_ctor_get(v___x_1715_, 0);
lean_inc(v_a_1716_);
lean_dec_ref(v___x_1715_);
v___x_1717_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__2___redArg___closed__3));
v___x_1752_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__0___redArg(v___x_1717_, v___y_1704_);
v_a_1753_ = lean_ctor_get(v___x_1752_, 0);
lean_inc(v_a_1753_);
lean_dec_ref(v___x_1752_);
v___x_1754_ = lean_unbox(v_a_1753_);
lean_dec(v_a_1753_);
if (v___x_1754_ == 0)
{
lean_dec(v_head_1708_);
lean_inc(v___y_1705_);
lean_inc_ref(v___y_1704_);
lean_inc(v___y_1703_);
lean_inc_ref(v___y_1702_);
lean_inc(v___y_1701_);
lean_inc_ref(v___y_1700_);
lean_inc(v___y_1699_);
lean_inc_ref(v___y_1698_);
lean_inc(v___y_1697_);
lean_inc(v___y_1696_);
v___y_1719_ = v___y_1696_;
v___y_1720_ = v___y_1697_;
v___y_1721_ = v___y_1698_;
v___y_1722_ = v___y_1699_;
v___y_1723_ = v___y_1700_;
v___y_1724_ = v___y_1701_;
v___y_1725_ = v___y_1702_;
v___y_1726_ = v___y_1703_;
v___y_1727_ = v___y_1704_;
v___y_1728_ = v___y_1705_;
goto v___jp_1718_;
}
else
{
lean_object* v___x_1755_; 
v___x_1755_ = l_Lean_Meta_Grind_updateLastTag(v___y_1696_, v___y_1697_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_);
if (lean_obj_tag(v___x_1755_) == 0)
{
lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; 
lean_dec_ref(v___x_1755_);
lean_inc_ref(v_a_1693_);
v___x_1756_ = l_Lean_MessageData_ofExpr(v_a_1693_);
v___x_1757_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__2___redArg___closed__7, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__2___redArg___closed__7_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__2___redArg___closed__7);
v___x_1758_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1758_, 0, v___x_1756_);
lean_ctor_set(v___x_1758_, 1, v___x_1757_);
v___x_1759_ = l_Lean_MessageData_ofExpr(v_head_1708_);
v___x_1760_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1760_, 0, v___x_1758_);
lean_ctor_set(v___x_1760_, 1, v___x_1759_);
v___x_1761_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg(v___x_1717_, v___x_1760_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_);
if (lean_obj_tag(v___x_1761_) == 0)
{
lean_dec_ref(v___x_1761_);
lean_inc(v___y_1705_);
lean_inc_ref(v___y_1704_);
lean_inc(v___y_1703_);
lean_inc_ref(v___y_1702_);
lean_inc(v___y_1701_);
lean_inc_ref(v___y_1700_);
lean_inc(v___y_1699_);
lean_inc_ref(v___y_1698_);
lean_inc(v___y_1697_);
lean_inc(v___y_1696_);
v___y_1719_ = v___y_1696_;
v___y_1720_ = v___y_1697_;
v___y_1721_ = v___y_1698_;
v___y_1722_ = v___y_1699_;
v___y_1723_ = v___y_1700_;
v___y_1724_ = v___y_1701_;
v___y_1725_ = v___y_1702_;
v___y_1726_ = v___y_1703_;
v___y_1727_ = v___y_1704_;
v___y_1728_ = v___y_1705_;
goto v___jp_1718_;
}
else
{
lean_dec(v_a_1716_);
lean_del_object(v___x_1711_);
lean_dec(v_tail_1709_);
lean_dec(v___y_1705_);
lean_dec_ref(v___y_1704_);
lean_dec(v___y_1703_);
lean_dec_ref(v___y_1702_);
lean_dec(v___y_1701_);
lean_dec_ref(v___y_1700_);
lean_dec(v___y_1699_);
lean_dec_ref(v___y_1698_);
lean_dec(v___y_1697_);
lean_dec(v___y_1696_);
lean_dec_ref(v_a_1693_);
return v___x_1761_;
}
}
else
{
lean_dec(v_a_1716_);
lean_del_object(v___x_1711_);
lean_dec(v_tail_1709_);
lean_dec(v_head_1708_);
lean_dec(v___y_1705_);
lean_dec_ref(v___y_1704_);
lean_dec(v___y_1703_);
lean_dec_ref(v___y_1702_);
lean_dec(v___y_1701_);
lean_dec_ref(v___y_1700_);
lean_dec(v___y_1699_);
lean_dec_ref(v___y_1698_);
lean_dec(v___y_1697_);
lean_dec(v___y_1696_);
lean_dec_ref(v_a_1693_);
return v___x_1755_;
}
}
v___jp_1718_:
{
lean_object* v___x_1729_; 
lean_inc(v___y_1728_);
lean_inc_ref(v___y_1727_);
lean_inc(v___y_1726_);
lean_inc_ref(v___y_1725_);
lean_inc(v_a_1716_);
v___x_1729_ = l_Lean_Meta_check(v_a_1716_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_);
if (lean_obj_tag(v___x_1729_) == 0)
{
lean_object* v___x_1730_; lean_object* v_a_1731_; uint8_t v___x_1732_; 
lean_dec_ref(v___x_1729_);
v___x_1730_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__0___redArg(v___x_1717_, v___y_1727_);
v_a_1731_ = lean_ctor_get(v___x_1730_, 0);
lean_inc(v_a_1731_);
lean_dec_ref(v___x_1730_);
v___x_1732_ = lean_unbox(v_a_1731_);
lean_dec(v_a_1731_);
if (v___x_1732_ == 0)
{
lean_dec(v___y_1728_);
lean_dec_ref(v___y_1727_);
lean_dec(v___y_1726_);
lean_dec_ref(v___y_1725_);
lean_dec(v___y_1724_);
lean_dec_ref(v___y_1723_);
lean_dec(v___y_1722_);
lean_dec_ref(v___y_1721_);
lean_dec(v___y_1720_);
lean_dec(v___y_1719_);
lean_dec(v_a_1716_);
lean_del_object(v___x_1711_);
v_as_x27_1694_ = v_tail_1709_;
v_b_1695_ = v___x_1713_;
goto _start;
}
else
{
lean_object* v___x_1734_; 
v___x_1734_ = l_Lean_Meta_Grind_updateLastTag(v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_);
lean_dec(v___y_1724_);
lean_dec_ref(v___y_1723_);
lean_dec(v___y_1722_);
lean_dec_ref(v___y_1721_);
lean_dec(v___y_1720_);
lean_dec(v___y_1719_);
if (lean_obj_tag(v___x_1734_) == 0)
{
lean_object* v___x_1735_; 
lean_dec_ref(v___x_1734_);
lean_inc(v___y_1728_);
lean_inc_ref(v___y_1727_);
lean_inc(v___y_1726_);
lean_inc_ref(v___y_1725_);
v___x_1735_ = lean_infer_type(v_a_1716_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_);
if (lean_obj_tag(v___x_1735_) == 0)
{
lean_object* v_a_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1740_; 
v_a_1736_ = lean_ctor_get(v___x_1735_, 0);
lean_inc(v_a_1736_);
lean_dec_ref(v___x_1735_);
v___x_1737_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__2___redArg___closed__5, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__2___redArg___closed__5_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__2___redArg___closed__5);
v___x_1738_ = l_Lean_MessageData_ofExpr(v_a_1736_);
if (v_isShared_1712_ == 0)
{
lean_ctor_set_tag(v___x_1711_, 7);
lean_ctor_set(v___x_1711_, 1, v___x_1738_);
lean_ctor_set(v___x_1711_, 0, v___x_1737_);
v___x_1740_ = v___x_1711_;
goto v_reusejp_1739_;
}
else
{
lean_object* v_reuseFailAlloc_1743_; 
v_reuseFailAlloc_1743_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1743_, 0, v___x_1737_);
lean_ctor_set(v_reuseFailAlloc_1743_, 1, v___x_1738_);
v___x_1740_ = v_reuseFailAlloc_1743_;
goto v_reusejp_1739_;
}
v_reusejp_1739_:
{
lean_object* v___x_1741_; 
v___x_1741_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg(v___x_1717_, v___x_1740_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_);
lean_dec(v___y_1728_);
lean_dec_ref(v___y_1727_);
lean_dec(v___y_1726_);
lean_dec_ref(v___y_1725_);
if (lean_obj_tag(v___x_1741_) == 0)
{
lean_dec_ref(v___x_1741_);
v_as_x27_1694_ = v_tail_1709_;
v_b_1695_ = v___x_1713_;
goto _start;
}
else
{
lean_dec(v_tail_1709_);
lean_dec(v___y_1705_);
lean_dec_ref(v___y_1704_);
lean_dec(v___y_1703_);
lean_dec_ref(v___y_1702_);
lean_dec(v___y_1701_);
lean_dec_ref(v___y_1700_);
lean_dec(v___y_1699_);
lean_dec_ref(v___y_1698_);
lean_dec(v___y_1697_);
lean_dec(v___y_1696_);
lean_dec_ref(v_a_1693_);
return v___x_1741_;
}
}
}
else
{
lean_object* v_a_1744_; lean_object* v___x_1746_; uint8_t v_isShared_1747_; uint8_t v_isSharedCheck_1751_; 
lean_dec(v___y_1728_);
lean_dec_ref(v___y_1727_);
lean_dec(v___y_1726_);
lean_dec_ref(v___y_1725_);
lean_del_object(v___x_1711_);
lean_dec(v_tail_1709_);
lean_dec(v___y_1705_);
lean_dec_ref(v___y_1704_);
lean_dec(v___y_1703_);
lean_dec_ref(v___y_1702_);
lean_dec(v___y_1701_);
lean_dec_ref(v___y_1700_);
lean_dec(v___y_1699_);
lean_dec_ref(v___y_1698_);
lean_dec(v___y_1697_);
lean_dec(v___y_1696_);
lean_dec_ref(v_a_1693_);
v_a_1744_ = lean_ctor_get(v___x_1735_, 0);
v_isSharedCheck_1751_ = !lean_is_exclusive(v___x_1735_);
if (v_isSharedCheck_1751_ == 0)
{
v___x_1746_ = v___x_1735_;
v_isShared_1747_ = v_isSharedCheck_1751_;
goto v_resetjp_1745_;
}
else
{
lean_inc(v_a_1744_);
lean_dec(v___x_1735_);
v___x_1746_ = lean_box(0);
v_isShared_1747_ = v_isSharedCheck_1751_;
goto v_resetjp_1745_;
}
v_resetjp_1745_:
{
lean_object* v___x_1749_; 
if (v_isShared_1747_ == 0)
{
v___x_1749_ = v___x_1746_;
goto v_reusejp_1748_;
}
else
{
lean_object* v_reuseFailAlloc_1750_; 
v_reuseFailAlloc_1750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1750_, 0, v_a_1744_);
v___x_1749_ = v_reuseFailAlloc_1750_;
goto v_reusejp_1748_;
}
v_reusejp_1748_:
{
return v___x_1749_;
}
}
}
}
else
{
lean_dec(v___y_1728_);
lean_dec_ref(v___y_1727_);
lean_dec(v___y_1726_);
lean_dec_ref(v___y_1725_);
lean_dec(v_a_1716_);
lean_del_object(v___x_1711_);
lean_dec(v_tail_1709_);
lean_dec(v___y_1705_);
lean_dec_ref(v___y_1704_);
lean_dec(v___y_1703_);
lean_dec_ref(v___y_1702_);
lean_dec(v___y_1701_);
lean_dec_ref(v___y_1700_);
lean_dec(v___y_1699_);
lean_dec_ref(v___y_1698_);
lean_dec(v___y_1697_);
lean_dec(v___y_1696_);
lean_dec_ref(v_a_1693_);
return v___x_1734_;
}
}
}
else
{
lean_dec(v___y_1728_);
lean_dec_ref(v___y_1727_);
lean_dec(v___y_1726_);
lean_dec_ref(v___y_1725_);
lean_dec(v___y_1724_);
lean_dec_ref(v___y_1723_);
lean_dec(v___y_1722_);
lean_dec_ref(v___y_1721_);
lean_dec(v___y_1720_);
lean_dec(v___y_1719_);
lean_dec(v_a_1716_);
lean_del_object(v___x_1711_);
lean_dec(v_tail_1709_);
lean_dec(v___y_1705_);
lean_dec_ref(v___y_1704_);
lean_dec(v___y_1703_);
lean_dec_ref(v___y_1702_);
lean_dec(v___y_1701_);
lean_dec_ref(v___y_1700_);
lean_dec(v___y_1699_);
lean_dec_ref(v___y_1698_);
lean_dec(v___y_1697_);
lean_dec(v___y_1696_);
lean_dec_ref(v_a_1693_);
return v___x_1729_;
}
}
}
else
{
lean_object* v_a_1762_; lean_object* v___x_1764_; uint8_t v_isShared_1765_; uint8_t v_isSharedCheck_1769_; 
lean_del_object(v___x_1711_);
lean_dec(v_tail_1709_);
lean_dec(v_head_1708_);
lean_dec(v___y_1705_);
lean_dec_ref(v___y_1704_);
lean_dec(v___y_1703_);
lean_dec_ref(v___y_1702_);
lean_dec(v___y_1701_);
lean_dec_ref(v___y_1700_);
lean_dec(v___y_1699_);
lean_dec_ref(v___y_1698_);
lean_dec(v___y_1697_);
lean_dec(v___y_1696_);
lean_dec_ref(v_a_1693_);
v_a_1762_ = lean_ctor_get(v___x_1715_, 0);
v_isSharedCheck_1769_ = !lean_is_exclusive(v___x_1715_);
if (v_isSharedCheck_1769_ == 0)
{
v___x_1764_ = v___x_1715_;
v_isShared_1765_ = v_isSharedCheck_1769_;
goto v_resetjp_1763_;
}
else
{
lean_inc(v_a_1762_);
lean_dec(v___x_1715_);
v___x_1764_ = lean_box(0);
v_isShared_1765_ = v_isSharedCheck_1769_;
goto v_resetjp_1763_;
}
v_resetjp_1763_:
{
lean_object* v___x_1767_; 
if (v_isShared_1765_ == 0)
{
v___x_1767_ = v___x_1764_;
goto v_reusejp_1766_;
}
else
{
lean_object* v_reuseFailAlloc_1768_; 
v_reuseFailAlloc_1768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1768_, 0, v_a_1762_);
v___x_1767_ = v_reuseFailAlloc_1768_;
goto v_reusejp_1766_;
}
v_reusejp_1766_:
{
return v___x_1767_;
}
}
}
}
else
{
lean_del_object(v___x_1711_);
lean_dec(v_head_1708_);
v_as_x27_1694_ = v_tail_1709_;
v_b_1695_ = v___x_1713_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__2___redArg___boxed(lean_object* v_a_1772_, lean_object* v_as_x27_1773_, lean_object* v_b_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_){
_start:
{
lean_object* v_res_1786_; 
v_res_1786_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__2___redArg(v_a_1772_, v_as_x27_1773_, v_b_1774_, v___y_1775_, v___y_1776_, v___y_1777_, v___y_1778_, v___y_1779_, v___y_1780_, v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_);
return v_res_1786_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__3___redArg(lean_object* v_a_1787_, lean_object* v_as_x27_1788_, lean_object* v_b_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_){
_start:
{
if (lean_obj_tag(v_as_x27_1788_) == 0)
{
lean_object* v___x_1801_; 
lean_dec(v___y_1799_);
lean_dec_ref(v___y_1798_);
lean_dec(v___y_1797_);
lean_dec_ref(v___y_1796_);
lean_dec(v___y_1795_);
lean_dec_ref(v___y_1794_);
lean_dec(v___y_1793_);
lean_dec_ref(v___y_1792_);
lean_dec(v___y_1791_);
lean_dec(v___y_1790_);
lean_dec(v_a_1787_);
v___x_1801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1801_, 0, v_b_1789_);
return v___x_1801_;
}
else
{
lean_object* v_head_1802_; lean_object* v_tail_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; 
v_head_1802_ = lean_ctor_get(v_as_x27_1788_, 0);
lean_inc(v_head_1802_);
v_tail_1803_ = lean_ctor_get(v_as_x27_1788_, 1);
lean_inc(v_tail_1803_);
lean_dec_ref(v_as_x27_1788_);
v___x_1804_ = lean_box(0);
lean_inc(v___y_1799_);
lean_inc_ref(v___y_1798_);
lean_inc(v___y_1797_);
lean_inc_ref(v___y_1796_);
lean_inc(v___y_1795_);
lean_inc_ref(v___y_1794_);
lean_inc(v___y_1793_);
lean_inc_ref(v___y_1792_);
lean_inc(v___y_1791_);
lean_inc(v___y_1790_);
lean_inc(v_a_1787_);
v___x_1805_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__2___redArg(v_head_1802_, v_a_1787_, v___x_1804_, v___y_1790_, v___y_1791_, v___y_1792_, v___y_1793_, v___y_1794_, v___y_1795_, v___y_1796_, v___y_1797_, v___y_1798_, v___y_1799_);
if (lean_obj_tag(v___x_1805_) == 0)
{
lean_dec_ref(v___x_1805_);
v_as_x27_1788_ = v_tail_1803_;
v_b_1789_ = v___x_1804_;
goto _start;
}
else
{
lean_dec(v_tail_1803_);
lean_dec(v___y_1799_);
lean_dec_ref(v___y_1798_);
lean_dec(v___y_1797_);
lean_dec_ref(v___y_1796_);
lean_dec(v___y_1795_);
lean_dec_ref(v___y_1794_);
lean_dec(v___y_1793_);
lean_dec_ref(v___y_1792_);
lean_dec(v___y_1791_);
lean_dec(v___y_1790_);
lean_dec(v_a_1787_);
return v___x_1805_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__3___redArg___boxed(lean_object* v_a_1807_, lean_object* v_as_x27_1808_, lean_object* v_b_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_){
_start:
{
lean_object* v_res_1821_; 
v_res_1821_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__3___redArg(v_a_1807_, v_as_x27_1808_, v_b_1809_, v___y_1810_, v___y_1811_, v___y_1812_, v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_);
return v_res_1821_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__4___redArg(lean_object* v_as_x27_1822_, lean_object* v_b_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_){
_start:
{
if (lean_obj_tag(v_as_x27_1822_) == 0)
{
lean_object* v___x_1835_; 
lean_dec(v___y_1833_);
lean_dec_ref(v___y_1832_);
lean_dec(v___y_1831_);
lean_dec_ref(v___y_1830_);
lean_dec(v___y_1829_);
lean_dec_ref(v___y_1828_);
lean_dec(v___y_1827_);
lean_dec_ref(v___y_1826_);
lean_dec(v___y_1825_);
lean_dec(v___y_1824_);
v___x_1835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1835_, 0, v_b_1823_);
return v___x_1835_;
}
else
{
lean_object* v_head_1836_; lean_object* v_tail_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; 
v_head_1836_ = lean_ctor_get(v_as_x27_1822_, 0);
lean_inc(v_head_1836_);
v_tail_1837_ = lean_ctor_get(v_as_x27_1822_, 1);
lean_inc(v_tail_1837_);
lean_dec_ref(v_as_x27_1822_);
v___x_1838_ = lean_box(0);
lean_inc(v___y_1833_);
lean_inc_ref(v___y_1832_);
lean_inc(v___y_1831_);
lean_inc_ref(v___y_1830_);
lean_inc(v___y_1829_);
lean_inc_ref(v___y_1828_);
lean_inc(v___y_1827_);
lean_inc_ref(v___y_1826_);
lean_inc(v___y_1825_);
lean_inc(v___y_1824_);
lean_inc(v_head_1836_);
v___x_1839_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__3___redArg(v_head_1836_, v_head_1836_, v___x_1838_, v___y_1824_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_, v___y_1833_);
if (lean_obj_tag(v___x_1839_) == 0)
{
lean_dec_ref(v___x_1839_);
v_as_x27_1822_ = v_tail_1837_;
v_b_1823_ = v___x_1838_;
goto _start;
}
else
{
lean_dec(v_tail_1837_);
lean_dec(v___y_1833_);
lean_dec_ref(v___y_1832_);
lean_dec(v___y_1831_);
lean_dec_ref(v___y_1830_);
lean_dec(v___y_1829_);
lean_dec_ref(v___y_1828_);
lean_dec(v___y_1827_);
lean_dec_ref(v___y_1826_);
lean_dec(v___y_1825_);
lean_dec(v___y_1824_);
return v___x_1839_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__4___redArg___boxed(lean_object* v_as_x27_1841_, lean_object* v_b_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_){
_start:
{
lean_object* v_res_1854_; 
v_res_1854_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__4___redArg(v_as_x27_1841_, v_b_1842_, v___y_1843_, v___y_1844_, v___y_1845_, v___y_1846_, v___y_1847_, v___y_1848_, v___y_1849_, v___y_1850_, v___y_1851_, v___y_1852_);
return v_res_1854_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs(lean_object* v_a_1855_, lean_object* v_a_1856_, lean_object* v_a_1857_, lean_object* v_a_1858_, lean_object* v_a_1859_, lean_object* v_a_1860_, lean_object* v_a_1861_, lean_object* v_a_1862_, lean_object* v_a_1863_, lean_object* v_a_1864_){
_start:
{
lean_object* v___x_1866_; uint8_t v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; 
v___x_1866_ = lean_st_ref_get(v_a_1855_);
v___x_1867_ = 0;
v___x_1868_ = l_Lean_Meta_Grind_Goal_getEqcs(v___x_1866_, v___x_1867_);
v___x_1869_ = lean_box(0);
v___x_1870_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__4___redArg(v___x_1868_, v___x_1869_, v_a_1855_, v_a_1856_, v_a_1857_, v_a_1858_, v_a_1859_, v_a_1860_, v_a_1861_, v_a_1862_, v_a_1863_, v_a_1864_);
if (lean_obj_tag(v___x_1870_) == 0)
{
lean_object* v___x_1872_; uint8_t v_isShared_1873_; uint8_t v_isSharedCheck_1877_; 
v_isSharedCheck_1877_ = !lean_is_exclusive(v___x_1870_);
if (v_isSharedCheck_1877_ == 0)
{
lean_object* v_unused_1878_; 
v_unused_1878_ = lean_ctor_get(v___x_1870_, 0);
lean_dec(v_unused_1878_);
v___x_1872_ = v___x_1870_;
v_isShared_1873_ = v_isSharedCheck_1877_;
goto v_resetjp_1871_;
}
else
{
lean_dec(v___x_1870_);
v___x_1872_ = lean_box(0);
v_isShared_1873_ = v_isSharedCheck_1877_;
goto v_resetjp_1871_;
}
v_resetjp_1871_:
{
lean_object* v___x_1875_; 
if (v_isShared_1873_ == 0)
{
lean_ctor_set(v___x_1872_, 0, v___x_1869_);
v___x_1875_ = v___x_1872_;
goto v_reusejp_1874_;
}
else
{
lean_object* v_reuseFailAlloc_1876_; 
v_reuseFailAlloc_1876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1876_, 0, v___x_1869_);
v___x_1875_ = v_reuseFailAlloc_1876_;
goto v_reusejp_1874_;
}
v_reusejp_1874_:
{
return v___x_1875_;
}
}
}
else
{
return v___x_1870_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs___boxed(lean_object* v_a_1879_, lean_object* v_a_1880_, lean_object* v_a_1881_, lean_object* v_a_1882_, lean_object* v_a_1883_, lean_object* v_a_1884_, lean_object* v_a_1885_, lean_object* v_a_1886_, lean_object* v_a_1887_, lean_object* v_a_1888_, lean_object* v_a_1889_){
_start:
{
lean_object* v_res_1890_; 
v_res_1890_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs(v_a_1879_, v_a_1880_, v_a_1881_, v_a_1882_, v_a_1883_, v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_, v_a_1888_);
return v_res_1890_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1(lean_object* v_cls_1891_, lean_object* v_msg_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_){
_start:
{
lean_object* v___x_1904_; 
v___x_1904_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg(v_cls_1891_, v_msg_1892_, v___y_1899_, v___y_1900_, v___y_1901_, v___y_1902_);
return v___x_1904_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___boxed(lean_object* v_cls_1905_, lean_object* v_msg_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_){
_start:
{
lean_object* v_res_1918_; 
v_res_1918_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1(v_cls_1905_, v_msg_1906_, v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_, v___y_1912_, v___y_1913_, v___y_1914_, v___y_1915_, v___y_1916_);
lean_dec(v___y_1916_);
lean_dec_ref(v___y_1915_);
lean_dec(v___y_1914_);
lean_dec_ref(v___y_1913_);
lean_dec(v___y_1912_);
lean_dec_ref(v___y_1911_);
lean_dec(v___y_1910_);
lean_dec_ref(v___y_1909_);
lean_dec(v___y_1908_);
lean_dec(v___y_1907_);
return v_res_1918_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__2(lean_object* v_a_1919_, lean_object* v_as_1920_, lean_object* v_as_x27_1921_, lean_object* v_b_1922_, lean_object* v_a_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_){
_start:
{
lean_object* v___x_1935_; 
v___x_1935_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__2___redArg(v_a_1919_, v_as_x27_1921_, v_b_1922_, v___y_1924_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_, v___y_1929_, v___y_1930_, v___y_1931_, v___y_1932_, v___y_1933_);
return v___x_1935_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__2___boxed(lean_object* v_a_1936_, lean_object* v_as_1937_, lean_object* v_as_x27_1938_, lean_object* v_b_1939_, lean_object* v_a_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_){
_start:
{
lean_object* v_res_1952_; 
v_res_1952_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__2(v_a_1936_, v_as_1937_, v_as_x27_1938_, v_b_1939_, v_a_1940_, v___y_1941_, v___y_1942_, v___y_1943_, v___y_1944_, v___y_1945_, v___y_1946_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_);
lean_dec(v_as_1937_);
return v_res_1952_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__3(lean_object* v_a_1953_, lean_object* v_as_1954_, lean_object* v_as_x27_1955_, lean_object* v_b_1956_, lean_object* v_a_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_){
_start:
{
lean_object* v___x_1969_; 
v___x_1969_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__3___redArg(v_a_1953_, v_as_x27_1955_, v_b_1956_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_, v___y_1966_, v___y_1967_);
return v___x_1969_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__3___boxed(lean_object* v_a_1970_, lean_object* v_as_1971_, lean_object* v_as_x27_1972_, lean_object* v_b_1973_, lean_object* v_a_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_){
_start:
{
lean_object* v_res_1986_; 
v_res_1986_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__3(v_a_1970_, v_as_1971_, v_as_x27_1972_, v_b_1973_, v_a_1974_, v___y_1975_, v___y_1976_, v___y_1977_, v___y_1978_, v___y_1979_, v___y_1980_, v___y_1981_, v___y_1982_, v___y_1983_, v___y_1984_);
lean_dec(v_as_1971_);
return v_res_1986_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__4(lean_object* v_as_1987_, lean_object* v_as_x27_1988_, lean_object* v_b_1989_, lean_object* v_a_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_){
_start:
{
lean_object* v___x_2002_; 
v___x_2002_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__4___redArg(v_as_x27_1988_, v_b_1989_, v___y_1991_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_, v___y_1997_, v___y_1998_, v___y_1999_, v___y_2000_);
return v___x_2002_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__4___boxed(lean_object* v_as_2003_, lean_object* v_as_x27_2004_, lean_object* v_b_2005_, lean_object* v_a_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_){
_start:
{
lean_object* v_res_2018_; 
v_res_2018_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__4(v_as_2003_, v_as_x27_2004_, v_b_2005_, v_a_2006_, v___y_2007_, v___y_2008_, v___y_2009_, v___y_2010_, v___y_2011_, v___y_2012_, v___y_2013_, v___y_2014_, v___y_2015_, v___y_2016_);
lean_dec(v_as_2003_);
return v_res_2018_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_Grind_checkInvariants_spec__0(lean_object* v_opts_2019_, lean_object* v_opt_2020_){
_start:
{
lean_object* v_name_2021_; lean_object* v_defValue_2022_; lean_object* v_map_2023_; lean_object* v___x_2024_; 
v_name_2021_ = lean_ctor_get(v_opt_2020_, 0);
v_defValue_2022_ = lean_ctor_get(v_opt_2020_, 1);
v_map_2023_ = lean_ctor_get(v_opts_2019_, 0);
v___x_2024_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2023_, v_name_2021_);
if (lean_obj_tag(v___x_2024_) == 0)
{
uint8_t v___x_2025_; 
v___x_2025_ = lean_unbox(v_defValue_2022_);
return v___x_2025_;
}
else
{
lean_object* v_val_2026_; 
v_val_2026_ = lean_ctor_get(v___x_2024_, 0);
lean_inc(v_val_2026_);
lean_dec_ref(v___x_2024_);
if (lean_obj_tag(v_val_2026_) == 1)
{
uint8_t v_v_2027_; 
v_v_2027_ = lean_ctor_get_uint8(v_val_2026_, 0);
lean_dec_ref(v_val_2026_);
return v_v_2027_;
}
else
{
uint8_t v___x_2028_; 
lean_dec(v_val_2026_);
v___x_2028_ = lean_unbox(v_defValue_2022_);
return v___x_2028_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Grind_checkInvariants_spec__0___boxed(lean_object* v_opts_2029_, lean_object* v_opt_2030_){
_start:
{
uint8_t v_res_2031_; lean_object* v_r_2032_; 
v_res_2031_ = l_Lean_Option_get___at___00Lean_Meta_Grind_checkInvariants_spec__0(v_opts_2029_, v_opt_2030_);
lean_dec_ref(v_opt_2030_);
lean_dec_ref(v_opts_2029_);
v_r_2032_ = lean_box(v_res_2031_);
return v_r_2032_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__2_spec__5(lean_object* v_as_2033_, size_t v_sz_2034_, size_t v_i_2035_, lean_object* v_b_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_){
_start:
{
uint8_t v___x_2048_; 
v___x_2048_ = lean_usize_dec_lt(v_i_2035_, v_sz_2034_);
if (v___x_2048_ == 0)
{
lean_object* v___x_2049_; 
lean_dec(v___y_2046_);
lean_dec_ref(v___y_2045_);
lean_dec(v___y_2044_);
lean_dec_ref(v___y_2043_);
lean_dec(v___y_2042_);
lean_dec_ref(v___y_2041_);
lean_dec(v___y_2040_);
lean_dec_ref(v___y_2039_);
lean_dec(v___y_2038_);
lean_dec(v___y_2037_);
v___x_2049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2049_, 0, v_b_2036_);
return v___x_2049_;
}
else
{
lean_object* v___x_2050_; lean_object* v_a_2051_; lean_object* v___x_2052_; 
lean_dec_ref(v_b_2036_);
v___x_2050_ = lean_st_ref_get(v___y_2037_);
v_a_2051_ = lean_array_uget_borrowed(v_as_2033_, v_i_2035_);
lean_inc(v_a_2051_);
v___x_2052_ = l_Lean_Meta_Grind_Goal_getENode(v___x_2050_, v_a_2051_, v___y_2043_, v___y_2044_, v___y_2045_, v___y_2046_);
if (lean_obj_tag(v___x_2052_) == 0)
{
lean_object* v_a_2053_; lean_object* v_self_2054_; lean_object* v___x_2055_; 
v_a_2053_ = lean_ctor_get(v___x_2052_, 0);
lean_inc(v_a_2053_);
lean_dec_ref(v___x_2052_);
v_self_2054_ = lean_ctor_get(v_a_2053_, 0);
lean_inc(v___y_2046_);
lean_inc_ref(v___y_2045_);
lean_inc(v___y_2044_);
lean_inc_ref(v___y_2043_);
lean_inc(v___y_2042_);
lean_inc_ref(v___y_2041_);
lean_inc(v___y_2040_);
lean_inc_ref(v___y_2039_);
lean_inc(v___y_2038_);
lean_inc(v___y_2037_);
lean_inc_ref(v_self_2054_);
v___x_2055_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents(v_self_2054_, v___y_2037_, v___y_2038_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_, v___y_2043_, v___y_2044_, v___y_2045_, v___y_2046_);
if (lean_obj_tag(v___x_2055_) == 0)
{
lean_object* v___x_2056_; lean_object* v_a_2058_; lean_object* v___x_2063_; uint8_t v___x_2064_; 
lean_dec_ref(v___x_2055_);
v___x_2056_ = lean_box(0);
v___x_2063_ = lean_box(0);
v___x_2064_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_2053_);
if (v___x_2064_ == 0)
{
lean_dec(v_a_2053_);
v_a_2058_ = v___x_2063_;
goto v___jp_2057_;
}
else
{
lean_object* v___x_2065_; 
lean_inc(v___y_2046_);
lean_inc_ref(v___y_2045_);
lean_inc(v___y_2044_);
lean_inc_ref(v___y_2043_);
lean_inc(v___y_2042_);
lean_inc_ref(v___y_2041_);
lean_inc(v___y_2040_);
lean_inc_ref(v___y_2039_);
lean_inc(v___y_2038_);
lean_inc(v___y_2037_);
v___x_2065_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc(v_a_2053_, v___y_2037_, v___y_2038_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_, v___y_2043_, v___y_2044_, v___y_2045_, v___y_2046_);
if (lean_obj_tag(v___x_2065_) == 0)
{
lean_dec_ref(v___x_2065_);
v_a_2058_ = v___x_2063_;
goto v___jp_2057_;
}
else
{
lean_object* v_a_2066_; lean_object* v___x_2068_; uint8_t v_isShared_2069_; uint8_t v_isSharedCheck_2073_; 
lean_dec(v___y_2046_);
lean_dec_ref(v___y_2045_);
lean_dec(v___y_2044_);
lean_dec_ref(v___y_2043_);
lean_dec(v___y_2042_);
lean_dec_ref(v___y_2041_);
lean_dec(v___y_2040_);
lean_dec_ref(v___y_2039_);
lean_dec(v___y_2038_);
lean_dec(v___y_2037_);
v_a_2066_ = lean_ctor_get(v___x_2065_, 0);
v_isSharedCheck_2073_ = !lean_is_exclusive(v___x_2065_);
if (v_isSharedCheck_2073_ == 0)
{
v___x_2068_ = v___x_2065_;
v_isShared_2069_ = v_isSharedCheck_2073_;
goto v_resetjp_2067_;
}
else
{
lean_inc(v_a_2066_);
lean_dec(v___x_2065_);
v___x_2068_ = lean_box(0);
v_isShared_2069_ = v_isSharedCheck_2073_;
goto v_resetjp_2067_;
}
v_resetjp_2067_:
{
lean_object* v___x_2071_; 
if (v_isShared_2069_ == 0)
{
v___x_2071_ = v___x_2068_;
goto v_reusejp_2070_;
}
else
{
lean_object* v_reuseFailAlloc_2072_; 
v_reuseFailAlloc_2072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2072_, 0, v_a_2066_);
v___x_2071_ = v_reuseFailAlloc_2072_;
goto v_reusejp_2070_;
}
v_reusejp_2070_:
{
return v___x_2071_;
}
}
}
}
v___jp_2057_:
{
lean_object* v___x_2059_; size_t v___x_2060_; size_t v___x_2061_; 
v___x_2059_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2059_, 0, v___x_2056_);
lean_ctor_set(v___x_2059_, 1, v_a_2058_);
v___x_2060_ = ((size_t)1ULL);
v___x_2061_ = lean_usize_add(v_i_2035_, v___x_2060_);
v_i_2035_ = v___x_2061_;
v_b_2036_ = v___x_2059_;
goto _start;
}
}
else
{
lean_object* v_a_2074_; lean_object* v___x_2076_; uint8_t v_isShared_2077_; uint8_t v_isSharedCheck_2081_; 
lean_dec(v_a_2053_);
lean_dec(v___y_2046_);
lean_dec_ref(v___y_2045_);
lean_dec(v___y_2044_);
lean_dec_ref(v___y_2043_);
lean_dec(v___y_2042_);
lean_dec_ref(v___y_2041_);
lean_dec(v___y_2040_);
lean_dec_ref(v___y_2039_);
lean_dec(v___y_2038_);
lean_dec(v___y_2037_);
v_a_2074_ = lean_ctor_get(v___x_2055_, 0);
v_isSharedCheck_2081_ = !lean_is_exclusive(v___x_2055_);
if (v_isSharedCheck_2081_ == 0)
{
v___x_2076_ = v___x_2055_;
v_isShared_2077_ = v_isSharedCheck_2081_;
goto v_resetjp_2075_;
}
else
{
lean_inc(v_a_2074_);
lean_dec(v___x_2055_);
v___x_2076_ = lean_box(0);
v_isShared_2077_ = v_isSharedCheck_2081_;
goto v_resetjp_2075_;
}
v_resetjp_2075_:
{
lean_object* v___x_2079_; 
if (v_isShared_2077_ == 0)
{
v___x_2079_ = v___x_2076_;
goto v_reusejp_2078_;
}
else
{
lean_object* v_reuseFailAlloc_2080_; 
v_reuseFailAlloc_2080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2080_, 0, v_a_2074_);
v___x_2079_ = v_reuseFailAlloc_2080_;
goto v_reusejp_2078_;
}
v_reusejp_2078_:
{
return v___x_2079_;
}
}
}
}
else
{
lean_object* v_a_2082_; lean_object* v___x_2084_; uint8_t v_isShared_2085_; uint8_t v_isSharedCheck_2089_; 
lean_dec(v___y_2046_);
lean_dec_ref(v___y_2045_);
lean_dec(v___y_2044_);
lean_dec_ref(v___y_2043_);
lean_dec(v___y_2042_);
lean_dec_ref(v___y_2041_);
lean_dec(v___y_2040_);
lean_dec_ref(v___y_2039_);
lean_dec(v___y_2038_);
lean_dec(v___y_2037_);
v_a_2082_ = lean_ctor_get(v___x_2052_, 0);
v_isSharedCheck_2089_ = !lean_is_exclusive(v___x_2052_);
if (v_isSharedCheck_2089_ == 0)
{
v___x_2084_ = v___x_2052_;
v_isShared_2085_ = v_isSharedCheck_2089_;
goto v_resetjp_2083_;
}
else
{
lean_inc(v_a_2082_);
lean_dec(v___x_2052_);
v___x_2084_ = lean_box(0);
v_isShared_2085_ = v_isSharedCheck_2089_;
goto v_resetjp_2083_;
}
v_resetjp_2083_:
{
lean_object* v___x_2087_; 
if (v_isShared_2085_ == 0)
{
v___x_2087_ = v___x_2084_;
goto v_reusejp_2086_;
}
else
{
lean_object* v_reuseFailAlloc_2088_; 
v_reuseFailAlloc_2088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2088_, 0, v_a_2082_);
v___x_2087_ = v_reuseFailAlloc_2088_;
goto v_reusejp_2086_;
}
v_reusejp_2086_:
{
return v___x_2087_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__2_spec__5___boxed(lean_object* v_as_2090_, lean_object* v_sz_2091_, lean_object* v_i_2092_, lean_object* v_b_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_){
_start:
{
size_t v_sz_boxed_2105_; size_t v_i_boxed_2106_; lean_object* v_res_2107_; 
v_sz_boxed_2105_ = lean_unbox_usize(v_sz_2091_);
lean_dec(v_sz_2091_);
v_i_boxed_2106_ = lean_unbox_usize(v_i_2092_);
lean_dec(v_i_2092_);
v_res_2107_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__2_spec__5(v_as_2090_, v_sz_boxed_2105_, v_i_boxed_2106_, v_b_2093_, v___y_2094_, v___y_2095_, v___y_2096_, v___y_2097_, v___y_2098_, v___y_2099_, v___y_2100_, v___y_2101_, v___y_2102_, v___y_2103_);
lean_dec_ref(v_as_2090_);
return v_res_2107_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__2(lean_object* v_as_2111_, size_t v_sz_2112_, size_t v_i_2113_, lean_object* v_b_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_){
_start:
{
uint8_t v___x_2126_; 
v___x_2126_ = lean_usize_dec_lt(v_i_2113_, v_sz_2112_);
if (v___x_2126_ == 0)
{
lean_object* v___x_2127_; 
lean_dec(v___y_2124_);
lean_dec_ref(v___y_2123_);
lean_dec(v___y_2122_);
lean_dec_ref(v___y_2121_);
lean_dec(v___y_2120_);
lean_dec_ref(v___y_2119_);
lean_dec(v___y_2118_);
lean_dec_ref(v___y_2117_);
lean_dec(v___y_2116_);
lean_dec(v___y_2115_);
v___x_2127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2127_, 0, v_b_2114_);
return v___x_2127_;
}
else
{
lean_object* v___x_2128_; lean_object* v_a_2129_; lean_object* v___x_2130_; 
lean_dec_ref(v_b_2114_);
v___x_2128_ = lean_st_ref_get(v___y_2115_);
v_a_2129_ = lean_array_uget_borrowed(v_as_2111_, v_i_2113_);
lean_inc(v_a_2129_);
v___x_2130_ = l_Lean_Meta_Grind_Goal_getENode(v___x_2128_, v_a_2129_, v___y_2121_, v___y_2122_, v___y_2123_, v___y_2124_);
if (lean_obj_tag(v___x_2130_) == 0)
{
lean_object* v_a_2131_; lean_object* v_self_2132_; lean_object* v___x_2133_; 
v_a_2131_ = lean_ctor_get(v___x_2130_, 0);
lean_inc(v_a_2131_);
lean_dec_ref(v___x_2130_);
v_self_2132_ = lean_ctor_get(v_a_2131_, 0);
lean_inc(v___y_2124_);
lean_inc_ref(v___y_2123_);
lean_inc(v___y_2122_);
lean_inc_ref(v___y_2121_);
lean_inc(v___y_2120_);
lean_inc_ref(v___y_2119_);
lean_inc(v___y_2118_);
lean_inc_ref(v___y_2117_);
lean_inc(v___y_2116_);
lean_inc(v___y_2115_);
lean_inc_ref(v_self_2132_);
v___x_2133_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents(v_self_2132_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_, v___y_2122_, v___y_2123_, v___y_2124_);
if (lean_obj_tag(v___x_2133_) == 0)
{
uint8_t v___x_2139_; 
lean_dec_ref(v___x_2133_);
v___x_2139_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_2131_);
if (v___x_2139_ == 0)
{
lean_dec(v_a_2131_);
goto v___jp_2134_;
}
else
{
lean_object* v___x_2140_; 
lean_inc(v___y_2124_);
lean_inc_ref(v___y_2123_);
lean_inc(v___y_2122_);
lean_inc_ref(v___y_2121_);
lean_inc(v___y_2120_);
lean_inc_ref(v___y_2119_);
lean_inc(v___y_2118_);
lean_inc_ref(v___y_2117_);
lean_inc(v___y_2116_);
lean_inc(v___y_2115_);
v___x_2140_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc(v_a_2131_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_, v___y_2122_, v___y_2123_, v___y_2124_);
if (lean_obj_tag(v___x_2140_) == 0)
{
lean_dec_ref(v___x_2140_);
goto v___jp_2134_;
}
else
{
lean_object* v_a_2141_; lean_object* v___x_2143_; uint8_t v_isShared_2144_; uint8_t v_isSharedCheck_2148_; 
lean_dec(v___y_2124_);
lean_dec_ref(v___y_2123_);
lean_dec(v___y_2122_);
lean_dec_ref(v___y_2121_);
lean_dec(v___y_2120_);
lean_dec_ref(v___y_2119_);
lean_dec(v___y_2118_);
lean_dec_ref(v___y_2117_);
lean_dec(v___y_2116_);
lean_dec(v___y_2115_);
v_a_2141_ = lean_ctor_get(v___x_2140_, 0);
v_isSharedCheck_2148_ = !lean_is_exclusive(v___x_2140_);
if (v_isSharedCheck_2148_ == 0)
{
v___x_2143_ = v___x_2140_;
v_isShared_2144_ = v_isSharedCheck_2148_;
goto v_resetjp_2142_;
}
else
{
lean_inc(v_a_2141_);
lean_dec(v___x_2140_);
v___x_2143_ = lean_box(0);
v_isShared_2144_ = v_isSharedCheck_2148_;
goto v_resetjp_2142_;
}
v_resetjp_2142_:
{
lean_object* v___x_2146_; 
if (v_isShared_2144_ == 0)
{
v___x_2146_ = v___x_2143_;
goto v_reusejp_2145_;
}
else
{
lean_object* v_reuseFailAlloc_2147_; 
v_reuseFailAlloc_2147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2147_, 0, v_a_2141_);
v___x_2146_ = v_reuseFailAlloc_2147_;
goto v_reusejp_2145_;
}
v_reusejp_2145_:
{
return v___x_2146_;
}
}
}
}
v___jp_2134_:
{
lean_object* v___x_2135_; size_t v___x_2136_; size_t v___x_2137_; lean_object* v___x_2138_; 
v___x_2135_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__2___closed__0));
v___x_2136_ = ((size_t)1ULL);
v___x_2137_ = lean_usize_add(v_i_2113_, v___x_2136_);
v___x_2138_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__2_spec__5(v_as_2111_, v_sz_2112_, v___x_2137_, v___x_2135_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_, v___y_2122_, v___y_2123_, v___y_2124_);
return v___x_2138_;
}
}
else
{
lean_object* v_a_2149_; lean_object* v___x_2151_; uint8_t v_isShared_2152_; uint8_t v_isSharedCheck_2156_; 
lean_dec(v_a_2131_);
lean_dec(v___y_2124_);
lean_dec_ref(v___y_2123_);
lean_dec(v___y_2122_);
lean_dec_ref(v___y_2121_);
lean_dec(v___y_2120_);
lean_dec_ref(v___y_2119_);
lean_dec(v___y_2118_);
lean_dec_ref(v___y_2117_);
lean_dec(v___y_2116_);
lean_dec(v___y_2115_);
v_a_2149_ = lean_ctor_get(v___x_2133_, 0);
v_isSharedCheck_2156_ = !lean_is_exclusive(v___x_2133_);
if (v_isSharedCheck_2156_ == 0)
{
v___x_2151_ = v___x_2133_;
v_isShared_2152_ = v_isSharedCheck_2156_;
goto v_resetjp_2150_;
}
else
{
lean_inc(v_a_2149_);
lean_dec(v___x_2133_);
v___x_2151_ = lean_box(0);
v_isShared_2152_ = v_isSharedCheck_2156_;
goto v_resetjp_2150_;
}
v_resetjp_2150_:
{
lean_object* v___x_2154_; 
if (v_isShared_2152_ == 0)
{
v___x_2154_ = v___x_2151_;
goto v_reusejp_2153_;
}
else
{
lean_object* v_reuseFailAlloc_2155_; 
v_reuseFailAlloc_2155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2155_, 0, v_a_2149_);
v___x_2154_ = v_reuseFailAlloc_2155_;
goto v_reusejp_2153_;
}
v_reusejp_2153_:
{
return v___x_2154_;
}
}
}
}
else
{
lean_object* v_a_2157_; lean_object* v___x_2159_; uint8_t v_isShared_2160_; uint8_t v_isSharedCheck_2164_; 
lean_dec(v___y_2124_);
lean_dec_ref(v___y_2123_);
lean_dec(v___y_2122_);
lean_dec_ref(v___y_2121_);
lean_dec(v___y_2120_);
lean_dec_ref(v___y_2119_);
lean_dec(v___y_2118_);
lean_dec_ref(v___y_2117_);
lean_dec(v___y_2116_);
lean_dec(v___y_2115_);
v_a_2157_ = lean_ctor_get(v___x_2130_, 0);
v_isSharedCheck_2164_ = !lean_is_exclusive(v___x_2130_);
if (v_isSharedCheck_2164_ == 0)
{
v___x_2159_ = v___x_2130_;
v_isShared_2160_ = v_isSharedCheck_2164_;
goto v_resetjp_2158_;
}
else
{
lean_inc(v_a_2157_);
lean_dec(v___x_2130_);
v___x_2159_ = lean_box(0);
v_isShared_2160_ = v_isSharedCheck_2164_;
goto v_resetjp_2158_;
}
v_resetjp_2158_:
{
lean_object* v___x_2162_; 
if (v_isShared_2160_ == 0)
{
v___x_2162_ = v___x_2159_;
goto v_reusejp_2161_;
}
else
{
lean_object* v_reuseFailAlloc_2163_; 
v_reuseFailAlloc_2163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2163_, 0, v_a_2157_);
v___x_2162_ = v_reuseFailAlloc_2163_;
goto v_reusejp_2161_;
}
v_reusejp_2161_:
{
return v___x_2162_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__2___boxed(lean_object* v_as_2165_, lean_object* v_sz_2166_, lean_object* v_i_2167_, lean_object* v_b_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_){
_start:
{
size_t v_sz_boxed_2180_; size_t v_i_boxed_2181_; lean_object* v_res_2182_; 
v_sz_boxed_2180_ = lean_unbox_usize(v_sz_2166_);
lean_dec(v_sz_2166_);
v_i_boxed_2181_ = lean_unbox_usize(v_i_2167_);
lean_dec(v_i_2167_);
v_res_2182_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__2(v_as_2165_, v_sz_boxed_2180_, v_i_boxed_2181_, v_b_2168_, v___y_2169_, v___y_2170_, v___y_2171_, v___y_2172_, v___y_2173_, v___y_2174_, v___y_2175_, v___y_2176_, v___y_2177_, v___y_2178_);
lean_dec_ref(v_as_2165_);
return v_res_2182_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__1_spec__3_spec__4(lean_object* v_as_2183_, size_t v_sz_2184_, size_t v_i_2185_, lean_object* v_b_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_){
_start:
{
uint8_t v___x_2198_; 
v___x_2198_ = lean_usize_dec_lt(v_i_2185_, v_sz_2184_);
if (v___x_2198_ == 0)
{
lean_object* v___x_2199_; 
lean_dec(v___y_2196_);
lean_dec_ref(v___y_2195_);
lean_dec(v___y_2194_);
lean_dec_ref(v___y_2193_);
lean_dec(v___y_2192_);
lean_dec_ref(v___y_2191_);
lean_dec(v___y_2190_);
lean_dec_ref(v___y_2189_);
lean_dec(v___y_2188_);
lean_dec(v___y_2187_);
v___x_2199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2199_, 0, v_b_2186_);
return v___x_2199_;
}
else
{
lean_object* v___x_2200_; lean_object* v_a_2201_; lean_object* v___x_2202_; 
lean_dec_ref(v_b_2186_);
v___x_2200_ = lean_st_ref_get(v___y_2187_);
v_a_2201_ = lean_array_uget_borrowed(v_as_2183_, v_i_2185_);
lean_inc(v_a_2201_);
v___x_2202_ = l_Lean_Meta_Grind_Goal_getENode(v___x_2200_, v_a_2201_, v___y_2193_, v___y_2194_, v___y_2195_, v___y_2196_);
if (lean_obj_tag(v___x_2202_) == 0)
{
lean_object* v_a_2203_; lean_object* v_self_2204_; lean_object* v___x_2205_; 
v_a_2203_ = lean_ctor_get(v___x_2202_, 0);
lean_inc(v_a_2203_);
lean_dec_ref(v___x_2202_);
v_self_2204_ = lean_ctor_get(v_a_2203_, 0);
lean_inc(v___y_2196_);
lean_inc_ref(v___y_2195_);
lean_inc(v___y_2194_);
lean_inc_ref(v___y_2193_);
lean_inc(v___y_2192_);
lean_inc_ref(v___y_2191_);
lean_inc(v___y_2190_);
lean_inc_ref(v___y_2189_);
lean_inc(v___y_2188_);
lean_inc(v___y_2187_);
lean_inc_ref(v_self_2204_);
v___x_2205_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents(v_self_2204_, v___y_2187_, v___y_2188_, v___y_2189_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_, v___y_2194_, v___y_2195_, v___y_2196_);
if (lean_obj_tag(v___x_2205_) == 0)
{
lean_object* v___x_2206_; lean_object* v_a_2208_; lean_object* v___x_2213_; uint8_t v___x_2214_; 
lean_dec_ref(v___x_2205_);
v___x_2206_ = lean_box(0);
v___x_2213_ = lean_box(0);
v___x_2214_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_2203_);
if (v___x_2214_ == 0)
{
lean_dec(v_a_2203_);
v_a_2208_ = v___x_2213_;
goto v___jp_2207_;
}
else
{
lean_object* v___x_2215_; 
lean_inc(v___y_2196_);
lean_inc_ref(v___y_2195_);
lean_inc(v___y_2194_);
lean_inc_ref(v___y_2193_);
lean_inc(v___y_2192_);
lean_inc_ref(v___y_2191_);
lean_inc(v___y_2190_);
lean_inc_ref(v___y_2189_);
lean_inc(v___y_2188_);
lean_inc(v___y_2187_);
v___x_2215_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc(v_a_2203_, v___y_2187_, v___y_2188_, v___y_2189_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_, v___y_2194_, v___y_2195_, v___y_2196_);
if (lean_obj_tag(v___x_2215_) == 0)
{
lean_dec_ref(v___x_2215_);
v_a_2208_ = v___x_2213_;
goto v___jp_2207_;
}
else
{
lean_object* v_a_2216_; lean_object* v___x_2218_; uint8_t v_isShared_2219_; uint8_t v_isSharedCheck_2223_; 
lean_dec(v___y_2196_);
lean_dec_ref(v___y_2195_);
lean_dec(v___y_2194_);
lean_dec_ref(v___y_2193_);
lean_dec(v___y_2192_);
lean_dec_ref(v___y_2191_);
lean_dec(v___y_2190_);
lean_dec_ref(v___y_2189_);
lean_dec(v___y_2188_);
lean_dec(v___y_2187_);
v_a_2216_ = lean_ctor_get(v___x_2215_, 0);
v_isSharedCheck_2223_ = !lean_is_exclusive(v___x_2215_);
if (v_isSharedCheck_2223_ == 0)
{
v___x_2218_ = v___x_2215_;
v_isShared_2219_ = v_isSharedCheck_2223_;
goto v_resetjp_2217_;
}
else
{
lean_inc(v_a_2216_);
lean_dec(v___x_2215_);
v___x_2218_ = lean_box(0);
v_isShared_2219_ = v_isSharedCheck_2223_;
goto v_resetjp_2217_;
}
v_resetjp_2217_:
{
lean_object* v___x_2221_; 
if (v_isShared_2219_ == 0)
{
v___x_2221_ = v___x_2218_;
goto v_reusejp_2220_;
}
else
{
lean_object* v_reuseFailAlloc_2222_; 
v_reuseFailAlloc_2222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2222_, 0, v_a_2216_);
v___x_2221_ = v_reuseFailAlloc_2222_;
goto v_reusejp_2220_;
}
v_reusejp_2220_:
{
return v___x_2221_;
}
}
}
}
v___jp_2207_:
{
lean_object* v___x_2209_; size_t v___x_2210_; size_t v___x_2211_; 
v___x_2209_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2209_, 0, v___x_2206_);
lean_ctor_set(v___x_2209_, 1, v_a_2208_);
v___x_2210_ = ((size_t)1ULL);
v___x_2211_ = lean_usize_add(v_i_2185_, v___x_2210_);
v_i_2185_ = v___x_2211_;
v_b_2186_ = v___x_2209_;
goto _start;
}
}
else
{
lean_object* v_a_2224_; lean_object* v___x_2226_; uint8_t v_isShared_2227_; uint8_t v_isSharedCheck_2231_; 
lean_dec(v_a_2203_);
lean_dec(v___y_2196_);
lean_dec_ref(v___y_2195_);
lean_dec(v___y_2194_);
lean_dec_ref(v___y_2193_);
lean_dec(v___y_2192_);
lean_dec_ref(v___y_2191_);
lean_dec(v___y_2190_);
lean_dec_ref(v___y_2189_);
lean_dec(v___y_2188_);
lean_dec(v___y_2187_);
v_a_2224_ = lean_ctor_get(v___x_2205_, 0);
v_isSharedCheck_2231_ = !lean_is_exclusive(v___x_2205_);
if (v_isSharedCheck_2231_ == 0)
{
v___x_2226_ = v___x_2205_;
v_isShared_2227_ = v_isSharedCheck_2231_;
goto v_resetjp_2225_;
}
else
{
lean_inc(v_a_2224_);
lean_dec(v___x_2205_);
v___x_2226_ = lean_box(0);
v_isShared_2227_ = v_isSharedCheck_2231_;
goto v_resetjp_2225_;
}
v_resetjp_2225_:
{
lean_object* v___x_2229_; 
if (v_isShared_2227_ == 0)
{
v___x_2229_ = v___x_2226_;
goto v_reusejp_2228_;
}
else
{
lean_object* v_reuseFailAlloc_2230_; 
v_reuseFailAlloc_2230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2230_, 0, v_a_2224_);
v___x_2229_ = v_reuseFailAlloc_2230_;
goto v_reusejp_2228_;
}
v_reusejp_2228_:
{
return v___x_2229_;
}
}
}
}
else
{
lean_object* v_a_2232_; lean_object* v___x_2234_; uint8_t v_isShared_2235_; uint8_t v_isSharedCheck_2239_; 
lean_dec(v___y_2196_);
lean_dec_ref(v___y_2195_);
lean_dec(v___y_2194_);
lean_dec_ref(v___y_2193_);
lean_dec(v___y_2192_);
lean_dec_ref(v___y_2191_);
lean_dec(v___y_2190_);
lean_dec_ref(v___y_2189_);
lean_dec(v___y_2188_);
lean_dec(v___y_2187_);
v_a_2232_ = lean_ctor_get(v___x_2202_, 0);
v_isSharedCheck_2239_ = !lean_is_exclusive(v___x_2202_);
if (v_isSharedCheck_2239_ == 0)
{
v___x_2234_ = v___x_2202_;
v_isShared_2235_ = v_isSharedCheck_2239_;
goto v_resetjp_2233_;
}
else
{
lean_inc(v_a_2232_);
lean_dec(v___x_2202_);
v___x_2234_ = lean_box(0);
v_isShared_2235_ = v_isSharedCheck_2239_;
goto v_resetjp_2233_;
}
v_resetjp_2233_:
{
lean_object* v___x_2237_; 
if (v_isShared_2235_ == 0)
{
v___x_2237_ = v___x_2234_;
goto v_reusejp_2236_;
}
else
{
lean_object* v_reuseFailAlloc_2238_; 
v_reuseFailAlloc_2238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2238_, 0, v_a_2232_);
v___x_2237_ = v_reuseFailAlloc_2238_;
goto v_reusejp_2236_;
}
v_reusejp_2236_:
{
return v___x_2237_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__1_spec__3_spec__4___boxed(lean_object* v_as_2240_, lean_object* v_sz_2241_, lean_object* v_i_2242_, lean_object* v_b_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_){
_start:
{
size_t v_sz_boxed_2255_; size_t v_i_boxed_2256_; lean_object* v_res_2257_; 
v_sz_boxed_2255_ = lean_unbox_usize(v_sz_2241_);
lean_dec(v_sz_2241_);
v_i_boxed_2256_ = lean_unbox_usize(v_i_2242_);
lean_dec(v_i_2242_);
v_res_2257_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__1_spec__3_spec__4(v_as_2240_, v_sz_boxed_2255_, v_i_boxed_2256_, v_b_2243_, v___y_2244_, v___y_2245_, v___y_2246_, v___y_2247_, v___y_2248_, v___y_2249_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_);
lean_dec_ref(v_as_2240_);
return v_res_2257_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__1_spec__3(lean_object* v_as_2261_, size_t v_sz_2262_, size_t v_i_2263_, lean_object* v_b_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_){
_start:
{
uint8_t v___x_2276_; 
v___x_2276_ = lean_usize_dec_lt(v_i_2263_, v_sz_2262_);
if (v___x_2276_ == 0)
{
lean_object* v___x_2277_; 
lean_dec(v___y_2274_);
lean_dec_ref(v___y_2273_);
lean_dec(v___y_2272_);
lean_dec_ref(v___y_2271_);
lean_dec(v___y_2270_);
lean_dec_ref(v___y_2269_);
lean_dec(v___y_2268_);
lean_dec_ref(v___y_2267_);
lean_dec(v___y_2266_);
lean_dec(v___y_2265_);
v___x_2277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2277_, 0, v_b_2264_);
return v___x_2277_;
}
else
{
lean_object* v___x_2278_; lean_object* v_a_2279_; lean_object* v___x_2280_; 
lean_dec_ref(v_b_2264_);
v___x_2278_ = lean_st_ref_get(v___y_2265_);
v_a_2279_ = lean_array_uget_borrowed(v_as_2261_, v_i_2263_);
lean_inc(v_a_2279_);
v___x_2280_ = l_Lean_Meta_Grind_Goal_getENode(v___x_2278_, v_a_2279_, v___y_2271_, v___y_2272_, v___y_2273_, v___y_2274_);
if (lean_obj_tag(v___x_2280_) == 0)
{
lean_object* v_a_2281_; lean_object* v_self_2282_; lean_object* v___x_2283_; 
v_a_2281_ = lean_ctor_get(v___x_2280_, 0);
lean_inc(v_a_2281_);
lean_dec_ref(v___x_2280_);
v_self_2282_ = lean_ctor_get(v_a_2281_, 0);
lean_inc(v___y_2274_);
lean_inc_ref(v___y_2273_);
lean_inc(v___y_2272_);
lean_inc_ref(v___y_2271_);
lean_inc(v___y_2270_);
lean_inc_ref(v___y_2269_);
lean_inc(v___y_2268_);
lean_inc_ref(v___y_2267_);
lean_inc(v___y_2266_);
lean_inc(v___y_2265_);
lean_inc_ref(v_self_2282_);
v___x_2283_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents(v_self_2282_, v___y_2265_, v___y_2266_, v___y_2267_, v___y_2268_, v___y_2269_, v___y_2270_, v___y_2271_, v___y_2272_, v___y_2273_, v___y_2274_);
if (lean_obj_tag(v___x_2283_) == 0)
{
uint8_t v___x_2289_; 
lean_dec_ref(v___x_2283_);
v___x_2289_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_2281_);
if (v___x_2289_ == 0)
{
lean_dec(v_a_2281_);
goto v___jp_2284_;
}
else
{
lean_object* v___x_2290_; 
lean_inc(v___y_2274_);
lean_inc_ref(v___y_2273_);
lean_inc(v___y_2272_);
lean_inc_ref(v___y_2271_);
lean_inc(v___y_2270_);
lean_inc_ref(v___y_2269_);
lean_inc(v___y_2268_);
lean_inc_ref(v___y_2267_);
lean_inc(v___y_2266_);
lean_inc(v___y_2265_);
v___x_2290_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc(v_a_2281_, v___y_2265_, v___y_2266_, v___y_2267_, v___y_2268_, v___y_2269_, v___y_2270_, v___y_2271_, v___y_2272_, v___y_2273_, v___y_2274_);
if (lean_obj_tag(v___x_2290_) == 0)
{
lean_dec_ref(v___x_2290_);
goto v___jp_2284_;
}
else
{
lean_object* v_a_2291_; lean_object* v___x_2293_; uint8_t v_isShared_2294_; uint8_t v_isSharedCheck_2298_; 
lean_dec(v___y_2274_);
lean_dec_ref(v___y_2273_);
lean_dec(v___y_2272_);
lean_dec_ref(v___y_2271_);
lean_dec(v___y_2270_);
lean_dec_ref(v___y_2269_);
lean_dec(v___y_2268_);
lean_dec_ref(v___y_2267_);
lean_dec(v___y_2266_);
lean_dec(v___y_2265_);
v_a_2291_ = lean_ctor_get(v___x_2290_, 0);
v_isSharedCheck_2298_ = !lean_is_exclusive(v___x_2290_);
if (v_isSharedCheck_2298_ == 0)
{
v___x_2293_ = v___x_2290_;
v_isShared_2294_ = v_isSharedCheck_2298_;
goto v_resetjp_2292_;
}
else
{
lean_inc(v_a_2291_);
lean_dec(v___x_2290_);
v___x_2293_ = lean_box(0);
v_isShared_2294_ = v_isSharedCheck_2298_;
goto v_resetjp_2292_;
}
v_resetjp_2292_:
{
lean_object* v___x_2296_; 
if (v_isShared_2294_ == 0)
{
v___x_2296_ = v___x_2293_;
goto v_reusejp_2295_;
}
else
{
lean_object* v_reuseFailAlloc_2297_; 
v_reuseFailAlloc_2297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2297_, 0, v_a_2291_);
v___x_2296_ = v_reuseFailAlloc_2297_;
goto v_reusejp_2295_;
}
v_reusejp_2295_:
{
return v___x_2296_;
}
}
}
}
v___jp_2284_:
{
lean_object* v___x_2285_; size_t v___x_2286_; size_t v___x_2287_; lean_object* v___x_2288_; 
v___x_2285_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__1_spec__3___closed__0));
v___x_2286_ = ((size_t)1ULL);
v___x_2287_ = lean_usize_add(v_i_2263_, v___x_2286_);
v___x_2288_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__1_spec__3_spec__4(v_as_2261_, v_sz_2262_, v___x_2287_, v___x_2285_, v___y_2265_, v___y_2266_, v___y_2267_, v___y_2268_, v___y_2269_, v___y_2270_, v___y_2271_, v___y_2272_, v___y_2273_, v___y_2274_);
return v___x_2288_;
}
}
else
{
lean_object* v_a_2299_; lean_object* v___x_2301_; uint8_t v_isShared_2302_; uint8_t v_isSharedCheck_2306_; 
lean_dec(v_a_2281_);
lean_dec(v___y_2274_);
lean_dec_ref(v___y_2273_);
lean_dec(v___y_2272_);
lean_dec_ref(v___y_2271_);
lean_dec(v___y_2270_);
lean_dec_ref(v___y_2269_);
lean_dec(v___y_2268_);
lean_dec_ref(v___y_2267_);
lean_dec(v___y_2266_);
lean_dec(v___y_2265_);
v_a_2299_ = lean_ctor_get(v___x_2283_, 0);
v_isSharedCheck_2306_ = !lean_is_exclusive(v___x_2283_);
if (v_isSharedCheck_2306_ == 0)
{
v___x_2301_ = v___x_2283_;
v_isShared_2302_ = v_isSharedCheck_2306_;
goto v_resetjp_2300_;
}
else
{
lean_inc(v_a_2299_);
lean_dec(v___x_2283_);
v___x_2301_ = lean_box(0);
v_isShared_2302_ = v_isSharedCheck_2306_;
goto v_resetjp_2300_;
}
v_resetjp_2300_:
{
lean_object* v___x_2304_; 
if (v_isShared_2302_ == 0)
{
v___x_2304_ = v___x_2301_;
goto v_reusejp_2303_;
}
else
{
lean_object* v_reuseFailAlloc_2305_; 
v_reuseFailAlloc_2305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2305_, 0, v_a_2299_);
v___x_2304_ = v_reuseFailAlloc_2305_;
goto v_reusejp_2303_;
}
v_reusejp_2303_:
{
return v___x_2304_;
}
}
}
}
else
{
lean_object* v_a_2307_; lean_object* v___x_2309_; uint8_t v_isShared_2310_; uint8_t v_isSharedCheck_2314_; 
lean_dec(v___y_2274_);
lean_dec_ref(v___y_2273_);
lean_dec(v___y_2272_);
lean_dec_ref(v___y_2271_);
lean_dec(v___y_2270_);
lean_dec_ref(v___y_2269_);
lean_dec(v___y_2268_);
lean_dec_ref(v___y_2267_);
lean_dec(v___y_2266_);
lean_dec(v___y_2265_);
v_a_2307_ = lean_ctor_get(v___x_2280_, 0);
v_isSharedCheck_2314_ = !lean_is_exclusive(v___x_2280_);
if (v_isSharedCheck_2314_ == 0)
{
v___x_2309_ = v___x_2280_;
v_isShared_2310_ = v_isSharedCheck_2314_;
goto v_resetjp_2308_;
}
else
{
lean_inc(v_a_2307_);
lean_dec(v___x_2280_);
v___x_2309_ = lean_box(0);
v_isShared_2310_ = v_isSharedCheck_2314_;
goto v_resetjp_2308_;
}
v_resetjp_2308_:
{
lean_object* v___x_2312_; 
if (v_isShared_2310_ == 0)
{
v___x_2312_ = v___x_2309_;
goto v_reusejp_2311_;
}
else
{
lean_object* v_reuseFailAlloc_2313_; 
v_reuseFailAlloc_2313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2313_, 0, v_a_2307_);
v___x_2312_ = v_reuseFailAlloc_2313_;
goto v_reusejp_2311_;
}
v_reusejp_2311_:
{
return v___x_2312_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__1_spec__3___boxed(lean_object* v_as_2315_, lean_object* v_sz_2316_, lean_object* v_i_2317_, lean_object* v_b_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_){
_start:
{
size_t v_sz_boxed_2330_; size_t v_i_boxed_2331_; lean_object* v_res_2332_; 
v_sz_boxed_2330_ = lean_unbox_usize(v_sz_2316_);
lean_dec(v_sz_2316_);
v_i_boxed_2331_ = lean_unbox_usize(v_i_2317_);
lean_dec(v_i_2317_);
v_res_2332_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__1_spec__3(v_as_2315_, v_sz_boxed_2330_, v_i_boxed_2331_, v_b_2318_, v___y_2319_, v___y_2320_, v___y_2321_, v___y_2322_, v___y_2323_, v___y_2324_, v___y_2325_, v___y_2326_, v___y_2327_, v___y_2328_);
lean_dec_ref(v_as_2315_);
return v_res_2332_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__1(lean_object* v_inh_2333_, lean_object* v_n_2334_, lean_object* v_b_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_){
_start:
{
if (lean_obj_tag(v_n_2334_) == 0)
{
lean_object* v_cs_2347_; lean_object* v___x_2349_; uint8_t v_isShared_2350_; uint8_t v_isSharedCheck_2381_; 
v_cs_2347_ = lean_ctor_get(v_n_2334_, 0);
v_isSharedCheck_2381_ = !lean_is_exclusive(v_n_2334_);
if (v_isSharedCheck_2381_ == 0)
{
v___x_2349_ = v_n_2334_;
v_isShared_2350_ = v_isSharedCheck_2381_;
goto v_resetjp_2348_;
}
else
{
lean_inc(v_cs_2347_);
lean_dec(v_n_2334_);
v___x_2349_ = lean_box(0);
v_isShared_2350_ = v_isSharedCheck_2381_;
goto v_resetjp_2348_;
}
v_resetjp_2348_:
{
lean_object* v___x_2351_; lean_object* v___x_2352_; size_t v_sz_2353_; size_t v___x_2354_; lean_object* v___x_2355_; 
v___x_2351_ = lean_box(0);
v___x_2352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2352_, 0, v___x_2351_);
lean_ctor_set(v___x_2352_, 1, v_b_2335_);
v_sz_2353_ = lean_array_size(v_cs_2347_);
v___x_2354_ = ((size_t)0ULL);
v___x_2355_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__1_spec__2(v_inh_2333_, v_cs_2347_, v_sz_2353_, v___x_2354_, v___x_2352_, v___y_2336_, v___y_2337_, v___y_2338_, v___y_2339_, v___y_2340_, v___y_2341_, v___y_2342_, v___y_2343_, v___y_2344_, v___y_2345_);
lean_dec_ref(v_cs_2347_);
if (lean_obj_tag(v___x_2355_) == 0)
{
lean_object* v_a_2356_; lean_object* v___x_2358_; uint8_t v_isShared_2359_; uint8_t v_isSharedCheck_2372_; 
v_a_2356_ = lean_ctor_get(v___x_2355_, 0);
v_isSharedCheck_2372_ = !lean_is_exclusive(v___x_2355_);
if (v_isSharedCheck_2372_ == 0)
{
v___x_2358_ = v___x_2355_;
v_isShared_2359_ = v_isSharedCheck_2372_;
goto v_resetjp_2357_;
}
else
{
lean_inc(v_a_2356_);
lean_dec(v___x_2355_);
v___x_2358_ = lean_box(0);
v_isShared_2359_ = v_isSharedCheck_2372_;
goto v_resetjp_2357_;
}
v_resetjp_2357_:
{
lean_object* v_fst_2360_; 
v_fst_2360_ = lean_ctor_get(v_a_2356_, 0);
if (lean_obj_tag(v_fst_2360_) == 0)
{
lean_object* v_snd_2361_; lean_object* v___x_2363_; 
v_snd_2361_ = lean_ctor_get(v_a_2356_, 1);
lean_inc(v_snd_2361_);
lean_dec(v_a_2356_);
if (v_isShared_2350_ == 0)
{
lean_ctor_set_tag(v___x_2349_, 1);
lean_ctor_set(v___x_2349_, 0, v_snd_2361_);
v___x_2363_ = v___x_2349_;
goto v_reusejp_2362_;
}
else
{
lean_object* v_reuseFailAlloc_2367_; 
v_reuseFailAlloc_2367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2367_, 0, v_snd_2361_);
v___x_2363_ = v_reuseFailAlloc_2367_;
goto v_reusejp_2362_;
}
v_reusejp_2362_:
{
lean_object* v___x_2365_; 
if (v_isShared_2359_ == 0)
{
lean_ctor_set(v___x_2358_, 0, v___x_2363_);
v___x_2365_ = v___x_2358_;
goto v_reusejp_2364_;
}
else
{
lean_object* v_reuseFailAlloc_2366_; 
v_reuseFailAlloc_2366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2366_, 0, v___x_2363_);
v___x_2365_ = v_reuseFailAlloc_2366_;
goto v_reusejp_2364_;
}
v_reusejp_2364_:
{
return v___x_2365_;
}
}
}
else
{
lean_object* v_val_2368_; lean_object* v___x_2370_; 
lean_inc_ref(v_fst_2360_);
lean_dec(v_a_2356_);
lean_del_object(v___x_2349_);
v_val_2368_ = lean_ctor_get(v_fst_2360_, 0);
lean_inc(v_val_2368_);
lean_dec_ref(v_fst_2360_);
if (v_isShared_2359_ == 0)
{
lean_ctor_set(v___x_2358_, 0, v_val_2368_);
v___x_2370_ = v___x_2358_;
goto v_reusejp_2369_;
}
else
{
lean_object* v_reuseFailAlloc_2371_; 
v_reuseFailAlloc_2371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2371_, 0, v_val_2368_);
v___x_2370_ = v_reuseFailAlloc_2371_;
goto v_reusejp_2369_;
}
v_reusejp_2369_:
{
return v___x_2370_;
}
}
}
}
else
{
lean_object* v_a_2373_; lean_object* v___x_2375_; uint8_t v_isShared_2376_; uint8_t v_isSharedCheck_2380_; 
lean_del_object(v___x_2349_);
v_a_2373_ = lean_ctor_get(v___x_2355_, 0);
v_isSharedCheck_2380_ = !lean_is_exclusive(v___x_2355_);
if (v_isSharedCheck_2380_ == 0)
{
v___x_2375_ = v___x_2355_;
v_isShared_2376_ = v_isSharedCheck_2380_;
goto v_resetjp_2374_;
}
else
{
lean_inc(v_a_2373_);
lean_dec(v___x_2355_);
v___x_2375_ = lean_box(0);
v_isShared_2376_ = v_isSharedCheck_2380_;
goto v_resetjp_2374_;
}
v_resetjp_2374_:
{
lean_object* v___x_2378_; 
if (v_isShared_2376_ == 0)
{
v___x_2378_ = v___x_2375_;
goto v_reusejp_2377_;
}
else
{
lean_object* v_reuseFailAlloc_2379_; 
v_reuseFailAlloc_2379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2379_, 0, v_a_2373_);
v___x_2378_ = v_reuseFailAlloc_2379_;
goto v_reusejp_2377_;
}
v_reusejp_2377_:
{
return v___x_2378_;
}
}
}
}
}
else
{
lean_object* v_vs_2382_; lean_object* v___x_2384_; uint8_t v_isShared_2385_; uint8_t v_isSharedCheck_2416_; 
v_vs_2382_ = lean_ctor_get(v_n_2334_, 0);
v_isSharedCheck_2416_ = !lean_is_exclusive(v_n_2334_);
if (v_isSharedCheck_2416_ == 0)
{
v___x_2384_ = v_n_2334_;
v_isShared_2385_ = v_isSharedCheck_2416_;
goto v_resetjp_2383_;
}
else
{
lean_inc(v_vs_2382_);
lean_dec(v_n_2334_);
v___x_2384_ = lean_box(0);
v_isShared_2385_ = v_isSharedCheck_2416_;
goto v_resetjp_2383_;
}
v_resetjp_2383_:
{
lean_object* v___x_2386_; lean_object* v___x_2387_; size_t v_sz_2388_; size_t v___x_2389_; lean_object* v___x_2390_; 
v___x_2386_ = lean_box(0);
v___x_2387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2387_, 0, v___x_2386_);
lean_ctor_set(v___x_2387_, 1, v_b_2335_);
v_sz_2388_ = lean_array_size(v_vs_2382_);
v___x_2389_ = ((size_t)0ULL);
v___x_2390_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__1_spec__3(v_vs_2382_, v_sz_2388_, v___x_2389_, v___x_2387_, v___y_2336_, v___y_2337_, v___y_2338_, v___y_2339_, v___y_2340_, v___y_2341_, v___y_2342_, v___y_2343_, v___y_2344_, v___y_2345_);
lean_dec_ref(v_vs_2382_);
if (lean_obj_tag(v___x_2390_) == 0)
{
lean_object* v_a_2391_; lean_object* v___x_2393_; uint8_t v_isShared_2394_; uint8_t v_isSharedCheck_2407_; 
v_a_2391_ = lean_ctor_get(v___x_2390_, 0);
v_isSharedCheck_2407_ = !lean_is_exclusive(v___x_2390_);
if (v_isSharedCheck_2407_ == 0)
{
v___x_2393_ = v___x_2390_;
v_isShared_2394_ = v_isSharedCheck_2407_;
goto v_resetjp_2392_;
}
else
{
lean_inc(v_a_2391_);
lean_dec(v___x_2390_);
v___x_2393_ = lean_box(0);
v_isShared_2394_ = v_isSharedCheck_2407_;
goto v_resetjp_2392_;
}
v_resetjp_2392_:
{
lean_object* v_fst_2395_; 
v_fst_2395_ = lean_ctor_get(v_a_2391_, 0);
if (lean_obj_tag(v_fst_2395_) == 0)
{
lean_object* v_snd_2396_; lean_object* v___x_2398_; 
v_snd_2396_ = lean_ctor_get(v_a_2391_, 1);
lean_inc(v_snd_2396_);
lean_dec(v_a_2391_);
if (v_isShared_2385_ == 0)
{
lean_ctor_set(v___x_2384_, 0, v_snd_2396_);
v___x_2398_ = v___x_2384_;
goto v_reusejp_2397_;
}
else
{
lean_object* v_reuseFailAlloc_2402_; 
v_reuseFailAlloc_2402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2402_, 0, v_snd_2396_);
v___x_2398_ = v_reuseFailAlloc_2402_;
goto v_reusejp_2397_;
}
v_reusejp_2397_:
{
lean_object* v___x_2400_; 
if (v_isShared_2394_ == 0)
{
lean_ctor_set(v___x_2393_, 0, v___x_2398_);
v___x_2400_ = v___x_2393_;
goto v_reusejp_2399_;
}
else
{
lean_object* v_reuseFailAlloc_2401_; 
v_reuseFailAlloc_2401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2401_, 0, v___x_2398_);
v___x_2400_ = v_reuseFailAlloc_2401_;
goto v_reusejp_2399_;
}
v_reusejp_2399_:
{
return v___x_2400_;
}
}
}
else
{
lean_object* v_val_2403_; lean_object* v___x_2405_; 
lean_inc_ref(v_fst_2395_);
lean_dec(v_a_2391_);
lean_del_object(v___x_2384_);
v_val_2403_ = lean_ctor_get(v_fst_2395_, 0);
lean_inc(v_val_2403_);
lean_dec_ref(v_fst_2395_);
if (v_isShared_2394_ == 0)
{
lean_ctor_set(v___x_2393_, 0, v_val_2403_);
v___x_2405_ = v___x_2393_;
goto v_reusejp_2404_;
}
else
{
lean_object* v_reuseFailAlloc_2406_; 
v_reuseFailAlloc_2406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2406_, 0, v_val_2403_);
v___x_2405_ = v_reuseFailAlloc_2406_;
goto v_reusejp_2404_;
}
v_reusejp_2404_:
{
return v___x_2405_;
}
}
}
}
else
{
lean_object* v_a_2408_; lean_object* v___x_2410_; uint8_t v_isShared_2411_; uint8_t v_isSharedCheck_2415_; 
lean_del_object(v___x_2384_);
v_a_2408_ = lean_ctor_get(v___x_2390_, 0);
v_isSharedCheck_2415_ = !lean_is_exclusive(v___x_2390_);
if (v_isSharedCheck_2415_ == 0)
{
v___x_2410_ = v___x_2390_;
v_isShared_2411_ = v_isSharedCheck_2415_;
goto v_resetjp_2409_;
}
else
{
lean_inc(v_a_2408_);
lean_dec(v___x_2390_);
v___x_2410_ = lean_box(0);
v_isShared_2411_ = v_isSharedCheck_2415_;
goto v_resetjp_2409_;
}
v_resetjp_2409_:
{
lean_object* v___x_2413_; 
if (v_isShared_2411_ == 0)
{
v___x_2413_ = v___x_2410_;
goto v_reusejp_2412_;
}
else
{
lean_object* v_reuseFailAlloc_2414_; 
v_reuseFailAlloc_2414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2414_, 0, v_a_2408_);
v___x_2413_ = v_reuseFailAlloc_2414_;
goto v_reusejp_2412_;
}
v_reusejp_2412_:
{
return v___x_2413_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__1_spec__2(lean_object* v_inh_2417_, lean_object* v_as_2418_, size_t v_sz_2419_, size_t v_i_2420_, lean_object* v_b_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_){
_start:
{
uint8_t v___x_2433_; 
v___x_2433_ = lean_usize_dec_lt(v_i_2420_, v_sz_2419_);
if (v___x_2433_ == 0)
{
lean_object* v___x_2434_; 
lean_dec(v___y_2431_);
lean_dec_ref(v___y_2430_);
lean_dec(v___y_2429_);
lean_dec_ref(v___y_2428_);
lean_dec(v___y_2427_);
lean_dec_ref(v___y_2426_);
lean_dec(v___y_2425_);
lean_dec_ref(v___y_2424_);
lean_dec(v___y_2423_);
lean_dec(v___y_2422_);
v___x_2434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2434_, 0, v_b_2421_);
return v___x_2434_;
}
else
{
lean_object* v_snd_2435_; lean_object* v___x_2437_; uint8_t v_isShared_2438_; uint8_t v_isSharedCheck_2469_; 
v_snd_2435_ = lean_ctor_get(v_b_2421_, 1);
v_isSharedCheck_2469_ = !lean_is_exclusive(v_b_2421_);
if (v_isSharedCheck_2469_ == 0)
{
lean_object* v_unused_2470_; 
v_unused_2470_ = lean_ctor_get(v_b_2421_, 0);
lean_dec(v_unused_2470_);
v___x_2437_ = v_b_2421_;
v_isShared_2438_ = v_isSharedCheck_2469_;
goto v_resetjp_2436_;
}
else
{
lean_inc(v_snd_2435_);
lean_dec(v_b_2421_);
v___x_2437_ = lean_box(0);
v_isShared_2438_ = v_isSharedCheck_2469_;
goto v_resetjp_2436_;
}
v_resetjp_2436_:
{
lean_object* v_a_2439_; lean_object* v___x_2440_; 
v_a_2439_ = lean_array_uget_borrowed(v_as_2418_, v_i_2420_);
lean_inc(v___y_2431_);
lean_inc_ref(v___y_2430_);
lean_inc(v___y_2429_);
lean_inc_ref(v___y_2428_);
lean_inc(v___y_2427_);
lean_inc_ref(v___y_2426_);
lean_inc(v___y_2425_);
lean_inc_ref(v___y_2424_);
lean_inc(v___y_2423_);
lean_inc(v___y_2422_);
lean_inc(v_snd_2435_);
lean_inc(v_a_2439_);
v___x_2440_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__1(v_inh_2417_, v_a_2439_, v_snd_2435_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_, v___y_2426_, v___y_2427_, v___y_2428_, v___y_2429_, v___y_2430_, v___y_2431_);
if (lean_obj_tag(v___x_2440_) == 0)
{
lean_object* v_a_2441_; lean_object* v___x_2443_; uint8_t v_isShared_2444_; uint8_t v_isSharedCheck_2460_; 
v_a_2441_ = lean_ctor_get(v___x_2440_, 0);
v_isSharedCheck_2460_ = !lean_is_exclusive(v___x_2440_);
if (v_isSharedCheck_2460_ == 0)
{
v___x_2443_ = v___x_2440_;
v_isShared_2444_ = v_isSharedCheck_2460_;
goto v_resetjp_2442_;
}
else
{
lean_inc(v_a_2441_);
lean_dec(v___x_2440_);
v___x_2443_ = lean_box(0);
v_isShared_2444_ = v_isSharedCheck_2460_;
goto v_resetjp_2442_;
}
v_resetjp_2442_:
{
if (lean_obj_tag(v_a_2441_) == 0)
{
lean_object* v___x_2445_; lean_object* v___x_2447_; 
lean_dec(v___y_2431_);
lean_dec_ref(v___y_2430_);
lean_dec(v___y_2429_);
lean_dec_ref(v___y_2428_);
lean_dec(v___y_2427_);
lean_dec_ref(v___y_2426_);
lean_dec(v___y_2425_);
lean_dec_ref(v___y_2424_);
lean_dec(v___y_2423_);
lean_dec(v___y_2422_);
v___x_2445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2445_, 0, v_a_2441_);
if (v_isShared_2438_ == 0)
{
lean_ctor_set(v___x_2437_, 0, v___x_2445_);
v___x_2447_ = v___x_2437_;
goto v_reusejp_2446_;
}
else
{
lean_object* v_reuseFailAlloc_2451_; 
v_reuseFailAlloc_2451_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2451_, 0, v___x_2445_);
lean_ctor_set(v_reuseFailAlloc_2451_, 1, v_snd_2435_);
v___x_2447_ = v_reuseFailAlloc_2451_;
goto v_reusejp_2446_;
}
v_reusejp_2446_:
{
lean_object* v___x_2449_; 
if (v_isShared_2444_ == 0)
{
lean_ctor_set(v___x_2443_, 0, v___x_2447_);
v___x_2449_ = v___x_2443_;
goto v_reusejp_2448_;
}
else
{
lean_object* v_reuseFailAlloc_2450_; 
v_reuseFailAlloc_2450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2450_, 0, v___x_2447_);
v___x_2449_ = v_reuseFailAlloc_2450_;
goto v_reusejp_2448_;
}
v_reusejp_2448_:
{
return v___x_2449_;
}
}
}
else
{
lean_object* v_a_2452_; lean_object* v___x_2453_; lean_object* v___x_2455_; 
lean_del_object(v___x_2443_);
lean_dec(v_snd_2435_);
v_a_2452_ = lean_ctor_get(v_a_2441_, 0);
lean_inc(v_a_2452_);
lean_dec_ref(v_a_2441_);
v___x_2453_ = lean_box(0);
if (v_isShared_2438_ == 0)
{
lean_ctor_set(v___x_2437_, 1, v_a_2452_);
lean_ctor_set(v___x_2437_, 0, v___x_2453_);
v___x_2455_ = v___x_2437_;
goto v_reusejp_2454_;
}
else
{
lean_object* v_reuseFailAlloc_2459_; 
v_reuseFailAlloc_2459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2459_, 0, v___x_2453_);
lean_ctor_set(v_reuseFailAlloc_2459_, 1, v_a_2452_);
v___x_2455_ = v_reuseFailAlloc_2459_;
goto v_reusejp_2454_;
}
v_reusejp_2454_:
{
size_t v___x_2456_; size_t v___x_2457_; 
v___x_2456_ = ((size_t)1ULL);
v___x_2457_ = lean_usize_add(v_i_2420_, v___x_2456_);
v_i_2420_ = v___x_2457_;
v_b_2421_ = v___x_2455_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_2461_; lean_object* v___x_2463_; uint8_t v_isShared_2464_; uint8_t v_isSharedCheck_2468_; 
lean_del_object(v___x_2437_);
lean_dec(v_snd_2435_);
lean_dec(v___y_2431_);
lean_dec_ref(v___y_2430_);
lean_dec(v___y_2429_);
lean_dec_ref(v___y_2428_);
lean_dec(v___y_2427_);
lean_dec_ref(v___y_2426_);
lean_dec(v___y_2425_);
lean_dec_ref(v___y_2424_);
lean_dec(v___y_2423_);
lean_dec(v___y_2422_);
v_a_2461_ = lean_ctor_get(v___x_2440_, 0);
v_isSharedCheck_2468_ = !lean_is_exclusive(v___x_2440_);
if (v_isSharedCheck_2468_ == 0)
{
v___x_2463_ = v___x_2440_;
v_isShared_2464_ = v_isSharedCheck_2468_;
goto v_resetjp_2462_;
}
else
{
lean_inc(v_a_2461_);
lean_dec(v___x_2440_);
v___x_2463_ = lean_box(0);
v_isShared_2464_ = v_isSharedCheck_2468_;
goto v_resetjp_2462_;
}
v_resetjp_2462_:
{
lean_object* v___x_2466_; 
if (v_isShared_2464_ == 0)
{
v___x_2466_ = v___x_2463_;
goto v_reusejp_2465_;
}
else
{
lean_object* v_reuseFailAlloc_2467_; 
v_reuseFailAlloc_2467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2467_, 0, v_a_2461_);
v___x_2466_ = v_reuseFailAlloc_2467_;
goto v_reusejp_2465_;
}
v_reusejp_2465_:
{
return v___x_2466_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__1_spec__2___boxed(lean_object* v_inh_2471_, lean_object* v_as_2472_, lean_object* v_sz_2473_, lean_object* v_i_2474_, lean_object* v_b_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_){
_start:
{
size_t v_sz_boxed_2487_; size_t v_i_boxed_2488_; lean_object* v_res_2489_; 
v_sz_boxed_2487_ = lean_unbox_usize(v_sz_2473_);
lean_dec(v_sz_2473_);
v_i_boxed_2488_ = lean_unbox_usize(v_i_2474_);
lean_dec(v_i_2474_);
v_res_2489_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__1_spec__2(v_inh_2471_, v_as_2472_, v_sz_boxed_2487_, v_i_boxed_2488_, v_b_2475_, v___y_2476_, v___y_2477_, v___y_2478_, v___y_2479_, v___y_2480_, v___y_2481_, v___y_2482_, v___y_2483_, v___y_2484_, v___y_2485_);
lean_dec_ref(v_as_2472_);
return v_res_2489_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__1___boxed(lean_object* v_inh_2490_, lean_object* v_n_2491_, lean_object* v_b_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_){
_start:
{
lean_object* v_res_2504_; 
v_res_2504_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__1(v_inh_2490_, v_n_2491_, v_b_2492_, v___y_2493_, v___y_2494_, v___y_2495_, v___y_2496_, v___y_2497_, v___y_2498_, v___y_2499_, v___y_2500_, v___y_2501_, v___y_2502_);
return v_res_2504_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1(lean_object* v_t_2505_, lean_object* v_init_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_){
_start:
{
lean_object* v_root_2518_; lean_object* v_tail_2519_; lean_object* v___x_2520_; 
v_root_2518_ = lean_ctor_get(v_t_2505_, 0);
lean_inc_ref(v_root_2518_);
v_tail_2519_ = lean_ctor_get(v_t_2505_, 1);
lean_inc_ref(v_tail_2519_);
lean_dec_ref(v_t_2505_);
lean_inc(v___y_2516_);
lean_inc_ref(v___y_2515_);
lean_inc(v___y_2514_);
lean_inc_ref(v___y_2513_);
lean_inc(v___y_2512_);
lean_inc_ref(v___y_2511_);
lean_inc(v___y_2510_);
lean_inc_ref(v___y_2509_);
lean_inc(v___y_2508_);
lean_inc(v___y_2507_);
v___x_2520_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__1(v_init_2506_, v_root_2518_, v_init_2506_, v___y_2507_, v___y_2508_, v___y_2509_, v___y_2510_, v___y_2511_, v___y_2512_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_);
if (lean_obj_tag(v___x_2520_) == 0)
{
lean_object* v_a_2521_; lean_object* v___x_2523_; uint8_t v_isShared_2524_; uint8_t v_isSharedCheck_2557_; 
v_a_2521_ = lean_ctor_get(v___x_2520_, 0);
v_isSharedCheck_2557_ = !lean_is_exclusive(v___x_2520_);
if (v_isSharedCheck_2557_ == 0)
{
v___x_2523_ = v___x_2520_;
v_isShared_2524_ = v_isSharedCheck_2557_;
goto v_resetjp_2522_;
}
else
{
lean_inc(v_a_2521_);
lean_dec(v___x_2520_);
v___x_2523_ = lean_box(0);
v_isShared_2524_ = v_isSharedCheck_2557_;
goto v_resetjp_2522_;
}
v_resetjp_2522_:
{
if (lean_obj_tag(v_a_2521_) == 0)
{
lean_object* v_a_2525_; lean_object* v___x_2527_; 
lean_dec_ref(v_tail_2519_);
lean_dec(v___y_2516_);
lean_dec_ref(v___y_2515_);
lean_dec(v___y_2514_);
lean_dec_ref(v___y_2513_);
lean_dec(v___y_2512_);
lean_dec_ref(v___y_2511_);
lean_dec(v___y_2510_);
lean_dec_ref(v___y_2509_);
lean_dec(v___y_2508_);
lean_dec(v___y_2507_);
v_a_2525_ = lean_ctor_get(v_a_2521_, 0);
lean_inc(v_a_2525_);
lean_dec_ref(v_a_2521_);
if (v_isShared_2524_ == 0)
{
lean_ctor_set(v___x_2523_, 0, v_a_2525_);
v___x_2527_ = v___x_2523_;
goto v_reusejp_2526_;
}
else
{
lean_object* v_reuseFailAlloc_2528_; 
v_reuseFailAlloc_2528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2528_, 0, v_a_2525_);
v___x_2527_ = v_reuseFailAlloc_2528_;
goto v_reusejp_2526_;
}
v_reusejp_2526_:
{
return v___x_2527_;
}
}
else
{
lean_object* v_a_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; size_t v_sz_2532_; size_t v___x_2533_; lean_object* v___x_2534_; 
lean_del_object(v___x_2523_);
v_a_2529_ = lean_ctor_get(v_a_2521_, 0);
lean_inc(v_a_2529_);
lean_dec_ref(v_a_2521_);
v___x_2530_ = lean_box(0);
v___x_2531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2531_, 0, v___x_2530_);
lean_ctor_set(v___x_2531_, 1, v_a_2529_);
v_sz_2532_ = lean_array_size(v_tail_2519_);
v___x_2533_ = ((size_t)0ULL);
v___x_2534_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__2(v_tail_2519_, v_sz_2532_, v___x_2533_, v___x_2531_, v___y_2507_, v___y_2508_, v___y_2509_, v___y_2510_, v___y_2511_, v___y_2512_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_);
lean_dec_ref(v_tail_2519_);
if (lean_obj_tag(v___x_2534_) == 0)
{
lean_object* v_a_2535_; lean_object* v___x_2537_; uint8_t v_isShared_2538_; uint8_t v_isSharedCheck_2548_; 
v_a_2535_ = lean_ctor_get(v___x_2534_, 0);
v_isSharedCheck_2548_ = !lean_is_exclusive(v___x_2534_);
if (v_isSharedCheck_2548_ == 0)
{
v___x_2537_ = v___x_2534_;
v_isShared_2538_ = v_isSharedCheck_2548_;
goto v_resetjp_2536_;
}
else
{
lean_inc(v_a_2535_);
lean_dec(v___x_2534_);
v___x_2537_ = lean_box(0);
v_isShared_2538_ = v_isSharedCheck_2548_;
goto v_resetjp_2536_;
}
v_resetjp_2536_:
{
lean_object* v_fst_2539_; 
v_fst_2539_ = lean_ctor_get(v_a_2535_, 0);
if (lean_obj_tag(v_fst_2539_) == 0)
{
lean_object* v_snd_2540_; lean_object* v___x_2542_; 
v_snd_2540_ = lean_ctor_get(v_a_2535_, 1);
lean_inc(v_snd_2540_);
lean_dec(v_a_2535_);
if (v_isShared_2538_ == 0)
{
lean_ctor_set(v___x_2537_, 0, v_snd_2540_);
v___x_2542_ = v___x_2537_;
goto v_reusejp_2541_;
}
else
{
lean_object* v_reuseFailAlloc_2543_; 
v_reuseFailAlloc_2543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2543_, 0, v_snd_2540_);
v___x_2542_ = v_reuseFailAlloc_2543_;
goto v_reusejp_2541_;
}
v_reusejp_2541_:
{
return v___x_2542_;
}
}
else
{
lean_object* v_val_2544_; lean_object* v___x_2546_; 
lean_inc_ref(v_fst_2539_);
lean_dec(v_a_2535_);
v_val_2544_ = lean_ctor_get(v_fst_2539_, 0);
lean_inc(v_val_2544_);
lean_dec_ref(v_fst_2539_);
if (v_isShared_2538_ == 0)
{
lean_ctor_set(v___x_2537_, 0, v_val_2544_);
v___x_2546_ = v___x_2537_;
goto v_reusejp_2545_;
}
else
{
lean_object* v_reuseFailAlloc_2547_; 
v_reuseFailAlloc_2547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2547_, 0, v_val_2544_);
v___x_2546_ = v_reuseFailAlloc_2547_;
goto v_reusejp_2545_;
}
v_reusejp_2545_:
{
return v___x_2546_;
}
}
}
}
else
{
lean_object* v_a_2549_; lean_object* v___x_2551_; uint8_t v_isShared_2552_; uint8_t v_isSharedCheck_2556_; 
v_a_2549_ = lean_ctor_get(v___x_2534_, 0);
v_isSharedCheck_2556_ = !lean_is_exclusive(v___x_2534_);
if (v_isSharedCheck_2556_ == 0)
{
v___x_2551_ = v___x_2534_;
v_isShared_2552_ = v_isSharedCheck_2556_;
goto v_resetjp_2550_;
}
else
{
lean_inc(v_a_2549_);
lean_dec(v___x_2534_);
v___x_2551_ = lean_box(0);
v_isShared_2552_ = v_isSharedCheck_2556_;
goto v_resetjp_2550_;
}
v_resetjp_2550_:
{
lean_object* v___x_2554_; 
if (v_isShared_2552_ == 0)
{
v___x_2554_ = v___x_2551_;
goto v_reusejp_2553_;
}
else
{
lean_object* v_reuseFailAlloc_2555_; 
v_reuseFailAlloc_2555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2555_, 0, v_a_2549_);
v___x_2554_ = v_reuseFailAlloc_2555_;
goto v_reusejp_2553_;
}
v_reusejp_2553_:
{
return v___x_2554_;
}
}
}
}
}
}
else
{
lean_object* v_a_2558_; lean_object* v___x_2560_; uint8_t v_isShared_2561_; uint8_t v_isSharedCheck_2565_; 
lean_dec_ref(v_tail_2519_);
lean_dec(v___y_2516_);
lean_dec_ref(v___y_2515_);
lean_dec(v___y_2514_);
lean_dec_ref(v___y_2513_);
lean_dec(v___y_2512_);
lean_dec_ref(v___y_2511_);
lean_dec(v___y_2510_);
lean_dec_ref(v___y_2509_);
lean_dec(v___y_2508_);
lean_dec(v___y_2507_);
v_a_2558_ = lean_ctor_get(v___x_2520_, 0);
v_isSharedCheck_2565_ = !lean_is_exclusive(v___x_2520_);
if (v_isSharedCheck_2565_ == 0)
{
v___x_2560_ = v___x_2520_;
v_isShared_2561_ = v_isSharedCheck_2565_;
goto v_resetjp_2559_;
}
else
{
lean_inc(v_a_2558_);
lean_dec(v___x_2520_);
v___x_2560_ = lean_box(0);
v_isShared_2561_ = v_isSharedCheck_2565_;
goto v_resetjp_2559_;
}
v_resetjp_2559_:
{
lean_object* v___x_2563_; 
if (v_isShared_2561_ == 0)
{
v___x_2563_ = v___x_2560_;
goto v_reusejp_2562_;
}
else
{
lean_object* v_reuseFailAlloc_2564_; 
v_reuseFailAlloc_2564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2564_, 0, v_a_2558_);
v___x_2563_ = v_reuseFailAlloc_2564_;
goto v_reusejp_2562_;
}
v_reusejp_2562_:
{
return v___x_2563_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1___boxed(lean_object* v_t_2566_, lean_object* v_init_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_){
_start:
{
lean_object* v_res_2579_; 
v_res_2579_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1(v_t_2566_, v_init_2567_, v___y_2568_, v___y_2569_, v___y_2570_, v___y_2571_, v___y_2572_, v___y_2573_, v___y_2574_, v___y_2575_, v___y_2576_, v___y_2577_);
return v_res_2579_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_checkInvariants(uint8_t v_expensive_2580_, lean_object* v_a_2581_, lean_object* v_a_2582_, lean_object* v_a_2583_, lean_object* v_a_2584_, lean_object* v_a_2585_, lean_object* v_a_2586_, lean_object* v_a_2587_, lean_object* v_a_2588_, lean_object* v_a_2589_, lean_object* v_a_2590_){
_start:
{
lean_object* v___y_2596_; lean_object* v___y_2597_; lean_object* v___y_2598_; lean_object* v___y_2599_; lean_object* v___y_2600_; lean_object* v___y_2601_; lean_object* v___y_2602_; lean_object* v___y_2603_; lean_object* v___y_2604_; lean_object* v___y_2605_; lean_object* v___y_2611_; lean_object* v___y_2612_; lean_object* v___y_2613_; lean_object* v___y_2614_; lean_object* v___y_2615_; lean_object* v___y_2616_; lean_object* v___y_2617_; lean_object* v___y_2618_; lean_object* v___y_2619_; lean_object* v___y_2620_; uint8_t v_debug_2622_; 
v_debug_2622_ = lean_ctor_get_uint8(v_a_2583_, sizeof(void*)*7 + 2);
if (v_debug_2622_ == 0)
{
v___y_2596_ = v_a_2581_;
v___y_2597_ = v_a_2582_;
v___y_2598_ = v_a_2583_;
v___y_2599_ = v_a_2584_;
v___y_2600_ = v_a_2585_;
v___y_2601_ = v_a_2586_;
v___y_2602_ = v_a_2587_;
v___y_2603_ = v_a_2588_;
v___y_2604_ = v_a_2589_;
v___y_2605_ = v_a_2590_;
goto v___jp_2595_;
}
else
{
lean_object* v___x_2623_; 
v___x_2623_ = l_Lean_Meta_Grind_getExprs___redArg(v_a_2581_);
if (lean_obj_tag(v___x_2623_) == 0)
{
lean_object* v_a_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; 
v_a_2624_ = lean_ctor_get(v___x_2623_, 0);
lean_inc(v_a_2624_);
lean_dec_ref(v___x_2623_);
v___x_2625_ = lean_box(0);
lean_inc(v_a_2590_);
lean_inc_ref(v_a_2589_);
lean_inc(v_a_2588_);
lean_inc_ref(v_a_2587_);
lean_inc(v_a_2586_);
lean_inc_ref(v_a_2585_);
lean_inc(v_a_2584_);
lean_inc_ref(v_a_2583_);
lean_inc(v_a_2582_);
lean_inc(v_a_2581_);
v___x_2626_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1(v_a_2624_, v___x_2625_, v_a_2581_, v_a_2582_, v_a_2583_, v_a_2584_, v_a_2585_, v_a_2586_, v_a_2587_, v_a_2588_, v_a_2589_, v_a_2590_);
if (lean_obj_tag(v___x_2626_) == 0)
{
lean_dec_ref(v___x_2626_);
if (v_expensive_2580_ == 0)
{
v___y_2611_ = v_a_2581_;
v___y_2612_ = v_a_2582_;
v___y_2613_ = v_a_2583_;
v___y_2614_ = v_a_2584_;
v___y_2615_ = v_a_2585_;
v___y_2616_ = v_a_2586_;
v___y_2617_ = v_a_2587_;
v___y_2618_ = v_a_2588_;
v___y_2619_ = v_a_2589_;
v___y_2620_ = v_a_2590_;
goto v___jp_2610_;
}
else
{
lean_object* v___x_2627_; 
lean_inc(v_a_2590_);
lean_inc_ref(v_a_2589_);
lean_inc(v_a_2588_);
lean_inc_ref(v_a_2587_);
lean_inc(v_a_2586_);
lean_inc_ref(v_a_2585_);
lean_inc(v_a_2584_);
lean_inc_ref(v_a_2583_);
lean_inc(v_a_2582_);
lean_inc(v_a_2581_);
v___x_2627_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq(v_a_2581_, v_a_2582_, v_a_2583_, v_a_2584_, v_a_2585_, v_a_2586_, v_a_2587_, v_a_2588_, v_a_2589_, v_a_2590_);
if (lean_obj_tag(v___x_2627_) == 0)
{
lean_dec_ref(v___x_2627_);
v___y_2611_ = v_a_2581_;
v___y_2612_ = v_a_2582_;
v___y_2613_ = v_a_2583_;
v___y_2614_ = v_a_2584_;
v___y_2615_ = v_a_2585_;
v___y_2616_ = v_a_2586_;
v___y_2617_ = v_a_2587_;
v___y_2618_ = v_a_2588_;
v___y_2619_ = v_a_2589_;
v___y_2620_ = v_a_2590_;
goto v___jp_2610_;
}
else
{
lean_dec(v_a_2590_);
lean_dec_ref(v_a_2589_);
lean_dec(v_a_2588_);
lean_dec_ref(v_a_2587_);
lean_dec(v_a_2586_);
lean_dec_ref(v_a_2585_);
lean_dec(v_a_2584_);
lean_dec_ref(v_a_2583_);
lean_dec(v_a_2582_);
lean_dec(v_a_2581_);
return v___x_2627_;
}
}
}
else
{
lean_dec(v_a_2590_);
lean_dec_ref(v_a_2589_);
lean_dec(v_a_2588_);
lean_dec_ref(v_a_2587_);
lean_dec(v_a_2586_);
lean_dec_ref(v_a_2585_);
lean_dec(v_a_2584_);
lean_dec_ref(v_a_2583_);
lean_dec(v_a_2582_);
lean_dec(v_a_2581_);
return v___x_2626_;
}
}
else
{
lean_object* v_a_2628_; lean_object* v___x_2630_; uint8_t v_isShared_2631_; uint8_t v_isSharedCheck_2635_; 
lean_dec(v_a_2590_);
lean_dec_ref(v_a_2589_);
lean_dec(v_a_2588_);
lean_dec_ref(v_a_2587_);
lean_dec(v_a_2586_);
lean_dec_ref(v_a_2585_);
lean_dec(v_a_2584_);
lean_dec_ref(v_a_2583_);
lean_dec(v_a_2582_);
lean_dec(v_a_2581_);
v_a_2628_ = lean_ctor_get(v___x_2623_, 0);
v_isSharedCheck_2635_ = !lean_is_exclusive(v___x_2623_);
if (v_isSharedCheck_2635_ == 0)
{
v___x_2630_ = v___x_2623_;
v_isShared_2631_ = v_isSharedCheck_2635_;
goto v_resetjp_2629_;
}
else
{
lean_inc(v_a_2628_);
lean_dec(v___x_2623_);
v___x_2630_ = lean_box(0);
v_isShared_2631_ = v_isSharedCheck_2635_;
goto v_resetjp_2629_;
}
v_resetjp_2629_:
{
lean_object* v___x_2633_; 
if (v_isShared_2631_ == 0)
{
v___x_2633_ = v___x_2630_;
goto v_reusejp_2632_;
}
else
{
lean_object* v_reuseFailAlloc_2634_; 
v_reuseFailAlloc_2634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2634_, 0, v_a_2628_);
v___x_2633_ = v_reuseFailAlloc_2634_;
goto v_reusejp_2632_;
}
v_reusejp_2632_:
{
return v___x_2633_;
}
}
}
}
v___jp_2592_:
{
lean_object* v___x_2593_; lean_object* v___x_2594_; 
v___x_2593_ = lean_box(0);
v___x_2594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2594_, 0, v___x_2593_);
return v___x_2594_;
}
v___jp_2595_:
{
if (v_expensive_2580_ == 0)
{
lean_dec(v___y_2605_);
lean_dec_ref(v___y_2604_);
lean_dec(v___y_2603_);
lean_dec_ref(v___y_2602_);
lean_dec(v___y_2601_);
lean_dec_ref(v___y_2600_);
lean_dec(v___y_2599_);
lean_dec_ref(v___y_2598_);
lean_dec(v___y_2597_);
lean_dec(v___y_2596_);
goto v___jp_2592_;
}
else
{
lean_object* v_options_2606_; lean_object* v___x_2607_; uint8_t v___x_2608_; 
v_options_2606_ = lean_ctor_get(v___y_2604_, 2);
v___x_2607_ = l_Lean_Meta_Grind_grind_debug_proofs;
v___x_2608_ = l_Lean_Option_get___at___00Lean_Meta_Grind_checkInvariants_spec__0(v_options_2606_, v___x_2607_);
if (v___x_2608_ == 0)
{
lean_dec(v___y_2605_);
lean_dec_ref(v___y_2604_);
lean_dec(v___y_2603_);
lean_dec_ref(v___y_2602_);
lean_dec(v___y_2601_);
lean_dec_ref(v___y_2600_);
lean_dec(v___y_2599_);
lean_dec_ref(v___y_2598_);
lean_dec(v___y_2597_);
lean_dec(v___y_2596_);
goto v___jp_2592_;
}
else
{
lean_object* v___x_2609_; 
v___x_2609_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs(v___y_2596_, v___y_2597_, v___y_2598_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_, v___y_2605_);
return v___x_2609_;
}
}
}
v___jp_2610_:
{
lean_object* v___x_2621_; 
lean_inc(v___y_2620_);
lean_inc_ref(v___y_2619_);
lean_inc(v___y_2618_);
lean_inc_ref(v___y_2617_);
lean_inc(v___y_2616_);
lean_inc_ref(v___y_2615_);
lean_inc(v___y_2614_);
lean_inc_ref(v___y_2613_);
lean_inc(v___y_2612_);
lean_inc(v___y_2611_);
v___x_2621_ = l_Lean_Meta_Grind_Solvers_checkInvariants(v___y_2611_, v___y_2612_, v___y_2613_, v___y_2614_, v___y_2615_, v___y_2616_, v___y_2617_, v___y_2618_, v___y_2619_, v___y_2620_);
if (lean_obj_tag(v___x_2621_) == 0)
{
lean_dec_ref(v___x_2621_);
v___y_2596_ = v___y_2611_;
v___y_2597_ = v___y_2612_;
v___y_2598_ = v___y_2613_;
v___y_2599_ = v___y_2614_;
v___y_2600_ = v___y_2615_;
v___y_2601_ = v___y_2616_;
v___y_2602_ = v___y_2617_;
v___y_2603_ = v___y_2618_;
v___y_2604_ = v___y_2619_;
v___y_2605_ = v___y_2620_;
goto v___jp_2595_;
}
else
{
lean_dec(v___y_2620_);
lean_dec_ref(v___y_2619_);
lean_dec(v___y_2618_);
lean_dec_ref(v___y_2617_);
lean_dec(v___y_2616_);
lean_dec_ref(v___y_2615_);
lean_dec(v___y_2614_);
lean_dec_ref(v___y_2613_);
lean_dec(v___y_2612_);
lean_dec(v___y_2611_);
return v___x_2621_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_checkInvariants___boxed(lean_object* v_expensive_2636_, lean_object* v_a_2637_, lean_object* v_a_2638_, lean_object* v_a_2639_, lean_object* v_a_2640_, lean_object* v_a_2641_, lean_object* v_a_2642_, lean_object* v_a_2643_, lean_object* v_a_2644_, lean_object* v_a_2645_, lean_object* v_a_2646_, lean_object* v_a_2647_){
_start:
{
uint8_t v_expensive_boxed_2648_; lean_object* v_res_2649_; 
v_expensive_boxed_2648_ = lean_unbox(v_expensive_2636_);
v_res_2649_ = l_Lean_Meta_Grind_checkInvariants(v_expensive_boxed_2648_, v_a_2637_, v_a_2638_, v_a_2639_, v_a_2640_, v_a_2641_, v_a_2642_, v_a_2643_, v_a_2644_, v_a_2645_, v_a_2646_);
return v_res_2649_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Goal_checkInvariants_spec__0___redArg___lam__0(lean_object* v_x_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_){
_start:
{
lean_object* v___x_2661_; 
v___x_2661_ = lean_apply_10(v_x_2650_, v___y_2651_, v___y_2652_, v___y_2653_, v___y_2654_, v___y_2655_, v___y_2656_, v___y_2657_, v___y_2658_, v___y_2659_, lean_box(0));
return v___x_2661_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Goal_checkInvariants_spec__0___redArg___lam__0___boxed(lean_object* v_x_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_){
_start:
{
lean_object* v_res_2673_; 
v_res_2673_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Goal_checkInvariants_spec__0___redArg___lam__0(v_x_2662_, v___y_2663_, v___y_2664_, v___y_2665_, v___y_2666_, v___y_2667_, v___y_2668_, v___y_2669_, v___y_2670_, v___y_2671_);
return v_res_2673_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Goal_checkInvariants_spec__0___redArg(lean_object* v_mvarId_2674_, lean_object* v_x_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_){
_start:
{
lean_object* v___f_2686_; lean_object* v___x_2687_; 
v___f_2686_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Goal_checkInvariants_spec__0___redArg___lam__0___boxed), 11, 6);
lean_closure_set(v___f_2686_, 0, v_x_2675_);
lean_closure_set(v___f_2686_, 1, v___y_2676_);
lean_closure_set(v___f_2686_, 2, v___y_2677_);
lean_closure_set(v___f_2686_, 3, v___y_2678_);
lean_closure_set(v___f_2686_, 4, v___y_2679_);
lean_closure_set(v___f_2686_, 5, v___y_2680_);
v___x_2687_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_2674_, v___f_2686_, v___y_2681_, v___y_2682_, v___y_2683_, v___y_2684_);
if (lean_obj_tag(v___x_2687_) == 0)
{
return v___x_2687_;
}
else
{
lean_object* v_a_2688_; lean_object* v___x_2690_; uint8_t v_isShared_2691_; uint8_t v_isSharedCheck_2695_; 
v_a_2688_ = lean_ctor_get(v___x_2687_, 0);
v_isSharedCheck_2695_ = !lean_is_exclusive(v___x_2687_);
if (v_isSharedCheck_2695_ == 0)
{
v___x_2690_ = v___x_2687_;
v_isShared_2691_ = v_isSharedCheck_2695_;
goto v_resetjp_2689_;
}
else
{
lean_inc(v_a_2688_);
lean_dec(v___x_2687_);
v___x_2690_ = lean_box(0);
v_isShared_2691_ = v_isSharedCheck_2695_;
goto v_resetjp_2689_;
}
v_resetjp_2689_:
{
lean_object* v___x_2693_; 
if (v_isShared_2691_ == 0)
{
v___x_2693_ = v___x_2690_;
goto v_reusejp_2692_;
}
else
{
lean_object* v_reuseFailAlloc_2694_; 
v_reuseFailAlloc_2694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2694_, 0, v_a_2688_);
v___x_2693_ = v_reuseFailAlloc_2694_;
goto v_reusejp_2692_;
}
v_reusejp_2692_:
{
return v___x_2693_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Goal_checkInvariants_spec__0___redArg___boxed(lean_object* v_mvarId_2696_, lean_object* v_x_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_){
_start:
{
lean_object* v_res_2708_; 
v_res_2708_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Goal_checkInvariants_spec__0___redArg(v_mvarId_2696_, v_x_2697_, v___y_2698_, v___y_2699_, v___y_2700_, v___y_2701_, v___y_2702_, v___y_2703_, v___y_2704_, v___y_2705_, v___y_2706_);
return v_res_2708_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Goal_checkInvariants_spec__0(lean_object* v_00_u03b1_2709_, lean_object* v_mvarId_2710_, lean_object* v_x_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_){
_start:
{
lean_object* v___x_2722_; 
v___x_2722_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Goal_checkInvariants_spec__0___redArg(v_mvarId_2710_, v_x_2711_, v___y_2712_, v___y_2713_, v___y_2714_, v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_, v___y_2719_, v___y_2720_);
return v___x_2722_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Goal_checkInvariants_spec__0___boxed(lean_object* v_00_u03b1_2723_, lean_object* v_mvarId_2724_, lean_object* v_x_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_){
_start:
{
lean_object* v_res_2736_; 
v_res_2736_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Goal_checkInvariants_spec__0(v_00_u03b1_2723_, v_mvarId_2724_, v_x_2725_, v___y_2726_, v___y_2727_, v___y_2728_, v___y_2729_, v___y_2730_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_);
return v_res_2736_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Goal_checkInvariants___lam__0(lean_object* v_goal_2737_, uint8_t v_expensive_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_){
_start:
{
lean_object* v___x_2749_; lean_object* v___x_2750_; 
v___x_2749_ = lean_st_mk_ref(v_goal_2737_);
lean_inc(v___x_2749_);
v___x_2750_ = l_Lean_Meta_Grind_checkInvariants(v_expensive_2738_, v___x_2749_, v___y_2739_, v___y_2740_, v___y_2741_, v___y_2742_, v___y_2743_, v___y_2744_, v___y_2745_, v___y_2746_, v___y_2747_);
if (lean_obj_tag(v___x_2750_) == 0)
{
lean_object* v___x_2752_; uint8_t v_isShared_2753_; uint8_t v_isSharedCheck_2759_; 
v_isSharedCheck_2759_ = !lean_is_exclusive(v___x_2750_);
if (v_isSharedCheck_2759_ == 0)
{
lean_object* v_unused_2760_; 
v_unused_2760_ = lean_ctor_get(v___x_2750_, 0);
lean_dec(v_unused_2760_);
v___x_2752_ = v___x_2750_;
v_isShared_2753_ = v_isSharedCheck_2759_;
goto v_resetjp_2751_;
}
else
{
lean_dec(v___x_2750_);
v___x_2752_ = lean_box(0);
v_isShared_2753_ = v_isSharedCheck_2759_;
goto v_resetjp_2751_;
}
v_resetjp_2751_:
{
lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2757_; 
v___x_2754_ = lean_st_ref_get(v___x_2749_);
v___x_2755_ = lean_st_ref_get(v___x_2749_);
lean_dec(v___x_2749_);
lean_dec(v___x_2755_);
if (v_isShared_2753_ == 0)
{
lean_ctor_set(v___x_2752_, 0, v___x_2754_);
v___x_2757_ = v___x_2752_;
goto v_reusejp_2756_;
}
else
{
lean_object* v_reuseFailAlloc_2758_; 
v_reuseFailAlloc_2758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2758_, 0, v___x_2754_);
v___x_2757_ = v_reuseFailAlloc_2758_;
goto v_reusejp_2756_;
}
v_reusejp_2756_:
{
return v___x_2757_;
}
}
}
else
{
lean_object* v_a_2761_; lean_object* v___x_2763_; uint8_t v_isShared_2764_; uint8_t v_isSharedCheck_2768_; 
lean_dec(v___x_2749_);
v_a_2761_ = lean_ctor_get(v___x_2750_, 0);
v_isSharedCheck_2768_ = !lean_is_exclusive(v___x_2750_);
if (v_isSharedCheck_2768_ == 0)
{
v___x_2763_ = v___x_2750_;
v_isShared_2764_ = v_isSharedCheck_2768_;
goto v_resetjp_2762_;
}
else
{
lean_inc(v_a_2761_);
lean_dec(v___x_2750_);
v___x_2763_ = lean_box(0);
v_isShared_2764_ = v_isSharedCheck_2768_;
goto v_resetjp_2762_;
}
v_resetjp_2762_:
{
lean_object* v___x_2766_; 
if (v_isShared_2764_ == 0)
{
v___x_2766_ = v___x_2763_;
goto v_reusejp_2765_;
}
else
{
lean_object* v_reuseFailAlloc_2767_; 
v_reuseFailAlloc_2767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2767_, 0, v_a_2761_);
v___x_2766_ = v_reuseFailAlloc_2767_;
goto v_reusejp_2765_;
}
v_reusejp_2765_:
{
return v___x_2766_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Goal_checkInvariants___lam__0___boxed(lean_object* v_goal_2769_, lean_object* v_expensive_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_, lean_object* v___y_2780_){
_start:
{
uint8_t v_expensive_boxed_2781_; lean_object* v_res_2782_; 
v_expensive_boxed_2781_ = lean_unbox(v_expensive_2770_);
v_res_2782_ = l_Lean_Meta_Grind_Goal_checkInvariants___lam__0(v_goal_2769_, v_expensive_boxed_2781_, v___y_2771_, v___y_2772_, v___y_2773_, v___y_2774_, v___y_2775_, v___y_2776_, v___y_2777_, v___y_2778_, v___y_2779_);
return v_res_2782_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Goal_checkInvariants(lean_object* v_goal_2783_, uint8_t v_expensive_2784_, lean_object* v_a_2785_, lean_object* v_a_2786_, lean_object* v_a_2787_, lean_object* v_a_2788_, lean_object* v_a_2789_, lean_object* v_a_2790_, lean_object* v_a_2791_, lean_object* v_a_2792_, lean_object* v_a_2793_){
_start:
{
lean_object* v_mvarId_2795_; lean_object* v___x_2796_; lean_object* v___f_2797_; lean_object* v___x_2798_; 
v_mvarId_2795_ = lean_ctor_get(v_goal_2783_, 1);
lean_inc(v_mvarId_2795_);
v___x_2796_ = lean_box(v_expensive_2784_);
v___f_2797_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Goal_checkInvariants___lam__0___boxed), 12, 2);
lean_closure_set(v___f_2797_, 0, v_goal_2783_);
lean_closure_set(v___f_2797_, 1, v___x_2796_);
v___x_2798_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Goal_checkInvariants_spec__0___redArg(v_mvarId_2795_, v___f_2797_, v_a_2785_, v_a_2786_, v_a_2787_, v_a_2788_, v_a_2789_, v_a_2790_, v_a_2791_, v_a_2792_, v_a_2793_);
if (lean_obj_tag(v___x_2798_) == 0)
{
lean_object* v___x_2800_; uint8_t v_isShared_2801_; uint8_t v_isSharedCheck_2806_; 
v_isSharedCheck_2806_ = !lean_is_exclusive(v___x_2798_);
if (v_isSharedCheck_2806_ == 0)
{
lean_object* v_unused_2807_; 
v_unused_2807_ = lean_ctor_get(v___x_2798_, 0);
lean_dec(v_unused_2807_);
v___x_2800_ = v___x_2798_;
v_isShared_2801_ = v_isSharedCheck_2806_;
goto v_resetjp_2799_;
}
else
{
lean_dec(v___x_2798_);
v___x_2800_ = lean_box(0);
v_isShared_2801_ = v_isSharedCheck_2806_;
goto v_resetjp_2799_;
}
v_resetjp_2799_:
{
lean_object* v___x_2802_; lean_object* v___x_2804_; 
v___x_2802_ = lean_box(0);
if (v_isShared_2801_ == 0)
{
lean_ctor_set(v___x_2800_, 0, v___x_2802_);
v___x_2804_ = v___x_2800_;
goto v_reusejp_2803_;
}
else
{
lean_object* v_reuseFailAlloc_2805_; 
v_reuseFailAlloc_2805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2805_, 0, v___x_2802_);
v___x_2804_ = v_reuseFailAlloc_2805_;
goto v_reusejp_2803_;
}
v_reusejp_2803_:
{
return v___x_2804_;
}
}
}
else
{
lean_object* v_a_2808_; lean_object* v___x_2810_; uint8_t v_isShared_2811_; uint8_t v_isSharedCheck_2815_; 
v_a_2808_ = lean_ctor_get(v___x_2798_, 0);
v_isSharedCheck_2815_ = !lean_is_exclusive(v___x_2798_);
if (v_isSharedCheck_2815_ == 0)
{
v___x_2810_ = v___x_2798_;
v_isShared_2811_ = v_isSharedCheck_2815_;
goto v_resetjp_2809_;
}
else
{
lean_inc(v_a_2808_);
lean_dec(v___x_2798_);
v___x_2810_ = lean_box(0);
v_isShared_2811_ = v_isSharedCheck_2815_;
goto v_resetjp_2809_;
}
v_resetjp_2809_:
{
lean_object* v___x_2813_; 
if (v_isShared_2811_ == 0)
{
v___x_2813_ = v___x_2810_;
goto v_reusejp_2812_;
}
else
{
lean_object* v_reuseFailAlloc_2814_; 
v_reuseFailAlloc_2814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2814_, 0, v_a_2808_);
v___x_2813_ = v_reuseFailAlloc_2814_;
goto v_reusejp_2812_;
}
v_reusejp_2812_:
{
return v___x_2813_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Goal_checkInvariants___boxed(lean_object* v_goal_2816_, lean_object* v_expensive_2817_, lean_object* v_a_2818_, lean_object* v_a_2819_, lean_object* v_a_2820_, lean_object* v_a_2821_, lean_object* v_a_2822_, lean_object* v_a_2823_, lean_object* v_a_2824_, lean_object* v_a_2825_, lean_object* v_a_2826_, lean_object* v_a_2827_){
_start:
{
uint8_t v_expensive_boxed_2828_; lean_object* v_res_2829_; 
v_expensive_boxed_2828_ = lean_unbox(v_expensive_2817_);
v_res_2829_ = l_Lean_Meta_Grind_Goal_checkInvariants(v_goal_2816_, v_expensive_boxed_2828_, v_a_2818_, v_a_2819_, v_a_2820_, v_a_2821_, v_a_2822_, v_a_2823_, v_a_2824_, v_a_2825_, v_a_2826_);
return v_res_2829_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Util(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Inv(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Grind_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Inv(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
lean_object* initialize_Init_Grind_Util(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Util(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Inv(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Inv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Inv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Inv(builtin);
}
#ifdef __cplusplus
}
#endif
