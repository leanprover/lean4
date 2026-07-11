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
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getExprs___redArg(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_get_x21___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(lean_object*, lean_object*);
uint8_t lean_bool_not(uint8_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_instInhabitedGoalM(lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
uint8_t lean_expr_equal(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Meta_Grind_Goal_getENode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isRoot___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getParents___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_ParentSet_isEmpty(lean_object*);
lean_object* l_Lean_Meta_Grind_ParentSet_elems(lean_object*);
lean_object* l_Lean_Meta_Grind_useFunCC___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Meta_Grind_Goal_getRoot_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
uint8_t l_Lean_Meta_Grind_isMatchCond(lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t l_Lean_Meta_Grind_ENode_isRoot(lean_object*);
lean_object* l_Lean_Meta_Grind_Goal_getRoot(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Goal_getTarget_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Goal_getNext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_hasSameType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_congrHash(lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_isCongruent(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isCongrRoot___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getCongrRoot___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Goal_getEqcs(lean_object*, uint8_t);
lean_object* l_Lean_Meta_Grind_mkEqHEqProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_check(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_updateLastTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "Lean.Meta.Tactic.Grind.Inv"};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__0 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__0_value;
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 63, .m_capacity = 63, .m_length = 62, .m_data = "_private.Lean.Meta.Tactic.Grind.Inv.0.Lean.Meta.Grind.checkEqc"};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__1 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__1_value;
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 75, .m_capacity = 75, .m_length = 74, .m_data = "assertion violation: isSameExpr n root.self\n    -- Go to next element\n    "};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__2 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__2_value;
static lean_once_cell_t l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__3;
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 173, .m_capacity = 173, .m_length = 172, .m_data = "assertion violation: ( __do_lift._@.Lean.Meta.Tactic.Grind.Inv.684779629._hygCtx._hyg.282.0 )\n    -- Starting at `curr`, following the `target\?` field leads to `root`.\n    "};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__4 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__4_value;
static lean_once_cell_t l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__5;
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2___redArg(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 148, .m_capacity = 148, .m_length = 147, .m_data = "assertion violation: isSameExpr ( __do_lift._@.Lean.Meta.Tactic.Grind.Inv.684779629._hygCtx._hyg.53.0 ) root.self\n    -- Check congruence root\n    "};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___closed__0 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___closed__0_value;
static lean_once_cell_t l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___closed__1;
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 202, .m_capacity = 202, .m_length = 201, .m_data = "assertion violation: ( __do_lift._@.Lean.Meta.Tactic.Grind.Inv.684779629._hygCtx._hyg.219.0 )\n    -- If the equivalence class does not have HEq proofs, then the types must be definitionally equal.\n    "};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___closed__2 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___closed__2_value;
static lean_once_cell_t l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___closed__3;
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 114, .m_capacity = 114, .m_length = 113, .m_data = "assertion violation: isSameExpr e ( __do_lift._@.Lean.Meta.Tactic.Grind.Inv.684779629._hygCtx._hyg.172.0 )\n      "};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___closed__4 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___closed__4_value;
static lean_once_cell_t l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___closed__5;
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "assertion violation: root.size == size\n\n"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2(lean_object*, lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkChild___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkChild___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkChild(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkChild___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___closed__0 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___closed__0_value;
static const lean_ctor_object l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___closed__1 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___closed__1_value;
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "HEq"};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___closed__2 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___closed__2_value;
static const lean_ctor_object l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(67, 180, 169, 191, 74, 196, 152, 188)}};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___closed__3 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___closed__3_value;
static const lean_ctor_object l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___closed__4 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___closed__4_value;
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 102, .m_capacity = 102, .m_length = 101, .m_data = "assertion violation: ( __do_lift._@.Lean.Meta.Tactic.Grind.Inv.3145645808._hygCtx._hyg.193.0 )\n      "};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__1 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__1_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__2;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 100, .m_capacity = 100, .m_length = 99, .m_data = "assertion violation: ( __do_lift._@.Lean.Meta.Tactic.Grind.Inv.3145645808._hygCtx._hyg.488.0 )\n    "};
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
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 105, .m_capacity = 105, .m_length = 104, .m_data = "assertion violation: ( __do_lift._@.Lean.Meta.Tactic.Grind.Inv.3145645808._hygCtx._hyg.532.0 ).isEmpty\n\n"};
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
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 114, .m_capacity = 114, .m_length = 109, .m_data = "assertion violation: !isSameExpr e₁ e₂\n      -- and the two expressions must not be structurally equal\n      "};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg___closed__1_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg___closed__2;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 40, .m_data = "assertion violation: !Expr.equal e₁ e₂\n\n"};
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
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__0___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__0___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__0___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__0___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "grind"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__0_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "debug"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__1 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__1_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "proofs"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__2 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__2_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__3_value_aux_0),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(92, 174, 15, 22, 76, 124, 59, 78)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__3_value_aux_1),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(25, 245, 48, 218, 201, 55, 112, 25)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__3 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__3_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__4 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__4_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__5 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__5_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__6;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "checked: "};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__7 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__7_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__8;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " = "};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__9 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__9_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__10;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v___x_14_; lean_object* v___x_30826__overap_15_; lean_object* v___x_16_; 
v___x_14_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__0___closed__0, &l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__0___closed__0);
v___x_30826__overap_15_ = lean_panic_fn_borrowed(v___x_14_, v_msg_2_);
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
v___x_16_ = lean_apply_11(v___x_30826__overap_15_, v___y_3_, v___y_4_, v___y_5_, v___y_6_, v___y_7_, v___y_8_, v___y_9_, v___y_10_, v___y_11_, v___y_12_, lean_box(0));
return v___x_16_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__0___boxed(lean_object* v_msg_17_, lean_object* v___y_18_, lean_object* v___y_19_, lean_object* v___y_20_, lean_object* v___y_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_, lean_object* v___y_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__0(v_msg_17_, v___y_18_, v___y_19_, v___y_20_, v___y_21_, v___y_22_, v___y_23_, v___y_24_, v___y_25_, v___y_26_, v___y_27_);
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
lean_object* v___x_43_; lean_object* v___x_32503__overap_44_; lean_object* v___x_45_; 
v___x_43_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__4___closed__0, &l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__4___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__4___closed__0);
v___x_32503__overap_44_ = lean_panic_fn_borrowed(v___x_43_, v_msg_31_);
lean_inc(v___y_41_);
lean_inc_ref(v___y_40_);
lean_inc(v___y_39_);
lean_inc_ref(v___y_38_);
lean_inc(v___y_37_);
lean_inc_ref(v___y_36_);
lean_inc(v___y_35_);
lean_inc_ref(v___y_34_);
lean_inc(v___y_33_);
lean_inc(v___y_32_);
v___x_45_ = lean_apply_11(v___x_32503__overap_44_, v___y_32_, v___y_33_, v___y_34_, v___y_35_, v___y_36_, v___y_37_, v___y_38_, v___y_39_, v___y_40_, v___y_41_, lean_box(0));
return v___x_45_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__4___boxed(lean_object* v_msg_46_, lean_object* v___y_47_, lean_object* v___y_48_, lean_object* v___y_49_, lean_object* v___y_50_, lean_object* v___y_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_, lean_object* v___y_56_, lean_object* v___y_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__4(v_msg_46_, v___y_47_, v___y_48_, v___y_49_, v___y_50_, v___y_51_, v___y_52_, v___y_53_, v___y_54_, v___y_55_, v___y_56_);
lean_dec(v___y_56_);
lean_dec_ref(v___y_55_);
lean_dec(v___y_54_);
lean_dec_ref(v___y_53_);
lean_dec(v___y_52_);
lean_dec_ref(v___y_51_);
lean_dec(v___y_50_);
lean_dec_ref(v___y_49_);
lean_dec(v___y_48_);
lean_dec(v___y_47_);
return v_res_58_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__1___redArg(lean_object* v_a_59_, lean_object* v___y_60_){
_start:
{
lean_object* v___x_62_; lean_object* v___x_63_; 
v___x_62_ = lean_st_ref_get(v___y_60_);
v___x_63_ = l_Lean_Meta_Grind_Goal_getTarget_x3f(v___x_62_, v_a_59_);
lean_dec(v___x_62_);
if (lean_obj_tag(v___x_63_) == 1)
{
lean_object* v_val_64_; 
lean_dec_ref(v_a_59_);
v_val_64_ = lean_ctor_get(v___x_63_, 0);
lean_inc(v_val_64_);
lean_dec_ref_known(v___x_63_, 1);
v_a_59_ = v_val_64_;
goto _start;
}
else
{
lean_object* v___x_66_; 
lean_dec(v___x_63_);
v___x_66_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_66_, 0, v_a_59_);
return v___x_66_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__1___redArg___boxed(lean_object* v_a_67_, lean_object* v___y_68_, lean_object* v___y_69_){
_start:
{
lean_object* v_res_70_; 
v_res_70_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__1___redArg(v_a_67_, v___y_68_);
lean_dec(v___y_68_);
return v_res_70_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; 
v___x_74_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__2));
v___x_75_ = lean_unsigned_to_nat(4u);
v___x_76_ = lean_unsigned_to_nat(40u);
v___x_77_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__1));
v___x_78_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__0));
v___x_79_ = l_mkPanicMessageWithDecl(v___x_78_, v___x_77_, v___x_76_, v___x_75_, v___x_74_);
return v___x_79_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__5(void){
_start:
{
lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; 
v___x_81_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__4));
v___x_82_ = lean_unsigned_to_nat(6u);
v___x_83_ = lean_unsigned_to_nat(32u);
v___x_84_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__1));
v___x_85_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__0));
v___x_86_ = l_mkPanicMessageWithDecl(v___x_85_, v___x_84_, v___x_83_, v___x_82_, v___x_81_);
return v___x_86_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0(lean_object* v_root_87_, lean_object* v_snd_88_, lean_object* v_curr_89_, lean_object* v___x_90_, lean_object* v_____r_91_, lean_object* v___y_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_, lean_object* v___y_99_, lean_object* v___y_100_, lean_object* v___y_101_){
_start:
{
lean_object* v___y_104_; lean_object* v___y_105_; lean_object* v___y_106_; lean_object* v___y_107_; lean_object* v___y_108_; lean_object* v___y_109_; lean_object* v___y_110_; lean_object* v___y_111_; lean_object* v___y_112_; lean_object* v___y_113_; uint8_t v_heqProofs_153_; 
v_heqProofs_153_ = lean_ctor_get_uint8(v_root_87_, sizeof(void*)*12 + 4);
if (v_heqProofs_153_ == 0)
{
lean_object* v___x_154_; 
lean_inc_ref(v_curr_89_);
lean_inc(v_snd_88_);
v___x_154_ = l_Lean_Meta_Grind_hasSameType(v_snd_88_, v_curr_89_, v___y_98_, v___y_99_, v___y_100_, v___y_101_);
if (lean_obj_tag(v___x_154_) == 0)
{
lean_object* v_a_155_; uint8_t v___x_156_; 
v_a_155_ = lean_ctor_get(v___x_154_, 0);
lean_inc(v_a_155_);
lean_dec_ref_known(v___x_154_, 1);
v___x_156_ = lean_unbox(v_a_155_);
lean_dec(v_a_155_);
if (v___x_156_ == 0)
{
lean_object* v___x_157_; lean_object* v___x_158_; 
lean_dec(v___x_90_);
lean_dec_ref(v_curr_89_);
lean_dec(v_snd_88_);
v___x_157_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__5, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__5_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__5);
v___x_158_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__0(v___x_157_, v___y_92_, v___y_93_, v___y_94_, v___y_95_, v___y_96_, v___y_97_, v___y_98_, v___y_99_, v___y_100_, v___y_101_);
return v___x_158_;
}
else
{
v___y_104_ = v___y_92_;
v___y_105_ = v___y_93_;
v___y_106_ = v___y_94_;
v___y_107_ = v___y_95_;
v___y_108_ = v___y_96_;
v___y_109_ = v___y_97_;
v___y_110_ = v___y_98_;
v___y_111_ = v___y_99_;
v___y_112_ = v___y_100_;
v___y_113_ = v___y_101_;
goto v___jp_103_;
}
}
else
{
lean_object* v_a_159_; lean_object* v___x_161_; uint8_t v_isShared_162_; uint8_t v_isSharedCheck_166_; 
lean_dec(v___x_90_);
lean_dec_ref(v_curr_89_);
lean_dec(v_snd_88_);
v_a_159_ = lean_ctor_get(v___x_154_, 0);
v_isSharedCheck_166_ = !lean_is_exclusive(v___x_154_);
if (v_isSharedCheck_166_ == 0)
{
v___x_161_ = v___x_154_;
v_isShared_162_ = v_isSharedCheck_166_;
goto v_resetjp_160_;
}
else
{
lean_inc(v_a_159_);
lean_dec(v___x_154_);
v___x_161_ = lean_box(0);
v_isShared_162_ = v_isSharedCheck_166_;
goto v_resetjp_160_;
}
v_resetjp_160_:
{
lean_object* v___x_164_; 
if (v_isShared_162_ == 0)
{
v___x_164_ = v___x_161_;
goto v_reusejp_163_;
}
else
{
lean_object* v_reuseFailAlloc_165_; 
v_reuseFailAlloc_165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_165_, 0, v_a_159_);
v___x_164_ = v_reuseFailAlloc_165_;
goto v_reusejp_163_;
}
v_reusejp_163_:
{
return v___x_164_;
}
}
}
}
else
{
v___y_104_ = v___y_92_;
v___y_105_ = v___y_93_;
v___y_106_ = v___y_94_;
v___y_107_ = v___y_95_;
v___y_108_ = v___y_96_;
v___y_109_ = v___y_97_;
v___y_110_ = v___y_98_;
v___y_111_ = v___y_99_;
v___y_112_ = v___y_100_;
v___y_113_ = v___y_101_;
goto v___jp_103_;
}
v___jp_103_:
{
lean_object* v___x_114_; 
lean_inc(v_snd_88_);
v___x_114_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__1___redArg(v_snd_88_, v___y_104_);
if (lean_obj_tag(v___x_114_) == 0)
{
lean_object* v_a_115_; uint8_t v___x_116_; 
v_a_115_ = lean_ctor_get(v___x_114_, 0);
lean_inc(v_a_115_);
lean_dec_ref_known(v___x_114_, 1);
v___x_116_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_a_115_, v_curr_89_);
lean_dec(v_a_115_);
if (v___x_116_ == 0)
{
lean_object* v___x_117_; lean_object* v___x_118_; 
lean_dec(v___x_90_);
lean_dec_ref(v_curr_89_);
lean_dec(v_snd_88_);
v___x_117_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__3, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__3_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__3);
v___x_118_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__0(v___x_117_, v___y_104_, v___y_105_, v___y_106_, v___y_107_, v___y_108_, v___y_109_, v___y_110_, v___y_111_, v___y_112_, v___y_113_);
return v___x_118_;
}
else
{
lean_object* v___x_119_; lean_object* v___x_120_; 
v___x_119_ = lean_st_ref_get(v___y_104_);
v___x_120_ = l_Lean_Meta_Grind_Goal_getNext(v___x_119_, v_snd_88_, v___y_110_, v___y_111_, v___y_112_, v___y_113_);
lean_dec(v___x_119_);
if (lean_obj_tag(v___x_120_) == 0)
{
lean_object* v_a_121_; lean_object* v___x_123_; uint8_t v_isShared_124_; uint8_t v_isSharedCheck_136_; 
v_a_121_ = lean_ctor_get(v___x_120_, 0);
v_isSharedCheck_136_ = !lean_is_exclusive(v___x_120_);
if (v_isSharedCheck_136_ == 0)
{
v___x_123_ = v___x_120_;
v_isShared_124_ = v_isSharedCheck_136_;
goto v_resetjp_122_;
}
else
{
lean_inc(v_a_121_);
lean_dec(v___x_120_);
v___x_123_ = lean_box(0);
v_isShared_124_ = v_isSharedCheck_136_;
goto v_resetjp_122_;
}
v_resetjp_122_:
{
uint8_t v___x_125_; 
v___x_125_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_curr_89_, v_a_121_);
lean_dec_ref(v_curr_89_);
if (v___x_125_ == 0)
{
lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_129_; 
v___x_126_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_126_, 0, v___x_90_);
lean_ctor_set(v___x_126_, 1, v_a_121_);
v___x_127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_127_, 0, v___x_126_);
if (v_isShared_124_ == 0)
{
lean_ctor_set(v___x_123_, 0, v___x_127_);
v___x_129_ = v___x_123_;
goto v_reusejp_128_;
}
else
{
lean_object* v_reuseFailAlloc_130_; 
v_reuseFailAlloc_130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_130_, 0, v___x_127_);
v___x_129_ = v_reuseFailAlloc_130_;
goto v_reusejp_128_;
}
v_reusejp_128_:
{
return v___x_129_;
}
}
else
{
lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_134_; 
v___x_131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_131_, 0, v___x_90_);
lean_ctor_set(v___x_131_, 1, v_a_121_);
v___x_132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_132_, 0, v___x_131_);
if (v_isShared_124_ == 0)
{
lean_ctor_set(v___x_123_, 0, v___x_132_);
v___x_134_ = v___x_123_;
goto v_reusejp_133_;
}
else
{
lean_object* v_reuseFailAlloc_135_; 
v_reuseFailAlloc_135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_135_, 0, v___x_132_);
v___x_134_ = v_reuseFailAlloc_135_;
goto v_reusejp_133_;
}
v_reusejp_133_:
{
return v___x_134_;
}
}
}
}
else
{
lean_object* v_a_137_; lean_object* v___x_139_; uint8_t v_isShared_140_; uint8_t v_isSharedCheck_144_; 
lean_dec(v___x_90_);
lean_dec_ref(v_curr_89_);
v_a_137_ = lean_ctor_get(v___x_120_, 0);
v_isSharedCheck_144_ = !lean_is_exclusive(v___x_120_);
if (v_isSharedCheck_144_ == 0)
{
v___x_139_ = v___x_120_;
v_isShared_140_ = v_isSharedCheck_144_;
goto v_resetjp_138_;
}
else
{
lean_inc(v_a_137_);
lean_dec(v___x_120_);
v___x_139_ = lean_box(0);
v_isShared_140_ = v_isSharedCheck_144_;
goto v_resetjp_138_;
}
v_resetjp_138_:
{
lean_object* v___x_142_; 
if (v_isShared_140_ == 0)
{
v___x_142_ = v___x_139_;
goto v_reusejp_141_;
}
else
{
lean_object* v_reuseFailAlloc_143_; 
v_reuseFailAlloc_143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_143_, 0, v_a_137_);
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
lean_object* v_a_145_; lean_object* v___x_147_; uint8_t v_isShared_148_; uint8_t v_isSharedCheck_152_; 
lean_dec(v___x_90_);
lean_dec_ref(v_curr_89_);
lean_dec(v_snd_88_);
v_a_145_ = lean_ctor_get(v___x_114_, 0);
v_isSharedCheck_152_ = !lean_is_exclusive(v___x_114_);
if (v_isSharedCheck_152_ == 0)
{
v___x_147_ = v___x_114_;
v_isShared_148_ = v_isSharedCheck_152_;
goto v_resetjp_146_;
}
else
{
lean_inc(v_a_145_);
lean_dec(v___x_114_);
v___x_147_ = lean_box(0);
v_isShared_148_ = v_isSharedCheck_152_;
goto v_resetjp_146_;
}
v_resetjp_146_:
{
lean_object* v___x_150_; 
if (v_isShared_148_ == 0)
{
v___x_150_ = v___x_147_;
goto v_reusejp_149_;
}
else
{
lean_object* v_reuseFailAlloc_151_; 
v_reuseFailAlloc_151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_151_, 0, v_a_145_);
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
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___boxed(lean_object* v_root_167_, lean_object* v_snd_168_, lean_object* v_curr_169_, lean_object* v___x_170_, lean_object* v_____r_171_, lean_object* v___y_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_, lean_object* v___y_180_, lean_object* v___y_181_, lean_object* v___y_182_){
_start:
{
lean_object* v_res_183_; 
v_res_183_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0(v_root_167_, v_snd_168_, v_curr_169_, v___x_170_, v_____r_171_, v___y_172_, v___y_173_, v___y_174_, v___y_175_, v___y_176_, v___y_177_, v___y_178_, v___y_179_, v___y_180_, v___y_181_);
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
lean_dec_ref(v_root_167_);
return v_res_183_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2_spec__4___redArg(lean_object* v___x_184_, lean_object* v_keys_185_, lean_object* v_vals_186_, lean_object* v_i_187_, lean_object* v_k_188_){
_start:
{
lean_object* v___x_189_; uint8_t v___x_190_; 
v___x_189_ = lean_array_get_size(v_keys_185_);
v___x_190_ = lean_nat_dec_lt(v_i_187_, v___x_189_);
if (v___x_190_ == 0)
{
lean_object* v___x_191_; 
lean_dec_ref(v_k_188_);
lean_dec(v_i_187_);
v___x_191_ = lean_box(0);
return v___x_191_;
}
else
{
lean_object* v_k_x27_192_; uint8_t v___x_193_; 
v_k_x27_192_ = lean_array_fget_borrowed(v_keys_185_, v_i_187_);
lean_inc(v_k_x27_192_);
lean_inc_ref(v_k_188_);
v___x_193_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_isCongruent(v___x_184_, v_k_188_, v_k_x27_192_);
if (v___x_193_ == 0)
{
lean_object* v___x_194_; lean_object* v___x_195_; 
v___x_194_ = lean_unsigned_to_nat(1u);
v___x_195_ = lean_nat_add(v_i_187_, v___x_194_);
lean_dec(v_i_187_);
v_i_187_ = v___x_195_;
goto _start;
}
else
{
lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; 
lean_dec_ref(v_k_188_);
v___x_197_ = lean_array_fget_borrowed(v_vals_186_, v_i_187_);
lean_dec(v_i_187_);
lean_inc(v___x_197_);
lean_inc(v_k_x27_192_);
v___x_198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_198_, 0, v_k_x27_192_);
lean_ctor_set(v___x_198_, 1, v___x_197_);
v___x_199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_199_, 0, v___x_198_);
return v___x_199_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2_spec__4___redArg___boxed(lean_object* v___x_200_, lean_object* v_keys_201_, lean_object* v_vals_202_, lean_object* v_i_203_, lean_object* v_k_204_){
_start:
{
lean_object* v_res_205_; 
v_res_205_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2_spec__4___redArg(v___x_200_, v_keys_201_, v_vals_202_, v_i_203_, v_k_204_);
lean_dec_ref(v_vals_202_);
lean_dec_ref(v_keys_201_);
lean_dec_ref(v___x_200_);
return v_res_205_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2___redArg(lean_object* v___x_206_, lean_object* v_x_207_, size_t v_x_208_, lean_object* v_x_209_){
_start:
{
if (lean_obj_tag(v_x_207_) == 0)
{
lean_object* v_es_210_; lean_object* v___x_211_; size_t v___x_212_; size_t v___x_213_; lean_object* v_j_214_; lean_object* v___x_215_; 
v_es_210_ = lean_ctor_get(v_x_207_, 0);
lean_inc_ref(v_es_210_);
lean_dec_ref_known(v_x_207_, 1);
v___x_211_ = lean_box(2);
v___x_212_ = ((size_t)31ULL);
v___x_213_ = lean_usize_land(v_x_208_, v___x_212_);
v_j_214_ = lean_usize_to_nat(v___x_213_);
v___x_215_ = lean_array_get(v___x_211_, v_es_210_, v_j_214_);
lean_dec(v_j_214_);
lean_dec_ref(v_es_210_);
switch(lean_obj_tag(v___x_215_))
{
case 0:
{
lean_object* v_key_216_; lean_object* v_val_217_; uint8_t v___x_218_; 
v_key_216_ = lean_ctor_get(v___x_215_, 0);
lean_inc_n(v_key_216_, 2);
v_val_217_ = lean_ctor_get(v___x_215_, 1);
lean_inc(v_val_217_);
lean_dec_ref_known(v___x_215_, 2);
v___x_218_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_isCongruent(v___x_206_, v_x_209_, v_key_216_);
if (v___x_218_ == 0)
{
lean_object* v___x_219_; 
lean_dec(v_val_217_);
lean_dec(v_key_216_);
v___x_219_ = lean_box(0);
return v___x_219_;
}
else
{
lean_object* v___x_220_; lean_object* v___x_221_; 
v___x_220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_220_, 0, v_key_216_);
lean_ctor_set(v___x_220_, 1, v_val_217_);
v___x_221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_221_, 0, v___x_220_);
return v___x_221_;
}
}
case 1:
{
lean_object* v_node_222_; size_t v___x_223_; size_t v___x_224_; 
v_node_222_ = lean_ctor_get(v___x_215_, 0);
lean_inc(v_node_222_);
lean_dec_ref_known(v___x_215_, 1);
v___x_223_ = ((size_t)5ULL);
v___x_224_ = lean_usize_shift_right(v_x_208_, v___x_223_);
v_x_207_ = v_node_222_;
v_x_208_ = v___x_224_;
goto _start;
}
default: 
{
lean_object* v___x_226_; 
lean_dec_ref(v_x_209_);
v___x_226_ = lean_box(0);
return v___x_226_;
}
}
}
else
{
lean_object* v_ks_227_; lean_object* v_vs_228_; lean_object* v___x_229_; lean_object* v___x_230_; 
v_ks_227_ = lean_ctor_get(v_x_207_, 0);
lean_inc_ref(v_ks_227_);
v_vs_228_ = lean_ctor_get(v_x_207_, 1);
lean_inc_ref(v_vs_228_);
lean_dec_ref_known(v_x_207_, 2);
v___x_229_ = lean_unsigned_to_nat(0u);
v___x_230_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2_spec__4___redArg(v___x_206_, v_ks_227_, v_vs_228_, v___x_229_, v_x_209_);
lean_dec_ref(v_vs_228_);
lean_dec_ref(v_ks_227_);
return v___x_230_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2___redArg___boxed(lean_object* v___x_231_, lean_object* v_x_232_, lean_object* v_x_233_, lean_object* v_x_234_){
_start:
{
size_t v_x_33267__boxed_235_; lean_object* v_res_236_; 
v_x_33267__boxed_235_ = lean_unbox_usize(v_x_233_);
lean_dec(v_x_233_);
v_res_236_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2___redArg(v___x_231_, v_x_232_, v_x_33267__boxed_235_, v_x_234_);
lean_dec_ref(v___x_231_);
return v_res_236_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2___redArg(lean_object* v___x_237_, lean_object* v_x_238_, lean_object* v_x_239_){
_start:
{
uint64_t v___x_240_; size_t v___x_241_; lean_object* v___x_242_; 
lean_inc_ref(v_x_239_);
v___x_240_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_congrHash(v___x_237_, v_x_239_);
v___x_241_ = lean_uint64_to_usize(v___x_240_);
lean_inc_ref(v_x_238_);
v___x_242_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2___redArg(v___x_237_, v_x_238_, v___x_241_, v_x_239_);
return v___x_242_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2___redArg___boxed(lean_object* v___x_243_, lean_object* v_x_244_, lean_object* v_x_245_){
_start:
{
lean_object* v_res_246_; 
v_res_246_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2___redArg(v___x_243_, v_x_244_, v_x_245_);
lean_dec_ref(v_x_244_);
lean_dec_ref(v___x_243_);
return v_res_246_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; 
v___x_248_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___closed__0));
v___x_249_ = lean_unsigned_to_nat(4u);
v___x_250_ = lean_unsigned_to_nat(22u);
v___x_251_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__1));
v___x_252_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__0));
v___x_253_ = l_mkPanicMessageWithDecl(v___x_252_, v___x_251_, v___x_250_, v___x_249_, v___x_248_);
return v___x_253_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; 
v___x_255_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___closed__2));
v___x_256_ = lean_unsigned_to_nat(8u);
v___x_257_ = lean_unsigned_to_nat(29u);
v___x_258_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__1));
v___x_259_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__0));
v___x_260_ = l_mkPanicMessageWithDecl(v___x_259_, v___x_258_, v___x_257_, v___x_256_, v___x_255_);
return v___x_260_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___closed__5(void){
_start:
{
lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; 
v___x_262_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___closed__4));
v___x_263_ = lean_unsigned_to_nat(10u);
v___x_264_ = lean_unsigned_to_nat(27u);
v___x_265_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__1));
v___x_266_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__0));
v___x_267_ = l_mkPanicMessageWithDecl(v___x_266_, v___x_265_, v___x_264_, v___x_263_, v___x_262_);
return v___x_267_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg(lean_object* v_curr_268_, lean_object* v_root_269_, lean_object* v_a_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_){
_start:
{
lean_object* v___y_283_; lean_object* v___x_303_; lean_object* v_fst_304_; lean_object* v_snd_305_; lean_object* v___x_306_; 
v___x_303_ = lean_st_ref_get(v___y_271_);
v_fst_304_ = lean_ctor_get(v_a_270_, 0);
lean_inc(v_fst_304_);
v_snd_305_ = lean_ctor_get(v_a_270_, 1);
lean_inc_n(v_snd_305_, 2);
lean_dec_ref(v_a_270_);
v___x_306_ = l_Lean_Meta_Grind_Goal_getRoot(v___x_303_, v_snd_305_, v___y_277_, v___y_278_, v___y_279_, v___y_280_);
lean_dec(v___x_303_);
if (lean_obj_tag(v___x_306_) == 0)
{
lean_object* v_a_307_; uint8_t v___x_308_; 
v_a_307_ = lean_ctor_get(v___x_306_, 0);
lean_inc(v_a_307_);
lean_dec_ref_known(v___x_306_, 1);
v___x_308_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_a_307_, v_curr_268_);
lean_dec(v_a_307_);
if (v___x_308_ == 0)
{
lean_object* v___x_309_; lean_object* v___x_310_; 
lean_dec(v_snd_305_);
lean_dec(v_fst_304_);
v___x_309_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___closed__1, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___closed__1_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___closed__1);
v___x_310_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__0(v___x_309_, v___y_271_, v___y_272_, v___y_273_, v___y_274_, v___y_275_, v___y_276_, v___y_277_, v___y_278_, v___y_279_, v___y_280_);
v___y_283_ = v___x_310_;
goto v___jp_282_;
}
else
{
lean_object* v___x_311_; lean_object* v___x_312_; uint8_t v___x_313_; 
v___x_311_ = lean_unsigned_to_nat(1u);
v___x_312_ = lean_nat_add(v_fst_304_, v___x_311_);
lean_dec(v_fst_304_);
v___x_313_ = l_Lean_Expr_isApp(v_snd_305_);
if (v___x_313_ == 0)
{
lean_object* v___x_314_; lean_object* v___x_315_; 
v___x_314_ = lean_box(0);
lean_inc_ref(v_curr_268_);
v___x_315_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0(v_root_269_, v_snd_305_, v_curr_268_, v___x_312_, v___x_314_, v___y_271_, v___y_272_, v___y_273_, v___y_274_, v___y_275_, v___y_276_, v___y_277_, v___y_278_, v___y_279_, v___y_280_);
v___y_283_ = v___x_315_;
goto v___jp_282_;
}
else
{
lean_object* v___x_316_; lean_object* v_toGoalState_317_; lean_object* v_enodeMap_318_; lean_object* v_congrTable_319_; lean_object* v___x_320_; 
v___x_316_ = lean_st_ref_get(v___y_271_);
v_toGoalState_317_ = lean_ctor_get(v___x_316_, 0);
lean_inc_ref(v_toGoalState_317_);
lean_dec(v___x_316_);
v_enodeMap_318_ = lean_ctor_get(v_toGoalState_317_, 1);
lean_inc_ref(v_enodeMap_318_);
v_congrTable_319_ = lean_ctor_get(v_toGoalState_317_, 4);
lean_inc_ref(v_congrTable_319_);
lean_dec_ref(v_toGoalState_317_);
lean_inc(v_snd_305_);
v___x_320_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2___redArg(v_enodeMap_318_, v_congrTable_319_, v_snd_305_);
lean_dec_ref(v_congrTable_319_);
lean_dec_ref(v_enodeMap_318_);
if (lean_obj_tag(v___x_320_) == 0)
{
lean_object* v___x_321_; 
lean_inc(v_snd_305_);
v___x_321_ = l_Lean_Meta_Grind_isCongrRoot___redArg(v_snd_305_, v___y_271_, v___y_277_, v___y_278_, v___y_279_, v___y_280_);
if (lean_obj_tag(v___x_321_) == 0)
{
lean_object* v_a_322_; uint8_t v___x_323_; 
v_a_322_ = lean_ctor_get(v___x_321_, 0);
lean_inc(v_a_322_);
lean_dec_ref_known(v___x_321_, 1);
v___x_323_ = lean_unbox(v_a_322_);
lean_dec(v_a_322_);
if (v___x_323_ == 0)
{
lean_object* v___x_324_; lean_object* v___x_325_; 
lean_dec(v___x_312_);
lean_dec(v_snd_305_);
v___x_324_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___closed__3, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___closed__3_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___closed__3);
v___x_325_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__0(v___x_324_, v___y_271_, v___y_272_, v___y_273_, v___y_274_, v___y_275_, v___y_276_, v___y_277_, v___y_278_, v___y_279_, v___y_280_);
v___y_283_ = v___x_325_;
goto v___jp_282_;
}
else
{
lean_object* v___x_326_; lean_object* v___x_327_; 
v___x_326_ = lean_box(0);
lean_inc_ref(v_curr_268_);
v___x_327_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0(v_root_269_, v_snd_305_, v_curr_268_, v___x_312_, v___x_326_, v___y_271_, v___y_272_, v___y_273_, v___y_274_, v___y_275_, v___y_276_, v___y_277_, v___y_278_, v___y_279_, v___y_280_);
v___y_283_ = v___x_327_;
goto v___jp_282_;
}
}
else
{
lean_object* v_a_328_; lean_object* v___x_330_; uint8_t v_isShared_331_; uint8_t v_isSharedCheck_335_; 
lean_dec(v___x_312_);
lean_dec(v_snd_305_);
lean_dec_ref(v_curr_268_);
v_a_328_ = lean_ctor_get(v___x_321_, 0);
v_isSharedCheck_335_ = !lean_is_exclusive(v___x_321_);
if (v_isSharedCheck_335_ == 0)
{
v___x_330_ = v___x_321_;
v_isShared_331_ = v_isSharedCheck_335_;
goto v_resetjp_329_;
}
else
{
lean_inc(v_a_328_);
lean_dec(v___x_321_);
v___x_330_ = lean_box(0);
v_isShared_331_ = v_isSharedCheck_335_;
goto v_resetjp_329_;
}
v_resetjp_329_:
{
lean_object* v___x_333_; 
if (v_isShared_331_ == 0)
{
v___x_333_ = v___x_330_;
goto v_reusejp_332_;
}
else
{
lean_object* v_reuseFailAlloc_334_; 
v_reuseFailAlloc_334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_334_, 0, v_a_328_);
v___x_333_ = v_reuseFailAlloc_334_;
goto v_reusejp_332_;
}
v_reusejp_332_:
{
return v___x_333_;
}
}
}
}
else
{
lean_object* v_val_336_; lean_object* v_fst_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; 
v_val_336_ = lean_ctor_get(v___x_320_, 0);
lean_inc(v_val_336_);
lean_dec_ref_known(v___x_320_, 1);
v_fst_337_ = lean_ctor_get(v_val_336_, 0);
lean_inc(v_fst_337_);
lean_dec(v_val_336_);
v___x_338_ = l_Lean_Expr_getAppFn(v_fst_337_);
v___x_339_ = l_Lean_Expr_getAppFn(v_snd_305_);
v___x_340_ = l_Lean_Meta_Grind_hasSameType(v___x_338_, v___x_339_, v___y_277_, v___y_278_, v___y_279_, v___y_280_);
if (lean_obj_tag(v___x_340_) == 0)
{
lean_object* v_a_341_; uint8_t v___x_342_; 
v_a_341_ = lean_ctor_get(v___x_340_, 0);
lean_inc(v_a_341_);
lean_dec_ref_known(v___x_340_, 1);
v___x_342_ = lean_unbox(v_a_341_);
lean_dec(v_a_341_);
if (v___x_342_ == 0)
{
lean_object* v___x_343_; lean_object* v___x_344_; 
lean_dec(v_fst_337_);
v___x_343_ = lean_box(0);
lean_inc_ref(v_curr_268_);
v___x_344_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0(v_root_269_, v_snd_305_, v_curr_268_, v___x_312_, v___x_343_, v___y_271_, v___y_272_, v___y_273_, v___y_274_, v___y_275_, v___y_276_, v___y_277_, v___y_278_, v___y_279_, v___y_280_);
v___y_283_ = v___x_344_;
goto v___jp_282_;
}
else
{
lean_object* v___x_345_; 
lean_inc(v_snd_305_);
v___x_345_ = l_Lean_Meta_Grind_getCongrRoot___redArg(v_snd_305_, v___y_271_, v___y_277_, v___y_278_, v___y_279_, v___y_280_);
if (lean_obj_tag(v___x_345_) == 0)
{
lean_object* v_a_346_; uint8_t v___x_347_; 
v_a_346_ = lean_ctor_get(v___x_345_, 0);
lean_inc(v_a_346_);
lean_dec_ref_known(v___x_345_, 1);
v___x_347_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_fst_337_, v_a_346_);
lean_dec(v_a_346_);
lean_dec(v_fst_337_);
if (v___x_347_ == 0)
{
lean_object* v___x_348_; lean_object* v___x_349_; 
lean_dec(v___x_312_);
lean_dec(v_snd_305_);
v___x_348_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___closed__5, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___closed__5_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___closed__5);
v___x_349_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__0(v___x_348_, v___y_271_, v___y_272_, v___y_273_, v___y_274_, v___y_275_, v___y_276_, v___y_277_, v___y_278_, v___y_279_, v___y_280_);
v___y_283_ = v___x_349_;
goto v___jp_282_;
}
else
{
lean_object* v___x_350_; lean_object* v___x_351_; 
v___x_350_ = lean_box(0);
lean_inc_ref(v_curr_268_);
v___x_351_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0(v_root_269_, v_snd_305_, v_curr_268_, v___x_312_, v___x_350_, v___y_271_, v___y_272_, v___y_273_, v___y_274_, v___y_275_, v___y_276_, v___y_277_, v___y_278_, v___y_279_, v___y_280_);
v___y_283_ = v___x_351_;
goto v___jp_282_;
}
}
else
{
lean_object* v_a_352_; lean_object* v___x_354_; uint8_t v_isShared_355_; uint8_t v_isSharedCheck_359_; 
lean_dec(v_fst_337_);
lean_dec(v___x_312_);
lean_dec(v_snd_305_);
lean_dec_ref(v_curr_268_);
v_a_352_ = lean_ctor_get(v___x_345_, 0);
v_isSharedCheck_359_ = !lean_is_exclusive(v___x_345_);
if (v_isSharedCheck_359_ == 0)
{
v___x_354_ = v___x_345_;
v_isShared_355_ = v_isSharedCheck_359_;
goto v_resetjp_353_;
}
else
{
lean_inc(v_a_352_);
lean_dec(v___x_345_);
v___x_354_ = lean_box(0);
v_isShared_355_ = v_isSharedCheck_359_;
goto v_resetjp_353_;
}
v_resetjp_353_:
{
lean_object* v___x_357_; 
if (v_isShared_355_ == 0)
{
v___x_357_ = v___x_354_;
goto v_reusejp_356_;
}
else
{
lean_object* v_reuseFailAlloc_358_; 
v_reuseFailAlloc_358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_358_, 0, v_a_352_);
v___x_357_ = v_reuseFailAlloc_358_;
goto v_reusejp_356_;
}
v_reusejp_356_:
{
return v___x_357_;
}
}
}
}
}
else
{
lean_object* v_a_360_; lean_object* v___x_362_; uint8_t v_isShared_363_; uint8_t v_isSharedCheck_367_; 
lean_dec(v_fst_337_);
lean_dec(v___x_312_);
lean_dec(v_snd_305_);
lean_dec_ref(v_curr_268_);
v_a_360_ = lean_ctor_get(v___x_340_, 0);
v_isSharedCheck_367_ = !lean_is_exclusive(v___x_340_);
if (v_isSharedCheck_367_ == 0)
{
v___x_362_ = v___x_340_;
v_isShared_363_ = v_isSharedCheck_367_;
goto v_resetjp_361_;
}
else
{
lean_inc(v_a_360_);
lean_dec(v___x_340_);
v___x_362_ = lean_box(0);
v_isShared_363_ = v_isSharedCheck_367_;
goto v_resetjp_361_;
}
v_resetjp_361_:
{
lean_object* v___x_365_; 
if (v_isShared_363_ == 0)
{
v___x_365_ = v___x_362_;
goto v_reusejp_364_;
}
else
{
lean_object* v_reuseFailAlloc_366_; 
v_reuseFailAlloc_366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_366_, 0, v_a_360_);
v___x_365_ = v_reuseFailAlloc_366_;
goto v_reusejp_364_;
}
v_reusejp_364_:
{
return v___x_365_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_368_; lean_object* v___x_370_; uint8_t v_isShared_371_; uint8_t v_isSharedCheck_375_; 
lean_dec(v_snd_305_);
lean_dec(v_fst_304_);
lean_dec_ref(v_curr_268_);
v_a_368_ = lean_ctor_get(v___x_306_, 0);
v_isSharedCheck_375_ = !lean_is_exclusive(v___x_306_);
if (v_isSharedCheck_375_ == 0)
{
v___x_370_ = v___x_306_;
v_isShared_371_ = v_isSharedCheck_375_;
goto v_resetjp_369_;
}
else
{
lean_inc(v_a_368_);
lean_dec(v___x_306_);
v___x_370_ = lean_box(0);
v_isShared_371_ = v_isSharedCheck_375_;
goto v_resetjp_369_;
}
v_resetjp_369_:
{
lean_object* v___x_373_; 
if (v_isShared_371_ == 0)
{
v___x_373_ = v___x_370_;
goto v_reusejp_372_;
}
else
{
lean_object* v_reuseFailAlloc_374_; 
v_reuseFailAlloc_374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_374_, 0, v_a_368_);
v___x_373_ = v_reuseFailAlloc_374_;
goto v_reusejp_372_;
}
v_reusejp_372_:
{
return v___x_373_;
}
}
}
v___jp_282_:
{
if (lean_obj_tag(v___y_283_) == 0)
{
lean_object* v_a_284_; lean_object* v___x_286_; uint8_t v_isShared_287_; uint8_t v_isSharedCheck_294_; 
v_a_284_ = lean_ctor_get(v___y_283_, 0);
v_isSharedCheck_294_ = !lean_is_exclusive(v___y_283_);
if (v_isSharedCheck_294_ == 0)
{
v___x_286_ = v___y_283_;
v_isShared_287_ = v_isSharedCheck_294_;
goto v_resetjp_285_;
}
else
{
lean_inc(v_a_284_);
lean_dec(v___y_283_);
v___x_286_ = lean_box(0);
v_isShared_287_ = v_isSharedCheck_294_;
goto v_resetjp_285_;
}
v_resetjp_285_:
{
if (lean_obj_tag(v_a_284_) == 0)
{
lean_object* v_a_288_; lean_object* v___x_290_; 
lean_dec_ref(v_curr_268_);
v_a_288_ = lean_ctor_get(v_a_284_, 0);
lean_inc(v_a_288_);
lean_dec_ref_known(v_a_284_, 1);
if (v_isShared_287_ == 0)
{
lean_ctor_set(v___x_286_, 0, v_a_288_);
v___x_290_ = v___x_286_;
goto v_reusejp_289_;
}
else
{
lean_object* v_reuseFailAlloc_291_; 
v_reuseFailAlloc_291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_291_, 0, v_a_288_);
v___x_290_ = v_reuseFailAlloc_291_;
goto v_reusejp_289_;
}
v_reusejp_289_:
{
return v___x_290_;
}
}
else
{
lean_object* v_a_292_; 
lean_del_object(v___x_286_);
v_a_292_ = lean_ctor_get(v_a_284_, 0);
lean_inc(v_a_292_);
lean_dec_ref_known(v_a_284_, 1);
v_a_270_ = v_a_292_;
goto _start;
}
}
}
else
{
lean_object* v_a_295_; lean_object* v___x_297_; uint8_t v_isShared_298_; uint8_t v_isSharedCheck_302_; 
lean_dec_ref(v_curr_268_);
v_a_295_ = lean_ctor_get(v___y_283_, 0);
v_isSharedCheck_302_ = !lean_is_exclusive(v___y_283_);
if (v_isSharedCheck_302_ == 0)
{
v___x_297_ = v___y_283_;
v_isShared_298_ = v_isSharedCheck_302_;
goto v_resetjp_296_;
}
else
{
lean_inc(v_a_295_);
lean_dec(v___y_283_);
v___x_297_ = lean_box(0);
v_isShared_298_ = v_isSharedCheck_302_;
goto v_resetjp_296_;
}
v_resetjp_296_:
{
lean_object* v___x_300_; 
if (v_isShared_298_ == 0)
{
v___x_300_ = v___x_297_;
goto v_reusejp_299_;
}
else
{
lean_object* v_reuseFailAlloc_301_; 
v_reuseFailAlloc_301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_301_, 0, v_a_295_);
v___x_300_ = v_reuseFailAlloc_301_;
goto v_reusejp_299_;
}
v_reusejp_299_:
{
return v___x_300_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___boxed(lean_object* v_curr_376_, lean_object* v_root_377_, lean_object* v_a_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_){
_start:
{
lean_object* v_res_390_; 
v_res_390_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg(v_curr_376_, v_root_377_, v_a_378_, v___y_379_, v___y_380_, v___y_381_, v___y_382_, v___y_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_);
lean_dec(v___y_388_);
lean_dec_ref(v___y_387_);
lean_dec(v___y_386_);
lean_dec_ref(v___y_385_);
lean_dec(v___y_384_);
lean_dec_ref(v___y_383_);
lean_dec(v___y_382_);
lean_dec_ref(v___y_381_);
lean_dec(v___y_380_);
lean_dec(v___y_379_);
lean_dec_ref(v_root_377_);
return v_res_390_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc___closed__1(void){
_start:
{
lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; 
v___x_392_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc___closed__0));
v___x_393_ = lean_unsigned_to_nat(2u);
v___x_394_ = lean_unsigned_to_nat(46u);
v___x_395_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__1));
v___x_396_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__0));
v___x_397_ = l_mkPanicMessageWithDecl(v___x_396_, v___x_395_, v___x_394_, v___x_393_, v___x_392_);
return v___x_397_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc(lean_object* v_root_398_, lean_object* v_a_399_, lean_object* v_a_400_, lean_object* v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_a_404_, lean_object* v_a_405_, lean_object* v_a_406_, lean_object* v_a_407_, lean_object* v_a_408_){
_start:
{
lean_object* v_self_410_; lean_object* v_size_411_; lean_object* v_size_412_; lean_object* v___x_413_; lean_object* v___x_414_; 
v_self_410_ = lean_ctor_get(v_root_398_, 0);
lean_inc_ref_n(v_self_410_, 2);
v_size_411_ = lean_ctor_get(v_root_398_, 6);
lean_inc(v_size_411_);
v_size_412_ = lean_unsigned_to_nat(0u);
v___x_413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_413_, 0, v_size_412_);
lean_ctor_set(v___x_413_, 1, v_self_410_);
v___x_414_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg(v_self_410_, v_root_398_, v___x_413_, v_a_399_, v_a_400_, v_a_401_, v_a_402_, v_a_403_, v_a_404_, v_a_405_, v_a_406_, v_a_407_, v_a_408_);
lean_dec_ref(v_root_398_);
if (lean_obj_tag(v___x_414_) == 0)
{
lean_object* v_a_415_; lean_object* v___x_417_; uint8_t v_isShared_418_; uint8_t v_isSharedCheck_427_; 
v_a_415_ = lean_ctor_get(v___x_414_, 0);
v_isSharedCheck_427_ = !lean_is_exclusive(v___x_414_);
if (v_isSharedCheck_427_ == 0)
{
v___x_417_ = v___x_414_;
v_isShared_418_ = v_isSharedCheck_427_;
goto v_resetjp_416_;
}
else
{
lean_inc(v_a_415_);
lean_dec(v___x_414_);
v___x_417_ = lean_box(0);
v_isShared_418_ = v_isSharedCheck_427_;
goto v_resetjp_416_;
}
v_resetjp_416_:
{
lean_object* v_fst_419_; uint8_t v___x_420_; 
v_fst_419_ = lean_ctor_get(v_a_415_, 0);
lean_inc(v_fst_419_);
lean_dec(v_a_415_);
v___x_420_ = lean_nat_dec_eq(v_size_411_, v_fst_419_);
lean_dec(v_fst_419_);
lean_dec(v_size_411_);
if (v___x_420_ == 0)
{
lean_object* v___x_421_; lean_object* v___x_422_; 
lean_del_object(v___x_417_);
v___x_421_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc___closed__1, &l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc___closed__1);
v___x_422_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__4(v___x_421_, v_a_399_, v_a_400_, v_a_401_, v_a_402_, v_a_403_, v_a_404_, v_a_405_, v_a_406_, v_a_407_, v_a_408_);
return v___x_422_;
}
else
{
lean_object* v___x_423_; lean_object* v___x_425_; 
v___x_423_ = lean_box(0);
if (v_isShared_418_ == 0)
{
lean_ctor_set(v___x_417_, 0, v___x_423_);
v___x_425_ = v___x_417_;
goto v_reusejp_424_;
}
else
{
lean_object* v_reuseFailAlloc_426_; 
v_reuseFailAlloc_426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_426_, 0, v___x_423_);
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
else
{
lean_object* v_a_428_; lean_object* v___x_430_; uint8_t v_isShared_431_; uint8_t v_isSharedCheck_435_; 
lean_dec(v_size_411_);
v_a_428_ = lean_ctor_get(v___x_414_, 0);
v_isSharedCheck_435_ = !lean_is_exclusive(v___x_414_);
if (v_isSharedCheck_435_ == 0)
{
v___x_430_ = v___x_414_;
v_isShared_431_ = v_isSharedCheck_435_;
goto v_resetjp_429_;
}
else
{
lean_inc(v_a_428_);
lean_dec(v___x_414_);
v___x_430_ = lean_box(0);
v_isShared_431_ = v_isSharedCheck_435_;
goto v_resetjp_429_;
}
v_resetjp_429_:
{
lean_object* v___x_433_; 
if (v_isShared_431_ == 0)
{
v___x_433_ = v___x_430_;
goto v_reusejp_432_;
}
else
{
lean_object* v_reuseFailAlloc_434_; 
v_reuseFailAlloc_434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_434_, 0, v_a_428_);
v___x_433_ = v_reuseFailAlloc_434_;
goto v_reusejp_432_;
}
v_reusejp_432_:
{
return v___x_433_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc___boxed(lean_object* v_root_436_, lean_object* v_a_437_, lean_object* v_a_438_, lean_object* v_a_439_, lean_object* v_a_440_, lean_object* v_a_441_, lean_object* v_a_442_, lean_object* v_a_443_, lean_object* v_a_444_, lean_object* v_a_445_, lean_object* v_a_446_, lean_object* v_a_447_){
_start:
{
lean_object* v_res_448_; 
v_res_448_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc(v_root_436_, v_a_437_, v_a_438_, v_a_439_, v_a_440_, v_a_441_, v_a_442_, v_a_443_, v_a_444_, v_a_445_, v_a_446_);
lean_dec(v_a_446_);
lean_dec_ref(v_a_445_);
lean_dec(v_a_444_);
lean_dec_ref(v_a_443_);
lean_dec(v_a_442_);
lean_dec_ref(v_a_441_);
lean_dec(v_a_440_);
lean_dec_ref(v_a_439_);
lean_dec(v_a_438_);
lean_dec(v_a_437_);
return v_res_448_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__1(lean_object* v_inst_449_, lean_object* v_a_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_){
_start:
{
lean_object* v___x_462_; 
v___x_462_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__1___redArg(v_a_450_, v___y_451_);
return v___x_462_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__1___boxed(lean_object* v_inst_463_, lean_object* v_a_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_){
_start:
{
lean_object* v_res_476_; 
v_res_476_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__1(v_inst_463_, v_a_464_, v___y_465_, v___y_466_, v___y_467_, v___y_468_, v___y_469_, v___y_470_, v___y_471_, v___y_472_, v___y_473_, v___y_474_);
lean_dec(v___y_474_);
lean_dec_ref(v___y_473_);
lean_dec(v___y_472_);
lean_dec_ref(v___y_471_);
lean_dec(v___y_470_);
lean_dec_ref(v___y_469_);
lean_dec(v___y_468_);
lean_dec_ref(v___y_467_);
lean_dec(v___y_466_);
lean_dec(v___y_465_);
return v_res_476_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2(lean_object* v___x_477_, lean_object* v_00_u03b2_478_, lean_object* v_x_479_, lean_object* v_x_480_){
_start:
{
lean_object* v___x_481_; 
v___x_481_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2___redArg(v___x_477_, v_x_479_, v_x_480_);
return v___x_481_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2___boxed(lean_object* v___x_482_, lean_object* v_00_u03b2_483_, lean_object* v_x_484_, lean_object* v_x_485_){
_start:
{
lean_object* v_res_486_; 
v_res_486_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2(v___x_482_, v_00_u03b2_483_, v_x_484_, v_x_485_);
lean_dec_ref(v_x_484_);
lean_dec_ref(v___x_482_);
return v_res_486_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3(lean_object* v_curr_487_, lean_object* v_root_488_, lean_object* v_inst_489_, lean_object* v_a_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_){
_start:
{
lean_object* v___x_502_; 
v___x_502_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg(v_curr_487_, v_root_488_, v_a_490_, v___y_491_, v___y_492_, v___y_493_, v___y_494_, v___y_495_, v___y_496_, v___y_497_, v___y_498_, v___y_499_, v___y_500_);
return v___x_502_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___boxed(lean_object* v_curr_503_, lean_object* v_root_504_, lean_object* v_inst_505_, lean_object* v_a_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_){
_start:
{
lean_object* v_res_518_; 
v_res_518_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3(v_curr_503_, v_root_504_, v_inst_505_, v_a_506_, v___y_507_, v___y_508_, v___y_509_, v___y_510_, v___y_511_, v___y_512_, v___y_513_, v___y_514_, v___y_515_, v___y_516_);
lean_dec(v___y_516_);
lean_dec_ref(v___y_515_);
lean_dec(v___y_514_);
lean_dec_ref(v___y_513_);
lean_dec(v___y_512_);
lean_dec_ref(v___y_511_);
lean_dec(v___y_510_);
lean_dec_ref(v___y_509_);
lean_dec(v___y_508_);
lean_dec(v___y_507_);
lean_dec_ref(v_root_504_);
return v_res_518_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2(lean_object* v___x_519_, lean_object* v_00_u03b2_520_, lean_object* v_x_521_, size_t v_x_522_, lean_object* v_x_523_){
_start:
{
lean_object* v___x_524_; 
lean_inc_ref(v_x_521_);
v___x_524_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2___redArg(v___x_519_, v_x_521_, v_x_522_, v_x_523_);
return v___x_524_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2___boxed(lean_object* v___x_525_, lean_object* v_00_u03b2_526_, lean_object* v_x_527_, lean_object* v_x_528_, lean_object* v_x_529_){
_start:
{
size_t v_x_33772__boxed_530_; lean_object* v_res_531_; 
v_x_33772__boxed_530_ = lean_unbox_usize(v_x_528_);
lean_dec(v_x_528_);
v_res_531_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2(v___x_525_, v_00_u03b2_526_, v_x_527_, v_x_33772__boxed_530_, v_x_529_);
lean_dec_ref(v_x_527_);
lean_dec_ref(v___x_525_);
return v_res_531_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2_spec__4(lean_object* v___x_532_, lean_object* v_00_u03b2_533_, lean_object* v_keys_534_, lean_object* v_vals_535_, lean_object* v_heq_536_, lean_object* v_i_537_, lean_object* v_k_538_){
_start:
{
lean_object* v___x_539_; 
v___x_539_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2_spec__4___redArg(v___x_532_, v_keys_534_, v_vals_535_, v_i_537_, v_k_538_);
return v___x_539_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2_spec__4___boxed(lean_object* v___x_540_, lean_object* v_00_u03b2_541_, lean_object* v_keys_542_, lean_object* v_vals_543_, lean_object* v_heq_544_, lean_object* v_i_545_, lean_object* v_k_546_){
_start:
{
lean_object* v_res_547_; 
v_res_547_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2_spec__4(v___x_540_, v_00_u03b2_541_, v_keys_542_, v_vals_543_, v_heq_544_, v_i_545_, v_k_546_);
lean_dec_ref(v_vals_543_);
lean_dec_ref(v_keys_542_);
lean_dec_ref(v___x_540_);
return v_res_547_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkChild___redArg(lean_object* v_e_548_, lean_object* v_child_549_, lean_object* v_a_550_){
_start:
{
lean_object* v___x_552_; lean_object* v___x_553_; 
v___x_552_ = lean_st_ref_get(v_a_550_);
v___x_553_ = l_Lean_Meta_Grind_Goal_getRoot_x3f(v___x_552_, v_child_549_);
lean_dec(v___x_552_);
if (lean_obj_tag(v___x_553_) == 1)
{
lean_object* v_val_554_; lean_object* v___x_556_; uint8_t v_isShared_557_; uint8_t v_isSharedCheck_563_; 
v_val_554_ = lean_ctor_get(v___x_553_, 0);
v_isSharedCheck_563_ = !lean_is_exclusive(v___x_553_);
if (v_isSharedCheck_563_ == 0)
{
v___x_556_ = v___x_553_;
v_isShared_557_ = v_isSharedCheck_563_;
goto v_resetjp_555_;
}
else
{
lean_inc(v_val_554_);
lean_dec(v___x_553_);
v___x_556_ = lean_box(0);
v_isShared_557_ = v_isSharedCheck_563_;
goto v_resetjp_555_;
}
v_resetjp_555_:
{
uint8_t v___x_558_; lean_object* v___x_559_; lean_object* v___x_561_; 
v___x_558_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_val_554_, v_e_548_);
lean_dec(v_val_554_);
v___x_559_ = lean_box(v___x_558_);
if (v_isShared_557_ == 0)
{
lean_ctor_set_tag(v___x_556_, 0);
lean_ctor_set(v___x_556_, 0, v___x_559_);
v___x_561_ = v___x_556_;
goto v_reusejp_560_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v___x_559_);
v___x_561_ = v_reuseFailAlloc_562_;
goto v_reusejp_560_;
}
v_reusejp_560_:
{
return v___x_561_;
}
}
}
else
{
uint8_t v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; 
lean_dec(v___x_553_);
v___x_564_ = 0;
v___x_565_ = lean_box(v___x_564_);
v___x_566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_566_, 0, v___x_565_);
return v___x_566_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkChild___redArg___boxed(lean_object* v_e_567_, lean_object* v_child_568_, lean_object* v_a_569_, lean_object* v_a_570_){
_start:
{
lean_object* v_res_571_; 
v_res_571_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkChild___redArg(v_e_567_, v_child_568_, v_a_569_);
lean_dec(v_a_569_);
lean_dec_ref(v_child_568_);
lean_dec_ref(v_e_567_);
return v_res_571_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkChild(lean_object* v_e_572_, lean_object* v_child_573_, lean_object* v_a_574_, lean_object* v_a_575_, lean_object* v_a_576_, lean_object* v_a_577_, lean_object* v_a_578_, lean_object* v_a_579_, lean_object* v_a_580_, lean_object* v_a_581_, lean_object* v_a_582_, lean_object* v_a_583_){
_start:
{
lean_object* v___x_585_; 
v___x_585_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkChild___redArg(v_e_572_, v_child_573_, v_a_574_);
return v___x_585_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkChild___boxed(lean_object* v_e_586_, lean_object* v_child_587_, lean_object* v_a_588_, lean_object* v_a_589_, lean_object* v_a_590_, lean_object* v_a_591_, lean_object* v_a_592_, lean_object* v_a_593_, lean_object* v_a_594_, lean_object* v_a_595_, lean_object* v_a_596_, lean_object* v_a_597_, lean_object* v_a_598_){
_start:
{
lean_object* v_res_599_; 
v_res_599_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkChild(v_e_586_, v_child_587_, v_a_588_, v_a_589_, v_a_590_, v_a_591_, v_a_592_, v_a_593_, v_a_594_, v_a_595_, v_a_596_, v_a_597_);
lean_dec(v_a_597_);
lean_dec_ref(v_a_596_);
lean_dec(v_a_595_);
lean_dec_ref(v_a_594_);
lean_dec(v_a_593_);
lean_dec_ref(v_a_592_);
lean_dec(v_a_591_);
lean_dec_ref(v_a_590_);
lean_dec(v_a_589_);
lean_dec(v_a_588_);
lean_dec_ref(v_child_587_);
lean_dec_ref(v_e_586_);
return v_res_599_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___lam__0(lean_object* v___x_600_, lean_object* v_body_601_, lean_object* v_____r_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_){
_start:
{
lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; 
v___x_614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_614_, 0, v___x_600_);
lean_ctor_set(v___x_614_, 1, v_body_601_);
v___x_615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_615_, 0, v___x_614_);
v___x_616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_616_, 0, v___x_615_);
return v___x_616_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___lam__0___boxed(lean_object* v___x_617_, lean_object* v_body_618_, lean_object* v_____r_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_){
_start:
{
lean_object* v_res_631_; 
v_res_631_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___lam__0(v___x_617_, v_body_618_, v_____r_619_, v___y_620_, v___y_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_);
lean_dec(v___y_629_);
lean_dec_ref(v___y_628_);
lean_dec(v___y_627_);
lean_dec_ref(v___y_626_);
lean_dec(v___y_625_);
lean_dec_ref(v___y_624_);
lean_dec(v___y_623_);
lean_dec_ref(v___y_622_);
lean_dec(v___y_621_);
lean_dec(v___y_620_);
return v_res_631_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___lam__1(lean_object* v___f_632_, lean_object* v_x_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_){
_start:
{
lean_object* v___x_645_; lean_object* v___x_646_; 
v___x_645_ = lean_box(0);
lean_inc(v___y_643_);
lean_inc_ref(v___y_642_);
lean_inc(v___y_641_);
lean_inc_ref(v___y_640_);
lean_inc(v___y_639_);
lean_inc_ref(v___y_638_);
lean_inc(v___y_637_);
lean_inc_ref(v___y_636_);
lean_inc(v___y_635_);
lean_inc(v___y_634_);
v___x_646_ = lean_apply_12(v___f_632_, v___x_645_, v___y_634_, v___y_635_, v___y_636_, v___y_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_, v___y_642_, v___y_643_, lean_box(0));
return v___x_646_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___lam__1___boxed(lean_object* v___f_647_, lean_object* v_x_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_){
_start:
{
lean_object* v_res_660_; 
v_res_660_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___lam__1(v___f_647_, v_x_648_, v___y_649_, v___y_650_, v___y_651_, v___y_652_, v___y_653_, v___y_654_, v___y_655_, v___y_656_, v___y_657_, v___y_658_);
lean_dec(v___y_658_);
lean_dec_ref(v___y_657_);
lean_dec(v___y_656_);
lean_dec_ref(v___y_655_);
lean_dec(v___y_654_);
lean_dec_ref(v___y_653_);
lean_dec(v___y_652_);
lean_dec_ref(v___y_651_);
lean_dec(v___y_650_);
lean_dec(v___y_649_);
return v_res_660_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg(lean_object* v_e_670_, lean_object* v_a_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_){
_start:
{
lean_object* v___y_684_; lean_object* v_snd_704_; lean_object* v___x_706_; uint8_t v_isShared_707_; uint8_t v_isSharedCheck_808_; 
v_snd_704_ = lean_ctor_get(v_a_671_, 1);
v_isSharedCheck_808_ = !lean_is_exclusive(v_a_671_);
if (v_isSharedCheck_808_ == 0)
{
lean_object* v_unused_809_; 
v_unused_809_ = lean_ctor_get(v_a_671_, 0);
lean_dec(v_unused_809_);
v___x_706_ = v_a_671_;
v_isShared_707_ = v_isSharedCheck_808_;
goto v_resetjp_705_;
}
else
{
lean_inc(v_snd_704_);
lean_dec(v_a_671_);
v___x_706_ = lean_box(0);
v_isShared_707_ = v_isSharedCheck_808_;
goto v_resetjp_705_;
}
v___jp_683_:
{
if (lean_obj_tag(v___y_684_) == 0)
{
lean_object* v_a_685_; lean_object* v___x_687_; uint8_t v_isShared_688_; uint8_t v_isSharedCheck_695_; 
v_a_685_ = lean_ctor_get(v___y_684_, 0);
v_isSharedCheck_695_ = !lean_is_exclusive(v___y_684_);
if (v_isSharedCheck_695_ == 0)
{
v___x_687_ = v___y_684_;
v_isShared_688_ = v_isSharedCheck_695_;
goto v_resetjp_686_;
}
else
{
lean_inc(v_a_685_);
lean_dec(v___y_684_);
v___x_687_ = lean_box(0);
v_isShared_688_ = v_isSharedCheck_695_;
goto v_resetjp_686_;
}
v_resetjp_686_:
{
if (lean_obj_tag(v_a_685_) == 0)
{
lean_object* v_a_689_; lean_object* v___x_691_; 
v_a_689_ = lean_ctor_get(v_a_685_, 0);
lean_inc(v_a_689_);
lean_dec_ref_known(v_a_685_, 1);
if (v_isShared_688_ == 0)
{
lean_ctor_set(v___x_687_, 0, v_a_689_);
v___x_691_ = v___x_687_;
goto v_reusejp_690_;
}
else
{
lean_object* v_reuseFailAlloc_692_; 
v_reuseFailAlloc_692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_692_, 0, v_a_689_);
v___x_691_ = v_reuseFailAlloc_692_;
goto v_reusejp_690_;
}
v_reusejp_690_:
{
return v___x_691_;
}
}
else
{
lean_object* v_a_693_; 
lean_del_object(v___x_687_);
v_a_693_ = lean_ctor_get(v_a_685_, 0);
lean_inc(v_a_693_);
lean_dec_ref_known(v_a_685_, 1);
v_a_671_ = v_a_693_;
goto _start;
}
}
}
else
{
lean_object* v_a_696_; lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_703_; 
v_a_696_ = lean_ctor_get(v___y_684_, 0);
v_isSharedCheck_703_ = !lean_is_exclusive(v___y_684_);
if (v_isSharedCheck_703_ == 0)
{
v___x_698_ = v___y_684_;
v_isShared_699_ = v_isSharedCheck_703_;
goto v_resetjp_697_;
}
else
{
lean_inc(v_a_696_);
lean_dec(v___y_684_);
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
v_resetjp_705_:
{
if (lean_obj_tag(v_snd_704_) == 7)
{
lean_object* v_binderType_708_; lean_object* v_body_709_; lean_object* v___x_710_; 
v_binderType_708_ = lean_ctor_get(v_snd_704_, 1);
v_body_709_ = lean_ctor_get(v_snd_704_, 2);
lean_inc_ref(v_binderType_708_);
v___x_710_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_binderType_708_, v___y_679_);
if (lean_obj_tag(v___x_710_) == 0)
{
lean_object* v_a_711_; lean_object* v___x_712_; lean_object* v___f_713_; lean_object* v___x_714_; uint8_t v___x_715_; 
v_a_711_ = lean_ctor_get(v___x_710_, 0);
lean_inc(v_a_711_);
lean_dec_ref_known(v___x_710_, 1);
v___x_712_ = lean_box(0);
lean_inc_ref(v_body_709_);
v___f_713_ = lean_alloc_closure((void*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___lam__0___boxed), 14, 2);
lean_closure_set(v___f_713_, 0, v___x_712_);
lean_closure_set(v___f_713_, 1, v_body_709_);
v___x_714_ = l_Lean_Expr_cleanupAnnotations(v_a_711_);
v___x_715_ = l_Lean_Expr_isApp(v___x_714_);
if (v___x_715_ == 0)
{
lean_object* v___x_716_; lean_object* v___x_717_; 
lean_dec_ref(v___x_714_);
lean_dec_ref_known(v_snd_704_, 3);
lean_del_object(v___x_706_);
v___x_716_ = lean_box(0);
v___x_717_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___lam__1(v___f_713_, v___x_716_, v___y_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_);
v___y_684_ = v___x_717_;
goto v___jp_683_;
}
else
{
lean_object* v___x_718_; uint8_t v___x_719_; 
v___x_718_ = l_Lean_Expr_appFnCleanup___redArg(v___x_714_);
v___x_719_ = l_Lean_Expr_isApp(v___x_718_);
if (v___x_719_ == 0)
{
lean_object* v___x_720_; lean_object* v___x_721_; 
lean_dec_ref(v___x_718_);
lean_dec_ref_known(v_snd_704_, 3);
lean_del_object(v___x_706_);
v___x_720_ = lean_box(0);
v___x_721_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___lam__1(v___f_713_, v___x_720_, v___y_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_);
v___y_684_ = v___x_721_;
goto v___jp_683_;
}
else
{
lean_object* v_arg_722_; lean_object* v___x_723_; uint8_t v___x_724_; 
v_arg_722_ = lean_ctor_get(v___x_718_, 1);
lean_inc_ref(v_arg_722_);
v___x_723_ = l_Lean_Expr_appFnCleanup___redArg(v___x_718_);
v___x_724_ = l_Lean_Expr_isApp(v___x_723_);
if (v___x_724_ == 0)
{
lean_object* v___x_725_; lean_object* v___x_726_; 
lean_dec_ref(v___x_723_);
lean_dec_ref(v_arg_722_);
lean_dec_ref_known(v_snd_704_, 3);
lean_del_object(v___x_706_);
v___x_725_ = lean_box(0);
v___x_726_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___lam__1(v___f_713_, v___x_725_, v___y_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_);
v___y_684_ = v___x_726_;
goto v___jp_683_;
}
else
{
lean_object* v_arg_727_; lean_object* v___x_728_; lean_object* v___x_729_; uint8_t v___x_730_; 
v_arg_727_ = lean_ctor_get(v___x_723_, 1);
lean_inc_ref(v_arg_727_);
v___x_728_ = l_Lean_Expr_appFnCleanup___redArg(v___x_723_);
v___x_729_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___closed__1));
v___x_730_ = l_Lean_Expr_isConstOf(v___x_728_, v___x_729_);
if (v___x_730_ == 0)
{
uint8_t v___x_731_; 
lean_dec_ref(v_arg_722_);
v___x_731_ = l_Lean_Expr_isApp(v___x_728_);
if (v___x_731_ == 0)
{
lean_object* v___x_732_; lean_object* v___x_733_; 
lean_dec_ref(v___x_728_);
lean_dec_ref(v_arg_727_);
lean_dec_ref_known(v_snd_704_, 3);
lean_del_object(v___x_706_);
v___x_732_ = lean_box(0);
v___x_733_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___lam__1(v___f_713_, v___x_732_, v___y_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_);
v___y_684_ = v___x_733_;
goto v___jp_683_;
}
else
{
lean_object* v_arg_734_; lean_object* v___x_735_; lean_object* v___x_736_; uint8_t v___x_737_; lean_object* v___y_739_; 
v_arg_734_ = lean_ctor_get(v___x_728_, 1);
lean_inc_ref(v_arg_734_);
v___x_735_ = l_Lean_Expr_appFnCleanup___redArg(v___x_728_);
v___x_736_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___closed__3));
v___x_737_ = l_Lean_Expr_isConstOf(v___x_735_, v___x_736_);
lean_dec_ref(v___x_735_);
if (v___x_737_ == 0)
{
lean_object* v___x_764_; lean_object* v___x_765_; 
lean_dec_ref(v_arg_734_);
lean_dec_ref(v_arg_727_);
lean_dec_ref_known(v_snd_704_, 3);
lean_del_object(v___x_706_);
v___x_764_ = lean_box(0);
v___x_765_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___lam__1(v___f_713_, v___x_764_, v___y_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_);
v___y_684_ = v___x_765_;
goto v___jp_683_;
}
else
{
lean_object* v___x_766_; 
lean_dec_ref(v___f_713_);
v___x_766_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkChild___redArg(v_e_670_, v_arg_734_, v___y_672_);
lean_dec_ref(v_arg_734_);
if (lean_obj_tag(v___x_766_) == 0)
{
lean_object* v_a_767_; uint8_t v___x_768_; 
v_a_767_ = lean_ctor_get(v___x_766_, 0);
lean_inc(v_a_767_);
v___x_768_ = lean_unbox(v_a_767_);
lean_dec(v_a_767_);
if (v___x_768_ == 0)
{
lean_object* v___x_769_; 
lean_dec_ref_known(v___x_766_, 1);
v___x_769_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkChild___redArg(v_e_670_, v_arg_727_, v___y_672_);
lean_dec_ref(v_arg_727_);
v___y_739_ = v___x_769_;
goto v___jp_738_;
}
else
{
lean_dec_ref(v_arg_727_);
v___y_739_ = v___x_766_;
goto v___jp_738_;
}
}
else
{
lean_dec_ref(v_arg_727_);
v___y_739_ = v___x_766_;
goto v___jp_738_;
}
}
v___jp_738_:
{
if (lean_obj_tag(v___y_739_) == 0)
{
lean_object* v_a_740_; lean_object* v___x_742_; uint8_t v_isShared_743_; uint8_t v_isSharedCheck_755_; 
v_a_740_ = lean_ctor_get(v___y_739_, 0);
v_isSharedCheck_755_ = !lean_is_exclusive(v___y_739_);
if (v_isSharedCheck_755_ == 0)
{
v___x_742_ = v___y_739_;
v_isShared_743_ = v_isSharedCheck_755_;
goto v_resetjp_741_;
}
else
{
lean_inc(v_a_740_);
lean_dec(v___y_739_);
v___x_742_ = lean_box(0);
v_isShared_743_ = v_isSharedCheck_755_;
goto v_resetjp_741_;
}
v_resetjp_741_:
{
uint8_t v___x_744_; 
v___x_744_ = lean_unbox(v_a_740_);
lean_dec(v_a_740_);
if (v___x_744_ == 0)
{
lean_object* v___x_745_; lean_object* v___x_746_; 
lean_inc_ref(v_body_709_);
lean_del_object(v___x_742_);
lean_dec_ref_known(v_snd_704_, 3);
lean_del_object(v___x_706_);
v___x_745_ = lean_box(0);
v___x_746_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___lam__0(v___x_712_, v_body_709_, v___x_745_, v___y_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_);
v___y_684_ = v___x_746_;
goto v___jp_683_;
}
else
{
lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_750_; 
v___x_747_ = lean_box(v___x_737_);
v___x_748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_748_, 0, v___x_747_);
if (v_isShared_707_ == 0)
{
lean_ctor_set(v___x_706_, 0, v___x_748_);
v___x_750_ = v___x_706_;
goto v_reusejp_749_;
}
else
{
lean_object* v_reuseFailAlloc_754_; 
v_reuseFailAlloc_754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_754_, 0, v___x_748_);
lean_ctor_set(v_reuseFailAlloc_754_, 1, v_snd_704_);
v___x_750_ = v_reuseFailAlloc_754_;
goto v_reusejp_749_;
}
v_reusejp_749_:
{
lean_object* v___x_752_; 
if (v_isShared_743_ == 0)
{
lean_ctor_set(v___x_742_, 0, v___x_750_);
v___x_752_ = v___x_742_;
goto v_reusejp_751_;
}
else
{
lean_object* v_reuseFailAlloc_753_; 
v_reuseFailAlloc_753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_753_, 0, v___x_750_);
v___x_752_ = v_reuseFailAlloc_753_;
goto v_reusejp_751_;
}
v_reusejp_751_:
{
return v___x_752_;
}
}
}
}
}
else
{
lean_object* v_a_756_; lean_object* v___x_758_; uint8_t v_isShared_759_; uint8_t v_isSharedCheck_763_; 
lean_dec_ref_known(v_snd_704_, 3);
lean_del_object(v___x_706_);
v_a_756_ = lean_ctor_get(v___y_739_, 0);
v_isSharedCheck_763_ = !lean_is_exclusive(v___y_739_);
if (v_isSharedCheck_763_ == 0)
{
v___x_758_ = v___y_739_;
v_isShared_759_ = v_isSharedCheck_763_;
goto v_resetjp_757_;
}
else
{
lean_inc(v_a_756_);
lean_dec(v___y_739_);
v___x_758_ = lean_box(0);
v_isShared_759_ = v_isSharedCheck_763_;
goto v_resetjp_757_;
}
v_resetjp_757_:
{
lean_object* v___x_761_; 
if (v_isShared_759_ == 0)
{
v___x_761_ = v___x_758_;
goto v_reusejp_760_;
}
else
{
lean_object* v_reuseFailAlloc_762_; 
v_reuseFailAlloc_762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_762_, 0, v_a_756_);
v___x_761_ = v_reuseFailAlloc_762_;
goto v_reusejp_760_;
}
v_reusejp_760_:
{
return v___x_761_;
}
}
}
}
}
}
else
{
lean_object* v___x_770_; 
lean_dec_ref(v___x_728_);
lean_dec_ref(v_arg_727_);
lean_dec_ref(v___f_713_);
v___x_770_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkChild___redArg(v_e_670_, v_arg_722_, v___y_672_);
lean_dec_ref(v_arg_722_);
if (lean_obj_tag(v___x_770_) == 0)
{
lean_object* v_a_771_; lean_object* v___x_773_; uint8_t v_isShared_774_; uint8_t v_isSharedCheck_786_; 
v_a_771_ = lean_ctor_get(v___x_770_, 0);
v_isSharedCheck_786_ = !lean_is_exclusive(v___x_770_);
if (v_isSharedCheck_786_ == 0)
{
v___x_773_ = v___x_770_;
v_isShared_774_ = v_isSharedCheck_786_;
goto v_resetjp_772_;
}
else
{
lean_inc(v_a_771_);
lean_dec(v___x_770_);
v___x_773_ = lean_box(0);
v_isShared_774_ = v_isSharedCheck_786_;
goto v_resetjp_772_;
}
v_resetjp_772_:
{
uint8_t v___x_775_; 
v___x_775_ = lean_unbox(v_a_771_);
lean_dec(v_a_771_);
if (v___x_775_ == 0)
{
lean_object* v___x_776_; lean_object* v___x_777_; 
lean_inc_ref(v_body_709_);
lean_del_object(v___x_773_);
lean_dec_ref_known(v_snd_704_, 3);
lean_del_object(v___x_706_);
v___x_776_ = lean_box(0);
v___x_777_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___lam__0(v___x_712_, v_body_709_, v___x_776_, v___y_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_);
v___y_684_ = v___x_777_;
goto v___jp_683_;
}
else
{
lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_781_; 
v___x_778_ = lean_box(v___x_730_);
v___x_779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_779_, 0, v___x_778_);
if (v_isShared_707_ == 0)
{
lean_ctor_set(v___x_706_, 0, v___x_779_);
v___x_781_ = v___x_706_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_785_; 
v_reuseFailAlloc_785_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_785_, 0, v___x_779_);
lean_ctor_set(v_reuseFailAlloc_785_, 1, v_snd_704_);
v___x_781_ = v_reuseFailAlloc_785_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
lean_object* v___x_783_; 
if (v_isShared_774_ == 0)
{
lean_ctor_set(v___x_773_, 0, v___x_781_);
v___x_783_ = v___x_773_;
goto v_reusejp_782_;
}
else
{
lean_object* v_reuseFailAlloc_784_; 
v_reuseFailAlloc_784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_784_, 0, v___x_781_);
v___x_783_ = v_reuseFailAlloc_784_;
goto v_reusejp_782_;
}
v_reusejp_782_:
{
return v___x_783_;
}
}
}
}
}
else
{
lean_object* v_a_787_; lean_object* v___x_789_; uint8_t v_isShared_790_; uint8_t v_isSharedCheck_794_; 
lean_dec_ref_known(v_snd_704_, 3);
lean_del_object(v___x_706_);
v_a_787_ = lean_ctor_get(v___x_770_, 0);
v_isSharedCheck_794_ = !lean_is_exclusive(v___x_770_);
if (v_isSharedCheck_794_ == 0)
{
v___x_789_ = v___x_770_;
v_isShared_790_ = v_isSharedCheck_794_;
goto v_resetjp_788_;
}
else
{
lean_inc(v_a_787_);
lean_dec(v___x_770_);
v___x_789_ = lean_box(0);
v_isShared_790_ = v_isSharedCheck_794_;
goto v_resetjp_788_;
}
v_resetjp_788_:
{
lean_object* v___x_792_; 
if (v_isShared_790_ == 0)
{
v___x_792_ = v___x_789_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v_a_787_);
v___x_792_ = v_reuseFailAlloc_793_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
return v___x_792_;
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
lean_object* v_a_795_; lean_object* v___x_797_; uint8_t v_isShared_798_; uint8_t v_isSharedCheck_802_; 
lean_dec_ref_known(v_snd_704_, 3);
lean_del_object(v___x_706_);
v_a_795_ = lean_ctor_get(v___x_710_, 0);
v_isSharedCheck_802_ = !lean_is_exclusive(v___x_710_);
if (v_isSharedCheck_802_ == 0)
{
v___x_797_ = v___x_710_;
v_isShared_798_ = v_isSharedCheck_802_;
goto v_resetjp_796_;
}
else
{
lean_inc(v_a_795_);
lean_dec(v___x_710_);
v___x_797_ = lean_box(0);
v_isShared_798_ = v_isSharedCheck_802_;
goto v_resetjp_796_;
}
v_resetjp_796_:
{
lean_object* v___x_800_; 
if (v_isShared_798_ == 0)
{
v___x_800_ = v___x_797_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_801_; 
v_reuseFailAlloc_801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_801_, 0, v_a_795_);
v___x_800_ = v_reuseFailAlloc_801_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
return v___x_800_;
}
}
}
}
else
{
lean_object* v___x_803_; lean_object* v___x_805_; 
v___x_803_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___closed__4));
if (v_isShared_707_ == 0)
{
lean_ctor_set(v___x_706_, 0, v___x_803_);
v___x_805_ = v___x_706_;
goto v_reusejp_804_;
}
else
{
lean_object* v_reuseFailAlloc_807_; 
v_reuseFailAlloc_807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_807_, 0, v___x_803_);
lean_ctor_set(v_reuseFailAlloc_807_, 1, v_snd_704_);
v___x_805_ = v_reuseFailAlloc_807_;
goto v_reusejp_804_;
}
v_reusejp_804_:
{
lean_object* v___x_806_; 
v___x_806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_806_, 0, v___x_805_);
return v___x_806_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___boxed(lean_object* v_e_810_, lean_object* v_a_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_){
_start:
{
lean_object* v_res_823_; 
v_res_823_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg(v_e_810_, v_a_811_, v___y_812_, v___y_813_, v___y_814_, v___y_815_, v___y_816_, v___y_817_, v___y_818_, v___y_819_, v___y_820_, v___y_821_);
lean_dec(v___y_821_);
lean_dec_ref(v___y_820_);
lean_dec(v___y_819_);
lean_dec_ref(v___y_818_);
lean_dec(v___y_817_);
lean_dec_ref(v___y_816_);
lean_dec(v___y_815_);
lean_dec_ref(v___y_814_);
lean_dec(v___y_813_);
lean_dec(v___y_812_);
lean_dec_ref(v_e_810_);
return v_res_823_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent(lean_object* v_e_831_, lean_object* v_parent_832_, lean_object* v_a_833_, lean_object* v_a_834_, lean_object* v_a_835_, lean_object* v_a_836_, lean_object* v_a_837_, lean_object* v_a_838_, lean_object* v_a_839_, lean_object* v_a_840_, lean_object* v_a_841_, lean_object* v_a_842_){
_start:
{
lean_object* v___x_844_; 
v___x_844_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_parent_832_, v_a_840_);
if (lean_obj_tag(v___x_844_) == 0)
{
lean_object* v_a_845_; lean_object* v___x_847_; uint8_t v_isShared_848_; uint8_t v_isSharedCheck_887_; 
v_a_845_ = lean_ctor_get(v___x_844_, 0);
v_isSharedCheck_887_ = !lean_is_exclusive(v___x_844_);
if (v_isSharedCheck_887_ == 0)
{
v___x_847_ = v___x_844_;
v_isShared_848_ = v_isSharedCheck_887_;
goto v_resetjp_846_;
}
else
{
lean_inc(v_a_845_);
lean_dec(v___x_844_);
v___x_847_ = lean_box(0);
v_isShared_848_ = v_isSharedCheck_887_;
goto v_resetjp_846_;
}
v_resetjp_846_:
{
lean_object* v___x_855_; uint8_t v___x_856_; 
v___x_855_ = l_Lean_Expr_cleanupAnnotations(v_a_845_);
v___x_856_ = l_Lean_Expr_isApp(v___x_855_);
if (v___x_856_ == 0)
{
lean_dec_ref(v___x_855_);
goto v___jp_849_;
}
else
{
lean_object* v_arg_857_; lean_object* v___x_858_; lean_object* v___x_859_; uint8_t v___x_860_; 
v_arg_857_ = lean_ctor_get(v___x_855_, 1);
lean_inc_ref(v_arg_857_);
v___x_858_ = l_Lean_Expr_appFnCleanup___redArg(v___x_855_);
v___x_859_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent___closed__3));
v___x_860_ = l_Lean_Expr_isConstOf(v___x_858_, v___x_859_);
lean_dec_ref(v___x_858_);
if (v___x_860_ == 0)
{
lean_dec_ref(v_arg_857_);
goto v___jp_849_;
}
else
{
lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; 
lean_del_object(v___x_847_);
v___x_861_ = lean_box(0);
v___x_862_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_862_, 0, v___x_861_);
lean_ctor_set(v___x_862_, 1, v_arg_857_);
v___x_863_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg(v_e_831_, v___x_862_, v_a_833_, v_a_834_, v_a_835_, v_a_836_, v_a_837_, v_a_838_, v_a_839_, v_a_840_, v_a_841_, v_a_842_);
if (lean_obj_tag(v___x_863_) == 0)
{
lean_object* v_a_864_; lean_object* v___x_866_; uint8_t v_isShared_867_; uint8_t v_isSharedCheck_878_; 
v_a_864_ = lean_ctor_get(v___x_863_, 0);
v_isSharedCheck_878_ = !lean_is_exclusive(v___x_863_);
if (v_isSharedCheck_878_ == 0)
{
v___x_866_ = v___x_863_;
v_isShared_867_ = v_isSharedCheck_878_;
goto v_resetjp_865_;
}
else
{
lean_inc(v_a_864_);
lean_dec(v___x_863_);
v___x_866_ = lean_box(0);
v_isShared_867_ = v_isSharedCheck_878_;
goto v_resetjp_865_;
}
v_resetjp_865_:
{
lean_object* v_fst_868_; 
v_fst_868_ = lean_ctor_get(v_a_864_, 0);
lean_inc(v_fst_868_);
lean_dec(v_a_864_);
if (lean_obj_tag(v_fst_868_) == 0)
{
uint8_t v___x_869_; lean_object* v___x_870_; lean_object* v___x_872_; 
v___x_869_ = 0;
v___x_870_ = lean_box(v___x_869_);
if (v_isShared_867_ == 0)
{
lean_ctor_set(v___x_866_, 0, v___x_870_);
v___x_872_ = v___x_866_;
goto v_reusejp_871_;
}
else
{
lean_object* v_reuseFailAlloc_873_; 
v_reuseFailAlloc_873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_873_, 0, v___x_870_);
v___x_872_ = v_reuseFailAlloc_873_;
goto v_reusejp_871_;
}
v_reusejp_871_:
{
return v___x_872_;
}
}
else
{
lean_object* v_val_874_; lean_object* v___x_876_; 
v_val_874_ = lean_ctor_get(v_fst_868_, 0);
lean_inc(v_val_874_);
lean_dec_ref_known(v_fst_868_, 1);
if (v_isShared_867_ == 0)
{
lean_ctor_set(v___x_866_, 0, v_val_874_);
v___x_876_ = v___x_866_;
goto v_reusejp_875_;
}
else
{
lean_object* v_reuseFailAlloc_877_; 
v_reuseFailAlloc_877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_877_, 0, v_val_874_);
v___x_876_ = v_reuseFailAlloc_877_;
goto v_reusejp_875_;
}
v_reusejp_875_:
{
return v___x_876_;
}
}
}
}
else
{
lean_object* v_a_879_; lean_object* v___x_881_; uint8_t v_isShared_882_; uint8_t v_isSharedCheck_886_; 
v_a_879_ = lean_ctor_get(v___x_863_, 0);
v_isSharedCheck_886_ = !lean_is_exclusive(v___x_863_);
if (v_isSharedCheck_886_ == 0)
{
v___x_881_ = v___x_863_;
v_isShared_882_ = v_isSharedCheck_886_;
goto v_resetjp_880_;
}
else
{
lean_inc(v_a_879_);
lean_dec(v___x_863_);
v___x_881_ = lean_box(0);
v_isShared_882_ = v_isSharedCheck_886_;
goto v_resetjp_880_;
}
v_resetjp_880_:
{
lean_object* v___x_884_; 
if (v_isShared_882_ == 0)
{
v___x_884_ = v___x_881_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_885_; 
v_reuseFailAlloc_885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_885_, 0, v_a_879_);
v___x_884_ = v_reuseFailAlloc_885_;
goto v_reusejp_883_;
}
v_reusejp_883_:
{
return v___x_884_;
}
}
}
}
}
v___jp_849_:
{
uint8_t v___x_850_; lean_object* v___x_851_; lean_object* v___x_853_; 
v___x_850_ = 0;
v___x_851_ = lean_box(v___x_850_);
if (v_isShared_848_ == 0)
{
lean_ctor_set(v___x_847_, 0, v___x_851_);
v___x_853_ = v___x_847_;
goto v_reusejp_852_;
}
else
{
lean_object* v_reuseFailAlloc_854_; 
v_reuseFailAlloc_854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_854_, 0, v___x_851_);
v___x_853_ = v_reuseFailAlloc_854_;
goto v_reusejp_852_;
}
v_reusejp_852_:
{
return v___x_853_;
}
}
}
}
else
{
lean_object* v_a_888_; lean_object* v___x_890_; uint8_t v_isShared_891_; uint8_t v_isSharedCheck_895_; 
v_a_888_ = lean_ctor_get(v___x_844_, 0);
v_isSharedCheck_895_ = !lean_is_exclusive(v___x_844_);
if (v_isSharedCheck_895_ == 0)
{
v___x_890_ = v___x_844_;
v_isShared_891_ = v_isSharedCheck_895_;
goto v_resetjp_889_;
}
else
{
lean_inc(v_a_888_);
lean_dec(v___x_844_);
v___x_890_ = lean_box(0);
v_isShared_891_ = v_isSharedCheck_895_;
goto v_resetjp_889_;
}
v_resetjp_889_:
{
lean_object* v___x_893_; 
if (v_isShared_891_ == 0)
{
v___x_893_ = v___x_890_;
goto v_reusejp_892_;
}
else
{
lean_object* v_reuseFailAlloc_894_; 
v_reuseFailAlloc_894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_894_, 0, v_a_888_);
v___x_893_ = v_reuseFailAlloc_894_;
goto v_reusejp_892_;
}
v_reusejp_892_:
{
return v___x_893_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent___boxed(lean_object* v_e_896_, lean_object* v_parent_897_, lean_object* v_a_898_, lean_object* v_a_899_, lean_object* v_a_900_, lean_object* v_a_901_, lean_object* v_a_902_, lean_object* v_a_903_, lean_object* v_a_904_, lean_object* v_a_905_, lean_object* v_a_906_, lean_object* v_a_907_, lean_object* v_a_908_){
_start:
{
lean_object* v_res_909_; 
v_res_909_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent(v_e_896_, v_parent_897_, v_a_898_, v_a_899_, v_a_900_, v_a_901_, v_a_902_, v_a_903_, v_a_904_, v_a_905_, v_a_906_, v_a_907_);
lean_dec(v_a_907_);
lean_dec_ref(v_a_906_);
lean_dec(v_a_905_);
lean_dec_ref(v_a_904_);
lean_dec(v_a_903_);
lean_dec_ref(v_a_902_);
lean_dec(v_a_901_);
lean_dec_ref(v_a_900_);
lean_dec(v_a_899_);
lean_dec(v_a_898_);
lean_dec_ref(v_e_896_);
return v_res_909_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0(lean_object* v_e_910_, lean_object* v_inst_911_, lean_object* v_a_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_){
_start:
{
lean_object* v___x_924_; 
v___x_924_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg(v_e_910_, v_a_912_, v___y_913_, v___y_914_, v___y_915_, v___y_916_, v___y_917_, v___y_918_, v___y_919_, v___y_920_, v___y_921_, v___y_922_);
return v___x_924_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___boxed(lean_object* v_e_925_, lean_object* v_inst_926_, lean_object* v_a_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_){
_start:
{
lean_object* v_res_939_; 
v_res_939_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0(v_e_925_, v_inst_926_, v_a_927_, v___y_928_, v___y_929_, v___y_930_, v___y_931_, v___y_932_, v___y_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_);
lean_dec(v___y_937_);
lean_dec_ref(v___y_936_);
lean_dec(v___y_935_);
lean_dec_ref(v___y_934_);
lean_dec(v___y_933_);
lean_dec_ref(v___y_932_);
lean_dec(v___y_931_);
lean_dec_ref(v___y_930_);
lean_dec(v___y_929_);
lean_dec(v___y_928_);
lean_dec_ref(v_e_925_);
return v_res_939_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__0___closed__0(void){
_start:
{
lean_object* v___x_940_; 
v___x_940_ = l_Lean_Meta_Grind_instInhabitedGoalM(lean_box(0));
return v___x_940_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__0(lean_object* v_msg_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_){
_start:
{
lean_object* v___x_953_; lean_object* v___x_60107__overap_954_; lean_object* v___x_955_; 
v___x_953_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__0___closed__0, &l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__0___closed__0);
v___x_60107__overap_954_ = lean_panic_fn_borrowed(v___x_953_, v_msg_941_);
lean_inc(v___y_951_);
lean_inc_ref(v___y_950_);
lean_inc(v___y_949_);
lean_inc_ref(v___y_948_);
lean_inc(v___y_947_);
lean_inc_ref(v___y_946_);
lean_inc(v___y_945_);
lean_inc_ref(v___y_944_);
lean_inc(v___y_943_);
lean_inc(v___y_942_);
v___x_955_ = lean_apply_11(v___x_60107__overap_954_, v___y_942_, v___y_943_, v___y_944_, v___y_945_, v___y_946_, v___y_947_, v___y_948_, v___y_949_, v___y_950_, v___y_951_, lean_box(0));
return v___x_955_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__0___boxed(lean_object* v_msg_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_){
_start:
{
lean_object* v_res_968_; 
v_res_968_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__0(v_msg_956_, v___y_957_, v___y_958_, v___y_959_, v___y_960_, v___y_961_, v___y_962_, v___y_963_, v___y_964_, v___y_965_, v___y_966_);
lean_dec(v___y_966_);
lean_dec_ref(v___y_965_);
lean_dec(v___y_964_);
lean_dec_ref(v___y_963_);
lean_dec(v___y_962_);
lean_dec_ref(v___y_961_);
lean_dec(v___y_960_);
lean_dec_ref(v___y_959_);
lean_dec(v___y_958_);
lean_dec(v___y_957_);
return v_res_968_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__1_spec__1(lean_object* v_msgData_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_){
_start:
{
lean_object* v___x_975_; lean_object* v_env_976_; lean_object* v___x_977_; lean_object* v_mctx_978_; lean_object* v_lctx_979_; lean_object* v_options_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; 
v___x_975_ = lean_st_ref_get(v___y_973_);
v_env_976_ = lean_ctor_get(v___x_975_, 0);
lean_inc_ref(v_env_976_);
lean_dec(v___x_975_);
v___x_977_ = lean_st_ref_get(v___y_971_);
v_mctx_978_ = lean_ctor_get(v___x_977_, 0);
lean_inc_ref(v_mctx_978_);
lean_dec(v___x_977_);
v_lctx_979_ = lean_ctor_get(v___y_970_, 2);
v_options_980_ = lean_ctor_get(v___y_972_, 2);
lean_inc_ref(v_options_980_);
lean_inc_ref(v_lctx_979_);
v___x_981_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_981_, 0, v_env_976_);
lean_ctor_set(v___x_981_, 1, v_mctx_978_);
lean_ctor_set(v___x_981_, 2, v_lctx_979_);
lean_ctor_set(v___x_981_, 3, v_options_980_);
v___x_982_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_982_, 0, v___x_981_);
lean_ctor_set(v___x_982_, 1, v_msgData_969_);
v___x_983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_983_, 0, v___x_982_);
return v___x_983_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__1_spec__1___boxed(lean_object* v_msgData_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_){
_start:
{
lean_object* v_res_990_; 
v_res_990_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__1_spec__1(v_msgData_984_, v___y_985_, v___y_986_, v___y_987_, v___y_988_);
lean_dec(v___y_988_);
lean_dec_ref(v___y_987_);
lean_dec(v___y_986_);
lean_dec_ref(v___y_985_);
return v_res_990_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__1___redArg(lean_object* v_msg_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_){
_start:
{
lean_object* v_ref_997_; lean_object* v___x_998_; lean_object* v_a_999_; lean_object* v___x_1001_; uint8_t v_isShared_1002_; uint8_t v_isSharedCheck_1007_; 
v_ref_997_ = lean_ctor_get(v___y_994_, 5);
v___x_998_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__1_spec__1(v_msg_991_, v___y_992_, v___y_993_, v___y_994_, v___y_995_);
v_a_999_ = lean_ctor_get(v___x_998_, 0);
v_isSharedCheck_1007_ = !lean_is_exclusive(v___x_998_);
if (v_isSharedCheck_1007_ == 0)
{
v___x_1001_ = v___x_998_;
v_isShared_1002_ = v_isSharedCheck_1007_;
goto v_resetjp_1000_;
}
else
{
lean_inc(v_a_999_);
lean_dec(v___x_998_);
v___x_1001_ = lean_box(0);
v_isShared_1002_ = v_isSharedCheck_1007_;
goto v_resetjp_1000_;
}
v_resetjp_1000_:
{
lean_object* v___x_1003_; lean_object* v___x_1005_; 
lean_inc(v_ref_997_);
v___x_1003_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1003_, 0, v_ref_997_);
lean_ctor_set(v___x_1003_, 1, v_a_999_);
if (v_isShared_1002_ == 0)
{
lean_ctor_set_tag(v___x_1001_, 1);
lean_ctor_set(v___x_1001_, 0, v___x_1003_);
v___x_1005_ = v___x_1001_;
goto v_reusejp_1004_;
}
else
{
lean_object* v_reuseFailAlloc_1006_; 
v_reuseFailAlloc_1006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1006_, 0, v___x_1003_);
v___x_1005_ = v_reuseFailAlloc_1006_;
goto v_reusejp_1004_;
}
v_reusejp_1004_:
{
return v___x_1005_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__1___redArg___boxed(lean_object* v_msg_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_){
_start:
{
lean_object* v_res_1014_; 
v_res_1014_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__1___redArg(v_msg_1008_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_);
lean_dec(v___y_1012_);
lean_dec_ref(v___y_1011_);
lean_dec(v___y_1010_);
lean_dec_ref(v___y_1009_);
return v_res_1014_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__2___redArg(lean_object* v_e_1015_, uint8_t v_a_1016_, lean_object* v_as_1017_, size_t v_sz_1018_, size_t v_i_1019_, uint8_t v_b_1020_, lean_object* v___y_1021_){
_start:
{
uint8_t v___x_1023_; 
v___x_1023_ = lean_usize_dec_lt(v_i_1019_, v_sz_1018_);
if (v___x_1023_ == 0)
{
lean_object* v___x_1024_; lean_object* v___x_1025_; 
v___x_1024_ = lean_box(v_b_1020_);
v___x_1025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1025_, 0, v___x_1024_);
return v___x_1025_;
}
else
{
lean_object* v_a_1026_; lean_object* v___x_1027_; 
v_a_1026_ = lean_array_uget_borrowed(v_as_1017_, v_i_1019_);
v___x_1027_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkChild___redArg(v_e_1015_, v_a_1026_, v___y_1021_);
if (lean_obj_tag(v___x_1027_) == 0)
{
lean_object* v_a_1028_; lean_object* v___x_1030_; uint8_t v_isShared_1031_; uint8_t v_isSharedCheck_1040_; 
v_a_1028_ = lean_ctor_get(v___x_1027_, 0);
v_isSharedCheck_1040_ = !lean_is_exclusive(v___x_1027_);
if (v_isSharedCheck_1040_ == 0)
{
v___x_1030_ = v___x_1027_;
v_isShared_1031_ = v_isSharedCheck_1040_;
goto v_resetjp_1029_;
}
else
{
lean_inc(v_a_1028_);
lean_dec(v___x_1027_);
v___x_1030_ = lean_box(0);
v_isShared_1031_ = v_isSharedCheck_1040_;
goto v_resetjp_1029_;
}
v_resetjp_1029_:
{
uint8_t v___x_1032_; 
v___x_1032_ = lean_unbox(v_a_1028_);
lean_dec(v_a_1028_);
if (v___x_1032_ == 0)
{
size_t v___x_1033_; size_t v___x_1034_; 
lean_del_object(v___x_1030_);
v___x_1033_ = ((size_t)1ULL);
v___x_1034_ = lean_usize_add(v_i_1019_, v___x_1033_);
v_i_1019_ = v___x_1034_;
goto _start;
}
else
{
lean_object* v___x_1036_; lean_object* v___x_1038_; 
v___x_1036_ = lean_box(v_a_1016_);
if (v_isShared_1031_ == 0)
{
lean_ctor_set(v___x_1030_, 0, v___x_1036_);
v___x_1038_ = v___x_1030_;
goto v_reusejp_1037_;
}
else
{
lean_object* v_reuseFailAlloc_1039_; 
v_reuseFailAlloc_1039_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1039_, 0, v___x_1036_);
v___x_1038_ = v_reuseFailAlloc_1039_;
goto v_reusejp_1037_;
}
v_reusejp_1037_:
{
return v___x_1038_;
}
}
}
}
else
{
return v___x_1027_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__2___redArg___boxed(lean_object* v_e_1041_, lean_object* v_a_1042_, lean_object* v_as_1043_, lean_object* v_sz_1044_, lean_object* v_i_1045_, lean_object* v_b_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_){
_start:
{
uint8_t v_a_66539__boxed_1049_; size_t v_sz_boxed_1050_; size_t v_i_boxed_1051_; uint8_t v_b_boxed_1052_; lean_object* v_res_1053_; 
v_a_66539__boxed_1049_ = lean_unbox(v_a_1042_);
v_sz_boxed_1050_ = lean_unbox_usize(v_sz_1044_);
lean_dec(v_sz_1044_);
v_i_boxed_1051_ = lean_unbox_usize(v_i_1045_);
lean_dec(v_i_1045_);
v_b_boxed_1052_ = lean_unbox(v_b_1046_);
v_res_1053_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__2___redArg(v_e_1041_, v_a_66539__boxed_1049_, v_as_1043_, v_sz_boxed_1050_, v_i_boxed_1051_, v_b_boxed_1052_, v___y_1047_);
lean_dec(v___y_1047_);
lean_dec_ref(v_as_1043_);
lean_dec_ref(v_e_1041_);
return v_res_1053_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__2(void){
_start:
{
lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; 
v___x_1056_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__1));
v___x_1057_ = lean_unsigned_to_nat(8u);
v___x_1058_ = lean_unsigned_to_nat(75u);
v___x_1059_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__0));
v___x_1060_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__0));
v___x_1061_ = l_mkPanicMessageWithDecl(v___x_1060_, v___x_1059_, v___x_1058_, v___x_1057_, v___x_1056_);
return v___x_1061_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__4(void){
_start:
{
lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; 
v___x_1063_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__3));
v___x_1064_ = lean_unsigned_to_nat(10u);
v___x_1065_ = lean_unsigned_to_nat(93u);
v___x_1066_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__0));
v___x_1067_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__0));
v___x_1068_ = l_mkPanicMessageWithDecl(v___x_1067_, v___x_1066_, v___x_1065_, v___x_1064_, v___x_1063_);
return v___x_1068_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__6(void){
_start:
{
lean_object* v___x_1070_; lean_object* v___x_1071_; 
v___x_1070_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__5));
v___x_1071_ = l_Lean_stringToMessageData(v___x_1070_);
return v___x_1071_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__8(void){
_start:
{
lean_object* v___x_1073_; lean_object* v___x_1074_; 
v___x_1073_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__7));
v___x_1074_ = l_Lean_stringToMessageData(v___x_1073_);
return v___x_1074_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__9(void){
_start:
{
lean_object* v___x_1075_; lean_object* v_dummy_1076_; 
v___x_1075_ = lean_box(0);
v_dummy_1076_ = l_Lean_Expr_sort___override(v___x_1075_);
return v_dummy_1076_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg(lean_object* v_e_1077_, uint8_t v_a_1078_, lean_object* v_as_x27_1079_, lean_object* v_b_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_){
_start:
{
if (lean_obj_tag(v_as_x27_1079_) == 0)
{
lean_object* v___x_1092_; 
lean_dec_ref(v_e_1077_);
v___x_1092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1092_, 0, v_b_1080_);
return v___x_1092_;
}
else
{
lean_object* v_head_1093_; lean_object* v_tail_1094_; lean_object* v___y_1096_; lean_object* v___x_1116_; 
v_head_1093_ = lean_ctor_get(v_as_x27_1079_, 0);
v_tail_1094_ = lean_ctor_get(v_as_x27_1079_, 1);
lean_inc(v_head_1093_);
v___x_1116_ = l_Lean_Meta_Grind_useFunCC___redArg(v_head_1093_, v___y_1081_, v___y_1087_, v___y_1088_, v___y_1089_, v___y_1090_);
if (lean_obj_tag(v___x_1116_) == 0)
{
lean_object* v_a_1117_; lean_object* v___x_1118_; lean_object* v___y_1120_; lean_object* v___y_1121_; lean_object* v___y_1122_; lean_object* v___y_1123_; lean_object* v___y_1124_; lean_object* v___y_1125_; lean_object* v___y_1126_; lean_object* v___y_1127_; lean_object* v___y_1128_; lean_object* v___y_1129_; lean_object* v___y_1145_; lean_object* v___y_1146_; lean_object* v___y_1147_; lean_object* v___y_1148_; lean_object* v___y_1149_; lean_object* v___y_1150_; lean_object* v___y_1151_; lean_object* v___y_1152_; lean_object* v___y_1153_; lean_object* v___y_1154_; lean_object* v___y_1155_; uint8_t v_found_1163_; lean_object* v___y_1164_; lean_object* v___y_1165_; lean_object* v___y_1166_; lean_object* v___y_1167_; lean_object* v___y_1168_; lean_object* v___y_1169_; lean_object* v___y_1170_; lean_object* v___y_1171_; lean_object* v___y_1172_; lean_object* v___y_1173_; lean_object* v___y_1188_; uint8_t v_found_1189_; lean_object* v___y_1190_; lean_object* v___y_1191_; lean_object* v___y_1192_; lean_object* v___y_1193_; lean_object* v___y_1194_; lean_object* v___y_1195_; lean_object* v___y_1196_; lean_object* v___y_1197_; lean_object* v___y_1198_; lean_object* v___y_1199_; uint8_t v___y_1206_; uint8_t v___x_1254_; 
v_a_1117_ = lean_ctor_get(v___x_1116_, 0);
lean_inc(v_a_1117_);
lean_dec_ref_known(v___x_1116_, 1);
v___x_1118_ = lean_box(0);
v___x_1254_ = l_Lean_Expr_isApp(v_head_1093_);
if (v___x_1254_ == 0)
{
lean_dec(v_a_1117_);
v___y_1206_ = v___x_1254_;
goto v___jp_1205_;
}
else
{
uint8_t v___x_1255_; 
v___x_1255_ = lean_unbox(v_a_1117_);
lean_dec(v_a_1117_);
v___y_1206_ = v___x_1255_;
goto v___jp_1205_;
}
v___jp_1119_:
{
lean_object* v___x_1130_; 
lean_inc(v_head_1093_);
v___x_1130_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent(v_e_1077_, v_head_1093_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_, v___y_1127_, v___y_1128_, v___y_1129_);
if (lean_obj_tag(v___x_1130_) == 0)
{
lean_object* v_a_1131_; uint8_t v___x_1132_; 
v_a_1131_ = lean_ctor_get(v___x_1130_, 0);
lean_inc(v_a_1131_);
lean_dec_ref_known(v___x_1130_, 1);
v___x_1132_ = lean_unbox(v_a_1131_);
lean_dec(v_a_1131_);
if (v___x_1132_ == 0)
{
lean_object* v___x_1133_; lean_object* v___x_1134_; 
v___x_1133_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__2, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__2_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__2);
v___x_1134_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__0(v___x_1133_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_, v___y_1127_, v___y_1128_, v___y_1129_);
v___y_1096_ = v___x_1134_;
goto v___jp_1095_;
}
else
{
v_as_x27_1079_ = v_tail_1094_;
v_b_1080_ = v___x_1118_;
goto _start;
}
}
else
{
lean_object* v_a_1136_; lean_object* v___x_1138_; uint8_t v_isShared_1139_; uint8_t v_isSharedCheck_1143_; 
lean_dec_ref(v_e_1077_);
v_a_1136_ = lean_ctor_get(v___x_1130_, 0);
v_isSharedCheck_1143_ = !lean_is_exclusive(v___x_1130_);
if (v_isSharedCheck_1143_ == 0)
{
v___x_1138_ = v___x_1130_;
v_isShared_1139_ = v_isSharedCheck_1143_;
goto v_resetjp_1137_;
}
else
{
lean_inc(v_a_1136_);
lean_dec(v___x_1130_);
v___x_1138_ = lean_box(0);
v_isShared_1139_ = v_isSharedCheck_1143_;
goto v_resetjp_1137_;
}
v_resetjp_1137_:
{
lean_object* v___x_1141_; 
if (v_isShared_1139_ == 0)
{
v___x_1141_ = v___x_1138_;
goto v_reusejp_1140_;
}
else
{
lean_object* v_reuseFailAlloc_1142_; 
v_reuseFailAlloc_1142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1142_, 0, v_a_1136_);
v___x_1141_ = v_reuseFailAlloc_1142_;
goto v_reusejp_1140_;
}
v_reusejp_1140_:
{
return v___x_1141_;
}
}
}
}
v___jp_1144_:
{
lean_object* v___x_1156_; lean_object* v_a_1157_; uint8_t v___x_1158_; 
v___x_1156_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkChild___redArg(v_e_1077_, v___y_1145_, v___y_1146_);
lean_dec_ref(v___y_1145_);
v_a_1157_ = lean_ctor_get(v___x_1156_, 0);
lean_inc(v_a_1157_);
lean_dec_ref(v___x_1156_);
v___x_1158_ = lean_unbox(v_a_1157_);
lean_dec(v_a_1157_);
if (v___x_1158_ == 0)
{
lean_object* v___x_1159_; lean_object* v___x_1160_; 
v___x_1159_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__4, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__4);
v___x_1160_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__0(v___x_1159_, v___y_1146_, v___y_1147_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_, v___y_1152_, v___y_1153_, v___y_1154_, v___y_1155_);
v___y_1096_ = v___x_1160_;
goto v___jp_1095_;
}
else
{
v_as_x27_1079_ = v_tail_1094_;
v_b_1080_ = v___x_1118_;
goto _start;
}
}
v___jp_1162_:
{
if (v_found_1163_ == 0)
{
lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v_a_1176_; uint8_t v___x_1177_; 
v___x_1174_ = l_Lean_Expr_getAppFn(v_head_1093_);
v___x_1175_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkChild___redArg(v_e_1077_, v___x_1174_, v___y_1164_);
v_a_1176_ = lean_ctor_get(v___x_1175_, 0);
lean_inc(v_a_1176_);
lean_dec_ref(v___x_1175_);
v___x_1177_ = lean_unbox(v_a_1176_);
lean_dec(v_a_1176_);
if (v___x_1177_ == 0)
{
lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; 
lean_dec_ref(v___x_1174_);
v___x_1178_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__6, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__6_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__6);
v___x_1179_ = l_Lean_MessageData_ofExpr(v_e_1077_);
v___x_1180_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1180_, 0, v___x_1178_);
lean_ctor_set(v___x_1180_, 1, v___x_1179_);
v___x_1181_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__8, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__8_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__8);
v___x_1182_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1182_, 0, v___x_1180_);
lean_ctor_set(v___x_1182_, 1, v___x_1181_);
lean_inc(v_head_1093_);
v___x_1183_ = l_Lean_MessageData_ofExpr(v_head_1093_);
v___x_1184_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1184_, 0, v___x_1182_);
lean_ctor_set(v___x_1184_, 1, v___x_1183_);
v___x_1185_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__1___redArg(v___x_1184_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_);
return v___x_1185_;
}
else
{
v___y_1145_ = v___x_1174_;
v___y_1146_ = v___y_1164_;
v___y_1147_ = v___y_1165_;
v___y_1148_ = v___y_1166_;
v___y_1149_ = v___y_1167_;
v___y_1150_ = v___y_1168_;
v___y_1151_ = v___y_1169_;
v___y_1152_ = v___y_1170_;
v___y_1153_ = v___y_1171_;
v___y_1154_ = v___y_1172_;
v___y_1155_ = v___y_1173_;
goto v___jp_1144_;
}
}
else
{
v_as_x27_1079_ = v_tail_1094_;
v_b_1080_ = v___x_1118_;
goto _start;
}
}
v___jp_1187_:
{
uint8_t v___x_1200_; 
v___x_1200_ = l_Lean_Expr_hasLooseBVars(v___y_1188_);
if (v___x_1200_ == 0)
{
lean_object* v___x_1201_; lean_object* v_a_1202_; uint8_t v___x_1203_; 
v___x_1201_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkChild___redArg(v_e_1077_, v___y_1188_, v___y_1190_);
lean_dec_ref(v___y_1188_);
v_a_1202_ = lean_ctor_get(v___x_1201_, 0);
lean_inc(v_a_1202_);
lean_dec_ref(v___x_1201_);
v___x_1203_ = lean_unbox(v_a_1202_);
lean_dec(v_a_1202_);
if (v___x_1203_ == 0)
{
v_found_1163_ = v_found_1189_;
v___y_1164_ = v___y_1190_;
v___y_1165_ = v___y_1191_;
v___y_1166_ = v___y_1192_;
v___y_1167_ = v___y_1193_;
v___y_1168_ = v___y_1194_;
v___y_1169_ = v___y_1195_;
v___y_1170_ = v___y_1196_;
v___y_1171_ = v___y_1197_;
v___y_1172_ = v___y_1198_;
v___y_1173_ = v___y_1199_;
goto v___jp_1162_;
}
else
{
v_as_x27_1079_ = v_tail_1094_;
v_b_1080_ = v___x_1118_;
goto _start;
}
}
else
{
lean_dec_ref(v___y_1188_);
v_found_1163_ = v_found_1189_;
v___y_1164_ = v___y_1190_;
v___y_1165_ = v___y_1191_;
v___y_1166_ = v___y_1192_;
v___y_1167_ = v___y_1193_;
v___y_1168_ = v___y_1194_;
v___y_1169_ = v___y_1195_;
v___y_1170_ = v___y_1196_;
v___y_1171_ = v___y_1197_;
v___y_1172_ = v___y_1198_;
v___y_1173_ = v___y_1199_;
goto v___jp_1162_;
}
}
v___jp_1205_:
{
if (v___y_1206_ == 0)
{
uint8_t v___x_1207_; 
v___x_1207_ = l_Lean_Meta_Grind_isMatchCond(v_head_1093_);
if (v___x_1207_ == 0)
{
lean_object* v_dummy_1208_; lean_object* v_nargs_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; size_t v_sz_1214_; size_t v___x_1215_; lean_object* v___x_1216_; 
v_dummy_1208_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__9, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__9_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__9);
v_nargs_1209_ = l_Lean_Expr_getAppNumArgs(v_head_1093_);
lean_inc(v_nargs_1209_);
v___x_1210_ = lean_mk_array(v_nargs_1209_, v_dummy_1208_);
v___x_1211_ = lean_unsigned_to_nat(1u);
v___x_1212_ = lean_nat_sub(v_nargs_1209_, v___x_1211_);
lean_dec(v_nargs_1209_);
lean_inc(v_head_1093_);
v___x_1213_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_head_1093_, v___x_1210_, v___x_1212_);
v_sz_1214_ = lean_array_size(v___x_1213_);
v___x_1215_ = ((size_t)0ULL);
v___x_1216_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__2___redArg(v_e_1077_, v_a_1078_, v___x_1213_, v_sz_1214_, v___x_1215_, v___x_1207_, v___y_1081_);
lean_dec_ref(v___x_1213_);
if (lean_obj_tag(v___x_1216_) == 0)
{
if (lean_obj_tag(v_head_1093_) == 7)
{
lean_object* v_a_1217_; lean_object* v_binderType_1218_; lean_object* v_body_1219_; lean_object* v___x_1220_; lean_object* v_a_1221_; uint8_t v___x_1222_; 
v_a_1217_ = lean_ctor_get(v___x_1216_, 0);
lean_inc(v_a_1217_);
lean_dec_ref_known(v___x_1216_, 1);
v_binderType_1218_ = lean_ctor_get(v_head_1093_, 1);
v_body_1219_ = lean_ctor_get(v_head_1093_, 2);
v___x_1220_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkChild___redArg(v_e_1077_, v_binderType_1218_, v___y_1081_);
v_a_1221_ = lean_ctor_get(v___x_1220_, 0);
lean_inc(v_a_1221_);
lean_dec_ref(v___x_1220_);
v___x_1222_ = lean_unbox(v_a_1221_);
lean_dec(v_a_1221_);
if (v___x_1222_ == 0)
{
uint8_t v___x_1223_; 
v___x_1223_ = lean_unbox(v_a_1217_);
lean_dec(v_a_1217_);
lean_inc_ref(v_body_1219_);
v___y_1188_ = v_body_1219_;
v_found_1189_ = v___x_1223_;
v___y_1190_ = v___y_1081_;
v___y_1191_ = v___y_1082_;
v___y_1192_ = v___y_1083_;
v___y_1193_ = v___y_1084_;
v___y_1194_ = v___y_1085_;
v___y_1195_ = v___y_1086_;
v___y_1196_ = v___y_1087_;
v___y_1197_ = v___y_1088_;
v___y_1198_ = v___y_1089_;
v___y_1199_ = v___y_1090_;
goto v___jp_1187_;
}
else
{
lean_dec(v_a_1217_);
lean_inc_ref(v_body_1219_);
v___y_1188_ = v_body_1219_;
v_found_1189_ = v_a_1078_;
v___y_1190_ = v___y_1081_;
v___y_1191_ = v___y_1082_;
v___y_1192_ = v___y_1083_;
v___y_1193_ = v___y_1084_;
v___y_1194_ = v___y_1085_;
v___y_1195_ = v___y_1086_;
v___y_1196_ = v___y_1087_;
v___y_1197_ = v___y_1088_;
v___y_1198_ = v___y_1089_;
v___y_1199_ = v___y_1090_;
goto v___jp_1187_;
}
}
else
{
lean_object* v_a_1224_; uint8_t v___x_1225_; 
v_a_1224_ = lean_ctor_get(v___x_1216_, 0);
lean_inc(v_a_1224_);
lean_dec_ref_known(v___x_1216_, 1);
v___x_1225_ = lean_unbox(v_a_1224_);
lean_dec(v_a_1224_);
v_found_1163_ = v___x_1225_;
v___y_1164_ = v___y_1081_;
v___y_1165_ = v___y_1082_;
v___y_1166_ = v___y_1083_;
v___y_1167_ = v___y_1084_;
v___y_1168_ = v___y_1085_;
v___y_1169_ = v___y_1086_;
v___y_1170_ = v___y_1087_;
v___y_1171_ = v___y_1088_;
v___y_1172_ = v___y_1089_;
v___y_1173_ = v___y_1090_;
goto v___jp_1162_;
}
}
else
{
lean_object* v_a_1226_; lean_object* v___x_1228_; uint8_t v_isShared_1229_; uint8_t v_isSharedCheck_1233_; 
lean_dec_ref(v_e_1077_);
v_a_1226_ = lean_ctor_get(v___x_1216_, 0);
v_isSharedCheck_1233_ = !lean_is_exclusive(v___x_1216_);
if (v_isSharedCheck_1233_ == 0)
{
v___x_1228_ = v___x_1216_;
v_isShared_1229_ = v_isSharedCheck_1233_;
goto v_resetjp_1227_;
}
else
{
lean_inc(v_a_1226_);
lean_dec(v___x_1216_);
v___x_1228_ = lean_box(0);
v_isShared_1229_ = v_isSharedCheck_1233_;
goto v_resetjp_1227_;
}
v_resetjp_1227_:
{
lean_object* v___x_1231_; 
if (v_isShared_1229_ == 0)
{
v___x_1231_ = v___x_1228_;
goto v_reusejp_1230_;
}
else
{
lean_object* v_reuseFailAlloc_1232_; 
v_reuseFailAlloc_1232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1232_, 0, v_a_1226_);
v___x_1231_ = v_reuseFailAlloc_1232_;
goto v_reusejp_1230_;
}
v_reusejp_1230_:
{
return v___x_1231_;
}
}
}
}
else
{
lean_object* v___x_1234_; 
lean_inc(v_head_1093_);
v___x_1234_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent(v_e_1077_, v_head_1093_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_, v___y_1087_, v___y_1088_, v___y_1089_, v___y_1090_);
if (lean_obj_tag(v___x_1234_) == 0)
{
lean_object* v_a_1235_; uint8_t v___x_1236_; 
v_a_1235_ = lean_ctor_get(v___x_1234_, 0);
lean_inc(v_a_1235_);
lean_dec_ref_known(v___x_1234_, 1);
v___x_1236_ = lean_unbox(v_a_1235_);
lean_dec(v_a_1235_);
if (v___x_1236_ == 0)
{
lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; 
v___x_1237_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__6, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__6_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__6);
v___x_1238_ = l_Lean_MessageData_ofExpr(v_e_1077_);
v___x_1239_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1239_, 0, v___x_1237_);
lean_ctor_set(v___x_1239_, 1, v___x_1238_);
v___x_1240_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__8, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__8_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__8);
v___x_1241_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1241_, 0, v___x_1239_);
lean_ctor_set(v___x_1241_, 1, v___x_1240_);
lean_inc(v_head_1093_);
v___x_1242_ = l_Lean_MessageData_ofExpr(v_head_1093_);
v___x_1243_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1243_, 0, v___x_1241_);
lean_ctor_set(v___x_1243_, 1, v___x_1242_);
v___x_1244_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__1___redArg(v___x_1243_, v___y_1087_, v___y_1088_, v___y_1089_, v___y_1090_);
return v___x_1244_;
}
else
{
v___y_1120_ = v___y_1081_;
v___y_1121_ = v___y_1082_;
v___y_1122_ = v___y_1083_;
v___y_1123_ = v___y_1084_;
v___y_1124_ = v___y_1085_;
v___y_1125_ = v___y_1086_;
v___y_1126_ = v___y_1087_;
v___y_1127_ = v___y_1088_;
v___y_1128_ = v___y_1089_;
v___y_1129_ = v___y_1090_;
goto v___jp_1119_;
}
}
else
{
lean_object* v_a_1245_; lean_object* v___x_1247_; uint8_t v_isShared_1248_; uint8_t v_isSharedCheck_1252_; 
lean_dec_ref(v_e_1077_);
v_a_1245_ = lean_ctor_get(v___x_1234_, 0);
v_isSharedCheck_1252_ = !lean_is_exclusive(v___x_1234_);
if (v_isSharedCheck_1252_ == 0)
{
v___x_1247_ = v___x_1234_;
v_isShared_1248_ = v_isSharedCheck_1252_;
goto v_resetjp_1246_;
}
else
{
lean_inc(v_a_1245_);
lean_dec(v___x_1234_);
v___x_1247_ = lean_box(0);
v_isShared_1248_ = v_isSharedCheck_1252_;
goto v_resetjp_1246_;
}
v_resetjp_1246_:
{
lean_object* v___x_1250_; 
if (v_isShared_1248_ == 0)
{
v___x_1250_ = v___x_1247_;
goto v_reusejp_1249_;
}
else
{
lean_object* v_reuseFailAlloc_1251_; 
v_reuseFailAlloc_1251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1251_, 0, v_a_1245_);
v___x_1250_ = v_reuseFailAlloc_1251_;
goto v_reusejp_1249_;
}
v_reusejp_1249_:
{
return v___x_1250_;
}
}
}
}
}
else
{
v_as_x27_1079_ = v_tail_1094_;
v_b_1080_ = v___x_1118_;
goto _start;
}
}
}
else
{
lean_object* v_a_1256_; lean_object* v___x_1258_; uint8_t v_isShared_1259_; uint8_t v_isSharedCheck_1263_; 
lean_dec_ref(v_e_1077_);
v_a_1256_ = lean_ctor_get(v___x_1116_, 0);
v_isSharedCheck_1263_ = !lean_is_exclusive(v___x_1116_);
if (v_isSharedCheck_1263_ == 0)
{
v___x_1258_ = v___x_1116_;
v_isShared_1259_ = v_isSharedCheck_1263_;
goto v_resetjp_1257_;
}
else
{
lean_inc(v_a_1256_);
lean_dec(v___x_1116_);
v___x_1258_ = lean_box(0);
v_isShared_1259_ = v_isSharedCheck_1263_;
goto v_resetjp_1257_;
}
v_resetjp_1257_:
{
lean_object* v___x_1261_; 
if (v_isShared_1259_ == 0)
{
v___x_1261_ = v___x_1258_;
goto v_reusejp_1260_;
}
else
{
lean_object* v_reuseFailAlloc_1262_; 
v_reuseFailAlloc_1262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1262_, 0, v_a_1256_);
v___x_1261_ = v_reuseFailAlloc_1262_;
goto v_reusejp_1260_;
}
v_reusejp_1260_:
{
return v___x_1261_;
}
}
}
v___jp_1095_:
{
if (lean_obj_tag(v___y_1096_) == 0)
{
lean_object* v_a_1097_; lean_object* v___x_1099_; uint8_t v_isShared_1100_; uint8_t v_isSharedCheck_1107_; 
v_a_1097_ = lean_ctor_get(v___y_1096_, 0);
v_isSharedCheck_1107_ = !lean_is_exclusive(v___y_1096_);
if (v_isSharedCheck_1107_ == 0)
{
v___x_1099_ = v___y_1096_;
v_isShared_1100_ = v_isSharedCheck_1107_;
goto v_resetjp_1098_;
}
else
{
lean_inc(v_a_1097_);
lean_dec(v___y_1096_);
v___x_1099_ = lean_box(0);
v_isShared_1100_ = v_isSharedCheck_1107_;
goto v_resetjp_1098_;
}
v_resetjp_1098_:
{
if (lean_obj_tag(v_a_1097_) == 0)
{
lean_object* v_a_1101_; lean_object* v___x_1103_; 
lean_dec_ref(v_e_1077_);
v_a_1101_ = lean_ctor_get(v_a_1097_, 0);
lean_inc(v_a_1101_);
lean_dec_ref_known(v_a_1097_, 1);
if (v_isShared_1100_ == 0)
{
lean_ctor_set(v___x_1099_, 0, v_a_1101_);
v___x_1103_ = v___x_1099_;
goto v_reusejp_1102_;
}
else
{
lean_object* v_reuseFailAlloc_1104_; 
v_reuseFailAlloc_1104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1104_, 0, v_a_1101_);
v___x_1103_ = v_reuseFailAlloc_1104_;
goto v_reusejp_1102_;
}
v_reusejp_1102_:
{
return v___x_1103_;
}
}
else
{
lean_object* v_a_1105_; 
lean_del_object(v___x_1099_);
v_a_1105_ = lean_ctor_get(v_a_1097_, 0);
lean_inc(v_a_1105_);
lean_dec_ref_known(v_a_1097_, 1);
v_as_x27_1079_ = v_tail_1094_;
v_b_1080_ = v_a_1105_;
goto _start;
}
}
}
else
{
lean_object* v_a_1108_; lean_object* v___x_1110_; uint8_t v_isShared_1111_; uint8_t v_isSharedCheck_1115_; 
lean_dec_ref(v_e_1077_);
v_a_1108_ = lean_ctor_get(v___y_1096_, 0);
v_isSharedCheck_1115_ = !lean_is_exclusive(v___y_1096_);
if (v_isSharedCheck_1115_ == 0)
{
v___x_1110_ = v___y_1096_;
v_isShared_1111_ = v_isSharedCheck_1115_;
goto v_resetjp_1109_;
}
else
{
lean_inc(v_a_1108_);
lean_dec(v___y_1096_);
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
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___boxed(lean_object* v_e_1264_, lean_object* v_a_1265_, lean_object* v_as_x27_1266_, lean_object* v_b_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_){
_start:
{
uint8_t v_a_66636__boxed_1279_; lean_object* v_res_1280_; 
v_a_66636__boxed_1279_ = lean_unbox(v_a_1265_);
v_res_1280_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg(v_e_1264_, v_a_66636__boxed_1279_, v_as_x27_1266_, v_b_1267_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_, v___y_1276_, v___y_1277_);
lean_dec(v___y_1277_);
lean_dec_ref(v___y_1276_);
lean_dec(v___y_1275_);
lean_dec_ref(v___y_1274_);
lean_dec(v___y_1273_);
lean_dec_ref(v___y_1272_);
lean_dec(v___y_1271_);
lean_dec_ref(v___y_1270_);
lean_dec(v___y_1269_);
lean_dec(v___y_1268_);
lean_dec(v_as_x27_1266_);
return v_res_1280_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents___closed__1(void){
_start:
{
lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; 
v___x_1282_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents___closed__0));
v___x_1283_ = lean_unsigned_to_nat(6u);
v___x_1284_ = lean_unsigned_to_nat(96u);
v___x_1285_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__0));
v___x_1286_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__0));
v___x_1287_ = l_mkPanicMessageWithDecl(v___x_1286_, v___x_1285_, v___x_1284_, v___x_1283_, v___x_1282_);
return v___x_1287_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents(lean_object* v_e_1288_, lean_object* v_a_1289_, lean_object* v_a_1290_, lean_object* v_a_1291_, lean_object* v_a_1292_, lean_object* v_a_1293_, lean_object* v_a_1294_, lean_object* v_a_1295_, lean_object* v_a_1296_, lean_object* v_a_1297_, lean_object* v_a_1298_){
_start:
{
lean_object* v___x_1300_; 
v___x_1300_ = l_Lean_Meta_Grind_isRoot___redArg(v_e_1288_, v_a_1289_);
if (lean_obj_tag(v___x_1300_) == 0)
{
lean_object* v_a_1301_; uint8_t v___x_1302_; 
v_a_1301_ = lean_ctor_get(v___x_1300_, 0);
lean_inc(v_a_1301_);
lean_dec_ref_known(v___x_1300_, 1);
v___x_1302_ = lean_unbox(v_a_1301_);
if (v___x_1302_ == 0)
{
lean_object* v___x_1303_; 
lean_dec(v_a_1301_);
v___x_1303_ = l_Lean_Meta_Grind_getParents___redArg(v_e_1288_, v_a_1289_);
lean_dec_ref(v_e_1288_);
if (lean_obj_tag(v___x_1303_) == 0)
{
lean_object* v_a_1304_; lean_object* v___x_1306_; uint8_t v_isShared_1307_; uint8_t v_isSharedCheck_1315_; 
v_a_1304_ = lean_ctor_get(v___x_1303_, 0);
v_isSharedCheck_1315_ = !lean_is_exclusive(v___x_1303_);
if (v_isSharedCheck_1315_ == 0)
{
v___x_1306_ = v___x_1303_;
v_isShared_1307_ = v_isSharedCheck_1315_;
goto v_resetjp_1305_;
}
else
{
lean_inc(v_a_1304_);
lean_dec(v___x_1303_);
v___x_1306_ = lean_box(0);
v_isShared_1307_ = v_isSharedCheck_1315_;
goto v_resetjp_1305_;
}
v_resetjp_1305_:
{
uint8_t v___x_1308_; 
v___x_1308_ = l_Lean_Meta_Grind_ParentSet_isEmpty(v_a_1304_);
lean_dec(v_a_1304_);
if (v___x_1308_ == 0)
{
lean_object* v___x_1309_; lean_object* v___x_1310_; 
lean_del_object(v___x_1306_);
v___x_1309_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents___closed__1, &l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents___closed__1);
v___x_1310_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__4(v___x_1309_, v_a_1289_, v_a_1290_, v_a_1291_, v_a_1292_, v_a_1293_, v_a_1294_, v_a_1295_, v_a_1296_, v_a_1297_, v_a_1298_);
return v___x_1310_;
}
else
{
lean_object* v___x_1311_; lean_object* v___x_1313_; 
v___x_1311_ = lean_box(0);
if (v_isShared_1307_ == 0)
{
lean_ctor_set(v___x_1306_, 0, v___x_1311_);
v___x_1313_ = v___x_1306_;
goto v_reusejp_1312_;
}
else
{
lean_object* v_reuseFailAlloc_1314_; 
v_reuseFailAlloc_1314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1314_, 0, v___x_1311_);
v___x_1313_ = v_reuseFailAlloc_1314_;
goto v_reusejp_1312_;
}
v_reusejp_1312_:
{
return v___x_1313_;
}
}
}
}
else
{
lean_object* v_a_1316_; lean_object* v___x_1318_; uint8_t v_isShared_1319_; uint8_t v_isSharedCheck_1323_; 
v_a_1316_ = lean_ctor_get(v___x_1303_, 0);
v_isSharedCheck_1323_ = !lean_is_exclusive(v___x_1303_);
if (v_isSharedCheck_1323_ == 0)
{
v___x_1318_ = v___x_1303_;
v_isShared_1319_ = v_isSharedCheck_1323_;
goto v_resetjp_1317_;
}
else
{
lean_inc(v_a_1316_);
lean_dec(v___x_1303_);
v___x_1318_ = lean_box(0);
v_isShared_1319_ = v_isSharedCheck_1323_;
goto v_resetjp_1317_;
}
v_resetjp_1317_:
{
lean_object* v___x_1321_; 
if (v_isShared_1319_ == 0)
{
v___x_1321_ = v___x_1318_;
goto v_reusejp_1320_;
}
else
{
lean_object* v_reuseFailAlloc_1322_; 
v_reuseFailAlloc_1322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1322_, 0, v_a_1316_);
v___x_1321_ = v_reuseFailAlloc_1322_;
goto v_reusejp_1320_;
}
v_reusejp_1320_:
{
return v___x_1321_;
}
}
}
}
else
{
lean_object* v___x_1324_; 
v___x_1324_ = l_Lean_Meta_Grind_getParents___redArg(v_e_1288_, v_a_1289_);
if (lean_obj_tag(v___x_1324_) == 0)
{
lean_object* v_a_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; uint8_t v___x_1328_; lean_object* v___x_1329_; 
v_a_1325_ = lean_ctor_get(v___x_1324_, 0);
lean_inc(v_a_1325_);
lean_dec_ref_known(v___x_1324_, 1);
v___x_1326_ = l_Lean_Meta_Grind_ParentSet_elems(v_a_1325_);
lean_dec(v_a_1325_);
v___x_1327_ = lean_box(0);
v___x_1328_ = lean_unbox(v_a_1301_);
lean_dec(v_a_1301_);
v___x_1329_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg(v_e_1288_, v___x_1328_, v___x_1326_, v___x_1327_, v_a_1289_, v_a_1290_, v_a_1291_, v_a_1292_, v_a_1293_, v_a_1294_, v_a_1295_, v_a_1296_, v_a_1297_, v_a_1298_);
lean_dec(v___x_1326_);
if (lean_obj_tag(v___x_1329_) == 0)
{
lean_object* v___x_1331_; uint8_t v_isShared_1332_; uint8_t v_isSharedCheck_1336_; 
v_isSharedCheck_1336_ = !lean_is_exclusive(v___x_1329_);
if (v_isSharedCheck_1336_ == 0)
{
lean_object* v_unused_1337_; 
v_unused_1337_ = lean_ctor_get(v___x_1329_, 0);
lean_dec(v_unused_1337_);
v___x_1331_ = v___x_1329_;
v_isShared_1332_ = v_isSharedCheck_1336_;
goto v_resetjp_1330_;
}
else
{
lean_dec(v___x_1329_);
v___x_1331_ = lean_box(0);
v_isShared_1332_ = v_isSharedCheck_1336_;
goto v_resetjp_1330_;
}
v_resetjp_1330_:
{
lean_object* v___x_1334_; 
if (v_isShared_1332_ == 0)
{
lean_ctor_set(v___x_1331_, 0, v___x_1327_);
v___x_1334_ = v___x_1331_;
goto v_reusejp_1333_;
}
else
{
lean_object* v_reuseFailAlloc_1335_; 
v_reuseFailAlloc_1335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1335_, 0, v___x_1327_);
v___x_1334_ = v_reuseFailAlloc_1335_;
goto v_reusejp_1333_;
}
v_reusejp_1333_:
{
return v___x_1334_;
}
}
}
else
{
return v___x_1329_;
}
}
else
{
lean_object* v_a_1338_; lean_object* v___x_1340_; uint8_t v_isShared_1341_; uint8_t v_isSharedCheck_1345_; 
lean_dec(v_a_1301_);
lean_dec_ref(v_e_1288_);
v_a_1338_ = lean_ctor_get(v___x_1324_, 0);
v_isSharedCheck_1345_ = !lean_is_exclusive(v___x_1324_);
if (v_isSharedCheck_1345_ == 0)
{
v___x_1340_ = v___x_1324_;
v_isShared_1341_ = v_isSharedCheck_1345_;
goto v_resetjp_1339_;
}
else
{
lean_inc(v_a_1338_);
lean_dec(v___x_1324_);
v___x_1340_ = lean_box(0);
v_isShared_1341_ = v_isSharedCheck_1345_;
goto v_resetjp_1339_;
}
v_resetjp_1339_:
{
lean_object* v___x_1343_; 
if (v_isShared_1341_ == 0)
{
v___x_1343_ = v___x_1340_;
goto v_reusejp_1342_;
}
else
{
lean_object* v_reuseFailAlloc_1344_; 
v_reuseFailAlloc_1344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1344_, 0, v_a_1338_);
v___x_1343_ = v_reuseFailAlloc_1344_;
goto v_reusejp_1342_;
}
v_reusejp_1342_:
{
return v___x_1343_;
}
}
}
}
}
else
{
lean_object* v_a_1346_; lean_object* v___x_1348_; uint8_t v_isShared_1349_; uint8_t v_isSharedCheck_1353_; 
lean_dec_ref(v_e_1288_);
v_a_1346_ = lean_ctor_get(v___x_1300_, 0);
v_isSharedCheck_1353_ = !lean_is_exclusive(v___x_1300_);
if (v_isSharedCheck_1353_ == 0)
{
v___x_1348_ = v___x_1300_;
v_isShared_1349_ = v_isSharedCheck_1353_;
goto v_resetjp_1347_;
}
else
{
lean_inc(v_a_1346_);
lean_dec(v___x_1300_);
v___x_1348_ = lean_box(0);
v_isShared_1349_ = v_isSharedCheck_1353_;
goto v_resetjp_1347_;
}
v_resetjp_1347_:
{
lean_object* v___x_1351_; 
if (v_isShared_1349_ == 0)
{
v___x_1351_ = v___x_1348_;
goto v_reusejp_1350_;
}
else
{
lean_object* v_reuseFailAlloc_1352_; 
v_reuseFailAlloc_1352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1352_, 0, v_a_1346_);
v___x_1351_ = v_reuseFailAlloc_1352_;
goto v_reusejp_1350_;
}
v_reusejp_1350_:
{
return v___x_1351_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents___boxed(lean_object* v_e_1354_, lean_object* v_a_1355_, lean_object* v_a_1356_, lean_object* v_a_1357_, lean_object* v_a_1358_, lean_object* v_a_1359_, lean_object* v_a_1360_, lean_object* v_a_1361_, lean_object* v_a_1362_, lean_object* v_a_1363_, lean_object* v_a_1364_, lean_object* v_a_1365_){
_start:
{
lean_object* v_res_1366_; 
v_res_1366_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents(v_e_1354_, v_a_1355_, v_a_1356_, v_a_1357_, v_a_1358_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_, v_a_1363_, v_a_1364_);
lean_dec(v_a_1364_);
lean_dec_ref(v_a_1363_);
lean_dec(v_a_1362_);
lean_dec_ref(v_a_1361_);
lean_dec(v_a_1360_);
lean_dec_ref(v_a_1359_);
lean_dec(v_a_1358_);
lean_dec_ref(v_a_1357_);
lean_dec(v_a_1356_);
lean_dec(v_a_1355_);
return v_res_1366_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__1(lean_object* v_00_u03b1_1367_, lean_object* v_msg_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_){
_start:
{
lean_object* v___x_1380_; 
v___x_1380_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__1___redArg(v_msg_1368_, v___y_1375_, v___y_1376_, v___y_1377_, v___y_1378_);
return v___x_1380_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__1___boxed(lean_object* v_00_u03b1_1381_, lean_object* v_msg_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_){
_start:
{
lean_object* v_res_1394_; 
v_res_1394_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__1(v_00_u03b1_1381_, v_msg_1382_, v___y_1383_, v___y_1384_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_, v___y_1392_);
lean_dec(v___y_1392_);
lean_dec_ref(v___y_1391_);
lean_dec(v___y_1390_);
lean_dec_ref(v___y_1389_);
lean_dec(v___y_1388_);
lean_dec_ref(v___y_1387_);
lean_dec(v___y_1386_);
lean_dec_ref(v___y_1385_);
lean_dec(v___y_1384_);
lean_dec(v___y_1383_);
return v_res_1394_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__2(lean_object* v_e_1395_, uint8_t v_a_1396_, lean_object* v_as_1397_, size_t v_sz_1398_, size_t v_i_1399_, uint8_t v_b_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_){
_start:
{
lean_object* v___x_1412_; 
v___x_1412_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__2___redArg(v_e_1395_, v_a_1396_, v_as_1397_, v_sz_1398_, v_i_1399_, v_b_1400_, v___y_1401_);
return v___x_1412_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__2___boxed(lean_object** _args){
lean_object* v_e_1413_ = _args[0];
lean_object* v_a_1414_ = _args[1];
lean_object* v_as_1415_ = _args[2];
lean_object* v_sz_1416_ = _args[3];
lean_object* v_i_1417_ = _args[4];
lean_object* v_b_1418_ = _args[5];
lean_object* v___y_1419_ = _args[6];
lean_object* v___y_1420_ = _args[7];
lean_object* v___y_1421_ = _args[8];
lean_object* v___y_1422_ = _args[9];
lean_object* v___y_1423_ = _args[10];
lean_object* v___y_1424_ = _args[11];
lean_object* v___y_1425_ = _args[12];
lean_object* v___y_1426_ = _args[13];
lean_object* v___y_1427_ = _args[14];
lean_object* v___y_1428_ = _args[15];
lean_object* v___y_1429_ = _args[16];
_start:
{
uint8_t v_a_67209__boxed_1430_; size_t v_sz_boxed_1431_; size_t v_i_boxed_1432_; uint8_t v_b_boxed_1433_; lean_object* v_res_1434_; 
v_a_67209__boxed_1430_ = lean_unbox(v_a_1414_);
v_sz_boxed_1431_ = lean_unbox_usize(v_sz_1416_);
lean_dec(v_sz_1416_);
v_i_boxed_1432_ = lean_unbox_usize(v_i_1417_);
lean_dec(v_i_1417_);
v_b_boxed_1433_ = lean_unbox(v_b_1418_);
v_res_1434_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__2(v_e_1413_, v_a_67209__boxed_1430_, v_as_1415_, v_sz_boxed_1431_, v_i_boxed_1432_, v_b_boxed_1433_, v___y_1419_, v___y_1420_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1426_, v___y_1427_, v___y_1428_);
lean_dec(v___y_1428_);
lean_dec_ref(v___y_1427_);
lean_dec(v___y_1426_);
lean_dec_ref(v___y_1425_);
lean_dec(v___y_1424_);
lean_dec_ref(v___y_1423_);
lean_dec(v___y_1422_);
lean_dec_ref(v___y_1421_);
lean_dec(v___y_1420_);
lean_dec(v___y_1419_);
lean_dec_ref(v_as_1415_);
lean_dec_ref(v_e_1413_);
return v_res_1434_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3(lean_object* v_e_1435_, uint8_t v_a_1436_, lean_object* v_as_1437_, lean_object* v_as_x27_1438_, lean_object* v_b_1439_, lean_object* v_a_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_){
_start:
{
lean_object* v___x_1452_; 
v___x_1452_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg(v_e_1435_, v_a_1436_, v_as_x27_1438_, v_b_1439_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_);
return v___x_1452_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___boxed(lean_object** _args){
lean_object* v_e_1453_ = _args[0];
lean_object* v_a_1454_ = _args[1];
lean_object* v_as_1455_ = _args[2];
lean_object* v_as_x27_1456_ = _args[3];
lean_object* v_b_1457_ = _args[4];
lean_object* v_a_1458_ = _args[5];
lean_object* v___y_1459_ = _args[6];
lean_object* v___y_1460_ = _args[7];
lean_object* v___y_1461_ = _args[8];
lean_object* v___y_1462_ = _args[9];
lean_object* v___y_1463_ = _args[10];
lean_object* v___y_1464_ = _args[11];
lean_object* v___y_1465_ = _args[12];
lean_object* v___y_1466_ = _args[13];
lean_object* v___y_1467_ = _args[14];
lean_object* v___y_1468_ = _args[15];
lean_object* v___y_1469_ = _args[16];
_start:
{
uint8_t v_a_67247__boxed_1470_; lean_object* v_res_1471_; 
v_a_67247__boxed_1470_ = lean_unbox(v_a_1454_);
v_res_1471_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3(v_e_1453_, v_a_67247__boxed_1470_, v_as_1455_, v_as_x27_1456_, v_b_1457_, v_a_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_);
lean_dec(v___y_1468_);
lean_dec_ref(v___y_1467_);
lean_dec(v___y_1466_);
lean_dec_ref(v___y_1465_);
lean_dec(v___y_1464_);
lean_dec_ref(v___y_1463_);
lean_dec(v___y_1462_);
lean_dec_ref(v___y_1461_);
lean_dec(v___y_1460_);
lean_dec(v___y_1459_);
lean_dec(v_as_x27_1456_);
lean_dec(v_as_1455_);
return v_res_1471_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; 
v___x_1474_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg___closed__1));
v___x_1475_ = lean_unsigned_to_nat(6u);
v___x_1476_ = lean_unsigned_to_nat(105u);
v___x_1477_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg___closed__0));
v___x_1478_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__0));
v___x_1479_ = l_mkPanicMessageWithDecl(v___x_1478_, v___x_1477_, v___x_1476_, v___x_1475_, v___x_1474_);
return v___x_1479_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; 
v___x_1481_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg___closed__3));
v___x_1482_ = lean_unsigned_to_nat(6u);
v___x_1483_ = lean_unsigned_to_nat(107u);
v___x_1484_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg___closed__0));
v___x_1485_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__0));
v___x_1486_ = l_mkPanicMessageWithDecl(v___x_1485_, v___x_1484_, v___x_1483_, v___x_1482_, v___x_1481_);
return v___x_1486_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg(lean_object* v_upperBound_1487_, lean_object* v_a_1488_, lean_object* v___x_1489_, lean_object* v_a_1490_, lean_object* v_b_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_){
_start:
{
lean_object* v_a_1504_; lean_object* v___y_1509_; uint8_t v___x_1528_; 
v___x_1528_ = lean_nat_dec_lt(v_a_1490_, v_upperBound_1487_);
if (v___x_1528_ == 0)
{
lean_object* v___x_1529_; 
lean_dec(v_a_1490_);
v___x_1529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1529_, 0, v_b_1491_);
return v___x_1529_;
}
else
{
lean_object* v___x_1530_; lean_object* v___x_1531_; uint8_t v___x_1532_; uint8_t v___x_1533_; 
v___x_1530_ = l_Lean_instInhabitedExpr;
v___x_1531_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1530_, v_a_1488_, v_a_1490_);
v___x_1532_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_1489_, v___x_1531_);
v___x_1533_ = lean_bool_not(v___x_1532_);
if (v___x_1533_ == 0)
{
lean_object* v___x_1534_; lean_object* v___x_1535_; 
lean_dec(v___x_1531_);
v___x_1534_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg___closed__2, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg___closed__2_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg___closed__2);
v___x_1535_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__0(v___x_1534_, v___y_1492_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_, v___y_1500_, v___y_1501_);
v___y_1509_ = v___x_1535_;
goto v___jp_1508_;
}
else
{
uint8_t v___x_1536_; uint8_t v___x_1537_; 
v___x_1536_ = lean_expr_equal(v___x_1489_, v___x_1531_);
lean_dec(v___x_1531_);
v___x_1537_ = lean_bool_not(v___x_1536_);
if (v___x_1537_ == 0)
{
lean_object* v___x_1538_; lean_object* v___x_1539_; 
v___x_1538_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg___closed__4, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg___closed__4_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg___closed__4);
v___x_1539_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__0(v___x_1538_, v___y_1492_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_, v___y_1500_, v___y_1501_);
v___y_1509_ = v___x_1539_;
goto v___jp_1508_;
}
else
{
lean_object* v___x_1540_; 
v___x_1540_ = lean_box(0);
v_a_1504_ = v___x_1540_;
goto v___jp_1503_;
}
}
}
v___jp_1503_:
{
lean_object* v___x_1505_; lean_object* v___x_1506_; 
v___x_1505_ = lean_unsigned_to_nat(1u);
v___x_1506_ = lean_nat_add(v_a_1490_, v___x_1505_);
lean_dec(v_a_1490_);
v_a_1490_ = v___x_1506_;
v_b_1491_ = v_a_1504_;
goto _start;
}
v___jp_1508_:
{
if (lean_obj_tag(v___y_1509_) == 0)
{
lean_object* v_a_1510_; lean_object* v___x_1512_; uint8_t v_isShared_1513_; uint8_t v_isSharedCheck_1519_; 
v_a_1510_ = lean_ctor_get(v___y_1509_, 0);
v_isSharedCheck_1519_ = !lean_is_exclusive(v___y_1509_);
if (v_isSharedCheck_1519_ == 0)
{
v___x_1512_ = v___y_1509_;
v_isShared_1513_ = v_isSharedCheck_1519_;
goto v_resetjp_1511_;
}
else
{
lean_inc(v_a_1510_);
lean_dec(v___y_1509_);
v___x_1512_ = lean_box(0);
v_isShared_1513_ = v_isSharedCheck_1519_;
goto v_resetjp_1511_;
}
v_resetjp_1511_:
{
if (lean_obj_tag(v_a_1510_) == 0)
{
lean_object* v_a_1514_; lean_object* v___x_1516_; 
lean_dec(v_a_1490_);
v_a_1514_ = lean_ctor_get(v_a_1510_, 0);
lean_inc(v_a_1514_);
lean_dec_ref_known(v_a_1510_, 1);
if (v_isShared_1513_ == 0)
{
lean_ctor_set(v___x_1512_, 0, v_a_1514_);
v___x_1516_ = v___x_1512_;
goto v_reusejp_1515_;
}
else
{
lean_object* v_reuseFailAlloc_1517_; 
v_reuseFailAlloc_1517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1517_, 0, v_a_1514_);
v___x_1516_ = v_reuseFailAlloc_1517_;
goto v_reusejp_1515_;
}
v_reusejp_1515_:
{
return v___x_1516_;
}
}
else
{
lean_object* v_a_1518_; 
lean_del_object(v___x_1512_);
v_a_1518_ = lean_ctor_get(v_a_1510_, 0);
lean_inc(v_a_1518_);
lean_dec_ref_known(v_a_1510_, 1);
v_a_1504_ = v_a_1518_;
goto v___jp_1503_;
}
}
}
else
{
lean_object* v_a_1520_; lean_object* v___x_1522_; uint8_t v_isShared_1523_; uint8_t v_isSharedCheck_1527_; 
lean_dec(v_a_1490_);
v_a_1520_ = lean_ctor_get(v___y_1509_, 0);
v_isSharedCheck_1527_ = !lean_is_exclusive(v___y_1509_);
if (v_isSharedCheck_1527_ == 0)
{
v___x_1522_ = v___y_1509_;
v_isShared_1523_ = v_isSharedCheck_1527_;
goto v_resetjp_1521_;
}
else
{
lean_inc(v_a_1520_);
lean_dec(v___y_1509_);
v___x_1522_ = lean_box(0);
v_isShared_1523_ = v_isSharedCheck_1527_;
goto v_resetjp_1521_;
}
v_resetjp_1521_:
{
lean_object* v___x_1525_; 
if (v_isShared_1523_ == 0)
{
v___x_1525_ = v___x_1522_;
goto v_reusejp_1524_;
}
else
{
lean_object* v_reuseFailAlloc_1526_; 
v_reuseFailAlloc_1526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1526_, 0, v_a_1520_);
v___x_1525_ = v_reuseFailAlloc_1526_;
goto v_reusejp_1524_;
}
v_reusejp_1524_:
{
return v___x_1525_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg___boxed(lean_object* v_upperBound_1541_, lean_object* v_a_1542_, lean_object* v___x_1543_, lean_object* v_a_1544_, lean_object* v_b_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_){
_start:
{
lean_object* v_res_1557_; 
v_res_1557_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg(v_upperBound_1541_, v_a_1542_, v___x_1543_, v_a_1544_, v_b_1545_, v___y_1546_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_, v___y_1554_, v___y_1555_);
lean_dec(v___y_1555_);
lean_dec_ref(v___y_1554_);
lean_dec(v___y_1553_);
lean_dec_ref(v___y_1552_);
lean_dec(v___y_1551_);
lean_dec_ref(v___y_1550_);
lean_dec(v___y_1549_);
lean_dec_ref(v___y_1548_);
lean_dec(v___y_1547_);
lean_dec(v___y_1546_);
lean_dec_ref(v___x_1543_);
lean_dec_ref(v_a_1542_);
lean_dec(v_upperBound_1541_);
return v_res_1557_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__1___redArg(lean_object* v_upperBound_1558_, lean_object* v___x_1559_, lean_object* v_a_1560_, lean_object* v_a_1561_, lean_object* v_b_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_){
_start:
{
uint8_t v___x_1574_; 
v___x_1574_ = lean_nat_dec_lt(v_a_1561_, v_upperBound_1558_);
if (v___x_1574_ == 0)
{
lean_object* v___x_1575_; 
lean_dec(v_a_1561_);
v___x_1575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1575_, 0, v_b_1562_);
return v___x_1575_;
}
else
{
lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; 
v___x_1576_ = lean_box(0);
v___x_1577_ = l_Lean_instInhabitedExpr;
v___x_1578_ = lean_unsigned_to_nat(1u);
v___x_1579_ = lean_nat_add(v_a_1561_, v___x_1578_);
v___x_1580_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1577_, v_a_1560_, v_a_1561_);
lean_dec(v_a_1561_);
lean_inc(v___x_1579_);
v___x_1581_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg(v___x_1559_, v_a_1560_, v___x_1580_, v___x_1579_, v___x_1576_, v___y_1563_, v___y_1564_, v___y_1565_, v___y_1566_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_, v___y_1571_, v___y_1572_);
lean_dec(v___x_1580_);
if (lean_obj_tag(v___x_1581_) == 0)
{
lean_dec_ref_known(v___x_1581_, 1);
v_a_1561_ = v___x_1579_;
v_b_1562_ = v___x_1576_;
goto _start;
}
else
{
lean_dec(v___x_1579_);
return v___x_1581_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__1___redArg___boxed(lean_object* v_upperBound_1583_, lean_object* v___x_1584_, lean_object* v_a_1585_, lean_object* v_a_1586_, lean_object* v_b_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_){
_start:
{
lean_object* v_res_1599_; 
v_res_1599_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__1___redArg(v_upperBound_1583_, v___x_1584_, v_a_1585_, v_a_1586_, v_b_1587_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_, v___y_1592_, v___y_1593_, v___y_1594_, v___y_1595_, v___y_1596_, v___y_1597_);
lean_dec(v___y_1597_);
lean_dec_ref(v___y_1596_);
lean_dec(v___y_1595_);
lean_dec_ref(v___y_1594_);
lean_dec(v___y_1593_);
lean_dec_ref(v___y_1592_);
lean_dec(v___y_1591_);
lean_dec_ref(v___y_1590_);
lean_dec(v___y_1589_);
lean_dec(v___y_1588_);
lean_dec_ref(v_a_1585_);
lean_dec(v___x_1584_);
lean_dec(v_upperBound_1583_);
return v_res_1599_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq(lean_object* v_a_1600_, lean_object* v_a_1601_, lean_object* v_a_1602_, lean_object* v_a_1603_, lean_object* v_a_1604_, lean_object* v_a_1605_, lean_object* v_a_1606_, lean_object* v_a_1607_, lean_object* v_a_1608_, lean_object* v_a_1609_){
_start:
{
lean_object* v___x_1611_; 
v___x_1611_ = l_Lean_Meta_Grind_getExprs___redArg(v_a_1600_);
if (lean_obj_tag(v___x_1611_) == 0)
{
lean_object* v_a_1612_; lean_object* v_size_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; 
v_a_1612_ = lean_ctor_get(v___x_1611_, 0);
lean_inc(v_a_1612_);
lean_dec_ref_known(v___x_1611_, 1);
v_size_1613_ = lean_ctor_get(v_a_1612_, 2);
lean_inc(v_size_1613_);
v___x_1614_ = lean_unsigned_to_nat(0u);
v___x_1615_ = lean_box(0);
v___x_1616_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__1___redArg(v_size_1613_, v_size_1613_, v_a_1612_, v___x_1614_, v___x_1615_, v_a_1600_, v_a_1601_, v_a_1602_, v_a_1603_, v_a_1604_, v_a_1605_, v_a_1606_, v_a_1607_, v_a_1608_, v_a_1609_);
lean_dec(v_a_1612_);
lean_dec(v_size_1613_);
if (lean_obj_tag(v___x_1616_) == 0)
{
lean_object* v___x_1618_; uint8_t v_isShared_1619_; uint8_t v_isSharedCheck_1623_; 
v_isSharedCheck_1623_ = !lean_is_exclusive(v___x_1616_);
if (v_isSharedCheck_1623_ == 0)
{
lean_object* v_unused_1624_; 
v_unused_1624_ = lean_ctor_get(v___x_1616_, 0);
lean_dec(v_unused_1624_);
v___x_1618_ = v___x_1616_;
v_isShared_1619_ = v_isSharedCheck_1623_;
goto v_resetjp_1617_;
}
else
{
lean_dec(v___x_1616_);
v___x_1618_ = lean_box(0);
v_isShared_1619_ = v_isSharedCheck_1623_;
goto v_resetjp_1617_;
}
v_resetjp_1617_:
{
lean_object* v___x_1621_; 
if (v_isShared_1619_ == 0)
{
lean_ctor_set(v___x_1618_, 0, v___x_1615_);
v___x_1621_ = v___x_1618_;
goto v_reusejp_1620_;
}
else
{
lean_object* v_reuseFailAlloc_1622_; 
v_reuseFailAlloc_1622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1622_, 0, v___x_1615_);
v___x_1621_ = v_reuseFailAlloc_1622_;
goto v_reusejp_1620_;
}
v_reusejp_1620_:
{
return v___x_1621_;
}
}
}
else
{
return v___x_1616_;
}
}
else
{
lean_object* v_a_1625_; lean_object* v___x_1627_; uint8_t v_isShared_1628_; uint8_t v_isSharedCheck_1632_; 
v_a_1625_ = lean_ctor_get(v___x_1611_, 0);
v_isSharedCheck_1632_ = !lean_is_exclusive(v___x_1611_);
if (v_isSharedCheck_1632_ == 0)
{
v___x_1627_ = v___x_1611_;
v_isShared_1628_ = v_isSharedCheck_1632_;
goto v_resetjp_1626_;
}
else
{
lean_inc(v_a_1625_);
lean_dec(v___x_1611_);
v___x_1627_ = lean_box(0);
v_isShared_1628_ = v_isSharedCheck_1632_;
goto v_resetjp_1626_;
}
v_resetjp_1626_:
{
lean_object* v___x_1630_; 
if (v_isShared_1628_ == 0)
{
v___x_1630_ = v___x_1627_;
goto v_reusejp_1629_;
}
else
{
lean_object* v_reuseFailAlloc_1631_; 
v_reuseFailAlloc_1631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1631_, 0, v_a_1625_);
v___x_1630_ = v_reuseFailAlloc_1631_;
goto v_reusejp_1629_;
}
v_reusejp_1629_:
{
return v___x_1630_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq___boxed(lean_object* v_a_1633_, lean_object* v_a_1634_, lean_object* v_a_1635_, lean_object* v_a_1636_, lean_object* v_a_1637_, lean_object* v_a_1638_, lean_object* v_a_1639_, lean_object* v_a_1640_, lean_object* v_a_1641_, lean_object* v_a_1642_, lean_object* v_a_1643_){
_start:
{
lean_object* v_res_1644_; 
v_res_1644_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq(v_a_1633_, v_a_1634_, v_a_1635_, v_a_1636_, v_a_1637_, v_a_1638_, v_a_1639_, v_a_1640_, v_a_1641_, v_a_1642_);
lean_dec(v_a_1642_);
lean_dec_ref(v_a_1641_);
lean_dec(v_a_1640_);
lean_dec_ref(v_a_1639_);
lean_dec(v_a_1638_);
lean_dec_ref(v_a_1637_);
lean_dec(v_a_1636_);
lean_dec_ref(v_a_1635_);
lean_dec(v_a_1634_);
lean_dec(v_a_1633_);
return v_res_1644_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0(lean_object* v_upperBound_1645_, lean_object* v_a_1646_, lean_object* v___x_1647_, lean_object* v_inst_1648_, lean_object* v_R_1649_, lean_object* v_a_1650_, lean_object* v_b_1651_, lean_object* v_c_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_){
_start:
{
lean_object* v___x_1664_; 
v___x_1664_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg(v_upperBound_1645_, v_a_1646_, v___x_1647_, v_a_1650_, v_b_1651_, v___y_1653_, v___y_1654_, v___y_1655_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_, v___y_1661_, v___y_1662_);
return v___x_1664_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___boxed(lean_object** _args){
lean_object* v_upperBound_1665_ = _args[0];
lean_object* v_a_1666_ = _args[1];
lean_object* v___x_1667_ = _args[2];
lean_object* v_inst_1668_ = _args[3];
lean_object* v_R_1669_ = _args[4];
lean_object* v_a_1670_ = _args[5];
lean_object* v_b_1671_ = _args[6];
lean_object* v_c_1672_ = _args[7];
lean_object* v___y_1673_ = _args[8];
lean_object* v___y_1674_ = _args[9];
lean_object* v___y_1675_ = _args[10];
lean_object* v___y_1676_ = _args[11];
lean_object* v___y_1677_ = _args[12];
lean_object* v___y_1678_ = _args[13];
lean_object* v___y_1679_ = _args[14];
lean_object* v___y_1680_ = _args[15];
lean_object* v___y_1681_ = _args[16];
lean_object* v___y_1682_ = _args[17];
lean_object* v___y_1683_ = _args[18];
_start:
{
lean_object* v_res_1684_; 
v_res_1684_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0(v_upperBound_1665_, v_a_1666_, v___x_1667_, v_inst_1668_, v_R_1669_, v_a_1670_, v_b_1671_, v_c_1672_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_);
lean_dec(v___y_1682_);
lean_dec_ref(v___y_1681_);
lean_dec(v___y_1680_);
lean_dec_ref(v___y_1679_);
lean_dec(v___y_1678_);
lean_dec_ref(v___y_1677_);
lean_dec(v___y_1676_);
lean_dec_ref(v___y_1675_);
lean_dec(v___y_1674_);
lean_dec(v___y_1673_);
lean_dec_ref(v___x_1667_);
lean_dec_ref(v_a_1666_);
lean_dec(v_upperBound_1665_);
return v_res_1684_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__1(lean_object* v_upperBound_1685_, lean_object* v___x_1686_, lean_object* v_a_1687_, lean_object* v_inst_1688_, lean_object* v_R_1689_, lean_object* v_a_1690_, lean_object* v_b_1691_, lean_object* v_c_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_){
_start:
{
lean_object* v___x_1704_; 
v___x_1704_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__1___redArg(v_upperBound_1685_, v___x_1686_, v_a_1687_, v_a_1690_, v_b_1691_, v___y_1693_, v___y_1694_, v___y_1695_, v___y_1696_, v___y_1697_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_);
return v___x_1704_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__1___boxed(lean_object** _args){
lean_object* v_upperBound_1705_ = _args[0];
lean_object* v___x_1706_ = _args[1];
lean_object* v_a_1707_ = _args[2];
lean_object* v_inst_1708_ = _args[3];
lean_object* v_R_1709_ = _args[4];
lean_object* v_a_1710_ = _args[5];
lean_object* v_b_1711_ = _args[6];
lean_object* v_c_1712_ = _args[7];
lean_object* v___y_1713_ = _args[8];
lean_object* v___y_1714_ = _args[9];
lean_object* v___y_1715_ = _args[10];
lean_object* v___y_1716_ = _args[11];
lean_object* v___y_1717_ = _args[12];
lean_object* v___y_1718_ = _args[13];
lean_object* v___y_1719_ = _args[14];
lean_object* v___y_1720_ = _args[15];
lean_object* v___y_1721_ = _args[16];
lean_object* v___y_1722_ = _args[17];
lean_object* v___y_1723_ = _args[18];
_start:
{
lean_object* v_res_1724_; 
v_res_1724_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__1(v_upperBound_1705_, v___x_1706_, v_a_1707_, v_inst_1708_, v_R_1709_, v_a_1710_, v_b_1711_, v_c_1712_, v___y_1713_, v___y_1714_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_);
lean_dec(v___y_1722_);
lean_dec_ref(v___y_1721_);
lean_dec(v___y_1720_);
lean_dec_ref(v___y_1719_);
lean_dec(v___y_1718_);
lean_dec_ref(v___y_1717_);
lean_dec(v___y_1716_);
lean_dec_ref(v___y_1715_);
lean_dec(v___y_1714_);
lean_dec(v___y_1713_);
lean_dec_ref(v_a_1707_);
lean_dec(v___x_1706_);
lean_dec(v_upperBound_1705_);
return v_res_1724_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1725_; double v___x_1726_; 
v___x_1725_ = lean_unsigned_to_nat(0u);
v___x_1726_ = lean_float_of_nat(v___x_1725_);
return v___x_1726_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__0___redArg(lean_object* v_cls_1730_, lean_object* v_msg_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_){
_start:
{
lean_object* v_ref_1737_; lean_object* v___x_1738_; lean_object* v_a_1739_; lean_object* v___x_1741_; uint8_t v_isShared_1742_; uint8_t v_isSharedCheck_1783_; 
v_ref_1737_ = lean_ctor_get(v___y_1734_, 5);
v___x_1738_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__1_spec__1(v_msg_1731_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_);
v_a_1739_ = lean_ctor_get(v___x_1738_, 0);
v_isSharedCheck_1783_ = !lean_is_exclusive(v___x_1738_);
if (v_isSharedCheck_1783_ == 0)
{
v___x_1741_ = v___x_1738_;
v_isShared_1742_ = v_isSharedCheck_1783_;
goto v_resetjp_1740_;
}
else
{
lean_inc(v_a_1739_);
lean_dec(v___x_1738_);
v___x_1741_ = lean_box(0);
v_isShared_1742_ = v_isSharedCheck_1783_;
goto v_resetjp_1740_;
}
v_resetjp_1740_:
{
lean_object* v___x_1743_; lean_object* v_traceState_1744_; lean_object* v_env_1745_; lean_object* v_nextMacroScope_1746_; lean_object* v_ngen_1747_; lean_object* v_auxDeclNGen_1748_; lean_object* v_cache_1749_; lean_object* v_messages_1750_; lean_object* v_infoState_1751_; lean_object* v_snapshotTasks_1752_; lean_object* v___x_1754_; uint8_t v_isShared_1755_; uint8_t v_isSharedCheck_1782_; 
v___x_1743_ = lean_st_ref_take(v___y_1735_);
v_traceState_1744_ = lean_ctor_get(v___x_1743_, 4);
v_env_1745_ = lean_ctor_get(v___x_1743_, 0);
v_nextMacroScope_1746_ = lean_ctor_get(v___x_1743_, 1);
v_ngen_1747_ = lean_ctor_get(v___x_1743_, 2);
v_auxDeclNGen_1748_ = lean_ctor_get(v___x_1743_, 3);
v_cache_1749_ = lean_ctor_get(v___x_1743_, 5);
v_messages_1750_ = lean_ctor_get(v___x_1743_, 6);
v_infoState_1751_ = lean_ctor_get(v___x_1743_, 7);
v_snapshotTasks_1752_ = lean_ctor_get(v___x_1743_, 8);
v_isSharedCheck_1782_ = !lean_is_exclusive(v___x_1743_);
if (v_isSharedCheck_1782_ == 0)
{
v___x_1754_ = v___x_1743_;
v_isShared_1755_ = v_isSharedCheck_1782_;
goto v_resetjp_1753_;
}
else
{
lean_inc(v_snapshotTasks_1752_);
lean_inc(v_infoState_1751_);
lean_inc(v_messages_1750_);
lean_inc(v_cache_1749_);
lean_inc(v_traceState_1744_);
lean_inc(v_auxDeclNGen_1748_);
lean_inc(v_ngen_1747_);
lean_inc(v_nextMacroScope_1746_);
lean_inc(v_env_1745_);
lean_dec(v___x_1743_);
v___x_1754_ = lean_box(0);
v_isShared_1755_ = v_isSharedCheck_1782_;
goto v_resetjp_1753_;
}
v_resetjp_1753_:
{
uint64_t v_tid_1756_; lean_object* v_traces_1757_; lean_object* v___x_1759_; uint8_t v_isShared_1760_; uint8_t v_isSharedCheck_1781_; 
v_tid_1756_ = lean_ctor_get_uint64(v_traceState_1744_, sizeof(void*)*1);
v_traces_1757_ = lean_ctor_get(v_traceState_1744_, 0);
v_isSharedCheck_1781_ = !lean_is_exclusive(v_traceState_1744_);
if (v_isSharedCheck_1781_ == 0)
{
v___x_1759_ = v_traceState_1744_;
v_isShared_1760_ = v_isSharedCheck_1781_;
goto v_resetjp_1758_;
}
else
{
lean_inc(v_traces_1757_);
lean_dec(v_traceState_1744_);
v___x_1759_ = lean_box(0);
v_isShared_1760_ = v_isSharedCheck_1781_;
goto v_resetjp_1758_;
}
v_resetjp_1758_:
{
lean_object* v___x_1761_; double v___x_1762_; uint8_t v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1771_; 
v___x_1761_ = lean_box(0);
v___x_1762_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__0___redArg___closed__0);
v___x_1763_ = 0;
v___x_1764_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__0___redArg___closed__1));
v___x_1765_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1765_, 0, v_cls_1730_);
lean_ctor_set(v___x_1765_, 1, v___x_1761_);
lean_ctor_set(v___x_1765_, 2, v___x_1764_);
lean_ctor_set_float(v___x_1765_, sizeof(void*)*3, v___x_1762_);
lean_ctor_set_float(v___x_1765_, sizeof(void*)*3 + 8, v___x_1762_);
lean_ctor_set_uint8(v___x_1765_, sizeof(void*)*3 + 16, v___x_1763_);
v___x_1766_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__0___redArg___closed__2));
v___x_1767_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1767_, 0, v___x_1765_);
lean_ctor_set(v___x_1767_, 1, v_a_1739_);
lean_ctor_set(v___x_1767_, 2, v___x_1766_);
lean_inc(v_ref_1737_);
v___x_1768_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1768_, 0, v_ref_1737_);
lean_ctor_set(v___x_1768_, 1, v___x_1767_);
v___x_1769_ = l_Lean_PersistentArray_push___redArg(v_traces_1757_, v___x_1768_);
if (v_isShared_1760_ == 0)
{
lean_ctor_set(v___x_1759_, 0, v___x_1769_);
v___x_1771_ = v___x_1759_;
goto v_reusejp_1770_;
}
else
{
lean_object* v_reuseFailAlloc_1780_; 
v_reuseFailAlloc_1780_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1780_, 0, v___x_1769_);
lean_ctor_set_uint64(v_reuseFailAlloc_1780_, sizeof(void*)*1, v_tid_1756_);
v___x_1771_ = v_reuseFailAlloc_1780_;
goto v_reusejp_1770_;
}
v_reusejp_1770_:
{
lean_object* v___x_1773_; 
if (v_isShared_1755_ == 0)
{
lean_ctor_set(v___x_1754_, 4, v___x_1771_);
v___x_1773_ = v___x_1754_;
goto v_reusejp_1772_;
}
else
{
lean_object* v_reuseFailAlloc_1779_; 
v_reuseFailAlloc_1779_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1779_, 0, v_env_1745_);
lean_ctor_set(v_reuseFailAlloc_1779_, 1, v_nextMacroScope_1746_);
lean_ctor_set(v_reuseFailAlloc_1779_, 2, v_ngen_1747_);
lean_ctor_set(v_reuseFailAlloc_1779_, 3, v_auxDeclNGen_1748_);
lean_ctor_set(v_reuseFailAlloc_1779_, 4, v___x_1771_);
lean_ctor_set(v_reuseFailAlloc_1779_, 5, v_cache_1749_);
lean_ctor_set(v_reuseFailAlloc_1779_, 6, v_messages_1750_);
lean_ctor_set(v_reuseFailAlloc_1779_, 7, v_infoState_1751_);
lean_ctor_set(v_reuseFailAlloc_1779_, 8, v_snapshotTasks_1752_);
v___x_1773_ = v_reuseFailAlloc_1779_;
goto v_reusejp_1772_;
}
v_reusejp_1772_:
{
lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1777_; 
v___x_1774_ = lean_st_ref_set(v___y_1735_, v___x_1773_);
v___x_1775_ = lean_box(0);
if (v_isShared_1742_ == 0)
{
lean_ctor_set(v___x_1741_, 0, v___x_1775_);
v___x_1777_ = v___x_1741_;
goto v_reusejp_1776_;
}
else
{
lean_object* v_reuseFailAlloc_1778_; 
v_reuseFailAlloc_1778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1778_, 0, v___x_1775_);
v___x_1777_ = v_reuseFailAlloc_1778_;
goto v_reusejp_1776_;
}
v_reusejp_1776_:
{
return v___x_1777_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__0___redArg___boxed(lean_object* v_cls_1784_, lean_object* v_msg_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_){
_start:
{
lean_object* v_res_1791_; 
v_res_1791_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__0___redArg(v_cls_1784_, v_msg_1785_, v___y_1786_, v___y_1787_, v___y_1788_, v___y_1789_);
lean_dec(v___y_1789_);
lean_dec_ref(v___y_1788_);
lean_dec(v___y_1787_);
lean_dec_ref(v___y_1786_);
return v_res_1791_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__6(void){
_start:
{
lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; 
v___x_1802_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__3));
v___x_1803_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__5));
v___x_1804_ = l_Lean_Name_append(v___x_1803_, v___x_1802_);
return v___x_1804_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__8(void){
_start:
{
lean_object* v___x_1806_; lean_object* v___x_1807_; 
v___x_1806_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__7));
v___x_1807_ = l_Lean_stringToMessageData(v___x_1806_);
return v___x_1807_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__10(void){
_start:
{
lean_object* v___x_1809_; lean_object* v___x_1810_; 
v___x_1809_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__9));
v___x_1810_ = l_Lean_stringToMessageData(v___x_1809_);
return v___x_1810_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg(lean_object* v_a_1811_, lean_object* v_as_x27_1812_, lean_object* v_b_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_){
_start:
{
if (lean_obj_tag(v_as_x27_1812_) == 0)
{
lean_object* v___x_1825_; 
lean_dec_ref(v_a_1811_);
v___x_1825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1825_, 0, v_b_1813_);
return v___x_1825_;
}
else
{
lean_object* v_head_1826_; lean_object* v_tail_1827_; lean_object* v___x_1828_; uint8_t v___x_1829_; 
v_head_1826_ = lean_ctor_get(v_as_x27_1812_, 0);
v_tail_1827_ = lean_ctor_get(v_as_x27_1812_, 1);
v___x_1828_ = lean_box(0);
v___x_1829_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_a_1811_, v_head_1826_);
if (v___x_1829_ == 0)
{
lean_object* v___x_1830_; 
lean_inc(v_head_1826_);
lean_inc_ref(v_a_1811_);
v___x_1830_ = l_Lean_Meta_Grind_mkEqHEqProof(v_a_1811_, v_head_1826_, v___y_1814_, v___y_1815_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_, v___y_1820_, v___y_1821_, v___y_1822_, v___y_1823_);
if (lean_obj_tag(v___x_1830_) == 0)
{
lean_object* v_options_1831_; lean_object* v_a_1832_; lean_object* v_inheritedTraceOptions_1833_; uint8_t v_hasTrace_1834_; lean_object* v___x_1835_; lean_object* v___y_1837_; lean_object* v___y_1838_; lean_object* v___y_1839_; lean_object* v___y_1840_; lean_object* v___y_1841_; lean_object* v___y_1842_; lean_object* v___y_1843_; lean_object* v___y_1844_; lean_object* v___y_1845_; lean_object* v___y_1846_; 
v_options_1831_ = lean_ctor_get(v___y_1822_, 2);
v_a_1832_ = lean_ctor_get(v___x_1830_, 0);
lean_inc(v_a_1832_);
lean_dec_ref_known(v___x_1830_, 1);
v_inheritedTraceOptions_1833_ = lean_ctor_get(v___y_1822_, 13);
v_hasTrace_1834_ = lean_ctor_get_uint8(v_options_1831_, sizeof(void*)*1);
v___x_1835_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__3));
if (v_hasTrace_1834_ == 0)
{
v___y_1837_ = v___y_1814_;
v___y_1838_ = v___y_1815_;
v___y_1839_ = v___y_1816_;
v___y_1840_ = v___y_1817_;
v___y_1841_ = v___y_1818_;
v___y_1842_ = v___y_1819_;
v___y_1843_ = v___y_1820_;
v___y_1844_ = v___y_1821_;
v___y_1845_ = v___y_1822_;
v___y_1846_ = v___y_1823_;
goto v___jp_1836_;
}
else
{
lean_object* v___x_1872_; uint8_t v___x_1873_; 
v___x_1872_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__6, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__6_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__6);
v___x_1873_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1833_, v_options_1831_, v___x_1872_);
if (v___x_1873_ == 0)
{
v___y_1837_ = v___y_1814_;
v___y_1838_ = v___y_1815_;
v___y_1839_ = v___y_1816_;
v___y_1840_ = v___y_1817_;
v___y_1841_ = v___y_1818_;
v___y_1842_ = v___y_1819_;
v___y_1843_ = v___y_1820_;
v___y_1844_ = v___y_1821_;
v___y_1845_ = v___y_1822_;
v___y_1846_ = v___y_1823_;
goto v___jp_1836_;
}
else
{
lean_object* v___x_1874_; 
v___x_1874_ = l_Lean_Meta_Grind_updateLastTag(v___y_1814_, v___y_1815_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_, v___y_1820_, v___y_1821_, v___y_1822_, v___y_1823_);
if (lean_obj_tag(v___x_1874_) == 0)
{
lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; 
lean_dec_ref_known(v___x_1874_, 1);
lean_inc_ref(v_a_1811_);
v___x_1875_ = l_Lean_MessageData_ofExpr(v_a_1811_);
v___x_1876_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__10, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__10_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__10);
v___x_1877_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1877_, 0, v___x_1875_);
lean_ctor_set(v___x_1877_, 1, v___x_1876_);
lean_inc(v_head_1826_);
v___x_1878_ = l_Lean_MessageData_ofExpr(v_head_1826_);
v___x_1879_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1879_, 0, v___x_1877_);
lean_ctor_set(v___x_1879_, 1, v___x_1878_);
v___x_1880_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__0___redArg(v___x_1835_, v___x_1879_, v___y_1820_, v___y_1821_, v___y_1822_, v___y_1823_);
if (lean_obj_tag(v___x_1880_) == 0)
{
lean_dec_ref_known(v___x_1880_, 1);
v___y_1837_ = v___y_1814_;
v___y_1838_ = v___y_1815_;
v___y_1839_ = v___y_1816_;
v___y_1840_ = v___y_1817_;
v___y_1841_ = v___y_1818_;
v___y_1842_ = v___y_1819_;
v___y_1843_ = v___y_1820_;
v___y_1844_ = v___y_1821_;
v___y_1845_ = v___y_1822_;
v___y_1846_ = v___y_1823_;
goto v___jp_1836_;
}
else
{
lean_dec(v_a_1832_);
lean_dec_ref(v_a_1811_);
return v___x_1880_;
}
}
else
{
lean_dec(v_a_1832_);
lean_dec_ref(v_a_1811_);
return v___x_1874_;
}
}
}
v___jp_1836_:
{
uint8_t v___x_1847_; lean_object* v___x_1848_; 
v___x_1847_ = 0;
lean_inc(v_a_1832_);
v___x_1848_ = l_Lean_Meta_check(v_a_1832_, v___x_1847_, v___y_1843_, v___y_1844_, v___y_1845_, v___y_1846_);
if (lean_obj_tag(v___x_1848_) == 0)
{
lean_object* v_options_1849_; uint8_t v_hasTrace_1850_; 
lean_dec_ref_known(v___x_1848_, 1);
v_options_1849_ = lean_ctor_get(v___y_1845_, 2);
v_hasTrace_1850_ = lean_ctor_get_uint8(v_options_1849_, sizeof(void*)*1);
if (v_hasTrace_1850_ == 0)
{
lean_dec(v_a_1832_);
v_as_x27_1812_ = v_tail_1827_;
v_b_1813_ = v___x_1828_;
goto _start;
}
else
{
lean_object* v_inheritedTraceOptions_1852_; lean_object* v___x_1853_; uint8_t v___x_1854_; 
v_inheritedTraceOptions_1852_ = lean_ctor_get(v___y_1845_, 13);
v___x_1853_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__6, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__6_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__6);
v___x_1854_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1852_, v_options_1849_, v___x_1853_);
if (v___x_1854_ == 0)
{
lean_dec(v_a_1832_);
v_as_x27_1812_ = v_tail_1827_;
v_b_1813_ = v___x_1828_;
goto _start;
}
else
{
lean_object* v___x_1856_; 
v___x_1856_ = l_Lean_Meta_Grind_updateLastTag(v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_, v___y_1841_, v___y_1842_, v___y_1843_, v___y_1844_, v___y_1845_, v___y_1846_);
if (lean_obj_tag(v___x_1856_) == 0)
{
lean_object* v___x_1857_; 
lean_dec_ref_known(v___x_1856_, 1);
lean_inc(v___y_1846_);
lean_inc_ref(v___y_1845_);
lean_inc(v___y_1844_);
lean_inc_ref(v___y_1843_);
v___x_1857_ = lean_infer_type(v_a_1832_, v___y_1843_, v___y_1844_, v___y_1845_, v___y_1846_);
if (lean_obj_tag(v___x_1857_) == 0)
{
lean_object* v_a_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; 
v_a_1858_ = lean_ctor_get(v___x_1857_, 0);
lean_inc(v_a_1858_);
lean_dec_ref_known(v___x_1857_, 1);
v___x_1859_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__8, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__8_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__8);
v___x_1860_ = l_Lean_MessageData_ofExpr(v_a_1858_);
v___x_1861_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1861_, 0, v___x_1859_);
lean_ctor_set(v___x_1861_, 1, v___x_1860_);
v___x_1862_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__0___redArg(v___x_1835_, v___x_1861_, v___y_1843_, v___y_1844_, v___y_1845_, v___y_1846_);
if (lean_obj_tag(v___x_1862_) == 0)
{
lean_dec_ref_known(v___x_1862_, 1);
v_as_x27_1812_ = v_tail_1827_;
v_b_1813_ = v___x_1828_;
goto _start;
}
else
{
lean_dec_ref(v_a_1811_);
return v___x_1862_;
}
}
else
{
lean_object* v_a_1864_; lean_object* v___x_1866_; uint8_t v_isShared_1867_; uint8_t v_isSharedCheck_1871_; 
lean_dec_ref(v_a_1811_);
v_a_1864_ = lean_ctor_get(v___x_1857_, 0);
v_isSharedCheck_1871_ = !lean_is_exclusive(v___x_1857_);
if (v_isSharedCheck_1871_ == 0)
{
v___x_1866_ = v___x_1857_;
v_isShared_1867_ = v_isSharedCheck_1871_;
goto v_resetjp_1865_;
}
else
{
lean_inc(v_a_1864_);
lean_dec(v___x_1857_);
v___x_1866_ = lean_box(0);
v_isShared_1867_ = v_isSharedCheck_1871_;
goto v_resetjp_1865_;
}
v_resetjp_1865_:
{
lean_object* v___x_1869_; 
if (v_isShared_1867_ == 0)
{
v___x_1869_ = v___x_1866_;
goto v_reusejp_1868_;
}
else
{
lean_object* v_reuseFailAlloc_1870_; 
v_reuseFailAlloc_1870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1870_, 0, v_a_1864_);
v___x_1869_ = v_reuseFailAlloc_1870_;
goto v_reusejp_1868_;
}
v_reusejp_1868_:
{
return v___x_1869_;
}
}
}
}
else
{
lean_dec(v_a_1832_);
lean_dec_ref(v_a_1811_);
return v___x_1856_;
}
}
}
}
else
{
lean_dec(v_a_1832_);
lean_dec_ref(v_a_1811_);
return v___x_1848_;
}
}
}
else
{
lean_object* v_a_1881_; lean_object* v___x_1883_; uint8_t v_isShared_1884_; uint8_t v_isSharedCheck_1888_; 
lean_dec_ref(v_a_1811_);
v_a_1881_ = lean_ctor_get(v___x_1830_, 0);
v_isSharedCheck_1888_ = !lean_is_exclusive(v___x_1830_);
if (v_isSharedCheck_1888_ == 0)
{
v___x_1883_ = v___x_1830_;
v_isShared_1884_ = v_isSharedCheck_1888_;
goto v_resetjp_1882_;
}
else
{
lean_inc(v_a_1881_);
lean_dec(v___x_1830_);
v___x_1883_ = lean_box(0);
v_isShared_1884_ = v_isSharedCheck_1888_;
goto v_resetjp_1882_;
}
v_resetjp_1882_:
{
lean_object* v___x_1886_; 
if (v_isShared_1884_ == 0)
{
v___x_1886_ = v___x_1883_;
goto v_reusejp_1885_;
}
else
{
lean_object* v_reuseFailAlloc_1887_; 
v_reuseFailAlloc_1887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1887_, 0, v_a_1881_);
v___x_1886_ = v_reuseFailAlloc_1887_;
goto v_reusejp_1885_;
}
v_reusejp_1885_:
{
return v___x_1886_;
}
}
}
}
else
{
v_as_x27_1812_ = v_tail_1827_;
v_b_1813_ = v___x_1828_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___boxed(lean_object* v_a_1890_, lean_object* v_as_x27_1891_, lean_object* v_b_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_){
_start:
{
lean_object* v_res_1904_; 
v_res_1904_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg(v_a_1890_, v_as_x27_1891_, v_b_1892_, v___y_1893_, v___y_1894_, v___y_1895_, v___y_1896_, v___y_1897_, v___y_1898_, v___y_1899_, v___y_1900_, v___y_1901_, v___y_1902_);
lean_dec(v___y_1902_);
lean_dec_ref(v___y_1901_);
lean_dec(v___y_1900_);
lean_dec_ref(v___y_1899_);
lean_dec(v___y_1898_);
lean_dec_ref(v___y_1897_);
lean_dec(v___y_1896_);
lean_dec_ref(v___y_1895_);
lean_dec(v___y_1894_);
lean_dec(v___y_1893_);
lean_dec(v_as_x27_1891_);
return v_res_1904_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__2___redArg(lean_object* v_a_1905_, lean_object* v_as_x27_1906_, lean_object* v_b_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_){
_start:
{
if (lean_obj_tag(v_as_x27_1906_) == 0)
{
lean_object* v___x_1919_; 
v___x_1919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1919_, 0, v_b_1907_);
return v___x_1919_;
}
else
{
lean_object* v_head_1920_; lean_object* v_tail_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; 
v_head_1920_ = lean_ctor_get(v_as_x27_1906_, 0);
v_tail_1921_ = lean_ctor_get(v_as_x27_1906_, 1);
v___x_1922_ = lean_box(0);
lean_inc(v_head_1920_);
v___x_1923_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg(v_head_1920_, v_a_1905_, v___x_1922_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_, v___y_1912_, v___y_1913_, v___y_1914_, v___y_1915_, v___y_1916_, v___y_1917_);
if (lean_obj_tag(v___x_1923_) == 0)
{
lean_dec_ref_known(v___x_1923_, 1);
v_as_x27_1906_ = v_tail_1921_;
v_b_1907_ = v___x_1922_;
goto _start;
}
else
{
return v___x_1923_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__2___redArg___boxed(lean_object* v_a_1925_, lean_object* v_as_x27_1926_, lean_object* v_b_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_){
_start:
{
lean_object* v_res_1939_; 
v_res_1939_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__2___redArg(v_a_1925_, v_as_x27_1926_, v_b_1927_, v___y_1928_, v___y_1929_, v___y_1930_, v___y_1931_, v___y_1932_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_);
lean_dec(v___y_1937_);
lean_dec_ref(v___y_1936_);
lean_dec(v___y_1935_);
lean_dec_ref(v___y_1934_);
lean_dec(v___y_1933_);
lean_dec_ref(v___y_1932_);
lean_dec(v___y_1931_);
lean_dec_ref(v___y_1930_);
lean_dec(v___y_1929_);
lean_dec(v___y_1928_);
lean_dec(v_as_x27_1926_);
lean_dec(v_a_1925_);
return v_res_1939_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__3___redArg(lean_object* v_as_x27_1940_, lean_object* v_b_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_){
_start:
{
if (lean_obj_tag(v_as_x27_1940_) == 0)
{
lean_object* v___x_1953_; 
v___x_1953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1953_, 0, v_b_1941_);
return v___x_1953_;
}
else
{
lean_object* v_head_1954_; lean_object* v_tail_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; 
v_head_1954_ = lean_ctor_get(v_as_x27_1940_, 0);
v_tail_1955_ = lean_ctor_get(v_as_x27_1940_, 1);
v___x_1956_ = lean_box(0);
v___x_1957_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__2___redArg(v_head_1954_, v_head_1954_, v___x_1956_, v___y_1942_, v___y_1943_, v___y_1944_, v___y_1945_, v___y_1946_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_, v___y_1951_);
if (lean_obj_tag(v___x_1957_) == 0)
{
lean_dec_ref_known(v___x_1957_, 1);
v_as_x27_1940_ = v_tail_1955_;
v_b_1941_ = v___x_1956_;
goto _start;
}
else
{
return v___x_1957_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__3___redArg___boxed(lean_object* v_as_x27_1959_, lean_object* v_b_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_){
_start:
{
lean_object* v_res_1972_; 
v_res_1972_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__3___redArg(v_as_x27_1959_, v_b_1960_, v___y_1961_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_, v___y_1966_, v___y_1967_, v___y_1968_, v___y_1969_, v___y_1970_);
lean_dec(v___y_1970_);
lean_dec_ref(v___y_1969_);
lean_dec(v___y_1968_);
lean_dec_ref(v___y_1967_);
lean_dec(v___y_1966_);
lean_dec_ref(v___y_1965_);
lean_dec(v___y_1964_);
lean_dec_ref(v___y_1963_);
lean_dec(v___y_1962_);
lean_dec(v___y_1961_);
lean_dec(v_as_x27_1959_);
return v_res_1972_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs(lean_object* v_a_1973_, lean_object* v_a_1974_, lean_object* v_a_1975_, lean_object* v_a_1976_, lean_object* v_a_1977_, lean_object* v_a_1978_, lean_object* v_a_1979_, lean_object* v_a_1980_, lean_object* v_a_1981_, lean_object* v_a_1982_){
_start:
{
lean_object* v___x_1984_; uint8_t v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; 
v___x_1984_ = lean_st_ref_get(v_a_1973_);
v___x_1985_ = 0;
v___x_1986_ = l_Lean_Meta_Grind_Goal_getEqcs(v___x_1984_, v___x_1985_);
lean_dec(v___x_1984_);
v___x_1987_ = lean_box(0);
v___x_1988_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__3___redArg(v___x_1986_, v___x_1987_, v_a_1973_, v_a_1974_, v_a_1975_, v_a_1976_, v_a_1977_, v_a_1978_, v_a_1979_, v_a_1980_, v_a_1981_, v_a_1982_);
lean_dec(v___x_1986_);
if (lean_obj_tag(v___x_1988_) == 0)
{
lean_object* v___x_1990_; uint8_t v_isShared_1991_; uint8_t v_isSharedCheck_1995_; 
v_isSharedCheck_1995_ = !lean_is_exclusive(v___x_1988_);
if (v_isSharedCheck_1995_ == 0)
{
lean_object* v_unused_1996_; 
v_unused_1996_ = lean_ctor_get(v___x_1988_, 0);
lean_dec(v_unused_1996_);
v___x_1990_ = v___x_1988_;
v_isShared_1991_ = v_isSharedCheck_1995_;
goto v_resetjp_1989_;
}
else
{
lean_dec(v___x_1988_);
v___x_1990_ = lean_box(0);
v_isShared_1991_ = v_isSharedCheck_1995_;
goto v_resetjp_1989_;
}
v_resetjp_1989_:
{
lean_object* v___x_1993_; 
if (v_isShared_1991_ == 0)
{
lean_ctor_set(v___x_1990_, 0, v___x_1987_);
v___x_1993_ = v___x_1990_;
goto v_reusejp_1992_;
}
else
{
lean_object* v_reuseFailAlloc_1994_; 
v_reuseFailAlloc_1994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1994_, 0, v___x_1987_);
v___x_1993_ = v_reuseFailAlloc_1994_;
goto v_reusejp_1992_;
}
v_reusejp_1992_:
{
return v___x_1993_;
}
}
}
else
{
return v___x_1988_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs___boxed(lean_object* v_a_1997_, lean_object* v_a_1998_, lean_object* v_a_1999_, lean_object* v_a_2000_, lean_object* v_a_2001_, lean_object* v_a_2002_, lean_object* v_a_2003_, lean_object* v_a_2004_, lean_object* v_a_2005_, lean_object* v_a_2006_, lean_object* v_a_2007_){
_start:
{
lean_object* v_res_2008_; 
v_res_2008_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs(v_a_1997_, v_a_1998_, v_a_1999_, v_a_2000_, v_a_2001_, v_a_2002_, v_a_2003_, v_a_2004_, v_a_2005_, v_a_2006_);
lean_dec(v_a_2006_);
lean_dec_ref(v_a_2005_);
lean_dec(v_a_2004_);
lean_dec_ref(v_a_2003_);
lean_dec(v_a_2002_);
lean_dec_ref(v_a_2001_);
lean_dec(v_a_2000_);
lean_dec_ref(v_a_1999_);
lean_dec(v_a_1998_);
lean_dec(v_a_1997_);
return v_res_2008_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__0(lean_object* v_cls_2009_, lean_object* v_msg_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_){
_start:
{
lean_object* v___x_2022_; 
v___x_2022_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__0___redArg(v_cls_2009_, v_msg_2010_, v___y_2017_, v___y_2018_, v___y_2019_, v___y_2020_);
return v___x_2022_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__0___boxed(lean_object* v_cls_2023_, lean_object* v_msg_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_){
_start:
{
lean_object* v_res_2036_; 
v_res_2036_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__0(v_cls_2023_, v_msg_2024_, v___y_2025_, v___y_2026_, v___y_2027_, v___y_2028_, v___y_2029_, v___y_2030_, v___y_2031_, v___y_2032_, v___y_2033_, v___y_2034_);
lean_dec(v___y_2034_);
lean_dec_ref(v___y_2033_);
lean_dec(v___y_2032_);
lean_dec_ref(v___y_2031_);
lean_dec(v___y_2030_);
lean_dec_ref(v___y_2029_);
lean_dec(v___y_2028_);
lean_dec_ref(v___y_2027_);
lean_dec(v___y_2026_);
lean_dec(v___y_2025_);
return v_res_2036_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1(lean_object* v_a_2037_, lean_object* v_as_2038_, lean_object* v_as_x27_2039_, lean_object* v_b_2040_, lean_object* v_a_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_){
_start:
{
lean_object* v___x_2053_; 
v___x_2053_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg(v_a_2037_, v_as_x27_2039_, v_b_2040_, v___y_2042_, v___y_2043_, v___y_2044_, v___y_2045_, v___y_2046_, v___y_2047_, v___y_2048_, v___y_2049_, v___y_2050_, v___y_2051_);
return v___x_2053_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___boxed(lean_object* v_a_2054_, lean_object* v_as_2055_, lean_object* v_as_x27_2056_, lean_object* v_b_2057_, lean_object* v_a_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_){
_start:
{
lean_object* v_res_2070_; 
v_res_2070_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1(v_a_2054_, v_as_2055_, v_as_x27_2056_, v_b_2057_, v_a_2058_, v___y_2059_, v___y_2060_, v___y_2061_, v___y_2062_, v___y_2063_, v___y_2064_, v___y_2065_, v___y_2066_, v___y_2067_, v___y_2068_);
lean_dec(v___y_2068_);
lean_dec_ref(v___y_2067_);
lean_dec(v___y_2066_);
lean_dec_ref(v___y_2065_);
lean_dec(v___y_2064_);
lean_dec_ref(v___y_2063_);
lean_dec(v___y_2062_);
lean_dec_ref(v___y_2061_);
lean_dec(v___y_2060_);
lean_dec(v___y_2059_);
lean_dec(v_as_x27_2056_);
lean_dec(v_as_2055_);
return v_res_2070_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__2(lean_object* v_a_2071_, lean_object* v_as_2072_, lean_object* v_as_x27_2073_, lean_object* v_b_2074_, lean_object* v_a_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_){
_start:
{
lean_object* v___x_2087_; 
v___x_2087_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__2___redArg(v_a_2071_, v_as_x27_2073_, v_b_2074_, v___y_2076_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_, v___y_2081_, v___y_2082_, v___y_2083_, v___y_2084_, v___y_2085_);
return v___x_2087_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__2___boxed(lean_object* v_a_2088_, lean_object* v_as_2089_, lean_object* v_as_x27_2090_, lean_object* v_b_2091_, lean_object* v_a_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_){
_start:
{
lean_object* v_res_2104_; 
v_res_2104_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__2(v_a_2088_, v_as_2089_, v_as_x27_2090_, v_b_2091_, v_a_2092_, v___y_2093_, v___y_2094_, v___y_2095_, v___y_2096_, v___y_2097_, v___y_2098_, v___y_2099_, v___y_2100_, v___y_2101_, v___y_2102_);
lean_dec(v___y_2102_);
lean_dec_ref(v___y_2101_);
lean_dec(v___y_2100_);
lean_dec_ref(v___y_2099_);
lean_dec(v___y_2098_);
lean_dec_ref(v___y_2097_);
lean_dec(v___y_2096_);
lean_dec_ref(v___y_2095_);
lean_dec(v___y_2094_);
lean_dec(v___y_2093_);
lean_dec(v_as_x27_2090_);
lean_dec(v_as_2089_);
lean_dec(v_a_2088_);
return v_res_2104_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__3(lean_object* v_as_2105_, lean_object* v_as_x27_2106_, lean_object* v_b_2107_, lean_object* v_a_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_){
_start:
{
lean_object* v___x_2120_; 
v___x_2120_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__3___redArg(v_as_x27_2106_, v_b_2107_, v___y_2109_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_);
return v___x_2120_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__3___boxed(lean_object* v_as_2121_, lean_object* v_as_x27_2122_, lean_object* v_b_2123_, lean_object* v_a_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_){
_start:
{
lean_object* v_res_2136_; 
v_res_2136_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__3(v_as_2121_, v_as_x27_2122_, v_b_2123_, v_a_2124_, v___y_2125_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_, v___y_2131_, v___y_2132_, v___y_2133_, v___y_2134_);
lean_dec(v___y_2134_);
lean_dec_ref(v___y_2133_);
lean_dec(v___y_2132_);
lean_dec_ref(v___y_2131_);
lean_dec(v___y_2130_);
lean_dec_ref(v___y_2129_);
lean_dec(v___y_2128_);
lean_dec_ref(v___y_2127_);
lean_dec(v___y_2126_);
lean_dec(v___y_2125_);
lean_dec(v_as_x27_2122_);
lean_dec(v_as_2121_);
return v_res_2136_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_Grind_checkInvariants_spec__0(lean_object* v_opts_2137_, lean_object* v_opt_2138_){
_start:
{
lean_object* v_name_2139_; lean_object* v_defValue_2140_; lean_object* v_map_2141_; lean_object* v___x_2142_; 
v_name_2139_ = lean_ctor_get(v_opt_2138_, 0);
v_defValue_2140_ = lean_ctor_get(v_opt_2138_, 1);
v_map_2141_ = lean_ctor_get(v_opts_2137_, 0);
v___x_2142_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2141_, v_name_2139_);
if (lean_obj_tag(v___x_2142_) == 0)
{
uint8_t v___x_2143_; 
v___x_2143_ = lean_unbox(v_defValue_2140_);
return v___x_2143_;
}
else
{
lean_object* v_val_2144_; 
v_val_2144_ = lean_ctor_get(v___x_2142_, 0);
lean_inc(v_val_2144_);
lean_dec_ref_known(v___x_2142_, 1);
if (lean_obj_tag(v_val_2144_) == 1)
{
uint8_t v_v_2145_; 
v_v_2145_ = lean_ctor_get_uint8(v_val_2144_, 0);
lean_dec_ref_known(v_val_2144_, 0);
return v_v_2145_;
}
else
{
uint8_t v___x_2146_; 
lean_dec(v_val_2144_);
v___x_2146_ = lean_unbox(v_defValue_2140_);
return v___x_2146_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Grind_checkInvariants_spec__0___boxed(lean_object* v_opts_2147_, lean_object* v_opt_2148_){
_start:
{
uint8_t v_res_2149_; lean_object* v_r_2150_; 
v_res_2149_ = l_Lean_Option_get___at___00Lean_Meta_Grind_checkInvariants_spec__0(v_opts_2147_, v_opt_2148_);
lean_dec_ref(v_opt_2148_);
lean_dec_ref(v_opts_2147_);
v_r_2150_ = lean_box(v_res_2149_);
return v_r_2150_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__2_spec__5(lean_object* v_as_2151_, size_t v_sz_2152_, size_t v_i_2153_, lean_object* v_b_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_){
_start:
{
uint8_t v___x_2166_; 
v___x_2166_ = lean_usize_dec_lt(v_i_2153_, v_sz_2152_);
if (v___x_2166_ == 0)
{
lean_object* v___x_2167_; 
v___x_2167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2167_, 0, v_b_2154_);
return v___x_2167_;
}
else
{
lean_object* v___x_2168_; lean_object* v_a_2169_; lean_object* v___x_2170_; 
lean_dec_ref(v_b_2154_);
v___x_2168_ = lean_st_ref_get(v___y_2155_);
v_a_2169_ = lean_array_uget_borrowed(v_as_2151_, v_i_2153_);
lean_inc(v_a_2169_);
v___x_2170_ = l_Lean_Meta_Grind_Goal_getENode(v___x_2168_, v_a_2169_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_);
lean_dec(v___x_2168_);
if (lean_obj_tag(v___x_2170_) == 0)
{
lean_object* v_a_2171_; lean_object* v_self_2172_; lean_object* v___x_2173_; 
v_a_2171_ = lean_ctor_get(v___x_2170_, 0);
lean_inc(v_a_2171_);
lean_dec_ref_known(v___x_2170_, 1);
v_self_2172_ = lean_ctor_get(v_a_2171_, 0);
lean_inc_ref(v_self_2172_);
v___x_2173_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents(v_self_2172_, v___y_2155_, v___y_2156_, v___y_2157_, v___y_2158_, v___y_2159_, v___y_2160_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_);
if (lean_obj_tag(v___x_2173_) == 0)
{
lean_object* v___x_2174_; lean_object* v_a_2176_; lean_object* v___x_2181_; uint8_t v___x_2182_; 
lean_dec_ref_known(v___x_2173_, 1);
v___x_2174_ = lean_box(0);
v___x_2181_ = lean_box(0);
v___x_2182_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_2171_);
if (v___x_2182_ == 0)
{
lean_dec(v_a_2171_);
v_a_2176_ = v___x_2181_;
goto v___jp_2175_;
}
else
{
lean_object* v___x_2183_; 
v___x_2183_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc(v_a_2171_, v___y_2155_, v___y_2156_, v___y_2157_, v___y_2158_, v___y_2159_, v___y_2160_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_);
if (lean_obj_tag(v___x_2183_) == 0)
{
lean_dec_ref_known(v___x_2183_, 1);
v_a_2176_ = v___x_2181_;
goto v___jp_2175_;
}
else
{
lean_object* v_a_2184_; lean_object* v___x_2186_; uint8_t v_isShared_2187_; uint8_t v_isSharedCheck_2191_; 
v_a_2184_ = lean_ctor_get(v___x_2183_, 0);
v_isSharedCheck_2191_ = !lean_is_exclusive(v___x_2183_);
if (v_isSharedCheck_2191_ == 0)
{
v___x_2186_ = v___x_2183_;
v_isShared_2187_ = v_isSharedCheck_2191_;
goto v_resetjp_2185_;
}
else
{
lean_inc(v_a_2184_);
lean_dec(v___x_2183_);
v___x_2186_ = lean_box(0);
v_isShared_2187_ = v_isSharedCheck_2191_;
goto v_resetjp_2185_;
}
v_resetjp_2185_:
{
lean_object* v___x_2189_; 
if (v_isShared_2187_ == 0)
{
v___x_2189_ = v___x_2186_;
goto v_reusejp_2188_;
}
else
{
lean_object* v_reuseFailAlloc_2190_; 
v_reuseFailAlloc_2190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2190_, 0, v_a_2184_);
v___x_2189_ = v_reuseFailAlloc_2190_;
goto v_reusejp_2188_;
}
v_reusejp_2188_:
{
return v___x_2189_;
}
}
}
}
v___jp_2175_:
{
lean_object* v___x_2177_; size_t v___x_2178_; size_t v___x_2179_; 
v___x_2177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2177_, 0, v___x_2174_);
lean_ctor_set(v___x_2177_, 1, v_a_2176_);
v___x_2178_ = ((size_t)1ULL);
v___x_2179_ = lean_usize_add(v_i_2153_, v___x_2178_);
v_i_2153_ = v___x_2179_;
v_b_2154_ = v___x_2177_;
goto _start;
}
}
else
{
lean_object* v_a_2192_; lean_object* v___x_2194_; uint8_t v_isShared_2195_; uint8_t v_isSharedCheck_2199_; 
lean_dec(v_a_2171_);
v_a_2192_ = lean_ctor_get(v___x_2173_, 0);
v_isSharedCheck_2199_ = !lean_is_exclusive(v___x_2173_);
if (v_isSharedCheck_2199_ == 0)
{
v___x_2194_ = v___x_2173_;
v_isShared_2195_ = v_isSharedCheck_2199_;
goto v_resetjp_2193_;
}
else
{
lean_inc(v_a_2192_);
lean_dec(v___x_2173_);
v___x_2194_ = lean_box(0);
v_isShared_2195_ = v_isSharedCheck_2199_;
goto v_resetjp_2193_;
}
v_resetjp_2193_:
{
lean_object* v___x_2197_; 
if (v_isShared_2195_ == 0)
{
v___x_2197_ = v___x_2194_;
goto v_reusejp_2196_;
}
else
{
lean_object* v_reuseFailAlloc_2198_; 
v_reuseFailAlloc_2198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2198_, 0, v_a_2192_);
v___x_2197_ = v_reuseFailAlloc_2198_;
goto v_reusejp_2196_;
}
v_reusejp_2196_:
{
return v___x_2197_;
}
}
}
}
else
{
lean_object* v_a_2200_; lean_object* v___x_2202_; uint8_t v_isShared_2203_; uint8_t v_isSharedCheck_2207_; 
v_a_2200_ = lean_ctor_get(v___x_2170_, 0);
v_isSharedCheck_2207_ = !lean_is_exclusive(v___x_2170_);
if (v_isSharedCheck_2207_ == 0)
{
v___x_2202_ = v___x_2170_;
v_isShared_2203_ = v_isSharedCheck_2207_;
goto v_resetjp_2201_;
}
else
{
lean_inc(v_a_2200_);
lean_dec(v___x_2170_);
v___x_2202_ = lean_box(0);
v_isShared_2203_ = v_isSharedCheck_2207_;
goto v_resetjp_2201_;
}
v_resetjp_2201_:
{
lean_object* v___x_2205_; 
if (v_isShared_2203_ == 0)
{
v___x_2205_ = v___x_2202_;
goto v_reusejp_2204_;
}
else
{
lean_object* v_reuseFailAlloc_2206_; 
v_reuseFailAlloc_2206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2206_, 0, v_a_2200_);
v___x_2205_ = v_reuseFailAlloc_2206_;
goto v_reusejp_2204_;
}
v_reusejp_2204_:
{
return v___x_2205_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__2_spec__5___boxed(lean_object* v_as_2208_, lean_object* v_sz_2209_, lean_object* v_i_2210_, lean_object* v_b_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_){
_start:
{
size_t v_sz_boxed_2223_; size_t v_i_boxed_2224_; lean_object* v_res_2225_; 
v_sz_boxed_2223_ = lean_unbox_usize(v_sz_2209_);
lean_dec(v_sz_2209_);
v_i_boxed_2224_ = lean_unbox_usize(v_i_2210_);
lean_dec(v_i_2210_);
v_res_2225_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__2_spec__5(v_as_2208_, v_sz_boxed_2223_, v_i_boxed_2224_, v_b_2211_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_, v___y_2216_, v___y_2217_, v___y_2218_, v___y_2219_, v___y_2220_, v___y_2221_);
lean_dec(v___y_2221_);
lean_dec_ref(v___y_2220_);
lean_dec(v___y_2219_);
lean_dec_ref(v___y_2218_);
lean_dec(v___y_2217_);
lean_dec_ref(v___y_2216_);
lean_dec(v___y_2215_);
lean_dec_ref(v___y_2214_);
lean_dec(v___y_2213_);
lean_dec(v___y_2212_);
lean_dec_ref(v_as_2208_);
return v_res_2225_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__2(lean_object* v_as_2229_, size_t v_sz_2230_, size_t v_i_2231_, lean_object* v_b_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_){
_start:
{
uint8_t v___x_2244_; 
v___x_2244_ = lean_usize_dec_lt(v_i_2231_, v_sz_2230_);
if (v___x_2244_ == 0)
{
lean_object* v___x_2245_; 
v___x_2245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2245_, 0, v_b_2232_);
return v___x_2245_;
}
else
{
lean_object* v___x_2246_; lean_object* v_a_2247_; lean_object* v___x_2248_; 
lean_dec_ref(v_b_2232_);
v___x_2246_ = lean_st_ref_get(v___y_2233_);
v_a_2247_ = lean_array_uget_borrowed(v_as_2229_, v_i_2231_);
lean_inc(v_a_2247_);
v___x_2248_ = l_Lean_Meta_Grind_Goal_getENode(v___x_2246_, v_a_2247_, v___y_2239_, v___y_2240_, v___y_2241_, v___y_2242_);
lean_dec(v___x_2246_);
if (lean_obj_tag(v___x_2248_) == 0)
{
lean_object* v_a_2249_; lean_object* v_self_2250_; lean_object* v___x_2251_; 
v_a_2249_ = lean_ctor_get(v___x_2248_, 0);
lean_inc(v_a_2249_);
lean_dec_ref_known(v___x_2248_, 1);
v_self_2250_ = lean_ctor_get(v_a_2249_, 0);
lean_inc_ref(v_self_2250_);
v___x_2251_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents(v_self_2250_, v___y_2233_, v___y_2234_, v___y_2235_, v___y_2236_, v___y_2237_, v___y_2238_, v___y_2239_, v___y_2240_, v___y_2241_, v___y_2242_);
if (lean_obj_tag(v___x_2251_) == 0)
{
uint8_t v___x_2257_; 
lean_dec_ref_known(v___x_2251_, 1);
v___x_2257_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_2249_);
if (v___x_2257_ == 0)
{
lean_dec(v_a_2249_);
goto v___jp_2252_;
}
else
{
lean_object* v___x_2258_; 
v___x_2258_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc(v_a_2249_, v___y_2233_, v___y_2234_, v___y_2235_, v___y_2236_, v___y_2237_, v___y_2238_, v___y_2239_, v___y_2240_, v___y_2241_, v___y_2242_);
if (lean_obj_tag(v___x_2258_) == 0)
{
lean_dec_ref_known(v___x_2258_, 1);
goto v___jp_2252_;
}
else
{
lean_object* v_a_2259_; lean_object* v___x_2261_; uint8_t v_isShared_2262_; uint8_t v_isSharedCheck_2266_; 
v_a_2259_ = lean_ctor_get(v___x_2258_, 0);
v_isSharedCheck_2266_ = !lean_is_exclusive(v___x_2258_);
if (v_isSharedCheck_2266_ == 0)
{
v___x_2261_ = v___x_2258_;
v_isShared_2262_ = v_isSharedCheck_2266_;
goto v_resetjp_2260_;
}
else
{
lean_inc(v_a_2259_);
lean_dec(v___x_2258_);
v___x_2261_ = lean_box(0);
v_isShared_2262_ = v_isSharedCheck_2266_;
goto v_resetjp_2260_;
}
v_resetjp_2260_:
{
lean_object* v___x_2264_; 
if (v_isShared_2262_ == 0)
{
v___x_2264_ = v___x_2261_;
goto v_reusejp_2263_;
}
else
{
lean_object* v_reuseFailAlloc_2265_; 
v_reuseFailAlloc_2265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2265_, 0, v_a_2259_);
v___x_2264_ = v_reuseFailAlloc_2265_;
goto v_reusejp_2263_;
}
v_reusejp_2263_:
{
return v___x_2264_;
}
}
}
}
v___jp_2252_:
{
lean_object* v___x_2253_; size_t v___x_2254_; size_t v___x_2255_; lean_object* v___x_2256_; 
v___x_2253_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__2___closed__0));
v___x_2254_ = ((size_t)1ULL);
v___x_2255_ = lean_usize_add(v_i_2231_, v___x_2254_);
v___x_2256_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__2_spec__5(v_as_2229_, v_sz_2230_, v___x_2255_, v___x_2253_, v___y_2233_, v___y_2234_, v___y_2235_, v___y_2236_, v___y_2237_, v___y_2238_, v___y_2239_, v___y_2240_, v___y_2241_, v___y_2242_);
return v___x_2256_;
}
}
else
{
lean_object* v_a_2267_; lean_object* v___x_2269_; uint8_t v_isShared_2270_; uint8_t v_isSharedCheck_2274_; 
lean_dec(v_a_2249_);
v_a_2267_ = lean_ctor_get(v___x_2251_, 0);
v_isSharedCheck_2274_ = !lean_is_exclusive(v___x_2251_);
if (v_isSharedCheck_2274_ == 0)
{
v___x_2269_ = v___x_2251_;
v_isShared_2270_ = v_isSharedCheck_2274_;
goto v_resetjp_2268_;
}
else
{
lean_inc(v_a_2267_);
lean_dec(v___x_2251_);
v___x_2269_ = lean_box(0);
v_isShared_2270_ = v_isSharedCheck_2274_;
goto v_resetjp_2268_;
}
v_resetjp_2268_:
{
lean_object* v___x_2272_; 
if (v_isShared_2270_ == 0)
{
v___x_2272_ = v___x_2269_;
goto v_reusejp_2271_;
}
else
{
lean_object* v_reuseFailAlloc_2273_; 
v_reuseFailAlloc_2273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2273_, 0, v_a_2267_);
v___x_2272_ = v_reuseFailAlloc_2273_;
goto v_reusejp_2271_;
}
v_reusejp_2271_:
{
return v___x_2272_;
}
}
}
}
else
{
lean_object* v_a_2275_; lean_object* v___x_2277_; uint8_t v_isShared_2278_; uint8_t v_isSharedCheck_2282_; 
v_a_2275_ = lean_ctor_get(v___x_2248_, 0);
v_isSharedCheck_2282_ = !lean_is_exclusive(v___x_2248_);
if (v_isSharedCheck_2282_ == 0)
{
v___x_2277_ = v___x_2248_;
v_isShared_2278_ = v_isSharedCheck_2282_;
goto v_resetjp_2276_;
}
else
{
lean_inc(v_a_2275_);
lean_dec(v___x_2248_);
v___x_2277_ = lean_box(0);
v_isShared_2278_ = v_isSharedCheck_2282_;
goto v_resetjp_2276_;
}
v_resetjp_2276_:
{
lean_object* v___x_2280_; 
if (v_isShared_2278_ == 0)
{
v___x_2280_ = v___x_2277_;
goto v_reusejp_2279_;
}
else
{
lean_object* v_reuseFailAlloc_2281_; 
v_reuseFailAlloc_2281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2281_, 0, v_a_2275_);
v___x_2280_ = v_reuseFailAlloc_2281_;
goto v_reusejp_2279_;
}
v_reusejp_2279_:
{
return v___x_2280_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__2___boxed(lean_object* v_as_2283_, lean_object* v_sz_2284_, lean_object* v_i_2285_, lean_object* v_b_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_){
_start:
{
size_t v_sz_boxed_2298_; size_t v_i_boxed_2299_; lean_object* v_res_2300_; 
v_sz_boxed_2298_ = lean_unbox_usize(v_sz_2284_);
lean_dec(v_sz_2284_);
v_i_boxed_2299_ = lean_unbox_usize(v_i_2285_);
lean_dec(v_i_2285_);
v_res_2300_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__2(v_as_2283_, v_sz_boxed_2298_, v_i_boxed_2299_, v_b_2286_, v___y_2287_, v___y_2288_, v___y_2289_, v___y_2290_, v___y_2291_, v___y_2292_, v___y_2293_, v___y_2294_, v___y_2295_, v___y_2296_);
lean_dec(v___y_2296_);
lean_dec_ref(v___y_2295_);
lean_dec(v___y_2294_);
lean_dec_ref(v___y_2293_);
lean_dec(v___y_2292_);
lean_dec_ref(v___y_2291_);
lean_dec(v___y_2290_);
lean_dec_ref(v___y_2289_);
lean_dec(v___y_2288_);
lean_dec(v___y_2287_);
lean_dec_ref(v_as_2283_);
return v_res_2300_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__1_spec__3_spec__4(lean_object* v_as_2301_, size_t v_sz_2302_, size_t v_i_2303_, lean_object* v_b_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_){
_start:
{
uint8_t v___x_2316_; 
v___x_2316_ = lean_usize_dec_lt(v_i_2303_, v_sz_2302_);
if (v___x_2316_ == 0)
{
lean_object* v___x_2317_; 
v___x_2317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2317_, 0, v_b_2304_);
return v___x_2317_;
}
else
{
lean_object* v___x_2318_; lean_object* v_a_2319_; lean_object* v___x_2320_; 
lean_dec_ref(v_b_2304_);
v___x_2318_ = lean_st_ref_get(v___y_2305_);
v_a_2319_ = lean_array_uget_borrowed(v_as_2301_, v_i_2303_);
lean_inc(v_a_2319_);
v___x_2320_ = l_Lean_Meta_Grind_Goal_getENode(v___x_2318_, v_a_2319_, v___y_2311_, v___y_2312_, v___y_2313_, v___y_2314_);
lean_dec(v___x_2318_);
if (lean_obj_tag(v___x_2320_) == 0)
{
lean_object* v_a_2321_; lean_object* v_self_2322_; lean_object* v___x_2323_; 
v_a_2321_ = lean_ctor_get(v___x_2320_, 0);
lean_inc(v_a_2321_);
lean_dec_ref_known(v___x_2320_, 1);
v_self_2322_ = lean_ctor_get(v_a_2321_, 0);
lean_inc_ref(v_self_2322_);
v___x_2323_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents(v_self_2322_, v___y_2305_, v___y_2306_, v___y_2307_, v___y_2308_, v___y_2309_, v___y_2310_, v___y_2311_, v___y_2312_, v___y_2313_, v___y_2314_);
if (lean_obj_tag(v___x_2323_) == 0)
{
lean_object* v___x_2324_; lean_object* v_a_2326_; lean_object* v___x_2331_; uint8_t v___x_2332_; 
lean_dec_ref_known(v___x_2323_, 1);
v___x_2324_ = lean_box(0);
v___x_2331_ = lean_box(0);
v___x_2332_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_2321_);
if (v___x_2332_ == 0)
{
lean_dec(v_a_2321_);
v_a_2326_ = v___x_2331_;
goto v___jp_2325_;
}
else
{
lean_object* v___x_2333_; 
v___x_2333_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc(v_a_2321_, v___y_2305_, v___y_2306_, v___y_2307_, v___y_2308_, v___y_2309_, v___y_2310_, v___y_2311_, v___y_2312_, v___y_2313_, v___y_2314_);
if (lean_obj_tag(v___x_2333_) == 0)
{
lean_dec_ref_known(v___x_2333_, 1);
v_a_2326_ = v___x_2331_;
goto v___jp_2325_;
}
else
{
lean_object* v_a_2334_; lean_object* v___x_2336_; uint8_t v_isShared_2337_; uint8_t v_isSharedCheck_2341_; 
v_a_2334_ = lean_ctor_get(v___x_2333_, 0);
v_isSharedCheck_2341_ = !lean_is_exclusive(v___x_2333_);
if (v_isSharedCheck_2341_ == 0)
{
v___x_2336_ = v___x_2333_;
v_isShared_2337_ = v_isSharedCheck_2341_;
goto v_resetjp_2335_;
}
else
{
lean_inc(v_a_2334_);
lean_dec(v___x_2333_);
v___x_2336_ = lean_box(0);
v_isShared_2337_ = v_isSharedCheck_2341_;
goto v_resetjp_2335_;
}
v_resetjp_2335_:
{
lean_object* v___x_2339_; 
if (v_isShared_2337_ == 0)
{
v___x_2339_ = v___x_2336_;
goto v_reusejp_2338_;
}
else
{
lean_object* v_reuseFailAlloc_2340_; 
v_reuseFailAlloc_2340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2340_, 0, v_a_2334_);
v___x_2339_ = v_reuseFailAlloc_2340_;
goto v_reusejp_2338_;
}
v_reusejp_2338_:
{
return v___x_2339_;
}
}
}
}
v___jp_2325_:
{
lean_object* v___x_2327_; size_t v___x_2328_; size_t v___x_2329_; 
v___x_2327_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2327_, 0, v___x_2324_);
lean_ctor_set(v___x_2327_, 1, v_a_2326_);
v___x_2328_ = ((size_t)1ULL);
v___x_2329_ = lean_usize_add(v_i_2303_, v___x_2328_);
v_i_2303_ = v___x_2329_;
v_b_2304_ = v___x_2327_;
goto _start;
}
}
else
{
lean_object* v_a_2342_; lean_object* v___x_2344_; uint8_t v_isShared_2345_; uint8_t v_isSharedCheck_2349_; 
lean_dec(v_a_2321_);
v_a_2342_ = lean_ctor_get(v___x_2323_, 0);
v_isSharedCheck_2349_ = !lean_is_exclusive(v___x_2323_);
if (v_isSharedCheck_2349_ == 0)
{
v___x_2344_ = v___x_2323_;
v_isShared_2345_ = v_isSharedCheck_2349_;
goto v_resetjp_2343_;
}
else
{
lean_inc(v_a_2342_);
lean_dec(v___x_2323_);
v___x_2344_ = lean_box(0);
v_isShared_2345_ = v_isSharedCheck_2349_;
goto v_resetjp_2343_;
}
v_resetjp_2343_:
{
lean_object* v___x_2347_; 
if (v_isShared_2345_ == 0)
{
v___x_2347_ = v___x_2344_;
goto v_reusejp_2346_;
}
else
{
lean_object* v_reuseFailAlloc_2348_; 
v_reuseFailAlloc_2348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2348_, 0, v_a_2342_);
v___x_2347_ = v_reuseFailAlloc_2348_;
goto v_reusejp_2346_;
}
v_reusejp_2346_:
{
return v___x_2347_;
}
}
}
}
else
{
lean_object* v_a_2350_; lean_object* v___x_2352_; uint8_t v_isShared_2353_; uint8_t v_isSharedCheck_2357_; 
v_a_2350_ = lean_ctor_get(v___x_2320_, 0);
v_isSharedCheck_2357_ = !lean_is_exclusive(v___x_2320_);
if (v_isSharedCheck_2357_ == 0)
{
v___x_2352_ = v___x_2320_;
v_isShared_2353_ = v_isSharedCheck_2357_;
goto v_resetjp_2351_;
}
else
{
lean_inc(v_a_2350_);
lean_dec(v___x_2320_);
v___x_2352_ = lean_box(0);
v_isShared_2353_ = v_isSharedCheck_2357_;
goto v_resetjp_2351_;
}
v_resetjp_2351_:
{
lean_object* v___x_2355_; 
if (v_isShared_2353_ == 0)
{
v___x_2355_ = v___x_2352_;
goto v_reusejp_2354_;
}
else
{
lean_object* v_reuseFailAlloc_2356_; 
v_reuseFailAlloc_2356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2356_, 0, v_a_2350_);
v___x_2355_ = v_reuseFailAlloc_2356_;
goto v_reusejp_2354_;
}
v_reusejp_2354_:
{
return v___x_2355_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__1_spec__3_spec__4___boxed(lean_object* v_as_2358_, lean_object* v_sz_2359_, lean_object* v_i_2360_, lean_object* v_b_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_){
_start:
{
size_t v_sz_boxed_2373_; size_t v_i_boxed_2374_; lean_object* v_res_2375_; 
v_sz_boxed_2373_ = lean_unbox_usize(v_sz_2359_);
lean_dec(v_sz_2359_);
v_i_boxed_2374_ = lean_unbox_usize(v_i_2360_);
lean_dec(v_i_2360_);
v_res_2375_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__1_spec__3_spec__4(v_as_2358_, v_sz_boxed_2373_, v_i_boxed_2374_, v_b_2361_, v___y_2362_, v___y_2363_, v___y_2364_, v___y_2365_, v___y_2366_, v___y_2367_, v___y_2368_, v___y_2369_, v___y_2370_, v___y_2371_);
lean_dec(v___y_2371_);
lean_dec_ref(v___y_2370_);
lean_dec(v___y_2369_);
lean_dec_ref(v___y_2368_);
lean_dec(v___y_2367_);
lean_dec_ref(v___y_2366_);
lean_dec(v___y_2365_);
lean_dec_ref(v___y_2364_);
lean_dec(v___y_2363_);
lean_dec(v___y_2362_);
lean_dec_ref(v_as_2358_);
return v_res_2375_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__1_spec__3(lean_object* v_as_2379_, size_t v_sz_2380_, size_t v_i_2381_, lean_object* v_b_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_){
_start:
{
uint8_t v___x_2394_; 
v___x_2394_ = lean_usize_dec_lt(v_i_2381_, v_sz_2380_);
if (v___x_2394_ == 0)
{
lean_object* v___x_2395_; 
v___x_2395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2395_, 0, v_b_2382_);
return v___x_2395_;
}
else
{
lean_object* v___x_2396_; lean_object* v_a_2397_; lean_object* v___x_2398_; 
lean_dec_ref(v_b_2382_);
v___x_2396_ = lean_st_ref_get(v___y_2383_);
v_a_2397_ = lean_array_uget_borrowed(v_as_2379_, v_i_2381_);
lean_inc(v_a_2397_);
v___x_2398_ = l_Lean_Meta_Grind_Goal_getENode(v___x_2396_, v_a_2397_, v___y_2389_, v___y_2390_, v___y_2391_, v___y_2392_);
lean_dec(v___x_2396_);
if (lean_obj_tag(v___x_2398_) == 0)
{
lean_object* v_a_2399_; lean_object* v_self_2400_; lean_object* v___x_2401_; 
v_a_2399_ = lean_ctor_get(v___x_2398_, 0);
lean_inc(v_a_2399_);
lean_dec_ref_known(v___x_2398_, 1);
v_self_2400_ = lean_ctor_get(v_a_2399_, 0);
lean_inc_ref(v_self_2400_);
v___x_2401_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents(v_self_2400_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_, v___y_2387_, v___y_2388_, v___y_2389_, v___y_2390_, v___y_2391_, v___y_2392_);
if (lean_obj_tag(v___x_2401_) == 0)
{
uint8_t v___x_2407_; 
lean_dec_ref_known(v___x_2401_, 1);
v___x_2407_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_2399_);
if (v___x_2407_ == 0)
{
lean_dec(v_a_2399_);
goto v___jp_2402_;
}
else
{
lean_object* v___x_2408_; 
v___x_2408_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc(v_a_2399_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_, v___y_2387_, v___y_2388_, v___y_2389_, v___y_2390_, v___y_2391_, v___y_2392_);
if (lean_obj_tag(v___x_2408_) == 0)
{
lean_dec_ref_known(v___x_2408_, 1);
goto v___jp_2402_;
}
else
{
lean_object* v_a_2409_; lean_object* v___x_2411_; uint8_t v_isShared_2412_; uint8_t v_isSharedCheck_2416_; 
v_a_2409_ = lean_ctor_get(v___x_2408_, 0);
v_isSharedCheck_2416_ = !lean_is_exclusive(v___x_2408_);
if (v_isSharedCheck_2416_ == 0)
{
v___x_2411_ = v___x_2408_;
v_isShared_2412_ = v_isSharedCheck_2416_;
goto v_resetjp_2410_;
}
else
{
lean_inc(v_a_2409_);
lean_dec(v___x_2408_);
v___x_2411_ = lean_box(0);
v_isShared_2412_ = v_isSharedCheck_2416_;
goto v_resetjp_2410_;
}
v_resetjp_2410_:
{
lean_object* v___x_2414_; 
if (v_isShared_2412_ == 0)
{
v___x_2414_ = v___x_2411_;
goto v_reusejp_2413_;
}
else
{
lean_object* v_reuseFailAlloc_2415_; 
v_reuseFailAlloc_2415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2415_, 0, v_a_2409_);
v___x_2414_ = v_reuseFailAlloc_2415_;
goto v_reusejp_2413_;
}
v_reusejp_2413_:
{
return v___x_2414_;
}
}
}
}
v___jp_2402_:
{
lean_object* v___x_2403_; size_t v___x_2404_; size_t v___x_2405_; lean_object* v___x_2406_; 
v___x_2403_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__1_spec__3___closed__0));
v___x_2404_ = ((size_t)1ULL);
v___x_2405_ = lean_usize_add(v_i_2381_, v___x_2404_);
v___x_2406_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__1_spec__3_spec__4(v_as_2379_, v_sz_2380_, v___x_2405_, v___x_2403_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_, v___y_2387_, v___y_2388_, v___y_2389_, v___y_2390_, v___y_2391_, v___y_2392_);
return v___x_2406_;
}
}
else
{
lean_object* v_a_2417_; lean_object* v___x_2419_; uint8_t v_isShared_2420_; uint8_t v_isSharedCheck_2424_; 
lean_dec(v_a_2399_);
v_a_2417_ = lean_ctor_get(v___x_2401_, 0);
v_isSharedCheck_2424_ = !lean_is_exclusive(v___x_2401_);
if (v_isSharedCheck_2424_ == 0)
{
v___x_2419_ = v___x_2401_;
v_isShared_2420_ = v_isSharedCheck_2424_;
goto v_resetjp_2418_;
}
else
{
lean_inc(v_a_2417_);
lean_dec(v___x_2401_);
v___x_2419_ = lean_box(0);
v_isShared_2420_ = v_isSharedCheck_2424_;
goto v_resetjp_2418_;
}
v_resetjp_2418_:
{
lean_object* v___x_2422_; 
if (v_isShared_2420_ == 0)
{
v___x_2422_ = v___x_2419_;
goto v_reusejp_2421_;
}
else
{
lean_object* v_reuseFailAlloc_2423_; 
v_reuseFailAlloc_2423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2423_, 0, v_a_2417_);
v___x_2422_ = v_reuseFailAlloc_2423_;
goto v_reusejp_2421_;
}
v_reusejp_2421_:
{
return v___x_2422_;
}
}
}
}
else
{
lean_object* v_a_2425_; lean_object* v___x_2427_; uint8_t v_isShared_2428_; uint8_t v_isSharedCheck_2432_; 
v_a_2425_ = lean_ctor_get(v___x_2398_, 0);
v_isSharedCheck_2432_ = !lean_is_exclusive(v___x_2398_);
if (v_isSharedCheck_2432_ == 0)
{
v___x_2427_ = v___x_2398_;
v_isShared_2428_ = v_isSharedCheck_2432_;
goto v_resetjp_2426_;
}
else
{
lean_inc(v_a_2425_);
lean_dec(v___x_2398_);
v___x_2427_ = lean_box(0);
v_isShared_2428_ = v_isSharedCheck_2432_;
goto v_resetjp_2426_;
}
v_resetjp_2426_:
{
lean_object* v___x_2430_; 
if (v_isShared_2428_ == 0)
{
v___x_2430_ = v___x_2427_;
goto v_reusejp_2429_;
}
else
{
lean_object* v_reuseFailAlloc_2431_; 
v_reuseFailAlloc_2431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2431_, 0, v_a_2425_);
v___x_2430_ = v_reuseFailAlloc_2431_;
goto v_reusejp_2429_;
}
v_reusejp_2429_:
{
return v___x_2430_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__1_spec__3___boxed(lean_object* v_as_2433_, lean_object* v_sz_2434_, lean_object* v_i_2435_, lean_object* v_b_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_){
_start:
{
size_t v_sz_boxed_2448_; size_t v_i_boxed_2449_; lean_object* v_res_2450_; 
v_sz_boxed_2448_ = lean_unbox_usize(v_sz_2434_);
lean_dec(v_sz_2434_);
v_i_boxed_2449_ = lean_unbox_usize(v_i_2435_);
lean_dec(v_i_2435_);
v_res_2450_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__1_spec__3(v_as_2433_, v_sz_boxed_2448_, v_i_boxed_2449_, v_b_2436_, v___y_2437_, v___y_2438_, v___y_2439_, v___y_2440_, v___y_2441_, v___y_2442_, v___y_2443_, v___y_2444_, v___y_2445_, v___y_2446_);
lean_dec(v___y_2446_);
lean_dec_ref(v___y_2445_);
lean_dec(v___y_2444_);
lean_dec_ref(v___y_2443_);
lean_dec(v___y_2442_);
lean_dec_ref(v___y_2441_);
lean_dec(v___y_2440_);
lean_dec_ref(v___y_2439_);
lean_dec(v___y_2438_);
lean_dec(v___y_2437_);
lean_dec_ref(v_as_2433_);
return v_res_2450_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__1(lean_object* v_init_2451_, lean_object* v_n_2452_, lean_object* v_b_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_){
_start:
{
if (lean_obj_tag(v_n_2452_) == 0)
{
lean_object* v_cs_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; size_t v_sz_2468_; size_t v___x_2469_; lean_object* v___x_2470_; 
v_cs_2465_ = lean_ctor_get(v_n_2452_, 0);
v___x_2466_ = lean_box(0);
v___x_2467_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2467_, 0, v___x_2466_);
lean_ctor_set(v___x_2467_, 1, v_b_2453_);
v_sz_2468_ = lean_array_size(v_cs_2465_);
v___x_2469_ = ((size_t)0ULL);
v___x_2470_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__1_spec__2(v_init_2451_, v_cs_2465_, v_sz_2468_, v___x_2469_, v___x_2467_, v___y_2454_, v___y_2455_, v___y_2456_, v___y_2457_, v___y_2458_, v___y_2459_, v___y_2460_, v___y_2461_, v___y_2462_, v___y_2463_);
if (lean_obj_tag(v___x_2470_) == 0)
{
lean_object* v_a_2471_; lean_object* v___x_2473_; uint8_t v_isShared_2474_; uint8_t v_isSharedCheck_2485_; 
v_a_2471_ = lean_ctor_get(v___x_2470_, 0);
v_isSharedCheck_2485_ = !lean_is_exclusive(v___x_2470_);
if (v_isSharedCheck_2485_ == 0)
{
v___x_2473_ = v___x_2470_;
v_isShared_2474_ = v_isSharedCheck_2485_;
goto v_resetjp_2472_;
}
else
{
lean_inc(v_a_2471_);
lean_dec(v___x_2470_);
v___x_2473_ = lean_box(0);
v_isShared_2474_ = v_isSharedCheck_2485_;
goto v_resetjp_2472_;
}
v_resetjp_2472_:
{
lean_object* v_fst_2475_; 
v_fst_2475_ = lean_ctor_get(v_a_2471_, 0);
if (lean_obj_tag(v_fst_2475_) == 0)
{
lean_object* v_snd_2476_; lean_object* v___x_2477_; lean_object* v___x_2479_; 
v_snd_2476_ = lean_ctor_get(v_a_2471_, 1);
lean_inc(v_snd_2476_);
lean_dec(v_a_2471_);
v___x_2477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2477_, 0, v_snd_2476_);
if (v_isShared_2474_ == 0)
{
lean_ctor_set(v___x_2473_, 0, v___x_2477_);
v___x_2479_ = v___x_2473_;
goto v_reusejp_2478_;
}
else
{
lean_object* v_reuseFailAlloc_2480_; 
v_reuseFailAlloc_2480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2480_, 0, v___x_2477_);
v___x_2479_ = v_reuseFailAlloc_2480_;
goto v_reusejp_2478_;
}
v_reusejp_2478_:
{
return v___x_2479_;
}
}
else
{
lean_object* v_val_2481_; lean_object* v___x_2483_; 
lean_inc_ref(v_fst_2475_);
lean_dec(v_a_2471_);
v_val_2481_ = lean_ctor_get(v_fst_2475_, 0);
lean_inc(v_val_2481_);
lean_dec_ref_known(v_fst_2475_, 1);
if (v_isShared_2474_ == 0)
{
lean_ctor_set(v___x_2473_, 0, v_val_2481_);
v___x_2483_ = v___x_2473_;
goto v_reusejp_2482_;
}
else
{
lean_object* v_reuseFailAlloc_2484_; 
v_reuseFailAlloc_2484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2484_, 0, v_val_2481_);
v___x_2483_ = v_reuseFailAlloc_2484_;
goto v_reusejp_2482_;
}
v_reusejp_2482_:
{
return v___x_2483_;
}
}
}
}
else
{
lean_object* v_a_2486_; lean_object* v___x_2488_; uint8_t v_isShared_2489_; uint8_t v_isSharedCheck_2493_; 
v_a_2486_ = lean_ctor_get(v___x_2470_, 0);
v_isSharedCheck_2493_ = !lean_is_exclusive(v___x_2470_);
if (v_isSharedCheck_2493_ == 0)
{
v___x_2488_ = v___x_2470_;
v_isShared_2489_ = v_isSharedCheck_2493_;
goto v_resetjp_2487_;
}
else
{
lean_inc(v_a_2486_);
lean_dec(v___x_2470_);
v___x_2488_ = lean_box(0);
v_isShared_2489_ = v_isSharedCheck_2493_;
goto v_resetjp_2487_;
}
v_resetjp_2487_:
{
lean_object* v___x_2491_; 
if (v_isShared_2489_ == 0)
{
v___x_2491_ = v___x_2488_;
goto v_reusejp_2490_;
}
else
{
lean_object* v_reuseFailAlloc_2492_; 
v_reuseFailAlloc_2492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2492_, 0, v_a_2486_);
v___x_2491_ = v_reuseFailAlloc_2492_;
goto v_reusejp_2490_;
}
v_reusejp_2490_:
{
return v___x_2491_;
}
}
}
}
else
{
lean_object* v_vs_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; size_t v_sz_2497_; size_t v___x_2498_; lean_object* v___x_2499_; 
v_vs_2494_ = lean_ctor_get(v_n_2452_, 0);
v___x_2495_ = lean_box(0);
v___x_2496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2496_, 0, v___x_2495_);
lean_ctor_set(v___x_2496_, 1, v_b_2453_);
v_sz_2497_ = lean_array_size(v_vs_2494_);
v___x_2498_ = ((size_t)0ULL);
v___x_2499_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__1_spec__3(v_vs_2494_, v_sz_2497_, v___x_2498_, v___x_2496_, v___y_2454_, v___y_2455_, v___y_2456_, v___y_2457_, v___y_2458_, v___y_2459_, v___y_2460_, v___y_2461_, v___y_2462_, v___y_2463_);
if (lean_obj_tag(v___x_2499_) == 0)
{
lean_object* v_a_2500_; lean_object* v___x_2502_; uint8_t v_isShared_2503_; uint8_t v_isSharedCheck_2514_; 
v_a_2500_ = lean_ctor_get(v___x_2499_, 0);
v_isSharedCheck_2514_ = !lean_is_exclusive(v___x_2499_);
if (v_isSharedCheck_2514_ == 0)
{
v___x_2502_ = v___x_2499_;
v_isShared_2503_ = v_isSharedCheck_2514_;
goto v_resetjp_2501_;
}
else
{
lean_inc(v_a_2500_);
lean_dec(v___x_2499_);
v___x_2502_ = lean_box(0);
v_isShared_2503_ = v_isSharedCheck_2514_;
goto v_resetjp_2501_;
}
v_resetjp_2501_:
{
lean_object* v_fst_2504_; 
v_fst_2504_ = lean_ctor_get(v_a_2500_, 0);
if (lean_obj_tag(v_fst_2504_) == 0)
{
lean_object* v_snd_2505_; lean_object* v___x_2506_; lean_object* v___x_2508_; 
v_snd_2505_ = lean_ctor_get(v_a_2500_, 1);
lean_inc(v_snd_2505_);
lean_dec(v_a_2500_);
v___x_2506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2506_, 0, v_snd_2505_);
if (v_isShared_2503_ == 0)
{
lean_ctor_set(v___x_2502_, 0, v___x_2506_);
v___x_2508_ = v___x_2502_;
goto v_reusejp_2507_;
}
else
{
lean_object* v_reuseFailAlloc_2509_; 
v_reuseFailAlloc_2509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2509_, 0, v___x_2506_);
v___x_2508_ = v_reuseFailAlloc_2509_;
goto v_reusejp_2507_;
}
v_reusejp_2507_:
{
return v___x_2508_;
}
}
else
{
lean_object* v_val_2510_; lean_object* v___x_2512_; 
lean_inc_ref(v_fst_2504_);
lean_dec(v_a_2500_);
v_val_2510_ = lean_ctor_get(v_fst_2504_, 0);
lean_inc(v_val_2510_);
lean_dec_ref_known(v_fst_2504_, 1);
if (v_isShared_2503_ == 0)
{
lean_ctor_set(v___x_2502_, 0, v_val_2510_);
v___x_2512_ = v___x_2502_;
goto v_reusejp_2511_;
}
else
{
lean_object* v_reuseFailAlloc_2513_; 
v_reuseFailAlloc_2513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2513_, 0, v_val_2510_);
v___x_2512_ = v_reuseFailAlloc_2513_;
goto v_reusejp_2511_;
}
v_reusejp_2511_:
{
return v___x_2512_;
}
}
}
}
else
{
lean_object* v_a_2515_; lean_object* v___x_2517_; uint8_t v_isShared_2518_; uint8_t v_isSharedCheck_2522_; 
v_a_2515_ = lean_ctor_get(v___x_2499_, 0);
v_isSharedCheck_2522_ = !lean_is_exclusive(v___x_2499_);
if (v_isSharedCheck_2522_ == 0)
{
v___x_2517_ = v___x_2499_;
v_isShared_2518_ = v_isSharedCheck_2522_;
goto v_resetjp_2516_;
}
else
{
lean_inc(v_a_2515_);
lean_dec(v___x_2499_);
v___x_2517_ = lean_box(0);
v_isShared_2518_ = v_isSharedCheck_2522_;
goto v_resetjp_2516_;
}
v_resetjp_2516_:
{
lean_object* v___x_2520_; 
if (v_isShared_2518_ == 0)
{
v___x_2520_ = v___x_2517_;
goto v_reusejp_2519_;
}
else
{
lean_object* v_reuseFailAlloc_2521_; 
v_reuseFailAlloc_2521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2521_, 0, v_a_2515_);
v___x_2520_ = v_reuseFailAlloc_2521_;
goto v_reusejp_2519_;
}
v_reusejp_2519_:
{
return v___x_2520_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__1_spec__2(lean_object* v_init_2523_, lean_object* v_as_2524_, size_t v_sz_2525_, size_t v_i_2526_, lean_object* v_b_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_){
_start:
{
uint8_t v___x_2539_; 
v___x_2539_ = lean_usize_dec_lt(v_i_2526_, v_sz_2525_);
if (v___x_2539_ == 0)
{
lean_object* v___x_2540_; 
v___x_2540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2540_, 0, v_b_2527_);
return v___x_2540_;
}
else
{
lean_object* v_snd_2541_; lean_object* v___x_2543_; uint8_t v_isShared_2544_; uint8_t v_isSharedCheck_2575_; 
v_snd_2541_ = lean_ctor_get(v_b_2527_, 1);
v_isSharedCheck_2575_ = !lean_is_exclusive(v_b_2527_);
if (v_isSharedCheck_2575_ == 0)
{
lean_object* v_unused_2576_; 
v_unused_2576_ = lean_ctor_get(v_b_2527_, 0);
lean_dec(v_unused_2576_);
v___x_2543_ = v_b_2527_;
v_isShared_2544_ = v_isSharedCheck_2575_;
goto v_resetjp_2542_;
}
else
{
lean_inc(v_snd_2541_);
lean_dec(v_b_2527_);
v___x_2543_ = lean_box(0);
v_isShared_2544_ = v_isSharedCheck_2575_;
goto v_resetjp_2542_;
}
v_resetjp_2542_:
{
lean_object* v_a_2545_; lean_object* v___x_2546_; 
v_a_2545_ = lean_array_uget_borrowed(v_as_2524_, v_i_2526_);
lean_inc(v_snd_2541_);
v___x_2546_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__1(v_init_2523_, v_a_2545_, v_snd_2541_, v___y_2528_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_, v___y_2536_, v___y_2537_);
if (lean_obj_tag(v___x_2546_) == 0)
{
lean_object* v_a_2547_; lean_object* v___x_2549_; uint8_t v_isShared_2550_; uint8_t v_isSharedCheck_2566_; 
v_a_2547_ = lean_ctor_get(v___x_2546_, 0);
v_isSharedCheck_2566_ = !lean_is_exclusive(v___x_2546_);
if (v_isSharedCheck_2566_ == 0)
{
v___x_2549_ = v___x_2546_;
v_isShared_2550_ = v_isSharedCheck_2566_;
goto v_resetjp_2548_;
}
else
{
lean_inc(v_a_2547_);
lean_dec(v___x_2546_);
v___x_2549_ = lean_box(0);
v_isShared_2550_ = v_isSharedCheck_2566_;
goto v_resetjp_2548_;
}
v_resetjp_2548_:
{
if (lean_obj_tag(v_a_2547_) == 0)
{
lean_object* v___x_2551_; lean_object* v___x_2553_; 
v___x_2551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2551_, 0, v_a_2547_);
if (v_isShared_2544_ == 0)
{
lean_ctor_set(v___x_2543_, 0, v___x_2551_);
v___x_2553_ = v___x_2543_;
goto v_reusejp_2552_;
}
else
{
lean_object* v_reuseFailAlloc_2557_; 
v_reuseFailAlloc_2557_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2557_, 0, v___x_2551_);
lean_ctor_set(v_reuseFailAlloc_2557_, 1, v_snd_2541_);
v___x_2553_ = v_reuseFailAlloc_2557_;
goto v_reusejp_2552_;
}
v_reusejp_2552_:
{
lean_object* v___x_2555_; 
if (v_isShared_2550_ == 0)
{
lean_ctor_set(v___x_2549_, 0, v___x_2553_);
v___x_2555_ = v___x_2549_;
goto v_reusejp_2554_;
}
else
{
lean_object* v_reuseFailAlloc_2556_; 
v_reuseFailAlloc_2556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2556_, 0, v___x_2553_);
v___x_2555_ = v_reuseFailAlloc_2556_;
goto v_reusejp_2554_;
}
v_reusejp_2554_:
{
return v___x_2555_;
}
}
}
else
{
lean_object* v_a_2558_; lean_object* v___x_2559_; lean_object* v___x_2561_; 
lean_del_object(v___x_2549_);
lean_dec(v_snd_2541_);
v_a_2558_ = lean_ctor_get(v_a_2547_, 0);
lean_inc(v_a_2558_);
lean_dec_ref_known(v_a_2547_, 1);
v___x_2559_ = lean_box(0);
if (v_isShared_2544_ == 0)
{
lean_ctor_set(v___x_2543_, 1, v_a_2558_);
lean_ctor_set(v___x_2543_, 0, v___x_2559_);
v___x_2561_ = v___x_2543_;
goto v_reusejp_2560_;
}
else
{
lean_object* v_reuseFailAlloc_2565_; 
v_reuseFailAlloc_2565_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2565_, 0, v___x_2559_);
lean_ctor_set(v_reuseFailAlloc_2565_, 1, v_a_2558_);
v___x_2561_ = v_reuseFailAlloc_2565_;
goto v_reusejp_2560_;
}
v_reusejp_2560_:
{
size_t v___x_2562_; size_t v___x_2563_; 
v___x_2562_ = ((size_t)1ULL);
v___x_2563_ = lean_usize_add(v_i_2526_, v___x_2562_);
v_i_2526_ = v___x_2563_;
v_b_2527_ = v___x_2561_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_2567_; lean_object* v___x_2569_; uint8_t v_isShared_2570_; uint8_t v_isSharedCheck_2574_; 
lean_del_object(v___x_2543_);
lean_dec(v_snd_2541_);
v_a_2567_ = lean_ctor_get(v___x_2546_, 0);
v_isSharedCheck_2574_ = !lean_is_exclusive(v___x_2546_);
if (v_isSharedCheck_2574_ == 0)
{
v___x_2569_ = v___x_2546_;
v_isShared_2570_ = v_isSharedCheck_2574_;
goto v_resetjp_2568_;
}
else
{
lean_inc(v_a_2567_);
lean_dec(v___x_2546_);
v___x_2569_ = lean_box(0);
v_isShared_2570_ = v_isSharedCheck_2574_;
goto v_resetjp_2568_;
}
v_resetjp_2568_:
{
lean_object* v___x_2572_; 
if (v_isShared_2570_ == 0)
{
v___x_2572_ = v___x_2569_;
goto v_reusejp_2571_;
}
else
{
lean_object* v_reuseFailAlloc_2573_; 
v_reuseFailAlloc_2573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2573_, 0, v_a_2567_);
v___x_2572_ = v_reuseFailAlloc_2573_;
goto v_reusejp_2571_;
}
v_reusejp_2571_:
{
return v___x_2572_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__1_spec__2___boxed(lean_object* v_init_2577_, lean_object* v_as_2578_, lean_object* v_sz_2579_, lean_object* v_i_2580_, lean_object* v_b_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_, lean_object* v___y_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_){
_start:
{
size_t v_sz_boxed_2593_; size_t v_i_boxed_2594_; lean_object* v_res_2595_; 
v_sz_boxed_2593_ = lean_unbox_usize(v_sz_2579_);
lean_dec(v_sz_2579_);
v_i_boxed_2594_ = lean_unbox_usize(v_i_2580_);
lean_dec(v_i_2580_);
v_res_2595_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__1_spec__2(v_init_2577_, v_as_2578_, v_sz_boxed_2593_, v_i_boxed_2594_, v_b_2581_, v___y_2582_, v___y_2583_, v___y_2584_, v___y_2585_, v___y_2586_, v___y_2587_, v___y_2588_, v___y_2589_, v___y_2590_, v___y_2591_);
lean_dec(v___y_2591_);
lean_dec_ref(v___y_2590_);
lean_dec(v___y_2589_);
lean_dec_ref(v___y_2588_);
lean_dec(v___y_2587_);
lean_dec_ref(v___y_2586_);
lean_dec(v___y_2585_);
lean_dec_ref(v___y_2584_);
lean_dec(v___y_2583_);
lean_dec(v___y_2582_);
lean_dec_ref(v_as_2578_);
return v_res_2595_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__1___boxed(lean_object* v_init_2596_, lean_object* v_n_2597_, lean_object* v_b_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_){
_start:
{
lean_object* v_res_2610_; 
v_res_2610_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__1(v_init_2596_, v_n_2597_, v_b_2598_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_, v___y_2607_, v___y_2608_);
lean_dec(v___y_2608_);
lean_dec_ref(v___y_2607_);
lean_dec(v___y_2606_);
lean_dec_ref(v___y_2605_);
lean_dec(v___y_2604_);
lean_dec_ref(v___y_2603_);
lean_dec(v___y_2602_);
lean_dec_ref(v___y_2601_);
lean_dec(v___y_2600_);
lean_dec(v___y_2599_);
lean_dec_ref(v_n_2597_);
return v_res_2610_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1(lean_object* v_t_2611_, lean_object* v_init_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_){
_start:
{
lean_object* v_root_2624_; lean_object* v_tail_2625_; lean_object* v___x_2626_; 
v_root_2624_ = lean_ctor_get(v_t_2611_, 0);
v_tail_2625_ = lean_ctor_get(v_t_2611_, 1);
v___x_2626_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__1(v_init_2612_, v_root_2624_, v_init_2612_, v___y_2613_, v___y_2614_, v___y_2615_, v___y_2616_, v___y_2617_, v___y_2618_, v___y_2619_, v___y_2620_, v___y_2621_, v___y_2622_);
if (lean_obj_tag(v___x_2626_) == 0)
{
lean_object* v_a_2627_; lean_object* v___x_2629_; uint8_t v_isShared_2630_; uint8_t v_isSharedCheck_2663_; 
v_a_2627_ = lean_ctor_get(v___x_2626_, 0);
v_isSharedCheck_2663_ = !lean_is_exclusive(v___x_2626_);
if (v_isSharedCheck_2663_ == 0)
{
v___x_2629_ = v___x_2626_;
v_isShared_2630_ = v_isSharedCheck_2663_;
goto v_resetjp_2628_;
}
else
{
lean_inc(v_a_2627_);
lean_dec(v___x_2626_);
v___x_2629_ = lean_box(0);
v_isShared_2630_ = v_isSharedCheck_2663_;
goto v_resetjp_2628_;
}
v_resetjp_2628_:
{
if (lean_obj_tag(v_a_2627_) == 0)
{
lean_object* v_a_2631_; lean_object* v___x_2633_; 
v_a_2631_ = lean_ctor_get(v_a_2627_, 0);
lean_inc(v_a_2631_);
lean_dec_ref_known(v_a_2627_, 1);
if (v_isShared_2630_ == 0)
{
lean_ctor_set(v___x_2629_, 0, v_a_2631_);
v___x_2633_ = v___x_2629_;
goto v_reusejp_2632_;
}
else
{
lean_object* v_reuseFailAlloc_2634_; 
v_reuseFailAlloc_2634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2634_, 0, v_a_2631_);
v___x_2633_ = v_reuseFailAlloc_2634_;
goto v_reusejp_2632_;
}
v_reusejp_2632_:
{
return v___x_2633_;
}
}
else
{
lean_object* v_a_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; size_t v_sz_2638_; size_t v___x_2639_; lean_object* v___x_2640_; 
lean_del_object(v___x_2629_);
v_a_2635_ = lean_ctor_get(v_a_2627_, 0);
lean_inc(v_a_2635_);
lean_dec_ref_known(v_a_2627_, 1);
v___x_2636_ = lean_box(0);
v___x_2637_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2637_, 0, v___x_2636_);
lean_ctor_set(v___x_2637_, 1, v_a_2635_);
v_sz_2638_ = lean_array_size(v_tail_2625_);
v___x_2639_ = ((size_t)0ULL);
v___x_2640_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__2(v_tail_2625_, v_sz_2638_, v___x_2639_, v___x_2637_, v___y_2613_, v___y_2614_, v___y_2615_, v___y_2616_, v___y_2617_, v___y_2618_, v___y_2619_, v___y_2620_, v___y_2621_, v___y_2622_);
if (lean_obj_tag(v___x_2640_) == 0)
{
lean_object* v_a_2641_; lean_object* v___x_2643_; uint8_t v_isShared_2644_; uint8_t v_isSharedCheck_2654_; 
v_a_2641_ = lean_ctor_get(v___x_2640_, 0);
v_isSharedCheck_2654_ = !lean_is_exclusive(v___x_2640_);
if (v_isSharedCheck_2654_ == 0)
{
v___x_2643_ = v___x_2640_;
v_isShared_2644_ = v_isSharedCheck_2654_;
goto v_resetjp_2642_;
}
else
{
lean_inc(v_a_2641_);
lean_dec(v___x_2640_);
v___x_2643_ = lean_box(0);
v_isShared_2644_ = v_isSharedCheck_2654_;
goto v_resetjp_2642_;
}
v_resetjp_2642_:
{
lean_object* v_fst_2645_; 
v_fst_2645_ = lean_ctor_get(v_a_2641_, 0);
if (lean_obj_tag(v_fst_2645_) == 0)
{
lean_object* v_snd_2646_; lean_object* v___x_2648_; 
v_snd_2646_ = lean_ctor_get(v_a_2641_, 1);
lean_inc(v_snd_2646_);
lean_dec(v_a_2641_);
if (v_isShared_2644_ == 0)
{
lean_ctor_set(v___x_2643_, 0, v_snd_2646_);
v___x_2648_ = v___x_2643_;
goto v_reusejp_2647_;
}
else
{
lean_object* v_reuseFailAlloc_2649_; 
v_reuseFailAlloc_2649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2649_, 0, v_snd_2646_);
v___x_2648_ = v_reuseFailAlloc_2649_;
goto v_reusejp_2647_;
}
v_reusejp_2647_:
{
return v___x_2648_;
}
}
else
{
lean_object* v_val_2650_; lean_object* v___x_2652_; 
lean_inc_ref(v_fst_2645_);
lean_dec(v_a_2641_);
v_val_2650_ = lean_ctor_get(v_fst_2645_, 0);
lean_inc(v_val_2650_);
lean_dec_ref_known(v_fst_2645_, 1);
if (v_isShared_2644_ == 0)
{
lean_ctor_set(v___x_2643_, 0, v_val_2650_);
v___x_2652_ = v___x_2643_;
goto v_reusejp_2651_;
}
else
{
lean_object* v_reuseFailAlloc_2653_; 
v_reuseFailAlloc_2653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2653_, 0, v_val_2650_);
v___x_2652_ = v_reuseFailAlloc_2653_;
goto v_reusejp_2651_;
}
v_reusejp_2651_:
{
return v___x_2652_;
}
}
}
}
else
{
lean_object* v_a_2655_; lean_object* v___x_2657_; uint8_t v_isShared_2658_; uint8_t v_isSharedCheck_2662_; 
v_a_2655_ = lean_ctor_get(v___x_2640_, 0);
v_isSharedCheck_2662_ = !lean_is_exclusive(v___x_2640_);
if (v_isSharedCheck_2662_ == 0)
{
v___x_2657_ = v___x_2640_;
v_isShared_2658_ = v_isSharedCheck_2662_;
goto v_resetjp_2656_;
}
else
{
lean_inc(v_a_2655_);
lean_dec(v___x_2640_);
v___x_2657_ = lean_box(0);
v_isShared_2658_ = v_isSharedCheck_2662_;
goto v_resetjp_2656_;
}
v_resetjp_2656_:
{
lean_object* v___x_2660_; 
if (v_isShared_2658_ == 0)
{
v___x_2660_ = v___x_2657_;
goto v_reusejp_2659_;
}
else
{
lean_object* v_reuseFailAlloc_2661_; 
v_reuseFailAlloc_2661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2661_, 0, v_a_2655_);
v___x_2660_ = v_reuseFailAlloc_2661_;
goto v_reusejp_2659_;
}
v_reusejp_2659_:
{
return v___x_2660_;
}
}
}
}
}
}
else
{
lean_object* v_a_2664_; lean_object* v___x_2666_; uint8_t v_isShared_2667_; uint8_t v_isSharedCheck_2671_; 
v_a_2664_ = lean_ctor_get(v___x_2626_, 0);
v_isSharedCheck_2671_ = !lean_is_exclusive(v___x_2626_);
if (v_isSharedCheck_2671_ == 0)
{
v___x_2666_ = v___x_2626_;
v_isShared_2667_ = v_isSharedCheck_2671_;
goto v_resetjp_2665_;
}
else
{
lean_inc(v_a_2664_);
lean_dec(v___x_2626_);
v___x_2666_ = lean_box(0);
v_isShared_2667_ = v_isSharedCheck_2671_;
goto v_resetjp_2665_;
}
v_resetjp_2665_:
{
lean_object* v___x_2669_; 
if (v_isShared_2667_ == 0)
{
v___x_2669_ = v___x_2666_;
goto v_reusejp_2668_;
}
else
{
lean_object* v_reuseFailAlloc_2670_; 
v_reuseFailAlloc_2670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2670_, 0, v_a_2664_);
v___x_2669_ = v_reuseFailAlloc_2670_;
goto v_reusejp_2668_;
}
v_reusejp_2668_:
{
return v___x_2669_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1___boxed(lean_object* v_t_2672_, lean_object* v_init_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_){
_start:
{
lean_object* v_res_2685_; 
v_res_2685_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1(v_t_2672_, v_init_2673_, v___y_2674_, v___y_2675_, v___y_2676_, v___y_2677_, v___y_2678_, v___y_2679_, v___y_2680_, v___y_2681_, v___y_2682_, v___y_2683_);
lean_dec(v___y_2683_);
lean_dec_ref(v___y_2682_);
lean_dec(v___y_2681_);
lean_dec_ref(v___y_2680_);
lean_dec(v___y_2679_);
lean_dec_ref(v___y_2678_);
lean_dec(v___y_2677_);
lean_dec_ref(v___y_2676_);
lean_dec(v___y_2675_);
lean_dec(v___y_2674_);
lean_dec_ref(v_t_2672_);
return v_res_2685_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_checkInvariants(uint8_t v_expensive_2686_, lean_object* v_a_2687_, lean_object* v_a_2688_, lean_object* v_a_2689_, lean_object* v_a_2690_, lean_object* v_a_2691_, lean_object* v_a_2692_, lean_object* v_a_2693_, lean_object* v_a_2694_, lean_object* v_a_2695_, lean_object* v_a_2696_){
_start:
{
lean_object* v___y_2702_; lean_object* v___y_2703_; lean_object* v___y_2704_; lean_object* v___y_2705_; lean_object* v___y_2706_; lean_object* v___y_2707_; lean_object* v___y_2708_; lean_object* v___y_2709_; lean_object* v___y_2710_; lean_object* v___y_2711_; lean_object* v___y_2717_; lean_object* v___y_2718_; lean_object* v___y_2719_; lean_object* v___y_2720_; lean_object* v___y_2721_; lean_object* v___y_2722_; lean_object* v___y_2723_; lean_object* v___y_2724_; lean_object* v___y_2725_; lean_object* v___y_2726_; uint8_t v_debug_2728_; 
v_debug_2728_ = lean_ctor_get_uint8(v_a_2689_, sizeof(void*)*8 + 2);
if (v_debug_2728_ == 0)
{
v___y_2702_ = v_a_2687_;
v___y_2703_ = v_a_2688_;
v___y_2704_ = v_a_2689_;
v___y_2705_ = v_a_2690_;
v___y_2706_ = v_a_2691_;
v___y_2707_ = v_a_2692_;
v___y_2708_ = v_a_2693_;
v___y_2709_ = v_a_2694_;
v___y_2710_ = v_a_2695_;
v___y_2711_ = v_a_2696_;
goto v___jp_2701_;
}
else
{
lean_object* v___x_2729_; 
v___x_2729_ = l_Lean_Meta_Grind_getExprs___redArg(v_a_2687_);
if (lean_obj_tag(v___x_2729_) == 0)
{
lean_object* v_a_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; 
v_a_2730_ = lean_ctor_get(v___x_2729_, 0);
lean_inc(v_a_2730_);
lean_dec_ref_known(v___x_2729_, 1);
v___x_2731_ = lean_box(0);
v___x_2732_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1(v_a_2730_, v___x_2731_, v_a_2687_, v_a_2688_, v_a_2689_, v_a_2690_, v_a_2691_, v_a_2692_, v_a_2693_, v_a_2694_, v_a_2695_, v_a_2696_);
lean_dec(v_a_2730_);
if (lean_obj_tag(v___x_2732_) == 0)
{
lean_dec_ref_known(v___x_2732_, 1);
if (v_expensive_2686_ == 0)
{
v___y_2717_ = v_a_2687_;
v___y_2718_ = v_a_2688_;
v___y_2719_ = v_a_2689_;
v___y_2720_ = v_a_2690_;
v___y_2721_ = v_a_2691_;
v___y_2722_ = v_a_2692_;
v___y_2723_ = v_a_2693_;
v___y_2724_ = v_a_2694_;
v___y_2725_ = v_a_2695_;
v___y_2726_ = v_a_2696_;
goto v___jp_2716_;
}
else
{
lean_object* v___x_2733_; 
v___x_2733_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq(v_a_2687_, v_a_2688_, v_a_2689_, v_a_2690_, v_a_2691_, v_a_2692_, v_a_2693_, v_a_2694_, v_a_2695_, v_a_2696_);
if (lean_obj_tag(v___x_2733_) == 0)
{
lean_dec_ref_known(v___x_2733_, 1);
v___y_2717_ = v_a_2687_;
v___y_2718_ = v_a_2688_;
v___y_2719_ = v_a_2689_;
v___y_2720_ = v_a_2690_;
v___y_2721_ = v_a_2691_;
v___y_2722_ = v_a_2692_;
v___y_2723_ = v_a_2693_;
v___y_2724_ = v_a_2694_;
v___y_2725_ = v_a_2695_;
v___y_2726_ = v_a_2696_;
goto v___jp_2716_;
}
else
{
return v___x_2733_;
}
}
}
else
{
return v___x_2732_;
}
}
else
{
lean_object* v_a_2734_; lean_object* v___x_2736_; uint8_t v_isShared_2737_; uint8_t v_isSharedCheck_2741_; 
v_a_2734_ = lean_ctor_get(v___x_2729_, 0);
v_isSharedCheck_2741_ = !lean_is_exclusive(v___x_2729_);
if (v_isSharedCheck_2741_ == 0)
{
v___x_2736_ = v___x_2729_;
v_isShared_2737_ = v_isSharedCheck_2741_;
goto v_resetjp_2735_;
}
else
{
lean_inc(v_a_2734_);
lean_dec(v___x_2729_);
v___x_2736_ = lean_box(0);
v_isShared_2737_ = v_isSharedCheck_2741_;
goto v_resetjp_2735_;
}
v_resetjp_2735_:
{
lean_object* v___x_2739_; 
if (v_isShared_2737_ == 0)
{
v___x_2739_ = v___x_2736_;
goto v_reusejp_2738_;
}
else
{
lean_object* v_reuseFailAlloc_2740_; 
v_reuseFailAlloc_2740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2740_, 0, v_a_2734_);
v___x_2739_ = v_reuseFailAlloc_2740_;
goto v_reusejp_2738_;
}
v_reusejp_2738_:
{
return v___x_2739_;
}
}
}
}
v___jp_2698_:
{
lean_object* v___x_2699_; lean_object* v___x_2700_; 
v___x_2699_ = lean_box(0);
v___x_2700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2700_, 0, v___x_2699_);
return v___x_2700_;
}
v___jp_2701_:
{
if (v_expensive_2686_ == 0)
{
goto v___jp_2698_;
}
else
{
lean_object* v_options_2712_; lean_object* v___x_2713_; uint8_t v___x_2714_; 
v_options_2712_ = lean_ctor_get(v___y_2710_, 2);
v___x_2713_ = l_Lean_Meta_Grind_grind_debug_proofs;
v___x_2714_ = l_Lean_Option_get___at___00Lean_Meta_Grind_checkInvariants_spec__0(v_options_2712_, v___x_2713_);
if (v___x_2714_ == 0)
{
goto v___jp_2698_;
}
else
{
lean_object* v___x_2715_; 
v___x_2715_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs(v___y_2702_, v___y_2703_, v___y_2704_, v___y_2705_, v___y_2706_, v___y_2707_, v___y_2708_, v___y_2709_, v___y_2710_, v___y_2711_);
return v___x_2715_;
}
}
}
v___jp_2716_:
{
lean_object* v___x_2727_; 
v___x_2727_ = l_Lean_Meta_Grind_Solvers_checkInvariants(v___y_2717_, v___y_2718_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_, v___y_2723_, v___y_2724_, v___y_2725_, v___y_2726_);
if (lean_obj_tag(v___x_2727_) == 0)
{
lean_dec_ref_known(v___x_2727_, 1);
v___y_2702_ = v___y_2717_;
v___y_2703_ = v___y_2718_;
v___y_2704_ = v___y_2719_;
v___y_2705_ = v___y_2720_;
v___y_2706_ = v___y_2721_;
v___y_2707_ = v___y_2722_;
v___y_2708_ = v___y_2723_;
v___y_2709_ = v___y_2724_;
v___y_2710_ = v___y_2725_;
v___y_2711_ = v___y_2726_;
goto v___jp_2701_;
}
else
{
return v___x_2727_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_checkInvariants___boxed(lean_object* v_expensive_2742_, lean_object* v_a_2743_, lean_object* v_a_2744_, lean_object* v_a_2745_, lean_object* v_a_2746_, lean_object* v_a_2747_, lean_object* v_a_2748_, lean_object* v_a_2749_, lean_object* v_a_2750_, lean_object* v_a_2751_, lean_object* v_a_2752_, lean_object* v_a_2753_){
_start:
{
uint8_t v_expensive_boxed_2754_; lean_object* v_res_2755_; 
v_expensive_boxed_2754_ = lean_unbox(v_expensive_2742_);
v_res_2755_ = l_Lean_Meta_Grind_checkInvariants(v_expensive_boxed_2754_, v_a_2743_, v_a_2744_, v_a_2745_, v_a_2746_, v_a_2747_, v_a_2748_, v_a_2749_, v_a_2750_, v_a_2751_, v_a_2752_);
lean_dec(v_a_2752_);
lean_dec_ref(v_a_2751_);
lean_dec(v_a_2750_);
lean_dec_ref(v_a_2749_);
lean_dec(v_a_2748_);
lean_dec_ref(v_a_2747_);
lean_dec(v_a_2746_);
lean_dec_ref(v_a_2745_);
lean_dec(v_a_2744_);
lean_dec(v_a_2743_);
return v_res_2755_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Goal_checkInvariants_spec__0___redArg___lam__0(lean_object* v_x_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_, lean_object* v___y_2764_, lean_object* v___y_2765_){
_start:
{
lean_object* v___x_2767_; 
lean_inc(v___y_2761_);
lean_inc_ref(v___y_2760_);
lean_inc(v___y_2759_);
lean_inc_ref(v___y_2758_);
lean_inc(v___y_2757_);
v___x_2767_ = lean_apply_10(v_x_2756_, v___y_2757_, v___y_2758_, v___y_2759_, v___y_2760_, v___y_2761_, v___y_2762_, v___y_2763_, v___y_2764_, v___y_2765_, lean_box(0));
return v___x_2767_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Goal_checkInvariants_spec__0___redArg___lam__0___boxed(lean_object* v_x_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_){
_start:
{
lean_object* v_res_2779_; 
v_res_2779_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Goal_checkInvariants_spec__0___redArg___lam__0(v_x_2768_, v___y_2769_, v___y_2770_, v___y_2771_, v___y_2772_, v___y_2773_, v___y_2774_, v___y_2775_, v___y_2776_, v___y_2777_);
lean_dec(v___y_2773_);
lean_dec_ref(v___y_2772_);
lean_dec(v___y_2771_);
lean_dec_ref(v___y_2770_);
lean_dec(v___y_2769_);
return v_res_2779_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Goal_checkInvariants_spec__0___redArg(lean_object* v_mvarId_2780_, lean_object* v_x_2781_, lean_object* v___y_2782_, lean_object* v___y_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_, lean_object* v___y_2787_, lean_object* v___y_2788_, lean_object* v___y_2789_, lean_object* v___y_2790_){
_start:
{
lean_object* v___f_2792_; lean_object* v___x_2793_; 
lean_inc(v___y_2786_);
lean_inc_ref(v___y_2785_);
lean_inc(v___y_2784_);
lean_inc_ref(v___y_2783_);
lean_inc(v___y_2782_);
v___f_2792_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Goal_checkInvariants_spec__0___redArg___lam__0___boxed), 11, 6);
lean_closure_set(v___f_2792_, 0, v_x_2781_);
lean_closure_set(v___f_2792_, 1, v___y_2782_);
lean_closure_set(v___f_2792_, 2, v___y_2783_);
lean_closure_set(v___f_2792_, 3, v___y_2784_);
lean_closure_set(v___f_2792_, 4, v___y_2785_);
lean_closure_set(v___f_2792_, 5, v___y_2786_);
v___x_2793_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_2780_, v___f_2792_, v___y_2787_, v___y_2788_, v___y_2789_, v___y_2790_);
if (lean_obj_tag(v___x_2793_) == 0)
{
return v___x_2793_;
}
else
{
lean_object* v_a_2794_; lean_object* v___x_2796_; uint8_t v_isShared_2797_; uint8_t v_isSharedCheck_2801_; 
v_a_2794_ = lean_ctor_get(v___x_2793_, 0);
v_isSharedCheck_2801_ = !lean_is_exclusive(v___x_2793_);
if (v_isSharedCheck_2801_ == 0)
{
v___x_2796_ = v___x_2793_;
v_isShared_2797_ = v_isSharedCheck_2801_;
goto v_resetjp_2795_;
}
else
{
lean_inc(v_a_2794_);
lean_dec(v___x_2793_);
v___x_2796_ = lean_box(0);
v_isShared_2797_ = v_isSharedCheck_2801_;
goto v_resetjp_2795_;
}
v_resetjp_2795_:
{
lean_object* v___x_2799_; 
if (v_isShared_2797_ == 0)
{
v___x_2799_ = v___x_2796_;
goto v_reusejp_2798_;
}
else
{
lean_object* v_reuseFailAlloc_2800_; 
v_reuseFailAlloc_2800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2800_, 0, v_a_2794_);
v___x_2799_ = v_reuseFailAlloc_2800_;
goto v_reusejp_2798_;
}
v_reusejp_2798_:
{
return v___x_2799_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Goal_checkInvariants_spec__0___redArg___boxed(lean_object* v_mvarId_2802_, lean_object* v_x_2803_, lean_object* v___y_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_, lean_object* v___y_2807_, lean_object* v___y_2808_, lean_object* v___y_2809_, lean_object* v___y_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_){
_start:
{
lean_object* v_res_2814_; 
v_res_2814_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Goal_checkInvariants_spec__0___redArg(v_mvarId_2802_, v_x_2803_, v___y_2804_, v___y_2805_, v___y_2806_, v___y_2807_, v___y_2808_, v___y_2809_, v___y_2810_, v___y_2811_, v___y_2812_);
lean_dec(v___y_2812_);
lean_dec_ref(v___y_2811_);
lean_dec(v___y_2810_);
lean_dec_ref(v___y_2809_);
lean_dec(v___y_2808_);
lean_dec_ref(v___y_2807_);
lean_dec(v___y_2806_);
lean_dec_ref(v___y_2805_);
lean_dec(v___y_2804_);
return v_res_2814_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Goal_checkInvariants_spec__0(lean_object* v_00_u03b1_2815_, lean_object* v_mvarId_2816_, lean_object* v_x_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_){
_start:
{
lean_object* v___x_2828_; 
v___x_2828_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Goal_checkInvariants_spec__0___redArg(v_mvarId_2816_, v_x_2817_, v___y_2818_, v___y_2819_, v___y_2820_, v___y_2821_, v___y_2822_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_);
return v___x_2828_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Goal_checkInvariants_spec__0___boxed(lean_object* v_00_u03b1_2829_, lean_object* v_mvarId_2830_, lean_object* v_x_2831_, lean_object* v___y_2832_, lean_object* v___y_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_){
_start:
{
lean_object* v_res_2842_; 
v_res_2842_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Goal_checkInvariants_spec__0(v_00_u03b1_2829_, v_mvarId_2830_, v_x_2831_, v___y_2832_, v___y_2833_, v___y_2834_, v___y_2835_, v___y_2836_, v___y_2837_, v___y_2838_, v___y_2839_, v___y_2840_);
lean_dec(v___y_2840_);
lean_dec_ref(v___y_2839_);
lean_dec(v___y_2838_);
lean_dec_ref(v___y_2837_);
lean_dec(v___y_2836_);
lean_dec_ref(v___y_2835_);
lean_dec(v___y_2834_);
lean_dec_ref(v___y_2833_);
lean_dec(v___y_2832_);
return v_res_2842_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Goal_checkInvariants___lam__0(lean_object* v_goal_2843_, uint8_t v_expensive_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_, lean_object* v___y_2847_, lean_object* v___y_2848_, lean_object* v___y_2849_, lean_object* v___y_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_, lean_object* v___y_2853_){
_start:
{
lean_object* v___x_2855_; lean_object* v___x_2856_; 
v___x_2855_ = lean_st_mk_ref(v_goal_2843_);
v___x_2856_ = l_Lean_Meta_Grind_checkInvariants(v_expensive_2844_, v___x_2855_, v___y_2845_, v___y_2846_, v___y_2847_, v___y_2848_, v___y_2849_, v___y_2850_, v___y_2851_, v___y_2852_, v___y_2853_);
if (lean_obj_tag(v___x_2856_) == 0)
{
lean_object* v___x_2858_; uint8_t v_isShared_2859_; uint8_t v_isSharedCheck_2865_; 
v_isSharedCheck_2865_ = !lean_is_exclusive(v___x_2856_);
if (v_isSharedCheck_2865_ == 0)
{
lean_object* v_unused_2866_; 
v_unused_2866_ = lean_ctor_get(v___x_2856_, 0);
lean_dec(v_unused_2866_);
v___x_2858_ = v___x_2856_;
v_isShared_2859_ = v_isSharedCheck_2865_;
goto v_resetjp_2857_;
}
else
{
lean_dec(v___x_2856_);
v___x_2858_ = lean_box(0);
v_isShared_2859_ = v_isSharedCheck_2865_;
goto v_resetjp_2857_;
}
v_resetjp_2857_:
{
lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2863_; 
v___x_2860_ = lean_st_ref_get(v___x_2855_);
v___x_2861_ = lean_st_ref_get(v___x_2855_);
lean_dec(v___x_2855_);
lean_dec(v___x_2861_);
if (v_isShared_2859_ == 0)
{
lean_ctor_set(v___x_2858_, 0, v___x_2860_);
v___x_2863_ = v___x_2858_;
goto v_reusejp_2862_;
}
else
{
lean_object* v_reuseFailAlloc_2864_; 
v_reuseFailAlloc_2864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2864_, 0, v___x_2860_);
v___x_2863_ = v_reuseFailAlloc_2864_;
goto v_reusejp_2862_;
}
v_reusejp_2862_:
{
return v___x_2863_;
}
}
}
else
{
lean_object* v_a_2867_; lean_object* v___x_2869_; uint8_t v_isShared_2870_; uint8_t v_isSharedCheck_2874_; 
lean_dec(v___x_2855_);
v_a_2867_ = lean_ctor_get(v___x_2856_, 0);
v_isSharedCheck_2874_ = !lean_is_exclusive(v___x_2856_);
if (v_isSharedCheck_2874_ == 0)
{
v___x_2869_ = v___x_2856_;
v_isShared_2870_ = v_isSharedCheck_2874_;
goto v_resetjp_2868_;
}
else
{
lean_inc(v_a_2867_);
lean_dec(v___x_2856_);
v___x_2869_ = lean_box(0);
v_isShared_2870_ = v_isSharedCheck_2874_;
goto v_resetjp_2868_;
}
v_resetjp_2868_:
{
lean_object* v___x_2872_; 
if (v_isShared_2870_ == 0)
{
v___x_2872_ = v___x_2869_;
goto v_reusejp_2871_;
}
else
{
lean_object* v_reuseFailAlloc_2873_; 
v_reuseFailAlloc_2873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2873_, 0, v_a_2867_);
v___x_2872_ = v_reuseFailAlloc_2873_;
goto v_reusejp_2871_;
}
v_reusejp_2871_:
{
return v___x_2872_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Goal_checkInvariants___lam__0___boxed(lean_object* v_goal_2875_, lean_object* v_expensive_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_, lean_object* v___y_2884_, lean_object* v___y_2885_, lean_object* v___y_2886_){
_start:
{
uint8_t v_expensive_boxed_2887_; lean_object* v_res_2888_; 
v_expensive_boxed_2887_ = lean_unbox(v_expensive_2876_);
v_res_2888_ = l_Lean_Meta_Grind_Goal_checkInvariants___lam__0(v_goal_2875_, v_expensive_boxed_2887_, v___y_2877_, v___y_2878_, v___y_2879_, v___y_2880_, v___y_2881_, v___y_2882_, v___y_2883_, v___y_2884_, v___y_2885_);
lean_dec(v___y_2885_);
lean_dec_ref(v___y_2884_);
lean_dec(v___y_2883_);
lean_dec_ref(v___y_2882_);
lean_dec(v___y_2881_);
lean_dec_ref(v___y_2880_);
lean_dec(v___y_2879_);
lean_dec_ref(v___y_2878_);
lean_dec(v___y_2877_);
return v_res_2888_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Goal_checkInvariants(lean_object* v_goal_2889_, uint8_t v_expensive_2890_, lean_object* v_a_2891_, lean_object* v_a_2892_, lean_object* v_a_2893_, lean_object* v_a_2894_, lean_object* v_a_2895_, lean_object* v_a_2896_, lean_object* v_a_2897_, lean_object* v_a_2898_, lean_object* v_a_2899_){
_start:
{
lean_object* v_mvarId_2901_; lean_object* v___x_2902_; lean_object* v___f_2903_; lean_object* v___x_2904_; 
v_mvarId_2901_ = lean_ctor_get(v_goal_2889_, 1);
lean_inc(v_mvarId_2901_);
v___x_2902_ = lean_box(v_expensive_2890_);
v___f_2903_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Goal_checkInvariants___lam__0___boxed), 12, 2);
lean_closure_set(v___f_2903_, 0, v_goal_2889_);
lean_closure_set(v___f_2903_, 1, v___x_2902_);
v___x_2904_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Goal_checkInvariants_spec__0___redArg(v_mvarId_2901_, v___f_2903_, v_a_2891_, v_a_2892_, v_a_2893_, v_a_2894_, v_a_2895_, v_a_2896_, v_a_2897_, v_a_2898_, v_a_2899_);
if (lean_obj_tag(v___x_2904_) == 0)
{
lean_object* v___x_2906_; uint8_t v_isShared_2907_; uint8_t v_isSharedCheck_2912_; 
v_isSharedCheck_2912_ = !lean_is_exclusive(v___x_2904_);
if (v_isSharedCheck_2912_ == 0)
{
lean_object* v_unused_2913_; 
v_unused_2913_ = lean_ctor_get(v___x_2904_, 0);
lean_dec(v_unused_2913_);
v___x_2906_ = v___x_2904_;
v_isShared_2907_ = v_isSharedCheck_2912_;
goto v_resetjp_2905_;
}
else
{
lean_dec(v___x_2904_);
v___x_2906_ = lean_box(0);
v_isShared_2907_ = v_isSharedCheck_2912_;
goto v_resetjp_2905_;
}
v_resetjp_2905_:
{
lean_object* v___x_2908_; lean_object* v___x_2910_; 
v___x_2908_ = lean_box(0);
if (v_isShared_2907_ == 0)
{
lean_ctor_set(v___x_2906_, 0, v___x_2908_);
v___x_2910_ = v___x_2906_;
goto v_reusejp_2909_;
}
else
{
lean_object* v_reuseFailAlloc_2911_; 
v_reuseFailAlloc_2911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2911_, 0, v___x_2908_);
v___x_2910_ = v_reuseFailAlloc_2911_;
goto v_reusejp_2909_;
}
v_reusejp_2909_:
{
return v___x_2910_;
}
}
}
else
{
lean_object* v_a_2914_; lean_object* v___x_2916_; uint8_t v_isShared_2917_; uint8_t v_isSharedCheck_2921_; 
v_a_2914_ = lean_ctor_get(v___x_2904_, 0);
v_isSharedCheck_2921_ = !lean_is_exclusive(v___x_2904_);
if (v_isSharedCheck_2921_ == 0)
{
v___x_2916_ = v___x_2904_;
v_isShared_2917_ = v_isSharedCheck_2921_;
goto v_resetjp_2915_;
}
else
{
lean_inc(v_a_2914_);
lean_dec(v___x_2904_);
v___x_2916_ = lean_box(0);
v_isShared_2917_ = v_isSharedCheck_2921_;
goto v_resetjp_2915_;
}
v_resetjp_2915_:
{
lean_object* v___x_2919_; 
if (v_isShared_2917_ == 0)
{
v___x_2919_ = v___x_2916_;
goto v_reusejp_2918_;
}
else
{
lean_object* v_reuseFailAlloc_2920_; 
v_reuseFailAlloc_2920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2920_, 0, v_a_2914_);
v___x_2919_ = v_reuseFailAlloc_2920_;
goto v_reusejp_2918_;
}
v_reusejp_2918_:
{
return v___x_2919_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Goal_checkInvariants___boxed(lean_object* v_goal_2922_, lean_object* v_expensive_2923_, lean_object* v_a_2924_, lean_object* v_a_2925_, lean_object* v_a_2926_, lean_object* v_a_2927_, lean_object* v_a_2928_, lean_object* v_a_2929_, lean_object* v_a_2930_, lean_object* v_a_2931_, lean_object* v_a_2932_, lean_object* v_a_2933_){
_start:
{
uint8_t v_expensive_boxed_2934_; lean_object* v_res_2935_; 
v_expensive_boxed_2934_ = lean_unbox(v_expensive_2923_);
v_res_2935_ = l_Lean_Meta_Grind_Goal_checkInvariants(v_goal_2922_, v_expensive_boxed_2934_, v_a_2924_, v_a_2925_, v_a_2926_, v_a_2927_, v_a_2928_, v_a_2929_, v_a_2930_, v_a_2931_, v_a_2932_);
lean_dec(v_a_2932_);
lean_dec_ref(v_a_2931_);
lean_dec(v_a_2930_);
lean_dec_ref(v_a_2929_);
lean_dec(v_a_2928_);
lean_dec_ref(v_a_2927_);
lean_dec(v_a_2926_);
lean_dec_ref(v_a_2925_);
lean_dec(v_a_2924_);
return v_res_2935_;
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
