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
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
uint8_t lean_expr_equal(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_instInhabitedGoalM(lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0(lean_object*, lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___boxed(lean_object**);
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
lean_object* v___x_14_; lean_object* v___x_31831__overap_15_; lean_object* v___x_16_; 
v___x_14_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__0___closed__0, &l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__0___closed__0);
v___x_31831__overap_15_ = lean_panic_fn_borrowed(v___x_14_, v_msg_2_);
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
v___x_16_ = lean_apply_11(v___x_31831__overap_15_, v___y_3_, v___y_4_, v___y_5_, v___y_6_, v___y_7_, v___y_8_, v___y_9_, v___y_10_, v___y_11_, v___y_12_, lean_box(0));
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
lean_object* v___x_43_; lean_object* v___x_33520__overap_44_; lean_object* v___x_45_; 
v___x_43_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__4___closed__0, &l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__4___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__4___closed__0);
v___x_33520__overap_44_ = lean_panic_fn_borrowed(v___x_43_, v_msg_31_);
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
v___x_45_ = lean_apply_11(v___x_33520__overap_44_, v___y_32_, v___y_33_, v___y_34_, v___y_35_, v___y_36_, v___y_37_, v___y_38_, v___y_39_, v___y_40_, v___y_41_, lean_box(0));
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
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0(lean_object* v_root_87_, lean_object* v_snd_88_, size_t v___x_89_, lean_object* v___x_90_, lean_object* v_curr_91_, lean_object* v_____r_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_, lean_object* v___y_99_, lean_object* v___y_100_, lean_object* v___y_101_, lean_object* v___y_102_){
_start:
{
lean_object* v___y_105_; lean_object* v___y_106_; lean_object* v___y_107_; lean_object* v___y_108_; lean_object* v___y_109_; lean_object* v___y_110_; lean_object* v___y_111_; lean_object* v___y_112_; lean_object* v___y_113_; lean_object* v___y_114_; uint8_t v_heqProofs_156_; 
v_heqProofs_156_ = lean_ctor_get_uint8(v_root_87_, sizeof(void*)*12 + 4);
if (v_heqProofs_156_ == 0)
{
lean_object* v___x_157_; 
lean_inc(v_snd_88_);
v___x_157_ = l_Lean_Meta_Grind_hasSameType(v_snd_88_, v_curr_91_, v___y_99_, v___y_100_, v___y_101_, v___y_102_);
if (lean_obj_tag(v___x_157_) == 0)
{
lean_object* v_a_158_; uint8_t v___x_159_; 
v_a_158_ = lean_ctor_get(v___x_157_, 0);
lean_inc(v_a_158_);
lean_dec_ref_known(v___x_157_, 1);
v___x_159_ = lean_unbox(v_a_158_);
lean_dec(v_a_158_);
if (v___x_159_ == 0)
{
lean_object* v___x_160_; lean_object* v___x_161_; 
lean_dec(v___x_90_);
lean_dec(v_snd_88_);
v___x_160_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__5, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__5_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__5);
v___x_161_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__0(v___x_160_, v___y_93_, v___y_94_, v___y_95_, v___y_96_, v___y_97_, v___y_98_, v___y_99_, v___y_100_, v___y_101_, v___y_102_);
return v___x_161_;
}
else
{
v___y_105_ = v___y_93_;
v___y_106_ = v___y_94_;
v___y_107_ = v___y_95_;
v___y_108_ = v___y_96_;
v___y_109_ = v___y_97_;
v___y_110_ = v___y_98_;
v___y_111_ = v___y_99_;
v___y_112_ = v___y_100_;
v___y_113_ = v___y_101_;
v___y_114_ = v___y_102_;
goto v___jp_104_;
}
}
else
{
lean_object* v_a_162_; lean_object* v___x_164_; uint8_t v_isShared_165_; uint8_t v_isSharedCheck_169_; 
lean_dec(v___x_90_);
lean_dec(v_snd_88_);
v_a_162_ = lean_ctor_get(v___x_157_, 0);
v_isSharedCheck_169_ = !lean_is_exclusive(v___x_157_);
if (v_isSharedCheck_169_ == 0)
{
v___x_164_ = v___x_157_;
v_isShared_165_ = v_isSharedCheck_169_;
goto v_resetjp_163_;
}
else
{
lean_inc(v_a_162_);
lean_dec(v___x_157_);
v___x_164_ = lean_box(0);
v_isShared_165_ = v_isSharedCheck_169_;
goto v_resetjp_163_;
}
v_resetjp_163_:
{
lean_object* v___x_167_; 
if (v_isShared_165_ == 0)
{
v___x_167_ = v___x_164_;
goto v_reusejp_166_;
}
else
{
lean_object* v_reuseFailAlloc_168_; 
v_reuseFailAlloc_168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_168_, 0, v_a_162_);
v___x_167_ = v_reuseFailAlloc_168_;
goto v_reusejp_166_;
}
v_reusejp_166_:
{
return v___x_167_;
}
}
}
}
else
{
lean_dec_ref(v_curr_91_);
v___y_105_ = v___y_93_;
v___y_106_ = v___y_94_;
v___y_107_ = v___y_95_;
v___y_108_ = v___y_96_;
v___y_109_ = v___y_97_;
v___y_110_ = v___y_98_;
v___y_111_ = v___y_99_;
v___y_112_ = v___y_100_;
v___y_113_ = v___y_101_;
v___y_114_ = v___y_102_;
goto v___jp_104_;
}
v___jp_104_:
{
lean_object* v___x_115_; 
lean_inc(v_snd_88_);
v___x_115_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__1___redArg(v_snd_88_, v___y_105_);
if (lean_obj_tag(v___x_115_) == 0)
{
lean_object* v_a_116_; size_t v___x_117_; uint8_t v___x_118_; 
v_a_116_ = lean_ctor_get(v___x_115_, 0);
lean_inc(v_a_116_);
lean_dec_ref_known(v___x_115_, 1);
v___x_117_ = lean_ptr_addr(v_a_116_);
lean_dec(v_a_116_);
v___x_118_ = lean_usize_dec_eq(v___x_117_, v___x_89_);
if (v___x_118_ == 0)
{
lean_object* v___x_119_; lean_object* v___x_120_; 
lean_dec(v___x_90_);
lean_dec(v_snd_88_);
v___x_119_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__3, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__3_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__3);
v___x_120_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__0(v___x_119_, v___y_105_, v___y_106_, v___y_107_, v___y_108_, v___y_109_, v___y_110_, v___y_111_, v___y_112_, v___y_113_, v___y_114_);
return v___x_120_;
}
else
{
lean_object* v___x_121_; lean_object* v___x_122_; 
v___x_121_ = lean_st_ref_get(v___y_105_);
v___x_122_ = l_Lean_Meta_Grind_Goal_getNext(v___x_121_, v_snd_88_, v___y_111_, v___y_112_, v___y_113_, v___y_114_);
lean_dec(v___x_121_);
if (lean_obj_tag(v___x_122_) == 0)
{
lean_object* v_a_123_; lean_object* v___x_125_; uint8_t v_isShared_126_; uint8_t v_isSharedCheck_139_; 
v_a_123_ = lean_ctor_get(v___x_122_, 0);
v_isSharedCheck_139_ = !lean_is_exclusive(v___x_122_);
if (v_isSharedCheck_139_ == 0)
{
v___x_125_ = v___x_122_;
v_isShared_126_ = v_isSharedCheck_139_;
goto v_resetjp_124_;
}
else
{
lean_inc(v_a_123_);
lean_dec(v___x_122_);
v___x_125_ = lean_box(0);
v_isShared_126_ = v_isSharedCheck_139_;
goto v_resetjp_124_;
}
v_resetjp_124_:
{
size_t v___x_127_; uint8_t v___x_128_; 
v___x_127_ = lean_ptr_addr(v_a_123_);
v___x_128_ = lean_usize_dec_eq(v___x_89_, v___x_127_);
if (v___x_128_ == 0)
{
lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_132_; 
v___x_129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_129_, 0, v___x_90_);
lean_ctor_set(v___x_129_, 1, v_a_123_);
v___x_130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_130_, 0, v___x_129_);
if (v_isShared_126_ == 0)
{
lean_ctor_set(v___x_125_, 0, v___x_130_);
v___x_132_ = v___x_125_;
goto v_reusejp_131_;
}
else
{
lean_object* v_reuseFailAlloc_133_; 
v_reuseFailAlloc_133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_133_, 0, v___x_130_);
v___x_132_ = v_reuseFailAlloc_133_;
goto v_reusejp_131_;
}
v_reusejp_131_:
{
return v___x_132_;
}
}
else
{
lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_137_; 
v___x_134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_134_, 0, v___x_90_);
lean_ctor_set(v___x_134_, 1, v_a_123_);
v___x_135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_135_, 0, v___x_134_);
if (v_isShared_126_ == 0)
{
lean_ctor_set(v___x_125_, 0, v___x_135_);
v___x_137_ = v___x_125_;
goto v_reusejp_136_;
}
else
{
lean_object* v_reuseFailAlloc_138_; 
v_reuseFailAlloc_138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_138_, 0, v___x_135_);
v___x_137_ = v_reuseFailAlloc_138_;
goto v_reusejp_136_;
}
v_reusejp_136_:
{
return v___x_137_;
}
}
}
}
else
{
lean_object* v_a_140_; lean_object* v___x_142_; uint8_t v_isShared_143_; uint8_t v_isSharedCheck_147_; 
lean_dec(v___x_90_);
v_a_140_ = lean_ctor_get(v___x_122_, 0);
v_isSharedCheck_147_ = !lean_is_exclusive(v___x_122_);
if (v_isSharedCheck_147_ == 0)
{
v___x_142_ = v___x_122_;
v_isShared_143_ = v_isSharedCheck_147_;
goto v_resetjp_141_;
}
else
{
lean_inc(v_a_140_);
lean_dec(v___x_122_);
v___x_142_ = lean_box(0);
v_isShared_143_ = v_isSharedCheck_147_;
goto v_resetjp_141_;
}
v_resetjp_141_:
{
lean_object* v___x_145_; 
if (v_isShared_143_ == 0)
{
v___x_145_ = v___x_142_;
goto v_reusejp_144_;
}
else
{
lean_object* v_reuseFailAlloc_146_; 
v_reuseFailAlloc_146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_146_, 0, v_a_140_);
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
}
else
{
lean_object* v_a_148_; lean_object* v___x_150_; uint8_t v_isShared_151_; uint8_t v_isSharedCheck_155_; 
lean_dec(v___x_90_);
lean_dec(v_snd_88_);
v_a_148_ = lean_ctor_get(v___x_115_, 0);
v_isSharedCheck_155_ = !lean_is_exclusive(v___x_115_);
if (v_isSharedCheck_155_ == 0)
{
v___x_150_ = v___x_115_;
v_isShared_151_ = v_isSharedCheck_155_;
goto v_resetjp_149_;
}
else
{
lean_inc(v_a_148_);
lean_dec(v___x_115_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___boxed(lean_object** _args){
lean_object* v_root_170_ = _args[0];
lean_object* v_snd_171_ = _args[1];
lean_object* v___x_172_ = _args[2];
lean_object* v___x_173_ = _args[3];
lean_object* v_curr_174_ = _args[4];
lean_object* v_____r_175_ = _args[5];
lean_object* v___y_176_ = _args[6];
lean_object* v___y_177_ = _args[7];
lean_object* v___y_178_ = _args[8];
lean_object* v___y_179_ = _args[9];
lean_object* v___y_180_ = _args[10];
lean_object* v___y_181_ = _args[11];
lean_object* v___y_182_ = _args[12];
lean_object* v___y_183_ = _args[13];
lean_object* v___y_184_ = _args[14];
lean_object* v___y_185_ = _args[15];
lean_object* v___y_186_ = _args[16];
_start:
{
size_t v___x_34097__boxed_187_; lean_object* v_res_188_; 
v___x_34097__boxed_187_ = lean_unbox_usize(v___x_172_);
lean_dec(v___x_172_);
v_res_188_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0(v_root_170_, v_snd_171_, v___x_34097__boxed_187_, v___x_173_, v_curr_174_, v_____r_175_, v___y_176_, v___y_177_, v___y_178_, v___y_179_, v___y_180_, v___y_181_, v___y_182_, v___y_183_, v___y_184_, v___y_185_);
lean_dec(v___y_185_);
lean_dec_ref(v___y_184_);
lean_dec(v___y_183_);
lean_dec_ref(v___y_182_);
lean_dec(v___y_181_);
lean_dec_ref(v___y_180_);
lean_dec(v___y_179_);
lean_dec_ref(v___y_178_);
lean_dec(v___y_177_);
lean_dec(v___y_176_);
lean_dec_ref(v_root_170_);
return v_res_188_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2_spec__4___redArg(lean_object* v___x_189_, lean_object* v_keys_190_, lean_object* v_vals_191_, lean_object* v_i_192_, lean_object* v_k_193_){
_start:
{
lean_object* v___x_194_; uint8_t v___x_195_; 
v___x_194_ = lean_array_get_size(v_keys_190_);
v___x_195_ = lean_nat_dec_lt(v_i_192_, v___x_194_);
if (v___x_195_ == 0)
{
lean_object* v___x_196_; 
lean_dec_ref(v_k_193_);
lean_dec(v_i_192_);
v___x_196_ = lean_box(0);
return v___x_196_;
}
else
{
lean_object* v_k_x27_197_; uint8_t v___x_198_; 
v_k_x27_197_ = lean_array_fget_borrowed(v_keys_190_, v_i_192_);
lean_inc(v_k_x27_197_);
lean_inc_ref(v_k_193_);
v___x_198_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_isCongruent(v___x_189_, v_k_193_, v_k_x27_197_);
if (v___x_198_ == 0)
{
lean_object* v___x_199_; lean_object* v___x_200_; 
v___x_199_ = lean_unsigned_to_nat(1u);
v___x_200_ = lean_nat_add(v_i_192_, v___x_199_);
lean_dec(v_i_192_);
v_i_192_ = v___x_200_;
goto _start;
}
else
{
lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; 
lean_dec_ref(v_k_193_);
v___x_202_ = lean_array_fget_borrowed(v_vals_191_, v_i_192_);
lean_dec(v_i_192_);
lean_inc(v___x_202_);
lean_inc(v_k_x27_197_);
v___x_203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_203_, 0, v_k_x27_197_);
lean_ctor_set(v___x_203_, 1, v___x_202_);
v___x_204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_204_, 0, v___x_203_);
return v___x_204_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2_spec__4___redArg___boxed(lean_object* v___x_205_, lean_object* v_keys_206_, lean_object* v_vals_207_, lean_object* v_i_208_, lean_object* v_k_209_){
_start:
{
lean_object* v_res_210_; 
v_res_210_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2_spec__4___redArg(v___x_205_, v_keys_206_, v_vals_207_, v_i_208_, v_k_209_);
lean_dec_ref(v_vals_207_);
lean_dec_ref(v_keys_206_);
lean_dec_ref(v___x_205_);
return v_res_210_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2___redArg(lean_object* v___x_211_, lean_object* v_x_212_, size_t v_x_213_, lean_object* v_x_214_){
_start:
{
if (lean_obj_tag(v_x_212_) == 0)
{
lean_object* v_es_215_; lean_object* v___x_216_; size_t v___x_217_; size_t v___x_218_; lean_object* v_j_219_; lean_object* v___x_220_; 
v_es_215_ = lean_ctor_get(v_x_212_, 0);
lean_inc_ref(v_es_215_);
lean_dec_ref_known(v_x_212_, 1);
v___x_216_ = lean_box(2);
v___x_217_ = ((size_t)31ULL);
v___x_218_ = lean_usize_land(v_x_213_, v___x_217_);
v_j_219_ = lean_usize_to_nat(v___x_218_);
v___x_220_ = lean_array_get(v___x_216_, v_es_215_, v_j_219_);
lean_dec(v_j_219_);
lean_dec_ref(v_es_215_);
switch(lean_obj_tag(v___x_220_))
{
case 0:
{
lean_object* v_key_221_; lean_object* v_val_222_; uint8_t v___x_223_; 
v_key_221_ = lean_ctor_get(v___x_220_, 0);
lean_inc_n(v_key_221_, 2);
v_val_222_ = lean_ctor_get(v___x_220_, 1);
lean_inc(v_val_222_);
lean_dec_ref_known(v___x_220_, 2);
v___x_223_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_isCongruent(v___x_211_, v_x_214_, v_key_221_);
if (v___x_223_ == 0)
{
lean_object* v___x_224_; 
lean_dec(v_val_222_);
lean_dec(v_key_221_);
v___x_224_ = lean_box(0);
return v___x_224_;
}
else
{
lean_object* v___x_225_; lean_object* v___x_226_; 
v___x_225_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_225_, 0, v_key_221_);
lean_ctor_set(v___x_225_, 1, v_val_222_);
v___x_226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_226_, 0, v___x_225_);
return v___x_226_;
}
}
case 1:
{
lean_object* v_node_227_; size_t v___x_228_; size_t v___x_229_; 
v_node_227_ = lean_ctor_get(v___x_220_, 0);
lean_inc(v_node_227_);
lean_dec_ref_known(v___x_220_, 1);
v___x_228_ = ((size_t)5ULL);
v___x_229_ = lean_usize_shift_right(v_x_213_, v___x_228_);
v_x_212_ = v_node_227_;
v_x_213_ = v___x_229_;
goto _start;
}
default: 
{
lean_object* v___x_231_; 
lean_dec_ref(v_x_214_);
v___x_231_ = lean_box(0);
return v___x_231_;
}
}
}
else
{
lean_object* v_ks_232_; lean_object* v_vs_233_; lean_object* v___x_234_; lean_object* v___x_235_; 
v_ks_232_ = lean_ctor_get(v_x_212_, 0);
lean_inc_ref(v_ks_232_);
v_vs_233_ = lean_ctor_get(v_x_212_, 1);
lean_inc_ref(v_vs_233_);
lean_dec_ref_known(v_x_212_, 2);
v___x_234_ = lean_unsigned_to_nat(0u);
v___x_235_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2_spec__4___redArg(v___x_211_, v_ks_232_, v_vs_233_, v___x_234_, v_x_214_);
lean_dec_ref(v_vs_233_);
lean_dec_ref(v_ks_232_);
return v___x_235_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2___redArg___boxed(lean_object* v___x_236_, lean_object* v_x_237_, lean_object* v_x_238_, lean_object* v_x_239_){
_start:
{
size_t v_x_34310__boxed_240_; lean_object* v_res_241_; 
v_x_34310__boxed_240_ = lean_unbox_usize(v_x_238_);
lean_dec(v_x_238_);
v_res_241_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2___redArg(v___x_236_, v_x_237_, v_x_34310__boxed_240_, v_x_239_);
lean_dec_ref(v___x_236_);
return v_res_241_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2___redArg(lean_object* v___x_242_, lean_object* v_x_243_, lean_object* v_x_244_){
_start:
{
uint64_t v___x_245_; size_t v___x_246_; lean_object* v___x_247_; 
lean_inc_ref(v_x_244_);
v___x_245_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_congrHash(v___x_242_, v_x_244_);
v___x_246_ = lean_uint64_to_usize(v___x_245_);
lean_inc_ref(v_x_243_);
v___x_247_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2___redArg(v___x_242_, v_x_243_, v___x_246_, v_x_244_);
return v___x_247_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2___redArg___boxed(lean_object* v___x_248_, lean_object* v_x_249_, lean_object* v_x_250_){
_start:
{
lean_object* v_res_251_; 
v_res_251_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2___redArg(v___x_248_, v_x_249_, v_x_250_);
lean_dec_ref(v_x_249_);
lean_dec_ref(v___x_248_);
return v_res_251_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; 
v___x_253_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___closed__0));
v___x_254_ = lean_unsigned_to_nat(4u);
v___x_255_ = lean_unsigned_to_nat(22u);
v___x_256_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__1));
v___x_257_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__0));
v___x_258_ = l_mkPanicMessageWithDecl(v___x_257_, v___x_256_, v___x_255_, v___x_254_, v___x_253_);
return v___x_258_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; 
v___x_260_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___closed__2));
v___x_261_ = lean_unsigned_to_nat(8u);
v___x_262_ = lean_unsigned_to_nat(29u);
v___x_263_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__1));
v___x_264_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__0));
v___x_265_ = l_mkPanicMessageWithDecl(v___x_264_, v___x_263_, v___x_262_, v___x_261_, v___x_260_);
return v___x_265_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___closed__5(void){
_start:
{
lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; 
v___x_267_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___closed__4));
v___x_268_ = lean_unsigned_to_nat(10u);
v___x_269_ = lean_unsigned_to_nat(27u);
v___x_270_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__1));
v___x_271_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__0));
v___x_272_ = l_mkPanicMessageWithDecl(v___x_271_, v___x_270_, v___x_269_, v___x_268_, v___x_267_);
return v___x_272_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg(lean_object* v_curr_273_, lean_object* v_root_274_, lean_object* v_a_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_){
_start:
{
lean_object* v___y_288_; lean_object* v___x_308_; lean_object* v_fst_309_; lean_object* v_snd_310_; lean_object* v___x_311_; 
v___x_308_ = lean_st_ref_get(v___y_276_);
v_fst_309_ = lean_ctor_get(v_a_275_, 0);
lean_inc(v_fst_309_);
v_snd_310_ = lean_ctor_get(v_a_275_, 1);
lean_inc_n(v_snd_310_, 2);
lean_dec_ref(v_a_275_);
v___x_311_ = l_Lean_Meta_Grind_Goal_getRoot(v___x_308_, v_snd_310_, v___y_282_, v___y_283_, v___y_284_, v___y_285_);
lean_dec(v___x_308_);
if (lean_obj_tag(v___x_311_) == 0)
{
lean_object* v_a_312_; size_t v___x_313_; size_t v___x_314_; uint8_t v___x_315_; 
v_a_312_ = lean_ctor_get(v___x_311_, 0);
lean_inc(v_a_312_);
lean_dec_ref_known(v___x_311_, 1);
v___x_313_ = lean_ptr_addr(v_a_312_);
lean_dec(v_a_312_);
v___x_314_ = lean_ptr_addr(v_curr_273_);
v___x_315_ = lean_usize_dec_eq(v___x_313_, v___x_314_);
if (v___x_315_ == 0)
{
lean_object* v___x_316_; lean_object* v___x_317_; 
lean_dec(v_snd_310_);
lean_dec(v_fst_309_);
v___x_316_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___closed__1, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___closed__1_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___closed__1);
v___x_317_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__0(v___x_316_, v___y_276_, v___y_277_, v___y_278_, v___y_279_, v___y_280_, v___y_281_, v___y_282_, v___y_283_, v___y_284_, v___y_285_);
v___y_288_ = v___x_317_;
goto v___jp_287_;
}
else
{
lean_object* v___x_318_; lean_object* v___x_319_; uint8_t v___x_320_; 
v___x_318_ = lean_unsigned_to_nat(1u);
v___x_319_ = lean_nat_add(v_fst_309_, v___x_318_);
lean_dec(v_fst_309_);
v___x_320_ = l_Lean_Expr_isApp(v_snd_310_);
if (v___x_320_ == 0)
{
lean_object* v___x_321_; lean_object* v___x_322_; 
v___x_321_ = lean_box(0);
lean_inc_ref(v_curr_273_);
v___x_322_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0(v_root_274_, v_snd_310_, v___x_314_, v___x_319_, v_curr_273_, v___x_321_, v___y_276_, v___y_277_, v___y_278_, v___y_279_, v___y_280_, v___y_281_, v___y_282_, v___y_283_, v___y_284_, v___y_285_);
v___y_288_ = v___x_322_;
goto v___jp_287_;
}
else
{
lean_object* v___x_323_; lean_object* v_toGoalState_324_; lean_object* v_enodeMap_325_; lean_object* v_congrTable_326_; lean_object* v___x_327_; 
v___x_323_ = lean_st_ref_get(v___y_276_);
v_toGoalState_324_ = lean_ctor_get(v___x_323_, 0);
lean_inc_ref(v_toGoalState_324_);
lean_dec(v___x_323_);
v_enodeMap_325_ = lean_ctor_get(v_toGoalState_324_, 1);
lean_inc_ref(v_enodeMap_325_);
v_congrTable_326_ = lean_ctor_get(v_toGoalState_324_, 4);
lean_inc_ref(v_congrTable_326_);
lean_dec_ref(v_toGoalState_324_);
lean_inc(v_snd_310_);
v___x_327_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2___redArg(v_enodeMap_325_, v_congrTable_326_, v_snd_310_);
lean_dec_ref(v_congrTable_326_);
lean_dec_ref(v_enodeMap_325_);
if (lean_obj_tag(v___x_327_) == 0)
{
lean_object* v___x_328_; 
lean_inc(v_snd_310_);
v___x_328_ = l_Lean_Meta_Grind_isCongrRoot___redArg(v_snd_310_, v___y_276_, v___y_282_, v___y_283_, v___y_284_, v___y_285_);
if (lean_obj_tag(v___x_328_) == 0)
{
lean_object* v_a_329_; uint8_t v___x_330_; 
v_a_329_ = lean_ctor_get(v___x_328_, 0);
lean_inc(v_a_329_);
lean_dec_ref_known(v___x_328_, 1);
v___x_330_ = lean_unbox(v_a_329_);
lean_dec(v_a_329_);
if (v___x_330_ == 0)
{
lean_object* v___x_331_; lean_object* v___x_332_; 
lean_dec(v___x_319_);
lean_dec(v_snd_310_);
v___x_331_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___closed__3, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___closed__3_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___closed__3);
v___x_332_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__0(v___x_331_, v___y_276_, v___y_277_, v___y_278_, v___y_279_, v___y_280_, v___y_281_, v___y_282_, v___y_283_, v___y_284_, v___y_285_);
v___y_288_ = v___x_332_;
goto v___jp_287_;
}
else
{
lean_object* v___x_333_; lean_object* v___x_334_; 
v___x_333_ = lean_box(0);
lean_inc_ref(v_curr_273_);
v___x_334_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0(v_root_274_, v_snd_310_, v___x_314_, v___x_319_, v_curr_273_, v___x_333_, v___y_276_, v___y_277_, v___y_278_, v___y_279_, v___y_280_, v___y_281_, v___y_282_, v___y_283_, v___y_284_, v___y_285_);
v___y_288_ = v___x_334_;
goto v___jp_287_;
}
}
else
{
lean_object* v_a_335_; lean_object* v___x_337_; uint8_t v_isShared_338_; uint8_t v_isSharedCheck_342_; 
lean_dec(v___x_319_);
lean_dec(v_snd_310_);
lean_dec_ref(v_curr_273_);
v_a_335_ = lean_ctor_get(v___x_328_, 0);
v_isSharedCheck_342_ = !lean_is_exclusive(v___x_328_);
if (v_isSharedCheck_342_ == 0)
{
v___x_337_ = v___x_328_;
v_isShared_338_ = v_isSharedCheck_342_;
goto v_resetjp_336_;
}
else
{
lean_inc(v_a_335_);
lean_dec(v___x_328_);
v___x_337_ = lean_box(0);
v_isShared_338_ = v_isSharedCheck_342_;
goto v_resetjp_336_;
}
v_resetjp_336_:
{
lean_object* v___x_340_; 
if (v_isShared_338_ == 0)
{
v___x_340_ = v___x_337_;
goto v_reusejp_339_;
}
else
{
lean_object* v_reuseFailAlloc_341_; 
v_reuseFailAlloc_341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_341_, 0, v_a_335_);
v___x_340_ = v_reuseFailAlloc_341_;
goto v_reusejp_339_;
}
v_reusejp_339_:
{
return v___x_340_;
}
}
}
}
else
{
lean_object* v_val_343_; lean_object* v_fst_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; 
v_val_343_ = lean_ctor_get(v___x_327_, 0);
lean_inc(v_val_343_);
lean_dec_ref_known(v___x_327_, 1);
v_fst_344_ = lean_ctor_get(v_val_343_, 0);
lean_inc(v_fst_344_);
lean_dec(v_val_343_);
v___x_345_ = l_Lean_Expr_getAppFn(v_fst_344_);
v___x_346_ = l_Lean_Expr_getAppFn(v_snd_310_);
v___x_347_ = l_Lean_Meta_Grind_hasSameType(v___x_345_, v___x_346_, v___y_282_, v___y_283_, v___y_284_, v___y_285_);
if (lean_obj_tag(v___x_347_) == 0)
{
lean_object* v_a_348_; uint8_t v___x_349_; 
v_a_348_ = lean_ctor_get(v___x_347_, 0);
lean_inc(v_a_348_);
lean_dec_ref_known(v___x_347_, 1);
v___x_349_ = lean_unbox(v_a_348_);
lean_dec(v_a_348_);
if (v___x_349_ == 0)
{
lean_object* v___x_350_; lean_object* v___x_351_; 
lean_dec(v_fst_344_);
v___x_350_ = lean_box(0);
lean_inc_ref(v_curr_273_);
v___x_351_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0(v_root_274_, v_snd_310_, v___x_314_, v___x_319_, v_curr_273_, v___x_350_, v___y_276_, v___y_277_, v___y_278_, v___y_279_, v___y_280_, v___y_281_, v___y_282_, v___y_283_, v___y_284_, v___y_285_);
v___y_288_ = v___x_351_;
goto v___jp_287_;
}
else
{
lean_object* v___x_352_; 
lean_inc(v_snd_310_);
v___x_352_ = l_Lean_Meta_Grind_getCongrRoot___redArg(v_snd_310_, v___y_276_, v___y_282_, v___y_283_, v___y_284_, v___y_285_);
if (lean_obj_tag(v___x_352_) == 0)
{
lean_object* v_a_353_; size_t v___x_354_; size_t v___x_355_; uint8_t v___x_356_; 
v_a_353_ = lean_ctor_get(v___x_352_, 0);
lean_inc(v_a_353_);
lean_dec_ref_known(v___x_352_, 1);
v___x_354_ = lean_ptr_addr(v_fst_344_);
lean_dec(v_fst_344_);
v___x_355_ = lean_ptr_addr(v_a_353_);
lean_dec(v_a_353_);
v___x_356_ = lean_usize_dec_eq(v___x_354_, v___x_355_);
if (v___x_356_ == 0)
{
lean_object* v___x_357_; lean_object* v___x_358_; 
lean_dec(v___x_319_);
lean_dec(v_snd_310_);
v___x_357_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___closed__5, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___closed__5_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___closed__5);
v___x_358_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__0(v___x_357_, v___y_276_, v___y_277_, v___y_278_, v___y_279_, v___y_280_, v___y_281_, v___y_282_, v___y_283_, v___y_284_, v___y_285_);
v___y_288_ = v___x_358_;
goto v___jp_287_;
}
else
{
lean_object* v___x_359_; lean_object* v___x_360_; 
v___x_359_ = lean_box(0);
lean_inc_ref(v_curr_273_);
v___x_360_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0(v_root_274_, v_snd_310_, v___x_314_, v___x_319_, v_curr_273_, v___x_359_, v___y_276_, v___y_277_, v___y_278_, v___y_279_, v___y_280_, v___y_281_, v___y_282_, v___y_283_, v___y_284_, v___y_285_);
v___y_288_ = v___x_360_;
goto v___jp_287_;
}
}
else
{
lean_object* v_a_361_; lean_object* v___x_363_; uint8_t v_isShared_364_; uint8_t v_isSharedCheck_368_; 
lean_dec(v_fst_344_);
lean_dec(v___x_319_);
lean_dec(v_snd_310_);
lean_dec_ref(v_curr_273_);
v_a_361_ = lean_ctor_get(v___x_352_, 0);
v_isSharedCheck_368_ = !lean_is_exclusive(v___x_352_);
if (v_isSharedCheck_368_ == 0)
{
v___x_363_ = v___x_352_;
v_isShared_364_ = v_isSharedCheck_368_;
goto v_resetjp_362_;
}
else
{
lean_inc(v_a_361_);
lean_dec(v___x_352_);
v___x_363_ = lean_box(0);
v_isShared_364_ = v_isSharedCheck_368_;
goto v_resetjp_362_;
}
v_resetjp_362_:
{
lean_object* v___x_366_; 
if (v_isShared_364_ == 0)
{
v___x_366_ = v___x_363_;
goto v_reusejp_365_;
}
else
{
lean_object* v_reuseFailAlloc_367_; 
v_reuseFailAlloc_367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_367_, 0, v_a_361_);
v___x_366_ = v_reuseFailAlloc_367_;
goto v_reusejp_365_;
}
v_reusejp_365_:
{
return v___x_366_;
}
}
}
}
}
else
{
lean_object* v_a_369_; lean_object* v___x_371_; uint8_t v_isShared_372_; uint8_t v_isSharedCheck_376_; 
lean_dec(v_fst_344_);
lean_dec(v___x_319_);
lean_dec(v_snd_310_);
lean_dec_ref(v_curr_273_);
v_a_369_ = lean_ctor_get(v___x_347_, 0);
v_isSharedCheck_376_ = !lean_is_exclusive(v___x_347_);
if (v_isSharedCheck_376_ == 0)
{
v___x_371_ = v___x_347_;
v_isShared_372_ = v_isSharedCheck_376_;
goto v_resetjp_370_;
}
else
{
lean_inc(v_a_369_);
lean_dec(v___x_347_);
v___x_371_ = lean_box(0);
v_isShared_372_ = v_isSharedCheck_376_;
goto v_resetjp_370_;
}
v_resetjp_370_:
{
lean_object* v___x_374_; 
if (v_isShared_372_ == 0)
{
v___x_374_ = v___x_371_;
goto v_reusejp_373_;
}
else
{
lean_object* v_reuseFailAlloc_375_; 
v_reuseFailAlloc_375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_375_, 0, v_a_369_);
v___x_374_ = v_reuseFailAlloc_375_;
goto v_reusejp_373_;
}
v_reusejp_373_:
{
return v___x_374_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_377_; lean_object* v___x_379_; uint8_t v_isShared_380_; uint8_t v_isSharedCheck_384_; 
lean_dec(v_snd_310_);
lean_dec(v_fst_309_);
lean_dec_ref(v_curr_273_);
v_a_377_ = lean_ctor_get(v___x_311_, 0);
v_isSharedCheck_384_ = !lean_is_exclusive(v___x_311_);
if (v_isSharedCheck_384_ == 0)
{
v___x_379_ = v___x_311_;
v_isShared_380_ = v_isSharedCheck_384_;
goto v_resetjp_378_;
}
else
{
lean_inc(v_a_377_);
lean_dec(v___x_311_);
v___x_379_ = lean_box(0);
v_isShared_380_ = v_isSharedCheck_384_;
goto v_resetjp_378_;
}
v_resetjp_378_:
{
lean_object* v___x_382_; 
if (v_isShared_380_ == 0)
{
v___x_382_ = v___x_379_;
goto v_reusejp_381_;
}
else
{
lean_object* v_reuseFailAlloc_383_; 
v_reuseFailAlloc_383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_383_, 0, v_a_377_);
v___x_382_ = v_reuseFailAlloc_383_;
goto v_reusejp_381_;
}
v_reusejp_381_:
{
return v___x_382_;
}
}
}
v___jp_287_:
{
if (lean_obj_tag(v___y_288_) == 0)
{
lean_object* v_a_289_; lean_object* v___x_291_; uint8_t v_isShared_292_; uint8_t v_isSharedCheck_299_; 
v_a_289_ = lean_ctor_get(v___y_288_, 0);
v_isSharedCheck_299_ = !lean_is_exclusive(v___y_288_);
if (v_isSharedCheck_299_ == 0)
{
v___x_291_ = v___y_288_;
v_isShared_292_ = v_isSharedCheck_299_;
goto v_resetjp_290_;
}
else
{
lean_inc(v_a_289_);
lean_dec(v___y_288_);
v___x_291_ = lean_box(0);
v_isShared_292_ = v_isSharedCheck_299_;
goto v_resetjp_290_;
}
v_resetjp_290_:
{
if (lean_obj_tag(v_a_289_) == 0)
{
lean_object* v_a_293_; lean_object* v___x_295_; 
lean_dec_ref(v_curr_273_);
v_a_293_ = lean_ctor_get(v_a_289_, 0);
lean_inc(v_a_293_);
lean_dec_ref_known(v_a_289_, 1);
if (v_isShared_292_ == 0)
{
lean_ctor_set(v___x_291_, 0, v_a_293_);
v___x_295_ = v___x_291_;
goto v_reusejp_294_;
}
else
{
lean_object* v_reuseFailAlloc_296_; 
v_reuseFailAlloc_296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_296_, 0, v_a_293_);
v___x_295_ = v_reuseFailAlloc_296_;
goto v_reusejp_294_;
}
v_reusejp_294_:
{
return v___x_295_;
}
}
else
{
lean_object* v_a_297_; 
lean_del_object(v___x_291_);
v_a_297_ = lean_ctor_get(v_a_289_, 0);
lean_inc(v_a_297_);
lean_dec_ref_known(v_a_289_, 1);
v_a_275_ = v_a_297_;
goto _start;
}
}
}
else
{
lean_object* v_a_300_; lean_object* v___x_302_; uint8_t v_isShared_303_; uint8_t v_isSharedCheck_307_; 
lean_dec_ref(v_curr_273_);
v_a_300_ = lean_ctor_get(v___y_288_, 0);
v_isSharedCheck_307_ = !lean_is_exclusive(v___y_288_);
if (v_isSharedCheck_307_ == 0)
{
v___x_302_ = v___y_288_;
v_isShared_303_ = v_isSharedCheck_307_;
goto v_resetjp_301_;
}
else
{
lean_inc(v_a_300_);
lean_dec(v___y_288_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___boxed(lean_object* v_curr_385_, lean_object* v_root_386_, lean_object* v_a_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_){
_start:
{
lean_object* v_res_399_; 
v_res_399_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg(v_curr_385_, v_root_386_, v_a_387_, v___y_388_, v___y_389_, v___y_390_, v___y_391_, v___y_392_, v___y_393_, v___y_394_, v___y_395_, v___y_396_, v___y_397_);
lean_dec(v___y_397_);
lean_dec_ref(v___y_396_);
lean_dec(v___y_395_);
lean_dec_ref(v___y_394_);
lean_dec(v___y_393_);
lean_dec_ref(v___y_392_);
lean_dec(v___y_391_);
lean_dec_ref(v___y_390_);
lean_dec(v___y_389_);
lean_dec(v___y_388_);
lean_dec_ref(v_root_386_);
return v_res_399_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc___closed__1(void){
_start:
{
lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; 
v___x_401_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc___closed__0));
v___x_402_ = lean_unsigned_to_nat(2u);
v___x_403_ = lean_unsigned_to_nat(46u);
v___x_404_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__1));
v___x_405_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__0));
v___x_406_ = l_mkPanicMessageWithDecl(v___x_405_, v___x_404_, v___x_403_, v___x_402_, v___x_401_);
return v___x_406_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc(lean_object* v_root_407_, lean_object* v_a_408_, lean_object* v_a_409_, lean_object* v_a_410_, lean_object* v_a_411_, lean_object* v_a_412_, lean_object* v_a_413_, lean_object* v_a_414_, lean_object* v_a_415_, lean_object* v_a_416_, lean_object* v_a_417_){
_start:
{
lean_object* v_self_419_; lean_object* v_size_420_; lean_object* v_size_421_; lean_object* v___x_422_; lean_object* v___x_423_; 
v_self_419_ = lean_ctor_get(v_root_407_, 0);
lean_inc_ref_n(v_self_419_, 2);
v_size_420_ = lean_ctor_get(v_root_407_, 6);
lean_inc(v_size_420_);
v_size_421_ = lean_unsigned_to_nat(0u);
v___x_422_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_422_, 0, v_size_421_);
lean_ctor_set(v___x_422_, 1, v_self_419_);
v___x_423_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg(v_self_419_, v_root_407_, v___x_422_, v_a_408_, v_a_409_, v_a_410_, v_a_411_, v_a_412_, v_a_413_, v_a_414_, v_a_415_, v_a_416_, v_a_417_);
lean_dec_ref(v_root_407_);
if (lean_obj_tag(v___x_423_) == 0)
{
lean_object* v_a_424_; lean_object* v___x_426_; uint8_t v_isShared_427_; uint8_t v_isSharedCheck_436_; 
v_a_424_ = lean_ctor_get(v___x_423_, 0);
v_isSharedCheck_436_ = !lean_is_exclusive(v___x_423_);
if (v_isSharedCheck_436_ == 0)
{
v___x_426_ = v___x_423_;
v_isShared_427_ = v_isSharedCheck_436_;
goto v_resetjp_425_;
}
else
{
lean_inc(v_a_424_);
lean_dec(v___x_423_);
v___x_426_ = lean_box(0);
v_isShared_427_ = v_isSharedCheck_436_;
goto v_resetjp_425_;
}
v_resetjp_425_:
{
lean_object* v_fst_428_; uint8_t v___x_429_; 
v_fst_428_ = lean_ctor_get(v_a_424_, 0);
lean_inc(v_fst_428_);
lean_dec(v_a_424_);
v___x_429_ = lean_nat_dec_eq(v_size_420_, v_fst_428_);
lean_dec(v_fst_428_);
lean_dec(v_size_420_);
if (v___x_429_ == 0)
{
lean_object* v___x_430_; lean_object* v___x_431_; 
lean_del_object(v___x_426_);
v___x_430_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc___closed__1, &l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc___closed__1);
v___x_431_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__4(v___x_430_, v_a_408_, v_a_409_, v_a_410_, v_a_411_, v_a_412_, v_a_413_, v_a_414_, v_a_415_, v_a_416_, v_a_417_);
return v___x_431_;
}
else
{
lean_object* v___x_432_; lean_object* v___x_434_; 
v___x_432_ = lean_box(0);
if (v_isShared_427_ == 0)
{
lean_ctor_set(v___x_426_, 0, v___x_432_);
v___x_434_ = v___x_426_;
goto v_reusejp_433_;
}
else
{
lean_object* v_reuseFailAlloc_435_; 
v_reuseFailAlloc_435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_435_, 0, v___x_432_);
v___x_434_ = v_reuseFailAlloc_435_;
goto v_reusejp_433_;
}
v_reusejp_433_:
{
return v___x_434_;
}
}
}
}
else
{
lean_object* v_a_437_; lean_object* v___x_439_; uint8_t v_isShared_440_; uint8_t v_isSharedCheck_444_; 
lean_dec(v_size_420_);
v_a_437_ = lean_ctor_get(v___x_423_, 0);
v_isSharedCheck_444_ = !lean_is_exclusive(v___x_423_);
if (v_isSharedCheck_444_ == 0)
{
v___x_439_ = v___x_423_;
v_isShared_440_ = v_isSharedCheck_444_;
goto v_resetjp_438_;
}
else
{
lean_inc(v_a_437_);
lean_dec(v___x_423_);
v___x_439_ = lean_box(0);
v_isShared_440_ = v_isSharedCheck_444_;
goto v_resetjp_438_;
}
v_resetjp_438_:
{
lean_object* v___x_442_; 
if (v_isShared_440_ == 0)
{
v___x_442_ = v___x_439_;
goto v_reusejp_441_;
}
else
{
lean_object* v_reuseFailAlloc_443_; 
v_reuseFailAlloc_443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_443_, 0, v_a_437_);
v___x_442_ = v_reuseFailAlloc_443_;
goto v_reusejp_441_;
}
v_reusejp_441_:
{
return v___x_442_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc___boxed(lean_object* v_root_445_, lean_object* v_a_446_, lean_object* v_a_447_, lean_object* v_a_448_, lean_object* v_a_449_, lean_object* v_a_450_, lean_object* v_a_451_, lean_object* v_a_452_, lean_object* v_a_453_, lean_object* v_a_454_, lean_object* v_a_455_, lean_object* v_a_456_){
_start:
{
lean_object* v_res_457_; 
v_res_457_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc(v_root_445_, v_a_446_, v_a_447_, v_a_448_, v_a_449_, v_a_450_, v_a_451_, v_a_452_, v_a_453_, v_a_454_, v_a_455_);
lean_dec(v_a_455_);
lean_dec_ref(v_a_454_);
lean_dec(v_a_453_);
lean_dec_ref(v_a_452_);
lean_dec(v_a_451_);
lean_dec_ref(v_a_450_);
lean_dec(v_a_449_);
lean_dec_ref(v_a_448_);
lean_dec(v_a_447_);
lean_dec(v_a_446_);
return v_res_457_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__1(lean_object* v_inst_458_, lean_object* v_a_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_){
_start:
{
lean_object* v___x_471_; 
v___x_471_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__1___redArg(v_a_459_, v___y_460_);
return v___x_471_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__1___boxed(lean_object* v_inst_472_, lean_object* v_a_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_){
_start:
{
lean_object* v_res_485_; 
v_res_485_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__1(v_inst_472_, v_a_473_, v___y_474_, v___y_475_, v___y_476_, v___y_477_, v___y_478_, v___y_479_, v___y_480_, v___y_481_, v___y_482_, v___y_483_);
lean_dec(v___y_483_);
lean_dec_ref(v___y_482_);
lean_dec(v___y_481_);
lean_dec_ref(v___y_480_);
lean_dec(v___y_479_);
lean_dec_ref(v___y_478_);
lean_dec(v___y_477_);
lean_dec_ref(v___y_476_);
lean_dec(v___y_475_);
lean_dec(v___y_474_);
return v_res_485_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2(lean_object* v___x_486_, lean_object* v_00_u03b2_487_, lean_object* v_x_488_, lean_object* v_x_489_){
_start:
{
lean_object* v___x_490_; 
v___x_490_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2___redArg(v___x_486_, v_x_488_, v_x_489_);
return v___x_490_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2___boxed(lean_object* v___x_491_, lean_object* v_00_u03b2_492_, lean_object* v_x_493_, lean_object* v_x_494_){
_start:
{
lean_object* v_res_495_; 
v_res_495_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2(v___x_491_, v_00_u03b2_492_, v_x_493_, v_x_494_);
lean_dec_ref(v_x_493_);
lean_dec_ref(v___x_491_);
return v_res_495_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3(lean_object* v_curr_496_, lean_object* v_root_497_, lean_object* v_inst_498_, lean_object* v_a_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_){
_start:
{
lean_object* v___x_511_; 
v___x_511_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg(v_curr_496_, v_root_497_, v_a_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_, v___y_504_, v___y_505_, v___y_506_, v___y_507_, v___y_508_, v___y_509_);
return v___x_511_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___boxed(lean_object* v_curr_512_, lean_object* v_root_513_, lean_object* v_inst_514_, lean_object* v_a_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_){
_start:
{
lean_object* v_res_527_; 
v_res_527_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3(v_curr_512_, v_root_513_, v_inst_514_, v_a_515_, v___y_516_, v___y_517_, v___y_518_, v___y_519_, v___y_520_, v___y_521_, v___y_522_, v___y_523_, v___y_524_, v___y_525_);
lean_dec(v___y_525_);
lean_dec_ref(v___y_524_);
lean_dec(v___y_523_);
lean_dec_ref(v___y_522_);
lean_dec(v___y_521_);
lean_dec_ref(v___y_520_);
lean_dec(v___y_519_);
lean_dec_ref(v___y_518_);
lean_dec(v___y_517_);
lean_dec(v___y_516_);
lean_dec_ref(v_root_513_);
return v_res_527_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2(lean_object* v___x_528_, lean_object* v_00_u03b2_529_, lean_object* v_x_530_, size_t v_x_531_, lean_object* v_x_532_){
_start:
{
lean_object* v___x_533_; 
lean_inc_ref(v_x_530_);
v___x_533_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2___redArg(v___x_528_, v_x_530_, v_x_531_, v_x_532_);
return v___x_533_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2___boxed(lean_object* v___x_534_, lean_object* v_00_u03b2_535_, lean_object* v_x_536_, lean_object* v_x_537_, lean_object* v_x_538_){
_start:
{
size_t v_x_34823__boxed_539_; lean_object* v_res_540_; 
v_x_34823__boxed_539_ = lean_unbox_usize(v_x_537_);
lean_dec(v_x_537_);
v_res_540_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2(v___x_534_, v_00_u03b2_535_, v_x_536_, v_x_34823__boxed_539_, v_x_538_);
lean_dec_ref(v_x_536_);
lean_dec_ref(v___x_534_);
return v_res_540_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2_spec__4(lean_object* v___x_541_, lean_object* v_00_u03b2_542_, lean_object* v_keys_543_, lean_object* v_vals_544_, lean_object* v_heq_545_, lean_object* v_i_546_, lean_object* v_k_547_){
_start:
{
lean_object* v___x_548_; 
v___x_548_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2_spec__4___redArg(v___x_541_, v_keys_543_, v_vals_544_, v_i_546_, v_k_547_);
return v___x_548_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2_spec__4___boxed(lean_object* v___x_549_, lean_object* v_00_u03b2_550_, lean_object* v_keys_551_, lean_object* v_vals_552_, lean_object* v_heq_553_, lean_object* v_i_554_, lean_object* v_k_555_){
_start:
{
lean_object* v_res_556_; 
v_res_556_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2_spec__4(v___x_549_, v_00_u03b2_550_, v_keys_551_, v_vals_552_, v_heq_553_, v_i_554_, v_k_555_);
lean_dec_ref(v_vals_552_);
lean_dec_ref(v_keys_551_);
lean_dec_ref(v___x_549_);
return v_res_556_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkChild___redArg(lean_object* v_e_557_, lean_object* v_child_558_, lean_object* v_a_559_){
_start:
{
lean_object* v___x_561_; lean_object* v___x_562_; 
v___x_561_ = lean_st_ref_get(v_a_559_);
v___x_562_ = l_Lean_Meta_Grind_Goal_getRoot_x3f(v___x_561_, v_child_558_);
lean_dec(v___x_561_);
if (lean_obj_tag(v___x_562_) == 1)
{
lean_object* v_val_563_; lean_object* v___x_565_; uint8_t v_isShared_566_; uint8_t v_isSharedCheck_574_; 
v_val_563_ = lean_ctor_get(v___x_562_, 0);
v_isSharedCheck_574_ = !lean_is_exclusive(v___x_562_);
if (v_isSharedCheck_574_ == 0)
{
v___x_565_ = v___x_562_;
v_isShared_566_ = v_isSharedCheck_574_;
goto v_resetjp_564_;
}
else
{
lean_inc(v_val_563_);
lean_dec(v___x_562_);
v___x_565_ = lean_box(0);
v_isShared_566_ = v_isSharedCheck_574_;
goto v_resetjp_564_;
}
v_resetjp_564_:
{
size_t v___x_567_; size_t v___x_568_; uint8_t v___x_569_; lean_object* v___x_570_; lean_object* v___x_572_; 
v___x_567_ = lean_ptr_addr(v_val_563_);
lean_dec(v_val_563_);
v___x_568_ = lean_ptr_addr(v_e_557_);
v___x_569_ = lean_usize_dec_eq(v___x_567_, v___x_568_);
v___x_570_ = lean_box(v___x_569_);
if (v_isShared_566_ == 0)
{
lean_ctor_set_tag(v___x_565_, 0);
lean_ctor_set(v___x_565_, 0, v___x_570_);
v___x_572_ = v___x_565_;
goto v_reusejp_571_;
}
else
{
lean_object* v_reuseFailAlloc_573_; 
v_reuseFailAlloc_573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_573_, 0, v___x_570_);
v___x_572_ = v_reuseFailAlloc_573_;
goto v_reusejp_571_;
}
v_reusejp_571_:
{
return v___x_572_;
}
}
}
else
{
uint8_t v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; 
lean_dec(v___x_562_);
v___x_575_ = 0;
v___x_576_ = lean_box(v___x_575_);
v___x_577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_577_, 0, v___x_576_);
return v___x_577_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkChild___redArg___boxed(lean_object* v_e_578_, lean_object* v_child_579_, lean_object* v_a_580_, lean_object* v_a_581_){
_start:
{
lean_object* v_res_582_; 
v_res_582_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkChild___redArg(v_e_578_, v_child_579_, v_a_580_);
lean_dec(v_a_580_);
lean_dec_ref(v_child_579_);
lean_dec_ref(v_e_578_);
return v_res_582_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkChild(lean_object* v_e_583_, lean_object* v_child_584_, lean_object* v_a_585_, lean_object* v_a_586_, lean_object* v_a_587_, lean_object* v_a_588_, lean_object* v_a_589_, lean_object* v_a_590_, lean_object* v_a_591_, lean_object* v_a_592_, lean_object* v_a_593_, lean_object* v_a_594_){
_start:
{
lean_object* v___x_596_; 
v___x_596_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkChild___redArg(v_e_583_, v_child_584_, v_a_585_);
return v___x_596_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkChild___boxed(lean_object* v_e_597_, lean_object* v_child_598_, lean_object* v_a_599_, lean_object* v_a_600_, lean_object* v_a_601_, lean_object* v_a_602_, lean_object* v_a_603_, lean_object* v_a_604_, lean_object* v_a_605_, lean_object* v_a_606_, lean_object* v_a_607_, lean_object* v_a_608_, lean_object* v_a_609_){
_start:
{
lean_object* v_res_610_; 
v_res_610_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkChild(v_e_597_, v_child_598_, v_a_599_, v_a_600_, v_a_601_, v_a_602_, v_a_603_, v_a_604_, v_a_605_, v_a_606_, v_a_607_, v_a_608_);
lean_dec(v_a_608_);
lean_dec_ref(v_a_607_);
lean_dec(v_a_606_);
lean_dec_ref(v_a_605_);
lean_dec(v_a_604_);
lean_dec_ref(v_a_603_);
lean_dec(v_a_602_);
lean_dec_ref(v_a_601_);
lean_dec(v_a_600_);
lean_dec(v_a_599_);
lean_dec_ref(v_child_598_);
lean_dec_ref(v_e_597_);
return v_res_610_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___lam__0(lean_object* v___x_611_, lean_object* v_body_612_, lean_object* v_____r_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_){
_start:
{
lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; 
v___x_625_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_625_, 0, v___x_611_);
lean_ctor_set(v___x_625_, 1, v_body_612_);
v___x_626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_626_, 0, v___x_625_);
v___x_627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_627_, 0, v___x_626_);
return v___x_627_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___lam__0___boxed(lean_object* v___x_628_, lean_object* v_body_629_, lean_object* v_____r_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_){
_start:
{
lean_object* v_res_642_; 
v_res_642_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___lam__0(v___x_628_, v_body_629_, v_____r_630_, v___y_631_, v___y_632_, v___y_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_, v___y_638_, v___y_639_, v___y_640_);
lean_dec(v___y_640_);
lean_dec_ref(v___y_639_);
lean_dec(v___y_638_);
lean_dec_ref(v___y_637_);
lean_dec(v___y_636_);
lean_dec_ref(v___y_635_);
lean_dec(v___y_634_);
lean_dec_ref(v___y_633_);
lean_dec(v___y_632_);
lean_dec(v___y_631_);
return v_res_642_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___lam__1(lean_object* v___f_643_, lean_object* v_x_644_, lean_object* v___y_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_){
_start:
{
lean_object* v___x_656_; lean_object* v___x_657_; 
v___x_656_ = lean_box(0);
lean_inc(v___y_654_);
lean_inc_ref(v___y_653_);
lean_inc(v___y_652_);
lean_inc_ref(v___y_651_);
lean_inc(v___y_650_);
lean_inc_ref(v___y_649_);
lean_inc(v___y_648_);
lean_inc_ref(v___y_647_);
lean_inc(v___y_646_);
lean_inc(v___y_645_);
v___x_657_ = lean_apply_12(v___f_643_, v___x_656_, v___y_645_, v___y_646_, v___y_647_, v___y_648_, v___y_649_, v___y_650_, v___y_651_, v___y_652_, v___y_653_, v___y_654_, lean_box(0));
return v___x_657_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___lam__1___boxed(lean_object* v___f_658_, lean_object* v_x_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_){
_start:
{
lean_object* v_res_671_; 
v_res_671_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___lam__1(v___f_658_, v_x_659_, v___y_660_, v___y_661_, v___y_662_, v___y_663_, v___y_664_, v___y_665_, v___y_666_, v___y_667_, v___y_668_, v___y_669_);
lean_dec(v___y_669_);
lean_dec_ref(v___y_668_);
lean_dec(v___y_667_);
lean_dec_ref(v___y_666_);
lean_dec(v___y_665_);
lean_dec_ref(v___y_664_);
lean_dec(v___y_663_);
lean_dec_ref(v___y_662_);
lean_dec(v___y_661_);
lean_dec(v___y_660_);
return v_res_671_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg(lean_object* v_e_681_, lean_object* v_a_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_){
_start:
{
lean_object* v___y_695_; lean_object* v_snd_715_; lean_object* v___x_717_; uint8_t v_isShared_718_; uint8_t v_isSharedCheck_819_; 
v_snd_715_ = lean_ctor_get(v_a_682_, 1);
v_isSharedCheck_819_ = !lean_is_exclusive(v_a_682_);
if (v_isSharedCheck_819_ == 0)
{
lean_object* v_unused_820_; 
v_unused_820_ = lean_ctor_get(v_a_682_, 0);
lean_dec(v_unused_820_);
v___x_717_ = v_a_682_;
v_isShared_718_ = v_isSharedCheck_819_;
goto v_resetjp_716_;
}
else
{
lean_inc(v_snd_715_);
lean_dec(v_a_682_);
v___x_717_ = lean_box(0);
v_isShared_718_ = v_isSharedCheck_819_;
goto v_resetjp_716_;
}
v___jp_694_:
{
if (lean_obj_tag(v___y_695_) == 0)
{
lean_object* v_a_696_; lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_706_; 
v_a_696_ = lean_ctor_get(v___y_695_, 0);
v_isSharedCheck_706_ = !lean_is_exclusive(v___y_695_);
if (v_isSharedCheck_706_ == 0)
{
v___x_698_ = v___y_695_;
v_isShared_699_ = v_isSharedCheck_706_;
goto v_resetjp_697_;
}
else
{
lean_inc(v_a_696_);
lean_dec(v___y_695_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_706_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
if (lean_obj_tag(v_a_696_) == 0)
{
lean_object* v_a_700_; lean_object* v___x_702_; 
v_a_700_ = lean_ctor_get(v_a_696_, 0);
lean_inc(v_a_700_);
lean_dec_ref_known(v_a_696_, 1);
if (v_isShared_699_ == 0)
{
lean_ctor_set(v___x_698_, 0, v_a_700_);
v___x_702_ = v___x_698_;
goto v_reusejp_701_;
}
else
{
lean_object* v_reuseFailAlloc_703_; 
v_reuseFailAlloc_703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_703_, 0, v_a_700_);
v___x_702_ = v_reuseFailAlloc_703_;
goto v_reusejp_701_;
}
v_reusejp_701_:
{
return v___x_702_;
}
}
else
{
lean_object* v_a_704_; 
lean_del_object(v___x_698_);
v_a_704_ = lean_ctor_get(v_a_696_, 0);
lean_inc(v_a_704_);
lean_dec_ref_known(v_a_696_, 1);
v_a_682_ = v_a_704_;
goto _start;
}
}
}
else
{
lean_object* v_a_707_; lean_object* v___x_709_; uint8_t v_isShared_710_; uint8_t v_isSharedCheck_714_; 
v_a_707_ = lean_ctor_get(v___y_695_, 0);
v_isSharedCheck_714_ = !lean_is_exclusive(v___y_695_);
if (v_isSharedCheck_714_ == 0)
{
v___x_709_ = v___y_695_;
v_isShared_710_ = v_isSharedCheck_714_;
goto v_resetjp_708_;
}
else
{
lean_inc(v_a_707_);
lean_dec(v___y_695_);
v___x_709_ = lean_box(0);
v_isShared_710_ = v_isSharedCheck_714_;
goto v_resetjp_708_;
}
v_resetjp_708_:
{
lean_object* v___x_712_; 
if (v_isShared_710_ == 0)
{
v___x_712_ = v___x_709_;
goto v_reusejp_711_;
}
else
{
lean_object* v_reuseFailAlloc_713_; 
v_reuseFailAlloc_713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_713_, 0, v_a_707_);
v___x_712_ = v_reuseFailAlloc_713_;
goto v_reusejp_711_;
}
v_reusejp_711_:
{
return v___x_712_;
}
}
}
}
v_resetjp_716_:
{
if (lean_obj_tag(v_snd_715_) == 7)
{
lean_object* v_binderType_719_; lean_object* v_body_720_; lean_object* v___x_721_; 
v_binderType_719_ = lean_ctor_get(v_snd_715_, 1);
v_body_720_ = lean_ctor_get(v_snd_715_, 2);
lean_inc_ref(v_binderType_719_);
v___x_721_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_binderType_719_, v___y_690_);
if (lean_obj_tag(v___x_721_) == 0)
{
lean_object* v_a_722_; lean_object* v___x_723_; lean_object* v___f_724_; lean_object* v___x_725_; uint8_t v___x_726_; 
v_a_722_ = lean_ctor_get(v___x_721_, 0);
lean_inc(v_a_722_);
lean_dec_ref_known(v___x_721_, 1);
v___x_723_ = lean_box(0);
lean_inc_ref(v_body_720_);
v___f_724_ = lean_alloc_closure((void*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___lam__0___boxed), 14, 2);
lean_closure_set(v___f_724_, 0, v___x_723_);
lean_closure_set(v___f_724_, 1, v_body_720_);
v___x_725_ = l_Lean_Expr_cleanupAnnotations(v_a_722_);
v___x_726_ = l_Lean_Expr_isApp(v___x_725_);
if (v___x_726_ == 0)
{
lean_object* v___x_727_; lean_object* v___x_728_; 
lean_dec_ref(v___x_725_);
lean_dec_ref_known(v_snd_715_, 3);
lean_del_object(v___x_717_);
v___x_727_ = lean_box(0);
v___x_728_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___lam__1(v___f_724_, v___x_727_, v___y_683_, v___y_684_, v___y_685_, v___y_686_, v___y_687_, v___y_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_);
v___y_695_ = v___x_728_;
goto v___jp_694_;
}
else
{
lean_object* v___x_729_; uint8_t v___x_730_; 
v___x_729_ = l_Lean_Expr_appFnCleanup___redArg(v___x_725_);
v___x_730_ = l_Lean_Expr_isApp(v___x_729_);
if (v___x_730_ == 0)
{
lean_object* v___x_731_; lean_object* v___x_732_; 
lean_dec_ref(v___x_729_);
lean_dec_ref_known(v_snd_715_, 3);
lean_del_object(v___x_717_);
v___x_731_ = lean_box(0);
v___x_732_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___lam__1(v___f_724_, v___x_731_, v___y_683_, v___y_684_, v___y_685_, v___y_686_, v___y_687_, v___y_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_);
v___y_695_ = v___x_732_;
goto v___jp_694_;
}
else
{
lean_object* v_arg_733_; lean_object* v___x_734_; uint8_t v___x_735_; 
v_arg_733_ = lean_ctor_get(v___x_729_, 1);
lean_inc_ref(v_arg_733_);
v___x_734_ = l_Lean_Expr_appFnCleanup___redArg(v___x_729_);
v___x_735_ = l_Lean_Expr_isApp(v___x_734_);
if (v___x_735_ == 0)
{
lean_object* v___x_736_; lean_object* v___x_737_; 
lean_dec_ref(v___x_734_);
lean_dec_ref(v_arg_733_);
lean_dec_ref_known(v_snd_715_, 3);
lean_del_object(v___x_717_);
v___x_736_ = lean_box(0);
v___x_737_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___lam__1(v___f_724_, v___x_736_, v___y_683_, v___y_684_, v___y_685_, v___y_686_, v___y_687_, v___y_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_);
v___y_695_ = v___x_737_;
goto v___jp_694_;
}
else
{
lean_object* v_arg_738_; lean_object* v___x_739_; lean_object* v___x_740_; uint8_t v___x_741_; 
v_arg_738_ = lean_ctor_get(v___x_734_, 1);
lean_inc_ref(v_arg_738_);
v___x_739_ = l_Lean_Expr_appFnCleanup___redArg(v___x_734_);
v___x_740_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___closed__1));
v___x_741_ = l_Lean_Expr_isConstOf(v___x_739_, v___x_740_);
if (v___x_741_ == 0)
{
uint8_t v___x_742_; 
lean_dec_ref(v_arg_733_);
v___x_742_ = l_Lean_Expr_isApp(v___x_739_);
if (v___x_742_ == 0)
{
lean_object* v___x_743_; lean_object* v___x_744_; 
lean_dec_ref(v___x_739_);
lean_dec_ref(v_arg_738_);
lean_dec_ref_known(v_snd_715_, 3);
lean_del_object(v___x_717_);
v___x_743_ = lean_box(0);
v___x_744_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___lam__1(v___f_724_, v___x_743_, v___y_683_, v___y_684_, v___y_685_, v___y_686_, v___y_687_, v___y_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_);
v___y_695_ = v___x_744_;
goto v___jp_694_;
}
else
{
lean_object* v_arg_745_; lean_object* v___x_746_; lean_object* v___x_747_; uint8_t v___x_748_; lean_object* v___y_750_; 
v_arg_745_ = lean_ctor_get(v___x_739_, 1);
lean_inc_ref(v_arg_745_);
v___x_746_ = l_Lean_Expr_appFnCleanup___redArg(v___x_739_);
v___x_747_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___closed__3));
v___x_748_ = l_Lean_Expr_isConstOf(v___x_746_, v___x_747_);
lean_dec_ref(v___x_746_);
if (v___x_748_ == 0)
{
lean_object* v___x_775_; lean_object* v___x_776_; 
lean_dec_ref(v_arg_745_);
lean_dec_ref(v_arg_738_);
lean_dec_ref_known(v_snd_715_, 3);
lean_del_object(v___x_717_);
v___x_775_ = lean_box(0);
v___x_776_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___lam__1(v___f_724_, v___x_775_, v___y_683_, v___y_684_, v___y_685_, v___y_686_, v___y_687_, v___y_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_);
v___y_695_ = v___x_776_;
goto v___jp_694_;
}
else
{
lean_object* v___x_777_; 
lean_dec_ref(v___f_724_);
v___x_777_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkChild___redArg(v_e_681_, v_arg_745_, v___y_683_);
lean_dec_ref(v_arg_745_);
if (lean_obj_tag(v___x_777_) == 0)
{
lean_object* v_a_778_; uint8_t v___x_779_; 
v_a_778_ = lean_ctor_get(v___x_777_, 0);
lean_inc(v_a_778_);
v___x_779_ = lean_unbox(v_a_778_);
lean_dec(v_a_778_);
if (v___x_779_ == 0)
{
lean_object* v___x_780_; 
lean_dec_ref_known(v___x_777_, 1);
v___x_780_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkChild___redArg(v_e_681_, v_arg_738_, v___y_683_);
lean_dec_ref(v_arg_738_);
v___y_750_ = v___x_780_;
goto v___jp_749_;
}
else
{
lean_dec_ref(v_arg_738_);
v___y_750_ = v___x_777_;
goto v___jp_749_;
}
}
else
{
lean_dec_ref(v_arg_738_);
v___y_750_ = v___x_777_;
goto v___jp_749_;
}
}
v___jp_749_:
{
if (lean_obj_tag(v___y_750_) == 0)
{
lean_object* v_a_751_; lean_object* v___x_753_; uint8_t v_isShared_754_; uint8_t v_isSharedCheck_766_; 
v_a_751_ = lean_ctor_get(v___y_750_, 0);
v_isSharedCheck_766_ = !lean_is_exclusive(v___y_750_);
if (v_isSharedCheck_766_ == 0)
{
v___x_753_ = v___y_750_;
v_isShared_754_ = v_isSharedCheck_766_;
goto v_resetjp_752_;
}
else
{
lean_inc(v_a_751_);
lean_dec(v___y_750_);
v___x_753_ = lean_box(0);
v_isShared_754_ = v_isSharedCheck_766_;
goto v_resetjp_752_;
}
v_resetjp_752_:
{
uint8_t v___x_755_; 
v___x_755_ = lean_unbox(v_a_751_);
lean_dec(v_a_751_);
if (v___x_755_ == 0)
{
lean_object* v___x_756_; lean_object* v___x_757_; 
lean_inc_ref(v_body_720_);
lean_del_object(v___x_753_);
lean_dec_ref_known(v_snd_715_, 3);
lean_del_object(v___x_717_);
v___x_756_ = lean_box(0);
v___x_757_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___lam__0(v___x_723_, v_body_720_, v___x_756_, v___y_683_, v___y_684_, v___y_685_, v___y_686_, v___y_687_, v___y_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_);
v___y_695_ = v___x_757_;
goto v___jp_694_;
}
else
{
lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_761_; 
v___x_758_ = lean_box(v___x_748_);
v___x_759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_759_, 0, v___x_758_);
if (v_isShared_718_ == 0)
{
lean_ctor_set(v___x_717_, 0, v___x_759_);
v___x_761_ = v___x_717_;
goto v_reusejp_760_;
}
else
{
lean_object* v_reuseFailAlloc_765_; 
v_reuseFailAlloc_765_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_765_, 0, v___x_759_);
lean_ctor_set(v_reuseFailAlloc_765_, 1, v_snd_715_);
v___x_761_ = v_reuseFailAlloc_765_;
goto v_reusejp_760_;
}
v_reusejp_760_:
{
lean_object* v___x_763_; 
if (v_isShared_754_ == 0)
{
lean_ctor_set(v___x_753_, 0, v___x_761_);
v___x_763_ = v___x_753_;
goto v_reusejp_762_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v___x_761_);
v___x_763_ = v_reuseFailAlloc_764_;
goto v_reusejp_762_;
}
v_reusejp_762_:
{
return v___x_763_;
}
}
}
}
}
else
{
lean_object* v_a_767_; lean_object* v___x_769_; uint8_t v_isShared_770_; uint8_t v_isSharedCheck_774_; 
lean_dec_ref_known(v_snd_715_, 3);
lean_del_object(v___x_717_);
v_a_767_ = lean_ctor_get(v___y_750_, 0);
v_isSharedCheck_774_ = !lean_is_exclusive(v___y_750_);
if (v_isSharedCheck_774_ == 0)
{
v___x_769_ = v___y_750_;
v_isShared_770_ = v_isSharedCheck_774_;
goto v_resetjp_768_;
}
else
{
lean_inc(v_a_767_);
lean_dec(v___y_750_);
v___x_769_ = lean_box(0);
v_isShared_770_ = v_isSharedCheck_774_;
goto v_resetjp_768_;
}
v_resetjp_768_:
{
lean_object* v___x_772_; 
if (v_isShared_770_ == 0)
{
v___x_772_ = v___x_769_;
goto v_reusejp_771_;
}
else
{
lean_object* v_reuseFailAlloc_773_; 
v_reuseFailAlloc_773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_773_, 0, v_a_767_);
v___x_772_ = v_reuseFailAlloc_773_;
goto v_reusejp_771_;
}
v_reusejp_771_:
{
return v___x_772_;
}
}
}
}
}
}
else
{
lean_object* v___x_781_; 
lean_dec_ref(v___x_739_);
lean_dec_ref(v_arg_738_);
lean_dec_ref(v___f_724_);
v___x_781_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkChild___redArg(v_e_681_, v_arg_733_, v___y_683_);
lean_dec_ref(v_arg_733_);
if (lean_obj_tag(v___x_781_) == 0)
{
lean_object* v_a_782_; lean_object* v___x_784_; uint8_t v_isShared_785_; uint8_t v_isSharedCheck_797_; 
v_a_782_ = lean_ctor_get(v___x_781_, 0);
v_isSharedCheck_797_ = !lean_is_exclusive(v___x_781_);
if (v_isSharedCheck_797_ == 0)
{
v___x_784_ = v___x_781_;
v_isShared_785_ = v_isSharedCheck_797_;
goto v_resetjp_783_;
}
else
{
lean_inc(v_a_782_);
lean_dec(v___x_781_);
v___x_784_ = lean_box(0);
v_isShared_785_ = v_isSharedCheck_797_;
goto v_resetjp_783_;
}
v_resetjp_783_:
{
uint8_t v___x_786_; 
v___x_786_ = lean_unbox(v_a_782_);
lean_dec(v_a_782_);
if (v___x_786_ == 0)
{
lean_object* v___x_787_; lean_object* v___x_788_; 
lean_inc_ref(v_body_720_);
lean_del_object(v___x_784_);
lean_dec_ref_known(v_snd_715_, 3);
lean_del_object(v___x_717_);
v___x_787_ = lean_box(0);
v___x_788_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___lam__0(v___x_723_, v_body_720_, v___x_787_, v___y_683_, v___y_684_, v___y_685_, v___y_686_, v___y_687_, v___y_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_);
v___y_695_ = v___x_788_;
goto v___jp_694_;
}
else
{
lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_792_; 
v___x_789_ = lean_box(v___x_741_);
v___x_790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_790_, 0, v___x_789_);
if (v_isShared_718_ == 0)
{
lean_ctor_set(v___x_717_, 0, v___x_790_);
v___x_792_ = v___x_717_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v___x_790_);
lean_ctor_set(v_reuseFailAlloc_796_, 1, v_snd_715_);
v___x_792_ = v_reuseFailAlloc_796_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
lean_object* v___x_794_; 
if (v_isShared_785_ == 0)
{
lean_ctor_set(v___x_784_, 0, v___x_792_);
v___x_794_ = v___x_784_;
goto v_reusejp_793_;
}
else
{
lean_object* v_reuseFailAlloc_795_; 
v_reuseFailAlloc_795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_795_, 0, v___x_792_);
v___x_794_ = v_reuseFailAlloc_795_;
goto v_reusejp_793_;
}
v_reusejp_793_:
{
return v___x_794_;
}
}
}
}
}
else
{
lean_object* v_a_798_; lean_object* v___x_800_; uint8_t v_isShared_801_; uint8_t v_isSharedCheck_805_; 
lean_dec_ref_known(v_snd_715_, 3);
lean_del_object(v___x_717_);
v_a_798_ = lean_ctor_get(v___x_781_, 0);
v_isSharedCheck_805_ = !lean_is_exclusive(v___x_781_);
if (v_isSharedCheck_805_ == 0)
{
v___x_800_ = v___x_781_;
v_isShared_801_ = v_isSharedCheck_805_;
goto v_resetjp_799_;
}
else
{
lean_inc(v_a_798_);
lean_dec(v___x_781_);
v___x_800_ = lean_box(0);
v_isShared_801_ = v_isSharedCheck_805_;
goto v_resetjp_799_;
}
v_resetjp_799_:
{
lean_object* v___x_803_; 
if (v_isShared_801_ == 0)
{
v___x_803_ = v___x_800_;
goto v_reusejp_802_;
}
else
{
lean_object* v_reuseFailAlloc_804_; 
v_reuseFailAlloc_804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_804_, 0, v_a_798_);
v___x_803_ = v_reuseFailAlloc_804_;
goto v_reusejp_802_;
}
v_reusejp_802_:
{
return v___x_803_;
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
lean_object* v_a_806_; lean_object* v___x_808_; uint8_t v_isShared_809_; uint8_t v_isSharedCheck_813_; 
lean_dec_ref_known(v_snd_715_, 3);
lean_del_object(v___x_717_);
v_a_806_ = lean_ctor_get(v___x_721_, 0);
v_isSharedCheck_813_ = !lean_is_exclusive(v___x_721_);
if (v_isSharedCheck_813_ == 0)
{
v___x_808_ = v___x_721_;
v_isShared_809_ = v_isSharedCheck_813_;
goto v_resetjp_807_;
}
else
{
lean_inc(v_a_806_);
lean_dec(v___x_721_);
v___x_808_ = lean_box(0);
v_isShared_809_ = v_isSharedCheck_813_;
goto v_resetjp_807_;
}
v_resetjp_807_:
{
lean_object* v___x_811_; 
if (v_isShared_809_ == 0)
{
v___x_811_ = v___x_808_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v_a_806_);
v___x_811_ = v_reuseFailAlloc_812_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
return v___x_811_;
}
}
}
}
else
{
lean_object* v___x_814_; lean_object* v___x_816_; 
v___x_814_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___closed__4));
if (v_isShared_718_ == 0)
{
lean_ctor_set(v___x_717_, 0, v___x_814_);
v___x_816_ = v___x_717_;
goto v_reusejp_815_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v___x_814_);
lean_ctor_set(v_reuseFailAlloc_818_, 1, v_snd_715_);
v___x_816_ = v_reuseFailAlloc_818_;
goto v_reusejp_815_;
}
v_reusejp_815_:
{
lean_object* v___x_817_; 
v___x_817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_817_, 0, v___x_816_);
return v___x_817_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___boxed(lean_object* v_e_821_, lean_object* v_a_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_){
_start:
{
lean_object* v_res_834_; 
v_res_834_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg(v_e_821_, v_a_822_, v___y_823_, v___y_824_, v___y_825_, v___y_826_, v___y_827_, v___y_828_, v___y_829_, v___y_830_, v___y_831_, v___y_832_);
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
lean_dec_ref(v_e_821_);
return v_res_834_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent(lean_object* v_e_842_, lean_object* v_parent_843_, lean_object* v_a_844_, lean_object* v_a_845_, lean_object* v_a_846_, lean_object* v_a_847_, lean_object* v_a_848_, lean_object* v_a_849_, lean_object* v_a_850_, lean_object* v_a_851_, lean_object* v_a_852_, lean_object* v_a_853_){
_start:
{
lean_object* v___x_855_; 
v___x_855_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_parent_843_, v_a_851_);
if (lean_obj_tag(v___x_855_) == 0)
{
lean_object* v_a_856_; lean_object* v___x_858_; uint8_t v_isShared_859_; uint8_t v_isSharedCheck_898_; 
v_a_856_ = lean_ctor_get(v___x_855_, 0);
v_isSharedCheck_898_ = !lean_is_exclusive(v___x_855_);
if (v_isSharedCheck_898_ == 0)
{
v___x_858_ = v___x_855_;
v_isShared_859_ = v_isSharedCheck_898_;
goto v_resetjp_857_;
}
else
{
lean_inc(v_a_856_);
lean_dec(v___x_855_);
v___x_858_ = lean_box(0);
v_isShared_859_ = v_isSharedCheck_898_;
goto v_resetjp_857_;
}
v_resetjp_857_:
{
lean_object* v___x_866_; uint8_t v___x_867_; 
v___x_866_ = l_Lean_Expr_cleanupAnnotations(v_a_856_);
v___x_867_ = l_Lean_Expr_isApp(v___x_866_);
if (v___x_867_ == 0)
{
lean_dec_ref(v___x_866_);
goto v___jp_860_;
}
else
{
lean_object* v_arg_868_; lean_object* v___x_869_; lean_object* v___x_870_; uint8_t v___x_871_; 
v_arg_868_ = lean_ctor_get(v___x_866_, 1);
lean_inc_ref(v_arg_868_);
v___x_869_ = l_Lean_Expr_appFnCleanup___redArg(v___x_866_);
v___x_870_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent___closed__3));
v___x_871_ = l_Lean_Expr_isConstOf(v___x_869_, v___x_870_);
lean_dec_ref(v___x_869_);
if (v___x_871_ == 0)
{
lean_dec_ref(v_arg_868_);
goto v___jp_860_;
}
else
{
lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; 
lean_del_object(v___x_858_);
v___x_872_ = lean_box(0);
v___x_873_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_873_, 0, v___x_872_);
lean_ctor_set(v___x_873_, 1, v_arg_868_);
v___x_874_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg(v_e_842_, v___x_873_, v_a_844_, v_a_845_, v_a_846_, v_a_847_, v_a_848_, v_a_849_, v_a_850_, v_a_851_, v_a_852_, v_a_853_);
if (lean_obj_tag(v___x_874_) == 0)
{
lean_object* v_a_875_; lean_object* v___x_877_; uint8_t v_isShared_878_; uint8_t v_isSharedCheck_889_; 
v_a_875_ = lean_ctor_get(v___x_874_, 0);
v_isSharedCheck_889_ = !lean_is_exclusive(v___x_874_);
if (v_isSharedCheck_889_ == 0)
{
v___x_877_ = v___x_874_;
v_isShared_878_ = v_isSharedCheck_889_;
goto v_resetjp_876_;
}
else
{
lean_inc(v_a_875_);
lean_dec(v___x_874_);
v___x_877_ = lean_box(0);
v_isShared_878_ = v_isSharedCheck_889_;
goto v_resetjp_876_;
}
v_resetjp_876_:
{
lean_object* v_fst_879_; 
v_fst_879_ = lean_ctor_get(v_a_875_, 0);
lean_inc(v_fst_879_);
lean_dec(v_a_875_);
if (lean_obj_tag(v_fst_879_) == 0)
{
uint8_t v___x_880_; lean_object* v___x_881_; lean_object* v___x_883_; 
v___x_880_ = 0;
v___x_881_ = lean_box(v___x_880_);
if (v_isShared_878_ == 0)
{
lean_ctor_set(v___x_877_, 0, v___x_881_);
v___x_883_ = v___x_877_;
goto v_reusejp_882_;
}
else
{
lean_object* v_reuseFailAlloc_884_; 
v_reuseFailAlloc_884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_884_, 0, v___x_881_);
v___x_883_ = v_reuseFailAlloc_884_;
goto v_reusejp_882_;
}
v_reusejp_882_:
{
return v___x_883_;
}
}
else
{
lean_object* v_val_885_; lean_object* v___x_887_; 
v_val_885_ = lean_ctor_get(v_fst_879_, 0);
lean_inc(v_val_885_);
lean_dec_ref_known(v_fst_879_, 1);
if (v_isShared_878_ == 0)
{
lean_ctor_set(v___x_877_, 0, v_val_885_);
v___x_887_ = v___x_877_;
goto v_reusejp_886_;
}
else
{
lean_object* v_reuseFailAlloc_888_; 
v_reuseFailAlloc_888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_888_, 0, v_val_885_);
v___x_887_ = v_reuseFailAlloc_888_;
goto v_reusejp_886_;
}
v_reusejp_886_:
{
return v___x_887_;
}
}
}
}
else
{
lean_object* v_a_890_; lean_object* v___x_892_; uint8_t v_isShared_893_; uint8_t v_isSharedCheck_897_; 
v_a_890_ = lean_ctor_get(v___x_874_, 0);
v_isSharedCheck_897_ = !lean_is_exclusive(v___x_874_);
if (v_isSharedCheck_897_ == 0)
{
v___x_892_ = v___x_874_;
v_isShared_893_ = v_isSharedCheck_897_;
goto v_resetjp_891_;
}
else
{
lean_inc(v_a_890_);
lean_dec(v___x_874_);
v___x_892_ = lean_box(0);
v_isShared_893_ = v_isSharedCheck_897_;
goto v_resetjp_891_;
}
v_resetjp_891_:
{
lean_object* v___x_895_; 
if (v_isShared_893_ == 0)
{
v___x_895_ = v___x_892_;
goto v_reusejp_894_;
}
else
{
lean_object* v_reuseFailAlloc_896_; 
v_reuseFailAlloc_896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_896_, 0, v_a_890_);
v___x_895_ = v_reuseFailAlloc_896_;
goto v_reusejp_894_;
}
v_reusejp_894_:
{
return v___x_895_;
}
}
}
}
}
v___jp_860_:
{
uint8_t v___x_861_; lean_object* v___x_862_; lean_object* v___x_864_; 
v___x_861_ = 0;
v___x_862_ = lean_box(v___x_861_);
if (v_isShared_859_ == 0)
{
lean_ctor_set(v___x_858_, 0, v___x_862_);
v___x_864_ = v___x_858_;
goto v_reusejp_863_;
}
else
{
lean_object* v_reuseFailAlloc_865_; 
v_reuseFailAlloc_865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_865_, 0, v___x_862_);
v___x_864_ = v_reuseFailAlloc_865_;
goto v_reusejp_863_;
}
v_reusejp_863_:
{
return v___x_864_;
}
}
}
}
else
{
lean_object* v_a_899_; lean_object* v___x_901_; uint8_t v_isShared_902_; uint8_t v_isSharedCheck_906_; 
v_a_899_ = lean_ctor_get(v___x_855_, 0);
v_isSharedCheck_906_ = !lean_is_exclusive(v___x_855_);
if (v_isSharedCheck_906_ == 0)
{
v___x_901_ = v___x_855_;
v_isShared_902_ = v_isSharedCheck_906_;
goto v_resetjp_900_;
}
else
{
lean_inc(v_a_899_);
lean_dec(v___x_855_);
v___x_901_ = lean_box(0);
v_isShared_902_ = v_isSharedCheck_906_;
goto v_resetjp_900_;
}
v_resetjp_900_:
{
lean_object* v___x_904_; 
if (v_isShared_902_ == 0)
{
v___x_904_ = v___x_901_;
goto v_reusejp_903_;
}
else
{
lean_object* v_reuseFailAlloc_905_; 
v_reuseFailAlloc_905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_905_, 0, v_a_899_);
v___x_904_ = v_reuseFailAlloc_905_;
goto v_reusejp_903_;
}
v_reusejp_903_:
{
return v___x_904_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent___boxed(lean_object* v_e_907_, lean_object* v_parent_908_, lean_object* v_a_909_, lean_object* v_a_910_, lean_object* v_a_911_, lean_object* v_a_912_, lean_object* v_a_913_, lean_object* v_a_914_, lean_object* v_a_915_, lean_object* v_a_916_, lean_object* v_a_917_, lean_object* v_a_918_, lean_object* v_a_919_){
_start:
{
lean_object* v_res_920_; 
v_res_920_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent(v_e_907_, v_parent_908_, v_a_909_, v_a_910_, v_a_911_, v_a_912_, v_a_913_, v_a_914_, v_a_915_, v_a_916_, v_a_917_, v_a_918_);
lean_dec(v_a_918_);
lean_dec_ref(v_a_917_);
lean_dec(v_a_916_);
lean_dec_ref(v_a_915_);
lean_dec(v_a_914_);
lean_dec_ref(v_a_913_);
lean_dec(v_a_912_);
lean_dec_ref(v_a_911_);
lean_dec(v_a_910_);
lean_dec(v_a_909_);
lean_dec_ref(v_e_907_);
return v_res_920_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0(lean_object* v_e_921_, lean_object* v_inst_922_, lean_object* v_a_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_){
_start:
{
lean_object* v___x_935_; 
v___x_935_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg(v_e_921_, v_a_923_, v___y_924_, v___y_925_, v___y_926_, v___y_927_, v___y_928_, v___y_929_, v___y_930_, v___y_931_, v___y_932_, v___y_933_);
return v___x_935_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___boxed(lean_object* v_e_936_, lean_object* v_inst_937_, lean_object* v_a_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_){
_start:
{
lean_object* v_res_950_; 
v_res_950_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0(v_e_936_, v_inst_937_, v_a_938_, v___y_939_, v___y_940_, v___y_941_, v___y_942_, v___y_943_, v___y_944_, v___y_945_, v___y_946_, v___y_947_, v___y_948_);
lean_dec(v___y_948_);
lean_dec_ref(v___y_947_);
lean_dec(v___y_946_);
lean_dec_ref(v___y_945_);
lean_dec(v___y_944_);
lean_dec_ref(v___y_943_);
lean_dec(v___y_942_);
lean_dec_ref(v___y_941_);
lean_dec(v___y_940_);
lean_dec(v___y_939_);
lean_dec_ref(v_e_936_);
return v_res_950_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__0___closed__0(void){
_start:
{
lean_object* v___x_951_; 
v___x_951_ = l_Lean_Meta_Grind_instInhabitedGoalM(lean_box(0));
return v___x_951_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__0(lean_object* v_msg_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_){
_start:
{
lean_object* v___x_964_; lean_object* v___x_60107__overap_965_; lean_object* v___x_966_; 
v___x_964_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__0___closed__0, &l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__0___closed__0);
v___x_60107__overap_965_ = lean_panic_fn_borrowed(v___x_964_, v_msg_952_);
lean_inc(v___y_962_);
lean_inc_ref(v___y_961_);
lean_inc(v___y_960_);
lean_inc_ref(v___y_959_);
lean_inc(v___y_958_);
lean_inc_ref(v___y_957_);
lean_inc(v___y_956_);
lean_inc_ref(v___y_955_);
lean_inc(v___y_954_);
lean_inc(v___y_953_);
v___x_966_ = lean_apply_11(v___x_60107__overap_965_, v___y_953_, v___y_954_, v___y_955_, v___y_956_, v___y_957_, v___y_958_, v___y_959_, v___y_960_, v___y_961_, v___y_962_, lean_box(0));
return v___x_966_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__0___boxed(lean_object* v_msg_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_){
_start:
{
lean_object* v_res_979_; 
v_res_979_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__0(v_msg_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_, v___y_974_, v___y_975_, v___y_976_, v___y_977_);
lean_dec(v___y_977_);
lean_dec_ref(v___y_976_);
lean_dec(v___y_975_);
lean_dec_ref(v___y_974_);
lean_dec(v___y_973_);
lean_dec_ref(v___y_972_);
lean_dec(v___y_971_);
lean_dec_ref(v___y_970_);
lean_dec(v___y_969_);
lean_dec(v___y_968_);
return v_res_979_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__1_spec__1(lean_object* v_msgData_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_){
_start:
{
lean_object* v___x_986_; lean_object* v_env_987_; lean_object* v___x_988_; lean_object* v_mctx_989_; lean_object* v_lctx_990_; lean_object* v_options_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; 
v___x_986_ = lean_st_ref_get(v___y_984_);
v_env_987_ = lean_ctor_get(v___x_986_, 0);
lean_inc_ref(v_env_987_);
lean_dec(v___x_986_);
v___x_988_ = lean_st_ref_get(v___y_982_);
v_mctx_989_ = lean_ctor_get(v___x_988_, 0);
lean_inc_ref(v_mctx_989_);
lean_dec(v___x_988_);
v_lctx_990_ = lean_ctor_get(v___y_981_, 2);
v_options_991_ = lean_ctor_get(v___y_983_, 2);
lean_inc_ref(v_options_991_);
lean_inc_ref(v_lctx_990_);
v___x_992_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_992_, 0, v_env_987_);
lean_ctor_set(v___x_992_, 1, v_mctx_989_);
lean_ctor_set(v___x_992_, 2, v_lctx_990_);
lean_ctor_set(v___x_992_, 3, v_options_991_);
v___x_993_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_993_, 0, v___x_992_);
lean_ctor_set(v___x_993_, 1, v_msgData_980_);
v___x_994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_994_, 0, v___x_993_);
return v___x_994_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__1_spec__1___boxed(lean_object* v_msgData_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_){
_start:
{
lean_object* v_res_1001_; 
v_res_1001_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__1_spec__1(v_msgData_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_);
lean_dec(v___y_999_);
lean_dec_ref(v___y_998_);
lean_dec(v___y_997_);
lean_dec_ref(v___y_996_);
return v_res_1001_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__1___redArg(lean_object* v_msg_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_){
_start:
{
lean_object* v_ref_1008_; lean_object* v___x_1009_; lean_object* v_a_1010_; lean_object* v___x_1012_; uint8_t v_isShared_1013_; uint8_t v_isSharedCheck_1018_; 
v_ref_1008_ = lean_ctor_get(v___y_1005_, 5);
v___x_1009_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__1_spec__1(v_msg_1002_, v___y_1003_, v___y_1004_, v___y_1005_, v___y_1006_);
v_a_1010_ = lean_ctor_get(v___x_1009_, 0);
v_isSharedCheck_1018_ = !lean_is_exclusive(v___x_1009_);
if (v_isSharedCheck_1018_ == 0)
{
v___x_1012_ = v___x_1009_;
v_isShared_1013_ = v_isSharedCheck_1018_;
goto v_resetjp_1011_;
}
else
{
lean_inc(v_a_1010_);
lean_dec(v___x_1009_);
v___x_1012_ = lean_box(0);
v_isShared_1013_ = v_isSharedCheck_1018_;
goto v_resetjp_1011_;
}
v_resetjp_1011_:
{
lean_object* v___x_1014_; lean_object* v___x_1016_; 
lean_inc(v_ref_1008_);
v___x_1014_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1014_, 0, v_ref_1008_);
lean_ctor_set(v___x_1014_, 1, v_a_1010_);
if (v_isShared_1013_ == 0)
{
lean_ctor_set_tag(v___x_1012_, 1);
lean_ctor_set(v___x_1012_, 0, v___x_1014_);
v___x_1016_ = v___x_1012_;
goto v_reusejp_1015_;
}
else
{
lean_object* v_reuseFailAlloc_1017_; 
v_reuseFailAlloc_1017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1017_, 0, v___x_1014_);
v___x_1016_ = v_reuseFailAlloc_1017_;
goto v_reusejp_1015_;
}
v_reusejp_1015_:
{
return v___x_1016_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__1___redArg___boxed(lean_object* v_msg_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_){
_start:
{
lean_object* v_res_1025_; 
v_res_1025_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__1___redArg(v_msg_1019_, v___y_1020_, v___y_1021_, v___y_1022_, v___y_1023_);
lean_dec(v___y_1023_);
lean_dec_ref(v___y_1022_);
lean_dec(v___y_1021_);
lean_dec_ref(v___y_1020_);
return v_res_1025_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__2___redArg(lean_object* v_e_1026_, uint8_t v_a_1027_, lean_object* v_as_1028_, size_t v_sz_1029_, size_t v_i_1030_, uint8_t v_b_1031_, lean_object* v___y_1032_){
_start:
{
uint8_t v___x_1034_; 
v___x_1034_ = lean_usize_dec_lt(v_i_1030_, v_sz_1029_);
if (v___x_1034_ == 0)
{
lean_object* v___x_1035_; lean_object* v___x_1036_; 
v___x_1035_ = lean_box(v_b_1031_);
v___x_1036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1036_, 0, v___x_1035_);
return v___x_1036_;
}
else
{
lean_object* v_a_1037_; lean_object* v___x_1038_; 
v_a_1037_ = lean_array_uget_borrowed(v_as_1028_, v_i_1030_);
v___x_1038_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkChild___redArg(v_e_1026_, v_a_1037_, v___y_1032_);
if (lean_obj_tag(v___x_1038_) == 0)
{
lean_object* v_a_1039_; lean_object* v___x_1041_; uint8_t v_isShared_1042_; uint8_t v_isSharedCheck_1051_; 
v_a_1039_ = lean_ctor_get(v___x_1038_, 0);
v_isSharedCheck_1051_ = !lean_is_exclusive(v___x_1038_);
if (v_isSharedCheck_1051_ == 0)
{
v___x_1041_ = v___x_1038_;
v_isShared_1042_ = v_isSharedCheck_1051_;
goto v_resetjp_1040_;
}
else
{
lean_inc(v_a_1039_);
lean_dec(v___x_1038_);
v___x_1041_ = lean_box(0);
v_isShared_1042_ = v_isSharedCheck_1051_;
goto v_resetjp_1040_;
}
v_resetjp_1040_:
{
uint8_t v___x_1043_; 
v___x_1043_ = lean_unbox(v_a_1039_);
lean_dec(v_a_1039_);
if (v___x_1043_ == 0)
{
size_t v___x_1044_; size_t v___x_1045_; 
lean_del_object(v___x_1041_);
v___x_1044_ = ((size_t)1ULL);
v___x_1045_ = lean_usize_add(v_i_1030_, v___x_1044_);
v_i_1030_ = v___x_1045_;
goto _start;
}
else
{
lean_object* v___x_1047_; lean_object* v___x_1049_; 
v___x_1047_ = lean_box(v_a_1027_);
if (v_isShared_1042_ == 0)
{
lean_ctor_set(v___x_1041_, 0, v___x_1047_);
v___x_1049_ = v___x_1041_;
goto v_reusejp_1048_;
}
else
{
lean_object* v_reuseFailAlloc_1050_; 
v_reuseFailAlloc_1050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1050_, 0, v___x_1047_);
v___x_1049_ = v_reuseFailAlloc_1050_;
goto v_reusejp_1048_;
}
v_reusejp_1048_:
{
return v___x_1049_;
}
}
}
}
else
{
return v___x_1038_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__2___redArg___boxed(lean_object* v_e_1052_, lean_object* v_a_1053_, lean_object* v_as_1054_, lean_object* v_sz_1055_, lean_object* v_i_1056_, lean_object* v_b_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_){
_start:
{
uint8_t v_a_66539__boxed_1060_; size_t v_sz_boxed_1061_; size_t v_i_boxed_1062_; uint8_t v_b_boxed_1063_; lean_object* v_res_1064_; 
v_a_66539__boxed_1060_ = lean_unbox(v_a_1053_);
v_sz_boxed_1061_ = lean_unbox_usize(v_sz_1055_);
lean_dec(v_sz_1055_);
v_i_boxed_1062_ = lean_unbox_usize(v_i_1056_);
lean_dec(v_i_1056_);
v_b_boxed_1063_ = lean_unbox(v_b_1057_);
v_res_1064_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__2___redArg(v_e_1052_, v_a_66539__boxed_1060_, v_as_1054_, v_sz_boxed_1061_, v_i_boxed_1062_, v_b_boxed_1063_, v___y_1058_);
lean_dec(v___y_1058_);
lean_dec_ref(v_as_1054_);
lean_dec_ref(v_e_1052_);
return v_res_1064_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__2(void){
_start:
{
lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; 
v___x_1067_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__1));
v___x_1068_ = lean_unsigned_to_nat(8u);
v___x_1069_ = lean_unsigned_to_nat(75u);
v___x_1070_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__0));
v___x_1071_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__0));
v___x_1072_ = l_mkPanicMessageWithDecl(v___x_1071_, v___x_1070_, v___x_1069_, v___x_1068_, v___x_1067_);
return v___x_1072_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__4(void){
_start:
{
lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; 
v___x_1074_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__3));
v___x_1075_ = lean_unsigned_to_nat(10u);
v___x_1076_ = lean_unsigned_to_nat(93u);
v___x_1077_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__0));
v___x_1078_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__0));
v___x_1079_ = l_mkPanicMessageWithDecl(v___x_1078_, v___x_1077_, v___x_1076_, v___x_1075_, v___x_1074_);
return v___x_1079_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__6(void){
_start:
{
lean_object* v___x_1081_; lean_object* v___x_1082_; 
v___x_1081_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__5));
v___x_1082_ = l_Lean_stringToMessageData(v___x_1081_);
return v___x_1082_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__8(void){
_start:
{
lean_object* v___x_1084_; lean_object* v___x_1085_; 
v___x_1084_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__7));
v___x_1085_ = l_Lean_stringToMessageData(v___x_1084_);
return v___x_1085_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__9(void){
_start:
{
lean_object* v___x_1086_; lean_object* v_dummy_1087_; 
v___x_1086_ = lean_box(0);
v_dummy_1087_ = l_Lean_Expr_sort___override(v___x_1086_);
return v_dummy_1087_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg(lean_object* v_e_1088_, uint8_t v_a_1089_, lean_object* v_as_x27_1090_, lean_object* v_b_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_){
_start:
{
if (lean_obj_tag(v_as_x27_1090_) == 0)
{
lean_object* v___x_1103_; 
lean_dec_ref(v_e_1088_);
v___x_1103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1103_, 0, v_b_1091_);
return v___x_1103_;
}
else
{
lean_object* v_head_1104_; lean_object* v_tail_1105_; lean_object* v___y_1107_; lean_object* v___x_1127_; 
v_head_1104_ = lean_ctor_get(v_as_x27_1090_, 0);
v_tail_1105_ = lean_ctor_get(v_as_x27_1090_, 1);
lean_inc(v_head_1104_);
v___x_1127_ = l_Lean_Meta_Grind_useFunCC___redArg(v_head_1104_, v___y_1092_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_);
if (lean_obj_tag(v___x_1127_) == 0)
{
lean_object* v_a_1128_; lean_object* v___x_1129_; lean_object* v___y_1131_; lean_object* v___y_1132_; lean_object* v___y_1133_; lean_object* v___y_1134_; lean_object* v___y_1135_; lean_object* v___y_1136_; lean_object* v___y_1137_; lean_object* v___y_1138_; lean_object* v___y_1139_; lean_object* v___y_1140_; lean_object* v___y_1156_; lean_object* v___y_1157_; lean_object* v___y_1158_; lean_object* v___y_1159_; lean_object* v___y_1160_; lean_object* v___y_1161_; lean_object* v___y_1162_; lean_object* v___y_1163_; lean_object* v___y_1164_; lean_object* v___y_1165_; lean_object* v___y_1166_; uint8_t v_found_1174_; lean_object* v___y_1175_; lean_object* v___y_1176_; lean_object* v___y_1177_; lean_object* v___y_1178_; lean_object* v___y_1179_; lean_object* v___y_1180_; lean_object* v___y_1181_; lean_object* v___y_1182_; lean_object* v___y_1183_; lean_object* v___y_1184_; lean_object* v___y_1199_; uint8_t v_found_1200_; lean_object* v___y_1201_; lean_object* v___y_1202_; lean_object* v___y_1203_; lean_object* v___y_1204_; lean_object* v___y_1205_; lean_object* v___y_1206_; lean_object* v___y_1207_; lean_object* v___y_1208_; lean_object* v___y_1209_; lean_object* v___y_1210_; uint8_t v___y_1217_; uint8_t v___x_1265_; 
v_a_1128_ = lean_ctor_get(v___x_1127_, 0);
lean_inc(v_a_1128_);
lean_dec_ref_known(v___x_1127_, 1);
v___x_1129_ = lean_box(0);
v___x_1265_ = l_Lean_Expr_isApp(v_head_1104_);
if (v___x_1265_ == 0)
{
lean_dec(v_a_1128_);
v___y_1217_ = v___x_1265_;
goto v___jp_1216_;
}
else
{
uint8_t v___x_1266_; 
v___x_1266_ = lean_unbox(v_a_1128_);
lean_dec(v_a_1128_);
v___y_1217_ = v___x_1266_;
goto v___jp_1216_;
}
v___jp_1130_:
{
lean_object* v___x_1141_; 
lean_inc(v_head_1104_);
v___x_1141_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent(v_e_1088_, v_head_1104_, v___y_1131_, v___y_1132_, v___y_1133_, v___y_1134_, v___y_1135_, v___y_1136_, v___y_1137_, v___y_1138_, v___y_1139_, v___y_1140_);
if (lean_obj_tag(v___x_1141_) == 0)
{
lean_object* v_a_1142_; uint8_t v___x_1143_; 
v_a_1142_ = lean_ctor_get(v___x_1141_, 0);
lean_inc(v_a_1142_);
lean_dec_ref_known(v___x_1141_, 1);
v___x_1143_ = lean_unbox(v_a_1142_);
lean_dec(v_a_1142_);
if (v___x_1143_ == 0)
{
lean_object* v___x_1144_; lean_object* v___x_1145_; 
v___x_1144_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__2, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__2_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__2);
v___x_1145_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__0(v___x_1144_, v___y_1131_, v___y_1132_, v___y_1133_, v___y_1134_, v___y_1135_, v___y_1136_, v___y_1137_, v___y_1138_, v___y_1139_, v___y_1140_);
v___y_1107_ = v___x_1145_;
goto v___jp_1106_;
}
else
{
v_as_x27_1090_ = v_tail_1105_;
v_b_1091_ = v___x_1129_;
goto _start;
}
}
else
{
lean_object* v_a_1147_; lean_object* v___x_1149_; uint8_t v_isShared_1150_; uint8_t v_isSharedCheck_1154_; 
lean_dec_ref(v_e_1088_);
v_a_1147_ = lean_ctor_get(v___x_1141_, 0);
v_isSharedCheck_1154_ = !lean_is_exclusive(v___x_1141_);
if (v_isSharedCheck_1154_ == 0)
{
v___x_1149_ = v___x_1141_;
v_isShared_1150_ = v_isSharedCheck_1154_;
goto v_resetjp_1148_;
}
else
{
lean_inc(v_a_1147_);
lean_dec(v___x_1141_);
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
v___jp_1155_:
{
lean_object* v___x_1167_; lean_object* v_a_1168_; uint8_t v___x_1169_; 
v___x_1167_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkChild___redArg(v_e_1088_, v___y_1156_, v___y_1157_);
lean_dec_ref(v___y_1156_);
v_a_1168_ = lean_ctor_get(v___x_1167_, 0);
lean_inc(v_a_1168_);
lean_dec_ref(v___x_1167_);
v___x_1169_ = lean_unbox(v_a_1168_);
lean_dec(v_a_1168_);
if (v___x_1169_ == 0)
{
lean_object* v___x_1170_; lean_object* v___x_1171_; 
v___x_1170_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__4, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__4);
v___x_1171_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__0(v___x_1170_, v___y_1157_, v___y_1158_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_);
v___y_1107_ = v___x_1171_;
goto v___jp_1106_;
}
else
{
v_as_x27_1090_ = v_tail_1105_;
v_b_1091_ = v___x_1129_;
goto _start;
}
}
v___jp_1173_:
{
if (v_found_1174_ == 0)
{
lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v_a_1187_; uint8_t v___x_1188_; 
v___x_1185_ = l_Lean_Expr_getAppFn(v_head_1104_);
v___x_1186_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkChild___redArg(v_e_1088_, v___x_1185_, v___y_1175_);
v_a_1187_ = lean_ctor_get(v___x_1186_, 0);
lean_inc(v_a_1187_);
lean_dec_ref(v___x_1186_);
v___x_1188_ = lean_unbox(v_a_1187_);
lean_dec(v_a_1187_);
if (v___x_1188_ == 0)
{
lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; 
lean_dec_ref(v___x_1185_);
v___x_1189_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__6, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__6_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__6);
v___x_1190_ = l_Lean_MessageData_ofExpr(v_e_1088_);
v___x_1191_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1191_, 0, v___x_1189_);
lean_ctor_set(v___x_1191_, 1, v___x_1190_);
v___x_1192_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__8, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__8_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__8);
v___x_1193_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1193_, 0, v___x_1191_);
lean_ctor_set(v___x_1193_, 1, v___x_1192_);
lean_inc(v_head_1104_);
v___x_1194_ = l_Lean_MessageData_ofExpr(v_head_1104_);
v___x_1195_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1195_, 0, v___x_1193_);
lean_ctor_set(v___x_1195_, 1, v___x_1194_);
v___x_1196_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__1___redArg(v___x_1195_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_);
return v___x_1196_;
}
else
{
v___y_1156_ = v___x_1185_;
v___y_1157_ = v___y_1175_;
v___y_1158_ = v___y_1176_;
v___y_1159_ = v___y_1177_;
v___y_1160_ = v___y_1178_;
v___y_1161_ = v___y_1179_;
v___y_1162_ = v___y_1180_;
v___y_1163_ = v___y_1181_;
v___y_1164_ = v___y_1182_;
v___y_1165_ = v___y_1183_;
v___y_1166_ = v___y_1184_;
goto v___jp_1155_;
}
}
else
{
v_as_x27_1090_ = v_tail_1105_;
v_b_1091_ = v___x_1129_;
goto _start;
}
}
v___jp_1198_:
{
uint8_t v___x_1211_; 
v___x_1211_ = l_Lean_Expr_hasLooseBVars(v___y_1199_);
if (v___x_1211_ == 0)
{
lean_object* v___x_1212_; lean_object* v_a_1213_; uint8_t v___x_1214_; 
v___x_1212_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkChild___redArg(v_e_1088_, v___y_1199_, v___y_1201_);
lean_dec_ref(v___y_1199_);
v_a_1213_ = lean_ctor_get(v___x_1212_, 0);
lean_inc(v_a_1213_);
lean_dec_ref(v___x_1212_);
v___x_1214_ = lean_unbox(v_a_1213_);
lean_dec(v_a_1213_);
if (v___x_1214_ == 0)
{
v_found_1174_ = v_found_1200_;
v___y_1175_ = v___y_1201_;
v___y_1176_ = v___y_1202_;
v___y_1177_ = v___y_1203_;
v___y_1178_ = v___y_1204_;
v___y_1179_ = v___y_1205_;
v___y_1180_ = v___y_1206_;
v___y_1181_ = v___y_1207_;
v___y_1182_ = v___y_1208_;
v___y_1183_ = v___y_1209_;
v___y_1184_ = v___y_1210_;
goto v___jp_1173_;
}
else
{
v_as_x27_1090_ = v_tail_1105_;
v_b_1091_ = v___x_1129_;
goto _start;
}
}
else
{
lean_dec_ref(v___y_1199_);
v_found_1174_ = v_found_1200_;
v___y_1175_ = v___y_1201_;
v___y_1176_ = v___y_1202_;
v___y_1177_ = v___y_1203_;
v___y_1178_ = v___y_1204_;
v___y_1179_ = v___y_1205_;
v___y_1180_ = v___y_1206_;
v___y_1181_ = v___y_1207_;
v___y_1182_ = v___y_1208_;
v___y_1183_ = v___y_1209_;
v___y_1184_ = v___y_1210_;
goto v___jp_1173_;
}
}
v___jp_1216_:
{
if (v___y_1217_ == 0)
{
uint8_t v___x_1218_; 
v___x_1218_ = l_Lean_Meta_Grind_isMatchCond(v_head_1104_);
if (v___x_1218_ == 0)
{
lean_object* v_dummy_1219_; lean_object* v_nargs_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; size_t v_sz_1225_; size_t v___x_1226_; lean_object* v___x_1227_; 
v_dummy_1219_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__9, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__9_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__9);
v_nargs_1220_ = l_Lean_Expr_getAppNumArgs(v_head_1104_);
lean_inc(v_nargs_1220_);
v___x_1221_ = lean_mk_array(v_nargs_1220_, v_dummy_1219_);
v___x_1222_ = lean_unsigned_to_nat(1u);
v___x_1223_ = lean_nat_sub(v_nargs_1220_, v___x_1222_);
lean_dec(v_nargs_1220_);
lean_inc(v_head_1104_);
v___x_1224_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_head_1104_, v___x_1221_, v___x_1223_);
v_sz_1225_ = lean_array_size(v___x_1224_);
v___x_1226_ = ((size_t)0ULL);
v___x_1227_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__2___redArg(v_e_1088_, v_a_1089_, v___x_1224_, v_sz_1225_, v___x_1226_, v___x_1218_, v___y_1092_);
lean_dec_ref(v___x_1224_);
if (lean_obj_tag(v___x_1227_) == 0)
{
if (lean_obj_tag(v_head_1104_) == 7)
{
lean_object* v_a_1228_; lean_object* v_binderType_1229_; lean_object* v_body_1230_; lean_object* v___x_1231_; lean_object* v_a_1232_; uint8_t v___x_1233_; 
v_a_1228_ = lean_ctor_get(v___x_1227_, 0);
lean_inc(v_a_1228_);
lean_dec_ref_known(v___x_1227_, 1);
v_binderType_1229_ = lean_ctor_get(v_head_1104_, 1);
v_body_1230_ = lean_ctor_get(v_head_1104_, 2);
v___x_1231_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkChild___redArg(v_e_1088_, v_binderType_1229_, v___y_1092_);
v_a_1232_ = lean_ctor_get(v___x_1231_, 0);
lean_inc(v_a_1232_);
lean_dec_ref(v___x_1231_);
v___x_1233_ = lean_unbox(v_a_1232_);
lean_dec(v_a_1232_);
if (v___x_1233_ == 0)
{
uint8_t v___x_1234_; 
v___x_1234_ = lean_unbox(v_a_1228_);
lean_dec(v_a_1228_);
lean_inc_ref(v_body_1230_);
v___y_1199_ = v_body_1230_;
v_found_1200_ = v___x_1234_;
v___y_1201_ = v___y_1092_;
v___y_1202_ = v___y_1093_;
v___y_1203_ = v___y_1094_;
v___y_1204_ = v___y_1095_;
v___y_1205_ = v___y_1096_;
v___y_1206_ = v___y_1097_;
v___y_1207_ = v___y_1098_;
v___y_1208_ = v___y_1099_;
v___y_1209_ = v___y_1100_;
v___y_1210_ = v___y_1101_;
goto v___jp_1198_;
}
else
{
lean_dec(v_a_1228_);
lean_inc_ref(v_body_1230_);
v___y_1199_ = v_body_1230_;
v_found_1200_ = v_a_1089_;
v___y_1201_ = v___y_1092_;
v___y_1202_ = v___y_1093_;
v___y_1203_ = v___y_1094_;
v___y_1204_ = v___y_1095_;
v___y_1205_ = v___y_1096_;
v___y_1206_ = v___y_1097_;
v___y_1207_ = v___y_1098_;
v___y_1208_ = v___y_1099_;
v___y_1209_ = v___y_1100_;
v___y_1210_ = v___y_1101_;
goto v___jp_1198_;
}
}
else
{
lean_object* v_a_1235_; uint8_t v___x_1236_; 
v_a_1235_ = lean_ctor_get(v___x_1227_, 0);
lean_inc(v_a_1235_);
lean_dec_ref_known(v___x_1227_, 1);
v___x_1236_ = lean_unbox(v_a_1235_);
lean_dec(v_a_1235_);
v_found_1174_ = v___x_1236_;
v___y_1175_ = v___y_1092_;
v___y_1176_ = v___y_1093_;
v___y_1177_ = v___y_1094_;
v___y_1178_ = v___y_1095_;
v___y_1179_ = v___y_1096_;
v___y_1180_ = v___y_1097_;
v___y_1181_ = v___y_1098_;
v___y_1182_ = v___y_1099_;
v___y_1183_ = v___y_1100_;
v___y_1184_ = v___y_1101_;
goto v___jp_1173_;
}
}
else
{
lean_object* v_a_1237_; lean_object* v___x_1239_; uint8_t v_isShared_1240_; uint8_t v_isSharedCheck_1244_; 
lean_dec_ref(v_e_1088_);
v_a_1237_ = lean_ctor_get(v___x_1227_, 0);
v_isSharedCheck_1244_ = !lean_is_exclusive(v___x_1227_);
if (v_isSharedCheck_1244_ == 0)
{
v___x_1239_ = v___x_1227_;
v_isShared_1240_ = v_isSharedCheck_1244_;
goto v_resetjp_1238_;
}
else
{
lean_inc(v_a_1237_);
lean_dec(v___x_1227_);
v___x_1239_ = lean_box(0);
v_isShared_1240_ = v_isSharedCheck_1244_;
goto v_resetjp_1238_;
}
v_resetjp_1238_:
{
lean_object* v___x_1242_; 
if (v_isShared_1240_ == 0)
{
v___x_1242_ = v___x_1239_;
goto v_reusejp_1241_;
}
else
{
lean_object* v_reuseFailAlloc_1243_; 
v_reuseFailAlloc_1243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1243_, 0, v_a_1237_);
v___x_1242_ = v_reuseFailAlloc_1243_;
goto v_reusejp_1241_;
}
v_reusejp_1241_:
{
return v___x_1242_;
}
}
}
}
else
{
lean_object* v___x_1245_; 
lean_inc(v_head_1104_);
v___x_1245_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent(v_e_1088_, v_head_1104_, v___y_1092_, v___y_1093_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_);
if (lean_obj_tag(v___x_1245_) == 0)
{
lean_object* v_a_1246_; uint8_t v___x_1247_; 
v_a_1246_ = lean_ctor_get(v___x_1245_, 0);
lean_inc(v_a_1246_);
lean_dec_ref_known(v___x_1245_, 1);
v___x_1247_ = lean_unbox(v_a_1246_);
lean_dec(v_a_1246_);
if (v___x_1247_ == 0)
{
lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; 
v___x_1248_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__6, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__6_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__6);
v___x_1249_ = l_Lean_MessageData_ofExpr(v_e_1088_);
v___x_1250_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1250_, 0, v___x_1248_);
lean_ctor_set(v___x_1250_, 1, v___x_1249_);
v___x_1251_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__8, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__8_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__8);
v___x_1252_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1252_, 0, v___x_1250_);
lean_ctor_set(v___x_1252_, 1, v___x_1251_);
lean_inc(v_head_1104_);
v___x_1253_ = l_Lean_MessageData_ofExpr(v_head_1104_);
v___x_1254_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1254_, 0, v___x_1252_);
lean_ctor_set(v___x_1254_, 1, v___x_1253_);
v___x_1255_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__1___redArg(v___x_1254_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_);
return v___x_1255_;
}
else
{
v___y_1131_ = v___y_1092_;
v___y_1132_ = v___y_1093_;
v___y_1133_ = v___y_1094_;
v___y_1134_ = v___y_1095_;
v___y_1135_ = v___y_1096_;
v___y_1136_ = v___y_1097_;
v___y_1137_ = v___y_1098_;
v___y_1138_ = v___y_1099_;
v___y_1139_ = v___y_1100_;
v___y_1140_ = v___y_1101_;
goto v___jp_1130_;
}
}
else
{
lean_object* v_a_1256_; lean_object* v___x_1258_; uint8_t v_isShared_1259_; uint8_t v_isSharedCheck_1263_; 
lean_dec_ref(v_e_1088_);
v_a_1256_ = lean_ctor_get(v___x_1245_, 0);
v_isSharedCheck_1263_ = !lean_is_exclusive(v___x_1245_);
if (v_isSharedCheck_1263_ == 0)
{
v___x_1258_ = v___x_1245_;
v_isShared_1259_ = v_isSharedCheck_1263_;
goto v_resetjp_1257_;
}
else
{
lean_inc(v_a_1256_);
lean_dec(v___x_1245_);
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
}
}
else
{
v_as_x27_1090_ = v_tail_1105_;
v_b_1091_ = v___x_1129_;
goto _start;
}
}
}
else
{
lean_object* v_a_1267_; lean_object* v___x_1269_; uint8_t v_isShared_1270_; uint8_t v_isSharedCheck_1274_; 
lean_dec_ref(v_e_1088_);
v_a_1267_ = lean_ctor_get(v___x_1127_, 0);
v_isSharedCheck_1274_ = !lean_is_exclusive(v___x_1127_);
if (v_isSharedCheck_1274_ == 0)
{
v___x_1269_ = v___x_1127_;
v_isShared_1270_ = v_isSharedCheck_1274_;
goto v_resetjp_1268_;
}
else
{
lean_inc(v_a_1267_);
lean_dec(v___x_1127_);
v___x_1269_ = lean_box(0);
v_isShared_1270_ = v_isSharedCheck_1274_;
goto v_resetjp_1268_;
}
v_resetjp_1268_:
{
lean_object* v___x_1272_; 
if (v_isShared_1270_ == 0)
{
v___x_1272_ = v___x_1269_;
goto v_reusejp_1271_;
}
else
{
lean_object* v_reuseFailAlloc_1273_; 
v_reuseFailAlloc_1273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1273_, 0, v_a_1267_);
v___x_1272_ = v_reuseFailAlloc_1273_;
goto v_reusejp_1271_;
}
v_reusejp_1271_:
{
return v___x_1272_;
}
}
}
v___jp_1106_:
{
if (lean_obj_tag(v___y_1107_) == 0)
{
lean_object* v_a_1108_; lean_object* v___x_1110_; uint8_t v_isShared_1111_; uint8_t v_isSharedCheck_1118_; 
v_a_1108_ = lean_ctor_get(v___y_1107_, 0);
v_isSharedCheck_1118_ = !lean_is_exclusive(v___y_1107_);
if (v_isSharedCheck_1118_ == 0)
{
v___x_1110_ = v___y_1107_;
v_isShared_1111_ = v_isSharedCheck_1118_;
goto v_resetjp_1109_;
}
else
{
lean_inc(v_a_1108_);
lean_dec(v___y_1107_);
v___x_1110_ = lean_box(0);
v_isShared_1111_ = v_isSharedCheck_1118_;
goto v_resetjp_1109_;
}
v_resetjp_1109_:
{
if (lean_obj_tag(v_a_1108_) == 0)
{
lean_object* v_a_1112_; lean_object* v___x_1114_; 
lean_dec_ref(v_e_1088_);
v_a_1112_ = lean_ctor_get(v_a_1108_, 0);
lean_inc(v_a_1112_);
lean_dec_ref_known(v_a_1108_, 1);
if (v_isShared_1111_ == 0)
{
lean_ctor_set(v___x_1110_, 0, v_a_1112_);
v___x_1114_ = v___x_1110_;
goto v_reusejp_1113_;
}
else
{
lean_object* v_reuseFailAlloc_1115_; 
v_reuseFailAlloc_1115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1115_, 0, v_a_1112_);
v___x_1114_ = v_reuseFailAlloc_1115_;
goto v_reusejp_1113_;
}
v_reusejp_1113_:
{
return v___x_1114_;
}
}
else
{
lean_object* v_a_1116_; 
lean_del_object(v___x_1110_);
v_a_1116_ = lean_ctor_get(v_a_1108_, 0);
lean_inc(v_a_1116_);
lean_dec_ref_known(v_a_1108_, 1);
v_as_x27_1090_ = v_tail_1105_;
v_b_1091_ = v_a_1116_;
goto _start;
}
}
}
else
{
lean_object* v_a_1119_; lean_object* v___x_1121_; uint8_t v_isShared_1122_; uint8_t v_isSharedCheck_1126_; 
lean_dec_ref(v_e_1088_);
v_a_1119_ = lean_ctor_get(v___y_1107_, 0);
v_isSharedCheck_1126_ = !lean_is_exclusive(v___y_1107_);
if (v_isSharedCheck_1126_ == 0)
{
v___x_1121_ = v___y_1107_;
v_isShared_1122_ = v_isSharedCheck_1126_;
goto v_resetjp_1120_;
}
else
{
lean_inc(v_a_1119_);
lean_dec(v___y_1107_);
v___x_1121_ = lean_box(0);
v_isShared_1122_ = v_isSharedCheck_1126_;
goto v_resetjp_1120_;
}
v_resetjp_1120_:
{
lean_object* v___x_1124_; 
if (v_isShared_1122_ == 0)
{
v___x_1124_ = v___x_1121_;
goto v_reusejp_1123_;
}
else
{
lean_object* v_reuseFailAlloc_1125_; 
v_reuseFailAlloc_1125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1125_, 0, v_a_1119_);
v___x_1124_ = v_reuseFailAlloc_1125_;
goto v_reusejp_1123_;
}
v_reusejp_1123_:
{
return v___x_1124_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___boxed(lean_object* v_e_1275_, lean_object* v_a_1276_, lean_object* v_as_x27_1277_, lean_object* v_b_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_){
_start:
{
uint8_t v_a_66636__boxed_1290_; lean_object* v_res_1291_; 
v_a_66636__boxed_1290_ = lean_unbox(v_a_1276_);
v_res_1291_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg(v_e_1275_, v_a_66636__boxed_1290_, v_as_x27_1277_, v_b_1278_, v___y_1279_, v___y_1280_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_, v___y_1288_);
lean_dec(v___y_1288_);
lean_dec_ref(v___y_1287_);
lean_dec(v___y_1286_);
lean_dec_ref(v___y_1285_);
lean_dec(v___y_1284_);
lean_dec_ref(v___y_1283_);
lean_dec(v___y_1282_);
lean_dec_ref(v___y_1281_);
lean_dec(v___y_1280_);
lean_dec(v___y_1279_);
lean_dec(v_as_x27_1277_);
return v_res_1291_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents___closed__1(void){
_start:
{
lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; 
v___x_1293_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents___closed__0));
v___x_1294_ = lean_unsigned_to_nat(6u);
v___x_1295_ = lean_unsigned_to_nat(96u);
v___x_1296_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__0));
v___x_1297_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__0));
v___x_1298_ = l_mkPanicMessageWithDecl(v___x_1297_, v___x_1296_, v___x_1295_, v___x_1294_, v___x_1293_);
return v___x_1298_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents(lean_object* v_e_1299_, lean_object* v_a_1300_, lean_object* v_a_1301_, lean_object* v_a_1302_, lean_object* v_a_1303_, lean_object* v_a_1304_, lean_object* v_a_1305_, lean_object* v_a_1306_, lean_object* v_a_1307_, lean_object* v_a_1308_, lean_object* v_a_1309_){
_start:
{
lean_object* v___x_1311_; 
v___x_1311_ = l_Lean_Meta_Grind_isRoot___redArg(v_e_1299_, v_a_1300_);
if (lean_obj_tag(v___x_1311_) == 0)
{
lean_object* v_a_1312_; uint8_t v___x_1313_; 
v_a_1312_ = lean_ctor_get(v___x_1311_, 0);
lean_inc(v_a_1312_);
lean_dec_ref_known(v___x_1311_, 1);
v___x_1313_ = lean_unbox(v_a_1312_);
if (v___x_1313_ == 0)
{
lean_object* v___x_1314_; 
lean_dec(v_a_1312_);
v___x_1314_ = l_Lean_Meta_Grind_getParents___redArg(v_e_1299_, v_a_1300_);
lean_dec_ref(v_e_1299_);
if (lean_obj_tag(v___x_1314_) == 0)
{
lean_object* v_a_1315_; lean_object* v___x_1317_; uint8_t v_isShared_1318_; uint8_t v_isSharedCheck_1326_; 
v_a_1315_ = lean_ctor_get(v___x_1314_, 0);
v_isSharedCheck_1326_ = !lean_is_exclusive(v___x_1314_);
if (v_isSharedCheck_1326_ == 0)
{
v___x_1317_ = v___x_1314_;
v_isShared_1318_ = v_isSharedCheck_1326_;
goto v_resetjp_1316_;
}
else
{
lean_inc(v_a_1315_);
lean_dec(v___x_1314_);
v___x_1317_ = lean_box(0);
v_isShared_1318_ = v_isSharedCheck_1326_;
goto v_resetjp_1316_;
}
v_resetjp_1316_:
{
uint8_t v___x_1319_; 
v___x_1319_ = l_Lean_Meta_Grind_ParentSet_isEmpty(v_a_1315_);
lean_dec(v_a_1315_);
if (v___x_1319_ == 0)
{
lean_object* v___x_1320_; lean_object* v___x_1321_; 
lean_del_object(v___x_1317_);
v___x_1320_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents___closed__1, &l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents___closed__1);
v___x_1321_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__4(v___x_1320_, v_a_1300_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
return v___x_1321_;
}
else
{
lean_object* v___x_1322_; lean_object* v___x_1324_; 
v___x_1322_ = lean_box(0);
if (v_isShared_1318_ == 0)
{
lean_ctor_set(v___x_1317_, 0, v___x_1322_);
v___x_1324_ = v___x_1317_;
goto v_reusejp_1323_;
}
else
{
lean_object* v_reuseFailAlloc_1325_; 
v_reuseFailAlloc_1325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1325_, 0, v___x_1322_);
v___x_1324_ = v_reuseFailAlloc_1325_;
goto v_reusejp_1323_;
}
v_reusejp_1323_:
{
return v___x_1324_;
}
}
}
}
else
{
lean_object* v_a_1327_; lean_object* v___x_1329_; uint8_t v_isShared_1330_; uint8_t v_isSharedCheck_1334_; 
v_a_1327_ = lean_ctor_get(v___x_1314_, 0);
v_isSharedCheck_1334_ = !lean_is_exclusive(v___x_1314_);
if (v_isSharedCheck_1334_ == 0)
{
v___x_1329_ = v___x_1314_;
v_isShared_1330_ = v_isSharedCheck_1334_;
goto v_resetjp_1328_;
}
else
{
lean_inc(v_a_1327_);
lean_dec(v___x_1314_);
v___x_1329_ = lean_box(0);
v_isShared_1330_ = v_isSharedCheck_1334_;
goto v_resetjp_1328_;
}
v_resetjp_1328_:
{
lean_object* v___x_1332_; 
if (v_isShared_1330_ == 0)
{
v___x_1332_ = v___x_1329_;
goto v_reusejp_1331_;
}
else
{
lean_object* v_reuseFailAlloc_1333_; 
v_reuseFailAlloc_1333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1333_, 0, v_a_1327_);
v___x_1332_ = v_reuseFailAlloc_1333_;
goto v_reusejp_1331_;
}
v_reusejp_1331_:
{
return v___x_1332_;
}
}
}
}
else
{
lean_object* v___x_1335_; 
v___x_1335_ = l_Lean_Meta_Grind_getParents___redArg(v_e_1299_, v_a_1300_);
if (lean_obj_tag(v___x_1335_) == 0)
{
lean_object* v_a_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; uint8_t v___x_1339_; lean_object* v___x_1340_; 
v_a_1336_ = lean_ctor_get(v___x_1335_, 0);
lean_inc(v_a_1336_);
lean_dec_ref_known(v___x_1335_, 1);
v___x_1337_ = l_Lean_Meta_Grind_ParentSet_elems(v_a_1336_);
lean_dec(v_a_1336_);
v___x_1338_ = lean_box(0);
v___x_1339_ = lean_unbox(v_a_1312_);
lean_dec(v_a_1312_);
v___x_1340_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg(v_e_1299_, v___x_1339_, v___x_1337_, v___x_1338_, v_a_1300_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
lean_dec(v___x_1337_);
if (lean_obj_tag(v___x_1340_) == 0)
{
lean_object* v___x_1342_; uint8_t v_isShared_1343_; uint8_t v_isSharedCheck_1347_; 
v_isSharedCheck_1347_ = !lean_is_exclusive(v___x_1340_);
if (v_isSharedCheck_1347_ == 0)
{
lean_object* v_unused_1348_; 
v_unused_1348_ = lean_ctor_get(v___x_1340_, 0);
lean_dec(v_unused_1348_);
v___x_1342_ = v___x_1340_;
v_isShared_1343_ = v_isSharedCheck_1347_;
goto v_resetjp_1341_;
}
else
{
lean_dec(v___x_1340_);
v___x_1342_ = lean_box(0);
v_isShared_1343_ = v_isSharedCheck_1347_;
goto v_resetjp_1341_;
}
v_resetjp_1341_:
{
lean_object* v___x_1345_; 
if (v_isShared_1343_ == 0)
{
lean_ctor_set(v___x_1342_, 0, v___x_1338_);
v___x_1345_ = v___x_1342_;
goto v_reusejp_1344_;
}
else
{
lean_object* v_reuseFailAlloc_1346_; 
v_reuseFailAlloc_1346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1346_, 0, v___x_1338_);
v___x_1345_ = v_reuseFailAlloc_1346_;
goto v_reusejp_1344_;
}
v_reusejp_1344_:
{
return v___x_1345_;
}
}
}
else
{
return v___x_1340_;
}
}
else
{
lean_object* v_a_1349_; lean_object* v___x_1351_; uint8_t v_isShared_1352_; uint8_t v_isSharedCheck_1356_; 
lean_dec(v_a_1312_);
lean_dec_ref(v_e_1299_);
v_a_1349_ = lean_ctor_get(v___x_1335_, 0);
v_isSharedCheck_1356_ = !lean_is_exclusive(v___x_1335_);
if (v_isSharedCheck_1356_ == 0)
{
v___x_1351_ = v___x_1335_;
v_isShared_1352_ = v_isSharedCheck_1356_;
goto v_resetjp_1350_;
}
else
{
lean_inc(v_a_1349_);
lean_dec(v___x_1335_);
v___x_1351_ = lean_box(0);
v_isShared_1352_ = v_isSharedCheck_1356_;
goto v_resetjp_1350_;
}
v_resetjp_1350_:
{
lean_object* v___x_1354_; 
if (v_isShared_1352_ == 0)
{
v___x_1354_ = v___x_1351_;
goto v_reusejp_1353_;
}
else
{
lean_object* v_reuseFailAlloc_1355_; 
v_reuseFailAlloc_1355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1355_, 0, v_a_1349_);
v___x_1354_ = v_reuseFailAlloc_1355_;
goto v_reusejp_1353_;
}
v_reusejp_1353_:
{
return v___x_1354_;
}
}
}
}
}
else
{
lean_object* v_a_1357_; lean_object* v___x_1359_; uint8_t v_isShared_1360_; uint8_t v_isSharedCheck_1364_; 
lean_dec_ref(v_e_1299_);
v_a_1357_ = lean_ctor_get(v___x_1311_, 0);
v_isSharedCheck_1364_ = !lean_is_exclusive(v___x_1311_);
if (v_isSharedCheck_1364_ == 0)
{
v___x_1359_ = v___x_1311_;
v_isShared_1360_ = v_isSharedCheck_1364_;
goto v_resetjp_1358_;
}
else
{
lean_inc(v_a_1357_);
lean_dec(v___x_1311_);
v___x_1359_ = lean_box(0);
v_isShared_1360_ = v_isSharedCheck_1364_;
goto v_resetjp_1358_;
}
v_resetjp_1358_:
{
lean_object* v___x_1362_; 
if (v_isShared_1360_ == 0)
{
v___x_1362_ = v___x_1359_;
goto v_reusejp_1361_;
}
else
{
lean_object* v_reuseFailAlloc_1363_; 
v_reuseFailAlloc_1363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1363_, 0, v_a_1357_);
v___x_1362_ = v_reuseFailAlloc_1363_;
goto v_reusejp_1361_;
}
v_reusejp_1361_:
{
return v___x_1362_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents___boxed(lean_object* v_e_1365_, lean_object* v_a_1366_, lean_object* v_a_1367_, lean_object* v_a_1368_, lean_object* v_a_1369_, lean_object* v_a_1370_, lean_object* v_a_1371_, lean_object* v_a_1372_, lean_object* v_a_1373_, lean_object* v_a_1374_, lean_object* v_a_1375_, lean_object* v_a_1376_){
_start:
{
lean_object* v_res_1377_; 
v_res_1377_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents(v_e_1365_, v_a_1366_, v_a_1367_, v_a_1368_, v_a_1369_, v_a_1370_, v_a_1371_, v_a_1372_, v_a_1373_, v_a_1374_, v_a_1375_);
lean_dec(v_a_1375_);
lean_dec_ref(v_a_1374_);
lean_dec(v_a_1373_);
lean_dec_ref(v_a_1372_);
lean_dec(v_a_1371_);
lean_dec_ref(v_a_1370_);
lean_dec(v_a_1369_);
lean_dec_ref(v_a_1368_);
lean_dec(v_a_1367_);
lean_dec(v_a_1366_);
return v_res_1377_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__1(lean_object* v_00_u03b1_1378_, lean_object* v_msg_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_){
_start:
{
lean_object* v___x_1391_; 
v___x_1391_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__1___redArg(v_msg_1379_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_);
return v___x_1391_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__1___boxed(lean_object* v_00_u03b1_1392_, lean_object* v_msg_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_){
_start:
{
lean_object* v_res_1405_; 
v_res_1405_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__1(v_00_u03b1_1392_, v_msg_1393_, v___y_1394_, v___y_1395_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_);
lean_dec(v___y_1403_);
lean_dec_ref(v___y_1402_);
lean_dec(v___y_1401_);
lean_dec_ref(v___y_1400_);
lean_dec(v___y_1399_);
lean_dec_ref(v___y_1398_);
lean_dec(v___y_1397_);
lean_dec_ref(v___y_1396_);
lean_dec(v___y_1395_);
lean_dec(v___y_1394_);
return v_res_1405_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__2(lean_object* v_e_1406_, uint8_t v_a_1407_, lean_object* v_as_1408_, size_t v_sz_1409_, size_t v_i_1410_, uint8_t v_b_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_){
_start:
{
lean_object* v___x_1423_; 
v___x_1423_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__2___redArg(v_e_1406_, v_a_1407_, v_as_1408_, v_sz_1409_, v_i_1410_, v_b_1411_, v___y_1412_);
return v___x_1423_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__2___boxed(lean_object** _args){
lean_object* v_e_1424_ = _args[0];
lean_object* v_a_1425_ = _args[1];
lean_object* v_as_1426_ = _args[2];
lean_object* v_sz_1427_ = _args[3];
lean_object* v_i_1428_ = _args[4];
lean_object* v_b_1429_ = _args[5];
lean_object* v___y_1430_ = _args[6];
lean_object* v___y_1431_ = _args[7];
lean_object* v___y_1432_ = _args[8];
lean_object* v___y_1433_ = _args[9];
lean_object* v___y_1434_ = _args[10];
lean_object* v___y_1435_ = _args[11];
lean_object* v___y_1436_ = _args[12];
lean_object* v___y_1437_ = _args[13];
lean_object* v___y_1438_ = _args[14];
lean_object* v___y_1439_ = _args[15];
lean_object* v___y_1440_ = _args[16];
_start:
{
uint8_t v_a_67209__boxed_1441_; size_t v_sz_boxed_1442_; size_t v_i_boxed_1443_; uint8_t v_b_boxed_1444_; lean_object* v_res_1445_; 
v_a_67209__boxed_1441_ = lean_unbox(v_a_1425_);
v_sz_boxed_1442_ = lean_unbox_usize(v_sz_1427_);
lean_dec(v_sz_1427_);
v_i_boxed_1443_ = lean_unbox_usize(v_i_1428_);
lean_dec(v_i_1428_);
v_b_boxed_1444_ = lean_unbox(v_b_1429_);
v_res_1445_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__2(v_e_1424_, v_a_67209__boxed_1441_, v_as_1426_, v_sz_boxed_1442_, v_i_boxed_1443_, v_b_boxed_1444_, v___y_1430_, v___y_1431_, v___y_1432_, v___y_1433_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_);
lean_dec(v___y_1439_);
lean_dec_ref(v___y_1438_);
lean_dec(v___y_1437_);
lean_dec_ref(v___y_1436_);
lean_dec(v___y_1435_);
lean_dec_ref(v___y_1434_);
lean_dec(v___y_1433_);
lean_dec_ref(v___y_1432_);
lean_dec(v___y_1431_);
lean_dec(v___y_1430_);
lean_dec_ref(v_as_1426_);
lean_dec_ref(v_e_1424_);
return v_res_1445_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3(lean_object* v_e_1446_, uint8_t v_a_1447_, lean_object* v_as_1448_, lean_object* v_as_x27_1449_, lean_object* v_b_1450_, lean_object* v_a_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_){
_start:
{
lean_object* v___x_1463_; 
v___x_1463_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg(v_e_1446_, v_a_1447_, v_as_x27_1449_, v_b_1450_, v___y_1452_, v___y_1453_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_);
return v___x_1463_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___boxed(lean_object** _args){
lean_object* v_e_1464_ = _args[0];
lean_object* v_a_1465_ = _args[1];
lean_object* v_as_1466_ = _args[2];
lean_object* v_as_x27_1467_ = _args[3];
lean_object* v_b_1468_ = _args[4];
lean_object* v_a_1469_ = _args[5];
lean_object* v___y_1470_ = _args[6];
lean_object* v___y_1471_ = _args[7];
lean_object* v___y_1472_ = _args[8];
lean_object* v___y_1473_ = _args[9];
lean_object* v___y_1474_ = _args[10];
lean_object* v___y_1475_ = _args[11];
lean_object* v___y_1476_ = _args[12];
lean_object* v___y_1477_ = _args[13];
lean_object* v___y_1478_ = _args[14];
lean_object* v___y_1479_ = _args[15];
lean_object* v___y_1480_ = _args[16];
_start:
{
uint8_t v_a_67247__boxed_1481_; lean_object* v_res_1482_; 
v_a_67247__boxed_1481_ = lean_unbox(v_a_1465_);
v_res_1482_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3(v_e_1464_, v_a_67247__boxed_1481_, v_as_1466_, v_as_x27_1467_, v_b_1468_, v_a_1469_, v___y_1470_, v___y_1471_, v___y_1472_, v___y_1473_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_);
lean_dec(v___y_1479_);
lean_dec_ref(v___y_1478_);
lean_dec(v___y_1477_);
lean_dec_ref(v___y_1476_);
lean_dec(v___y_1475_);
lean_dec_ref(v___y_1474_);
lean_dec(v___y_1473_);
lean_dec_ref(v___y_1472_);
lean_dec(v___y_1471_);
lean_dec(v___y_1470_);
lean_dec(v_as_x27_1467_);
lean_dec(v_as_1466_);
return v_res_1482_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; 
v___x_1485_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg___closed__1));
v___x_1486_ = lean_unsigned_to_nat(6u);
v___x_1487_ = lean_unsigned_to_nat(107u);
v___x_1488_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg___closed__0));
v___x_1489_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__0));
v___x_1490_ = l_mkPanicMessageWithDecl(v___x_1489_, v___x_1488_, v___x_1487_, v___x_1486_, v___x_1485_);
return v___x_1490_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; 
v___x_1492_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg___closed__3));
v___x_1493_ = lean_unsigned_to_nat(6u);
v___x_1494_ = lean_unsigned_to_nat(105u);
v___x_1495_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg___closed__0));
v___x_1496_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__0));
v___x_1497_ = l_mkPanicMessageWithDecl(v___x_1496_, v___x_1495_, v___x_1494_, v___x_1493_, v___x_1492_);
return v___x_1497_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg(lean_object* v_upperBound_1498_, lean_object* v_a_1499_, lean_object* v___x_1500_, lean_object* v_a_1501_, lean_object* v_b_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_){
_start:
{
lean_object* v_a_1515_; lean_object* v___y_1520_; uint8_t v___x_1539_; 
v___x_1539_ = lean_nat_dec_lt(v_a_1501_, v_upperBound_1498_);
if (v___x_1539_ == 0)
{
lean_object* v___x_1540_; 
lean_dec(v_a_1501_);
v___x_1540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1540_, 0, v_b_1502_);
return v___x_1540_;
}
else
{
lean_object* v___x_1541_; lean_object* v___x_1542_; size_t v___x_1543_; size_t v___x_1544_; uint8_t v___x_1545_; 
v___x_1541_ = l_Lean_instInhabitedExpr;
v___x_1542_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1541_, v_a_1499_, v_a_1501_);
v___x_1543_ = lean_ptr_addr(v___x_1500_);
v___x_1544_ = lean_ptr_addr(v___x_1542_);
v___x_1545_ = lean_usize_dec_eq(v___x_1543_, v___x_1544_);
if (v___x_1545_ == 0)
{
uint8_t v___x_1546_; 
v___x_1546_ = lean_expr_equal(v___x_1500_, v___x_1542_);
lean_dec(v___x_1542_);
if (v___x_1546_ == 0)
{
lean_object* v___x_1547_; 
v___x_1547_ = lean_box(0);
v_a_1515_ = v___x_1547_;
goto v___jp_1514_;
}
else
{
lean_object* v___x_1548_; lean_object* v___x_1549_; 
v___x_1548_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg___closed__2, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg___closed__2_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg___closed__2);
v___x_1549_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__0(v___x_1548_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_, v___y_1509_, v___y_1510_, v___y_1511_, v___y_1512_);
v___y_1520_ = v___x_1549_;
goto v___jp_1519_;
}
}
else
{
lean_object* v___x_1550_; lean_object* v___x_1551_; 
lean_dec(v___x_1542_);
v___x_1550_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg___closed__4, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg___closed__4_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg___closed__4);
v___x_1551_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__0(v___x_1550_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_, v___y_1509_, v___y_1510_, v___y_1511_, v___y_1512_);
v___y_1520_ = v___x_1551_;
goto v___jp_1519_;
}
}
v___jp_1514_:
{
lean_object* v___x_1516_; lean_object* v___x_1517_; 
v___x_1516_ = lean_unsigned_to_nat(1u);
v___x_1517_ = lean_nat_add(v_a_1501_, v___x_1516_);
lean_dec(v_a_1501_);
v_a_1501_ = v___x_1517_;
v_b_1502_ = v_a_1515_;
goto _start;
}
v___jp_1519_:
{
if (lean_obj_tag(v___y_1520_) == 0)
{
lean_object* v_a_1521_; lean_object* v___x_1523_; uint8_t v_isShared_1524_; uint8_t v_isSharedCheck_1530_; 
v_a_1521_ = lean_ctor_get(v___y_1520_, 0);
v_isSharedCheck_1530_ = !lean_is_exclusive(v___y_1520_);
if (v_isSharedCheck_1530_ == 0)
{
v___x_1523_ = v___y_1520_;
v_isShared_1524_ = v_isSharedCheck_1530_;
goto v_resetjp_1522_;
}
else
{
lean_inc(v_a_1521_);
lean_dec(v___y_1520_);
v___x_1523_ = lean_box(0);
v_isShared_1524_ = v_isSharedCheck_1530_;
goto v_resetjp_1522_;
}
v_resetjp_1522_:
{
if (lean_obj_tag(v_a_1521_) == 0)
{
lean_object* v_a_1525_; lean_object* v___x_1527_; 
lean_dec(v_a_1501_);
v_a_1525_ = lean_ctor_get(v_a_1521_, 0);
lean_inc(v_a_1525_);
lean_dec_ref_known(v_a_1521_, 1);
if (v_isShared_1524_ == 0)
{
lean_ctor_set(v___x_1523_, 0, v_a_1525_);
v___x_1527_ = v___x_1523_;
goto v_reusejp_1526_;
}
else
{
lean_object* v_reuseFailAlloc_1528_; 
v_reuseFailAlloc_1528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1528_, 0, v_a_1525_);
v___x_1527_ = v_reuseFailAlloc_1528_;
goto v_reusejp_1526_;
}
v_reusejp_1526_:
{
return v___x_1527_;
}
}
else
{
lean_object* v_a_1529_; 
lean_del_object(v___x_1523_);
v_a_1529_ = lean_ctor_get(v_a_1521_, 0);
lean_inc(v_a_1529_);
lean_dec_ref_known(v_a_1521_, 1);
v_a_1515_ = v_a_1529_;
goto v___jp_1514_;
}
}
}
else
{
lean_object* v_a_1531_; lean_object* v___x_1533_; uint8_t v_isShared_1534_; uint8_t v_isSharedCheck_1538_; 
lean_dec(v_a_1501_);
v_a_1531_ = lean_ctor_get(v___y_1520_, 0);
v_isSharedCheck_1538_ = !lean_is_exclusive(v___y_1520_);
if (v_isSharedCheck_1538_ == 0)
{
v___x_1533_ = v___y_1520_;
v_isShared_1534_ = v_isSharedCheck_1538_;
goto v_resetjp_1532_;
}
else
{
lean_inc(v_a_1531_);
lean_dec(v___y_1520_);
v___x_1533_ = lean_box(0);
v_isShared_1534_ = v_isSharedCheck_1538_;
goto v_resetjp_1532_;
}
v_resetjp_1532_:
{
lean_object* v___x_1536_; 
if (v_isShared_1534_ == 0)
{
v___x_1536_ = v___x_1533_;
goto v_reusejp_1535_;
}
else
{
lean_object* v_reuseFailAlloc_1537_; 
v_reuseFailAlloc_1537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1537_, 0, v_a_1531_);
v___x_1536_ = v_reuseFailAlloc_1537_;
goto v_reusejp_1535_;
}
v_reusejp_1535_:
{
return v___x_1536_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg___boxed(lean_object* v_upperBound_1552_, lean_object* v_a_1553_, lean_object* v___x_1554_, lean_object* v_a_1555_, lean_object* v_b_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_){
_start:
{
lean_object* v_res_1568_; 
v_res_1568_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg(v_upperBound_1552_, v_a_1553_, v___x_1554_, v_a_1555_, v_b_1556_, v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_, v___y_1562_, v___y_1563_, v___y_1564_, v___y_1565_, v___y_1566_);
lean_dec(v___y_1566_);
lean_dec_ref(v___y_1565_);
lean_dec(v___y_1564_);
lean_dec_ref(v___y_1563_);
lean_dec(v___y_1562_);
lean_dec_ref(v___y_1561_);
lean_dec(v___y_1560_);
lean_dec_ref(v___y_1559_);
lean_dec(v___y_1558_);
lean_dec(v___y_1557_);
lean_dec_ref(v___x_1554_);
lean_dec_ref(v_a_1553_);
lean_dec(v_upperBound_1552_);
return v_res_1568_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__1___redArg(lean_object* v_upperBound_1569_, lean_object* v___x_1570_, lean_object* v_a_1571_, lean_object* v_a_1572_, lean_object* v_b_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_){
_start:
{
uint8_t v___x_1585_; 
v___x_1585_ = lean_nat_dec_lt(v_a_1572_, v_upperBound_1569_);
if (v___x_1585_ == 0)
{
lean_object* v___x_1586_; 
lean_dec(v_a_1572_);
v___x_1586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1586_, 0, v_b_1573_);
return v___x_1586_;
}
else
{
lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; 
v___x_1587_ = lean_box(0);
v___x_1588_ = l_Lean_instInhabitedExpr;
v___x_1589_ = lean_unsigned_to_nat(1u);
v___x_1590_ = lean_nat_add(v_a_1572_, v___x_1589_);
v___x_1591_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1588_, v_a_1571_, v_a_1572_);
lean_dec(v_a_1572_);
lean_inc(v___x_1590_);
v___x_1592_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg(v___x_1570_, v_a_1571_, v___x_1591_, v___x_1590_, v___x_1587_, v___y_1574_, v___y_1575_, v___y_1576_, v___y_1577_, v___y_1578_, v___y_1579_, v___y_1580_, v___y_1581_, v___y_1582_, v___y_1583_);
lean_dec(v___x_1591_);
if (lean_obj_tag(v___x_1592_) == 0)
{
lean_dec_ref_known(v___x_1592_, 1);
v_a_1572_ = v___x_1590_;
v_b_1573_ = v___x_1587_;
goto _start;
}
else
{
lean_dec(v___x_1590_);
return v___x_1592_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__1___redArg___boxed(lean_object* v_upperBound_1594_, lean_object* v___x_1595_, lean_object* v_a_1596_, lean_object* v_a_1597_, lean_object* v_b_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_){
_start:
{
lean_object* v_res_1610_; 
v_res_1610_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__1___redArg(v_upperBound_1594_, v___x_1595_, v_a_1596_, v_a_1597_, v_b_1598_, v___y_1599_, v___y_1600_, v___y_1601_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_, v___y_1606_, v___y_1607_, v___y_1608_);
lean_dec(v___y_1608_);
lean_dec_ref(v___y_1607_);
lean_dec(v___y_1606_);
lean_dec_ref(v___y_1605_);
lean_dec(v___y_1604_);
lean_dec_ref(v___y_1603_);
lean_dec(v___y_1602_);
lean_dec_ref(v___y_1601_);
lean_dec(v___y_1600_);
lean_dec(v___y_1599_);
lean_dec_ref(v_a_1596_);
lean_dec(v___x_1595_);
lean_dec(v_upperBound_1594_);
return v_res_1610_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq(lean_object* v_a_1611_, lean_object* v_a_1612_, lean_object* v_a_1613_, lean_object* v_a_1614_, lean_object* v_a_1615_, lean_object* v_a_1616_, lean_object* v_a_1617_, lean_object* v_a_1618_, lean_object* v_a_1619_, lean_object* v_a_1620_){
_start:
{
lean_object* v___x_1622_; 
v___x_1622_ = l_Lean_Meta_Grind_getExprs___redArg(v_a_1611_);
if (lean_obj_tag(v___x_1622_) == 0)
{
lean_object* v_a_1623_; lean_object* v_size_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; 
v_a_1623_ = lean_ctor_get(v___x_1622_, 0);
lean_inc(v_a_1623_);
lean_dec_ref_known(v___x_1622_, 1);
v_size_1624_ = lean_ctor_get(v_a_1623_, 2);
lean_inc(v_size_1624_);
v___x_1625_ = lean_unsigned_to_nat(0u);
v___x_1626_ = lean_box(0);
v___x_1627_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__1___redArg(v_size_1624_, v_size_1624_, v_a_1623_, v___x_1625_, v___x_1626_, v_a_1611_, v_a_1612_, v_a_1613_, v_a_1614_, v_a_1615_, v_a_1616_, v_a_1617_, v_a_1618_, v_a_1619_, v_a_1620_);
lean_dec(v_a_1623_);
lean_dec(v_size_1624_);
if (lean_obj_tag(v___x_1627_) == 0)
{
lean_object* v___x_1629_; uint8_t v_isShared_1630_; uint8_t v_isSharedCheck_1634_; 
v_isSharedCheck_1634_ = !lean_is_exclusive(v___x_1627_);
if (v_isSharedCheck_1634_ == 0)
{
lean_object* v_unused_1635_; 
v_unused_1635_ = lean_ctor_get(v___x_1627_, 0);
lean_dec(v_unused_1635_);
v___x_1629_ = v___x_1627_;
v_isShared_1630_ = v_isSharedCheck_1634_;
goto v_resetjp_1628_;
}
else
{
lean_dec(v___x_1627_);
v___x_1629_ = lean_box(0);
v_isShared_1630_ = v_isSharedCheck_1634_;
goto v_resetjp_1628_;
}
v_resetjp_1628_:
{
lean_object* v___x_1632_; 
if (v_isShared_1630_ == 0)
{
lean_ctor_set(v___x_1629_, 0, v___x_1626_);
v___x_1632_ = v___x_1629_;
goto v_reusejp_1631_;
}
else
{
lean_object* v_reuseFailAlloc_1633_; 
v_reuseFailAlloc_1633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1633_, 0, v___x_1626_);
v___x_1632_ = v_reuseFailAlloc_1633_;
goto v_reusejp_1631_;
}
v_reusejp_1631_:
{
return v___x_1632_;
}
}
}
else
{
return v___x_1627_;
}
}
else
{
lean_object* v_a_1636_; lean_object* v___x_1638_; uint8_t v_isShared_1639_; uint8_t v_isSharedCheck_1643_; 
v_a_1636_ = lean_ctor_get(v___x_1622_, 0);
v_isSharedCheck_1643_ = !lean_is_exclusive(v___x_1622_);
if (v_isSharedCheck_1643_ == 0)
{
v___x_1638_ = v___x_1622_;
v_isShared_1639_ = v_isSharedCheck_1643_;
goto v_resetjp_1637_;
}
else
{
lean_inc(v_a_1636_);
lean_dec(v___x_1622_);
v___x_1638_ = lean_box(0);
v_isShared_1639_ = v_isSharedCheck_1643_;
goto v_resetjp_1637_;
}
v_resetjp_1637_:
{
lean_object* v___x_1641_; 
if (v_isShared_1639_ == 0)
{
v___x_1641_ = v___x_1638_;
goto v_reusejp_1640_;
}
else
{
lean_object* v_reuseFailAlloc_1642_; 
v_reuseFailAlloc_1642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1642_, 0, v_a_1636_);
v___x_1641_ = v_reuseFailAlloc_1642_;
goto v_reusejp_1640_;
}
v_reusejp_1640_:
{
return v___x_1641_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq___boxed(lean_object* v_a_1644_, lean_object* v_a_1645_, lean_object* v_a_1646_, lean_object* v_a_1647_, lean_object* v_a_1648_, lean_object* v_a_1649_, lean_object* v_a_1650_, lean_object* v_a_1651_, lean_object* v_a_1652_, lean_object* v_a_1653_, lean_object* v_a_1654_){
_start:
{
lean_object* v_res_1655_; 
v_res_1655_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq(v_a_1644_, v_a_1645_, v_a_1646_, v_a_1647_, v_a_1648_, v_a_1649_, v_a_1650_, v_a_1651_, v_a_1652_, v_a_1653_);
lean_dec(v_a_1653_);
lean_dec_ref(v_a_1652_);
lean_dec(v_a_1651_);
lean_dec_ref(v_a_1650_);
lean_dec(v_a_1649_);
lean_dec_ref(v_a_1648_);
lean_dec(v_a_1647_);
lean_dec_ref(v_a_1646_);
lean_dec(v_a_1645_);
lean_dec(v_a_1644_);
return v_res_1655_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0(lean_object* v_upperBound_1656_, lean_object* v_a_1657_, lean_object* v___x_1658_, lean_object* v_inst_1659_, lean_object* v_R_1660_, lean_object* v_a_1661_, lean_object* v_b_1662_, lean_object* v_c_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_){
_start:
{
lean_object* v___x_1675_; 
v___x_1675_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg(v_upperBound_1656_, v_a_1657_, v___x_1658_, v_a_1661_, v_b_1662_, v___y_1664_, v___y_1665_, v___y_1666_, v___y_1667_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_);
return v___x_1675_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___boxed(lean_object** _args){
lean_object* v_upperBound_1676_ = _args[0];
lean_object* v_a_1677_ = _args[1];
lean_object* v___x_1678_ = _args[2];
lean_object* v_inst_1679_ = _args[3];
lean_object* v_R_1680_ = _args[4];
lean_object* v_a_1681_ = _args[5];
lean_object* v_b_1682_ = _args[6];
lean_object* v_c_1683_ = _args[7];
lean_object* v___y_1684_ = _args[8];
lean_object* v___y_1685_ = _args[9];
lean_object* v___y_1686_ = _args[10];
lean_object* v___y_1687_ = _args[11];
lean_object* v___y_1688_ = _args[12];
lean_object* v___y_1689_ = _args[13];
lean_object* v___y_1690_ = _args[14];
lean_object* v___y_1691_ = _args[15];
lean_object* v___y_1692_ = _args[16];
lean_object* v___y_1693_ = _args[17];
lean_object* v___y_1694_ = _args[18];
_start:
{
lean_object* v_res_1695_; 
v_res_1695_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0(v_upperBound_1676_, v_a_1677_, v___x_1678_, v_inst_1679_, v_R_1680_, v_a_1681_, v_b_1682_, v_c_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_, v___y_1693_);
lean_dec(v___y_1693_);
lean_dec_ref(v___y_1692_);
lean_dec(v___y_1691_);
lean_dec_ref(v___y_1690_);
lean_dec(v___y_1689_);
lean_dec_ref(v___y_1688_);
lean_dec(v___y_1687_);
lean_dec_ref(v___y_1686_);
lean_dec(v___y_1685_);
lean_dec(v___y_1684_);
lean_dec_ref(v___x_1678_);
lean_dec_ref(v_a_1677_);
lean_dec(v_upperBound_1676_);
return v_res_1695_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__1(lean_object* v_upperBound_1696_, lean_object* v___x_1697_, lean_object* v_a_1698_, lean_object* v_inst_1699_, lean_object* v_R_1700_, lean_object* v_a_1701_, lean_object* v_b_1702_, lean_object* v_c_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_){
_start:
{
lean_object* v___x_1715_; 
v___x_1715_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__1___redArg(v_upperBound_1696_, v___x_1697_, v_a_1698_, v_a_1701_, v_b_1702_, v___y_1704_, v___y_1705_, v___y_1706_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_);
return v___x_1715_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__1___boxed(lean_object** _args){
lean_object* v_upperBound_1716_ = _args[0];
lean_object* v___x_1717_ = _args[1];
lean_object* v_a_1718_ = _args[2];
lean_object* v_inst_1719_ = _args[3];
lean_object* v_R_1720_ = _args[4];
lean_object* v_a_1721_ = _args[5];
lean_object* v_b_1722_ = _args[6];
lean_object* v_c_1723_ = _args[7];
lean_object* v___y_1724_ = _args[8];
lean_object* v___y_1725_ = _args[9];
lean_object* v___y_1726_ = _args[10];
lean_object* v___y_1727_ = _args[11];
lean_object* v___y_1728_ = _args[12];
lean_object* v___y_1729_ = _args[13];
lean_object* v___y_1730_ = _args[14];
lean_object* v___y_1731_ = _args[15];
lean_object* v___y_1732_ = _args[16];
lean_object* v___y_1733_ = _args[17];
lean_object* v___y_1734_ = _args[18];
_start:
{
lean_object* v_res_1735_; 
v_res_1735_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__1(v_upperBound_1716_, v___x_1717_, v_a_1718_, v_inst_1719_, v_R_1720_, v_a_1721_, v_b_1722_, v_c_1723_, v___y_1724_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_);
lean_dec(v___y_1733_);
lean_dec_ref(v___y_1732_);
lean_dec(v___y_1731_);
lean_dec_ref(v___y_1730_);
lean_dec(v___y_1729_);
lean_dec_ref(v___y_1728_);
lean_dec(v___y_1727_);
lean_dec_ref(v___y_1726_);
lean_dec(v___y_1725_);
lean_dec(v___y_1724_);
lean_dec_ref(v_a_1718_);
lean_dec(v___x_1717_);
lean_dec(v_upperBound_1716_);
return v_res_1735_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1736_; double v___x_1737_; 
v___x_1736_ = lean_unsigned_to_nat(0u);
v___x_1737_ = lean_float_of_nat(v___x_1736_);
return v___x_1737_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__0___redArg(lean_object* v_cls_1741_, lean_object* v_msg_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_){
_start:
{
lean_object* v_ref_1748_; lean_object* v___x_1749_; lean_object* v_a_1750_; lean_object* v___x_1752_; uint8_t v_isShared_1753_; uint8_t v_isSharedCheck_1794_; 
v_ref_1748_ = lean_ctor_get(v___y_1745_, 5);
v___x_1749_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__1_spec__1(v_msg_1742_, v___y_1743_, v___y_1744_, v___y_1745_, v___y_1746_);
v_a_1750_ = lean_ctor_get(v___x_1749_, 0);
v_isSharedCheck_1794_ = !lean_is_exclusive(v___x_1749_);
if (v_isSharedCheck_1794_ == 0)
{
v___x_1752_ = v___x_1749_;
v_isShared_1753_ = v_isSharedCheck_1794_;
goto v_resetjp_1751_;
}
else
{
lean_inc(v_a_1750_);
lean_dec(v___x_1749_);
v___x_1752_ = lean_box(0);
v_isShared_1753_ = v_isSharedCheck_1794_;
goto v_resetjp_1751_;
}
v_resetjp_1751_:
{
lean_object* v___x_1754_; lean_object* v_traceState_1755_; lean_object* v_env_1756_; lean_object* v_nextMacroScope_1757_; lean_object* v_ngen_1758_; lean_object* v_auxDeclNGen_1759_; lean_object* v_cache_1760_; lean_object* v_messages_1761_; lean_object* v_infoState_1762_; lean_object* v_snapshotTasks_1763_; lean_object* v___x_1765_; uint8_t v_isShared_1766_; uint8_t v_isSharedCheck_1793_; 
v___x_1754_ = lean_st_ref_take(v___y_1746_);
v_traceState_1755_ = lean_ctor_get(v___x_1754_, 4);
v_env_1756_ = lean_ctor_get(v___x_1754_, 0);
v_nextMacroScope_1757_ = lean_ctor_get(v___x_1754_, 1);
v_ngen_1758_ = lean_ctor_get(v___x_1754_, 2);
v_auxDeclNGen_1759_ = lean_ctor_get(v___x_1754_, 3);
v_cache_1760_ = lean_ctor_get(v___x_1754_, 5);
v_messages_1761_ = lean_ctor_get(v___x_1754_, 6);
v_infoState_1762_ = lean_ctor_get(v___x_1754_, 7);
v_snapshotTasks_1763_ = lean_ctor_get(v___x_1754_, 8);
v_isSharedCheck_1793_ = !lean_is_exclusive(v___x_1754_);
if (v_isSharedCheck_1793_ == 0)
{
v___x_1765_ = v___x_1754_;
v_isShared_1766_ = v_isSharedCheck_1793_;
goto v_resetjp_1764_;
}
else
{
lean_inc(v_snapshotTasks_1763_);
lean_inc(v_infoState_1762_);
lean_inc(v_messages_1761_);
lean_inc(v_cache_1760_);
lean_inc(v_traceState_1755_);
lean_inc(v_auxDeclNGen_1759_);
lean_inc(v_ngen_1758_);
lean_inc(v_nextMacroScope_1757_);
lean_inc(v_env_1756_);
lean_dec(v___x_1754_);
v___x_1765_ = lean_box(0);
v_isShared_1766_ = v_isSharedCheck_1793_;
goto v_resetjp_1764_;
}
v_resetjp_1764_:
{
uint64_t v_tid_1767_; lean_object* v_traces_1768_; lean_object* v___x_1770_; uint8_t v_isShared_1771_; uint8_t v_isSharedCheck_1792_; 
v_tid_1767_ = lean_ctor_get_uint64(v_traceState_1755_, sizeof(void*)*1);
v_traces_1768_ = lean_ctor_get(v_traceState_1755_, 0);
v_isSharedCheck_1792_ = !lean_is_exclusive(v_traceState_1755_);
if (v_isSharedCheck_1792_ == 0)
{
v___x_1770_ = v_traceState_1755_;
v_isShared_1771_ = v_isSharedCheck_1792_;
goto v_resetjp_1769_;
}
else
{
lean_inc(v_traces_1768_);
lean_dec(v_traceState_1755_);
v___x_1770_ = lean_box(0);
v_isShared_1771_ = v_isSharedCheck_1792_;
goto v_resetjp_1769_;
}
v_resetjp_1769_:
{
lean_object* v___x_1772_; double v___x_1773_; uint8_t v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1782_; 
v___x_1772_ = lean_box(0);
v___x_1773_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__0___redArg___closed__0);
v___x_1774_ = 0;
v___x_1775_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__0___redArg___closed__1));
v___x_1776_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1776_, 0, v_cls_1741_);
lean_ctor_set(v___x_1776_, 1, v___x_1772_);
lean_ctor_set(v___x_1776_, 2, v___x_1775_);
lean_ctor_set_float(v___x_1776_, sizeof(void*)*3, v___x_1773_);
lean_ctor_set_float(v___x_1776_, sizeof(void*)*3 + 8, v___x_1773_);
lean_ctor_set_uint8(v___x_1776_, sizeof(void*)*3 + 16, v___x_1774_);
v___x_1777_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__0___redArg___closed__2));
v___x_1778_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1778_, 0, v___x_1776_);
lean_ctor_set(v___x_1778_, 1, v_a_1750_);
lean_ctor_set(v___x_1778_, 2, v___x_1777_);
lean_inc(v_ref_1748_);
v___x_1779_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1779_, 0, v_ref_1748_);
lean_ctor_set(v___x_1779_, 1, v___x_1778_);
v___x_1780_ = l_Lean_PersistentArray_push___redArg(v_traces_1768_, v___x_1779_);
if (v_isShared_1771_ == 0)
{
lean_ctor_set(v___x_1770_, 0, v___x_1780_);
v___x_1782_ = v___x_1770_;
goto v_reusejp_1781_;
}
else
{
lean_object* v_reuseFailAlloc_1791_; 
v_reuseFailAlloc_1791_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1791_, 0, v___x_1780_);
lean_ctor_set_uint64(v_reuseFailAlloc_1791_, sizeof(void*)*1, v_tid_1767_);
v___x_1782_ = v_reuseFailAlloc_1791_;
goto v_reusejp_1781_;
}
v_reusejp_1781_:
{
lean_object* v___x_1784_; 
if (v_isShared_1766_ == 0)
{
lean_ctor_set(v___x_1765_, 4, v___x_1782_);
v___x_1784_ = v___x_1765_;
goto v_reusejp_1783_;
}
else
{
lean_object* v_reuseFailAlloc_1790_; 
v_reuseFailAlloc_1790_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1790_, 0, v_env_1756_);
lean_ctor_set(v_reuseFailAlloc_1790_, 1, v_nextMacroScope_1757_);
lean_ctor_set(v_reuseFailAlloc_1790_, 2, v_ngen_1758_);
lean_ctor_set(v_reuseFailAlloc_1790_, 3, v_auxDeclNGen_1759_);
lean_ctor_set(v_reuseFailAlloc_1790_, 4, v___x_1782_);
lean_ctor_set(v_reuseFailAlloc_1790_, 5, v_cache_1760_);
lean_ctor_set(v_reuseFailAlloc_1790_, 6, v_messages_1761_);
lean_ctor_set(v_reuseFailAlloc_1790_, 7, v_infoState_1762_);
lean_ctor_set(v_reuseFailAlloc_1790_, 8, v_snapshotTasks_1763_);
v___x_1784_ = v_reuseFailAlloc_1790_;
goto v_reusejp_1783_;
}
v_reusejp_1783_:
{
lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1788_; 
v___x_1785_ = lean_st_ref_set(v___y_1746_, v___x_1784_);
v___x_1786_ = lean_box(0);
if (v_isShared_1753_ == 0)
{
lean_ctor_set(v___x_1752_, 0, v___x_1786_);
v___x_1788_ = v___x_1752_;
goto v_reusejp_1787_;
}
else
{
lean_object* v_reuseFailAlloc_1789_; 
v_reuseFailAlloc_1789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1789_, 0, v___x_1786_);
v___x_1788_ = v_reuseFailAlloc_1789_;
goto v_reusejp_1787_;
}
v_reusejp_1787_:
{
return v___x_1788_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__0___redArg___boxed(lean_object* v_cls_1795_, lean_object* v_msg_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_){
_start:
{
lean_object* v_res_1802_; 
v_res_1802_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__0___redArg(v_cls_1795_, v_msg_1796_, v___y_1797_, v___y_1798_, v___y_1799_, v___y_1800_);
lean_dec(v___y_1800_);
lean_dec_ref(v___y_1799_);
lean_dec(v___y_1798_);
lean_dec_ref(v___y_1797_);
return v_res_1802_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__6(void){
_start:
{
lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; 
v___x_1813_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__3));
v___x_1814_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__5));
v___x_1815_ = l_Lean_Name_append(v___x_1814_, v___x_1813_);
return v___x_1815_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__8(void){
_start:
{
lean_object* v___x_1817_; lean_object* v___x_1818_; 
v___x_1817_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__7));
v___x_1818_ = l_Lean_stringToMessageData(v___x_1817_);
return v___x_1818_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__10(void){
_start:
{
lean_object* v___x_1820_; lean_object* v___x_1821_; 
v___x_1820_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__9));
v___x_1821_ = l_Lean_stringToMessageData(v___x_1820_);
return v___x_1821_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg(lean_object* v_a_1822_, lean_object* v_as_x27_1823_, lean_object* v_b_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_){
_start:
{
if (lean_obj_tag(v_as_x27_1823_) == 0)
{
lean_object* v___x_1836_; 
lean_dec_ref(v_a_1822_);
v___x_1836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1836_, 0, v_b_1824_);
return v___x_1836_;
}
else
{
lean_object* v_head_1837_; lean_object* v_tail_1838_; lean_object* v___x_1839_; size_t v___x_1840_; size_t v___x_1841_; uint8_t v___x_1842_; 
v_head_1837_ = lean_ctor_get(v_as_x27_1823_, 0);
v_tail_1838_ = lean_ctor_get(v_as_x27_1823_, 1);
v___x_1839_ = lean_box(0);
v___x_1840_ = lean_ptr_addr(v_a_1822_);
v___x_1841_ = lean_ptr_addr(v_head_1837_);
v___x_1842_ = lean_usize_dec_eq(v___x_1840_, v___x_1841_);
if (v___x_1842_ == 0)
{
lean_object* v___x_1843_; 
lean_inc(v_head_1837_);
lean_inc_ref(v_a_1822_);
v___x_1843_ = l_Lean_Meta_Grind_mkEqHEqProof(v_a_1822_, v_head_1837_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_, v___y_1833_, v___y_1834_);
if (lean_obj_tag(v___x_1843_) == 0)
{
lean_object* v_options_1844_; lean_object* v_a_1845_; lean_object* v_inheritedTraceOptions_1846_; uint8_t v_hasTrace_1847_; lean_object* v___x_1848_; lean_object* v___y_1850_; lean_object* v___y_1851_; lean_object* v___y_1852_; lean_object* v___y_1853_; lean_object* v___y_1854_; lean_object* v___y_1855_; lean_object* v___y_1856_; lean_object* v___y_1857_; lean_object* v___y_1858_; lean_object* v___y_1859_; 
v_options_1844_ = lean_ctor_get(v___y_1833_, 2);
v_a_1845_ = lean_ctor_get(v___x_1843_, 0);
lean_inc(v_a_1845_);
lean_dec_ref_known(v___x_1843_, 1);
v_inheritedTraceOptions_1846_ = lean_ctor_get(v___y_1833_, 13);
v_hasTrace_1847_ = lean_ctor_get_uint8(v_options_1844_, sizeof(void*)*1);
v___x_1848_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__3));
if (v_hasTrace_1847_ == 0)
{
v___y_1850_ = v___y_1825_;
v___y_1851_ = v___y_1826_;
v___y_1852_ = v___y_1827_;
v___y_1853_ = v___y_1828_;
v___y_1854_ = v___y_1829_;
v___y_1855_ = v___y_1830_;
v___y_1856_ = v___y_1831_;
v___y_1857_ = v___y_1832_;
v___y_1858_ = v___y_1833_;
v___y_1859_ = v___y_1834_;
goto v___jp_1849_;
}
else
{
lean_object* v___x_1885_; uint8_t v___x_1886_; 
v___x_1885_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__6, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__6_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__6);
v___x_1886_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1846_, v_options_1844_, v___x_1885_);
if (v___x_1886_ == 0)
{
v___y_1850_ = v___y_1825_;
v___y_1851_ = v___y_1826_;
v___y_1852_ = v___y_1827_;
v___y_1853_ = v___y_1828_;
v___y_1854_ = v___y_1829_;
v___y_1855_ = v___y_1830_;
v___y_1856_ = v___y_1831_;
v___y_1857_ = v___y_1832_;
v___y_1858_ = v___y_1833_;
v___y_1859_ = v___y_1834_;
goto v___jp_1849_;
}
else
{
lean_object* v___x_1887_; 
v___x_1887_ = l_Lean_Meta_Grind_updateLastTag(v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_, v___y_1833_, v___y_1834_);
if (lean_obj_tag(v___x_1887_) == 0)
{
lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; 
lean_dec_ref_known(v___x_1887_, 1);
lean_inc_ref(v_a_1822_);
v___x_1888_ = l_Lean_MessageData_ofExpr(v_a_1822_);
v___x_1889_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__10, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__10_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__10);
v___x_1890_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1890_, 0, v___x_1888_);
lean_ctor_set(v___x_1890_, 1, v___x_1889_);
lean_inc(v_head_1837_);
v___x_1891_ = l_Lean_MessageData_ofExpr(v_head_1837_);
v___x_1892_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1892_, 0, v___x_1890_);
lean_ctor_set(v___x_1892_, 1, v___x_1891_);
v___x_1893_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__0___redArg(v___x_1848_, v___x_1892_, v___y_1831_, v___y_1832_, v___y_1833_, v___y_1834_);
if (lean_obj_tag(v___x_1893_) == 0)
{
lean_dec_ref_known(v___x_1893_, 1);
v___y_1850_ = v___y_1825_;
v___y_1851_ = v___y_1826_;
v___y_1852_ = v___y_1827_;
v___y_1853_ = v___y_1828_;
v___y_1854_ = v___y_1829_;
v___y_1855_ = v___y_1830_;
v___y_1856_ = v___y_1831_;
v___y_1857_ = v___y_1832_;
v___y_1858_ = v___y_1833_;
v___y_1859_ = v___y_1834_;
goto v___jp_1849_;
}
else
{
lean_dec(v_a_1845_);
lean_dec_ref(v_a_1822_);
return v___x_1893_;
}
}
else
{
lean_dec(v_a_1845_);
lean_dec_ref(v_a_1822_);
return v___x_1887_;
}
}
}
v___jp_1849_:
{
uint8_t v___x_1860_; lean_object* v___x_1861_; 
v___x_1860_ = 0;
lean_inc(v_a_1845_);
v___x_1861_ = l_Lean_Meta_check(v_a_1845_, v___x_1860_, v___y_1856_, v___y_1857_, v___y_1858_, v___y_1859_);
if (lean_obj_tag(v___x_1861_) == 0)
{
lean_object* v_options_1862_; uint8_t v_hasTrace_1863_; 
lean_dec_ref_known(v___x_1861_, 1);
v_options_1862_ = lean_ctor_get(v___y_1858_, 2);
v_hasTrace_1863_ = lean_ctor_get_uint8(v_options_1862_, sizeof(void*)*1);
if (v_hasTrace_1863_ == 0)
{
lean_dec(v_a_1845_);
v_as_x27_1823_ = v_tail_1838_;
v_b_1824_ = v___x_1839_;
goto _start;
}
else
{
lean_object* v_inheritedTraceOptions_1865_; lean_object* v___x_1866_; uint8_t v___x_1867_; 
v_inheritedTraceOptions_1865_ = lean_ctor_get(v___y_1858_, 13);
v___x_1866_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__6, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__6_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__6);
v___x_1867_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1865_, v_options_1862_, v___x_1866_);
if (v___x_1867_ == 0)
{
lean_dec(v_a_1845_);
v_as_x27_1823_ = v_tail_1838_;
v_b_1824_ = v___x_1839_;
goto _start;
}
else
{
lean_object* v___x_1869_; 
v___x_1869_ = l_Lean_Meta_Grind_updateLastTag(v___y_1850_, v___y_1851_, v___y_1852_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_, v___y_1858_, v___y_1859_);
if (lean_obj_tag(v___x_1869_) == 0)
{
lean_object* v___x_1870_; 
lean_dec_ref_known(v___x_1869_, 1);
lean_inc(v___y_1859_);
lean_inc_ref(v___y_1858_);
lean_inc(v___y_1857_);
lean_inc_ref(v___y_1856_);
v___x_1870_ = lean_infer_type(v_a_1845_, v___y_1856_, v___y_1857_, v___y_1858_, v___y_1859_);
if (lean_obj_tag(v___x_1870_) == 0)
{
lean_object* v_a_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; 
v_a_1871_ = lean_ctor_get(v___x_1870_, 0);
lean_inc(v_a_1871_);
lean_dec_ref_known(v___x_1870_, 1);
v___x_1872_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__8, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__8_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__8);
v___x_1873_ = l_Lean_MessageData_ofExpr(v_a_1871_);
v___x_1874_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1874_, 0, v___x_1872_);
lean_ctor_set(v___x_1874_, 1, v___x_1873_);
v___x_1875_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__0___redArg(v___x_1848_, v___x_1874_, v___y_1856_, v___y_1857_, v___y_1858_, v___y_1859_);
if (lean_obj_tag(v___x_1875_) == 0)
{
lean_dec_ref_known(v___x_1875_, 1);
v_as_x27_1823_ = v_tail_1838_;
v_b_1824_ = v___x_1839_;
goto _start;
}
else
{
lean_dec_ref(v_a_1822_);
return v___x_1875_;
}
}
else
{
lean_object* v_a_1877_; lean_object* v___x_1879_; uint8_t v_isShared_1880_; uint8_t v_isSharedCheck_1884_; 
lean_dec_ref(v_a_1822_);
v_a_1877_ = lean_ctor_get(v___x_1870_, 0);
v_isSharedCheck_1884_ = !lean_is_exclusive(v___x_1870_);
if (v_isSharedCheck_1884_ == 0)
{
v___x_1879_ = v___x_1870_;
v_isShared_1880_ = v_isSharedCheck_1884_;
goto v_resetjp_1878_;
}
else
{
lean_inc(v_a_1877_);
lean_dec(v___x_1870_);
v___x_1879_ = lean_box(0);
v_isShared_1880_ = v_isSharedCheck_1884_;
goto v_resetjp_1878_;
}
v_resetjp_1878_:
{
lean_object* v___x_1882_; 
if (v_isShared_1880_ == 0)
{
v___x_1882_ = v___x_1879_;
goto v_reusejp_1881_;
}
else
{
lean_object* v_reuseFailAlloc_1883_; 
v_reuseFailAlloc_1883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1883_, 0, v_a_1877_);
v___x_1882_ = v_reuseFailAlloc_1883_;
goto v_reusejp_1881_;
}
v_reusejp_1881_:
{
return v___x_1882_;
}
}
}
}
else
{
lean_dec(v_a_1845_);
lean_dec_ref(v_a_1822_);
return v___x_1869_;
}
}
}
}
else
{
lean_dec(v_a_1845_);
lean_dec_ref(v_a_1822_);
return v___x_1861_;
}
}
}
else
{
lean_object* v_a_1894_; lean_object* v___x_1896_; uint8_t v_isShared_1897_; uint8_t v_isSharedCheck_1901_; 
lean_dec_ref(v_a_1822_);
v_a_1894_ = lean_ctor_get(v___x_1843_, 0);
v_isSharedCheck_1901_ = !lean_is_exclusive(v___x_1843_);
if (v_isSharedCheck_1901_ == 0)
{
v___x_1896_ = v___x_1843_;
v_isShared_1897_ = v_isSharedCheck_1901_;
goto v_resetjp_1895_;
}
else
{
lean_inc(v_a_1894_);
lean_dec(v___x_1843_);
v___x_1896_ = lean_box(0);
v_isShared_1897_ = v_isSharedCheck_1901_;
goto v_resetjp_1895_;
}
v_resetjp_1895_:
{
lean_object* v___x_1899_; 
if (v_isShared_1897_ == 0)
{
v___x_1899_ = v___x_1896_;
goto v_reusejp_1898_;
}
else
{
lean_object* v_reuseFailAlloc_1900_; 
v_reuseFailAlloc_1900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1900_, 0, v_a_1894_);
v___x_1899_ = v_reuseFailAlloc_1900_;
goto v_reusejp_1898_;
}
v_reusejp_1898_:
{
return v___x_1899_;
}
}
}
}
else
{
v_as_x27_1823_ = v_tail_1838_;
v_b_1824_ = v___x_1839_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___boxed(lean_object* v_a_1903_, lean_object* v_as_x27_1904_, lean_object* v_b_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_){
_start:
{
lean_object* v_res_1917_; 
v_res_1917_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg(v_a_1903_, v_as_x27_1904_, v_b_1905_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_, v___y_1912_, v___y_1913_, v___y_1914_, v___y_1915_);
lean_dec(v___y_1915_);
lean_dec_ref(v___y_1914_);
lean_dec(v___y_1913_);
lean_dec_ref(v___y_1912_);
lean_dec(v___y_1911_);
lean_dec_ref(v___y_1910_);
lean_dec(v___y_1909_);
lean_dec_ref(v___y_1908_);
lean_dec(v___y_1907_);
lean_dec(v___y_1906_);
lean_dec(v_as_x27_1904_);
return v_res_1917_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__2___redArg(lean_object* v_a_1918_, lean_object* v_as_x27_1919_, lean_object* v_b_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_){
_start:
{
if (lean_obj_tag(v_as_x27_1919_) == 0)
{
lean_object* v___x_1932_; 
v___x_1932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1932_, 0, v_b_1920_);
return v___x_1932_;
}
else
{
lean_object* v_head_1933_; lean_object* v_tail_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; 
v_head_1933_ = lean_ctor_get(v_as_x27_1919_, 0);
v_tail_1934_ = lean_ctor_get(v_as_x27_1919_, 1);
v___x_1935_ = lean_box(0);
lean_inc(v_head_1933_);
v___x_1936_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg(v_head_1933_, v_a_1918_, v___x_1935_, v___y_1921_, v___y_1922_, v___y_1923_, v___y_1924_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_, v___y_1929_, v___y_1930_);
if (lean_obj_tag(v___x_1936_) == 0)
{
lean_dec_ref_known(v___x_1936_, 1);
v_as_x27_1919_ = v_tail_1934_;
v_b_1920_ = v___x_1935_;
goto _start;
}
else
{
return v___x_1936_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__2___redArg___boxed(lean_object* v_a_1938_, lean_object* v_as_x27_1939_, lean_object* v_b_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_){
_start:
{
lean_object* v_res_1952_; 
v_res_1952_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__2___redArg(v_a_1938_, v_as_x27_1939_, v_b_1940_, v___y_1941_, v___y_1942_, v___y_1943_, v___y_1944_, v___y_1945_, v___y_1946_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_);
lean_dec(v___y_1950_);
lean_dec_ref(v___y_1949_);
lean_dec(v___y_1948_);
lean_dec_ref(v___y_1947_);
lean_dec(v___y_1946_);
lean_dec_ref(v___y_1945_);
lean_dec(v___y_1944_);
lean_dec_ref(v___y_1943_);
lean_dec(v___y_1942_);
lean_dec(v___y_1941_);
lean_dec(v_as_x27_1939_);
lean_dec(v_a_1938_);
return v_res_1952_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__3___redArg(lean_object* v_as_x27_1953_, lean_object* v_b_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_){
_start:
{
if (lean_obj_tag(v_as_x27_1953_) == 0)
{
lean_object* v___x_1966_; 
v___x_1966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1966_, 0, v_b_1954_);
return v___x_1966_;
}
else
{
lean_object* v_head_1967_; lean_object* v_tail_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; 
v_head_1967_ = lean_ctor_get(v_as_x27_1953_, 0);
v_tail_1968_ = lean_ctor_get(v_as_x27_1953_, 1);
v___x_1969_ = lean_box(0);
v___x_1970_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__2___redArg(v_head_1967_, v_head_1967_, v___x_1969_, v___y_1955_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_, v___y_1964_);
if (lean_obj_tag(v___x_1970_) == 0)
{
lean_dec_ref_known(v___x_1970_, 1);
v_as_x27_1953_ = v_tail_1968_;
v_b_1954_ = v___x_1969_;
goto _start;
}
else
{
return v___x_1970_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__3___redArg___boxed(lean_object* v_as_x27_1972_, lean_object* v_b_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_){
_start:
{
lean_object* v_res_1985_; 
v_res_1985_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__3___redArg(v_as_x27_1972_, v_b_1973_, v___y_1974_, v___y_1975_, v___y_1976_, v___y_1977_, v___y_1978_, v___y_1979_, v___y_1980_, v___y_1981_, v___y_1982_, v___y_1983_);
lean_dec(v___y_1983_);
lean_dec_ref(v___y_1982_);
lean_dec(v___y_1981_);
lean_dec_ref(v___y_1980_);
lean_dec(v___y_1979_);
lean_dec_ref(v___y_1978_);
lean_dec(v___y_1977_);
lean_dec_ref(v___y_1976_);
lean_dec(v___y_1975_);
lean_dec(v___y_1974_);
lean_dec(v_as_x27_1972_);
return v_res_1985_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs(lean_object* v_a_1986_, lean_object* v_a_1987_, lean_object* v_a_1988_, lean_object* v_a_1989_, lean_object* v_a_1990_, lean_object* v_a_1991_, lean_object* v_a_1992_, lean_object* v_a_1993_, lean_object* v_a_1994_, lean_object* v_a_1995_){
_start:
{
lean_object* v___x_1997_; uint8_t v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; 
v___x_1997_ = lean_st_ref_get(v_a_1986_);
v___x_1998_ = 0;
v___x_1999_ = l_Lean_Meta_Grind_Goal_getEqcs(v___x_1997_, v___x_1998_);
lean_dec(v___x_1997_);
v___x_2000_ = lean_box(0);
v___x_2001_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__3___redArg(v___x_1999_, v___x_2000_, v_a_1986_, v_a_1987_, v_a_1988_, v_a_1989_, v_a_1990_, v_a_1991_, v_a_1992_, v_a_1993_, v_a_1994_, v_a_1995_);
lean_dec(v___x_1999_);
if (lean_obj_tag(v___x_2001_) == 0)
{
lean_object* v___x_2003_; uint8_t v_isShared_2004_; uint8_t v_isSharedCheck_2008_; 
v_isSharedCheck_2008_ = !lean_is_exclusive(v___x_2001_);
if (v_isSharedCheck_2008_ == 0)
{
lean_object* v_unused_2009_; 
v_unused_2009_ = lean_ctor_get(v___x_2001_, 0);
lean_dec(v_unused_2009_);
v___x_2003_ = v___x_2001_;
v_isShared_2004_ = v_isSharedCheck_2008_;
goto v_resetjp_2002_;
}
else
{
lean_dec(v___x_2001_);
v___x_2003_ = lean_box(0);
v_isShared_2004_ = v_isSharedCheck_2008_;
goto v_resetjp_2002_;
}
v_resetjp_2002_:
{
lean_object* v___x_2006_; 
if (v_isShared_2004_ == 0)
{
lean_ctor_set(v___x_2003_, 0, v___x_2000_);
v___x_2006_ = v___x_2003_;
goto v_reusejp_2005_;
}
else
{
lean_object* v_reuseFailAlloc_2007_; 
v_reuseFailAlloc_2007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2007_, 0, v___x_2000_);
v___x_2006_ = v_reuseFailAlloc_2007_;
goto v_reusejp_2005_;
}
v_reusejp_2005_:
{
return v___x_2006_;
}
}
}
else
{
return v___x_2001_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs___boxed(lean_object* v_a_2010_, lean_object* v_a_2011_, lean_object* v_a_2012_, lean_object* v_a_2013_, lean_object* v_a_2014_, lean_object* v_a_2015_, lean_object* v_a_2016_, lean_object* v_a_2017_, lean_object* v_a_2018_, lean_object* v_a_2019_, lean_object* v_a_2020_){
_start:
{
lean_object* v_res_2021_; 
v_res_2021_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs(v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_, v_a_2015_, v_a_2016_, v_a_2017_, v_a_2018_, v_a_2019_);
lean_dec(v_a_2019_);
lean_dec_ref(v_a_2018_);
lean_dec(v_a_2017_);
lean_dec_ref(v_a_2016_);
lean_dec(v_a_2015_);
lean_dec_ref(v_a_2014_);
lean_dec(v_a_2013_);
lean_dec_ref(v_a_2012_);
lean_dec(v_a_2011_);
lean_dec(v_a_2010_);
return v_res_2021_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__0(lean_object* v_cls_2022_, lean_object* v_msg_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_){
_start:
{
lean_object* v___x_2035_; 
v___x_2035_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__0___redArg(v_cls_2022_, v_msg_2023_, v___y_2030_, v___y_2031_, v___y_2032_, v___y_2033_);
return v___x_2035_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__0___boxed(lean_object* v_cls_2036_, lean_object* v_msg_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_){
_start:
{
lean_object* v_res_2049_; 
v_res_2049_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__0(v_cls_2036_, v_msg_2037_, v___y_2038_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_, v___y_2043_, v___y_2044_, v___y_2045_, v___y_2046_, v___y_2047_);
lean_dec(v___y_2047_);
lean_dec_ref(v___y_2046_);
lean_dec(v___y_2045_);
lean_dec_ref(v___y_2044_);
lean_dec(v___y_2043_);
lean_dec_ref(v___y_2042_);
lean_dec(v___y_2041_);
lean_dec_ref(v___y_2040_);
lean_dec(v___y_2039_);
lean_dec(v___y_2038_);
return v_res_2049_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1(lean_object* v_a_2050_, lean_object* v_as_2051_, lean_object* v_as_x27_2052_, lean_object* v_b_2053_, lean_object* v_a_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_){
_start:
{
lean_object* v___x_2066_; 
v___x_2066_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg(v_a_2050_, v_as_x27_2052_, v_b_2053_, v___y_2055_, v___y_2056_, v___y_2057_, v___y_2058_, v___y_2059_, v___y_2060_, v___y_2061_, v___y_2062_, v___y_2063_, v___y_2064_);
return v___x_2066_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___boxed(lean_object* v_a_2067_, lean_object* v_as_2068_, lean_object* v_as_x27_2069_, lean_object* v_b_2070_, lean_object* v_a_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_){
_start:
{
lean_object* v_res_2083_; 
v_res_2083_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1(v_a_2067_, v_as_2068_, v_as_x27_2069_, v_b_2070_, v_a_2071_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_, v___y_2081_);
lean_dec(v___y_2081_);
lean_dec_ref(v___y_2080_);
lean_dec(v___y_2079_);
lean_dec_ref(v___y_2078_);
lean_dec(v___y_2077_);
lean_dec_ref(v___y_2076_);
lean_dec(v___y_2075_);
lean_dec_ref(v___y_2074_);
lean_dec(v___y_2073_);
lean_dec(v___y_2072_);
lean_dec(v_as_x27_2069_);
lean_dec(v_as_2068_);
return v_res_2083_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__2(lean_object* v_a_2084_, lean_object* v_as_2085_, lean_object* v_as_x27_2086_, lean_object* v_b_2087_, lean_object* v_a_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_){
_start:
{
lean_object* v___x_2100_; 
v___x_2100_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__2___redArg(v_a_2084_, v_as_x27_2086_, v_b_2087_, v___y_2089_, v___y_2090_, v___y_2091_, v___y_2092_, v___y_2093_, v___y_2094_, v___y_2095_, v___y_2096_, v___y_2097_, v___y_2098_);
return v___x_2100_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__2___boxed(lean_object* v_a_2101_, lean_object* v_as_2102_, lean_object* v_as_x27_2103_, lean_object* v_b_2104_, lean_object* v_a_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_){
_start:
{
lean_object* v_res_2117_; 
v_res_2117_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__2(v_a_2101_, v_as_2102_, v_as_x27_2103_, v_b_2104_, v_a_2105_, v___y_2106_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_);
lean_dec(v___y_2115_);
lean_dec_ref(v___y_2114_);
lean_dec(v___y_2113_);
lean_dec_ref(v___y_2112_);
lean_dec(v___y_2111_);
lean_dec_ref(v___y_2110_);
lean_dec(v___y_2109_);
lean_dec_ref(v___y_2108_);
lean_dec(v___y_2107_);
lean_dec(v___y_2106_);
lean_dec(v_as_x27_2103_);
lean_dec(v_as_2102_);
lean_dec(v_a_2101_);
return v_res_2117_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__3(lean_object* v_as_2118_, lean_object* v_as_x27_2119_, lean_object* v_b_2120_, lean_object* v_a_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_){
_start:
{
lean_object* v___x_2133_; 
v___x_2133_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__3___redArg(v_as_x27_2119_, v_b_2120_, v___y_2122_, v___y_2123_, v___y_2124_, v___y_2125_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_, v___y_2131_);
return v___x_2133_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__3___boxed(lean_object* v_as_2134_, lean_object* v_as_x27_2135_, lean_object* v_b_2136_, lean_object* v_a_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_){
_start:
{
lean_object* v_res_2149_; 
v_res_2149_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__3(v_as_2134_, v_as_x27_2135_, v_b_2136_, v_a_2137_, v___y_2138_, v___y_2139_, v___y_2140_, v___y_2141_, v___y_2142_, v___y_2143_, v___y_2144_, v___y_2145_, v___y_2146_, v___y_2147_);
lean_dec(v___y_2147_);
lean_dec_ref(v___y_2146_);
lean_dec(v___y_2145_);
lean_dec_ref(v___y_2144_);
lean_dec(v___y_2143_);
lean_dec_ref(v___y_2142_);
lean_dec(v___y_2141_);
lean_dec_ref(v___y_2140_);
lean_dec(v___y_2139_);
lean_dec(v___y_2138_);
lean_dec(v_as_x27_2135_);
lean_dec(v_as_2134_);
return v_res_2149_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_Grind_checkInvariants_spec__0(lean_object* v_opts_2150_, lean_object* v_opt_2151_){
_start:
{
lean_object* v_name_2152_; lean_object* v_defValue_2153_; lean_object* v_map_2154_; lean_object* v___x_2155_; 
v_name_2152_ = lean_ctor_get(v_opt_2151_, 0);
v_defValue_2153_ = lean_ctor_get(v_opt_2151_, 1);
v_map_2154_ = lean_ctor_get(v_opts_2150_, 0);
v___x_2155_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2154_, v_name_2152_);
if (lean_obj_tag(v___x_2155_) == 0)
{
uint8_t v___x_2156_; 
v___x_2156_ = lean_unbox(v_defValue_2153_);
return v___x_2156_;
}
else
{
lean_object* v_val_2157_; 
v_val_2157_ = lean_ctor_get(v___x_2155_, 0);
lean_inc(v_val_2157_);
lean_dec_ref_known(v___x_2155_, 1);
if (lean_obj_tag(v_val_2157_) == 1)
{
uint8_t v_v_2158_; 
v_v_2158_ = lean_ctor_get_uint8(v_val_2157_, 0);
lean_dec_ref_known(v_val_2157_, 0);
return v_v_2158_;
}
else
{
uint8_t v___x_2159_; 
lean_dec(v_val_2157_);
v___x_2159_ = lean_unbox(v_defValue_2153_);
return v___x_2159_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Grind_checkInvariants_spec__0___boxed(lean_object* v_opts_2160_, lean_object* v_opt_2161_){
_start:
{
uint8_t v_res_2162_; lean_object* v_r_2163_; 
v_res_2162_ = l_Lean_Option_get___at___00Lean_Meta_Grind_checkInvariants_spec__0(v_opts_2160_, v_opt_2161_);
lean_dec_ref(v_opt_2161_);
lean_dec_ref(v_opts_2160_);
v_r_2163_ = lean_box(v_res_2162_);
return v_r_2163_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__2_spec__5(lean_object* v_as_2164_, size_t v_sz_2165_, size_t v_i_2166_, lean_object* v_b_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_){
_start:
{
uint8_t v___x_2179_; 
v___x_2179_ = lean_usize_dec_lt(v_i_2166_, v_sz_2165_);
if (v___x_2179_ == 0)
{
lean_object* v___x_2180_; 
v___x_2180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2180_, 0, v_b_2167_);
return v___x_2180_;
}
else
{
lean_object* v___x_2181_; lean_object* v_a_2182_; lean_object* v___x_2183_; 
lean_dec_ref(v_b_2167_);
v___x_2181_ = lean_st_ref_get(v___y_2168_);
v_a_2182_ = lean_array_uget_borrowed(v_as_2164_, v_i_2166_);
lean_inc(v_a_2182_);
v___x_2183_ = l_Lean_Meta_Grind_Goal_getENode(v___x_2181_, v_a_2182_, v___y_2174_, v___y_2175_, v___y_2176_, v___y_2177_);
lean_dec(v___x_2181_);
if (lean_obj_tag(v___x_2183_) == 0)
{
lean_object* v_a_2184_; lean_object* v_self_2185_; lean_object* v___x_2186_; 
v_a_2184_ = lean_ctor_get(v___x_2183_, 0);
lean_inc(v_a_2184_);
lean_dec_ref_known(v___x_2183_, 1);
v_self_2185_ = lean_ctor_get(v_a_2184_, 0);
lean_inc_ref(v_self_2185_);
v___x_2186_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents(v_self_2185_, v___y_2168_, v___y_2169_, v___y_2170_, v___y_2171_, v___y_2172_, v___y_2173_, v___y_2174_, v___y_2175_, v___y_2176_, v___y_2177_);
if (lean_obj_tag(v___x_2186_) == 0)
{
lean_object* v___x_2187_; lean_object* v_a_2189_; lean_object* v___x_2194_; uint8_t v___x_2195_; 
lean_dec_ref_known(v___x_2186_, 1);
v___x_2187_ = lean_box(0);
v___x_2194_ = lean_box(0);
v___x_2195_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_2184_);
if (v___x_2195_ == 0)
{
lean_dec(v_a_2184_);
v_a_2189_ = v___x_2194_;
goto v___jp_2188_;
}
else
{
lean_object* v___x_2196_; 
v___x_2196_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc(v_a_2184_, v___y_2168_, v___y_2169_, v___y_2170_, v___y_2171_, v___y_2172_, v___y_2173_, v___y_2174_, v___y_2175_, v___y_2176_, v___y_2177_);
if (lean_obj_tag(v___x_2196_) == 0)
{
lean_dec_ref_known(v___x_2196_, 1);
v_a_2189_ = v___x_2194_;
goto v___jp_2188_;
}
else
{
lean_object* v_a_2197_; lean_object* v___x_2199_; uint8_t v_isShared_2200_; uint8_t v_isSharedCheck_2204_; 
v_a_2197_ = lean_ctor_get(v___x_2196_, 0);
v_isSharedCheck_2204_ = !lean_is_exclusive(v___x_2196_);
if (v_isSharedCheck_2204_ == 0)
{
v___x_2199_ = v___x_2196_;
v_isShared_2200_ = v_isSharedCheck_2204_;
goto v_resetjp_2198_;
}
else
{
lean_inc(v_a_2197_);
lean_dec(v___x_2196_);
v___x_2199_ = lean_box(0);
v_isShared_2200_ = v_isSharedCheck_2204_;
goto v_resetjp_2198_;
}
v_resetjp_2198_:
{
lean_object* v___x_2202_; 
if (v_isShared_2200_ == 0)
{
v___x_2202_ = v___x_2199_;
goto v_reusejp_2201_;
}
else
{
lean_object* v_reuseFailAlloc_2203_; 
v_reuseFailAlloc_2203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2203_, 0, v_a_2197_);
v___x_2202_ = v_reuseFailAlloc_2203_;
goto v_reusejp_2201_;
}
v_reusejp_2201_:
{
return v___x_2202_;
}
}
}
}
v___jp_2188_:
{
lean_object* v___x_2190_; size_t v___x_2191_; size_t v___x_2192_; 
v___x_2190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2190_, 0, v___x_2187_);
lean_ctor_set(v___x_2190_, 1, v_a_2189_);
v___x_2191_ = ((size_t)1ULL);
v___x_2192_ = lean_usize_add(v_i_2166_, v___x_2191_);
v_i_2166_ = v___x_2192_;
v_b_2167_ = v___x_2190_;
goto _start;
}
}
else
{
lean_object* v_a_2205_; lean_object* v___x_2207_; uint8_t v_isShared_2208_; uint8_t v_isSharedCheck_2212_; 
lean_dec(v_a_2184_);
v_a_2205_ = lean_ctor_get(v___x_2186_, 0);
v_isSharedCheck_2212_ = !lean_is_exclusive(v___x_2186_);
if (v_isSharedCheck_2212_ == 0)
{
v___x_2207_ = v___x_2186_;
v_isShared_2208_ = v_isSharedCheck_2212_;
goto v_resetjp_2206_;
}
else
{
lean_inc(v_a_2205_);
lean_dec(v___x_2186_);
v___x_2207_ = lean_box(0);
v_isShared_2208_ = v_isSharedCheck_2212_;
goto v_resetjp_2206_;
}
v_resetjp_2206_:
{
lean_object* v___x_2210_; 
if (v_isShared_2208_ == 0)
{
v___x_2210_ = v___x_2207_;
goto v_reusejp_2209_;
}
else
{
lean_object* v_reuseFailAlloc_2211_; 
v_reuseFailAlloc_2211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2211_, 0, v_a_2205_);
v___x_2210_ = v_reuseFailAlloc_2211_;
goto v_reusejp_2209_;
}
v_reusejp_2209_:
{
return v___x_2210_;
}
}
}
}
else
{
lean_object* v_a_2213_; lean_object* v___x_2215_; uint8_t v_isShared_2216_; uint8_t v_isSharedCheck_2220_; 
v_a_2213_ = lean_ctor_get(v___x_2183_, 0);
v_isSharedCheck_2220_ = !lean_is_exclusive(v___x_2183_);
if (v_isSharedCheck_2220_ == 0)
{
v___x_2215_ = v___x_2183_;
v_isShared_2216_ = v_isSharedCheck_2220_;
goto v_resetjp_2214_;
}
else
{
lean_inc(v_a_2213_);
lean_dec(v___x_2183_);
v___x_2215_ = lean_box(0);
v_isShared_2216_ = v_isSharedCheck_2220_;
goto v_resetjp_2214_;
}
v_resetjp_2214_:
{
lean_object* v___x_2218_; 
if (v_isShared_2216_ == 0)
{
v___x_2218_ = v___x_2215_;
goto v_reusejp_2217_;
}
else
{
lean_object* v_reuseFailAlloc_2219_; 
v_reuseFailAlloc_2219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2219_, 0, v_a_2213_);
v___x_2218_ = v_reuseFailAlloc_2219_;
goto v_reusejp_2217_;
}
v_reusejp_2217_:
{
return v___x_2218_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__2_spec__5___boxed(lean_object* v_as_2221_, lean_object* v_sz_2222_, lean_object* v_i_2223_, lean_object* v_b_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_){
_start:
{
size_t v_sz_boxed_2236_; size_t v_i_boxed_2237_; lean_object* v_res_2238_; 
v_sz_boxed_2236_ = lean_unbox_usize(v_sz_2222_);
lean_dec(v_sz_2222_);
v_i_boxed_2237_ = lean_unbox_usize(v_i_2223_);
lean_dec(v_i_2223_);
v_res_2238_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__2_spec__5(v_as_2221_, v_sz_boxed_2236_, v_i_boxed_2237_, v_b_2224_, v___y_2225_, v___y_2226_, v___y_2227_, v___y_2228_, v___y_2229_, v___y_2230_, v___y_2231_, v___y_2232_, v___y_2233_, v___y_2234_);
lean_dec(v___y_2234_);
lean_dec_ref(v___y_2233_);
lean_dec(v___y_2232_);
lean_dec_ref(v___y_2231_);
lean_dec(v___y_2230_);
lean_dec_ref(v___y_2229_);
lean_dec(v___y_2228_);
lean_dec_ref(v___y_2227_);
lean_dec(v___y_2226_);
lean_dec(v___y_2225_);
lean_dec_ref(v_as_2221_);
return v_res_2238_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__2(lean_object* v_as_2242_, size_t v_sz_2243_, size_t v_i_2244_, lean_object* v_b_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_){
_start:
{
uint8_t v___x_2257_; 
v___x_2257_ = lean_usize_dec_lt(v_i_2244_, v_sz_2243_);
if (v___x_2257_ == 0)
{
lean_object* v___x_2258_; 
v___x_2258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2258_, 0, v_b_2245_);
return v___x_2258_;
}
else
{
lean_object* v___x_2259_; lean_object* v_a_2260_; lean_object* v___x_2261_; 
lean_dec_ref(v_b_2245_);
v___x_2259_ = lean_st_ref_get(v___y_2246_);
v_a_2260_ = lean_array_uget_borrowed(v_as_2242_, v_i_2244_);
lean_inc(v_a_2260_);
v___x_2261_ = l_Lean_Meta_Grind_Goal_getENode(v___x_2259_, v_a_2260_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_);
lean_dec(v___x_2259_);
if (lean_obj_tag(v___x_2261_) == 0)
{
lean_object* v_a_2262_; lean_object* v_self_2263_; lean_object* v___x_2264_; 
v_a_2262_ = lean_ctor_get(v___x_2261_, 0);
lean_inc(v_a_2262_);
lean_dec_ref_known(v___x_2261_, 1);
v_self_2263_ = lean_ctor_get(v_a_2262_, 0);
lean_inc_ref(v_self_2263_);
v___x_2264_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents(v_self_2263_, v___y_2246_, v___y_2247_, v___y_2248_, v___y_2249_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_);
if (lean_obj_tag(v___x_2264_) == 0)
{
uint8_t v___x_2270_; 
lean_dec_ref_known(v___x_2264_, 1);
v___x_2270_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_2262_);
if (v___x_2270_ == 0)
{
lean_dec(v_a_2262_);
goto v___jp_2265_;
}
else
{
lean_object* v___x_2271_; 
v___x_2271_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc(v_a_2262_, v___y_2246_, v___y_2247_, v___y_2248_, v___y_2249_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_);
if (lean_obj_tag(v___x_2271_) == 0)
{
lean_dec_ref_known(v___x_2271_, 1);
goto v___jp_2265_;
}
else
{
lean_object* v_a_2272_; lean_object* v___x_2274_; uint8_t v_isShared_2275_; uint8_t v_isSharedCheck_2279_; 
v_a_2272_ = lean_ctor_get(v___x_2271_, 0);
v_isSharedCheck_2279_ = !lean_is_exclusive(v___x_2271_);
if (v_isSharedCheck_2279_ == 0)
{
v___x_2274_ = v___x_2271_;
v_isShared_2275_ = v_isSharedCheck_2279_;
goto v_resetjp_2273_;
}
else
{
lean_inc(v_a_2272_);
lean_dec(v___x_2271_);
v___x_2274_ = lean_box(0);
v_isShared_2275_ = v_isSharedCheck_2279_;
goto v_resetjp_2273_;
}
v_resetjp_2273_:
{
lean_object* v___x_2277_; 
if (v_isShared_2275_ == 0)
{
v___x_2277_ = v___x_2274_;
goto v_reusejp_2276_;
}
else
{
lean_object* v_reuseFailAlloc_2278_; 
v_reuseFailAlloc_2278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2278_, 0, v_a_2272_);
v___x_2277_ = v_reuseFailAlloc_2278_;
goto v_reusejp_2276_;
}
v_reusejp_2276_:
{
return v___x_2277_;
}
}
}
}
v___jp_2265_:
{
lean_object* v___x_2266_; size_t v___x_2267_; size_t v___x_2268_; lean_object* v___x_2269_; 
v___x_2266_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__2___closed__0));
v___x_2267_ = ((size_t)1ULL);
v___x_2268_ = lean_usize_add(v_i_2244_, v___x_2267_);
v___x_2269_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__2_spec__5(v_as_2242_, v_sz_2243_, v___x_2268_, v___x_2266_, v___y_2246_, v___y_2247_, v___y_2248_, v___y_2249_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_);
return v___x_2269_;
}
}
else
{
lean_object* v_a_2280_; lean_object* v___x_2282_; uint8_t v_isShared_2283_; uint8_t v_isSharedCheck_2287_; 
lean_dec(v_a_2262_);
v_a_2280_ = lean_ctor_get(v___x_2264_, 0);
v_isSharedCheck_2287_ = !lean_is_exclusive(v___x_2264_);
if (v_isSharedCheck_2287_ == 0)
{
v___x_2282_ = v___x_2264_;
v_isShared_2283_ = v_isSharedCheck_2287_;
goto v_resetjp_2281_;
}
else
{
lean_inc(v_a_2280_);
lean_dec(v___x_2264_);
v___x_2282_ = lean_box(0);
v_isShared_2283_ = v_isSharedCheck_2287_;
goto v_resetjp_2281_;
}
v_resetjp_2281_:
{
lean_object* v___x_2285_; 
if (v_isShared_2283_ == 0)
{
v___x_2285_ = v___x_2282_;
goto v_reusejp_2284_;
}
else
{
lean_object* v_reuseFailAlloc_2286_; 
v_reuseFailAlloc_2286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2286_, 0, v_a_2280_);
v___x_2285_ = v_reuseFailAlloc_2286_;
goto v_reusejp_2284_;
}
v_reusejp_2284_:
{
return v___x_2285_;
}
}
}
}
else
{
lean_object* v_a_2288_; lean_object* v___x_2290_; uint8_t v_isShared_2291_; uint8_t v_isSharedCheck_2295_; 
v_a_2288_ = lean_ctor_get(v___x_2261_, 0);
v_isSharedCheck_2295_ = !lean_is_exclusive(v___x_2261_);
if (v_isSharedCheck_2295_ == 0)
{
v___x_2290_ = v___x_2261_;
v_isShared_2291_ = v_isSharedCheck_2295_;
goto v_resetjp_2289_;
}
else
{
lean_inc(v_a_2288_);
lean_dec(v___x_2261_);
v___x_2290_ = lean_box(0);
v_isShared_2291_ = v_isSharedCheck_2295_;
goto v_resetjp_2289_;
}
v_resetjp_2289_:
{
lean_object* v___x_2293_; 
if (v_isShared_2291_ == 0)
{
v___x_2293_ = v___x_2290_;
goto v_reusejp_2292_;
}
else
{
lean_object* v_reuseFailAlloc_2294_; 
v_reuseFailAlloc_2294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2294_, 0, v_a_2288_);
v___x_2293_ = v_reuseFailAlloc_2294_;
goto v_reusejp_2292_;
}
v_reusejp_2292_:
{
return v___x_2293_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__2___boxed(lean_object* v_as_2296_, lean_object* v_sz_2297_, lean_object* v_i_2298_, lean_object* v_b_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_){
_start:
{
size_t v_sz_boxed_2311_; size_t v_i_boxed_2312_; lean_object* v_res_2313_; 
v_sz_boxed_2311_ = lean_unbox_usize(v_sz_2297_);
lean_dec(v_sz_2297_);
v_i_boxed_2312_ = lean_unbox_usize(v_i_2298_);
lean_dec(v_i_2298_);
v_res_2313_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__2(v_as_2296_, v_sz_boxed_2311_, v_i_boxed_2312_, v_b_2299_, v___y_2300_, v___y_2301_, v___y_2302_, v___y_2303_, v___y_2304_, v___y_2305_, v___y_2306_, v___y_2307_, v___y_2308_, v___y_2309_);
lean_dec(v___y_2309_);
lean_dec_ref(v___y_2308_);
lean_dec(v___y_2307_);
lean_dec_ref(v___y_2306_);
lean_dec(v___y_2305_);
lean_dec_ref(v___y_2304_);
lean_dec(v___y_2303_);
lean_dec_ref(v___y_2302_);
lean_dec(v___y_2301_);
lean_dec(v___y_2300_);
lean_dec_ref(v_as_2296_);
return v_res_2313_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__1_spec__3_spec__4(lean_object* v_as_2314_, size_t v_sz_2315_, size_t v_i_2316_, lean_object* v_b_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_){
_start:
{
uint8_t v___x_2329_; 
v___x_2329_ = lean_usize_dec_lt(v_i_2316_, v_sz_2315_);
if (v___x_2329_ == 0)
{
lean_object* v___x_2330_; 
v___x_2330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2330_, 0, v_b_2317_);
return v___x_2330_;
}
else
{
lean_object* v___x_2331_; lean_object* v_a_2332_; lean_object* v___x_2333_; 
lean_dec_ref(v_b_2317_);
v___x_2331_ = lean_st_ref_get(v___y_2318_);
v_a_2332_ = lean_array_uget_borrowed(v_as_2314_, v_i_2316_);
lean_inc(v_a_2332_);
v___x_2333_ = l_Lean_Meta_Grind_Goal_getENode(v___x_2331_, v_a_2332_, v___y_2324_, v___y_2325_, v___y_2326_, v___y_2327_);
lean_dec(v___x_2331_);
if (lean_obj_tag(v___x_2333_) == 0)
{
lean_object* v_a_2334_; lean_object* v_self_2335_; lean_object* v___x_2336_; 
v_a_2334_ = lean_ctor_get(v___x_2333_, 0);
lean_inc(v_a_2334_);
lean_dec_ref_known(v___x_2333_, 1);
v_self_2335_ = lean_ctor_get(v_a_2334_, 0);
lean_inc_ref(v_self_2335_);
v___x_2336_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents(v_self_2335_, v___y_2318_, v___y_2319_, v___y_2320_, v___y_2321_, v___y_2322_, v___y_2323_, v___y_2324_, v___y_2325_, v___y_2326_, v___y_2327_);
if (lean_obj_tag(v___x_2336_) == 0)
{
lean_object* v___x_2337_; lean_object* v_a_2339_; lean_object* v___x_2344_; uint8_t v___x_2345_; 
lean_dec_ref_known(v___x_2336_, 1);
v___x_2337_ = lean_box(0);
v___x_2344_ = lean_box(0);
v___x_2345_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_2334_);
if (v___x_2345_ == 0)
{
lean_dec(v_a_2334_);
v_a_2339_ = v___x_2344_;
goto v___jp_2338_;
}
else
{
lean_object* v___x_2346_; 
v___x_2346_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc(v_a_2334_, v___y_2318_, v___y_2319_, v___y_2320_, v___y_2321_, v___y_2322_, v___y_2323_, v___y_2324_, v___y_2325_, v___y_2326_, v___y_2327_);
if (lean_obj_tag(v___x_2346_) == 0)
{
lean_dec_ref_known(v___x_2346_, 1);
v_a_2339_ = v___x_2344_;
goto v___jp_2338_;
}
else
{
lean_object* v_a_2347_; lean_object* v___x_2349_; uint8_t v_isShared_2350_; uint8_t v_isSharedCheck_2354_; 
v_a_2347_ = lean_ctor_get(v___x_2346_, 0);
v_isSharedCheck_2354_ = !lean_is_exclusive(v___x_2346_);
if (v_isSharedCheck_2354_ == 0)
{
v___x_2349_ = v___x_2346_;
v_isShared_2350_ = v_isSharedCheck_2354_;
goto v_resetjp_2348_;
}
else
{
lean_inc(v_a_2347_);
lean_dec(v___x_2346_);
v___x_2349_ = lean_box(0);
v_isShared_2350_ = v_isSharedCheck_2354_;
goto v_resetjp_2348_;
}
v_resetjp_2348_:
{
lean_object* v___x_2352_; 
if (v_isShared_2350_ == 0)
{
v___x_2352_ = v___x_2349_;
goto v_reusejp_2351_;
}
else
{
lean_object* v_reuseFailAlloc_2353_; 
v_reuseFailAlloc_2353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2353_, 0, v_a_2347_);
v___x_2352_ = v_reuseFailAlloc_2353_;
goto v_reusejp_2351_;
}
v_reusejp_2351_:
{
return v___x_2352_;
}
}
}
}
v___jp_2338_:
{
lean_object* v___x_2340_; size_t v___x_2341_; size_t v___x_2342_; 
v___x_2340_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2340_, 0, v___x_2337_);
lean_ctor_set(v___x_2340_, 1, v_a_2339_);
v___x_2341_ = ((size_t)1ULL);
v___x_2342_ = lean_usize_add(v_i_2316_, v___x_2341_);
v_i_2316_ = v___x_2342_;
v_b_2317_ = v___x_2340_;
goto _start;
}
}
else
{
lean_object* v_a_2355_; lean_object* v___x_2357_; uint8_t v_isShared_2358_; uint8_t v_isSharedCheck_2362_; 
lean_dec(v_a_2334_);
v_a_2355_ = lean_ctor_get(v___x_2336_, 0);
v_isSharedCheck_2362_ = !lean_is_exclusive(v___x_2336_);
if (v_isSharedCheck_2362_ == 0)
{
v___x_2357_ = v___x_2336_;
v_isShared_2358_ = v_isSharedCheck_2362_;
goto v_resetjp_2356_;
}
else
{
lean_inc(v_a_2355_);
lean_dec(v___x_2336_);
v___x_2357_ = lean_box(0);
v_isShared_2358_ = v_isSharedCheck_2362_;
goto v_resetjp_2356_;
}
v_resetjp_2356_:
{
lean_object* v___x_2360_; 
if (v_isShared_2358_ == 0)
{
v___x_2360_ = v___x_2357_;
goto v_reusejp_2359_;
}
else
{
lean_object* v_reuseFailAlloc_2361_; 
v_reuseFailAlloc_2361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2361_, 0, v_a_2355_);
v___x_2360_ = v_reuseFailAlloc_2361_;
goto v_reusejp_2359_;
}
v_reusejp_2359_:
{
return v___x_2360_;
}
}
}
}
else
{
lean_object* v_a_2363_; lean_object* v___x_2365_; uint8_t v_isShared_2366_; uint8_t v_isSharedCheck_2370_; 
v_a_2363_ = lean_ctor_get(v___x_2333_, 0);
v_isSharedCheck_2370_ = !lean_is_exclusive(v___x_2333_);
if (v_isSharedCheck_2370_ == 0)
{
v___x_2365_ = v___x_2333_;
v_isShared_2366_ = v_isSharedCheck_2370_;
goto v_resetjp_2364_;
}
else
{
lean_inc(v_a_2363_);
lean_dec(v___x_2333_);
v___x_2365_ = lean_box(0);
v_isShared_2366_ = v_isSharedCheck_2370_;
goto v_resetjp_2364_;
}
v_resetjp_2364_:
{
lean_object* v___x_2368_; 
if (v_isShared_2366_ == 0)
{
v___x_2368_ = v___x_2365_;
goto v_reusejp_2367_;
}
else
{
lean_object* v_reuseFailAlloc_2369_; 
v_reuseFailAlloc_2369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2369_, 0, v_a_2363_);
v___x_2368_ = v_reuseFailAlloc_2369_;
goto v_reusejp_2367_;
}
v_reusejp_2367_:
{
return v___x_2368_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__1_spec__3_spec__4___boxed(lean_object* v_as_2371_, lean_object* v_sz_2372_, lean_object* v_i_2373_, lean_object* v_b_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_){
_start:
{
size_t v_sz_boxed_2386_; size_t v_i_boxed_2387_; lean_object* v_res_2388_; 
v_sz_boxed_2386_ = lean_unbox_usize(v_sz_2372_);
lean_dec(v_sz_2372_);
v_i_boxed_2387_ = lean_unbox_usize(v_i_2373_);
lean_dec(v_i_2373_);
v_res_2388_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__1_spec__3_spec__4(v_as_2371_, v_sz_boxed_2386_, v_i_boxed_2387_, v_b_2374_, v___y_2375_, v___y_2376_, v___y_2377_, v___y_2378_, v___y_2379_, v___y_2380_, v___y_2381_, v___y_2382_, v___y_2383_, v___y_2384_);
lean_dec(v___y_2384_);
lean_dec_ref(v___y_2383_);
lean_dec(v___y_2382_);
lean_dec_ref(v___y_2381_);
lean_dec(v___y_2380_);
lean_dec_ref(v___y_2379_);
lean_dec(v___y_2378_);
lean_dec_ref(v___y_2377_);
lean_dec(v___y_2376_);
lean_dec(v___y_2375_);
lean_dec_ref(v_as_2371_);
return v_res_2388_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__1_spec__3(lean_object* v_as_2392_, size_t v_sz_2393_, size_t v_i_2394_, lean_object* v_b_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_){
_start:
{
uint8_t v___x_2407_; 
v___x_2407_ = lean_usize_dec_lt(v_i_2394_, v_sz_2393_);
if (v___x_2407_ == 0)
{
lean_object* v___x_2408_; 
v___x_2408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2408_, 0, v_b_2395_);
return v___x_2408_;
}
else
{
lean_object* v___x_2409_; lean_object* v_a_2410_; lean_object* v___x_2411_; 
lean_dec_ref(v_b_2395_);
v___x_2409_ = lean_st_ref_get(v___y_2396_);
v_a_2410_ = lean_array_uget_borrowed(v_as_2392_, v_i_2394_);
lean_inc(v_a_2410_);
v___x_2411_ = l_Lean_Meta_Grind_Goal_getENode(v___x_2409_, v_a_2410_, v___y_2402_, v___y_2403_, v___y_2404_, v___y_2405_);
lean_dec(v___x_2409_);
if (lean_obj_tag(v___x_2411_) == 0)
{
lean_object* v_a_2412_; lean_object* v_self_2413_; lean_object* v___x_2414_; 
v_a_2412_ = lean_ctor_get(v___x_2411_, 0);
lean_inc(v_a_2412_);
lean_dec_ref_known(v___x_2411_, 1);
v_self_2413_ = lean_ctor_get(v_a_2412_, 0);
lean_inc_ref(v_self_2413_);
v___x_2414_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents(v_self_2413_, v___y_2396_, v___y_2397_, v___y_2398_, v___y_2399_, v___y_2400_, v___y_2401_, v___y_2402_, v___y_2403_, v___y_2404_, v___y_2405_);
if (lean_obj_tag(v___x_2414_) == 0)
{
uint8_t v___x_2420_; 
lean_dec_ref_known(v___x_2414_, 1);
v___x_2420_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_2412_);
if (v___x_2420_ == 0)
{
lean_dec(v_a_2412_);
goto v___jp_2415_;
}
else
{
lean_object* v___x_2421_; 
v___x_2421_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc(v_a_2412_, v___y_2396_, v___y_2397_, v___y_2398_, v___y_2399_, v___y_2400_, v___y_2401_, v___y_2402_, v___y_2403_, v___y_2404_, v___y_2405_);
if (lean_obj_tag(v___x_2421_) == 0)
{
lean_dec_ref_known(v___x_2421_, 1);
goto v___jp_2415_;
}
else
{
lean_object* v_a_2422_; lean_object* v___x_2424_; uint8_t v_isShared_2425_; uint8_t v_isSharedCheck_2429_; 
v_a_2422_ = lean_ctor_get(v___x_2421_, 0);
v_isSharedCheck_2429_ = !lean_is_exclusive(v___x_2421_);
if (v_isSharedCheck_2429_ == 0)
{
v___x_2424_ = v___x_2421_;
v_isShared_2425_ = v_isSharedCheck_2429_;
goto v_resetjp_2423_;
}
else
{
lean_inc(v_a_2422_);
lean_dec(v___x_2421_);
v___x_2424_ = lean_box(0);
v_isShared_2425_ = v_isSharedCheck_2429_;
goto v_resetjp_2423_;
}
v_resetjp_2423_:
{
lean_object* v___x_2427_; 
if (v_isShared_2425_ == 0)
{
v___x_2427_ = v___x_2424_;
goto v_reusejp_2426_;
}
else
{
lean_object* v_reuseFailAlloc_2428_; 
v_reuseFailAlloc_2428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2428_, 0, v_a_2422_);
v___x_2427_ = v_reuseFailAlloc_2428_;
goto v_reusejp_2426_;
}
v_reusejp_2426_:
{
return v___x_2427_;
}
}
}
}
v___jp_2415_:
{
lean_object* v___x_2416_; size_t v___x_2417_; size_t v___x_2418_; lean_object* v___x_2419_; 
v___x_2416_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__1_spec__3___closed__0));
v___x_2417_ = ((size_t)1ULL);
v___x_2418_ = lean_usize_add(v_i_2394_, v___x_2417_);
v___x_2419_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__1_spec__3_spec__4(v_as_2392_, v_sz_2393_, v___x_2418_, v___x_2416_, v___y_2396_, v___y_2397_, v___y_2398_, v___y_2399_, v___y_2400_, v___y_2401_, v___y_2402_, v___y_2403_, v___y_2404_, v___y_2405_);
return v___x_2419_;
}
}
else
{
lean_object* v_a_2430_; lean_object* v___x_2432_; uint8_t v_isShared_2433_; uint8_t v_isSharedCheck_2437_; 
lean_dec(v_a_2412_);
v_a_2430_ = lean_ctor_get(v___x_2414_, 0);
v_isSharedCheck_2437_ = !lean_is_exclusive(v___x_2414_);
if (v_isSharedCheck_2437_ == 0)
{
v___x_2432_ = v___x_2414_;
v_isShared_2433_ = v_isSharedCheck_2437_;
goto v_resetjp_2431_;
}
else
{
lean_inc(v_a_2430_);
lean_dec(v___x_2414_);
v___x_2432_ = lean_box(0);
v_isShared_2433_ = v_isSharedCheck_2437_;
goto v_resetjp_2431_;
}
v_resetjp_2431_:
{
lean_object* v___x_2435_; 
if (v_isShared_2433_ == 0)
{
v___x_2435_ = v___x_2432_;
goto v_reusejp_2434_;
}
else
{
lean_object* v_reuseFailAlloc_2436_; 
v_reuseFailAlloc_2436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2436_, 0, v_a_2430_);
v___x_2435_ = v_reuseFailAlloc_2436_;
goto v_reusejp_2434_;
}
v_reusejp_2434_:
{
return v___x_2435_;
}
}
}
}
else
{
lean_object* v_a_2438_; lean_object* v___x_2440_; uint8_t v_isShared_2441_; uint8_t v_isSharedCheck_2445_; 
v_a_2438_ = lean_ctor_get(v___x_2411_, 0);
v_isSharedCheck_2445_ = !lean_is_exclusive(v___x_2411_);
if (v_isSharedCheck_2445_ == 0)
{
v___x_2440_ = v___x_2411_;
v_isShared_2441_ = v_isSharedCheck_2445_;
goto v_resetjp_2439_;
}
else
{
lean_inc(v_a_2438_);
lean_dec(v___x_2411_);
v___x_2440_ = lean_box(0);
v_isShared_2441_ = v_isSharedCheck_2445_;
goto v_resetjp_2439_;
}
v_resetjp_2439_:
{
lean_object* v___x_2443_; 
if (v_isShared_2441_ == 0)
{
v___x_2443_ = v___x_2440_;
goto v_reusejp_2442_;
}
else
{
lean_object* v_reuseFailAlloc_2444_; 
v_reuseFailAlloc_2444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2444_, 0, v_a_2438_);
v___x_2443_ = v_reuseFailAlloc_2444_;
goto v_reusejp_2442_;
}
v_reusejp_2442_:
{
return v___x_2443_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__1_spec__3___boxed(lean_object* v_as_2446_, lean_object* v_sz_2447_, lean_object* v_i_2448_, lean_object* v_b_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_){
_start:
{
size_t v_sz_boxed_2461_; size_t v_i_boxed_2462_; lean_object* v_res_2463_; 
v_sz_boxed_2461_ = lean_unbox_usize(v_sz_2447_);
lean_dec(v_sz_2447_);
v_i_boxed_2462_ = lean_unbox_usize(v_i_2448_);
lean_dec(v_i_2448_);
v_res_2463_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__1_spec__3(v_as_2446_, v_sz_boxed_2461_, v_i_boxed_2462_, v_b_2449_, v___y_2450_, v___y_2451_, v___y_2452_, v___y_2453_, v___y_2454_, v___y_2455_, v___y_2456_, v___y_2457_, v___y_2458_, v___y_2459_);
lean_dec(v___y_2459_);
lean_dec_ref(v___y_2458_);
lean_dec(v___y_2457_);
lean_dec_ref(v___y_2456_);
lean_dec(v___y_2455_);
lean_dec_ref(v___y_2454_);
lean_dec(v___y_2453_);
lean_dec_ref(v___y_2452_);
lean_dec(v___y_2451_);
lean_dec(v___y_2450_);
lean_dec_ref(v_as_2446_);
return v_res_2463_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__1(lean_object* v_init_2464_, lean_object* v_n_2465_, lean_object* v_b_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_){
_start:
{
if (lean_obj_tag(v_n_2465_) == 0)
{
lean_object* v_cs_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; size_t v_sz_2481_; size_t v___x_2482_; lean_object* v___x_2483_; 
v_cs_2478_ = lean_ctor_get(v_n_2465_, 0);
v___x_2479_ = lean_box(0);
v___x_2480_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2480_, 0, v___x_2479_);
lean_ctor_set(v___x_2480_, 1, v_b_2466_);
v_sz_2481_ = lean_array_size(v_cs_2478_);
v___x_2482_ = ((size_t)0ULL);
v___x_2483_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__1_spec__2(v_init_2464_, v_cs_2478_, v_sz_2481_, v___x_2482_, v___x_2480_, v___y_2467_, v___y_2468_, v___y_2469_, v___y_2470_, v___y_2471_, v___y_2472_, v___y_2473_, v___y_2474_, v___y_2475_, v___y_2476_);
if (lean_obj_tag(v___x_2483_) == 0)
{
lean_object* v_a_2484_; lean_object* v___x_2486_; uint8_t v_isShared_2487_; uint8_t v_isSharedCheck_2498_; 
v_a_2484_ = lean_ctor_get(v___x_2483_, 0);
v_isSharedCheck_2498_ = !lean_is_exclusive(v___x_2483_);
if (v_isSharedCheck_2498_ == 0)
{
v___x_2486_ = v___x_2483_;
v_isShared_2487_ = v_isSharedCheck_2498_;
goto v_resetjp_2485_;
}
else
{
lean_inc(v_a_2484_);
lean_dec(v___x_2483_);
v___x_2486_ = lean_box(0);
v_isShared_2487_ = v_isSharedCheck_2498_;
goto v_resetjp_2485_;
}
v_resetjp_2485_:
{
lean_object* v_fst_2488_; 
v_fst_2488_ = lean_ctor_get(v_a_2484_, 0);
if (lean_obj_tag(v_fst_2488_) == 0)
{
lean_object* v_snd_2489_; lean_object* v___x_2490_; lean_object* v___x_2492_; 
v_snd_2489_ = lean_ctor_get(v_a_2484_, 1);
lean_inc(v_snd_2489_);
lean_dec(v_a_2484_);
v___x_2490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2490_, 0, v_snd_2489_);
if (v_isShared_2487_ == 0)
{
lean_ctor_set(v___x_2486_, 0, v___x_2490_);
v___x_2492_ = v___x_2486_;
goto v_reusejp_2491_;
}
else
{
lean_object* v_reuseFailAlloc_2493_; 
v_reuseFailAlloc_2493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2493_, 0, v___x_2490_);
v___x_2492_ = v_reuseFailAlloc_2493_;
goto v_reusejp_2491_;
}
v_reusejp_2491_:
{
return v___x_2492_;
}
}
else
{
lean_object* v_val_2494_; lean_object* v___x_2496_; 
lean_inc_ref(v_fst_2488_);
lean_dec(v_a_2484_);
v_val_2494_ = lean_ctor_get(v_fst_2488_, 0);
lean_inc(v_val_2494_);
lean_dec_ref_known(v_fst_2488_, 1);
if (v_isShared_2487_ == 0)
{
lean_ctor_set(v___x_2486_, 0, v_val_2494_);
v___x_2496_ = v___x_2486_;
goto v_reusejp_2495_;
}
else
{
lean_object* v_reuseFailAlloc_2497_; 
v_reuseFailAlloc_2497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2497_, 0, v_val_2494_);
v___x_2496_ = v_reuseFailAlloc_2497_;
goto v_reusejp_2495_;
}
v_reusejp_2495_:
{
return v___x_2496_;
}
}
}
}
else
{
lean_object* v_a_2499_; lean_object* v___x_2501_; uint8_t v_isShared_2502_; uint8_t v_isSharedCheck_2506_; 
v_a_2499_ = lean_ctor_get(v___x_2483_, 0);
v_isSharedCheck_2506_ = !lean_is_exclusive(v___x_2483_);
if (v_isSharedCheck_2506_ == 0)
{
v___x_2501_ = v___x_2483_;
v_isShared_2502_ = v_isSharedCheck_2506_;
goto v_resetjp_2500_;
}
else
{
lean_inc(v_a_2499_);
lean_dec(v___x_2483_);
v___x_2501_ = lean_box(0);
v_isShared_2502_ = v_isSharedCheck_2506_;
goto v_resetjp_2500_;
}
v_resetjp_2500_:
{
lean_object* v___x_2504_; 
if (v_isShared_2502_ == 0)
{
v___x_2504_ = v___x_2501_;
goto v_reusejp_2503_;
}
else
{
lean_object* v_reuseFailAlloc_2505_; 
v_reuseFailAlloc_2505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2505_, 0, v_a_2499_);
v___x_2504_ = v_reuseFailAlloc_2505_;
goto v_reusejp_2503_;
}
v_reusejp_2503_:
{
return v___x_2504_;
}
}
}
}
else
{
lean_object* v_vs_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; size_t v_sz_2510_; size_t v___x_2511_; lean_object* v___x_2512_; 
v_vs_2507_ = lean_ctor_get(v_n_2465_, 0);
v___x_2508_ = lean_box(0);
v___x_2509_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2509_, 0, v___x_2508_);
lean_ctor_set(v___x_2509_, 1, v_b_2466_);
v_sz_2510_ = lean_array_size(v_vs_2507_);
v___x_2511_ = ((size_t)0ULL);
v___x_2512_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__1_spec__3(v_vs_2507_, v_sz_2510_, v___x_2511_, v___x_2509_, v___y_2467_, v___y_2468_, v___y_2469_, v___y_2470_, v___y_2471_, v___y_2472_, v___y_2473_, v___y_2474_, v___y_2475_, v___y_2476_);
if (lean_obj_tag(v___x_2512_) == 0)
{
lean_object* v_a_2513_; lean_object* v___x_2515_; uint8_t v_isShared_2516_; uint8_t v_isSharedCheck_2527_; 
v_a_2513_ = lean_ctor_get(v___x_2512_, 0);
v_isSharedCheck_2527_ = !lean_is_exclusive(v___x_2512_);
if (v_isSharedCheck_2527_ == 0)
{
v___x_2515_ = v___x_2512_;
v_isShared_2516_ = v_isSharedCheck_2527_;
goto v_resetjp_2514_;
}
else
{
lean_inc(v_a_2513_);
lean_dec(v___x_2512_);
v___x_2515_ = lean_box(0);
v_isShared_2516_ = v_isSharedCheck_2527_;
goto v_resetjp_2514_;
}
v_resetjp_2514_:
{
lean_object* v_fst_2517_; 
v_fst_2517_ = lean_ctor_get(v_a_2513_, 0);
if (lean_obj_tag(v_fst_2517_) == 0)
{
lean_object* v_snd_2518_; lean_object* v___x_2519_; lean_object* v___x_2521_; 
v_snd_2518_ = lean_ctor_get(v_a_2513_, 1);
lean_inc(v_snd_2518_);
lean_dec(v_a_2513_);
v___x_2519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2519_, 0, v_snd_2518_);
if (v_isShared_2516_ == 0)
{
lean_ctor_set(v___x_2515_, 0, v___x_2519_);
v___x_2521_ = v___x_2515_;
goto v_reusejp_2520_;
}
else
{
lean_object* v_reuseFailAlloc_2522_; 
v_reuseFailAlloc_2522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2522_, 0, v___x_2519_);
v___x_2521_ = v_reuseFailAlloc_2522_;
goto v_reusejp_2520_;
}
v_reusejp_2520_:
{
return v___x_2521_;
}
}
else
{
lean_object* v_val_2523_; lean_object* v___x_2525_; 
lean_inc_ref(v_fst_2517_);
lean_dec(v_a_2513_);
v_val_2523_ = lean_ctor_get(v_fst_2517_, 0);
lean_inc(v_val_2523_);
lean_dec_ref_known(v_fst_2517_, 1);
if (v_isShared_2516_ == 0)
{
lean_ctor_set(v___x_2515_, 0, v_val_2523_);
v___x_2525_ = v___x_2515_;
goto v_reusejp_2524_;
}
else
{
lean_object* v_reuseFailAlloc_2526_; 
v_reuseFailAlloc_2526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2526_, 0, v_val_2523_);
v___x_2525_ = v_reuseFailAlloc_2526_;
goto v_reusejp_2524_;
}
v_reusejp_2524_:
{
return v___x_2525_;
}
}
}
}
else
{
lean_object* v_a_2528_; lean_object* v___x_2530_; uint8_t v_isShared_2531_; uint8_t v_isSharedCheck_2535_; 
v_a_2528_ = lean_ctor_get(v___x_2512_, 0);
v_isSharedCheck_2535_ = !lean_is_exclusive(v___x_2512_);
if (v_isSharedCheck_2535_ == 0)
{
v___x_2530_ = v___x_2512_;
v_isShared_2531_ = v_isSharedCheck_2535_;
goto v_resetjp_2529_;
}
else
{
lean_inc(v_a_2528_);
lean_dec(v___x_2512_);
v___x_2530_ = lean_box(0);
v_isShared_2531_ = v_isSharedCheck_2535_;
goto v_resetjp_2529_;
}
v_resetjp_2529_:
{
lean_object* v___x_2533_; 
if (v_isShared_2531_ == 0)
{
v___x_2533_ = v___x_2530_;
goto v_reusejp_2532_;
}
else
{
lean_object* v_reuseFailAlloc_2534_; 
v_reuseFailAlloc_2534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2534_, 0, v_a_2528_);
v___x_2533_ = v_reuseFailAlloc_2534_;
goto v_reusejp_2532_;
}
v_reusejp_2532_:
{
return v___x_2533_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__1_spec__2(lean_object* v_init_2536_, lean_object* v_as_2537_, size_t v_sz_2538_, size_t v_i_2539_, lean_object* v_b_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_){
_start:
{
uint8_t v___x_2552_; 
v___x_2552_ = lean_usize_dec_lt(v_i_2539_, v_sz_2538_);
if (v___x_2552_ == 0)
{
lean_object* v___x_2553_; 
v___x_2553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2553_, 0, v_b_2540_);
return v___x_2553_;
}
else
{
lean_object* v_snd_2554_; lean_object* v___x_2556_; uint8_t v_isShared_2557_; uint8_t v_isSharedCheck_2588_; 
v_snd_2554_ = lean_ctor_get(v_b_2540_, 1);
v_isSharedCheck_2588_ = !lean_is_exclusive(v_b_2540_);
if (v_isSharedCheck_2588_ == 0)
{
lean_object* v_unused_2589_; 
v_unused_2589_ = lean_ctor_get(v_b_2540_, 0);
lean_dec(v_unused_2589_);
v___x_2556_ = v_b_2540_;
v_isShared_2557_ = v_isSharedCheck_2588_;
goto v_resetjp_2555_;
}
else
{
lean_inc(v_snd_2554_);
lean_dec(v_b_2540_);
v___x_2556_ = lean_box(0);
v_isShared_2557_ = v_isSharedCheck_2588_;
goto v_resetjp_2555_;
}
v_resetjp_2555_:
{
lean_object* v_a_2558_; lean_object* v___x_2559_; 
v_a_2558_ = lean_array_uget_borrowed(v_as_2537_, v_i_2539_);
lean_inc(v_snd_2554_);
v___x_2559_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__1(v_init_2536_, v_a_2558_, v_snd_2554_, v___y_2541_, v___y_2542_, v___y_2543_, v___y_2544_, v___y_2545_, v___y_2546_, v___y_2547_, v___y_2548_, v___y_2549_, v___y_2550_);
if (lean_obj_tag(v___x_2559_) == 0)
{
lean_object* v_a_2560_; lean_object* v___x_2562_; uint8_t v_isShared_2563_; uint8_t v_isSharedCheck_2579_; 
v_a_2560_ = lean_ctor_get(v___x_2559_, 0);
v_isSharedCheck_2579_ = !lean_is_exclusive(v___x_2559_);
if (v_isSharedCheck_2579_ == 0)
{
v___x_2562_ = v___x_2559_;
v_isShared_2563_ = v_isSharedCheck_2579_;
goto v_resetjp_2561_;
}
else
{
lean_inc(v_a_2560_);
lean_dec(v___x_2559_);
v___x_2562_ = lean_box(0);
v_isShared_2563_ = v_isSharedCheck_2579_;
goto v_resetjp_2561_;
}
v_resetjp_2561_:
{
if (lean_obj_tag(v_a_2560_) == 0)
{
lean_object* v___x_2564_; lean_object* v___x_2566_; 
v___x_2564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2564_, 0, v_a_2560_);
if (v_isShared_2557_ == 0)
{
lean_ctor_set(v___x_2556_, 0, v___x_2564_);
v___x_2566_ = v___x_2556_;
goto v_reusejp_2565_;
}
else
{
lean_object* v_reuseFailAlloc_2570_; 
v_reuseFailAlloc_2570_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2570_, 0, v___x_2564_);
lean_ctor_set(v_reuseFailAlloc_2570_, 1, v_snd_2554_);
v___x_2566_ = v_reuseFailAlloc_2570_;
goto v_reusejp_2565_;
}
v_reusejp_2565_:
{
lean_object* v___x_2568_; 
if (v_isShared_2563_ == 0)
{
lean_ctor_set(v___x_2562_, 0, v___x_2566_);
v___x_2568_ = v___x_2562_;
goto v_reusejp_2567_;
}
else
{
lean_object* v_reuseFailAlloc_2569_; 
v_reuseFailAlloc_2569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2569_, 0, v___x_2566_);
v___x_2568_ = v_reuseFailAlloc_2569_;
goto v_reusejp_2567_;
}
v_reusejp_2567_:
{
return v___x_2568_;
}
}
}
else
{
lean_object* v_a_2571_; lean_object* v___x_2572_; lean_object* v___x_2574_; 
lean_del_object(v___x_2562_);
lean_dec(v_snd_2554_);
v_a_2571_ = lean_ctor_get(v_a_2560_, 0);
lean_inc(v_a_2571_);
lean_dec_ref_known(v_a_2560_, 1);
v___x_2572_ = lean_box(0);
if (v_isShared_2557_ == 0)
{
lean_ctor_set(v___x_2556_, 1, v_a_2571_);
lean_ctor_set(v___x_2556_, 0, v___x_2572_);
v___x_2574_ = v___x_2556_;
goto v_reusejp_2573_;
}
else
{
lean_object* v_reuseFailAlloc_2578_; 
v_reuseFailAlloc_2578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2578_, 0, v___x_2572_);
lean_ctor_set(v_reuseFailAlloc_2578_, 1, v_a_2571_);
v___x_2574_ = v_reuseFailAlloc_2578_;
goto v_reusejp_2573_;
}
v_reusejp_2573_:
{
size_t v___x_2575_; size_t v___x_2576_; 
v___x_2575_ = ((size_t)1ULL);
v___x_2576_ = lean_usize_add(v_i_2539_, v___x_2575_);
v_i_2539_ = v___x_2576_;
v_b_2540_ = v___x_2574_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_2580_; lean_object* v___x_2582_; uint8_t v_isShared_2583_; uint8_t v_isSharedCheck_2587_; 
lean_del_object(v___x_2556_);
lean_dec(v_snd_2554_);
v_a_2580_ = lean_ctor_get(v___x_2559_, 0);
v_isSharedCheck_2587_ = !lean_is_exclusive(v___x_2559_);
if (v_isSharedCheck_2587_ == 0)
{
v___x_2582_ = v___x_2559_;
v_isShared_2583_ = v_isSharedCheck_2587_;
goto v_resetjp_2581_;
}
else
{
lean_inc(v_a_2580_);
lean_dec(v___x_2559_);
v___x_2582_ = lean_box(0);
v_isShared_2583_ = v_isSharedCheck_2587_;
goto v_resetjp_2581_;
}
v_resetjp_2581_:
{
lean_object* v___x_2585_; 
if (v_isShared_2583_ == 0)
{
v___x_2585_ = v___x_2582_;
goto v_reusejp_2584_;
}
else
{
lean_object* v_reuseFailAlloc_2586_; 
v_reuseFailAlloc_2586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2586_, 0, v_a_2580_);
v___x_2585_ = v_reuseFailAlloc_2586_;
goto v_reusejp_2584_;
}
v_reusejp_2584_:
{
return v___x_2585_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__1_spec__2___boxed(lean_object* v_init_2590_, lean_object* v_as_2591_, lean_object* v_sz_2592_, lean_object* v_i_2593_, lean_object* v_b_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_){
_start:
{
size_t v_sz_boxed_2606_; size_t v_i_boxed_2607_; lean_object* v_res_2608_; 
v_sz_boxed_2606_ = lean_unbox_usize(v_sz_2592_);
lean_dec(v_sz_2592_);
v_i_boxed_2607_ = lean_unbox_usize(v_i_2593_);
lean_dec(v_i_2593_);
v_res_2608_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__1_spec__2(v_init_2590_, v_as_2591_, v_sz_boxed_2606_, v_i_boxed_2607_, v_b_2594_, v___y_2595_, v___y_2596_, v___y_2597_, v___y_2598_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_);
lean_dec(v___y_2604_);
lean_dec_ref(v___y_2603_);
lean_dec(v___y_2602_);
lean_dec_ref(v___y_2601_);
lean_dec(v___y_2600_);
lean_dec_ref(v___y_2599_);
lean_dec(v___y_2598_);
lean_dec_ref(v___y_2597_);
lean_dec(v___y_2596_);
lean_dec(v___y_2595_);
lean_dec_ref(v_as_2591_);
return v_res_2608_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__1___boxed(lean_object* v_init_2609_, lean_object* v_n_2610_, lean_object* v_b_2611_, lean_object* v___y_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_){
_start:
{
lean_object* v_res_2623_; 
v_res_2623_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__1(v_init_2609_, v_n_2610_, v_b_2611_, v___y_2612_, v___y_2613_, v___y_2614_, v___y_2615_, v___y_2616_, v___y_2617_, v___y_2618_, v___y_2619_, v___y_2620_, v___y_2621_);
lean_dec(v___y_2621_);
lean_dec_ref(v___y_2620_);
lean_dec(v___y_2619_);
lean_dec_ref(v___y_2618_);
lean_dec(v___y_2617_);
lean_dec_ref(v___y_2616_);
lean_dec(v___y_2615_);
lean_dec_ref(v___y_2614_);
lean_dec(v___y_2613_);
lean_dec(v___y_2612_);
lean_dec_ref(v_n_2610_);
return v_res_2623_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1(lean_object* v_t_2624_, lean_object* v_init_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_){
_start:
{
lean_object* v_root_2637_; lean_object* v_tail_2638_; lean_object* v___x_2639_; 
v_root_2637_ = lean_ctor_get(v_t_2624_, 0);
v_tail_2638_ = lean_ctor_get(v_t_2624_, 1);
v___x_2639_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__1(v_init_2625_, v_root_2637_, v_init_2625_, v___y_2626_, v___y_2627_, v___y_2628_, v___y_2629_, v___y_2630_, v___y_2631_, v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_);
if (lean_obj_tag(v___x_2639_) == 0)
{
lean_object* v_a_2640_; lean_object* v___x_2642_; uint8_t v_isShared_2643_; uint8_t v_isSharedCheck_2676_; 
v_a_2640_ = lean_ctor_get(v___x_2639_, 0);
v_isSharedCheck_2676_ = !lean_is_exclusive(v___x_2639_);
if (v_isSharedCheck_2676_ == 0)
{
v___x_2642_ = v___x_2639_;
v_isShared_2643_ = v_isSharedCheck_2676_;
goto v_resetjp_2641_;
}
else
{
lean_inc(v_a_2640_);
lean_dec(v___x_2639_);
v___x_2642_ = lean_box(0);
v_isShared_2643_ = v_isSharedCheck_2676_;
goto v_resetjp_2641_;
}
v_resetjp_2641_:
{
if (lean_obj_tag(v_a_2640_) == 0)
{
lean_object* v_a_2644_; lean_object* v___x_2646_; 
v_a_2644_ = lean_ctor_get(v_a_2640_, 0);
lean_inc(v_a_2644_);
lean_dec_ref_known(v_a_2640_, 1);
if (v_isShared_2643_ == 0)
{
lean_ctor_set(v___x_2642_, 0, v_a_2644_);
v___x_2646_ = v___x_2642_;
goto v_reusejp_2645_;
}
else
{
lean_object* v_reuseFailAlloc_2647_; 
v_reuseFailAlloc_2647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2647_, 0, v_a_2644_);
v___x_2646_ = v_reuseFailAlloc_2647_;
goto v_reusejp_2645_;
}
v_reusejp_2645_:
{
return v___x_2646_;
}
}
else
{
lean_object* v_a_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; size_t v_sz_2651_; size_t v___x_2652_; lean_object* v___x_2653_; 
lean_del_object(v___x_2642_);
v_a_2648_ = lean_ctor_get(v_a_2640_, 0);
lean_inc(v_a_2648_);
lean_dec_ref_known(v_a_2640_, 1);
v___x_2649_ = lean_box(0);
v___x_2650_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2650_, 0, v___x_2649_);
lean_ctor_set(v___x_2650_, 1, v_a_2648_);
v_sz_2651_ = lean_array_size(v_tail_2638_);
v___x_2652_ = ((size_t)0ULL);
v___x_2653_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__2(v_tail_2638_, v_sz_2651_, v___x_2652_, v___x_2650_, v___y_2626_, v___y_2627_, v___y_2628_, v___y_2629_, v___y_2630_, v___y_2631_, v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_);
if (lean_obj_tag(v___x_2653_) == 0)
{
lean_object* v_a_2654_; lean_object* v___x_2656_; uint8_t v_isShared_2657_; uint8_t v_isSharedCheck_2667_; 
v_a_2654_ = lean_ctor_get(v___x_2653_, 0);
v_isSharedCheck_2667_ = !lean_is_exclusive(v___x_2653_);
if (v_isSharedCheck_2667_ == 0)
{
v___x_2656_ = v___x_2653_;
v_isShared_2657_ = v_isSharedCheck_2667_;
goto v_resetjp_2655_;
}
else
{
lean_inc(v_a_2654_);
lean_dec(v___x_2653_);
v___x_2656_ = lean_box(0);
v_isShared_2657_ = v_isSharedCheck_2667_;
goto v_resetjp_2655_;
}
v_resetjp_2655_:
{
lean_object* v_fst_2658_; 
v_fst_2658_ = lean_ctor_get(v_a_2654_, 0);
if (lean_obj_tag(v_fst_2658_) == 0)
{
lean_object* v_snd_2659_; lean_object* v___x_2661_; 
v_snd_2659_ = lean_ctor_get(v_a_2654_, 1);
lean_inc(v_snd_2659_);
lean_dec(v_a_2654_);
if (v_isShared_2657_ == 0)
{
lean_ctor_set(v___x_2656_, 0, v_snd_2659_);
v___x_2661_ = v___x_2656_;
goto v_reusejp_2660_;
}
else
{
lean_object* v_reuseFailAlloc_2662_; 
v_reuseFailAlloc_2662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2662_, 0, v_snd_2659_);
v___x_2661_ = v_reuseFailAlloc_2662_;
goto v_reusejp_2660_;
}
v_reusejp_2660_:
{
return v___x_2661_;
}
}
else
{
lean_object* v_val_2663_; lean_object* v___x_2665_; 
lean_inc_ref(v_fst_2658_);
lean_dec(v_a_2654_);
v_val_2663_ = lean_ctor_get(v_fst_2658_, 0);
lean_inc(v_val_2663_);
lean_dec_ref_known(v_fst_2658_, 1);
if (v_isShared_2657_ == 0)
{
lean_ctor_set(v___x_2656_, 0, v_val_2663_);
v___x_2665_ = v___x_2656_;
goto v_reusejp_2664_;
}
else
{
lean_object* v_reuseFailAlloc_2666_; 
v_reuseFailAlloc_2666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2666_, 0, v_val_2663_);
v___x_2665_ = v_reuseFailAlloc_2666_;
goto v_reusejp_2664_;
}
v_reusejp_2664_:
{
return v___x_2665_;
}
}
}
}
else
{
lean_object* v_a_2668_; lean_object* v___x_2670_; uint8_t v_isShared_2671_; uint8_t v_isSharedCheck_2675_; 
v_a_2668_ = lean_ctor_get(v___x_2653_, 0);
v_isSharedCheck_2675_ = !lean_is_exclusive(v___x_2653_);
if (v_isSharedCheck_2675_ == 0)
{
v___x_2670_ = v___x_2653_;
v_isShared_2671_ = v_isSharedCheck_2675_;
goto v_resetjp_2669_;
}
else
{
lean_inc(v_a_2668_);
lean_dec(v___x_2653_);
v___x_2670_ = lean_box(0);
v_isShared_2671_ = v_isSharedCheck_2675_;
goto v_resetjp_2669_;
}
v_resetjp_2669_:
{
lean_object* v___x_2673_; 
if (v_isShared_2671_ == 0)
{
v___x_2673_ = v___x_2670_;
goto v_reusejp_2672_;
}
else
{
lean_object* v_reuseFailAlloc_2674_; 
v_reuseFailAlloc_2674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2674_, 0, v_a_2668_);
v___x_2673_ = v_reuseFailAlloc_2674_;
goto v_reusejp_2672_;
}
v_reusejp_2672_:
{
return v___x_2673_;
}
}
}
}
}
}
else
{
lean_object* v_a_2677_; lean_object* v___x_2679_; uint8_t v_isShared_2680_; uint8_t v_isSharedCheck_2684_; 
v_a_2677_ = lean_ctor_get(v___x_2639_, 0);
v_isSharedCheck_2684_ = !lean_is_exclusive(v___x_2639_);
if (v_isSharedCheck_2684_ == 0)
{
v___x_2679_ = v___x_2639_;
v_isShared_2680_ = v_isSharedCheck_2684_;
goto v_resetjp_2678_;
}
else
{
lean_inc(v_a_2677_);
lean_dec(v___x_2639_);
v___x_2679_ = lean_box(0);
v_isShared_2680_ = v_isSharedCheck_2684_;
goto v_resetjp_2678_;
}
v_resetjp_2678_:
{
lean_object* v___x_2682_; 
if (v_isShared_2680_ == 0)
{
v___x_2682_ = v___x_2679_;
goto v_reusejp_2681_;
}
else
{
lean_object* v_reuseFailAlloc_2683_; 
v_reuseFailAlloc_2683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2683_, 0, v_a_2677_);
v___x_2682_ = v_reuseFailAlloc_2683_;
goto v_reusejp_2681_;
}
v_reusejp_2681_:
{
return v___x_2682_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1___boxed(lean_object* v_t_2685_, lean_object* v_init_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_){
_start:
{
lean_object* v_res_2698_; 
v_res_2698_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1(v_t_2685_, v_init_2686_, v___y_2687_, v___y_2688_, v___y_2689_, v___y_2690_, v___y_2691_, v___y_2692_, v___y_2693_, v___y_2694_, v___y_2695_, v___y_2696_);
lean_dec(v___y_2696_);
lean_dec_ref(v___y_2695_);
lean_dec(v___y_2694_);
lean_dec_ref(v___y_2693_);
lean_dec(v___y_2692_);
lean_dec_ref(v___y_2691_);
lean_dec(v___y_2690_);
lean_dec_ref(v___y_2689_);
lean_dec(v___y_2688_);
lean_dec(v___y_2687_);
lean_dec_ref(v_t_2685_);
return v_res_2698_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_checkInvariants(uint8_t v_expensive_2699_, lean_object* v_a_2700_, lean_object* v_a_2701_, lean_object* v_a_2702_, lean_object* v_a_2703_, lean_object* v_a_2704_, lean_object* v_a_2705_, lean_object* v_a_2706_, lean_object* v_a_2707_, lean_object* v_a_2708_, lean_object* v_a_2709_){
_start:
{
lean_object* v___y_2715_; lean_object* v___y_2716_; lean_object* v___y_2717_; lean_object* v___y_2718_; lean_object* v___y_2719_; lean_object* v___y_2720_; lean_object* v___y_2721_; lean_object* v___y_2722_; lean_object* v___y_2723_; lean_object* v___y_2724_; lean_object* v___y_2730_; lean_object* v___y_2731_; lean_object* v___y_2732_; lean_object* v___y_2733_; lean_object* v___y_2734_; lean_object* v___y_2735_; lean_object* v___y_2736_; lean_object* v___y_2737_; lean_object* v___y_2738_; lean_object* v___y_2739_; uint8_t v_debug_2741_; 
v_debug_2741_ = lean_ctor_get_uint8(v_a_2702_, sizeof(void*)*8 + 2);
if (v_debug_2741_ == 0)
{
v___y_2715_ = v_a_2700_;
v___y_2716_ = v_a_2701_;
v___y_2717_ = v_a_2702_;
v___y_2718_ = v_a_2703_;
v___y_2719_ = v_a_2704_;
v___y_2720_ = v_a_2705_;
v___y_2721_ = v_a_2706_;
v___y_2722_ = v_a_2707_;
v___y_2723_ = v_a_2708_;
v___y_2724_ = v_a_2709_;
goto v___jp_2714_;
}
else
{
lean_object* v___x_2742_; 
v___x_2742_ = l_Lean_Meta_Grind_getExprs___redArg(v_a_2700_);
if (lean_obj_tag(v___x_2742_) == 0)
{
lean_object* v_a_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; 
v_a_2743_ = lean_ctor_get(v___x_2742_, 0);
lean_inc(v_a_2743_);
lean_dec_ref_known(v___x_2742_, 1);
v___x_2744_ = lean_box(0);
v___x_2745_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1(v_a_2743_, v___x_2744_, v_a_2700_, v_a_2701_, v_a_2702_, v_a_2703_, v_a_2704_, v_a_2705_, v_a_2706_, v_a_2707_, v_a_2708_, v_a_2709_);
lean_dec(v_a_2743_);
if (lean_obj_tag(v___x_2745_) == 0)
{
lean_dec_ref_known(v___x_2745_, 1);
if (v_expensive_2699_ == 0)
{
v___y_2730_ = v_a_2700_;
v___y_2731_ = v_a_2701_;
v___y_2732_ = v_a_2702_;
v___y_2733_ = v_a_2703_;
v___y_2734_ = v_a_2704_;
v___y_2735_ = v_a_2705_;
v___y_2736_ = v_a_2706_;
v___y_2737_ = v_a_2707_;
v___y_2738_ = v_a_2708_;
v___y_2739_ = v_a_2709_;
goto v___jp_2729_;
}
else
{
lean_object* v___x_2746_; 
v___x_2746_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq(v_a_2700_, v_a_2701_, v_a_2702_, v_a_2703_, v_a_2704_, v_a_2705_, v_a_2706_, v_a_2707_, v_a_2708_, v_a_2709_);
if (lean_obj_tag(v___x_2746_) == 0)
{
lean_dec_ref_known(v___x_2746_, 1);
v___y_2730_ = v_a_2700_;
v___y_2731_ = v_a_2701_;
v___y_2732_ = v_a_2702_;
v___y_2733_ = v_a_2703_;
v___y_2734_ = v_a_2704_;
v___y_2735_ = v_a_2705_;
v___y_2736_ = v_a_2706_;
v___y_2737_ = v_a_2707_;
v___y_2738_ = v_a_2708_;
v___y_2739_ = v_a_2709_;
goto v___jp_2729_;
}
else
{
return v___x_2746_;
}
}
}
else
{
return v___x_2745_;
}
}
else
{
lean_object* v_a_2747_; lean_object* v___x_2749_; uint8_t v_isShared_2750_; uint8_t v_isSharedCheck_2754_; 
v_a_2747_ = lean_ctor_get(v___x_2742_, 0);
v_isSharedCheck_2754_ = !lean_is_exclusive(v___x_2742_);
if (v_isSharedCheck_2754_ == 0)
{
v___x_2749_ = v___x_2742_;
v_isShared_2750_ = v_isSharedCheck_2754_;
goto v_resetjp_2748_;
}
else
{
lean_inc(v_a_2747_);
lean_dec(v___x_2742_);
v___x_2749_ = lean_box(0);
v_isShared_2750_ = v_isSharedCheck_2754_;
goto v_resetjp_2748_;
}
v_resetjp_2748_:
{
lean_object* v___x_2752_; 
if (v_isShared_2750_ == 0)
{
v___x_2752_ = v___x_2749_;
goto v_reusejp_2751_;
}
else
{
lean_object* v_reuseFailAlloc_2753_; 
v_reuseFailAlloc_2753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2753_, 0, v_a_2747_);
v___x_2752_ = v_reuseFailAlloc_2753_;
goto v_reusejp_2751_;
}
v_reusejp_2751_:
{
return v___x_2752_;
}
}
}
}
v___jp_2711_:
{
lean_object* v___x_2712_; lean_object* v___x_2713_; 
v___x_2712_ = lean_box(0);
v___x_2713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2713_, 0, v___x_2712_);
return v___x_2713_;
}
v___jp_2714_:
{
if (v_expensive_2699_ == 0)
{
goto v___jp_2711_;
}
else
{
lean_object* v_options_2725_; lean_object* v___x_2726_; uint8_t v___x_2727_; 
v_options_2725_ = lean_ctor_get(v___y_2723_, 2);
v___x_2726_ = l_Lean_Meta_Grind_grind_debug_proofs;
v___x_2727_ = l_Lean_Option_get___at___00Lean_Meta_Grind_checkInvariants_spec__0(v_options_2725_, v___x_2726_);
if (v___x_2727_ == 0)
{
goto v___jp_2711_;
}
else
{
lean_object* v___x_2728_; 
v___x_2728_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs(v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_, v___y_2723_, v___y_2724_);
return v___x_2728_;
}
}
}
v___jp_2729_:
{
lean_object* v___x_2740_; 
v___x_2740_ = l_Lean_Meta_Grind_Solvers_checkInvariants(v___y_2730_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_, v___y_2735_, v___y_2736_, v___y_2737_, v___y_2738_, v___y_2739_);
if (lean_obj_tag(v___x_2740_) == 0)
{
lean_dec_ref_known(v___x_2740_, 1);
v___y_2715_ = v___y_2730_;
v___y_2716_ = v___y_2731_;
v___y_2717_ = v___y_2732_;
v___y_2718_ = v___y_2733_;
v___y_2719_ = v___y_2734_;
v___y_2720_ = v___y_2735_;
v___y_2721_ = v___y_2736_;
v___y_2722_ = v___y_2737_;
v___y_2723_ = v___y_2738_;
v___y_2724_ = v___y_2739_;
goto v___jp_2714_;
}
else
{
return v___x_2740_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_checkInvariants___boxed(lean_object* v_expensive_2755_, lean_object* v_a_2756_, lean_object* v_a_2757_, lean_object* v_a_2758_, lean_object* v_a_2759_, lean_object* v_a_2760_, lean_object* v_a_2761_, lean_object* v_a_2762_, lean_object* v_a_2763_, lean_object* v_a_2764_, lean_object* v_a_2765_, lean_object* v_a_2766_){
_start:
{
uint8_t v_expensive_boxed_2767_; lean_object* v_res_2768_; 
v_expensive_boxed_2767_ = lean_unbox(v_expensive_2755_);
v_res_2768_ = l_Lean_Meta_Grind_checkInvariants(v_expensive_boxed_2767_, v_a_2756_, v_a_2757_, v_a_2758_, v_a_2759_, v_a_2760_, v_a_2761_, v_a_2762_, v_a_2763_, v_a_2764_, v_a_2765_);
lean_dec(v_a_2765_);
lean_dec_ref(v_a_2764_);
lean_dec(v_a_2763_);
lean_dec_ref(v_a_2762_);
lean_dec(v_a_2761_);
lean_dec_ref(v_a_2760_);
lean_dec(v_a_2759_);
lean_dec_ref(v_a_2758_);
lean_dec(v_a_2757_);
lean_dec(v_a_2756_);
return v_res_2768_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Goal_checkInvariants_spec__0___redArg___lam__0(lean_object* v_x_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_){
_start:
{
lean_object* v___x_2780_; 
lean_inc(v___y_2774_);
lean_inc_ref(v___y_2773_);
lean_inc(v___y_2772_);
lean_inc_ref(v___y_2771_);
lean_inc(v___y_2770_);
v___x_2780_ = lean_apply_10(v_x_2769_, v___y_2770_, v___y_2771_, v___y_2772_, v___y_2773_, v___y_2774_, v___y_2775_, v___y_2776_, v___y_2777_, v___y_2778_, lean_box(0));
return v___x_2780_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Goal_checkInvariants_spec__0___redArg___lam__0___boxed(lean_object* v_x_2781_, lean_object* v___y_2782_, lean_object* v___y_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_, lean_object* v___y_2787_, lean_object* v___y_2788_, lean_object* v___y_2789_, lean_object* v___y_2790_, lean_object* v___y_2791_){
_start:
{
lean_object* v_res_2792_; 
v_res_2792_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Goal_checkInvariants_spec__0___redArg___lam__0(v_x_2781_, v___y_2782_, v___y_2783_, v___y_2784_, v___y_2785_, v___y_2786_, v___y_2787_, v___y_2788_, v___y_2789_, v___y_2790_);
lean_dec(v___y_2786_);
lean_dec_ref(v___y_2785_);
lean_dec(v___y_2784_);
lean_dec_ref(v___y_2783_);
lean_dec(v___y_2782_);
return v_res_2792_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Goal_checkInvariants_spec__0___redArg(lean_object* v_mvarId_2793_, lean_object* v_x_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_, lean_object* v___y_2803_){
_start:
{
lean_object* v___f_2805_; lean_object* v___x_2806_; 
lean_inc(v___y_2799_);
lean_inc_ref(v___y_2798_);
lean_inc(v___y_2797_);
lean_inc_ref(v___y_2796_);
lean_inc(v___y_2795_);
v___f_2805_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Goal_checkInvariants_spec__0___redArg___lam__0___boxed), 11, 6);
lean_closure_set(v___f_2805_, 0, v_x_2794_);
lean_closure_set(v___f_2805_, 1, v___y_2795_);
lean_closure_set(v___f_2805_, 2, v___y_2796_);
lean_closure_set(v___f_2805_, 3, v___y_2797_);
lean_closure_set(v___f_2805_, 4, v___y_2798_);
lean_closure_set(v___f_2805_, 5, v___y_2799_);
v___x_2806_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_2793_, v___f_2805_, v___y_2800_, v___y_2801_, v___y_2802_, v___y_2803_);
if (lean_obj_tag(v___x_2806_) == 0)
{
return v___x_2806_;
}
else
{
lean_object* v_a_2807_; lean_object* v___x_2809_; uint8_t v_isShared_2810_; uint8_t v_isSharedCheck_2814_; 
v_a_2807_ = lean_ctor_get(v___x_2806_, 0);
v_isSharedCheck_2814_ = !lean_is_exclusive(v___x_2806_);
if (v_isSharedCheck_2814_ == 0)
{
v___x_2809_ = v___x_2806_;
v_isShared_2810_ = v_isSharedCheck_2814_;
goto v_resetjp_2808_;
}
else
{
lean_inc(v_a_2807_);
lean_dec(v___x_2806_);
v___x_2809_ = lean_box(0);
v_isShared_2810_ = v_isSharedCheck_2814_;
goto v_resetjp_2808_;
}
v_resetjp_2808_:
{
lean_object* v___x_2812_; 
if (v_isShared_2810_ == 0)
{
v___x_2812_ = v___x_2809_;
goto v_reusejp_2811_;
}
else
{
lean_object* v_reuseFailAlloc_2813_; 
v_reuseFailAlloc_2813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2813_, 0, v_a_2807_);
v___x_2812_ = v_reuseFailAlloc_2813_;
goto v_reusejp_2811_;
}
v_reusejp_2811_:
{
return v___x_2812_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Goal_checkInvariants_spec__0___redArg___boxed(lean_object* v_mvarId_2815_, lean_object* v_x_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_){
_start:
{
lean_object* v_res_2827_; 
v_res_2827_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Goal_checkInvariants_spec__0___redArg(v_mvarId_2815_, v_x_2816_, v___y_2817_, v___y_2818_, v___y_2819_, v___y_2820_, v___y_2821_, v___y_2822_, v___y_2823_, v___y_2824_, v___y_2825_);
lean_dec(v___y_2825_);
lean_dec_ref(v___y_2824_);
lean_dec(v___y_2823_);
lean_dec_ref(v___y_2822_);
lean_dec(v___y_2821_);
lean_dec_ref(v___y_2820_);
lean_dec(v___y_2819_);
lean_dec_ref(v___y_2818_);
lean_dec(v___y_2817_);
return v_res_2827_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Goal_checkInvariants_spec__0(lean_object* v_00_u03b1_2828_, lean_object* v_mvarId_2829_, lean_object* v_x_2830_, lean_object* v___y_2831_, lean_object* v___y_2832_, lean_object* v___y_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_){
_start:
{
lean_object* v___x_2841_; 
v___x_2841_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Goal_checkInvariants_spec__0___redArg(v_mvarId_2829_, v_x_2830_, v___y_2831_, v___y_2832_, v___y_2833_, v___y_2834_, v___y_2835_, v___y_2836_, v___y_2837_, v___y_2838_, v___y_2839_);
return v___x_2841_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Goal_checkInvariants_spec__0___boxed(lean_object* v_00_u03b1_2842_, lean_object* v_mvarId_2843_, lean_object* v_x_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_, lean_object* v___y_2847_, lean_object* v___y_2848_, lean_object* v___y_2849_, lean_object* v___y_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_, lean_object* v___y_2853_, lean_object* v___y_2854_){
_start:
{
lean_object* v_res_2855_; 
v_res_2855_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Goal_checkInvariants_spec__0(v_00_u03b1_2842_, v_mvarId_2843_, v_x_2844_, v___y_2845_, v___y_2846_, v___y_2847_, v___y_2848_, v___y_2849_, v___y_2850_, v___y_2851_, v___y_2852_, v___y_2853_);
lean_dec(v___y_2853_);
lean_dec_ref(v___y_2852_);
lean_dec(v___y_2851_);
lean_dec_ref(v___y_2850_);
lean_dec(v___y_2849_);
lean_dec_ref(v___y_2848_);
lean_dec(v___y_2847_);
lean_dec_ref(v___y_2846_);
lean_dec(v___y_2845_);
return v_res_2855_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Goal_checkInvariants___lam__0(lean_object* v_goal_2856_, uint8_t v_expensive_2857_, lean_object* v___y_2858_, lean_object* v___y_2859_, lean_object* v___y_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_, lean_object* v___y_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_){
_start:
{
lean_object* v___x_2868_; lean_object* v___x_2869_; 
v___x_2868_ = lean_st_mk_ref(v_goal_2856_);
v___x_2869_ = l_Lean_Meta_Grind_checkInvariants(v_expensive_2857_, v___x_2868_, v___y_2858_, v___y_2859_, v___y_2860_, v___y_2861_, v___y_2862_, v___y_2863_, v___y_2864_, v___y_2865_, v___y_2866_);
if (lean_obj_tag(v___x_2869_) == 0)
{
lean_object* v___x_2871_; uint8_t v_isShared_2872_; uint8_t v_isSharedCheck_2878_; 
v_isSharedCheck_2878_ = !lean_is_exclusive(v___x_2869_);
if (v_isSharedCheck_2878_ == 0)
{
lean_object* v_unused_2879_; 
v_unused_2879_ = lean_ctor_get(v___x_2869_, 0);
lean_dec(v_unused_2879_);
v___x_2871_ = v___x_2869_;
v_isShared_2872_ = v_isSharedCheck_2878_;
goto v_resetjp_2870_;
}
else
{
lean_dec(v___x_2869_);
v___x_2871_ = lean_box(0);
v_isShared_2872_ = v_isSharedCheck_2878_;
goto v_resetjp_2870_;
}
v_resetjp_2870_:
{
lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2876_; 
v___x_2873_ = lean_st_ref_get(v___x_2868_);
v___x_2874_ = lean_st_ref_get(v___x_2868_);
lean_dec(v___x_2868_);
lean_dec(v___x_2874_);
if (v_isShared_2872_ == 0)
{
lean_ctor_set(v___x_2871_, 0, v___x_2873_);
v___x_2876_ = v___x_2871_;
goto v_reusejp_2875_;
}
else
{
lean_object* v_reuseFailAlloc_2877_; 
v_reuseFailAlloc_2877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2877_, 0, v___x_2873_);
v___x_2876_ = v_reuseFailAlloc_2877_;
goto v_reusejp_2875_;
}
v_reusejp_2875_:
{
return v___x_2876_;
}
}
}
else
{
lean_object* v_a_2880_; lean_object* v___x_2882_; uint8_t v_isShared_2883_; uint8_t v_isSharedCheck_2887_; 
lean_dec(v___x_2868_);
v_a_2880_ = lean_ctor_get(v___x_2869_, 0);
v_isSharedCheck_2887_ = !lean_is_exclusive(v___x_2869_);
if (v_isSharedCheck_2887_ == 0)
{
v___x_2882_ = v___x_2869_;
v_isShared_2883_ = v_isSharedCheck_2887_;
goto v_resetjp_2881_;
}
else
{
lean_inc(v_a_2880_);
lean_dec(v___x_2869_);
v___x_2882_ = lean_box(0);
v_isShared_2883_ = v_isSharedCheck_2887_;
goto v_resetjp_2881_;
}
v_resetjp_2881_:
{
lean_object* v___x_2885_; 
if (v_isShared_2883_ == 0)
{
v___x_2885_ = v___x_2882_;
goto v_reusejp_2884_;
}
else
{
lean_object* v_reuseFailAlloc_2886_; 
v_reuseFailAlloc_2886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2886_, 0, v_a_2880_);
v___x_2885_ = v_reuseFailAlloc_2886_;
goto v_reusejp_2884_;
}
v_reusejp_2884_:
{
return v___x_2885_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Goal_checkInvariants___lam__0___boxed(lean_object* v_goal_2888_, lean_object* v_expensive_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_, lean_object* v___y_2892_, lean_object* v___y_2893_, lean_object* v___y_2894_, lean_object* v___y_2895_, lean_object* v___y_2896_, lean_object* v___y_2897_, lean_object* v___y_2898_, lean_object* v___y_2899_){
_start:
{
uint8_t v_expensive_boxed_2900_; lean_object* v_res_2901_; 
v_expensive_boxed_2900_ = lean_unbox(v_expensive_2889_);
v_res_2901_ = l_Lean_Meta_Grind_Goal_checkInvariants___lam__0(v_goal_2888_, v_expensive_boxed_2900_, v___y_2890_, v___y_2891_, v___y_2892_, v___y_2893_, v___y_2894_, v___y_2895_, v___y_2896_, v___y_2897_, v___y_2898_);
lean_dec(v___y_2898_);
lean_dec_ref(v___y_2897_);
lean_dec(v___y_2896_);
lean_dec_ref(v___y_2895_);
lean_dec(v___y_2894_);
lean_dec_ref(v___y_2893_);
lean_dec(v___y_2892_);
lean_dec_ref(v___y_2891_);
lean_dec(v___y_2890_);
return v_res_2901_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Goal_checkInvariants(lean_object* v_goal_2902_, uint8_t v_expensive_2903_, lean_object* v_a_2904_, lean_object* v_a_2905_, lean_object* v_a_2906_, lean_object* v_a_2907_, lean_object* v_a_2908_, lean_object* v_a_2909_, lean_object* v_a_2910_, lean_object* v_a_2911_, lean_object* v_a_2912_){
_start:
{
lean_object* v_mvarId_2914_; lean_object* v___x_2915_; lean_object* v___f_2916_; lean_object* v___x_2917_; 
v_mvarId_2914_ = lean_ctor_get(v_goal_2902_, 1);
lean_inc(v_mvarId_2914_);
v___x_2915_ = lean_box(v_expensive_2903_);
v___f_2916_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Goal_checkInvariants___lam__0___boxed), 12, 2);
lean_closure_set(v___f_2916_, 0, v_goal_2902_);
lean_closure_set(v___f_2916_, 1, v___x_2915_);
v___x_2917_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Goal_checkInvariants_spec__0___redArg(v_mvarId_2914_, v___f_2916_, v_a_2904_, v_a_2905_, v_a_2906_, v_a_2907_, v_a_2908_, v_a_2909_, v_a_2910_, v_a_2911_, v_a_2912_);
if (lean_obj_tag(v___x_2917_) == 0)
{
lean_object* v___x_2919_; uint8_t v_isShared_2920_; uint8_t v_isSharedCheck_2925_; 
v_isSharedCheck_2925_ = !lean_is_exclusive(v___x_2917_);
if (v_isSharedCheck_2925_ == 0)
{
lean_object* v_unused_2926_; 
v_unused_2926_ = lean_ctor_get(v___x_2917_, 0);
lean_dec(v_unused_2926_);
v___x_2919_ = v___x_2917_;
v_isShared_2920_ = v_isSharedCheck_2925_;
goto v_resetjp_2918_;
}
else
{
lean_dec(v___x_2917_);
v___x_2919_ = lean_box(0);
v_isShared_2920_ = v_isSharedCheck_2925_;
goto v_resetjp_2918_;
}
v_resetjp_2918_:
{
lean_object* v___x_2921_; lean_object* v___x_2923_; 
v___x_2921_ = lean_box(0);
if (v_isShared_2920_ == 0)
{
lean_ctor_set(v___x_2919_, 0, v___x_2921_);
v___x_2923_ = v___x_2919_;
goto v_reusejp_2922_;
}
else
{
lean_object* v_reuseFailAlloc_2924_; 
v_reuseFailAlloc_2924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2924_, 0, v___x_2921_);
v___x_2923_ = v_reuseFailAlloc_2924_;
goto v_reusejp_2922_;
}
v_reusejp_2922_:
{
return v___x_2923_;
}
}
}
else
{
lean_object* v_a_2927_; lean_object* v___x_2929_; uint8_t v_isShared_2930_; uint8_t v_isSharedCheck_2934_; 
v_a_2927_ = lean_ctor_get(v___x_2917_, 0);
v_isSharedCheck_2934_ = !lean_is_exclusive(v___x_2917_);
if (v_isSharedCheck_2934_ == 0)
{
v___x_2929_ = v___x_2917_;
v_isShared_2930_ = v_isSharedCheck_2934_;
goto v_resetjp_2928_;
}
else
{
lean_inc(v_a_2927_);
lean_dec(v___x_2917_);
v___x_2929_ = lean_box(0);
v_isShared_2930_ = v_isSharedCheck_2934_;
goto v_resetjp_2928_;
}
v_resetjp_2928_:
{
lean_object* v___x_2932_; 
if (v_isShared_2930_ == 0)
{
v___x_2932_ = v___x_2929_;
goto v_reusejp_2931_;
}
else
{
lean_object* v_reuseFailAlloc_2933_; 
v_reuseFailAlloc_2933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2933_, 0, v_a_2927_);
v___x_2932_ = v_reuseFailAlloc_2933_;
goto v_reusejp_2931_;
}
v_reusejp_2931_:
{
return v___x_2932_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Goal_checkInvariants___boxed(lean_object* v_goal_2935_, lean_object* v_expensive_2936_, lean_object* v_a_2937_, lean_object* v_a_2938_, lean_object* v_a_2939_, lean_object* v_a_2940_, lean_object* v_a_2941_, lean_object* v_a_2942_, lean_object* v_a_2943_, lean_object* v_a_2944_, lean_object* v_a_2945_, lean_object* v_a_2946_){
_start:
{
uint8_t v_expensive_boxed_2947_; lean_object* v_res_2948_; 
v_expensive_boxed_2947_ = lean_unbox(v_expensive_2936_);
v_res_2948_ = l_Lean_Meta_Grind_Goal_checkInvariants(v_goal_2935_, v_expensive_boxed_2947_, v_a_2937_, v_a_2938_, v_a_2939_, v_a_2940_, v_a_2941_, v_a_2942_, v_a_2943_, v_a_2944_, v_a_2945_);
lean_dec(v_a_2945_);
lean_dec_ref(v_a_2944_);
lean_dec(v_a_2943_);
lean_dec_ref(v_a_2942_);
lean_dec(v_a_2941_);
lean_dec_ref(v_a_2940_);
lean_dec(v_a_2939_);
lean_dec_ref(v_a_2938_);
lean_dec(v_a_2937_);
return v_res_2948_;
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
