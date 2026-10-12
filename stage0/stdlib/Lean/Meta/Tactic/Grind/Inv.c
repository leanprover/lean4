// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Inv
// Imports: public import Lean.Meta.Tactic.Grind.Types import Init.Grind.Util import Lean.Meta.Tactic.Grind.Util import Lean.Meta.Sym.Canon
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
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getExprs___redArg(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_get_x21___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
uint8_t lean_expr_equal(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_instInhabitedGoalM___redArg();
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Meta_Grind_Goal_getENode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_ENode_isRoot(lean_object*);
lean_object* l_Lean_Meta_Grind_Goal_getRoot(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
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
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Meta_Grind_getCongrRoot___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isRoot___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getParents___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_ParentSet_isEmpty(lean_object*);
lean_object* l_Lean_Meta_Grind_ParentSet_elems(lean_object*);
lean_object* l_Lean_Meta_Grind_Goal_getRoot_x3f(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Meta_Grind_useFunCC___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_isMatchCond(lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Meta_Sym_Canon_normNumLit_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Goal_getEqcs(lean_object*, uint8_t);
lean_object* l_Lean_Meta_Grind_mkEqHEqProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_check(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_updateLastTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
extern lean_object* l_Lean_Meta_Grind_grind_debug_proofs;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Solvers_checkInvariants(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__1___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "Lean.Meta.Tactic.Grind.Inv"};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__0 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__0_value;
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 63, .m_capacity = 63, .m_length = 62, .m_data = "_private.Lean.Meta.Tactic.Grind.Inv.0.Lean.Meta.Grind.checkEqc"};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__1 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__1_value;
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 75, .m_capacity = 75, .m_length = 74, .m_data = "assertion violation: isSameExpr n root.self\n    -- Go to next element\n    "};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__2 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__2_value;
static lean_once_cell_t l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__3;
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 173, .m_capacity = 173, .m_length = 172, .m_data = "assertion violation: ( __do_lift._@.Lean.Meta.Tactic.Grind.Inv.684779629._hygCtx._hyg.279.0 )\n    -- Starting at `curr`, following the `target\?` field leads to `root`.\n    "};
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
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 202, .m_capacity = 202, .m_length = 201, .m_data = "assertion violation: ( __do_lift._@.Lean.Meta.Tactic.Grind.Inv.684779629._hygCtx._hyg.218.0 )\n    -- If the equivalence class does not have HEq proofs, then the types must be definitionally equal.\n    "};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___closed__2 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___closed__2_value;
static lean_once_cell_t l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___closed__3;
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 114, .m_capacity = 114, .m_length = 113, .m_data = "assertion violation: isSameExpr e ( __do_lift._@.Lean.Meta.Tactic.Grind.Inv.684779629._hygCtx._hyg.171.0 )\n      "};
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
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 100, .m_capacity = 100, .m_length = 99, .m_data = "assertion violation: ( __do_lift._@.Lean.Meta.Tactic.Grind.Inv.3145645808._hygCtx._hyg.486.0 )\n    "};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__1 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__1_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__2;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "e: "};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__3 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__3_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__4;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = ", parent: "};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__5 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__5_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__6;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 102, .m_capacity = 102, .m_length = 101, .m_data = "assertion violation: ( __do_lift._@.Lean.Meta.Tactic.Grind.Inv.3145645808._hygCtx._hyg.193.0 )\n      "};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__7 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__7_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__8;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__9;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 105, .m_capacity = 105, .m_length = 104, .m_data = "assertion violation: ( __do_lift._@.Lean.Meta.Tactic.Grind.Inv.3145645808._hygCtx._hyg.530.0 ).isEmpty\n\n"};
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
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 70, .m_capacity = 70, .m_length = 69, .m_data = "_private.Lean.Meta.Tactic.Grind.Inv.0.Lean.Meta.Grind.checkCongrTable"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__1___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__1___redArg___closed__0_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 99, .m_capacity = 99, .m_length = 98, .m_data = "assertion violation: ( __do_lift._@.Lean.Meta.Tactic.Grind.Inv.3283713146._hygCtx._hyg.56.0 )\n    "};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__1___redArg___closed__1 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__1___redArg___closed__1_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__1___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__1___redArg___closed__2;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__1___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 53, .m_capacity = 53, .m_length = 52, .m_data = "`grind` internal error, stale congruence table entry"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__1___redArg___closed__3 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__1___redArg___closed__3_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__1___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__1___redArg___closed__4;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__1___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "assertion violation: isSameExpr e e'\n\n"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__1___redArg___closed__5 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__1___redArg___closed__5_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__1___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__1___redArg___closed__6;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0_spec__1_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0___redArg___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0_spec__1_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0_spec__1_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_Grind_checkInvariants_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Grind_checkInvariants_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__2_spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Lean.Meta.Grind.checkInvariants"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__2_spec__5___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__2_spec__5___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__2_spec__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 108, .m_capacity = 108, .m_length = 107, .m_data = "assertion violation: ( __do_lift._@.Lean.Meta.Tactic.Grind.Inv.3119225764._hygCtx._hyg.90.0 ).isNone\n      "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__2_spec__5___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__2_spec__5___closed__1_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__2_spec__5___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__2_spec__5___closed__2;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__2_spec__5(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__1_spec__3_spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__1_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = l_Lean_Meta_Grind_instInhabitedGoalM___redArg();
return v___x_1_;
}
}
lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__1(lean_object* v_msg_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_, lean_object* v___y_7_, lean_object* v___y_8_, lean_object* v___y_9_, lean_object* v___y_10_, lean_object* v___y_11_, lean_object* v___y_12_){
_start:
{
lean_object* v___x_14_; lean_object* v___x_24848__overap_15_; lean_object* v___x_16_; 
v___x_14_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__1___closed__0, &l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__1___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__1___closed__0);
v___x_24848__overap_15_ = lean_panic_fn_borrowed(v___x_14_, v_msg_2_);
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
v___x_16_ = lean_apply_11(v___x_24848__overap_15_, v___y_3_, v___y_4_, v___y_5_, v___y_6_, v___y_7_, v___y_8_, v___y_9_, v___y_10_, v___y_11_, v___y_12_, lean_box(0));
return v___x_16_;
}
}
LEAN_EXPORT void l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__1_0interp(lean_interpreter_value* stack)
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
v_res_17_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__1(v_msg_2_, v___y_3_, v___y_4_, v___y_5_, v___y_6_, v___y_7_, v___y_8_, v___y_9_, v___y_10_, v___y_11_, v___y_12_);
stack->m_obj
 = v_res_17_;
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__1___boxed(lean_object* v_msg_18_, lean_object* v___y_19_, lean_object* v___y_20_, lean_object* v___y_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_, lean_object* v___y_28_, lean_object* v___y_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__1(v_msg_18_, v___y_19_, v___y_20_, v___y_21_, v___y_22_, v___y_23_, v___y_24_, v___y_25_, v___y_26_, v___y_27_, v___y_28_);
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
lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__4(lean_object* v_msg_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_, lean_object* v___y_36_, lean_object* v___y_37_, lean_object* v___y_38_, lean_object* v___y_39_, lean_object* v___y_40_, lean_object* v___y_41_){
_start:
{
lean_object* v___x_43_; lean_object* v___x_25809__overap_44_; lean_object* v___x_45_; 
v___x_43_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__1___closed__0, &l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__1___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__1___closed__0);
v___x_25809__overap_44_ = lean_panic_fn_borrowed(v___x_43_, v_msg_31_);
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
v___x_45_ = lean_apply_11(v___x_25809__overap_44_, v___y_32_, v___y_33_, v___y_34_, v___y_35_, v___y_36_, v___y_37_, v___y_38_, v___y_39_, v___y_40_, v___y_41_, lean_box(0));
return v___x_45_;
}
}
LEAN_EXPORT void l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_31_ = stack[0].m_obj;
lean_object* v___y_32_ = stack[1].m_obj;
lean_object* v___y_33_ = stack[2].m_obj;
lean_object* v___y_34_ = stack[3].m_obj;
lean_object* v___y_35_ = stack[4].m_obj;
lean_object* v___y_36_ = stack[5].m_obj;
lean_object* v___y_37_ = stack[6].m_obj;
lean_object* v___y_38_ = stack[7].m_obj;
lean_object* v___y_39_ = stack[8].m_obj;
lean_object* v___y_40_ = stack[9].m_obj;
lean_object* v___y_41_ = stack[10].m_obj;
lean_object* v_res_46_;
v_res_46_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__4(v_msg_31_, v___y_32_, v___y_33_, v___y_34_, v___y_35_, v___y_36_, v___y_37_, v___y_38_, v___y_39_, v___y_40_, v___y_41_);
stack->m_obj
 = v_res_46_;
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__4___boxed(lean_object* v_msg_47_, lean_object* v___y_48_, lean_object* v___y_49_, lean_object* v___y_50_, lean_object* v___y_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_, lean_object* v___y_56_, lean_object* v___y_57_, lean_object* v___y_58_){
_start:
{
lean_object* v_res_59_; 
v_res_59_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__4(v_msg_47_, v___y_48_, v___y_49_, v___y_50_, v___y_51_, v___y_52_, v___y_53_, v___y_54_, v___y_55_, v___y_56_, v___y_57_);
lean_dec(v___y_57_);
lean_dec_ref(v___y_56_);
lean_dec(v___y_55_);
lean_dec_ref(v___y_54_);
lean_dec(v___y_53_);
lean_dec_ref(v___y_52_);
lean_dec(v___y_51_);
lean_dec_ref(v___y_50_);
lean_dec(v___y_49_);
lean_dec(v___y_48_);
return v_res_59_;
}
}
lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__0___redArg(lean_object* v_a_60_, lean_object* v___y_61_){
_start:
{
lean_object* v___x_63_; lean_object* v___x_64_; 
v___x_63_ = lean_st_ref_get(v___y_61_);
v___x_64_ = l_Lean_Meta_Grind_Goal_getTarget_x3f(v___x_63_, v_a_60_);
lean_dec(v___x_63_);
if (lean_obj_tag(v___x_64_) == 1)
{
lean_object* v_val_65_; 
lean_dec_ref(v_a_60_);
v_val_65_ = lean_ctor_get(v___x_64_, 0);
lean_inc(v_val_65_);
lean_dec_ref_known(v___x_64_, 1);
v_a_60_ = v_val_65_;
goto _start;
}
else
{
lean_object* v___x_67_; 
lean_dec(v___x_64_);
v___x_67_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_67_, 0, v_a_60_);
return v___x_67_;
}
}
}
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_60_ = stack[0].m_obj;
lean_object* v___y_61_ = stack[1].m_obj;
lean_object* v_res_68_;
v_res_68_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__0___redArg(v_a_60_, v___y_61_);
stack->m_obj
 = v_res_68_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__0___redArg___boxed(lean_object* v_a_69_, lean_object* v___y_70_, lean_object* v___y_71_){
_start:
{
lean_object* v_res_72_; 
v_res_72_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__0___redArg(v_a_69_, v___y_70_);
lean_dec(v___y_70_);
return v_res_72_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; 
v___x_76_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__2));
v___x_77_ = lean_unsigned_to_nat(4u);
v___x_78_ = lean_unsigned_to_nat(41u);
v___x_79_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__1));
v___x_80_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__0));
v___x_81_ = l_mkPanicMessageWithDecl(v___x_80_, v___x_79_, v___x_78_, v___x_77_, v___x_76_);
return v___x_81_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__5(void){
_start:
{
lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; 
v___x_83_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__4));
v___x_84_ = lean_unsigned_to_nat(6u);
v___x_85_ = lean_unsigned_to_nat(33u);
v___x_86_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__1));
v___x_87_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__0));
v___x_88_ = l_mkPanicMessageWithDecl(v___x_87_, v___x_86_, v___x_85_, v___x_84_, v___x_83_);
return v___x_88_;
}
}
lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0(lean_object* v_root_89_, lean_object* v_snd_90_, lean_object* v_curr_91_, lean_object* v___x_92_, lean_object* v_____r_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_, lean_object* v___y_99_, lean_object* v___y_100_, lean_object* v___y_101_, lean_object* v___y_102_, lean_object* v___y_103_){
_start:
{
lean_object* v___y_106_; lean_object* v___y_107_; lean_object* v___y_108_; lean_object* v___y_109_; lean_object* v___y_110_; lean_object* v___y_111_; lean_object* v___y_112_; lean_object* v___y_113_; lean_object* v___y_114_; lean_object* v___y_115_; uint8_t v_heqProofs_158_; 
v_heqProofs_158_ = lean_ctor_get_uint8(v_root_89_, sizeof(void*)*12 + 4);
if (v_heqProofs_158_ == 0)
{
lean_object* v___x_159_; 
lean_inc_ref(v_curr_91_);
lean_inc(v_snd_90_);
v___x_159_ = l_Lean_Meta_Grind_hasSameType(v_snd_90_, v_curr_91_, v___y_100_, v___y_101_, v___y_102_, v___y_103_);
if (lean_obj_tag(v___x_159_) == 0)
{
lean_object* v_a_160_; uint8_t v___x_161_; 
v_a_160_ = lean_ctor_get(v___x_159_, 0);
lean_inc(v_a_160_);
lean_dec_ref_known(v___x_159_, 1);
v___x_161_ = lean_unbox(v_a_160_);
lean_dec(v_a_160_);
if (v___x_161_ == 0)
{
lean_object* v___x_162_; lean_object* v___x_163_; 
lean_dec(v___x_92_);
lean_dec_ref(v_curr_91_);
lean_dec(v_snd_90_);
v___x_162_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__5, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__5_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__5);
v___x_163_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__1(v___x_162_, v___y_94_, v___y_95_, v___y_96_, v___y_97_, v___y_98_, v___y_99_, v___y_100_, v___y_101_, v___y_102_, v___y_103_);
return v___x_163_;
}
else
{
v___y_106_ = v___y_94_;
v___y_107_ = v___y_95_;
v___y_108_ = v___y_96_;
v___y_109_ = v___y_97_;
v___y_110_ = v___y_98_;
v___y_111_ = v___y_99_;
v___y_112_ = v___y_100_;
v___y_113_ = v___y_101_;
v___y_114_ = v___y_102_;
v___y_115_ = v___y_103_;
goto v___jp_105_;
}
}
else
{
lean_object* v_a_164_; lean_object* v___x_166_; uint8_t v_isShared_167_; uint8_t v_isSharedCheck_171_; 
lean_dec(v___x_92_);
lean_dec_ref(v_curr_91_);
lean_dec(v_snd_90_);
v_a_164_ = lean_ctor_get(v___x_159_, 0);
v_isSharedCheck_171_ = !lean_is_exclusive(v___x_159_);
if (v_isSharedCheck_171_ == 0)
{
v___x_166_ = v___x_159_;
v_isShared_167_ = v_isSharedCheck_171_;
goto v_resetjp_165_;
}
else
{
lean_inc(v_a_164_);
lean_dec(v___x_159_);
v___x_166_ = lean_box(0);
v_isShared_167_ = v_isSharedCheck_171_;
goto v_resetjp_165_;
}
v_resetjp_165_:
{
lean_object* v___x_169_; 
if (v_isShared_167_ == 0)
{
v___x_169_ = v___x_166_;
goto v_reusejp_168_;
}
else
{
lean_object* v_reuseFailAlloc_170_; 
v_reuseFailAlloc_170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_170_, 0, v_a_164_);
v___x_169_ = v_reuseFailAlloc_170_;
goto v_reusejp_168_;
}
v_reusejp_168_:
{
return v___x_169_;
}
}
}
}
else
{
v___y_106_ = v___y_94_;
v___y_107_ = v___y_95_;
v___y_108_ = v___y_96_;
v___y_109_ = v___y_97_;
v___y_110_ = v___y_98_;
v___y_111_ = v___y_99_;
v___y_112_ = v___y_100_;
v___y_113_ = v___y_101_;
v___y_114_ = v___y_102_;
v___y_115_ = v___y_103_;
goto v___jp_105_;
}
v___jp_105_:
{
lean_object* v___x_116_; 
lean_inc(v_snd_90_);
v___x_116_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__0___redArg(v_snd_90_, v___y_106_);
if (lean_obj_tag(v___x_116_) == 0)
{
lean_object* v_a_117_; size_t v___x_118_; size_t v___x_119_; uint8_t v___x_120_; 
v_a_117_ = lean_ctor_get(v___x_116_, 0);
lean_inc(v_a_117_);
lean_dec_ref_known(v___x_116_, 1);
v___x_118_ = lean_ptr_addr(v_a_117_);
lean_dec(v_a_117_);
v___x_119_ = lean_ptr_addr(v_curr_91_);
lean_dec_ref(v_curr_91_);
v___x_120_ = lean_usize_dec_eq(v___x_118_, v___x_119_);
if (v___x_120_ == 0)
{
lean_object* v___x_121_; lean_object* v___x_122_; 
lean_dec(v___x_92_);
lean_dec(v_snd_90_);
v___x_121_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__3, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__3_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__3);
v___x_122_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__1(v___x_121_, v___y_106_, v___y_107_, v___y_108_, v___y_109_, v___y_110_, v___y_111_, v___y_112_, v___y_113_, v___y_114_, v___y_115_);
return v___x_122_;
}
else
{
lean_object* v___x_123_; lean_object* v___x_124_; 
v___x_123_ = lean_st_ref_get(v___y_106_);
v___x_124_ = l_Lean_Meta_Grind_Goal_getNext(v___x_123_, v_snd_90_, v___y_112_, v___y_113_, v___y_114_, v___y_115_);
lean_dec(v___x_123_);
if (lean_obj_tag(v___x_124_) == 0)
{
lean_object* v_a_125_; lean_object* v___x_127_; uint8_t v_isShared_128_; uint8_t v_isSharedCheck_141_; 
v_a_125_ = lean_ctor_get(v___x_124_, 0);
v_isSharedCheck_141_ = !lean_is_exclusive(v___x_124_);
if (v_isSharedCheck_141_ == 0)
{
v___x_127_ = v___x_124_;
v_isShared_128_ = v_isSharedCheck_141_;
goto v_resetjp_126_;
}
else
{
lean_inc(v_a_125_);
lean_dec(v___x_124_);
v___x_127_ = lean_box(0);
v_isShared_128_ = v_isSharedCheck_141_;
goto v_resetjp_126_;
}
v_resetjp_126_:
{
size_t v___x_129_; uint8_t v___x_130_; 
v___x_129_ = lean_ptr_addr(v_a_125_);
v___x_130_ = lean_usize_dec_eq(v___x_119_, v___x_129_);
if (v___x_130_ == 0)
{
lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_134_; 
v___x_131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_131_, 0, v___x_92_);
lean_ctor_set(v___x_131_, 1, v_a_125_);
v___x_132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_132_, 0, v___x_131_);
if (v_isShared_128_ == 0)
{
lean_ctor_set(v___x_127_, 0, v___x_132_);
v___x_134_ = v___x_127_;
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
else
{
lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_139_; 
v___x_136_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_136_, 0, v___x_92_);
lean_ctor_set(v___x_136_, 1, v_a_125_);
v___x_137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_137_, 0, v___x_136_);
if (v_isShared_128_ == 0)
{
lean_ctor_set(v___x_127_, 0, v___x_137_);
v___x_139_ = v___x_127_;
goto v_reusejp_138_;
}
else
{
lean_object* v_reuseFailAlloc_140_; 
v_reuseFailAlloc_140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_140_, 0, v___x_137_);
v___x_139_ = v_reuseFailAlloc_140_;
goto v_reusejp_138_;
}
v_reusejp_138_:
{
return v___x_139_;
}
}
}
}
else
{
lean_object* v_a_142_; lean_object* v___x_144_; uint8_t v_isShared_145_; uint8_t v_isSharedCheck_149_; 
lean_dec(v___x_92_);
v_a_142_ = lean_ctor_get(v___x_124_, 0);
v_isSharedCheck_149_ = !lean_is_exclusive(v___x_124_);
if (v_isSharedCheck_149_ == 0)
{
v___x_144_ = v___x_124_;
v_isShared_145_ = v_isSharedCheck_149_;
goto v_resetjp_143_;
}
else
{
lean_inc(v_a_142_);
lean_dec(v___x_124_);
v___x_144_ = lean_box(0);
v_isShared_145_ = v_isSharedCheck_149_;
goto v_resetjp_143_;
}
v_resetjp_143_:
{
lean_object* v___x_147_; 
if (v_isShared_145_ == 0)
{
v___x_147_ = v___x_144_;
goto v_reusejp_146_;
}
else
{
lean_object* v_reuseFailAlloc_148_; 
v_reuseFailAlloc_148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_148_, 0, v_a_142_);
v___x_147_ = v_reuseFailAlloc_148_;
goto v_reusejp_146_;
}
v_reusejp_146_:
{
return v___x_147_;
}
}
}
}
}
else
{
lean_object* v_a_150_; lean_object* v___x_152_; uint8_t v_isShared_153_; uint8_t v_isSharedCheck_157_; 
lean_dec(v___x_92_);
lean_dec_ref(v_curr_91_);
lean_dec(v_snd_90_);
v_a_150_ = lean_ctor_get(v___x_116_, 0);
v_isSharedCheck_157_ = !lean_is_exclusive(v___x_116_);
if (v_isSharedCheck_157_ == 0)
{
v___x_152_ = v___x_116_;
v_isShared_153_ = v_isSharedCheck_157_;
goto v_resetjp_151_;
}
else
{
lean_inc(v_a_150_);
lean_dec(v___x_116_);
v___x_152_ = lean_box(0);
v_isShared_153_ = v_isSharedCheck_157_;
goto v_resetjp_151_;
}
v_resetjp_151_:
{
lean_object* v___x_155_; 
if (v_isShared_153_ == 0)
{
v___x_155_ = v___x_152_;
goto v_reusejp_154_;
}
else
{
lean_object* v_reuseFailAlloc_156_; 
v_reuseFailAlloc_156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_156_, 0, v_a_150_);
v___x_155_ = v_reuseFailAlloc_156_;
goto v_reusejp_154_;
}
v_reusejp_154_:
{
return v___x_155_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_root_89_ = stack[0].m_obj;
lean_object* v_snd_90_ = stack[1].m_obj;
lean_object* v_curr_91_ = stack[2].m_obj;
lean_object* v___x_92_ = stack[3].m_obj;
lean_object* v_____r_93_ = stack[4].m_obj;
lean_object* v___y_94_ = stack[5].m_obj;
lean_object* v___y_95_ = stack[6].m_obj;
lean_object* v___y_96_ = stack[7].m_obj;
lean_object* v___y_97_ = stack[8].m_obj;
lean_object* v___y_98_ = stack[9].m_obj;
lean_object* v___y_99_ = stack[10].m_obj;
lean_object* v___y_100_ = stack[11].m_obj;
lean_object* v___y_101_ = stack[12].m_obj;
lean_object* v___y_102_ = stack[13].m_obj;
lean_object* v___y_103_ = stack[14].m_obj;
lean_object* v_res_172_;
v_res_172_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0(v_root_89_, v_snd_90_, v_curr_91_, v___x_92_, v_____r_93_, v___y_94_, v___y_95_, v___y_96_, v___y_97_, v___y_98_, v___y_99_, v___y_100_, v___y_101_, v___y_102_, v___y_103_);
stack->m_obj
 = v_res_172_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___boxed(lean_object* v_root_173_, lean_object* v_snd_174_, lean_object* v_curr_175_, lean_object* v___x_176_, lean_object* v_____r_177_, lean_object* v___y_178_, lean_object* v___y_179_, lean_object* v___y_180_, lean_object* v___y_181_, lean_object* v___y_182_, lean_object* v___y_183_, lean_object* v___y_184_, lean_object* v___y_185_, lean_object* v___y_186_, lean_object* v___y_187_, lean_object* v___y_188_){
_start:
{
lean_object* v_res_189_; 
v_res_189_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0(v_root_173_, v_snd_174_, v_curr_175_, v___x_176_, v_____r_177_, v___y_178_, v___y_179_, v___y_180_, v___y_181_, v___y_182_, v___y_183_, v___y_184_, v___y_185_, v___y_186_, v___y_187_);
lean_dec(v___y_187_);
lean_dec_ref(v___y_186_);
lean_dec(v___y_185_);
lean_dec_ref(v___y_184_);
lean_dec(v___y_183_);
lean_dec_ref(v___y_182_);
lean_dec(v___y_181_);
lean_dec_ref(v___y_180_);
lean_dec(v___y_179_);
lean_dec(v___y_178_);
lean_dec_ref(v_root_173_);
return v_res_189_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2_spec__4___redArg(lean_object* v___x_190_, lean_object* v_keys_191_, lean_object* v_vals_192_, lean_object* v_i_193_, lean_object* v_k_194_){
_start:
{
lean_object* v___x_195_; uint8_t v___x_196_; 
v___x_195_ = lean_array_get_size(v_keys_191_);
v___x_196_ = lean_nat_dec_lt(v_i_193_, v___x_195_);
if (v___x_196_ == 0)
{
lean_object* v___x_197_; 
lean_dec_ref(v_k_194_);
lean_dec(v_i_193_);
v___x_197_ = lean_box(0);
return v___x_197_;
}
else
{
lean_object* v_k_x27_198_; uint8_t v___x_199_; 
v_k_x27_198_ = lean_array_fget_borrowed(v_keys_191_, v_i_193_);
lean_inc(v_k_x27_198_);
lean_inc_ref(v_k_194_);
v___x_199_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_isCongruent(v___x_190_, v_k_194_, v_k_x27_198_);
if (v___x_199_ == 0)
{
lean_object* v___x_200_; lean_object* v___x_201_; 
v___x_200_ = lean_unsigned_to_nat(1u);
v___x_201_ = lean_nat_add(v_i_193_, v___x_200_);
lean_dec(v_i_193_);
v_i_193_ = v___x_201_;
goto _start;
}
else
{
lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; 
lean_dec_ref(v_k_194_);
v___x_203_ = lean_array_fget_borrowed(v_vals_192_, v_i_193_);
lean_dec(v_i_193_);
lean_inc(v___x_203_);
lean_inc(v_k_x27_198_);
v___x_204_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_204_, 0, v_k_x27_198_);
lean_ctor_set(v___x_204_, 1, v___x_203_);
v___x_205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_205_, 0, v___x_204_);
return v___x_205_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2_spec__4___redArg___boxed(lean_object* v___x_206_, lean_object* v_keys_207_, lean_object* v_vals_208_, lean_object* v_i_209_, lean_object* v_k_210_){
_start:
{
lean_object* v_res_211_; 
v_res_211_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2_spec__4___redArg(v___x_206_, v_keys_207_, v_vals_208_, v_i_209_, v_k_210_);
lean_dec_ref(v_vals_208_);
lean_dec_ref(v_keys_207_);
lean_dec_ref(v___x_206_);
return v_res_211_;
}
}
lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2___redArg(lean_object* v___x_212_, lean_object* v_x_213_, size_t v_x_214_, lean_object* v_x_215_){
_start:
{
if (lean_obj_tag(v_x_213_) == 0)
{
lean_object* v_es_216_; lean_object* v___x_217_; size_t v___x_218_; size_t v___x_219_; lean_object* v_j_220_; lean_object* v___x_221_; 
v_es_216_ = lean_ctor_get(v_x_213_, 0);
lean_inc_ref(v_es_216_);
lean_dec_ref_known(v_x_213_, 1);
v___x_217_ = lean_box(2);
v___x_218_ = ((size_t)31ULL);
v___x_219_ = lean_usize_land(v_x_214_, v___x_218_);
v_j_220_ = lean_usize_to_nat(v___x_219_);
v___x_221_ = lean_array_get(v___x_217_, v_es_216_, v_j_220_);
lean_dec(v_j_220_);
lean_dec_ref(v_es_216_);
switch(lean_obj_tag(v___x_221_))
{
case 0:
{
lean_object* v_key_222_; lean_object* v_val_223_; uint8_t v___x_224_; 
v_key_222_ = lean_ctor_get(v___x_221_, 0);
lean_inc_n(v_key_222_, 2);
v_val_223_ = lean_ctor_get(v___x_221_, 1);
lean_inc(v_val_223_);
lean_dec_ref_known(v___x_221_, 2);
v___x_224_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_isCongruent(v___x_212_, v_x_215_, v_key_222_);
if (v___x_224_ == 0)
{
lean_object* v___x_225_; 
lean_dec(v_val_223_);
lean_dec(v_key_222_);
v___x_225_ = lean_box(0);
return v___x_225_;
}
else
{
lean_object* v___x_226_; lean_object* v___x_227_; 
v___x_226_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_226_, 0, v_key_222_);
lean_ctor_set(v___x_226_, 1, v_val_223_);
v___x_227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_227_, 0, v___x_226_);
return v___x_227_;
}
}
case 1:
{
lean_object* v_node_228_; size_t v___x_229_; size_t v___x_230_; 
v_node_228_ = lean_ctor_get(v___x_221_, 0);
lean_inc(v_node_228_);
lean_dec_ref_known(v___x_221_, 1);
v___x_229_ = ((size_t)5ULL);
v___x_230_ = lean_usize_shift_right(v_x_214_, v___x_229_);
v_x_213_ = v_node_228_;
v_x_214_ = v___x_230_;
goto _start;
}
default: 
{
lean_object* v___x_232_; 
lean_dec_ref(v_x_215_);
v___x_232_ = lean_box(0);
return v___x_232_;
}
}
}
else
{
lean_object* v_ks_233_; lean_object* v_vs_234_; lean_object* v___x_235_; lean_object* v___x_236_; 
v_ks_233_ = lean_ctor_get(v_x_213_, 0);
lean_inc_ref(v_ks_233_);
v_vs_234_ = lean_ctor_get(v_x_213_, 1);
lean_inc_ref(v_vs_234_);
lean_dec_ref_known(v_x_213_, 2);
v___x_235_ = lean_unsigned_to_nat(0u);
v___x_236_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2_spec__4___redArg(v___x_212_, v_ks_233_, v_vs_234_, v___x_235_, v_x_215_);
lean_dec_ref(v_vs_234_);
lean_dec_ref(v_ks_233_);
return v___x_236_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_212_ = stack[0].m_obj;
lean_object* v_x_213_ = stack[1].m_obj;
size_t v_x_214_ = stack[2].m_num;
lean_object* v_x_215_ = stack[3].m_obj;
lean_object* v_res_237_;
v_res_237_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2___redArg(v___x_212_, v_x_213_, v_x_214_, v_x_215_);
stack->m_obj
 = v_res_237_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2___redArg___boxed(lean_object* v___x_238_, lean_object* v_x_239_, lean_object* v_x_240_, lean_object* v_x_241_){
_start:
{
size_t v_x_26807__boxed_242_; lean_object* v_res_243_; 
v_x_26807__boxed_242_ = lean_unbox_usize(v_x_240_);
lean_dec(v_x_240_);
v_res_243_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2___redArg(v___x_238_, v_x_239_, v_x_26807__boxed_242_, v_x_241_);
lean_dec_ref(v___x_238_);
return v_res_243_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2___redArg(lean_object* v___x_244_, lean_object* v_x_245_, lean_object* v_x_246_){
_start:
{
uint64_t v___x_247_; size_t v___x_248_; lean_object* v___x_249_; 
lean_inc_ref(v_x_246_);
v___x_247_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_congrHash(v___x_244_, v_x_246_);
v___x_248_ = lean_uint64_to_usize(v___x_247_);
lean_inc_ref(v_x_245_);
v___x_249_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2___redArg(v___x_244_, v_x_245_, v___x_248_, v_x_246_);
return v___x_249_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2___redArg___boxed(lean_object* v___x_250_, lean_object* v_x_251_, lean_object* v_x_252_){
_start:
{
lean_object* v_res_253_; 
v_res_253_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2___redArg(v___x_250_, v_x_251_, v_x_252_);
lean_dec_ref(v_x_251_);
lean_dec_ref(v___x_250_);
return v_res_253_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; 
v___x_255_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___closed__0));
v___x_256_ = lean_unsigned_to_nat(4u);
v___x_257_ = lean_unsigned_to_nat(23u);
v___x_258_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__1));
v___x_259_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__0));
v___x_260_ = l_mkPanicMessageWithDecl(v___x_259_, v___x_258_, v___x_257_, v___x_256_, v___x_255_);
return v___x_260_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; 
v___x_262_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___closed__2));
v___x_263_ = lean_unsigned_to_nat(8u);
v___x_264_ = lean_unsigned_to_nat(30u);
v___x_265_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__1));
v___x_266_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__0));
v___x_267_ = l_mkPanicMessageWithDecl(v___x_266_, v___x_265_, v___x_264_, v___x_263_, v___x_262_);
return v___x_267_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___closed__5(void){
_start:
{
lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; 
v___x_269_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___closed__4));
v___x_270_ = lean_unsigned_to_nat(10u);
v___x_271_ = lean_unsigned_to_nat(28u);
v___x_272_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__1));
v___x_273_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__0));
v___x_274_ = l_mkPanicMessageWithDecl(v___x_273_, v___x_272_, v___x_271_, v___x_270_, v___x_269_);
return v___x_274_;
}
}
lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg(lean_object* v_curr_275_, lean_object* v_root_276_, lean_object* v_a_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_){
_start:
{
lean_object* v___y_290_; lean_object* v_fst_310_; lean_object* v_snd_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; 
v_fst_310_ = lean_ctor_get(v_a_277_, 0);
lean_inc(v_fst_310_);
v_snd_311_ = lean_ctor_get(v_a_277_, 1);
lean_inc_n(v_snd_311_, 2);
lean_dec_ref(v_a_277_);
v___x_312_ = lean_unsigned_to_nat(1u);
v___x_313_ = lean_nat_add(v_fst_310_, v___x_312_);
lean_dec(v_fst_310_);
v___x_314_ = lean_st_ref_get(v___y_278_);
v___x_315_ = l_Lean_Meta_Grind_Goal_getRoot(v___x_314_, v_snd_311_, v___y_284_, v___y_285_, v___y_286_, v___y_287_);
lean_dec(v___x_314_);
if (lean_obj_tag(v___x_315_) == 0)
{
lean_object* v_a_316_; size_t v___x_317_; size_t v___x_318_; uint8_t v___x_319_; 
v_a_316_ = lean_ctor_get(v___x_315_, 0);
lean_inc(v_a_316_);
lean_dec_ref_known(v___x_315_, 1);
v___x_317_ = lean_ptr_addr(v_a_316_);
lean_dec(v_a_316_);
v___x_318_ = lean_ptr_addr(v_curr_275_);
v___x_319_ = lean_usize_dec_eq(v___x_317_, v___x_318_);
if (v___x_319_ == 0)
{
lean_object* v___x_320_; lean_object* v___x_321_; 
lean_dec(v___x_313_);
lean_dec(v_snd_311_);
v___x_320_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___closed__1, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___closed__1_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___closed__1);
v___x_321_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__1(v___x_320_, v___y_278_, v___y_279_, v___y_280_, v___y_281_, v___y_282_, v___y_283_, v___y_284_, v___y_285_, v___y_286_, v___y_287_);
v___y_290_ = v___x_321_;
goto v___jp_289_;
}
else
{
uint8_t v___x_322_; 
v___x_322_ = l_Lean_Expr_isApp(v_snd_311_);
if (v___x_322_ == 0)
{
lean_object* v___x_323_; lean_object* v___x_324_; 
v___x_323_ = lean_box(0);
lean_inc_ref(v_curr_275_);
v___x_324_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0(v_root_276_, v_snd_311_, v_curr_275_, v___x_313_, v___x_323_, v___y_278_, v___y_279_, v___y_280_, v___y_281_, v___y_282_, v___y_283_, v___y_284_, v___y_285_, v___y_286_, v___y_287_);
v___y_290_ = v___x_324_;
goto v___jp_289_;
}
else
{
lean_object* v___x_325_; lean_object* v_toGoalState_326_; lean_object* v_enodeMap_327_; lean_object* v_congrTable_328_; lean_object* v___x_329_; 
v___x_325_ = lean_st_ref_get(v___y_278_);
v_toGoalState_326_ = lean_ctor_get(v___x_325_, 0);
lean_inc_ref(v_toGoalState_326_);
lean_dec(v___x_325_);
v_enodeMap_327_ = lean_ctor_get(v_toGoalState_326_, 1);
lean_inc_ref(v_enodeMap_327_);
v_congrTable_328_ = lean_ctor_get(v_toGoalState_326_, 4);
lean_inc_ref(v_congrTable_328_);
lean_dec_ref(v_toGoalState_326_);
lean_inc(v_snd_311_);
v___x_329_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2___redArg(v_enodeMap_327_, v_congrTable_328_, v_snd_311_);
lean_dec_ref(v_congrTable_328_);
lean_dec_ref(v_enodeMap_327_);
if (lean_obj_tag(v___x_329_) == 0)
{
lean_object* v___x_330_; 
lean_inc(v_snd_311_);
v___x_330_ = l_Lean_Meta_Grind_isCongrRoot___redArg(v_snd_311_, v___y_278_, v___y_284_, v___y_285_, v___y_286_, v___y_287_);
if (lean_obj_tag(v___x_330_) == 0)
{
lean_object* v_a_331_; uint8_t v___x_332_; 
v_a_331_ = lean_ctor_get(v___x_330_, 0);
lean_inc(v_a_331_);
lean_dec_ref_known(v___x_330_, 1);
v___x_332_ = lean_unbox(v_a_331_);
lean_dec(v_a_331_);
if (v___x_332_ == 0)
{
lean_object* v___x_333_; lean_object* v___x_334_; 
lean_dec(v___x_313_);
lean_dec(v_snd_311_);
v___x_333_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___closed__3, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___closed__3_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___closed__3);
v___x_334_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__1(v___x_333_, v___y_278_, v___y_279_, v___y_280_, v___y_281_, v___y_282_, v___y_283_, v___y_284_, v___y_285_, v___y_286_, v___y_287_);
v___y_290_ = v___x_334_;
goto v___jp_289_;
}
else
{
lean_object* v___x_335_; lean_object* v___x_336_; 
v___x_335_ = lean_box(0);
lean_inc_ref(v_curr_275_);
v___x_336_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0(v_root_276_, v_snd_311_, v_curr_275_, v___x_313_, v___x_335_, v___y_278_, v___y_279_, v___y_280_, v___y_281_, v___y_282_, v___y_283_, v___y_284_, v___y_285_, v___y_286_, v___y_287_);
v___y_290_ = v___x_336_;
goto v___jp_289_;
}
}
else
{
lean_object* v_a_337_; lean_object* v___x_339_; uint8_t v_isShared_340_; uint8_t v_isSharedCheck_344_; 
lean_dec(v___x_313_);
lean_dec(v_snd_311_);
lean_dec_ref(v_curr_275_);
v_a_337_ = lean_ctor_get(v___x_330_, 0);
v_isSharedCheck_344_ = !lean_is_exclusive(v___x_330_);
if (v_isSharedCheck_344_ == 0)
{
v___x_339_ = v___x_330_;
v_isShared_340_ = v_isSharedCheck_344_;
goto v_resetjp_338_;
}
else
{
lean_inc(v_a_337_);
lean_dec(v___x_330_);
v___x_339_ = lean_box(0);
v_isShared_340_ = v_isSharedCheck_344_;
goto v_resetjp_338_;
}
v_resetjp_338_:
{
lean_object* v___x_342_; 
if (v_isShared_340_ == 0)
{
v___x_342_ = v___x_339_;
goto v_reusejp_341_;
}
else
{
lean_object* v_reuseFailAlloc_343_; 
v_reuseFailAlloc_343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_343_, 0, v_a_337_);
v___x_342_ = v_reuseFailAlloc_343_;
goto v_reusejp_341_;
}
v_reusejp_341_:
{
return v___x_342_;
}
}
}
}
else
{
lean_object* v_val_345_; lean_object* v_fst_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; 
v_val_345_ = lean_ctor_get(v___x_329_, 0);
lean_inc(v_val_345_);
lean_dec_ref_known(v___x_329_, 1);
v_fst_346_ = lean_ctor_get(v_val_345_, 0);
lean_inc(v_fst_346_);
lean_dec(v_val_345_);
v___x_347_ = l_Lean_Expr_getAppFn(v_fst_346_);
v___x_348_ = l_Lean_Expr_getAppFn(v_snd_311_);
v___x_349_ = l_Lean_Meta_Grind_hasSameType(v___x_347_, v___x_348_, v___y_284_, v___y_285_, v___y_286_, v___y_287_);
if (lean_obj_tag(v___x_349_) == 0)
{
lean_object* v_a_350_; uint8_t v___x_351_; 
v_a_350_ = lean_ctor_get(v___x_349_, 0);
lean_inc(v_a_350_);
lean_dec_ref_known(v___x_349_, 1);
v___x_351_ = lean_unbox(v_a_350_);
lean_dec(v_a_350_);
if (v___x_351_ == 0)
{
lean_object* v___x_352_; lean_object* v___x_353_; 
lean_dec(v_fst_346_);
v___x_352_ = lean_box(0);
lean_inc_ref(v_curr_275_);
v___x_353_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0(v_root_276_, v_snd_311_, v_curr_275_, v___x_313_, v___x_352_, v___y_278_, v___y_279_, v___y_280_, v___y_281_, v___y_282_, v___y_283_, v___y_284_, v___y_285_, v___y_286_, v___y_287_);
v___y_290_ = v___x_353_;
goto v___jp_289_;
}
else
{
lean_object* v___x_354_; 
lean_inc(v_snd_311_);
v___x_354_ = l_Lean_Meta_Grind_getCongrRoot___redArg(v_snd_311_, v___y_278_, v___y_284_, v___y_285_, v___y_286_, v___y_287_);
if (lean_obj_tag(v___x_354_) == 0)
{
lean_object* v_a_355_; size_t v___x_356_; size_t v___x_357_; uint8_t v___x_358_; 
v_a_355_ = lean_ctor_get(v___x_354_, 0);
lean_inc(v_a_355_);
lean_dec_ref_known(v___x_354_, 1);
v___x_356_ = lean_ptr_addr(v_fst_346_);
lean_dec(v_fst_346_);
v___x_357_ = lean_ptr_addr(v_a_355_);
lean_dec(v_a_355_);
v___x_358_ = lean_usize_dec_eq(v___x_356_, v___x_357_);
if (v___x_358_ == 0)
{
lean_object* v___x_359_; lean_object* v___x_360_; 
lean_dec(v___x_313_);
lean_dec(v_snd_311_);
v___x_359_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___closed__5, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___closed__5_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___closed__5);
v___x_360_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__1(v___x_359_, v___y_278_, v___y_279_, v___y_280_, v___y_281_, v___y_282_, v___y_283_, v___y_284_, v___y_285_, v___y_286_, v___y_287_);
v___y_290_ = v___x_360_;
goto v___jp_289_;
}
else
{
lean_object* v___x_361_; lean_object* v___x_362_; 
v___x_361_ = lean_box(0);
lean_inc_ref(v_curr_275_);
v___x_362_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0(v_root_276_, v_snd_311_, v_curr_275_, v___x_313_, v___x_361_, v___y_278_, v___y_279_, v___y_280_, v___y_281_, v___y_282_, v___y_283_, v___y_284_, v___y_285_, v___y_286_, v___y_287_);
v___y_290_ = v___x_362_;
goto v___jp_289_;
}
}
else
{
lean_object* v_a_363_; lean_object* v___x_365_; uint8_t v_isShared_366_; uint8_t v_isSharedCheck_370_; 
lean_dec(v_fst_346_);
lean_dec(v___x_313_);
lean_dec(v_snd_311_);
lean_dec_ref(v_curr_275_);
v_a_363_ = lean_ctor_get(v___x_354_, 0);
v_isSharedCheck_370_ = !lean_is_exclusive(v___x_354_);
if (v_isSharedCheck_370_ == 0)
{
v___x_365_ = v___x_354_;
v_isShared_366_ = v_isSharedCheck_370_;
goto v_resetjp_364_;
}
else
{
lean_inc(v_a_363_);
lean_dec(v___x_354_);
v___x_365_ = lean_box(0);
v_isShared_366_ = v_isSharedCheck_370_;
goto v_resetjp_364_;
}
v_resetjp_364_:
{
lean_object* v___x_368_; 
if (v_isShared_366_ == 0)
{
v___x_368_ = v___x_365_;
goto v_reusejp_367_;
}
else
{
lean_object* v_reuseFailAlloc_369_; 
v_reuseFailAlloc_369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_369_, 0, v_a_363_);
v___x_368_ = v_reuseFailAlloc_369_;
goto v_reusejp_367_;
}
v_reusejp_367_:
{
return v___x_368_;
}
}
}
}
}
else
{
lean_object* v_a_371_; lean_object* v___x_373_; uint8_t v_isShared_374_; uint8_t v_isSharedCheck_378_; 
lean_dec(v_fst_346_);
lean_dec(v___x_313_);
lean_dec(v_snd_311_);
lean_dec_ref(v_curr_275_);
v_a_371_ = lean_ctor_get(v___x_349_, 0);
v_isSharedCheck_378_ = !lean_is_exclusive(v___x_349_);
if (v_isSharedCheck_378_ == 0)
{
v___x_373_ = v___x_349_;
v_isShared_374_ = v_isSharedCheck_378_;
goto v_resetjp_372_;
}
else
{
lean_inc(v_a_371_);
lean_dec(v___x_349_);
v___x_373_ = lean_box(0);
v_isShared_374_ = v_isSharedCheck_378_;
goto v_resetjp_372_;
}
v_resetjp_372_:
{
lean_object* v___x_376_; 
if (v_isShared_374_ == 0)
{
v___x_376_ = v___x_373_;
goto v_reusejp_375_;
}
else
{
lean_object* v_reuseFailAlloc_377_; 
v_reuseFailAlloc_377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_377_, 0, v_a_371_);
v___x_376_ = v_reuseFailAlloc_377_;
goto v_reusejp_375_;
}
v_reusejp_375_:
{
return v___x_376_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_379_; lean_object* v___x_381_; uint8_t v_isShared_382_; uint8_t v_isSharedCheck_386_; 
lean_dec(v___x_313_);
lean_dec(v_snd_311_);
lean_dec_ref(v_curr_275_);
v_a_379_ = lean_ctor_get(v___x_315_, 0);
v_isSharedCheck_386_ = !lean_is_exclusive(v___x_315_);
if (v_isSharedCheck_386_ == 0)
{
v___x_381_ = v___x_315_;
v_isShared_382_ = v_isSharedCheck_386_;
goto v_resetjp_380_;
}
else
{
lean_inc(v_a_379_);
lean_dec(v___x_315_);
v___x_381_ = lean_box(0);
v_isShared_382_ = v_isSharedCheck_386_;
goto v_resetjp_380_;
}
v_resetjp_380_:
{
lean_object* v___x_384_; 
if (v_isShared_382_ == 0)
{
v___x_384_ = v___x_381_;
goto v_reusejp_383_;
}
else
{
lean_object* v_reuseFailAlloc_385_; 
v_reuseFailAlloc_385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_385_, 0, v_a_379_);
v___x_384_ = v_reuseFailAlloc_385_;
goto v_reusejp_383_;
}
v_reusejp_383_:
{
return v___x_384_;
}
}
}
v___jp_289_:
{
if (lean_obj_tag(v___y_290_) == 0)
{
lean_object* v_a_291_; lean_object* v___x_293_; uint8_t v_isShared_294_; uint8_t v_isSharedCheck_301_; 
v_a_291_ = lean_ctor_get(v___y_290_, 0);
v_isSharedCheck_301_ = !lean_is_exclusive(v___y_290_);
if (v_isSharedCheck_301_ == 0)
{
v___x_293_ = v___y_290_;
v_isShared_294_ = v_isSharedCheck_301_;
goto v_resetjp_292_;
}
else
{
lean_inc(v_a_291_);
lean_dec(v___y_290_);
v___x_293_ = lean_box(0);
v_isShared_294_ = v_isSharedCheck_301_;
goto v_resetjp_292_;
}
v_resetjp_292_:
{
if (lean_obj_tag(v_a_291_) == 0)
{
lean_object* v_a_295_; lean_object* v___x_297_; 
lean_dec_ref(v_curr_275_);
v_a_295_ = lean_ctor_get(v_a_291_, 0);
lean_inc(v_a_295_);
lean_dec_ref_known(v_a_291_, 1);
if (v_isShared_294_ == 0)
{
lean_ctor_set(v___x_293_, 0, v_a_295_);
v___x_297_ = v___x_293_;
goto v_reusejp_296_;
}
else
{
lean_object* v_reuseFailAlloc_298_; 
v_reuseFailAlloc_298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_298_, 0, v_a_295_);
v___x_297_ = v_reuseFailAlloc_298_;
goto v_reusejp_296_;
}
v_reusejp_296_:
{
return v___x_297_;
}
}
else
{
lean_object* v_a_299_; 
lean_del_object(v___x_293_);
v_a_299_ = lean_ctor_get(v_a_291_, 0);
lean_inc(v_a_299_);
lean_dec_ref_known(v_a_291_, 1);
v_a_277_ = v_a_299_;
goto _start;
}
}
}
else
{
lean_object* v_a_302_; lean_object* v___x_304_; uint8_t v_isShared_305_; uint8_t v_isSharedCheck_309_; 
lean_dec_ref(v_curr_275_);
v_a_302_ = lean_ctor_get(v___y_290_, 0);
v_isSharedCheck_309_ = !lean_is_exclusive(v___y_290_);
if (v_isSharedCheck_309_ == 0)
{
v___x_304_ = v___y_290_;
v_isShared_305_ = v_isSharedCheck_309_;
goto v_resetjp_303_;
}
else
{
lean_inc(v_a_302_);
lean_dec(v___y_290_);
v___x_304_ = lean_box(0);
v_isShared_305_ = v_isSharedCheck_309_;
goto v_resetjp_303_;
}
v_resetjp_303_:
{
lean_object* v___x_307_; 
if (v_isShared_305_ == 0)
{
v___x_307_ = v___x_304_;
goto v_reusejp_306_;
}
else
{
lean_object* v_reuseFailAlloc_308_; 
v_reuseFailAlloc_308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_308_, 0, v_a_302_);
v___x_307_ = v_reuseFailAlloc_308_;
goto v_reusejp_306_;
}
v_reusejp_306_:
{
return v___x_307_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_curr_275_ = stack[0].m_obj;
lean_object* v_root_276_ = stack[1].m_obj;
lean_object* v_a_277_ = stack[2].m_obj;
lean_object* v___y_278_ = stack[3].m_obj;
lean_object* v___y_279_ = stack[4].m_obj;
lean_object* v___y_280_ = stack[5].m_obj;
lean_object* v___y_281_ = stack[6].m_obj;
lean_object* v___y_282_ = stack[7].m_obj;
lean_object* v___y_283_ = stack[8].m_obj;
lean_object* v___y_284_ = stack[9].m_obj;
lean_object* v___y_285_ = stack[10].m_obj;
lean_object* v___y_286_ = stack[11].m_obj;
lean_object* v___y_287_ = stack[12].m_obj;
lean_object* v_res_387_;
v_res_387_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg(v_curr_275_, v_root_276_, v_a_277_, v___y_278_, v___y_279_, v___y_280_, v___y_281_, v___y_282_, v___y_283_, v___y_284_, v___y_285_, v___y_286_, v___y_287_);
stack->m_obj
 = v_res_387_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___boxed(lean_object* v_curr_388_, lean_object* v_root_389_, lean_object* v_a_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_){
_start:
{
lean_object* v_res_402_; 
v_res_402_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg(v_curr_388_, v_root_389_, v_a_390_, v___y_391_, v___y_392_, v___y_393_, v___y_394_, v___y_395_, v___y_396_, v___y_397_, v___y_398_, v___y_399_, v___y_400_);
lean_dec(v___y_400_);
lean_dec_ref(v___y_399_);
lean_dec(v___y_398_);
lean_dec_ref(v___y_397_);
lean_dec(v___y_396_);
lean_dec_ref(v___y_395_);
lean_dec(v___y_394_);
lean_dec_ref(v___y_393_);
lean_dec(v___y_392_);
lean_dec(v___y_391_);
lean_dec_ref(v_root_389_);
return v_res_402_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc___closed__1(void){
_start:
{
lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; 
v___x_404_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc___closed__0));
v___x_405_ = lean_unsigned_to_nat(2u);
v___x_406_ = lean_unsigned_to_nat(47u);
v___x_407_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__1));
v___x_408_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__0));
v___x_409_ = l_mkPanicMessageWithDecl(v___x_408_, v___x_407_, v___x_406_, v___x_405_, v___x_404_);
return v___x_409_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc(lean_object* v_root_410_, lean_object* v_a_411_, lean_object* v_a_412_, lean_object* v_a_413_, lean_object* v_a_414_, lean_object* v_a_415_, lean_object* v_a_416_, lean_object* v_a_417_, lean_object* v_a_418_, lean_object* v_a_419_, lean_object* v_a_420_){
_start:
{
lean_object* v_self_422_; lean_object* v_size_423_; lean_object* v_size_424_; lean_object* v___x_425_; lean_object* v___x_426_; 
v_self_422_ = lean_ctor_get(v_root_410_, 0);
lean_inc_ref_n(v_self_422_, 2);
v_size_423_ = lean_ctor_get(v_root_410_, 6);
lean_inc(v_size_423_);
v_size_424_ = lean_unsigned_to_nat(0u);
v___x_425_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_425_, 0, v_size_424_);
lean_ctor_set(v___x_425_, 1, v_self_422_);
v___x_426_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg(v_self_422_, v_root_410_, v___x_425_, v_a_411_, v_a_412_, v_a_413_, v_a_414_, v_a_415_, v_a_416_, v_a_417_, v_a_418_, v_a_419_, v_a_420_);
lean_dec_ref(v_root_410_);
if (lean_obj_tag(v___x_426_) == 0)
{
lean_object* v_a_427_; lean_object* v___x_429_; uint8_t v_isShared_430_; uint8_t v_isSharedCheck_439_; 
v_a_427_ = lean_ctor_get(v___x_426_, 0);
v_isSharedCheck_439_ = !lean_is_exclusive(v___x_426_);
if (v_isSharedCheck_439_ == 0)
{
v___x_429_ = v___x_426_;
v_isShared_430_ = v_isSharedCheck_439_;
goto v_resetjp_428_;
}
else
{
lean_inc(v_a_427_);
lean_dec(v___x_426_);
v___x_429_ = lean_box(0);
v_isShared_430_ = v_isSharedCheck_439_;
goto v_resetjp_428_;
}
v_resetjp_428_:
{
lean_object* v_fst_431_; uint8_t v___x_432_; 
v_fst_431_ = lean_ctor_get(v_a_427_, 0);
lean_inc(v_fst_431_);
lean_dec(v_a_427_);
v___x_432_ = lean_nat_dec_eq(v_size_423_, v_fst_431_);
lean_dec(v_fst_431_);
lean_dec(v_size_423_);
if (v___x_432_ == 0)
{
lean_object* v___x_433_; lean_object* v___x_434_; 
lean_del_object(v___x_429_);
v___x_433_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc___closed__1, &l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc___closed__1);
v___x_434_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__4(v___x_433_, v_a_411_, v_a_412_, v_a_413_, v_a_414_, v_a_415_, v_a_416_, v_a_417_, v_a_418_, v_a_419_, v_a_420_);
return v___x_434_;
}
else
{
lean_object* v___x_435_; lean_object* v___x_437_; 
v___x_435_ = lean_box(0);
if (v_isShared_430_ == 0)
{
lean_ctor_set(v___x_429_, 0, v___x_435_);
v___x_437_ = v___x_429_;
goto v_reusejp_436_;
}
else
{
lean_object* v_reuseFailAlloc_438_; 
v_reuseFailAlloc_438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_438_, 0, v___x_435_);
v___x_437_ = v_reuseFailAlloc_438_;
goto v_reusejp_436_;
}
v_reusejp_436_:
{
return v___x_437_;
}
}
}
}
else
{
lean_object* v_a_440_; lean_object* v___x_442_; uint8_t v_isShared_443_; uint8_t v_isSharedCheck_447_; 
lean_dec(v_size_423_);
v_a_440_ = lean_ctor_get(v___x_426_, 0);
v_isSharedCheck_447_ = !lean_is_exclusive(v___x_426_);
if (v_isSharedCheck_447_ == 0)
{
v___x_442_ = v___x_426_;
v_isShared_443_ = v_isSharedCheck_447_;
goto v_resetjp_441_;
}
else
{
lean_inc(v_a_440_);
lean_dec(v___x_426_);
v___x_442_ = lean_box(0);
v_isShared_443_ = v_isSharedCheck_447_;
goto v_resetjp_441_;
}
v_resetjp_441_:
{
lean_object* v___x_445_; 
if (v_isShared_443_ == 0)
{
v___x_445_ = v___x_442_;
goto v_reusejp_444_;
}
else
{
lean_object* v_reuseFailAlloc_446_; 
v_reuseFailAlloc_446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_446_, 0, v_a_440_);
v___x_445_ = v_reuseFailAlloc_446_;
goto v_reusejp_444_;
}
v_reusejp_444_:
{
return v___x_445_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_0interp(lean_interpreter_value* stack)
{
lean_object* v_root_410_ = stack[0].m_obj;
lean_object* v_a_411_ = stack[1].m_obj;
lean_object* v_a_412_ = stack[2].m_obj;
lean_object* v_a_413_ = stack[3].m_obj;
lean_object* v_a_414_ = stack[4].m_obj;
lean_object* v_a_415_ = stack[5].m_obj;
lean_object* v_a_416_ = stack[6].m_obj;
lean_object* v_a_417_ = stack[7].m_obj;
lean_object* v_a_418_ = stack[8].m_obj;
lean_object* v_a_419_ = stack[9].m_obj;
lean_object* v_a_420_ = stack[10].m_obj;
lean_object* v_res_448_;
v_res_448_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc(v_root_410_, v_a_411_, v_a_412_, v_a_413_, v_a_414_, v_a_415_, v_a_416_, v_a_417_, v_a_418_, v_a_419_, v_a_420_);
stack->m_obj
 = v_res_448_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc___boxed(lean_object* v_root_449_, lean_object* v_a_450_, lean_object* v_a_451_, lean_object* v_a_452_, lean_object* v_a_453_, lean_object* v_a_454_, lean_object* v_a_455_, lean_object* v_a_456_, lean_object* v_a_457_, lean_object* v_a_458_, lean_object* v_a_459_, lean_object* v_a_460_){
_start:
{
lean_object* v_res_461_; 
v_res_461_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc(v_root_449_, v_a_450_, v_a_451_, v_a_452_, v_a_453_, v_a_454_, v_a_455_, v_a_456_, v_a_457_, v_a_458_, v_a_459_);
lean_dec(v_a_459_);
lean_dec_ref(v_a_458_);
lean_dec(v_a_457_);
lean_dec_ref(v_a_456_);
lean_dec(v_a_455_);
lean_dec_ref(v_a_454_);
lean_dec(v_a_453_);
lean_dec_ref(v_a_452_);
lean_dec(v_a_451_);
lean_dec(v_a_450_);
return v_res_461_;
}
}
lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__0(lean_object* v_inst_462_, lean_object* v_a_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_){
_start:
{
lean_object* v___x_475_; 
v___x_475_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__0___redArg(v_a_463_, v___y_464_);
return v___x_475_;
}
}
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_463_ = stack[1].m_obj;
lean_object* v___y_464_ = stack[2].m_obj;
lean_object* v___y_465_ = stack[3].m_obj;
lean_object* v___y_466_ = stack[4].m_obj;
lean_object* v___y_467_ = stack[5].m_obj;
lean_object* v___y_468_ = stack[6].m_obj;
lean_object* v___y_469_ = stack[7].m_obj;
lean_object* v___y_470_ = stack[8].m_obj;
lean_object* v___y_471_ = stack[9].m_obj;
lean_object* v___y_472_ = stack[10].m_obj;
lean_object* v___y_473_ = stack[11].m_obj;
lean_object* v_res_476_;
v_res_476_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__0(lean_box(0), v_a_463_, v___y_464_, v___y_465_, v___y_466_, v___y_467_, v___y_468_, v___y_469_, v___y_470_, v___y_471_, v___y_472_, v___y_473_);
stack->m_obj
 = v_res_476_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__0___boxed(lean_object* v_inst_477_, lean_object* v_a_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_){
_start:
{
lean_object* v_res_490_; 
v_res_490_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__0(v_inst_477_, v_a_478_, v___y_479_, v___y_480_, v___y_481_, v___y_482_, v___y_483_, v___y_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_);
lean_dec(v___y_488_);
lean_dec_ref(v___y_487_);
lean_dec(v___y_486_);
lean_dec_ref(v___y_485_);
lean_dec(v___y_484_);
lean_dec_ref(v___y_483_);
lean_dec(v___y_482_);
lean_dec_ref(v___y_481_);
lean_dec(v___y_480_);
lean_dec(v___y_479_);
return v_res_490_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2(lean_object* v___x_491_, lean_object* v_00_u03b2_492_, lean_object* v_x_493_, lean_object* v_x_494_){
_start:
{
lean_object* v___x_495_; 
v___x_495_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2___redArg(v___x_491_, v_x_493_, v_x_494_);
return v___x_495_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2___boxed(lean_object* v___x_496_, lean_object* v_00_u03b2_497_, lean_object* v_x_498_, lean_object* v_x_499_){
_start:
{
lean_object* v_res_500_; 
v_res_500_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2(v___x_496_, v_00_u03b2_497_, v_x_498_, v_x_499_);
lean_dec_ref(v_x_498_);
lean_dec_ref(v___x_496_);
return v_res_500_;
}
}
lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3(lean_object* v_curr_501_, lean_object* v_root_502_, lean_object* v_inst_503_, lean_object* v_a_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_){
_start:
{
lean_object* v___x_516_; 
v___x_516_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg(v_curr_501_, v_root_502_, v_a_504_, v___y_505_, v___y_506_, v___y_507_, v___y_508_, v___y_509_, v___y_510_, v___y_511_, v___y_512_, v___y_513_, v___y_514_);
return v___x_516_;
}
}
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_curr_501_ = stack[0].m_obj;
lean_object* v_root_502_ = stack[1].m_obj;
lean_object* v_a_504_ = stack[3].m_obj;
lean_object* v___y_505_ = stack[4].m_obj;
lean_object* v___y_506_ = stack[5].m_obj;
lean_object* v___y_507_ = stack[6].m_obj;
lean_object* v___y_508_ = stack[7].m_obj;
lean_object* v___y_509_ = stack[8].m_obj;
lean_object* v___y_510_ = stack[9].m_obj;
lean_object* v___y_511_ = stack[10].m_obj;
lean_object* v___y_512_ = stack[11].m_obj;
lean_object* v___y_513_ = stack[12].m_obj;
lean_object* v___y_514_ = stack[13].m_obj;
lean_object* v_res_517_;
v_res_517_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3(v_curr_501_, v_root_502_, lean_box(0), v_a_504_, v___y_505_, v___y_506_, v___y_507_, v___y_508_, v___y_509_, v___y_510_, v___y_511_, v___y_512_, v___y_513_, v___y_514_);
stack->m_obj
 = v_res_517_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___boxed(lean_object* v_curr_518_, lean_object* v_root_519_, lean_object* v_inst_520_, lean_object* v_a_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_){
_start:
{
lean_object* v_res_533_; 
v_res_533_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3(v_curr_518_, v_root_519_, v_inst_520_, v_a_521_, v___y_522_, v___y_523_, v___y_524_, v___y_525_, v___y_526_, v___y_527_, v___y_528_, v___y_529_, v___y_530_, v___y_531_);
lean_dec(v___y_531_);
lean_dec_ref(v___y_530_);
lean_dec(v___y_529_);
lean_dec_ref(v___y_528_);
lean_dec(v___y_527_);
lean_dec_ref(v___y_526_);
lean_dec(v___y_525_);
lean_dec_ref(v___y_524_);
lean_dec(v___y_523_);
lean_dec(v___y_522_);
lean_dec_ref(v_root_519_);
return v_res_533_;
}
}
lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2(lean_object* v___x_534_, lean_object* v_00_u03b2_535_, lean_object* v_x_536_, size_t v_x_537_, lean_object* v_x_538_){
_start:
{
lean_object* v___x_539_; 
lean_inc_ref(v_x_536_);
v___x_539_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2___redArg(v___x_534_, v_x_536_, v_x_537_, v_x_538_);
return v___x_539_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_534_ = stack[0].m_obj;
lean_object* v_x_536_ = stack[2].m_obj;
size_t v_x_537_ = stack[3].m_num;
lean_object* v_x_538_ = stack[4].m_obj;
lean_object* v_res_540_;
v_res_540_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2(v___x_534_, lean_box(0), v_x_536_, v_x_537_, v_x_538_);
stack->m_obj
 = v_res_540_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2___boxed(lean_object* v___x_541_, lean_object* v_00_u03b2_542_, lean_object* v_x_543_, lean_object* v_x_544_, lean_object* v_x_545_){
_start:
{
size_t v_x_27581__boxed_546_; lean_object* v_res_547_; 
v_x_27581__boxed_546_ = lean_unbox_usize(v_x_544_);
lean_dec(v_x_544_);
v_res_547_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2(v___x_541_, v_00_u03b2_542_, v_x_543_, v_x_27581__boxed_546_, v_x_545_);
lean_dec_ref(v_x_543_);
lean_dec_ref(v___x_541_);
return v_res_547_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2_spec__4(lean_object* v___x_548_, lean_object* v_00_u03b2_549_, lean_object* v_keys_550_, lean_object* v_vals_551_, lean_object* v_heq_552_, lean_object* v_i_553_, lean_object* v_k_554_){
_start:
{
lean_object* v___x_555_; 
v___x_555_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2_spec__4___redArg(v___x_548_, v_keys_550_, v_vals_551_, v_i_553_, v_k_554_);
return v___x_555_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2_spec__4___boxed(lean_object* v___x_556_, lean_object* v_00_u03b2_557_, lean_object* v_keys_558_, lean_object* v_vals_559_, lean_object* v_heq_560_, lean_object* v_i_561_, lean_object* v_k_562_){
_start:
{
lean_object* v_res_563_; 
v_res_563_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2_spec__4(v___x_556_, v_00_u03b2_557_, v_keys_558_, v_vals_559_, v_heq_560_, v_i_561_, v_k_562_);
lean_dec_ref(v_vals_559_);
lean_dec_ref(v_keys_558_);
lean_dec_ref(v___x_556_);
return v_res_563_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkChild___redArg(lean_object* v_e_564_, lean_object* v_child_565_, lean_object* v_a_566_){
_start:
{
lean_object* v___x_568_; lean_object* v___x_569_; 
v___x_568_ = lean_st_ref_get(v_a_566_);
v___x_569_ = l_Lean_Meta_Grind_Goal_getRoot_x3f(v___x_568_, v_child_565_);
lean_dec(v___x_568_);
if (lean_obj_tag(v___x_569_) == 1)
{
lean_object* v_val_570_; lean_object* v___x_572_; uint8_t v_isShared_573_; uint8_t v_isSharedCheck_581_; 
v_val_570_ = lean_ctor_get(v___x_569_, 0);
v_isSharedCheck_581_ = !lean_is_exclusive(v___x_569_);
if (v_isSharedCheck_581_ == 0)
{
v___x_572_ = v___x_569_;
v_isShared_573_ = v_isSharedCheck_581_;
goto v_resetjp_571_;
}
else
{
lean_inc(v_val_570_);
lean_dec(v___x_569_);
v___x_572_ = lean_box(0);
v_isShared_573_ = v_isSharedCheck_581_;
goto v_resetjp_571_;
}
v_resetjp_571_:
{
size_t v___x_574_; size_t v___x_575_; uint8_t v___x_576_; lean_object* v___x_577_; lean_object* v___x_579_; 
v___x_574_ = lean_ptr_addr(v_val_570_);
lean_dec(v_val_570_);
v___x_575_ = lean_ptr_addr(v_e_564_);
v___x_576_ = lean_usize_dec_eq(v___x_574_, v___x_575_);
v___x_577_ = lean_box(v___x_576_);
if (v_isShared_573_ == 0)
{
lean_ctor_set_tag(v___x_572_, 0);
lean_ctor_set(v___x_572_, 0, v___x_577_);
v___x_579_ = v___x_572_;
goto v_reusejp_578_;
}
else
{
lean_object* v_reuseFailAlloc_580_; 
v_reuseFailAlloc_580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_580_, 0, v___x_577_);
v___x_579_ = v_reuseFailAlloc_580_;
goto v_reusejp_578_;
}
v_reusejp_578_:
{
return v___x_579_;
}
}
}
else
{
uint8_t v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; 
lean_dec(v___x_569_);
v___x_582_ = 0;
v___x_583_ = lean_box(v___x_582_);
v___x_584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_584_, 0, v___x_583_);
return v___x_584_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkChild___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_564_ = stack[0].m_obj;
lean_object* v_child_565_ = stack[1].m_obj;
lean_object* v_a_566_ = stack[2].m_obj;
lean_object* v_res_585_;
v_res_585_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkChild___redArg(v_e_564_, v_child_565_, v_a_566_);
stack->m_obj
 = v_res_585_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkChild___redArg___boxed(lean_object* v_e_586_, lean_object* v_child_587_, lean_object* v_a_588_, lean_object* v_a_589_){
_start:
{
lean_object* v_res_590_; 
v_res_590_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkChild___redArg(v_e_586_, v_child_587_, v_a_588_);
lean_dec(v_a_588_);
lean_dec_ref(v_child_587_);
lean_dec_ref(v_e_586_);
return v_res_590_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkChild(lean_object* v_e_591_, lean_object* v_child_592_, lean_object* v_a_593_, lean_object* v_a_594_, lean_object* v_a_595_, lean_object* v_a_596_, lean_object* v_a_597_, lean_object* v_a_598_, lean_object* v_a_599_, lean_object* v_a_600_, lean_object* v_a_601_, lean_object* v_a_602_){
_start:
{
lean_object* v___x_604_; 
v___x_604_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkChild___redArg(v_e_591_, v_child_592_, v_a_593_);
return v___x_604_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkChild_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_591_ = stack[0].m_obj;
lean_object* v_child_592_ = stack[1].m_obj;
lean_object* v_a_593_ = stack[2].m_obj;
lean_object* v_a_594_ = stack[3].m_obj;
lean_object* v_a_595_ = stack[4].m_obj;
lean_object* v_a_596_ = stack[5].m_obj;
lean_object* v_a_597_ = stack[6].m_obj;
lean_object* v_a_598_ = stack[7].m_obj;
lean_object* v_a_599_ = stack[8].m_obj;
lean_object* v_a_600_ = stack[9].m_obj;
lean_object* v_a_601_ = stack[10].m_obj;
lean_object* v_a_602_ = stack[11].m_obj;
lean_object* v_res_605_;
v_res_605_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkChild(v_e_591_, v_child_592_, v_a_593_, v_a_594_, v_a_595_, v_a_596_, v_a_597_, v_a_598_, v_a_599_, v_a_600_, v_a_601_, v_a_602_);
stack->m_obj
 = v_res_605_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkChild___boxed(lean_object* v_e_606_, lean_object* v_child_607_, lean_object* v_a_608_, lean_object* v_a_609_, lean_object* v_a_610_, lean_object* v_a_611_, lean_object* v_a_612_, lean_object* v_a_613_, lean_object* v_a_614_, lean_object* v_a_615_, lean_object* v_a_616_, lean_object* v_a_617_, lean_object* v_a_618_){
_start:
{
lean_object* v_res_619_; 
v_res_619_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkChild(v_e_606_, v_child_607_, v_a_608_, v_a_609_, v_a_610_, v_a_611_, v_a_612_, v_a_613_, v_a_614_, v_a_615_, v_a_616_, v_a_617_);
lean_dec(v_a_617_);
lean_dec_ref(v_a_616_);
lean_dec(v_a_615_);
lean_dec_ref(v_a_614_);
lean_dec(v_a_613_);
lean_dec_ref(v_a_612_);
lean_dec(v_a_611_);
lean_dec_ref(v_a_610_);
lean_dec(v_a_609_);
lean_dec(v_a_608_);
lean_dec_ref(v_child_607_);
lean_dec_ref(v_e_606_);
return v_res_619_;
}
}
lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___lam__0(lean_object* v___x_620_, lean_object* v_body_621_, lean_object* v_____r_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_){
_start:
{
lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; 
v___x_634_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_634_, 0, v___x_620_);
lean_ctor_set(v___x_634_, 1, v_body_621_);
v___x_635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_635_, 0, v___x_634_);
v___x_636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_636_, 0, v___x_635_);
return v___x_636_;
}
}
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_620_ = stack[0].m_obj;
lean_object* v_body_621_ = stack[1].m_obj;
lean_object* v_____r_622_ = stack[2].m_obj;
lean_object* v___y_623_ = stack[3].m_obj;
lean_object* v___y_624_ = stack[4].m_obj;
lean_object* v___y_625_ = stack[5].m_obj;
lean_object* v___y_626_ = stack[6].m_obj;
lean_object* v___y_627_ = stack[7].m_obj;
lean_object* v___y_628_ = stack[8].m_obj;
lean_object* v___y_629_ = stack[9].m_obj;
lean_object* v___y_630_ = stack[10].m_obj;
lean_object* v___y_631_ = stack[11].m_obj;
lean_object* v___y_632_ = stack[12].m_obj;
lean_object* v_res_637_;
v_res_637_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___lam__0(v___x_620_, v_body_621_, v_____r_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_, v___y_630_, v___y_631_, v___y_632_);
stack->m_obj
 = v_res_637_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___lam__0___boxed(lean_object* v___x_638_, lean_object* v_body_639_, lean_object* v_____r_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_){
_start:
{
lean_object* v_res_652_; 
v_res_652_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___lam__0(v___x_638_, v_body_639_, v_____r_640_, v___y_641_, v___y_642_, v___y_643_, v___y_644_, v___y_645_, v___y_646_, v___y_647_, v___y_648_, v___y_649_, v___y_650_);
lean_dec(v___y_650_);
lean_dec_ref(v___y_649_);
lean_dec(v___y_648_);
lean_dec_ref(v___y_647_);
lean_dec(v___y_646_);
lean_dec_ref(v___y_645_);
lean_dec(v___y_644_);
lean_dec_ref(v___y_643_);
lean_dec(v___y_642_);
lean_dec(v___y_641_);
return v_res_652_;
}
}
lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___lam__1(lean_object* v___f_653_, lean_object* v_x_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_){
_start:
{
lean_object* v___x_666_; lean_object* v___x_667_; 
v___x_666_ = lean_box(0);
lean_inc(v___y_664_);
lean_inc_ref(v___y_663_);
lean_inc(v___y_662_);
lean_inc_ref(v___y_661_);
lean_inc(v___y_660_);
lean_inc_ref(v___y_659_);
lean_inc(v___y_658_);
lean_inc_ref(v___y_657_);
lean_inc(v___y_656_);
lean_inc(v___y_655_);
v___x_667_ = lean_apply_12(v___f_653_, v___x_666_, v___y_655_, v___y_656_, v___y_657_, v___y_658_, v___y_659_, v___y_660_, v___y_661_, v___y_662_, v___y_663_, v___y_664_, lean_box(0));
return v___x_667_;
}
}
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_653_ = stack[0].m_obj;
lean_object* v_x_654_ = stack[1].m_obj;
lean_object* v___y_655_ = stack[2].m_obj;
lean_object* v___y_656_ = stack[3].m_obj;
lean_object* v___y_657_ = stack[4].m_obj;
lean_object* v___y_658_ = stack[5].m_obj;
lean_object* v___y_659_ = stack[6].m_obj;
lean_object* v___y_660_ = stack[7].m_obj;
lean_object* v___y_661_ = stack[8].m_obj;
lean_object* v___y_662_ = stack[9].m_obj;
lean_object* v___y_663_ = stack[10].m_obj;
lean_object* v___y_664_ = stack[11].m_obj;
lean_object* v_res_668_;
v_res_668_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___lam__1(v___f_653_, v_x_654_, v___y_655_, v___y_656_, v___y_657_, v___y_658_, v___y_659_, v___y_660_, v___y_661_, v___y_662_, v___y_663_, v___y_664_);
stack->m_obj
 = v_res_668_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___lam__1___boxed(lean_object* v___f_669_, lean_object* v_x_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_){
_start:
{
lean_object* v_res_682_; 
v_res_682_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___lam__1(v___f_669_, v_x_670_, v___y_671_, v___y_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_);
lean_dec(v___y_680_);
lean_dec_ref(v___y_679_);
lean_dec(v___y_678_);
lean_dec_ref(v___y_677_);
lean_dec(v___y_676_);
lean_dec_ref(v___y_675_);
lean_dec(v___y_674_);
lean_dec_ref(v___y_673_);
lean_dec(v___y_672_);
lean_dec(v___y_671_);
return v_res_682_;
}
}
lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg(lean_object* v_e_692_, lean_object* v_a_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_){
_start:
{
lean_object* v___y_706_; lean_object* v_snd_726_; lean_object* v___x_728_; uint8_t v_isShared_729_; uint8_t v_isSharedCheck_830_; 
v_snd_726_ = lean_ctor_get(v_a_693_, 1);
v_isSharedCheck_830_ = !lean_is_exclusive(v_a_693_);
if (v_isSharedCheck_830_ == 0)
{
lean_object* v_unused_831_; 
v_unused_831_ = lean_ctor_get(v_a_693_, 0);
lean_dec(v_unused_831_);
v___x_728_ = v_a_693_;
v_isShared_729_ = v_isSharedCheck_830_;
goto v_resetjp_727_;
}
else
{
lean_inc(v_snd_726_);
lean_dec(v_a_693_);
v___x_728_ = lean_box(0);
v_isShared_729_ = v_isSharedCheck_830_;
goto v_resetjp_727_;
}
v___jp_705_:
{
if (lean_obj_tag(v___y_706_) == 0)
{
lean_object* v_a_707_; lean_object* v___x_709_; uint8_t v_isShared_710_; uint8_t v_isSharedCheck_717_; 
v_a_707_ = lean_ctor_get(v___y_706_, 0);
v_isSharedCheck_717_ = !lean_is_exclusive(v___y_706_);
if (v_isSharedCheck_717_ == 0)
{
v___x_709_ = v___y_706_;
v_isShared_710_ = v_isSharedCheck_717_;
goto v_resetjp_708_;
}
else
{
lean_inc(v_a_707_);
lean_dec(v___y_706_);
v___x_709_ = lean_box(0);
v_isShared_710_ = v_isSharedCheck_717_;
goto v_resetjp_708_;
}
v_resetjp_708_:
{
if (lean_obj_tag(v_a_707_) == 0)
{
lean_object* v_a_711_; lean_object* v___x_713_; 
v_a_711_ = lean_ctor_get(v_a_707_, 0);
lean_inc(v_a_711_);
lean_dec_ref_known(v_a_707_, 1);
if (v_isShared_710_ == 0)
{
lean_ctor_set(v___x_709_, 0, v_a_711_);
v___x_713_ = v___x_709_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_714_; 
v_reuseFailAlloc_714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_714_, 0, v_a_711_);
v___x_713_ = v_reuseFailAlloc_714_;
goto v_reusejp_712_;
}
v_reusejp_712_:
{
return v___x_713_;
}
}
else
{
lean_object* v_a_715_; 
lean_del_object(v___x_709_);
v_a_715_ = lean_ctor_get(v_a_707_, 0);
lean_inc(v_a_715_);
lean_dec_ref_known(v_a_707_, 1);
v_a_693_ = v_a_715_;
goto _start;
}
}
}
else
{
lean_object* v_a_718_; lean_object* v___x_720_; uint8_t v_isShared_721_; uint8_t v_isSharedCheck_725_; 
v_a_718_ = lean_ctor_get(v___y_706_, 0);
v_isSharedCheck_725_ = !lean_is_exclusive(v___y_706_);
if (v_isSharedCheck_725_ == 0)
{
v___x_720_ = v___y_706_;
v_isShared_721_ = v_isSharedCheck_725_;
goto v_resetjp_719_;
}
else
{
lean_inc(v_a_718_);
lean_dec(v___y_706_);
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
v_resetjp_727_:
{
if (lean_obj_tag(v_snd_726_) == 7)
{
lean_object* v_binderType_730_; lean_object* v_body_731_; lean_object* v___x_732_; lean_object* v___f_733_; lean_object* v___x_734_; 
v_binderType_730_ = lean_ctor_get(v_snd_726_, 1);
v_body_731_ = lean_ctor_get(v_snd_726_, 2);
v___x_732_ = lean_box(0);
lean_inc_ref(v_body_731_);
v___f_733_ = lean_alloc_closure((void*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___lam__0___boxed), 14, 2);
lean_closure_set(v___f_733_, 0, v___x_732_);
lean_closure_set(v___f_733_, 1, v_body_731_);
lean_inc_ref(v_binderType_730_);
v___x_734_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_binderType_730_, v___y_701_);
if (lean_obj_tag(v___x_734_) == 0)
{
lean_object* v_a_735_; lean_object* v___x_736_; uint8_t v___x_737_; 
v_a_735_ = lean_ctor_get(v___x_734_, 0);
lean_inc(v_a_735_);
lean_dec_ref_known(v___x_734_, 1);
v___x_736_ = l_Lean_Expr_cleanupAnnotations(v_a_735_);
v___x_737_ = l_Lean_Expr_isApp(v___x_736_);
if (v___x_737_ == 0)
{
lean_object* v___x_738_; lean_object* v___x_739_; 
lean_dec_ref(v___x_736_);
lean_dec_ref_known(v_snd_726_, 3);
lean_del_object(v___x_728_);
v___x_738_ = lean_box(0);
v___x_739_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___lam__1(v___f_733_, v___x_738_, v___y_694_, v___y_695_, v___y_696_, v___y_697_, v___y_698_, v___y_699_, v___y_700_, v___y_701_, v___y_702_, v___y_703_);
v___y_706_ = v___x_739_;
goto v___jp_705_;
}
else
{
lean_object* v___x_740_; uint8_t v___x_741_; 
v___x_740_ = l_Lean_Expr_appFnCleanup___redArg(v___x_736_);
v___x_741_ = l_Lean_Expr_isApp(v___x_740_);
if (v___x_741_ == 0)
{
lean_object* v___x_742_; lean_object* v___x_743_; 
lean_dec_ref(v___x_740_);
lean_dec_ref_known(v_snd_726_, 3);
lean_del_object(v___x_728_);
v___x_742_ = lean_box(0);
v___x_743_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___lam__1(v___f_733_, v___x_742_, v___y_694_, v___y_695_, v___y_696_, v___y_697_, v___y_698_, v___y_699_, v___y_700_, v___y_701_, v___y_702_, v___y_703_);
v___y_706_ = v___x_743_;
goto v___jp_705_;
}
else
{
lean_object* v_arg_744_; lean_object* v___x_745_; uint8_t v___x_746_; 
v_arg_744_ = lean_ctor_get(v___x_740_, 1);
lean_inc_ref(v_arg_744_);
v___x_745_ = l_Lean_Expr_appFnCleanup___redArg(v___x_740_);
v___x_746_ = l_Lean_Expr_isApp(v___x_745_);
if (v___x_746_ == 0)
{
lean_object* v___x_747_; lean_object* v___x_748_; 
lean_dec_ref(v___x_745_);
lean_dec_ref(v_arg_744_);
lean_dec_ref_known(v_snd_726_, 3);
lean_del_object(v___x_728_);
v___x_747_ = lean_box(0);
v___x_748_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___lam__1(v___f_733_, v___x_747_, v___y_694_, v___y_695_, v___y_696_, v___y_697_, v___y_698_, v___y_699_, v___y_700_, v___y_701_, v___y_702_, v___y_703_);
v___y_706_ = v___x_748_;
goto v___jp_705_;
}
else
{
lean_object* v_arg_749_; lean_object* v___x_750_; lean_object* v___x_751_; uint8_t v___x_752_; 
v_arg_749_ = lean_ctor_get(v___x_745_, 1);
lean_inc_ref(v_arg_749_);
v___x_750_ = l_Lean_Expr_appFnCleanup___redArg(v___x_745_);
v___x_751_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___closed__1));
v___x_752_ = l_Lean_Expr_isConstOf(v___x_750_, v___x_751_);
if (v___x_752_ == 0)
{
uint8_t v___x_753_; 
lean_dec_ref(v_arg_744_);
v___x_753_ = l_Lean_Expr_isApp(v___x_750_);
if (v___x_753_ == 0)
{
lean_object* v___x_754_; lean_object* v___x_755_; 
lean_dec_ref(v___x_750_);
lean_dec_ref(v_arg_749_);
lean_dec_ref_known(v_snd_726_, 3);
lean_del_object(v___x_728_);
v___x_754_ = lean_box(0);
v___x_755_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___lam__1(v___f_733_, v___x_754_, v___y_694_, v___y_695_, v___y_696_, v___y_697_, v___y_698_, v___y_699_, v___y_700_, v___y_701_, v___y_702_, v___y_703_);
v___y_706_ = v___x_755_;
goto v___jp_705_;
}
else
{
lean_object* v_arg_756_; lean_object* v___x_757_; lean_object* v___x_758_; uint8_t v___x_759_; lean_object* v___y_761_; 
v_arg_756_ = lean_ctor_get(v___x_750_, 1);
lean_inc_ref(v_arg_756_);
v___x_757_ = l_Lean_Expr_appFnCleanup___redArg(v___x_750_);
v___x_758_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___closed__3));
v___x_759_ = l_Lean_Expr_isConstOf(v___x_757_, v___x_758_);
lean_dec_ref(v___x_757_);
if (v___x_759_ == 0)
{
lean_object* v___x_786_; lean_object* v___x_787_; 
lean_dec_ref(v_arg_756_);
lean_dec_ref(v_arg_749_);
lean_dec_ref_known(v_snd_726_, 3);
lean_del_object(v___x_728_);
v___x_786_ = lean_box(0);
v___x_787_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___lam__1(v___f_733_, v___x_786_, v___y_694_, v___y_695_, v___y_696_, v___y_697_, v___y_698_, v___y_699_, v___y_700_, v___y_701_, v___y_702_, v___y_703_);
v___y_706_ = v___x_787_;
goto v___jp_705_;
}
else
{
lean_object* v___x_788_; 
lean_dec_ref(v___f_733_);
v___x_788_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkChild___redArg(v_e_692_, v_arg_756_, v___y_694_);
lean_dec_ref(v_arg_756_);
if (lean_obj_tag(v___x_788_) == 0)
{
lean_object* v_a_789_; uint8_t v___x_790_; 
v_a_789_ = lean_ctor_get(v___x_788_, 0);
v___x_790_ = lean_unbox(v_a_789_);
if (v___x_790_ == 0)
{
lean_object* v___x_791_; 
lean_dec_ref_known(v___x_788_, 1);
v___x_791_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkChild___redArg(v_e_692_, v_arg_749_, v___y_694_);
lean_dec_ref(v_arg_749_);
v___y_761_ = v___x_791_;
goto v___jp_760_;
}
else
{
lean_dec_ref(v_arg_749_);
v___y_761_ = v___x_788_;
goto v___jp_760_;
}
}
else
{
lean_dec_ref(v_arg_749_);
v___y_761_ = v___x_788_;
goto v___jp_760_;
}
}
v___jp_760_:
{
if (lean_obj_tag(v___y_761_) == 0)
{
lean_object* v_a_762_; lean_object* v___x_764_; uint8_t v_isShared_765_; uint8_t v_isSharedCheck_777_; 
v_a_762_ = lean_ctor_get(v___y_761_, 0);
v_isSharedCheck_777_ = !lean_is_exclusive(v___y_761_);
if (v_isSharedCheck_777_ == 0)
{
v___x_764_ = v___y_761_;
v_isShared_765_ = v_isSharedCheck_777_;
goto v_resetjp_763_;
}
else
{
lean_inc(v_a_762_);
lean_dec(v___y_761_);
v___x_764_ = lean_box(0);
v_isShared_765_ = v_isSharedCheck_777_;
goto v_resetjp_763_;
}
v_resetjp_763_:
{
uint8_t v___x_766_; 
v___x_766_ = lean_unbox(v_a_762_);
lean_dec(v_a_762_);
if (v___x_766_ == 0)
{
lean_object* v___x_767_; lean_object* v___x_768_; 
lean_inc_ref(v_body_731_);
lean_del_object(v___x_764_);
lean_dec_ref_known(v_snd_726_, 3);
lean_del_object(v___x_728_);
v___x_767_ = lean_box(0);
v___x_768_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___lam__0(v___x_732_, v_body_731_, v___x_767_, v___y_694_, v___y_695_, v___y_696_, v___y_697_, v___y_698_, v___y_699_, v___y_700_, v___y_701_, v___y_702_, v___y_703_);
v___y_706_ = v___x_768_;
goto v___jp_705_;
}
else
{
lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_772_; 
v___x_769_ = lean_box(v___x_759_);
v___x_770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_770_, 0, v___x_769_);
if (v_isShared_729_ == 0)
{
lean_ctor_set(v___x_728_, 0, v___x_770_);
v___x_772_ = v___x_728_;
goto v_reusejp_771_;
}
else
{
lean_object* v_reuseFailAlloc_776_; 
v_reuseFailAlloc_776_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_776_, 0, v___x_770_);
lean_ctor_set(v_reuseFailAlloc_776_, 1, v_snd_726_);
v___x_772_ = v_reuseFailAlloc_776_;
goto v_reusejp_771_;
}
v_reusejp_771_:
{
lean_object* v___x_774_; 
if (v_isShared_765_ == 0)
{
lean_ctor_set(v___x_764_, 0, v___x_772_);
v___x_774_ = v___x_764_;
goto v_reusejp_773_;
}
else
{
lean_object* v_reuseFailAlloc_775_; 
v_reuseFailAlloc_775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_775_, 0, v___x_772_);
v___x_774_ = v_reuseFailAlloc_775_;
goto v_reusejp_773_;
}
v_reusejp_773_:
{
return v___x_774_;
}
}
}
}
}
else
{
lean_object* v_a_778_; lean_object* v___x_780_; uint8_t v_isShared_781_; uint8_t v_isSharedCheck_785_; 
lean_dec_ref_known(v_snd_726_, 3);
lean_del_object(v___x_728_);
v_a_778_ = lean_ctor_get(v___y_761_, 0);
v_isSharedCheck_785_ = !lean_is_exclusive(v___y_761_);
if (v_isSharedCheck_785_ == 0)
{
v___x_780_ = v___y_761_;
v_isShared_781_ = v_isSharedCheck_785_;
goto v_resetjp_779_;
}
else
{
lean_inc(v_a_778_);
lean_dec(v___y_761_);
v___x_780_ = lean_box(0);
v_isShared_781_ = v_isSharedCheck_785_;
goto v_resetjp_779_;
}
v_resetjp_779_:
{
lean_object* v___x_783_; 
if (v_isShared_781_ == 0)
{
v___x_783_ = v___x_780_;
goto v_reusejp_782_;
}
else
{
lean_object* v_reuseFailAlloc_784_; 
v_reuseFailAlloc_784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_784_, 0, v_a_778_);
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
}
else
{
lean_object* v___x_792_; 
lean_dec_ref(v___x_750_);
lean_dec_ref(v_arg_749_);
lean_dec_ref(v___f_733_);
v___x_792_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkChild___redArg(v_e_692_, v_arg_744_, v___y_694_);
lean_dec_ref(v_arg_744_);
if (lean_obj_tag(v___x_792_) == 0)
{
lean_object* v_a_793_; lean_object* v___x_795_; uint8_t v_isShared_796_; uint8_t v_isSharedCheck_808_; 
v_a_793_ = lean_ctor_get(v___x_792_, 0);
v_isSharedCheck_808_ = !lean_is_exclusive(v___x_792_);
if (v_isSharedCheck_808_ == 0)
{
v___x_795_ = v___x_792_;
v_isShared_796_ = v_isSharedCheck_808_;
goto v_resetjp_794_;
}
else
{
lean_inc(v_a_793_);
lean_dec(v___x_792_);
v___x_795_ = lean_box(0);
v_isShared_796_ = v_isSharedCheck_808_;
goto v_resetjp_794_;
}
v_resetjp_794_:
{
uint8_t v___x_797_; 
v___x_797_ = lean_unbox(v_a_793_);
lean_dec(v_a_793_);
if (v___x_797_ == 0)
{
lean_object* v___x_798_; lean_object* v___x_799_; 
lean_inc_ref(v_body_731_);
lean_del_object(v___x_795_);
lean_dec_ref_known(v_snd_726_, 3);
lean_del_object(v___x_728_);
v___x_798_ = lean_box(0);
v___x_799_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___lam__0(v___x_732_, v_body_731_, v___x_798_, v___y_694_, v___y_695_, v___y_696_, v___y_697_, v___y_698_, v___y_699_, v___y_700_, v___y_701_, v___y_702_, v___y_703_);
v___y_706_ = v___x_799_;
goto v___jp_705_;
}
else
{
lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_803_; 
v___x_800_ = lean_box(v___x_752_);
v___x_801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_801_, 0, v___x_800_);
if (v_isShared_729_ == 0)
{
lean_ctor_set(v___x_728_, 0, v___x_801_);
v___x_803_ = v___x_728_;
goto v_reusejp_802_;
}
else
{
lean_object* v_reuseFailAlloc_807_; 
v_reuseFailAlloc_807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_807_, 0, v___x_801_);
lean_ctor_set(v_reuseFailAlloc_807_, 1, v_snd_726_);
v___x_803_ = v_reuseFailAlloc_807_;
goto v_reusejp_802_;
}
v_reusejp_802_:
{
lean_object* v___x_805_; 
if (v_isShared_796_ == 0)
{
lean_ctor_set(v___x_795_, 0, v___x_803_);
v___x_805_ = v___x_795_;
goto v_reusejp_804_;
}
else
{
lean_object* v_reuseFailAlloc_806_; 
v_reuseFailAlloc_806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_806_, 0, v___x_803_);
v___x_805_ = v_reuseFailAlloc_806_;
goto v_reusejp_804_;
}
v_reusejp_804_:
{
return v___x_805_;
}
}
}
}
}
else
{
lean_object* v_a_809_; lean_object* v___x_811_; uint8_t v_isShared_812_; uint8_t v_isSharedCheck_816_; 
lean_dec_ref_known(v_snd_726_, 3);
lean_del_object(v___x_728_);
v_a_809_ = lean_ctor_get(v___x_792_, 0);
v_isSharedCheck_816_ = !lean_is_exclusive(v___x_792_);
if (v_isSharedCheck_816_ == 0)
{
v___x_811_ = v___x_792_;
v_isShared_812_ = v_isSharedCheck_816_;
goto v_resetjp_810_;
}
else
{
lean_inc(v_a_809_);
lean_dec(v___x_792_);
v___x_811_ = lean_box(0);
v_isShared_812_ = v_isSharedCheck_816_;
goto v_resetjp_810_;
}
v_resetjp_810_:
{
lean_object* v___x_814_; 
if (v_isShared_812_ == 0)
{
v___x_814_ = v___x_811_;
goto v_reusejp_813_;
}
else
{
lean_object* v_reuseFailAlloc_815_; 
v_reuseFailAlloc_815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_815_, 0, v_a_809_);
v___x_814_ = v_reuseFailAlloc_815_;
goto v_reusejp_813_;
}
v_reusejp_813_:
{
return v___x_814_;
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
lean_object* v_a_817_; lean_object* v___x_819_; uint8_t v_isShared_820_; uint8_t v_isSharedCheck_824_; 
lean_dec_ref(v___f_733_);
lean_dec_ref_known(v_snd_726_, 3);
lean_del_object(v___x_728_);
v_a_817_ = lean_ctor_get(v___x_734_, 0);
v_isSharedCheck_824_ = !lean_is_exclusive(v___x_734_);
if (v_isSharedCheck_824_ == 0)
{
v___x_819_ = v___x_734_;
v_isShared_820_ = v_isSharedCheck_824_;
goto v_resetjp_818_;
}
else
{
lean_inc(v_a_817_);
lean_dec(v___x_734_);
v___x_819_ = lean_box(0);
v_isShared_820_ = v_isSharedCheck_824_;
goto v_resetjp_818_;
}
v_resetjp_818_:
{
lean_object* v___x_822_; 
if (v_isShared_820_ == 0)
{
v___x_822_ = v___x_819_;
goto v_reusejp_821_;
}
else
{
lean_object* v_reuseFailAlloc_823_; 
v_reuseFailAlloc_823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_823_, 0, v_a_817_);
v___x_822_ = v_reuseFailAlloc_823_;
goto v_reusejp_821_;
}
v_reusejp_821_:
{
return v___x_822_;
}
}
}
}
else
{
lean_object* v___x_825_; lean_object* v___x_827_; 
v___x_825_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___closed__4));
if (v_isShared_729_ == 0)
{
lean_ctor_set(v___x_728_, 0, v___x_825_);
v___x_827_ = v___x_728_;
goto v_reusejp_826_;
}
else
{
lean_object* v_reuseFailAlloc_829_; 
v_reuseFailAlloc_829_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_829_, 0, v___x_825_);
lean_ctor_set(v_reuseFailAlloc_829_, 1, v_snd_726_);
v___x_827_ = v_reuseFailAlloc_829_;
goto v_reusejp_826_;
}
v_reusejp_826_:
{
lean_object* v___x_828_; 
v___x_828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_828_, 0, v___x_827_);
return v___x_828_;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_692_ = stack[0].m_obj;
lean_object* v_a_693_ = stack[1].m_obj;
lean_object* v___y_694_ = stack[2].m_obj;
lean_object* v___y_695_ = stack[3].m_obj;
lean_object* v___y_696_ = stack[4].m_obj;
lean_object* v___y_697_ = stack[5].m_obj;
lean_object* v___y_698_ = stack[6].m_obj;
lean_object* v___y_699_ = stack[7].m_obj;
lean_object* v___y_700_ = stack[8].m_obj;
lean_object* v___y_701_ = stack[9].m_obj;
lean_object* v___y_702_ = stack[10].m_obj;
lean_object* v___y_703_ = stack[11].m_obj;
lean_object* v_res_832_;
v_res_832_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg(v_e_692_, v_a_693_, v___y_694_, v___y_695_, v___y_696_, v___y_697_, v___y_698_, v___y_699_, v___y_700_, v___y_701_, v___y_702_, v___y_703_);
stack->m_obj
 = v_res_832_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___boxed(lean_object* v_e_833_, lean_object* v_a_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_){
_start:
{
lean_object* v_res_846_; 
v_res_846_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg(v_e_833_, v_a_834_, v___y_835_, v___y_836_, v___y_837_, v___y_838_, v___y_839_, v___y_840_, v___y_841_, v___y_842_, v___y_843_, v___y_844_);
lean_dec(v___y_844_);
lean_dec_ref(v___y_843_);
lean_dec(v___y_842_);
lean_dec_ref(v___y_841_);
lean_dec(v___y_840_);
lean_dec_ref(v___y_839_);
lean_dec(v___y_838_);
lean_dec_ref(v___y_837_);
lean_dec(v___y_836_);
lean_dec(v___y_835_);
lean_dec_ref(v_e_833_);
return v_res_846_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent(lean_object* v_e_854_, lean_object* v_parent_855_, lean_object* v_a_856_, lean_object* v_a_857_, lean_object* v_a_858_, lean_object* v_a_859_, lean_object* v_a_860_, lean_object* v_a_861_, lean_object* v_a_862_, lean_object* v_a_863_, lean_object* v_a_864_, lean_object* v_a_865_){
_start:
{
lean_object* v___x_871_; 
v___x_871_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_parent_855_, v_a_863_);
if (lean_obj_tag(v___x_871_) == 0)
{
lean_object* v_a_872_; lean_object* v___x_873_; uint8_t v___x_874_; 
v_a_872_ = lean_ctor_get(v___x_871_, 0);
lean_inc(v_a_872_);
lean_dec_ref_known(v___x_871_, 1);
v___x_873_ = l_Lean_Expr_cleanupAnnotations(v_a_872_);
v___x_874_ = l_Lean_Expr_isApp(v___x_873_);
if (v___x_874_ == 0)
{
lean_dec_ref(v___x_873_);
goto v___jp_867_;
}
else
{
lean_object* v_arg_875_; lean_object* v___x_876_; lean_object* v___x_877_; uint8_t v___x_878_; 
v_arg_875_ = lean_ctor_get(v___x_873_, 1);
lean_inc_ref(v_arg_875_);
v___x_876_ = l_Lean_Expr_appFnCleanup___redArg(v___x_873_);
v___x_877_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent___closed__3));
v___x_878_ = l_Lean_Expr_isConstOf(v___x_876_, v___x_877_);
lean_dec_ref(v___x_876_);
if (v___x_878_ == 0)
{
lean_dec_ref(v_arg_875_);
goto v___jp_867_;
}
else
{
lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; 
v___x_879_ = lean_box(0);
v___x_880_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_880_, 0, v___x_879_);
lean_ctor_set(v___x_880_, 1, v_arg_875_);
v___x_881_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg(v_e_854_, v___x_880_, v_a_856_, v_a_857_, v_a_858_, v_a_859_, v_a_860_, v_a_861_, v_a_862_, v_a_863_, v_a_864_, v_a_865_);
if (lean_obj_tag(v___x_881_) == 0)
{
lean_object* v_a_882_; lean_object* v___x_884_; uint8_t v_isShared_885_; uint8_t v_isSharedCheck_896_; 
v_a_882_ = lean_ctor_get(v___x_881_, 0);
v_isSharedCheck_896_ = !lean_is_exclusive(v___x_881_);
if (v_isSharedCheck_896_ == 0)
{
v___x_884_ = v___x_881_;
v_isShared_885_ = v_isSharedCheck_896_;
goto v_resetjp_883_;
}
else
{
lean_inc(v_a_882_);
lean_dec(v___x_881_);
v___x_884_ = lean_box(0);
v_isShared_885_ = v_isSharedCheck_896_;
goto v_resetjp_883_;
}
v_resetjp_883_:
{
lean_object* v_fst_886_; 
v_fst_886_ = lean_ctor_get(v_a_882_, 0);
lean_inc(v_fst_886_);
lean_dec(v_a_882_);
if (lean_obj_tag(v_fst_886_) == 0)
{
uint8_t v___x_887_; lean_object* v___x_888_; lean_object* v___x_890_; 
v___x_887_ = 0;
v___x_888_ = lean_box(v___x_887_);
if (v_isShared_885_ == 0)
{
lean_ctor_set(v___x_884_, 0, v___x_888_);
v___x_890_ = v___x_884_;
goto v_reusejp_889_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v___x_888_);
v___x_890_ = v_reuseFailAlloc_891_;
goto v_reusejp_889_;
}
v_reusejp_889_:
{
return v___x_890_;
}
}
else
{
lean_object* v_val_892_; lean_object* v___x_894_; 
v_val_892_ = lean_ctor_get(v_fst_886_, 0);
lean_inc(v_val_892_);
lean_dec_ref_known(v_fst_886_, 1);
if (v_isShared_885_ == 0)
{
lean_ctor_set(v___x_884_, 0, v_val_892_);
v___x_894_ = v___x_884_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_895_; 
v_reuseFailAlloc_895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_895_, 0, v_val_892_);
v___x_894_ = v_reuseFailAlloc_895_;
goto v_reusejp_893_;
}
v_reusejp_893_:
{
return v___x_894_;
}
}
}
}
else
{
lean_object* v_a_897_; lean_object* v___x_899_; uint8_t v_isShared_900_; uint8_t v_isSharedCheck_904_; 
v_a_897_ = lean_ctor_get(v___x_881_, 0);
v_isSharedCheck_904_ = !lean_is_exclusive(v___x_881_);
if (v_isSharedCheck_904_ == 0)
{
v___x_899_ = v___x_881_;
v_isShared_900_ = v_isSharedCheck_904_;
goto v_resetjp_898_;
}
else
{
lean_inc(v_a_897_);
lean_dec(v___x_881_);
v___x_899_ = lean_box(0);
v_isShared_900_ = v_isSharedCheck_904_;
goto v_resetjp_898_;
}
v_resetjp_898_:
{
lean_object* v___x_902_; 
if (v_isShared_900_ == 0)
{
v___x_902_ = v___x_899_;
goto v_reusejp_901_;
}
else
{
lean_object* v_reuseFailAlloc_903_; 
v_reuseFailAlloc_903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_903_, 0, v_a_897_);
v___x_902_ = v_reuseFailAlloc_903_;
goto v_reusejp_901_;
}
v_reusejp_901_:
{
return v___x_902_;
}
}
}
}
}
}
else
{
lean_object* v_a_905_; lean_object* v___x_907_; uint8_t v_isShared_908_; uint8_t v_isSharedCheck_912_; 
v_a_905_ = lean_ctor_get(v___x_871_, 0);
v_isSharedCheck_912_ = !lean_is_exclusive(v___x_871_);
if (v_isSharedCheck_912_ == 0)
{
v___x_907_ = v___x_871_;
v_isShared_908_ = v_isSharedCheck_912_;
goto v_resetjp_906_;
}
else
{
lean_inc(v_a_905_);
lean_dec(v___x_871_);
v___x_907_ = lean_box(0);
v_isShared_908_ = v_isSharedCheck_912_;
goto v_resetjp_906_;
}
v_resetjp_906_:
{
lean_object* v___x_910_; 
if (v_isShared_908_ == 0)
{
v___x_910_ = v___x_907_;
goto v_reusejp_909_;
}
else
{
lean_object* v_reuseFailAlloc_911_; 
v_reuseFailAlloc_911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_911_, 0, v_a_905_);
v___x_910_ = v_reuseFailAlloc_911_;
goto v_reusejp_909_;
}
v_reusejp_909_:
{
return v___x_910_;
}
}
}
v___jp_867_:
{
uint8_t v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; 
v___x_868_ = 0;
v___x_869_ = lean_box(v___x_868_);
v___x_870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_870_, 0, v___x_869_);
return v___x_870_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_854_ = stack[0].m_obj;
lean_object* v_parent_855_ = stack[1].m_obj;
lean_object* v_a_856_ = stack[2].m_obj;
lean_object* v_a_857_ = stack[3].m_obj;
lean_object* v_a_858_ = stack[4].m_obj;
lean_object* v_a_859_ = stack[5].m_obj;
lean_object* v_a_860_ = stack[6].m_obj;
lean_object* v_a_861_ = stack[7].m_obj;
lean_object* v_a_862_ = stack[8].m_obj;
lean_object* v_a_863_ = stack[9].m_obj;
lean_object* v_a_864_ = stack[10].m_obj;
lean_object* v_a_865_ = stack[11].m_obj;
lean_object* v_res_913_;
v_res_913_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent(v_e_854_, v_parent_855_, v_a_856_, v_a_857_, v_a_858_, v_a_859_, v_a_860_, v_a_861_, v_a_862_, v_a_863_, v_a_864_, v_a_865_);
stack->m_obj
 = v_res_913_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent___boxed(lean_object* v_e_914_, lean_object* v_parent_915_, lean_object* v_a_916_, lean_object* v_a_917_, lean_object* v_a_918_, lean_object* v_a_919_, lean_object* v_a_920_, lean_object* v_a_921_, lean_object* v_a_922_, lean_object* v_a_923_, lean_object* v_a_924_, lean_object* v_a_925_, lean_object* v_a_926_){
_start:
{
lean_object* v_res_927_; 
v_res_927_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent(v_e_914_, v_parent_915_, v_a_916_, v_a_917_, v_a_918_, v_a_919_, v_a_920_, v_a_921_, v_a_922_, v_a_923_, v_a_924_, v_a_925_);
lean_dec(v_a_925_);
lean_dec_ref(v_a_924_);
lean_dec(v_a_923_);
lean_dec_ref(v_a_922_);
lean_dec(v_a_921_);
lean_dec_ref(v_a_920_);
lean_dec(v_a_919_);
lean_dec_ref(v_a_918_);
lean_dec(v_a_917_);
lean_dec(v_a_916_);
lean_dec_ref(v_e_914_);
return v_res_927_;
}
}
lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0(lean_object* v_e_928_, lean_object* v_inst_929_, lean_object* v_a_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_){
_start:
{
lean_object* v___x_942_; 
v___x_942_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg(v_e_928_, v_a_930_, v___y_931_, v___y_932_, v___y_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_, v___y_938_, v___y_939_, v___y_940_);
return v___x_942_;
}
}
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_928_ = stack[0].m_obj;
lean_object* v_a_930_ = stack[2].m_obj;
lean_object* v___y_931_ = stack[3].m_obj;
lean_object* v___y_932_ = stack[4].m_obj;
lean_object* v___y_933_ = stack[5].m_obj;
lean_object* v___y_934_ = stack[6].m_obj;
lean_object* v___y_935_ = stack[7].m_obj;
lean_object* v___y_936_ = stack[8].m_obj;
lean_object* v___y_937_ = stack[9].m_obj;
lean_object* v___y_938_ = stack[10].m_obj;
lean_object* v___y_939_ = stack[11].m_obj;
lean_object* v___y_940_ = stack[12].m_obj;
lean_object* v_res_943_;
v_res_943_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0(v_e_928_, lean_box(0), v_a_930_, v___y_931_, v___y_932_, v___y_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_, v___y_938_, v___y_939_, v___y_940_);
stack->m_obj
 = v_res_943_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___boxed(lean_object* v_e_944_, lean_object* v_inst_945_, lean_object* v_a_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_){
_start:
{
lean_object* v_res_958_; 
v_res_958_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0(v_e_944_, v_inst_945_, v_a_946_, v___y_947_, v___y_948_, v___y_949_, v___y_950_, v___y_951_, v___y_952_, v___y_953_, v___y_954_, v___y_955_, v___y_956_);
lean_dec(v___y_956_);
lean_dec_ref(v___y_955_);
lean_dec(v___y_954_);
lean_dec_ref(v___y_953_);
lean_dec(v___y_952_);
lean_dec_ref(v___y_951_);
lean_dec(v___y_950_);
lean_dec_ref(v___y_949_);
lean_dec(v___y_948_);
lean_dec(v___y_947_);
lean_dec_ref(v_e_944_);
return v_res_958_;
}
}
lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__0(lean_object* v_msg_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_){
_start:
{
lean_object* v___x_971_; lean_object* v___x_31894__overap_972_; lean_object* v___x_973_; 
v___x_971_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__1___closed__0, &l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__1___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__1___closed__0);
v___x_31894__overap_972_ = lean_panic_fn_borrowed(v___x_971_, v_msg_959_);
lean_inc(v___y_969_);
lean_inc_ref(v___y_968_);
lean_inc(v___y_967_);
lean_inc_ref(v___y_966_);
lean_inc(v___y_965_);
lean_inc_ref(v___y_964_);
lean_inc(v___y_963_);
lean_inc_ref(v___y_962_);
lean_inc(v___y_961_);
lean_inc(v___y_960_);
v___x_973_ = lean_apply_11(v___x_31894__overap_972_, v___y_960_, v___y_961_, v___y_962_, v___y_963_, v___y_964_, v___y_965_, v___y_966_, v___y_967_, v___y_968_, v___y_969_, lean_box(0));
return v___x_973_;
}
}
LEAN_EXPORT void l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_959_ = stack[0].m_obj;
lean_object* v___y_960_ = stack[1].m_obj;
lean_object* v___y_961_ = stack[2].m_obj;
lean_object* v___y_962_ = stack[3].m_obj;
lean_object* v___y_963_ = stack[4].m_obj;
lean_object* v___y_964_ = stack[5].m_obj;
lean_object* v___y_965_ = stack[6].m_obj;
lean_object* v___y_966_ = stack[7].m_obj;
lean_object* v___y_967_ = stack[8].m_obj;
lean_object* v___y_968_ = stack[9].m_obj;
lean_object* v___y_969_ = stack[10].m_obj;
lean_object* v_res_974_;
v_res_974_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__0(v_msg_959_, v___y_960_, v___y_961_, v___y_962_, v___y_963_, v___y_964_, v___y_965_, v___y_966_, v___y_967_, v___y_968_, v___y_969_);
stack->m_obj
 = v_res_974_;
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__0___boxed(lean_object* v_msg_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_){
_start:
{
lean_object* v_res_987_; 
v_res_987_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__0(v_msg_975_, v___y_976_, v___y_977_, v___y_978_, v___y_979_, v___y_980_, v___y_981_, v___y_982_, v___y_983_, v___y_984_, v___y_985_);
lean_dec(v___y_985_);
lean_dec_ref(v___y_984_);
lean_dec(v___y_983_);
lean_dec_ref(v___y_982_);
lean_dec(v___y_981_);
lean_dec_ref(v___y_980_);
lean_dec(v___y_979_);
lean_dec_ref(v___y_978_);
lean_dec(v___y_977_);
lean_dec(v___y_976_);
return v_res_987_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__1_spec__1(lean_object* v_msgData_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_){
_start:
{
lean_object* v___x_994_; lean_object* v_env_995_; uint8_t v___x_996_; lean_object* v_env_997_; lean_object* v___x_998_; lean_object* v_toCold_999_; lean_object* v_mctx_1000_; lean_object* v_lctx_1001_; lean_object* v_options_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; 
v___x_994_ = lean_st_ref_get(v___y_992_);
v_env_995_ = lean_ctor_get(v___x_994_, 0);
lean_inc_ref(v_env_995_);
lean_dec(v___x_994_);
v___x_996_ = 0;
v_env_997_ = l_Lean_Environment_setRecordingDeps(v_env_995_, v___x_996_);
v___x_998_ = lean_st_ref_get(v___y_990_);
v_toCold_999_ = lean_ctor_get(v___y_991_, 0);
v_mctx_1000_ = lean_ctor_get(v___x_998_, 0);
lean_inc_ref(v_mctx_1000_);
lean_dec(v___x_998_);
v_lctx_1001_ = lean_ctor_get(v___y_989_, 2);
v_options_1002_ = lean_ctor_get(v_toCold_999_, 2);
lean_inc_ref(v_options_1002_);
lean_inc_ref(v_lctx_1001_);
v___x_1003_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1003_, 0, v_env_997_);
lean_ctor_set(v___x_1003_, 1, v_mctx_1000_);
lean_ctor_set(v___x_1003_, 2, v_lctx_1001_);
lean_ctor_set(v___x_1003_, 3, v_options_1002_);
v___x_1004_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1004_, 0, v___x_1003_);
lean_ctor_set(v___x_1004_, 1, v_msgData_988_);
v___x_1005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1005_, 0, v___x_1004_);
return v___x_1005_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_988_ = stack[0].m_obj;
lean_object* v___y_989_ = stack[1].m_obj;
lean_object* v___y_990_ = stack[2].m_obj;
lean_object* v___y_991_ = stack[3].m_obj;
lean_object* v___y_992_ = stack[4].m_obj;
lean_object* v_res_1006_;
v_res_1006_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__1_spec__1(v_msgData_988_, v___y_989_, v___y_990_, v___y_991_, v___y_992_);
stack->m_obj
 = v_res_1006_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__1_spec__1___boxed(lean_object* v_msgData_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_){
_start:
{
lean_object* v_res_1013_; 
v_res_1013_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__1_spec__1(v_msgData_1007_, v___y_1008_, v___y_1009_, v___y_1010_, v___y_1011_);
lean_dec(v___y_1011_);
lean_dec_ref(v___y_1010_);
lean_dec(v___y_1009_);
lean_dec_ref(v___y_1008_);
return v_res_1013_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__1___redArg(lean_object* v_msg_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_){
_start:
{
lean_object* v_ref_1020_; lean_object* v___x_1021_; lean_object* v_a_1022_; lean_object* v___x_1024_; uint8_t v_isShared_1025_; uint8_t v_isSharedCheck_1030_; 
v_ref_1020_ = lean_ctor_get(v___y_1017_, 2);
v___x_1021_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__1_spec__1(v_msg_1014_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_);
v_a_1022_ = lean_ctor_get(v___x_1021_, 0);
v_isSharedCheck_1030_ = !lean_is_exclusive(v___x_1021_);
if (v_isSharedCheck_1030_ == 0)
{
v___x_1024_ = v___x_1021_;
v_isShared_1025_ = v_isSharedCheck_1030_;
goto v_resetjp_1023_;
}
else
{
lean_inc(v_a_1022_);
lean_dec(v___x_1021_);
v___x_1024_ = lean_box(0);
v_isShared_1025_ = v_isSharedCheck_1030_;
goto v_resetjp_1023_;
}
v_resetjp_1023_:
{
lean_object* v___x_1026_; lean_object* v___x_1028_; 
lean_inc(v_ref_1020_);
v___x_1026_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1026_, 0, v_ref_1020_);
lean_ctor_set(v___x_1026_, 1, v_a_1022_);
if (v_isShared_1025_ == 0)
{
lean_ctor_set_tag(v___x_1024_, 1);
lean_ctor_set(v___x_1024_, 0, v___x_1026_);
v___x_1028_ = v___x_1024_;
goto v_reusejp_1027_;
}
else
{
lean_object* v_reuseFailAlloc_1029_; 
v_reuseFailAlloc_1029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1029_, 0, v___x_1026_);
v___x_1028_ = v_reuseFailAlloc_1029_;
goto v_reusejp_1027_;
}
v_reusejp_1027_:
{
return v___x_1028_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1014_ = stack[0].m_obj;
lean_object* v___y_1015_ = stack[1].m_obj;
lean_object* v___y_1016_ = stack[2].m_obj;
lean_object* v___y_1017_ = stack[3].m_obj;
lean_object* v___y_1018_ = stack[4].m_obj;
lean_object* v_res_1031_;
v_res_1031_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__1___redArg(v_msg_1014_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_);
stack->m_obj
 = v_res_1031_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__1___redArg___boxed(lean_object* v_msg_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_){
_start:
{
lean_object* v_res_1038_; 
v_res_1038_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__1___redArg(v_msg_1032_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_);
lean_dec(v___y_1036_);
lean_dec_ref(v___y_1035_);
lean_dec(v___y_1034_);
lean_dec_ref(v___y_1033_);
return v_res_1038_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__2___redArg(lean_object* v_e_1039_, uint8_t v_a_1040_, lean_object* v_as_1041_, size_t v_sz_1042_, size_t v_i_1043_, uint8_t v_b_1044_, lean_object* v___y_1045_){
_start:
{
uint8_t v___x_1047_; 
v___x_1047_ = lean_usize_dec_lt(v_i_1043_, v_sz_1042_);
if (v___x_1047_ == 0)
{
lean_object* v___x_1048_; lean_object* v___x_1049_; 
v___x_1048_ = lean_box(v_b_1044_);
v___x_1049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1049_, 0, v___x_1048_);
return v___x_1049_;
}
else
{
lean_object* v_a_1050_; lean_object* v___x_1051_; 
v_a_1050_ = lean_array_uget_borrowed(v_as_1041_, v_i_1043_);
v___x_1051_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkChild___redArg(v_e_1039_, v_a_1050_, v___y_1045_);
if (lean_obj_tag(v___x_1051_) == 0)
{
lean_object* v_a_1052_; lean_object* v___x_1054_; uint8_t v_isShared_1055_; uint8_t v_isSharedCheck_1064_; 
v_a_1052_ = lean_ctor_get(v___x_1051_, 0);
v_isSharedCheck_1064_ = !lean_is_exclusive(v___x_1051_);
if (v_isSharedCheck_1064_ == 0)
{
v___x_1054_ = v___x_1051_;
v_isShared_1055_ = v_isSharedCheck_1064_;
goto v_resetjp_1053_;
}
else
{
lean_inc(v_a_1052_);
lean_dec(v___x_1051_);
v___x_1054_ = lean_box(0);
v_isShared_1055_ = v_isSharedCheck_1064_;
goto v_resetjp_1053_;
}
v_resetjp_1053_:
{
uint8_t v___x_1056_; 
v___x_1056_ = lean_unbox(v_a_1052_);
lean_dec(v_a_1052_);
if (v___x_1056_ == 0)
{
size_t v___x_1057_; size_t v___x_1058_; 
lean_del_object(v___x_1054_);
v___x_1057_ = ((size_t)1ULL);
v___x_1058_ = lean_usize_add(v_i_1043_, v___x_1057_);
v_i_1043_ = v___x_1058_;
goto _start;
}
else
{
lean_object* v___x_1060_; lean_object* v___x_1062_; 
v___x_1060_ = lean_box(v_a_1040_);
if (v_isShared_1055_ == 0)
{
lean_ctor_set(v___x_1054_, 0, v___x_1060_);
v___x_1062_ = v___x_1054_;
goto v_reusejp_1061_;
}
else
{
lean_object* v_reuseFailAlloc_1063_; 
v_reuseFailAlloc_1063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1063_, 0, v___x_1060_);
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
else
{
return v___x_1051_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1039_ = stack[0].m_obj;
uint8_t v_a_1040_ = stack[1].m_num;
lean_object* v_as_1041_ = stack[2].m_obj;
size_t v_sz_1042_ = stack[3].m_num;
size_t v_i_1043_ = stack[4].m_num;
uint8_t v_b_1044_ = stack[5].m_num;
lean_object* v___y_1045_ = stack[6].m_obj;
lean_object* v_res_1065_;
v_res_1065_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__2___redArg(v_e_1039_, v_a_1040_, v_as_1041_, v_sz_1042_, v_i_1043_, v_b_1044_, v___y_1045_);
stack->m_obj
 = v_res_1065_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__2___redArg___boxed(lean_object* v_e_1066_, lean_object* v_a_1067_, lean_object* v_as_1068_, lean_object* v_sz_1069_, lean_object* v_i_1070_, lean_object* v_b_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_){
_start:
{
uint8_t v_a_38316__boxed_1074_; size_t v_sz_boxed_1075_; size_t v_i_boxed_1076_; uint8_t v_b_boxed_1077_; lean_object* v_res_1078_; 
v_a_38316__boxed_1074_ = lean_unbox(v_a_1067_);
v_sz_boxed_1075_ = lean_unbox_usize(v_sz_1069_);
lean_dec(v_sz_1069_);
v_i_boxed_1076_ = lean_unbox_usize(v_i_1070_);
lean_dec(v_i_1070_);
v_b_boxed_1077_ = lean_unbox(v_b_1071_);
v_res_1078_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__2___redArg(v_e_1066_, v_a_38316__boxed_1074_, v_as_1068_, v_sz_boxed_1075_, v_i_boxed_1076_, v_b_boxed_1077_, v___y_1072_);
lean_dec(v___y_1072_);
lean_dec_ref(v_as_1068_);
lean_dec_ref(v_e_1066_);
return v_res_1078_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__2(void){
_start:
{
lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; 
v___x_1081_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__1));
v___x_1082_ = lean_unsigned_to_nat(10u);
v___x_1083_ = lean_unsigned_to_nat(94u);
v___x_1084_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__0));
v___x_1085_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__0));
v___x_1086_ = l_mkPanicMessageWithDecl(v___x_1085_, v___x_1084_, v___x_1083_, v___x_1082_, v___x_1081_);
return v___x_1086_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__4(void){
_start:
{
lean_object* v___x_1088_; lean_object* v___x_1089_; 
v___x_1088_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__3));
v___x_1089_ = l_Lean_stringToMessageData(v___x_1088_);
return v___x_1089_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__6(void){
_start:
{
lean_object* v___x_1091_; lean_object* v___x_1092_; 
v___x_1091_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__5));
v___x_1092_ = l_Lean_stringToMessageData(v___x_1091_);
return v___x_1092_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__8(void){
_start:
{
lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; 
v___x_1094_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__7));
v___x_1095_ = lean_unsigned_to_nat(8u);
v___x_1096_ = lean_unsigned_to_nat(76u);
v___x_1097_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__0));
v___x_1098_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__0));
v___x_1099_ = l_mkPanicMessageWithDecl(v___x_1098_, v___x_1097_, v___x_1096_, v___x_1095_, v___x_1094_);
return v___x_1099_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__9(void){
_start:
{
lean_object* v___x_1100_; lean_object* v_dummy_1101_; 
v___x_1100_ = lean_box(0);
v_dummy_1101_ = l_Lean_Expr_sort___override(v___x_1100_);
return v_dummy_1101_;
}
}
lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg(lean_object* v_e_1102_, uint8_t v_a_1103_, lean_object* v_as_x27_1104_, lean_object* v_b_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_){
_start:
{
if (lean_obj_tag(v_as_x27_1104_) == 0)
{
lean_object* v___x_1117_; 
lean_dec_ref(v_e_1102_);
v___x_1117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1117_, 0, v_b_1105_);
return v___x_1117_;
}
else
{
lean_object* v_head_1118_; lean_object* v_tail_1119_; lean_object* v___y_1121_; lean_object* v___x_1141_; lean_object* v___y_1143_; lean_object* v___y_1144_; lean_object* v___y_1145_; lean_object* v___y_1146_; lean_object* v___y_1147_; lean_object* v___y_1148_; lean_object* v___y_1149_; lean_object* v___y_1150_; lean_object* v___y_1151_; lean_object* v___y_1152_; lean_object* v___y_1153_; uint8_t v_found_1161_; lean_object* v___y_1162_; lean_object* v___y_1163_; lean_object* v___y_1164_; lean_object* v___y_1165_; lean_object* v___y_1166_; lean_object* v___y_1167_; lean_object* v___y_1168_; lean_object* v___y_1169_; lean_object* v___y_1170_; lean_object* v___y_1171_; lean_object* v___y_1186_; uint8_t v_found_1187_; lean_object* v___y_1188_; lean_object* v___y_1189_; lean_object* v___y_1190_; lean_object* v___y_1191_; lean_object* v___y_1192_; lean_object* v___y_1193_; lean_object* v___y_1194_; lean_object* v___y_1195_; lean_object* v___y_1196_; lean_object* v___y_1197_; lean_object* v___y_1204_; lean_object* v___y_1205_; lean_object* v___y_1206_; lean_object* v___y_1207_; lean_object* v___y_1208_; lean_object* v___y_1209_; lean_object* v___y_1210_; lean_object* v___y_1211_; lean_object* v___y_1212_; lean_object* v___y_1213_; lean_object* v___x_1228_; 
v_head_1118_ = lean_ctor_get(v_as_x27_1104_, 0);
v_tail_1119_ = lean_ctor_get(v_as_x27_1104_, 1);
v___x_1141_ = lean_box(0);
lean_inc(v_head_1118_);
v___x_1228_ = l_Lean_Meta_Grind_useFunCC___redArg(v_head_1118_, v___y_1106_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_);
if (lean_obj_tag(v___x_1228_) == 0)
{
lean_object* v_a_1229_; uint8_t v___y_1231_; uint8_t v___x_1279_; 
v_a_1229_ = lean_ctor_get(v___x_1228_, 0);
lean_inc(v_a_1229_);
lean_dec_ref_known(v___x_1228_, 1);
v___x_1279_ = l_Lean_Expr_isApp(v_head_1118_);
if (v___x_1279_ == 0)
{
lean_dec(v_a_1229_);
v___y_1231_ = v___x_1279_;
goto v___jp_1230_;
}
else
{
uint8_t v___x_1280_; 
v___x_1280_ = lean_unbox(v_a_1229_);
lean_dec(v_a_1229_);
v___y_1231_ = v___x_1280_;
goto v___jp_1230_;
}
v___jp_1230_:
{
if (v___y_1231_ == 0)
{
uint8_t v___x_1232_; 
v___x_1232_ = l_Lean_Meta_Grind_isMatchCond(v_head_1118_);
if (v___x_1232_ == 0)
{
lean_object* v_dummy_1233_; lean_object* v_nargs_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; size_t v_sz_1239_; size_t v___x_1240_; lean_object* v___x_1241_; 
v_dummy_1233_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__9, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__9_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__9);
v_nargs_1234_ = l_Lean_Expr_getAppNumArgs(v_head_1118_);
lean_inc(v_nargs_1234_);
v___x_1235_ = lean_mk_array(v_nargs_1234_, v_dummy_1233_);
v___x_1236_ = lean_unsigned_to_nat(1u);
v___x_1237_ = lean_nat_sub(v_nargs_1234_, v___x_1236_);
lean_dec(v_nargs_1234_);
lean_inc(v_head_1118_);
v___x_1238_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_head_1118_, v___x_1235_, v___x_1237_);
v_sz_1239_ = lean_array_size(v___x_1238_);
v___x_1240_ = ((size_t)0ULL);
v___x_1241_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__2___redArg(v_e_1102_, v_a_1103_, v___x_1238_, v_sz_1239_, v___x_1240_, v___x_1232_, v___y_1106_);
lean_dec_ref(v___x_1238_);
if (lean_obj_tag(v___x_1241_) == 0)
{
if (lean_obj_tag(v_head_1118_) == 7)
{
lean_object* v_a_1242_; lean_object* v_binderType_1243_; lean_object* v_body_1244_; lean_object* v___x_1245_; lean_object* v_a_1246_; uint8_t v___x_1247_; 
v_a_1242_ = lean_ctor_get(v___x_1241_, 0);
lean_inc(v_a_1242_);
lean_dec_ref_known(v___x_1241_, 1);
v_binderType_1243_ = lean_ctor_get(v_head_1118_, 1);
v_body_1244_ = lean_ctor_get(v_head_1118_, 2);
v___x_1245_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkChild___redArg(v_e_1102_, v_binderType_1243_, v___y_1106_);
v_a_1246_ = lean_ctor_get(v___x_1245_, 0);
lean_inc(v_a_1246_);
lean_dec_ref(v___x_1245_);
v___x_1247_ = lean_unbox(v_a_1246_);
lean_dec(v_a_1246_);
if (v___x_1247_ == 0)
{
uint8_t v___x_1248_; 
v___x_1248_ = lean_unbox(v_a_1242_);
lean_dec(v_a_1242_);
lean_inc_ref(v_body_1244_);
v___y_1186_ = v_body_1244_;
v_found_1187_ = v___x_1248_;
v___y_1188_ = v___y_1106_;
v___y_1189_ = v___y_1107_;
v___y_1190_ = v___y_1108_;
v___y_1191_ = v___y_1109_;
v___y_1192_ = v___y_1110_;
v___y_1193_ = v___y_1111_;
v___y_1194_ = v___y_1112_;
v___y_1195_ = v___y_1113_;
v___y_1196_ = v___y_1114_;
v___y_1197_ = v___y_1115_;
goto v___jp_1185_;
}
else
{
lean_dec(v_a_1242_);
lean_inc_ref(v_body_1244_);
v___y_1186_ = v_body_1244_;
v_found_1187_ = v_a_1103_;
v___y_1188_ = v___y_1106_;
v___y_1189_ = v___y_1107_;
v___y_1190_ = v___y_1108_;
v___y_1191_ = v___y_1109_;
v___y_1192_ = v___y_1110_;
v___y_1193_ = v___y_1111_;
v___y_1194_ = v___y_1112_;
v___y_1195_ = v___y_1113_;
v___y_1196_ = v___y_1114_;
v___y_1197_ = v___y_1115_;
goto v___jp_1185_;
}
}
else
{
lean_object* v_a_1249_; uint8_t v___x_1250_; 
v_a_1249_ = lean_ctor_get(v___x_1241_, 0);
lean_inc(v_a_1249_);
lean_dec_ref_known(v___x_1241_, 1);
v___x_1250_ = lean_unbox(v_a_1249_);
lean_dec(v_a_1249_);
v_found_1161_ = v___x_1250_;
v___y_1162_ = v___y_1106_;
v___y_1163_ = v___y_1107_;
v___y_1164_ = v___y_1108_;
v___y_1165_ = v___y_1109_;
v___y_1166_ = v___y_1110_;
v___y_1167_ = v___y_1111_;
v___y_1168_ = v___y_1112_;
v___y_1169_ = v___y_1113_;
v___y_1170_ = v___y_1114_;
v___y_1171_ = v___y_1115_;
goto v___jp_1160_;
}
}
else
{
lean_object* v_a_1251_; lean_object* v___x_1253_; uint8_t v_isShared_1254_; uint8_t v_isSharedCheck_1258_; 
lean_dec_ref(v_e_1102_);
v_a_1251_ = lean_ctor_get(v___x_1241_, 0);
v_isSharedCheck_1258_ = !lean_is_exclusive(v___x_1241_);
if (v_isSharedCheck_1258_ == 0)
{
v___x_1253_ = v___x_1241_;
v_isShared_1254_ = v_isSharedCheck_1258_;
goto v_resetjp_1252_;
}
else
{
lean_inc(v_a_1251_);
lean_dec(v___x_1241_);
v___x_1253_ = lean_box(0);
v_isShared_1254_ = v_isSharedCheck_1258_;
goto v_resetjp_1252_;
}
v_resetjp_1252_:
{
lean_object* v___x_1256_; 
if (v_isShared_1254_ == 0)
{
v___x_1256_ = v___x_1253_;
goto v_reusejp_1255_;
}
else
{
lean_object* v_reuseFailAlloc_1257_; 
v_reuseFailAlloc_1257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1257_, 0, v_a_1251_);
v___x_1256_ = v_reuseFailAlloc_1257_;
goto v_reusejp_1255_;
}
v_reusejp_1255_:
{
return v___x_1256_;
}
}
}
}
else
{
lean_object* v___x_1259_; 
lean_inc(v_head_1118_);
v___x_1259_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent(v_e_1102_, v_head_1118_, v___y_1106_, v___y_1107_, v___y_1108_, v___y_1109_, v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_);
if (lean_obj_tag(v___x_1259_) == 0)
{
lean_object* v_a_1260_; uint8_t v___x_1261_; 
v_a_1260_ = lean_ctor_get(v___x_1259_, 0);
lean_inc(v_a_1260_);
lean_dec_ref_known(v___x_1259_, 1);
v___x_1261_ = lean_unbox(v_a_1260_);
lean_dec(v_a_1260_);
if (v___x_1261_ == 0)
{
lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; 
v___x_1262_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__4, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__4);
v___x_1263_ = l_Lean_MessageData_ofExpr(v_e_1102_);
v___x_1264_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1264_, 0, v___x_1262_);
lean_ctor_set(v___x_1264_, 1, v___x_1263_);
v___x_1265_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__6, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__6_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__6);
v___x_1266_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1266_, 0, v___x_1264_);
lean_ctor_set(v___x_1266_, 1, v___x_1265_);
lean_inc(v_head_1118_);
v___x_1267_ = l_Lean_MessageData_ofExpr(v_head_1118_);
v___x_1268_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1268_, 0, v___x_1266_);
lean_ctor_set(v___x_1268_, 1, v___x_1267_);
v___x_1269_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__1___redArg(v___x_1268_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_);
return v___x_1269_;
}
else
{
v___y_1204_ = v___y_1106_;
v___y_1205_ = v___y_1107_;
v___y_1206_ = v___y_1108_;
v___y_1207_ = v___y_1109_;
v___y_1208_ = v___y_1110_;
v___y_1209_ = v___y_1111_;
v___y_1210_ = v___y_1112_;
v___y_1211_ = v___y_1113_;
v___y_1212_ = v___y_1114_;
v___y_1213_ = v___y_1115_;
goto v___jp_1203_;
}
}
else
{
lean_object* v_a_1270_; lean_object* v___x_1272_; uint8_t v_isShared_1273_; uint8_t v_isSharedCheck_1277_; 
lean_dec_ref(v_e_1102_);
v_a_1270_ = lean_ctor_get(v___x_1259_, 0);
v_isSharedCheck_1277_ = !lean_is_exclusive(v___x_1259_);
if (v_isSharedCheck_1277_ == 0)
{
v___x_1272_ = v___x_1259_;
v_isShared_1273_ = v_isSharedCheck_1277_;
goto v_resetjp_1271_;
}
else
{
lean_inc(v_a_1270_);
lean_dec(v___x_1259_);
v___x_1272_ = lean_box(0);
v_isShared_1273_ = v_isSharedCheck_1277_;
goto v_resetjp_1271_;
}
v_resetjp_1271_:
{
lean_object* v___x_1275_; 
if (v_isShared_1273_ == 0)
{
v___x_1275_ = v___x_1272_;
goto v_reusejp_1274_;
}
else
{
lean_object* v_reuseFailAlloc_1276_; 
v_reuseFailAlloc_1276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1276_, 0, v_a_1270_);
v___x_1275_ = v_reuseFailAlloc_1276_;
goto v_reusejp_1274_;
}
v_reusejp_1274_:
{
return v___x_1275_;
}
}
}
}
}
else
{
v_as_x27_1104_ = v_tail_1119_;
v_b_1105_ = v___x_1141_;
goto _start;
}
}
}
else
{
lean_object* v_a_1281_; lean_object* v___x_1283_; uint8_t v_isShared_1284_; uint8_t v_isSharedCheck_1288_; 
lean_dec_ref(v_e_1102_);
v_a_1281_ = lean_ctor_get(v___x_1228_, 0);
v_isSharedCheck_1288_ = !lean_is_exclusive(v___x_1228_);
if (v_isSharedCheck_1288_ == 0)
{
v___x_1283_ = v___x_1228_;
v_isShared_1284_ = v_isSharedCheck_1288_;
goto v_resetjp_1282_;
}
else
{
lean_inc(v_a_1281_);
lean_dec(v___x_1228_);
v___x_1283_ = lean_box(0);
v_isShared_1284_ = v_isSharedCheck_1288_;
goto v_resetjp_1282_;
}
v_resetjp_1282_:
{
lean_object* v___x_1286_; 
if (v_isShared_1284_ == 0)
{
v___x_1286_ = v___x_1283_;
goto v_reusejp_1285_;
}
else
{
lean_object* v_reuseFailAlloc_1287_; 
v_reuseFailAlloc_1287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1287_, 0, v_a_1281_);
v___x_1286_ = v_reuseFailAlloc_1287_;
goto v_reusejp_1285_;
}
v_reusejp_1285_:
{
return v___x_1286_;
}
}
}
v___jp_1120_:
{
if (lean_obj_tag(v___y_1121_) == 0)
{
lean_object* v_a_1122_; lean_object* v___x_1124_; uint8_t v_isShared_1125_; uint8_t v_isSharedCheck_1132_; 
v_a_1122_ = lean_ctor_get(v___y_1121_, 0);
v_isSharedCheck_1132_ = !lean_is_exclusive(v___y_1121_);
if (v_isSharedCheck_1132_ == 0)
{
v___x_1124_ = v___y_1121_;
v_isShared_1125_ = v_isSharedCheck_1132_;
goto v_resetjp_1123_;
}
else
{
lean_inc(v_a_1122_);
lean_dec(v___y_1121_);
v___x_1124_ = lean_box(0);
v_isShared_1125_ = v_isSharedCheck_1132_;
goto v_resetjp_1123_;
}
v_resetjp_1123_:
{
if (lean_obj_tag(v_a_1122_) == 0)
{
lean_object* v_a_1126_; lean_object* v___x_1128_; 
lean_dec_ref(v_e_1102_);
v_a_1126_ = lean_ctor_get(v_a_1122_, 0);
lean_inc(v_a_1126_);
lean_dec_ref_known(v_a_1122_, 1);
if (v_isShared_1125_ == 0)
{
lean_ctor_set(v___x_1124_, 0, v_a_1126_);
v___x_1128_ = v___x_1124_;
goto v_reusejp_1127_;
}
else
{
lean_object* v_reuseFailAlloc_1129_; 
v_reuseFailAlloc_1129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1129_, 0, v_a_1126_);
v___x_1128_ = v_reuseFailAlloc_1129_;
goto v_reusejp_1127_;
}
v_reusejp_1127_:
{
return v___x_1128_;
}
}
else
{
lean_object* v_a_1130_; 
lean_del_object(v___x_1124_);
v_a_1130_ = lean_ctor_get(v_a_1122_, 0);
lean_inc(v_a_1130_);
lean_dec_ref_known(v_a_1122_, 1);
v_as_x27_1104_ = v_tail_1119_;
v_b_1105_ = v_a_1130_;
goto _start;
}
}
}
else
{
lean_object* v_a_1133_; lean_object* v___x_1135_; uint8_t v_isShared_1136_; uint8_t v_isSharedCheck_1140_; 
lean_dec_ref(v_e_1102_);
v_a_1133_ = lean_ctor_get(v___y_1121_, 0);
v_isSharedCheck_1140_ = !lean_is_exclusive(v___y_1121_);
if (v_isSharedCheck_1140_ == 0)
{
v___x_1135_ = v___y_1121_;
v_isShared_1136_ = v_isSharedCheck_1140_;
goto v_resetjp_1134_;
}
else
{
lean_inc(v_a_1133_);
lean_dec(v___y_1121_);
v___x_1135_ = lean_box(0);
v_isShared_1136_ = v_isSharedCheck_1140_;
goto v_resetjp_1134_;
}
v_resetjp_1134_:
{
lean_object* v___x_1138_; 
if (v_isShared_1136_ == 0)
{
v___x_1138_ = v___x_1135_;
goto v_reusejp_1137_;
}
else
{
lean_object* v_reuseFailAlloc_1139_; 
v_reuseFailAlloc_1139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1139_, 0, v_a_1133_);
v___x_1138_ = v_reuseFailAlloc_1139_;
goto v_reusejp_1137_;
}
v_reusejp_1137_:
{
return v___x_1138_;
}
}
}
}
v___jp_1142_:
{
lean_object* v___x_1154_; lean_object* v_a_1155_; uint8_t v___x_1156_; 
v___x_1154_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkChild___redArg(v_e_1102_, v___y_1143_, v___y_1144_);
lean_dec_ref(v___y_1143_);
v_a_1155_ = lean_ctor_get(v___x_1154_, 0);
lean_inc(v_a_1155_);
lean_dec_ref(v___x_1154_);
v___x_1156_ = lean_unbox(v_a_1155_);
lean_dec(v_a_1155_);
if (v___x_1156_ == 0)
{
lean_object* v___x_1157_; lean_object* v___x_1158_; 
v___x_1157_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__2, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__2_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__2);
v___x_1158_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__0(v___x_1157_, v___y_1144_, v___y_1145_, v___y_1146_, v___y_1147_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_, v___y_1152_, v___y_1153_);
v___y_1121_ = v___x_1158_;
goto v___jp_1120_;
}
else
{
v_as_x27_1104_ = v_tail_1119_;
v_b_1105_ = v___x_1141_;
goto _start;
}
}
v___jp_1160_:
{
if (v_found_1161_ == 0)
{
lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v_a_1174_; uint8_t v___x_1175_; 
v___x_1172_ = l_Lean_Expr_getAppFn(v_head_1118_);
v___x_1173_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkChild___redArg(v_e_1102_, v___x_1172_, v___y_1162_);
v_a_1174_ = lean_ctor_get(v___x_1173_, 0);
lean_inc(v_a_1174_);
lean_dec_ref(v___x_1173_);
v___x_1175_ = lean_unbox(v_a_1174_);
lean_dec(v_a_1174_);
if (v___x_1175_ == 0)
{
lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; 
lean_dec_ref(v___x_1172_);
v___x_1176_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__4, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__4);
v___x_1177_ = l_Lean_MessageData_ofExpr(v_e_1102_);
v___x_1178_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1178_, 0, v___x_1176_);
lean_ctor_set(v___x_1178_, 1, v___x_1177_);
v___x_1179_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__6, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__6_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__6);
v___x_1180_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1180_, 0, v___x_1178_);
lean_ctor_set(v___x_1180_, 1, v___x_1179_);
lean_inc(v_head_1118_);
v___x_1181_ = l_Lean_MessageData_ofExpr(v_head_1118_);
v___x_1182_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1182_, 0, v___x_1180_);
lean_ctor_set(v___x_1182_, 1, v___x_1181_);
v___x_1183_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__1___redArg(v___x_1182_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_);
return v___x_1183_;
}
else
{
v___y_1143_ = v___x_1172_;
v___y_1144_ = v___y_1162_;
v___y_1145_ = v___y_1163_;
v___y_1146_ = v___y_1164_;
v___y_1147_ = v___y_1165_;
v___y_1148_ = v___y_1166_;
v___y_1149_ = v___y_1167_;
v___y_1150_ = v___y_1168_;
v___y_1151_ = v___y_1169_;
v___y_1152_ = v___y_1170_;
v___y_1153_ = v___y_1171_;
goto v___jp_1142_;
}
}
else
{
v_as_x27_1104_ = v_tail_1119_;
v_b_1105_ = v___x_1141_;
goto _start;
}
}
v___jp_1185_:
{
uint8_t v___x_1198_; 
v___x_1198_ = l_Lean_Expr_hasLooseBVars(v___y_1186_);
if (v___x_1198_ == 0)
{
lean_object* v___x_1199_; lean_object* v_a_1200_; uint8_t v___x_1201_; 
v___x_1199_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkChild___redArg(v_e_1102_, v___y_1186_, v___y_1188_);
lean_dec_ref(v___y_1186_);
v_a_1200_ = lean_ctor_get(v___x_1199_, 0);
lean_inc(v_a_1200_);
lean_dec_ref(v___x_1199_);
v___x_1201_ = lean_unbox(v_a_1200_);
lean_dec(v_a_1200_);
if (v___x_1201_ == 0)
{
v_found_1161_ = v_found_1187_;
v___y_1162_ = v___y_1188_;
v___y_1163_ = v___y_1189_;
v___y_1164_ = v___y_1190_;
v___y_1165_ = v___y_1191_;
v___y_1166_ = v___y_1192_;
v___y_1167_ = v___y_1193_;
v___y_1168_ = v___y_1194_;
v___y_1169_ = v___y_1195_;
v___y_1170_ = v___y_1196_;
v___y_1171_ = v___y_1197_;
goto v___jp_1160_;
}
else
{
v_as_x27_1104_ = v_tail_1119_;
v_b_1105_ = v___x_1141_;
goto _start;
}
}
else
{
lean_dec_ref(v___y_1186_);
v_found_1161_ = v_found_1187_;
v___y_1162_ = v___y_1188_;
v___y_1163_ = v___y_1189_;
v___y_1164_ = v___y_1190_;
v___y_1165_ = v___y_1191_;
v___y_1166_ = v___y_1192_;
v___y_1167_ = v___y_1193_;
v___y_1168_ = v___y_1194_;
v___y_1169_ = v___y_1195_;
v___y_1170_ = v___y_1196_;
v___y_1171_ = v___y_1197_;
goto v___jp_1160_;
}
}
v___jp_1203_:
{
lean_object* v___x_1214_; 
lean_inc(v_head_1118_);
v___x_1214_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent(v_e_1102_, v_head_1118_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_, v___y_1211_, v___y_1212_, v___y_1213_);
if (lean_obj_tag(v___x_1214_) == 0)
{
lean_object* v_a_1215_; uint8_t v___x_1216_; 
v_a_1215_ = lean_ctor_get(v___x_1214_, 0);
lean_inc(v_a_1215_);
lean_dec_ref_known(v___x_1214_, 1);
v___x_1216_ = lean_unbox(v_a_1215_);
lean_dec(v_a_1215_);
if (v___x_1216_ == 0)
{
lean_object* v___x_1217_; lean_object* v___x_1218_; 
v___x_1217_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__8, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__8_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__8);
v___x_1218_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__0(v___x_1217_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_, v___y_1211_, v___y_1212_, v___y_1213_);
v___y_1121_ = v___x_1218_;
goto v___jp_1120_;
}
else
{
v_as_x27_1104_ = v_tail_1119_;
v_b_1105_ = v___x_1141_;
goto _start;
}
}
else
{
lean_object* v_a_1220_; lean_object* v___x_1222_; uint8_t v_isShared_1223_; uint8_t v_isSharedCheck_1227_; 
lean_dec_ref(v_e_1102_);
v_a_1220_ = lean_ctor_get(v___x_1214_, 0);
v_isSharedCheck_1227_ = !lean_is_exclusive(v___x_1214_);
if (v_isSharedCheck_1227_ == 0)
{
v___x_1222_ = v___x_1214_;
v_isShared_1223_ = v_isSharedCheck_1227_;
goto v_resetjp_1221_;
}
else
{
lean_inc(v_a_1220_);
lean_dec(v___x_1214_);
v___x_1222_ = lean_box(0);
v_isShared_1223_ = v_isSharedCheck_1227_;
goto v_resetjp_1221_;
}
v_resetjp_1221_:
{
lean_object* v___x_1225_; 
if (v_isShared_1223_ == 0)
{
v___x_1225_ = v___x_1222_;
goto v_reusejp_1224_;
}
else
{
lean_object* v_reuseFailAlloc_1226_; 
v_reuseFailAlloc_1226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1226_, 0, v_a_1220_);
v___x_1225_ = v_reuseFailAlloc_1226_;
goto v_reusejp_1224_;
}
v_reusejp_1224_:
{
return v___x_1225_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1102_ = stack[0].m_obj;
uint8_t v_a_1103_ = stack[1].m_num;
lean_object* v_as_x27_1104_ = stack[2].m_obj;
lean_object* v_b_1105_ = stack[3].m_obj;
lean_object* v___y_1106_ = stack[4].m_obj;
lean_object* v___y_1107_ = stack[5].m_obj;
lean_object* v___y_1108_ = stack[6].m_obj;
lean_object* v___y_1109_ = stack[7].m_obj;
lean_object* v___y_1110_ = stack[8].m_obj;
lean_object* v___y_1111_ = stack[9].m_obj;
lean_object* v___y_1112_ = stack[10].m_obj;
lean_object* v___y_1113_ = stack[11].m_obj;
lean_object* v___y_1114_ = stack[12].m_obj;
lean_object* v___y_1115_ = stack[13].m_obj;
lean_object* v_res_1289_;
v_res_1289_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg(v_e_1102_, v_a_1103_, v_as_x27_1104_, v_b_1105_, v___y_1106_, v___y_1107_, v___y_1108_, v___y_1109_, v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_);
stack->m_obj
 = v_res_1289_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___boxed(lean_object* v_e_1290_, lean_object* v_a_1291_, lean_object* v_as_x27_1292_, lean_object* v_b_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_){
_start:
{
uint8_t v_a_38436__boxed_1305_; lean_object* v_res_1306_; 
v_a_38436__boxed_1305_ = lean_unbox(v_a_1291_);
v_res_1306_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg(v_e_1290_, v_a_38436__boxed_1305_, v_as_x27_1292_, v_b_1293_, v___y_1294_, v___y_1295_, v___y_1296_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_);
lean_dec(v___y_1303_);
lean_dec_ref(v___y_1302_);
lean_dec(v___y_1301_);
lean_dec_ref(v___y_1300_);
lean_dec(v___y_1299_);
lean_dec_ref(v___y_1298_);
lean_dec(v___y_1297_);
lean_dec_ref(v___y_1296_);
lean_dec(v___y_1295_);
lean_dec(v___y_1294_);
lean_dec(v_as_x27_1292_);
return v_res_1306_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents___closed__1(void){
_start:
{
lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; 
v___x_1308_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents___closed__0));
v___x_1309_ = lean_unsigned_to_nat(6u);
v___x_1310_ = lean_unsigned_to_nat(97u);
v___x_1311_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__0));
v___x_1312_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__0));
v___x_1313_ = l_mkPanicMessageWithDecl(v___x_1312_, v___x_1311_, v___x_1310_, v___x_1309_, v___x_1308_);
return v___x_1313_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents(lean_object* v_e_1314_, lean_object* v_a_1315_, lean_object* v_a_1316_, lean_object* v_a_1317_, lean_object* v_a_1318_, lean_object* v_a_1319_, lean_object* v_a_1320_, lean_object* v_a_1321_, lean_object* v_a_1322_, lean_object* v_a_1323_, lean_object* v_a_1324_){
_start:
{
lean_object* v___x_1326_; 
v___x_1326_ = l_Lean_Meta_Grind_isRoot___redArg(v_e_1314_, v_a_1315_);
if (lean_obj_tag(v___x_1326_) == 0)
{
lean_object* v_a_1327_; uint8_t v___x_1328_; 
v_a_1327_ = lean_ctor_get(v___x_1326_, 0);
lean_inc(v_a_1327_);
lean_dec_ref_known(v___x_1326_, 1);
v___x_1328_ = lean_unbox(v_a_1327_);
if (v___x_1328_ == 0)
{
lean_object* v___x_1329_; 
lean_dec(v_a_1327_);
v___x_1329_ = l_Lean_Meta_Grind_getParents___redArg(v_e_1314_, v_a_1315_);
lean_dec_ref(v_e_1314_);
if (lean_obj_tag(v___x_1329_) == 0)
{
lean_object* v_a_1330_; lean_object* v___x_1332_; uint8_t v_isShared_1333_; uint8_t v_isSharedCheck_1341_; 
v_a_1330_ = lean_ctor_get(v___x_1329_, 0);
v_isSharedCheck_1341_ = !lean_is_exclusive(v___x_1329_);
if (v_isSharedCheck_1341_ == 0)
{
v___x_1332_ = v___x_1329_;
v_isShared_1333_ = v_isSharedCheck_1341_;
goto v_resetjp_1331_;
}
else
{
lean_inc(v_a_1330_);
lean_dec(v___x_1329_);
v___x_1332_ = lean_box(0);
v_isShared_1333_ = v_isSharedCheck_1341_;
goto v_resetjp_1331_;
}
v_resetjp_1331_:
{
uint8_t v___x_1334_; 
v___x_1334_ = l_Lean_Meta_Grind_ParentSet_isEmpty(v_a_1330_);
lean_dec(v_a_1330_);
if (v___x_1334_ == 0)
{
lean_object* v___x_1335_; lean_object* v___x_1336_; 
lean_del_object(v___x_1332_);
v___x_1335_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents___closed__1, &l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents___closed__1);
v___x_1336_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__4(v___x_1335_, v_a_1315_, v_a_1316_, v_a_1317_, v_a_1318_, v_a_1319_, v_a_1320_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
return v___x_1336_;
}
else
{
lean_object* v___x_1337_; lean_object* v___x_1339_; 
v___x_1337_ = lean_box(0);
if (v_isShared_1333_ == 0)
{
lean_ctor_set(v___x_1332_, 0, v___x_1337_);
v___x_1339_ = v___x_1332_;
goto v_reusejp_1338_;
}
else
{
lean_object* v_reuseFailAlloc_1340_; 
v_reuseFailAlloc_1340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1340_, 0, v___x_1337_);
v___x_1339_ = v_reuseFailAlloc_1340_;
goto v_reusejp_1338_;
}
v_reusejp_1338_:
{
return v___x_1339_;
}
}
}
}
else
{
lean_object* v_a_1342_; lean_object* v___x_1344_; uint8_t v_isShared_1345_; uint8_t v_isSharedCheck_1349_; 
v_a_1342_ = lean_ctor_get(v___x_1329_, 0);
v_isSharedCheck_1349_ = !lean_is_exclusive(v___x_1329_);
if (v_isSharedCheck_1349_ == 0)
{
v___x_1344_ = v___x_1329_;
v_isShared_1345_ = v_isSharedCheck_1349_;
goto v_resetjp_1343_;
}
else
{
lean_inc(v_a_1342_);
lean_dec(v___x_1329_);
v___x_1344_ = lean_box(0);
v_isShared_1345_ = v_isSharedCheck_1349_;
goto v_resetjp_1343_;
}
v_resetjp_1343_:
{
lean_object* v___x_1347_; 
if (v_isShared_1345_ == 0)
{
v___x_1347_ = v___x_1344_;
goto v_reusejp_1346_;
}
else
{
lean_object* v_reuseFailAlloc_1348_; 
v_reuseFailAlloc_1348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1348_, 0, v_a_1342_);
v___x_1347_ = v_reuseFailAlloc_1348_;
goto v_reusejp_1346_;
}
v_reusejp_1346_:
{
return v___x_1347_;
}
}
}
}
else
{
lean_object* v___x_1350_; 
v___x_1350_ = l_Lean_Meta_Grind_getParents___redArg(v_e_1314_, v_a_1315_);
if (lean_obj_tag(v___x_1350_) == 0)
{
lean_object* v_a_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; uint8_t v___x_1354_; lean_object* v___x_1355_; 
v_a_1351_ = lean_ctor_get(v___x_1350_, 0);
lean_inc(v_a_1351_);
lean_dec_ref_known(v___x_1350_, 1);
v___x_1352_ = l_Lean_Meta_Grind_ParentSet_elems(v_a_1351_);
lean_dec(v_a_1351_);
v___x_1353_ = lean_box(0);
v___x_1354_ = lean_unbox(v_a_1327_);
lean_dec(v_a_1327_);
v___x_1355_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg(v_e_1314_, v___x_1354_, v___x_1352_, v___x_1353_, v_a_1315_, v_a_1316_, v_a_1317_, v_a_1318_, v_a_1319_, v_a_1320_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
lean_dec(v___x_1352_);
if (lean_obj_tag(v___x_1355_) == 0)
{
lean_object* v___x_1357_; uint8_t v_isShared_1358_; uint8_t v_isSharedCheck_1362_; 
v_isSharedCheck_1362_ = !lean_is_exclusive(v___x_1355_);
if (v_isSharedCheck_1362_ == 0)
{
lean_object* v_unused_1363_; 
v_unused_1363_ = lean_ctor_get(v___x_1355_, 0);
lean_dec(v_unused_1363_);
v___x_1357_ = v___x_1355_;
v_isShared_1358_ = v_isSharedCheck_1362_;
goto v_resetjp_1356_;
}
else
{
lean_dec(v___x_1355_);
v___x_1357_ = lean_box(0);
v_isShared_1358_ = v_isSharedCheck_1362_;
goto v_resetjp_1356_;
}
v_resetjp_1356_:
{
lean_object* v___x_1360_; 
if (v_isShared_1358_ == 0)
{
lean_ctor_set(v___x_1357_, 0, v___x_1353_);
v___x_1360_ = v___x_1357_;
goto v_reusejp_1359_;
}
else
{
lean_object* v_reuseFailAlloc_1361_; 
v_reuseFailAlloc_1361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1361_, 0, v___x_1353_);
v___x_1360_ = v_reuseFailAlloc_1361_;
goto v_reusejp_1359_;
}
v_reusejp_1359_:
{
return v___x_1360_;
}
}
}
else
{
return v___x_1355_;
}
}
else
{
lean_object* v_a_1364_; lean_object* v___x_1366_; uint8_t v_isShared_1367_; uint8_t v_isSharedCheck_1371_; 
lean_dec(v_a_1327_);
lean_dec_ref(v_e_1314_);
v_a_1364_ = lean_ctor_get(v___x_1350_, 0);
v_isSharedCheck_1371_ = !lean_is_exclusive(v___x_1350_);
if (v_isSharedCheck_1371_ == 0)
{
v___x_1366_ = v___x_1350_;
v_isShared_1367_ = v_isSharedCheck_1371_;
goto v_resetjp_1365_;
}
else
{
lean_inc(v_a_1364_);
lean_dec(v___x_1350_);
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
else
{
lean_object* v_a_1372_; lean_object* v___x_1374_; uint8_t v_isShared_1375_; uint8_t v_isSharedCheck_1379_; 
lean_dec_ref(v_e_1314_);
v_a_1372_ = lean_ctor_get(v___x_1326_, 0);
v_isSharedCheck_1379_ = !lean_is_exclusive(v___x_1326_);
if (v_isSharedCheck_1379_ == 0)
{
v___x_1374_ = v___x_1326_;
v_isShared_1375_ = v_isSharedCheck_1379_;
goto v_resetjp_1373_;
}
else
{
lean_inc(v_a_1372_);
lean_dec(v___x_1326_);
v___x_1374_ = lean_box(0);
v_isShared_1375_ = v_isSharedCheck_1379_;
goto v_resetjp_1373_;
}
v_resetjp_1373_:
{
lean_object* v___x_1377_; 
if (v_isShared_1375_ == 0)
{
v___x_1377_ = v___x_1374_;
goto v_reusejp_1376_;
}
else
{
lean_object* v_reuseFailAlloc_1378_; 
v_reuseFailAlloc_1378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1378_, 0, v_a_1372_);
v___x_1377_ = v_reuseFailAlloc_1378_;
goto v_reusejp_1376_;
}
v_reusejp_1376_:
{
return v___x_1377_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1314_ = stack[0].m_obj;
lean_object* v_a_1315_ = stack[1].m_obj;
lean_object* v_a_1316_ = stack[2].m_obj;
lean_object* v_a_1317_ = stack[3].m_obj;
lean_object* v_a_1318_ = stack[4].m_obj;
lean_object* v_a_1319_ = stack[5].m_obj;
lean_object* v_a_1320_ = stack[6].m_obj;
lean_object* v_a_1321_ = stack[7].m_obj;
lean_object* v_a_1322_ = stack[8].m_obj;
lean_object* v_a_1323_ = stack[9].m_obj;
lean_object* v_a_1324_ = stack[10].m_obj;
lean_object* v_res_1380_;
v_res_1380_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents(v_e_1314_, v_a_1315_, v_a_1316_, v_a_1317_, v_a_1318_, v_a_1319_, v_a_1320_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
stack->m_obj
 = v_res_1380_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents___boxed(lean_object* v_e_1381_, lean_object* v_a_1382_, lean_object* v_a_1383_, lean_object* v_a_1384_, lean_object* v_a_1385_, lean_object* v_a_1386_, lean_object* v_a_1387_, lean_object* v_a_1388_, lean_object* v_a_1389_, lean_object* v_a_1390_, lean_object* v_a_1391_, lean_object* v_a_1392_){
_start:
{
lean_object* v_res_1393_; 
v_res_1393_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents(v_e_1381_, v_a_1382_, v_a_1383_, v_a_1384_, v_a_1385_, v_a_1386_, v_a_1387_, v_a_1388_, v_a_1389_, v_a_1390_, v_a_1391_);
lean_dec(v_a_1391_);
lean_dec_ref(v_a_1390_);
lean_dec(v_a_1389_);
lean_dec_ref(v_a_1388_);
lean_dec(v_a_1387_);
lean_dec_ref(v_a_1386_);
lean_dec(v_a_1385_);
lean_dec_ref(v_a_1384_);
lean_dec(v_a_1383_);
lean_dec(v_a_1382_);
return v_res_1393_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__1(lean_object* v_00_u03b1_1394_, lean_object* v_msg_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_){
_start:
{
lean_object* v___x_1407_; 
v___x_1407_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__1___redArg(v_msg_1395_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_);
return v___x_1407_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1395_ = stack[1].m_obj;
lean_object* v___y_1396_ = stack[2].m_obj;
lean_object* v___y_1397_ = stack[3].m_obj;
lean_object* v___y_1398_ = stack[4].m_obj;
lean_object* v___y_1399_ = stack[5].m_obj;
lean_object* v___y_1400_ = stack[6].m_obj;
lean_object* v___y_1401_ = stack[7].m_obj;
lean_object* v___y_1402_ = stack[8].m_obj;
lean_object* v___y_1403_ = stack[9].m_obj;
lean_object* v___y_1404_ = stack[10].m_obj;
lean_object* v___y_1405_ = stack[11].m_obj;
lean_object* v_res_1408_;
v_res_1408_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__1(lean_box(0), v_msg_1395_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_);
stack->m_obj
 = v_res_1408_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__1___boxed(lean_object* v_00_u03b1_1409_, lean_object* v_msg_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_){
_start:
{
lean_object* v_res_1422_; 
v_res_1422_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__1(v_00_u03b1_1409_, v_msg_1410_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_, v___y_1416_, v___y_1417_, v___y_1418_, v___y_1419_, v___y_1420_);
lean_dec(v___y_1420_);
lean_dec_ref(v___y_1419_);
lean_dec(v___y_1418_);
lean_dec_ref(v___y_1417_);
lean_dec(v___y_1416_);
lean_dec_ref(v___y_1415_);
lean_dec(v___y_1414_);
lean_dec_ref(v___y_1413_);
lean_dec(v___y_1412_);
lean_dec(v___y_1411_);
return v_res_1422_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__2(lean_object* v_e_1423_, uint8_t v_a_1424_, lean_object* v_as_1425_, size_t v_sz_1426_, size_t v_i_1427_, uint8_t v_b_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_){
_start:
{
lean_object* v___x_1440_; 
v___x_1440_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__2___redArg(v_e_1423_, v_a_1424_, v_as_1425_, v_sz_1426_, v_i_1427_, v_b_1428_, v___y_1429_);
return v___x_1440_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1423_ = stack[0].m_obj;
uint8_t v_a_1424_ = stack[1].m_num;
lean_object* v_as_1425_ = stack[2].m_obj;
size_t v_sz_1426_ = stack[3].m_num;
size_t v_i_1427_ = stack[4].m_num;
uint8_t v_b_1428_ = stack[5].m_num;
lean_object* v___y_1429_ = stack[6].m_obj;
lean_object* v___y_1430_ = stack[7].m_obj;
lean_object* v___y_1431_ = stack[8].m_obj;
lean_object* v___y_1432_ = stack[9].m_obj;
lean_object* v___y_1433_ = stack[10].m_obj;
lean_object* v___y_1434_ = stack[11].m_obj;
lean_object* v___y_1435_ = stack[12].m_obj;
lean_object* v___y_1436_ = stack[13].m_obj;
lean_object* v___y_1437_ = stack[14].m_obj;
lean_object* v___y_1438_ = stack[15].m_obj;
lean_object* v_res_1441_;
v_res_1441_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__2(v_e_1423_, v_a_1424_, v_as_1425_, v_sz_1426_, v_i_1427_, v_b_1428_, v___y_1429_, v___y_1430_, v___y_1431_, v___y_1432_, v___y_1433_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_);
stack->m_obj
 = v_res_1441_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__2___boxed(lean_object** _args){
lean_object* v_e_1442_ = _args[0];
lean_object* v_a_1443_ = _args[1];
lean_object* v_as_1444_ = _args[2];
lean_object* v_sz_1445_ = _args[3];
lean_object* v_i_1446_ = _args[4];
lean_object* v_b_1447_ = _args[5];
lean_object* v___y_1448_ = _args[6];
lean_object* v___y_1449_ = _args[7];
lean_object* v___y_1450_ = _args[8];
lean_object* v___y_1451_ = _args[9];
lean_object* v___y_1452_ = _args[10];
lean_object* v___y_1453_ = _args[11];
lean_object* v___y_1454_ = _args[12];
lean_object* v___y_1455_ = _args[13];
lean_object* v___y_1456_ = _args[14];
lean_object* v___y_1457_ = _args[15];
lean_object* v___y_1458_ = _args[16];
_start:
{
uint8_t v_a_39308__boxed_1459_; size_t v_sz_boxed_1460_; size_t v_i_boxed_1461_; uint8_t v_b_boxed_1462_; lean_object* v_res_1463_; 
v_a_39308__boxed_1459_ = lean_unbox(v_a_1443_);
v_sz_boxed_1460_ = lean_unbox_usize(v_sz_1445_);
lean_dec(v_sz_1445_);
v_i_boxed_1461_ = lean_unbox_usize(v_i_1446_);
lean_dec(v_i_1446_);
v_b_boxed_1462_ = lean_unbox(v_b_1447_);
v_res_1463_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__2(v_e_1442_, v_a_39308__boxed_1459_, v_as_1444_, v_sz_boxed_1460_, v_i_boxed_1461_, v_b_boxed_1462_, v___y_1448_, v___y_1449_, v___y_1450_, v___y_1451_, v___y_1452_, v___y_1453_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_);
lean_dec(v___y_1457_);
lean_dec_ref(v___y_1456_);
lean_dec(v___y_1455_);
lean_dec_ref(v___y_1454_);
lean_dec(v___y_1453_);
lean_dec_ref(v___y_1452_);
lean_dec(v___y_1451_);
lean_dec_ref(v___y_1450_);
lean_dec(v___y_1449_);
lean_dec(v___y_1448_);
lean_dec_ref(v_as_1444_);
lean_dec_ref(v_e_1442_);
return v_res_1463_;
}
}
lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3(lean_object* v_e_1464_, uint8_t v_a_1465_, lean_object* v_as_1466_, lean_object* v_as_x27_1467_, lean_object* v_b_1468_, lean_object* v_a_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_){
_start:
{
lean_object* v___x_1481_; 
v___x_1481_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg(v_e_1464_, v_a_1465_, v_as_x27_1467_, v_b_1468_, v___y_1470_, v___y_1471_, v___y_1472_, v___y_1473_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_);
return v___x_1481_;
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1464_ = stack[0].m_obj;
uint8_t v_a_1465_ = stack[1].m_num;
lean_object* v_as_1466_ = stack[2].m_obj;
lean_object* v_as_x27_1467_ = stack[3].m_obj;
lean_object* v_b_1468_ = stack[4].m_obj;
lean_object* v___y_1470_ = stack[6].m_obj;
lean_object* v___y_1471_ = stack[7].m_obj;
lean_object* v___y_1472_ = stack[8].m_obj;
lean_object* v___y_1473_ = stack[9].m_obj;
lean_object* v___y_1474_ = stack[10].m_obj;
lean_object* v___y_1475_ = stack[11].m_obj;
lean_object* v___y_1476_ = stack[12].m_obj;
lean_object* v___y_1477_ = stack[13].m_obj;
lean_object* v___y_1478_ = stack[14].m_obj;
lean_object* v___y_1479_ = stack[15].m_obj;
lean_object* v_res_1482_;
v_res_1482_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3(v_e_1464_, v_a_1465_, v_as_1466_, v_as_x27_1467_, v_b_1468_, lean_box(0), v___y_1470_, v___y_1471_, v___y_1472_, v___y_1473_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_);
stack->m_obj
 = v_res_1482_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___boxed(lean_object** _args){
lean_object* v_e_1483_ = _args[0];
lean_object* v_a_1484_ = _args[1];
lean_object* v_as_1485_ = _args[2];
lean_object* v_as_x27_1486_ = _args[3];
lean_object* v_b_1487_ = _args[4];
lean_object* v_a_1488_ = _args[5];
lean_object* v___y_1489_ = _args[6];
lean_object* v___y_1490_ = _args[7];
lean_object* v___y_1491_ = _args[8];
lean_object* v___y_1492_ = _args[9];
lean_object* v___y_1493_ = _args[10];
lean_object* v___y_1494_ = _args[11];
lean_object* v___y_1495_ = _args[12];
lean_object* v___y_1496_ = _args[13];
lean_object* v___y_1497_ = _args[14];
lean_object* v___y_1498_ = _args[15];
lean_object* v___y_1499_ = _args[16];
_start:
{
uint8_t v_a_39371__boxed_1500_; lean_object* v_res_1501_; 
v_a_39371__boxed_1500_ = lean_unbox(v_a_1484_);
v_res_1501_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3(v_e_1483_, v_a_39371__boxed_1500_, v_as_1485_, v_as_x27_1486_, v_b_1487_, v_a_1488_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_);
lean_dec(v___y_1498_);
lean_dec_ref(v___y_1497_);
lean_dec(v___y_1496_);
lean_dec_ref(v___y_1495_);
lean_dec(v___y_1494_);
lean_dec_ref(v___y_1493_);
lean_dec(v___y_1492_);
lean_dec_ref(v___y_1491_);
lean_dec(v___y_1490_);
lean_dec(v___y_1489_);
lean_dec(v_as_x27_1486_);
lean_dec(v_as_1485_);
return v_res_1501_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; 
v___x_1504_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg___closed__1));
v___x_1505_ = lean_unsigned_to_nat(6u);
v___x_1506_ = lean_unsigned_to_nat(108u);
v___x_1507_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg___closed__0));
v___x_1508_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__0));
v___x_1509_ = l_mkPanicMessageWithDecl(v___x_1508_, v___x_1507_, v___x_1506_, v___x_1505_, v___x_1504_);
return v___x_1509_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; 
v___x_1511_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg___closed__3));
v___x_1512_ = lean_unsigned_to_nat(6u);
v___x_1513_ = lean_unsigned_to_nat(106u);
v___x_1514_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg___closed__0));
v___x_1515_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__0));
v___x_1516_ = l_mkPanicMessageWithDecl(v___x_1515_, v___x_1514_, v___x_1513_, v___x_1512_, v___x_1511_);
return v___x_1516_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg(lean_object* v_upperBound_1517_, lean_object* v_a_1518_, lean_object* v___x_1519_, lean_object* v_a_1520_, lean_object* v_b_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_){
_start:
{
lean_object* v_a_1534_; lean_object* v___y_1539_; uint8_t v___x_1558_; 
v___x_1558_ = lean_nat_dec_lt(v_a_1520_, v_upperBound_1517_);
if (v___x_1558_ == 0)
{
lean_object* v___x_1559_; 
lean_dec(v_a_1520_);
v___x_1559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1559_, 0, v_b_1521_);
return v___x_1559_;
}
else
{
lean_object* v___x_1560_; lean_object* v___x_1561_; size_t v___x_1562_; size_t v___x_1563_; uint8_t v___x_1564_; 
v___x_1560_ = l_Lean_instInhabitedExpr;
v___x_1561_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1560_, v_a_1518_, v_a_1520_);
v___x_1562_ = lean_ptr_addr(v___x_1519_);
v___x_1563_ = lean_ptr_addr(v___x_1561_);
v___x_1564_ = lean_usize_dec_eq(v___x_1562_, v___x_1563_);
if (v___x_1564_ == 0)
{
uint8_t v___x_1565_; 
v___x_1565_ = lean_expr_equal(v___x_1519_, v___x_1561_);
lean_dec(v___x_1561_);
if (v___x_1565_ == 0)
{
lean_object* v___x_1566_; 
v___x_1566_ = lean_box(0);
v_a_1534_ = v___x_1566_;
goto v___jp_1533_;
}
else
{
lean_object* v___x_1567_; lean_object* v___x_1568_; 
v___x_1567_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg___closed__2, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg___closed__2_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg___closed__2);
v___x_1568_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__0(v___x_1567_, v___y_1522_, v___y_1523_, v___y_1524_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_);
v___y_1539_ = v___x_1568_;
goto v___jp_1538_;
}
}
else
{
lean_object* v___x_1569_; lean_object* v___x_1570_; 
lean_dec(v___x_1561_);
v___x_1569_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg___closed__4, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg___closed__4_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg___closed__4);
v___x_1570_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__0(v___x_1569_, v___y_1522_, v___y_1523_, v___y_1524_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_);
v___y_1539_ = v___x_1570_;
goto v___jp_1538_;
}
}
v___jp_1533_:
{
lean_object* v___x_1535_; lean_object* v___x_1536_; 
v___x_1535_ = lean_unsigned_to_nat(1u);
v___x_1536_ = lean_nat_add(v_a_1520_, v___x_1535_);
lean_dec(v_a_1520_);
v_a_1520_ = v___x_1536_;
v_b_1521_ = v_a_1534_;
goto _start;
}
v___jp_1538_:
{
if (lean_obj_tag(v___y_1539_) == 0)
{
lean_object* v_a_1540_; lean_object* v___x_1542_; uint8_t v_isShared_1543_; uint8_t v_isSharedCheck_1549_; 
v_a_1540_ = lean_ctor_get(v___y_1539_, 0);
v_isSharedCheck_1549_ = !lean_is_exclusive(v___y_1539_);
if (v_isSharedCheck_1549_ == 0)
{
v___x_1542_ = v___y_1539_;
v_isShared_1543_ = v_isSharedCheck_1549_;
goto v_resetjp_1541_;
}
else
{
lean_inc(v_a_1540_);
lean_dec(v___y_1539_);
v___x_1542_ = lean_box(0);
v_isShared_1543_ = v_isSharedCheck_1549_;
goto v_resetjp_1541_;
}
v_resetjp_1541_:
{
if (lean_obj_tag(v_a_1540_) == 0)
{
lean_object* v_a_1544_; lean_object* v___x_1546_; 
lean_dec(v_a_1520_);
v_a_1544_ = lean_ctor_get(v_a_1540_, 0);
lean_inc(v_a_1544_);
lean_dec_ref_known(v_a_1540_, 1);
if (v_isShared_1543_ == 0)
{
lean_ctor_set(v___x_1542_, 0, v_a_1544_);
v___x_1546_ = v___x_1542_;
goto v_reusejp_1545_;
}
else
{
lean_object* v_reuseFailAlloc_1547_; 
v_reuseFailAlloc_1547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1547_, 0, v_a_1544_);
v___x_1546_ = v_reuseFailAlloc_1547_;
goto v_reusejp_1545_;
}
v_reusejp_1545_:
{
return v___x_1546_;
}
}
else
{
lean_object* v_a_1548_; 
lean_del_object(v___x_1542_);
v_a_1548_ = lean_ctor_get(v_a_1540_, 0);
lean_inc(v_a_1548_);
lean_dec_ref_known(v_a_1540_, 1);
v_a_1534_ = v_a_1548_;
goto v___jp_1533_;
}
}
}
else
{
lean_object* v_a_1550_; lean_object* v___x_1552_; uint8_t v_isShared_1553_; uint8_t v_isSharedCheck_1557_; 
lean_dec(v_a_1520_);
v_a_1550_ = lean_ctor_get(v___y_1539_, 0);
v_isSharedCheck_1557_ = !lean_is_exclusive(v___y_1539_);
if (v_isSharedCheck_1557_ == 0)
{
v___x_1552_ = v___y_1539_;
v_isShared_1553_ = v_isSharedCheck_1557_;
goto v_resetjp_1551_;
}
else
{
lean_inc(v_a_1550_);
lean_dec(v___y_1539_);
v___x_1552_ = lean_box(0);
v_isShared_1553_ = v_isSharedCheck_1557_;
goto v_resetjp_1551_;
}
v_resetjp_1551_:
{
lean_object* v___x_1555_; 
if (v_isShared_1553_ == 0)
{
v___x_1555_ = v___x_1552_;
goto v_reusejp_1554_;
}
else
{
lean_object* v_reuseFailAlloc_1556_; 
v_reuseFailAlloc_1556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1556_, 0, v_a_1550_);
v___x_1555_ = v_reuseFailAlloc_1556_;
goto v_reusejp_1554_;
}
v_reusejp_1554_:
{
return v___x_1555_;
}
}
}
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_1517_ = stack[0].m_obj;
lean_object* v_a_1518_ = stack[1].m_obj;
lean_object* v___x_1519_ = stack[2].m_obj;
lean_object* v_a_1520_ = stack[3].m_obj;
lean_object* v_b_1521_ = stack[4].m_obj;
lean_object* v___y_1522_ = stack[5].m_obj;
lean_object* v___y_1523_ = stack[6].m_obj;
lean_object* v___y_1524_ = stack[7].m_obj;
lean_object* v___y_1525_ = stack[8].m_obj;
lean_object* v___y_1526_ = stack[9].m_obj;
lean_object* v___y_1527_ = stack[10].m_obj;
lean_object* v___y_1528_ = stack[11].m_obj;
lean_object* v___y_1529_ = stack[12].m_obj;
lean_object* v___y_1530_ = stack[13].m_obj;
lean_object* v___y_1531_ = stack[14].m_obj;
lean_object* v_res_1571_;
v_res_1571_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg(v_upperBound_1517_, v_a_1518_, v___x_1519_, v_a_1520_, v_b_1521_, v___y_1522_, v___y_1523_, v___y_1524_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_);
stack->m_obj
 = v_res_1571_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg___boxed(lean_object* v_upperBound_1572_, lean_object* v_a_1573_, lean_object* v___x_1574_, lean_object* v_a_1575_, lean_object* v_b_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_){
_start:
{
lean_object* v_res_1588_; 
v_res_1588_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg(v_upperBound_1572_, v_a_1573_, v___x_1574_, v_a_1575_, v_b_1576_, v___y_1577_, v___y_1578_, v___y_1579_, v___y_1580_, v___y_1581_, v___y_1582_, v___y_1583_, v___y_1584_, v___y_1585_, v___y_1586_);
lean_dec(v___y_1586_);
lean_dec_ref(v___y_1585_);
lean_dec(v___y_1584_);
lean_dec_ref(v___y_1583_);
lean_dec(v___y_1582_);
lean_dec_ref(v___y_1581_);
lean_dec(v___y_1580_);
lean_dec_ref(v___y_1579_);
lean_dec(v___y_1578_);
lean_dec(v___y_1577_);
lean_dec_ref(v___x_1574_);
lean_dec_ref(v_a_1573_);
lean_dec(v_upperBound_1572_);
return v_res_1588_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__1___redArg(lean_object* v_upperBound_1589_, lean_object* v___x_1590_, lean_object* v_a_1591_, lean_object* v_a_1592_, lean_object* v_b_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_){
_start:
{
uint8_t v___x_1605_; 
v___x_1605_ = lean_nat_dec_lt(v_a_1592_, v_upperBound_1589_);
if (v___x_1605_ == 0)
{
lean_object* v___x_1606_; 
lean_dec(v_a_1592_);
v___x_1606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1606_, 0, v_b_1593_);
return v___x_1606_;
}
else
{
lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; 
v___x_1607_ = lean_box(0);
v___x_1608_ = l_Lean_instInhabitedExpr;
v___x_1609_ = lean_unsigned_to_nat(1u);
v___x_1610_ = lean_nat_add(v_a_1592_, v___x_1609_);
v___x_1611_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1608_, v_a_1591_, v_a_1592_);
lean_dec(v_a_1592_);
lean_inc(v___x_1610_);
v___x_1612_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg(v___x_1590_, v_a_1591_, v___x_1611_, v___x_1610_, v___x_1607_, v___y_1594_, v___y_1595_, v___y_1596_, v___y_1597_, v___y_1598_, v___y_1599_, v___y_1600_, v___y_1601_, v___y_1602_, v___y_1603_);
lean_dec(v___x_1611_);
if (lean_obj_tag(v___x_1612_) == 0)
{
lean_dec_ref_known(v___x_1612_, 1);
v_a_1592_ = v___x_1610_;
v_b_1593_ = v___x_1607_;
goto _start;
}
else
{
lean_dec(v___x_1610_);
return v___x_1612_;
}
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_1589_ = stack[0].m_obj;
lean_object* v___x_1590_ = stack[1].m_obj;
lean_object* v_a_1591_ = stack[2].m_obj;
lean_object* v_a_1592_ = stack[3].m_obj;
lean_object* v_b_1593_ = stack[4].m_obj;
lean_object* v___y_1594_ = stack[5].m_obj;
lean_object* v___y_1595_ = stack[6].m_obj;
lean_object* v___y_1596_ = stack[7].m_obj;
lean_object* v___y_1597_ = stack[8].m_obj;
lean_object* v___y_1598_ = stack[9].m_obj;
lean_object* v___y_1599_ = stack[10].m_obj;
lean_object* v___y_1600_ = stack[11].m_obj;
lean_object* v___y_1601_ = stack[12].m_obj;
lean_object* v___y_1602_ = stack[13].m_obj;
lean_object* v___y_1603_ = stack[14].m_obj;
lean_object* v_res_1614_;
v_res_1614_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__1___redArg(v_upperBound_1589_, v___x_1590_, v_a_1591_, v_a_1592_, v_b_1593_, v___y_1594_, v___y_1595_, v___y_1596_, v___y_1597_, v___y_1598_, v___y_1599_, v___y_1600_, v___y_1601_, v___y_1602_, v___y_1603_);
stack->m_obj
 = v_res_1614_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__1___redArg___boxed(lean_object* v_upperBound_1615_, lean_object* v___x_1616_, lean_object* v_a_1617_, lean_object* v_a_1618_, lean_object* v_b_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_){
_start:
{
lean_object* v_res_1631_; 
v_res_1631_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__1___redArg(v_upperBound_1615_, v___x_1616_, v_a_1617_, v_a_1618_, v_b_1619_, v___y_1620_, v___y_1621_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_);
lean_dec(v___y_1629_);
lean_dec_ref(v___y_1628_);
lean_dec(v___y_1627_);
lean_dec_ref(v___y_1626_);
lean_dec(v___y_1625_);
lean_dec_ref(v___y_1624_);
lean_dec(v___y_1623_);
lean_dec_ref(v___y_1622_);
lean_dec(v___y_1621_);
lean_dec(v___y_1620_);
lean_dec_ref(v_a_1617_);
lean_dec(v___x_1616_);
lean_dec(v_upperBound_1615_);
return v_res_1631_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq(lean_object* v_a_1632_, lean_object* v_a_1633_, lean_object* v_a_1634_, lean_object* v_a_1635_, lean_object* v_a_1636_, lean_object* v_a_1637_, lean_object* v_a_1638_, lean_object* v_a_1639_, lean_object* v_a_1640_, lean_object* v_a_1641_){
_start:
{
lean_object* v___x_1643_; 
v___x_1643_ = l_Lean_Meta_Grind_getExprs___redArg(v_a_1632_);
if (lean_obj_tag(v___x_1643_) == 0)
{
lean_object* v_a_1644_; lean_object* v_size_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; 
v_a_1644_ = lean_ctor_get(v___x_1643_, 0);
lean_inc(v_a_1644_);
lean_dec_ref_known(v___x_1643_, 1);
v_size_1645_ = lean_ctor_get(v_a_1644_, 2);
lean_inc(v_size_1645_);
v___x_1646_ = lean_unsigned_to_nat(0u);
v___x_1647_ = lean_box(0);
v___x_1648_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__1___redArg(v_size_1645_, v_size_1645_, v_a_1644_, v___x_1646_, v___x_1647_, v_a_1632_, v_a_1633_, v_a_1634_, v_a_1635_, v_a_1636_, v_a_1637_, v_a_1638_, v_a_1639_, v_a_1640_, v_a_1641_);
lean_dec(v_a_1644_);
lean_dec(v_size_1645_);
if (lean_obj_tag(v___x_1648_) == 0)
{
lean_object* v___x_1650_; uint8_t v_isShared_1651_; uint8_t v_isSharedCheck_1655_; 
v_isSharedCheck_1655_ = !lean_is_exclusive(v___x_1648_);
if (v_isSharedCheck_1655_ == 0)
{
lean_object* v_unused_1656_; 
v_unused_1656_ = lean_ctor_get(v___x_1648_, 0);
lean_dec(v_unused_1656_);
v___x_1650_ = v___x_1648_;
v_isShared_1651_ = v_isSharedCheck_1655_;
goto v_resetjp_1649_;
}
else
{
lean_dec(v___x_1648_);
v___x_1650_ = lean_box(0);
v_isShared_1651_ = v_isSharedCheck_1655_;
goto v_resetjp_1649_;
}
v_resetjp_1649_:
{
lean_object* v___x_1653_; 
if (v_isShared_1651_ == 0)
{
lean_ctor_set(v___x_1650_, 0, v___x_1647_);
v___x_1653_ = v___x_1650_;
goto v_reusejp_1652_;
}
else
{
lean_object* v_reuseFailAlloc_1654_; 
v_reuseFailAlloc_1654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1654_, 0, v___x_1647_);
v___x_1653_ = v_reuseFailAlloc_1654_;
goto v_reusejp_1652_;
}
v_reusejp_1652_:
{
return v___x_1653_;
}
}
}
else
{
return v___x_1648_;
}
}
else
{
lean_object* v_a_1657_; lean_object* v___x_1659_; uint8_t v_isShared_1660_; uint8_t v_isSharedCheck_1664_; 
v_a_1657_ = lean_ctor_get(v___x_1643_, 0);
v_isSharedCheck_1664_ = !lean_is_exclusive(v___x_1643_);
if (v_isSharedCheck_1664_ == 0)
{
v___x_1659_ = v___x_1643_;
v_isShared_1660_ = v_isSharedCheck_1664_;
goto v_resetjp_1658_;
}
else
{
lean_inc(v_a_1657_);
lean_dec(v___x_1643_);
v___x_1659_ = lean_box(0);
v_isShared_1660_ = v_isSharedCheck_1664_;
goto v_resetjp_1658_;
}
v_resetjp_1658_:
{
lean_object* v___x_1662_; 
if (v_isShared_1660_ == 0)
{
v___x_1662_ = v___x_1659_;
goto v_reusejp_1661_;
}
else
{
lean_object* v_reuseFailAlloc_1663_; 
v_reuseFailAlloc_1663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1663_, 0, v_a_1657_);
v___x_1662_ = v_reuseFailAlloc_1663_;
goto v_reusejp_1661_;
}
v_reusejp_1661_:
{
return v___x_1662_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1632_ = stack[0].m_obj;
lean_object* v_a_1633_ = stack[1].m_obj;
lean_object* v_a_1634_ = stack[2].m_obj;
lean_object* v_a_1635_ = stack[3].m_obj;
lean_object* v_a_1636_ = stack[4].m_obj;
lean_object* v_a_1637_ = stack[5].m_obj;
lean_object* v_a_1638_ = stack[6].m_obj;
lean_object* v_a_1639_ = stack[7].m_obj;
lean_object* v_a_1640_ = stack[8].m_obj;
lean_object* v_a_1641_ = stack[9].m_obj;
lean_object* v_res_1665_;
v_res_1665_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq(v_a_1632_, v_a_1633_, v_a_1634_, v_a_1635_, v_a_1636_, v_a_1637_, v_a_1638_, v_a_1639_, v_a_1640_, v_a_1641_);
stack->m_obj
 = v_res_1665_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq___boxed(lean_object* v_a_1666_, lean_object* v_a_1667_, lean_object* v_a_1668_, lean_object* v_a_1669_, lean_object* v_a_1670_, lean_object* v_a_1671_, lean_object* v_a_1672_, lean_object* v_a_1673_, lean_object* v_a_1674_, lean_object* v_a_1675_, lean_object* v_a_1676_){
_start:
{
lean_object* v_res_1677_; 
v_res_1677_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq(v_a_1666_, v_a_1667_, v_a_1668_, v_a_1669_, v_a_1670_, v_a_1671_, v_a_1672_, v_a_1673_, v_a_1674_, v_a_1675_);
lean_dec(v_a_1675_);
lean_dec_ref(v_a_1674_);
lean_dec(v_a_1673_);
lean_dec_ref(v_a_1672_);
lean_dec(v_a_1671_);
lean_dec_ref(v_a_1670_);
lean_dec(v_a_1669_);
lean_dec_ref(v_a_1668_);
lean_dec(v_a_1667_);
lean_dec(v_a_1666_);
return v_res_1677_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0(lean_object* v_upperBound_1678_, lean_object* v_a_1679_, lean_object* v___x_1680_, lean_object* v_inst_1681_, lean_object* v_R_1682_, lean_object* v_a_1683_, lean_object* v_b_1684_, lean_object* v_c_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_){
_start:
{
lean_object* v___x_1697_; 
v___x_1697_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg(v_upperBound_1678_, v_a_1679_, v___x_1680_, v_a_1683_, v_b_1684_, v___y_1686_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_, v___y_1693_, v___y_1694_, v___y_1695_);
return v___x_1697_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_1678_ = stack[0].m_obj;
lean_object* v_a_1679_ = stack[1].m_obj;
lean_object* v___x_1680_ = stack[2].m_obj;
lean_object* v_a_1683_ = stack[5].m_obj;
lean_object* v_b_1684_ = stack[6].m_obj;
lean_object* v___y_1686_ = stack[8].m_obj;
lean_object* v___y_1687_ = stack[9].m_obj;
lean_object* v___y_1688_ = stack[10].m_obj;
lean_object* v___y_1689_ = stack[11].m_obj;
lean_object* v___y_1690_ = stack[12].m_obj;
lean_object* v___y_1691_ = stack[13].m_obj;
lean_object* v___y_1692_ = stack[14].m_obj;
lean_object* v___y_1693_ = stack[15].m_obj;
lean_object* v___y_1694_ = stack[16].m_obj;
lean_object* v___y_1695_ = stack[17].m_obj;
lean_object* v_res_1698_;
v_res_1698_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0(v_upperBound_1678_, v_a_1679_, v___x_1680_, lean_box(0), lean_box(0), v_a_1683_, v_b_1684_, lean_box(0), v___y_1686_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_, v___y_1693_, v___y_1694_, v___y_1695_);
stack->m_obj
 = v_res_1698_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___boxed(lean_object** _args){
lean_object* v_upperBound_1699_ = _args[0];
lean_object* v_a_1700_ = _args[1];
lean_object* v___x_1701_ = _args[2];
lean_object* v_inst_1702_ = _args[3];
lean_object* v_R_1703_ = _args[4];
lean_object* v_a_1704_ = _args[5];
lean_object* v_b_1705_ = _args[6];
lean_object* v_c_1706_ = _args[7];
lean_object* v___y_1707_ = _args[8];
lean_object* v___y_1708_ = _args[9];
lean_object* v___y_1709_ = _args[10];
lean_object* v___y_1710_ = _args[11];
lean_object* v___y_1711_ = _args[12];
lean_object* v___y_1712_ = _args[13];
lean_object* v___y_1713_ = _args[14];
lean_object* v___y_1714_ = _args[15];
lean_object* v___y_1715_ = _args[16];
lean_object* v___y_1716_ = _args[17];
lean_object* v___y_1717_ = _args[18];
_start:
{
lean_object* v_res_1718_; 
v_res_1718_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0(v_upperBound_1699_, v_a_1700_, v___x_1701_, v_inst_1702_, v_R_1703_, v_a_1704_, v_b_1705_, v_c_1706_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_, v___y_1715_, v___y_1716_);
lean_dec(v___y_1716_);
lean_dec_ref(v___y_1715_);
lean_dec(v___y_1714_);
lean_dec_ref(v___y_1713_);
lean_dec(v___y_1712_);
lean_dec_ref(v___y_1711_);
lean_dec(v___y_1710_);
lean_dec_ref(v___y_1709_);
lean_dec(v___y_1708_);
lean_dec(v___y_1707_);
lean_dec_ref(v___x_1701_);
lean_dec_ref(v_a_1700_);
lean_dec(v_upperBound_1699_);
return v_res_1718_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__1(lean_object* v_upperBound_1719_, lean_object* v___x_1720_, lean_object* v_a_1721_, lean_object* v_inst_1722_, lean_object* v_R_1723_, lean_object* v_a_1724_, lean_object* v_b_1725_, lean_object* v_c_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_){
_start:
{
lean_object* v___x_1738_; 
v___x_1738_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__1___redArg(v_upperBound_1719_, v___x_1720_, v_a_1721_, v_a_1724_, v_b_1725_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_);
return v___x_1738_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_1719_ = stack[0].m_obj;
lean_object* v___x_1720_ = stack[1].m_obj;
lean_object* v_a_1721_ = stack[2].m_obj;
lean_object* v_a_1724_ = stack[5].m_obj;
lean_object* v_b_1725_ = stack[6].m_obj;
lean_object* v___y_1727_ = stack[8].m_obj;
lean_object* v___y_1728_ = stack[9].m_obj;
lean_object* v___y_1729_ = stack[10].m_obj;
lean_object* v___y_1730_ = stack[11].m_obj;
lean_object* v___y_1731_ = stack[12].m_obj;
lean_object* v___y_1732_ = stack[13].m_obj;
lean_object* v___y_1733_ = stack[14].m_obj;
lean_object* v___y_1734_ = stack[15].m_obj;
lean_object* v___y_1735_ = stack[16].m_obj;
lean_object* v___y_1736_ = stack[17].m_obj;
lean_object* v_res_1739_;
v_res_1739_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__1(v_upperBound_1719_, v___x_1720_, v_a_1721_, lean_box(0), lean_box(0), v_a_1724_, v_b_1725_, lean_box(0), v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_);
stack->m_obj
 = v_res_1739_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__1___boxed(lean_object** _args){
lean_object* v_upperBound_1740_ = _args[0];
lean_object* v___x_1741_ = _args[1];
lean_object* v_a_1742_ = _args[2];
lean_object* v_inst_1743_ = _args[3];
lean_object* v_R_1744_ = _args[4];
lean_object* v_a_1745_ = _args[5];
lean_object* v_b_1746_ = _args[6];
lean_object* v_c_1747_ = _args[7];
lean_object* v___y_1748_ = _args[8];
lean_object* v___y_1749_ = _args[9];
lean_object* v___y_1750_ = _args[10];
lean_object* v___y_1751_ = _args[11];
lean_object* v___y_1752_ = _args[12];
lean_object* v___y_1753_ = _args[13];
lean_object* v___y_1754_ = _args[14];
lean_object* v___y_1755_ = _args[15];
lean_object* v___y_1756_ = _args[16];
lean_object* v___y_1757_ = _args[17];
lean_object* v___y_1758_ = _args[18];
_start:
{
lean_object* v_res_1759_; 
v_res_1759_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__1(v_upperBound_1740_, v___x_1741_, v_a_1742_, v_inst_1743_, v_R_1744_, v_a_1745_, v_b_1746_, v_c_1747_, v___y_1748_, v___y_1749_, v___y_1750_, v___y_1751_, v___y_1752_, v___y_1753_, v___y_1754_, v___y_1755_, v___y_1756_, v___y_1757_);
lean_dec(v___y_1757_);
lean_dec_ref(v___y_1756_);
lean_dec(v___y_1755_);
lean_dec_ref(v___y_1754_);
lean_dec(v___y_1753_);
lean_dec_ref(v___y_1752_);
lean_dec(v___y_1751_);
lean_dec_ref(v___y_1750_);
lean_dec(v___y_1749_);
lean_dec(v___y_1748_);
lean_dec_ref(v_a_1742_);
lean_dec(v___x_1741_);
lean_dec(v_upperBound_1740_);
return v_res_1759_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1760_; double v___x_1761_; 
v___x_1760_ = lean_unsigned_to_nat(0u);
v___x_1761_ = lean_float_of_nat(v___x_1760_);
return v___x_1761_;
}
}
lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__0___redArg(lean_object* v_cls_1765_, lean_object* v_msg_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_){
_start:
{
lean_object* v_ref_1772_; lean_object* v___x_1773_; lean_object* v_a_1774_; lean_object* v___x_1776_; uint8_t v_isShared_1777_; uint8_t v_isSharedCheck_1819_; 
v_ref_1772_ = lean_ctor_get(v___y_1769_, 2);
v___x_1773_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__1_spec__1(v_msg_1766_, v___y_1767_, v___y_1768_, v___y_1769_, v___y_1770_);
v_a_1774_ = lean_ctor_get(v___x_1773_, 0);
v_isSharedCheck_1819_ = !lean_is_exclusive(v___x_1773_);
if (v_isSharedCheck_1819_ == 0)
{
v___x_1776_ = v___x_1773_;
v_isShared_1777_ = v_isSharedCheck_1819_;
goto v_resetjp_1775_;
}
else
{
lean_inc(v_a_1774_);
lean_dec(v___x_1773_);
v___x_1776_ = lean_box(0);
v_isShared_1777_ = v_isSharedCheck_1819_;
goto v_resetjp_1775_;
}
v_resetjp_1775_:
{
lean_object* v___x_1778_; lean_object* v_traceState_1779_; lean_object* v_env_1780_; lean_object* v_nextMacroScope_1781_; lean_object* v_ngen_1782_; lean_object* v_auxDeclNGen_1783_; lean_object* v_cache_1784_; lean_object* v_recordedDeps_1785_; lean_object* v_messages_1786_; lean_object* v_infoState_1787_; lean_object* v_snapshotTasks_1788_; lean_object* v___x_1790_; uint8_t v_isShared_1791_; uint8_t v_isSharedCheck_1818_; 
v___x_1778_ = lean_st_ref_take(v___y_1770_);
v_traceState_1779_ = lean_ctor_get(v___x_1778_, 4);
v_env_1780_ = lean_ctor_get(v___x_1778_, 0);
v_nextMacroScope_1781_ = lean_ctor_get(v___x_1778_, 1);
v_ngen_1782_ = lean_ctor_get(v___x_1778_, 2);
v_auxDeclNGen_1783_ = lean_ctor_get(v___x_1778_, 3);
v_cache_1784_ = lean_ctor_get(v___x_1778_, 5);
v_recordedDeps_1785_ = lean_ctor_get(v___x_1778_, 6);
v_messages_1786_ = lean_ctor_get(v___x_1778_, 7);
v_infoState_1787_ = lean_ctor_get(v___x_1778_, 8);
v_snapshotTasks_1788_ = lean_ctor_get(v___x_1778_, 9);
v_isSharedCheck_1818_ = !lean_is_exclusive(v___x_1778_);
if (v_isSharedCheck_1818_ == 0)
{
v___x_1790_ = v___x_1778_;
v_isShared_1791_ = v_isSharedCheck_1818_;
goto v_resetjp_1789_;
}
else
{
lean_inc(v_snapshotTasks_1788_);
lean_inc(v_infoState_1787_);
lean_inc(v_messages_1786_);
lean_inc(v_recordedDeps_1785_);
lean_inc(v_cache_1784_);
lean_inc(v_traceState_1779_);
lean_inc(v_auxDeclNGen_1783_);
lean_inc(v_ngen_1782_);
lean_inc(v_nextMacroScope_1781_);
lean_inc(v_env_1780_);
lean_dec(v___x_1778_);
v___x_1790_ = lean_box(0);
v_isShared_1791_ = v_isSharedCheck_1818_;
goto v_resetjp_1789_;
}
v_resetjp_1789_:
{
uint64_t v_tid_1792_; lean_object* v_traces_1793_; lean_object* v___x_1795_; uint8_t v_isShared_1796_; uint8_t v_isSharedCheck_1817_; 
v_tid_1792_ = lean_ctor_get_uint64(v_traceState_1779_, sizeof(void*)*1);
v_traces_1793_ = lean_ctor_get(v_traceState_1779_, 0);
v_isSharedCheck_1817_ = !lean_is_exclusive(v_traceState_1779_);
if (v_isSharedCheck_1817_ == 0)
{
v___x_1795_ = v_traceState_1779_;
v_isShared_1796_ = v_isSharedCheck_1817_;
goto v_resetjp_1794_;
}
else
{
lean_inc(v_traces_1793_);
lean_dec(v_traceState_1779_);
v___x_1795_ = lean_box(0);
v_isShared_1796_ = v_isSharedCheck_1817_;
goto v_resetjp_1794_;
}
v_resetjp_1794_:
{
lean_object* v___x_1797_; lean_object* v___x_1798_; double v___x_1799_; uint8_t v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1808_; 
v___x_1797_ = lean_box(0);
v___x_1798_ = lean_box(0);
v___x_1799_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__0___redArg___closed__0);
v___x_1800_ = 0;
v___x_1801_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__0___redArg___closed__1));
v___x_1802_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1802_, 0, v_cls_1765_);
lean_ctor_set(v___x_1802_, 1, v___x_1798_);
lean_ctor_set(v___x_1802_, 2, v___x_1801_);
lean_ctor_set_float(v___x_1802_, sizeof(void*)*3, v___x_1799_);
lean_ctor_set_float(v___x_1802_, sizeof(void*)*3 + 8, v___x_1799_);
lean_ctor_set_uint8(v___x_1802_, sizeof(void*)*3 + 16, v___x_1800_);
v___x_1803_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__0___redArg___closed__2));
v___x_1804_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1804_, 0, v___x_1802_);
lean_ctor_set(v___x_1804_, 1, v_a_1774_);
lean_ctor_set(v___x_1804_, 2, v___x_1803_);
lean_inc(v_ref_1772_);
v___x_1805_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1805_, 0, v_ref_1772_);
lean_ctor_set(v___x_1805_, 1, v___x_1804_);
v___x_1806_ = l_Lean_PersistentArray_push___redArg(v_traces_1793_, v___x_1805_);
if (v_isShared_1796_ == 0)
{
lean_ctor_set(v___x_1795_, 0, v___x_1806_);
v___x_1808_ = v___x_1795_;
goto v_reusejp_1807_;
}
else
{
lean_object* v_reuseFailAlloc_1816_; 
v_reuseFailAlloc_1816_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1816_, 0, v___x_1806_);
lean_ctor_set_uint64(v_reuseFailAlloc_1816_, sizeof(void*)*1, v_tid_1792_);
v___x_1808_ = v_reuseFailAlloc_1816_;
goto v_reusejp_1807_;
}
v_reusejp_1807_:
{
lean_object* v___x_1810_; 
if (v_isShared_1791_ == 0)
{
lean_ctor_set(v___x_1790_, 4, v___x_1808_);
v___x_1810_ = v___x_1790_;
goto v_reusejp_1809_;
}
else
{
lean_object* v_reuseFailAlloc_1815_; 
v_reuseFailAlloc_1815_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1815_, 0, v_env_1780_);
lean_ctor_set(v_reuseFailAlloc_1815_, 1, v_nextMacroScope_1781_);
lean_ctor_set(v_reuseFailAlloc_1815_, 2, v_ngen_1782_);
lean_ctor_set(v_reuseFailAlloc_1815_, 3, v_auxDeclNGen_1783_);
lean_ctor_set(v_reuseFailAlloc_1815_, 4, v___x_1808_);
lean_ctor_set(v_reuseFailAlloc_1815_, 5, v_cache_1784_);
lean_ctor_set(v_reuseFailAlloc_1815_, 6, v_recordedDeps_1785_);
lean_ctor_set(v_reuseFailAlloc_1815_, 7, v_messages_1786_);
lean_ctor_set(v_reuseFailAlloc_1815_, 8, v_infoState_1787_);
lean_ctor_set(v_reuseFailAlloc_1815_, 9, v_snapshotTasks_1788_);
v___x_1810_ = v_reuseFailAlloc_1815_;
goto v_reusejp_1809_;
}
v_reusejp_1809_:
{
lean_object* v___x_1811_; lean_object* v___x_1813_; 
v___x_1811_ = lean_st_ref_put(v___y_1770_, v___x_1810_);
if (v_isShared_1777_ == 0)
{
lean_ctor_set(v___x_1776_, 0, v___x_1797_);
v___x_1813_ = v___x_1776_;
goto v_reusejp_1812_;
}
else
{
lean_object* v_reuseFailAlloc_1814_; 
v_reuseFailAlloc_1814_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1814_, 0, v___x_1797_);
v___x_1813_ = v_reuseFailAlloc_1814_;
goto v_reusejp_1812_;
}
v_reusejp_1812_:
{
return v___x_1813_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_1765_ = stack[0].m_obj;
lean_object* v_msg_1766_ = stack[1].m_obj;
lean_object* v___y_1767_ = stack[2].m_obj;
lean_object* v___y_1768_ = stack[3].m_obj;
lean_object* v___y_1769_ = stack[4].m_obj;
lean_object* v___y_1770_ = stack[5].m_obj;
lean_object* v_res_1820_;
v_res_1820_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__0___redArg(v_cls_1765_, v_msg_1766_, v___y_1767_, v___y_1768_, v___y_1769_, v___y_1770_);
stack->m_obj
 = v_res_1820_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__0___redArg___boxed(lean_object* v_cls_1821_, lean_object* v_msg_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_){
_start:
{
lean_object* v_res_1828_; 
v_res_1828_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__0___redArg(v_cls_1821_, v_msg_1822_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_);
lean_dec(v___y_1826_);
lean_dec_ref(v___y_1825_);
lean_dec(v___y_1824_);
lean_dec_ref(v___y_1823_);
return v_res_1828_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__6(void){
_start:
{
lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; 
v___x_1839_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__3));
v___x_1840_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__5));
v___x_1841_ = l_Lean_Name_append(v___x_1840_, v___x_1839_);
return v___x_1841_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__8(void){
_start:
{
lean_object* v___x_1843_; lean_object* v___x_1844_; 
v___x_1843_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__7));
v___x_1844_ = l_Lean_stringToMessageData(v___x_1843_);
return v___x_1844_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__10(void){
_start:
{
lean_object* v___x_1846_; lean_object* v___x_1847_; 
v___x_1846_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__9));
v___x_1847_ = l_Lean_stringToMessageData(v___x_1846_);
return v___x_1847_;
}
}
lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg(lean_object* v_a_1848_, lean_object* v_as_x27_1849_, lean_object* v_b_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_){
_start:
{
if (lean_obj_tag(v_as_x27_1849_) == 0)
{
lean_object* v___x_1862_; 
lean_dec_ref(v_a_1848_);
v___x_1862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1862_, 0, v_b_1850_);
return v___x_1862_;
}
else
{
lean_object* v_head_1863_; lean_object* v_tail_1864_; lean_object* v___x_1865_; size_t v___x_1866_; size_t v___x_1867_; uint8_t v___x_1868_; 
v_head_1863_ = lean_ctor_get(v_as_x27_1849_, 0);
v_tail_1864_ = lean_ctor_get(v_as_x27_1849_, 1);
v___x_1865_ = lean_box(0);
v___x_1866_ = lean_ptr_addr(v_a_1848_);
v___x_1867_ = lean_ptr_addr(v_head_1863_);
v___x_1868_ = lean_usize_dec_eq(v___x_1866_, v___x_1867_);
if (v___x_1868_ == 0)
{
lean_object* v___x_1869_; 
lean_inc(v_head_1863_);
lean_inc_ref(v_a_1848_);
v___x_1869_ = l_Lean_Meta_Grind_mkEqHEqProof(v_a_1848_, v_head_1863_, v___y_1851_, v___y_1852_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_, v___y_1858_, v___y_1859_, v___y_1860_);
if (lean_obj_tag(v___x_1869_) == 0)
{
lean_object* v_toCold_1870_; lean_object* v_options_1871_; lean_object* v_a_1872_; lean_object* v_inheritedTraceOptions_1873_; uint8_t v_hasTrace_1874_; lean_object* v___x_1875_; lean_object* v___y_1877_; lean_object* v___y_1878_; lean_object* v___y_1879_; lean_object* v___y_1880_; lean_object* v___y_1881_; lean_object* v___y_1882_; lean_object* v___y_1883_; lean_object* v___y_1884_; lean_object* v___y_1885_; lean_object* v___y_1886_; 
v_toCold_1870_ = lean_ctor_get(v___y_1859_, 0);
v_options_1871_ = lean_ctor_get(v_toCold_1870_, 2);
v_a_1872_ = lean_ctor_get(v___x_1869_, 0);
lean_inc(v_a_1872_);
lean_dec_ref_known(v___x_1869_, 1);
v_inheritedTraceOptions_1873_ = lean_ctor_get(v_toCold_1870_, 11);
v_hasTrace_1874_ = lean_ctor_get_uint8(v_options_1871_, sizeof(void*)*1);
v___x_1875_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__3));
if (v_hasTrace_1874_ == 0)
{
v___y_1877_ = v___y_1851_;
v___y_1878_ = v___y_1852_;
v___y_1879_ = v___y_1853_;
v___y_1880_ = v___y_1854_;
v___y_1881_ = v___y_1855_;
v___y_1882_ = v___y_1856_;
v___y_1883_ = v___y_1857_;
v___y_1884_ = v___y_1858_;
v___y_1885_ = v___y_1859_;
v___y_1886_ = v___y_1860_;
goto v___jp_1876_;
}
else
{
lean_object* v___x_1913_; uint8_t v___x_1914_; 
v___x_1913_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__6, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__6_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__6);
v___x_1914_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1873_, v_options_1871_, v___x_1913_);
if (v___x_1914_ == 0)
{
v___y_1877_ = v___y_1851_;
v___y_1878_ = v___y_1852_;
v___y_1879_ = v___y_1853_;
v___y_1880_ = v___y_1854_;
v___y_1881_ = v___y_1855_;
v___y_1882_ = v___y_1856_;
v___y_1883_ = v___y_1857_;
v___y_1884_ = v___y_1858_;
v___y_1885_ = v___y_1859_;
v___y_1886_ = v___y_1860_;
goto v___jp_1876_;
}
else
{
lean_object* v___x_1915_; 
v___x_1915_ = l_Lean_Meta_Grind_updateLastTag(v___y_1851_, v___y_1852_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_, v___y_1858_, v___y_1859_, v___y_1860_);
if (lean_obj_tag(v___x_1915_) == 0)
{
lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; 
lean_dec_ref_known(v___x_1915_, 1);
lean_inc_ref(v_a_1848_);
v___x_1916_ = l_Lean_MessageData_ofExpr(v_a_1848_);
v___x_1917_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__10, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__10_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__10);
v___x_1918_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1918_, 0, v___x_1916_);
lean_ctor_set(v___x_1918_, 1, v___x_1917_);
lean_inc(v_head_1863_);
v___x_1919_ = l_Lean_MessageData_ofExpr(v_head_1863_);
v___x_1920_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1920_, 0, v___x_1918_);
lean_ctor_set(v___x_1920_, 1, v___x_1919_);
v___x_1921_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__0___redArg(v___x_1875_, v___x_1920_, v___y_1857_, v___y_1858_, v___y_1859_, v___y_1860_);
if (lean_obj_tag(v___x_1921_) == 0)
{
lean_dec_ref_known(v___x_1921_, 1);
v___y_1877_ = v___y_1851_;
v___y_1878_ = v___y_1852_;
v___y_1879_ = v___y_1853_;
v___y_1880_ = v___y_1854_;
v___y_1881_ = v___y_1855_;
v___y_1882_ = v___y_1856_;
v___y_1883_ = v___y_1857_;
v___y_1884_ = v___y_1858_;
v___y_1885_ = v___y_1859_;
v___y_1886_ = v___y_1860_;
goto v___jp_1876_;
}
else
{
lean_dec(v_a_1872_);
lean_dec_ref(v_a_1848_);
return v___x_1921_;
}
}
else
{
lean_dec(v_a_1872_);
lean_dec_ref(v_a_1848_);
return v___x_1915_;
}
}
}
v___jp_1876_:
{
uint8_t v___x_1887_; lean_object* v___x_1888_; 
v___x_1887_ = 0;
lean_inc(v_a_1872_);
v___x_1888_ = l_Lean_Meta_check(v_a_1872_, v___x_1887_, v___y_1883_, v___y_1884_, v___y_1885_, v___y_1886_);
if (lean_obj_tag(v___x_1888_) == 0)
{
lean_object* v_toCold_1889_; lean_object* v_options_1890_; uint8_t v_hasTrace_1891_; 
lean_dec_ref_known(v___x_1888_, 1);
v_toCold_1889_ = lean_ctor_get(v___y_1885_, 0);
v_options_1890_ = lean_ctor_get(v_toCold_1889_, 2);
v_hasTrace_1891_ = lean_ctor_get_uint8(v_options_1890_, sizeof(void*)*1);
if (v_hasTrace_1891_ == 0)
{
lean_dec(v_a_1872_);
v_as_x27_1849_ = v_tail_1864_;
v_b_1850_ = v___x_1865_;
goto _start;
}
else
{
lean_object* v_inheritedTraceOptions_1893_; lean_object* v___x_1894_; uint8_t v___x_1895_; 
v_inheritedTraceOptions_1893_ = lean_ctor_get(v_toCold_1889_, 11);
v___x_1894_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__6, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__6_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__6);
v___x_1895_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1893_, v_options_1890_, v___x_1894_);
if (v___x_1895_ == 0)
{
lean_dec(v_a_1872_);
v_as_x27_1849_ = v_tail_1864_;
v_b_1850_ = v___x_1865_;
goto _start;
}
else
{
lean_object* v___x_1897_; 
v___x_1897_ = l_Lean_Meta_Grind_updateLastTag(v___y_1877_, v___y_1878_, v___y_1879_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_, v___y_1886_);
if (lean_obj_tag(v___x_1897_) == 0)
{
lean_object* v___x_1898_; 
lean_dec_ref_known(v___x_1897_, 1);
lean_inc(v___y_1886_);
lean_inc_ref(v___y_1885_);
lean_inc(v___y_1884_);
lean_inc_ref(v___y_1883_);
v___x_1898_ = lean_infer_type(v_a_1872_, v___y_1883_, v___y_1884_, v___y_1885_, v___y_1886_);
if (lean_obj_tag(v___x_1898_) == 0)
{
lean_object* v_a_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; 
v_a_1899_ = lean_ctor_get(v___x_1898_, 0);
lean_inc(v_a_1899_);
lean_dec_ref_known(v___x_1898_, 1);
v___x_1900_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__8, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__8_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__8);
v___x_1901_ = l_Lean_MessageData_ofExpr(v_a_1899_);
v___x_1902_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1902_, 0, v___x_1900_);
lean_ctor_set(v___x_1902_, 1, v___x_1901_);
v___x_1903_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__0___redArg(v___x_1875_, v___x_1902_, v___y_1883_, v___y_1884_, v___y_1885_, v___y_1886_);
if (lean_obj_tag(v___x_1903_) == 0)
{
lean_dec_ref_known(v___x_1903_, 1);
v_as_x27_1849_ = v_tail_1864_;
v_b_1850_ = v___x_1865_;
goto _start;
}
else
{
lean_dec_ref(v_a_1848_);
return v___x_1903_;
}
}
else
{
lean_object* v_a_1905_; lean_object* v___x_1907_; uint8_t v_isShared_1908_; uint8_t v_isSharedCheck_1912_; 
lean_dec_ref(v_a_1848_);
v_a_1905_ = lean_ctor_get(v___x_1898_, 0);
v_isSharedCheck_1912_ = !lean_is_exclusive(v___x_1898_);
if (v_isSharedCheck_1912_ == 0)
{
v___x_1907_ = v___x_1898_;
v_isShared_1908_ = v_isSharedCheck_1912_;
goto v_resetjp_1906_;
}
else
{
lean_inc(v_a_1905_);
lean_dec(v___x_1898_);
v___x_1907_ = lean_box(0);
v_isShared_1908_ = v_isSharedCheck_1912_;
goto v_resetjp_1906_;
}
v_resetjp_1906_:
{
lean_object* v___x_1910_; 
if (v_isShared_1908_ == 0)
{
v___x_1910_ = v___x_1907_;
goto v_reusejp_1909_;
}
else
{
lean_object* v_reuseFailAlloc_1911_; 
v_reuseFailAlloc_1911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1911_, 0, v_a_1905_);
v___x_1910_ = v_reuseFailAlloc_1911_;
goto v_reusejp_1909_;
}
v_reusejp_1909_:
{
return v___x_1910_;
}
}
}
}
else
{
lean_dec(v_a_1872_);
lean_dec_ref(v_a_1848_);
return v___x_1897_;
}
}
}
}
else
{
lean_dec(v_a_1872_);
lean_dec_ref(v_a_1848_);
return v___x_1888_;
}
}
}
else
{
lean_object* v_a_1922_; lean_object* v___x_1924_; uint8_t v_isShared_1925_; uint8_t v_isSharedCheck_1929_; 
lean_dec_ref(v_a_1848_);
v_a_1922_ = lean_ctor_get(v___x_1869_, 0);
v_isSharedCheck_1929_ = !lean_is_exclusive(v___x_1869_);
if (v_isSharedCheck_1929_ == 0)
{
v___x_1924_ = v___x_1869_;
v_isShared_1925_ = v_isSharedCheck_1929_;
goto v_resetjp_1923_;
}
else
{
lean_inc(v_a_1922_);
lean_dec(v___x_1869_);
v___x_1924_ = lean_box(0);
v_isShared_1925_ = v_isSharedCheck_1929_;
goto v_resetjp_1923_;
}
v_resetjp_1923_:
{
lean_object* v___x_1927_; 
if (v_isShared_1925_ == 0)
{
v___x_1927_ = v___x_1924_;
goto v_reusejp_1926_;
}
else
{
lean_object* v_reuseFailAlloc_1928_; 
v_reuseFailAlloc_1928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1928_, 0, v_a_1922_);
v___x_1927_ = v_reuseFailAlloc_1928_;
goto v_reusejp_1926_;
}
v_reusejp_1926_:
{
return v___x_1927_;
}
}
}
}
else
{
v_as_x27_1849_ = v_tail_1864_;
v_b_1850_ = v___x_1865_;
goto _start;
}
}
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1848_ = stack[0].m_obj;
lean_object* v_as_x27_1849_ = stack[1].m_obj;
lean_object* v_b_1850_ = stack[2].m_obj;
lean_object* v___y_1851_ = stack[3].m_obj;
lean_object* v___y_1852_ = stack[4].m_obj;
lean_object* v___y_1853_ = stack[5].m_obj;
lean_object* v___y_1854_ = stack[6].m_obj;
lean_object* v___y_1855_ = stack[7].m_obj;
lean_object* v___y_1856_ = stack[8].m_obj;
lean_object* v___y_1857_ = stack[9].m_obj;
lean_object* v___y_1858_ = stack[10].m_obj;
lean_object* v___y_1859_ = stack[11].m_obj;
lean_object* v___y_1860_ = stack[12].m_obj;
lean_object* v_res_1931_;
v_res_1931_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg(v_a_1848_, v_as_x27_1849_, v_b_1850_, v___y_1851_, v___y_1852_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_, v___y_1858_, v___y_1859_, v___y_1860_);
stack->m_obj
 = v_res_1931_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___boxed(lean_object* v_a_1932_, lean_object* v_as_x27_1933_, lean_object* v_b_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_){
_start:
{
lean_object* v_res_1946_; 
v_res_1946_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg(v_a_1932_, v_as_x27_1933_, v_b_1934_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_, v___y_1944_);
lean_dec(v___y_1944_);
lean_dec_ref(v___y_1943_);
lean_dec(v___y_1942_);
lean_dec_ref(v___y_1941_);
lean_dec(v___y_1940_);
lean_dec_ref(v___y_1939_);
lean_dec(v___y_1938_);
lean_dec_ref(v___y_1937_);
lean_dec(v___y_1936_);
lean_dec(v___y_1935_);
lean_dec(v_as_x27_1933_);
return v_res_1946_;
}
}
lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__2___redArg(lean_object* v_a_1947_, lean_object* v_as_x27_1948_, lean_object* v_b_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_){
_start:
{
if (lean_obj_tag(v_as_x27_1948_) == 0)
{
lean_object* v___x_1961_; 
v___x_1961_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1961_, 0, v_b_1949_);
return v___x_1961_;
}
else
{
lean_object* v_head_1962_; lean_object* v_tail_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; 
v_head_1962_ = lean_ctor_get(v_as_x27_1948_, 0);
v_tail_1963_ = lean_ctor_get(v_as_x27_1948_, 1);
v___x_1964_ = lean_box(0);
lean_inc(v_head_1962_);
v___x_1965_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg(v_head_1962_, v_a_1947_, v___x_1964_, v___y_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_);
if (lean_obj_tag(v___x_1965_) == 0)
{
lean_dec_ref_known(v___x_1965_, 1);
v_as_x27_1948_ = v_tail_1963_;
v_b_1949_ = v___x_1964_;
goto _start;
}
else
{
return v___x_1965_;
}
}
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1947_ = stack[0].m_obj;
lean_object* v_as_x27_1948_ = stack[1].m_obj;
lean_object* v_b_1949_ = stack[2].m_obj;
lean_object* v___y_1950_ = stack[3].m_obj;
lean_object* v___y_1951_ = stack[4].m_obj;
lean_object* v___y_1952_ = stack[5].m_obj;
lean_object* v___y_1953_ = stack[6].m_obj;
lean_object* v___y_1954_ = stack[7].m_obj;
lean_object* v___y_1955_ = stack[8].m_obj;
lean_object* v___y_1956_ = stack[9].m_obj;
lean_object* v___y_1957_ = stack[10].m_obj;
lean_object* v___y_1958_ = stack[11].m_obj;
lean_object* v___y_1959_ = stack[12].m_obj;
lean_object* v_res_1967_;
v_res_1967_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__2___redArg(v_a_1947_, v_as_x27_1948_, v_b_1949_, v___y_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_);
stack->m_obj
 = v_res_1967_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__2___redArg___boxed(lean_object* v_a_1968_, lean_object* v_as_x27_1969_, lean_object* v_b_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_){
_start:
{
lean_object* v_res_1982_; 
v_res_1982_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__2___redArg(v_a_1968_, v_as_x27_1969_, v_b_1970_, v___y_1971_, v___y_1972_, v___y_1973_, v___y_1974_, v___y_1975_, v___y_1976_, v___y_1977_, v___y_1978_, v___y_1979_, v___y_1980_);
lean_dec(v___y_1980_);
lean_dec_ref(v___y_1979_);
lean_dec(v___y_1978_);
lean_dec_ref(v___y_1977_);
lean_dec(v___y_1976_);
lean_dec_ref(v___y_1975_);
lean_dec(v___y_1974_);
lean_dec_ref(v___y_1973_);
lean_dec(v___y_1972_);
lean_dec(v___y_1971_);
lean_dec(v_as_x27_1969_);
lean_dec(v_a_1968_);
return v_res_1982_;
}
}
lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__3___redArg(lean_object* v_as_x27_1983_, lean_object* v_b_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_){
_start:
{
if (lean_obj_tag(v_as_x27_1983_) == 0)
{
lean_object* v___x_1996_; 
v___x_1996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1996_, 0, v_b_1984_);
return v___x_1996_;
}
else
{
lean_object* v_head_1997_; lean_object* v_tail_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; 
v_head_1997_ = lean_ctor_get(v_as_x27_1983_, 0);
v_tail_1998_ = lean_ctor_get(v_as_x27_1983_, 1);
v___x_1999_ = lean_box(0);
v___x_2000_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__2___redArg(v_head_1997_, v_head_1997_, v___x_1999_, v___y_1985_, v___y_1986_, v___y_1987_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_, v___y_1994_);
if (lean_obj_tag(v___x_2000_) == 0)
{
lean_dec_ref_known(v___x_2000_, 1);
v_as_x27_1983_ = v_tail_1998_;
v_b_1984_ = v___x_1999_;
goto _start;
}
else
{
return v___x_2000_;
}
}
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_x27_1983_ = stack[0].m_obj;
lean_object* v_b_1984_ = stack[1].m_obj;
lean_object* v___y_1985_ = stack[2].m_obj;
lean_object* v___y_1986_ = stack[3].m_obj;
lean_object* v___y_1987_ = stack[4].m_obj;
lean_object* v___y_1988_ = stack[5].m_obj;
lean_object* v___y_1989_ = stack[6].m_obj;
lean_object* v___y_1990_ = stack[7].m_obj;
lean_object* v___y_1991_ = stack[8].m_obj;
lean_object* v___y_1992_ = stack[9].m_obj;
lean_object* v___y_1993_ = stack[10].m_obj;
lean_object* v___y_1994_ = stack[11].m_obj;
lean_object* v_res_2002_;
v_res_2002_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__3___redArg(v_as_x27_1983_, v_b_1984_, v___y_1985_, v___y_1986_, v___y_1987_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_, v___y_1994_);
stack->m_obj
 = v_res_2002_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__3___redArg___boxed(lean_object* v_as_x27_2003_, lean_object* v_b_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_){
_start:
{
lean_object* v_res_2016_; 
v_res_2016_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__3___redArg(v_as_x27_2003_, v_b_2004_, v___y_2005_, v___y_2006_, v___y_2007_, v___y_2008_, v___y_2009_, v___y_2010_, v___y_2011_, v___y_2012_, v___y_2013_, v___y_2014_);
lean_dec(v___y_2014_);
lean_dec_ref(v___y_2013_);
lean_dec(v___y_2012_);
lean_dec_ref(v___y_2011_);
lean_dec(v___y_2010_);
lean_dec_ref(v___y_2009_);
lean_dec(v___y_2008_);
lean_dec_ref(v___y_2007_);
lean_dec(v___y_2006_);
lean_dec(v___y_2005_);
lean_dec(v_as_x27_2003_);
return v_res_2016_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs(lean_object* v_a_2017_, lean_object* v_a_2018_, lean_object* v_a_2019_, lean_object* v_a_2020_, lean_object* v_a_2021_, lean_object* v_a_2022_, lean_object* v_a_2023_, lean_object* v_a_2024_, lean_object* v_a_2025_, lean_object* v_a_2026_){
_start:
{
lean_object* v___x_2028_; uint8_t v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; 
v___x_2028_ = lean_st_ref_get(v_a_2017_);
v___x_2029_ = 0;
v___x_2030_ = l_Lean_Meta_Grind_Goal_getEqcs(v___x_2028_, v___x_2029_);
lean_dec(v___x_2028_);
v___x_2031_ = lean_box(0);
v___x_2032_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__3___redArg(v___x_2030_, v___x_2031_, v_a_2017_, v_a_2018_, v_a_2019_, v_a_2020_, v_a_2021_, v_a_2022_, v_a_2023_, v_a_2024_, v_a_2025_, v_a_2026_);
lean_dec(v___x_2030_);
if (lean_obj_tag(v___x_2032_) == 0)
{
lean_object* v___x_2034_; uint8_t v_isShared_2035_; uint8_t v_isSharedCheck_2039_; 
v_isSharedCheck_2039_ = !lean_is_exclusive(v___x_2032_);
if (v_isSharedCheck_2039_ == 0)
{
lean_object* v_unused_2040_; 
v_unused_2040_ = lean_ctor_get(v___x_2032_, 0);
lean_dec(v_unused_2040_);
v___x_2034_ = v___x_2032_;
v_isShared_2035_ = v_isSharedCheck_2039_;
goto v_resetjp_2033_;
}
else
{
lean_dec(v___x_2032_);
v___x_2034_ = lean_box(0);
v_isShared_2035_ = v_isSharedCheck_2039_;
goto v_resetjp_2033_;
}
v_resetjp_2033_:
{
lean_object* v___x_2037_; 
if (v_isShared_2035_ == 0)
{
lean_ctor_set(v___x_2034_, 0, v___x_2031_);
v___x_2037_ = v___x_2034_;
goto v_reusejp_2036_;
}
else
{
lean_object* v_reuseFailAlloc_2038_; 
v_reuseFailAlloc_2038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2038_, 0, v___x_2031_);
v___x_2037_ = v_reuseFailAlloc_2038_;
goto v_reusejp_2036_;
}
v_reusejp_2036_:
{
return v___x_2037_;
}
}
}
else
{
return v___x_2032_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2017_ = stack[0].m_obj;
lean_object* v_a_2018_ = stack[1].m_obj;
lean_object* v_a_2019_ = stack[2].m_obj;
lean_object* v_a_2020_ = stack[3].m_obj;
lean_object* v_a_2021_ = stack[4].m_obj;
lean_object* v_a_2022_ = stack[5].m_obj;
lean_object* v_a_2023_ = stack[6].m_obj;
lean_object* v_a_2024_ = stack[7].m_obj;
lean_object* v_a_2025_ = stack[8].m_obj;
lean_object* v_a_2026_ = stack[9].m_obj;
lean_object* v_res_2041_;
v_res_2041_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs(v_a_2017_, v_a_2018_, v_a_2019_, v_a_2020_, v_a_2021_, v_a_2022_, v_a_2023_, v_a_2024_, v_a_2025_, v_a_2026_);
stack->m_obj
 = v_res_2041_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs___boxed(lean_object* v_a_2042_, lean_object* v_a_2043_, lean_object* v_a_2044_, lean_object* v_a_2045_, lean_object* v_a_2046_, lean_object* v_a_2047_, lean_object* v_a_2048_, lean_object* v_a_2049_, lean_object* v_a_2050_, lean_object* v_a_2051_, lean_object* v_a_2052_){
_start:
{
lean_object* v_res_2053_; 
v_res_2053_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs(v_a_2042_, v_a_2043_, v_a_2044_, v_a_2045_, v_a_2046_, v_a_2047_, v_a_2048_, v_a_2049_, v_a_2050_, v_a_2051_);
lean_dec(v_a_2051_);
lean_dec_ref(v_a_2050_);
lean_dec(v_a_2049_);
lean_dec_ref(v_a_2048_);
lean_dec(v_a_2047_);
lean_dec_ref(v_a_2046_);
lean_dec(v_a_2045_);
lean_dec_ref(v_a_2044_);
lean_dec(v_a_2043_);
lean_dec(v_a_2042_);
return v_res_2053_;
}
}
lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__0(lean_object* v_cls_2054_, lean_object* v_msg_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_){
_start:
{
lean_object* v___x_2067_; 
v___x_2067_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__0___redArg(v_cls_2054_, v_msg_2055_, v___y_2062_, v___y_2063_, v___y_2064_, v___y_2065_);
return v___x_2067_;
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_2054_ = stack[0].m_obj;
lean_object* v_msg_2055_ = stack[1].m_obj;
lean_object* v___y_2056_ = stack[2].m_obj;
lean_object* v___y_2057_ = stack[3].m_obj;
lean_object* v___y_2058_ = stack[4].m_obj;
lean_object* v___y_2059_ = stack[5].m_obj;
lean_object* v___y_2060_ = stack[6].m_obj;
lean_object* v___y_2061_ = stack[7].m_obj;
lean_object* v___y_2062_ = stack[8].m_obj;
lean_object* v___y_2063_ = stack[9].m_obj;
lean_object* v___y_2064_ = stack[10].m_obj;
lean_object* v___y_2065_ = stack[11].m_obj;
lean_object* v_res_2068_;
v_res_2068_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__0(v_cls_2054_, v_msg_2055_, v___y_2056_, v___y_2057_, v___y_2058_, v___y_2059_, v___y_2060_, v___y_2061_, v___y_2062_, v___y_2063_, v___y_2064_, v___y_2065_);
stack->m_obj
 = v_res_2068_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__0___boxed(lean_object* v_cls_2069_, lean_object* v_msg_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_){
_start:
{
lean_object* v_res_2082_; 
v_res_2082_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__0(v_cls_2069_, v_msg_2070_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_);
lean_dec(v___y_2080_);
lean_dec_ref(v___y_2079_);
lean_dec(v___y_2078_);
lean_dec_ref(v___y_2077_);
lean_dec(v___y_2076_);
lean_dec_ref(v___y_2075_);
lean_dec(v___y_2074_);
lean_dec_ref(v___y_2073_);
lean_dec(v___y_2072_);
lean_dec(v___y_2071_);
return v_res_2082_;
}
}
lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1(lean_object* v_a_2083_, lean_object* v_as_2084_, lean_object* v_as_x27_2085_, lean_object* v_b_2086_, lean_object* v_a_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_){
_start:
{
lean_object* v___x_2099_; 
v___x_2099_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg(v_a_2083_, v_as_x27_2085_, v_b_2086_, v___y_2088_, v___y_2089_, v___y_2090_, v___y_2091_, v___y_2092_, v___y_2093_, v___y_2094_, v___y_2095_, v___y_2096_, v___y_2097_);
return v___x_2099_;
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2083_ = stack[0].m_obj;
lean_object* v_as_2084_ = stack[1].m_obj;
lean_object* v_as_x27_2085_ = stack[2].m_obj;
lean_object* v_b_2086_ = stack[3].m_obj;
lean_object* v___y_2088_ = stack[5].m_obj;
lean_object* v___y_2089_ = stack[6].m_obj;
lean_object* v___y_2090_ = stack[7].m_obj;
lean_object* v___y_2091_ = stack[8].m_obj;
lean_object* v___y_2092_ = stack[9].m_obj;
lean_object* v___y_2093_ = stack[10].m_obj;
lean_object* v___y_2094_ = stack[11].m_obj;
lean_object* v___y_2095_ = stack[12].m_obj;
lean_object* v___y_2096_ = stack[13].m_obj;
lean_object* v___y_2097_ = stack[14].m_obj;
lean_object* v_res_2100_;
v_res_2100_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1(v_a_2083_, v_as_2084_, v_as_x27_2085_, v_b_2086_, lean_box(0), v___y_2088_, v___y_2089_, v___y_2090_, v___y_2091_, v___y_2092_, v___y_2093_, v___y_2094_, v___y_2095_, v___y_2096_, v___y_2097_);
stack->m_obj
 = v_res_2100_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___boxed(lean_object* v_a_2101_, lean_object* v_as_2102_, lean_object* v_as_x27_2103_, lean_object* v_b_2104_, lean_object* v_a_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_){
_start:
{
lean_object* v_res_2117_; 
v_res_2117_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1(v_a_2101_, v_as_2102_, v_as_x27_2103_, v_b_2104_, v_a_2105_, v___y_2106_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_);
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
return v_res_2117_;
}
}
lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__2(lean_object* v_a_2118_, lean_object* v_as_2119_, lean_object* v_as_x27_2120_, lean_object* v_b_2121_, lean_object* v_a_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_){
_start:
{
lean_object* v___x_2134_; 
v___x_2134_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__2___redArg(v_a_2118_, v_as_x27_2120_, v_b_2121_, v___y_2123_, v___y_2124_, v___y_2125_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_, v___y_2131_, v___y_2132_);
return v___x_2134_;
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2118_ = stack[0].m_obj;
lean_object* v_as_2119_ = stack[1].m_obj;
lean_object* v_as_x27_2120_ = stack[2].m_obj;
lean_object* v_b_2121_ = stack[3].m_obj;
lean_object* v___y_2123_ = stack[5].m_obj;
lean_object* v___y_2124_ = stack[6].m_obj;
lean_object* v___y_2125_ = stack[7].m_obj;
lean_object* v___y_2126_ = stack[8].m_obj;
lean_object* v___y_2127_ = stack[9].m_obj;
lean_object* v___y_2128_ = stack[10].m_obj;
lean_object* v___y_2129_ = stack[11].m_obj;
lean_object* v___y_2130_ = stack[12].m_obj;
lean_object* v___y_2131_ = stack[13].m_obj;
lean_object* v___y_2132_ = stack[14].m_obj;
lean_object* v_res_2135_;
v_res_2135_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__2(v_a_2118_, v_as_2119_, v_as_x27_2120_, v_b_2121_, lean_box(0), v___y_2123_, v___y_2124_, v___y_2125_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_, v___y_2131_, v___y_2132_);
stack->m_obj
 = v_res_2135_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__2___boxed(lean_object* v_a_2136_, lean_object* v_as_2137_, lean_object* v_as_x27_2138_, lean_object* v_b_2139_, lean_object* v_a_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_){
_start:
{
lean_object* v_res_2152_; 
v_res_2152_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__2(v_a_2136_, v_as_2137_, v_as_x27_2138_, v_b_2139_, v_a_2140_, v___y_2141_, v___y_2142_, v___y_2143_, v___y_2144_, v___y_2145_, v___y_2146_, v___y_2147_, v___y_2148_, v___y_2149_, v___y_2150_);
lean_dec(v___y_2150_);
lean_dec_ref(v___y_2149_);
lean_dec(v___y_2148_);
lean_dec_ref(v___y_2147_);
lean_dec(v___y_2146_);
lean_dec_ref(v___y_2145_);
lean_dec(v___y_2144_);
lean_dec_ref(v___y_2143_);
lean_dec(v___y_2142_);
lean_dec(v___y_2141_);
lean_dec(v_as_x27_2138_);
lean_dec(v_as_2137_);
lean_dec(v_a_2136_);
return v_res_2152_;
}
}
lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__3(lean_object* v_as_2153_, lean_object* v_as_x27_2154_, lean_object* v_b_2155_, lean_object* v_a_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_){
_start:
{
lean_object* v___x_2168_; 
v___x_2168_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__3___redArg(v_as_x27_2154_, v_b_2155_, v___y_2157_, v___y_2158_, v___y_2159_, v___y_2160_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_, v___y_2165_, v___y_2166_);
return v___x_2168_;
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2153_ = stack[0].m_obj;
lean_object* v_as_x27_2154_ = stack[1].m_obj;
lean_object* v_b_2155_ = stack[2].m_obj;
lean_object* v___y_2157_ = stack[4].m_obj;
lean_object* v___y_2158_ = stack[5].m_obj;
lean_object* v___y_2159_ = stack[6].m_obj;
lean_object* v___y_2160_ = stack[7].m_obj;
lean_object* v___y_2161_ = stack[8].m_obj;
lean_object* v___y_2162_ = stack[9].m_obj;
lean_object* v___y_2163_ = stack[10].m_obj;
lean_object* v___y_2164_ = stack[11].m_obj;
lean_object* v___y_2165_ = stack[12].m_obj;
lean_object* v___y_2166_ = stack[13].m_obj;
lean_object* v_res_2169_;
v_res_2169_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__3(v_as_2153_, v_as_x27_2154_, v_b_2155_, lean_box(0), v___y_2157_, v___y_2158_, v___y_2159_, v___y_2160_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_, v___y_2165_, v___y_2166_);
stack->m_obj
 = v_res_2169_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__3___boxed(lean_object* v_as_2170_, lean_object* v_as_x27_2171_, lean_object* v_b_2172_, lean_object* v_a_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_){
_start:
{
lean_object* v_res_2185_; 
v_res_2185_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__3(v_as_2170_, v_as_x27_2171_, v_b_2172_, v_a_2173_, v___y_2174_, v___y_2175_, v___y_2176_, v___y_2177_, v___y_2178_, v___y_2179_, v___y_2180_, v___y_2181_, v___y_2182_, v___y_2183_);
lean_dec(v___y_2183_);
lean_dec_ref(v___y_2182_);
lean_dec(v___y_2181_);
lean_dec_ref(v___y_2180_);
lean_dec(v___y_2179_);
lean_dec_ref(v___y_2178_);
lean_dec(v___y_2177_);
lean_dec_ref(v___y_2176_);
lean_dec(v___y_2175_);
lean_dec(v___y_2174_);
lean_dec(v_as_x27_2171_);
lean_dec(v_as_2170_);
return v_res_2185_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; 
v___x_2188_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__1___redArg___closed__1));
v___x_2189_ = lean_unsigned_to_nat(4u);
v___x_2190_ = lean_unsigned_to_nat(131u);
v___x_2191_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__1___redArg___closed__0));
v___x_2192_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__0));
v___x_2193_ = l_mkPanicMessageWithDecl(v___x_2192_, v___x_2191_, v___x_2190_, v___x_2189_, v___x_2188_);
return v___x_2193_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__1___redArg___closed__4(void){
_start:
{
lean_object* v___x_2195_; lean_object* v___x_2196_; 
v___x_2195_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__1___redArg___closed__3));
v___x_2196_ = l_Lean_stringToMessageData(v___x_2195_);
return v___x_2196_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__1___redArg___closed__6(void){
_start:
{
lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; 
v___x_2198_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__1___redArg___closed__5));
v___x_2199_ = lean_unsigned_to_nat(4u);
v___x_2200_ = lean_unsigned_to_nat(134u);
v___x_2201_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__1___redArg___closed__0));
v___x_2202_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__0));
v___x_2203_ = l_mkPanicMessageWithDecl(v___x_2202_, v___x_2201_, v___x_2200_, v___x_2199_, v___x_2198_);
return v___x_2203_;
}
}
lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__1___redArg(lean_object* v___x_2204_, lean_object* v___x_2205_, lean_object* v_as_x27_2206_, lean_object* v_b_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_){
_start:
{
if (lean_obj_tag(v_as_x27_2206_) == 0)
{
lean_object* v___x_2219_; 
v___x_2219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2219_, 0, v_b_2207_);
return v___x_2219_;
}
else
{
lean_object* v_head_2220_; lean_object* v_tail_2221_; lean_object* v___y_2223_; lean_object* v___x_2243_; lean_object* v___x_2244_; 
v_head_2220_ = lean_ctor_get(v_as_x27_2206_, 0);
v_tail_2221_ = lean_ctor_get(v_as_x27_2206_, 1);
v___x_2243_ = lean_box(0);
lean_inc(v_head_2220_);
v___x_2244_ = l_Lean_Meta_Grind_isCongrRoot___redArg(v_head_2220_, v___y_2208_, v___y_2214_, v___y_2215_, v___y_2216_, v___y_2217_);
if (lean_obj_tag(v___x_2244_) == 0)
{
lean_object* v_a_2245_; uint8_t v___x_2246_; 
v_a_2245_ = lean_ctor_get(v___x_2244_, 0);
lean_inc(v_a_2245_);
lean_dec_ref_known(v___x_2244_, 1);
v___x_2246_ = lean_unbox(v_a_2245_);
lean_dec(v_a_2245_);
if (v___x_2246_ == 0)
{
lean_object* v___x_2247_; lean_object* v___x_2248_; 
v___x_2247_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__1___redArg___closed__2, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__1___redArg___closed__2_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__1___redArg___closed__2);
v___x_2248_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__0(v___x_2247_, v___y_2208_, v___y_2209_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_, v___y_2216_, v___y_2217_);
v___y_2223_ = v___x_2248_;
goto v___jp_2222_;
}
else
{
lean_object* v___x_2249_; 
lean_inc(v_head_2220_);
v___x_2249_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2___redArg(v___x_2204_, v___x_2205_, v_head_2220_);
if (lean_obj_tag(v___x_2249_) == 0)
{
lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; 
v___x_2250_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__1___redArg___closed__4, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__1___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__1___redArg___closed__4);
lean_inc(v_head_2220_);
v___x_2251_ = l_Lean_indentExpr(v_head_2220_);
v___x_2252_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2252_, 0, v___x_2250_);
lean_ctor_set(v___x_2252_, 1, v___x_2251_);
v___x_2253_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__1___redArg(v___x_2252_, v___y_2214_, v___y_2215_, v___y_2216_, v___y_2217_);
return v___x_2253_;
}
else
{
lean_object* v_val_2254_; lean_object* v_fst_2255_; size_t v___x_2256_; size_t v___x_2257_; uint8_t v___x_2258_; 
v_val_2254_ = lean_ctor_get(v___x_2249_, 0);
lean_inc(v_val_2254_);
lean_dec_ref_known(v___x_2249_, 1);
v_fst_2255_ = lean_ctor_get(v_val_2254_, 0);
lean_inc(v_fst_2255_);
lean_dec(v_val_2254_);
v___x_2256_ = lean_ptr_addr(v_head_2220_);
v___x_2257_ = lean_ptr_addr(v_fst_2255_);
lean_dec(v_fst_2255_);
v___x_2258_ = lean_usize_dec_eq(v___x_2256_, v___x_2257_);
if (v___x_2258_ == 0)
{
lean_object* v___x_2259_; lean_object* v___x_2260_; 
v___x_2259_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__1___redArg___closed__6, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__1___redArg___closed__6_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__1___redArg___closed__6);
v___x_2260_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__0(v___x_2259_, v___y_2208_, v___y_2209_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_, v___y_2216_, v___y_2217_);
v___y_2223_ = v___x_2260_;
goto v___jp_2222_;
}
else
{
v_as_x27_2206_ = v_tail_2221_;
v_b_2207_ = v___x_2243_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_2262_; lean_object* v___x_2264_; uint8_t v_isShared_2265_; uint8_t v_isSharedCheck_2269_; 
v_a_2262_ = lean_ctor_get(v___x_2244_, 0);
v_isSharedCheck_2269_ = !lean_is_exclusive(v___x_2244_);
if (v_isSharedCheck_2269_ == 0)
{
v___x_2264_ = v___x_2244_;
v_isShared_2265_ = v_isSharedCheck_2269_;
goto v_resetjp_2263_;
}
else
{
lean_inc(v_a_2262_);
lean_dec(v___x_2244_);
v___x_2264_ = lean_box(0);
v_isShared_2265_ = v_isSharedCheck_2269_;
goto v_resetjp_2263_;
}
v_resetjp_2263_:
{
lean_object* v___x_2267_; 
if (v_isShared_2265_ == 0)
{
v___x_2267_ = v___x_2264_;
goto v_reusejp_2266_;
}
else
{
lean_object* v_reuseFailAlloc_2268_; 
v_reuseFailAlloc_2268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2268_, 0, v_a_2262_);
v___x_2267_ = v_reuseFailAlloc_2268_;
goto v_reusejp_2266_;
}
v_reusejp_2266_:
{
return v___x_2267_;
}
}
}
v___jp_2222_:
{
if (lean_obj_tag(v___y_2223_) == 0)
{
lean_object* v_a_2224_; lean_object* v___x_2226_; uint8_t v_isShared_2227_; uint8_t v_isSharedCheck_2234_; 
v_a_2224_ = lean_ctor_get(v___y_2223_, 0);
v_isSharedCheck_2234_ = !lean_is_exclusive(v___y_2223_);
if (v_isSharedCheck_2234_ == 0)
{
v___x_2226_ = v___y_2223_;
v_isShared_2227_ = v_isSharedCheck_2234_;
goto v_resetjp_2225_;
}
else
{
lean_inc(v_a_2224_);
lean_dec(v___y_2223_);
v___x_2226_ = lean_box(0);
v_isShared_2227_ = v_isSharedCheck_2234_;
goto v_resetjp_2225_;
}
v_resetjp_2225_:
{
if (lean_obj_tag(v_a_2224_) == 0)
{
lean_object* v_a_2228_; lean_object* v___x_2230_; 
v_a_2228_ = lean_ctor_get(v_a_2224_, 0);
lean_inc(v_a_2228_);
lean_dec_ref_known(v_a_2224_, 1);
if (v_isShared_2227_ == 0)
{
lean_ctor_set(v___x_2226_, 0, v_a_2228_);
v___x_2230_ = v___x_2226_;
goto v_reusejp_2229_;
}
else
{
lean_object* v_reuseFailAlloc_2231_; 
v_reuseFailAlloc_2231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2231_, 0, v_a_2228_);
v___x_2230_ = v_reuseFailAlloc_2231_;
goto v_reusejp_2229_;
}
v_reusejp_2229_:
{
return v___x_2230_;
}
}
else
{
lean_object* v_a_2232_; 
lean_del_object(v___x_2226_);
v_a_2232_ = lean_ctor_get(v_a_2224_, 0);
lean_inc(v_a_2232_);
lean_dec_ref_known(v_a_2224_, 1);
v_as_x27_2206_ = v_tail_2221_;
v_b_2207_ = v_a_2232_;
goto _start;
}
}
}
else
{
lean_object* v_a_2235_; lean_object* v___x_2237_; uint8_t v_isShared_2238_; uint8_t v_isSharedCheck_2242_; 
v_a_2235_ = lean_ctor_get(v___y_2223_, 0);
v_isSharedCheck_2242_ = !lean_is_exclusive(v___y_2223_);
if (v_isSharedCheck_2242_ == 0)
{
v___x_2237_ = v___y_2223_;
v_isShared_2238_ = v_isSharedCheck_2242_;
goto v_resetjp_2236_;
}
else
{
lean_inc(v_a_2235_);
lean_dec(v___y_2223_);
v___x_2237_ = lean_box(0);
v_isShared_2238_ = v_isSharedCheck_2242_;
goto v_resetjp_2236_;
}
v_resetjp_2236_:
{
lean_object* v___x_2240_; 
if (v_isShared_2238_ == 0)
{
v___x_2240_ = v___x_2237_;
goto v_reusejp_2239_;
}
else
{
lean_object* v_reuseFailAlloc_2241_; 
v_reuseFailAlloc_2241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2241_, 0, v_a_2235_);
v___x_2240_ = v_reuseFailAlloc_2241_;
goto v_reusejp_2239_;
}
v_reusejp_2239_:
{
return v___x_2240_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2204_ = stack[0].m_obj;
lean_object* v___x_2205_ = stack[1].m_obj;
lean_object* v_as_x27_2206_ = stack[2].m_obj;
lean_object* v_b_2207_ = stack[3].m_obj;
lean_object* v___y_2208_ = stack[4].m_obj;
lean_object* v___y_2209_ = stack[5].m_obj;
lean_object* v___y_2210_ = stack[6].m_obj;
lean_object* v___y_2211_ = stack[7].m_obj;
lean_object* v___y_2212_ = stack[8].m_obj;
lean_object* v___y_2213_ = stack[9].m_obj;
lean_object* v___y_2214_ = stack[10].m_obj;
lean_object* v___y_2215_ = stack[11].m_obj;
lean_object* v___y_2216_ = stack[12].m_obj;
lean_object* v___y_2217_ = stack[13].m_obj;
lean_object* v_res_2270_;
v_res_2270_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__1___redArg(v___x_2204_, v___x_2205_, v_as_x27_2206_, v_b_2207_, v___y_2208_, v___y_2209_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_, v___y_2216_, v___y_2217_);
stack->m_obj
 = v_res_2270_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__1___redArg___boxed(lean_object* v___x_2271_, lean_object* v___x_2272_, lean_object* v_as_x27_2273_, lean_object* v_b_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_){
_start:
{
lean_object* v_res_2286_; 
v_res_2286_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__1___redArg(v___x_2271_, v___x_2272_, v_as_x27_2273_, v_b_2274_, v___y_2275_, v___y_2276_, v___y_2277_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_, v___y_2282_, v___y_2283_, v___y_2284_);
lean_dec(v___y_2284_);
lean_dec_ref(v___y_2283_);
lean_dec(v___y_2282_);
lean_dec_ref(v___y_2281_);
lean_dec(v___y_2280_);
lean_dec_ref(v___y_2279_);
lean_dec(v___y_2278_);
lean_dec_ref(v___y_2277_);
lean_dec(v___y_2276_);
lean_dec(v___y_2275_);
lean_dec(v_as_x27_2273_);
lean_dec_ref(v___x_2272_);
lean_dec_ref(v___x_2271_);
return v_res_2286_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__1(lean_object* v_a_2287_, lean_object* v_a_2288_){
_start:
{
if (lean_obj_tag(v_a_2287_) == 0)
{
lean_object* v___x_2289_; 
v___x_2289_ = l_List_reverse___redArg(v_a_2288_);
return v___x_2289_;
}
else
{
lean_object* v_head_2290_; lean_object* v_tail_2291_; lean_object* v___x_2293_; uint8_t v_isShared_2294_; uint8_t v_isSharedCheck_2300_; 
v_head_2290_ = lean_ctor_get(v_a_2287_, 0);
v_tail_2291_ = lean_ctor_get(v_a_2287_, 1);
v_isSharedCheck_2300_ = !lean_is_exclusive(v_a_2287_);
if (v_isSharedCheck_2300_ == 0)
{
v___x_2293_ = v_a_2287_;
v_isShared_2294_ = v_isSharedCheck_2300_;
goto v_resetjp_2292_;
}
else
{
lean_inc(v_tail_2291_);
lean_inc(v_head_2290_);
lean_dec(v_a_2287_);
v___x_2293_ = lean_box(0);
v_isShared_2294_ = v_isSharedCheck_2300_;
goto v_resetjp_2292_;
}
v_resetjp_2292_:
{
lean_object* v_fst_2295_; lean_object* v___x_2297_; 
v_fst_2295_ = lean_ctor_get(v_head_2290_, 0);
lean_inc(v_fst_2295_);
lean_dec(v_head_2290_);
if (v_isShared_2294_ == 0)
{
lean_ctor_set(v___x_2293_, 1, v_a_2288_);
lean_ctor_set(v___x_2293_, 0, v_fst_2295_);
v___x_2297_ = v___x_2293_;
goto v_reusejp_2296_;
}
else
{
lean_object* v_reuseFailAlloc_2299_; 
v_reuseFailAlloc_2299_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2299_, 0, v_fst_2295_);
lean_ctor_set(v_reuseFailAlloc_2299_, 1, v_a_2288_);
v___x_2297_ = v_reuseFailAlloc_2299_;
goto v_reusejp_2296_;
}
v_reusejp_2296_:
{
v_a_2287_ = v_tail_2291_;
v_a_2288_ = v___x_2297_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7___redArg(lean_object* v_f_2301_, lean_object* v_keys_2302_, lean_object* v_vals_2303_, lean_object* v_i_2304_, lean_object* v_acc_2305_){
_start:
{
lean_object* v___x_2306_; uint8_t v___x_2307_; 
v___x_2306_ = lean_array_get_size(v_keys_2302_);
v___x_2307_ = lean_nat_dec_lt(v_i_2304_, v___x_2306_);
if (v___x_2307_ == 0)
{
lean_dec(v_i_2304_);
lean_dec(v_f_2301_);
return v_acc_2305_;
}
else
{
lean_object* v_k_2308_; lean_object* v_v_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; 
v_k_2308_ = lean_array_fget_borrowed(v_keys_2302_, v_i_2304_);
v_v_2309_ = lean_array_fget_borrowed(v_vals_2303_, v_i_2304_);
lean_inc(v_f_2301_);
lean_inc(v_v_2309_);
lean_inc(v_k_2308_);
v___x_2310_ = lean_apply_3(v_f_2301_, v_acc_2305_, v_k_2308_, v_v_2309_);
v___x_2311_ = lean_unsigned_to_nat(1u);
v___x_2312_ = lean_nat_add(v_i_2304_, v___x_2311_);
lean_dec(v_i_2304_);
v_i_2304_ = v___x_2312_;
v_acc_2305_ = v___x_2310_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7___redArg___boxed(lean_object* v_f_2314_, lean_object* v_keys_2315_, lean_object* v_vals_2316_, lean_object* v_i_2317_, lean_object* v_acc_2318_){
_start:
{
lean_object* v_res_2319_; 
v_res_2319_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7___redArg(v_f_2314_, v_keys_2315_, v_vals_2316_, v_i_2317_, v_acc_2318_);
lean_dec_ref(v_vals_2316_);
lean_dec_ref(v_keys_2315_);
return v_res_2319_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg(lean_object* v_f_2320_, lean_object* v_as_2321_, size_t v_i_2322_, size_t v_stop_2323_, lean_object* v_b_2324_){
_start:
{
lean_object* v___y_2326_; uint8_t v___x_2330_; 
v___x_2330_ = lean_usize_dec_eq(v_i_2322_, v_stop_2323_);
if (v___x_2330_ == 0)
{
lean_object* v___x_2331_; 
v___x_2331_ = lean_array_uget_borrowed(v_as_2321_, v_i_2322_);
switch(lean_obj_tag(v___x_2331_))
{
case 0:
{
lean_object* v_key_2332_; lean_object* v_val_2333_; lean_object* v___x_2334_; 
v_key_2332_ = lean_ctor_get(v___x_2331_, 0);
v_val_2333_ = lean_ctor_get(v___x_2331_, 1);
lean_inc(v_f_2320_);
lean_inc(v_val_2333_);
lean_inc(v_key_2332_);
v___x_2334_ = lean_apply_3(v_f_2320_, v_b_2324_, v_key_2332_, v_val_2333_);
v___y_2326_ = v___x_2334_;
goto v___jp_2325_;
}
case 1:
{
lean_object* v_node_2335_; lean_object* v___x_2336_; 
v_node_2335_ = lean_ctor_get(v___x_2331_, 0);
lean_inc(v_f_2320_);
v___x_2336_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_f_2320_, v_node_2335_, v_b_2324_);
v___y_2326_ = v___x_2336_;
goto v___jp_2325_;
}
default: 
{
v___y_2326_ = v_b_2324_;
goto v___jp_2325_;
}
}
}
else
{
lean_dec(v_f_2320_);
return v_b_2324_;
}
v___jp_2325_:
{
size_t v___x_2327_; size_t v___x_2328_; 
v___x_2327_ = ((size_t)1ULL);
v___x_2328_ = lean_usize_add(v_i_2322_, v___x_2327_);
v_i_2322_ = v___x_2328_;
v_b_2324_ = v___y_2326_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_2320_ = stack[0].m_obj;
lean_object* v_as_2321_ = stack[1].m_obj;
size_t v_i_2322_ = stack[2].m_num;
size_t v_stop_2323_ = stack[3].m_num;
lean_object* v_b_2324_ = stack[4].m_obj;
lean_object* v_res_2337_;
v_res_2337_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg(v_f_2320_, v_as_2321_, v_i_2322_, v_stop_2323_, v_b_2324_);
stack->m_obj
 = v_res_2337_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(lean_object* v_f_2338_, lean_object* v_x_2339_, lean_object* v_x_2340_){
_start:
{
if (lean_obj_tag(v_x_2339_) == 0)
{
lean_object* v_es_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; uint8_t v___x_2344_; 
v_es_2341_ = lean_ctor_get(v_x_2339_, 0);
v___x_2342_ = lean_unsigned_to_nat(0u);
v___x_2343_ = lean_array_get_size(v_es_2341_);
v___x_2344_ = lean_nat_dec_lt(v___x_2342_, v___x_2343_);
if (v___x_2344_ == 0)
{
lean_dec(v_f_2338_);
return v_x_2340_;
}
else
{
size_t v___x_2345_; size_t v___x_2346_; lean_object* v___x_2347_; 
v___x_2345_ = ((size_t)0ULL);
v___x_2346_ = lean_usize_of_nat(v___x_2343_);
v___x_2347_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg(v_f_2338_, v_es_2341_, v___x_2345_, v___x_2346_, v_x_2340_);
return v___x_2347_;
}
}
else
{
lean_object* v_ks_2348_; lean_object* v_vs_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; 
v_ks_2348_ = lean_ctor_get(v_x_2339_, 0);
v_vs_2349_ = lean_ctor_get(v_x_2339_, 1);
v___x_2350_ = lean_unsigned_to_nat(0u);
v___x_2351_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7___redArg(v_f_2338_, v_ks_2348_, v_vs_2349_, v___x_2350_, v_x_2340_);
return v___x_2351_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0_spec__1_spec__3_spec__5___redArg___boxed(lean_object* v_f_2352_, lean_object* v_x_2353_, lean_object* v_x_2354_){
_start:
{
lean_object* v_res_2355_; 
v_res_2355_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_f_2352_, v_x_2353_, v_x_2354_);
lean_dec_ref(v_x_2353_);
return v_res_2355_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___boxed(lean_object* v_f_2356_, lean_object* v_as_2357_, lean_object* v_i_2358_, lean_object* v_stop_2359_, lean_object* v_b_2360_){
_start:
{
size_t v_i_boxed_2361_; size_t v_stop_boxed_2362_; lean_object* v_res_2363_; 
v_i_boxed_2361_ = lean_unbox_usize(v_i_2358_);
lean_dec(v_i_2358_);
v_stop_boxed_2362_ = lean_unbox_usize(v_stop_2359_);
lean_dec(v_stop_2359_);
v_res_2363_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg(v_f_2356_, v_as_2357_, v_i_boxed_2361_, v_stop_boxed_2362_, v_b_2360_);
lean_dec_ref(v_as_2357_);
return v_res_2363_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0_spec__1___redArg___lam__0(lean_object* v_f_2364_, lean_object* v_x1_2365_, lean_object* v_x2_2366_, lean_object* v_x3_2367_){
_start:
{
lean_object* v___x_2368_; 
v___x_2368_ = lean_apply_3(v_f_2364_, v_x1_2365_, v_x2_2366_, v_x3_2367_);
return v___x_2368_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0_spec__1___redArg(lean_object* v___x_2369_, lean_object* v_map_2370_, lean_object* v_f_2371_, lean_object* v_init_2372_){
_start:
{
lean_object* v___f_2373_; lean_object* v___x_2374_; 
v___f_2373_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0_spec__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2373_, 0, v_f_2371_);
v___x_2374_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v___f_2373_, v_map_2370_, v_init_2372_);
return v___x_2374_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v___x_2375_, lean_object* v_map_2376_, lean_object* v_f_2377_, lean_object* v_init_2378_){
_start:
{
lean_object* v_res_2379_; 
v_res_2379_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0_spec__1___redArg(v___x_2375_, v_map_2376_, v_f_2377_, v_init_2378_);
lean_dec_ref(v_map_2376_);
lean_dec_ref(v___x_2375_);
return v_res_2379_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0___redArg___lam__0(lean_object* v_ps_2380_, lean_object* v_k_2381_, lean_object* v_v_2382_){
_start:
{
lean_object* v___x_2383_; lean_object* v___x_2384_; 
v___x_2383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2383_, 0, v_k_2381_);
lean_ctor_set(v___x_2383_, 1, v_v_2382_);
v___x_2384_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2384_, 0, v___x_2383_);
lean_ctor_set(v___x_2384_, 1, v_ps_2380_);
return v___x_2384_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0___redArg(lean_object* v___x_2386_, lean_object* v_m_2387_){
_start:
{
lean_object* v___f_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; 
v___f_2388_ = ((lean_object*)(l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0___redArg___closed__0));
v___x_2389_ = lean_box(0);
v___x_2390_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0_spec__1___redArg(v___x_2386_, v_m_2387_, v___f_2388_, v___x_2389_);
return v___x_2390_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0___redArg___boxed(lean_object* v___x_2391_, lean_object* v_m_2392_){
_start:
{
lean_object* v_res_2393_; 
v_res_2393_ = l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0___redArg(v___x_2391_, v_m_2392_);
lean_dec_ref(v_m_2392_);
lean_dec_ref(v___x_2391_);
return v_res_2393_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0(lean_object* v___x_2394_, lean_object* v_s_2395_){
_start:
{
lean_object* v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; 
v___x_2396_ = l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0___redArg(v___x_2394_, v_s_2395_);
v___x_2397_ = lean_box(0);
v___x_2398_ = l_List_mapTR_loop___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__1(v___x_2396_, v___x_2397_);
return v___x_2398_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0___boxed(lean_object* v___x_2399_, lean_object* v_s_2400_){
_start:
{
lean_object* v_res_2401_; 
v_res_2401_ = l_Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0(v___x_2399_, v_s_2400_);
lean_dec_ref(v_s_2400_);
lean_dec_ref(v___x_2399_);
return v_res_2401_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable(lean_object* v_a_2402_, lean_object* v_a_2403_, lean_object* v_a_2404_, lean_object* v_a_2405_, lean_object* v_a_2406_, lean_object* v_a_2407_, lean_object* v_a_2408_, lean_object* v_a_2409_, lean_object* v_a_2410_, lean_object* v_a_2411_){
_start:
{
lean_object* v___x_2413_; lean_object* v_toGoalState_2414_; lean_object* v_enodeMap_2415_; lean_object* v_congrTable_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; 
v___x_2413_ = lean_st_ref_get(v_a_2402_);
v_toGoalState_2414_ = lean_ctor_get(v___x_2413_, 0);
lean_inc_ref(v_toGoalState_2414_);
lean_dec(v___x_2413_);
v_enodeMap_2415_ = lean_ctor_get(v_toGoalState_2414_, 1);
lean_inc_ref(v_enodeMap_2415_);
v_congrTable_2416_ = lean_ctor_get(v_toGoalState_2414_, 4);
lean_inc_ref(v_congrTable_2416_);
lean_dec_ref(v_toGoalState_2414_);
v___x_2417_ = l_Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0(v_enodeMap_2415_, v_congrTable_2416_);
v___x_2418_ = lean_box(0);
v___x_2419_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__1___redArg(v_enodeMap_2415_, v_congrTable_2416_, v___x_2417_, v___x_2418_, v_a_2402_, v_a_2403_, v_a_2404_, v_a_2405_, v_a_2406_, v_a_2407_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_);
lean_dec(v___x_2417_);
lean_dec_ref(v_congrTable_2416_);
lean_dec_ref(v_enodeMap_2415_);
if (lean_obj_tag(v___x_2419_) == 0)
{
lean_object* v___x_2421_; uint8_t v_isShared_2422_; uint8_t v_isSharedCheck_2426_; 
v_isSharedCheck_2426_ = !lean_is_exclusive(v___x_2419_);
if (v_isSharedCheck_2426_ == 0)
{
lean_object* v_unused_2427_; 
v_unused_2427_ = lean_ctor_get(v___x_2419_, 0);
lean_dec(v_unused_2427_);
v___x_2421_ = v___x_2419_;
v_isShared_2422_ = v_isSharedCheck_2426_;
goto v_resetjp_2420_;
}
else
{
lean_dec(v___x_2419_);
v___x_2421_ = lean_box(0);
v_isShared_2422_ = v_isSharedCheck_2426_;
goto v_resetjp_2420_;
}
v_resetjp_2420_:
{
lean_object* v___x_2424_; 
if (v_isShared_2422_ == 0)
{
lean_ctor_set(v___x_2421_, 0, v___x_2418_);
v___x_2424_ = v___x_2421_;
goto v_reusejp_2423_;
}
else
{
lean_object* v_reuseFailAlloc_2425_; 
v_reuseFailAlloc_2425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2425_, 0, v___x_2418_);
v___x_2424_ = v_reuseFailAlloc_2425_;
goto v_reusejp_2423_;
}
v_reusejp_2423_:
{
return v___x_2424_;
}
}
}
else
{
return v___x_2419_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2402_ = stack[0].m_obj;
lean_object* v_a_2403_ = stack[1].m_obj;
lean_object* v_a_2404_ = stack[2].m_obj;
lean_object* v_a_2405_ = stack[3].m_obj;
lean_object* v_a_2406_ = stack[4].m_obj;
lean_object* v_a_2407_ = stack[5].m_obj;
lean_object* v_a_2408_ = stack[6].m_obj;
lean_object* v_a_2409_ = stack[7].m_obj;
lean_object* v_a_2410_ = stack[8].m_obj;
lean_object* v_a_2411_ = stack[9].m_obj;
lean_object* v_res_2428_;
v_res_2428_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable(v_a_2402_, v_a_2403_, v_a_2404_, v_a_2405_, v_a_2406_, v_a_2407_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_);
stack->m_obj
 = v_res_2428_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable___boxed(lean_object* v_a_2429_, lean_object* v_a_2430_, lean_object* v_a_2431_, lean_object* v_a_2432_, lean_object* v_a_2433_, lean_object* v_a_2434_, lean_object* v_a_2435_, lean_object* v_a_2436_, lean_object* v_a_2437_, lean_object* v_a_2438_, lean_object* v_a_2439_){
_start:
{
lean_object* v_res_2440_; 
v_res_2440_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable(v_a_2429_, v_a_2430_, v_a_2431_, v_a_2432_, v_a_2433_, v_a_2434_, v_a_2435_, v_a_2436_, v_a_2437_, v_a_2438_);
lean_dec(v_a_2438_);
lean_dec_ref(v_a_2437_);
lean_dec(v_a_2436_);
lean_dec_ref(v_a_2435_);
lean_dec(v_a_2434_);
lean_dec_ref(v_a_2433_);
lean_dec(v_a_2432_);
lean_dec_ref(v_a_2431_);
lean_dec(v_a_2430_);
lean_dec(v_a_2429_);
return v_res_2440_;
}
}
lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__1(lean_object* v___x_2441_, lean_object* v___x_2442_, lean_object* v_as_2443_, lean_object* v_as_x27_2444_, lean_object* v_b_2445_, lean_object* v_a_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_){
_start:
{
lean_object* v___x_2458_; 
v___x_2458_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__1___redArg(v___x_2441_, v___x_2442_, v_as_x27_2444_, v_b_2445_, v___y_2447_, v___y_2448_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_, v___y_2453_, v___y_2454_, v___y_2455_, v___y_2456_);
return v___x_2458_;
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2441_ = stack[0].m_obj;
lean_object* v___x_2442_ = stack[1].m_obj;
lean_object* v_as_2443_ = stack[2].m_obj;
lean_object* v_as_x27_2444_ = stack[3].m_obj;
lean_object* v_b_2445_ = stack[4].m_obj;
lean_object* v___y_2447_ = stack[6].m_obj;
lean_object* v___y_2448_ = stack[7].m_obj;
lean_object* v___y_2449_ = stack[8].m_obj;
lean_object* v___y_2450_ = stack[9].m_obj;
lean_object* v___y_2451_ = stack[10].m_obj;
lean_object* v___y_2452_ = stack[11].m_obj;
lean_object* v___y_2453_ = stack[12].m_obj;
lean_object* v___y_2454_ = stack[13].m_obj;
lean_object* v___y_2455_ = stack[14].m_obj;
lean_object* v___y_2456_ = stack[15].m_obj;
lean_object* v_res_2459_;
v_res_2459_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__1(v___x_2441_, v___x_2442_, v_as_2443_, v_as_x27_2444_, v_b_2445_, lean_box(0), v___y_2447_, v___y_2448_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_, v___y_2453_, v___y_2454_, v___y_2455_, v___y_2456_);
stack->m_obj
 = v_res_2459_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__1___boxed(lean_object** _args){
lean_object* v___x_2460_ = _args[0];
lean_object* v___x_2461_ = _args[1];
lean_object* v_as_2462_ = _args[2];
lean_object* v_as_x27_2463_ = _args[3];
lean_object* v_b_2464_ = _args[4];
lean_object* v_a_2465_ = _args[5];
lean_object* v___y_2466_ = _args[6];
lean_object* v___y_2467_ = _args[7];
lean_object* v___y_2468_ = _args[8];
lean_object* v___y_2469_ = _args[9];
lean_object* v___y_2470_ = _args[10];
lean_object* v___y_2471_ = _args[11];
lean_object* v___y_2472_ = _args[12];
lean_object* v___y_2473_ = _args[13];
lean_object* v___y_2474_ = _args[14];
lean_object* v___y_2475_ = _args[15];
lean_object* v___y_2476_ = _args[16];
_start:
{
lean_object* v_res_2477_; 
v_res_2477_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__1(v___x_2460_, v___x_2461_, v_as_2462_, v_as_x27_2463_, v_b_2464_, v_a_2465_, v___y_2466_, v___y_2467_, v___y_2468_, v___y_2469_, v___y_2470_, v___y_2471_, v___y_2472_, v___y_2473_, v___y_2474_, v___y_2475_);
lean_dec(v___y_2475_);
lean_dec_ref(v___y_2474_);
lean_dec(v___y_2473_);
lean_dec_ref(v___y_2472_);
lean_dec(v___y_2471_);
lean_dec_ref(v___y_2470_);
lean_dec(v___y_2469_);
lean_dec_ref(v___y_2468_);
lean_dec(v___y_2467_);
lean_dec(v___y_2466_);
lean_dec(v_as_x27_2463_);
lean_dec(v_as_2462_);
lean_dec_ref(v___x_2461_);
lean_dec_ref(v___x_2460_);
return v_res_2477_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0(lean_object* v___x_2478_, lean_object* v_00_u03b2_2479_, lean_object* v_m_2480_){
_start:
{
lean_object* v___x_2481_; 
v___x_2481_ = l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0___redArg(v___x_2478_, v_m_2480_);
return v___x_2481_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0___boxed(lean_object* v___x_2482_, lean_object* v_00_u03b2_2483_, lean_object* v_m_2484_){
_start:
{
lean_object* v_res_2485_; 
v_res_2485_ = l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0(v___x_2482_, v_00_u03b2_2483_, v_m_2484_);
lean_dec_ref(v_m_2484_);
lean_dec_ref(v___x_2482_);
return v_res_2485_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0_spec__1(lean_object* v___x_2486_, lean_object* v_00_u03c3_2487_, lean_object* v_00_u03b2_2488_, lean_object* v_map_2489_, lean_object* v_f_2490_, lean_object* v_init_2491_){
_start:
{
lean_object* v___x_2492_; 
v___x_2492_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0_spec__1___redArg(v___x_2486_, v_map_2489_, v_f_2490_, v_init_2491_);
return v___x_2492_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0_spec__1___boxed(lean_object* v___x_2493_, lean_object* v_00_u03c3_2494_, lean_object* v_00_u03b2_2495_, lean_object* v_map_2496_, lean_object* v_f_2497_, lean_object* v_init_2498_){
_start:
{
lean_object* v_res_2499_; 
v_res_2499_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0_spec__1(v___x_2493_, v_00_u03c3_2494_, v_00_u03b2_2495_, v_map_2496_, v_f_2497_, v_init_2498_);
lean_dec_ref(v_map_2496_);
lean_dec_ref(v___x_2493_);
return v_res_2499_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_map_2500_, lean_object* v_f_2501_, lean_object* v_init_2502_){
_start:
{
lean_object* v___x_2503_; 
v___x_2503_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_f_2501_, v_map_2500_, v_init_2502_);
return v___x_2503_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_map_2504_, lean_object* v_f_2505_, lean_object* v_init_2506_){
_start:
{
lean_object* v_res_2507_; 
v_res_2507_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0_spec__1_spec__3___redArg(v_map_2504_, v_f_2505_, v_init_2506_);
lean_dec_ref(v_map_2504_);
return v_res_2507_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0_spec__1_spec__3(lean_object* v___x_2508_, lean_object* v_00_u03c3_2509_, lean_object* v_00_u03b2_2510_, lean_object* v_map_2511_, lean_object* v_f_2512_, lean_object* v_init_2513_){
_start:
{
lean_object* v___x_2514_; 
v___x_2514_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_f_2512_, v_map_2511_, v_init_2513_);
return v___x_2514_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v___x_2515_, lean_object* v_00_u03c3_2516_, lean_object* v_00_u03b2_2517_, lean_object* v_map_2518_, lean_object* v_f_2519_, lean_object* v_init_2520_){
_start:
{
lean_object* v_res_2521_; 
v_res_2521_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0_spec__1_spec__3(v___x_2515_, v_00_u03c3_2516_, v_00_u03b2_2517_, v_map_2518_, v_f_2519_, v_init_2520_);
lean_dec_ref(v_map_2518_);
lean_dec_ref(v___x_2515_);
return v_res_2521_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0_spec__1_spec__3_spec__5(lean_object* v_00_u03c3_2522_, lean_object* v_00_u03b1_2523_, lean_object* v_00_u03b2_2524_, lean_object* v_f_2525_, lean_object* v_x_2526_, lean_object* v_x_2527_){
_start:
{
lean_object* v___x_2528_; 
v___x_2528_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_f_2525_, v_x_2526_, v_x_2527_);
return v___x_2528_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0_spec__1_spec__3_spec__5___boxed(lean_object* v_00_u03c3_2529_, lean_object* v_00_u03b1_2530_, lean_object* v_00_u03b2_2531_, lean_object* v_f_2532_, lean_object* v_x_2533_, lean_object* v_x_2534_){
_start:
{
lean_object* v_res_2535_; 
v_res_2535_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0_spec__1_spec__3_spec__5(v_00_u03c3_2529_, v_00_u03b1_2530_, v_00_u03b2_2531_, v_f_2532_, v_x_2533_, v_x_2534_);
lean_dec_ref(v_x_2533_);
return v_res_2535_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6(lean_object* v_00_u03b1_2536_, lean_object* v_00_u03b2_2537_, lean_object* v_00_u03c3_2538_, lean_object* v_f_2539_, lean_object* v_as_2540_, size_t v_i_2541_, size_t v_stop_2542_, lean_object* v_b_2543_){
_start:
{
lean_object* v___x_2544_; 
v___x_2544_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg(v_f_2539_, v_as_2540_, v_i_2541_, v_stop_2542_, v_b_2543_);
return v___x_2544_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_2539_ = stack[3].m_obj;
lean_object* v_as_2540_ = stack[4].m_obj;
size_t v_i_2541_ = stack[5].m_num;
size_t v_stop_2542_ = stack[6].m_num;
lean_object* v_b_2543_ = stack[7].m_obj;
lean_object* v_res_2545_;
v_res_2545_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6(lean_box(0), lean_box(0), lean_box(0), v_f_2539_, v_as_2540_, v_i_2541_, v_stop_2542_, v_b_2543_);
stack->m_obj
 = v_res_2545_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___boxed(lean_object* v_00_u03b1_2546_, lean_object* v_00_u03b2_2547_, lean_object* v_00_u03c3_2548_, lean_object* v_f_2549_, lean_object* v_as_2550_, lean_object* v_i_2551_, lean_object* v_stop_2552_, lean_object* v_b_2553_){
_start:
{
size_t v_i_boxed_2554_; size_t v_stop_boxed_2555_; lean_object* v_res_2556_; 
v_i_boxed_2554_ = lean_unbox_usize(v_i_2551_);
lean_dec(v_i_2551_);
v_stop_boxed_2555_ = lean_unbox_usize(v_stop_2552_);
lean_dec(v_stop_2552_);
v_res_2556_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6(v_00_u03b1_2546_, v_00_u03b2_2547_, v_00_u03c3_2548_, v_f_2549_, v_as_2550_, v_i_boxed_2554_, v_stop_boxed_2555_, v_b_2553_);
lean_dec_ref(v_as_2550_);
return v_res_2556_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7(lean_object* v_00_u03c3_2557_, lean_object* v_00_u03b1_2558_, lean_object* v_00_u03b2_2559_, lean_object* v_f_2560_, lean_object* v_keys_2561_, lean_object* v_vals_2562_, lean_object* v_heq_2563_, lean_object* v_i_2564_, lean_object* v_acc_2565_){
_start:
{
lean_object* v___x_2566_; 
v___x_2566_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7___redArg(v_f_2560_, v_keys_2561_, v_vals_2562_, v_i_2564_, v_acc_2565_);
return v___x_2566_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7___boxed(lean_object* v_00_u03c3_2567_, lean_object* v_00_u03b1_2568_, lean_object* v_00_u03b2_2569_, lean_object* v_f_2570_, lean_object* v_keys_2571_, lean_object* v_vals_2572_, lean_object* v_heq_2573_, lean_object* v_i_2574_, lean_object* v_acc_2575_){
_start:
{
lean_object* v_res_2576_; 
v_res_2576_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7(v_00_u03c3_2567_, v_00_u03b1_2568_, v_00_u03b2_2569_, v_f_2570_, v_keys_2571_, v_vals_2572_, v_heq_2573_, v_i_2574_, v_acc_2575_);
lean_dec_ref(v_vals_2572_);
lean_dec_ref(v_keys_2571_);
return v_res_2576_;
}
}
uint8_t l_Lean_Option_get___at___00Lean_Meta_Grind_checkInvariants_spec__0(lean_object* v_opts_2577_, lean_object* v_opt_2578_){
_start:
{
lean_object* v_name_2579_; lean_object* v_defValue_2580_; lean_object* v_map_2581_; lean_object* v___x_2582_; 
v_name_2579_ = lean_ctor_get(v_opt_2578_, 0);
v_defValue_2580_ = lean_ctor_get(v_opt_2578_, 1);
v_map_2581_ = lean_ctor_get(v_opts_2577_, 0);
v___x_2582_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2581_, v_name_2579_);
if (lean_obj_tag(v___x_2582_) == 0)
{
uint8_t v___x_2583_; 
v___x_2583_ = lean_unbox(v_defValue_2580_);
return v___x_2583_;
}
else
{
lean_object* v_val_2584_; 
v_val_2584_ = lean_ctor_get(v___x_2582_, 0);
lean_inc(v_val_2584_);
lean_dec_ref_known(v___x_2582_, 1);
if (lean_obj_tag(v_val_2584_) == 1)
{
uint8_t v_v_2585_; 
v_v_2585_ = lean_ctor_get_uint8(v_val_2584_, 0);
lean_dec_ref_known(v_val_2584_, 0);
return v_v_2585_;
}
else
{
uint8_t v___x_2586_; 
lean_dec(v_val_2584_);
v___x_2586_ = lean_unbox(v_defValue_2580_);
return v___x_2586_;
}
}
}
}
LEAN_EXPORT void l_Lean_Option_get___at___00Lean_Meta_Grind_checkInvariants_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_2577_ = stack[0].m_obj;
lean_object* v_opt_2578_ = stack[1].m_obj;
uint8_t v_res_2587_;
v_res_2587_ = l_Lean_Option_get___at___00Lean_Meta_Grind_checkInvariants_spec__0(v_opts_2577_, v_opt_2578_);
stack->m_num = v_res_2587_;
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Grind_checkInvariants_spec__0___boxed(lean_object* v_opts_2588_, lean_object* v_opt_2589_){
_start:
{
uint8_t v_res_2590_; lean_object* v_r_2591_; 
v_res_2590_ = l_Lean_Option_get___at___00Lean_Meta_Grind_checkInvariants_spec__0(v_opts_2588_, v_opt_2589_);
lean_dec_ref(v_opt_2589_);
lean_dec_ref(v_opts_2588_);
v_r_2591_ = lean_box(v_res_2590_);
return v_r_2591_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__2_spec__5___closed__2(void){
_start:
{
lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; 
v___x_2594_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__2_spec__5___closed__1));
v___x_2595_ = lean_unsigned_to_nat(8u);
v___x_2596_ = lean_unsigned_to_nat(146u);
v___x_2597_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__2_spec__5___closed__0));
v___x_2598_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__0));
v___x_2599_ = l_mkPanicMessageWithDecl(v___x_2598_, v___x_2597_, v___x_2596_, v___x_2595_, v___x_2594_);
return v___x_2599_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__2_spec__5(lean_object* v_as_2600_, size_t v_sz_2601_, size_t v_i_2602_, lean_object* v_b_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_, lean_object* v___y_2613_){
_start:
{
uint8_t v___x_2615_; 
v___x_2615_ = lean_usize_dec_lt(v_i_2602_, v_sz_2601_);
if (v___x_2615_ == 0)
{
lean_object* v___x_2616_; 
v___x_2616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2616_, 0, v_b_2603_);
return v___x_2616_;
}
else
{
lean_object* v_snd_2617_; lean_object* v___x_2619_; uint8_t v_isShared_2620_; uint8_t v_isSharedCheck_2714_; 
v_snd_2617_ = lean_ctor_get(v_b_2603_, 1);
v_isSharedCheck_2714_ = !lean_is_exclusive(v_b_2603_);
if (v_isSharedCheck_2714_ == 0)
{
lean_object* v_unused_2715_; 
v_unused_2715_ = lean_ctor_get(v_b_2603_, 0);
lean_dec(v_unused_2715_);
v___x_2619_ = v_b_2603_;
v_isShared_2620_ = v_isSharedCheck_2714_;
goto v_resetjp_2618_;
}
else
{
lean_inc(v_snd_2617_);
lean_dec(v_b_2603_);
v___x_2619_ = lean_box(0);
v_isShared_2620_ = v_isSharedCheck_2714_;
goto v_resetjp_2618_;
}
v_resetjp_2618_:
{
lean_object* v___x_2621_; lean_object* v_a_2623_; lean_object* v___x_2630_; lean_object* v_a_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; 
v___x_2621_ = lean_box(0);
v___x_2630_ = lean_box(0);
v_a_2631_ = lean_array_uget_borrowed(v_as_2600_, v_i_2602_);
v___x_2632_ = lean_st_ref_get(v___y_2604_);
lean_inc(v_a_2631_);
v___x_2633_ = l_Lean_Meta_Grind_Goal_getENode(v___x_2632_, v_a_2631_, v___y_2610_, v___y_2611_, v___y_2612_, v___y_2613_);
lean_dec(v___x_2632_);
if (lean_obj_tag(v___x_2633_) == 0)
{
lean_object* v_a_2634_; lean_object* v___y_2636_; lean_object* v___y_2637_; lean_object* v___y_2638_; lean_object* v___y_2639_; lean_object* v___y_2640_; lean_object* v___y_2641_; lean_object* v___y_2642_; lean_object* v___y_2643_; lean_object* v___y_2644_; lean_object* v___y_2645_; lean_object* v_self_2656_; uint8_t v_interpreted_2657_; lean_object* v___x_2658_; 
v_a_2634_ = lean_ctor_get(v___x_2633_, 0);
lean_inc(v_a_2634_);
lean_dec_ref_known(v___x_2633_, 1);
v_self_2656_ = lean_ctor_get(v_a_2634_, 0);
v_interpreted_2657_ = lean_ctor_get_uint8(v_a_2634_, sizeof(void*)*12 + 1);
lean_inc_ref(v_self_2656_);
v___x_2658_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents(v_self_2656_, v___y_2604_, v___y_2605_, v___y_2606_, v___y_2607_, v___y_2608_, v___y_2609_, v___y_2610_, v___y_2611_, v___y_2612_, v___y_2613_);
if (lean_obj_tag(v___x_2658_) == 0)
{
lean_dec_ref_known(v___x_2658_, 1);
if (v_interpreted_2657_ == 0)
{
lean_dec(v_snd_2617_);
v___y_2636_ = v___y_2604_;
v___y_2637_ = v___y_2605_;
v___y_2638_ = v___y_2606_;
v___y_2639_ = v___y_2607_;
v___y_2640_ = v___y_2608_;
v___y_2641_ = v___y_2609_;
v___y_2642_ = v___y_2610_;
v___y_2643_ = v___y_2611_;
v___y_2644_ = v___y_2612_;
v___y_2645_ = v___y_2613_;
goto v___jp_2635_;
}
else
{
lean_object* v___x_2659_; 
lean_inc_ref(v_self_2656_);
v___x_2659_ = l_Lean_Meta_Sym_Canon_normNumLit_x3f(v_self_2656_, v___y_2610_, v___y_2611_, v___y_2612_, v___y_2613_);
if (lean_obj_tag(v___x_2659_) == 0)
{
lean_object* v_a_2660_; 
v_a_2660_ = lean_ctor_get(v___x_2659_, 0);
lean_inc(v_a_2660_);
lean_dec_ref_known(v___x_2659_, 1);
if (lean_obj_tag(v_a_2660_) == 0)
{
lean_dec(v_snd_2617_);
v___y_2636_ = v___y_2604_;
v___y_2637_ = v___y_2605_;
v___y_2638_ = v___y_2606_;
v___y_2639_ = v___y_2607_;
v___y_2640_ = v___y_2608_;
v___y_2641_ = v___y_2609_;
v___y_2642_ = v___y_2610_;
v___y_2643_ = v___y_2611_;
v___y_2644_ = v___y_2612_;
v___y_2645_ = v___y_2613_;
goto v___jp_2635_;
}
else
{
lean_object* v___x_2662_; uint8_t v_isShared_2663_; uint8_t v_isSharedCheck_2688_; 
lean_dec(v_a_2634_);
v_isSharedCheck_2688_ = !lean_is_exclusive(v_a_2660_);
if (v_isSharedCheck_2688_ == 0)
{
lean_object* v_unused_2689_; 
v_unused_2689_ = lean_ctor_get(v_a_2660_, 0);
lean_dec(v_unused_2689_);
v___x_2662_ = v_a_2660_;
v_isShared_2663_ = v_isSharedCheck_2688_;
goto v_resetjp_2661_;
}
else
{
lean_dec(v_a_2660_);
v___x_2662_ = lean_box(0);
v_isShared_2663_ = v_isSharedCheck_2688_;
goto v_resetjp_2661_;
}
v_resetjp_2661_:
{
lean_object* v___x_2664_; lean_object* v___x_2665_; 
v___x_2664_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__2_spec__5___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__2_spec__5___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__2_spec__5___closed__2);
v___x_2665_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__0(v___x_2664_, v___y_2604_, v___y_2605_, v___y_2606_, v___y_2607_, v___y_2608_, v___y_2609_, v___y_2610_, v___y_2611_, v___y_2612_, v___y_2613_);
if (lean_obj_tag(v___x_2665_) == 0)
{
lean_object* v_a_2666_; lean_object* v___x_2668_; uint8_t v_isShared_2669_; uint8_t v_isSharedCheck_2679_; 
v_a_2666_ = lean_ctor_get(v___x_2665_, 0);
v_isSharedCheck_2679_ = !lean_is_exclusive(v___x_2665_);
if (v_isSharedCheck_2679_ == 0)
{
v___x_2668_ = v___x_2665_;
v_isShared_2669_ = v_isSharedCheck_2679_;
goto v_resetjp_2667_;
}
else
{
lean_inc(v_a_2666_);
lean_dec(v___x_2665_);
v___x_2668_ = lean_box(0);
v_isShared_2669_ = v_isSharedCheck_2679_;
goto v_resetjp_2667_;
}
v_resetjp_2667_:
{
if (lean_obj_tag(v_a_2666_) == 0)
{
lean_object* v_a_2670_; lean_object* v___x_2672_; 
lean_del_object(v___x_2619_);
v_a_2670_ = lean_ctor_get(v_a_2666_, 0);
lean_inc(v_a_2670_);
lean_dec_ref_known(v_a_2666_, 1);
if (v_isShared_2663_ == 0)
{
lean_ctor_set(v___x_2662_, 0, v_a_2670_);
v___x_2672_ = v___x_2662_;
goto v_reusejp_2671_;
}
else
{
lean_object* v_reuseFailAlloc_2677_; 
v_reuseFailAlloc_2677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2677_, 0, v_a_2670_);
v___x_2672_ = v_reuseFailAlloc_2677_;
goto v_reusejp_2671_;
}
v_reusejp_2671_:
{
lean_object* v___x_2673_; lean_object* v___x_2675_; 
v___x_2673_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2673_, 0, v___x_2672_);
lean_ctor_set(v___x_2673_, 1, v_snd_2617_);
if (v_isShared_2669_ == 0)
{
lean_ctor_set(v___x_2668_, 0, v___x_2673_);
v___x_2675_ = v___x_2668_;
goto v_reusejp_2674_;
}
else
{
lean_object* v_reuseFailAlloc_2676_; 
v_reuseFailAlloc_2676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2676_, 0, v___x_2673_);
v___x_2675_ = v_reuseFailAlloc_2676_;
goto v_reusejp_2674_;
}
v_reusejp_2674_:
{
return v___x_2675_;
}
}
}
else
{
lean_object* v_a_2678_; 
lean_del_object(v___x_2668_);
lean_del_object(v___x_2662_);
lean_dec(v_snd_2617_);
v_a_2678_ = lean_ctor_get(v_a_2666_, 0);
lean_inc(v_a_2678_);
lean_dec_ref_known(v_a_2666_, 1);
v_a_2623_ = v_a_2678_;
goto v___jp_2622_;
}
}
}
else
{
lean_object* v_a_2680_; lean_object* v___x_2682_; uint8_t v_isShared_2683_; uint8_t v_isSharedCheck_2687_; 
lean_del_object(v___x_2662_);
lean_del_object(v___x_2619_);
lean_dec(v_snd_2617_);
v_a_2680_ = lean_ctor_get(v___x_2665_, 0);
v_isSharedCheck_2687_ = !lean_is_exclusive(v___x_2665_);
if (v_isSharedCheck_2687_ == 0)
{
v___x_2682_ = v___x_2665_;
v_isShared_2683_ = v_isSharedCheck_2687_;
goto v_resetjp_2681_;
}
else
{
lean_inc(v_a_2680_);
lean_dec(v___x_2665_);
v___x_2682_ = lean_box(0);
v_isShared_2683_ = v_isSharedCheck_2687_;
goto v_resetjp_2681_;
}
v_resetjp_2681_:
{
lean_object* v___x_2685_; 
if (v_isShared_2683_ == 0)
{
v___x_2685_ = v___x_2682_;
goto v_reusejp_2684_;
}
else
{
lean_object* v_reuseFailAlloc_2686_; 
v_reuseFailAlloc_2686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2686_, 0, v_a_2680_);
v___x_2685_ = v_reuseFailAlloc_2686_;
goto v_reusejp_2684_;
}
v_reusejp_2684_:
{
return v___x_2685_;
}
}
}
}
}
}
else
{
lean_object* v_a_2690_; lean_object* v___x_2692_; uint8_t v_isShared_2693_; uint8_t v_isSharedCheck_2697_; 
lean_dec(v_a_2634_);
lean_del_object(v___x_2619_);
lean_dec(v_snd_2617_);
v_a_2690_ = lean_ctor_get(v___x_2659_, 0);
v_isSharedCheck_2697_ = !lean_is_exclusive(v___x_2659_);
if (v_isSharedCheck_2697_ == 0)
{
v___x_2692_ = v___x_2659_;
v_isShared_2693_ = v_isSharedCheck_2697_;
goto v_resetjp_2691_;
}
else
{
lean_inc(v_a_2690_);
lean_dec(v___x_2659_);
v___x_2692_ = lean_box(0);
v_isShared_2693_ = v_isSharedCheck_2697_;
goto v_resetjp_2691_;
}
v_resetjp_2691_:
{
lean_object* v___x_2695_; 
if (v_isShared_2693_ == 0)
{
v___x_2695_ = v___x_2692_;
goto v_reusejp_2694_;
}
else
{
lean_object* v_reuseFailAlloc_2696_; 
v_reuseFailAlloc_2696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2696_, 0, v_a_2690_);
v___x_2695_ = v_reuseFailAlloc_2696_;
goto v_reusejp_2694_;
}
v_reusejp_2694_:
{
return v___x_2695_;
}
}
}
}
}
else
{
lean_object* v_a_2698_; lean_object* v___x_2700_; uint8_t v_isShared_2701_; uint8_t v_isSharedCheck_2705_; 
lean_dec(v_a_2634_);
lean_del_object(v___x_2619_);
lean_dec(v_snd_2617_);
v_a_2698_ = lean_ctor_get(v___x_2658_, 0);
v_isSharedCheck_2705_ = !lean_is_exclusive(v___x_2658_);
if (v_isSharedCheck_2705_ == 0)
{
v___x_2700_ = v___x_2658_;
v_isShared_2701_ = v_isSharedCheck_2705_;
goto v_resetjp_2699_;
}
else
{
lean_inc(v_a_2698_);
lean_dec(v___x_2658_);
v___x_2700_ = lean_box(0);
v_isShared_2701_ = v_isSharedCheck_2705_;
goto v_resetjp_2699_;
}
v_resetjp_2699_:
{
lean_object* v___x_2703_; 
if (v_isShared_2701_ == 0)
{
v___x_2703_ = v___x_2700_;
goto v_reusejp_2702_;
}
else
{
lean_object* v_reuseFailAlloc_2704_; 
v_reuseFailAlloc_2704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2704_, 0, v_a_2698_);
v___x_2703_ = v_reuseFailAlloc_2704_;
goto v_reusejp_2702_;
}
v_reusejp_2702_:
{
return v___x_2703_;
}
}
}
v___jp_2635_:
{
uint8_t v___x_2646_; 
v___x_2646_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_2634_);
if (v___x_2646_ == 0)
{
lean_dec(v_a_2634_);
v_a_2623_ = v___x_2630_;
goto v___jp_2622_;
}
else
{
lean_object* v___x_2647_; 
v___x_2647_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc(v_a_2634_, v___y_2636_, v___y_2637_, v___y_2638_, v___y_2639_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_);
if (lean_obj_tag(v___x_2647_) == 0)
{
lean_dec_ref_known(v___x_2647_, 1);
v_a_2623_ = v___x_2630_;
goto v___jp_2622_;
}
else
{
lean_object* v_a_2648_; lean_object* v___x_2650_; uint8_t v_isShared_2651_; uint8_t v_isSharedCheck_2655_; 
lean_del_object(v___x_2619_);
v_a_2648_ = lean_ctor_get(v___x_2647_, 0);
v_isSharedCheck_2655_ = !lean_is_exclusive(v___x_2647_);
if (v_isSharedCheck_2655_ == 0)
{
v___x_2650_ = v___x_2647_;
v_isShared_2651_ = v_isSharedCheck_2655_;
goto v_resetjp_2649_;
}
else
{
lean_inc(v_a_2648_);
lean_dec(v___x_2647_);
v___x_2650_ = lean_box(0);
v_isShared_2651_ = v_isSharedCheck_2655_;
goto v_resetjp_2649_;
}
v_resetjp_2649_:
{
lean_object* v___x_2653_; 
if (v_isShared_2651_ == 0)
{
v___x_2653_ = v___x_2650_;
goto v_reusejp_2652_;
}
else
{
lean_object* v_reuseFailAlloc_2654_; 
v_reuseFailAlloc_2654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2654_, 0, v_a_2648_);
v___x_2653_ = v_reuseFailAlloc_2654_;
goto v_reusejp_2652_;
}
v_reusejp_2652_:
{
return v___x_2653_;
}
}
}
}
}
}
else
{
lean_object* v_a_2706_; lean_object* v___x_2708_; uint8_t v_isShared_2709_; uint8_t v_isSharedCheck_2713_; 
lean_del_object(v___x_2619_);
lean_dec(v_snd_2617_);
v_a_2706_ = lean_ctor_get(v___x_2633_, 0);
v_isSharedCheck_2713_ = !lean_is_exclusive(v___x_2633_);
if (v_isSharedCheck_2713_ == 0)
{
v___x_2708_ = v___x_2633_;
v_isShared_2709_ = v_isSharedCheck_2713_;
goto v_resetjp_2707_;
}
else
{
lean_inc(v_a_2706_);
lean_dec(v___x_2633_);
v___x_2708_ = lean_box(0);
v_isShared_2709_ = v_isSharedCheck_2713_;
goto v_resetjp_2707_;
}
v_resetjp_2707_:
{
lean_object* v___x_2711_; 
if (v_isShared_2709_ == 0)
{
v___x_2711_ = v___x_2708_;
goto v_reusejp_2710_;
}
else
{
lean_object* v_reuseFailAlloc_2712_; 
v_reuseFailAlloc_2712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2712_, 0, v_a_2706_);
v___x_2711_ = v_reuseFailAlloc_2712_;
goto v_reusejp_2710_;
}
v_reusejp_2710_:
{
return v___x_2711_;
}
}
}
v___jp_2622_:
{
lean_object* v___x_2625_; 
if (v_isShared_2620_ == 0)
{
lean_ctor_set(v___x_2619_, 1, v_a_2623_);
lean_ctor_set(v___x_2619_, 0, v___x_2621_);
v___x_2625_ = v___x_2619_;
goto v_reusejp_2624_;
}
else
{
lean_object* v_reuseFailAlloc_2629_; 
v_reuseFailAlloc_2629_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2629_, 0, v___x_2621_);
lean_ctor_set(v_reuseFailAlloc_2629_, 1, v_a_2623_);
v___x_2625_ = v_reuseFailAlloc_2629_;
goto v_reusejp_2624_;
}
v_reusejp_2624_:
{
size_t v___x_2626_; size_t v___x_2627_; 
v___x_2626_ = ((size_t)1ULL);
v___x_2627_ = lean_usize_add(v_i_2602_, v___x_2626_);
v_i_2602_ = v___x_2627_;
v_b_2603_ = v___x_2625_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__2_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2600_ = stack[0].m_obj;
size_t v_sz_2601_ = stack[1].m_num;
size_t v_i_2602_ = stack[2].m_num;
lean_object* v_b_2603_ = stack[3].m_obj;
lean_object* v___y_2604_ = stack[4].m_obj;
lean_object* v___y_2605_ = stack[5].m_obj;
lean_object* v___y_2606_ = stack[6].m_obj;
lean_object* v___y_2607_ = stack[7].m_obj;
lean_object* v___y_2608_ = stack[8].m_obj;
lean_object* v___y_2609_ = stack[9].m_obj;
lean_object* v___y_2610_ = stack[10].m_obj;
lean_object* v___y_2611_ = stack[11].m_obj;
lean_object* v___y_2612_ = stack[12].m_obj;
lean_object* v___y_2613_ = stack[13].m_obj;
lean_object* v_res_2716_;
v_res_2716_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__2_spec__5(v_as_2600_, v_sz_2601_, v_i_2602_, v_b_2603_, v___y_2604_, v___y_2605_, v___y_2606_, v___y_2607_, v___y_2608_, v___y_2609_, v___y_2610_, v___y_2611_, v___y_2612_, v___y_2613_);
stack->m_obj
 = v_res_2716_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__2_spec__5___boxed(lean_object* v_as_2717_, lean_object* v_sz_2718_, lean_object* v_i_2719_, lean_object* v_b_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_){
_start:
{
size_t v_sz_boxed_2732_; size_t v_i_boxed_2733_; lean_object* v_res_2734_; 
v_sz_boxed_2732_ = lean_unbox_usize(v_sz_2718_);
lean_dec(v_sz_2718_);
v_i_boxed_2733_ = lean_unbox_usize(v_i_2719_);
lean_dec(v_i_2719_);
v_res_2734_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__2_spec__5(v_as_2717_, v_sz_boxed_2732_, v_i_boxed_2733_, v_b_2720_, v___y_2721_, v___y_2722_, v___y_2723_, v___y_2724_, v___y_2725_, v___y_2726_, v___y_2727_, v___y_2728_, v___y_2729_, v___y_2730_);
lean_dec(v___y_2730_);
lean_dec_ref(v___y_2729_);
lean_dec(v___y_2728_);
lean_dec_ref(v___y_2727_);
lean_dec(v___y_2726_);
lean_dec_ref(v___y_2725_);
lean_dec(v___y_2724_);
lean_dec_ref(v___y_2723_);
lean_dec(v___y_2722_);
lean_dec(v___y_2721_);
lean_dec_ref(v_as_2717_);
return v_res_2734_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__2(lean_object* v_as_2735_, size_t v_sz_2736_, size_t v_i_2737_, lean_object* v_b_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_){
_start:
{
uint8_t v___x_2750_; 
v___x_2750_ = lean_usize_dec_lt(v_i_2737_, v_sz_2736_);
if (v___x_2750_ == 0)
{
lean_object* v___x_2751_; 
v___x_2751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2751_, 0, v_b_2738_);
return v___x_2751_;
}
else
{
lean_object* v_snd_2752_; lean_object* v___x_2754_; uint8_t v_isShared_2755_; uint8_t v_isSharedCheck_2849_; 
v_snd_2752_ = lean_ctor_get(v_b_2738_, 1);
v_isSharedCheck_2849_ = !lean_is_exclusive(v_b_2738_);
if (v_isSharedCheck_2849_ == 0)
{
lean_object* v_unused_2850_; 
v_unused_2850_ = lean_ctor_get(v_b_2738_, 0);
lean_dec(v_unused_2850_);
v___x_2754_ = v_b_2738_;
v_isShared_2755_ = v_isSharedCheck_2849_;
goto v_resetjp_2753_;
}
else
{
lean_inc(v_snd_2752_);
lean_dec(v_b_2738_);
v___x_2754_ = lean_box(0);
v_isShared_2755_ = v_isSharedCheck_2849_;
goto v_resetjp_2753_;
}
v_resetjp_2753_:
{
lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v_a_2759_; lean_object* v_a_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; 
v___x_2756_ = lean_box(0);
v___x_2757_ = lean_box(0);
v_a_2766_ = lean_array_uget_borrowed(v_as_2735_, v_i_2737_);
v___x_2767_ = lean_st_ref_get(v___y_2739_);
lean_inc(v_a_2766_);
v___x_2768_ = l_Lean_Meta_Grind_Goal_getENode(v___x_2767_, v_a_2766_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_);
lean_dec(v___x_2767_);
if (lean_obj_tag(v___x_2768_) == 0)
{
lean_object* v_a_2769_; lean_object* v___y_2771_; lean_object* v___y_2772_; lean_object* v___y_2773_; lean_object* v___y_2774_; lean_object* v___y_2775_; lean_object* v___y_2776_; lean_object* v___y_2777_; lean_object* v___y_2778_; lean_object* v___y_2779_; lean_object* v___y_2780_; lean_object* v_self_2791_; uint8_t v_interpreted_2792_; lean_object* v___x_2793_; 
v_a_2769_ = lean_ctor_get(v___x_2768_, 0);
lean_inc(v_a_2769_);
lean_dec_ref_known(v___x_2768_, 1);
v_self_2791_ = lean_ctor_get(v_a_2769_, 0);
v_interpreted_2792_ = lean_ctor_get_uint8(v_a_2769_, sizeof(void*)*12 + 1);
lean_inc_ref(v_self_2791_);
v___x_2793_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents(v_self_2791_, v___y_2739_, v___y_2740_, v___y_2741_, v___y_2742_, v___y_2743_, v___y_2744_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_);
if (lean_obj_tag(v___x_2793_) == 0)
{
lean_dec_ref_known(v___x_2793_, 1);
if (v_interpreted_2792_ == 0)
{
lean_dec(v_snd_2752_);
v___y_2771_ = v___y_2739_;
v___y_2772_ = v___y_2740_;
v___y_2773_ = v___y_2741_;
v___y_2774_ = v___y_2742_;
v___y_2775_ = v___y_2743_;
v___y_2776_ = v___y_2744_;
v___y_2777_ = v___y_2745_;
v___y_2778_ = v___y_2746_;
v___y_2779_ = v___y_2747_;
v___y_2780_ = v___y_2748_;
goto v___jp_2770_;
}
else
{
lean_object* v___x_2794_; 
lean_inc_ref(v_self_2791_);
v___x_2794_ = l_Lean_Meta_Sym_Canon_normNumLit_x3f(v_self_2791_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_);
if (lean_obj_tag(v___x_2794_) == 0)
{
lean_object* v_a_2795_; 
v_a_2795_ = lean_ctor_get(v___x_2794_, 0);
lean_inc(v_a_2795_);
lean_dec_ref_known(v___x_2794_, 1);
if (lean_obj_tag(v_a_2795_) == 0)
{
lean_dec(v_snd_2752_);
v___y_2771_ = v___y_2739_;
v___y_2772_ = v___y_2740_;
v___y_2773_ = v___y_2741_;
v___y_2774_ = v___y_2742_;
v___y_2775_ = v___y_2743_;
v___y_2776_ = v___y_2744_;
v___y_2777_ = v___y_2745_;
v___y_2778_ = v___y_2746_;
v___y_2779_ = v___y_2747_;
v___y_2780_ = v___y_2748_;
goto v___jp_2770_;
}
else
{
lean_object* v___x_2797_; uint8_t v_isShared_2798_; uint8_t v_isSharedCheck_2823_; 
lean_dec(v_a_2769_);
v_isSharedCheck_2823_ = !lean_is_exclusive(v_a_2795_);
if (v_isSharedCheck_2823_ == 0)
{
lean_object* v_unused_2824_; 
v_unused_2824_ = lean_ctor_get(v_a_2795_, 0);
lean_dec(v_unused_2824_);
v___x_2797_ = v_a_2795_;
v_isShared_2798_ = v_isSharedCheck_2823_;
goto v_resetjp_2796_;
}
else
{
lean_dec(v_a_2795_);
v___x_2797_ = lean_box(0);
v_isShared_2798_ = v_isSharedCheck_2823_;
goto v_resetjp_2796_;
}
v_resetjp_2796_:
{
lean_object* v___x_2799_; lean_object* v___x_2800_; 
v___x_2799_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__2_spec__5___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__2_spec__5___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__2_spec__5___closed__2);
v___x_2800_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__0(v___x_2799_, v___y_2739_, v___y_2740_, v___y_2741_, v___y_2742_, v___y_2743_, v___y_2744_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_);
if (lean_obj_tag(v___x_2800_) == 0)
{
lean_object* v_a_2801_; lean_object* v___x_2803_; uint8_t v_isShared_2804_; uint8_t v_isSharedCheck_2814_; 
v_a_2801_ = lean_ctor_get(v___x_2800_, 0);
v_isSharedCheck_2814_ = !lean_is_exclusive(v___x_2800_);
if (v_isSharedCheck_2814_ == 0)
{
v___x_2803_ = v___x_2800_;
v_isShared_2804_ = v_isSharedCheck_2814_;
goto v_resetjp_2802_;
}
else
{
lean_inc(v_a_2801_);
lean_dec(v___x_2800_);
v___x_2803_ = lean_box(0);
v_isShared_2804_ = v_isSharedCheck_2814_;
goto v_resetjp_2802_;
}
v_resetjp_2802_:
{
if (lean_obj_tag(v_a_2801_) == 0)
{
lean_object* v_a_2805_; lean_object* v___x_2807_; 
lean_del_object(v___x_2754_);
v_a_2805_ = lean_ctor_get(v_a_2801_, 0);
lean_inc(v_a_2805_);
lean_dec_ref_known(v_a_2801_, 1);
if (v_isShared_2798_ == 0)
{
lean_ctor_set(v___x_2797_, 0, v_a_2805_);
v___x_2807_ = v___x_2797_;
goto v_reusejp_2806_;
}
else
{
lean_object* v_reuseFailAlloc_2812_; 
v_reuseFailAlloc_2812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2812_, 0, v_a_2805_);
v___x_2807_ = v_reuseFailAlloc_2812_;
goto v_reusejp_2806_;
}
v_reusejp_2806_:
{
lean_object* v___x_2808_; lean_object* v___x_2810_; 
v___x_2808_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2808_, 0, v___x_2807_);
lean_ctor_set(v___x_2808_, 1, v_snd_2752_);
if (v_isShared_2804_ == 0)
{
lean_ctor_set(v___x_2803_, 0, v___x_2808_);
v___x_2810_ = v___x_2803_;
goto v_reusejp_2809_;
}
else
{
lean_object* v_reuseFailAlloc_2811_; 
v_reuseFailAlloc_2811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2811_, 0, v___x_2808_);
v___x_2810_ = v_reuseFailAlloc_2811_;
goto v_reusejp_2809_;
}
v_reusejp_2809_:
{
return v___x_2810_;
}
}
}
else
{
lean_object* v_a_2813_; 
lean_del_object(v___x_2803_);
lean_del_object(v___x_2797_);
lean_dec(v_snd_2752_);
v_a_2813_ = lean_ctor_get(v_a_2801_, 0);
lean_inc(v_a_2813_);
lean_dec_ref_known(v_a_2801_, 1);
v_a_2759_ = v_a_2813_;
goto v___jp_2758_;
}
}
}
else
{
lean_object* v_a_2815_; lean_object* v___x_2817_; uint8_t v_isShared_2818_; uint8_t v_isSharedCheck_2822_; 
lean_del_object(v___x_2797_);
lean_del_object(v___x_2754_);
lean_dec(v_snd_2752_);
v_a_2815_ = lean_ctor_get(v___x_2800_, 0);
v_isSharedCheck_2822_ = !lean_is_exclusive(v___x_2800_);
if (v_isSharedCheck_2822_ == 0)
{
v___x_2817_ = v___x_2800_;
v_isShared_2818_ = v_isSharedCheck_2822_;
goto v_resetjp_2816_;
}
else
{
lean_inc(v_a_2815_);
lean_dec(v___x_2800_);
v___x_2817_ = lean_box(0);
v_isShared_2818_ = v_isSharedCheck_2822_;
goto v_resetjp_2816_;
}
v_resetjp_2816_:
{
lean_object* v___x_2820_; 
if (v_isShared_2818_ == 0)
{
v___x_2820_ = v___x_2817_;
goto v_reusejp_2819_;
}
else
{
lean_object* v_reuseFailAlloc_2821_; 
v_reuseFailAlloc_2821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2821_, 0, v_a_2815_);
v___x_2820_ = v_reuseFailAlloc_2821_;
goto v_reusejp_2819_;
}
v_reusejp_2819_:
{
return v___x_2820_;
}
}
}
}
}
}
else
{
lean_object* v_a_2825_; lean_object* v___x_2827_; uint8_t v_isShared_2828_; uint8_t v_isSharedCheck_2832_; 
lean_dec(v_a_2769_);
lean_del_object(v___x_2754_);
lean_dec(v_snd_2752_);
v_a_2825_ = lean_ctor_get(v___x_2794_, 0);
v_isSharedCheck_2832_ = !lean_is_exclusive(v___x_2794_);
if (v_isSharedCheck_2832_ == 0)
{
v___x_2827_ = v___x_2794_;
v_isShared_2828_ = v_isSharedCheck_2832_;
goto v_resetjp_2826_;
}
else
{
lean_inc(v_a_2825_);
lean_dec(v___x_2794_);
v___x_2827_ = lean_box(0);
v_isShared_2828_ = v_isSharedCheck_2832_;
goto v_resetjp_2826_;
}
v_resetjp_2826_:
{
lean_object* v___x_2830_; 
if (v_isShared_2828_ == 0)
{
v___x_2830_ = v___x_2827_;
goto v_reusejp_2829_;
}
else
{
lean_object* v_reuseFailAlloc_2831_; 
v_reuseFailAlloc_2831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2831_, 0, v_a_2825_);
v___x_2830_ = v_reuseFailAlloc_2831_;
goto v_reusejp_2829_;
}
v_reusejp_2829_:
{
return v___x_2830_;
}
}
}
}
}
else
{
lean_object* v_a_2833_; lean_object* v___x_2835_; uint8_t v_isShared_2836_; uint8_t v_isSharedCheck_2840_; 
lean_dec(v_a_2769_);
lean_del_object(v___x_2754_);
lean_dec(v_snd_2752_);
v_a_2833_ = lean_ctor_get(v___x_2793_, 0);
v_isSharedCheck_2840_ = !lean_is_exclusive(v___x_2793_);
if (v_isSharedCheck_2840_ == 0)
{
v___x_2835_ = v___x_2793_;
v_isShared_2836_ = v_isSharedCheck_2840_;
goto v_resetjp_2834_;
}
else
{
lean_inc(v_a_2833_);
lean_dec(v___x_2793_);
v___x_2835_ = lean_box(0);
v_isShared_2836_ = v_isSharedCheck_2840_;
goto v_resetjp_2834_;
}
v_resetjp_2834_:
{
lean_object* v___x_2838_; 
if (v_isShared_2836_ == 0)
{
v___x_2838_ = v___x_2835_;
goto v_reusejp_2837_;
}
else
{
lean_object* v_reuseFailAlloc_2839_; 
v_reuseFailAlloc_2839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2839_, 0, v_a_2833_);
v___x_2838_ = v_reuseFailAlloc_2839_;
goto v_reusejp_2837_;
}
v_reusejp_2837_:
{
return v___x_2838_;
}
}
}
v___jp_2770_:
{
uint8_t v___x_2781_; 
v___x_2781_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_2769_);
if (v___x_2781_ == 0)
{
lean_dec(v_a_2769_);
v_a_2759_ = v___x_2756_;
goto v___jp_2758_;
}
else
{
lean_object* v___x_2782_; 
v___x_2782_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc(v_a_2769_, v___y_2771_, v___y_2772_, v___y_2773_, v___y_2774_, v___y_2775_, v___y_2776_, v___y_2777_, v___y_2778_, v___y_2779_, v___y_2780_);
if (lean_obj_tag(v___x_2782_) == 0)
{
lean_dec_ref_known(v___x_2782_, 1);
v_a_2759_ = v___x_2756_;
goto v___jp_2758_;
}
else
{
lean_object* v_a_2783_; lean_object* v___x_2785_; uint8_t v_isShared_2786_; uint8_t v_isSharedCheck_2790_; 
lean_del_object(v___x_2754_);
v_a_2783_ = lean_ctor_get(v___x_2782_, 0);
v_isSharedCheck_2790_ = !lean_is_exclusive(v___x_2782_);
if (v_isSharedCheck_2790_ == 0)
{
v___x_2785_ = v___x_2782_;
v_isShared_2786_ = v_isSharedCheck_2790_;
goto v_resetjp_2784_;
}
else
{
lean_inc(v_a_2783_);
lean_dec(v___x_2782_);
v___x_2785_ = lean_box(0);
v_isShared_2786_ = v_isSharedCheck_2790_;
goto v_resetjp_2784_;
}
v_resetjp_2784_:
{
lean_object* v___x_2788_; 
if (v_isShared_2786_ == 0)
{
v___x_2788_ = v___x_2785_;
goto v_reusejp_2787_;
}
else
{
lean_object* v_reuseFailAlloc_2789_; 
v_reuseFailAlloc_2789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2789_, 0, v_a_2783_);
v___x_2788_ = v_reuseFailAlloc_2789_;
goto v_reusejp_2787_;
}
v_reusejp_2787_:
{
return v___x_2788_;
}
}
}
}
}
}
else
{
lean_object* v_a_2841_; lean_object* v___x_2843_; uint8_t v_isShared_2844_; uint8_t v_isSharedCheck_2848_; 
lean_del_object(v___x_2754_);
lean_dec(v_snd_2752_);
v_a_2841_ = lean_ctor_get(v___x_2768_, 0);
v_isSharedCheck_2848_ = !lean_is_exclusive(v___x_2768_);
if (v_isSharedCheck_2848_ == 0)
{
v___x_2843_ = v___x_2768_;
v_isShared_2844_ = v_isSharedCheck_2848_;
goto v_resetjp_2842_;
}
else
{
lean_inc(v_a_2841_);
lean_dec(v___x_2768_);
v___x_2843_ = lean_box(0);
v_isShared_2844_ = v_isSharedCheck_2848_;
goto v_resetjp_2842_;
}
v_resetjp_2842_:
{
lean_object* v___x_2846_; 
if (v_isShared_2844_ == 0)
{
v___x_2846_ = v___x_2843_;
goto v_reusejp_2845_;
}
else
{
lean_object* v_reuseFailAlloc_2847_; 
v_reuseFailAlloc_2847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2847_, 0, v_a_2841_);
v___x_2846_ = v_reuseFailAlloc_2847_;
goto v_reusejp_2845_;
}
v_reusejp_2845_:
{
return v___x_2846_;
}
}
}
v___jp_2758_:
{
lean_object* v___x_2761_; 
if (v_isShared_2755_ == 0)
{
lean_ctor_set(v___x_2754_, 1, v_a_2759_);
lean_ctor_set(v___x_2754_, 0, v___x_2757_);
v___x_2761_ = v___x_2754_;
goto v_reusejp_2760_;
}
else
{
lean_object* v_reuseFailAlloc_2765_; 
v_reuseFailAlloc_2765_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2765_, 0, v___x_2757_);
lean_ctor_set(v_reuseFailAlloc_2765_, 1, v_a_2759_);
v___x_2761_ = v_reuseFailAlloc_2765_;
goto v_reusejp_2760_;
}
v_reusejp_2760_:
{
size_t v___x_2762_; size_t v___x_2763_; lean_object* v___x_2764_; 
v___x_2762_ = ((size_t)1ULL);
v___x_2763_ = lean_usize_add(v_i_2737_, v___x_2762_);
v___x_2764_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__2_spec__5(v_as_2735_, v_sz_2736_, v___x_2763_, v___x_2761_, v___y_2739_, v___y_2740_, v___y_2741_, v___y_2742_, v___y_2743_, v___y_2744_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_);
return v___x_2764_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2735_ = stack[0].m_obj;
size_t v_sz_2736_ = stack[1].m_num;
size_t v_i_2737_ = stack[2].m_num;
lean_object* v_b_2738_ = stack[3].m_obj;
lean_object* v___y_2739_ = stack[4].m_obj;
lean_object* v___y_2740_ = stack[5].m_obj;
lean_object* v___y_2741_ = stack[6].m_obj;
lean_object* v___y_2742_ = stack[7].m_obj;
lean_object* v___y_2743_ = stack[8].m_obj;
lean_object* v___y_2744_ = stack[9].m_obj;
lean_object* v___y_2745_ = stack[10].m_obj;
lean_object* v___y_2746_ = stack[11].m_obj;
lean_object* v___y_2747_ = stack[12].m_obj;
lean_object* v___y_2748_ = stack[13].m_obj;
lean_object* v_res_2851_;
v_res_2851_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__2(v_as_2735_, v_sz_2736_, v_i_2737_, v_b_2738_, v___y_2739_, v___y_2740_, v___y_2741_, v___y_2742_, v___y_2743_, v___y_2744_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_);
stack->m_obj
 = v_res_2851_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__2___boxed(lean_object* v_as_2852_, lean_object* v_sz_2853_, lean_object* v_i_2854_, lean_object* v_b_2855_, lean_object* v___y_2856_, lean_object* v___y_2857_, lean_object* v___y_2858_, lean_object* v___y_2859_, lean_object* v___y_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_, lean_object* v___y_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_){
_start:
{
size_t v_sz_boxed_2867_; size_t v_i_boxed_2868_; lean_object* v_res_2869_; 
v_sz_boxed_2867_ = lean_unbox_usize(v_sz_2853_);
lean_dec(v_sz_2853_);
v_i_boxed_2868_ = lean_unbox_usize(v_i_2854_);
lean_dec(v_i_2854_);
v_res_2869_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__2(v_as_2852_, v_sz_boxed_2867_, v_i_boxed_2868_, v_b_2855_, v___y_2856_, v___y_2857_, v___y_2858_, v___y_2859_, v___y_2860_, v___y_2861_, v___y_2862_, v___y_2863_, v___y_2864_, v___y_2865_);
lean_dec(v___y_2865_);
lean_dec_ref(v___y_2864_);
lean_dec(v___y_2863_);
lean_dec_ref(v___y_2862_);
lean_dec(v___y_2861_);
lean_dec_ref(v___y_2860_);
lean_dec(v___y_2859_);
lean_dec_ref(v___y_2858_);
lean_dec(v___y_2857_);
lean_dec(v___y_2856_);
lean_dec_ref(v_as_2852_);
return v_res_2869_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__1_spec__3_spec__4(lean_object* v_as_2870_, size_t v_sz_2871_, size_t v_i_2872_, lean_object* v_b_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_){
_start:
{
uint8_t v___x_2885_; 
v___x_2885_ = lean_usize_dec_lt(v_i_2872_, v_sz_2871_);
if (v___x_2885_ == 0)
{
lean_object* v___x_2886_; 
v___x_2886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2886_, 0, v_b_2873_);
return v___x_2886_;
}
else
{
lean_object* v_snd_2887_; lean_object* v___x_2889_; uint8_t v_isShared_2890_; uint8_t v_isSharedCheck_2983_; 
v_snd_2887_ = lean_ctor_get(v_b_2873_, 1);
v_isSharedCheck_2983_ = !lean_is_exclusive(v_b_2873_);
if (v_isSharedCheck_2983_ == 0)
{
lean_object* v_unused_2984_; 
v_unused_2984_ = lean_ctor_get(v_b_2873_, 0);
lean_dec(v_unused_2984_);
v___x_2889_ = v_b_2873_;
v_isShared_2890_ = v_isSharedCheck_2983_;
goto v_resetjp_2888_;
}
else
{
lean_inc(v_snd_2887_);
lean_dec(v_b_2873_);
v___x_2889_ = lean_box(0);
v_isShared_2890_ = v_isSharedCheck_2983_;
goto v_resetjp_2888_;
}
v_resetjp_2888_:
{
lean_object* v___x_2891_; lean_object* v_a_2893_; lean_object* v___x_2900_; lean_object* v_a_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; 
v___x_2891_ = lean_box(0);
v___x_2900_ = lean_box(0);
v_a_2901_ = lean_array_uget_borrowed(v_as_2870_, v_i_2872_);
v___x_2902_ = lean_st_ref_get(v___y_2874_);
lean_inc(v_a_2901_);
v___x_2903_ = l_Lean_Meta_Grind_Goal_getENode(v___x_2902_, v_a_2901_, v___y_2880_, v___y_2881_, v___y_2882_, v___y_2883_);
lean_dec(v___x_2902_);
if (lean_obj_tag(v___x_2903_) == 0)
{
lean_object* v_a_2904_; lean_object* v___y_2906_; lean_object* v___y_2907_; lean_object* v___y_2908_; lean_object* v___y_2909_; lean_object* v___y_2910_; lean_object* v___y_2911_; lean_object* v___y_2912_; lean_object* v___y_2913_; lean_object* v___y_2914_; lean_object* v___y_2915_; lean_object* v_self_2926_; uint8_t v_interpreted_2927_; lean_object* v___x_2928_; 
v_a_2904_ = lean_ctor_get(v___x_2903_, 0);
lean_inc(v_a_2904_);
lean_dec_ref_known(v___x_2903_, 1);
v_self_2926_ = lean_ctor_get(v_a_2904_, 0);
v_interpreted_2927_ = lean_ctor_get_uint8(v_a_2904_, sizeof(void*)*12 + 1);
lean_inc_ref(v_self_2926_);
v___x_2928_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents(v_self_2926_, v___y_2874_, v___y_2875_, v___y_2876_, v___y_2877_, v___y_2878_, v___y_2879_, v___y_2880_, v___y_2881_, v___y_2882_, v___y_2883_);
if (lean_obj_tag(v___x_2928_) == 0)
{
lean_dec_ref_known(v___x_2928_, 1);
if (v_interpreted_2927_ == 0)
{
lean_dec(v_snd_2887_);
v___y_2906_ = v___y_2874_;
v___y_2907_ = v___y_2875_;
v___y_2908_ = v___y_2876_;
v___y_2909_ = v___y_2877_;
v___y_2910_ = v___y_2878_;
v___y_2911_ = v___y_2879_;
v___y_2912_ = v___y_2880_;
v___y_2913_ = v___y_2881_;
v___y_2914_ = v___y_2882_;
v___y_2915_ = v___y_2883_;
goto v___jp_2905_;
}
else
{
lean_object* v___x_2929_; 
lean_inc_ref(v_self_2926_);
v___x_2929_ = l_Lean_Meta_Sym_Canon_normNumLit_x3f(v_self_2926_, v___y_2880_, v___y_2881_, v___y_2882_, v___y_2883_);
if (lean_obj_tag(v___x_2929_) == 0)
{
lean_object* v_a_2930_; 
v_a_2930_ = lean_ctor_get(v___x_2929_, 0);
lean_inc(v_a_2930_);
lean_dec_ref_known(v___x_2929_, 1);
if (lean_obj_tag(v_a_2930_) == 0)
{
lean_dec(v_snd_2887_);
v___y_2906_ = v___y_2874_;
v___y_2907_ = v___y_2875_;
v___y_2908_ = v___y_2876_;
v___y_2909_ = v___y_2877_;
v___y_2910_ = v___y_2878_;
v___y_2911_ = v___y_2879_;
v___y_2912_ = v___y_2880_;
v___y_2913_ = v___y_2881_;
v___y_2914_ = v___y_2882_;
v___y_2915_ = v___y_2883_;
goto v___jp_2905_;
}
else
{
lean_object* v___x_2932_; uint8_t v_isShared_2933_; uint8_t v_isSharedCheck_2957_; 
lean_dec(v_a_2904_);
v_isSharedCheck_2957_ = !lean_is_exclusive(v_a_2930_);
if (v_isSharedCheck_2957_ == 0)
{
lean_object* v_unused_2958_; 
v_unused_2958_ = lean_ctor_get(v_a_2930_, 0);
lean_dec(v_unused_2958_);
v___x_2932_ = v_a_2930_;
v_isShared_2933_ = v_isSharedCheck_2957_;
goto v_resetjp_2931_;
}
else
{
lean_dec(v_a_2930_);
v___x_2932_ = lean_box(0);
v_isShared_2933_ = v_isSharedCheck_2957_;
goto v_resetjp_2931_;
}
v_resetjp_2931_:
{
lean_object* v___x_2934_; lean_object* v___x_2935_; 
v___x_2934_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__2_spec__5___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__2_spec__5___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__2_spec__5___closed__2);
v___x_2935_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__0(v___x_2934_, v___y_2874_, v___y_2875_, v___y_2876_, v___y_2877_, v___y_2878_, v___y_2879_, v___y_2880_, v___y_2881_, v___y_2882_, v___y_2883_);
if (lean_obj_tag(v___x_2935_) == 0)
{
lean_object* v_a_2936_; lean_object* v___x_2938_; uint8_t v_isShared_2939_; uint8_t v_isSharedCheck_2948_; 
v_a_2936_ = lean_ctor_get(v___x_2935_, 0);
v_isSharedCheck_2948_ = !lean_is_exclusive(v___x_2935_);
if (v_isSharedCheck_2948_ == 0)
{
v___x_2938_ = v___x_2935_;
v_isShared_2939_ = v_isSharedCheck_2948_;
goto v_resetjp_2937_;
}
else
{
lean_inc(v_a_2936_);
lean_dec(v___x_2935_);
v___x_2938_ = lean_box(0);
v_isShared_2939_ = v_isSharedCheck_2948_;
goto v_resetjp_2937_;
}
v_resetjp_2937_:
{
if (lean_obj_tag(v_a_2936_) == 0)
{
lean_object* v___x_2941_; 
lean_del_object(v___x_2889_);
if (v_isShared_2933_ == 0)
{
lean_ctor_set(v___x_2932_, 0, v_a_2936_);
v___x_2941_ = v___x_2932_;
goto v_reusejp_2940_;
}
else
{
lean_object* v_reuseFailAlloc_2946_; 
v_reuseFailAlloc_2946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2946_, 0, v_a_2936_);
v___x_2941_ = v_reuseFailAlloc_2946_;
goto v_reusejp_2940_;
}
v_reusejp_2940_:
{
lean_object* v___x_2942_; lean_object* v___x_2944_; 
v___x_2942_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2942_, 0, v___x_2941_);
lean_ctor_set(v___x_2942_, 1, v_snd_2887_);
if (v_isShared_2939_ == 0)
{
lean_ctor_set(v___x_2938_, 0, v___x_2942_);
v___x_2944_ = v___x_2938_;
goto v_reusejp_2943_;
}
else
{
lean_object* v_reuseFailAlloc_2945_; 
v_reuseFailAlloc_2945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2945_, 0, v___x_2942_);
v___x_2944_ = v_reuseFailAlloc_2945_;
goto v_reusejp_2943_;
}
v_reusejp_2943_:
{
return v___x_2944_;
}
}
}
else
{
lean_object* v_a_2947_; 
lean_del_object(v___x_2938_);
lean_del_object(v___x_2932_);
lean_dec(v_snd_2887_);
v_a_2947_ = lean_ctor_get(v_a_2936_, 0);
lean_inc(v_a_2947_);
lean_dec_ref_known(v_a_2936_, 1);
v_a_2893_ = v_a_2947_;
goto v___jp_2892_;
}
}
}
else
{
lean_object* v_a_2949_; lean_object* v___x_2951_; uint8_t v_isShared_2952_; uint8_t v_isSharedCheck_2956_; 
lean_del_object(v___x_2932_);
lean_del_object(v___x_2889_);
lean_dec(v_snd_2887_);
v_a_2949_ = lean_ctor_get(v___x_2935_, 0);
v_isSharedCheck_2956_ = !lean_is_exclusive(v___x_2935_);
if (v_isSharedCheck_2956_ == 0)
{
v___x_2951_ = v___x_2935_;
v_isShared_2952_ = v_isSharedCheck_2956_;
goto v_resetjp_2950_;
}
else
{
lean_inc(v_a_2949_);
lean_dec(v___x_2935_);
v___x_2951_ = lean_box(0);
v_isShared_2952_ = v_isSharedCheck_2956_;
goto v_resetjp_2950_;
}
v_resetjp_2950_:
{
lean_object* v___x_2954_; 
if (v_isShared_2952_ == 0)
{
v___x_2954_ = v___x_2951_;
goto v_reusejp_2953_;
}
else
{
lean_object* v_reuseFailAlloc_2955_; 
v_reuseFailAlloc_2955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2955_, 0, v_a_2949_);
v___x_2954_ = v_reuseFailAlloc_2955_;
goto v_reusejp_2953_;
}
v_reusejp_2953_:
{
return v___x_2954_;
}
}
}
}
}
}
else
{
lean_object* v_a_2959_; lean_object* v___x_2961_; uint8_t v_isShared_2962_; uint8_t v_isSharedCheck_2966_; 
lean_dec(v_a_2904_);
lean_del_object(v___x_2889_);
lean_dec(v_snd_2887_);
v_a_2959_ = lean_ctor_get(v___x_2929_, 0);
v_isSharedCheck_2966_ = !lean_is_exclusive(v___x_2929_);
if (v_isSharedCheck_2966_ == 0)
{
v___x_2961_ = v___x_2929_;
v_isShared_2962_ = v_isSharedCheck_2966_;
goto v_resetjp_2960_;
}
else
{
lean_inc(v_a_2959_);
lean_dec(v___x_2929_);
v___x_2961_ = lean_box(0);
v_isShared_2962_ = v_isSharedCheck_2966_;
goto v_resetjp_2960_;
}
v_resetjp_2960_:
{
lean_object* v___x_2964_; 
if (v_isShared_2962_ == 0)
{
v___x_2964_ = v___x_2961_;
goto v_reusejp_2963_;
}
else
{
lean_object* v_reuseFailAlloc_2965_; 
v_reuseFailAlloc_2965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2965_, 0, v_a_2959_);
v___x_2964_ = v_reuseFailAlloc_2965_;
goto v_reusejp_2963_;
}
v_reusejp_2963_:
{
return v___x_2964_;
}
}
}
}
}
else
{
lean_object* v_a_2967_; lean_object* v___x_2969_; uint8_t v_isShared_2970_; uint8_t v_isSharedCheck_2974_; 
lean_dec(v_a_2904_);
lean_del_object(v___x_2889_);
lean_dec(v_snd_2887_);
v_a_2967_ = lean_ctor_get(v___x_2928_, 0);
v_isSharedCheck_2974_ = !lean_is_exclusive(v___x_2928_);
if (v_isSharedCheck_2974_ == 0)
{
v___x_2969_ = v___x_2928_;
v_isShared_2970_ = v_isSharedCheck_2974_;
goto v_resetjp_2968_;
}
else
{
lean_inc(v_a_2967_);
lean_dec(v___x_2928_);
v___x_2969_ = lean_box(0);
v_isShared_2970_ = v_isSharedCheck_2974_;
goto v_resetjp_2968_;
}
v_resetjp_2968_:
{
lean_object* v___x_2972_; 
if (v_isShared_2970_ == 0)
{
v___x_2972_ = v___x_2969_;
goto v_reusejp_2971_;
}
else
{
lean_object* v_reuseFailAlloc_2973_; 
v_reuseFailAlloc_2973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2973_, 0, v_a_2967_);
v___x_2972_ = v_reuseFailAlloc_2973_;
goto v_reusejp_2971_;
}
v_reusejp_2971_:
{
return v___x_2972_;
}
}
}
v___jp_2905_:
{
uint8_t v___x_2916_; 
v___x_2916_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_2904_);
if (v___x_2916_ == 0)
{
lean_dec(v_a_2904_);
v_a_2893_ = v___x_2900_;
goto v___jp_2892_;
}
else
{
lean_object* v___x_2917_; 
v___x_2917_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc(v_a_2904_, v___y_2906_, v___y_2907_, v___y_2908_, v___y_2909_, v___y_2910_, v___y_2911_, v___y_2912_, v___y_2913_, v___y_2914_, v___y_2915_);
if (lean_obj_tag(v___x_2917_) == 0)
{
lean_dec_ref_known(v___x_2917_, 1);
v_a_2893_ = v___x_2900_;
goto v___jp_2892_;
}
else
{
lean_object* v_a_2918_; lean_object* v___x_2920_; uint8_t v_isShared_2921_; uint8_t v_isSharedCheck_2925_; 
lean_del_object(v___x_2889_);
v_a_2918_ = lean_ctor_get(v___x_2917_, 0);
v_isSharedCheck_2925_ = !lean_is_exclusive(v___x_2917_);
if (v_isSharedCheck_2925_ == 0)
{
v___x_2920_ = v___x_2917_;
v_isShared_2921_ = v_isSharedCheck_2925_;
goto v_resetjp_2919_;
}
else
{
lean_inc(v_a_2918_);
lean_dec(v___x_2917_);
v___x_2920_ = lean_box(0);
v_isShared_2921_ = v_isSharedCheck_2925_;
goto v_resetjp_2919_;
}
v_resetjp_2919_:
{
lean_object* v___x_2923_; 
if (v_isShared_2921_ == 0)
{
v___x_2923_ = v___x_2920_;
goto v_reusejp_2922_;
}
else
{
lean_object* v_reuseFailAlloc_2924_; 
v_reuseFailAlloc_2924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2924_, 0, v_a_2918_);
v___x_2923_ = v_reuseFailAlloc_2924_;
goto v_reusejp_2922_;
}
v_reusejp_2922_:
{
return v___x_2923_;
}
}
}
}
}
}
else
{
lean_object* v_a_2975_; lean_object* v___x_2977_; uint8_t v_isShared_2978_; uint8_t v_isSharedCheck_2982_; 
lean_del_object(v___x_2889_);
lean_dec(v_snd_2887_);
v_a_2975_ = lean_ctor_get(v___x_2903_, 0);
v_isSharedCheck_2982_ = !lean_is_exclusive(v___x_2903_);
if (v_isSharedCheck_2982_ == 0)
{
v___x_2977_ = v___x_2903_;
v_isShared_2978_ = v_isSharedCheck_2982_;
goto v_resetjp_2976_;
}
else
{
lean_inc(v_a_2975_);
lean_dec(v___x_2903_);
v___x_2977_ = lean_box(0);
v_isShared_2978_ = v_isSharedCheck_2982_;
goto v_resetjp_2976_;
}
v_resetjp_2976_:
{
lean_object* v___x_2980_; 
if (v_isShared_2978_ == 0)
{
v___x_2980_ = v___x_2977_;
goto v_reusejp_2979_;
}
else
{
lean_object* v_reuseFailAlloc_2981_; 
v_reuseFailAlloc_2981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2981_, 0, v_a_2975_);
v___x_2980_ = v_reuseFailAlloc_2981_;
goto v_reusejp_2979_;
}
v_reusejp_2979_:
{
return v___x_2980_;
}
}
}
v___jp_2892_:
{
lean_object* v___x_2895_; 
if (v_isShared_2890_ == 0)
{
lean_ctor_set(v___x_2889_, 1, v_a_2893_);
lean_ctor_set(v___x_2889_, 0, v___x_2891_);
v___x_2895_ = v___x_2889_;
goto v_reusejp_2894_;
}
else
{
lean_object* v_reuseFailAlloc_2899_; 
v_reuseFailAlloc_2899_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2899_, 0, v___x_2891_);
lean_ctor_set(v_reuseFailAlloc_2899_, 1, v_a_2893_);
v___x_2895_ = v_reuseFailAlloc_2899_;
goto v_reusejp_2894_;
}
v_reusejp_2894_:
{
size_t v___x_2896_; size_t v___x_2897_; 
v___x_2896_ = ((size_t)1ULL);
v___x_2897_ = lean_usize_add(v_i_2872_, v___x_2896_);
v_i_2872_ = v___x_2897_;
v_b_2873_ = v___x_2895_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__1_spec__3_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2870_ = stack[0].m_obj;
size_t v_sz_2871_ = stack[1].m_num;
size_t v_i_2872_ = stack[2].m_num;
lean_object* v_b_2873_ = stack[3].m_obj;
lean_object* v___y_2874_ = stack[4].m_obj;
lean_object* v___y_2875_ = stack[5].m_obj;
lean_object* v___y_2876_ = stack[6].m_obj;
lean_object* v___y_2877_ = stack[7].m_obj;
lean_object* v___y_2878_ = stack[8].m_obj;
lean_object* v___y_2879_ = stack[9].m_obj;
lean_object* v___y_2880_ = stack[10].m_obj;
lean_object* v___y_2881_ = stack[11].m_obj;
lean_object* v___y_2882_ = stack[12].m_obj;
lean_object* v___y_2883_ = stack[13].m_obj;
lean_object* v_res_2985_;
v_res_2985_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__1_spec__3_spec__4(v_as_2870_, v_sz_2871_, v_i_2872_, v_b_2873_, v___y_2874_, v___y_2875_, v___y_2876_, v___y_2877_, v___y_2878_, v___y_2879_, v___y_2880_, v___y_2881_, v___y_2882_, v___y_2883_);
stack->m_obj
 = v_res_2985_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__1_spec__3_spec__4___boxed(lean_object* v_as_2986_, lean_object* v_sz_2987_, lean_object* v_i_2988_, lean_object* v_b_2989_, lean_object* v___y_2990_, lean_object* v___y_2991_, lean_object* v___y_2992_, lean_object* v___y_2993_, lean_object* v___y_2994_, lean_object* v___y_2995_, lean_object* v___y_2996_, lean_object* v___y_2997_, lean_object* v___y_2998_, lean_object* v___y_2999_, lean_object* v___y_3000_){
_start:
{
size_t v_sz_boxed_3001_; size_t v_i_boxed_3002_; lean_object* v_res_3003_; 
v_sz_boxed_3001_ = lean_unbox_usize(v_sz_2987_);
lean_dec(v_sz_2987_);
v_i_boxed_3002_ = lean_unbox_usize(v_i_2988_);
lean_dec(v_i_2988_);
v_res_3003_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__1_spec__3_spec__4(v_as_2986_, v_sz_boxed_3001_, v_i_boxed_3002_, v_b_2989_, v___y_2990_, v___y_2991_, v___y_2992_, v___y_2993_, v___y_2994_, v___y_2995_, v___y_2996_, v___y_2997_, v___y_2998_, v___y_2999_);
lean_dec(v___y_2999_);
lean_dec_ref(v___y_2998_);
lean_dec(v___y_2997_);
lean_dec_ref(v___y_2996_);
lean_dec(v___y_2995_);
lean_dec_ref(v___y_2994_);
lean_dec(v___y_2993_);
lean_dec_ref(v___y_2992_);
lean_dec(v___y_2991_);
lean_dec(v___y_2990_);
lean_dec_ref(v_as_2986_);
return v_res_3003_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__1_spec__3(lean_object* v_as_3004_, size_t v_sz_3005_, size_t v_i_3006_, lean_object* v_b_3007_, lean_object* v___y_3008_, lean_object* v___y_3009_, lean_object* v___y_3010_, lean_object* v___y_3011_, lean_object* v___y_3012_, lean_object* v___y_3013_, lean_object* v___y_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_, lean_object* v___y_3017_){
_start:
{
uint8_t v___x_3019_; 
v___x_3019_ = lean_usize_dec_lt(v_i_3006_, v_sz_3005_);
if (v___x_3019_ == 0)
{
lean_object* v___x_3020_; 
v___x_3020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3020_, 0, v_b_3007_);
return v___x_3020_;
}
else
{
lean_object* v_snd_3021_; lean_object* v___x_3023_; uint8_t v_isShared_3024_; uint8_t v_isSharedCheck_3117_; 
v_snd_3021_ = lean_ctor_get(v_b_3007_, 1);
v_isSharedCheck_3117_ = !lean_is_exclusive(v_b_3007_);
if (v_isSharedCheck_3117_ == 0)
{
lean_object* v_unused_3118_; 
v_unused_3118_ = lean_ctor_get(v_b_3007_, 0);
lean_dec(v_unused_3118_);
v___x_3023_ = v_b_3007_;
v_isShared_3024_ = v_isSharedCheck_3117_;
goto v_resetjp_3022_;
}
else
{
lean_inc(v_snd_3021_);
lean_dec(v_b_3007_);
v___x_3023_ = lean_box(0);
v_isShared_3024_ = v_isSharedCheck_3117_;
goto v_resetjp_3022_;
}
v_resetjp_3022_:
{
lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v_a_3028_; lean_object* v_a_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; 
v___x_3025_ = lean_box(0);
v___x_3026_ = lean_box(0);
v_a_3035_ = lean_array_uget_borrowed(v_as_3004_, v_i_3006_);
v___x_3036_ = lean_st_ref_get(v___y_3008_);
lean_inc(v_a_3035_);
v___x_3037_ = l_Lean_Meta_Grind_Goal_getENode(v___x_3036_, v_a_3035_, v___y_3014_, v___y_3015_, v___y_3016_, v___y_3017_);
lean_dec(v___x_3036_);
if (lean_obj_tag(v___x_3037_) == 0)
{
lean_object* v_a_3038_; lean_object* v___y_3040_; lean_object* v___y_3041_; lean_object* v___y_3042_; lean_object* v___y_3043_; lean_object* v___y_3044_; lean_object* v___y_3045_; lean_object* v___y_3046_; lean_object* v___y_3047_; lean_object* v___y_3048_; lean_object* v___y_3049_; lean_object* v_self_3060_; uint8_t v_interpreted_3061_; lean_object* v___x_3062_; 
v_a_3038_ = lean_ctor_get(v___x_3037_, 0);
lean_inc(v_a_3038_);
lean_dec_ref_known(v___x_3037_, 1);
v_self_3060_ = lean_ctor_get(v_a_3038_, 0);
v_interpreted_3061_ = lean_ctor_get_uint8(v_a_3038_, sizeof(void*)*12 + 1);
lean_inc_ref(v_self_3060_);
v___x_3062_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents(v_self_3060_, v___y_3008_, v___y_3009_, v___y_3010_, v___y_3011_, v___y_3012_, v___y_3013_, v___y_3014_, v___y_3015_, v___y_3016_, v___y_3017_);
if (lean_obj_tag(v___x_3062_) == 0)
{
lean_dec_ref_known(v___x_3062_, 1);
if (v_interpreted_3061_ == 0)
{
lean_dec(v_snd_3021_);
v___y_3040_ = v___y_3008_;
v___y_3041_ = v___y_3009_;
v___y_3042_ = v___y_3010_;
v___y_3043_ = v___y_3011_;
v___y_3044_ = v___y_3012_;
v___y_3045_ = v___y_3013_;
v___y_3046_ = v___y_3014_;
v___y_3047_ = v___y_3015_;
v___y_3048_ = v___y_3016_;
v___y_3049_ = v___y_3017_;
goto v___jp_3039_;
}
else
{
lean_object* v___x_3063_; 
lean_inc_ref(v_self_3060_);
v___x_3063_ = l_Lean_Meta_Sym_Canon_normNumLit_x3f(v_self_3060_, v___y_3014_, v___y_3015_, v___y_3016_, v___y_3017_);
if (lean_obj_tag(v___x_3063_) == 0)
{
lean_object* v_a_3064_; 
v_a_3064_ = lean_ctor_get(v___x_3063_, 0);
lean_inc(v_a_3064_);
lean_dec_ref_known(v___x_3063_, 1);
if (lean_obj_tag(v_a_3064_) == 0)
{
lean_dec(v_snd_3021_);
v___y_3040_ = v___y_3008_;
v___y_3041_ = v___y_3009_;
v___y_3042_ = v___y_3010_;
v___y_3043_ = v___y_3011_;
v___y_3044_ = v___y_3012_;
v___y_3045_ = v___y_3013_;
v___y_3046_ = v___y_3014_;
v___y_3047_ = v___y_3015_;
v___y_3048_ = v___y_3016_;
v___y_3049_ = v___y_3017_;
goto v___jp_3039_;
}
else
{
lean_object* v___x_3066_; uint8_t v_isShared_3067_; uint8_t v_isSharedCheck_3091_; 
lean_dec(v_a_3038_);
v_isSharedCheck_3091_ = !lean_is_exclusive(v_a_3064_);
if (v_isSharedCheck_3091_ == 0)
{
lean_object* v_unused_3092_; 
v_unused_3092_ = lean_ctor_get(v_a_3064_, 0);
lean_dec(v_unused_3092_);
v___x_3066_ = v_a_3064_;
v_isShared_3067_ = v_isSharedCheck_3091_;
goto v_resetjp_3065_;
}
else
{
lean_dec(v_a_3064_);
v___x_3066_ = lean_box(0);
v_isShared_3067_ = v_isSharedCheck_3091_;
goto v_resetjp_3065_;
}
v_resetjp_3065_:
{
lean_object* v___x_3068_; lean_object* v___x_3069_; 
v___x_3068_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__2_spec__5___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__2_spec__5___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__2_spec__5___closed__2);
v___x_3069_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__0(v___x_3068_, v___y_3008_, v___y_3009_, v___y_3010_, v___y_3011_, v___y_3012_, v___y_3013_, v___y_3014_, v___y_3015_, v___y_3016_, v___y_3017_);
if (lean_obj_tag(v___x_3069_) == 0)
{
lean_object* v_a_3070_; lean_object* v___x_3072_; uint8_t v_isShared_3073_; uint8_t v_isSharedCheck_3082_; 
v_a_3070_ = lean_ctor_get(v___x_3069_, 0);
v_isSharedCheck_3082_ = !lean_is_exclusive(v___x_3069_);
if (v_isSharedCheck_3082_ == 0)
{
v___x_3072_ = v___x_3069_;
v_isShared_3073_ = v_isSharedCheck_3082_;
goto v_resetjp_3071_;
}
else
{
lean_inc(v_a_3070_);
lean_dec(v___x_3069_);
v___x_3072_ = lean_box(0);
v_isShared_3073_ = v_isSharedCheck_3082_;
goto v_resetjp_3071_;
}
v_resetjp_3071_:
{
if (lean_obj_tag(v_a_3070_) == 0)
{
lean_object* v___x_3075_; 
lean_del_object(v___x_3023_);
if (v_isShared_3067_ == 0)
{
lean_ctor_set(v___x_3066_, 0, v_a_3070_);
v___x_3075_ = v___x_3066_;
goto v_reusejp_3074_;
}
else
{
lean_object* v_reuseFailAlloc_3080_; 
v_reuseFailAlloc_3080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3080_, 0, v_a_3070_);
v___x_3075_ = v_reuseFailAlloc_3080_;
goto v_reusejp_3074_;
}
v_reusejp_3074_:
{
lean_object* v___x_3076_; lean_object* v___x_3078_; 
v___x_3076_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3076_, 0, v___x_3075_);
lean_ctor_set(v___x_3076_, 1, v_snd_3021_);
if (v_isShared_3073_ == 0)
{
lean_ctor_set(v___x_3072_, 0, v___x_3076_);
v___x_3078_ = v___x_3072_;
goto v_reusejp_3077_;
}
else
{
lean_object* v_reuseFailAlloc_3079_; 
v_reuseFailAlloc_3079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3079_, 0, v___x_3076_);
v___x_3078_ = v_reuseFailAlloc_3079_;
goto v_reusejp_3077_;
}
v_reusejp_3077_:
{
return v___x_3078_;
}
}
}
else
{
lean_object* v_a_3081_; 
lean_del_object(v___x_3072_);
lean_del_object(v___x_3066_);
lean_dec(v_snd_3021_);
v_a_3081_ = lean_ctor_get(v_a_3070_, 0);
lean_inc(v_a_3081_);
lean_dec_ref_known(v_a_3070_, 1);
v_a_3028_ = v_a_3081_;
goto v___jp_3027_;
}
}
}
else
{
lean_object* v_a_3083_; lean_object* v___x_3085_; uint8_t v_isShared_3086_; uint8_t v_isSharedCheck_3090_; 
lean_del_object(v___x_3066_);
lean_del_object(v___x_3023_);
lean_dec(v_snd_3021_);
v_a_3083_ = lean_ctor_get(v___x_3069_, 0);
v_isSharedCheck_3090_ = !lean_is_exclusive(v___x_3069_);
if (v_isSharedCheck_3090_ == 0)
{
v___x_3085_ = v___x_3069_;
v_isShared_3086_ = v_isSharedCheck_3090_;
goto v_resetjp_3084_;
}
else
{
lean_inc(v_a_3083_);
lean_dec(v___x_3069_);
v___x_3085_ = lean_box(0);
v_isShared_3086_ = v_isSharedCheck_3090_;
goto v_resetjp_3084_;
}
v_resetjp_3084_:
{
lean_object* v___x_3088_; 
if (v_isShared_3086_ == 0)
{
v___x_3088_ = v___x_3085_;
goto v_reusejp_3087_;
}
else
{
lean_object* v_reuseFailAlloc_3089_; 
v_reuseFailAlloc_3089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3089_, 0, v_a_3083_);
v___x_3088_ = v_reuseFailAlloc_3089_;
goto v_reusejp_3087_;
}
v_reusejp_3087_:
{
return v___x_3088_;
}
}
}
}
}
}
else
{
lean_object* v_a_3093_; lean_object* v___x_3095_; uint8_t v_isShared_3096_; uint8_t v_isSharedCheck_3100_; 
lean_dec(v_a_3038_);
lean_del_object(v___x_3023_);
lean_dec(v_snd_3021_);
v_a_3093_ = lean_ctor_get(v___x_3063_, 0);
v_isSharedCheck_3100_ = !lean_is_exclusive(v___x_3063_);
if (v_isSharedCheck_3100_ == 0)
{
v___x_3095_ = v___x_3063_;
v_isShared_3096_ = v_isSharedCheck_3100_;
goto v_resetjp_3094_;
}
else
{
lean_inc(v_a_3093_);
lean_dec(v___x_3063_);
v___x_3095_ = lean_box(0);
v_isShared_3096_ = v_isSharedCheck_3100_;
goto v_resetjp_3094_;
}
v_resetjp_3094_:
{
lean_object* v___x_3098_; 
if (v_isShared_3096_ == 0)
{
v___x_3098_ = v___x_3095_;
goto v_reusejp_3097_;
}
else
{
lean_object* v_reuseFailAlloc_3099_; 
v_reuseFailAlloc_3099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3099_, 0, v_a_3093_);
v___x_3098_ = v_reuseFailAlloc_3099_;
goto v_reusejp_3097_;
}
v_reusejp_3097_:
{
return v___x_3098_;
}
}
}
}
}
else
{
lean_object* v_a_3101_; lean_object* v___x_3103_; uint8_t v_isShared_3104_; uint8_t v_isSharedCheck_3108_; 
lean_dec(v_a_3038_);
lean_del_object(v___x_3023_);
lean_dec(v_snd_3021_);
v_a_3101_ = lean_ctor_get(v___x_3062_, 0);
v_isSharedCheck_3108_ = !lean_is_exclusive(v___x_3062_);
if (v_isSharedCheck_3108_ == 0)
{
v___x_3103_ = v___x_3062_;
v_isShared_3104_ = v_isSharedCheck_3108_;
goto v_resetjp_3102_;
}
else
{
lean_inc(v_a_3101_);
lean_dec(v___x_3062_);
v___x_3103_ = lean_box(0);
v_isShared_3104_ = v_isSharedCheck_3108_;
goto v_resetjp_3102_;
}
v_resetjp_3102_:
{
lean_object* v___x_3106_; 
if (v_isShared_3104_ == 0)
{
v___x_3106_ = v___x_3103_;
goto v_reusejp_3105_;
}
else
{
lean_object* v_reuseFailAlloc_3107_; 
v_reuseFailAlloc_3107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3107_, 0, v_a_3101_);
v___x_3106_ = v_reuseFailAlloc_3107_;
goto v_reusejp_3105_;
}
v_reusejp_3105_:
{
return v___x_3106_;
}
}
}
v___jp_3039_:
{
uint8_t v___x_3050_; 
v___x_3050_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_3038_);
if (v___x_3050_ == 0)
{
lean_dec(v_a_3038_);
v_a_3028_ = v___x_3025_;
goto v___jp_3027_;
}
else
{
lean_object* v___x_3051_; 
v___x_3051_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc(v_a_3038_, v___y_3040_, v___y_3041_, v___y_3042_, v___y_3043_, v___y_3044_, v___y_3045_, v___y_3046_, v___y_3047_, v___y_3048_, v___y_3049_);
if (lean_obj_tag(v___x_3051_) == 0)
{
lean_dec_ref_known(v___x_3051_, 1);
v_a_3028_ = v___x_3025_;
goto v___jp_3027_;
}
else
{
lean_object* v_a_3052_; lean_object* v___x_3054_; uint8_t v_isShared_3055_; uint8_t v_isSharedCheck_3059_; 
lean_del_object(v___x_3023_);
v_a_3052_ = lean_ctor_get(v___x_3051_, 0);
v_isSharedCheck_3059_ = !lean_is_exclusive(v___x_3051_);
if (v_isSharedCheck_3059_ == 0)
{
v___x_3054_ = v___x_3051_;
v_isShared_3055_ = v_isSharedCheck_3059_;
goto v_resetjp_3053_;
}
else
{
lean_inc(v_a_3052_);
lean_dec(v___x_3051_);
v___x_3054_ = lean_box(0);
v_isShared_3055_ = v_isSharedCheck_3059_;
goto v_resetjp_3053_;
}
v_resetjp_3053_:
{
lean_object* v___x_3057_; 
if (v_isShared_3055_ == 0)
{
v___x_3057_ = v___x_3054_;
goto v_reusejp_3056_;
}
else
{
lean_object* v_reuseFailAlloc_3058_; 
v_reuseFailAlloc_3058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3058_, 0, v_a_3052_);
v___x_3057_ = v_reuseFailAlloc_3058_;
goto v_reusejp_3056_;
}
v_reusejp_3056_:
{
return v___x_3057_;
}
}
}
}
}
}
else
{
lean_object* v_a_3109_; lean_object* v___x_3111_; uint8_t v_isShared_3112_; uint8_t v_isSharedCheck_3116_; 
lean_del_object(v___x_3023_);
lean_dec(v_snd_3021_);
v_a_3109_ = lean_ctor_get(v___x_3037_, 0);
v_isSharedCheck_3116_ = !lean_is_exclusive(v___x_3037_);
if (v_isSharedCheck_3116_ == 0)
{
v___x_3111_ = v___x_3037_;
v_isShared_3112_ = v_isSharedCheck_3116_;
goto v_resetjp_3110_;
}
else
{
lean_inc(v_a_3109_);
lean_dec(v___x_3037_);
v___x_3111_ = lean_box(0);
v_isShared_3112_ = v_isSharedCheck_3116_;
goto v_resetjp_3110_;
}
v_resetjp_3110_:
{
lean_object* v___x_3114_; 
if (v_isShared_3112_ == 0)
{
v___x_3114_ = v___x_3111_;
goto v_reusejp_3113_;
}
else
{
lean_object* v_reuseFailAlloc_3115_; 
v_reuseFailAlloc_3115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3115_, 0, v_a_3109_);
v___x_3114_ = v_reuseFailAlloc_3115_;
goto v_reusejp_3113_;
}
v_reusejp_3113_:
{
return v___x_3114_;
}
}
}
v___jp_3027_:
{
lean_object* v___x_3030_; 
if (v_isShared_3024_ == 0)
{
lean_ctor_set(v___x_3023_, 1, v_a_3028_);
lean_ctor_set(v___x_3023_, 0, v___x_3026_);
v___x_3030_ = v___x_3023_;
goto v_reusejp_3029_;
}
else
{
lean_object* v_reuseFailAlloc_3034_; 
v_reuseFailAlloc_3034_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3034_, 0, v___x_3026_);
lean_ctor_set(v_reuseFailAlloc_3034_, 1, v_a_3028_);
v___x_3030_ = v_reuseFailAlloc_3034_;
goto v_reusejp_3029_;
}
v_reusejp_3029_:
{
size_t v___x_3031_; size_t v___x_3032_; lean_object* v___x_3033_; 
v___x_3031_ = ((size_t)1ULL);
v___x_3032_ = lean_usize_add(v_i_3006_, v___x_3031_);
v___x_3033_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__1_spec__3_spec__4(v_as_3004_, v_sz_3005_, v___x_3032_, v___x_3030_, v___y_3008_, v___y_3009_, v___y_3010_, v___y_3011_, v___y_3012_, v___y_3013_, v___y_3014_, v___y_3015_, v___y_3016_, v___y_3017_);
return v___x_3033_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__1_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_3004_ = stack[0].m_obj;
size_t v_sz_3005_ = stack[1].m_num;
size_t v_i_3006_ = stack[2].m_num;
lean_object* v_b_3007_ = stack[3].m_obj;
lean_object* v___y_3008_ = stack[4].m_obj;
lean_object* v___y_3009_ = stack[5].m_obj;
lean_object* v___y_3010_ = stack[6].m_obj;
lean_object* v___y_3011_ = stack[7].m_obj;
lean_object* v___y_3012_ = stack[8].m_obj;
lean_object* v___y_3013_ = stack[9].m_obj;
lean_object* v___y_3014_ = stack[10].m_obj;
lean_object* v___y_3015_ = stack[11].m_obj;
lean_object* v___y_3016_ = stack[12].m_obj;
lean_object* v___y_3017_ = stack[13].m_obj;
lean_object* v_res_3119_;
v_res_3119_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__1_spec__3(v_as_3004_, v_sz_3005_, v_i_3006_, v_b_3007_, v___y_3008_, v___y_3009_, v___y_3010_, v___y_3011_, v___y_3012_, v___y_3013_, v___y_3014_, v___y_3015_, v___y_3016_, v___y_3017_);
stack->m_obj
 = v_res_3119_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__1_spec__3___boxed(lean_object* v_as_3120_, lean_object* v_sz_3121_, lean_object* v_i_3122_, lean_object* v_b_3123_, lean_object* v___y_3124_, lean_object* v___y_3125_, lean_object* v___y_3126_, lean_object* v___y_3127_, lean_object* v___y_3128_, lean_object* v___y_3129_, lean_object* v___y_3130_, lean_object* v___y_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_){
_start:
{
size_t v_sz_boxed_3135_; size_t v_i_boxed_3136_; lean_object* v_res_3137_; 
v_sz_boxed_3135_ = lean_unbox_usize(v_sz_3121_);
lean_dec(v_sz_3121_);
v_i_boxed_3136_ = lean_unbox_usize(v_i_3122_);
lean_dec(v_i_3122_);
v_res_3137_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__1_spec__3(v_as_3120_, v_sz_boxed_3135_, v_i_boxed_3136_, v_b_3123_, v___y_3124_, v___y_3125_, v___y_3126_, v___y_3127_, v___y_3128_, v___y_3129_, v___y_3130_, v___y_3131_, v___y_3132_, v___y_3133_);
lean_dec(v___y_3133_);
lean_dec_ref(v___y_3132_);
lean_dec(v___y_3131_);
lean_dec_ref(v___y_3130_);
lean_dec(v___y_3129_);
lean_dec_ref(v___y_3128_);
lean_dec(v___y_3127_);
lean_dec_ref(v___y_3126_);
lean_dec(v___y_3125_);
lean_dec(v___y_3124_);
lean_dec_ref(v_as_3120_);
return v_res_3137_;
}
}
lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__1(lean_object* v_init_3138_, lean_object* v_n_3139_, lean_object* v_b_3140_, lean_object* v___y_3141_, lean_object* v___y_3142_, lean_object* v___y_3143_, lean_object* v___y_3144_, lean_object* v___y_3145_, lean_object* v___y_3146_, lean_object* v___y_3147_, lean_object* v___y_3148_, lean_object* v___y_3149_, lean_object* v___y_3150_){
_start:
{
if (lean_obj_tag(v_n_3139_) == 0)
{
lean_object* v_cs_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; size_t v_sz_3155_; size_t v___x_3156_; lean_object* v___x_3157_; 
v_cs_3152_ = lean_ctor_get(v_n_3139_, 0);
v___x_3153_ = lean_box(0);
v___x_3154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3154_, 0, v___x_3153_);
lean_ctor_set(v___x_3154_, 1, v_b_3140_);
v_sz_3155_ = lean_array_size(v_cs_3152_);
v___x_3156_ = ((size_t)0ULL);
v___x_3157_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__1_spec__2(v_init_3138_, v_cs_3152_, v_sz_3155_, v___x_3156_, v___x_3154_, v___y_3141_, v___y_3142_, v___y_3143_, v___y_3144_, v___y_3145_, v___y_3146_, v___y_3147_, v___y_3148_, v___y_3149_, v___y_3150_);
if (lean_obj_tag(v___x_3157_) == 0)
{
lean_object* v_a_3158_; lean_object* v___x_3160_; uint8_t v_isShared_3161_; uint8_t v_isSharedCheck_3172_; 
v_a_3158_ = lean_ctor_get(v___x_3157_, 0);
v_isSharedCheck_3172_ = !lean_is_exclusive(v___x_3157_);
if (v_isSharedCheck_3172_ == 0)
{
v___x_3160_ = v___x_3157_;
v_isShared_3161_ = v_isSharedCheck_3172_;
goto v_resetjp_3159_;
}
else
{
lean_inc(v_a_3158_);
lean_dec(v___x_3157_);
v___x_3160_ = lean_box(0);
v_isShared_3161_ = v_isSharedCheck_3172_;
goto v_resetjp_3159_;
}
v_resetjp_3159_:
{
lean_object* v_fst_3162_; 
v_fst_3162_ = lean_ctor_get(v_a_3158_, 0);
if (lean_obj_tag(v_fst_3162_) == 0)
{
lean_object* v_snd_3163_; lean_object* v___x_3164_; lean_object* v___x_3166_; 
v_snd_3163_ = lean_ctor_get(v_a_3158_, 1);
lean_inc(v_snd_3163_);
lean_dec(v_a_3158_);
v___x_3164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3164_, 0, v_snd_3163_);
if (v_isShared_3161_ == 0)
{
lean_ctor_set(v___x_3160_, 0, v___x_3164_);
v___x_3166_ = v___x_3160_;
goto v_reusejp_3165_;
}
else
{
lean_object* v_reuseFailAlloc_3167_; 
v_reuseFailAlloc_3167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3167_, 0, v___x_3164_);
v___x_3166_ = v_reuseFailAlloc_3167_;
goto v_reusejp_3165_;
}
v_reusejp_3165_:
{
return v___x_3166_;
}
}
else
{
lean_object* v_val_3168_; lean_object* v___x_3170_; 
lean_inc_ref(v_fst_3162_);
lean_dec(v_a_3158_);
v_val_3168_ = lean_ctor_get(v_fst_3162_, 0);
lean_inc(v_val_3168_);
lean_dec_ref_known(v_fst_3162_, 1);
if (v_isShared_3161_ == 0)
{
lean_ctor_set(v___x_3160_, 0, v_val_3168_);
v___x_3170_ = v___x_3160_;
goto v_reusejp_3169_;
}
else
{
lean_object* v_reuseFailAlloc_3171_; 
v_reuseFailAlloc_3171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3171_, 0, v_val_3168_);
v___x_3170_ = v_reuseFailAlloc_3171_;
goto v_reusejp_3169_;
}
v_reusejp_3169_:
{
return v___x_3170_;
}
}
}
}
else
{
lean_object* v_a_3173_; lean_object* v___x_3175_; uint8_t v_isShared_3176_; uint8_t v_isSharedCheck_3180_; 
v_a_3173_ = lean_ctor_get(v___x_3157_, 0);
v_isSharedCheck_3180_ = !lean_is_exclusive(v___x_3157_);
if (v_isSharedCheck_3180_ == 0)
{
v___x_3175_ = v___x_3157_;
v_isShared_3176_ = v_isSharedCheck_3180_;
goto v_resetjp_3174_;
}
else
{
lean_inc(v_a_3173_);
lean_dec(v___x_3157_);
v___x_3175_ = lean_box(0);
v_isShared_3176_ = v_isSharedCheck_3180_;
goto v_resetjp_3174_;
}
v_resetjp_3174_:
{
lean_object* v___x_3178_; 
if (v_isShared_3176_ == 0)
{
v___x_3178_ = v___x_3175_;
goto v_reusejp_3177_;
}
else
{
lean_object* v_reuseFailAlloc_3179_; 
v_reuseFailAlloc_3179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3179_, 0, v_a_3173_);
v___x_3178_ = v_reuseFailAlloc_3179_;
goto v_reusejp_3177_;
}
v_reusejp_3177_:
{
return v___x_3178_;
}
}
}
}
else
{
lean_object* v_vs_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; size_t v_sz_3184_; size_t v___x_3185_; lean_object* v___x_3186_; 
v_vs_3181_ = lean_ctor_get(v_n_3139_, 0);
v___x_3182_ = lean_box(0);
v___x_3183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3183_, 0, v___x_3182_);
lean_ctor_set(v___x_3183_, 1, v_b_3140_);
v_sz_3184_ = lean_array_size(v_vs_3181_);
v___x_3185_ = ((size_t)0ULL);
v___x_3186_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__1_spec__3(v_vs_3181_, v_sz_3184_, v___x_3185_, v___x_3183_, v___y_3141_, v___y_3142_, v___y_3143_, v___y_3144_, v___y_3145_, v___y_3146_, v___y_3147_, v___y_3148_, v___y_3149_, v___y_3150_);
if (lean_obj_tag(v___x_3186_) == 0)
{
lean_object* v_a_3187_; lean_object* v___x_3189_; uint8_t v_isShared_3190_; uint8_t v_isSharedCheck_3201_; 
v_a_3187_ = lean_ctor_get(v___x_3186_, 0);
v_isSharedCheck_3201_ = !lean_is_exclusive(v___x_3186_);
if (v_isSharedCheck_3201_ == 0)
{
v___x_3189_ = v___x_3186_;
v_isShared_3190_ = v_isSharedCheck_3201_;
goto v_resetjp_3188_;
}
else
{
lean_inc(v_a_3187_);
lean_dec(v___x_3186_);
v___x_3189_ = lean_box(0);
v_isShared_3190_ = v_isSharedCheck_3201_;
goto v_resetjp_3188_;
}
v_resetjp_3188_:
{
lean_object* v_fst_3191_; 
v_fst_3191_ = lean_ctor_get(v_a_3187_, 0);
if (lean_obj_tag(v_fst_3191_) == 0)
{
lean_object* v_snd_3192_; lean_object* v___x_3193_; lean_object* v___x_3195_; 
v_snd_3192_ = lean_ctor_get(v_a_3187_, 1);
lean_inc(v_snd_3192_);
lean_dec(v_a_3187_);
v___x_3193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3193_, 0, v_snd_3192_);
if (v_isShared_3190_ == 0)
{
lean_ctor_set(v___x_3189_, 0, v___x_3193_);
v___x_3195_ = v___x_3189_;
goto v_reusejp_3194_;
}
else
{
lean_object* v_reuseFailAlloc_3196_; 
v_reuseFailAlloc_3196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3196_, 0, v___x_3193_);
v___x_3195_ = v_reuseFailAlloc_3196_;
goto v_reusejp_3194_;
}
v_reusejp_3194_:
{
return v___x_3195_;
}
}
else
{
lean_object* v_val_3197_; lean_object* v___x_3199_; 
lean_inc_ref(v_fst_3191_);
lean_dec(v_a_3187_);
v_val_3197_ = lean_ctor_get(v_fst_3191_, 0);
lean_inc(v_val_3197_);
lean_dec_ref_known(v_fst_3191_, 1);
if (v_isShared_3190_ == 0)
{
lean_ctor_set(v___x_3189_, 0, v_val_3197_);
v___x_3199_ = v___x_3189_;
goto v_reusejp_3198_;
}
else
{
lean_object* v_reuseFailAlloc_3200_; 
v_reuseFailAlloc_3200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3200_, 0, v_val_3197_);
v___x_3199_ = v_reuseFailAlloc_3200_;
goto v_reusejp_3198_;
}
v_reusejp_3198_:
{
return v___x_3199_;
}
}
}
}
else
{
lean_object* v_a_3202_; lean_object* v___x_3204_; uint8_t v_isShared_3205_; uint8_t v_isSharedCheck_3209_; 
v_a_3202_ = lean_ctor_get(v___x_3186_, 0);
v_isSharedCheck_3209_ = !lean_is_exclusive(v___x_3186_);
if (v_isSharedCheck_3209_ == 0)
{
v___x_3204_ = v___x_3186_;
v_isShared_3205_ = v_isSharedCheck_3209_;
goto v_resetjp_3203_;
}
else
{
lean_inc(v_a_3202_);
lean_dec(v___x_3186_);
v___x_3204_ = lean_box(0);
v_isShared_3205_ = v_isSharedCheck_3209_;
goto v_resetjp_3203_;
}
v_resetjp_3203_:
{
lean_object* v___x_3207_; 
if (v_isShared_3205_ == 0)
{
v___x_3207_ = v___x_3204_;
goto v_reusejp_3206_;
}
else
{
lean_object* v_reuseFailAlloc_3208_; 
v_reuseFailAlloc_3208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3208_, 0, v_a_3202_);
v___x_3207_ = v_reuseFailAlloc_3208_;
goto v_reusejp_3206_;
}
v_reusejp_3206_:
{
return v___x_3207_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_init_3138_ = stack[0].m_obj;
lean_object* v_n_3139_ = stack[1].m_obj;
lean_object* v_b_3140_ = stack[2].m_obj;
lean_object* v___y_3141_ = stack[3].m_obj;
lean_object* v___y_3142_ = stack[4].m_obj;
lean_object* v___y_3143_ = stack[5].m_obj;
lean_object* v___y_3144_ = stack[6].m_obj;
lean_object* v___y_3145_ = stack[7].m_obj;
lean_object* v___y_3146_ = stack[8].m_obj;
lean_object* v___y_3147_ = stack[9].m_obj;
lean_object* v___y_3148_ = stack[10].m_obj;
lean_object* v___y_3149_ = stack[11].m_obj;
lean_object* v___y_3150_ = stack[12].m_obj;
lean_object* v_res_3210_;
v_res_3210_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__1(v_init_3138_, v_n_3139_, v_b_3140_, v___y_3141_, v___y_3142_, v___y_3143_, v___y_3144_, v___y_3145_, v___y_3146_, v___y_3147_, v___y_3148_, v___y_3149_, v___y_3150_);
stack->m_obj
 = v_res_3210_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__1_spec__2(lean_object* v_init_3211_, lean_object* v_as_3212_, size_t v_sz_3213_, size_t v_i_3214_, lean_object* v_b_3215_, lean_object* v___y_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_, lean_object* v___y_3219_, lean_object* v___y_3220_, lean_object* v___y_3221_, lean_object* v___y_3222_, lean_object* v___y_3223_, lean_object* v___y_3224_, lean_object* v___y_3225_){
_start:
{
uint8_t v___x_3227_; 
v___x_3227_ = lean_usize_dec_lt(v_i_3214_, v_sz_3213_);
if (v___x_3227_ == 0)
{
lean_object* v___x_3228_; 
v___x_3228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3228_, 0, v_b_3215_);
return v___x_3228_;
}
else
{
lean_object* v_snd_3229_; lean_object* v___x_3231_; uint8_t v_isShared_3232_; uint8_t v_isSharedCheck_3263_; 
v_snd_3229_ = lean_ctor_get(v_b_3215_, 1);
v_isSharedCheck_3263_ = !lean_is_exclusive(v_b_3215_);
if (v_isSharedCheck_3263_ == 0)
{
lean_object* v_unused_3264_; 
v_unused_3264_ = lean_ctor_get(v_b_3215_, 0);
lean_dec(v_unused_3264_);
v___x_3231_ = v_b_3215_;
v_isShared_3232_ = v_isSharedCheck_3263_;
goto v_resetjp_3230_;
}
else
{
lean_inc(v_snd_3229_);
lean_dec(v_b_3215_);
v___x_3231_ = lean_box(0);
v_isShared_3232_ = v_isSharedCheck_3263_;
goto v_resetjp_3230_;
}
v_resetjp_3230_:
{
lean_object* v___x_3233_; lean_object* v_a_3234_; lean_object* v___x_3235_; 
v___x_3233_ = lean_box(0);
v_a_3234_ = lean_array_uget_borrowed(v_as_3212_, v_i_3214_);
lean_inc(v_snd_3229_);
v___x_3235_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__1(v_init_3211_, v_a_3234_, v_snd_3229_, v___y_3216_, v___y_3217_, v___y_3218_, v___y_3219_, v___y_3220_, v___y_3221_, v___y_3222_, v___y_3223_, v___y_3224_, v___y_3225_);
if (lean_obj_tag(v___x_3235_) == 0)
{
lean_object* v_a_3236_; lean_object* v___x_3238_; uint8_t v_isShared_3239_; uint8_t v_isSharedCheck_3254_; 
v_a_3236_ = lean_ctor_get(v___x_3235_, 0);
v_isSharedCheck_3254_ = !lean_is_exclusive(v___x_3235_);
if (v_isSharedCheck_3254_ == 0)
{
v___x_3238_ = v___x_3235_;
v_isShared_3239_ = v_isSharedCheck_3254_;
goto v_resetjp_3237_;
}
else
{
lean_inc(v_a_3236_);
lean_dec(v___x_3235_);
v___x_3238_ = lean_box(0);
v_isShared_3239_ = v_isSharedCheck_3254_;
goto v_resetjp_3237_;
}
v_resetjp_3237_:
{
if (lean_obj_tag(v_a_3236_) == 0)
{
lean_object* v___x_3240_; lean_object* v___x_3242_; 
v___x_3240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3240_, 0, v_a_3236_);
if (v_isShared_3232_ == 0)
{
lean_ctor_set(v___x_3231_, 0, v___x_3240_);
v___x_3242_ = v___x_3231_;
goto v_reusejp_3241_;
}
else
{
lean_object* v_reuseFailAlloc_3246_; 
v_reuseFailAlloc_3246_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3246_, 0, v___x_3240_);
lean_ctor_set(v_reuseFailAlloc_3246_, 1, v_snd_3229_);
v___x_3242_ = v_reuseFailAlloc_3246_;
goto v_reusejp_3241_;
}
v_reusejp_3241_:
{
lean_object* v___x_3244_; 
if (v_isShared_3239_ == 0)
{
lean_ctor_set(v___x_3238_, 0, v___x_3242_);
v___x_3244_ = v___x_3238_;
goto v_reusejp_3243_;
}
else
{
lean_object* v_reuseFailAlloc_3245_; 
v_reuseFailAlloc_3245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3245_, 0, v___x_3242_);
v___x_3244_ = v_reuseFailAlloc_3245_;
goto v_reusejp_3243_;
}
v_reusejp_3243_:
{
return v___x_3244_;
}
}
}
else
{
lean_object* v_a_3247_; lean_object* v___x_3249_; 
lean_del_object(v___x_3238_);
lean_dec(v_snd_3229_);
v_a_3247_ = lean_ctor_get(v_a_3236_, 0);
lean_inc(v_a_3247_);
lean_dec_ref_known(v_a_3236_, 1);
if (v_isShared_3232_ == 0)
{
lean_ctor_set(v___x_3231_, 1, v_a_3247_);
lean_ctor_set(v___x_3231_, 0, v___x_3233_);
v___x_3249_ = v___x_3231_;
goto v_reusejp_3248_;
}
else
{
lean_object* v_reuseFailAlloc_3253_; 
v_reuseFailAlloc_3253_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3253_, 0, v___x_3233_);
lean_ctor_set(v_reuseFailAlloc_3253_, 1, v_a_3247_);
v___x_3249_ = v_reuseFailAlloc_3253_;
goto v_reusejp_3248_;
}
v_reusejp_3248_:
{
size_t v___x_3250_; size_t v___x_3251_; 
v___x_3250_ = ((size_t)1ULL);
v___x_3251_ = lean_usize_add(v_i_3214_, v___x_3250_);
v_i_3214_ = v___x_3251_;
v_b_3215_ = v___x_3249_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_3255_; lean_object* v___x_3257_; uint8_t v_isShared_3258_; uint8_t v_isSharedCheck_3262_; 
lean_del_object(v___x_3231_);
lean_dec(v_snd_3229_);
v_a_3255_ = lean_ctor_get(v___x_3235_, 0);
v_isSharedCheck_3262_ = !lean_is_exclusive(v___x_3235_);
if (v_isSharedCheck_3262_ == 0)
{
v___x_3257_ = v___x_3235_;
v_isShared_3258_ = v_isSharedCheck_3262_;
goto v_resetjp_3256_;
}
else
{
lean_inc(v_a_3255_);
lean_dec(v___x_3235_);
v___x_3257_ = lean_box(0);
v_isShared_3258_ = v_isSharedCheck_3262_;
goto v_resetjp_3256_;
}
v_resetjp_3256_:
{
lean_object* v___x_3260_; 
if (v_isShared_3258_ == 0)
{
v___x_3260_ = v___x_3257_;
goto v_reusejp_3259_;
}
else
{
lean_object* v_reuseFailAlloc_3261_; 
v_reuseFailAlloc_3261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3261_, 0, v_a_3255_);
v___x_3260_ = v_reuseFailAlloc_3261_;
goto v_reusejp_3259_;
}
v_reusejp_3259_:
{
return v___x_3260_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_init_3211_ = stack[0].m_obj;
lean_object* v_as_3212_ = stack[1].m_obj;
size_t v_sz_3213_ = stack[2].m_num;
size_t v_i_3214_ = stack[3].m_num;
lean_object* v_b_3215_ = stack[4].m_obj;
lean_object* v___y_3216_ = stack[5].m_obj;
lean_object* v___y_3217_ = stack[6].m_obj;
lean_object* v___y_3218_ = stack[7].m_obj;
lean_object* v___y_3219_ = stack[8].m_obj;
lean_object* v___y_3220_ = stack[9].m_obj;
lean_object* v___y_3221_ = stack[10].m_obj;
lean_object* v___y_3222_ = stack[11].m_obj;
lean_object* v___y_3223_ = stack[12].m_obj;
lean_object* v___y_3224_ = stack[13].m_obj;
lean_object* v___y_3225_ = stack[14].m_obj;
lean_object* v_res_3265_;
v_res_3265_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__1_spec__2(v_init_3211_, v_as_3212_, v_sz_3213_, v_i_3214_, v_b_3215_, v___y_3216_, v___y_3217_, v___y_3218_, v___y_3219_, v___y_3220_, v___y_3221_, v___y_3222_, v___y_3223_, v___y_3224_, v___y_3225_);
stack->m_obj
 = v_res_3265_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__1_spec__2___boxed(lean_object* v_init_3266_, lean_object* v_as_3267_, lean_object* v_sz_3268_, lean_object* v_i_3269_, lean_object* v_b_3270_, lean_object* v___y_3271_, lean_object* v___y_3272_, lean_object* v___y_3273_, lean_object* v___y_3274_, lean_object* v___y_3275_, lean_object* v___y_3276_, lean_object* v___y_3277_, lean_object* v___y_3278_, lean_object* v___y_3279_, lean_object* v___y_3280_, lean_object* v___y_3281_){
_start:
{
size_t v_sz_boxed_3282_; size_t v_i_boxed_3283_; lean_object* v_res_3284_; 
v_sz_boxed_3282_ = lean_unbox_usize(v_sz_3268_);
lean_dec(v_sz_3268_);
v_i_boxed_3283_ = lean_unbox_usize(v_i_3269_);
lean_dec(v_i_3269_);
v_res_3284_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__1_spec__2(v_init_3266_, v_as_3267_, v_sz_boxed_3282_, v_i_boxed_3283_, v_b_3270_, v___y_3271_, v___y_3272_, v___y_3273_, v___y_3274_, v___y_3275_, v___y_3276_, v___y_3277_, v___y_3278_, v___y_3279_, v___y_3280_);
lean_dec(v___y_3280_);
lean_dec_ref(v___y_3279_);
lean_dec(v___y_3278_);
lean_dec_ref(v___y_3277_);
lean_dec(v___y_3276_);
lean_dec_ref(v___y_3275_);
lean_dec(v___y_3274_);
lean_dec_ref(v___y_3273_);
lean_dec(v___y_3272_);
lean_dec(v___y_3271_);
lean_dec_ref(v_as_3267_);
return v_res_3284_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__1___boxed(lean_object* v_init_3285_, lean_object* v_n_3286_, lean_object* v_b_3287_, lean_object* v___y_3288_, lean_object* v___y_3289_, lean_object* v___y_3290_, lean_object* v___y_3291_, lean_object* v___y_3292_, lean_object* v___y_3293_, lean_object* v___y_3294_, lean_object* v___y_3295_, lean_object* v___y_3296_, lean_object* v___y_3297_, lean_object* v___y_3298_){
_start:
{
lean_object* v_res_3299_; 
v_res_3299_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__1(v_init_3285_, v_n_3286_, v_b_3287_, v___y_3288_, v___y_3289_, v___y_3290_, v___y_3291_, v___y_3292_, v___y_3293_, v___y_3294_, v___y_3295_, v___y_3296_, v___y_3297_);
lean_dec(v___y_3297_);
lean_dec_ref(v___y_3296_);
lean_dec(v___y_3295_);
lean_dec_ref(v___y_3294_);
lean_dec(v___y_3293_);
lean_dec_ref(v___y_3292_);
lean_dec(v___y_3291_);
lean_dec_ref(v___y_3290_);
lean_dec(v___y_3289_);
lean_dec(v___y_3288_);
lean_dec_ref(v_n_3286_);
return v_res_3299_;
}
}
lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1(lean_object* v_t_3300_, lean_object* v_init_3301_, lean_object* v___y_3302_, lean_object* v___y_3303_, lean_object* v___y_3304_, lean_object* v___y_3305_, lean_object* v___y_3306_, lean_object* v___y_3307_, lean_object* v___y_3308_, lean_object* v___y_3309_, lean_object* v___y_3310_, lean_object* v___y_3311_){
_start:
{
lean_object* v_root_3313_; lean_object* v_tail_3314_; lean_object* v___x_3315_; 
v_root_3313_ = lean_ctor_get(v_t_3300_, 0);
v_tail_3314_ = lean_ctor_get(v_t_3300_, 1);
v___x_3315_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__1(v_init_3301_, v_root_3313_, v_init_3301_, v___y_3302_, v___y_3303_, v___y_3304_, v___y_3305_, v___y_3306_, v___y_3307_, v___y_3308_, v___y_3309_, v___y_3310_, v___y_3311_);
if (lean_obj_tag(v___x_3315_) == 0)
{
lean_object* v_a_3316_; lean_object* v___x_3318_; uint8_t v_isShared_3319_; uint8_t v_isSharedCheck_3352_; 
v_a_3316_ = lean_ctor_get(v___x_3315_, 0);
v_isSharedCheck_3352_ = !lean_is_exclusive(v___x_3315_);
if (v_isSharedCheck_3352_ == 0)
{
v___x_3318_ = v___x_3315_;
v_isShared_3319_ = v_isSharedCheck_3352_;
goto v_resetjp_3317_;
}
else
{
lean_inc(v_a_3316_);
lean_dec(v___x_3315_);
v___x_3318_ = lean_box(0);
v_isShared_3319_ = v_isSharedCheck_3352_;
goto v_resetjp_3317_;
}
v_resetjp_3317_:
{
if (lean_obj_tag(v_a_3316_) == 0)
{
lean_object* v_a_3320_; lean_object* v___x_3322_; 
v_a_3320_ = lean_ctor_get(v_a_3316_, 0);
lean_inc(v_a_3320_);
lean_dec_ref_known(v_a_3316_, 1);
if (v_isShared_3319_ == 0)
{
lean_ctor_set(v___x_3318_, 0, v_a_3320_);
v___x_3322_ = v___x_3318_;
goto v_reusejp_3321_;
}
else
{
lean_object* v_reuseFailAlloc_3323_; 
v_reuseFailAlloc_3323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3323_, 0, v_a_3320_);
v___x_3322_ = v_reuseFailAlloc_3323_;
goto v_reusejp_3321_;
}
v_reusejp_3321_:
{
return v___x_3322_;
}
}
else
{
lean_object* v_a_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; size_t v_sz_3327_; size_t v___x_3328_; lean_object* v___x_3329_; 
lean_del_object(v___x_3318_);
v_a_3324_ = lean_ctor_get(v_a_3316_, 0);
lean_inc(v_a_3324_);
lean_dec_ref_known(v_a_3316_, 1);
v___x_3325_ = lean_box(0);
v___x_3326_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3326_, 0, v___x_3325_);
lean_ctor_set(v___x_3326_, 1, v_a_3324_);
v_sz_3327_ = lean_array_size(v_tail_3314_);
v___x_3328_ = ((size_t)0ULL);
v___x_3329_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__2(v_tail_3314_, v_sz_3327_, v___x_3328_, v___x_3326_, v___y_3302_, v___y_3303_, v___y_3304_, v___y_3305_, v___y_3306_, v___y_3307_, v___y_3308_, v___y_3309_, v___y_3310_, v___y_3311_);
if (lean_obj_tag(v___x_3329_) == 0)
{
lean_object* v_a_3330_; lean_object* v___x_3332_; uint8_t v_isShared_3333_; uint8_t v_isSharedCheck_3343_; 
v_a_3330_ = lean_ctor_get(v___x_3329_, 0);
v_isSharedCheck_3343_ = !lean_is_exclusive(v___x_3329_);
if (v_isSharedCheck_3343_ == 0)
{
v___x_3332_ = v___x_3329_;
v_isShared_3333_ = v_isSharedCheck_3343_;
goto v_resetjp_3331_;
}
else
{
lean_inc(v_a_3330_);
lean_dec(v___x_3329_);
v___x_3332_ = lean_box(0);
v_isShared_3333_ = v_isSharedCheck_3343_;
goto v_resetjp_3331_;
}
v_resetjp_3331_:
{
lean_object* v_fst_3334_; 
v_fst_3334_ = lean_ctor_get(v_a_3330_, 0);
if (lean_obj_tag(v_fst_3334_) == 0)
{
lean_object* v_snd_3335_; lean_object* v___x_3337_; 
v_snd_3335_ = lean_ctor_get(v_a_3330_, 1);
lean_inc(v_snd_3335_);
lean_dec(v_a_3330_);
if (v_isShared_3333_ == 0)
{
lean_ctor_set(v___x_3332_, 0, v_snd_3335_);
v___x_3337_ = v___x_3332_;
goto v_reusejp_3336_;
}
else
{
lean_object* v_reuseFailAlloc_3338_; 
v_reuseFailAlloc_3338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3338_, 0, v_snd_3335_);
v___x_3337_ = v_reuseFailAlloc_3338_;
goto v_reusejp_3336_;
}
v_reusejp_3336_:
{
return v___x_3337_;
}
}
else
{
lean_object* v_val_3339_; lean_object* v___x_3341_; 
lean_inc_ref(v_fst_3334_);
lean_dec(v_a_3330_);
v_val_3339_ = lean_ctor_get(v_fst_3334_, 0);
lean_inc(v_val_3339_);
lean_dec_ref_known(v_fst_3334_, 1);
if (v_isShared_3333_ == 0)
{
lean_ctor_set(v___x_3332_, 0, v_val_3339_);
v___x_3341_ = v___x_3332_;
goto v_reusejp_3340_;
}
else
{
lean_object* v_reuseFailAlloc_3342_; 
v_reuseFailAlloc_3342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3342_, 0, v_val_3339_);
v___x_3341_ = v_reuseFailAlloc_3342_;
goto v_reusejp_3340_;
}
v_reusejp_3340_:
{
return v___x_3341_;
}
}
}
}
else
{
lean_object* v_a_3344_; lean_object* v___x_3346_; uint8_t v_isShared_3347_; uint8_t v_isSharedCheck_3351_; 
v_a_3344_ = lean_ctor_get(v___x_3329_, 0);
v_isSharedCheck_3351_ = !lean_is_exclusive(v___x_3329_);
if (v_isSharedCheck_3351_ == 0)
{
v___x_3346_ = v___x_3329_;
v_isShared_3347_ = v_isSharedCheck_3351_;
goto v_resetjp_3345_;
}
else
{
lean_inc(v_a_3344_);
lean_dec(v___x_3329_);
v___x_3346_ = lean_box(0);
v_isShared_3347_ = v_isSharedCheck_3351_;
goto v_resetjp_3345_;
}
v_resetjp_3345_:
{
lean_object* v___x_3349_; 
if (v_isShared_3347_ == 0)
{
v___x_3349_ = v___x_3346_;
goto v_reusejp_3348_;
}
else
{
lean_object* v_reuseFailAlloc_3350_; 
v_reuseFailAlloc_3350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3350_, 0, v_a_3344_);
v___x_3349_ = v_reuseFailAlloc_3350_;
goto v_reusejp_3348_;
}
v_reusejp_3348_:
{
return v___x_3349_;
}
}
}
}
}
}
else
{
lean_object* v_a_3353_; lean_object* v___x_3355_; uint8_t v_isShared_3356_; uint8_t v_isSharedCheck_3360_; 
v_a_3353_ = lean_ctor_get(v___x_3315_, 0);
v_isSharedCheck_3360_ = !lean_is_exclusive(v___x_3315_);
if (v_isSharedCheck_3360_ == 0)
{
v___x_3355_ = v___x_3315_;
v_isShared_3356_ = v_isSharedCheck_3360_;
goto v_resetjp_3354_;
}
else
{
lean_inc(v_a_3353_);
lean_dec(v___x_3315_);
v___x_3355_ = lean_box(0);
v_isShared_3356_ = v_isSharedCheck_3360_;
goto v_resetjp_3354_;
}
v_resetjp_3354_:
{
lean_object* v___x_3358_; 
if (v_isShared_3356_ == 0)
{
v___x_3358_ = v___x_3355_;
goto v_reusejp_3357_;
}
else
{
lean_object* v_reuseFailAlloc_3359_; 
v_reuseFailAlloc_3359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3359_, 0, v_a_3353_);
v___x_3358_ = v_reuseFailAlloc_3359_;
goto v_reusejp_3357_;
}
v_reusejp_3357_:
{
return v___x_3358_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_3300_ = stack[0].m_obj;
lean_object* v_init_3301_ = stack[1].m_obj;
lean_object* v___y_3302_ = stack[2].m_obj;
lean_object* v___y_3303_ = stack[3].m_obj;
lean_object* v___y_3304_ = stack[4].m_obj;
lean_object* v___y_3305_ = stack[5].m_obj;
lean_object* v___y_3306_ = stack[6].m_obj;
lean_object* v___y_3307_ = stack[7].m_obj;
lean_object* v___y_3308_ = stack[8].m_obj;
lean_object* v___y_3309_ = stack[9].m_obj;
lean_object* v___y_3310_ = stack[10].m_obj;
lean_object* v___y_3311_ = stack[11].m_obj;
lean_object* v_res_3361_;
v_res_3361_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1(v_t_3300_, v_init_3301_, v___y_3302_, v___y_3303_, v___y_3304_, v___y_3305_, v___y_3306_, v___y_3307_, v___y_3308_, v___y_3309_, v___y_3310_, v___y_3311_);
stack->m_obj
 = v_res_3361_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1___boxed(lean_object* v_t_3362_, lean_object* v_init_3363_, lean_object* v___y_3364_, lean_object* v___y_3365_, lean_object* v___y_3366_, lean_object* v___y_3367_, lean_object* v___y_3368_, lean_object* v___y_3369_, lean_object* v___y_3370_, lean_object* v___y_3371_, lean_object* v___y_3372_, lean_object* v___y_3373_, lean_object* v___y_3374_){
_start:
{
lean_object* v_res_3375_; 
v_res_3375_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1(v_t_3362_, v_init_3363_, v___y_3364_, v___y_3365_, v___y_3366_, v___y_3367_, v___y_3368_, v___y_3369_, v___y_3370_, v___y_3371_, v___y_3372_, v___y_3373_);
lean_dec(v___y_3373_);
lean_dec_ref(v___y_3372_);
lean_dec(v___y_3371_);
lean_dec_ref(v___y_3370_);
lean_dec(v___y_3369_);
lean_dec_ref(v___y_3368_);
lean_dec(v___y_3367_);
lean_dec_ref(v___y_3366_);
lean_dec(v___y_3365_);
lean_dec(v___y_3364_);
lean_dec_ref(v_t_3362_);
return v_res_3375_;
}
}
lean_object* l_Lean_Meta_Grind_checkInvariants(uint8_t v_expensive_3376_, lean_object* v_a_3377_, lean_object* v_a_3378_, lean_object* v_a_3379_, lean_object* v_a_3380_, lean_object* v_a_3381_, lean_object* v_a_3382_, lean_object* v_a_3383_, lean_object* v_a_3384_, lean_object* v_a_3385_, lean_object* v_a_3386_){
_start:
{
lean_object* v___y_3392_; lean_object* v___y_3393_; lean_object* v___y_3394_; lean_object* v___y_3395_; lean_object* v___y_3396_; lean_object* v___y_3397_; lean_object* v___y_3398_; lean_object* v___y_3399_; lean_object* v___y_3400_; lean_object* v___y_3401_; lean_object* v___y_3407_; lean_object* v___y_3408_; lean_object* v___y_3409_; lean_object* v___y_3410_; lean_object* v___y_3411_; lean_object* v___y_3412_; lean_object* v___y_3413_; lean_object* v___y_3414_; lean_object* v___y_3415_; lean_object* v___y_3416_; uint8_t v_debug_3418_; 
v_debug_3418_ = lean_ctor_get_uint8(v_a_3379_, sizeof(void*)*10 + 2);
if (v_debug_3418_ == 0)
{
v___y_3392_ = v_a_3377_;
v___y_3393_ = v_a_3378_;
v___y_3394_ = v_a_3379_;
v___y_3395_ = v_a_3380_;
v___y_3396_ = v_a_3381_;
v___y_3397_ = v_a_3382_;
v___y_3398_ = v_a_3383_;
v___y_3399_ = v_a_3384_;
v___y_3400_ = v_a_3385_;
v___y_3401_ = v_a_3386_;
goto v___jp_3391_;
}
else
{
lean_object* v___x_3419_; 
v___x_3419_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable(v_a_3377_, v_a_3378_, v_a_3379_, v_a_3380_, v_a_3381_, v_a_3382_, v_a_3383_, v_a_3384_, v_a_3385_, v_a_3386_);
if (lean_obj_tag(v___x_3419_) == 0)
{
lean_object* v___x_3420_; 
lean_dec_ref_known(v___x_3419_, 1);
v___x_3420_ = l_Lean_Meta_Grind_getExprs___redArg(v_a_3377_);
if (lean_obj_tag(v___x_3420_) == 0)
{
lean_object* v_a_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; 
v_a_3421_ = lean_ctor_get(v___x_3420_, 0);
lean_inc(v_a_3421_);
lean_dec_ref_known(v___x_3420_, 1);
v___x_3422_ = lean_box(0);
v___x_3423_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1(v_a_3421_, v___x_3422_, v_a_3377_, v_a_3378_, v_a_3379_, v_a_3380_, v_a_3381_, v_a_3382_, v_a_3383_, v_a_3384_, v_a_3385_, v_a_3386_);
lean_dec(v_a_3421_);
if (lean_obj_tag(v___x_3423_) == 0)
{
lean_dec_ref_known(v___x_3423_, 1);
if (v_expensive_3376_ == 0)
{
v___y_3407_ = v_a_3377_;
v___y_3408_ = v_a_3378_;
v___y_3409_ = v_a_3379_;
v___y_3410_ = v_a_3380_;
v___y_3411_ = v_a_3381_;
v___y_3412_ = v_a_3382_;
v___y_3413_ = v_a_3383_;
v___y_3414_ = v_a_3384_;
v___y_3415_ = v_a_3385_;
v___y_3416_ = v_a_3386_;
goto v___jp_3406_;
}
else
{
lean_object* v___x_3424_; 
v___x_3424_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq(v_a_3377_, v_a_3378_, v_a_3379_, v_a_3380_, v_a_3381_, v_a_3382_, v_a_3383_, v_a_3384_, v_a_3385_, v_a_3386_);
if (lean_obj_tag(v___x_3424_) == 0)
{
lean_dec_ref_known(v___x_3424_, 1);
v___y_3407_ = v_a_3377_;
v___y_3408_ = v_a_3378_;
v___y_3409_ = v_a_3379_;
v___y_3410_ = v_a_3380_;
v___y_3411_ = v_a_3381_;
v___y_3412_ = v_a_3382_;
v___y_3413_ = v_a_3383_;
v___y_3414_ = v_a_3384_;
v___y_3415_ = v_a_3385_;
v___y_3416_ = v_a_3386_;
goto v___jp_3406_;
}
else
{
return v___x_3424_;
}
}
}
else
{
return v___x_3423_;
}
}
else
{
lean_object* v_a_3425_; lean_object* v___x_3427_; uint8_t v_isShared_3428_; uint8_t v_isSharedCheck_3432_; 
v_a_3425_ = lean_ctor_get(v___x_3420_, 0);
v_isSharedCheck_3432_ = !lean_is_exclusive(v___x_3420_);
if (v_isSharedCheck_3432_ == 0)
{
v___x_3427_ = v___x_3420_;
v_isShared_3428_ = v_isSharedCheck_3432_;
goto v_resetjp_3426_;
}
else
{
lean_inc(v_a_3425_);
lean_dec(v___x_3420_);
v___x_3427_ = lean_box(0);
v_isShared_3428_ = v_isSharedCheck_3432_;
goto v_resetjp_3426_;
}
v_resetjp_3426_:
{
lean_object* v___x_3430_; 
if (v_isShared_3428_ == 0)
{
v___x_3430_ = v___x_3427_;
goto v_reusejp_3429_;
}
else
{
lean_object* v_reuseFailAlloc_3431_; 
v_reuseFailAlloc_3431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3431_, 0, v_a_3425_);
v___x_3430_ = v_reuseFailAlloc_3431_;
goto v_reusejp_3429_;
}
v_reusejp_3429_:
{
return v___x_3430_;
}
}
}
}
else
{
return v___x_3419_;
}
}
v___jp_3388_:
{
lean_object* v___x_3389_; lean_object* v___x_3390_; 
v___x_3389_ = lean_box(0);
v___x_3390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3390_, 0, v___x_3389_);
return v___x_3390_;
}
v___jp_3391_:
{
if (v_expensive_3376_ == 0)
{
goto v___jp_3388_;
}
else
{
lean_object* v___x_3402_; lean_object* v___x_3403_; uint8_t v___x_3404_; 
v___x_3402_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_3400_);
v___x_3403_ = l_Lean_Meta_Grind_grind_debug_proofs;
v___x_3404_ = l_Lean_Option_get___at___00Lean_Meta_Grind_checkInvariants_spec__0(v___x_3402_, v___x_3403_);
lean_dec_ref(v___x_3402_);
if (v___x_3404_ == 0)
{
goto v___jp_3388_;
}
else
{
lean_object* v___x_3405_; 
v___x_3405_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs(v___y_3392_, v___y_3393_, v___y_3394_, v___y_3395_, v___y_3396_, v___y_3397_, v___y_3398_, v___y_3399_, v___y_3400_, v___y_3401_);
return v___x_3405_;
}
}
}
v___jp_3406_:
{
lean_object* v___x_3417_; 
v___x_3417_ = l_Lean_Meta_Grind_Solvers_checkInvariants(v___y_3407_, v___y_3408_, v___y_3409_, v___y_3410_, v___y_3411_, v___y_3412_, v___y_3413_, v___y_3414_, v___y_3415_, v___y_3416_);
if (lean_obj_tag(v___x_3417_) == 0)
{
lean_dec_ref_known(v___x_3417_, 1);
v___y_3392_ = v___y_3407_;
v___y_3393_ = v___y_3408_;
v___y_3394_ = v___y_3409_;
v___y_3395_ = v___y_3410_;
v___y_3396_ = v___y_3411_;
v___y_3397_ = v___y_3412_;
v___y_3398_ = v___y_3413_;
v___y_3399_ = v___y_3414_;
v___y_3400_ = v___y_3415_;
v___y_3401_ = v___y_3416_;
goto v___jp_3391_;
}
else
{
return v___x_3417_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_checkInvariants_0interp(lean_interpreter_value* stack)
{
uint8_t v_expensive_3376_ = stack[0].m_num;
lean_object* v_a_3377_ = stack[1].m_obj;
lean_object* v_a_3378_ = stack[2].m_obj;
lean_object* v_a_3379_ = stack[3].m_obj;
lean_object* v_a_3380_ = stack[4].m_obj;
lean_object* v_a_3381_ = stack[5].m_obj;
lean_object* v_a_3382_ = stack[6].m_obj;
lean_object* v_a_3383_ = stack[7].m_obj;
lean_object* v_a_3384_ = stack[8].m_obj;
lean_object* v_a_3385_ = stack[9].m_obj;
lean_object* v_a_3386_ = stack[10].m_obj;
lean_object* v_res_3433_;
v_res_3433_ = l_Lean_Meta_Grind_checkInvariants(v_expensive_3376_, v_a_3377_, v_a_3378_, v_a_3379_, v_a_3380_, v_a_3381_, v_a_3382_, v_a_3383_, v_a_3384_, v_a_3385_, v_a_3386_);
stack->m_obj
 = v_res_3433_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_checkInvariants___boxed(lean_object* v_expensive_3434_, lean_object* v_a_3435_, lean_object* v_a_3436_, lean_object* v_a_3437_, lean_object* v_a_3438_, lean_object* v_a_3439_, lean_object* v_a_3440_, lean_object* v_a_3441_, lean_object* v_a_3442_, lean_object* v_a_3443_, lean_object* v_a_3444_, lean_object* v_a_3445_){
_start:
{
uint8_t v_expensive_boxed_3446_; lean_object* v_res_3447_; 
v_expensive_boxed_3446_ = lean_unbox(v_expensive_3434_);
v_res_3447_ = l_Lean_Meta_Grind_checkInvariants(v_expensive_boxed_3446_, v_a_3435_, v_a_3436_, v_a_3437_, v_a_3438_, v_a_3439_, v_a_3440_, v_a_3441_, v_a_3442_, v_a_3443_, v_a_3444_);
lean_dec(v_a_3444_);
lean_dec_ref(v_a_3443_);
lean_dec(v_a_3442_);
lean_dec_ref(v_a_3441_);
lean_dec(v_a_3440_);
lean_dec_ref(v_a_3439_);
lean_dec(v_a_3438_);
lean_dec_ref(v_a_3437_);
lean_dec(v_a_3436_);
lean_dec(v_a_3435_);
return v_res_3447_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Goal_checkInvariants_spec__0___redArg___lam__0(lean_object* v_x_3448_, lean_object* v___y_3449_, lean_object* v___y_3450_, lean_object* v___y_3451_, lean_object* v___y_3452_, lean_object* v___y_3453_, lean_object* v___y_3454_, lean_object* v___y_3455_, lean_object* v___y_3456_, lean_object* v___y_3457_){
_start:
{
lean_object* v___x_3459_; 
lean_inc(v___y_3453_);
lean_inc_ref(v___y_3452_);
lean_inc(v___y_3451_);
lean_inc_ref(v___y_3450_);
lean_inc(v___y_3449_);
v___x_3459_ = lean_apply_10(v_x_3448_, v___y_3449_, v___y_3450_, v___y_3451_, v___y_3452_, v___y_3453_, v___y_3454_, v___y_3455_, v___y_3456_, v___y_3457_, lean_box(0));
return v___x_3459_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Goal_checkInvariants_spec__0___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3448_ = stack[0].m_obj;
lean_object* v___y_3449_ = stack[1].m_obj;
lean_object* v___y_3450_ = stack[2].m_obj;
lean_object* v___y_3451_ = stack[3].m_obj;
lean_object* v___y_3452_ = stack[4].m_obj;
lean_object* v___y_3453_ = stack[5].m_obj;
lean_object* v___y_3454_ = stack[6].m_obj;
lean_object* v___y_3455_ = stack[7].m_obj;
lean_object* v___y_3456_ = stack[8].m_obj;
lean_object* v___y_3457_ = stack[9].m_obj;
lean_object* v_res_3460_;
v_res_3460_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Goal_checkInvariants_spec__0___redArg___lam__0(v_x_3448_, v___y_3449_, v___y_3450_, v___y_3451_, v___y_3452_, v___y_3453_, v___y_3454_, v___y_3455_, v___y_3456_, v___y_3457_);
stack->m_obj
 = v_res_3460_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Goal_checkInvariants_spec__0___redArg___lam__0___boxed(lean_object* v_x_3461_, lean_object* v___y_3462_, lean_object* v___y_3463_, lean_object* v___y_3464_, lean_object* v___y_3465_, lean_object* v___y_3466_, lean_object* v___y_3467_, lean_object* v___y_3468_, lean_object* v___y_3469_, lean_object* v___y_3470_, lean_object* v___y_3471_){
_start:
{
lean_object* v_res_3472_; 
v_res_3472_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Goal_checkInvariants_spec__0___redArg___lam__0(v_x_3461_, v___y_3462_, v___y_3463_, v___y_3464_, v___y_3465_, v___y_3466_, v___y_3467_, v___y_3468_, v___y_3469_, v___y_3470_);
lean_dec(v___y_3466_);
lean_dec_ref(v___y_3465_);
lean_dec(v___y_3464_);
lean_dec_ref(v___y_3463_);
lean_dec(v___y_3462_);
return v_res_3472_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Goal_checkInvariants_spec__0___redArg(lean_object* v_mvarId_3473_, lean_object* v_x_3474_, lean_object* v___y_3475_, lean_object* v___y_3476_, lean_object* v___y_3477_, lean_object* v___y_3478_, lean_object* v___y_3479_, lean_object* v___y_3480_, lean_object* v___y_3481_, lean_object* v___y_3482_, lean_object* v___y_3483_){
_start:
{
lean_object* v___f_3485_; lean_object* v___x_3486_; 
lean_inc(v___y_3479_);
lean_inc_ref(v___y_3478_);
lean_inc(v___y_3477_);
lean_inc_ref(v___y_3476_);
lean_inc(v___y_3475_);
v___f_3485_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Goal_checkInvariants_spec__0___redArg___lam__0___boxed), 11, 6);
lean_closure_set(v___f_3485_, 0, v_x_3474_);
lean_closure_set(v___f_3485_, 1, v___y_3475_);
lean_closure_set(v___f_3485_, 2, v___y_3476_);
lean_closure_set(v___f_3485_, 3, v___y_3477_);
lean_closure_set(v___f_3485_, 4, v___y_3478_);
lean_closure_set(v___f_3485_, 5, v___y_3479_);
v___x_3486_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_3473_, v___f_3485_, v___y_3480_, v___y_3481_, v___y_3482_, v___y_3483_);
if (lean_obj_tag(v___x_3486_) == 0)
{
return v___x_3486_;
}
else
{
lean_object* v_a_3487_; lean_object* v___x_3489_; uint8_t v_isShared_3490_; uint8_t v_isSharedCheck_3494_; 
v_a_3487_ = lean_ctor_get(v___x_3486_, 0);
v_isSharedCheck_3494_ = !lean_is_exclusive(v___x_3486_);
if (v_isSharedCheck_3494_ == 0)
{
v___x_3489_ = v___x_3486_;
v_isShared_3490_ = v_isSharedCheck_3494_;
goto v_resetjp_3488_;
}
else
{
lean_inc(v_a_3487_);
lean_dec(v___x_3486_);
v___x_3489_ = lean_box(0);
v_isShared_3490_ = v_isSharedCheck_3494_;
goto v_resetjp_3488_;
}
v_resetjp_3488_:
{
lean_object* v___x_3492_; 
if (v_isShared_3490_ == 0)
{
v___x_3492_ = v___x_3489_;
goto v_reusejp_3491_;
}
else
{
lean_object* v_reuseFailAlloc_3493_; 
v_reuseFailAlloc_3493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3493_, 0, v_a_3487_);
v___x_3492_ = v_reuseFailAlloc_3493_;
goto v_reusejp_3491_;
}
v_reusejp_3491_:
{
return v___x_3492_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Goal_checkInvariants_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_3473_ = stack[0].m_obj;
lean_object* v_x_3474_ = stack[1].m_obj;
lean_object* v___y_3475_ = stack[2].m_obj;
lean_object* v___y_3476_ = stack[3].m_obj;
lean_object* v___y_3477_ = stack[4].m_obj;
lean_object* v___y_3478_ = stack[5].m_obj;
lean_object* v___y_3479_ = stack[6].m_obj;
lean_object* v___y_3480_ = stack[7].m_obj;
lean_object* v___y_3481_ = stack[8].m_obj;
lean_object* v___y_3482_ = stack[9].m_obj;
lean_object* v___y_3483_ = stack[10].m_obj;
lean_object* v_res_3495_;
v_res_3495_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Goal_checkInvariants_spec__0___redArg(v_mvarId_3473_, v_x_3474_, v___y_3475_, v___y_3476_, v___y_3477_, v___y_3478_, v___y_3479_, v___y_3480_, v___y_3481_, v___y_3482_, v___y_3483_);
stack->m_obj
 = v_res_3495_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Goal_checkInvariants_spec__0___redArg___boxed(lean_object* v_mvarId_3496_, lean_object* v_x_3497_, lean_object* v___y_3498_, lean_object* v___y_3499_, lean_object* v___y_3500_, lean_object* v___y_3501_, lean_object* v___y_3502_, lean_object* v___y_3503_, lean_object* v___y_3504_, lean_object* v___y_3505_, lean_object* v___y_3506_, lean_object* v___y_3507_){
_start:
{
lean_object* v_res_3508_; 
v_res_3508_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Goal_checkInvariants_spec__0___redArg(v_mvarId_3496_, v_x_3497_, v___y_3498_, v___y_3499_, v___y_3500_, v___y_3501_, v___y_3502_, v___y_3503_, v___y_3504_, v___y_3505_, v___y_3506_);
lean_dec(v___y_3506_);
lean_dec_ref(v___y_3505_);
lean_dec(v___y_3504_);
lean_dec_ref(v___y_3503_);
lean_dec(v___y_3502_);
lean_dec_ref(v___y_3501_);
lean_dec(v___y_3500_);
lean_dec_ref(v___y_3499_);
lean_dec(v___y_3498_);
return v_res_3508_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Goal_checkInvariants_spec__0(lean_object* v_00_u03b1_3509_, lean_object* v_mvarId_3510_, lean_object* v_x_3511_, lean_object* v___y_3512_, lean_object* v___y_3513_, lean_object* v___y_3514_, lean_object* v___y_3515_, lean_object* v___y_3516_, lean_object* v___y_3517_, lean_object* v___y_3518_, lean_object* v___y_3519_, lean_object* v___y_3520_){
_start:
{
lean_object* v___x_3522_; 
v___x_3522_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Goal_checkInvariants_spec__0___redArg(v_mvarId_3510_, v_x_3511_, v___y_3512_, v___y_3513_, v___y_3514_, v___y_3515_, v___y_3516_, v___y_3517_, v___y_3518_, v___y_3519_, v___y_3520_);
return v___x_3522_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Goal_checkInvariants_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_3510_ = stack[1].m_obj;
lean_object* v_x_3511_ = stack[2].m_obj;
lean_object* v___y_3512_ = stack[3].m_obj;
lean_object* v___y_3513_ = stack[4].m_obj;
lean_object* v___y_3514_ = stack[5].m_obj;
lean_object* v___y_3515_ = stack[6].m_obj;
lean_object* v___y_3516_ = stack[7].m_obj;
lean_object* v___y_3517_ = stack[8].m_obj;
lean_object* v___y_3518_ = stack[9].m_obj;
lean_object* v___y_3519_ = stack[10].m_obj;
lean_object* v___y_3520_ = stack[11].m_obj;
lean_object* v_res_3523_;
v_res_3523_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Goal_checkInvariants_spec__0(lean_box(0), v_mvarId_3510_, v_x_3511_, v___y_3512_, v___y_3513_, v___y_3514_, v___y_3515_, v___y_3516_, v___y_3517_, v___y_3518_, v___y_3519_, v___y_3520_);
stack->m_obj
 = v_res_3523_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Goal_checkInvariants_spec__0___boxed(lean_object* v_00_u03b1_3524_, lean_object* v_mvarId_3525_, lean_object* v_x_3526_, lean_object* v___y_3527_, lean_object* v___y_3528_, lean_object* v___y_3529_, lean_object* v___y_3530_, lean_object* v___y_3531_, lean_object* v___y_3532_, lean_object* v___y_3533_, lean_object* v___y_3534_, lean_object* v___y_3535_, lean_object* v___y_3536_){
_start:
{
lean_object* v_res_3537_; 
v_res_3537_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Goal_checkInvariants_spec__0(v_00_u03b1_3524_, v_mvarId_3525_, v_x_3526_, v___y_3527_, v___y_3528_, v___y_3529_, v___y_3530_, v___y_3531_, v___y_3532_, v___y_3533_, v___y_3534_, v___y_3535_);
lean_dec(v___y_3535_);
lean_dec_ref(v___y_3534_);
lean_dec(v___y_3533_);
lean_dec_ref(v___y_3532_);
lean_dec(v___y_3531_);
lean_dec_ref(v___y_3530_);
lean_dec(v___y_3529_);
lean_dec_ref(v___y_3528_);
lean_dec(v___y_3527_);
return v_res_3537_;
}
}
lean_object* l_Lean_Meta_Grind_Goal_checkInvariants___lam__0(lean_object* v_goal_3538_, uint8_t v_expensive_3539_, lean_object* v___y_3540_, lean_object* v___y_3541_, lean_object* v___y_3542_, lean_object* v___y_3543_, lean_object* v___y_3544_, lean_object* v___y_3545_, lean_object* v___y_3546_, lean_object* v___y_3547_, lean_object* v___y_3548_){
_start:
{
lean_object* v___x_3550_; lean_object* v___x_3551_; 
v___x_3550_ = lean_st_mk_ref(v_goal_3538_);
v___x_3551_ = l_Lean_Meta_Grind_checkInvariants(v_expensive_3539_, v___x_3550_, v___y_3540_, v___y_3541_, v___y_3542_, v___y_3543_, v___y_3544_, v___y_3545_, v___y_3546_, v___y_3547_, v___y_3548_);
if (lean_obj_tag(v___x_3551_) == 0)
{
lean_object* v___x_3553_; uint8_t v_isShared_3554_; uint8_t v_isSharedCheck_3560_; 
v_isSharedCheck_3560_ = !lean_is_exclusive(v___x_3551_);
if (v_isSharedCheck_3560_ == 0)
{
lean_object* v_unused_3561_; 
v_unused_3561_ = lean_ctor_get(v___x_3551_, 0);
lean_dec(v_unused_3561_);
v___x_3553_ = v___x_3551_;
v_isShared_3554_ = v_isSharedCheck_3560_;
goto v_resetjp_3552_;
}
else
{
lean_dec(v___x_3551_);
v___x_3553_ = lean_box(0);
v_isShared_3554_ = v_isSharedCheck_3560_;
goto v_resetjp_3552_;
}
v_resetjp_3552_:
{
lean_object* v___x_3555_; lean_object* v___x_3556_; lean_object* v___x_3558_; 
v___x_3555_ = lean_st_ref_get(v___x_3550_);
v___x_3556_ = lean_st_ref_get(v___x_3550_);
lean_dec(v___x_3550_);
lean_dec(v___x_3556_);
if (v_isShared_3554_ == 0)
{
lean_ctor_set(v___x_3553_, 0, v___x_3555_);
v___x_3558_ = v___x_3553_;
goto v_reusejp_3557_;
}
else
{
lean_object* v_reuseFailAlloc_3559_; 
v_reuseFailAlloc_3559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3559_, 0, v___x_3555_);
v___x_3558_ = v_reuseFailAlloc_3559_;
goto v_reusejp_3557_;
}
v_reusejp_3557_:
{
return v___x_3558_;
}
}
}
else
{
lean_object* v_a_3562_; lean_object* v___x_3564_; uint8_t v_isShared_3565_; uint8_t v_isSharedCheck_3569_; 
lean_dec(v___x_3550_);
v_a_3562_ = lean_ctor_get(v___x_3551_, 0);
v_isSharedCheck_3569_ = !lean_is_exclusive(v___x_3551_);
if (v_isSharedCheck_3569_ == 0)
{
v___x_3564_ = v___x_3551_;
v_isShared_3565_ = v_isSharedCheck_3569_;
goto v_resetjp_3563_;
}
else
{
lean_inc(v_a_3562_);
lean_dec(v___x_3551_);
v___x_3564_ = lean_box(0);
v_isShared_3565_ = v_isSharedCheck_3569_;
goto v_resetjp_3563_;
}
v_resetjp_3563_:
{
lean_object* v___x_3567_; 
if (v_isShared_3565_ == 0)
{
v___x_3567_ = v___x_3564_;
goto v_reusejp_3566_;
}
else
{
lean_object* v_reuseFailAlloc_3568_; 
v_reuseFailAlloc_3568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3568_, 0, v_a_3562_);
v___x_3567_ = v_reuseFailAlloc_3568_;
goto v_reusejp_3566_;
}
v_reusejp_3566_:
{
return v___x_3567_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Goal_checkInvariants___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_goal_3538_ = stack[0].m_obj;
uint8_t v_expensive_3539_ = stack[1].m_num;
lean_object* v___y_3540_ = stack[2].m_obj;
lean_object* v___y_3541_ = stack[3].m_obj;
lean_object* v___y_3542_ = stack[4].m_obj;
lean_object* v___y_3543_ = stack[5].m_obj;
lean_object* v___y_3544_ = stack[6].m_obj;
lean_object* v___y_3545_ = stack[7].m_obj;
lean_object* v___y_3546_ = stack[8].m_obj;
lean_object* v___y_3547_ = stack[9].m_obj;
lean_object* v___y_3548_ = stack[10].m_obj;
lean_object* v_res_3570_;
v_res_3570_ = l_Lean_Meta_Grind_Goal_checkInvariants___lam__0(v_goal_3538_, v_expensive_3539_, v___y_3540_, v___y_3541_, v___y_3542_, v___y_3543_, v___y_3544_, v___y_3545_, v___y_3546_, v___y_3547_, v___y_3548_);
stack->m_obj
 = v_res_3570_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Goal_checkInvariants___lam__0___boxed(lean_object* v_goal_3571_, lean_object* v_expensive_3572_, lean_object* v___y_3573_, lean_object* v___y_3574_, lean_object* v___y_3575_, lean_object* v___y_3576_, lean_object* v___y_3577_, lean_object* v___y_3578_, lean_object* v___y_3579_, lean_object* v___y_3580_, lean_object* v___y_3581_, lean_object* v___y_3582_){
_start:
{
uint8_t v_expensive_boxed_3583_; lean_object* v_res_3584_; 
v_expensive_boxed_3583_ = lean_unbox(v_expensive_3572_);
v_res_3584_ = l_Lean_Meta_Grind_Goal_checkInvariants___lam__0(v_goal_3571_, v_expensive_boxed_3583_, v___y_3573_, v___y_3574_, v___y_3575_, v___y_3576_, v___y_3577_, v___y_3578_, v___y_3579_, v___y_3580_, v___y_3581_);
lean_dec(v___y_3581_);
lean_dec_ref(v___y_3580_);
lean_dec(v___y_3579_);
lean_dec_ref(v___y_3578_);
lean_dec(v___y_3577_);
lean_dec_ref(v___y_3576_);
lean_dec(v___y_3575_);
lean_dec_ref(v___y_3574_);
lean_dec(v___y_3573_);
return v_res_3584_;
}
}
lean_object* l_Lean_Meta_Grind_Goal_checkInvariants(lean_object* v_goal_3585_, uint8_t v_expensive_3586_, lean_object* v_a_3587_, lean_object* v_a_3588_, lean_object* v_a_3589_, lean_object* v_a_3590_, lean_object* v_a_3591_, lean_object* v_a_3592_, lean_object* v_a_3593_, lean_object* v_a_3594_, lean_object* v_a_3595_){
_start:
{
lean_object* v_mvarId_3597_; lean_object* v___x_3598_; lean_object* v___f_3599_; lean_object* v___x_3600_; lean_object* v___x_3601_; 
v_mvarId_3597_ = lean_ctor_get(v_goal_3585_, 1);
lean_inc(v_mvarId_3597_);
v___x_3598_ = lean_box(v_expensive_3586_);
v___f_3599_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Goal_checkInvariants___lam__0___boxed), 12, 2);
lean_closure_set(v___f_3599_, 0, v_goal_3585_);
lean_closure_set(v___f_3599_, 1, v___x_3598_);
v___x_3600_ = lean_box(0);
v___x_3601_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Goal_checkInvariants_spec__0___redArg(v_mvarId_3597_, v___f_3599_, v_a_3587_, v_a_3588_, v_a_3589_, v_a_3590_, v_a_3591_, v_a_3592_, v_a_3593_, v_a_3594_, v_a_3595_);
if (lean_obj_tag(v___x_3601_) == 0)
{
lean_object* v___x_3603_; uint8_t v_isShared_3604_; uint8_t v_isSharedCheck_3608_; 
v_isSharedCheck_3608_ = !lean_is_exclusive(v___x_3601_);
if (v_isSharedCheck_3608_ == 0)
{
lean_object* v_unused_3609_; 
v_unused_3609_ = lean_ctor_get(v___x_3601_, 0);
lean_dec(v_unused_3609_);
v___x_3603_ = v___x_3601_;
v_isShared_3604_ = v_isSharedCheck_3608_;
goto v_resetjp_3602_;
}
else
{
lean_dec(v___x_3601_);
v___x_3603_ = lean_box(0);
v_isShared_3604_ = v_isSharedCheck_3608_;
goto v_resetjp_3602_;
}
v_resetjp_3602_:
{
lean_object* v___x_3606_; 
if (v_isShared_3604_ == 0)
{
lean_ctor_set(v___x_3603_, 0, v___x_3600_);
v___x_3606_ = v___x_3603_;
goto v_reusejp_3605_;
}
else
{
lean_object* v_reuseFailAlloc_3607_; 
v_reuseFailAlloc_3607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3607_, 0, v___x_3600_);
v___x_3606_ = v_reuseFailAlloc_3607_;
goto v_reusejp_3605_;
}
v_reusejp_3605_:
{
return v___x_3606_;
}
}
}
else
{
lean_object* v_a_3610_; lean_object* v___x_3612_; uint8_t v_isShared_3613_; uint8_t v_isSharedCheck_3617_; 
v_a_3610_ = lean_ctor_get(v___x_3601_, 0);
v_isSharedCheck_3617_ = !lean_is_exclusive(v___x_3601_);
if (v_isSharedCheck_3617_ == 0)
{
v___x_3612_ = v___x_3601_;
v_isShared_3613_ = v_isSharedCheck_3617_;
goto v_resetjp_3611_;
}
else
{
lean_inc(v_a_3610_);
lean_dec(v___x_3601_);
v___x_3612_ = lean_box(0);
v_isShared_3613_ = v_isSharedCheck_3617_;
goto v_resetjp_3611_;
}
v_resetjp_3611_:
{
lean_object* v___x_3615_; 
if (v_isShared_3613_ == 0)
{
v___x_3615_ = v___x_3612_;
goto v_reusejp_3614_;
}
else
{
lean_object* v_reuseFailAlloc_3616_; 
v_reuseFailAlloc_3616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3616_, 0, v_a_3610_);
v___x_3615_ = v_reuseFailAlloc_3616_;
goto v_reusejp_3614_;
}
v_reusejp_3614_:
{
return v___x_3615_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Goal_checkInvariants_0interp(lean_interpreter_value* stack)
{
lean_object* v_goal_3585_ = stack[0].m_obj;
uint8_t v_expensive_3586_ = stack[1].m_num;
lean_object* v_a_3587_ = stack[2].m_obj;
lean_object* v_a_3588_ = stack[3].m_obj;
lean_object* v_a_3589_ = stack[4].m_obj;
lean_object* v_a_3590_ = stack[5].m_obj;
lean_object* v_a_3591_ = stack[6].m_obj;
lean_object* v_a_3592_ = stack[7].m_obj;
lean_object* v_a_3593_ = stack[8].m_obj;
lean_object* v_a_3594_ = stack[9].m_obj;
lean_object* v_a_3595_ = stack[10].m_obj;
lean_object* v_res_3618_;
v_res_3618_ = l_Lean_Meta_Grind_Goal_checkInvariants(v_goal_3585_, v_expensive_3586_, v_a_3587_, v_a_3588_, v_a_3589_, v_a_3590_, v_a_3591_, v_a_3592_, v_a_3593_, v_a_3594_, v_a_3595_);
stack->m_obj
 = v_res_3618_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Goal_checkInvariants___boxed(lean_object* v_goal_3619_, lean_object* v_expensive_3620_, lean_object* v_a_3621_, lean_object* v_a_3622_, lean_object* v_a_3623_, lean_object* v_a_3624_, lean_object* v_a_3625_, lean_object* v_a_3626_, lean_object* v_a_3627_, lean_object* v_a_3628_, lean_object* v_a_3629_, lean_object* v_a_3630_){
_start:
{
uint8_t v_expensive_boxed_3631_; lean_object* v_res_3632_; 
v_expensive_boxed_3631_ = lean_unbox(v_expensive_3620_);
v_res_3632_ = l_Lean_Meta_Grind_Goal_checkInvariants(v_goal_3619_, v_expensive_boxed_3631_, v_a_3621_, v_a_3622_, v_a_3623_, v_a_3624_, v_a_3625_, v_a_3626_, v_a_3627_, v_a_3628_, v_a_3629_);
lean_dec(v_a_3629_);
lean_dec_ref(v_a_3628_);
lean_dec(v_a_3627_);
lean_dec_ref(v_a_3626_);
lean_dec(v_a_3625_);
lean_dec_ref(v_a_3624_);
lean_dec(v_a_3623_);
lean_dec_ref(v_a_3622_);
lean_dec(v_a_3621_);
return v_res_3632_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Canon(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Inv(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_Grind_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Canon(builtin);
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
lean_object* initialize_Lean_Meta_Sym_Canon(uint8_t builtin);
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
res = initialize_Lean_Meta_Sym_Canon(builtin);
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
