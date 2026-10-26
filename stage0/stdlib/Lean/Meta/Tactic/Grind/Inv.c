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
lean_object* l_Lean_Meta_isConstructorApp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Goal_getEqc(lean_object*, lean_object*, uint8_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isBVar(lean_object*);
lean_object* l_Lean_Meta_Grind_useFunCC___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_isMatchCond(lean_object*);
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
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondNestedChild___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondNestedChild___closed__0;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondNestedChild___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondNestedChild___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondNestedChild___closed__1_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondNestedChild_spec__0___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondNestedChild_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondNestedChild(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondNestedChild___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondNestedChild_spec__0___redArg___boxed(lean_object**);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondNestedChild_spec__1___redArg___boxed(lean_object**);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondNestedChild_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondNestedChild_spec__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondNestedChild_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondNestedChild_spec__1___boxed(lean_object**);
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
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__1(lean_object* v_msg_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_, lean_object* v___y_7_, lean_object* v___y_8_, lean_object* v___y_9_, lean_object* v___y_10_, lean_object* v___y_11_, lean_object* v___y_12_){
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
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__1___boxed(lean_object* v_msg_17_, lean_object* v___y_18_, lean_object* v___y_19_, lean_object* v___y_20_, lean_object* v___y_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_, lean_object* v___y_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__1(v_msg_17_, v___y_18_, v___y_19_, v___y_20_, v___y_21_, v___y_22_, v___y_23_, v___y_24_, v___y_25_, v___y_26_, v___y_27_);
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
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__4(lean_object* v_msg_30_, lean_object* v___y_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_, lean_object* v___y_36_, lean_object* v___y_37_, lean_object* v___y_38_, lean_object* v___y_39_, lean_object* v___y_40_){
_start:
{
lean_object* v___x_42_; lean_object* v___x_25809__overap_43_; lean_object* v___x_44_; 
v___x_42_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__1___closed__0, &l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__1___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__1___closed__0);
v___x_25809__overap_43_ = lean_panic_fn_borrowed(v___x_42_, v_msg_30_);
lean_inc(v___y_40_);
lean_inc_ref(v___y_39_);
lean_inc(v___y_38_);
lean_inc_ref(v___y_37_);
lean_inc(v___y_36_);
lean_inc_ref(v___y_35_);
lean_inc(v___y_34_);
lean_inc_ref(v___y_33_);
lean_inc(v___y_32_);
lean_inc(v___y_31_);
v___x_44_ = lean_apply_11(v___x_25809__overap_43_, v___y_31_, v___y_32_, v___y_33_, v___y_34_, v___y_35_, v___y_36_, v___y_37_, v___y_38_, v___y_39_, v___y_40_, lean_box(0));
return v___x_44_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__4___boxed(lean_object* v_msg_45_, lean_object* v___y_46_, lean_object* v___y_47_, lean_object* v___y_48_, lean_object* v___y_49_, lean_object* v___y_50_, lean_object* v___y_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_, lean_object* v___y_56_){
_start:
{
lean_object* v_res_57_; 
v_res_57_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__4(v_msg_45_, v___y_46_, v___y_47_, v___y_48_, v___y_49_, v___y_50_, v___y_51_, v___y_52_, v___y_53_, v___y_54_, v___y_55_);
lean_dec(v___y_55_);
lean_dec_ref(v___y_54_);
lean_dec(v___y_53_);
lean_dec_ref(v___y_52_);
lean_dec(v___y_51_);
lean_dec_ref(v___y_50_);
lean_dec(v___y_49_);
lean_dec_ref(v___y_48_);
lean_dec(v___y_47_);
lean_dec(v___y_46_);
return v_res_57_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__0___redArg(lean_object* v_a_58_, lean_object* v___y_59_){
_start:
{
lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_61_ = lean_st_ref_get(v___y_59_);
v___x_62_ = l_Lean_Meta_Grind_Goal_getTarget_x3f(v___x_61_, v_a_58_);
lean_dec(v___x_61_);
if (lean_obj_tag(v___x_62_) == 1)
{
lean_object* v_val_63_; 
lean_dec_ref(v_a_58_);
v_val_63_ = lean_ctor_get(v___x_62_, 0);
lean_inc(v_val_63_);
lean_dec_ref_known(v___x_62_, 1);
v_a_58_ = v_val_63_;
goto _start;
}
else
{
lean_object* v___x_65_; 
lean_dec(v___x_62_);
v___x_65_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_65_, 0, v_a_58_);
return v___x_65_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__0___redArg___boxed(lean_object* v_a_66_, lean_object* v___y_67_, lean_object* v___y_68_){
_start:
{
lean_object* v_res_69_; 
v_res_69_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__0___redArg(v_a_66_, v___y_67_);
lean_dec(v___y_67_);
return v_res_69_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; 
v___x_73_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__2));
v___x_74_ = lean_unsigned_to_nat(4u);
v___x_75_ = lean_unsigned_to_nat(41u);
v___x_76_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__1));
v___x_77_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__0));
v___x_78_ = l_mkPanicMessageWithDecl(v___x_77_, v___x_76_, v___x_75_, v___x_74_, v___x_73_);
return v___x_78_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__5(void){
_start:
{
lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; 
v___x_80_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__4));
v___x_81_ = lean_unsigned_to_nat(6u);
v___x_82_ = lean_unsigned_to_nat(33u);
v___x_83_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__1));
v___x_84_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__0));
v___x_85_ = l_mkPanicMessageWithDecl(v___x_84_, v___x_83_, v___x_82_, v___x_81_, v___x_80_);
return v___x_85_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0(lean_object* v_root_86_, lean_object* v_snd_87_, lean_object* v_curr_88_, lean_object* v___x_89_, lean_object* v_____r_90_, lean_object* v___y_91_, lean_object* v___y_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_, lean_object* v___y_99_, lean_object* v___y_100_){
_start:
{
lean_object* v___y_103_; lean_object* v___y_104_; lean_object* v___y_105_; lean_object* v___y_106_; lean_object* v___y_107_; lean_object* v___y_108_; lean_object* v___y_109_; lean_object* v___y_110_; lean_object* v___y_111_; lean_object* v___y_112_; uint8_t v_heqProofs_155_; 
v_heqProofs_155_ = lean_ctor_get_uint8(v_root_86_, sizeof(void*)*12 + 4);
if (v_heqProofs_155_ == 0)
{
lean_object* v___x_156_; 
lean_inc_ref(v_curr_88_);
lean_inc(v_snd_87_);
v___x_156_ = l_Lean_Meta_Grind_hasSameType(v_snd_87_, v_curr_88_, v___y_97_, v___y_98_, v___y_99_, v___y_100_);
if (lean_obj_tag(v___x_156_) == 0)
{
lean_object* v_a_157_; uint8_t v___x_158_; 
v_a_157_ = lean_ctor_get(v___x_156_, 0);
lean_inc(v_a_157_);
lean_dec_ref_known(v___x_156_, 1);
v___x_158_ = lean_unbox(v_a_157_);
lean_dec(v_a_157_);
if (v___x_158_ == 0)
{
lean_object* v___x_159_; lean_object* v___x_160_; 
lean_dec(v___x_89_);
lean_dec_ref(v_curr_88_);
lean_dec(v_snd_87_);
v___x_159_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__5, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__5_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__5);
v___x_160_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__1(v___x_159_, v___y_91_, v___y_92_, v___y_93_, v___y_94_, v___y_95_, v___y_96_, v___y_97_, v___y_98_, v___y_99_, v___y_100_);
return v___x_160_;
}
else
{
v___y_103_ = v___y_91_;
v___y_104_ = v___y_92_;
v___y_105_ = v___y_93_;
v___y_106_ = v___y_94_;
v___y_107_ = v___y_95_;
v___y_108_ = v___y_96_;
v___y_109_ = v___y_97_;
v___y_110_ = v___y_98_;
v___y_111_ = v___y_99_;
v___y_112_ = v___y_100_;
goto v___jp_102_;
}
}
else
{
lean_object* v_a_161_; lean_object* v___x_163_; uint8_t v_isShared_164_; uint8_t v_isSharedCheck_168_; 
lean_dec(v___x_89_);
lean_dec_ref(v_curr_88_);
lean_dec(v_snd_87_);
v_a_161_ = lean_ctor_get(v___x_156_, 0);
v_isSharedCheck_168_ = !lean_is_exclusive(v___x_156_);
if (v_isSharedCheck_168_ == 0)
{
v___x_163_ = v___x_156_;
v_isShared_164_ = v_isSharedCheck_168_;
goto v_resetjp_162_;
}
else
{
lean_inc(v_a_161_);
lean_dec(v___x_156_);
v___x_163_ = lean_box(0);
v_isShared_164_ = v_isSharedCheck_168_;
goto v_resetjp_162_;
}
v_resetjp_162_:
{
lean_object* v___x_166_; 
if (v_isShared_164_ == 0)
{
v___x_166_ = v___x_163_;
goto v_reusejp_165_;
}
else
{
lean_object* v_reuseFailAlloc_167_; 
v_reuseFailAlloc_167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_167_, 0, v_a_161_);
v___x_166_ = v_reuseFailAlloc_167_;
goto v_reusejp_165_;
}
v_reusejp_165_:
{
return v___x_166_;
}
}
}
}
else
{
v___y_103_ = v___y_91_;
v___y_104_ = v___y_92_;
v___y_105_ = v___y_93_;
v___y_106_ = v___y_94_;
v___y_107_ = v___y_95_;
v___y_108_ = v___y_96_;
v___y_109_ = v___y_97_;
v___y_110_ = v___y_98_;
v___y_111_ = v___y_99_;
v___y_112_ = v___y_100_;
goto v___jp_102_;
}
v___jp_102_:
{
lean_object* v___x_113_; 
lean_inc(v_snd_87_);
v___x_113_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__0___redArg(v_snd_87_, v___y_103_);
if (lean_obj_tag(v___x_113_) == 0)
{
lean_object* v_a_114_; size_t v___x_115_; size_t v___x_116_; uint8_t v___x_117_; 
v_a_114_ = lean_ctor_get(v___x_113_, 0);
lean_inc(v_a_114_);
lean_dec_ref_known(v___x_113_, 1);
v___x_115_ = lean_ptr_addr(v_a_114_);
lean_dec(v_a_114_);
v___x_116_ = lean_ptr_addr(v_curr_88_);
lean_dec_ref(v_curr_88_);
v___x_117_ = lean_usize_dec_eq(v___x_115_, v___x_116_);
if (v___x_117_ == 0)
{
lean_object* v___x_118_; lean_object* v___x_119_; 
lean_dec(v___x_89_);
lean_dec(v_snd_87_);
v___x_118_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__3, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__3_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__3);
v___x_119_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__1(v___x_118_, v___y_103_, v___y_104_, v___y_105_, v___y_106_, v___y_107_, v___y_108_, v___y_109_, v___y_110_, v___y_111_, v___y_112_);
return v___x_119_;
}
else
{
lean_object* v___x_120_; lean_object* v___x_121_; 
v___x_120_ = lean_st_ref_get(v___y_103_);
v___x_121_ = l_Lean_Meta_Grind_Goal_getNext(v___x_120_, v_snd_87_, v___y_109_, v___y_110_, v___y_111_, v___y_112_);
lean_dec(v___x_120_);
if (lean_obj_tag(v___x_121_) == 0)
{
lean_object* v_a_122_; lean_object* v___x_124_; uint8_t v_isShared_125_; uint8_t v_isSharedCheck_138_; 
v_a_122_ = lean_ctor_get(v___x_121_, 0);
v_isSharedCheck_138_ = !lean_is_exclusive(v___x_121_);
if (v_isSharedCheck_138_ == 0)
{
v___x_124_ = v___x_121_;
v_isShared_125_ = v_isSharedCheck_138_;
goto v_resetjp_123_;
}
else
{
lean_inc(v_a_122_);
lean_dec(v___x_121_);
v___x_124_ = lean_box(0);
v_isShared_125_ = v_isSharedCheck_138_;
goto v_resetjp_123_;
}
v_resetjp_123_:
{
size_t v___x_126_; uint8_t v___x_127_; 
v___x_126_ = lean_ptr_addr(v_a_122_);
v___x_127_ = lean_usize_dec_eq(v___x_116_, v___x_126_);
if (v___x_127_ == 0)
{
lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_131_; 
v___x_128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_128_, 0, v___x_89_);
lean_ctor_set(v___x_128_, 1, v_a_122_);
v___x_129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_129_, 0, v___x_128_);
if (v_isShared_125_ == 0)
{
lean_ctor_set(v___x_124_, 0, v___x_129_);
v___x_131_ = v___x_124_;
goto v_reusejp_130_;
}
else
{
lean_object* v_reuseFailAlloc_132_; 
v_reuseFailAlloc_132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_132_, 0, v___x_129_);
v___x_131_ = v_reuseFailAlloc_132_;
goto v_reusejp_130_;
}
v_reusejp_130_:
{
return v___x_131_;
}
}
else
{
lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_136_; 
v___x_133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_133_, 0, v___x_89_);
lean_ctor_set(v___x_133_, 1, v_a_122_);
v___x_134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_134_, 0, v___x_133_);
if (v_isShared_125_ == 0)
{
lean_ctor_set(v___x_124_, 0, v___x_134_);
v___x_136_ = v___x_124_;
goto v_reusejp_135_;
}
else
{
lean_object* v_reuseFailAlloc_137_; 
v_reuseFailAlloc_137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_137_, 0, v___x_134_);
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
lean_object* v_a_139_; lean_object* v___x_141_; uint8_t v_isShared_142_; uint8_t v_isSharedCheck_146_; 
lean_dec(v___x_89_);
v_a_139_ = lean_ctor_get(v___x_121_, 0);
v_isSharedCheck_146_ = !lean_is_exclusive(v___x_121_);
if (v_isSharedCheck_146_ == 0)
{
v___x_141_ = v___x_121_;
v_isShared_142_ = v_isSharedCheck_146_;
goto v_resetjp_140_;
}
else
{
lean_inc(v_a_139_);
lean_dec(v___x_121_);
v___x_141_ = lean_box(0);
v_isShared_142_ = v_isSharedCheck_146_;
goto v_resetjp_140_;
}
v_resetjp_140_:
{
lean_object* v___x_144_; 
if (v_isShared_142_ == 0)
{
v___x_144_ = v___x_141_;
goto v_reusejp_143_;
}
else
{
lean_object* v_reuseFailAlloc_145_; 
v_reuseFailAlloc_145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_145_, 0, v_a_139_);
v___x_144_ = v_reuseFailAlloc_145_;
goto v_reusejp_143_;
}
v_reusejp_143_:
{
return v___x_144_;
}
}
}
}
}
else
{
lean_object* v_a_147_; lean_object* v___x_149_; uint8_t v_isShared_150_; uint8_t v_isSharedCheck_154_; 
lean_dec(v___x_89_);
lean_dec_ref(v_curr_88_);
lean_dec(v_snd_87_);
v_a_147_ = lean_ctor_get(v___x_113_, 0);
v_isSharedCheck_154_ = !lean_is_exclusive(v___x_113_);
if (v_isSharedCheck_154_ == 0)
{
v___x_149_ = v___x_113_;
v_isShared_150_ = v_isSharedCheck_154_;
goto v_resetjp_148_;
}
else
{
lean_inc(v_a_147_);
lean_dec(v___x_113_);
v___x_149_ = lean_box(0);
v_isShared_150_ = v_isSharedCheck_154_;
goto v_resetjp_148_;
}
v_resetjp_148_:
{
lean_object* v___x_152_; 
if (v_isShared_150_ == 0)
{
v___x_152_ = v___x_149_;
goto v_reusejp_151_;
}
else
{
lean_object* v_reuseFailAlloc_153_; 
v_reuseFailAlloc_153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_153_, 0, v_a_147_);
v___x_152_ = v_reuseFailAlloc_153_;
goto v_reusejp_151_;
}
v_reusejp_151_:
{
return v___x_152_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___boxed(lean_object* v_root_169_, lean_object* v_snd_170_, lean_object* v_curr_171_, lean_object* v___x_172_, lean_object* v_____r_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_, lean_object* v___y_180_, lean_object* v___y_181_, lean_object* v___y_182_, lean_object* v___y_183_, lean_object* v___y_184_){
_start:
{
lean_object* v_res_185_; 
v_res_185_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0(v_root_169_, v_snd_170_, v_curr_171_, v___x_172_, v_____r_173_, v___y_174_, v___y_175_, v___y_176_, v___y_177_, v___y_178_, v___y_179_, v___y_180_, v___y_181_, v___y_182_, v___y_183_);
lean_dec(v___y_183_);
lean_dec_ref(v___y_182_);
lean_dec(v___y_181_);
lean_dec_ref(v___y_180_);
lean_dec(v___y_179_);
lean_dec_ref(v___y_178_);
lean_dec(v___y_177_);
lean_dec_ref(v___y_176_);
lean_dec(v___y_175_);
lean_dec(v___y_174_);
lean_dec_ref(v_root_169_);
return v_res_185_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2_spec__4___redArg(lean_object* v___x_186_, lean_object* v_keys_187_, lean_object* v_vals_188_, lean_object* v_i_189_, lean_object* v_k_190_){
_start:
{
lean_object* v___x_191_; uint8_t v___x_192_; 
v___x_191_ = lean_array_get_size(v_keys_187_);
v___x_192_ = lean_nat_dec_lt(v_i_189_, v___x_191_);
if (v___x_192_ == 0)
{
lean_object* v___x_193_; 
lean_dec_ref(v_k_190_);
lean_dec(v_i_189_);
v___x_193_ = lean_box(0);
return v___x_193_;
}
else
{
lean_object* v_k_x27_194_; uint8_t v___x_195_; 
v_k_x27_194_ = lean_array_fget_borrowed(v_keys_187_, v_i_189_);
lean_inc(v_k_x27_194_);
lean_inc_ref(v_k_190_);
v___x_195_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_isCongruent(v___x_186_, v_k_190_, v_k_x27_194_);
if (v___x_195_ == 0)
{
lean_object* v___x_196_; lean_object* v___x_197_; 
v___x_196_ = lean_unsigned_to_nat(1u);
v___x_197_ = lean_nat_add(v_i_189_, v___x_196_);
lean_dec(v_i_189_);
v_i_189_ = v___x_197_;
goto _start;
}
else
{
lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; 
lean_dec_ref(v_k_190_);
v___x_199_ = lean_array_fget_borrowed(v_vals_188_, v_i_189_);
lean_dec(v_i_189_);
lean_inc(v___x_199_);
lean_inc(v_k_x27_194_);
v___x_200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_200_, 0, v_k_x27_194_);
lean_ctor_set(v___x_200_, 1, v___x_199_);
v___x_201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_201_, 0, v___x_200_);
return v___x_201_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2_spec__4___redArg___boxed(lean_object* v___x_202_, lean_object* v_keys_203_, lean_object* v_vals_204_, lean_object* v_i_205_, lean_object* v_k_206_){
_start:
{
lean_object* v_res_207_; 
v_res_207_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2_spec__4___redArg(v___x_202_, v_keys_203_, v_vals_204_, v_i_205_, v_k_206_);
lean_dec_ref(v_vals_204_);
lean_dec_ref(v_keys_203_);
lean_dec_ref(v___x_202_);
return v_res_207_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2___redArg(lean_object* v___x_208_, lean_object* v_x_209_, size_t v_x_210_, lean_object* v_x_211_){
_start:
{
if (lean_obj_tag(v_x_209_) == 0)
{
lean_object* v_es_212_; lean_object* v___x_213_; size_t v___x_214_; size_t v___x_215_; lean_object* v_j_216_; lean_object* v___x_217_; 
v_es_212_ = lean_ctor_get(v_x_209_, 0);
lean_inc_ref(v_es_212_);
lean_dec_ref_known(v_x_209_, 1);
v___x_213_ = lean_box(2);
v___x_214_ = ((size_t)31ULL);
v___x_215_ = lean_usize_land(v_x_210_, v___x_214_);
v_j_216_ = lean_usize_to_nat(v___x_215_);
v___x_217_ = lean_array_get(v___x_213_, v_es_212_, v_j_216_);
lean_dec(v_j_216_);
lean_dec_ref(v_es_212_);
switch(lean_obj_tag(v___x_217_))
{
case 0:
{
lean_object* v_key_218_; lean_object* v_val_219_; uint8_t v___x_220_; 
v_key_218_ = lean_ctor_get(v___x_217_, 0);
lean_inc_n(v_key_218_, 2);
v_val_219_ = lean_ctor_get(v___x_217_, 1);
lean_inc(v_val_219_);
lean_dec_ref_known(v___x_217_, 2);
v___x_220_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_isCongruent(v___x_208_, v_x_211_, v_key_218_);
if (v___x_220_ == 0)
{
lean_object* v___x_221_; 
lean_dec(v_val_219_);
lean_dec(v_key_218_);
v___x_221_ = lean_box(0);
return v___x_221_;
}
else
{
lean_object* v___x_222_; lean_object* v___x_223_; 
v___x_222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_222_, 0, v_key_218_);
lean_ctor_set(v___x_222_, 1, v_val_219_);
v___x_223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_223_, 0, v___x_222_);
return v___x_223_;
}
}
case 1:
{
lean_object* v_node_224_; size_t v___x_225_; size_t v___x_226_; 
v_node_224_ = lean_ctor_get(v___x_217_, 0);
lean_inc(v_node_224_);
lean_dec_ref_known(v___x_217_, 1);
v___x_225_ = ((size_t)5ULL);
v___x_226_ = lean_usize_shift_right(v_x_210_, v___x_225_);
v_x_209_ = v_node_224_;
v_x_210_ = v___x_226_;
goto _start;
}
default: 
{
lean_object* v___x_228_; 
lean_dec_ref(v_x_211_);
v___x_228_ = lean_box(0);
return v___x_228_;
}
}
}
else
{
lean_object* v_ks_229_; lean_object* v_vs_230_; lean_object* v___x_231_; lean_object* v___x_232_; 
v_ks_229_ = lean_ctor_get(v_x_209_, 0);
lean_inc_ref(v_ks_229_);
v_vs_230_ = lean_ctor_get(v_x_209_, 1);
lean_inc_ref(v_vs_230_);
lean_dec_ref_known(v_x_209_, 2);
v___x_231_ = lean_unsigned_to_nat(0u);
v___x_232_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2_spec__4___redArg(v___x_208_, v_ks_229_, v_vs_230_, v___x_231_, v_x_211_);
lean_dec_ref(v_vs_230_);
lean_dec_ref(v_ks_229_);
return v___x_232_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2___redArg___boxed(lean_object* v___x_233_, lean_object* v_x_234_, lean_object* v_x_235_, lean_object* v_x_236_){
_start:
{
size_t v_x_26629__boxed_237_; lean_object* v_res_238_; 
v_x_26629__boxed_237_ = lean_unbox_usize(v_x_235_);
lean_dec(v_x_235_);
v_res_238_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2___redArg(v___x_233_, v_x_234_, v_x_26629__boxed_237_, v_x_236_);
lean_dec_ref(v___x_233_);
return v_res_238_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2___redArg(lean_object* v___x_239_, lean_object* v_x_240_, lean_object* v_x_241_){
_start:
{
uint64_t v___x_242_; size_t v___x_243_; lean_object* v___x_244_; 
v___x_242_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_congrHash(v___x_239_, v_x_241_);
v___x_243_ = lean_uint64_to_usize(v___x_242_);
lean_inc_ref(v_x_240_);
v___x_244_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2___redArg(v___x_239_, v_x_240_, v___x_243_, v_x_241_);
return v___x_244_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2___redArg___boxed(lean_object* v___x_245_, lean_object* v_x_246_, lean_object* v_x_247_){
_start:
{
lean_object* v_res_248_; 
v_res_248_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2___redArg(v___x_245_, v_x_246_, v_x_247_);
lean_dec_ref(v_x_246_);
lean_dec_ref(v___x_245_);
return v_res_248_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; 
v___x_250_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___closed__0));
v___x_251_ = lean_unsigned_to_nat(4u);
v___x_252_ = lean_unsigned_to_nat(23u);
v___x_253_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__1));
v___x_254_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__0));
v___x_255_ = l_mkPanicMessageWithDecl(v___x_254_, v___x_253_, v___x_252_, v___x_251_, v___x_250_);
return v___x_255_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; 
v___x_257_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___closed__2));
v___x_258_ = lean_unsigned_to_nat(8u);
v___x_259_ = lean_unsigned_to_nat(30u);
v___x_260_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__1));
v___x_261_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__0));
v___x_262_ = l_mkPanicMessageWithDecl(v___x_261_, v___x_260_, v___x_259_, v___x_258_, v___x_257_);
return v___x_262_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___closed__5(void){
_start:
{
lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; 
v___x_264_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___closed__4));
v___x_265_ = lean_unsigned_to_nat(10u);
v___x_266_ = lean_unsigned_to_nat(28u);
v___x_267_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__1));
v___x_268_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__0));
v___x_269_ = l_mkPanicMessageWithDecl(v___x_268_, v___x_267_, v___x_266_, v___x_265_, v___x_264_);
return v___x_269_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg(lean_object* v_curr_270_, lean_object* v_root_271_, lean_object* v_a_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_){
_start:
{
lean_object* v___y_285_; lean_object* v_fst_305_; lean_object* v_snd_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; 
v_fst_305_ = lean_ctor_get(v_a_272_, 0);
lean_inc(v_fst_305_);
v_snd_306_ = lean_ctor_get(v_a_272_, 1);
lean_inc_n(v_snd_306_, 2);
lean_dec_ref(v_a_272_);
v___x_307_ = lean_unsigned_to_nat(1u);
v___x_308_ = lean_nat_add(v_fst_305_, v___x_307_);
lean_dec(v_fst_305_);
v___x_309_ = lean_st_ref_get(v___y_273_);
v___x_310_ = l_Lean_Meta_Grind_Goal_getRoot(v___x_309_, v_snd_306_, v___y_279_, v___y_280_, v___y_281_, v___y_282_);
lean_dec(v___x_309_);
if (lean_obj_tag(v___x_310_) == 0)
{
lean_object* v_a_311_; size_t v___x_312_; size_t v___x_313_; uint8_t v___x_314_; 
v_a_311_ = lean_ctor_get(v___x_310_, 0);
lean_inc(v_a_311_);
lean_dec_ref_known(v___x_310_, 1);
v___x_312_ = lean_ptr_addr(v_a_311_);
lean_dec(v_a_311_);
v___x_313_ = lean_ptr_addr(v_curr_270_);
v___x_314_ = lean_usize_dec_eq(v___x_312_, v___x_313_);
if (v___x_314_ == 0)
{
lean_object* v___x_315_; lean_object* v___x_316_; 
lean_dec(v___x_308_);
lean_dec(v_snd_306_);
v___x_315_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___closed__1, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___closed__1_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___closed__1);
v___x_316_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__1(v___x_315_, v___y_273_, v___y_274_, v___y_275_, v___y_276_, v___y_277_, v___y_278_, v___y_279_, v___y_280_, v___y_281_, v___y_282_);
v___y_285_ = v___x_316_;
goto v___jp_284_;
}
else
{
uint8_t v___x_317_; 
v___x_317_ = l_Lean_Expr_isApp(v_snd_306_);
if (v___x_317_ == 0)
{
lean_object* v___x_318_; lean_object* v___x_319_; 
v___x_318_ = lean_box(0);
lean_inc_ref(v_curr_270_);
v___x_319_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0(v_root_271_, v_snd_306_, v_curr_270_, v___x_308_, v___x_318_, v___y_273_, v___y_274_, v___y_275_, v___y_276_, v___y_277_, v___y_278_, v___y_279_, v___y_280_, v___y_281_, v___y_282_);
v___y_285_ = v___x_319_;
goto v___jp_284_;
}
else
{
lean_object* v___x_320_; lean_object* v_toGoalState_321_; lean_object* v_enodeMap_322_; lean_object* v_congrTable_323_; lean_object* v___x_324_; 
v___x_320_ = lean_st_ref_get(v___y_273_);
v_toGoalState_321_ = lean_ctor_get(v___x_320_, 0);
lean_inc_ref(v_toGoalState_321_);
lean_dec(v___x_320_);
v_enodeMap_322_ = lean_ctor_get(v_toGoalState_321_, 1);
lean_inc_ref(v_enodeMap_322_);
v_congrTable_323_ = lean_ctor_get(v_toGoalState_321_, 4);
lean_inc_ref(v_congrTable_323_);
lean_dec_ref(v_toGoalState_321_);
lean_inc(v_snd_306_);
v___x_324_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2___redArg(v_enodeMap_322_, v_congrTable_323_, v_snd_306_);
lean_dec_ref(v_congrTable_323_);
lean_dec_ref(v_enodeMap_322_);
if (lean_obj_tag(v___x_324_) == 0)
{
lean_object* v___x_325_; 
lean_inc(v_snd_306_);
v___x_325_ = l_Lean_Meta_Grind_isCongrRoot___redArg(v_snd_306_, v___y_273_, v___y_279_, v___y_280_, v___y_281_, v___y_282_);
if (lean_obj_tag(v___x_325_) == 0)
{
lean_object* v_a_326_; uint8_t v___x_327_; 
v_a_326_ = lean_ctor_get(v___x_325_, 0);
lean_inc(v_a_326_);
lean_dec_ref_known(v___x_325_, 1);
v___x_327_ = lean_unbox(v_a_326_);
lean_dec(v_a_326_);
if (v___x_327_ == 0)
{
lean_object* v___x_328_; lean_object* v___x_329_; 
lean_dec(v___x_308_);
lean_dec(v_snd_306_);
v___x_328_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___closed__3, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___closed__3_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___closed__3);
v___x_329_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__1(v___x_328_, v___y_273_, v___y_274_, v___y_275_, v___y_276_, v___y_277_, v___y_278_, v___y_279_, v___y_280_, v___y_281_, v___y_282_);
v___y_285_ = v___x_329_;
goto v___jp_284_;
}
else
{
lean_object* v___x_330_; lean_object* v___x_331_; 
v___x_330_ = lean_box(0);
lean_inc_ref(v_curr_270_);
v___x_331_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0(v_root_271_, v_snd_306_, v_curr_270_, v___x_308_, v___x_330_, v___y_273_, v___y_274_, v___y_275_, v___y_276_, v___y_277_, v___y_278_, v___y_279_, v___y_280_, v___y_281_, v___y_282_);
v___y_285_ = v___x_331_;
goto v___jp_284_;
}
}
else
{
lean_object* v_a_332_; lean_object* v___x_334_; uint8_t v_isShared_335_; uint8_t v_isSharedCheck_339_; 
lean_dec(v___x_308_);
lean_dec(v_snd_306_);
lean_dec_ref(v_curr_270_);
v_a_332_ = lean_ctor_get(v___x_325_, 0);
v_isSharedCheck_339_ = !lean_is_exclusive(v___x_325_);
if (v_isSharedCheck_339_ == 0)
{
v___x_334_ = v___x_325_;
v_isShared_335_ = v_isSharedCheck_339_;
goto v_resetjp_333_;
}
else
{
lean_inc(v_a_332_);
lean_dec(v___x_325_);
v___x_334_ = lean_box(0);
v_isShared_335_ = v_isSharedCheck_339_;
goto v_resetjp_333_;
}
v_resetjp_333_:
{
lean_object* v___x_337_; 
if (v_isShared_335_ == 0)
{
v___x_337_ = v___x_334_;
goto v_reusejp_336_;
}
else
{
lean_object* v_reuseFailAlloc_338_; 
v_reuseFailAlloc_338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_338_, 0, v_a_332_);
v___x_337_ = v_reuseFailAlloc_338_;
goto v_reusejp_336_;
}
v_reusejp_336_:
{
return v___x_337_;
}
}
}
}
else
{
lean_object* v_val_340_; lean_object* v_fst_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; 
v_val_340_ = lean_ctor_get(v___x_324_, 0);
lean_inc(v_val_340_);
lean_dec_ref_known(v___x_324_, 1);
v_fst_341_ = lean_ctor_get(v_val_340_, 0);
lean_inc(v_fst_341_);
lean_dec(v_val_340_);
v___x_342_ = l_Lean_Expr_getAppFn(v_fst_341_);
v___x_343_ = l_Lean_Expr_getAppFn(v_snd_306_);
v___x_344_ = l_Lean_Meta_Grind_hasSameType(v___x_342_, v___x_343_, v___y_279_, v___y_280_, v___y_281_, v___y_282_);
if (lean_obj_tag(v___x_344_) == 0)
{
lean_object* v_a_345_; uint8_t v___x_346_; 
v_a_345_ = lean_ctor_get(v___x_344_, 0);
lean_inc(v_a_345_);
lean_dec_ref_known(v___x_344_, 1);
v___x_346_ = lean_unbox(v_a_345_);
lean_dec(v_a_345_);
if (v___x_346_ == 0)
{
lean_object* v___x_347_; lean_object* v___x_348_; 
lean_dec(v_fst_341_);
v___x_347_ = lean_box(0);
lean_inc_ref(v_curr_270_);
v___x_348_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0(v_root_271_, v_snd_306_, v_curr_270_, v___x_308_, v___x_347_, v___y_273_, v___y_274_, v___y_275_, v___y_276_, v___y_277_, v___y_278_, v___y_279_, v___y_280_, v___y_281_, v___y_282_);
v___y_285_ = v___x_348_;
goto v___jp_284_;
}
else
{
lean_object* v___x_349_; 
lean_inc(v_snd_306_);
v___x_349_ = l_Lean_Meta_Grind_getCongrRoot___redArg(v_snd_306_, v___y_273_, v___y_279_, v___y_280_, v___y_281_, v___y_282_);
if (lean_obj_tag(v___x_349_) == 0)
{
lean_object* v_a_350_; size_t v___x_351_; size_t v___x_352_; uint8_t v___x_353_; 
v_a_350_ = lean_ctor_get(v___x_349_, 0);
lean_inc(v_a_350_);
lean_dec_ref_known(v___x_349_, 1);
v___x_351_ = lean_ptr_addr(v_fst_341_);
lean_dec(v_fst_341_);
v___x_352_ = lean_ptr_addr(v_a_350_);
lean_dec(v_a_350_);
v___x_353_ = lean_usize_dec_eq(v___x_351_, v___x_352_);
if (v___x_353_ == 0)
{
lean_object* v___x_354_; lean_object* v___x_355_; 
lean_dec(v___x_308_);
lean_dec(v_snd_306_);
v___x_354_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___closed__5, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___closed__5_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___closed__5);
v___x_355_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__1(v___x_354_, v___y_273_, v___y_274_, v___y_275_, v___y_276_, v___y_277_, v___y_278_, v___y_279_, v___y_280_, v___y_281_, v___y_282_);
v___y_285_ = v___x_355_;
goto v___jp_284_;
}
else
{
lean_object* v___x_356_; lean_object* v___x_357_; 
v___x_356_ = lean_box(0);
lean_inc_ref(v_curr_270_);
v___x_357_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0(v_root_271_, v_snd_306_, v_curr_270_, v___x_308_, v___x_356_, v___y_273_, v___y_274_, v___y_275_, v___y_276_, v___y_277_, v___y_278_, v___y_279_, v___y_280_, v___y_281_, v___y_282_);
v___y_285_ = v___x_357_;
goto v___jp_284_;
}
}
else
{
lean_object* v_a_358_; lean_object* v___x_360_; uint8_t v_isShared_361_; uint8_t v_isSharedCheck_365_; 
lean_dec(v_fst_341_);
lean_dec(v___x_308_);
lean_dec(v_snd_306_);
lean_dec_ref(v_curr_270_);
v_a_358_ = lean_ctor_get(v___x_349_, 0);
v_isSharedCheck_365_ = !lean_is_exclusive(v___x_349_);
if (v_isSharedCheck_365_ == 0)
{
v___x_360_ = v___x_349_;
v_isShared_361_ = v_isSharedCheck_365_;
goto v_resetjp_359_;
}
else
{
lean_inc(v_a_358_);
lean_dec(v___x_349_);
v___x_360_ = lean_box(0);
v_isShared_361_ = v_isSharedCheck_365_;
goto v_resetjp_359_;
}
v_resetjp_359_:
{
lean_object* v___x_363_; 
if (v_isShared_361_ == 0)
{
v___x_363_ = v___x_360_;
goto v_reusejp_362_;
}
else
{
lean_object* v_reuseFailAlloc_364_; 
v_reuseFailAlloc_364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_364_, 0, v_a_358_);
v___x_363_ = v_reuseFailAlloc_364_;
goto v_reusejp_362_;
}
v_reusejp_362_:
{
return v___x_363_;
}
}
}
}
}
else
{
lean_object* v_a_366_; lean_object* v___x_368_; uint8_t v_isShared_369_; uint8_t v_isSharedCheck_373_; 
lean_dec(v_fst_341_);
lean_dec(v___x_308_);
lean_dec(v_snd_306_);
lean_dec_ref(v_curr_270_);
v_a_366_ = lean_ctor_get(v___x_344_, 0);
v_isSharedCheck_373_ = !lean_is_exclusive(v___x_344_);
if (v_isSharedCheck_373_ == 0)
{
v___x_368_ = v___x_344_;
v_isShared_369_ = v_isSharedCheck_373_;
goto v_resetjp_367_;
}
else
{
lean_inc(v_a_366_);
lean_dec(v___x_344_);
v___x_368_ = lean_box(0);
v_isShared_369_ = v_isSharedCheck_373_;
goto v_resetjp_367_;
}
v_resetjp_367_:
{
lean_object* v___x_371_; 
if (v_isShared_369_ == 0)
{
v___x_371_ = v___x_368_;
goto v_reusejp_370_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v_a_366_);
v___x_371_ = v_reuseFailAlloc_372_;
goto v_reusejp_370_;
}
v_reusejp_370_:
{
return v___x_371_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_374_; lean_object* v___x_376_; uint8_t v_isShared_377_; uint8_t v_isSharedCheck_381_; 
lean_dec(v___x_308_);
lean_dec(v_snd_306_);
lean_dec_ref(v_curr_270_);
v_a_374_ = lean_ctor_get(v___x_310_, 0);
v_isSharedCheck_381_ = !lean_is_exclusive(v___x_310_);
if (v_isSharedCheck_381_ == 0)
{
v___x_376_ = v___x_310_;
v_isShared_377_ = v_isSharedCheck_381_;
goto v_resetjp_375_;
}
else
{
lean_inc(v_a_374_);
lean_dec(v___x_310_);
v___x_376_ = lean_box(0);
v_isShared_377_ = v_isSharedCheck_381_;
goto v_resetjp_375_;
}
v_resetjp_375_:
{
lean_object* v___x_379_; 
if (v_isShared_377_ == 0)
{
v___x_379_ = v___x_376_;
goto v_reusejp_378_;
}
else
{
lean_object* v_reuseFailAlloc_380_; 
v_reuseFailAlloc_380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_380_, 0, v_a_374_);
v___x_379_ = v_reuseFailAlloc_380_;
goto v_reusejp_378_;
}
v_reusejp_378_:
{
return v___x_379_;
}
}
}
v___jp_284_:
{
if (lean_obj_tag(v___y_285_) == 0)
{
lean_object* v_a_286_; lean_object* v___x_288_; uint8_t v_isShared_289_; uint8_t v_isSharedCheck_296_; 
v_a_286_ = lean_ctor_get(v___y_285_, 0);
v_isSharedCheck_296_ = !lean_is_exclusive(v___y_285_);
if (v_isSharedCheck_296_ == 0)
{
v___x_288_ = v___y_285_;
v_isShared_289_ = v_isSharedCheck_296_;
goto v_resetjp_287_;
}
else
{
lean_inc(v_a_286_);
lean_dec(v___y_285_);
v___x_288_ = lean_box(0);
v_isShared_289_ = v_isSharedCheck_296_;
goto v_resetjp_287_;
}
v_resetjp_287_:
{
if (lean_obj_tag(v_a_286_) == 0)
{
lean_object* v_a_290_; lean_object* v___x_292_; 
lean_dec_ref(v_curr_270_);
v_a_290_ = lean_ctor_get(v_a_286_, 0);
lean_inc(v_a_290_);
lean_dec_ref_known(v_a_286_, 1);
if (v_isShared_289_ == 0)
{
lean_ctor_set(v___x_288_, 0, v_a_290_);
v___x_292_ = v___x_288_;
goto v_reusejp_291_;
}
else
{
lean_object* v_reuseFailAlloc_293_; 
v_reuseFailAlloc_293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_293_, 0, v_a_290_);
v___x_292_ = v_reuseFailAlloc_293_;
goto v_reusejp_291_;
}
v_reusejp_291_:
{
return v___x_292_;
}
}
else
{
lean_object* v_a_294_; 
lean_del_object(v___x_288_);
v_a_294_ = lean_ctor_get(v_a_286_, 0);
lean_inc(v_a_294_);
lean_dec_ref_known(v_a_286_, 1);
v_a_272_ = v_a_294_;
goto _start;
}
}
}
else
{
lean_object* v_a_297_; lean_object* v___x_299_; uint8_t v_isShared_300_; uint8_t v_isSharedCheck_304_; 
lean_dec_ref(v_curr_270_);
v_a_297_ = lean_ctor_get(v___y_285_, 0);
v_isSharedCheck_304_ = !lean_is_exclusive(v___y_285_);
if (v_isSharedCheck_304_ == 0)
{
v___x_299_ = v___y_285_;
v_isShared_300_ = v_isSharedCheck_304_;
goto v_resetjp_298_;
}
else
{
lean_inc(v_a_297_);
lean_dec(v___y_285_);
v___x_299_ = lean_box(0);
v_isShared_300_ = v_isSharedCheck_304_;
goto v_resetjp_298_;
}
v_resetjp_298_:
{
lean_object* v___x_302_; 
if (v_isShared_300_ == 0)
{
v___x_302_ = v___x_299_;
goto v_reusejp_301_;
}
else
{
lean_object* v_reuseFailAlloc_303_; 
v_reuseFailAlloc_303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_303_, 0, v_a_297_);
v___x_302_ = v_reuseFailAlloc_303_;
goto v_reusejp_301_;
}
v_reusejp_301_:
{
return v___x_302_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___boxed(lean_object* v_curr_382_, lean_object* v_root_383_, lean_object* v_a_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_){
_start:
{
lean_object* v_res_396_; 
v_res_396_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg(v_curr_382_, v_root_383_, v_a_384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_, v___y_389_, v___y_390_, v___y_391_, v___y_392_, v___y_393_, v___y_394_);
lean_dec(v___y_394_);
lean_dec_ref(v___y_393_);
lean_dec(v___y_392_);
lean_dec_ref(v___y_391_);
lean_dec(v___y_390_);
lean_dec_ref(v___y_389_);
lean_dec(v___y_388_);
lean_dec_ref(v___y_387_);
lean_dec(v___y_386_);
lean_dec(v___y_385_);
lean_dec_ref(v_root_383_);
return v_res_396_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc___closed__1(void){
_start:
{
lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; 
v___x_398_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc___closed__0));
v___x_399_ = lean_unsigned_to_nat(2u);
v___x_400_ = lean_unsigned_to_nat(47u);
v___x_401_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__1));
v___x_402_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__0));
v___x_403_ = l_mkPanicMessageWithDecl(v___x_402_, v___x_401_, v___x_400_, v___x_399_, v___x_398_);
return v___x_403_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc(lean_object* v_root_404_, lean_object* v_a_405_, lean_object* v_a_406_, lean_object* v_a_407_, lean_object* v_a_408_, lean_object* v_a_409_, lean_object* v_a_410_, lean_object* v_a_411_, lean_object* v_a_412_, lean_object* v_a_413_, lean_object* v_a_414_){
_start:
{
lean_object* v_self_416_; lean_object* v_size_417_; lean_object* v_size_418_; lean_object* v___x_419_; lean_object* v___x_420_; 
v_self_416_ = lean_ctor_get(v_root_404_, 0);
lean_inc_ref_n(v_self_416_, 2);
v_size_417_ = lean_ctor_get(v_root_404_, 6);
lean_inc(v_size_417_);
v_size_418_ = lean_unsigned_to_nat(0u);
v___x_419_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_419_, 0, v_size_418_);
lean_ctor_set(v___x_419_, 1, v_self_416_);
v___x_420_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg(v_self_416_, v_root_404_, v___x_419_, v_a_405_, v_a_406_, v_a_407_, v_a_408_, v_a_409_, v_a_410_, v_a_411_, v_a_412_, v_a_413_, v_a_414_);
lean_dec_ref(v_root_404_);
if (lean_obj_tag(v___x_420_) == 0)
{
lean_object* v_a_421_; lean_object* v___x_423_; uint8_t v_isShared_424_; uint8_t v_isSharedCheck_433_; 
v_a_421_ = lean_ctor_get(v___x_420_, 0);
v_isSharedCheck_433_ = !lean_is_exclusive(v___x_420_);
if (v_isSharedCheck_433_ == 0)
{
v___x_423_ = v___x_420_;
v_isShared_424_ = v_isSharedCheck_433_;
goto v_resetjp_422_;
}
else
{
lean_inc(v_a_421_);
lean_dec(v___x_420_);
v___x_423_ = lean_box(0);
v_isShared_424_ = v_isSharedCheck_433_;
goto v_resetjp_422_;
}
v_resetjp_422_:
{
lean_object* v_fst_425_; uint8_t v___x_426_; 
v_fst_425_ = lean_ctor_get(v_a_421_, 0);
lean_inc(v_fst_425_);
lean_dec(v_a_421_);
v___x_426_ = lean_nat_dec_eq(v_size_417_, v_fst_425_);
lean_dec(v_fst_425_);
lean_dec(v_size_417_);
if (v___x_426_ == 0)
{
lean_object* v___x_427_; lean_object* v___x_428_; 
lean_del_object(v___x_423_);
v___x_427_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc___closed__1, &l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc___closed__1);
v___x_428_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__4(v___x_427_, v_a_405_, v_a_406_, v_a_407_, v_a_408_, v_a_409_, v_a_410_, v_a_411_, v_a_412_, v_a_413_, v_a_414_);
return v___x_428_;
}
else
{
lean_object* v___x_429_; lean_object* v___x_431_; 
v___x_429_ = lean_box(0);
if (v_isShared_424_ == 0)
{
lean_ctor_set(v___x_423_, 0, v___x_429_);
v___x_431_ = v___x_423_;
goto v_reusejp_430_;
}
else
{
lean_object* v_reuseFailAlloc_432_; 
v_reuseFailAlloc_432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_432_, 0, v___x_429_);
v___x_431_ = v_reuseFailAlloc_432_;
goto v_reusejp_430_;
}
v_reusejp_430_:
{
return v___x_431_;
}
}
}
}
else
{
lean_object* v_a_434_; lean_object* v___x_436_; uint8_t v_isShared_437_; uint8_t v_isSharedCheck_441_; 
lean_dec(v_size_417_);
v_a_434_ = lean_ctor_get(v___x_420_, 0);
v_isSharedCheck_441_ = !lean_is_exclusive(v___x_420_);
if (v_isSharedCheck_441_ == 0)
{
v___x_436_ = v___x_420_;
v_isShared_437_ = v_isSharedCheck_441_;
goto v_resetjp_435_;
}
else
{
lean_inc(v_a_434_);
lean_dec(v___x_420_);
v___x_436_ = lean_box(0);
v_isShared_437_ = v_isSharedCheck_441_;
goto v_resetjp_435_;
}
v_resetjp_435_:
{
lean_object* v___x_439_; 
if (v_isShared_437_ == 0)
{
v___x_439_ = v___x_436_;
goto v_reusejp_438_;
}
else
{
lean_object* v_reuseFailAlloc_440_; 
v_reuseFailAlloc_440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_440_, 0, v_a_434_);
v___x_439_ = v_reuseFailAlloc_440_;
goto v_reusejp_438_;
}
v_reusejp_438_:
{
return v___x_439_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc___boxed(lean_object* v_root_442_, lean_object* v_a_443_, lean_object* v_a_444_, lean_object* v_a_445_, lean_object* v_a_446_, lean_object* v_a_447_, lean_object* v_a_448_, lean_object* v_a_449_, lean_object* v_a_450_, lean_object* v_a_451_, lean_object* v_a_452_, lean_object* v_a_453_){
_start:
{
lean_object* v_res_454_; 
v_res_454_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc(v_root_442_, v_a_443_, v_a_444_, v_a_445_, v_a_446_, v_a_447_, v_a_448_, v_a_449_, v_a_450_, v_a_451_, v_a_452_);
lean_dec(v_a_452_);
lean_dec_ref(v_a_451_);
lean_dec(v_a_450_);
lean_dec_ref(v_a_449_);
lean_dec(v_a_448_);
lean_dec_ref(v_a_447_);
lean_dec(v_a_446_);
lean_dec_ref(v_a_445_);
lean_dec(v_a_444_);
lean_dec(v_a_443_);
return v_res_454_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__0(lean_object* v_inst_455_, lean_object* v_a_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_){
_start:
{
lean_object* v___x_468_; 
v___x_468_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__0___redArg(v_a_456_, v___y_457_);
return v___x_468_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__0___boxed(lean_object* v_inst_469_, lean_object* v_a_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_){
_start:
{
lean_object* v_res_482_; 
v_res_482_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__0(v_inst_469_, v_a_470_, v___y_471_, v___y_472_, v___y_473_, v___y_474_, v___y_475_, v___y_476_, v___y_477_, v___y_478_, v___y_479_, v___y_480_);
lean_dec(v___y_480_);
lean_dec_ref(v___y_479_);
lean_dec(v___y_478_);
lean_dec_ref(v___y_477_);
lean_dec(v___y_476_);
lean_dec_ref(v___y_475_);
lean_dec(v___y_474_);
lean_dec_ref(v___y_473_);
lean_dec(v___y_472_);
lean_dec(v___y_471_);
return v_res_482_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2(lean_object* v___x_483_, lean_object* v_00_u03b2_484_, lean_object* v_x_485_, lean_object* v_x_486_){
_start:
{
lean_object* v___x_487_; 
v___x_487_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2___redArg(v___x_483_, v_x_485_, v_x_486_);
return v___x_487_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2___boxed(lean_object* v___x_488_, lean_object* v_00_u03b2_489_, lean_object* v_x_490_, lean_object* v_x_491_){
_start:
{
lean_object* v_res_492_; 
v_res_492_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2(v___x_488_, v_00_u03b2_489_, v_x_490_, v_x_491_);
lean_dec_ref(v_x_490_);
lean_dec_ref(v___x_488_);
return v_res_492_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3(lean_object* v_curr_493_, lean_object* v_root_494_, lean_object* v_inst_495_, lean_object* v_a_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_){
_start:
{
lean_object* v___x_508_; 
v___x_508_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg(v_curr_493_, v_root_494_, v_a_496_, v___y_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_, v___y_504_, v___y_505_, v___y_506_);
return v___x_508_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___boxed(lean_object* v_curr_509_, lean_object* v_root_510_, lean_object* v_inst_511_, lean_object* v_a_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_){
_start:
{
lean_object* v_res_524_; 
v_res_524_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3(v_curr_509_, v_root_510_, v_inst_511_, v_a_512_, v___y_513_, v___y_514_, v___y_515_, v___y_516_, v___y_517_, v___y_518_, v___y_519_, v___y_520_, v___y_521_, v___y_522_);
lean_dec(v___y_522_);
lean_dec_ref(v___y_521_);
lean_dec(v___y_520_);
lean_dec_ref(v___y_519_);
lean_dec(v___y_518_);
lean_dec_ref(v___y_517_);
lean_dec(v___y_516_);
lean_dec_ref(v___y_515_);
lean_dec(v___y_514_);
lean_dec(v___y_513_);
lean_dec_ref(v_root_510_);
return v_res_524_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2(lean_object* v___x_525_, lean_object* v_00_u03b2_526_, lean_object* v_x_527_, size_t v_x_528_, lean_object* v_x_529_){
_start:
{
lean_object* v___x_530_; 
lean_inc_ref(v_x_527_);
v___x_530_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2___redArg(v___x_525_, v_x_527_, v_x_528_, v_x_529_);
return v___x_530_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2___boxed(lean_object* v___x_531_, lean_object* v_00_u03b2_532_, lean_object* v_x_533_, lean_object* v_x_534_, lean_object* v_x_535_){
_start:
{
size_t v_x_27142__boxed_536_; lean_object* v_res_537_; 
v_x_27142__boxed_536_ = lean_unbox_usize(v_x_534_);
lean_dec(v_x_534_);
v_res_537_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2(v___x_531_, v_00_u03b2_532_, v_x_533_, v_x_27142__boxed_536_, v_x_535_);
lean_dec_ref(v_x_533_);
lean_dec_ref(v___x_531_);
return v_res_537_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2_spec__4(lean_object* v___x_538_, lean_object* v_00_u03b2_539_, lean_object* v_keys_540_, lean_object* v_vals_541_, lean_object* v_heq_542_, lean_object* v_i_543_, lean_object* v_k_544_){
_start:
{
lean_object* v___x_545_; 
v___x_545_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2_spec__4___redArg(v___x_538_, v_keys_540_, v_vals_541_, v_i_543_, v_k_544_);
return v___x_545_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2_spec__4___boxed(lean_object* v___x_546_, lean_object* v_00_u03b2_547_, lean_object* v_keys_548_, lean_object* v_vals_549_, lean_object* v_heq_550_, lean_object* v_i_551_, lean_object* v_k_552_){
_start:
{
lean_object* v_res_553_; 
v_res_553_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2_spec__4(v___x_546_, v_00_u03b2_547_, v_keys_548_, v_vals_549_, v_heq_550_, v_i_551_, v_k_552_);
lean_dec_ref(v_vals_549_);
lean_dec_ref(v_keys_548_);
lean_dec_ref(v___x_546_);
return v_res_553_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkChild___redArg(lean_object* v_e_554_, lean_object* v_child_555_, lean_object* v_a_556_){
_start:
{
lean_object* v___x_558_; lean_object* v___x_559_; 
v___x_558_ = lean_st_ref_get(v_a_556_);
v___x_559_ = l_Lean_Meta_Grind_Goal_getRoot_x3f(v___x_558_, v_child_555_);
lean_dec(v___x_558_);
if (lean_obj_tag(v___x_559_) == 1)
{
lean_object* v_val_560_; lean_object* v___x_562_; uint8_t v_isShared_563_; uint8_t v_isSharedCheck_571_; 
v_val_560_ = lean_ctor_get(v___x_559_, 0);
v_isSharedCheck_571_ = !lean_is_exclusive(v___x_559_);
if (v_isSharedCheck_571_ == 0)
{
v___x_562_ = v___x_559_;
v_isShared_563_ = v_isSharedCheck_571_;
goto v_resetjp_561_;
}
else
{
lean_inc(v_val_560_);
lean_dec(v___x_559_);
v___x_562_ = lean_box(0);
v_isShared_563_ = v_isSharedCheck_571_;
goto v_resetjp_561_;
}
v_resetjp_561_:
{
size_t v___x_564_; size_t v___x_565_; uint8_t v___x_566_; lean_object* v___x_567_; lean_object* v___x_569_; 
v___x_564_ = lean_ptr_addr(v_val_560_);
lean_dec(v_val_560_);
v___x_565_ = lean_ptr_addr(v_e_554_);
v___x_566_ = lean_usize_dec_eq(v___x_564_, v___x_565_);
v___x_567_ = lean_box(v___x_566_);
if (v_isShared_563_ == 0)
{
lean_ctor_set_tag(v___x_562_, 0);
lean_ctor_set(v___x_562_, 0, v___x_567_);
v___x_569_ = v___x_562_;
goto v_reusejp_568_;
}
else
{
lean_object* v_reuseFailAlloc_570_; 
v_reuseFailAlloc_570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_570_, 0, v___x_567_);
v___x_569_ = v_reuseFailAlloc_570_;
goto v_reusejp_568_;
}
v_reusejp_568_:
{
return v___x_569_;
}
}
}
else
{
uint8_t v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; 
lean_dec(v___x_559_);
v___x_572_ = 0;
v___x_573_ = lean_box(v___x_572_);
v___x_574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_574_, 0, v___x_573_);
return v___x_574_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkChild___redArg___boxed(lean_object* v_e_575_, lean_object* v_child_576_, lean_object* v_a_577_, lean_object* v_a_578_){
_start:
{
lean_object* v_res_579_; 
v_res_579_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkChild___redArg(v_e_575_, v_child_576_, v_a_577_);
lean_dec(v_a_577_);
lean_dec_ref(v_child_576_);
lean_dec_ref(v_e_575_);
return v_res_579_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkChild(lean_object* v_e_580_, lean_object* v_child_581_, lean_object* v_a_582_, lean_object* v_a_583_, lean_object* v_a_584_, lean_object* v_a_585_, lean_object* v_a_586_, lean_object* v_a_587_, lean_object* v_a_588_, lean_object* v_a_589_, lean_object* v_a_590_, lean_object* v_a_591_){
_start:
{
lean_object* v___x_593_; 
v___x_593_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkChild___redArg(v_e_580_, v_child_581_, v_a_582_);
return v___x_593_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkChild___boxed(lean_object* v_e_594_, lean_object* v_child_595_, lean_object* v_a_596_, lean_object* v_a_597_, lean_object* v_a_598_, lean_object* v_a_599_, lean_object* v_a_600_, lean_object* v_a_601_, lean_object* v_a_602_, lean_object* v_a_603_, lean_object* v_a_604_, lean_object* v_a_605_, lean_object* v_a_606_){
_start:
{
lean_object* v_res_607_; 
v_res_607_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkChild(v_e_594_, v_child_595_, v_a_596_, v_a_597_, v_a_598_, v_a_599_, v_a_600_, v_a_601_, v_a_602_, v_a_603_, v_a_604_, v_a_605_);
lean_dec(v_a_605_);
lean_dec_ref(v_a_604_);
lean_dec(v_a_603_);
lean_dec_ref(v_a_602_);
lean_dec(v_a_601_);
lean_dec_ref(v_a_600_);
lean_dec(v_a_599_);
lean_dec_ref(v_a_598_);
lean_dec(v_a_597_);
lean_dec(v_a_596_);
lean_dec_ref(v_child_595_);
lean_dec_ref(v_e_594_);
return v_res_607_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondNestedChild___closed__0(void){
_start:
{
lean_object* v___x_608_; lean_object* v_dummy_609_; 
v___x_608_ = lean_box(0);
v_dummy_609_ = l_Lean_Expr_sort___override(v___x_608_);
return v_dummy_609_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondNestedChild_spec__0___redArg(uint8_t v___x_613_, lean_object* v_upperBound_614_, lean_object* v___x_615_, lean_object* v___x_616_, lean_object* v_e_617_, lean_object* v_a_618_, lean_object* v_b_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_){
_start:
{
lean_object* v_a_632_; uint8_t v___x_636_; 
v___x_636_ = lean_nat_dec_lt(v_a_618_, v_upperBound_614_);
if (v___x_636_ == 0)
{
lean_object* v___x_637_; 
lean_dec(v_a_618_);
v___x_637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_637_, 0, v_b_619_);
return v___x_637_;
}
else
{
lean_object* v___x_638_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; uint8_t v___x_648_; 
lean_dec_ref(v_b_619_);
v___x_638_ = lean_box(0);
v___x_644_ = l_Lean_instInhabitedExpr;
v___x_645_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondNestedChild___closed__1));
v___x_646_ = lean_array_get_borrowed(v___x_644_, v___x_615_, v_a_618_);
v___x_647_ = l_Lean_Expr_getAppFn(v___x_646_);
v___x_648_ = l_Lean_Expr_isBVar(v___x_647_);
lean_dec_ref(v___x_647_);
if (v___x_648_ == 0)
{
lean_object* v___x_649_; lean_object* v___x_650_; 
v___x_649_ = lean_array_get_borrowed(v___x_644_, v___x_616_, v_a_618_);
v___x_650_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkChild___redArg(v_e_617_, v___x_649_, v___y_620_);
if (lean_obj_tag(v___x_650_) == 0)
{
lean_object* v_a_651_; uint8_t v___x_652_; 
v_a_651_ = lean_ctor_get(v___x_650_, 0);
lean_inc(v_a_651_);
lean_dec_ref_known(v___x_650_, 1);
v___x_652_ = lean_unbox(v_a_651_);
lean_dec(v_a_651_);
if (v___x_652_ == 0)
{
lean_object* v___x_653_; 
lean_inc(v___x_646_);
lean_inc(v___x_649_);
v___x_653_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondNestedChild(v_e_617_, v___x_649_, v___x_646_, v___y_620_, v___y_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_);
if (lean_obj_tag(v___x_653_) == 0)
{
lean_object* v_a_654_; uint8_t v___x_655_; 
v_a_654_ = lean_ctor_get(v___x_653_, 0);
lean_inc(v_a_654_);
lean_dec_ref_known(v___x_653_, 1);
v___x_655_ = lean_unbox(v_a_654_);
lean_dec(v_a_654_);
if (v___x_655_ == 0)
{
v_a_632_ = v___x_645_;
goto v___jp_631_;
}
else
{
lean_dec(v_a_618_);
goto v___jp_639_;
}
}
else
{
lean_object* v_a_656_; lean_object* v___x_658_; uint8_t v_isShared_659_; uint8_t v_isSharedCheck_663_; 
lean_dec(v_a_618_);
v_a_656_ = lean_ctor_get(v___x_653_, 0);
v_isSharedCheck_663_ = !lean_is_exclusive(v___x_653_);
if (v_isSharedCheck_663_ == 0)
{
v___x_658_ = v___x_653_;
v_isShared_659_ = v_isSharedCheck_663_;
goto v_resetjp_657_;
}
else
{
lean_inc(v_a_656_);
lean_dec(v___x_653_);
v___x_658_ = lean_box(0);
v_isShared_659_ = v_isSharedCheck_663_;
goto v_resetjp_657_;
}
v_resetjp_657_:
{
lean_object* v___x_661_; 
if (v_isShared_659_ == 0)
{
v___x_661_ = v___x_658_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_662_; 
v_reuseFailAlloc_662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_662_, 0, v_a_656_);
v___x_661_ = v_reuseFailAlloc_662_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
return v___x_661_;
}
}
}
}
else
{
lean_dec(v_a_618_);
goto v___jp_639_;
}
}
else
{
lean_object* v_a_664_; lean_object* v___x_666_; uint8_t v_isShared_667_; uint8_t v_isSharedCheck_671_; 
lean_dec(v_a_618_);
v_a_664_ = lean_ctor_get(v___x_650_, 0);
v_isSharedCheck_671_ = !lean_is_exclusive(v___x_650_);
if (v_isSharedCheck_671_ == 0)
{
v___x_666_ = v___x_650_;
v_isShared_667_ = v_isSharedCheck_671_;
goto v_resetjp_665_;
}
else
{
lean_inc(v_a_664_);
lean_dec(v___x_650_);
v___x_666_ = lean_box(0);
v_isShared_667_ = v_isSharedCheck_671_;
goto v_resetjp_665_;
}
v_resetjp_665_:
{
lean_object* v___x_669_; 
if (v_isShared_667_ == 0)
{
v___x_669_ = v___x_666_;
goto v_reusejp_668_;
}
else
{
lean_object* v_reuseFailAlloc_670_; 
v_reuseFailAlloc_670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_670_, 0, v_a_664_);
v___x_669_ = v_reuseFailAlloc_670_;
goto v_reusejp_668_;
}
v_reusejp_668_:
{
return v___x_669_;
}
}
}
}
else
{
v_a_632_ = v___x_645_;
goto v___jp_631_;
}
v___jp_639_:
{
lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; 
v___x_640_ = lean_box(v___x_613_);
v___x_641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_641_, 0, v___x_640_);
v___x_642_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_642_, 0, v___x_641_);
lean_ctor_set(v___x_642_, 1, v___x_638_);
v___x_643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_643_, 0, v___x_642_);
return v___x_643_;
}
}
v___jp_631_:
{
lean_object* v___x_633_; lean_object* v___x_634_; 
v___x_633_ = lean_unsigned_to_nat(1u);
v___x_634_ = lean_nat_add(v_a_618_, v___x_633_);
lean_dec(v_a_618_);
lean_inc_ref(v_a_632_);
v_a_618_ = v___x_634_;
v_b_619_ = v_a_632_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondNestedChild_spec__1___redArg(lean_object* v_val_672_, lean_object* v_pat_673_, lean_object* v___x_674_, lean_object* v_e_675_, lean_object* v_as_x27_676_, lean_object* v_b_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_){
_start:
{
if (lean_obj_tag(v_as_x27_676_) == 0)
{
lean_object* v___x_689_; 
v___x_689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_689_, 0, v_b_677_);
return v___x_689_;
}
else
{
lean_object* v_head_690_; lean_object* v_tail_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; 
lean_dec_ref(v_b_677_);
v_head_690_ = lean_ctor_get(v_as_x27_676_, 0);
v_tail_691_ = lean_ctor_get(v_as_x27_676_, 1);
v___x_692_ = lean_box(0);
v___x_693_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondNestedChild___closed__1));
lean_inc(v_head_690_);
v___x_694_ = l_Lean_Meta_isConstructorApp_x3f(v_head_690_, v___y_684_, v___y_685_, v___y_686_, v___y_687_);
if (lean_obj_tag(v___x_694_) == 0)
{
lean_object* v_a_695_; 
v_a_695_ = lean_ctor_get(v___x_694_, 0);
lean_inc(v_a_695_);
lean_dec_ref_known(v___x_694_, 1);
if (lean_obj_tag(v_a_695_) == 1)
{
lean_object* v_val_696_; lean_object* v_toConstantVal_697_; lean_object* v_toConstantVal_698_; lean_object* v_numParams_699_; lean_object* v_numFields_700_; lean_object* v_name_701_; lean_object* v_name_702_; uint8_t v___x_703_; 
v_val_696_ = lean_ctor_get(v_a_695_, 0);
lean_inc(v_val_696_);
lean_dec_ref_known(v_a_695_, 1);
v_toConstantVal_697_ = lean_ctor_get(v_val_696_, 0);
lean_inc_ref(v_toConstantVal_697_);
v_toConstantVal_698_ = lean_ctor_get(v_val_672_, 0);
v_numParams_699_ = lean_ctor_get(v_val_696_, 3);
lean_inc(v_numParams_699_);
v_numFields_700_ = lean_ctor_get(v_val_696_, 4);
lean_inc(v_numFields_700_);
lean_dec(v_val_696_);
v_name_701_ = lean_ctor_get(v_toConstantVal_697_, 0);
lean_inc(v_name_701_);
lean_dec_ref(v_toConstantVal_697_);
v_name_702_ = lean_ctor_get(v_toConstantVal_698_, 0);
v___x_703_ = lean_name_eq(v_name_701_, v_name_702_);
lean_dec(v_name_701_);
if (v___x_703_ == 0)
{
lean_dec(v_numFields_700_);
lean_dec(v_numParams_699_);
v_as_x27_676_ = v_tail_691_;
v_b_677_ = v___x_693_;
goto _start;
}
else
{
lean_object* v___x_705_; lean_object* v___x_706_; uint8_t v___x_707_; 
v___x_705_ = lean_nat_add(v_numParams_699_, v_numFields_700_);
lean_dec(v_numFields_700_);
v___x_706_ = l_Lean_Expr_getAppNumArgs(v_pat_673_);
v___x_707_ = lean_nat_dec_eq(v___x_706_, v___x_705_);
lean_dec(v___x_706_);
if (v___x_707_ == 0)
{
lean_dec(v___x_705_);
lean_dec(v_numParams_699_);
v_as_x27_676_ = v_tail_691_;
v_b_677_ = v___x_693_;
goto _start;
}
else
{
lean_object* v_nargs_709_; lean_object* v_dummy_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; 
v_nargs_709_ = l_Lean_Expr_getAppNumArgs(v_head_690_);
v_dummy_710_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondNestedChild___closed__0, &l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondNestedChild___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondNestedChild___closed__0);
lean_inc(v_nargs_709_);
v___x_711_ = lean_mk_array(v_nargs_709_, v_dummy_710_);
v___x_712_ = lean_unsigned_to_nat(1u);
v___x_713_ = lean_nat_sub(v_nargs_709_, v___x_712_);
lean_dec(v_nargs_709_);
lean_inc(v_head_690_);
v___x_714_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_head_690_, v___x_711_, v___x_713_);
v___x_715_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondNestedChild_spec__0___redArg(v___x_703_, v___x_705_, v___x_674_, v___x_714_, v_e_675_, v_numParams_699_, v___x_693_, v___y_678_, v___y_679_, v___y_680_, v___y_681_, v___y_682_, v___y_683_, v___y_684_, v___y_685_, v___y_686_, v___y_687_);
lean_dec_ref(v___x_714_);
lean_dec(v___x_705_);
if (lean_obj_tag(v___x_715_) == 0)
{
lean_object* v_a_716_; lean_object* v___x_718_; uint8_t v_isShared_719_; uint8_t v_isSharedCheck_733_; 
v_a_716_ = lean_ctor_get(v___x_715_, 0);
v_isSharedCheck_733_ = !lean_is_exclusive(v___x_715_);
if (v_isSharedCheck_733_ == 0)
{
v___x_718_ = v___x_715_;
v_isShared_719_ = v_isSharedCheck_733_;
goto v_resetjp_717_;
}
else
{
lean_inc(v_a_716_);
lean_dec(v___x_715_);
v___x_718_ = lean_box(0);
v_isShared_719_ = v_isSharedCheck_733_;
goto v_resetjp_717_;
}
v_resetjp_717_:
{
lean_object* v_fst_720_; lean_object* v___x_722_; uint8_t v_isShared_723_; uint8_t v_isSharedCheck_731_; 
v_fst_720_ = lean_ctor_get(v_a_716_, 0);
v_isSharedCheck_731_ = !lean_is_exclusive(v_a_716_);
if (v_isSharedCheck_731_ == 0)
{
lean_object* v_unused_732_; 
v_unused_732_ = lean_ctor_get(v_a_716_, 1);
lean_dec(v_unused_732_);
v___x_722_ = v_a_716_;
v_isShared_723_ = v_isSharedCheck_731_;
goto v_resetjp_721_;
}
else
{
lean_inc(v_fst_720_);
lean_dec(v_a_716_);
v___x_722_ = lean_box(0);
v_isShared_723_ = v_isSharedCheck_731_;
goto v_resetjp_721_;
}
v_resetjp_721_:
{
if (lean_obj_tag(v_fst_720_) == 0)
{
lean_del_object(v___x_722_);
lean_del_object(v___x_718_);
v_as_x27_676_ = v_tail_691_;
v_b_677_ = v___x_693_;
goto _start;
}
else
{
lean_object* v___x_726_; 
if (v_isShared_723_ == 0)
{
lean_ctor_set(v___x_722_, 1, v___x_692_);
v___x_726_ = v___x_722_;
goto v_reusejp_725_;
}
else
{
lean_object* v_reuseFailAlloc_730_; 
v_reuseFailAlloc_730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_730_, 0, v_fst_720_);
lean_ctor_set(v_reuseFailAlloc_730_, 1, v___x_692_);
v___x_726_ = v_reuseFailAlloc_730_;
goto v_reusejp_725_;
}
v_reusejp_725_:
{
lean_object* v___x_728_; 
if (v_isShared_719_ == 0)
{
lean_ctor_set(v___x_718_, 0, v___x_726_);
v___x_728_ = v___x_718_;
goto v_reusejp_727_;
}
else
{
lean_object* v_reuseFailAlloc_729_; 
v_reuseFailAlloc_729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_729_, 0, v___x_726_);
v___x_728_ = v_reuseFailAlloc_729_;
goto v_reusejp_727_;
}
v_reusejp_727_:
{
return v___x_728_;
}
}
}
}
}
}
else
{
return v___x_715_;
}
}
}
}
else
{
lean_dec(v_a_695_);
v_as_x27_676_ = v_tail_691_;
v_b_677_ = v___x_693_;
goto _start;
}
}
else
{
lean_object* v_a_735_; lean_object* v___x_737_; uint8_t v_isShared_738_; uint8_t v_isSharedCheck_742_; 
v_a_735_ = lean_ctor_get(v___x_694_, 0);
v_isSharedCheck_742_ = !lean_is_exclusive(v___x_694_);
if (v_isSharedCheck_742_ == 0)
{
v___x_737_ = v___x_694_;
v_isShared_738_ = v_isSharedCheck_742_;
goto v_resetjp_736_;
}
else
{
lean_inc(v_a_735_);
lean_dec(v___x_694_);
v___x_737_ = lean_box(0);
v_isShared_738_ = v_isSharedCheck_742_;
goto v_resetjp_736_;
}
v_resetjp_736_:
{
lean_object* v___x_740_; 
if (v_isShared_738_ == 0)
{
v___x_740_ = v___x_737_;
goto v_reusejp_739_;
}
else
{
lean_object* v_reuseFailAlloc_741_; 
v_reuseFailAlloc_741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_741_, 0, v_a_735_);
v___x_740_ = v_reuseFailAlloc_741_;
goto v_reusejp_739_;
}
v_reusejp_739_:
{
return v___x_740_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondNestedChild(lean_object* v_e_743_, lean_object* v_lhs_744_, lean_object* v_pat_745_, lean_object* v_a_746_, lean_object* v_a_747_, lean_object* v_a_748_, lean_object* v_a_749_, lean_object* v_a_750_, lean_object* v_a_751_, lean_object* v_a_752_, lean_object* v_a_753_, lean_object* v_a_754_, lean_object* v_a_755_){
_start:
{
lean_object* v___x_757_; 
lean_inc_ref(v_pat_745_);
v___x_757_ = l_Lean_Meta_isConstructorApp_x3f(v_pat_745_, v_a_752_, v_a_753_, v_a_754_, v_a_755_);
if (lean_obj_tag(v___x_757_) == 0)
{
lean_object* v_a_758_; lean_object* v___x_760_; uint8_t v_isShared_761_; uint8_t v_isSharedCheck_801_; 
v_a_758_ = lean_ctor_get(v___x_757_, 0);
v_isSharedCheck_801_ = !lean_is_exclusive(v___x_757_);
if (v_isSharedCheck_801_ == 0)
{
v___x_760_ = v___x_757_;
v_isShared_761_ = v_isSharedCheck_801_;
goto v_resetjp_759_;
}
else
{
lean_inc(v_a_758_);
lean_dec(v___x_757_);
v___x_760_ = lean_box(0);
v_isShared_761_ = v_isSharedCheck_801_;
goto v_resetjp_759_;
}
v_resetjp_759_:
{
if (lean_obj_tag(v_a_758_) == 1)
{
lean_object* v_val_762_; lean_object* v_dummy_763_; lean_object* v_nargs_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; uint8_t v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; 
lean_del_object(v___x_760_);
v_val_762_ = lean_ctor_get(v_a_758_, 0);
lean_inc(v_val_762_);
lean_dec_ref_known(v_a_758_, 1);
v_dummy_763_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondNestedChild___closed__0, &l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondNestedChild___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondNestedChild___closed__0);
v_nargs_764_ = l_Lean_Expr_getAppNumArgs(v_pat_745_);
lean_inc(v_nargs_764_);
v___x_765_ = lean_mk_array(v_nargs_764_, v_dummy_763_);
v___x_766_ = lean_unsigned_to_nat(1u);
v___x_767_ = lean_nat_sub(v_nargs_764_, v___x_766_);
lean_dec(v_nargs_764_);
lean_inc_ref(v_pat_745_);
v___x_768_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_pat_745_, v___x_765_, v___x_767_);
v___x_769_ = 0;
v___x_770_ = lean_st_ref_get(v_a_746_);
v___x_771_ = l_Lean_Meta_Grind_Goal_getEqc(v___x_770_, v_lhs_744_, v___x_769_);
lean_dec(v___x_770_);
v___x_772_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondNestedChild___closed__1));
v___x_773_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondNestedChild_spec__1___redArg(v_val_762_, v_pat_745_, v___x_768_, v_e_743_, v___x_771_, v___x_772_, v_a_746_, v_a_747_, v_a_748_, v_a_749_, v_a_750_, v_a_751_, v_a_752_, v_a_753_, v_a_754_, v_a_755_);
lean_dec(v___x_771_);
lean_dec_ref(v___x_768_);
lean_dec_ref(v_pat_745_);
lean_dec(v_val_762_);
if (lean_obj_tag(v___x_773_) == 0)
{
lean_object* v_a_774_; lean_object* v___x_776_; uint8_t v_isShared_777_; uint8_t v_isSharedCheck_787_; 
v_a_774_ = lean_ctor_get(v___x_773_, 0);
v_isSharedCheck_787_ = !lean_is_exclusive(v___x_773_);
if (v_isSharedCheck_787_ == 0)
{
v___x_776_ = v___x_773_;
v_isShared_777_ = v_isSharedCheck_787_;
goto v_resetjp_775_;
}
else
{
lean_inc(v_a_774_);
lean_dec(v___x_773_);
v___x_776_ = lean_box(0);
v_isShared_777_ = v_isSharedCheck_787_;
goto v_resetjp_775_;
}
v_resetjp_775_:
{
lean_object* v_fst_778_; 
v_fst_778_ = lean_ctor_get(v_a_774_, 0);
lean_inc(v_fst_778_);
lean_dec(v_a_774_);
if (lean_obj_tag(v_fst_778_) == 0)
{
lean_object* v___x_779_; lean_object* v___x_781_; 
v___x_779_ = lean_box(v___x_769_);
if (v_isShared_777_ == 0)
{
lean_ctor_set(v___x_776_, 0, v___x_779_);
v___x_781_ = v___x_776_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v___x_779_);
v___x_781_ = v_reuseFailAlloc_782_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
return v___x_781_;
}
}
else
{
lean_object* v_val_783_; lean_object* v___x_785_; 
v_val_783_ = lean_ctor_get(v_fst_778_, 0);
lean_inc(v_val_783_);
lean_dec_ref_known(v_fst_778_, 1);
if (v_isShared_777_ == 0)
{
lean_ctor_set(v___x_776_, 0, v_val_783_);
v___x_785_ = v___x_776_;
goto v_reusejp_784_;
}
else
{
lean_object* v_reuseFailAlloc_786_; 
v_reuseFailAlloc_786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_786_, 0, v_val_783_);
v___x_785_ = v_reuseFailAlloc_786_;
goto v_reusejp_784_;
}
v_reusejp_784_:
{
return v___x_785_;
}
}
}
}
else
{
lean_object* v_a_788_; lean_object* v___x_790_; uint8_t v_isShared_791_; uint8_t v_isSharedCheck_795_; 
v_a_788_ = lean_ctor_get(v___x_773_, 0);
v_isSharedCheck_795_ = !lean_is_exclusive(v___x_773_);
if (v_isSharedCheck_795_ == 0)
{
v___x_790_ = v___x_773_;
v_isShared_791_ = v_isSharedCheck_795_;
goto v_resetjp_789_;
}
else
{
lean_inc(v_a_788_);
lean_dec(v___x_773_);
v___x_790_ = lean_box(0);
v_isShared_791_ = v_isSharedCheck_795_;
goto v_resetjp_789_;
}
v_resetjp_789_:
{
lean_object* v___x_793_; 
if (v_isShared_791_ == 0)
{
v___x_793_ = v___x_790_;
goto v_reusejp_792_;
}
else
{
lean_object* v_reuseFailAlloc_794_; 
v_reuseFailAlloc_794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_794_, 0, v_a_788_);
v___x_793_ = v_reuseFailAlloc_794_;
goto v_reusejp_792_;
}
v_reusejp_792_:
{
return v___x_793_;
}
}
}
}
else
{
uint8_t v___x_796_; lean_object* v___x_797_; lean_object* v___x_799_; 
lean_dec(v_a_758_);
lean_dec_ref(v_pat_745_);
lean_dec_ref(v_lhs_744_);
v___x_796_ = 0;
v___x_797_ = lean_box(v___x_796_);
if (v_isShared_761_ == 0)
{
lean_ctor_set(v___x_760_, 0, v___x_797_);
v___x_799_ = v___x_760_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v___x_797_);
v___x_799_ = v_reuseFailAlloc_800_;
goto v_reusejp_798_;
}
v_reusejp_798_:
{
return v___x_799_;
}
}
}
}
else
{
lean_object* v_a_802_; lean_object* v___x_804_; uint8_t v_isShared_805_; uint8_t v_isSharedCheck_809_; 
lean_dec_ref(v_pat_745_);
lean_dec_ref(v_lhs_744_);
v_a_802_ = lean_ctor_get(v___x_757_, 0);
v_isSharedCheck_809_ = !lean_is_exclusive(v___x_757_);
if (v_isSharedCheck_809_ == 0)
{
v___x_804_ = v___x_757_;
v_isShared_805_ = v_isSharedCheck_809_;
goto v_resetjp_803_;
}
else
{
lean_inc(v_a_802_);
lean_dec(v___x_757_);
v___x_804_ = lean_box(0);
v_isShared_805_ = v_isSharedCheck_809_;
goto v_resetjp_803_;
}
v_resetjp_803_:
{
lean_object* v___x_807_; 
if (v_isShared_805_ == 0)
{
v___x_807_ = v___x_804_;
goto v_reusejp_806_;
}
else
{
lean_object* v_reuseFailAlloc_808_; 
v_reuseFailAlloc_808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_808_, 0, v_a_802_);
v___x_807_ = v_reuseFailAlloc_808_;
goto v_reusejp_806_;
}
v_reusejp_806_:
{
return v___x_807_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondNestedChild___boxed(lean_object* v_e_810_, lean_object* v_lhs_811_, lean_object* v_pat_812_, lean_object* v_a_813_, lean_object* v_a_814_, lean_object* v_a_815_, lean_object* v_a_816_, lean_object* v_a_817_, lean_object* v_a_818_, lean_object* v_a_819_, lean_object* v_a_820_, lean_object* v_a_821_, lean_object* v_a_822_, lean_object* v_a_823_){
_start:
{
lean_object* v_res_824_; 
v_res_824_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondNestedChild(v_e_810_, v_lhs_811_, v_pat_812_, v_a_813_, v_a_814_, v_a_815_, v_a_816_, v_a_817_, v_a_818_, v_a_819_, v_a_820_, v_a_821_, v_a_822_);
lean_dec(v_a_822_);
lean_dec_ref(v_a_821_);
lean_dec(v_a_820_);
lean_dec_ref(v_a_819_);
lean_dec(v_a_818_);
lean_dec_ref(v_a_817_);
lean_dec(v_a_816_);
lean_dec_ref(v_a_815_);
lean_dec(v_a_814_);
lean_dec(v_a_813_);
lean_dec_ref(v_e_810_);
return v_res_824_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondNestedChild_spec__0___redArg___boxed(lean_object** _args){
lean_object* v___x_825_ = _args[0];
lean_object* v_upperBound_826_ = _args[1];
lean_object* v___x_827_ = _args[2];
lean_object* v___x_828_ = _args[3];
lean_object* v_e_829_ = _args[4];
lean_object* v_a_830_ = _args[5];
lean_object* v_b_831_ = _args[6];
lean_object* v___y_832_ = _args[7];
lean_object* v___y_833_ = _args[8];
lean_object* v___y_834_ = _args[9];
lean_object* v___y_835_ = _args[10];
lean_object* v___y_836_ = _args[11];
lean_object* v___y_837_ = _args[12];
lean_object* v___y_838_ = _args[13];
lean_object* v___y_839_ = _args[14];
lean_object* v___y_840_ = _args[15];
lean_object* v___y_841_ = _args[16];
lean_object* v___y_842_ = _args[17];
_start:
{
uint8_t v___x_25453__boxed_843_; lean_object* v_res_844_; 
v___x_25453__boxed_843_ = lean_unbox(v___x_825_);
v_res_844_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondNestedChild_spec__0___redArg(v___x_25453__boxed_843_, v_upperBound_826_, v___x_827_, v___x_828_, v_e_829_, v_a_830_, v_b_831_, v___y_832_, v___y_833_, v___y_834_, v___y_835_, v___y_836_, v___y_837_, v___y_838_, v___y_839_, v___y_840_, v___y_841_);
lean_dec(v___y_841_);
lean_dec_ref(v___y_840_);
lean_dec(v___y_839_);
lean_dec_ref(v___y_838_);
lean_dec(v___y_837_);
lean_dec_ref(v___y_836_);
lean_dec(v___y_835_);
lean_dec_ref(v___y_834_);
lean_dec(v___y_833_);
lean_dec(v___y_832_);
lean_dec_ref(v_e_829_);
lean_dec_ref(v___x_828_);
lean_dec_ref(v___x_827_);
lean_dec(v_upperBound_826_);
return v_res_844_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondNestedChild_spec__1___redArg___boxed(lean_object** _args){
lean_object* v_val_845_ = _args[0];
lean_object* v_pat_846_ = _args[1];
lean_object* v___x_847_ = _args[2];
lean_object* v_e_848_ = _args[3];
lean_object* v_as_x27_849_ = _args[4];
lean_object* v_b_850_ = _args[5];
lean_object* v___y_851_ = _args[6];
lean_object* v___y_852_ = _args[7];
lean_object* v___y_853_ = _args[8];
lean_object* v___y_854_ = _args[9];
lean_object* v___y_855_ = _args[10];
lean_object* v___y_856_ = _args[11];
lean_object* v___y_857_ = _args[12];
lean_object* v___y_858_ = _args[13];
lean_object* v___y_859_ = _args[14];
lean_object* v___y_860_ = _args[15];
lean_object* v___y_861_ = _args[16];
_start:
{
lean_object* v_res_862_; 
v_res_862_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondNestedChild_spec__1___redArg(v_val_845_, v_pat_846_, v___x_847_, v_e_848_, v_as_x27_849_, v_b_850_, v___y_851_, v___y_852_, v___y_853_, v___y_854_, v___y_855_, v___y_856_, v___y_857_, v___y_858_, v___y_859_, v___y_860_);
lean_dec(v___y_860_);
lean_dec_ref(v___y_859_);
lean_dec(v___y_858_);
lean_dec_ref(v___y_857_);
lean_dec(v___y_856_);
lean_dec_ref(v___y_855_);
lean_dec(v___y_854_);
lean_dec_ref(v___y_853_);
lean_dec(v___y_852_);
lean_dec(v___y_851_);
lean_dec(v_as_x27_849_);
lean_dec_ref(v_e_848_);
lean_dec_ref(v___x_847_);
lean_dec_ref(v_pat_846_);
lean_dec_ref(v_val_845_);
return v_res_862_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondNestedChild_spec__0(uint8_t v___x_863_, lean_object* v_upperBound_864_, lean_object* v___x_865_, lean_object* v___x_866_, lean_object* v_e_867_, lean_object* v_inst_868_, lean_object* v_R_869_, lean_object* v_a_870_, lean_object* v_b_871_, lean_object* v_c_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_){
_start:
{
lean_object* v___x_884_; 
v___x_884_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondNestedChild_spec__0___redArg(v___x_863_, v_upperBound_864_, v___x_865_, v___x_866_, v_e_867_, v_a_870_, v_b_871_, v___y_873_, v___y_874_, v___y_875_, v___y_876_, v___y_877_, v___y_878_, v___y_879_, v___y_880_, v___y_881_, v___y_882_);
return v___x_884_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondNestedChild_spec__0___boxed(lean_object** _args){
lean_object* v___x_885_ = _args[0];
lean_object* v_upperBound_886_ = _args[1];
lean_object* v___x_887_ = _args[2];
lean_object* v___x_888_ = _args[3];
lean_object* v_e_889_ = _args[4];
lean_object* v_inst_890_ = _args[5];
lean_object* v_R_891_ = _args[6];
lean_object* v_a_892_ = _args[7];
lean_object* v_b_893_ = _args[8];
lean_object* v_c_894_ = _args[9];
lean_object* v___y_895_ = _args[10];
lean_object* v___y_896_ = _args[11];
lean_object* v___y_897_ = _args[12];
lean_object* v___y_898_ = _args[13];
lean_object* v___y_899_ = _args[14];
lean_object* v___y_900_ = _args[15];
lean_object* v___y_901_ = _args[16];
lean_object* v___y_902_ = _args[17];
lean_object* v___y_903_ = _args[18];
lean_object* v___y_904_ = _args[19];
lean_object* v___y_905_ = _args[20];
_start:
{
uint8_t v___x_25798__boxed_906_; lean_object* v_res_907_; 
v___x_25798__boxed_906_ = lean_unbox(v___x_885_);
v_res_907_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondNestedChild_spec__0(v___x_25798__boxed_906_, v_upperBound_886_, v___x_887_, v___x_888_, v_e_889_, v_inst_890_, v_R_891_, v_a_892_, v_b_893_, v_c_894_, v___y_895_, v___y_896_, v___y_897_, v___y_898_, v___y_899_, v___y_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_);
lean_dec(v___y_904_);
lean_dec_ref(v___y_903_);
lean_dec(v___y_902_);
lean_dec_ref(v___y_901_);
lean_dec(v___y_900_);
lean_dec_ref(v___y_899_);
lean_dec(v___y_898_);
lean_dec_ref(v___y_897_);
lean_dec(v___y_896_);
lean_dec(v___y_895_);
lean_dec_ref(v_e_889_);
lean_dec_ref(v___x_888_);
lean_dec_ref(v___x_887_);
lean_dec(v_upperBound_886_);
return v_res_907_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondNestedChild_spec__1(lean_object* v_val_908_, lean_object* v_pat_909_, lean_object* v___x_910_, lean_object* v_e_911_, lean_object* v_as_912_, lean_object* v_as_x27_913_, lean_object* v_b_914_, lean_object* v_a_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_){
_start:
{
lean_object* v___x_927_; 
v___x_927_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondNestedChild_spec__1___redArg(v_val_908_, v_pat_909_, v___x_910_, v_e_911_, v_as_x27_913_, v_b_914_, v___y_916_, v___y_917_, v___y_918_, v___y_919_, v___y_920_, v___y_921_, v___y_922_, v___y_923_, v___y_924_, v___y_925_);
return v___x_927_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondNestedChild_spec__1___boxed(lean_object** _args){
lean_object* v_val_928_ = _args[0];
lean_object* v_pat_929_ = _args[1];
lean_object* v___x_930_ = _args[2];
lean_object* v_e_931_ = _args[3];
lean_object* v_as_932_ = _args[4];
lean_object* v_as_x27_933_ = _args[5];
lean_object* v_b_934_ = _args[6];
lean_object* v_a_935_ = _args[7];
lean_object* v___y_936_ = _args[8];
lean_object* v___y_937_ = _args[9];
lean_object* v___y_938_ = _args[10];
lean_object* v___y_939_ = _args[11];
lean_object* v___y_940_ = _args[12];
lean_object* v___y_941_ = _args[13];
lean_object* v___y_942_ = _args[14];
lean_object* v___y_943_ = _args[15];
lean_object* v___y_944_ = _args[16];
lean_object* v___y_945_ = _args[17];
lean_object* v___y_946_ = _args[18];
_start:
{
lean_object* v_res_947_; 
v_res_947_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondNestedChild_spec__1(v_val_928_, v_pat_929_, v___x_930_, v_e_931_, v_as_932_, v_as_x27_933_, v_b_934_, v_a_935_, v___y_936_, v___y_937_, v___y_938_, v___y_939_, v___y_940_, v___y_941_, v___y_942_, v___y_943_, v___y_944_, v___y_945_);
lean_dec(v___y_945_);
lean_dec_ref(v___y_944_);
lean_dec(v___y_943_);
lean_dec_ref(v___y_942_);
lean_dec(v___y_941_);
lean_dec_ref(v___y_940_);
lean_dec(v___y_939_);
lean_dec_ref(v___y_938_);
lean_dec(v___y_937_);
lean_dec(v___y_936_);
lean_dec(v_as_x27_933_);
lean_dec(v_as_932_);
lean_dec_ref(v_e_931_);
lean_dec_ref(v___x_930_);
lean_dec_ref(v_pat_929_);
lean_dec_ref(v_val_928_);
return v_res_947_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___lam__0(lean_object* v___x_948_, lean_object* v_body_949_, lean_object* v_____r_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_){
_start:
{
lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; 
v___x_962_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_962_, 0, v___x_948_);
lean_ctor_set(v___x_962_, 1, v_body_949_);
v___x_963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_963_, 0, v___x_962_);
v___x_964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_964_, 0, v___x_963_);
return v___x_964_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___lam__0___boxed(lean_object* v___x_965_, lean_object* v_body_966_, lean_object* v_____r_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_){
_start:
{
lean_object* v_res_979_; 
v_res_979_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___lam__0(v___x_965_, v_body_966_, v_____r_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_, v___y_974_, v___y_975_, v___y_976_, v___y_977_);
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
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___lam__1(lean_object* v___f_980_, lean_object* v_x_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_){
_start:
{
lean_object* v___x_993_; lean_object* v___x_994_; 
v___x_993_ = lean_box(0);
lean_inc(v___y_991_);
lean_inc_ref(v___y_990_);
lean_inc(v___y_989_);
lean_inc_ref(v___y_988_);
lean_inc(v___y_987_);
lean_inc_ref(v___y_986_);
lean_inc(v___y_985_);
lean_inc_ref(v___y_984_);
lean_inc(v___y_983_);
lean_inc(v___y_982_);
v___x_994_ = lean_apply_12(v___f_980_, v___x_993_, v___y_982_, v___y_983_, v___y_984_, v___y_985_, v___y_986_, v___y_987_, v___y_988_, v___y_989_, v___y_990_, v___y_991_, lean_box(0));
return v___x_994_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___lam__1___boxed(lean_object* v___f_995_, lean_object* v_x_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_){
_start:
{
lean_object* v_res_1008_; 
v_res_1008_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___lam__1(v___f_995_, v_x_996_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_, v___y_1001_, v___y_1002_, v___y_1003_, v___y_1004_, v___y_1005_, v___y_1006_);
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
return v_res_1008_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg(lean_object* v_e_1018_, lean_object* v_a_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_){
_start:
{
lean_object* v___y_1032_; lean_object* v_snd_1052_; lean_object* v___x_1054_; uint8_t v_isShared_1055_; uint8_t v_isSharedCheck_1212_; 
v_snd_1052_ = lean_ctor_get(v_a_1019_, 1);
v_isSharedCheck_1212_ = !lean_is_exclusive(v_a_1019_);
if (v_isSharedCheck_1212_ == 0)
{
lean_object* v_unused_1213_; 
v_unused_1213_ = lean_ctor_get(v_a_1019_, 0);
lean_dec(v_unused_1213_);
v___x_1054_ = v_a_1019_;
v_isShared_1055_ = v_isSharedCheck_1212_;
goto v_resetjp_1053_;
}
else
{
lean_inc(v_snd_1052_);
lean_dec(v_a_1019_);
v___x_1054_ = lean_box(0);
v_isShared_1055_ = v_isSharedCheck_1212_;
goto v_resetjp_1053_;
}
v___jp_1031_:
{
if (lean_obj_tag(v___y_1032_) == 0)
{
lean_object* v_a_1033_; lean_object* v___x_1035_; uint8_t v_isShared_1036_; uint8_t v_isSharedCheck_1043_; 
v_a_1033_ = lean_ctor_get(v___y_1032_, 0);
v_isSharedCheck_1043_ = !lean_is_exclusive(v___y_1032_);
if (v_isSharedCheck_1043_ == 0)
{
v___x_1035_ = v___y_1032_;
v_isShared_1036_ = v_isSharedCheck_1043_;
goto v_resetjp_1034_;
}
else
{
lean_inc(v_a_1033_);
lean_dec(v___y_1032_);
v___x_1035_ = lean_box(0);
v_isShared_1036_ = v_isSharedCheck_1043_;
goto v_resetjp_1034_;
}
v_resetjp_1034_:
{
if (lean_obj_tag(v_a_1033_) == 0)
{
lean_object* v_a_1037_; lean_object* v___x_1039_; 
v_a_1037_ = lean_ctor_get(v_a_1033_, 0);
lean_inc(v_a_1037_);
lean_dec_ref_known(v_a_1033_, 1);
if (v_isShared_1036_ == 0)
{
lean_ctor_set(v___x_1035_, 0, v_a_1037_);
v___x_1039_ = v___x_1035_;
goto v_reusejp_1038_;
}
else
{
lean_object* v_reuseFailAlloc_1040_; 
v_reuseFailAlloc_1040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1040_, 0, v_a_1037_);
v___x_1039_ = v_reuseFailAlloc_1040_;
goto v_reusejp_1038_;
}
v_reusejp_1038_:
{
return v___x_1039_;
}
}
else
{
lean_object* v_a_1041_; 
lean_del_object(v___x_1035_);
v_a_1041_ = lean_ctor_get(v_a_1033_, 0);
lean_inc(v_a_1041_);
lean_dec_ref_known(v_a_1033_, 1);
v_a_1019_ = v_a_1041_;
goto _start;
}
}
}
else
{
lean_object* v_a_1044_; lean_object* v___x_1046_; uint8_t v_isShared_1047_; uint8_t v_isSharedCheck_1051_; 
v_a_1044_ = lean_ctor_get(v___y_1032_, 0);
v_isSharedCheck_1051_ = !lean_is_exclusive(v___y_1032_);
if (v_isSharedCheck_1051_ == 0)
{
v___x_1046_ = v___y_1032_;
v_isShared_1047_ = v_isSharedCheck_1051_;
goto v_resetjp_1045_;
}
else
{
lean_inc(v_a_1044_);
lean_dec(v___y_1032_);
v___x_1046_ = lean_box(0);
v_isShared_1047_ = v_isSharedCheck_1051_;
goto v_resetjp_1045_;
}
v_resetjp_1045_:
{
lean_object* v___x_1049_; 
if (v_isShared_1047_ == 0)
{
v___x_1049_ = v___x_1046_;
goto v_reusejp_1048_;
}
else
{
lean_object* v_reuseFailAlloc_1050_; 
v_reuseFailAlloc_1050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1050_, 0, v_a_1044_);
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
v_resetjp_1053_:
{
if (lean_obj_tag(v_snd_1052_) == 7)
{
lean_object* v_binderType_1056_; lean_object* v_body_1057_; lean_object* v___x_1058_; lean_object* v___f_1059_; lean_object* v___x_1060_; 
v_binderType_1056_ = lean_ctor_get(v_snd_1052_, 1);
v_body_1057_ = lean_ctor_get(v_snd_1052_, 2);
v___x_1058_ = lean_box(0);
lean_inc_ref(v_body_1057_);
v___f_1059_ = lean_alloc_closure((void*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___lam__0___boxed), 14, 2);
lean_closure_set(v___f_1059_, 0, v___x_1058_);
lean_closure_set(v___f_1059_, 1, v_body_1057_);
lean_inc_ref(v_binderType_1056_);
v___x_1060_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_binderType_1056_, v___y_1027_);
if (lean_obj_tag(v___x_1060_) == 0)
{
lean_object* v_a_1061_; lean_object* v___x_1063_; uint8_t v_isShared_1064_; uint8_t v_isSharedCheck_1198_; 
v_a_1061_ = lean_ctor_get(v___x_1060_, 0);
v_isSharedCheck_1198_ = !lean_is_exclusive(v___x_1060_);
if (v_isSharedCheck_1198_ == 0)
{
v___x_1063_ = v___x_1060_;
v_isShared_1064_ = v_isSharedCheck_1198_;
goto v_resetjp_1062_;
}
else
{
lean_inc(v_a_1061_);
lean_dec(v___x_1060_);
v___x_1063_ = lean_box(0);
v_isShared_1064_ = v_isSharedCheck_1198_;
goto v_resetjp_1062_;
}
v_resetjp_1062_:
{
lean_object* v___x_1065_; uint8_t v___x_1066_; 
v___x_1065_ = l_Lean_Expr_cleanupAnnotations(v_a_1061_);
lean_dec(v_a_1061_);
v___x_1066_ = l_Lean_Expr_isApp(v___x_1065_);
if (v___x_1066_ == 0)
{
lean_object* v___x_1067_; lean_object* v___x_1068_; 
lean_dec_ref(v___x_1065_);
lean_del_object(v___x_1063_);
lean_dec_ref_known(v_snd_1052_, 3);
lean_del_object(v___x_1054_);
v___x_1067_ = lean_box(0);
v___x_1068_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___lam__1(v___f_1059_, v___x_1067_, v___y_1020_, v___y_1021_, v___y_1022_, v___y_1023_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_, v___y_1029_);
v___y_1032_ = v___x_1068_;
goto v___jp_1031_;
}
else
{
lean_object* v___x_1069_; uint8_t v___x_1070_; 
v___x_1069_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1065_);
v___x_1070_ = l_Lean_Expr_isApp(v___x_1069_);
if (v___x_1070_ == 0)
{
lean_object* v___x_1071_; lean_object* v___x_1072_; 
lean_dec_ref(v___x_1069_);
lean_dec_ref(v___x_1065_);
lean_del_object(v___x_1063_);
lean_dec_ref_known(v_snd_1052_, 3);
lean_del_object(v___x_1054_);
v___x_1071_ = lean_box(0);
v___x_1072_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___lam__1(v___f_1059_, v___x_1071_, v___y_1020_, v___y_1021_, v___y_1022_, v___y_1023_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_, v___y_1029_);
v___y_1032_ = v___x_1072_;
goto v___jp_1031_;
}
else
{
lean_object* v___x_1073_; uint8_t v___x_1074_; 
v___x_1073_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1069_);
v___x_1074_ = l_Lean_Expr_isApp(v___x_1073_);
if (v___x_1074_ == 0)
{
lean_object* v___x_1075_; lean_object* v___x_1076_; 
lean_dec_ref(v___x_1073_);
lean_dec_ref(v___x_1069_);
lean_dec_ref(v___x_1065_);
lean_del_object(v___x_1063_);
lean_dec_ref_known(v_snd_1052_, 3);
lean_del_object(v___x_1054_);
v___x_1075_ = lean_box(0);
v___x_1076_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___lam__1(v___f_1059_, v___x_1075_, v___y_1020_, v___y_1021_, v___y_1022_, v___y_1023_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_, v___y_1029_);
v___y_1032_ = v___x_1076_;
goto v___jp_1031_;
}
else
{
lean_object* v_arg_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; uint8_t v___x_1080_; 
v_arg_1077_ = lean_ctor_get(v___x_1065_, 1);
lean_inc_ref(v_arg_1077_);
lean_dec_ref(v___x_1065_);
v___x_1078_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1073_);
v___x_1079_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___closed__1));
v___x_1080_ = l_Lean_Expr_isConstOf(v___x_1078_, v___x_1079_);
if (v___x_1080_ == 0)
{
uint8_t v___x_1081_; 
lean_dec_ref(v___x_1069_);
v___x_1081_ = l_Lean_Expr_isApp(v___x_1078_);
if (v___x_1081_ == 0)
{
lean_object* v___x_1082_; lean_object* v___x_1083_; 
lean_dec_ref(v___x_1078_);
lean_dec_ref(v_arg_1077_);
lean_dec_ref(v___x_1073_);
lean_del_object(v___x_1063_);
lean_dec_ref_known(v_snd_1052_, 3);
lean_del_object(v___x_1054_);
v___x_1082_ = lean_box(0);
v___x_1083_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___lam__1(v___f_1059_, v___x_1082_, v___y_1020_, v___y_1021_, v___y_1022_, v___y_1023_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_, v___y_1029_);
v___y_1032_ = v___x_1083_;
goto v___jp_1031_;
}
else
{
lean_object* v___x_1084_; lean_object* v___x_1085_; uint8_t v___x_1086_; 
v___x_1084_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1078_);
v___x_1085_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___closed__3));
v___x_1086_ = l_Lean_Expr_isConstOf(v___x_1084_, v___x_1085_);
lean_dec_ref(v___x_1084_);
if (v___x_1086_ == 0)
{
lean_object* v___x_1096_; lean_object* v___x_1097_; 
lean_dec_ref(v___x_1078_);
lean_dec_ref(v_arg_1077_);
lean_dec_ref(v___x_1073_);
lean_del_object(v___x_1063_);
lean_dec_ref_known(v_snd_1052_, 3);
lean_del_object(v___x_1054_);
v___x_1096_ = lean_box(0);
v___x_1097_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___lam__1(v___f_1059_, v___x_1096_, v___y_1020_, v___y_1021_, v___y_1022_, v___y_1023_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_, v___y_1029_);
v___y_1032_ = v___x_1097_;
goto v___jp_1031_;
}
else
{
lean_object* v_arg_1098_; lean_object* v_arg_1099_; lean_object* v___x_1100_; 
lean_dec_ref(v___f_1059_);
v_arg_1098_ = lean_ctor_get(v___x_1073_, 1);
lean_inc_ref(v_arg_1098_);
lean_dec_ref(v___x_1073_);
v_arg_1099_ = lean_ctor_get(v___x_1078_, 1);
lean_inc_ref(v_arg_1099_);
lean_dec_ref(v___x_1078_);
v___x_1100_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkChild___redArg(v_e_1018_, v_arg_1099_, v___y_1020_);
lean_dec_ref(v_arg_1099_);
if (lean_obj_tag(v___x_1100_) == 0)
{
lean_object* v_a_1101_; uint8_t v___x_1102_; 
v_a_1101_ = lean_ctor_get(v___x_1100_, 0);
lean_inc(v_a_1101_);
lean_dec_ref_known(v___x_1100_, 1);
v___x_1102_ = lean_unbox(v_a_1101_);
lean_dec(v_a_1101_);
if (v___x_1102_ == 0)
{
lean_object* v___x_1103_; 
v___x_1103_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkChild___redArg(v_e_1018_, v_arg_1098_, v___y_1020_);
if (lean_obj_tag(v___x_1103_) == 0)
{
lean_object* v_a_1104_; uint8_t v___x_1105_; 
v_a_1104_ = lean_ctor_get(v___x_1103_, 0);
lean_inc(v_a_1104_);
lean_dec_ref_known(v___x_1103_, 1);
v___x_1105_ = lean_unbox(v_a_1104_);
lean_dec(v_a_1104_);
if (v___x_1105_ == 0)
{
lean_object* v___x_1106_; 
lean_del_object(v___x_1063_);
lean_del_object(v___x_1054_);
lean_inc_ref(v_arg_1098_);
v___x_1106_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondNestedChild(v_e_1018_, v_arg_1098_, v_arg_1077_, v___y_1020_, v___y_1021_, v___y_1022_, v___y_1023_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_, v___y_1029_);
if (lean_obj_tag(v___x_1106_) == 0)
{
lean_object* v_a_1107_; lean_object* v___x_1109_; uint8_t v_isShared_1110_; uint8_t v_isSharedCheck_1122_; 
v_a_1107_ = lean_ctor_get(v___x_1106_, 0);
v_isSharedCheck_1122_ = !lean_is_exclusive(v___x_1106_);
if (v_isSharedCheck_1122_ == 0)
{
v___x_1109_ = v___x_1106_;
v_isShared_1110_ = v_isSharedCheck_1122_;
goto v_resetjp_1108_;
}
else
{
lean_inc(v_a_1107_);
lean_dec(v___x_1106_);
v___x_1109_ = lean_box(0);
v_isShared_1110_ = v_isSharedCheck_1122_;
goto v_resetjp_1108_;
}
v_resetjp_1108_:
{
uint8_t v___x_1114_; 
v___x_1114_ = l_Lean_Expr_hasLooseBVars(v_arg_1098_);
lean_dec_ref(v_arg_1098_);
if (v___x_1114_ == 0)
{
uint8_t v___x_1115_; 
v___x_1115_ = lean_unbox(v_a_1107_);
lean_dec(v_a_1107_);
if (v___x_1115_ == 0)
{
lean_inc_ref(v_body_1057_);
lean_del_object(v___x_1109_);
lean_dec_ref_known(v_snd_1052_, 3);
goto v___jp_1111_;
}
else
{
lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1120_; 
v___x_1116_ = lean_box(v___x_1086_);
v___x_1117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1117_, 0, v___x_1116_);
v___x_1118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1118_, 0, v___x_1117_);
lean_ctor_set(v___x_1118_, 1, v_snd_1052_);
if (v_isShared_1110_ == 0)
{
lean_ctor_set(v___x_1109_, 0, v___x_1118_);
v___x_1120_ = v___x_1109_;
goto v_reusejp_1119_;
}
else
{
lean_object* v_reuseFailAlloc_1121_; 
v_reuseFailAlloc_1121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1121_, 0, v___x_1118_);
v___x_1120_ = v_reuseFailAlloc_1121_;
goto v_reusejp_1119_;
}
v_reusejp_1119_:
{
return v___x_1120_;
}
}
}
else
{
lean_inc_ref(v_body_1057_);
lean_del_object(v___x_1109_);
lean_dec(v_a_1107_);
lean_dec_ref_known(v_snd_1052_, 3);
goto v___jp_1111_;
}
v___jp_1111_:
{
lean_object* v___x_1112_; lean_object* v___x_1113_; 
v___x_1112_ = lean_box(0);
v___x_1113_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___lam__0(v___x_1058_, v_body_1057_, v___x_1112_, v___y_1020_, v___y_1021_, v___y_1022_, v___y_1023_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_, v___y_1029_);
v___y_1032_ = v___x_1113_;
goto v___jp_1031_;
}
}
}
else
{
lean_object* v_a_1123_; lean_object* v___x_1125_; uint8_t v_isShared_1126_; uint8_t v_isSharedCheck_1130_; 
lean_dec_ref(v_arg_1098_);
lean_dec_ref_known(v_snd_1052_, 3);
v_a_1123_ = lean_ctor_get(v___x_1106_, 0);
v_isSharedCheck_1130_ = !lean_is_exclusive(v___x_1106_);
if (v_isSharedCheck_1130_ == 0)
{
v___x_1125_ = v___x_1106_;
v_isShared_1126_ = v_isSharedCheck_1130_;
goto v_resetjp_1124_;
}
else
{
lean_inc(v_a_1123_);
lean_dec(v___x_1106_);
v___x_1125_ = lean_box(0);
v_isShared_1126_ = v_isSharedCheck_1130_;
goto v_resetjp_1124_;
}
v_resetjp_1124_:
{
lean_object* v___x_1128_; 
if (v_isShared_1126_ == 0)
{
v___x_1128_ = v___x_1125_;
goto v_reusejp_1127_;
}
else
{
lean_object* v_reuseFailAlloc_1129_; 
v_reuseFailAlloc_1129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1129_, 0, v_a_1123_);
v___x_1128_ = v_reuseFailAlloc_1129_;
goto v_reusejp_1127_;
}
v_reusejp_1127_:
{
return v___x_1128_;
}
}
}
}
else
{
lean_dec_ref(v_arg_1098_);
lean_dec_ref(v_arg_1077_);
goto v___jp_1087_;
}
}
else
{
lean_object* v_a_1131_; lean_object* v___x_1133_; uint8_t v_isShared_1134_; uint8_t v_isSharedCheck_1138_; 
lean_dec_ref(v_arg_1098_);
lean_dec_ref(v_arg_1077_);
lean_del_object(v___x_1063_);
lean_dec_ref_known(v_snd_1052_, 3);
lean_del_object(v___x_1054_);
v_a_1131_ = lean_ctor_get(v___x_1103_, 0);
v_isSharedCheck_1138_ = !lean_is_exclusive(v___x_1103_);
if (v_isSharedCheck_1138_ == 0)
{
v___x_1133_ = v___x_1103_;
v_isShared_1134_ = v_isSharedCheck_1138_;
goto v_resetjp_1132_;
}
else
{
lean_inc(v_a_1131_);
lean_dec(v___x_1103_);
v___x_1133_ = lean_box(0);
v_isShared_1134_ = v_isSharedCheck_1138_;
goto v_resetjp_1132_;
}
v_resetjp_1132_:
{
lean_object* v___x_1136_; 
if (v_isShared_1134_ == 0)
{
v___x_1136_ = v___x_1133_;
goto v_reusejp_1135_;
}
else
{
lean_object* v_reuseFailAlloc_1137_; 
v_reuseFailAlloc_1137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1137_, 0, v_a_1131_);
v___x_1136_ = v_reuseFailAlloc_1137_;
goto v_reusejp_1135_;
}
v_reusejp_1135_:
{
return v___x_1136_;
}
}
}
}
else
{
lean_dec_ref(v_arg_1098_);
lean_dec_ref(v_arg_1077_);
goto v___jp_1087_;
}
}
else
{
lean_object* v_a_1139_; lean_object* v___x_1141_; uint8_t v_isShared_1142_; uint8_t v_isSharedCheck_1146_; 
lean_dec_ref(v_arg_1098_);
lean_dec_ref(v_arg_1077_);
lean_del_object(v___x_1063_);
lean_dec_ref_known(v_snd_1052_, 3);
lean_del_object(v___x_1054_);
v_a_1139_ = lean_ctor_get(v___x_1100_, 0);
v_isSharedCheck_1146_ = !lean_is_exclusive(v___x_1100_);
if (v_isSharedCheck_1146_ == 0)
{
v___x_1141_ = v___x_1100_;
v_isShared_1142_ = v_isSharedCheck_1146_;
goto v_resetjp_1140_;
}
else
{
lean_inc(v_a_1139_);
lean_dec(v___x_1100_);
v___x_1141_ = lean_box(0);
v_isShared_1142_ = v_isSharedCheck_1146_;
goto v_resetjp_1140_;
}
v_resetjp_1140_:
{
lean_object* v___x_1144_; 
if (v_isShared_1142_ == 0)
{
v___x_1144_ = v___x_1141_;
goto v_reusejp_1143_;
}
else
{
lean_object* v_reuseFailAlloc_1145_; 
v_reuseFailAlloc_1145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1145_, 0, v_a_1139_);
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
v___jp_1087_:
{
lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1091_; 
v___x_1088_ = lean_box(v___x_1086_);
v___x_1089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1089_, 0, v___x_1088_);
if (v_isShared_1055_ == 0)
{
lean_ctor_set(v___x_1054_, 0, v___x_1089_);
v___x_1091_ = v___x_1054_;
goto v_reusejp_1090_;
}
else
{
lean_object* v_reuseFailAlloc_1095_; 
v_reuseFailAlloc_1095_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1095_, 0, v___x_1089_);
lean_ctor_set(v_reuseFailAlloc_1095_, 1, v_snd_1052_);
v___x_1091_ = v_reuseFailAlloc_1095_;
goto v_reusejp_1090_;
}
v_reusejp_1090_:
{
lean_object* v___x_1093_; 
if (v_isShared_1064_ == 0)
{
lean_ctor_set(v___x_1063_, 0, v___x_1091_);
v___x_1093_ = v___x_1063_;
goto v_reusejp_1092_;
}
else
{
lean_object* v_reuseFailAlloc_1094_; 
v_reuseFailAlloc_1094_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1094_, 0, v___x_1091_);
v___x_1093_ = v_reuseFailAlloc_1094_;
goto v_reusejp_1092_;
}
v_reusejp_1092_:
{
return v___x_1093_;
}
}
}
}
}
else
{
lean_object* v_arg_1147_; lean_object* v___x_1148_; 
lean_dec_ref(v___x_1078_);
lean_dec_ref(v___x_1073_);
lean_del_object(v___x_1063_);
lean_dec_ref(v___f_1059_);
v_arg_1147_ = lean_ctor_get(v___x_1069_, 1);
lean_inc_ref(v_arg_1147_);
lean_dec_ref(v___x_1069_);
v___x_1148_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkChild___redArg(v_e_1018_, v_arg_1147_, v___y_1020_);
if (lean_obj_tag(v___x_1148_) == 0)
{
lean_object* v_a_1149_; lean_object* v___x_1151_; uint8_t v_isShared_1152_; uint8_t v_isSharedCheck_1189_; 
v_a_1149_ = lean_ctor_get(v___x_1148_, 0);
v_isSharedCheck_1189_ = !lean_is_exclusive(v___x_1148_);
if (v_isSharedCheck_1189_ == 0)
{
v___x_1151_ = v___x_1148_;
v_isShared_1152_ = v_isSharedCheck_1189_;
goto v_resetjp_1150_;
}
else
{
lean_inc(v_a_1149_);
lean_dec(v___x_1148_);
v___x_1151_ = lean_box(0);
v_isShared_1152_ = v_isSharedCheck_1189_;
goto v_resetjp_1150_;
}
v_resetjp_1150_:
{
uint8_t v___x_1153_; 
v___x_1153_ = lean_unbox(v_a_1149_);
lean_dec(v_a_1149_);
if (v___x_1153_ == 0)
{
lean_object* v___x_1154_; 
lean_del_object(v___x_1151_);
lean_inc_ref(v_arg_1147_);
v___x_1154_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondNestedChild(v_e_1018_, v_arg_1147_, v_arg_1077_, v___y_1020_, v___y_1021_, v___y_1022_, v___y_1023_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_, v___y_1029_);
if (lean_obj_tag(v___x_1154_) == 0)
{
lean_object* v_a_1155_; lean_object* v___x_1157_; uint8_t v_isShared_1158_; uint8_t v_isSharedCheck_1172_; 
v_a_1155_ = lean_ctor_get(v___x_1154_, 0);
v_isSharedCheck_1172_ = !lean_is_exclusive(v___x_1154_);
if (v_isSharedCheck_1172_ == 0)
{
v___x_1157_ = v___x_1154_;
v_isShared_1158_ = v_isSharedCheck_1172_;
goto v_resetjp_1156_;
}
else
{
lean_inc(v_a_1155_);
lean_dec(v___x_1154_);
v___x_1157_ = lean_box(0);
v_isShared_1158_ = v_isSharedCheck_1172_;
goto v_resetjp_1156_;
}
v_resetjp_1156_:
{
uint8_t v___x_1162_; 
v___x_1162_ = l_Lean_Expr_hasLooseBVars(v_arg_1147_);
lean_dec_ref(v_arg_1147_);
if (v___x_1162_ == 0)
{
uint8_t v___x_1163_; 
v___x_1163_ = lean_unbox(v_a_1155_);
lean_dec(v_a_1155_);
if (v___x_1163_ == 0)
{
lean_inc_ref(v_body_1057_);
lean_del_object(v___x_1157_);
lean_dec_ref_known(v_snd_1052_, 3);
lean_del_object(v___x_1054_);
goto v___jp_1159_;
}
else
{
lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1167_; 
v___x_1164_ = lean_box(v___x_1080_);
v___x_1165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1165_, 0, v___x_1164_);
if (v_isShared_1055_ == 0)
{
lean_ctor_set(v___x_1054_, 0, v___x_1165_);
v___x_1167_ = v___x_1054_;
goto v_reusejp_1166_;
}
else
{
lean_object* v_reuseFailAlloc_1171_; 
v_reuseFailAlloc_1171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1171_, 0, v___x_1165_);
lean_ctor_set(v_reuseFailAlloc_1171_, 1, v_snd_1052_);
v___x_1167_ = v_reuseFailAlloc_1171_;
goto v_reusejp_1166_;
}
v_reusejp_1166_:
{
lean_object* v___x_1169_; 
if (v_isShared_1158_ == 0)
{
lean_ctor_set(v___x_1157_, 0, v___x_1167_);
v___x_1169_ = v___x_1157_;
goto v_reusejp_1168_;
}
else
{
lean_object* v_reuseFailAlloc_1170_; 
v_reuseFailAlloc_1170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1170_, 0, v___x_1167_);
v___x_1169_ = v_reuseFailAlloc_1170_;
goto v_reusejp_1168_;
}
v_reusejp_1168_:
{
return v___x_1169_;
}
}
}
}
else
{
lean_inc_ref(v_body_1057_);
lean_del_object(v___x_1157_);
lean_dec(v_a_1155_);
lean_dec_ref_known(v_snd_1052_, 3);
lean_del_object(v___x_1054_);
goto v___jp_1159_;
}
v___jp_1159_:
{
lean_object* v___x_1160_; lean_object* v___x_1161_; 
v___x_1160_ = lean_box(0);
v___x_1161_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___lam__0(v___x_1058_, v_body_1057_, v___x_1160_, v___y_1020_, v___y_1021_, v___y_1022_, v___y_1023_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_, v___y_1029_);
v___y_1032_ = v___x_1161_;
goto v___jp_1031_;
}
}
}
else
{
lean_object* v_a_1173_; lean_object* v___x_1175_; uint8_t v_isShared_1176_; uint8_t v_isSharedCheck_1180_; 
lean_dec_ref(v_arg_1147_);
lean_dec_ref_known(v_snd_1052_, 3);
lean_del_object(v___x_1054_);
v_a_1173_ = lean_ctor_get(v___x_1154_, 0);
v_isSharedCheck_1180_ = !lean_is_exclusive(v___x_1154_);
if (v_isSharedCheck_1180_ == 0)
{
v___x_1175_ = v___x_1154_;
v_isShared_1176_ = v_isSharedCheck_1180_;
goto v_resetjp_1174_;
}
else
{
lean_inc(v_a_1173_);
lean_dec(v___x_1154_);
v___x_1175_ = lean_box(0);
v_isShared_1176_ = v_isSharedCheck_1180_;
goto v_resetjp_1174_;
}
v_resetjp_1174_:
{
lean_object* v___x_1178_; 
if (v_isShared_1176_ == 0)
{
v___x_1178_ = v___x_1175_;
goto v_reusejp_1177_;
}
else
{
lean_object* v_reuseFailAlloc_1179_; 
v_reuseFailAlloc_1179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1179_, 0, v_a_1173_);
v___x_1178_ = v_reuseFailAlloc_1179_;
goto v_reusejp_1177_;
}
v_reusejp_1177_:
{
return v___x_1178_;
}
}
}
}
else
{
lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1184_; 
lean_dec_ref(v_arg_1147_);
lean_dec_ref(v_arg_1077_);
v___x_1181_ = lean_box(v___x_1080_);
v___x_1182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1182_, 0, v___x_1181_);
if (v_isShared_1055_ == 0)
{
lean_ctor_set(v___x_1054_, 0, v___x_1182_);
v___x_1184_ = v___x_1054_;
goto v_reusejp_1183_;
}
else
{
lean_object* v_reuseFailAlloc_1188_; 
v_reuseFailAlloc_1188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1188_, 0, v___x_1182_);
lean_ctor_set(v_reuseFailAlloc_1188_, 1, v_snd_1052_);
v___x_1184_ = v_reuseFailAlloc_1188_;
goto v_reusejp_1183_;
}
v_reusejp_1183_:
{
lean_object* v___x_1186_; 
if (v_isShared_1152_ == 0)
{
lean_ctor_set(v___x_1151_, 0, v___x_1184_);
v___x_1186_ = v___x_1151_;
goto v_reusejp_1185_;
}
else
{
lean_object* v_reuseFailAlloc_1187_; 
v_reuseFailAlloc_1187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1187_, 0, v___x_1184_);
v___x_1186_ = v_reuseFailAlloc_1187_;
goto v_reusejp_1185_;
}
v_reusejp_1185_:
{
return v___x_1186_;
}
}
}
}
}
else
{
lean_object* v_a_1190_; lean_object* v___x_1192_; uint8_t v_isShared_1193_; uint8_t v_isSharedCheck_1197_; 
lean_dec_ref(v_arg_1147_);
lean_dec_ref(v_arg_1077_);
lean_dec_ref_known(v_snd_1052_, 3);
lean_del_object(v___x_1054_);
v_a_1190_ = lean_ctor_get(v___x_1148_, 0);
v_isSharedCheck_1197_ = !lean_is_exclusive(v___x_1148_);
if (v_isSharedCheck_1197_ == 0)
{
v___x_1192_ = v___x_1148_;
v_isShared_1193_ = v_isSharedCheck_1197_;
goto v_resetjp_1191_;
}
else
{
lean_inc(v_a_1190_);
lean_dec(v___x_1148_);
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
}
}
}
}
else
{
lean_object* v_a_1199_; lean_object* v___x_1201_; uint8_t v_isShared_1202_; uint8_t v_isSharedCheck_1206_; 
lean_dec_ref(v___f_1059_);
lean_dec_ref_known(v_snd_1052_, 3);
lean_del_object(v___x_1054_);
v_a_1199_ = lean_ctor_get(v___x_1060_, 0);
v_isSharedCheck_1206_ = !lean_is_exclusive(v___x_1060_);
if (v_isSharedCheck_1206_ == 0)
{
v___x_1201_ = v___x_1060_;
v_isShared_1202_ = v_isSharedCheck_1206_;
goto v_resetjp_1200_;
}
else
{
lean_inc(v_a_1199_);
lean_dec(v___x_1060_);
v___x_1201_ = lean_box(0);
v_isShared_1202_ = v_isSharedCheck_1206_;
goto v_resetjp_1200_;
}
v_resetjp_1200_:
{
lean_object* v___x_1204_; 
if (v_isShared_1202_ == 0)
{
v___x_1204_ = v___x_1201_;
goto v_reusejp_1203_;
}
else
{
lean_object* v_reuseFailAlloc_1205_; 
v_reuseFailAlloc_1205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1205_, 0, v_a_1199_);
v___x_1204_ = v_reuseFailAlloc_1205_;
goto v_reusejp_1203_;
}
v_reusejp_1203_:
{
return v___x_1204_;
}
}
}
}
else
{
lean_object* v___x_1207_; lean_object* v___x_1209_; 
v___x_1207_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___closed__4));
if (v_isShared_1055_ == 0)
{
lean_ctor_set(v___x_1054_, 0, v___x_1207_);
v___x_1209_ = v___x_1054_;
goto v_reusejp_1208_;
}
else
{
lean_object* v_reuseFailAlloc_1211_; 
v_reuseFailAlloc_1211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1211_, 0, v___x_1207_);
lean_ctor_set(v_reuseFailAlloc_1211_, 1, v_snd_1052_);
v___x_1209_ = v_reuseFailAlloc_1211_;
goto v_reusejp_1208_;
}
v_reusejp_1208_:
{
lean_object* v___x_1210_; 
v___x_1210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1210_, 0, v___x_1209_);
return v___x_1210_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___boxed(lean_object* v_e_1214_, lean_object* v_a_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_){
_start:
{
lean_object* v_res_1227_; 
v_res_1227_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg(v_e_1214_, v_a_1215_, v___y_1216_, v___y_1217_, v___y_1218_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_);
lean_dec(v___y_1225_);
lean_dec_ref(v___y_1224_);
lean_dec(v___y_1223_);
lean_dec_ref(v___y_1222_);
lean_dec(v___y_1221_);
lean_dec_ref(v___y_1220_);
lean_dec(v___y_1219_);
lean_dec_ref(v___y_1218_);
lean_dec(v___y_1217_);
lean_dec(v___y_1216_);
lean_dec_ref(v_e_1214_);
return v_res_1227_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent(lean_object* v_e_1235_, lean_object* v_parent_1236_, lean_object* v_a_1237_, lean_object* v_a_1238_, lean_object* v_a_1239_, lean_object* v_a_1240_, lean_object* v_a_1241_, lean_object* v_a_1242_, lean_object* v_a_1243_, lean_object* v_a_1244_, lean_object* v_a_1245_, lean_object* v_a_1246_){
_start:
{
lean_object* v___x_1252_; 
v___x_1252_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_parent_1236_, v_a_1244_);
if (lean_obj_tag(v___x_1252_) == 0)
{
lean_object* v_a_1253_; lean_object* v___x_1254_; uint8_t v___x_1255_; 
v_a_1253_ = lean_ctor_get(v___x_1252_, 0);
lean_inc(v_a_1253_);
lean_dec_ref_known(v___x_1252_, 1);
v___x_1254_ = l_Lean_Expr_cleanupAnnotations(v_a_1253_);
lean_dec(v_a_1253_);
v___x_1255_ = l_Lean_Expr_isApp(v___x_1254_);
if (v___x_1255_ == 0)
{
lean_dec_ref(v___x_1254_);
goto v___jp_1248_;
}
else
{
lean_object* v___x_1256_; lean_object* v___x_1257_; uint8_t v___x_1258_; 
v___x_1256_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1254_);
v___x_1257_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent___closed__3));
v___x_1258_ = l_Lean_Expr_isConstOf(v___x_1256_, v___x_1257_);
lean_dec_ref(v___x_1256_);
if (v___x_1258_ == 0)
{
lean_dec_ref(v___x_1254_);
goto v___jp_1248_;
}
else
{
lean_object* v_arg_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; 
v_arg_1259_ = lean_ctor_get(v___x_1254_, 1);
lean_inc_ref(v_arg_1259_);
lean_dec_ref(v___x_1254_);
v___x_1260_ = lean_box(0);
v___x_1261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1261_, 0, v___x_1260_);
lean_ctor_set(v___x_1261_, 1, v_arg_1259_);
v___x_1262_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg(v_e_1235_, v___x_1261_, v_a_1237_, v_a_1238_, v_a_1239_, v_a_1240_, v_a_1241_, v_a_1242_, v_a_1243_, v_a_1244_, v_a_1245_, v_a_1246_);
if (lean_obj_tag(v___x_1262_) == 0)
{
lean_object* v_a_1263_; lean_object* v___x_1265_; uint8_t v_isShared_1266_; uint8_t v_isSharedCheck_1277_; 
v_a_1263_ = lean_ctor_get(v___x_1262_, 0);
v_isSharedCheck_1277_ = !lean_is_exclusive(v___x_1262_);
if (v_isSharedCheck_1277_ == 0)
{
v___x_1265_ = v___x_1262_;
v_isShared_1266_ = v_isSharedCheck_1277_;
goto v_resetjp_1264_;
}
else
{
lean_inc(v_a_1263_);
lean_dec(v___x_1262_);
v___x_1265_ = lean_box(0);
v_isShared_1266_ = v_isSharedCheck_1277_;
goto v_resetjp_1264_;
}
v_resetjp_1264_:
{
lean_object* v_fst_1267_; 
v_fst_1267_ = lean_ctor_get(v_a_1263_, 0);
lean_inc(v_fst_1267_);
lean_dec(v_a_1263_);
if (lean_obj_tag(v_fst_1267_) == 0)
{
uint8_t v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1271_; 
v___x_1268_ = 0;
v___x_1269_ = lean_box(v___x_1268_);
if (v_isShared_1266_ == 0)
{
lean_ctor_set(v___x_1265_, 0, v___x_1269_);
v___x_1271_ = v___x_1265_;
goto v_reusejp_1270_;
}
else
{
lean_object* v_reuseFailAlloc_1272_; 
v_reuseFailAlloc_1272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1272_, 0, v___x_1269_);
v___x_1271_ = v_reuseFailAlloc_1272_;
goto v_reusejp_1270_;
}
v_reusejp_1270_:
{
return v___x_1271_;
}
}
else
{
lean_object* v_val_1273_; lean_object* v___x_1275_; 
v_val_1273_ = lean_ctor_get(v_fst_1267_, 0);
lean_inc(v_val_1273_);
lean_dec_ref_known(v_fst_1267_, 1);
if (v_isShared_1266_ == 0)
{
lean_ctor_set(v___x_1265_, 0, v_val_1273_);
v___x_1275_ = v___x_1265_;
goto v_reusejp_1274_;
}
else
{
lean_object* v_reuseFailAlloc_1276_; 
v_reuseFailAlloc_1276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1276_, 0, v_val_1273_);
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
else
{
lean_object* v_a_1278_; lean_object* v___x_1280_; uint8_t v_isShared_1281_; uint8_t v_isSharedCheck_1285_; 
v_a_1278_ = lean_ctor_get(v___x_1262_, 0);
v_isSharedCheck_1285_ = !lean_is_exclusive(v___x_1262_);
if (v_isSharedCheck_1285_ == 0)
{
v___x_1280_ = v___x_1262_;
v_isShared_1281_ = v_isSharedCheck_1285_;
goto v_resetjp_1279_;
}
else
{
lean_inc(v_a_1278_);
lean_dec(v___x_1262_);
v___x_1280_ = lean_box(0);
v_isShared_1281_ = v_isSharedCheck_1285_;
goto v_resetjp_1279_;
}
v_resetjp_1279_:
{
lean_object* v___x_1283_; 
if (v_isShared_1281_ == 0)
{
v___x_1283_ = v___x_1280_;
goto v_reusejp_1282_;
}
else
{
lean_object* v_reuseFailAlloc_1284_; 
v_reuseFailAlloc_1284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1284_, 0, v_a_1278_);
v___x_1283_ = v_reuseFailAlloc_1284_;
goto v_reusejp_1282_;
}
v_reusejp_1282_:
{
return v___x_1283_;
}
}
}
}
}
}
else
{
lean_object* v_a_1286_; lean_object* v___x_1288_; uint8_t v_isShared_1289_; uint8_t v_isSharedCheck_1293_; 
v_a_1286_ = lean_ctor_get(v___x_1252_, 0);
v_isSharedCheck_1293_ = !lean_is_exclusive(v___x_1252_);
if (v_isSharedCheck_1293_ == 0)
{
v___x_1288_ = v___x_1252_;
v_isShared_1289_ = v_isSharedCheck_1293_;
goto v_resetjp_1287_;
}
else
{
lean_inc(v_a_1286_);
lean_dec(v___x_1252_);
v___x_1288_ = lean_box(0);
v_isShared_1289_ = v_isSharedCheck_1293_;
goto v_resetjp_1287_;
}
v_resetjp_1287_:
{
lean_object* v___x_1291_; 
if (v_isShared_1289_ == 0)
{
v___x_1291_ = v___x_1288_;
goto v_reusejp_1290_;
}
else
{
lean_object* v_reuseFailAlloc_1292_; 
v_reuseFailAlloc_1292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1292_, 0, v_a_1286_);
v___x_1291_ = v_reuseFailAlloc_1292_;
goto v_reusejp_1290_;
}
v_reusejp_1290_:
{
return v___x_1291_;
}
}
}
v___jp_1248_:
{
uint8_t v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; 
v___x_1249_ = 0;
v___x_1250_ = lean_box(v___x_1249_);
v___x_1251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1251_, 0, v___x_1250_);
return v___x_1251_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent___boxed(lean_object* v_e_1294_, lean_object* v_parent_1295_, lean_object* v_a_1296_, lean_object* v_a_1297_, lean_object* v_a_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_, lean_object* v_a_1301_, lean_object* v_a_1302_, lean_object* v_a_1303_, lean_object* v_a_1304_, lean_object* v_a_1305_, lean_object* v_a_1306_){
_start:
{
lean_object* v_res_1307_; 
v_res_1307_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent(v_e_1294_, v_parent_1295_, v_a_1296_, v_a_1297_, v_a_1298_, v_a_1299_, v_a_1300_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_, v_a_1305_);
lean_dec(v_a_1305_);
lean_dec_ref(v_a_1304_);
lean_dec(v_a_1303_);
lean_dec_ref(v_a_1302_);
lean_dec(v_a_1301_);
lean_dec_ref(v_a_1300_);
lean_dec(v_a_1299_);
lean_dec_ref(v_a_1298_);
lean_dec(v_a_1297_);
lean_dec(v_a_1296_);
lean_dec_ref(v_e_1294_);
return v_res_1307_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0(lean_object* v_e_1308_, lean_object* v_inst_1309_, lean_object* v_a_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_){
_start:
{
lean_object* v___x_1322_; 
v___x_1322_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg(v_e_1308_, v_a_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_);
return v___x_1322_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___boxed(lean_object* v_e_1323_, lean_object* v_inst_1324_, lean_object* v_a_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_){
_start:
{
lean_object* v_res_1337_; 
v_res_1337_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0(v_e_1323_, v_inst_1324_, v_a_1325_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_);
lean_dec(v___y_1335_);
lean_dec_ref(v___y_1334_);
lean_dec(v___y_1333_);
lean_dec_ref(v___y_1332_);
lean_dec(v___y_1331_);
lean_dec_ref(v___y_1330_);
lean_dec(v___y_1329_);
lean_dec_ref(v___y_1328_);
lean_dec(v___y_1327_);
lean_dec(v___y_1326_);
lean_dec_ref(v_e_1323_);
return v_res_1337_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__0(lean_object* v_msg_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_){
_start:
{
lean_object* v___x_1350_; lean_object* v___x_33112__overap_1351_; lean_object* v___x_1352_; 
v___x_1350_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__1___closed__0, &l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__1___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__1___closed__0);
v___x_33112__overap_1351_ = lean_panic_fn_borrowed(v___x_1350_, v_msg_1338_);
lean_inc(v___y_1348_);
lean_inc_ref(v___y_1347_);
lean_inc(v___y_1346_);
lean_inc_ref(v___y_1345_);
lean_inc(v___y_1344_);
lean_inc_ref(v___y_1343_);
lean_inc(v___y_1342_);
lean_inc_ref(v___y_1341_);
lean_inc(v___y_1340_);
lean_inc(v___y_1339_);
v___x_1352_ = lean_apply_11(v___x_33112__overap_1351_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_, lean_box(0));
return v___x_1352_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__0___boxed(lean_object* v_msg_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_){
_start:
{
lean_object* v_res_1365_; 
v_res_1365_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__0(v_msg_1353_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_, v___y_1362_, v___y_1363_);
lean_dec(v___y_1363_);
lean_dec_ref(v___y_1362_);
lean_dec(v___y_1361_);
lean_dec_ref(v___y_1360_);
lean_dec(v___y_1359_);
lean_dec_ref(v___y_1358_);
lean_dec(v___y_1357_);
lean_dec_ref(v___y_1356_);
lean_dec(v___y_1355_);
lean_dec(v___y_1354_);
return v_res_1365_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__1_spec__1(lean_object* v_msgData_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_){
_start:
{
lean_object* v___x_1372_; lean_object* v_env_1373_; uint8_t v___x_1374_; lean_object* v_env_1375_; lean_object* v___x_1376_; lean_object* v_toCold_1377_; lean_object* v_mctx_1378_; lean_object* v_lctx_1379_; lean_object* v_options_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; 
v___x_1372_ = lean_st_ref_get(v___y_1370_);
v_env_1373_ = lean_ctor_get(v___x_1372_, 0);
lean_inc_ref(v_env_1373_);
lean_dec(v___x_1372_);
v___x_1374_ = 0;
v_env_1375_ = l_Lean_Environment_setRecordingDeps(v_env_1373_, v___x_1374_);
v___x_1376_ = lean_st_ref_get(v___y_1368_);
v_toCold_1377_ = lean_ctor_get(v___y_1369_, 0);
v_mctx_1378_ = lean_ctor_get(v___x_1376_, 0);
lean_inc_ref(v_mctx_1378_);
lean_dec(v___x_1376_);
v_lctx_1379_ = lean_ctor_get(v___y_1367_, 2);
v_options_1380_ = lean_ctor_get(v_toCold_1377_, 2);
lean_inc_ref(v_options_1380_);
lean_inc_ref(v_lctx_1379_);
v___x_1381_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1381_, 0, v_env_1375_);
lean_ctor_set(v___x_1381_, 1, v_mctx_1378_);
lean_ctor_set(v___x_1381_, 2, v_lctx_1379_);
lean_ctor_set(v___x_1381_, 3, v_options_1380_);
v___x_1382_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1382_, 0, v___x_1381_);
lean_ctor_set(v___x_1382_, 1, v_msgData_1366_);
v___x_1383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1383_, 0, v___x_1382_);
return v___x_1383_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__1_spec__1___boxed(lean_object* v_msgData_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_){
_start:
{
lean_object* v_res_1390_; 
v_res_1390_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__1_spec__1(v_msgData_1384_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_);
lean_dec(v___y_1388_);
lean_dec_ref(v___y_1387_);
lean_dec(v___y_1386_);
lean_dec_ref(v___y_1385_);
return v_res_1390_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__1___redArg(lean_object* v_msg_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_){
_start:
{
lean_object* v_ref_1397_; lean_object* v___x_1398_; lean_object* v_a_1399_; lean_object* v___x_1401_; uint8_t v_isShared_1402_; uint8_t v_isSharedCheck_1407_; 
v_ref_1397_ = lean_ctor_get(v___y_1394_, 2);
v___x_1398_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__1_spec__1(v_msg_1391_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_);
v_a_1399_ = lean_ctor_get(v___x_1398_, 0);
v_isSharedCheck_1407_ = !lean_is_exclusive(v___x_1398_);
if (v_isSharedCheck_1407_ == 0)
{
v___x_1401_ = v___x_1398_;
v_isShared_1402_ = v_isSharedCheck_1407_;
goto v_resetjp_1400_;
}
else
{
lean_inc(v_a_1399_);
lean_dec(v___x_1398_);
v___x_1401_ = lean_box(0);
v_isShared_1402_ = v_isSharedCheck_1407_;
goto v_resetjp_1400_;
}
v_resetjp_1400_:
{
lean_object* v___x_1403_; lean_object* v___x_1405_; 
lean_inc(v_ref_1397_);
v___x_1403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1403_, 0, v_ref_1397_);
lean_ctor_set(v___x_1403_, 1, v_a_1399_);
if (v_isShared_1402_ == 0)
{
lean_ctor_set_tag(v___x_1401_, 1);
lean_ctor_set(v___x_1401_, 0, v___x_1403_);
v___x_1405_ = v___x_1401_;
goto v_reusejp_1404_;
}
else
{
lean_object* v_reuseFailAlloc_1406_; 
v_reuseFailAlloc_1406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1406_, 0, v___x_1403_);
v___x_1405_ = v_reuseFailAlloc_1406_;
goto v_reusejp_1404_;
}
v_reusejp_1404_:
{
return v___x_1405_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__1___redArg___boxed(lean_object* v_msg_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_){
_start:
{
lean_object* v_res_1414_; 
v_res_1414_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__1___redArg(v_msg_1408_, v___y_1409_, v___y_1410_, v___y_1411_, v___y_1412_);
lean_dec(v___y_1412_);
lean_dec_ref(v___y_1411_);
lean_dec(v___y_1410_);
lean_dec_ref(v___y_1409_);
return v_res_1414_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__2___redArg(lean_object* v_e_1415_, uint8_t v_a_1416_, lean_object* v_as_1417_, size_t v_sz_1418_, size_t v_i_1419_, uint8_t v_b_1420_, lean_object* v___y_1421_){
_start:
{
uint8_t v___x_1423_; 
v___x_1423_ = lean_usize_dec_lt(v_i_1419_, v_sz_1418_);
if (v___x_1423_ == 0)
{
lean_object* v___x_1424_; lean_object* v___x_1425_; 
v___x_1424_ = lean_box(v_b_1420_);
v___x_1425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1425_, 0, v___x_1424_);
return v___x_1425_;
}
else
{
lean_object* v_a_1426_; lean_object* v___x_1427_; 
v_a_1426_ = lean_array_uget_borrowed(v_as_1417_, v_i_1419_);
v___x_1427_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkChild___redArg(v_e_1415_, v_a_1426_, v___y_1421_);
if (lean_obj_tag(v___x_1427_) == 0)
{
lean_object* v_a_1428_; lean_object* v___x_1430_; uint8_t v_isShared_1431_; uint8_t v_isSharedCheck_1440_; 
v_a_1428_ = lean_ctor_get(v___x_1427_, 0);
v_isSharedCheck_1440_ = !lean_is_exclusive(v___x_1427_);
if (v_isSharedCheck_1440_ == 0)
{
v___x_1430_ = v___x_1427_;
v_isShared_1431_ = v_isSharedCheck_1440_;
goto v_resetjp_1429_;
}
else
{
lean_inc(v_a_1428_);
lean_dec(v___x_1427_);
v___x_1430_ = lean_box(0);
v_isShared_1431_ = v_isSharedCheck_1440_;
goto v_resetjp_1429_;
}
v_resetjp_1429_:
{
uint8_t v___x_1432_; 
v___x_1432_ = lean_unbox(v_a_1428_);
lean_dec(v_a_1428_);
if (v___x_1432_ == 0)
{
size_t v___x_1433_; size_t v___x_1434_; 
lean_del_object(v___x_1430_);
v___x_1433_ = ((size_t)1ULL);
v___x_1434_ = lean_usize_add(v_i_1419_, v___x_1433_);
v_i_1419_ = v___x_1434_;
goto _start;
}
else
{
lean_object* v___x_1436_; lean_object* v___x_1438_; 
v___x_1436_ = lean_box(v_a_1416_);
if (v_isShared_1431_ == 0)
{
lean_ctor_set(v___x_1430_, 0, v___x_1436_);
v___x_1438_ = v___x_1430_;
goto v_reusejp_1437_;
}
else
{
lean_object* v_reuseFailAlloc_1439_; 
v_reuseFailAlloc_1439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1439_, 0, v___x_1436_);
v___x_1438_ = v_reuseFailAlloc_1439_;
goto v_reusejp_1437_;
}
v_reusejp_1437_:
{
return v___x_1438_;
}
}
}
}
else
{
return v___x_1427_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__2___redArg___boxed(lean_object* v_e_1441_, lean_object* v_a_1442_, lean_object* v_as_1443_, lean_object* v_sz_1444_, lean_object* v_i_1445_, lean_object* v_b_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_){
_start:
{
uint8_t v_a_39476__boxed_1449_; size_t v_sz_boxed_1450_; size_t v_i_boxed_1451_; uint8_t v_b_boxed_1452_; lean_object* v_res_1453_; 
v_a_39476__boxed_1449_ = lean_unbox(v_a_1442_);
v_sz_boxed_1450_ = lean_unbox_usize(v_sz_1444_);
lean_dec(v_sz_1444_);
v_i_boxed_1451_ = lean_unbox_usize(v_i_1445_);
lean_dec(v_i_1445_);
v_b_boxed_1452_ = lean_unbox(v_b_1446_);
v_res_1453_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__2___redArg(v_e_1441_, v_a_39476__boxed_1449_, v_as_1443_, v_sz_boxed_1450_, v_i_boxed_1451_, v_b_boxed_1452_, v___y_1447_);
lean_dec(v___y_1447_);
lean_dec_ref(v_as_1443_);
lean_dec_ref(v_e_1441_);
return v_res_1453_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__2(void){
_start:
{
lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; 
v___x_1456_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__1));
v___x_1457_ = lean_unsigned_to_nat(10u);
v___x_1458_ = lean_unsigned_to_nat(118u);
v___x_1459_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__0));
v___x_1460_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__0));
v___x_1461_ = l_mkPanicMessageWithDecl(v___x_1460_, v___x_1459_, v___x_1458_, v___x_1457_, v___x_1456_);
return v___x_1461_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__4(void){
_start:
{
lean_object* v___x_1463_; lean_object* v___x_1464_; 
v___x_1463_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__3));
v___x_1464_ = l_Lean_stringToMessageData(v___x_1463_);
return v___x_1464_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__6(void){
_start:
{
lean_object* v___x_1466_; lean_object* v___x_1467_; 
v___x_1466_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__5));
v___x_1467_ = l_Lean_stringToMessageData(v___x_1466_);
return v___x_1467_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__8(void){
_start:
{
lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; 
v___x_1469_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__7));
v___x_1470_ = lean_unsigned_to_nat(8u);
v___x_1471_ = lean_unsigned_to_nat(100u);
v___x_1472_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__0));
v___x_1473_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__0));
v___x_1474_ = l_mkPanicMessageWithDecl(v___x_1473_, v___x_1472_, v___x_1471_, v___x_1470_, v___x_1469_);
return v___x_1474_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg(lean_object* v_e_1475_, uint8_t v_a_1476_, lean_object* v_as_x27_1477_, lean_object* v_b_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_){
_start:
{
if (lean_obj_tag(v_as_x27_1477_) == 0)
{
lean_object* v___x_1490_; 
lean_dec_ref(v_e_1475_);
v___x_1490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1490_, 0, v_b_1478_);
return v___x_1490_;
}
else
{
lean_object* v_head_1491_; lean_object* v_tail_1492_; lean_object* v___y_1494_; lean_object* v___x_1514_; lean_object* v___y_1516_; lean_object* v___y_1517_; lean_object* v___y_1518_; lean_object* v___y_1519_; lean_object* v___y_1520_; lean_object* v___y_1521_; lean_object* v___y_1522_; lean_object* v___y_1523_; lean_object* v___y_1524_; lean_object* v___y_1525_; lean_object* v___y_1526_; uint8_t v_found_1534_; lean_object* v___y_1535_; lean_object* v___y_1536_; lean_object* v___y_1537_; lean_object* v___y_1538_; lean_object* v___y_1539_; lean_object* v___y_1540_; lean_object* v___y_1541_; lean_object* v___y_1542_; lean_object* v___y_1543_; lean_object* v___y_1544_; lean_object* v___y_1559_; uint8_t v_found_1560_; lean_object* v___y_1561_; lean_object* v___y_1562_; lean_object* v___y_1563_; lean_object* v___y_1564_; lean_object* v___y_1565_; lean_object* v___y_1566_; lean_object* v___y_1567_; lean_object* v___y_1568_; lean_object* v___y_1569_; lean_object* v___y_1570_; lean_object* v___y_1577_; lean_object* v___y_1578_; lean_object* v___y_1579_; lean_object* v___y_1580_; lean_object* v___y_1581_; lean_object* v___y_1582_; lean_object* v___y_1583_; lean_object* v___y_1584_; lean_object* v___y_1585_; lean_object* v___y_1586_; lean_object* v___x_1601_; 
v_head_1491_ = lean_ctor_get(v_as_x27_1477_, 0);
v_tail_1492_ = lean_ctor_get(v_as_x27_1477_, 1);
v___x_1514_ = lean_box(0);
lean_inc(v_head_1491_);
v___x_1601_ = l_Lean_Meta_Grind_useFunCC___redArg(v_head_1491_, v___y_1479_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_);
if (lean_obj_tag(v___x_1601_) == 0)
{
lean_object* v_a_1602_; uint8_t v___x_1650_; 
v_a_1602_ = lean_ctor_get(v___x_1601_, 0);
lean_inc(v_a_1602_);
lean_dec_ref_known(v___x_1601_, 1);
v___x_1650_ = l_Lean_Expr_isApp(v_head_1491_);
if (v___x_1650_ == 0)
{
lean_dec(v_a_1602_);
goto v___jp_1603_;
}
else
{
uint8_t v___x_1651_; 
v___x_1651_ = lean_unbox(v_a_1602_);
lean_dec(v_a_1602_);
if (v___x_1651_ == 0)
{
goto v___jp_1603_;
}
else
{
v_as_x27_1477_ = v_tail_1492_;
v_b_1478_ = v___x_1514_;
goto _start;
}
}
v___jp_1603_:
{
uint8_t v___x_1604_; 
v___x_1604_ = l_Lean_Meta_Grind_isMatchCond(v_head_1491_);
if (v___x_1604_ == 0)
{
lean_object* v_dummy_1605_; lean_object* v_nargs_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; size_t v_sz_1611_; size_t v___x_1612_; lean_object* v___x_1613_; 
v_dummy_1605_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondNestedChild___closed__0, &l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondNestedChild___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondNestedChild___closed__0);
v_nargs_1606_ = l_Lean_Expr_getAppNumArgs(v_head_1491_);
lean_inc(v_nargs_1606_);
v___x_1607_ = lean_mk_array(v_nargs_1606_, v_dummy_1605_);
v___x_1608_ = lean_unsigned_to_nat(1u);
v___x_1609_ = lean_nat_sub(v_nargs_1606_, v___x_1608_);
lean_dec(v_nargs_1606_);
lean_inc(v_head_1491_);
v___x_1610_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_head_1491_, v___x_1607_, v___x_1609_);
v_sz_1611_ = lean_array_size(v___x_1610_);
v___x_1612_ = ((size_t)0ULL);
v___x_1613_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__2___redArg(v_e_1475_, v_a_1476_, v___x_1610_, v_sz_1611_, v___x_1612_, v___x_1604_, v___y_1479_);
lean_dec_ref(v___x_1610_);
if (lean_obj_tag(v___x_1613_) == 0)
{
if (lean_obj_tag(v_head_1491_) == 7)
{
lean_object* v_a_1614_; lean_object* v_binderType_1615_; lean_object* v_body_1616_; lean_object* v___x_1617_; lean_object* v_a_1618_; uint8_t v___x_1619_; 
v_a_1614_ = lean_ctor_get(v___x_1613_, 0);
lean_inc(v_a_1614_);
lean_dec_ref_known(v___x_1613_, 1);
v_binderType_1615_ = lean_ctor_get(v_head_1491_, 1);
v_body_1616_ = lean_ctor_get(v_head_1491_, 2);
v___x_1617_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkChild___redArg(v_e_1475_, v_binderType_1615_, v___y_1479_);
v_a_1618_ = lean_ctor_get(v___x_1617_, 0);
lean_inc(v_a_1618_);
lean_dec_ref(v___x_1617_);
v___x_1619_ = lean_unbox(v_a_1618_);
lean_dec(v_a_1618_);
if (v___x_1619_ == 0)
{
uint8_t v___x_1620_; 
v___x_1620_ = lean_unbox(v_a_1614_);
lean_dec(v_a_1614_);
lean_inc_ref(v_body_1616_);
v___y_1559_ = v_body_1616_;
v_found_1560_ = v___x_1620_;
v___y_1561_ = v___y_1479_;
v___y_1562_ = v___y_1480_;
v___y_1563_ = v___y_1481_;
v___y_1564_ = v___y_1482_;
v___y_1565_ = v___y_1483_;
v___y_1566_ = v___y_1484_;
v___y_1567_ = v___y_1485_;
v___y_1568_ = v___y_1486_;
v___y_1569_ = v___y_1487_;
v___y_1570_ = v___y_1488_;
goto v___jp_1558_;
}
else
{
lean_dec(v_a_1614_);
lean_inc_ref(v_body_1616_);
v___y_1559_ = v_body_1616_;
v_found_1560_ = v_a_1476_;
v___y_1561_ = v___y_1479_;
v___y_1562_ = v___y_1480_;
v___y_1563_ = v___y_1481_;
v___y_1564_ = v___y_1482_;
v___y_1565_ = v___y_1483_;
v___y_1566_ = v___y_1484_;
v___y_1567_ = v___y_1485_;
v___y_1568_ = v___y_1486_;
v___y_1569_ = v___y_1487_;
v___y_1570_ = v___y_1488_;
goto v___jp_1558_;
}
}
else
{
lean_object* v_a_1621_; uint8_t v___x_1622_; 
v_a_1621_ = lean_ctor_get(v___x_1613_, 0);
lean_inc(v_a_1621_);
lean_dec_ref_known(v___x_1613_, 1);
v___x_1622_ = lean_unbox(v_a_1621_);
lean_dec(v_a_1621_);
v_found_1534_ = v___x_1622_;
v___y_1535_ = v___y_1479_;
v___y_1536_ = v___y_1480_;
v___y_1537_ = v___y_1481_;
v___y_1538_ = v___y_1482_;
v___y_1539_ = v___y_1483_;
v___y_1540_ = v___y_1484_;
v___y_1541_ = v___y_1485_;
v___y_1542_ = v___y_1486_;
v___y_1543_ = v___y_1487_;
v___y_1544_ = v___y_1488_;
goto v___jp_1533_;
}
}
else
{
lean_object* v_a_1623_; lean_object* v___x_1625_; uint8_t v_isShared_1626_; uint8_t v_isSharedCheck_1630_; 
lean_dec_ref(v_e_1475_);
v_a_1623_ = lean_ctor_get(v___x_1613_, 0);
v_isSharedCheck_1630_ = !lean_is_exclusive(v___x_1613_);
if (v_isSharedCheck_1630_ == 0)
{
v___x_1625_ = v___x_1613_;
v_isShared_1626_ = v_isSharedCheck_1630_;
goto v_resetjp_1624_;
}
else
{
lean_inc(v_a_1623_);
lean_dec(v___x_1613_);
v___x_1625_ = lean_box(0);
v_isShared_1626_ = v_isSharedCheck_1630_;
goto v_resetjp_1624_;
}
v_resetjp_1624_:
{
lean_object* v___x_1628_; 
if (v_isShared_1626_ == 0)
{
v___x_1628_ = v___x_1625_;
goto v_reusejp_1627_;
}
else
{
lean_object* v_reuseFailAlloc_1629_; 
v_reuseFailAlloc_1629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1629_, 0, v_a_1623_);
v___x_1628_ = v_reuseFailAlloc_1629_;
goto v_reusejp_1627_;
}
v_reusejp_1627_:
{
return v___x_1628_;
}
}
}
}
else
{
lean_object* v___x_1631_; 
lean_inc(v_head_1491_);
v___x_1631_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent(v_e_1475_, v_head_1491_, v___y_1479_, v___y_1480_, v___y_1481_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_);
if (lean_obj_tag(v___x_1631_) == 0)
{
lean_object* v_a_1632_; uint8_t v___x_1633_; 
v_a_1632_ = lean_ctor_get(v___x_1631_, 0);
lean_inc(v_a_1632_);
lean_dec_ref_known(v___x_1631_, 1);
v___x_1633_ = lean_unbox(v_a_1632_);
lean_dec(v_a_1632_);
if (v___x_1633_ == 0)
{
lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; 
v___x_1634_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__4, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__4);
v___x_1635_ = l_Lean_MessageData_ofExpr(v_e_1475_);
v___x_1636_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1636_, 0, v___x_1634_);
lean_ctor_set(v___x_1636_, 1, v___x_1635_);
v___x_1637_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__6, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__6_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__6);
v___x_1638_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1638_, 0, v___x_1636_);
lean_ctor_set(v___x_1638_, 1, v___x_1637_);
lean_inc(v_head_1491_);
v___x_1639_ = l_Lean_MessageData_ofExpr(v_head_1491_);
v___x_1640_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1640_, 0, v___x_1638_);
lean_ctor_set(v___x_1640_, 1, v___x_1639_);
v___x_1641_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__1___redArg(v___x_1640_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_);
return v___x_1641_;
}
else
{
v___y_1577_ = v___y_1479_;
v___y_1578_ = v___y_1480_;
v___y_1579_ = v___y_1481_;
v___y_1580_ = v___y_1482_;
v___y_1581_ = v___y_1483_;
v___y_1582_ = v___y_1484_;
v___y_1583_ = v___y_1485_;
v___y_1584_ = v___y_1486_;
v___y_1585_ = v___y_1487_;
v___y_1586_ = v___y_1488_;
goto v___jp_1576_;
}
}
else
{
lean_object* v_a_1642_; lean_object* v___x_1644_; uint8_t v_isShared_1645_; uint8_t v_isSharedCheck_1649_; 
lean_dec_ref(v_e_1475_);
v_a_1642_ = lean_ctor_get(v___x_1631_, 0);
v_isSharedCheck_1649_ = !lean_is_exclusive(v___x_1631_);
if (v_isSharedCheck_1649_ == 0)
{
v___x_1644_ = v___x_1631_;
v_isShared_1645_ = v_isSharedCheck_1649_;
goto v_resetjp_1643_;
}
else
{
lean_inc(v_a_1642_);
lean_dec(v___x_1631_);
v___x_1644_ = lean_box(0);
v_isShared_1645_ = v_isSharedCheck_1649_;
goto v_resetjp_1643_;
}
v_resetjp_1643_:
{
lean_object* v___x_1647_; 
if (v_isShared_1645_ == 0)
{
v___x_1647_ = v___x_1644_;
goto v_reusejp_1646_;
}
else
{
lean_object* v_reuseFailAlloc_1648_; 
v_reuseFailAlloc_1648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1648_, 0, v_a_1642_);
v___x_1647_ = v_reuseFailAlloc_1648_;
goto v_reusejp_1646_;
}
v_reusejp_1646_:
{
return v___x_1647_;
}
}
}
}
}
}
else
{
lean_object* v_a_1653_; lean_object* v___x_1655_; uint8_t v_isShared_1656_; uint8_t v_isSharedCheck_1660_; 
lean_dec_ref(v_e_1475_);
v_a_1653_ = lean_ctor_get(v___x_1601_, 0);
v_isSharedCheck_1660_ = !lean_is_exclusive(v___x_1601_);
if (v_isSharedCheck_1660_ == 0)
{
v___x_1655_ = v___x_1601_;
v_isShared_1656_ = v_isSharedCheck_1660_;
goto v_resetjp_1654_;
}
else
{
lean_inc(v_a_1653_);
lean_dec(v___x_1601_);
v___x_1655_ = lean_box(0);
v_isShared_1656_ = v_isSharedCheck_1660_;
goto v_resetjp_1654_;
}
v_resetjp_1654_:
{
lean_object* v___x_1658_; 
if (v_isShared_1656_ == 0)
{
v___x_1658_ = v___x_1655_;
goto v_reusejp_1657_;
}
else
{
lean_object* v_reuseFailAlloc_1659_; 
v_reuseFailAlloc_1659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1659_, 0, v_a_1653_);
v___x_1658_ = v_reuseFailAlloc_1659_;
goto v_reusejp_1657_;
}
v_reusejp_1657_:
{
return v___x_1658_;
}
}
}
v___jp_1493_:
{
if (lean_obj_tag(v___y_1494_) == 0)
{
lean_object* v_a_1495_; lean_object* v___x_1497_; uint8_t v_isShared_1498_; uint8_t v_isSharedCheck_1505_; 
v_a_1495_ = lean_ctor_get(v___y_1494_, 0);
v_isSharedCheck_1505_ = !lean_is_exclusive(v___y_1494_);
if (v_isSharedCheck_1505_ == 0)
{
v___x_1497_ = v___y_1494_;
v_isShared_1498_ = v_isSharedCheck_1505_;
goto v_resetjp_1496_;
}
else
{
lean_inc(v_a_1495_);
lean_dec(v___y_1494_);
v___x_1497_ = lean_box(0);
v_isShared_1498_ = v_isSharedCheck_1505_;
goto v_resetjp_1496_;
}
v_resetjp_1496_:
{
if (lean_obj_tag(v_a_1495_) == 0)
{
lean_object* v_a_1499_; lean_object* v___x_1501_; 
lean_dec_ref(v_e_1475_);
v_a_1499_ = lean_ctor_get(v_a_1495_, 0);
lean_inc(v_a_1499_);
lean_dec_ref_known(v_a_1495_, 1);
if (v_isShared_1498_ == 0)
{
lean_ctor_set(v___x_1497_, 0, v_a_1499_);
v___x_1501_ = v___x_1497_;
goto v_reusejp_1500_;
}
else
{
lean_object* v_reuseFailAlloc_1502_; 
v_reuseFailAlloc_1502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1502_, 0, v_a_1499_);
v___x_1501_ = v_reuseFailAlloc_1502_;
goto v_reusejp_1500_;
}
v_reusejp_1500_:
{
return v___x_1501_;
}
}
else
{
lean_object* v_a_1503_; 
lean_del_object(v___x_1497_);
v_a_1503_ = lean_ctor_get(v_a_1495_, 0);
lean_inc(v_a_1503_);
lean_dec_ref_known(v_a_1495_, 1);
v_as_x27_1477_ = v_tail_1492_;
v_b_1478_ = v_a_1503_;
goto _start;
}
}
}
else
{
lean_object* v_a_1506_; lean_object* v___x_1508_; uint8_t v_isShared_1509_; uint8_t v_isSharedCheck_1513_; 
lean_dec_ref(v_e_1475_);
v_a_1506_ = lean_ctor_get(v___y_1494_, 0);
v_isSharedCheck_1513_ = !lean_is_exclusive(v___y_1494_);
if (v_isSharedCheck_1513_ == 0)
{
v___x_1508_ = v___y_1494_;
v_isShared_1509_ = v_isSharedCheck_1513_;
goto v_resetjp_1507_;
}
else
{
lean_inc(v_a_1506_);
lean_dec(v___y_1494_);
v___x_1508_ = lean_box(0);
v_isShared_1509_ = v_isSharedCheck_1513_;
goto v_resetjp_1507_;
}
v_resetjp_1507_:
{
lean_object* v___x_1511_; 
if (v_isShared_1509_ == 0)
{
v___x_1511_ = v___x_1508_;
goto v_reusejp_1510_;
}
else
{
lean_object* v_reuseFailAlloc_1512_; 
v_reuseFailAlloc_1512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1512_, 0, v_a_1506_);
v___x_1511_ = v_reuseFailAlloc_1512_;
goto v_reusejp_1510_;
}
v_reusejp_1510_:
{
return v___x_1511_;
}
}
}
}
v___jp_1515_:
{
lean_object* v___x_1527_; lean_object* v_a_1528_; uint8_t v___x_1529_; 
v___x_1527_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkChild___redArg(v_e_1475_, v___y_1516_, v___y_1517_);
lean_dec_ref(v___y_1516_);
v_a_1528_ = lean_ctor_get(v___x_1527_, 0);
lean_inc(v_a_1528_);
lean_dec_ref(v___x_1527_);
v___x_1529_ = lean_unbox(v_a_1528_);
lean_dec(v_a_1528_);
if (v___x_1529_ == 0)
{
lean_object* v___x_1530_; lean_object* v___x_1531_; 
v___x_1530_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__2, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__2_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__2);
v___x_1531_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__0(v___x_1530_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_, v___y_1525_, v___y_1526_);
v___y_1494_ = v___x_1531_;
goto v___jp_1493_;
}
else
{
v_as_x27_1477_ = v_tail_1492_;
v_b_1478_ = v___x_1514_;
goto _start;
}
}
v___jp_1533_:
{
if (v_found_1534_ == 0)
{
lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v_a_1547_; uint8_t v___x_1548_; 
v___x_1545_ = l_Lean_Expr_getAppFn(v_head_1491_);
v___x_1546_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkChild___redArg(v_e_1475_, v___x_1545_, v___y_1535_);
v_a_1547_ = lean_ctor_get(v___x_1546_, 0);
lean_inc(v_a_1547_);
lean_dec_ref(v___x_1546_);
v___x_1548_ = lean_unbox(v_a_1547_);
lean_dec(v_a_1547_);
if (v___x_1548_ == 0)
{
lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; 
lean_dec_ref(v___x_1545_);
v___x_1549_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__4, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__4);
v___x_1550_ = l_Lean_MessageData_ofExpr(v_e_1475_);
v___x_1551_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1551_, 0, v___x_1549_);
lean_ctor_set(v___x_1551_, 1, v___x_1550_);
v___x_1552_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__6, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__6_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__6);
v___x_1553_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1553_, 0, v___x_1551_);
lean_ctor_set(v___x_1553_, 1, v___x_1552_);
lean_inc(v_head_1491_);
v___x_1554_ = l_Lean_MessageData_ofExpr(v_head_1491_);
v___x_1555_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1555_, 0, v___x_1553_);
lean_ctor_set(v___x_1555_, 1, v___x_1554_);
v___x_1556_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__1___redArg(v___x_1555_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_);
return v___x_1556_;
}
else
{
v___y_1516_ = v___x_1545_;
v___y_1517_ = v___y_1535_;
v___y_1518_ = v___y_1536_;
v___y_1519_ = v___y_1537_;
v___y_1520_ = v___y_1538_;
v___y_1521_ = v___y_1539_;
v___y_1522_ = v___y_1540_;
v___y_1523_ = v___y_1541_;
v___y_1524_ = v___y_1542_;
v___y_1525_ = v___y_1543_;
v___y_1526_ = v___y_1544_;
goto v___jp_1515_;
}
}
else
{
v_as_x27_1477_ = v_tail_1492_;
v_b_1478_ = v___x_1514_;
goto _start;
}
}
v___jp_1558_:
{
uint8_t v___x_1571_; 
v___x_1571_ = l_Lean_Expr_hasLooseBVars(v___y_1559_);
if (v___x_1571_ == 0)
{
lean_object* v___x_1572_; lean_object* v_a_1573_; uint8_t v___x_1574_; 
v___x_1572_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkChild___redArg(v_e_1475_, v___y_1559_, v___y_1561_);
lean_dec_ref(v___y_1559_);
v_a_1573_ = lean_ctor_get(v___x_1572_, 0);
lean_inc(v_a_1573_);
lean_dec_ref(v___x_1572_);
v___x_1574_ = lean_unbox(v_a_1573_);
lean_dec(v_a_1573_);
if (v___x_1574_ == 0)
{
v_found_1534_ = v_found_1560_;
v___y_1535_ = v___y_1561_;
v___y_1536_ = v___y_1562_;
v___y_1537_ = v___y_1563_;
v___y_1538_ = v___y_1564_;
v___y_1539_ = v___y_1565_;
v___y_1540_ = v___y_1566_;
v___y_1541_ = v___y_1567_;
v___y_1542_ = v___y_1568_;
v___y_1543_ = v___y_1569_;
v___y_1544_ = v___y_1570_;
goto v___jp_1533_;
}
else
{
v_as_x27_1477_ = v_tail_1492_;
v_b_1478_ = v___x_1514_;
goto _start;
}
}
else
{
lean_dec_ref(v___y_1559_);
v_found_1534_ = v_found_1560_;
v___y_1535_ = v___y_1561_;
v___y_1536_ = v___y_1562_;
v___y_1537_ = v___y_1563_;
v___y_1538_ = v___y_1564_;
v___y_1539_ = v___y_1565_;
v___y_1540_ = v___y_1566_;
v___y_1541_ = v___y_1567_;
v___y_1542_ = v___y_1568_;
v___y_1543_ = v___y_1569_;
v___y_1544_ = v___y_1570_;
goto v___jp_1533_;
}
}
v___jp_1576_:
{
lean_object* v___x_1587_; 
lean_inc(v_head_1491_);
v___x_1587_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent(v_e_1475_, v_head_1491_, v___y_1577_, v___y_1578_, v___y_1579_, v___y_1580_, v___y_1581_, v___y_1582_, v___y_1583_, v___y_1584_, v___y_1585_, v___y_1586_);
if (lean_obj_tag(v___x_1587_) == 0)
{
lean_object* v_a_1588_; uint8_t v___x_1589_; 
v_a_1588_ = lean_ctor_get(v___x_1587_, 0);
lean_inc(v_a_1588_);
lean_dec_ref_known(v___x_1587_, 1);
v___x_1589_ = lean_unbox(v_a_1588_);
lean_dec(v_a_1588_);
if (v___x_1589_ == 0)
{
lean_object* v___x_1590_; lean_object* v___x_1591_; 
v___x_1590_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__8, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__8_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__8);
v___x_1591_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__0(v___x_1590_, v___y_1577_, v___y_1578_, v___y_1579_, v___y_1580_, v___y_1581_, v___y_1582_, v___y_1583_, v___y_1584_, v___y_1585_, v___y_1586_);
v___y_1494_ = v___x_1591_;
goto v___jp_1493_;
}
else
{
v_as_x27_1477_ = v_tail_1492_;
v_b_1478_ = v___x_1514_;
goto _start;
}
}
else
{
lean_object* v_a_1593_; lean_object* v___x_1595_; uint8_t v_isShared_1596_; uint8_t v_isSharedCheck_1600_; 
lean_dec_ref(v_e_1475_);
v_a_1593_ = lean_ctor_get(v___x_1587_, 0);
v_isSharedCheck_1600_ = !lean_is_exclusive(v___x_1587_);
if (v_isSharedCheck_1600_ == 0)
{
v___x_1595_ = v___x_1587_;
v_isShared_1596_ = v_isSharedCheck_1600_;
goto v_resetjp_1594_;
}
else
{
lean_inc(v_a_1593_);
lean_dec(v___x_1587_);
v___x_1595_ = lean_box(0);
v_isShared_1596_ = v_isSharedCheck_1600_;
goto v_resetjp_1594_;
}
v_resetjp_1594_:
{
lean_object* v___x_1598_; 
if (v_isShared_1596_ == 0)
{
v___x_1598_ = v___x_1595_;
goto v_reusejp_1597_;
}
else
{
lean_object* v_reuseFailAlloc_1599_; 
v_reuseFailAlloc_1599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1599_, 0, v_a_1593_);
v___x_1598_ = v_reuseFailAlloc_1599_;
goto v_reusejp_1597_;
}
v_reusejp_1597_:
{
return v___x_1598_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___boxed(lean_object* v_e_1661_, lean_object* v_a_1662_, lean_object* v_as_x27_1663_, lean_object* v_b_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_){
_start:
{
uint8_t v_a_39572__boxed_1676_; lean_object* v_res_1677_; 
v_a_39572__boxed_1676_ = lean_unbox(v_a_1662_);
v_res_1677_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg(v_e_1661_, v_a_39572__boxed_1676_, v_as_x27_1663_, v_b_1664_, v___y_1665_, v___y_1666_, v___y_1667_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_, v___y_1674_);
lean_dec(v___y_1674_);
lean_dec_ref(v___y_1673_);
lean_dec(v___y_1672_);
lean_dec_ref(v___y_1671_);
lean_dec(v___y_1670_);
lean_dec_ref(v___y_1669_);
lean_dec(v___y_1668_);
lean_dec_ref(v___y_1667_);
lean_dec(v___y_1666_);
lean_dec(v___y_1665_);
lean_dec(v_as_x27_1663_);
return v_res_1677_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents___closed__1(void){
_start:
{
lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; 
v___x_1679_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents___closed__0));
v___x_1680_ = lean_unsigned_to_nat(6u);
v___x_1681_ = lean_unsigned_to_nat(121u);
v___x_1682_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__0));
v___x_1683_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__0));
v___x_1684_ = l_mkPanicMessageWithDecl(v___x_1683_, v___x_1682_, v___x_1681_, v___x_1680_, v___x_1679_);
return v___x_1684_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents(lean_object* v_e_1685_, lean_object* v_a_1686_, lean_object* v_a_1687_, lean_object* v_a_1688_, lean_object* v_a_1689_, lean_object* v_a_1690_, lean_object* v_a_1691_, lean_object* v_a_1692_, lean_object* v_a_1693_, lean_object* v_a_1694_, lean_object* v_a_1695_){
_start:
{
lean_object* v___x_1697_; 
v___x_1697_ = l_Lean_Meta_Grind_isRoot___redArg(v_e_1685_, v_a_1686_);
if (lean_obj_tag(v___x_1697_) == 0)
{
lean_object* v_a_1698_; uint8_t v___x_1699_; 
v_a_1698_ = lean_ctor_get(v___x_1697_, 0);
lean_inc(v_a_1698_);
lean_dec_ref_known(v___x_1697_, 1);
v___x_1699_ = lean_unbox(v_a_1698_);
if (v___x_1699_ == 0)
{
lean_object* v___x_1700_; 
lean_dec(v_a_1698_);
v___x_1700_ = l_Lean_Meta_Grind_getParents___redArg(v_e_1685_, v_a_1686_);
lean_dec_ref(v_e_1685_);
if (lean_obj_tag(v___x_1700_) == 0)
{
lean_object* v_a_1701_; lean_object* v___x_1703_; uint8_t v_isShared_1704_; uint8_t v_isSharedCheck_1712_; 
v_a_1701_ = lean_ctor_get(v___x_1700_, 0);
v_isSharedCheck_1712_ = !lean_is_exclusive(v___x_1700_);
if (v_isSharedCheck_1712_ == 0)
{
v___x_1703_ = v___x_1700_;
v_isShared_1704_ = v_isSharedCheck_1712_;
goto v_resetjp_1702_;
}
else
{
lean_inc(v_a_1701_);
lean_dec(v___x_1700_);
v___x_1703_ = lean_box(0);
v_isShared_1704_ = v_isSharedCheck_1712_;
goto v_resetjp_1702_;
}
v_resetjp_1702_:
{
uint8_t v___x_1705_; 
v___x_1705_ = l_Lean_Meta_Grind_ParentSet_isEmpty(v_a_1701_);
lean_dec(v_a_1701_);
if (v___x_1705_ == 0)
{
lean_object* v___x_1706_; lean_object* v___x_1707_; 
lean_del_object(v___x_1703_);
v___x_1706_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents___closed__1, &l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents___closed__1);
v___x_1707_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__4(v___x_1706_, v_a_1686_, v_a_1687_, v_a_1688_, v_a_1689_, v_a_1690_, v_a_1691_, v_a_1692_, v_a_1693_, v_a_1694_, v_a_1695_);
return v___x_1707_;
}
else
{
lean_object* v___x_1708_; lean_object* v___x_1710_; 
v___x_1708_ = lean_box(0);
if (v_isShared_1704_ == 0)
{
lean_ctor_set(v___x_1703_, 0, v___x_1708_);
v___x_1710_ = v___x_1703_;
goto v_reusejp_1709_;
}
else
{
lean_object* v_reuseFailAlloc_1711_; 
v_reuseFailAlloc_1711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1711_, 0, v___x_1708_);
v___x_1710_ = v_reuseFailAlloc_1711_;
goto v_reusejp_1709_;
}
v_reusejp_1709_:
{
return v___x_1710_;
}
}
}
}
else
{
lean_object* v_a_1713_; lean_object* v___x_1715_; uint8_t v_isShared_1716_; uint8_t v_isSharedCheck_1720_; 
v_a_1713_ = lean_ctor_get(v___x_1700_, 0);
v_isSharedCheck_1720_ = !lean_is_exclusive(v___x_1700_);
if (v_isSharedCheck_1720_ == 0)
{
v___x_1715_ = v___x_1700_;
v_isShared_1716_ = v_isSharedCheck_1720_;
goto v_resetjp_1714_;
}
else
{
lean_inc(v_a_1713_);
lean_dec(v___x_1700_);
v___x_1715_ = lean_box(0);
v_isShared_1716_ = v_isSharedCheck_1720_;
goto v_resetjp_1714_;
}
v_resetjp_1714_:
{
lean_object* v___x_1718_; 
if (v_isShared_1716_ == 0)
{
v___x_1718_ = v___x_1715_;
goto v_reusejp_1717_;
}
else
{
lean_object* v_reuseFailAlloc_1719_; 
v_reuseFailAlloc_1719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1719_, 0, v_a_1713_);
v___x_1718_ = v_reuseFailAlloc_1719_;
goto v_reusejp_1717_;
}
v_reusejp_1717_:
{
return v___x_1718_;
}
}
}
}
else
{
lean_object* v___x_1721_; 
v___x_1721_ = l_Lean_Meta_Grind_getParents___redArg(v_e_1685_, v_a_1686_);
if (lean_obj_tag(v___x_1721_) == 0)
{
lean_object* v_a_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; uint8_t v___x_1725_; lean_object* v___x_1726_; 
v_a_1722_ = lean_ctor_get(v___x_1721_, 0);
lean_inc(v_a_1722_);
lean_dec_ref_known(v___x_1721_, 1);
v___x_1723_ = l_Lean_Meta_Grind_ParentSet_elems(v_a_1722_);
lean_dec(v_a_1722_);
v___x_1724_ = lean_box(0);
v___x_1725_ = lean_unbox(v_a_1698_);
lean_dec(v_a_1698_);
v___x_1726_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg(v_e_1685_, v___x_1725_, v___x_1723_, v___x_1724_, v_a_1686_, v_a_1687_, v_a_1688_, v_a_1689_, v_a_1690_, v_a_1691_, v_a_1692_, v_a_1693_, v_a_1694_, v_a_1695_);
lean_dec(v___x_1723_);
if (lean_obj_tag(v___x_1726_) == 0)
{
lean_object* v___x_1728_; uint8_t v_isShared_1729_; uint8_t v_isSharedCheck_1733_; 
v_isSharedCheck_1733_ = !lean_is_exclusive(v___x_1726_);
if (v_isSharedCheck_1733_ == 0)
{
lean_object* v_unused_1734_; 
v_unused_1734_ = lean_ctor_get(v___x_1726_, 0);
lean_dec(v_unused_1734_);
v___x_1728_ = v___x_1726_;
v_isShared_1729_ = v_isSharedCheck_1733_;
goto v_resetjp_1727_;
}
else
{
lean_dec(v___x_1726_);
v___x_1728_ = lean_box(0);
v_isShared_1729_ = v_isSharedCheck_1733_;
goto v_resetjp_1727_;
}
v_resetjp_1727_:
{
lean_object* v___x_1731_; 
if (v_isShared_1729_ == 0)
{
lean_ctor_set(v___x_1728_, 0, v___x_1724_);
v___x_1731_ = v___x_1728_;
goto v_reusejp_1730_;
}
else
{
lean_object* v_reuseFailAlloc_1732_; 
v_reuseFailAlloc_1732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1732_, 0, v___x_1724_);
v___x_1731_ = v_reuseFailAlloc_1732_;
goto v_reusejp_1730_;
}
v_reusejp_1730_:
{
return v___x_1731_;
}
}
}
else
{
return v___x_1726_;
}
}
else
{
lean_object* v_a_1735_; lean_object* v___x_1737_; uint8_t v_isShared_1738_; uint8_t v_isSharedCheck_1742_; 
lean_dec(v_a_1698_);
lean_dec_ref(v_e_1685_);
v_a_1735_ = lean_ctor_get(v___x_1721_, 0);
v_isSharedCheck_1742_ = !lean_is_exclusive(v___x_1721_);
if (v_isSharedCheck_1742_ == 0)
{
v___x_1737_ = v___x_1721_;
v_isShared_1738_ = v_isSharedCheck_1742_;
goto v_resetjp_1736_;
}
else
{
lean_inc(v_a_1735_);
lean_dec(v___x_1721_);
v___x_1737_ = lean_box(0);
v_isShared_1738_ = v_isSharedCheck_1742_;
goto v_resetjp_1736_;
}
v_resetjp_1736_:
{
lean_object* v___x_1740_; 
if (v_isShared_1738_ == 0)
{
v___x_1740_ = v___x_1737_;
goto v_reusejp_1739_;
}
else
{
lean_object* v_reuseFailAlloc_1741_; 
v_reuseFailAlloc_1741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1741_, 0, v_a_1735_);
v___x_1740_ = v_reuseFailAlloc_1741_;
goto v_reusejp_1739_;
}
v_reusejp_1739_:
{
return v___x_1740_;
}
}
}
}
}
else
{
lean_object* v_a_1743_; lean_object* v___x_1745_; uint8_t v_isShared_1746_; uint8_t v_isSharedCheck_1750_; 
lean_dec_ref(v_e_1685_);
v_a_1743_ = lean_ctor_get(v___x_1697_, 0);
v_isSharedCheck_1750_ = !lean_is_exclusive(v___x_1697_);
if (v_isSharedCheck_1750_ == 0)
{
v___x_1745_ = v___x_1697_;
v_isShared_1746_ = v_isSharedCheck_1750_;
goto v_resetjp_1744_;
}
else
{
lean_inc(v_a_1743_);
lean_dec(v___x_1697_);
v___x_1745_ = lean_box(0);
v_isShared_1746_ = v_isSharedCheck_1750_;
goto v_resetjp_1744_;
}
v_resetjp_1744_:
{
lean_object* v___x_1748_; 
if (v_isShared_1746_ == 0)
{
v___x_1748_ = v___x_1745_;
goto v_reusejp_1747_;
}
else
{
lean_object* v_reuseFailAlloc_1749_; 
v_reuseFailAlloc_1749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1749_, 0, v_a_1743_);
v___x_1748_ = v_reuseFailAlloc_1749_;
goto v_reusejp_1747_;
}
v_reusejp_1747_:
{
return v___x_1748_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents___boxed(lean_object* v_e_1751_, lean_object* v_a_1752_, lean_object* v_a_1753_, lean_object* v_a_1754_, lean_object* v_a_1755_, lean_object* v_a_1756_, lean_object* v_a_1757_, lean_object* v_a_1758_, lean_object* v_a_1759_, lean_object* v_a_1760_, lean_object* v_a_1761_, lean_object* v_a_1762_){
_start:
{
lean_object* v_res_1763_; 
v_res_1763_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents(v_e_1751_, v_a_1752_, v_a_1753_, v_a_1754_, v_a_1755_, v_a_1756_, v_a_1757_, v_a_1758_, v_a_1759_, v_a_1760_, v_a_1761_);
lean_dec(v_a_1761_);
lean_dec_ref(v_a_1760_);
lean_dec(v_a_1759_);
lean_dec_ref(v_a_1758_);
lean_dec(v_a_1757_);
lean_dec_ref(v_a_1756_);
lean_dec(v_a_1755_);
lean_dec_ref(v_a_1754_);
lean_dec(v_a_1753_);
lean_dec(v_a_1752_);
return v_res_1763_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__1(lean_object* v_00_u03b1_1764_, lean_object* v_msg_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_){
_start:
{
lean_object* v___x_1777_; 
v___x_1777_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__1___redArg(v_msg_1765_, v___y_1772_, v___y_1773_, v___y_1774_, v___y_1775_);
return v___x_1777_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__1___boxed(lean_object* v_00_u03b1_1778_, lean_object* v_msg_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_){
_start:
{
lean_object* v_res_1791_; 
v_res_1791_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__1(v_00_u03b1_1778_, v_msg_1779_, v___y_1780_, v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_, v___y_1785_, v___y_1786_, v___y_1787_, v___y_1788_, v___y_1789_);
lean_dec(v___y_1789_);
lean_dec_ref(v___y_1788_);
lean_dec(v___y_1787_);
lean_dec_ref(v___y_1786_);
lean_dec(v___y_1785_);
lean_dec_ref(v___y_1784_);
lean_dec(v___y_1783_);
lean_dec_ref(v___y_1782_);
lean_dec(v___y_1781_);
lean_dec(v___y_1780_);
return v_res_1791_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__2(lean_object* v_e_1792_, uint8_t v_a_1793_, lean_object* v_as_1794_, size_t v_sz_1795_, size_t v_i_1796_, uint8_t v_b_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_){
_start:
{
lean_object* v___x_1809_; 
v___x_1809_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__2___redArg(v_e_1792_, v_a_1793_, v_as_1794_, v_sz_1795_, v_i_1796_, v_b_1797_, v___y_1798_);
return v___x_1809_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__2___boxed(lean_object** _args){
lean_object* v_e_1810_ = _args[0];
lean_object* v_a_1811_ = _args[1];
lean_object* v_as_1812_ = _args[2];
lean_object* v_sz_1813_ = _args[3];
lean_object* v_i_1814_ = _args[4];
lean_object* v_b_1815_ = _args[5];
lean_object* v___y_1816_ = _args[6];
lean_object* v___y_1817_ = _args[7];
lean_object* v___y_1818_ = _args[8];
lean_object* v___y_1819_ = _args[9];
lean_object* v___y_1820_ = _args[10];
lean_object* v___y_1821_ = _args[11];
lean_object* v___y_1822_ = _args[12];
lean_object* v___y_1823_ = _args[13];
lean_object* v___y_1824_ = _args[14];
lean_object* v___y_1825_ = _args[15];
lean_object* v___y_1826_ = _args[16];
_start:
{
uint8_t v_a_40142__boxed_1827_; size_t v_sz_boxed_1828_; size_t v_i_boxed_1829_; uint8_t v_b_boxed_1830_; lean_object* v_res_1831_; 
v_a_40142__boxed_1827_ = lean_unbox(v_a_1811_);
v_sz_boxed_1828_ = lean_unbox_usize(v_sz_1813_);
lean_dec(v_sz_1813_);
v_i_boxed_1829_ = lean_unbox_usize(v_i_1814_);
lean_dec(v_i_1814_);
v_b_boxed_1830_ = lean_unbox(v_b_1815_);
v_res_1831_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__2(v_e_1810_, v_a_40142__boxed_1827_, v_as_1812_, v_sz_boxed_1828_, v_i_boxed_1829_, v_b_boxed_1830_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_, v___y_1820_, v___y_1821_, v___y_1822_, v___y_1823_, v___y_1824_, v___y_1825_);
lean_dec(v___y_1825_);
lean_dec_ref(v___y_1824_);
lean_dec(v___y_1823_);
lean_dec_ref(v___y_1822_);
lean_dec(v___y_1821_);
lean_dec_ref(v___y_1820_);
lean_dec(v___y_1819_);
lean_dec_ref(v___y_1818_);
lean_dec(v___y_1817_);
lean_dec(v___y_1816_);
lean_dec_ref(v_as_1812_);
lean_dec_ref(v_e_1810_);
return v_res_1831_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3(lean_object* v_e_1832_, uint8_t v_a_1833_, lean_object* v_as_1834_, lean_object* v_as_x27_1835_, lean_object* v_b_1836_, lean_object* v_a_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_){
_start:
{
lean_object* v___x_1849_; 
v___x_1849_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg(v_e_1832_, v_a_1833_, v_as_x27_1835_, v_b_1836_, v___y_1838_, v___y_1839_, v___y_1840_, v___y_1841_, v___y_1842_, v___y_1843_, v___y_1844_, v___y_1845_, v___y_1846_, v___y_1847_);
return v___x_1849_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___boxed(lean_object** _args){
lean_object* v_e_1850_ = _args[0];
lean_object* v_a_1851_ = _args[1];
lean_object* v_as_1852_ = _args[2];
lean_object* v_as_x27_1853_ = _args[3];
lean_object* v_b_1854_ = _args[4];
lean_object* v_a_1855_ = _args[5];
lean_object* v___y_1856_ = _args[6];
lean_object* v___y_1857_ = _args[7];
lean_object* v___y_1858_ = _args[8];
lean_object* v___y_1859_ = _args[9];
lean_object* v___y_1860_ = _args[10];
lean_object* v___y_1861_ = _args[11];
lean_object* v___y_1862_ = _args[12];
lean_object* v___y_1863_ = _args[13];
lean_object* v___y_1864_ = _args[14];
lean_object* v___y_1865_ = _args[15];
lean_object* v___y_1866_ = _args[16];
_start:
{
uint8_t v_a_40180__boxed_1867_; lean_object* v_res_1868_; 
v_a_40180__boxed_1867_ = lean_unbox(v_a_1851_);
v_res_1868_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3(v_e_1850_, v_a_40180__boxed_1867_, v_as_1852_, v_as_x27_1853_, v_b_1854_, v_a_1855_, v___y_1856_, v___y_1857_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_, v___y_1865_);
lean_dec(v___y_1865_);
lean_dec_ref(v___y_1864_);
lean_dec(v___y_1863_);
lean_dec_ref(v___y_1862_);
lean_dec(v___y_1861_);
lean_dec_ref(v___y_1860_);
lean_dec(v___y_1859_);
lean_dec_ref(v___y_1858_);
lean_dec(v___y_1857_);
lean_dec(v___y_1856_);
lean_dec(v_as_x27_1853_);
lean_dec(v_as_1852_);
return v_res_1868_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; 
v___x_1871_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg___closed__1));
v___x_1872_ = lean_unsigned_to_nat(6u);
v___x_1873_ = lean_unsigned_to_nat(132u);
v___x_1874_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg___closed__0));
v___x_1875_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__0));
v___x_1876_ = l_mkPanicMessageWithDecl(v___x_1875_, v___x_1874_, v___x_1873_, v___x_1872_, v___x_1871_);
return v___x_1876_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; 
v___x_1878_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg___closed__3));
v___x_1879_ = lean_unsigned_to_nat(6u);
v___x_1880_ = lean_unsigned_to_nat(130u);
v___x_1881_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg___closed__0));
v___x_1882_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__0));
v___x_1883_ = l_mkPanicMessageWithDecl(v___x_1882_, v___x_1881_, v___x_1880_, v___x_1879_, v___x_1878_);
return v___x_1883_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg(lean_object* v_upperBound_1884_, lean_object* v_a_1885_, lean_object* v___x_1886_, lean_object* v_a_1887_, lean_object* v_b_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_){
_start:
{
lean_object* v_a_1901_; lean_object* v___y_1906_; uint8_t v___x_1925_; 
v___x_1925_ = lean_nat_dec_lt(v_a_1887_, v_upperBound_1884_);
if (v___x_1925_ == 0)
{
lean_object* v___x_1926_; 
lean_dec(v_a_1887_);
v___x_1926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1926_, 0, v_b_1888_);
return v___x_1926_;
}
else
{
lean_object* v___x_1927_; lean_object* v___x_1928_; size_t v___x_1929_; size_t v___x_1930_; uint8_t v___x_1931_; 
v___x_1927_ = l_Lean_instInhabitedExpr;
v___x_1928_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1927_, v_a_1885_, v_a_1887_);
v___x_1929_ = lean_ptr_addr(v___x_1886_);
v___x_1930_ = lean_ptr_addr(v___x_1928_);
v___x_1931_ = lean_usize_dec_eq(v___x_1929_, v___x_1930_);
if (v___x_1931_ == 0)
{
uint8_t v___x_1932_; 
v___x_1932_ = lean_expr_equal(v___x_1886_, v___x_1928_);
lean_dec(v___x_1928_);
if (v___x_1932_ == 0)
{
lean_object* v___x_1933_; 
v___x_1933_ = lean_box(0);
v_a_1901_ = v___x_1933_;
goto v___jp_1900_;
}
else
{
lean_object* v___x_1934_; lean_object* v___x_1935_; 
v___x_1934_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg___closed__2, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg___closed__2_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg___closed__2);
v___x_1935_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__0(v___x_1934_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_, v___y_1896_, v___y_1897_, v___y_1898_);
v___y_1906_ = v___x_1935_;
goto v___jp_1905_;
}
}
else
{
lean_object* v___x_1936_; lean_object* v___x_1937_; 
lean_dec(v___x_1928_);
v___x_1936_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg___closed__4, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg___closed__4_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg___closed__4);
v___x_1937_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__0(v___x_1936_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_, v___y_1896_, v___y_1897_, v___y_1898_);
v___y_1906_ = v___x_1937_;
goto v___jp_1905_;
}
}
v___jp_1900_:
{
lean_object* v___x_1902_; lean_object* v___x_1903_; 
v___x_1902_ = lean_unsigned_to_nat(1u);
v___x_1903_ = lean_nat_add(v_a_1887_, v___x_1902_);
lean_dec(v_a_1887_);
v_a_1887_ = v___x_1903_;
v_b_1888_ = v_a_1901_;
goto _start;
}
v___jp_1905_:
{
if (lean_obj_tag(v___y_1906_) == 0)
{
lean_object* v_a_1907_; lean_object* v___x_1909_; uint8_t v_isShared_1910_; uint8_t v_isSharedCheck_1916_; 
v_a_1907_ = lean_ctor_get(v___y_1906_, 0);
v_isSharedCheck_1916_ = !lean_is_exclusive(v___y_1906_);
if (v_isSharedCheck_1916_ == 0)
{
v___x_1909_ = v___y_1906_;
v_isShared_1910_ = v_isSharedCheck_1916_;
goto v_resetjp_1908_;
}
else
{
lean_inc(v_a_1907_);
lean_dec(v___y_1906_);
v___x_1909_ = lean_box(0);
v_isShared_1910_ = v_isSharedCheck_1916_;
goto v_resetjp_1908_;
}
v_resetjp_1908_:
{
if (lean_obj_tag(v_a_1907_) == 0)
{
lean_object* v_a_1911_; lean_object* v___x_1913_; 
lean_dec(v_a_1887_);
v_a_1911_ = lean_ctor_get(v_a_1907_, 0);
lean_inc(v_a_1911_);
lean_dec_ref_known(v_a_1907_, 1);
if (v_isShared_1910_ == 0)
{
lean_ctor_set(v___x_1909_, 0, v_a_1911_);
v___x_1913_ = v___x_1909_;
goto v_reusejp_1912_;
}
else
{
lean_object* v_reuseFailAlloc_1914_; 
v_reuseFailAlloc_1914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1914_, 0, v_a_1911_);
v___x_1913_ = v_reuseFailAlloc_1914_;
goto v_reusejp_1912_;
}
v_reusejp_1912_:
{
return v___x_1913_;
}
}
else
{
lean_object* v_a_1915_; 
lean_del_object(v___x_1909_);
v_a_1915_ = lean_ctor_get(v_a_1907_, 0);
lean_inc(v_a_1915_);
lean_dec_ref_known(v_a_1907_, 1);
v_a_1901_ = v_a_1915_;
goto v___jp_1900_;
}
}
}
else
{
lean_object* v_a_1917_; lean_object* v___x_1919_; uint8_t v_isShared_1920_; uint8_t v_isSharedCheck_1924_; 
lean_dec(v_a_1887_);
v_a_1917_ = lean_ctor_get(v___y_1906_, 0);
v_isSharedCheck_1924_ = !lean_is_exclusive(v___y_1906_);
if (v_isSharedCheck_1924_ == 0)
{
v___x_1919_ = v___y_1906_;
v_isShared_1920_ = v_isSharedCheck_1924_;
goto v_resetjp_1918_;
}
else
{
lean_inc(v_a_1917_);
lean_dec(v___y_1906_);
v___x_1919_ = lean_box(0);
v_isShared_1920_ = v_isSharedCheck_1924_;
goto v_resetjp_1918_;
}
v_resetjp_1918_:
{
lean_object* v___x_1922_; 
if (v_isShared_1920_ == 0)
{
v___x_1922_ = v___x_1919_;
goto v_reusejp_1921_;
}
else
{
lean_object* v_reuseFailAlloc_1923_; 
v_reuseFailAlloc_1923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1923_, 0, v_a_1917_);
v___x_1922_ = v_reuseFailAlloc_1923_;
goto v_reusejp_1921_;
}
v_reusejp_1921_:
{
return v___x_1922_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg___boxed(lean_object* v_upperBound_1938_, lean_object* v_a_1939_, lean_object* v___x_1940_, lean_object* v_a_1941_, lean_object* v_b_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_){
_start:
{
lean_object* v_res_1954_; 
v_res_1954_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg(v_upperBound_1938_, v_a_1939_, v___x_1940_, v_a_1941_, v_b_1942_, v___y_1943_, v___y_1944_, v___y_1945_, v___y_1946_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_, v___y_1951_, v___y_1952_);
lean_dec(v___y_1952_);
lean_dec_ref(v___y_1951_);
lean_dec(v___y_1950_);
lean_dec_ref(v___y_1949_);
lean_dec(v___y_1948_);
lean_dec_ref(v___y_1947_);
lean_dec(v___y_1946_);
lean_dec_ref(v___y_1945_);
lean_dec(v___y_1944_);
lean_dec(v___y_1943_);
lean_dec_ref(v___x_1940_);
lean_dec_ref(v_a_1939_);
lean_dec(v_upperBound_1938_);
return v_res_1954_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__1___redArg(lean_object* v_upperBound_1955_, lean_object* v___x_1956_, lean_object* v_a_1957_, lean_object* v_a_1958_, lean_object* v_b_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_){
_start:
{
uint8_t v___x_1971_; 
v___x_1971_ = lean_nat_dec_lt(v_a_1958_, v_upperBound_1955_);
if (v___x_1971_ == 0)
{
lean_object* v___x_1972_; 
lean_dec(v_a_1958_);
v___x_1972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1972_, 0, v_b_1959_);
return v___x_1972_;
}
else
{
lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; 
v___x_1973_ = lean_box(0);
v___x_1974_ = l_Lean_instInhabitedExpr;
v___x_1975_ = lean_unsigned_to_nat(1u);
v___x_1976_ = lean_nat_add(v_a_1958_, v___x_1975_);
v___x_1977_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1974_, v_a_1957_, v_a_1958_);
lean_dec(v_a_1958_);
lean_inc(v___x_1976_);
v___x_1978_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg(v___x_1956_, v_a_1957_, v___x_1977_, v___x_1976_, v___x_1973_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_, v___y_1966_, v___y_1967_, v___y_1968_, v___y_1969_);
lean_dec(v___x_1977_);
if (lean_obj_tag(v___x_1978_) == 0)
{
lean_dec_ref_known(v___x_1978_, 1);
v_a_1958_ = v___x_1976_;
v_b_1959_ = v___x_1973_;
goto _start;
}
else
{
lean_dec(v___x_1976_);
return v___x_1978_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__1___redArg___boxed(lean_object* v_upperBound_1980_, lean_object* v___x_1981_, lean_object* v_a_1982_, lean_object* v_a_1983_, lean_object* v_b_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_){
_start:
{
lean_object* v_res_1996_; 
v_res_1996_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__1___redArg(v_upperBound_1980_, v___x_1981_, v_a_1982_, v_a_1983_, v_b_1984_, v___y_1985_, v___y_1986_, v___y_1987_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_, v___y_1994_);
lean_dec(v___y_1994_);
lean_dec_ref(v___y_1993_);
lean_dec(v___y_1992_);
lean_dec_ref(v___y_1991_);
lean_dec(v___y_1990_);
lean_dec_ref(v___y_1989_);
lean_dec(v___y_1988_);
lean_dec_ref(v___y_1987_);
lean_dec(v___y_1986_);
lean_dec(v___y_1985_);
lean_dec_ref(v_a_1982_);
lean_dec(v___x_1981_);
lean_dec(v_upperBound_1980_);
return v_res_1996_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq(lean_object* v_a_1997_, lean_object* v_a_1998_, lean_object* v_a_1999_, lean_object* v_a_2000_, lean_object* v_a_2001_, lean_object* v_a_2002_, lean_object* v_a_2003_, lean_object* v_a_2004_, lean_object* v_a_2005_, lean_object* v_a_2006_){
_start:
{
lean_object* v___x_2008_; 
v___x_2008_ = l_Lean_Meta_Grind_getExprs___redArg(v_a_1997_);
if (lean_obj_tag(v___x_2008_) == 0)
{
lean_object* v_a_2009_; lean_object* v_size_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; 
v_a_2009_ = lean_ctor_get(v___x_2008_, 0);
lean_inc(v_a_2009_);
lean_dec_ref_known(v___x_2008_, 1);
v_size_2010_ = lean_ctor_get(v_a_2009_, 2);
lean_inc(v_size_2010_);
v___x_2011_ = lean_unsigned_to_nat(0u);
v___x_2012_ = lean_box(0);
v___x_2013_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__1___redArg(v_size_2010_, v_size_2010_, v_a_2009_, v___x_2011_, v___x_2012_, v_a_1997_, v_a_1998_, v_a_1999_, v_a_2000_, v_a_2001_, v_a_2002_, v_a_2003_, v_a_2004_, v_a_2005_, v_a_2006_);
lean_dec(v_a_2009_);
lean_dec(v_size_2010_);
if (lean_obj_tag(v___x_2013_) == 0)
{
lean_object* v___x_2015_; uint8_t v_isShared_2016_; uint8_t v_isSharedCheck_2020_; 
v_isSharedCheck_2020_ = !lean_is_exclusive(v___x_2013_);
if (v_isSharedCheck_2020_ == 0)
{
lean_object* v_unused_2021_; 
v_unused_2021_ = lean_ctor_get(v___x_2013_, 0);
lean_dec(v_unused_2021_);
v___x_2015_ = v___x_2013_;
v_isShared_2016_ = v_isSharedCheck_2020_;
goto v_resetjp_2014_;
}
else
{
lean_dec(v___x_2013_);
v___x_2015_ = lean_box(0);
v_isShared_2016_ = v_isSharedCheck_2020_;
goto v_resetjp_2014_;
}
v_resetjp_2014_:
{
lean_object* v___x_2018_; 
if (v_isShared_2016_ == 0)
{
lean_ctor_set(v___x_2015_, 0, v___x_2012_);
v___x_2018_ = v___x_2015_;
goto v_reusejp_2017_;
}
else
{
lean_object* v_reuseFailAlloc_2019_; 
v_reuseFailAlloc_2019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2019_, 0, v___x_2012_);
v___x_2018_ = v_reuseFailAlloc_2019_;
goto v_reusejp_2017_;
}
v_reusejp_2017_:
{
return v___x_2018_;
}
}
}
else
{
return v___x_2013_;
}
}
else
{
lean_object* v_a_2022_; lean_object* v___x_2024_; uint8_t v_isShared_2025_; uint8_t v_isSharedCheck_2029_; 
v_a_2022_ = lean_ctor_get(v___x_2008_, 0);
v_isSharedCheck_2029_ = !lean_is_exclusive(v___x_2008_);
if (v_isSharedCheck_2029_ == 0)
{
v___x_2024_ = v___x_2008_;
v_isShared_2025_ = v_isSharedCheck_2029_;
goto v_resetjp_2023_;
}
else
{
lean_inc(v_a_2022_);
lean_dec(v___x_2008_);
v___x_2024_ = lean_box(0);
v_isShared_2025_ = v_isSharedCheck_2029_;
goto v_resetjp_2023_;
}
v_resetjp_2023_:
{
lean_object* v___x_2027_; 
if (v_isShared_2025_ == 0)
{
v___x_2027_ = v___x_2024_;
goto v_reusejp_2026_;
}
else
{
lean_object* v_reuseFailAlloc_2028_; 
v_reuseFailAlloc_2028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2028_, 0, v_a_2022_);
v___x_2027_ = v_reuseFailAlloc_2028_;
goto v_reusejp_2026_;
}
v_reusejp_2026_:
{
return v___x_2027_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq___boxed(lean_object* v_a_2030_, lean_object* v_a_2031_, lean_object* v_a_2032_, lean_object* v_a_2033_, lean_object* v_a_2034_, lean_object* v_a_2035_, lean_object* v_a_2036_, lean_object* v_a_2037_, lean_object* v_a_2038_, lean_object* v_a_2039_, lean_object* v_a_2040_){
_start:
{
lean_object* v_res_2041_; 
v_res_2041_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq(v_a_2030_, v_a_2031_, v_a_2032_, v_a_2033_, v_a_2034_, v_a_2035_, v_a_2036_, v_a_2037_, v_a_2038_, v_a_2039_);
lean_dec(v_a_2039_);
lean_dec_ref(v_a_2038_);
lean_dec(v_a_2037_);
lean_dec_ref(v_a_2036_);
lean_dec(v_a_2035_);
lean_dec_ref(v_a_2034_);
lean_dec(v_a_2033_);
lean_dec_ref(v_a_2032_);
lean_dec(v_a_2031_);
lean_dec(v_a_2030_);
return v_res_2041_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0(lean_object* v_upperBound_2042_, lean_object* v_a_2043_, lean_object* v___x_2044_, lean_object* v_inst_2045_, lean_object* v_R_2046_, lean_object* v_a_2047_, lean_object* v_b_2048_, lean_object* v_c_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_){
_start:
{
lean_object* v___x_2061_; 
v___x_2061_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg(v_upperBound_2042_, v_a_2043_, v___x_2044_, v_a_2047_, v_b_2048_, v___y_2050_, v___y_2051_, v___y_2052_, v___y_2053_, v___y_2054_, v___y_2055_, v___y_2056_, v___y_2057_, v___y_2058_, v___y_2059_);
return v___x_2061_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___boxed(lean_object** _args){
lean_object* v_upperBound_2062_ = _args[0];
lean_object* v_a_2063_ = _args[1];
lean_object* v___x_2064_ = _args[2];
lean_object* v_inst_2065_ = _args[3];
lean_object* v_R_2066_ = _args[4];
lean_object* v_a_2067_ = _args[5];
lean_object* v_b_2068_ = _args[6];
lean_object* v_c_2069_ = _args[7];
lean_object* v___y_2070_ = _args[8];
lean_object* v___y_2071_ = _args[9];
lean_object* v___y_2072_ = _args[10];
lean_object* v___y_2073_ = _args[11];
lean_object* v___y_2074_ = _args[12];
lean_object* v___y_2075_ = _args[13];
lean_object* v___y_2076_ = _args[14];
lean_object* v___y_2077_ = _args[15];
lean_object* v___y_2078_ = _args[16];
lean_object* v___y_2079_ = _args[17];
lean_object* v___y_2080_ = _args[18];
_start:
{
lean_object* v_res_2081_; 
v_res_2081_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0(v_upperBound_2062_, v_a_2063_, v___x_2064_, v_inst_2065_, v_R_2066_, v_a_2067_, v_b_2068_, v_c_2069_, v___y_2070_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_, v___y_2079_);
lean_dec(v___y_2079_);
lean_dec_ref(v___y_2078_);
lean_dec(v___y_2077_);
lean_dec_ref(v___y_2076_);
lean_dec(v___y_2075_);
lean_dec_ref(v___y_2074_);
lean_dec(v___y_2073_);
lean_dec_ref(v___y_2072_);
lean_dec(v___y_2071_);
lean_dec(v___y_2070_);
lean_dec_ref(v___x_2064_);
lean_dec_ref(v_a_2063_);
lean_dec(v_upperBound_2062_);
return v_res_2081_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__1(lean_object* v_upperBound_2082_, lean_object* v___x_2083_, lean_object* v_a_2084_, lean_object* v_inst_2085_, lean_object* v_R_2086_, lean_object* v_a_2087_, lean_object* v_b_2088_, lean_object* v_c_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_){
_start:
{
lean_object* v___x_2101_; 
v___x_2101_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__1___redArg(v_upperBound_2082_, v___x_2083_, v_a_2084_, v_a_2087_, v_b_2088_, v___y_2090_, v___y_2091_, v___y_2092_, v___y_2093_, v___y_2094_, v___y_2095_, v___y_2096_, v___y_2097_, v___y_2098_, v___y_2099_);
return v___x_2101_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__1___boxed(lean_object** _args){
lean_object* v_upperBound_2102_ = _args[0];
lean_object* v___x_2103_ = _args[1];
lean_object* v_a_2104_ = _args[2];
lean_object* v_inst_2105_ = _args[3];
lean_object* v_R_2106_ = _args[4];
lean_object* v_a_2107_ = _args[5];
lean_object* v_b_2108_ = _args[6];
lean_object* v_c_2109_ = _args[7];
lean_object* v___y_2110_ = _args[8];
lean_object* v___y_2111_ = _args[9];
lean_object* v___y_2112_ = _args[10];
lean_object* v___y_2113_ = _args[11];
lean_object* v___y_2114_ = _args[12];
lean_object* v___y_2115_ = _args[13];
lean_object* v___y_2116_ = _args[14];
lean_object* v___y_2117_ = _args[15];
lean_object* v___y_2118_ = _args[16];
lean_object* v___y_2119_ = _args[17];
lean_object* v___y_2120_ = _args[18];
_start:
{
lean_object* v_res_2121_; 
v_res_2121_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__1(v_upperBound_2102_, v___x_2103_, v_a_2104_, v_inst_2105_, v_R_2106_, v_a_2107_, v_b_2108_, v_c_2109_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_);
lean_dec(v___y_2119_);
lean_dec_ref(v___y_2118_);
lean_dec(v___y_2117_);
lean_dec_ref(v___y_2116_);
lean_dec(v___y_2115_);
lean_dec_ref(v___y_2114_);
lean_dec(v___y_2113_);
lean_dec_ref(v___y_2112_);
lean_dec(v___y_2111_);
lean_dec(v___y_2110_);
lean_dec_ref(v_a_2104_);
lean_dec(v___x_2103_);
lean_dec(v_upperBound_2102_);
return v_res_2121_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2122_; double v___x_2123_; 
v___x_2122_ = lean_unsigned_to_nat(0u);
v___x_2123_ = lean_float_of_nat(v___x_2122_);
return v___x_2123_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__0___redArg(lean_object* v_cls_2127_, lean_object* v_msg_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_){
_start:
{
lean_object* v_ref_2134_; lean_object* v___x_2135_; lean_object* v_a_2136_; lean_object* v___x_2138_; uint8_t v_isShared_2139_; uint8_t v_isSharedCheck_2181_; 
v_ref_2134_ = lean_ctor_get(v___y_2131_, 2);
v___x_2135_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__1_spec__1(v_msg_2128_, v___y_2129_, v___y_2130_, v___y_2131_, v___y_2132_);
v_a_2136_ = lean_ctor_get(v___x_2135_, 0);
v_isSharedCheck_2181_ = !lean_is_exclusive(v___x_2135_);
if (v_isSharedCheck_2181_ == 0)
{
v___x_2138_ = v___x_2135_;
v_isShared_2139_ = v_isSharedCheck_2181_;
goto v_resetjp_2137_;
}
else
{
lean_inc(v_a_2136_);
lean_dec(v___x_2135_);
v___x_2138_ = lean_box(0);
v_isShared_2139_ = v_isSharedCheck_2181_;
goto v_resetjp_2137_;
}
v_resetjp_2137_:
{
lean_object* v___x_2140_; lean_object* v_traceState_2141_; lean_object* v_env_2142_; lean_object* v_nextMacroScope_2143_; lean_object* v_ngen_2144_; lean_object* v_auxDeclNGen_2145_; lean_object* v_cache_2146_; lean_object* v_recordedDeps_2147_; lean_object* v_messages_2148_; lean_object* v_infoState_2149_; lean_object* v_snapshotTasks_2150_; lean_object* v___x_2152_; uint8_t v_isShared_2153_; uint8_t v_isSharedCheck_2180_; 
v___x_2140_ = lean_st_ref_take(v___y_2132_);
v_traceState_2141_ = lean_ctor_get(v___x_2140_, 4);
v_env_2142_ = lean_ctor_get(v___x_2140_, 0);
v_nextMacroScope_2143_ = lean_ctor_get(v___x_2140_, 1);
v_ngen_2144_ = lean_ctor_get(v___x_2140_, 2);
v_auxDeclNGen_2145_ = lean_ctor_get(v___x_2140_, 3);
v_cache_2146_ = lean_ctor_get(v___x_2140_, 5);
v_recordedDeps_2147_ = lean_ctor_get(v___x_2140_, 6);
v_messages_2148_ = lean_ctor_get(v___x_2140_, 7);
v_infoState_2149_ = lean_ctor_get(v___x_2140_, 8);
v_snapshotTasks_2150_ = lean_ctor_get(v___x_2140_, 9);
v_isSharedCheck_2180_ = !lean_is_exclusive(v___x_2140_);
if (v_isSharedCheck_2180_ == 0)
{
v___x_2152_ = v___x_2140_;
v_isShared_2153_ = v_isSharedCheck_2180_;
goto v_resetjp_2151_;
}
else
{
lean_inc(v_snapshotTasks_2150_);
lean_inc(v_infoState_2149_);
lean_inc(v_messages_2148_);
lean_inc(v_recordedDeps_2147_);
lean_inc(v_cache_2146_);
lean_inc(v_traceState_2141_);
lean_inc(v_auxDeclNGen_2145_);
lean_inc(v_ngen_2144_);
lean_inc(v_nextMacroScope_2143_);
lean_inc(v_env_2142_);
lean_dec(v___x_2140_);
v___x_2152_ = lean_box(0);
v_isShared_2153_ = v_isSharedCheck_2180_;
goto v_resetjp_2151_;
}
v_resetjp_2151_:
{
uint64_t v_tid_2154_; lean_object* v_traces_2155_; lean_object* v___x_2157_; uint8_t v_isShared_2158_; uint8_t v_isSharedCheck_2179_; 
v_tid_2154_ = lean_ctor_get_uint64(v_traceState_2141_, sizeof(void*)*1);
v_traces_2155_ = lean_ctor_get(v_traceState_2141_, 0);
v_isSharedCheck_2179_ = !lean_is_exclusive(v_traceState_2141_);
if (v_isSharedCheck_2179_ == 0)
{
v___x_2157_ = v_traceState_2141_;
v_isShared_2158_ = v_isSharedCheck_2179_;
goto v_resetjp_2156_;
}
else
{
lean_inc(v_traces_2155_);
lean_dec(v_traceState_2141_);
v___x_2157_ = lean_box(0);
v_isShared_2158_ = v_isSharedCheck_2179_;
goto v_resetjp_2156_;
}
v_resetjp_2156_:
{
lean_object* v___x_2159_; lean_object* v___x_2160_; double v___x_2161_; uint8_t v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2170_; 
v___x_2159_ = lean_box(0);
v___x_2160_ = lean_box(0);
v___x_2161_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__0___redArg___closed__0);
v___x_2162_ = 0;
v___x_2163_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__0___redArg___closed__1));
v___x_2164_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2164_, 0, v_cls_2127_);
lean_ctor_set(v___x_2164_, 1, v___x_2160_);
lean_ctor_set(v___x_2164_, 2, v___x_2163_);
lean_ctor_set_float(v___x_2164_, sizeof(void*)*3, v___x_2161_);
lean_ctor_set_float(v___x_2164_, sizeof(void*)*3 + 8, v___x_2161_);
lean_ctor_set_uint8(v___x_2164_, sizeof(void*)*3 + 16, v___x_2162_);
v___x_2165_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__0___redArg___closed__2));
v___x_2166_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2166_, 0, v___x_2164_);
lean_ctor_set(v___x_2166_, 1, v_a_2136_);
lean_ctor_set(v___x_2166_, 2, v___x_2165_);
lean_inc(v_ref_2134_);
v___x_2167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2167_, 0, v_ref_2134_);
lean_ctor_set(v___x_2167_, 1, v___x_2166_);
v___x_2168_ = l_Lean_PersistentArray_push___redArg(v_traces_2155_, v___x_2167_);
if (v_isShared_2158_ == 0)
{
lean_ctor_set(v___x_2157_, 0, v___x_2168_);
v___x_2170_ = v___x_2157_;
goto v_reusejp_2169_;
}
else
{
lean_object* v_reuseFailAlloc_2178_; 
v_reuseFailAlloc_2178_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2178_, 0, v___x_2168_);
lean_ctor_set_uint64(v_reuseFailAlloc_2178_, sizeof(void*)*1, v_tid_2154_);
v___x_2170_ = v_reuseFailAlloc_2178_;
goto v_reusejp_2169_;
}
v_reusejp_2169_:
{
lean_object* v___x_2172_; 
if (v_isShared_2153_ == 0)
{
lean_ctor_set(v___x_2152_, 4, v___x_2170_);
v___x_2172_ = v___x_2152_;
goto v_reusejp_2171_;
}
else
{
lean_object* v_reuseFailAlloc_2177_; 
v_reuseFailAlloc_2177_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2177_, 0, v_env_2142_);
lean_ctor_set(v_reuseFailAlloc_2177_, 1, v_nextMacroScope_2143_);
lean_ctor_set(v_reuseFailAlloc_2177_, 2, v_ngen_2144_);
lean_ctor_set(v_reuseFailAlloc_2177_, 3, v_auxDeclNGen_2145_);
lean_ctor_set(v_reuseFailAlloc_2177_, 4, v___x_2170_);
lean_ctor_set(v_reuseFailAlloc_2177_, 5, v_cache_2146_);
lean_ctor_set(v_reuseFailAlloc_2177_, 6, v_recordedDeps_2147_);
lean_ctor_set(v_reuseFailAlloc_2177_, 7, v_messages_2148_);
lean_ctor_set(v_reuseFailAlloc_2177_, 8, v_infoState_2149_);
lean_ctor_set(v_reuseFailAlloc_2177_, 9, v_snapshotTasks_2150_);
v___x_2172_ = v_reuseFailAlloc_2177_;
goto v_reusejp_2171_;
}
v_reusejp_2171_:
{
lean_object* v___x_2173_; lean_object* v___x_2175_; 
v___x_2173_ = lean_st_ref_put(v___y_2132_, v___x_2172_);
if (v_isShared_2139_ == 0)
{
lean_ctor_set(v___x_2138_, 0, v___x_2159_);
v___x_2175_ = v___x_2138_;
goto v_reusejp_2174_;
}
else
{
lean_object* v_reuseFailAlloc_2176_; 
v_reuseFailAlloc_2176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2176_, 0, v___x_2159_);
v___x_2175_ = v_reuseFailAlloc_2176_;
goto v_reusejp_2174_;
}
v_reusejp_2174_:
{
return v___x_2175_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__0___redArg___boxed(lean_object* v_cls_2182_, lean_object* v_msg_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_){
_start:
{
lean_object* v_res_2189_; 
v_res_2189_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__0___redArg(v_cls_2182_, v_msg_2183_, v___y_2184_, v___y_2185_, v___y_2186_, v___y_2187_);
lean_dec(v___y_2187_);
lean_dec_ref(v___y_2186_);
lean_dec(v___y_2185_);
lean_dec_ref(v___y_2184_);
return v_res_2189_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__6(void){
_start:
{
lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; 
v___x_2200_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__3));
v___x_2201_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__5));
v___x_2202_ = l_Lean_Name_append(v___x_2201_, v___x_2200_);
return v___x_2202_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__8(void){
_start:
{
lean_object* v___x_2204_; lean_object* v___x_2205_; 
v___x_2204_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__7));
v___x_2205_ = l_Lean_stringToMessageData(v___x_2204_);
return v___x_2205_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__10(void){
_start:
{
lean_object* v___x_2207_; lean_object* v___x_2208_; 
v___x_2207_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__9));
v___x_2208_ = l_Lean_stringToMessageData(v___x_2207_);
return v___x_2208_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg(lean_object* v_a_2209_, lean_object* v_as_x27_2210_, lean_object* v_b_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_){
_start:
{
if (lean_obj_tag(v_as_x27_2210_) == 0)
{
lean_object* v___x_2223_; 
lean_dec_ref(v_a_2209_);
v___x_2223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2223_, 0, v_b_2211_);
return v___x_2223_;
}
else
{
lean_object* v_head_2224_; lean_object* v_tail_2225_; lean_object* v___x_2226_; size_t v___x_2227_; size_t v___x_2228_; uint8_t v___x_2229_; 
v_head_2224_ = lean_ctor_get(v_as_x27_2210_, 0);
v_tail_2225_ = lean_ctor_get(v_as_x27_2210_, 1);
v___x_2226_ = lean_box(0);
v___x_2227_ = lean_ptr_addr(v_a_2209_);
v___x_2228_ = lean_ptr_addr(v_head_2224_);
v___x_2229_ = lean_usize_dec_eq(v___x_2227_, v___x_2228_);
if (v___x_2229_ == 0)
{
lean_object* v___x_2230_; 
lean_inc(v_head_2224_);
lean_inc_ref(v_a_2209_);
v___x_2230_ = l_Lean_Meta_Grind_mkEqHEqProof(v_a_2209_, v_head_2224_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_, v___y_2216_, v___y_2217_, v___y_2218_, v___y_2219_, v___y_2220_, v___y_2221_);
if (lean_obj_tag(v___x_2230_) == 0)
{
lean_object* v_toCold_2231_; lean_object* v_options_2232_; lean_object* v_a_2233_; lean_object* v_inheritedTraceOptions_2234_; uint8_t v_hasTrace_2235_; lean_object* v___x_2236_; lean_object* v___y_2238_; lean_object* v___y_2239_; lean_object* v___y_2240_; lean_object* v___y_2241_; lean_object* v___y_2242_; lean_object* v___y_2243_; lean_object* v___y_2244_; lean_object* v___y_2245_; lean_object* v___y_2246_; lean_object* v___y_2247_; 
v_toCold_2231_ = lean_ctor_get(v___y_2220_, 0);
v_options_2232_ = lean_ctor_get(v_toCold_2231_, 2);
v_a_2233_ = lean_ctor_get(v___x_2230_, 0);
lean_inc(v_a_2233_);
lean_dec_ref_known(v___x_2230_, 1);
v_inheritedTraceOptions_2234_ = lean_ctor_get(v_toCold_2231_, 11);
v_hasTrace_2235_ = lean_ctor_get_uint8(v_options_2232_, sizeof(void*)*1);
v___x_2236_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__3));
if (v_hasTrace_2235_ == 0)
{
v___y_2238_ = v___y_2212_;
v___y_2239_ = v___y_2213_;
v___y_2240_ = v___y_2214_;
v___y_2241_ = v___y_2215_;
v___y_2242_ = v___y_2216_;
v___y_2243_ = v___y_2217_;
v___y_2244_ = v___y_2218_;
v___y_2245_ = v___y_2219_;
v___y_2246_ = v___y_2220_;
v___y_2247_ = v___y_2221_;
goto v___jp_2237_;
}
else
{
lean_object* v___x_2274_; uint8_t v___x_2275_; 
v___x_2274_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__6, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__6_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__6);
v___x_2275_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2234_, v_options_2232_, v___x_2274_);
if (v___x_2275_ == 0)
{
v___y_2238_ = v___y_2212_;
v___y_2239_ = v___y_2213_;
v___y_2240_ = v___y_2214_;
v___y_2241_ = v___y_2215_;
v___y_2242_ = v___y_2216_;
v___y_2243_ = v___y_2217_;
v___y_2244_ = v___y_2218_;
v___y_2245_ = v___y_2219_;
v___y_2246_ = v___y_2220_;
v___y_2247_ = v___y_2221_;
goto v___jp_2237_;
}
else
{
lean_object* v___x_2276_; 
v___x_2276_ = l_Lean_Meta_Grind_updateLastTag(v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_, v___y_2216_, v___y_2217_, v___y_2218_, v___y_2219_, v___y_2220_, v___y_2221_);
if (lean_obj_tag(v___x_2276_) == 0)
{
lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; 
lean_dec_ref_known(v___x_2276_, 1);
lean_inc_ref(v_a_2209_);
v___x_2277_ = l_Lean_MessageData_ofExpr(v_a_2209_);
v___x_2278_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__10, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__10_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__10);
v___x_2279_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2279_, 0, v___x_2277_);
lean_ctor_set(v___x_2279_, 1, v___x_2278_);
lean_inc(v_head_2224_);
v___x_2280_ = l_Lean_MessageData_ofExpr(v_head_2224_);
v___x_2281_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2281_, 0, v___x_2279_);
lean_ctor_set(v___x_2281_, 1, v___x_2280_);
v___x_2282_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__0___redArg(v___x_2236_, v___x_2281_, v___y_2218_, v___y_2219_, v___y_2220_, v___y_2221_);
if (lean_obj_tag(v___x_2282_) == 0)
{
lean_dec_ref_known(v___x_2282_, 1);
v___y_2238_ = v___y_2212_;
v___y_2239_ = v___y_2213_;
v___y_2240_ = v___y_2214_;
v___y_2241_ = v___y_2215_;
v___y_2242_ = v___y_2216_;
v___y_2243_ = v___y_2217_;
v___y_2244_ = v___y_2218_;
v___y_2245_ = v___y_2219_;
v___y_2246_ = v___y_2220_;
v___y_2247_ = v___y_2221_;
goto v___jp_2237_;
}
else
{
lean_dec(v_a_2233_);
lean_dec_ref(v_a_2209_);
return v___x_2282_;
}
}
else
{
lean_dec(v_a_2233_);
lean_dec_ref(v_a_2209_);
return v___x_2276_;
}
}
}
v___jp_2237_:
{
uint8_t v___x_2248_; lean_object* v___x_2249_; 
v___x_2248_ = 0;
lean_inc(v_a_2233_);
v___x_2249_ = l_Lean_Meta_check(v_a_2233_, v___x_2248_, v___y_2244_, v___y_2245_, v___y_2246_, v___y_2247_);
if (lean_obj_tag(v___x_2249_) == 0)
{
lean_object* v_toCold_2250_; lean_object* v_options_2251_; uint8_t v_hasTrace_2252_; 
lean_dec_ref_known(v___x_2249_, 1);
v_toCold_2250_ = lean_ctor_get(v___y_2246_, 0);
v_options_2251_ = lean_ctor_get(v_toCold_2250_, 2);
v_hasTrace_2252_ = lean_ctor_get_uint8(v_options_2251_, sizeof(void*)*1);
if (v_hasTrace_2252_ == 0)
{
lean_dec(v_a_2233_);
v_as_x27_2210_ = v_tail_2225_;
v_b_2211_ = v___x_2226_;
goto _start;
}
else
{
lean_object* v_inheritedTraceOptions_2254_; lean_object* v___x_2255_; uint8_t v___x_2256_; 
v_inheritedTraceOptions_2254_ = lean_ctor_get(v_toCold_2250_, 11);
v___x_2255_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__6, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__6_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__6);
v___x_2256_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2254_, v_options_2251_, v___x_2255_);
if (v___x_2256_ == 0)
{
lean_dec(v_a_2233_);
v_as_x27_2210_ = v_tail_2225_;
v_b_2211_ = v___x_2226_;
goto _start;
}
else
{
lean_object* v___x_2258_; 
v___x_2258_ = l_Lean_Meta_Grind_updateLastTag(v___y_2238_, v___y_2239_, v___y_2240_, v___y_2241_, v___y_2242_, v___y_2243_, v___y_2244_, v___y_2245_, v___y_2246_, v___y_2247_);
if (lean_obj_tag(v___x_2258_) == 0)
{
lean_object* v___x_2259_; 
lean_dec_ref_known(v___x_2258_, 1);
lean_inc(v___y_2247_);
lean_inc_ref(v___y_2246_);
lean_inc(v___y_2245_);
lean_inc_ref(v___y_2244_);
v___x_2259_ = lean_infer_type(v_a_2233_, v___y_2244_, v___y_2245_, v___y_2246_, v___y_2247_);
if (lean_obj_tag(v___x_2259_) == 0)
{
lean_object* v_a_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; 
v_a_2260_ = lean_ctor_get(v___x_2259_, 0);
lean_inc(v_a_2260_);
lean_dec_ref_known(v___x_2259_, 1);
v___x_2261_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__8, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__8_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__8);
v___x_2262_ = l_Lean_MessageData_ofExpr(v_a_2260_);
v___x_2263_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2263_, 0, v___x_2261_);
lean_ctor_set(v___x_2263_, 1, v___x_2262_);
v___x_2264_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__0___redArg(v___x_2236_, v___x_2263_, v___y_2244_, v___y_2245_, v___y_2246_, v___y_2247_);
if (lean_obj_tag(v___x_2264_) == 0)
{
lean_dec_ref_known(v___x_2264_, 1);
v_as_x27_2210_ = v_tail_2225_;
v_b_2211_ = v___x_2226_;
goto _start;
}
else
{
lean_dec_ref(v_a_2209_);
return v___x_2264_;
}
}
else
{
lean_object* v_a_2266_; lean_object* v___x_2268_; uint8_t v_isShared_2269_; uint8_t v_isSharedCheck_2273_; 
lean_dec_ref(v_a_2209_);
v_a_2266_ = lean_ctor_get(v___x_2259_, 0);
v_isSharedCheck_2273_ = !lean_is_exclusive(v___x_2259_);
if (v_isSharedCheck_2273_ == 0)
{
v___x_2268_ = v___x_2259_;
v_isShared_2269_ = v_isSharedCheck_2273_;
goto v_resetjp_2267_;
}
else
{
lean_inc(v_a_2266_);
lean_dec(v___x_2259_);
v___x_2268_ = lean_box(0);
v_isShared_2269_ = v_isSharedCheck_2273_;
goto v_resetjp_2267_;
}
v_resetjp_2267_:
{
lean_object* v___x_2271_; 
if (v_isShared_2269_ == 0)
{
v___x_2271_ = v___x_2268_;
goto v_reusejp_2270_;
}
else
{
lean_object* v_reuseFailAlloc_2272_; 
v_reuseFailAlloc_2272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2272_, 0, v_a_2266_);
v___x_2271_ = v_reuseFailAlloc_2272_;
goto v_reusejp_2270_;
}
v_reusejp_2270_:
{
return v___x_2271_;
}
}
}
}
else
{
lean_dec(v_a_2233_);
lean_dec_ref(v_a_2209_);
return v___x_2258_;
}
}
}
}
else
{
lean_dec(v_a_2233_);
lean_dec_ref(v_a_2209_);
return v___x_2249_;
}
}
}
else
{
lean_object* v_a_2283_; lean_object* v___x_2285_; uint8_t v_isShared_2286_; uint8_t v_isSharedCheck_2290_; 
lean_dec_ref(v_a_2209_);
v_a_2283_ = lean_ctor_get(v___x_2230_, 0);
v_isSharedCheck_2290_ = !lean_is_exclusive(v___x_2230_);
if (v_isSharedCheck_2290_ == 0)
{
v___x_2285_ = v___x_2230_;
v_isShared_2286_ = v_isSharedCheck_2290_;
goto v_resetjp_2284_;
}
else
{
lean_inc(v_a_2283_);
lean_dec(v___x_2230_);
v___x_2285_ = lean_box(0);
v_isShared_2286_ = v_isSharedCheck_2290_;
goto v_resetjp_2284_;
}
v_resetjp_2284_:
{
lean_object* v___x_2288_; 
if (v_isShared_2286_ == 0)
{
v___x_2288_ = v___x_2285_;
goto v_reusejp_2287_;
}
else
{
lean_object* v_reuseFailAlloc_2289_; 
v_reuseFailAlloc_2289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2289_, 0, v_a_2283_);
v___x_2288_ = v_reuseFailAlloc_2289_;
goto v_reusejp_2287_;
}
v_reusejp_2287_:
{
return v___x_2288_;
}
}
}
}
else
{
v_as_x27_2210_ = v_tail_2225_;
v_b_2211_ = v___x_2226_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___boxed(lean_object* v_a_2292_, lean_object* v_as_x27_2293_, lean_object* v_b_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_){
_start:
{
lean_object* v_res_2306_; 
v_res_2306_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg(v_a_2292_, v_as_x27_2293_, v_b_2294_, v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_, v___y_2300_, v___y_2301_, v___y_2302_, v___y_2303_, v___y_2304_);
lean_dec(v___y_2304_);
lean_dec_ref(v___y_2303_);
lean_dec(v___y_2302_);
lean_dec_ref(v___y_2301_);
lean_dec(v___y_2300_);
lean_dec_ref(v___y_2299_);
lean_dec(v___y_2298_);
lean_dec_ref(v___y_2297_);
lean_dec(v___y_2296_);
lean_dec(v___y_2295_);
lean_dec(v_as_x27_2293_);
return v_res_2306_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__2___redArg(lean_object* v_a_2307_, lean_object* v_as_x27_2308_, lean_object* v_b_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_){
_start:
{
if (lean_obj_tag(v_as_x27_2308_) == 0)
{
lean_object* v___x_2321_; 
v___x_2321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2321_, 0, v_b_2309_);
return v___x_2321_;
}
else
{
lean_object* v_head_2322_; lean_object* v_tail_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; 
v_head_2322_ = lean_ctor_get(v_as_x27_2308_, 0);
v_tail_2323_ = lean_ctor_get(v_as_x27_2308_, 1);
v___x_2324_ = lean_box(0);
lean_inc(v_head_2322_);
v___x_2325_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg(v_head_2322_, v_a_2307_, v___x_2324_, v___y_2310_, v___y_2311_, v___y_2312_, v___y_2313_, v___y_2314_, v___y_2315_, v___y_2316_, v___y_2317_, v___y_2318_, v___y_2319_);
if (lean_obj_tag(v___x_2325_) == 0)
{
lean_dec_ref_known(v___x_2325_, 1);
v_as_x27_2308_ = v_tail_2323_;
v_b_2309_ = v___x_2324_;
goto _start;
}
else
{
return v___x_2325_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__2___redArg___boxed(lean_object* v_a_2327_, lean_object* v_as_x27_2328_, lean_object* v_b_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_){
_start:
{
lean_object* v_res_2341_; 
v_res_2341_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__2___redArg(v_a_2327_, v_as_x27_2328_, v_b_2329_, v___y_2330_, v___y_2331_, v___y_2332_, v___y_2333_, v___y_2334_, v___y_2335_, v___y_2336_, v___y_2337_, v___y_2338_, v___y_2339_);
lean_dec(v___y_2339_);
lean_dec_ref(v___y_2338_);
lean_dec(v___y_2337_);
lean_dec_ref(v___y_2336_);
lean_dec(v___y_2335_);
lean_dec_ref(v___y_2334_);
lean_dec(v___y_2333_);
lean_dec_ref(v___y_2332_);
lean_dec(v___y_2331_);
lean_dec(v___y_2330_);
lean_dec(v_as_x27_2328_);
lean_dec(v_a_2327_);
return v_res_2341_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__3___redArg(lean_object* v_as_x27_2342_, lean_object* v_b_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_){
_start:
{
if (lean_obj_tag(v_as_x27_2342_) == 0)
{
lean_object* v___x_2355_; 
v___x_2355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2355_, 0, v_b_2343_);
return v___x_2355_;
}
else
{
lean_object* v_head_2356_; lean_object* v_tail_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; 
v_head_2356_ = lean_ctor_get(v_as_x27_2342_, 0);
v_tail_2357_ = lean_ctor_get(v_as_x27_2342_, 1);
v___x_2358_ = lean_box(0);
v___x_2359_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__2___redArg(v_head_2356_, v_head_2356_, v___x_2358_, v___y_2344_, v___y_2345_, v___y_2346_, v___y_2347_, v___y_2348_, v___y_2349_, v___y_2350_, v___y_2351_, v___y_2352_, v___y_2353_);
if (lean_obj_tag(v___x_2359_) == 0)
{
lean_dec_ref_known(v___x_2359_, 1);
v_as_x27_2342_ = v_tail_2357_;
v_b_2343_ = v___x_2358_;
goto _start;
}
else
{
return v___x_2359_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__3___redArg___boxed(lean_object* v_as_x27_2361_, lean_object* v_b_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_){
_start:
{
lean_object* v_res_2374_; 
v_res_2374_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__3___redArg(v_as_x27_2361_, v_b_2362_, v___y_2363_, v___y_2364_, v___y_2365_, v___y_2366_, v___y_2367_, v___y_2368_, v___y_2369_, v___y_2370_, v___y_2371_, v___y_2372_);
lean_dec(v___y_2372_);
lean_dec_ref(v___y_2371_);
lean_dec(v___y_2370_);
lean_dec_ref(v___y_2369_);
lean_dec(v___y_2368_);
lean_dec_ref(v___y_2367_);
lean_dec(v___y_2366_);
lean_dec_ref(v___y_2365_);
lean_dec(v___y_2364_);
lean_dec(v___y_2363_);
lean_dec(v_as_x27_2361_);
return v_res_2374_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs(lean_object* v_a_2375_, lean_object* v_a_2376_, lean_object* v_a_2377_, lean_object* v_a_2378_, lean_object* v_a_2379_, lean_object* v_a_2380_, lean_object* v_a_2381_, lean_object* v_a_2382_, lean_object* v_a_2383_, lean_object* v_a_2384_){
_start:
{
lean_object* v___x_2386_; uint8_t v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; 
v___x_2386_ = lean_st_ref_get(v_a_2375_);
v___x_2387_ = 0;
v___x_2388_ = l_Lean_Meta_Grind_Goal_getEqcs(v___x_2386_, v___x_2387_);
lean_dec(v___x_2386_);
v___x_2389_ = lean_box(0);
v___x_2390_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__3___redArg(v___x_2388_, v___x_2389_, v_a_2375_, v_a_2376_, v_a_2377_, v_a_2378_, v_a_2379_, v_a_2380_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_);
lean_dec(v___x_2388_);
if (lean_obj_tag(v___x_2390_) == 0)
{
lean_object* v___x_2392_; uint8_t v_isShared_2393_; uint8_t v_isSharedCheck_2397_; 
v_isSharedCheck_2397_ = !lean_is_exclusive(v___x_2390_);
if (v_isSharedCheck_2397_ == 0)
{
lean_object* v_unused_2398_; 
v_unused_2398_ = lean_ctor_get(v___x_2390_, 0);
lean_dec(v_unused_2398_);
v___x_2392_ = v___x_2390_;
v_isShared_2393_ = v_isSharedCheck_2397_;
goto v_resetjp_2391_;
}
else
{
lean_dec(v___x_2390_);
v___x_2392_ = lean_box(0);
v_isShared_2393_ = v_isSharedCheck_2397_;
goto v_resetjp_2391_;
}
v_resetjp_2391_:
{
lean_object* v___x_2395_; 
if (v_isShared_2393_ == 0)
{
lean_ctor_set(v___x_2392_, 0, v___x_2389_);
v___x_2395_ = v___x_2392_;
goto v_reusejp_2394_;
}
else
{
lean_object* v_reuseFailAlloc_2396_; 
v_reuseFailAlloc_2396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2396_, 0, v___x_2389_);
v___x_2395_ = v_reuseFailAlloc_2396_;
goto v_reusejp_2394_;
}
v_reusejp_2394_:
{
return v___x_2395_;
}
}
}
else
{
return v___x_2390_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs___boxed(lean_object* v_a_2399_, lean_object* v_a_2400_, lean_object* v_a_2401_, lean_object* v_a_2402_, lean_object* v_a_2403_, lean_object* v_a_2404_, lean_object* v_a_2405_, lean_object* v_a_2406_, lean_object* v_a_2407_, lean_object* v_a_2408_, lean_object* v_a_2409_){
_start:
{
lean_object* v_res_2410_; 
v_res_2410_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs(v_a_2399_, v_a_2400_, v_a_2401_, v_a_2402_, v_a_2403_, v_a_2404_, v_a_2405_, v_a_2406_, v_a_2407_, v_a_2408_);
lean_dec(v_a_2408_);
lean_dec_ref(v_a_2407_);
lean_dec(v_a_2406_);
lean_dec_ref(v_a_2405_);
lean_dec(v_a_2404_);
lean_dec_ref(v_a_2403_);
lean_dec(v_a_2402_);
lean_dec_ref(v_a_2401_);
lean_dec(v_a_2400_);
lean_dec(v_a_2399_);
return v_res_2410_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__0(lean_object* v_cls_2411_, lean_object* v_msg_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_){
_start:
{
lean_object* v___x_2424_; 
v___x_2424_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__0___redArg(v_cls_2411_, v_msg_2412_, v___y_2419_, v___y_2420_, v___y_2421_, v___y_2422_);
return v___x_2424_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__0___boxed(lean_object* v_cls_2425_, lean_object* v_msg_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_){
_start:
{
lean_object* v_res_2438_; 
v_res_2438_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__0(v_cls_2425_, v_msg_2426_, v___y_2427_, v___y_2428_, v___y_2429_, v___y_2430_, v___y_2431_, v___y_2432_, v___y_2433_, v___y_2434_, v___y_2435_, v___y_2436_);
lean_dec(v___y_2436_);
lean_dec_ref(v___y_2435_);
lean_dec(v___y_2434_);
lean_dec_ref(v___y_2433_);
lean_dec(v___y_2432_);
lean_dec_ref(v___y_2431_);
lean_dec(v___y_2430_);
lean_dec_ref(v___y_2429_);
lean_dec(v___y_2428_);
lean_dec(v___y_2427_);
return v_res_2438_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1(lean_object* v_a_2439_, lean_object* v_as_2440_, lean_object* v_as_x27_2441_, lean_object* v_b_2442_, lean_object* v_a_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_){
_start:
{
lean_object* v___x_2455_; 
v___x_2455_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg(v_a_2439_, v_as_x27_2441_, v_b_2442_, v___y_2444_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_, v___y_2453_);
return v___x_2455_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___boxed(lean_object* v_a_2456_, lean_object* v_as_2457_, lean_object* v_as_x27_2458_, lean_object* v_b_2459_, lean_object* v_a_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_){
_start:
{
lean_object* v_res_2472_; 
v_res_2472_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1(v_a_2456_, v_as_2457_, v_as_x27_2458_, v_b_2459_, v_a_2460_, v___y_2461_, v___y_2462_, v___y_2463_, v___y_2464_, v___y_2465_, v___y_2466_, v___y_2467_, v___y_2468_, v___y_2469_, v___y_2470_);
lean_dec(v___y_2470_);
lean_dec_ref(v___y_2469_);
lean_dec(v___y_2468_);
lean_dec_ref(v___y_2467_);
lean_dec(v___y_2466_);
lean_dec_ref(v___y_2465_);
lean_dec(v___y_2464_);
lean_dec_ref(v___y_2463_);
lean_dec(v___y_2462_);
lean_dec(v___y_2461_);
lean_dec(v_as_x27_2458_);
lean_dec(v_as_2457_);
return v_res_2472_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__2(lean_object* v_a_2473_, lean_object* v_as_2474_, lean_object* v_as_x27_2475_, lean_object* v_b_2476_, lean_object* v_a_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_){
_start:
{
lean_object* v___x_2489_; 
v___x_2489_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__2___redArg(v_a_2473_, v_as_x27_2475_, v_b_2476_, v___y_2478_, v___y_2479_, v___y_2480_, v___y_2481_, v___y_2482_, v___y_2483_, v___y_2484_, v___y_2485_, v___y_2486_, v___y_2487_);
return v___x_2489_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__2___boxed(lean_object* v_a_2490_, lean_object* v_as_2491_, lean_object* v_as_x27_2492_, lean_object* v_b_2493_, lean_object* v_a_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_){
_start:
{
lean_object* v_res_2506_; 
v_res_2506_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__2(v_a_2490_, v_as_2491_, v_as_x27_2492_, v_b_2493_, v_a_2494_, v___y_2495_, v___y_2496_, v___y_2497_, v___y_2498_, v___y_2499_, v___y_2500_, v___y_2501_, v___y_2502_, v___y_2503_, v___y_2504_);
lean_dec(v___y_2504_);
lean_dec_ref(v___y_2503_);
lean_dec(v___y_2502_);
lean_dec_ref(v___y_2501_);
lean_dec(v___y_2500_);
lean_dec_ref(v___y_2499_);
lean_dec(v___y_2498_);
lean_dec_ref(v___y_2497_);
lean_dec(v___y_2496_);
lean_dec(v___y_2495_);
lean_dec(v_as_x27_2492_);
lean_dec(v_as_2491_);
lean_dec(v_a_2490_);
return v_res_2506_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__3(lean_object* v_as_2507_, lean_object* v_as_x27_2508_, lean_object* v_b_2509_, lean_object* v_a_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_){
_start:
{
lean_object* v___x_2522_; 
v___x_2522_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__3___redArg(v_as_x27_2508_, v_b_2509_, v___y_2511_, v___y_2512_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_, v___y_2517_, v___y_2518_, v___y_2519_, v___y_2520_);
return v___x_2522_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__3___boxed(lean_object* v_as_2523_, lean_object* v_as_x27_2524_, lean_object* v_b_2525_, lean_object* v_a_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_){
_start:
{
lean_object* v_res_2538_; 
v_res_2538_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__3(v_as_2523_, v_as_x27_2524_, v_b_2525_, v_a_2526_, v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_, v___y_2536_);
lean_dec(v___y_2536_);
lean_dec_ref(v___y_2535_);
lean_dec(v___y_2534_);
lean_dec_ref(v___y_2533_);
lean_dec(v___y_2532_);
lean_dec_ref(v___y_2531_);
lean_dec(v___y_2530_);
lean_dec_ref(v___y_2529_);
lean_dec(v___y_2528_);
lean_dec(v___y_2527_);
lean_dec(v_as_x27_2524_);
lean_dec(v_as_2523_);
return v_res_2538_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; 
v___x_2541_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__1___redArg___closed__1));
v___x_2542_ = lean_unsigned_to_nat(4u);
v___x_2543_ = lean_unsigned_to_nat(155u);
v___x_2544_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__1___redArg___closed__0));
v___x_2545_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__0));
v___x_2546_ = l_mkPanicMessageWithDecl(v___x_2545_, v___x_2544_, v___x_2543_, v___x_2542_, v___x_2541_);
return v___x_2546_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__1___redArg___closed__4(void){
_start:
{
lean_object* v___x_2548_; lean_object* v___x_2549_; 
v___x_2548_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__1___redArg___closed__3));
v___x_2549_ = l_Lean_stringToMessageData(v___x_2548_);
return v___x_2549_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__1___redArg___closed__6(void){
_start:
{
lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; 
v___x_2551_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__1___redArg___closed__5));
v___x_2552_ = lean_unsigned_to_nat(4u);
v___x_2553_ = lean_unsigned_to_nat(158u);
v___x_2554_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__1___redArg___closed__0));
v___x_2555_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__0));
v___x_2556_ = l_mkPanicMessageWithDecl(v___x_2555_, v___x_2554_, v___x_2553_, v___x_2552_, v___x_2551_);
return v___x_2556_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__1___redArg(lean_object* v___x_2557_, lean_object* v___x_2558_, lean_object* v_as_x27_2559_, lean_object* v_b_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_){
_start:
{
if (lean_obj_tag(v_as_x27_2559_) == 0)
{
lean_object* v___x_2572_; 
v___x_2572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2572_, 0, v_b_2560_);
return v___x_2572_;
}
else
{
lean_object* v_head_2573_; lean_object* v_tail_2574_; lean_object* v___y_2576_; lean_object* v___x_2596_; lean_object* v___x_2597_; 
v_head_2573_ = lean_ctor_get(v_as_x27_2559_, 0);
v_tail_2574_ = lean_ctor_get(v_as_x27_2559_, 1);
v___x_2596_ = lean_box(0);
lean_inc(v_head_2573_);
v___x_2597_ = l_Lean_Meta_Grind_isCongrRoot___redArg(v_head_2573_, v___y_2561_, v___y_2567_, v___y_2568_, v___y_2569_, v___y_2570_);
if (lean_obj_tag(v___x_2597_) == 0)
{
lean_object* v_a_2598_; uint8_t v___x_2599_; 
v_a_2598_ = lean_ctor_get(v___x_2597_, 0);
lean_inc(v_a_2598_);
lean_dec_ref_known(v___x_2597_, 1);
v___x_2599_ = lean_unbox(v_a_2598_);
lean_dec(v_a_2598_);
if (v___x_2599_ == 0)
{
lean_object* v___x_2600_; lean_object* v___x_2601_; 
v___x_2600_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__1___redArg___closed__2, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__1___redArg___closed__2_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__1___redArg___closed__2);
v___x_2601_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__0(v___x_2600_, v___y_2561_, v___y_2562_, v___y_2563_, v___y_2564_, v___y_2565_, v___y_2566_, v___y_2567_, v___y_2568_, v___y_2569_, v___y_2570_);
v___y_2576_ = v___x_2601_;
goto v___jp_2575_;
}
else
{
lean_object* v___x_2602_; 
lean_inc(v_head_2573_);
v___x_2602_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2___redArg(v___x_2557_, v___x_2558_, v_head_2573_);
if (lean_obj_tag(v___x_2602_) == 0)
{
lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; 
v___x_2603_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__1___redArg___closed__4, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__1___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__1___redArg___closed__4);
lean_inc(v_head_2573_);
v___x_2604_ = l_Lean_indentExpr(v_head_2573_);
v___x_2605_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2605_, 0, v___x_2603_);
lean_ctor_set(v___x_2605_, 1, v___x_2604_);
v___x_2606_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__1___redArg(v___x_2605_, v___y_2567_, v___y_2568_, v___y_2569_, v___y_2570_);
return v___x_2606_;
}
else
{
lean_object* v_val_2607_; lean_object* v_fst_2608_; size_t v___x_2609_; size_t v___x_2610_; uint8_t v___x_2611_; 
v_val_2607_ = lean_ctor_get(v___x_2602_, 0);
lean_inc(v_val_2607_);
lean_dec_ref_known(v___x_2602_, 1);
v_fst_2608_ = lean_ctor_get(v_val_2607_, 0);
lean_inc(v_fst_2608_);
lean_dec(v_val_2607_);
v___x_2609_ = lean_ptr_addr(v_head_2573_);
v___x_2610_ = lean_ptr_addr(v_fst_2608_);
lean_dec(v_fst_2608_);
v___x_2611_ = lean_usize_dec_eq(v___x_2609_, v___x_2610_);
if (v___x_2611_ == 0)
{
lean_object* v___x_2612_; lean_object* v___x_2613_; 
v___x_2612_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__1___redArg___closed__6, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__1___redArg___closed__6_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__1___redArg___closed__6);
v___x_2613_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__0(v___x_2612_, v___y_2561_, v___y_2562_, v___y_2563_, v___y_2564_, v___y_2565_, v___y_2566_, v___y_2567_, v___y_2568_, v___y_2569_, v___y_2570_);
v___y_2576_ = v___x_2613_;
goto v___jp_2575_;
}
else
{
v_as_x27_2559_ = v_tail_2574_;
v_b_2560_ = v___x_2596_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_2615_; lean_object* v___x_2617_; uint8_t v_isShared_2618_; uint8_t v_isSharedCheck_2622_; 
v_a_2615_ = lean_ctor_get(v___x_2597_, 0);
v_isSharedCheck_2622_ = !lean_is_exclusive(v___x_2597_);
if (v_isSharedCheck_2622_ == 0)
{
v___x_2617_ = v___x_2597_;
v_isShared_2618_ = v_isSharedCheck_2622_;
goto v_resetjp_2616_;
}
else
{
lean_inc(v_a_2615_);
lean_dec(v___x_2597_);
v___x_2617_ = lean_box(0);
v_isShared_2618_ = v_isSharedCheck_2622_;
goto v_resetjp_2616_;
}
v_resetjp_2616_:
{
lean_object* v___x_2620_; 
if (v_isShared_2618_ == 0)
{
v___x_2620_ = v___x_2617_;
goto v_reusejp_2619_;
}
else
{
lean_object* v_reuseFailAlloc_2621_; 
v_reuseFailAlloc_2621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2621_, 0, v_a_2615_);
v___x_2620_ = v_reuseFailAlloc_2621_;
goto v_reusejp_2619_;
}
v_reusejp_2619_:
{
return v___x_2620_;
}
}
}
v___jp_2575_:
{
if (lean_obj_tag(v___y_2576_) == 0)
{
lean_object* v_a_2577_; lean_object* v___x_2579_; uint8_t v_isShared_2580_; uint8_t v_isSharedCheck_2587_; 
v_a_2577_ = lean_ctor_get(v___y_2576_, 0);
v_isSharedCheck_2587_ = !lean_is_exclusive(v___y_2576_);
if (v_isSharedCheck_2587_ == 0)
{
v___x_2579_ = v___y_2576_;
v_isShared_2580_ = v_isSharedCheck_2587_;
goto v_resetjp_2578_;
}
else
{
lean_inc(v_a_2577_);
lean_dec(v___y_2576_);
v___x_2579_ = lean_box(0);
v_isShared_2580_ = v_isSharedCheck_2587_;
goto v_resetjp_2578_;
}
v_resetjp_2578_:
{
if (lean_obj_tag(v_a_2577_) == 0)
{
lean_object* v_a_2581_; lean_object* v___x_2583_; 
v_a_2581_ = lean_ctor_get(v_a_2577_, 0);
lean_inc(v_a_2581_);
lean_dec_ref_known(v_a_2577_, 1);
if (v_isShared_2580_ == 0)
{
lean_ctor_set(v___x_2579_, 0, v_a_2581_);
v___x_2583_ = v___x_2579_;
goto v_reusejp_2582_;
}
else
{
lean_object* v_reuseFailAlloc_2584_; 
v_reuseFailAlloc_2584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2584_, 0, v_a_2581_);
v___x_2583_ = v_reuseFailAlloc_2584_;
goto v_reusejp_2582_;
}
v_reusejp_2582_:
{
return v___x_2583_;
}
}
else
{
lean_object* v_a_2585_; 
lean_del_object(v___x_2579_);
v_a_2585_ = lean_ctor_get(v_a_2577_, 0);
lean_inc(v_a_2585_);
lean_dec_ref_known(v_a_2577_, 1);
v_as_x27_2559_ = v_tail_2574_;
v_b_2560_ = v_a_2585_;
goto _start;
}
}
}
else
{
lean_object* v_a_2588_; lean_object* v___x_2590_; uint8_t v_isShared_2591_; uint8_t v_isSharedCheck_2595_; 
v_a_2588_ = lean_ctor_get(v___y_2576_, 0);
v_isSharedCheck_2595_ = !lean_is_exclusive(v___y_2576_);
if (v_isSharedCheck_2595_ == 0)
{
v___x_2590_ = v___y_2576_;
v_isShared_2591_ = v_isSharedCheck_2595_;
goto v_resetjp_2589_;
}
else
{
lean_inc(v_a_2588_);
lean_dec(v___y_2576_);
v___x_2590_ = lean_box(0);
v_isShared_2591_ = v_isSharedCheck_2595_;
goto v_resetjp_2589_;
}
v_resetjp_2589_:
{
lean_object* v___x_2593_; 
if (v_isShared_2591_ == 0)
{
v___x_2593_ = v___x_2590_;
goto v_reusejp_2592_;
}
else
{
lean_object* v_reuseFailAlloc_2594_; 
v_reuseFailAlloc_2594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2594_, 0, v_a_2588_);
v___x_2593_ = v_reuseFailAlloc_2594_;
goto v_reusejp_2592_;
}
v_reusejp_2592_:
{
return v___x_2593_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__1___redArg___boxed(lean_object* v___x_2623_, lean_object* v___x_2624_, lean_object* v_as_x27_2625_, lean_object* v_b_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_){
_start:
{
lean_object* v_res_2638_; 
v_res_2638_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__1___redArg(v___x_2623_, v___x_2624_, v_as_x27_2625_, v_b_2626_, v___y_2627_, v___y_2628_, v___y_2629_, v___y_2630_, v___y_2631_, v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_);
lean_dec(v___y_2636_);
lean_dec_ref(v___y_2635_);
lean_dec(v___y_2634_);
lean_dec_ref(v___y_2633_);
lean_dec(v___y_2632_);
lean_dec_ref(v___y_2631_);
lean_dec(v___y_2630_);
lean_dec_ref(v___y_2629_);
lean_dec(v___y_2628_);
lean_dec(v___y_2627_);
lean_dec(v_as_x27_2625_);
lean_dec_ref(v___x_2624_);
lean_dec_ref(v___x_2623_);
return v_res_2638_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__1(lean_object* v_a_2639_, lean_object* v_a_2640_){
_start:
{
if (lean_obj_tag(v_a_2639_) == 0)
{
lean_object* v___x_2641_; 
v___x_2641_ = l_List_reverse___redArg(v_a_2640_);
return v___x_2641_;
}
else
{
lean_object* v_head_2642_; lean_object* v_tail_2643_; lean_object* v___x_2645_; uint8_t v_isShared_2646_; uint8_t v_isSharedCheck_2652_; 
v_head_2642_ = lean_ctor_get(v_a_2639_, 0);
v_tail_2643_ = lean_ctor_get(v_a_2639_, 1);
v_isSharedCheck_2652_ = !lean_is_exclusive(v_a_2639_);
if (v_isSharedCheck_2652_ == 0)
{
v___x_2645_ = v_a_2639_;
v_isShared_2646_ = v_isSharedCheck_2652_;
goto v_resetjp_2644_;
}
else
{
lean_inc(v_tail_2643_);
lean_inc(v_head_2642_);
lean_dec(v_a_2639_);
v___x_2645_ = lean_box(0);
v_isShared_2646_ = v_isSharedCheck_2652_;
goto v_resetjp_2644_;
}
v_resetjp_2644_:
{
lean_object* v_fst_2647_; lean_object* v___x_2649_; 
v_fst_2647_ = lean_ctor_get(v_head_2642_, 0);
lean_inc(v_fst_2647_);
lean_dec(v_head_2642_);
if (v_isShared_2646_ == 0)
{
lean_ctor_set(v___x_2645_, 1, v_a_2640_);
lean_ctor_set(v___x_2645_, 0, v_fst_2647_);
v___x_2649_ = v___x_2645_;
goto v_reusejp_2648_;
}
else
{
lean_object* v_reuseFailAlloc_2651_; 
v_reuseFailAlloc_2651_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2651_, 0, v_fst_2647_);
lean_ctor_set(v_reuseFailAlloc_2651_, 1, v_a_2640_);
v___x_2649_ = v_reuseFailAlloc_2651_;
goto v_reusejp_2648_;
}
v_reusejp_2648_:
{
v_a_2639_ = v_tail_2643_;
v_a_2640_ = v___x_2649_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7___redArg(lean_object* v_f_2653_, lean_object* v_keys_2654_, lean_object* v_vals_2655_, lean_object* v_i_2656_, lean_object* v_acc_2657_){
_start:
{
lean_object* v___x_2658_; uint8_t v___x_2659_; 
v___x_2658_ = lean_array_get_size(v_keys_2654_);
v___x_2659_ = lean_nat_dec_lt(v_i_2656_, v___x_2658_);
if (v___x_2659_ == 0)
{
lean_dec(v_i_2656_);
lean_dec(v_f_2653_);
return v_acc_2657_;
}
else
{
lean_object* v_k_2660_; lean_object* v_v_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; 
v_k_2660_ = lean_array_fget_borrowed(v_keys_2654_, v_i_2656_);
v_v_2661_ = lean_array_fget_borrowed(v_vals_2655_, v_i_2656_);
lean_inc(v_f_2653_);
lean_inc(v_v_2661_);
lean_inc(v_k_2660_);
v___x_2662_ = lean_apply_3(v_f_2653_, v_acc_2657_, v_k_2660_, v_v_2661_);
v___x_2663_ = lean_unsigned_to_nat(1u);
v___x_2664_ = lean_nat_add(v_i_2656_, v___x_2663_);
lean_dec(v_i_2656_);
v_i_2656_ = v___x_2664_;
v_acc_2657_ = v___x_2662_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7___redArg___boxed(lean_object* v_f_2666_, lean_object* v_keys_2667_, lean_object* v_vals_2668_, lean_object* v_i_2669_, lean_object* v_acc_2670_){
_start:
{
lean_object* v_res_2671_; 
v_res_2671_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7___redArg(v_f_2666_, v_keys_2667_, v_vals_2668_, v_i_2669_, v_acc_2670_);
lean_dec_ref(v_vals_2668_);
lean_dec_ref(v_keys_2667_);
return v_res_2671_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg(lean_object* v_f_2672_, lean_object* v_as_2673_, size_t v_i_2674_, size_t v_stop_2675_, lean_object* v_b_2676_){
_start:
{
lean_object* v___y_2678_; uint8_t v___x_2682_; 
v___x_2682_ = lean_usize_dec_eq(v_i_2674_, v_stop_2675_);
if (v___x_2682_ == 0)
{
lean_object* v___x_2683_; 
v___x_2683_ = lean_array_uget_borrowed(v_as_2673_, v_i_2674_);
switch(lean_obj_tag(v___x_2683_))
{
case 0:
{
lean_object* v_key_2684_; lean_object* v_val_2685_; lean_object* v___x_2686_; 
v_key_2684_ = lean_ctor_get(v___x_2683_, 0);
v_val_2685_ = lean_ctor_get(v___x_2683_, 1);
lean_inc(v_f_2672_);
lean_inc(v_val_2685_);
lean_inc(v_key_2684_);
v___x_2686_ = lean_apply_3(v_f_2672_, v_b_2676_, v_key_2684_, v_val_2685_);
v___y_2678_ = v___x_2686_;
goto v___jp_2677_;
}
case 1:
{
lean_object* v_node_2687_; lean_object* v___x_2688_; 
v_node_2687_ = lean_ctor_get(v___x_2683_, 0);
lean_inc(v_f_2672_);
v___x_2688_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_f_2672_, v_node_2687_, v_b_2676_);
v___y_2678_ = v___x_2688_;
goto v___jp_2677_;
}
default: 
{
v___y_2678_ = v_b_2676_;
goto v___jp_2677_;
}
}
}
else
{
lean_dec(v_f_2672_);
return v_b_2676_;
}
v___jp_2677_:
{
size_t v___x_2679_; size_t v___x_2680_; 
v___x_2679_ = ((size_t)1ULL);
v___x_2680_ = lean_usize_add(v_i_2674_, v___x_2679_);
v_i_2674_ = v___x_2680_;
v_b_2676_ = v___y_2678_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(lean_object* v_f_2689_, lean_object* v_x_2690_, lean_object* v_x_2691_){
_start:
{
if (lean_obj_tag(v_x_2690_) == 0)
{
lean_object* v_es_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; uint8_t v___x_2695_; 
v_es_2692_ = lean_ctor_get(v_x_2690_, 0);
v___x_2693_ = lean_unsigned_to_nat(0u);
v___x_2694_ = lean_array_get_size(v_es_2692_);
v___x_2695_ = lean_nat_dec_lt(v___x_2693_, v___x_2694_);
if (v___x_2695_ == 0)
{
lean_dec(v_f_2689_);
return v_x_2691_;
}
else
{
size_t v___x_2696_; size_t v___x_2697_; lean_object* v___x_2698_; 
v___x_2696_ = ((size_t)0ULL);
v___x_2697_ = lean_usize_of_nat(v___x_2694_);
v___x_2698_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg(v_f_2689_, v_es_2692_, v___x_2696_, v___x_2697_, v_x_2691_);
return v___x_2698_;
}
}
else
{
lean_object* v_ks_2699_; lean_object* v_vs_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; 
v_ks_2699_ = lean_ctor_get(v_x_2690_, 0);
v_vs_2700_ = lean_ctor_get(v_x_2690_, 1);
v___x_2701_ = lean_unsigned_to_nat(0u);
v___x_2702_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7___redArg(v_f_2689_, v_ks_2699_, v_vs_2700_, v___x_2701_, v_x_2691_);
return v___x_2702_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0_spec__1_spec__3_spec__5___redArg___boxed(lean_object* v_f_2703_, lean_object* v_x_2704_, lean_object* v_x_2705_){
_start:
{
lean_object* v_res_2706_; 
v_res_2706_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_f_2703_, v_x_2704_, v_x_2705_);
lean_dec_ref(v_x_2704_);
return v_res_2706_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___boxed(lean_object* v_f_2707_, lean_object* v_as_2708_, lean_object* v_i_2709_, lean_object* v_stop_2710_, lean_object* v_b_2711_){
_start:
{
size_t v_i_boxed_2712_; size_t v_stop_boxed_2713_; lean_object* v_res_2714_; 
v_i_boxed_2712_ = lean_unbox_usize(v_i_2709_);
lean_dec(v_i_2709_);
v_stop_boxed_2713_ = lean_unbox_usize(v_stop_2710_);
lean_dec(v_stop_2710_);
v_res_2714_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg(v_f_2707_, v_as_2708_, v_i_boxed_2712_, v_stop_boxed_2713_, v_b_2711_);
lean_dec_ref(v_as_2708_);
return v_res_2714_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0_spec__1___redArg___lam__0(lean_object* v_f_2715_, lean_object* v_x1_2716_, lean_object* v_x2_2717_, lean_object* v_x3_2718_){
_start:
{
lean_object* v___x_2719_; 
v___x_2719_ = lean_apply_3(v_f_2715_, v_x1_2716_, v_x2_2717_, v_x3_2718_);
return v___x_2719_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0_spec__1___redArg(lean_object* v___x_2720_, lean_object* v_map_2721_, lean_object* v_f_2722_, lean_object* v_init_2723_){
_start:
{
lean_object* v___f_2724_; lean_object* v___x_2725_; 
v___f_2724_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0_spec__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2724_, 0, v_f_2722_);
v___x_2725_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v___f_2724_, v_map_2721_, v_init_2723_);
return v___x_2725_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v___x_2726_, lean_object* v_map_2727_, lean_object* v_f_2728_, lean_object* v_init_2729_){
_start:
{
lean_object* v_res_2730_; 
v_res_2730_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0_spec__1___redArg(v___x_2726_, v_map_2727_, v_f_2728_, v_init_2729_);
lean_dec_ref(v_map_2727_);
lean_dec_ref(v___x_2726_);
return v_res_2730_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0___redArg___lam__0(lean_object* v_ps_2731_, lean_object* v_k_2732_, lean_object* v_v_2733_){
_start:
{
lean_object* v___x_2734_; lean_object* v___x_2735_; 
v___x_2734_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2734_, 0, v_k_2732_);
lean_ctor_set(v___x_2734_, 1, v_v_2733_);
v___x_2735_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2735_, 0, v___x_2734_);
lean_ctor_set(v___x_2735_, 1, v_ps_2731_);
return v___x_2735_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0___redArg(lean_object* v___x_2737_, lean_object* v_m_2738_){
_start:
{
lean_object* v___f_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; 
v___f_2739_ = ((lean_object*)(l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0___redArg___closed__0));
v___x_2740_ = lean_box(0);
v___x_2741_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0_spec__1___redArg(v___x_2737_, v_m_2738_, v___f_2739_, v___x_2740_);
return v___x_2741_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0___redArg___boxed(lean_object* v___x_2742_, lean_object* v_m_2743_){
_start:
{
lean_object* v_res_2744_; 
v_res_2744_ = l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0___redArg(v___x_2742_, v_m_2743_);
lean_dec_ref(v_m_2743_);
lean_dec_ref(v___x_2742_);
return v_res_2744_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0(lean_object* v___x_2745_, lean_object* v_s_2746_){
_start:
{
lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; 
v___x_2747_ = l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0___redArg(v___x_2745_, v_s_2746_);
v___x_2748_ = lean_box(0);
v___x_2749_ = l_List_mapTR_loop___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__1(v___x_2747_, v___x_2748_);
return v___x_2749_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0___boxed(lean_object* v___x_2750_, lean_object* v_s_2751_){
_start:
{
lean_object* v_res_2752_; 
v_res_2752_ = l_Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0(v___x_2750_, v_s_2751_);
lean_dec_ref(v_s_2751_);
lean_dec_ref(v___x_2750_);
return v_res_2752_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable(lean_object* v_a_2753_, lean_object* v_a_2754_, lean_object* v_a_2755_, lean_object* v_a_2756_, lean_object* v_a_2757_, lean_object* v_a_2758_, lean_object* v_a_2759_, lean_object* v_a_2760_, lean_object* v_a_2761_, lean_object* v_a_2762_){
_start:
{
lean_object* v___x_2764_; lean_object* v_toGoalState_2765_; lean_object* v_enodeMap_2766_; lean_object* v_congrTable_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; 
v___x_2764_ = lean_st_ref_get(v_a_2753_);
v_toGoalState_2765_ = lean_ctor_get(v___x_2764_, 0);
lean_inc_ref(v_toGoalState_2765_);
lean_dec(v___x_2764_);
v_enodeMap_2766_ = lean_ctor_get(v_toGoalState_2765_, 1);
lean_inc_ref(v_enodeMap_2766_);
v_congrTable_2767_ = lean_ctor_get(v_toGoalState_2765_, 4);
lean_inc_ref(v_congrTable_2767_);
lean_dec_ref(v_toGoalState_2765_);
v___x_2768_ = l_Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0(v_enodeMap_2766_, v_congrTable_2767_);
v___x_2769_ = lean_box(0);
v___x_2770_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__1___redArg(v_enodeMap_2766_, v_congrTable_2767_, v___x_2768_, v___x_2769_, v_a_2753_, v_a_2754_, v_a_2755_, v_a_2756_, v_a_2757_, v_a_2758_, v_a_2759_, v_a_2760_, v_a_2761_, v_a_2762_);
lean_dec(v___x_2768_);
lean_dec_ref(v_congrTable_2767_);
lean_dec_ref(v_enodeMap_2766_);
if (lean_obj_tag(v___x_2770_) == 0)
{
lean_object* v___x_2772_; uint8_t v_isShared_2773_; uint8_t v_isSharedCheck_2777_; 
v_isSharedCheck_2777_ = !lean_is_exclusive(v___x_2770_);
if (v_isSharedCheck_2777_ == 0)
{
lean_object* v_unused_2778_; 
v_unused_2778_ = lean_ctor_get(v___x_2770_, 0);
lean_dec(v_unused_2778_);
v___x_2772_ = v___x_2770_;
v_isShared_2773_ = v_isSharedCheck_2777_;
goto v_resetjp_2771_;
}
else
{
lean_dec(v___x_2770_);
v___x_2772_ = lean_box(0);
v_isShared_2773_ = v_isSharedCheck_2777_;
goto v_resetjp_2771_;
}
v_resetjp_2771_:
{
lean_object* v___x_2775_; 
if (v_isShared_2773_ == 0)
{
lean_ctor_set(v___x_2772_, 0, v___x_2769_);
v___x_2775_ = v___x_2772_;
goto v_reusejp_2774_;
}
else
{
lean_object* v_reuseFailAlloc_2776_; 
v_reuseFailAlloc_2776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2776_, 0, v___x_2769_);
v___x_2775_ = v_reuseFailAlloc_2776_;
goto v_reusejp_2774_;
}
v_reusejp_2774_:
{
return v___x_2775_;
}
}
}
else
{
return v___x_2770_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable___boxed(lean_object* v_a_2779_, lean_object* v_a_2780_, lean_object* v_a_2781_, lean_object* v_a_2782_, lean_object* v_a_2783_, lean_object* v_a_2784_, lean_object* v_a_2785_, lean_object* v_a_2786_, lean_object* v_a_2787_, lean_object* v_a_2788_, lean_object* v_a_2789_){
_start:
{
lean_object* v_res_2790_; 
v_res_2790_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable(v_a_2779_, v_a_2780_, v_a_2781_, v_a_2782_, v_a_2783_, v_a_2784_, v_a_2785_, v_a_2786_, v_a_2787_, v_a_2788_);
lean_dec(v_a_2788_);
lean_dec_ref(v_a_2787_);
lean_dec(v_a_2786_);
lean_dec_ref(v_a_2785_);
lean_dec(v_a_2784_);
lean_dec_ref(v_a_2783_);
lean_dec(v_a_2782_);
lean_dec_ref(v_a_2781_);
lean_dec(v_a_2780_);
lean_dec(v_a_2779_);
return v_res_2790_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__1(lean_object* v___x_2791_, lean_object* v___x_2792_, lean_object* v_as_2793_, lean_object* v_as_x27_2794_, lean_object* v_b_2795_, lean_object* v_a_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_, lean_object* v___y_2803_, lean_object* v___y_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_){
_start:
{
lean_object* v___x_2808_; 
v___x_2808_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__1___redArg(v___x_2791_, v___x_2792_, v_as_x27_2794_, v_b_2795_, v___y_2797_, v___y_2798_, v___y_2799_, v___y_2800_, v___y_2801_, v___y_2802_, v___y_2803_, v___y_2804_, v___y_2805_, v___y_2806_);
return v___x_2808_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__1___boxed(lean_object** _args){
lean_object* v___x_2809_ = _args[0];
lean_object* v___x_2810_ = _args[1];
lean_object* v_as_2811_ = _args[2];
lean_object* v_as_x27_2812_ = _args[3];
lean_object* v_b_2813_ = _args[4];
lean_object* v_a_2814_ = _args[5];
lean_object* v___y_2815_ = _args[6];
lean_object* v___y_2816_ = _args[7];
lean_object* v___y_2817_ = _args[8];
lean_object* v___y_2818_ = _args[9];
lean_object* v___y_2819_ = _args[10];
lean_object* v___y_2820_ = _args[11];
lean_object* v___y_2821_ = _args[12];
lean_object* v___y_2822_ = _args[13];
lean_object* v___y_2823_ = _args[14];
lean_object* v___y_2824_ = _args[15];
lean_object* v___y_2825_ = _args[16];
_start:
{
lean_object* v_res_2826_; 
v_res_2826_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__1(v___x_2809_, v___x_2810_, v_as_2811_, v_as_x27_2812_, v_b_2813_, v_a_2814_, v___y_2815_, v___y_2816_, v___y_2817_, v___y_2818_, v___y_2819_, v___y_2820_, v___y_2821_, v___y_2822_, v___y_2823_, v___y_2824_);
lean_dec(v___y_2824_);
lean_dec_ref(v___y_2823_);
lean_dec(v___y_2822_);
lean_dec_ref(v___y_2821_);
lean_dec(v___y_2820_);
lean_dec_ref(v___y_2819_);
lean_dec(v___y_2818_);
lean_dec_ref(v___y_2817_);
lean_dec(v___y_2816_);
lean_dec(v___y_2815_);
lean_dec(v_as_x27_2812_);
lean_dec(v_as_2811_);
lean_dec_ref(v___x_2810_);
lean_dec_ref(v___x_2809_);
return v_res_2826_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0(lean_object* v___x_2827_, lean_object* v_00_u03b2_2828_, lean_object* v_m_2829_){
_start:
{
lean_object* v___x_2830_; 
v___x_2830_ = l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0___redArg(v___x_2827_, v_m_2829_);
return v___x_2830_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0___boxed(lean_object* v___x_2831_, lean_object* v_00_u03b2_2832_, lean_object* v_m_2833_){
_start:
{
lean_object* v_res_2834_; 
v_res_2834_ = l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0(v___x_2831_, v_00_u03b2_2832_, v_m_2833_);
lean_dec_ref(v_m_2833_);
lean_dec_ref(v___x_2831_);
return v_res_2834_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0_spec__1(lean_object* v___x_2835_, lean_object* v_00_u03c3_2836_, lean_object* v_00_u03b2_2837_, lean_object* v_map_2838_, lean_object* v_f_2839_, lean_object* v_init_2840_){
_start:
{
lean_object* v___x_2841_; 
v___x_2841_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0_spec__1___redArg(v___x_2835_, v_map_2838_, v_f_2839_, v_init_2840_);
return v___x_2841_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0_spec__1___boxed(lean_object* v___x_2842_, lean_object* v_00_u03c3_2843_, lean_object* v_00_u03b2_2844_, lean_object* v_map_2845_, lean_object* v_f_2846_, lean_object* v_init_2847_){
_start:
{
lean_object* v_res_2848_; 
v_res_2848_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0_spec__1(v___x_2842_, v_00_u03c3_2843_, v_00_u03b2_2844_, v_map_2845_, v_f_2846_, v_init_2847_);
lean_dec_ref(v_map_2845_);
lean_dec_ref(v___x_2842_);
return v_res_2848_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_map_2849_, lean_object* v_f_2850_, lean_object* v_init_2851_){
_start:
{
lean_object* v___x_2852_; 
v___x_2852_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_f_2850_, v_map_2849_, v_init_2851_);
return v___x_2852_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_map_2853_, lean_object* v_f_2854_, lean_object* v_init_2855_){
_start:
{
lean_object* v_res_2856_; 
v_res_2856_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0_spec__1_spec__3___redArg(v_map_2853_, v_f_2854_, v_init_2855_);
lean_dec_ref(v_map_2853_);
return v_res_2856_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0_spec__1_spec__3(lean_object* v___x_2857_, lean_object* v_00_u03c3_2858_, lean_object* v_00_u03b2_2859_, lean_object* v_map_2860_, lean_object* v_f_2861_, lean_object* v_init_2862_){
_start:
{
lean_object* v___x_2863_; 
v___x_2863_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_f_2861_, v_map_2860_, v_init_2862_);
return v___x_2863_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v___x_2864_, lean_object* v_00_u03c3_2865_, lean_object* v_00_u03b2_2866_, lean_object* v_map_2867_, lean_object* v_f_2868_, lean_object* v_init_2869_){
_start:
{
lean_object* v_res_2870_; 
v_res_2870_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0_spec__1_spec__3(v___x_2864_, v_00_u03c3_2865_, v_00_u03b2_2866_, v_map_2867_, v_f_2868_, v_init_2869_);
lean_dec_ref(v_map_2867_);
lean_dec_ref(v___x_2864_);
return v_res_2870_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0_spec__1_spec__3_spec__5(lean_object* v_00_u03c3_2871_, lean_object* v_00_u03b1_2872_, lean_object* v_00_u03b2_2873_, lean_object* v_f_2874_, lean_object* v_x_2875_, lean_object* v_x_2876_){
_start:
{
lean_object* v___x_2877_; 
v___x_2877_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_f_2874_, v_x_2875_, v_x_2876_);
return v___x_2877_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0_spec__1_spec__3_spec__5___boxed(lean_object* v_00_u03c3_2878_, lean_object* v_00_u03b1_2879_, lean_object* v_00_u03b2_2880_, lean_object* v_f_2881_, lean_object* v_x_2882_, lean_object* v_x_2883_){
_start:
{
lean_object* v_res_2884_; 
v_res_2884_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0_spec__1_spec__3_spec__5(v_00_u03c3_2878_, v_00_u03b1_2879_, v_00_u03b2_2880_, v_f_2881_, v_x_2882_, v_x_2883_);
lean_dec_ref(v_x_2882_);
return v_res_2884_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6(lean_object* v_00_u03b1_2885_, lean_object* v_00_u03b2_2886_, lean_object* v_00_u03c3_2887_, lean_object* v_f_2888_, lean_object* v_as_2889_, size_t v_i_2890_, size_t v_stop_2891_, lean_object* v_b_2892_){
_start:
{
lean_object* v___x_2893_; 
v___x_2893_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg(v_f_2888_, v_as_2889_, v_i_2890_, v_stop_2891_, v_b_2892_);
return v___x_2893_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___boxed(lean_object* v_00_u03b1_2894_, lean_object* v_00_u03b2_2895_, lean_object* v_00_u03c3_2896_, lean_object* v_f_2897_, lean_object* v_as_2898_, lean_object* v_i_2899_, lean_object* v_stop_2900_, lean_object* v_b_2901_){
_start:
{
size_t v_i_boxed_2902_; size_t v_stop_boxed_2903_; lean_object* v_res_2904_; 
v_i_boxed_2902_ = lean_unbox_usize(v_i_2899_);
lean_dec(v_i_2899_);
v_stop_boxed_2903_ = lean_unbox_usize(v_stop_2900_);
lean_dec(v_stop_2900_);
v_res_2904_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6(v_00_u03b1_2894_, v_00_u03b2_2895_, v_00_u03c3_2896_, v_f_2897_, v_as_2898_, v_i_boxed_2902_, v_stop_boxed_2903_, v_b_2901_);
lean_dec_ref(v_as_2898_);
return v_res_2904_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7(lean_object* v_00_u03c3_2905_, lean_object* v_00_u03b1_2906_, lean_object* v_00_u03b2_2907_, lean_object* v_f_2908_, lean_object* v_keys_2909_, lean_object* v_vals_2910_, lean_object* v_heq_2911_, lean_object* v_i_2912_, lean_object* v_acc_2913_){
_start:
{
lean_object* v___x_2914_; 
v___x_2914_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7___redArg(v_f_2908_, v_keys_2909_, v_vals_2910_, v_i_2912_, v_acc_2913_);
return v___x_2914_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7___boxed(lean_object* v_00_u03c3_2915_, lean_object* v_00_u03b1_2916_, lean_object* v_00_u03b2_2917_, lean_object* v_f_2918_, lean_object* v_keys_2919_, lean_object* v_vals_2920_, lean_object* v_heq_2921_, lean_object* v_i_2922_, lean_object* v_acc_2923_){
_start:
{
lean_object* v_res_2924_; 
v_res_2924_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7(v_00_u03c3_2915_, v_00_u03b1_2916_, v_00_u03b2_2917_, v_f_2918_, v_keys_2919_, v_vals_2920_, v_heq_2921_, v_i_2922_, v_acc_2923_);
lean_dec_ref(v_vals_2920_);
lean_dec_ref(v_keys_2919_);
return v_res_2924_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_Grind_checkInvariants_spec__0(lean_object* v_opts_2925_, lean_object* v_opt_2926_){
_start:
{
lean_object* v_name_2927_; lean_object* v_defValue_2928_; lean_object* v_map_2929_; lean_object* v___x_2930_; 
v_name_2927_ = lean_ctor_get(v_opt_2926_, 0);
v_defValue_2928_ = lean_ctor_get(v_opt_2926_, 1);
v_map_2929_ = lean_ctor_get(v_opts_2925_, 0);
v___x_2930_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2929_, v_name_2927_);
if (lean_obj_tag(v___x_2930_) == 0)
{
uint8_t v___x_2931_; 
v___x_2931_ = lean_unbox(v_defValue_2928_);
return v___x_2931_;
}
else
{
lean_object* v_val_2932_; 
v_val_2932_ = lean_ctor_get(v___x_2930_, 0);
lean_inc(v_val_2932_);
lean_dec_ref_known(v___x_2930_, 1);
if (lean_obj_tag(v_val_2932_) == 1)
{
uint8_t v_v_2933_; 
v_v_2933_ = lean_ctor_get_uint8(v_val_2932_, 0);
lean_dec_ref_known(v_val_2932_, 0);
return v_v_2933_;
}
else
{
uint8_t v___x_2934_; 
lean_dec(v_val_2932_);
v___x_2934_ = lean_unbox(v_defValue_2928_);
return v___x_2934_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Grind_checkInvariants_spec__0___boxed(lean_object* v_opts_2935_, lean_object* v_opt_2936_){
_start:
{
uint8_t v_res_2937_; lean_object* v_r_2938_; 
v_res_2937_ = l_Lean_Option_get___at___00Lean_Meta_Grind_checkInvariants_spec__0(v_opts_2935_, v_opt_2936_);
lean_dec_ref(v_opt_2936_);
lean_dec_ref(v_opts_2935_);
v_r_2938_ = lean_box(v_res_2937_);
return v_r_2938_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__2_spec__5___closed__2(void){
_start:
{
lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; 
v___x_2941_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__2_spec__5___closed__1));
v___x_2942_ = lean_unsigned_to_nat(8u);
v___x_2943_ = lean_unsigned_to_nat(170u);
v___x_2944_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__2_spec__5___closed__0));
v___x_2945_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__0));
v___x_2946_ = l_mkPanicMessageWithDecl(v___x_2945_, v___x_2944_, v___x_2943_, v___x_2942_, v___x_2941_);
return v___x_2946_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__2_spec__5(lean_object* v_as_2947_, size_t v_sz_2948_, size_t v_i_2949_, lean_object* v_b_2950_, lean_object* v___y_2951_, lean_object* v___y_2952_, lean_object* v___y_2953_, lean_object* v___y_2954_, lean_object* v___y_2955_, lean_object* v___y_2956_, lean_object* v___y_2957_, lean_object* v___y_2958_, lean_object* v___y_2959_, lean_object* v___y_2960_){
_start:
{
uint8_t v___x_2962_; 
v___x_2962_ = lean_usize_dec_lt(v_i_2949_, v_sz_2948_);
if (v___x_2962_ == 0)
{
lean_object* v___x_2963_; 
v___x_2963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2963_, 0, v_b_2950_);
return v___x_2963_;
}
else
{
lean_object* v_snd_2964_; lean_object* v___x_2966_; uint8_t v_isShared_2967_; uint8_t v_isSharedCheck_3061_; 
v_snd_2964_ = lean_ctor_get(v_b_2950_, 1);
v_isSharedCheck_3061_ = !lean_is_exclusive(v_b_2950_);
if (v_isSharedCheck_3061_ == 0)
{
lean_object* v_unused_3062_; 
v_unused_3062_ = lean_ctor_get(v_b_2950_, 0);
lean_dec(v_unused_3062_);
v___x_2966_ = v_b_2950_;
v_isShared_2967_ = v_isSharedCheck_3061_;
goto v_resetjp_2965_;
}
else
{
lean_inc(v_snd_2964_);
lean_dec(v_b_2950_);
v___x_2966_ = lean_box(0);
v_isShared_2967_ = v_isSharedCheck_3061_;
goto v_resetjp_2965_;
}
v_resetjp_2965_:
{
lean_object* v___x_2968_; lean_object* v_a_2970_; lean_object* v___x_2977_; lean_object* v_a_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; 
v___x_2968_ = lean_box(0);
v___x_2977_ = lean_box(0);
v_a_2978_ = lean_array_uget_borrowed(v_as_2947_, v_i_2949_);
v___x_2979_ = lean_st_ref_get(v___y_2951_);
lean_inc(v_a_2978_);
v___x_2980_ = l_Lean_Meta_Grind_Goal_getENode(v___x_2979_, v_a_2978_, v___y_2957_, v___y_2958_, v___y_2959_, v___y_2960_);
lean_dec(v___x_2979_);
if (lean_obj_tag(v___x_2980_) == 0)
{
lean_object* v_a_2981_; lean_object* v___y_2983_; lean_object* v___y_2984_; lean_object* v___y_2985_; lean_object* v___y_2986_; lean_object* v___y_2987_; lean_object* v___y_2988_; lean_object* v___y_2989_; lean_object* v___y_2990_; lean_object* v___y_2991_; lean_object* v___y_2992_; lean_object* v_self_3003_; uint8_t v_interpreted_3004_; lean_object* v___x_3005_; 
v_a_2981_ = lean_ctor_get(v___x_2980_, 0);
lean_inc(v_a_2981_);
lean_dec_ref_known(v___x_2980_, 1);
v_self_3003_ = lean_ctor_get(v_a_2981_, 0);
v_interpreted_3004_ = lean_ctor_get_uint8(v_a_2981_, sizeof(void*)*12 + 1);
lean_inc_ref(v_self_3003_);
v___x_3005_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents(v_self_3003_, v___y_2951_, v___y_2952_, v___y_2953_, v___y_2954_, v___y_2955_, v___y_2956_, v___y_2957_, v___y_2958_, v___y_2959_, v___y_2960_);
if (lean_obj_tag(v___x_3005_) == 0)
{
lean_dec_ref_known(v___x_3005_, 1);
if (v_interpreted_3004_ == 0)
{
lean_dec(v_snd_2964_);
v___y_2983_ = v___y_2951_;
v___y_2984_ = v___y_2952_;
v___y_2985_ = v___y_2953_;
v___y_2986_ = v___y_2954_;
v___y_2987_ = v___y_2955_;
v___y_2988_ = v___y_2956_;
v___y_2989_ = v___y_2957_;
v___y_2990_ = v___y_2958_;
v___y_2991_ = v___y_2959_;
v___y_2992_ = v___y_2960_;
goto v___jp_2982_;
}
else
{
lean_object* v___x_3006_; 
lean_inc_ref(v_self_3003_);
v___x_3006_ = l_Lean_Meta_Sym_Canon_normNumLit_x3f(v_self_3003_, v___y_2957_, v___y_2958_, v___y_2959_, v___y_2960_);
if (lean_obj_tag(v___x_3006_) == 0)
{
lean_object* v_a_3007_; 
v_a_3007_ = lean_ctor_get(v___x_3006_, 0);
lean_inc(v_a_3007_);
lean_dec_ref_known(v___x_3006_, 1);
if (lean_obj_tag(v_a_3007_) == 0)
{
lean_dec(v_snd_2964_);
v___y_2983_ = v___y_2951_;
v___y_2984_ = v___y_2952_;
v___y_2985_ = v___y_2953_;
v___y_2986_ = v___y_2954_;
v___y_2987_ = v___y_2955_;
v___y_2988_ = v___y_2956_;
v___y_2989_ = v___y_2957_;
v___y_2990_ = v___y_2958_;
v___y_2991_ = v___y_2959_;
v___y_2992_ = v___y_2960_;
goto v___jp_2982_;
}
else
{
lean_object* v___x_3009_; uint8_t v_isShared_3010_; uint8_t v_isSharedCheck_3035_; 
lean_dec(v_a_2981_);
v_isSharedCheck_3035_ = !lean_is_exclusive(v_a_3007_);
if (v_isSharedCheck_3035_ == 0)
{
lean_object* v_unused_3036_; 
v_unused_3036_ = lean_ctor_get(v_a_3007_, 0);
lean_dec(v_unused_3036_);
v___x_3009_ = v_a_3007_;
v_isShared_3010_ = v_isSharedCheck_3035_;
goto v_resetjp_3008_;
}
else
{
lean_dec(v_a_3007_);
v___x_3009_ = lean_box(0);
v_isShared_3010_ = v_isSharedCheck_3035_;
goto v_resetjp_3008_;
}
v_resetjp_3008_:
{
lean_object* v___x_3011_; lean_object* v___x_3012_; 
v___x_3011_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__2_spec__5___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__2_spec__5___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__2_spec__5___closed__2);
v___x_3012_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__0(v___x_3011_, v___y_2951_, v___y_2952_, v___y_2953_, v___y_2954_, v___y_2955_, v___y_2956_, v___y_2957_, v___y_2958_, v___y_2959_, v___y_2960_);
if (lean_obj_tag(v___x_3012_) == 0)
{
lean_object* v_a_3013_; lean_object* v___x_3015_; uint8_t v_isShared_3016_; uint8_t v_isSharedCheck_3026_; 
v_a_3013_ = lean_ctor_get(v___x_3012_, 0);
v_isSharedCheck_3026_ = !lean_is_exclusive(v___x_3012_);
if (v_isSharedCheck_3026_ == 0)
{
v___x_3015_ = v___x_3012_;
v_isShared_3016_ = v_isSharedCheck_3026_;
goto v_resetjp_3014_;
}
else
{
lean_inc(v_a_3013_);
lean_dec(v___x_3012_);
v___x_3015_ = lean_box(0);
v_isShared_3016_ = v_isSharedCheck_3026_;
goto v_resetjp_3014_;
}
v_resetjp_3014_:
{
if (lean_obj_tag(v_a_3013_) == 0)
{
lean_object* v_a_3017_; lean_object* v___x_3019_; 
lean_del_object(v___x_2966_);
v_a_3017_ = lean_ctor_get(v_a_3013_, 0);
lean_inc(v_a_3017_);
lean_dec_ref_known(v_a_3013_, 1);
if (v_isShared_3010_ == 0)
{
lean_ctor_set(v___x_3009_, 0, v_a_3017_);
v___x_3019_ = v___x_3009_;
goto v_reusejp_3018_;
}
else
{
lean_object* v_reuseFailAlloc_3024_; 
v_reuseFailAlloc_3024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3024_, 0, v_a_3017_);
v___x_3019_ = v_reuseFailAlloc_3024_;
goto v_reusejp_3018_;
}
v_reusejp_3018_:
{
lean_object* v___x_3020_; lean_object* v___x_3022_; 
v___x_3020_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3020_, 0, v___x_3019_);
lean_ctor_set(v___x_3020_, 1, v_snd_2964_);
if (v_isShared_3016_ == 0)
{
lean_ctor_set(v___x_3015_, 0, v___x_3020_);
v___x_3022_ = v___x_3015_;
goto v_reusejp_3021_;
}
else
{
lean_object* v_reuseFailAlloc_3023_; 
v_reuseFailAlloc_3023_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3023_, 0, v___x_3020_);
v___x_3022_ = v_reuseFailAlloc_3023_;
goto v_reusejp_3021_;
}
v_reusejp_3021_:
{
return v___x_3022_;
}
}
}
else
{
lean_object* v_a_3025_; 
lean_del_object(v___x_3015_);
lean_del_object(v___x_3009_);
lean_dec(v_snd_2964_);
v_a_3025_ = lean_ctor_get(v_a_3013_, 0);
lean_inc(v_a_3025_);
lean_dec_ref_known(v_a_3013_, 1);
v_a_2970_ = v_a_3025_;
goto v___jp_2969_;
}
}
}
else
{
lean_object* v_a_3027_; lean_object* v___x_3029_; uint8_t v_isShared_3030_; uint8_t v_isSharedCheck_3034_; 
lean_del_object(v___x_3009_);
lean_del_object(v___x_2966_);
lean_dec(v_snd_2964_);
v_a_3027_ = lean_ctor_get(v___x_3012_, 0);
v_isSharedCheck_3034_ = !lean_is_exclusive(v___x_3012_);
if (v_isSharedCheck_3034_ == 0)
{
v___x_3029_ = v___x_3012_;
v_isShared_3030_ = v_isSharedCheck_3034_;
goto v_resetjp_3028_;
}
else
{
lean_inc(v_a_3027_);
lean_dec(v___x_3012_);
v___x_3029_ = lean_box(0);
v_isShared_3030_ = v_isSharedCheck_3034_;
goto v_resetjp_3028_;
}
v_resetjp_3028_:
{
lean_object* v___x_3032_; 
if (v_isShared_3030_ == 0)
{
v___x_3032_ = v___x_3029_;
goto v_reusejp_3031_;
}
else
{
lean_object* v_reuseFailAlloc_3033_; 
v_reuseFailAlloc_3033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3033_, 0, v_a_3027_);
v___x_3032_ = v_reuseFailAlloc_3033_;
goto v_reusejp_3031_;
}
v_reusejp_3031_:
{
return v___x_3032_;
}
}
}
}
}
}
else
{
lean_object* v_a_3037_; lean_object* v___x_3039_; uint8_t v_isShared_3040_; uint8_t v_isSharedCheck_3044_; 
lean_dec(v_a_2981_);
lean_del_object(v___x_2966_);
lean_dec(v_snd_2964_);
v_a_3037_ = lean_ctor_get(v___x_3006_, 0);
v_isSharedCheck_3044_ = !lean_is_exclusive(v___x_3006_);
if (v_isSharedCheck_3044_ == 0)
{
v___x_3039_ = v___x_3006_;
v_isShared_3040_ = v_isSharedCheck_3044_;
goto v_resetjp_3038_;
}
else
{
lean_inc(v_a_3037_);
lean_dec(v___x_3006_);
v___x_3039_ = lean_box(0);
v_isShared_3040_ = v_isSharedCheck_3044_;
goto v_resetjp_3038_;
}
v_resetjp_3038_:
{
lean_object* v___x_3042_; 
if (v_isShared_3040_ == 0)
{
v___x_3042_ = v___x_3039_;
goto v_reusejp_3041_;
}
else
{
lean_object* v_reuseFailAlloc_3043_; 
v_reuseFailAlloc_3043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3043_, 0, v_a_3037_);
v___x_3042_ = v_reuseFailAlloc_3043_;
goto v_reusejp_3041_;
}
v_reusejp_3041_:
{
return v___x_3042_;
}
}
}
}
}
else
{
lean_object* v_a_3045_; lean_object* v___x_3047_; uint8_t v_isShared_3048_; uint8_t v_isSharedCheck_3052_; 
lean_dec(v_a_2981_);
lean_del_object(v___x_2966_);
lean_dec(v_snd_2964_);
v_a_3045_ = lean_ctor_get(v___x_3005_, 0);
v_isSharedCheck_3052_ = !lean_is_exclusive(v___x_3005_);
if (v_isSharedCheck_3052_ == 0)
{
v___x_3047_ = v___x_3005_;
v_isShared_3048_ = v_isSharedCheck_3052_;
goto v_resetjp_3046_;
}
else
{
lean_inc(v_a_3045_);
lean_dec(v___x_3005_);
v___x_3047_ = lean_box(0);
v_isShared_3048_ = v_isSharedCheck_3052_;
goto v_resetjp_3046_;
}
v_resetjp_3046_:
{
lean_object* v___x_3050_; 
if (v_isShared_3048_ == 0)
{
v___x_3050_ = v___x_3047_;
goto v_reusejp_3049_;
}
else
{
lean_object* v_reuseFailAlloc_3051_; 
v_reuseFailAlloc_3051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3051_, 0, v_a_3045_);
v___x_3050_ = v_reuseFailAlloc_3051_;
goto v_reusejp_3049_;
}
v_reusejp_3049_:
{
return v___x_3050_;
}
}
}
v___jp_2982_:
{
uint8_t v___x_2993_; 
v___x_2993_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_2981_);
if (v___x_2993_ == 0)
{
lean_dec(v_a_2981_);
v_a_2970_ = v___x_2977_;
goto v___jp_2969_;
}
else
{
lean_object* v___x_2994_; 
v___x_2994_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc(v_a_2981_, v___y_2983_, v___y_2984_, v___y_2985_, v___y_2986_, v___y_2987_, v___y_2988_, v___y_2989_, v___y_2990_, v___y_2991_, v___y_2992_);
if (lean_obj_tag(v___x_2994_) == 0)
{
lean_dec_ref_known(v___x_2994_, 1);
v_a_2970_ = v___x_2977_;
goto v___jp_2969_;
}
else
{
lean_object* v_a_2995_; lean_object* v___x_2997_; uint8_t v_isShared_2998_; uint8_t v_isSharedCheck_3002_; 
lean_del_object(v___x_2966_);
v_a_2995_ = lean_ctor_get(v___x_2994_, 0);
v_isSharedCheck_3002_ = !lean_is_exclusive(v___x_2994_);
if (v_isSharedCheck_3002_ == 0)
{
v___x_2997_ = v___x_2994_;
v_isShared_2998_ = v_isSharedCheck_3002_;
goto v_resetjp_2996_;
}
else
{
lean_inc(v_a_2995_);
lean_dec(v___x_2994_);
v___x_2997_ = lean_box(0);
v_isShared_2998_ = v_isSharedCheck_3002_;
goto v_resetjp_2996_;
}
v_resetjp_2996_:
{
lean_object* v___x_3000_; 
if (v_isShared_2998_ == 0)
{
v___x_3000_ = v___x_2997_;
goto v_reusejp_2999_;
}
else
{
lean_object* v_reuseFailAlloc_3001_; 
v_reuseFailAlloc_3001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3001_, 0, v_a_2995_);
v___x_3000_ = v_reuseFailAlloc_3001_;
goto v_reusejp_2999_;
}
v_reusejp_2999_:
{
return v___x_3000_;
}
}
}
}
}
}
else
{
lean_object* v_a_3053_; lean_object* v___x_3055_; uint8_t v_isShared_3056_; uint8_t v_isSharedCheck_3060_; 
lean_del_object(v___x_2966_);
lean_dec(v_snd_2964_);
v_a_3053_ = lean_ctor_get(v___x_2980_, 0);
v_isSharedCheck_3060_ = !lean_is_exclusive(v___x_2980_);
if (v_isSharedCheck_3060_ == 0)
{
v___x_3055_ = v___x_2980_;
v_isShared_3056_ = v_isSharedCheck_3060_;
goto v_resetjp_3054_;
}
else
{
lean_inc(v_a_3053_);
lean_dec(v___x_2980_);
v___x_3055_ = lean_box(0);
v_isShared_3056_ = v_isSharedCheck_3060_;
goto v_resetjp_3054_;
}
v_resetjp_3054_:
{
lean_object* v___x_3058_; 
if (v_isShared_3056_ == 0)
{
v___x_3058_ = v___x_3055_;
goto v_reusejp_3057_;
}
else
{
lean_object* v_reuseFailAlloc_3059_; 
v_reuseFailAlloc_3059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3059_, 0, v_a_3053_);
v___x_3058_ = v_reuseFailAlloc_3059_;
goto v_reusejp_3057_;
}
v_reusejp_3057_:
{
return v___x_3058_;
}
}
}
v___jp_2969_:
{
lean_object* v___x_2972_; 
if (v_isShared_2967_ == 0)
{
lean_ctor_set(v___x_2966_, 1, v_a_2970_);
lean_ctor_set(v___x_2966_, 0, v___x_2968_);
v___x_2972_ = v___x_2966_;
goto v_reusejp_2971_;
}
else
{
lean_object* v_reuseFailAlloc_2976_; 
v_reuseFailAlloc_2976_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2976_, 0, v___x_2968_);
lean_ctor_set(v_reuseFailAlloc_2976_, 1, v_a_2970_);
v___x_2972_ = v_reuseFailAlloc_2976_;
goto v_reusejp_2971_;
}
v_reusejp_2971_:
{
size_t v___x_2973_; size_t v___x_2974_; 
v___x_2973_ = ((size_t)1ULL);
v___x_2974_ = lean_usize_add(v_i_2949_, v___x_2973_);
v_i_2949_ = v___x_2974_;
v_b_2950_ = v___x_2972_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__2_spec__5___boxed(lean_object* v_as_3063_, lean_object* v_sz_3064_, lean_object* v_i_3065_, lean_object* v_b_3066_, lean_object* v___y_3067_, lean_object* v___y_3068_, lean_object* v___y_3069_, lean_object* v___y_3070_, lean_object* v___y_3071_, lean_object* v___y_3072_, lean_object* v___y_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_){
_start:
{
size_t v_sz_boxed_3078_; size_t v_i_boxed_3079_; lean_object* v_res_3080_; 
v_sz_boxed_3078_ = lean_unbox_usize(v_sz_3064_);
lean_dec(v_sz_3064_);
v_i_boxed_3079_ = lean_unbox_usize(v_i_3065_);
lean_dec(v_i_3065_);
v_res_3080_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__2_spec__5(v_as_3063_, v_sz_boxed_3078_, v_i_boxed_3079_, v_b_3066_, v___y_3067_, v___y_3068_, v___y_3069_, v___y_3070_, v___y_3071_, v___y_3072_, v___y_3073_, v___y_3074_, v___y_3075_, v___y_3076_);
lean_dec(v___y_3076_);
lean_dec_ref(v___y_3075_);
lean_dec(v___y_3074_);
lean_dec_ref(v___y_3073_);
lean_dec(v___y_3072_);
lean_dec_ref(v___y_3071_);
lean_dec(v___y_3070_);
lean_dec_ref(v___y_3069_);
lean_dec(v___y_3068_);
lean_dec(v___y_3067_);
lean_dec_ref(v_as_3063_);
return v_res_3080_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__2(lean_object* v_as_3081_, size_t v_sz_3082_, size_t v_i_3083_, lean_object* v_b_3084_, lean_object* v___y_3085_, lean_object* v___y_3086_, lean_object* v___y_3087_, lean_object* v___y_3088_, lean_object* v___y_3089_, lean_object* v___y_3090_, lean_object* v___y_3091_, lean_object* v___y_3092_, lean_object* v___y_3093_, lean_object* v___y_3094_){
_start:
{
uint8_t v___x_3096_; 
v___x_3096_ = lean_usize_dec_lt(v_i_3083_, v_sz_3082_);
if (v___x_3096_ == 0)
{
lean_object* v___x_3097_; 
v___x_3097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3097_, 0, v_b_3084_);
return v___x_3097_;
}
else
{
lean_object* v_snd_3098_; lean_object* v___x_3100_; uint8_t v_isShared_3101_; uint8_t v_isSharedCheck_3195_; 
v_snd_3098_ = lean_ctor_get(v_b_3084_, 1);
v_isSharedCheck_3195_ = !lean_is_exclusive(v_b_3084_);
if (v_isSharedCheck_3195_ == 0)
{
lean_object* v_unused_3196_; 
v_unused_3196_ = lean_ctor_get(v_b_3084_, 0);
lean_dec(v_unused_3196_);
v___x_3100_ = v_b_3084_;
v_isShared_3101_ = v_isSharedCheck_3195_;
goto v_resetjp_3099_;
}
else
{
lean_inc(v_snd_3098_);
lean_dec(v_b_3084_);
v___x_3100_ = lean_box(0);
v_isShared_3101_ = v_isSharedCheck_3195_;
goto v_resetjp_3099_;
}
v_resetjp_3099_:
{
lean_object* v___x_3102_; lean_object* v___x_3103_; lean_object* v_a_3105_; lean_object* v_a_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; 
v___x_3102_ = lean_box(0);
v___x_3103_ = lean_box(0);
v_a_3112_ = lean_array_uget_borrowed(v_as_3081_, v_i_3083_);
v___x_3113_ = lean_st_ref_get(v___y_3085_);
lean_inc(v_a_3112_);
v___x_3114_ = l_Lean_Meta_Grind_Goal_getENode(v___x_3113_, v_a_3112_, v___y_3091_, v___y_3092_, v___y_3093_, v___y_3094_);
lean_dec(v___x_3113_);
if (lean_obj_tag(v___x_3114_) == 0)
{
lean_object* v_a_3115_; lean_object* v___y_3117_; lean_object* v___y_3118_; lean_object* v___y_3119_; lean_object* v___y_3120_; lean_object* v___y_3121_; lean_object* v___y_3122_; lean_object* v___y_3123_; lean_object* v___y_3124_; lean_object* v___y_3125_; lean_object* v___y_3126_; lean_object* v_self_3137_; uint8_t v_interpreted_3138_; lean_object* v___x_3139_; 
v_a_3115_ = lean_ctor_get(v___x_3114_, 0);
lean_inc(v_a_3115_);
lean_dec_ref_known(v___x_3114_, 1);
v_self_3137_ = lean_ctor_get(v_a_3115_, 0);
v_interpreted_3138_ = lean_ctor_get_uint8(v_a_3115_, sizeof(void*)*12 + 1);
lean_inc_ref(v_self_3137_);
v___x_3139_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents(v_self_3137_, v___y_3085_, v___y_3086_, v___y_3087_, v___y_3088_, v___y_3089_, v___y_3090_, v___y_3091_, v___y_3092_, v___y_3093_, v___y_3094_);
if (lean_obj_tag(v___x_3139_) == 0)
{
lean_dec_ref_known(v___x_3139_, 1);
if (v_interpreted_3138_ == 0)
{
lean_dec(v_snd_3098_);
v___y_3117_ = v___y_3085_;
v___y_3118_ = v___y_3086_;
v___y_3119_ = v___y_3087_;
v___y_3120_ = v___y_3088_;
v___y_3121_ = v___y_3089_;
v___y_3122_ = v___y_3090_;
v___y_3123_ = v___y_3091_;
v___y_3124_ = v___y_3092_;
v___y_3125_ = v___y_3093_;
v___y_3126_ = v___y_3094_;
goto v___jp_3116_;
}
else
{
lean_object* v___x_3140_; 
lean_inc_ref(v_self_3137_);
v___x_3140_ = l_Lean_Meta_Sym_Canon_normNumLit_x3f(v_self_3137_, v___y_3091_, v___y_3092_, v___y_3093_, v___y_3094_);
if (lean_obj_tag(v___x_3140_) == 0)
{
lean_object* v_a_3141_; 
v_a_3141_ = lean_ctor_get(v___x_3140_, 0);
lean_inc(v_a_3141_);
lean_dec_ref_known(v___x_3140_, 1);
if (lean_obj_tag(v_a_3141_) == 0)
{
lean_dec(v_snd_3098_);
v___y_3117_ = v___y_3085_;
v___y_3118_ = v___y_3086_;
v___y_3119_ = v___y_3087_;
v___y_3120_ = v___y_3088_;
v___y_3121_ = v___y_3089_;
v___y_3122_ = v___y_3090_;
v___y_3123_ = v___y_3091_;
v___y_3124_ = v___y_3092_;
v___y_3125_ = v___y_3093_;
v___y_3126_ = v___y_3094_;
goto v___jp_3116_;
}
else
{
lean_object* v___x_3143_; uint8_t v_isShared_3144_; uint8_t v_isSharedCheck_3169_; 
lean_dec(v_a_3115_);
v_isSharedCheck_3169_ = !lean_is_exclusive(v_a_3141_);
if (v_isSharedCheck_3169_ == 0)
{
lean_object* v_unused_3170_; 
v_unused_3170_ = lean_ctor_get(v_a_3141_, 0);
lean_dec(v_unused_3170_);
v___x_3143_ = v_a_3141_;
v_isShared_3144_ = v_isSharedCheck_3169_;
goto v_resetjp_3142_;
}
else
{
lean_dec(v_a_3141_);
v___x_3143_ = lean_box(0);
v_isShared_3144_ = v_isSharedCheck_3169_;
goto v_resetjp_3142_;
}
v_resetjp_3142_:
{
lean_object* v___x_3145_; lean_object* v___x_3146_; 
v___x_3145_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__2_spec__5___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__2_spec__5___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__2_spec__5___closed__2);
v___x_3146_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__0(v___x_3145_, v___y_3085_, v___y_3086_, v___y_3087_, v___y_3088_, v___y_3089_, v___y_3090_, v___y_3091_, v___y_3092_, v___y_3093_, v___y_3094_);
if (lean_obj_tag(v___x_3146_) == 0)
{
lean_object* v_a_3147_; lean_object* v___x_3149_; uint8_t v_isShared_3150_; uint8_t v_isSharedCheck_3160_; 
v_a_3147_ = lean_ctor_get(v___x_3146_, 0);
v_isSharedCheck_3160_ = !lean_is_exclusive(v___x_3146_);
if (v_isSharedCheck_3160_ == 0)
{
v___x_3149_ = v___x_3146_;
v_isShared_3150_ = v_isSharedCheck_3160_;
goto v_resetjp_3148_;
}
else
{
lean_inc(v_a_3147_);
lean_dec(v___x_3146_);
v___x_3149_ = lean_box(0);
v_isShared_3150_ = v_isSharedCheck_3160_;
goto v_resetjp_3148_;
}
v_resetjp_3148_:
{
if (lean_obj_tag(v_a_3147_) == 0)
{
lean_object* v_a_3151_; lean_object* v___x_3153_; 
lean_del_object(v___x_3100_);
v_a_3151_ = lean_ctor_get(v_a_3147_, 0);
lean_inc(v_a_3151_);
lean_dec_ref_known(v_a_3147_, 1);
if (v_isShared_3144_ == 0)
{
lean_ctor_set(v___x_3143_, 0, v_a_3151_);
v___x_3153_ = v___x_3143_;
goto v_reusejp_3152_;
}
else
{
lean_object* v_reuseFailAlloc_3158_; 
v_reuseFailAlloc_3158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3158_, 0, v_a_3151_);
v___x_3153_ = v_reuseFailAlloc_3158_;
goto v_reusejp_3152_;
}
v_reusejp_3152_:
{
lean_object* v___x_3154_; lean_object* v___x_3156_; 
v___x_3154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3154_, 0, v___x_3153_);
lean_ctor_set(v___x_3154_, 1, v_snd_3098_);
if (v_isShared_3150_ == 0)
{
lean_ctor_set(v___x_3149_, 0, v___x_3154_);
v___x_3156_ = v___x_3149_;
goto v_reusejp_3155_;
}
else
{
lean_object* v_reuseFailAlloc_3157_; 
v_reuseFailAlloc_3157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3157_, 0, v___x_3154_);
v___x_3156_ = v_reuseFailAlloc_3157_;
goto v_reusejp_3155_;
}
v_reusejp_3155_:
{
return v___x_3156_;
}
}
}
else
{
lean_object* v_a_3159_; 
lean_del_object(v___x_3149_);
lean_del_object(v___x_3143_);
lean_dec(v_snd_3098_);
v_a_3159_ = lean_ctor_get(v_a_3147_, 0);
lean_inc(v_a_3159_);
lean_dec_ref_known(v_a_3147_, 1);
v_a_3105_ = v_a_3159_;
goto v___jp_3104_;
}
}
}
else
{
lean_object* v_a_3161_; lean_object* v___x_3163_; uint8_t v_isShared_3164_; uint8_t v_isSharedCheck_3168_; 
lean_del_object(v___x_3143_);
lean_del_object(v___x_3100_);
lean_dec(v_snd_3098_);
v_a_3161_ = lean_ctor_get(v___x_3146_, 0);
v_isSharedCheck_3168_ = !lean_is_exclusive(v___x_3146_);
if (v_isSharedCheck_3168_ == 0)
{
v___x_3163_ = v___x_3146_;
v_isShared_3164_ = v_isSharedCheck_3168_;
goto v_resetjp_3162_;
}
else
{
lean_inc(v_a_3161_);
lean_dec(v___x_3146_);
v___x_3163_ = lean_box(0);
v_isShared_3164_ = v_isSharedCheck_3168_;
goto v_resetjp_3162_;
}
v_resetjp_3162_:
{
lean_object* v___x_3166_; 
if (v_isShared_3164_ == 0)
{
v___x_3166_ = v___x_3163_;
goto v_reusejp_3165_;
}
else
{
lean_object* v_reuseFailAlloc_3167_; 
v_reuseFailAlloc_3167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3167_, 0, v_a_3161_);
v___x_3166_ = v_reuseFailAlloc_3167_;
goto v_reusejp_3165_;
}
v_reusejp_3165_:
{
return v___x_3166_;
}
}
}
}
}
}
else
{
lean_object* v_a_3171_; lean_object* v___x_3173_; uint8_t v_isShared_3174_; uint8_t v_isSharedCheck_3178_; 
lean_dec(v_a_3115_);
lean_del_object(v___x_3100_);
lean_dec(v_snd_3098_);
v_a_3171_ = lean_ctor_get(v___x_3140_, 0);
v_isSharedCheck_3178_ = !lean_is_exclusive(v___x_3140_);
if (v_isSharedCheck_3178_ == 0)
{
v___x_3173_ = v___x_3140_;
v_isShared_3174_ = v_isSharedCheck_3178_;
goto v_resetjp_3172_;
}
else
{
lean_inc(v_a_3171_);
lean_dec(v___x_3140_);
v___x_3173_ = lean_box(0);
v_isShared_3174_ = v_isSharedCheck_3178_;
goto v_resetjp_3172_;
}
v_resetjp_3172_:
{
lean_object* v___x_3176_; 
if (v_isShared_3174_ == 0)
{
v___x_3176_ = v___x_3173_;
goto v_reusejp_3175_;
}
else
{
lean_object* v_reuseFailAlloc_3177_; 
v_reuseFailAlloc_3177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3177_, 0, v_a_3171_);
v___x_3176_ = v_reuseFailAlloc_3177_;
goto v_reusejp_3175_;
}
v_reusejp_3175_:
{
return v___x_3176_;
}
}
}
}
}
else
{
lean_object* v_a_3179_; lean_object* v___x_3181_; uint8_t v_isShared_3182_; uint8_t v_isSharedCheck_3186_; 
lean_dec(v_a_3115_);
lean_del_object(v___x_3100_);
lean_dec(v_snd_3098_);
v_a_3179_ = lean_ctor_get(v___x_3139_, 0);
v_isSharedCheck_3186_ = !lean_is_exclusive(v___x_3139_);
if (v_isSharedCheck_3186_ == 0)
{
v___x_3181_ = v___x_3139_;
v_isShared_3182_ = v_isSharedCheck_3186_;
goto v_resetjp_3180_;
}
else
{
lean_inc(v_a_3179_);
lean_dec(v___x_3139_);
v___x_3181_ = lean_box(0);
v_isShared_3182_ = v_isSharedCheck_3186_;
goto v_resetjp_3180_;
}
v_resetjp_3180_:
{
lean_object* v___x_3184_; 
if (v_isShared_3182_ == 0)
{
v___x_3184_ = v___x_3181_;
goto v_reusejp_3183_;
}
else
{
lean_object* v_reuseFailAlloc_3185_; 
v_reuseFailAlloc_3185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3185_, 0, v_a_3179_);
v___x_3184_ = v_reuseFailAlloc_3185_;
goto v_reusejp_3183_;
}
v_reusejp_3183_:
{
return v___x_3184_;
}
}
}
v___jp_3116_:
{
uint8_t v___x_3127_; 
v___x_3127_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_3115_);
if (v___x_3127_ == 0)
{
lean_dec(v_a_3115_);
v_a_3105_ = v___x_3102_;
goto v___jp_3104_;
}
else
{
lean_object* v___x_3128_; 
v___x_3128_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc(v_a_3115_, v___y_3117_, v___y_3118_, v___y_3119_, v___y_3120_, v___y_3121_, v___y_3122_, v___y_3123_, v___y_3124_, v___y_3125_, v___y_3126_);
if (lean_obj_tag(v___x_3128_) == 0)
{
lean_dec_ref_known(v___x_3128_, 1);
v_a_3105_ = v___x_3102_;
goto v___jp_3104_;
}
else
{
lean_object* v_a_3129_; lean_object* v___x_3131_; uint8_t v_isShared_3132_; uint8_t v_isSharedCheck_3136_; 
lean_del_object(v___x_3100_);
v_a_3129_ = lean_ctor_get(v___x_3128_, 0);
v_isSharedCheck_3136_ = !lean_is_exclusive(v___x_3128_);
if (v_isSharedCheck_3136_ == 0)
{
v___x_3131_ = v___x_3128_;
v_isShared_3132_ = v_isSharedCheck_3136_;
goto v_resetjp_3130_;
}
else
{
lean_inc(v_a_3129_);
lean_dec(v___x_3128_);
v___x_3131_ = lean_box(0);
v_isShared_3132_ = v_isSharedCheck_3136_;
goto v_resetjp_3130_;
}
v_resetjp_3130_:
{
lean_object* v___x_3134_; 
if (v_isShared_3132_ == 0)
{
v___x_3134_ = v___x_3131_;
goto v_reusejp_3133_;
}
else
{
lean_object* v_reuseFailAlloc_3135_; 
v_reuseFailAlloc_3135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3135_, 0, v_a_3129_);
v___x_3134_ = v_reuseFailAlloc_3135_;
goto v_reusejp_3133_;
}
v_reusejp_3133_:
{
return v___x_3134_;
}
}
}
}
}
}
else
{
lean_object* v_a_3187_; lean_object* v___x_3189_; uint8_t v_isShared_3190_; uint8_t v_isSharedCheck_3194_; 
lean_del_object(v___x_3100_);
lean_dec(v_snd_3098_);
v_a_3187_ = lean_ctor_get(v___x_3114_, 0);
v_isSharedCheck_3194_ = !lean_is_exclusive(v___x_3114_);
if (v_isSharedCheck_3194_ == 0)
{
v___x_3189_ = v___x_3114_;
v_isShared_3190_ = v_isSharedCheck_3194_;
goto v_resetjp_3188_;
}
else
{
lean_inc(v_a_3187_);
lean_dec(v___x_3114_);
v___x_3189_ = lean_box(0);
v_isShared_3190_ = v_isSharedCheck_3194_;
goto v_resetjp_3188_;
}
v_resetjp_3188_:
{
lean_object* v___x_3192_; 
if (v_isShared_3190_ == 0)
{
v___x_3192_ = v___x_3189_;
goto v_reusejp_3191_;
}
else
{
lean_object* v_reuseFailAlloc_3193_; 
v_reuseFailAlloc_3193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3193_, 0, v_a_3187_);
v___x_3192_ = v_reuseFailAlloc_3193_;
goto v_reusejp_3191_;
}
v_reusejp_3191_:
{
return v___x_3192_;
}
}
}
v___jp_3104_:
{
lean_object* v___x_3107_; 
if (v_isShared_3101_ == 0)
{
lean_ctor_set(v___x_3100_, 1, v_a_3105_);
lean_ctor_set(v___x_3100_, 0, v___x_3103_);
v___x_3107_ = v___x_3100_;
goto v_reusejp_3106_;
}
else
{
lean_object* v_reuseFailAlloc_3111_; 
v_reuseFailAlloc_3111_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3111_, 0, v___x_3103_);
lean_ctor_set(v_reuseFailAlloc_3111_, 1, v_a_3105_);
v___x_3107_ = v_reuseFailAlloc_3111_;
goto v_reusejp_3106_;
}
v_reusejp_3106_:
{
size_t v___x_3108_; size_t v___x_3109_; lean_object* v___x_3110_; 
v___x_3108_ = ((size_t)1ULL);
v___x_3109_ = lean_usize_add(v_i_3083_, v___x_3108_);
v___x_3110_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__2_spec__5(v_as_3081_, v_sz_3082_, v___x_3109_, v___x_3107_, v___y_3085_, v___y_3086_, v___y_3087_, v___y_3088_, v___y_3089_, v___y_3090_, v___y_3091_, v___y_3092_, v___y_3093_, v___y_3094_);
return v___x_3110_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__2___boxed(lean_object* v_as_3197_, lean_object* v_sz_3198_, lean_object* v_i_3199_, lean_object* v_b_3200_, lean_object* v___y_3201_, lean_object* v___y_3202_, lean_object* v___y_3203_, lean_object* v___y_3204_, lean_object* v___y_3205_, lean_object* v___y_3206_, lean_object* v___y_3207_, lean_object* v___y_3208_, lean_object* v___y_3209_, lean_object* v___y_3210_, lean_object* v___y_3211_){
_start:
{
size_t v_sz_boxed_3212_; size_t v_i_boxed_3213_; lean_object* v_res_3214_; 
v_sz_boxed_3212_ = lean_unbox_usize(v_sz_3198_);
lean_dec(v_sz_3198_);
v_i_boxed_3213_ = lean_unbox_usize(v_i_3199_);
lean_dec(v_i_3199_);
v_res_3214_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__2(v_as_3197_, v_sz_boxed_3212_, v_i_boxed_3213_, v_b_3200_, v___y_3201_, v___y_3202_, v___y_3203_, v___y_3204_, v___y_3205_, v___y_3206_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_);
lean_dec(v___y_3210_);
lean_dec_ref(v___y_3209_);
lean_dec(v___y_3208_);
lean_dec_ref(v___y_3207_);
lean_dec(v___y_3206_);
lean_dec_ref(v___y_3205_);
lean_dec(v___y_3204_);
lean_dec_ref(v___y_3203_);
lean_dec(v___y_3202_);
lean_dec(v___y_3201_);
lean_dec_ref(v_as_3197_);
return v_res_3214_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__1_spec__3_spec__4(lean_object* v_as_3215_, size_t v_sz_3216_, size_t v_i_3217_, lean_object* v_b_3218_, lean_object* v___y_3219_, lean_object* v___y_3220_, lean_object* v___y_3221_, lean_object* v___y_3222_, lean_object* v___y_3223_, lean_object* v___y_3224_, lean_object* v___y_3225_, lean_object* v___y_3226_, lean_object* v___y_3227_, lean_object* v___y_3228_){
_start:
{
uint8_t v___x_3230_; 
v___x_3230_ = lean_usize_dec_lt(v_i_3217_, v_sz_3216_);
if (v___x_3230_ == 0)
{
lean_object* v___x_3231_; 
v___x_3231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3231_, 0, v_b_3218_);
return v___x_3231_;
}
else
{
lean_object* v_snd_3232_; lean_object* v___x_3234_; uint8_t v_isShared_3235_; uint8_t v_isSharedCheck_3328_; 
v_snd_3232_ = lean_ctor_get(v_b_3218_, 1);
v_isSharedCheck_3328_ = !lean_is_exclusive(v_b_3218_);
if (v_isSharedCheck_3328_ == 0)
{
lean_object* v_unused_3329_; 
v_unused_3329_ = lean_ctor_get(v_b_3218_, 0);
lean_dec(v_unused_3329_);
v___x_3234_ = v_b_3218_;
v_isShared_3235_ = v_isSharedCheck_3328_;
goto v_resetjp_3233_;
}
else
{
lean_inc(v_snd_3232_);
lean_dec(v_b_3218_);
v___x_3234_ = lean_box(0);
v_isShared_3235_ = v_isSharedCheck_3328_;
goto v_resetjp_3233_;
}
v_resetjp_3233_:
{
lean_object* v___x_3236_; lean_object* v_a_3238_; lean_object* v___x_3245_; lean_object* v_a_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; 
v___x_3236_ = lean_box(0);
v___x_3245_ = lean_box(0);
v_a_3246_ = lean_array_uget_borrowed(v_as_3215_, v_i_3217_);
v___x_3247_ = lean_st_ref_get(v___y_3219_);
lean_inc(v_a_3246_);
v___x_3248_ = l_Lean_Meta_Grind_Goal_getENode(v___x_3247_, v_a_3246_, v___y_3225_, v___y_3226_, v___y_3227_, v___y_3228_);
lean_dec(v___x_3247_);
if (lean_obj_tag(v___x_3248_) == 0)
{
lean_object* v_a_3249_; lean_object* v___y_3251_; lean_object* v___y_3252_; lean_object* v___y_3253_; lean_object* v___y_3254_; lean_object* v___y_3255_; lean_object* v___y_3256_; lean_object* v___y_3257_; lean_object* v___y_3258_; lean_object* v___y_3259_; lean_object* v___y_3260_; lean_object* v_self_3271_; uint8_t v_interpreted_3272_; lean_object* v___x_3273_; 
v_a_3249_ = lean_ctor_get(v___x_3248_, 0);
lean_inc(v_a_3249_);
lean_dec_ref_known(v___x_3248_, 1);
v_self_3271_ = lean_ctor_get(v_a_3249_, 0);
v_interpreted_3272_ = lean_ctor_get_uint8(v_a_3249_, sizeof(void*)*12 + 1);
lean_inc_ref(v_self_3271_);
v___x_3273_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents(v_self_3271_, v___y_3219_, v___y_3220_, v___y_3221_, v___y_3222_, v___y_3223_, v___y_3224_, v___y_3225_, v___y_3226_, v___y_3227_, v___y_3228_);
if (lean_obj_tag(v___x_3273_) == 0)
{
lean_dec_ref_known(v___x_3273_, 1);
if (v_interpreted_3272_ == 0)
{
lean_dec(v_snd_3232_);
v___y_3251_ = v___y_3219_;
v___y_3252_ = v___y_3220_;
v___y_3253_ = v___y_3221_;
v___y_3254_ = v___y_3222_;
v___y_3255_ = v___y_3223_;
v___y_3256_ = v___y_3224_;
v___y_3257_ = v___y_3225_;
v___y_3258_ = v___y_3226_;
v___y_3259_ = v___y_3227_;
v___y_3260_ = v___y_3228_;
goto v___jp_3250_;
}
else
{
lean_object* v___x_3274_; 
lean_inc_ref(v_self_3271_);
v___x_3274_ = l_Lean_Meta_Sym_Canon_normNumLit_x3f(v_self_3271_, v___y_3225_, v___y_3226_, v___y_3227_, v___y_3228_);
if (lean_obj_tag(v___x_3274_) == 0)
{
lean_object* v_a_3275_; 
v_a_3275_ = lean_ctor_get(v___x_3274_, 0);
lean_inc(v_a_3275_);
lean_dec_ref_known(v___x_3274_, 1);
if (lean_obj_tag(v_a_3275_) == 0)
{
lean_dec(v_snd_3232_);
v___y_3251_ = v___y_3219_;
v___y_3252_ = v___y_3220_;
v___y_3253_ = v___y_3221_;
v___y_3254_ = v___y_3222_;
v___y_3255_ = v___y_3223_;
v___y_3256_ = v___y_3224_;
v___y_3257_ = v___y_3225_;
v___y_3258_ = v___y_3226_;
v___y_3259_ = v___y_3227_;
v___y_3260_ = v___y_3228_;
goto v___jp_3250_;
}
else
{
lean_object* v___x_3277_; uint8_t v_isShared_3278_; uint8_t v_isSharedCheck_3302_; 
lean_dec(v_a_3249_);
v_isSharedCheck_3302_ = !lean_is_exclusive(v_a_3275_);
if (v_isSharedCheck_3302_ == 0)
{
lean_object* v_unused_3303_; 
v_unused_3303_ = lean_ctor_get(v_a_3275_, 0);
lean_dec(v_unused_3303_);
v___x_3277_ = v_a_3275_;
v_isShared_3278_ = v_isSharedCheck_3302_;
goto v_resetjp_3276_;
}
else
{
lean_dec(v_a_3275_);
v___x_3277_ = lean_box(0);
v_isShared_3278_ = v_isSharedCheck_3302_;
goto v_resetjp_3276_;
}
v_resetjp_3276_:
{
lean_object* v___x_3279_; lean_object* v___x_3280_; 
v___x_3279_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__2_spec__5___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__2_spec__5___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__2_spec__5___closed__2);
v___x_3280_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__0(v___x_3279_, v___y_3219_, v___y_3220_, v___y_3221_, v___y_3222_, v___y_3223_, v___y_3224_, v___y_3225_, v___y_3226_, v___y_3227_, v___y_3228_);
if (lean_obj_tag(v___x_3280_) == 0)
{
lean_object* v_a_3281_; lean_object* v___x_3283_; uint8_t v_isShared_3284_; uint8_t v_isSharedCheck_3293_; 
v_a_3281_ = lean_ctor_get(v___x_3280_, 0);
v_isSharedCheck_3293_ = !lean_is_exclusive(v___x_3280_);
if (v_isSharedCheck_3293_ == 0)
{
v___x_3283_ = v___x_3280_;
v_isShared_3284_ = v_isSharedCheck_3293_;
goto v_resetjp_3282_;
}
else
{
lean_inc(v_a_3281_);
lean_dec(v___x_3280_);
v___x_3283_ = lean_box(0);
v_isShared_3284_ = v_isSharedCheck_3293_;
goto v_resetjp_3282_;
}
v_resetjp_3282_:
{
if (lean_obj_tag(v_a_3281_) == 0)
{
lean_object* v___x_3286_; 
lean_del_object(v___x_3234_);
if (v_isShared_3278_ == 0)
{
lean_ctor_set(v___x_3277_, 0, v_a_3281_);
v___x_3286_ = v___x_3277_;
goto v_reusejp_3285_;
}
else
{
lean_object* v_reuseFailAlloc_3291_; 
v_reuseFailAlloc_3291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3291_, 0, v_a_3281_);
v___x_3286_ = v_reuseFailAlloc_3291_;
goto v_reusejp_3285_;
}
v_reusejp_3285_:
{
lean_object* v___x_3287_; lean_object* v___x_3289_; 
v___x_3287_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3287_, 0, v___x_3286_);
lean_ctor_set(v___x_3287_, 1, v_snd_3232_);
if (v_isShared_3284_ == 0)
{
lean_ctor_set(v___x_3283_, 0, v___x_3287_);
v___x_3289_ = v___x_3283_;
goto v_reusejp_3288_;
}
else
{
lean_object* v_reuseFailAlloc_3290_; 
v_reuseFailAlloc_3290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3290_, 0, v___x_3287_);
v___x_3289_ = v_reuseFailAlloc_3290_;
goto v_reusejp_3288_;
}
v_reusejp_3288_:
{
return v___x_3289_;
}
}
}
else
{
lean_object* v_a_3292_; 
lean_del_object(v___x_3283_);
lean_del_object(v___x_3277_);
lean_dec(v_snd_3232_);
v_a_3292_ = lean_ctor_get(v_a_3281_, 0);
lean_inc(v_a_3292_);
lean_dec_ref_known(v_a_3281_, 1);
v_a_3238_ = v_a_3292_;
goto v___jp_3237_;
}
}
}
else
{
lean_object* v_a_3294_; lean_object* v___x_3296_; uint8_t v_isShared_3297_; uint8_t v_isSharedCheck_3301_; 
lean_del_object(v___x_3277_);
lean_del_object(v___x_3234_);
lean_dec(v_snd_3232_);
v_a_3294_ = lean_ctor_get(v___x_3280_, 0);
v_isSharedCheck_3301_ = !lean_is_exclusive(v___x_3280_);
if (v_isSharedCheck_3301_ == 0)
{
v___x_3296_ = v___x_3280_;
v_isShared_3297_ = v_isSharedCheck_3301_;
goto v_resetjp_3295_;
}
else
{
lean_inc(v_a_3294_);
lean_dec(v___x_3280_);
v___x_3296_ = lean_box(0);
v_isShared_3297_ = v_isSharedCheck_3301_;
goto v_resetjp_3295_;
}
v_resetjp_3295_:
{
lean_object* v___x_3299_; 
if (v_isShared_3297_ == 0)
{
v___x_3299_ = v___x_3296_;
goto v_reusejp_3298_;
}
else
{
lean_object* v_reuseFailAlloc_3300_; 
v_reuseFailAlloc_3300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3300_, 0, v_a_3294_);
v___x_3299_ = v_reuseFailAlloc_3300_;
goto v_reusejp_3298_;
}
v_reusejp_3298_:
{
return v___x_3299_;
}
}
}
}
}
}
else
{
lean_object* v_a_3304_; lean_object* v___x_3306_; uint8_t v_isShared_3307_; uint8_t v_isSharedCheck_3311_; 
lean_dec(v_a_3249_);
lean_del_object(v___x_3234_);
lean_dec(v_snd_3232_);
v_a_3304_ = lean_ctor_get(v___x_3274_, 0);
v_isSharedCheck_3311_ = !lean_is_exclusive(v___x_3274_);
if (v_isSharedCheck_3311_ == 0)
{
v___x_3306_ = v___x_3274_;
v_isShared_3307_ = v_isSharedCheck_3311_;
goto v_resetjp_3305_;
}
else
{
lean_inc(v_a_3304_);
lean_dec(v___x_3274_);
v___x_3306_ = lean_box(0);
v_isShared_3307_ = v_isSharedCheck_3311_;
goto v_resetjp_3305_;
}
v_resetjp_3305_:
{
lean_object* v___x_3309_; 
if (v_isShared_3307_ == 0)
{
v___x_3309_ = v___x_3306_;
goto v_reusejp_3308_;
}
else
{
lean_object* v_reuseFailAlloc_3310_; 
v_reuseFailAlloc_3310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3310_, 0, v_a_3304_);
v___x_3309_ = v_reuseFailAlloc_3310_;
goto v_reusejp_3308_;
}
v_reusejp_3308_:
{
return v___x_3309_;
}
}
}
}
}
else
{
lean_object* v_a_3312_; lean_object* v___x_3314_; uint8_t v_isShared_3315_; uint8_t v_isSharedCheck_3319_; 
lean_dec(v_a_3249_);
lean_del_object(v___x_3234_);
lean_dec(v_snd_3232_);
v_a_3312_ = lean_ctor_get(v___x_3273_, 0);
v_isSharedCheck_3319_ = !lean_is_exclusive(v___x_3273_);
if (v_isSharedCheck_3319_ == 0)
{
v___x_3314_ = v___x_3273_;
v_isShared_3315_ = v_isSharedCheck_3319_;
goto v_resetjp_3313_;
}
else
{
lean_inc(v_a_3312_);
lean_dec(v___x_3273_);
v___x_3314_ = lean_box(0);
v_isShared_3315_ = v_isSharedCheck_3319_;
goto v_resetjp_3313_;
}
v_resetjp_3313_:
{
lean_object* v___x_3317_; 
if (v_isShared_3315_ == 0)
{
v___x_3317_ = v___x_3314_;
goto v_reusejp_3316_;
}
else
{
lean_object* v_reuseFailAlloc_3318_; 
v_reuseFailAlloc_3318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3318_, 0, v_a_3312_);
v___x_3317_ = v_reuseFailAlloc_3318_;
goto v_reusejp_3316_;
}
v_reusejp_3316_:
{
return v___x_3317_;
}
}
}
v___jp_3250_:
{
uint8_t v___x_3261_; 
v___x_3261_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_3249_);
if (v___x_3261_ == 0)
{
lean_dec(v_a_3249_);
v_a_3238_ = v___x_3245_;
goto v___jp_3237_;
}
else
{
lean_object* v___x_3262_; 
v___x_3262_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc(v_a_3249_, v___y_3251_, v___y_3252_, v___y_3253_, v___y_3254_, v___y_3255_, v___y_3256_, v___y_3257_, v___y_3258_, v___y_3259_, v___y_3260_);
if (lean_obj_tag(v___x_3262_) == 0)
{
lean_dec_ref_known(v___x_3262_, 1);
v_a_3238_ = v___x_3245_;
goto v___jp_3237_;
}
else
{
lean_object* v_a_3263_; lean_object* v___x_3265_; uint8_t v_isShared_3266_; uint8_t v_isSharedCheck_3270_; 
lean_del_object(v___x_3234_);
v_a_3263_ = lean_ctor_get(v___x_3262_, 0);
v_isSharedCheck_3270_ = !lean_is_exclusive(v___x_3262_);
if (v_isSharedCheck_3270_ == 0)
{
v___x_3265_ = v___x_3262_;
v_isShared_3266_ = v_isSharedCheck_3270_;
goto v_resetjp_3264_;
}
else
{
lean_inc(v_a_3263_);
lean_dec(v___x_3262_);
v___x_3265_ = lean_box(0);
v_isShared_3266_ = v_isSharedCheck_3270_;
goto v_resetjp_3264_;
}
v_resetjp_3264_:
{
lean_object* v___x_3268_; 
if (v_isShared_3266_ == 0)
{
v___x_3268_ = v___x_3265_;
goto v_reusejp_3267_;
}
else
{
lean_object* v_reuseFailAlloc_3269_; 
v_reuseFailAlloc_3269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3269_, 0, v_a_3263_);
v___x_3268_ = v_reuseFailAlloc_3269_;
goto v_reusejp_3267_;
}
v_reusejp_3267_:
{
return v___x_3268_;
}
}
}
}
}
}
else
{
lean_object* v_a_3320_; lean_object* v___x_3322_; uint8_t v_isShared_3323_; uint8_t v_isSharedCheck_3327_; 
lean_del_object(v___x_3234_);
lean_dec(v_snd_3232_);
v_a_3320_ = lean_ctor_get(v___x_3248_, 0);
v_isSharedCheck_3327_ = !lean_is_exclusive(v___x_3248_);
if (v_isSharedCheck_3327_ == 0)
{
v___x_3322_ = v___x_3248_;
v_isShared_3323_ = v_isSharedCheck_3327_;
goto v_resetjp_3321_;
}
else
{
lean_inc(v_a_3320_);
lean_dec(v___x_3248_);
v___x_3322_ = lean_box(0);
v_isShared_3323_ = v_isSharedCheck_3327_;
goto v_resetjp_3321_;
}
v_resetjp_3321_:
{
lean_object* v___x_3325_; 
if (v_isShared_3323_ == 0)
{
v___x_3325_ = v___x_3322_;
goto v_reusejp_3324_;
}
else
{
lean_object* v_reuseFailAlloc_3326_; 
v_reuseFailAlloc_3326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3326_, 0, v_a_3320_);
v___x_3325_ = v_reuseFailAlloc_3326_;
goto v_reusejp_3324_;
}
v_reusejp_3324_:
{
return v___x_3325_;
}
}
}
v___jp_3237_:
{
lean_object* v___x_3240_; 
if (v_isShared_3235_ == 0)
{
lean_ctor_set(v___x_3234_, 1, v_a_3238_);
lean_ctor_set(v___x_3234_, 0, v___x_3236_);
v___x_3240_ = v___x_3234_;
goto v_reusejp_3239_;
}
else
{
lean_object* v_reuseFailAlloc_3244_; 
v_reuseFailAlloc_3244_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3244_, 0, v___x_3236_);
lean_ctor_set(v_reuseFailAlloc_3244_, 1, v_a_3238_);
v___x_3240_ = v_reuseFailAlloc_3244_;
goto v_reusejp_3239_;
}
v_reusejp_3239_:
{
size_t v___x_3241_; size_t v___x_3242_; 
v___x_3241_ = ((size_t)1ULL);
v___x_3242_ = lean_usize_add(v_i_3217_, v___x_3241_);
v_i_3217_ = v___x_3242_;
v_b_3218_ = v___x_3240_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__1_spec__3_spec__4___boxed(lean_object* v_as_3330_, lean_object* v_sz_3331_, lean_object* v_i_3332_, lean_object* v_b_3333_, lean_object* v___y_3334_, lean_object* v___y_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_, lean_object* v___y_3338_, lean_object* v___y_3339_, lean_object* v___y_3340_, lean_object* v___y_3341_, lean_object* v___y_3342_, lean_object* v___y_3343_, lean_object* v___y_3344_){
_start:
{
size_t v_sz_boxed_3345_; size_t v_i_boxed_3346_; lean_object* v_res_3347_; 
v_sz_boxed_3345_ = lean_unbox_usize(v_sz_3331_);
lean_dec(v_sz_3331_);
v_i_boxed_3346_ = lean_unbox_usize(v_i_3332_);
lean_dec(v_i_3332_);
v_res_3347_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__1_spec__3_spec__4(v_as_3330_, v_sz_boxed_3345_, v_i_boxed_3346_, v_b_3333_, v___y_3334_, v___y_3335_, v___y_3336_, v___y_3337_, v___y_3338_, v___y_3339_, v___y_3340_, v___y_3341_, v___y_3342_, v___y_3343_);
lean_dec(v___y_3343_);
lean_dec_ref(v___y_3342_);
lean_dec(v___y_3341_);
lean_dec_ref(v___y_3340_);
lean_dec(v___y_3339_);
lean_dec_ref(v___y_3338_);
lean_dec(v___y_3337_);
lean_dec_ref(v___y_3336_);
lean_dec(v___y_3335_);
lean_dec(v___y_3334_);
lean_dec_ref(v_as_3330_);
return v_res_3347_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__1_spec__3(lean_object* v_as_3348_, size_t v_sz_3349_, size_t v_i_3350_, lean_object* v_b_3351_, lean_object* v___y_3352_, lean_object* v___y_3353_, lean_object* v___y_3354_, lean_object* v___y_3355_, lean_object* v___y_3356_, lean_object* v___y_3357_, lean_object* v___y_3358_, lean_object* v___y_3359_, lean_object* v___y_3360_, lean_object* v___y_3361_){
_start:
{
uint8_t v___x_3363_; 
v___x_3363_ = lean_usize_dec_lt(v_i_3350_, v_sz_3349_);
if (v___x_3363_ == 0)
{
lean_object* v___x_3364_; 
v___x_3364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3364_, 0, v_b_3351_);
return v___x_3364_;
}
else
{
lean_object* v_snd_3365_; lean_object* v___x_3367_; uint8_t v_isShared_3368_; uint8_t v_isSharedCheck_3461_; 
v_snd_3365_ = lean_ctor_get(v_b_3351_, 1);
v_isSharedCheck_3461_ = !lean_is_exclusive(v_b_3351_);
if (v_isSharedCheck_3461_ == 0)
{
lean_object* v_unused_3462_; 
v_unused_3462_ = lean_ctor_get(v_b_3351_, 0);
lean_dec(v_unused_3462_);
v___x_3367_ = v_b_3351_;
v_isShared_3368_ = v_isSharedCheck_3461_;
goto v_resetjp_3366_;
}
else
{
lean_inc(v_snd_3365_);
lean_dec(v_b_3351_);
v___x_3367_ = lean_box(0);
v_isShared_3368_ = v_isSharedCheck_3461_;
goto v_resetjp_3366_;
}
v_resetjp_3366_:
{
lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v_a_3372_; lean_object* v_a_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; 
v___x_3369_ = lean_box(0);
v___x_3370_ = lean_box(0);
v_a_3379_ = lean_array_uget_borrowed(v_as_3348_, v_i_3350_);
v___x_3380_ = lean_st_ref_get(v___y_3352_);
lean_inc(v_a_3379_);
v___x_3381_ = l_Lean_Meta_Grind_Goal_getENode(v___x_3380_, v_a_3379_, v___y_3358_, v___y_3359_, v___y_3360_, v___y_3361_);
lean_dec(v___x_3380_);
if (lean_obj_tag(v___x_3381_) == 0)
{
lean_object* v_a_3382_; lean_object* v___y_3384_; lean_object* v___y_3385_; lean_object* v___y_3386_; lean_object* v___y_3387_; lean_object* v___y_3388_; lean_object* v___y_3389_; lean_object* v___y_3390_; lean_object* v___y_3391_; lean_object* v___y_3392_; lean_object* v___y_3393_; lean_object* v_self_3404_; uint8_t v_interpreted_3405_; lean_object* v___x_3406_; 
v_a_3382_ = lean_ctor_get(v___x_3381_, 0);
lean_inc(v_a_3382_);
lean_dec_ref_known(v___x_3381_, 1);
v_self_3404_ = lean_ctor_get(v_a_3382_, 0);
v_interpreted_3405_ = lean_ctor_get_uint8(v_a_3382_, sizeof(void*)*12 + 1);
lean_inc_ref(v_self_3404_);
v___x_3406_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents(v_self_3404_, v___y_3352_, v___y_3353_, v___y_3354_, v___y_3355_, v___y_3356_, v___y_3357_, v___y_3358_, v___y_3359_, v___y_3360_, v___y_3361_);
if (lean_obj_tag(v___x_3406_) == 0)
{
lean_dec_ref_known(v___x_3406_, 1);
if (v_interpreted_3405_ == 0)
{
lean_dec(v_snd_3365_);
v___y_3384_ = v___y_3352_;
v___y_3385_ = v___y_3353_;
v___y_3386_ = v___y_3354_;
v___y_3387_ = v___y_3355_;
v___y_3388_ = v___y_3356_;
v___y_3389_ = v___y_3357_;
v___y_3390_ = v___y_3358_;
v___y_3391_ = v___y_3359_;
v___y_3392_ = v___y_3360_;
v___y_3393_ = v___y_3361_;
goto v___jp_3383_;
}
else
{
lean_object* v___x_3407_; 
lean_inc_ref(v_self_3404_);
v___x_3407_ = l_Lean_Meta_Sym_Canon_normNumLit_x3f(v_self_3404_, v___y_3358_, v___y_3359_, v___y_3360_, v___y_3361_);
if (lean_obj_tag(v___x_3407_) == 0)
{
lean_object* v_a_3408_; 
v_a_3408_ = lean_ctor_get(v___x_3407_, 0);
lean_inc(v_a_3408_);
lean_dec_ref_known(v___x_3407_, 1);
if (lean_obj_tag(v_a_3408_) == 0)
{
lean_dec(v_snd_3365_);
v___y_3384_ = v___y_3352_;
v___y_3385_ = v___y_3353_;
v___y_3386_ = v___y_3354_;
v___y_3387_ = v___y_3355_;
v___y_3388_ = v___y_3356_;
v___y_3389_ = v___y_3357_;
v___y_3390_ = v___y_3358_;
v___y_3391_ = v___y_3359_;
v___y_3392_ = v___y_3360_;
v___y_3393_ = v___y_3361_;
goto v___jp_3383_;
}
else
{
lean_object* v___x_3410_; uint8_t v_isShared_3411_; uint8_t v_isSharedCheck_3435_; 
lean_dec(v_a_3382_);
v_isSharedCheck_3435_ = !lean_is_exclusive(v_a_3408_);
if (v_isSharedCheck_3435_ == 0)
{
lean_object* v_unused_3436_; 
v_unused_3436_ = lean_ctor_get(v_a_3408_, 0);
lean_dec(v_unused_3436_);
v___x_3410_ = v_a_3408_;
v_isShared_3411_ = v_isSharedCheck_3435_;
goto v_resetjp_3409_;
}
else
{
lean_dec(v_a_3408_);
v___x_3410_ = lean_box(0);
v_isShared_3411_ = v_isSharedCheck_3435_;
goto v_resetjp_3409_;
}
v_resetjp_3409_:
{
lean_object* v___x_3412_; lean_object* v___x_3413_; 
v___x_3412_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__2_spec__5___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__2_spec__5___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__2_spec__5___closed__2);
v___x_3413_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__0(v___x_3412_, v___y_3352_, v___y_3353_, v___y_3354_, v___y_3355_, v___y_3356_, v___y_3357_, v___y_3358_, v___y_3359_, v___y_3360_, v___y_3361_);
if (lean_obj_tag(v___x_3413_) == 0)
{
lean_object* v_a_3414_; lean_object* v___x_3416_; uint8_t v_isShared_3417_; uint8_t v_isSharedCheck_3426_; 
v_a_3414_ = lean_ctor_get(v___x_3413_, 0);
v_isSharedCheck_3426_ = !lean_is_exclusive(v___x_3413_);
if (v_isSharedCheck_3426_ == 0)
{
v___x_3416_ = v___x_3413_;
v_isShared_3417_ = v_isSharedCheck_3426_;
goto v_resetjp_3415_;
}
else
{
lean_inc(v_a_3414_);
lean_dec(v___x_3413_);
v___x_3416_ = lean_box(0);
v_isShared_3417_ = v_isSharedCheck_3426_;
goto v_resetjp_3415_;
}
v_resetjp_3415_:
{
if (lean_obj_tag(v_a_3414_) == 0)
{
lean_object* v___x_3419_; 
lean_del_object(v___x_3367_);
if (v_isShared_3411_ == 0)
{
lean_ctor_set(v___x_3410_, 0, v_a_3414_);
v___x_3419_ = v___x_3410_;
goto v_reusejp_3418_;
}
else
{
lean_object* v_reuseFailAlloc_3424_; 
v_reuseFailAlloc_3424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3424_, 0, v_a_3414_);
v___x_3419_ = v_reuseFailAlloc_3424_;
goto v_reusejp_3418_;
}
v_reusejp_3418_:
{
lean_object* v___x_3420_; lean_object* v___x_3422_; 
v___x_3420_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3420_, 0, v___x_3419_);
lean_ctor_set(v___x_3420_, 1, v_snd_3365_);
if (v_isShared_3417_ == 0)
{
lean_ctor_set(v___x_3416_, 0, v___x_3420_);
v___x_3422_ = v___x_3416_;
goto v_reusejp_3421_;
}
else
{
lean_object* v_reuseFailAlloc_3423_; 
v_reuseFailAlloc_3423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3423_, 0, v___x_3420_);
v___x_3422_ = v_reuseFailAlloc_3423_;
goto v_reusejp_3421_;
}
v_reusejp_3421_:
{
return v___x_3422_;
}
}
}
else
{
lean_object* v_a_3425_; 
lean_del_object(v___x_3416_);
lean_del_object(v___x_3410_);
lean_dec(v_snd_3365_);
v_a_3425_ = lean_ctor_get(v_a_3414_, 0);
lean_inc(v_a_3425_);
lean_dec_ref_known(v_a_3414_, 1);
v_a_3372_ = v_a_3425_;
goto v___jp_3371_;
}
}
}
else
{
lean_object* v_a_3427_; lean_object* v___x_3429_; uint8_t v_isShared_3430_; uint8_t v_isSharedCheck_3434_; 
lean_del_object(v___x_3410_);
lean_del_object(v___x_3367_);
lean_dec(v_snd_3365_);
v_a_3427_ = lean_ctor_get(v___x_3413_, 0);
v_isSharedCheck_3434_ = !lean_is_exclusive(v___x_3413_);
if (v_isSharedCheck_3434_ == 0)
{
v___x_3429_ = v___x_3413_;
v_isShared_3430_ = v_isSharedCheck_3434_;
goto v_resetjp_3428_;
}
else
{
lean_inc(v_a_3427_);
lean_dec(v___x_3413_);
v___x_3429_ = lean_box(0);
v_isShared_3430_ = v_isSharedCheck_3434_;
goto v_resetjp_3428_;
}
v_resetjp_3428_:
{
lean_object* v___x_3432_; 
if (v_isShared_3430_ == 0)
{
v___x_3432_ = v___x_3429_;
goto v_reusejp_3431_;
}
else
{
lean_object* v_reuseFailAlloc_3433_; 
v_reuseFailAlloc_3433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3433_, 0, v_a_3427_);
v___x_3432_ = v_reuseFailAlloc_3433_;
goto v_reusejp_3431_;
}
v_reusejp_3431_:
{
return v___x_3432_;
}
}
}
}
}
}
else
{
lean_object* v_a_3437_; lean_object* v___x_3439_; uint8_t v_isShared_3440_; uint8_t v_isSharedCheck_3444_; 
lean_dec(v_a_3382_);
lean_del_object(v___x_3367_);
lean_dec(v_snd_3365_);
v_a_3437_ = lean_ctor_get(v___x_3407_, 0);
v_isSharedCheck_3444_ = !lean_is_exclusive(v___x_3407_);
if (v_isSharedCheck_3444_ == 0)
{
v___x_3439_ = v___x_3407_;
v_isShared_3440_ = v_isSharedCheck_3444_;
goto v_resetjp_3438_;
}
else
{
lean_inc(v_a_3437_);
lean_dec(v___x_3407_);
v___x_3439_ = lean_box(0);
v_isShared_3440_ = v_isSharedCheck_3444_;
goto v_resetjp_3438_;
}
v_resetjp_3438_:
{
lean_object* v___x_3442_; 
if (v_isShared_3440_ == 0)
{
v___x_3442_ = v___x_3439_;
goto v_reusejp_3441_;
}
else
{
lean_object* v_reuseFailAlloc_3443_; 
v_reuseFailAlloc_3443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3443_, 0, v_a_3437_);
v___x_3442_ = v_reuseFailAlloc_3443_;
goto v_reusejp_3441_;
}
v_reusejp_3441_:
{
return v___x_3442_;
}
}
}
}
}
else
{
lean_object* v_a_3445_; lean_object* v___x_3447_; uint8_t v_isShared_3448_; uint8_t v_isSharedCheck_3452_; 
lean_dec(v_a_3382_);
lean_del_object(v___x_3367_);
lean_dec(v_snd_3365_);
v_a_3445_ = lean_ctor_get(v___x_3406_, 0);
v_isSharedCheck_3452_ = !lean_is_exclusive(v___x_3406_);
if (v_isSharedCheck_3452_ == 0)
{
v___x_3447_ = v___x_3406_;
v_isShared_3448_ = v_isSharedCheck_3452_;
goto v_resetjp_3446_;
}
else
{
lean_inc(v_a_3445_);
lean_dec(v___x_3406_);
v___x_3447_ = lean_box(0);
v_isShared_3448_ = v_isSharedCheck_3452_;
goto v_resetjp_3446_;
}
v_resetjp_3446_:
{
lean_object* v___x_3450_; 
if (v_isShared_3448_ == 0)
{
v___x_3450_ = v___x_3447_;
goto v_reusejp_3449_;
}
else
{
lean_object* v_reuseFailAlloc_3451_; 
v_reuseFailAlloc_3451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3451_, 0, v_a_3445_);
v___x_3450_ = v_reuseFailAlloc_3451_;
goto v_reusejp_3449_;
}
v_reusejp_3449_:
{
return v___x_3450_;
}
}
}
v___jp_3383_:
{
uint8_t v___x_3394_; 
v___x_3394_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_3382_);
if (v___x_3394_ == 0)
{
lean_dec(v_a_3382_);
v_a_3372_ = v___x_3369_;
goto v___jp_3371_;
}
else
{
lean_object* v___x_3395_; 
v___x_3395_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc(v_a_3382_, v___y_3384_, v___y_3385_, v___y_3386_, v___y_3387_, v___y_3388_, v___y_3389_, v___y_3390_, v___y_3391_, v___y_3392_, v___y_3393_);
if (lean_obj_tag(v___x_3395_) == 0)
{
lean_dec_ref_known(v___x_3395_, 1);
v_a_3372_ = v___x_3369_;
goto v___jp_3371_;
}
else
{
lean_object* v_a_3396_; lean_object* v___x_3398_; uint8_t v_isShared_3399_; uint8_t v_isSharedCheck_3403_; 
lean_del_object(v___x_3367_);
v_a_3396_ = lean_ctor_get(v___x_3395_, 0);
v_isSharedCheck_3403_ = !lean_is_exclusive(v___x_3395_);
if (v_isSharedCheck_3403_ == 0)
{
v___x_3398_ = v___x_3395_;
v_isShared_3399_ = v_isSharedCheck_3403_;
goto v_resetjp_3397_;
}
else
{
lean_inc(v_a_3396_);
lean_dec(v___x_3395_);
v___x_3398_ = lean_box(0);
v_isShared_3399_ = v_isSharedCheck_3403_;
goto v_resetjp_3397_;
}
v_resetjp_3397_:
{
lean_object* v___x_3401_; 
if (v_isShared_3399_ == 0)
{
v___x_3401_ = v___x_3398_;
goto v_reusejp_3400_;
}
else
{
lean_object* v_reuseFailAlloc_3402_; 
v_reuseFailAlloc_3402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3402_, 0, v_a_3396_);
v___x_3401_ = v_reuseFailAlloc_3402_;
goto v_reusejp_3400_;
}
v_reusejp_3400_:
{
return v___x_3401_;
}
}
}
}
}
}
else
{
lean_object* v_a_3453_; lean_object* v___x_3455_; uint8_t v_isShared_3456_; uint8_t v_isSharedCheck_3460_; 
lean_del_object(v___x_3367_);
lean_dec(v_snd_3365_);
v_a_3453_ = lean_ctor_get(v___x_3381_, 0);
v_isSharedCheck_3460_ = !lean_is_exclusive(v___x_3381_);
if (v_isSharedCheck_3460_ == 0)
{
v___x_3455_ = v___x_3381_;
v_isShared_3456_ = v_isSharedCheck_3460_;
goto v_resetjp_3454_;
}
else
{
lean_inc(v_a_3453_);
lean_dec(v___x_3381_);
v___x_3455_ = lean_box(0);
v_isShared_3456_ = v_isSharedCheck_3460_;
goto v_resetjp_3454_;
}
v_resetjp_3454_:
{
lean_object* v___x_3458_; 
if (v_isShared_3456_ == 0)
{
v___x_3458_ = v___x_3455_;
goto v_reusejp_3457_;
}
else
{
lean_object* v_reuseFailAlloc_3459_; 
v_reuseFailAlloc_3459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3459_, 0, v_a_3453_);
v___x_3458_ = v_reuseFailAlloc_3459_;
goto v_reusejp_3457_;
}
v_reusejp_3457_:
{
return v___x_3458_;
}
}
}
v___jp_3371_:
{
lean_object* v___x_3374_; 
if (v_isShared_3368_ == 0)
{
lean_ctor_set(v___x_3367_, 1, v_a_3372_);
lean_ctor_set(v___x_3367_, 0, v___x_3370_);
v___x_3374_ = v___x_3367_;
goto v_reusejp_3373_;
}
else
{
lean_object* v_reuseFailAlloc_3378_; 
v_reuseFailAlloc_3378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3378_, 0, v___x_3370_);
lean_ctor_set(v_reuseFailAlloc_3378_, 1, v_a_3372_);
v___x_3374_ = v_reuseFailAlloc_3378_;
goto v_reusejp_3373_;
}
v_reusejp_3373_:
{
size_t v___x_3375_; size_t v___x_3376_; lean_object* v___x_3377_; 
v___x_3375_ = ((size_t)1ULL);
v___x_3376_ = lean_usize_add(v_i_3350_, v___x_3375_);
v___x_3377_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__1_spec__3_spec__4(v_as_3348_, v_sz_3349_, v___x_3376_, v___x_3374_, v___y_3352_, v___y_3353_, v___y_3354_, v___y_3355_, v___y_3356_, v___y_3357_, v___y_3358_, v___y_3359_, v___y_3360_, v___y_3361_);
return v___x_3377_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__1_spec__3___boxed(lean_object* v_as_3463_, lean_object* v_sz_3464_, lean_object* v_i_3465_, lean_object* v_b_3466_, lean_object* v___y_3467_, lean_object* v___y_3468_, lean_object* v___y_3469_, lean_object* v___y_3470_, lean_object* v___y_3471_, lean_object* v___y_3472_, lean_object* v___y_3473_, lean_object* v___y_3474_, lean_object* v___y_3475_, lean_object* v___y_3476_, lean_object* v___y_3477_){
_start:
{
size_t v_sz_boxed_3478_; size_t v_i_boxed_3479_; lean_object* v_res_3480_; 
v_sz_boxed_3478_ = lean_unbox_usize(v_sz_3464_);
lean_dec(v_sz_3464_);
v_i_boxed_3479_ = lean_unbox_usize(v_i_3465_);
lean_dec(v_i_3465_);
v_res_3480_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__1_spec__3(v_as_3463_, v_sz_boxed_3478_, v_i_boxed_3479_, v_b_3466_, v___y_3467_, v___y_3468_, v___y_3469_, v___y_3470_, v___y_3471_, v___y_3472_, v___y_3473_, v___y_3474_, v___y_3475_, v___y_3476_);
lean_dec(v___y_3476_);
lean_dec_ref(v___y_3475_);
lean_dec(v___y_3474_);
lean_dec_ref(v___y_3473_);
lean_dec(v___y_3472_);
lean_dec_ref(v___y_3471_);
lean_dec(v___y_3470_);
lean_dec_ref(v___y_3469_);
lean_dec(v___y_3468_);
lean_dec(v___y_3467_);
lean_dec_ref(v_as_3463_);
return v_res_3480_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__1(lean_object* v_init_3481_, lean_object* v_n_3482_, lean_object* v_b_3483_, lean_object* v___y_3484_, lean_object* v___y_3485_, lean_object* v___y_3486_, lean_object* v___y_3487_, lean_object* v___y_3488_, lean_object* v___y_3489_, lean_object* v___y_3490_, lean_object* v___y_3491_, lean_object* v___y_3492_, lean_object* v___y_3493_){
_start:
{
if (lean_obj_tag(v_n_3482_) == 0)
{
lean_object* v_cs_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; size_t v_sz_3498_; size_t v___x_3499_; lean_object* v___x_3500_; 
v_cs_3495_ = lean_ctor_get(v_n_3482_, 0);
v___x_3496_ = lean_box(0);
v___x_3497_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3497_, 0, v___x_3496_);
lean_ctor_set(v___x_3497_, 1, v_b_3483_);
v_sz_3498_ = lean_array_size(v_cs_3495_);
v___x_3499_ = ((size_t)0ULL);
v___x_3500_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__1_spec__2(v_init_3481_, v_cs_3495_, v_sz_3498_, v___x_3499_, v___x_3497_, v___y_3484_, v___y_3485_, v___y_3486_, v___y_3487_, v___y_3488_, v___y_3489_, v___y_3490_, v___y_3491_, v___y_3492_, v___y_3493_);
if (lean_obj_tag(v___x_3500_) == 0)
{
lean_object* v_a_3501_; lean_object* v___x_3503_; uint8_t v_isShared_3504_; uint8_t v_isSharedCheck_3515_; 
v_a_3501_ = lean_ctor_get(v___x_3500_, 0);
v_isSharedCheck_3515_ = !lean_is_exclusive(v___x_3500_);
if (v_isSharedCheck_3515_ == 0)
{
v___x_3503_ = v___x_3500_;
v_isShared_3504_ = v_isSharedCheck_3515_;
goto v_resetjp_3502_;
}
else
{
lean_inc(v_a_3501_);
lean_dec(v___x_3500_);
v___x_3503_ = lean_box(0);
v_isShared_3504_ = v_isSharedCheck_3515_;
goto v_resetjp_3502_;
}
v_resetjp_3502_:
{
lean_object* v_fst_3505_; 
v_fst_3505_ = lean_ctor_get(v_a_3501_, 0);
if (lean_obj_tag(v_fst_3505_) == 0)
{
lean_object* v_snd_3506_; lean_object* v___x_3507_; lean_object* v___x_3509_; 
v_snd_3506_ = lean_ctor_get(v_a_3501_, 1);
lean_inc(v_snd_3506_);
lean_dec(v_a_3501_);
v___x_3507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3507_, 0, v_snd_3506_);
if (v_isShared_3504_ == 0)
{
lean_ctor_set(v___x_3503_, 0, v___x_3507_);
v___x_3509_ = v___x_3503_;
goto v_reusejp_3508_;
}
else
{
lean_object* v_reuseFailAlloc_3510_; 
v_reuseFailAlloc_3510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3510_, 0, v___x_3507_);
v___x_3509_ = v_reuseFailAlloc_3510_;
goto v_reusejp_3508_;
}
v_reusejp_3508_:
{
return v___x_3509_;
}
}
else
{
lean_object* v_val_3511_; lean_object* v___x_3513_; 
lean_inc_ref(v_fst_3505_);
lean_dec(v_a_3501_);
v_val_3511_ = lean_ctor_get(v_fst_3505_, 0);
lean_inc(v_val_3511_);
lean_dec_ref_known(v_fst_3505_, 1);
if (v_isShared_3504_ == 0)
{
lean_ctor_set(v___x_3503_, 0, v_val_3511_);
v___x_3513_ = v___x_3503_;
goto v_reusejp_3512_;
}
else
{
lean_object* v_reuseFailAlloc_3514_; 
v_reuseFailAlloc_3514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3514_, 0, v_val_3511_);
v___x_3513_ = v_reuseFailAlloc_3514_;
goto v_reusejp_3512_;
}
v_reusejp_3512_:
{
return v___x_3513_;
}
}
}
}
else
{
lean_object* v_a_3516_; lean_object* v___x_3518_; uint8_t v_isShared_3519_; uint8_t v_isSharedCheck_3523_; 
v_a_3516_ = lean_ctor_get(v___x_3500_, 0);
v_isSharedCheck_3523_ = !lean_is_exclusive(v___x_3500_);
if (v_isSharedCheck_3523_ == 0)
{
v___x_3518_ = v___x_3500_;
v_isShared_3519_ = v_isSharedCheck_3523_;
goto v_resetjp_3517_;
}
else
{
lean_inc(v_a_3516_);
lean_dec(v___x_3500_);
v___x_3518_ = lean_box(0);
v_isShared_3519_ = v_isSharedCheck_3523_;
goto v_resetjp_3517_;
}
v_resetjp_3517_:
{
lean_object* v___x_3521_; 
if (v_isShared_3519_ == 0)
{
v___x_3521_ = v___x_3518_;
goto v_reusejp_3520_;
}
else
{
lean_object* v_reuseFailAlloc_3522_; 
v_reuseFailAlloc_3522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3522_, 0, v_a_3516_);
v___x_3521_ = v_reuseFailAlloc_3522_;
goto v_reusejp_3520_;
}
v_reusejp_3520_:
{
return v___x_3521_;
}
}
}
}
else
{
lean_object* v_vs_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; size_t v_sz_3527_; size_t v___x_3528_; lean_object* v___x_3529_; 
v_vs_3524_ = lean_ctor_get(v_n_3482_, 0);
v___x_3525_ = lean_box(0);
v___x_3526_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3526_, 0, v___x_3525_);
lean_ctor_set(v___x_3526_, 1, v_b_3483_);
v_sz_3527_ = lean_array_size(v_vs_3524_);
v___x_3528_ = ((size_t)0ULL);
v___x_3529_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__1_spec__3(v_vs_3524_, v_sz_3527_, v___x_3528_, v___x_3526_, v___y_3484_, v___y_3485_, v___y_3486_, v___y_3487_, v___y_3488_, v___y_3489_, v___y_3490_, v___y_3491_, v___y_3492_, v___y_3493_);
if (lean_obj_tag(v___x_3529_) == 0)
{
lean_object* v_a_3530_; lean_object* v___x_3532_; uint8_t v_isShared_3533_; uint8_t v_isSharedCheck_3544_; 
v_a_3530_ = lean_ctor_get(v___x_3529_, 0);
v_isSharedCheck_3544_ = !lean_is_exclusive(v___x_3529_);
if (v_isSharedCheck_3544_ == 0)
{
v___x_3532_ = v___x_3529_;
v_isShared_3533_ = v_isSharedCheck_3544_;
goto v_resetjp_3531_;
}
else
{
lean_inc(v_a_3530_);
lean_dec(v___x_3529_);
v___x_3532_ = lean_box(0);
v_isShared_3533_ = v_isSharedCheck_3544_;
goto v_resetjp_3531_;
}
v_resetjp_3531_:
{
lean_object* v_fst_3534_; 
v_fst_3534_ = lean_ctor_get(v_a_3530_, 0);
if (lean_obj_tag(v_fst_3534_) == 0)
{
lean_object* v_snd_3535_; lean_object* v___x_3536_; lean_object* v___x_3538_; 
v_snd_3535_ = lean_ctor_get(v_a_3530_, 1);
lean_inc(v_snd_3535_);
lean_dec(v_a_3530_);
v___x_3536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3536_, 0, v_snd_3535_);
if (v_isShared_3533_ == 0)
{
lean_ctor_set(v___x_3532_, 0, v___x_3536_);
v___x_3538_ = v___x_3532_;
goto v_reusejp_3537_;
}
else
{
lean_object* v_reuseFailAlloc_3539_; 
v_reuseFailAlloc_3539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3539_, 0, v___x_3536_);
v___x_3538_ = v_reuseFailAlloc_3539_;
goto v_reusejp_3537_;
}
v_reusejp_3537_:
{
return v___x_3538_;
}
}
else
{
lean_object* v_val_3540_; lean_object* v___x_3542_; 
lean_inc_ref(v_fst_3534_);
lean_dec(v_a_3530_);
v_val_3540_ = lean_ctor_get(v_fst_3534_, 0);
lean_inc(v_val_3540_);
lean_dec_ref_known(v_fst_3534_, 1);
if (v_isShared_3533_ == 0)
{
lean_ctor_set(v___x_3532_, 0, v_val_3540_);
v___x_3542_ = v___x_3532_;
goto v_reusejp_3541_;
}
else
{
lean_object* v_reuseFailAlloc_3543_; 
v_reuseFailAlloc_3543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3543_, 0, v_val_3540_);
v___x_3542_ = v_reuseFailAlloc_3543_;
goto v_reusejp_3541_;
}
v_reusejp_3541_:
{
return v___x_3542_;
}
}
}
}
else
{
lean_object* v_a_3545_; lean_object* v___x_3547_; uint8_t v_isShared_3548_; uint8_t v_isSharedCheck_3552_; 
v_a_3545_ = lean_ctor_get(v___x_3529_, 0);
v_isSharedCheck_3552_ = !lean_is_exclusive(v___x_3529_);
if (v_isSharedCheck_3552_ == 0)
{
v___x_3547_ = v___x_3529_;
v_isShared_3548_ = v_isSharedCheck_3552_;
goto v_resetjp_3546_;
}
else
{
lean_inc(v_a_3545_);
lean_dec(v___x_3529_);
v___x_3547_ = lean_box(0);
v_isShared_3548_ = v_isSharedCheck_3552_;
goto v_resetjp_3546_;
}
v_resetjp_3546_:
{
lean_object* v___x_3550_; 
if (v_isShared_3548_ == 0)
{
v___x_3550_ = v___x_3547_;
goto v_reusejp_3549_;
}
else
{
lean_object* v_reuseFailAlloc_3551_; 
v_reuseFailAlloc_3551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3551_, 0, v_a_3545_);
v___x_3550_ = v_reuseFailAlloc_3551_;
goto v_reusejp_3549_;
}
v_reusejp_3549_:
{
return v___x_3550_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__1_spec__2(lean_object* v_init_3553_, lean_object* v_as_3554_, size_t v_sz_3555_, size_t v_i_3556_, lean_object* v_b_3557_, lean_object* v___y_3558_, lean_object* v___y_3559_, lean_object* v___y_3560_, lean_object* v___y_3561_, lean_object* v___y_3562_, lean_object* v___y_3563_, lean_object* v___y_3564_, lean_object* v___y_3565_, lean_object* v___y_3566_, lean_object* v___y_3567_){
_start:
{
uint8_t v___x_3569_; 
v___x_3569_ = lean_usize_dec_lt(v_i_3556_, v_sz_3555_);
if (v___x_3569_ == 0)
{
lean_object* v___x_3570_; 
v___x_3570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3570_, 0, v_b_3557_);
return v___x_3570_;
}
else
{
lean_object* v_snd_3571_; lean_object* v___x_3573_; uint8_t v_isShared_3574_; uint8_t v_isSharedCheck_3605_; 
v_snd_3571_ = lean_ctor_get(v_b_3557_, 1);
v_isSharedCheck_3605_ = !lean_is_exclusive(v_b_3557_);
if (v_isSharedCheck_3605_ == 0)
{
lean_object* v_unused_3606_; 
v_unused_3606_ = lean_ctor_get(v_b_3557_, 0);
lean_dec(v_unused_3606_);
v___x_3573_ = v_b_3557_;
v_isShared_3574_ = v_isSharedCheck_3605_;
goto v_resetjp_3572_;
}
else
{
lean_inc(v_snd_3571_);
lean_dec(v_b_3557_);
v___x_3573_ = lean_box(0);
v_isShared_3574_ = v_isSharedCheck_3605_;
goto v_resetjp_3572_;
}
v_resetjp_3572_:
{
lean_object* v___x_3575_; lean_object* v_a_3576_; lean_object* v___x_3577_; 
v___x_3575_ = lean_box(0);
v_a_3576_ = lean_array_uget_borrowed(v_as_3554_, v_i_3556_);
lean_inc(v_snd_3571_);
v___x_3577_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__1(v_init_3553_, v_a_3576_, v_snd_3571_, v___y_3558_, v___y_3559_, v___y_3560_, v___y_3561_, v___y_3562_, v___y_3563_, v___y_3564_, v___y_3565_, v___y_3566_, v___y_3567_);
if (lean_obj_tag(v___x_3577_) == 0)
{
lean_object* v_a_3578_; lean_object* v___x_3580_; uint8_t v_isShared_3581_; uint8_t v_isSharedCheck_3596_; 
v_a_3578_ = lean_ctor_get(v___x_3577_, 0);
v_isSharedCheck_3596_ = !lean_is_exclusive(v___x_3577_);
if (v_isSharedCheck_3596_ == 0)
{
v___x_3580_ = v___x_3577_;
v_isShared_3581_ = v_isSharedCheck_3596_;
goto v_resetjp_3579_;
}
else
{
lean_inc(v_a_3578_);
lean_dec(v___x_3577_);
v___x_3580_ = lean_box(0);
v_isShared_3581_ = v_isSharedCheck_3596_;
goto v_resetjp_3579_;
}
v_resetjp_3579_:
{
if (lean_obj_tag(v_a_3578_) == 0)
{
lean_object* v___x_3582_; lean_object* v___x_3584_; 
v___x_3582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3582_, 0, v_a_3578_);
if (v_isShared_3574_ == 0)
{
lean_ctor_set(v___x_3573_, 0, v___x_3582_);
v___x_3584_ = v___x_3573_;
goto v_reusejp_3583_;
}
else
{
lean_object* v_reuseFailAlloc_3588_; 
v_reuseFailAlloc_3588_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3588_, 0, v___x_3582_);
lean_ctor_set(v_reuseFailAlloc_3588_, 1, v_snd_3571_);
v___x_3584_ = v_reuseFailAlloc_3588_;
goto v_reusejp_3583_;
}
v_reusejp_3583_:
{
lean_object* v___x_3586_; 
if (v_isShared_3581_ == 0)
{
lean_ctor_set(v___x_3580_, 0, v___x_3584_);
v___x_3586_ = v___x_3580_;
goto v_reusejp_3585_;
}
else
{
lean_object* v_reuseFailAlloc_3587_; 
v_reuseFailAlloc_3587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3587_, 0, v___x_3584_);
v___x_3586_ = v_reuseFailAlloc_3587_;
goto v_reusejp_3585_;
}
v_reusejp_3585_:
{
return v___x_3586_;
}
}
}
else
{
lean_object* v_a_3589_; lean_object* v___x_3591_; 
lean_del_object(v___x_3580_);
lean_dec(v_snd_3571_);
v_a_3589_ = lean_ctor_get(v_a_3578_, 0);
lean_inc(v_a_3589_);
lean_dec_ref_known(v_a_3578_, 1);
if (v_isShared_3574_ == 0)
{
lean_ctor_set(v___x_3573_, 1, v_a_3589_);
lean_ctor_set(v___x_3573_, 0, v___x_3575_);
v___x_3591_ = v___x_3573_;
goto v_reusejp_3590_;
}
else
{
lean_object* v_reuseFailAlloc_3595_; 
v_reuseFailAlloc_3595_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3595_, 0, v___x_3575_);
lean_ctor_set(v_reuseFailAlloc_3595_, 1, v_a_3589_);
v___x_3591_ = v_reuseFailAlloc_3595_;
goto v_reusejp_3590_;
}
v_reusejp_3590_:
{
size_t v___x_3592_; size_t v___x_3593_; 
v___x_3592_ = ((size_t)1ULL);
v___x_3593_ = lean_usize_add(v_i_3556_, v___x_3592_);
v_i_3556_ = v___x_3593_;
v_b_3557_ = v___x_3591_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_3597_; lean_object* v___x_3599_; uint8_t v_isShared_3600_; uint8_t v_isSharedCheck_3604_; 
lean_del_object(v___x_3573_);
lean_dec(v_snd_3571_);
v_a_3597_ = lean_ctor_get(v___x_3577_, 0);
v_isSharedCheck_3604_ = !lean_is_exclusive(v___x_3577_);
if (v_isSharedCheck_3604_ == 0)
{
v___x_3599_ = v___x_3577_;
v_isShared_3600_ = v_isSharedCheck_3604_;
goto v_resetjp_3598_;
}
else
{
lean_inc(v_a_3597_);
lean_dec(v___x_3577_);
v___x_3599_ = lean_box(0);
v_isShared_3600_ = v_isSharedCheck_3604_;
goto v_resetjp_3598_;
}
v_resetjp_3598_:
{
lean_object* v___x_3602_; 
if (v_isShared_3600_ == 0)
{
v___x_3602_ = v___x_3599_;
goto v_reusejp_3601_;
}
else
{
lean_object* v_reuseFailAlloc_3603_; 
v_reuseFailAlloc_3603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3603_, 0, v_a_3597_);
v___x_3602_ = v_reuseFailAlloc_3603_;
goto v_reusejp_3601_;
}
v_reusejp_3601_:
{
return v___x_3602_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__1_spec__2___boxed(lean_object* v_init_3607_, lean_object* v_as_3608_, lean_object* v_sz_3609_, lean_object* v_i_3610_, lean_object* v_b_3611_, lean_object* v___y_3612_, lean_object* v___y_3613_, lean_object* v___y_3614_, lean_object* v___y_3615_, lean_object* v___y_3616_, lean_object* v___y_3617_, lean_object* v___y_3618_, lean_object* v___y_3619_, lean_object* v___y_3620_, lean_object* v___y_3621_, lean_object* v___y_3622_){
_start:
{
size_t v_sz_boxed_3623_; size_t v_i_boxed_3624_; lean_object* v_res_3625_; 
v_sz_boxed_3623_ = lean_unbox_usize(v_sz_3609_);
lean_dec(v_sz_3609_);
v_i_boxed_3624_ = lean_unbox_usize(v_i_3610_);
lean_dec(v_i_3610_);
v_res_3625_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__1_spec__2(v_init_3607_, v_as_3608_, v_sz_boxed_3623_, v_i_boxed_3624_, v_b_3611_, v___y_3612_, v___y_3613_, v___y_3614_, v___y_3615_, v___y_3616_, v___y_3617_, v___y_3618_, v___y_3619_, v___y_3620_, v___y_3621_);
lean_dec(v___y_3621_);
lean_dec_ref(v___y_3620_);
lean_dec(v___y_3619_);
lean_dec_ref(v___y_3618_);
lean_dec(v___y_3617_);
lean_dec_ref(v___y_3616_);
lean_dec(v___y_3615_);
lean_dec_ref(v___y_3614_);
lean_dec(v___y_3613_);
lean_dec(v___y_3612_);
lean_dec_ref(v_as_3608_);
return v_res_3625_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__1___boxed(lean_object* v_init_3626_, lean_object* v_n_3627_, lean_object* v_b_3628_, lean_object* v___y_3629_, lean_object* v___y_3630_, lean_object* v___y_3631_, lean_object* v___y_3632_, lean_object* v___y_3633_, lean_object* v___y_3634_, lean_object* v___y_3635_, lean_object* v___y_3636_, lean_object* v___y_3637_, lean_object* v___y_3638_, lean_object* v___y_3639_){
_start:
{
lean_object* v_res_3640_; 
v_res_3640_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__1(v_init_3626_, v_n_3627_, v_b_3628_, v___y_3629_, v___y_3630_, v___y_3631_, v___y_3632_, v___y_3633_, v___y_3634_, v___y_3635_, v___y_3636_, v___y_3637_, v___y_3638_);
lean_dec(v___y_3638_);
lean_dec_ref(v___y_3637_);
lean_dec(v___y_3636_);
lean_dec_ref(v___y_3635_);
lean_dec(v___y_3634_);
lean_dec_ref(v___y_3633_);
lean_dec(v___y_3632_);
lean_dec_ref(v___y_3631_);
lean_dec(v___y_3630_);
lean_dec(v___y_3629_);
lean_dec_ref(v_n_3627_);
return v_res_3640_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1(lean_object* v_t_3641_, lean_object* v_init_3642_, lean_object* v___y_3643_, lean_object* v___y_3644_, lean_object* v___y_3645_, lean_object* v___y_3646_, lean_object* v___y_3647_, lean_object* v___y_3648_, lean_object* v___y_3649_, lean_object* v___y_3650_, lean_object* v___y_3651_, lean_object* v___y_3652_){
_start:
{
lean_object* v_root_3654_; lean_object* v_tail_3655_; lean_object* v___x_3656_; 
v_root_3654_ = lean_ctor_get(v_t_3641_, 0);
v_tail_3655_ = lean_ctor_get(v_t_3641_, 1);
v___x_3656_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__1(v_init_3642_, v_root_3654_, v_init_3642_, v___y_3643_, v___y_3644_, v___y_3645_, v___y_3646_, v___y_3647_, v___y_3648_, v___y_3649_, v___y_3650_, v___y_3651_, v___y_3652_);
if (lean_obj_tag(v___x_3656_) == 0)
{
lean_object* v_a_3657_; lean_object* v___x_3659_; uint8_t v_isShared_3660_; uint8_t v_isSharedCheck_3693_; 
v_a_3657_ = lean_ctor_get(v___x_3656_, 0);
v_isSharedCheck_3693_ = !lean_is_exclusive(v___x_3656_);
if (v_isSharedCheck_3693_ == 0)
{
v___x_3659_ = v___x_3656_;
v_isShared_3660_ = v_isSharedCheck_3693_;
goto v_resetjp_3658_;
}
else
{
lean_inc(v_a_3657_);
lean_dec(v___x_3656_);
v___x_3659_ = lean_box(0);
v_isShared_3660_ = v_isSharedCheck_3693_;
goto v_resetjp_3658_;
}
v_resetjp_3658_:
{
if (lean_obj_tag(v_a_3657_) == 0)
{
lean_object* v_a_3661_; lean_object* v___x_3663_; 
v_a_3661_ = lean_ctor_get(v_a_3657_, 0);
lean_inc(v_a_3661_);
lean_dec_ref_known(v_a_3657_, 1);
if (v_isShared_3660_ == 0)
{
lean_ctor_set(v___x_3659_, 0, v_a_3661_);
v___x_3663_ = v___x_3659_;
goto v_reusejp_3662_;
}
else
{
lean_object* v_reuseFailAlloc_3664_; 
v_reuseFailAlloc_3664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3664_, 0, v_a_3661_);
v___x_3663_ = v_reuseFailAlloc_3664_;
goto v_reusejp_3662_;
}
v_reusejp_3662_:
{
return v___x_3663_;
}
}
else
{
lean_object* v_a_3665_; lean_object* v___x_3666_; lean_object* v___x_3667_; size_t v_sz_3668_; size_t v___x_3669_; lean_object* v___x_3670_; 
lean_del_object(v___x_3659_);
v_a_3665_ = lean_ctor_get(v_a_3657_, 0);
lean_inc(v_a_3665_);
lean_dec_ref_known(v_a_3657_, 1);
v___x_3666_ = lean_box(0);
v___x_3667_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3667_, 0, v___x_3666_);
lean_ctor_set(v___x_3667_, 1, v_a_3665_);
v_sz_3668_ = lean_array_size(v_tail_3655_);
v___x_3669_ = ((size_t)0ULL);
v___x_3670_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__2(v_tail_3655_, v_sz_3668_, v___x_3669_, v___x_3667_, v___y_3643_, v___y_3644_, v___y_3645_, v___y_3646_, v___y_3647_, v___y_3648_, v___y_3649_, v___y_3650_, v___y_3651_, v___y_3652_);
if (lean_obj_tag(v___x_3670_) == 0)
{
lean_object* v_a_3671_; lean_object* v___x_3673_; uint8_t v_isShared_3674_; uint8_t v_isSharedCheck_3684_; 
v_a_3671_ = lean_ctor_get(v___x_3670_, 0);
v_isSharedCheck_3684_ = !lean_is_exclusive(v___x_3670_);
if (v_isSharedCheck_3684_ == 0)
{
v___x_3673_ = v___x_3670_;
v_isShared_3674_ = v_isSharedCheck_3684_;
goto v_resetjp_3672_;
}
else
{
lean_inc(v_a_3671_);
lean_dec(v___x_3670_);
v___x_3673_ = lean_box(0);
v_isShared_3674_ = v_isSharedCheck_3684_;
goto v_resetjp_3672_;
}
v_resetjp_3672_:
{
lean_object* v_fst_3675_; 
v_fst_3675_ = lean_ctor_get(v_a_3671_, 0);
if (lean_obj_tag(v_fst_3675_) == 0)
{
lean_object* v_snd_3676_; lean_object* v___x_3678_; 
v_snd_3676_ = lean_ctor_get(v_a_3671_, 1);
lean_inc(v_snd_3676_);
lean_dec(v_a_3671_);
if (v_isShared_3674_ == 0)
{
lean_ctor_set(v___x_3673_, 0, v_snd_3676_);
v___x_3678_ = v___x_3673_;
goto v_reusejp_3677_;
}
else
{
lean_object* v_reuseFailAlloc_3679_; 
v_reuseFailAlloc_3679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3679_, 0, v_snd_3676_);
v___x_3678_ = v_reuseFailAlloc_3679_;
goto v_reusejp_3677_;
}
v_reusejp_3677_:
{
return v___x_3678_;
}
}
else
{
lean_object* v_val_3680_; lean_object* v___x_3682_; 
lean_inc_ref(v_fst_3675_);
lean_dec(v_a_3671_);
v_val_3680_ = lean_ctor_get(v_fst_3675_, 0);
lean_inc(v_val_3680_);
lean_dec_ref_known(v_fst_3675_, 1);
if (v_isShared_3674_ == 0)
{
lean_ctor_set(v___x_3673_, 0, v_val_3680_);
v___x_3682_ = v___x_3673_;
goto v_reusejp_3681_;
}
else
{
lean_object* v_reuseFailAlloc_3683_; 
v_reuseFailAlloc_3683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3683_, 0, v_val_3680_);
v___x_3682_ = v_reuseFailAlloc_3683_;
goto v_reusejp_3681_;
}
v_reusejp_3681_:
{
return v___x_3682_;
}
}
}
}
else
{
lean_object* v_a_3685_; lean_object* v___x_3687_; uint8_t v_isShared_3688_; uint8_t v_isSharedCheck_3692_; 
v_a_3685_ = lean_ctor_get(v___x_3670_, 0);
v_isSharedCheck_3692_ = !lean_is_exclusive(v___x_3670_);
if (v_isSharedCheck_3692_ == 0)
{
v___x_3687_ = v___x_3670_;
v_isShared_3688_ = v_isSharedCheck_3692_;
goto v_resetjp_3686_;
}
else
{
lean_inc(v_a_3685_);
lean_dec(v___x_3670_);
v___x_3687_ = lean_box(0);
v_isShared_3688_ = v_isSharedCheck_3692_;
goto v_resetjp_3686_;
}
v_resetjp_3686_:
{
lean_object* v___x_3690_; 
if (v_isShared_3688_ == 0)
{
v___x_3690_ = v___x_3687_;
goto v_reusejp_3689_;
}
else
{
lean_object* v_reuseFailAlloc_3691_; 
v_reuseFailAlloc_3691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3691_, 0, v_a_3685_);
v___x_3690_ = v_reuseFailAlloc_3691_;
goto v_reusejp_3689_;
}
v_reusejp_3689_:
{
return v___x_3690_;
}
}
}
}
}
}
else
{
lean_object* v_a_3694_; lean_object* v___x_3696_; uint8_t v_isShared_3697_; uint8_t v_isSharedCheck_3701_; 
v_a_3694_ = lean_ctor_get(v___x_3656_, 0);
v_isSharedCheck_3701_ = !lean_is_exclusive(v___x_3656_);
if (v_isSharedCheck_3701_ == 0)
{
v___x_3696_ = v___x_3656_;
v_isShared_3697_ = v_isSharedCheck_3701_;
goto v_resetjp_3695_;
}
else
{
lean_inc(v_a_3694_);
lean_dec(v___x_3656_);
v___x_3696_ = lean_box(0);
v_isShared_3697_ = v_isSharedCheck_3701_;
goto v_resetjp_3695_;
}
v_resetjp_3695_:
{
lean_object* v___x_3699_; 
if (v_isShared_3697_ == 0)
{
v___x_3699_ = v___x_3696_;
goto v_reusejp_3698_;
}
else
{
lean_object* v_reuseFailAlloc_3700_; 
v_reuseFailAlloc_3700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3700_, 0, v_a_3694_);
v___x_3699_ = v_reuseFailAlloc_3700_;
goto v_reusejp_3698_;
}
v_reusejp_3698_:
{
return v___x_3699_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1___boxed(lean_object* v_t_3702_, lean_object* v_init_3703_, lean_object* v___y_3704_, lean_object* v___y_3705_, lean_object* v___y_3706_, lean_object* v___y_3707_, lean_object* v___y_3708_, lean_object* v___y_3709_, lean_object* v___y_3710_, lean_object* v___y_3711_, lean_object* v___y_3712_, lean_object* v___y_3713_, lean_object* v___y_3714_){
_start:
{
lean_object* v_res_3715_; 
v_res_3715_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1(v_t_3702_, v_init_3703_, v___y_3704_, v___y_3705_, v___y_3706_, v___y_3707_, v___y_3708_, v___y_3709_, v___y_3710_, v___y_3711_, v___y_3712_, v___y_3713_);
lean_dec(v___y_3713_);
lean_dec_ref(v___y_3712_);
lean_dec(v___y_3711_);
lean_dec_ref(v___y_3710_);
lean_dec(v___y_3709_);
lean_dec_ref(v___y_3708_);
lean_dec(v___y_3707_);
lean_dec_ref(v___y_3706_);
lean_dec(v___y_3705_);
lean_dec(v___y_3704_);
lean_dec_ref(v_t_3702_);
return v_res_3715_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_checkInvariants(uint8_t v_expensive_3716_, lean_object* v_a_3717_, lean_object* v_a_3718_, lean_object* v_a_3719_, lean_object* v_a_3720_, lean_object* v_a_3721_, lean_object* v_a_3722_, lean_object* v_a_3723_, lean_object* v_a_3724_, lean_object* v_a_3725_, lean_object* v_a_3726_){
_start:
{
lean_object* v___y_3732_; lean_object* v___y_3733_; lean_object* v___y_3734_; lean_object* v___y_3735_; lean_object* v___y_3736_; lean_object* v___y_3737_; lean_object* v___y_3738_; lean_object* v___y_3739_; lean_object* v___y_3740_; lean_object* v___y_3741_; lean_object* v___y_3747_; lean_object* v___y_3748_; lean_object* v___y_3749_; lean_object* v___y_3750_; lean_object* v___y_3751_; lean_object* v___y_3752_; lean_object* v___y_3753_; lean_object* v___y_3754_; lean_object* v___y_3755_; lean_object* v___y_3756_; uint8_t v_debug_3758_; 
v_debug_3758_ = lean_ctor_get_uint8(v_a_3719_, sizeof(void*)*12 + 2);
if (v_debug_3758_ == 0)
{
v___y_3732_ = v_a_3717_;
v___y_3733_ = v_a_3718_;
v___y_3734_ = v_a_3719_;
v___y_3735_ = v_a_3720_;
v___y_3736_ = v_a_3721_;
v___y_3737_ = v_a_3722_;
v___y_3738_ = v_a_3723_;
v___y_3739_ = v_a_3724_;
v___y_3740_ = v_a_3725_;
v___y_3741_ = v_a_3726_;
goto v___jp_3731_;
}
else
{
lean_object* v___x_3759_; 
v___x_3759_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkCongrTable(v_a_3717_, v_a_3718_, v_a_3719_, v_a_3720_, v_a_3721_, v_a_3722_, v_a_3723_, v_a_3724_, v_a_3725_, v_a_3726_);
if (lean_obj_tag(v___x_3759_) == 0)
{
lean_object* v___x_3760_; 
lean_dec_ref_known(v___x_3759_, 1);
v___x_3760_ = l_Lean_Meta_Grind_getExprs___redArg(v_a_3717_);
if (lean_obj_tag(v___x_3760_) == 0)
{
lean_object* v_a_3761_; lean_object* v___x_3762_; lean_object* v___x_3763_; 
v_a_3761_ = lean_ctor_get(v___x_3760_, 0);
lean_inc(v_a_3761_);
lean_dec_ref_known(v___x_3760_, 1);
v___x_3762_ = lean_box(0);
v___x_3763_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1(v_a_3761_, v___x_3762_, v_a_3717_, v_a_3718_, v_a_3719_, v_a_3720_, v_a_3721_, v_a_3722_, v_a_3723_, v_a_3724_, v_a_3725_, v_a_3726_);
lean_dec(v_a_3761_);
if (lean_obj_tag(v___x_3763_) == 0)
{
lean_dec_ref_known(v___x_3763_, 1);
if (v_expensive_3716_ == 0)
{
v___y_3747_ = v_a_3717_;
v___y_3748_ = v_a_3718_;
v___y_3749_ = v_a_3719_;
v___y_3750_ = v_a_3720_;
v___y_3751_ = v_a_3721_;
v___y_3752_ = v_a_3722_;
v___y_3753_ = v_a_3723_;
v___y_3754_ = v_a_3724_;
v___y_3755_ = v_a_3725_;
v___y_3756_ = v_a_3726_;
goto v___jp_3746_;
}
else
{
lean_object* v___x_3764_; 
v___x_3764_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq(v_a_3717_, v_a_3718_, v_a_3719_, v_a_3720_, v_a_3721_, v_a_3722_, v_a_3723_, v_a_3724_, v_a_3725_, v_a_3726_);
if (lean_obj_tag(v___x_3764_) == 0)
{
lean_dec_ref_known(v___x_3764_, 1);
v___y_3747_ = v_a_3717_;
v___y_3748_ = v_a_3718_;
v___y_3749_ = v_a_3719_;
v___y_3750_ = v_a_3720_;
v___y_3751_ = v_a_3721_;
v___y_3752_ = v_a_3722_;
v___y_3753_ = v_a_3723_;
v___y_3754_ = v_a_3724_;
v___y_3755_ = v_a_3725_;
v___y_3756_ = v_a_3726_;
goto v___jp_3746_;
}
else
{
return v___x_3764_;
}
}
}
else
{
return v___x_3763_;
}
}
else
{
lean_object* v_a_3765_; lean_object* v___x_3767_; uint8_t v_isShared_3768_; uint8_t v_isSharedCheck_3772_; 
v_a_3765_ = lean_ctor_get(v___x_3760_, 0);
v_isSharedCheck_3772_ = !lean_is_exclusive(v___x_3760_);
if (v_isSharedCheck_3772_ == 0)
{
v___x_3767_ = v___x_3760_;
v_isShared_3768_ = v_isSharedCheck_3772_;
goto v_resetjp_3766_;
}
else
{
lean_inc(v_a_3765_);
lean_dec(v___x_3760_);
v___x_3767_ = lean_box(0);
v_isShared_3768_ = v_isSharedCheck_3772_;
goto v_resetjp_3766_;
}
v_resetjp_3766_:
{
lean_object* v___x_3770_; 
if (v_isShared_3768_ == 0)
{
v___x_3770_ = v___x_3767_;
goto v_reusejp_3769_;
}
else
{
lean_object* v_reuseFailAlloc_3771_; 
v_reuseFailAlloc_3771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3771_, 0, v_a_3765_);
v___x_3770_ = v_reuseFailAlloc_3771_;
goto v_reusejp_3769_;
}
v_reusejp_3769_:
{
return v___x_3770_;
}
}
}
}
else
{
return v___x_3759_;
}
}
v___jp_3728_:
{
lean_object* v___x_3729_; lean_object* v___x_3730_; 
v___x_3729_ = lean_box(0);
v___x_3730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3730_, 0, v___x_3729_);
return v___x_3730_;
}
v___jp_3731_:
{
if (v_expensive_3716_ == 0)
{
goto v___jp_3728_;
}
else
{
lean_object* v___x_3742_; lean_object* v___x_3743_; uint8_t v___x_3744_; 
v___x_3742_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_3740_);
v___x_3743_ = l_Lean_Meta_Grind_grind_debug_proofs;
v___x_3744_ = l_Lean_Option_get___at___00Lean_Meta_Grind_checkInvariants_spec__0(v___x_3742_, v___x_3743_);
lean_dec_ref(v___x_3742_);
if (v___x_3744_ == 0)
{
goto v___jp_3728_;
}
else
{
lean_object* v___x_3745_; 
v___x_3745_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs(v___y_3732_, v___y_3733_, v___y_3734_, v___y_3735_, v___y_3736_, v___y_3737_, v___y_3738_, v___y_3739_, v___y_3740_, v___y_3741_);
return v___x_3745_;
}
}
}
v___jp_3746_:
{
lean_object* v___x_3757_; 
v___x_3757_ = l_Lean_Meta_Grind_Solvers_checkInvariants(v___y_3747_, v___y_3748_, v___y_3749_, v___y_3750_, v___y_3751_, v___y_3752_, v___y_3753_, v___y_3754_, v___y_3755_, v___y_3756_);
if (lean_obj_tag(v___x_3757_) == 0)
{
lean_dec_ref_known(v___x_3757_, 1);
v___y_3732_ = v___y_3747_;
v___y_3733_ = v___y_3748_;
v___y_3734_ = v___y_3749_;
v___y_3735_ = v___y_3750_;
v___y_3736_ = v___y_3751_;
v___y_3737_ = v___y_3752_;
v___y_3738_ = v___y_3753_;
v___y_3739_ = v___y_3754_;
v___y_3740_ = v___y_3755_;
v___y_3741_ = v___y_3756_;
goto v___jp_3731_;
}
else
{
return v___x_3757_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_checkInvariants___boxed(lean_object* v_expensive_3773_, lean_object* v_a_3774_, lean_object* v_a_3775_, lean_object* v_a_3776_, lean_object* v_a_3777_, lean_object* v_a_3778_, lean_object* v_a_3779_, lean_object* v_a_3780_, lean_object* v_a_3781_, lean_object* v_a_3782_, lean_object* v_a_3783_, lean_object* v_a_3784_){
_start:
{
uint8_t v_expensive_boxed_3785_; lean_object* v_res_3786_; 
v_expensive_boxed_3785_ = lean_unbox(v_expensive_3773_);
v_res_3786_ = l_Lean_Meta_Grind_checkInvariants(v_expensive_boxed_3785_, v_a_3774_, v_a_3775_, v_a_3776_, v_a_3777_, v_a_3778_, v_a_3779_, v_a_3780_, v_a_3781_, v_a_3782_, v_a_3783_);
lean_dec(v_a_3783_);
lean_dec_ref(v_a_3782_);
lean_dec(v_a_3781_);
lean_dec_ref(v_a_3780_);
lean_dec(v_a_3779_);
lean_dec_ref(v_a_3778_);
lean_dec(v_a_3777_);
lean_dec_ref(v_a_3776_);
lean_dec(v_a_3775_);
lean_dec(v_a_3774_);
return v_res_3786_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Goal_checkInvariants_spec__0___redArg___lam__0(lean_object* v_x_3787_, lean_object* v___y_3788_, lean_object* v___y_3789_, lean_object* v___y_3790_, lean_object* v___y_3791_, lean_object* v___y_3792_, lean_object* v___y_3793_, lean_object* v___y_3794_, lean_object* v___y_3795_, lean_object* v___y_3796_){
_start:
{
lean_object* v___x_3798_; 
lean_inc(v___y_3792_);
lean_inc_ref(v___y_3791_);
lean_inc(v___y_3790_);
lean_inc_ref(v___y_3789_);
lean_inc(v___y_3788_);
v___x_3798_ = lean_apply_10(v_x_3787_, v___y_3788_, v___y_3789_, v___y_3790_, v___y_3791_, v___y_3792_, v___y_3793_, v___y_3794_, v___y_3795_, v___y_3796_, lean_box(0));
return v___x_3798_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Goal_checkInvariants_spec__0___redArg___lam__0___boxed(lean_object* v_x_3799_, lean_object* v___y_3800_, lean_object* v___y_3801_, lean_object* v___y_3802_, lean_object* v___y_3803_, lean_object* v___y_3804_, lean_object* v___y_3805_, lean_object* v___y_3806_, lean_object* v___y_3807_, lean_object* v___y_3808_, lean_object* v___y_3809_){
_start:
{
lean_object* v_res_3810_; 
v_res_3810_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Goal_checkInvariants_spec__0___redArg___lam__0(v_x_3799_, v___y_3800_, v___y_3801_, v___y_3802_, v___y_3803_, v___y_3804_, v___y_3805_, v___y_3806_, v___y_3807_, v___y_3808_);
lean_dec(v___y_3804_);
lean_dec_ref(v___y_3803_);
lean_dec(v___y_3802_);
lean_dec_ref(v___y_3801_);
lean_dec(v___y_3800_);
return v_res_3810_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Goal_checkInvariants_spec__0___redArg(lean_object* v_mvarId_3811_, lean_object* v_x_3812_, lean_object* v___y_3813_, lean_object* v___y_3814_, lean_object* v___y_3815_, lean_object* v___y_3816_, lean_object* v___y_3817_, lean_object* v___y_3818_, lean_object* v___y_3819_, lean_object* v___y_3820_, lean_object* v___y_3821_){
_start:
{
lean_object* v___f_3823_; lean_object* v___x_3824_; 
lean_inc(v___y_3817_);
lean_inc_ref(v___y_3816_);
lean_inc(v___y_3815_);
lean_inc_ref(v___y_3814_);
lean_inc(v___y_3813_);
v___f_3823_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Goal_checkInvariants_spec__0___redArg___lam__0___boxed), 11, 6);
lean_closure_set(v___f_3823_, 0, v_x_3812_);
lean_closure_set(v___f_3823_, 1, v___y_3813_);
lean_closure_set(v___f_3823_, 2, v___y_3814_);
lean_closure_set(v___f_3823_, 3, v___y_3815_);
lean_closure_set(v___f_3823_, 4, v___y_3816_);
lean_closure_set(v___f_3823_, 5, v___y_3817_);
v___x_3824_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_3811_, v___f_3823_, v___y_3818_, v___y_3819_, v___y_3820_, v___y_3821_);
if (lean_obj_tag(v___x_3824_) == 0)
{
return v___x_3824_;
}
else
{
lean_object* v_a_3825_; lean_object* v___x_3827_; uint8_t v_isShared_3828_; uint8_t v_isSharedCheck_3832_; 
v_a_3825_ = lean_ctor_get(v___x_3824_, 0);
v_isSharedCheck_3832_ = !lean_is_exclusive(v___x_3824_);
if (v_isSharedCheck_3832_ == 0)
{
v___x_3827_ = v___x_3824_;
v_isShared_3828_ = v_isSharedCheck_3832_;
goto v_resetjp_3826_;
}
else
{
lean_inc(v_a_3825_);
lean_dec(v___x_3824_);
v___x_3827_ = lean_box(0);
v_isShared_3828_ = v_isSharedCheck_3832_;
goto v_resetjp_3826_;
}
v_resetjp_3826_:
{
lean_object* v___x_3830_; 
if (v_isShared_3828_ == 0)
{
v___x_3830_ = v___x_3827_;
goto v_reusejp_3829_;
}
else
{
lean_object* v_reuseFailAlloc_3831_; 
v_reuseFailAlloc_3831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3831_, 0, v_a_3825_);
v___x_3830_ = v_reuseFailAlloc_3831_;
goto v_reusejp_3829_;
}
v_reusejp_3829_:
{
return v___x_3830_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Goal_checkInvariants_spec__0___redArg___boxed(lean_object* v_mvarId_3833_, lean_object* v_x_3834_, lean_object* v___y_3835_, lean_object* v___y_3836_, lean_object* v___y_3837_, lean_object* v___y_3838_, lean_object* v___y_3839_, lean_object* v___y_3840_, lean_object* v___y_3841_, lean_object* v___y_3842_, lean_object* v___y_3843_, lean_object* v___y_3844_){
_start:
{
lean_object* v_res_3845_; 
v_res_3845_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Goal_checkInvariants_spec__0___redArg(v_mvarId_3833_, v_x_3834_, v___y_3835_, v___y_3836_, v___y_3837_, v___y_3838_, v___y_3839_, v___y_3840_, v___y_3841_, v___y_3842_, v___y_3843_);
lean_dec(v___y_3843_);
lean_dec_ref(v___y_3842_);
lean_dec(v___y_3841_);
lean_dec_ref(v___y_3840_);
lean_dec(v___y_3839_);
lean_dec_ref(v___y_3838_);
lean_dec(v___y_3837_);
lean_dec_ref(v___y_3836_);
lean_dec(v___y_3835_);
return v_res_3845_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Goal_checkInvariants_spec__0(lean_object* v_00_u03b1_3846_, lean_object* v_mvarId_3847_, lean_object* v_x_3848_, lean_object* v___y_3849_, lean_object* v___y_3850_, lean_object* v___y_3851_, lean_object* v___y_3852_, lean_object* v___y_3853_, lean_object* v___y_3854_, lean_object* v___y_3855_, lean_object* v___y_3856_, lean_object* v___y_3857_){
_start:
{
lean_object* v___x_3859_; 
v___x_3859_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Goal_checkInvariants_spec__0___redArg(v_mvarId_3847_, v_x_3848_, v___y_3849_, v___y_3850_, v___y_3851_, v___y_3852_, v___y_3853_, v___y_3854_, v___y_3855_, v___y_3856_, v___y_3857_);
return v___x_3859_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Goal_checkInvariants_spec__0___boxed(lean_object* v_00_u03b1_3860_, lean_object* v_mvarId_3861_, lean_object* v_x_3862_, lean_object* v___y_3863_, lean_object* v___y_3864_, lean_object* v___y_3865_, lean_object* v___y_3866_, lean_object* v___y_3867_, lean_object* v___y_3868_, lean_object* v___y_3869_, lean_object* v___y_3870_, lean_object* v___y_3871_, lean_object* v___y_3872_){
_start:
{
lean_object* v_res_3873_; 
v_res_3873_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Goal_checkInvariants_spec__0(v_00_u03b1_3860_, v_mvarId_3861_, v_x_3862_, v___y_3863_, v___y_3864_, v___y_3865_, v___y_3866_, v___y_3867_, v___y_3868_, v___y_3869_, v___y_3870_, v___y_3871_);
lean_dec(v___y_3871_);
lean_dec_ref(v___y_3870_);
lean_dec(v___y_3869_);
lean_dec_ref(v___y_3868_);
lean_dec(v___y_3867_);
lean_dec_ref(v___y_3866_);
lean_dec(v___y_3865_);
lean_dec_ref(v___y_3864_);
lean_dec(v___y_3863_);
return v_res_3873_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Goal_checkInvariants___lam__0(lean_object* v_goal_3874_, uint8_t v_expensive_3875_, lean_object* v___y_3876_, lean_object* v___y_3877_, lean_object* v___y_3878_, lean_object* v___y_3879_, lean_object* v___y_3880_, lean_object* v___y_3881_, lean_object* v___y_3882_, lean_object* v___y_3883_, lean_object* v___y_3884_){
_start:
{
lean_object* v___x_3886_; lean_object* v___x_3887_; 
v___x_3886_ = lean_st_mk_ref(v_goal_3874_);
v___x_3887_ = l_Lean_Meta_Grind_checkInvariants(v_expensive_3875_, v___x_3886_, v___y_3876_, v___y_3877_, v___y_3878_, v___y_3879_, v___y_3880_, v___y_3881_, v___y_3882_, v___y_3883_, v___y_3884_);
if (lean_obj_tag(v___x_3887_) == 0)
{
lean_object* v___x_3889_; uint8_t v_isShared_3890_; uint8_t v_isSharedCheck_3896_; 
v_isSharedCheck_3896_ = !lean_is_exclusive(v___x_3887_);
if (v_isSharedCheck_3896_ == 0)
{
lean_object* v_unused_3897_; 
v_unused_3897_ = lean_ctor_get(v___x_3887_, 0);
lean_dec(v_unused_3897_);
v___x_3889_ = v___x_3887_;
v_isShared_3890_ = v_isSharedCheck_3896_;
goto v_resetjp_3888_;
}
else
{
lean_dec(v___x_3887_);
v___x_3889_ = lean_box(0);
v_isShared_3890_ = v_isSharedCheck_3896_;
goto v_resetjp_3888_;
}
v_resetjp_3888_:
{
lean_object* v___x_3891_; lean_object* v___x_3892_; lean_object* v___x_3894_; 
v___x_3891_ = lean_st_ref_get(v___x_3886_);
v___x_3892_ = lean_st_ref_get(v___x_3886_);
lean_dec(v___x_3886_);
lean_dec(v___x_3892_);
if (v_isShared_3890_ == 0)
{
lean_ctor_set(v___x_3889_, 0, v___x_3891_);
v___x_3894_ = v___x_3889_;
goto v_reusejp_3893_;
}
else
{
lean_object* v_reuseFailAlloc_3895_; 
v_reuseFailAlloc_3895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3895_, 0, v___x_3891_);
v___x_3894_ = v_reuseFailAlloc_3895_;
goto v_reusejp_3893_;
}
v_reusejp_3893_:
{
return v___x_3894_;
}
}
}
else
{
lean_object* v_a_3898_; lean_object* v___x_3900_; uint8_t v_isShared_3901_; uint8_t v_isSharedCheck_3905_; 
lean_dec(v___x_3886_);
v_a_3898_ = lean_ctor_get(v___x_3887_, 0);
v_isSharedCheck_3905_ = !lean_is_exclusive(v___x_3887_);
if (v_isSharedCheck_3905_ == 0)
{
v___x_3900_ = v___x_3887_;
v_isShared_3901_ = v_isSharedCheck_3905_;
goto v_resetjp_3899_;
}
else
{
lean_inc(v_a_3898_);
lean_dec(v___x_3887_);
v___x_3900_ = lean_box(0);
v_isShared_3901_ = v_isSharedCheck_3905_;
goto v_resetjp_3899_;
}
v_resetjp_3899_:
{
lean_object* v___x_3903_; 
if (v_isShared_3901_ == 0)
{
v___x_3903_ = v___x_3900_;
goto v_reusejp_3902_;
}
else
{
lean_object* v_reuseFailAlloc_3904_; 
v_reuseFailAlloc_3904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3904_, 0, v_a_3898_);
v___x_3903_ = v_reuseFailAlloc_3904_;
goto v_reusejp_3902_;
}
v_reusejp_3902_:
{
return v___x_3903_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Goal_checkInvariants___lam__0___boxed(lean_object* v_goal_3906_, lean_object* v_expensive_3907_, lean_object* v___y_3908_, lean_object* v___y_3909_, lean_object* v___y_3910_, lean_object* v___y_3911_, lean_object* v___y_3912_, lean_object* v___y_3913_, lean_object* v___y_3914_, lean_object* v___y_3915_, lean_object* v___y_3916_, lean_object* v___y_3917_){
_start:
{
uint8_t v_expensive_boxed_3918_; lean_object* v_res_3919_; 
v_expensive_boxed_3918_ = lean_unbox(v_expensive_3907_);
v_res_3919_ = l_Lean_Meta_Grind_Goal_checkInvariants___lam__0(v_goal_3906_, v_expensive_boxed_3918_, v___y_3908_, v___y_3909_, v___y_3910_, v___y_3911_, v___y_3912_, v___y_3913_, v___y_3914_, v___y_3915_, v___y_3916_);
lean_dec(v___y_3916_);
lean_dec_ref(v___y_3915_);
lean_dec(v___y_3914_);
lean_dec_ref(v___y_3913_);
lean_dec(v___y_3912_);
lean_dec_ref(v___y_3911_);
lean_dec(v___y_3910_);
lean_dec_ref(v___y_3909_);
lean_dec(v___y_3908_);
return v_res_3919_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Goal_checkInvariants(lean_object* v_goal_3920_, uint8_t v_expensive_3921_, lean_object* v_a_3922_, lean_object* v_a_3923_, lean_object* v_a_3924_, lean_object* v_a_3925_, lean_object* v_a_3926_, lean_object* v_a_3927_, lean_object* v_a_3928_, lean_object* v_a_3929_, lean_object* v_a_3930_){
_start:
{
lean_object* v_mvarId_3932_; lean_object* v___x_3933_; lean_object* v___f_3934_; lean_object* v___x_3935_; lean_object* v___x_3936_; 
v_mvarId_3932_ = lean_ctor_get(v_goal_3920_, 1);
lean_inc(v_mvarId_3932_);
v___x_3933_ = lean_box(v_expensive_3921_);
v___f_3934_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Goal_checkInvariants___lam__0___boxed), 12, 2);
lean_closure_set(v___f_3934_, 0, v_goal_3920_);
lean_closure_set(v___f_3934_, 1, v___x_3933_);
v___x_3935_ = lean_box(0);
v___x_3936_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Goal_checkInvariants_spec__0___redArg(v_mvarId_3932_, v___f_3934_, v_a_3922_, v_a_3923_, v_a_3924_, v_a_3925_, v_a_3926_, v_a_3927_, v_a_3928_, v_a_3929_, v_a_3930_);
if (lean_obj_tag(v___x_3936_) == 0)
{
lean_object* v___x_3938_; uint8_t v_isShared_3939_; uint8_t v_isSharedCheck_3943_; 
v_isSharedCheck_3943_ = !lean_is_exclusive(v___x_3936_);
if (v_isSharedCheck_3943_ == 0)
{
lean_object* v_unused_3944_; 
v_unused_3944_ = lean_ctor_get(v___x_3936_, 0);
lean_dec(v_unused_3944_);
v___x_3938_ = v___x_3936_;
v_isShared_3939_ = v_isSharedCheck_3943_;
goto v_resetjp_3937_;
}
else
{
lean_dec(v___x_3936_);
v___x_3938_ = lean_box(0);
v_isShared_3939_ = v_isSharedCheck_3943_;
goto v_resetjp_3937_;
}
v_resetjp_3937_:
{
lean_object* v___x_3941_; 
if (v_isShared_3939_ == 0)
{
lean_ctor_set(v___x_3938_, 0, v___x_3935_);
v___x_3941_ = v___x_3938_;
goto v_reusejp_3940_;
}
else
{
lean_object* v_reuseFailAlloc_3942_; 
v_reuseFailAlloc_3942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3942_, 0, v___x_3935_);
v___x_3941_ = v_reuseFailAlloc_3942_;
goto v_reusejp_3940_;
}
v_reusejp_3940_:
{
return v___x_3941_;
}
}
}
else
{
lean_object* v_a_3945_; lean_object* v___x_3947_; uint8_t v_isShared_3948_; uint8_t v_isSharedCheck_3952_; 
v_a_3945_ = lean_ctor_get(v___x_3936_, 0);
v_isSharedCheck_3952_ = !lean_is_exclusive(v___x_3936_);
if (v_isSharedCheck_3952_ == 0)
{
v___x_3947_ = v___x_3936_;
v_isShared_3948_ = v_isSharedCheck_3952_;
goto v_resetjp_3946_;
}
else
{
lean_inc(v_a_3945_);
lean_dec(v___x_3936_);
v___x_3947_ = lean_box(0);
v_isShared_3948_ = v_isSharedCheck_3952_;
goto v_resetjp_3946_;
}
v_resetjp_3946_:
{
lean_object* v___x_3950_; 
if (v_isShared_3948_ == 0)
{
v___x_3950_ = v___x_3947_;
goto v_reusejp_3949_;
}
else
{
lean_object* v_reuseFailAlloc_3951_; 
v_reuseFailAlloc_3951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3951_, 0, v_a_3945_);
v___x_3950_ = v_reuseFailAlloc_3951_;
goto v_reusejp_3949_;
}
v_reusejp_3949_:
{
return v___x_3950_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Goal_checkInvariants___boxed(lean_object* v_goal_3953_, lean_object* v_expensive_3954_, lean_object* v_a_3955_, lean_object* v_a_3956_, lean_object* v_a_3957_, lean_object* v_a_3958_, lean_object* v_a_3959_, lean_object* v_a_3960_, lean_object* v_a_3961_, lean_object* v_a_3962_, lean_object* v_a_3963_, lean_object* v_a_3964_){
_start:
{
uint8_t v_expensive_boxed_3965_; lean_object* v_res_3966_; 
v_expensive_boxed_3965_ = lean_unbox(v_expensive_3954_);
v_res_3966_ = l_Lean_Meta_Grind_Goal_checkInvariants(v_goal_3953_, v_expensive_boxed_3965_, v_a_3955_, v_a_3956_, v_a_3957_, v_a_3958_, v_a_3959_, v_a_3960_, v_a_3961_, v_a_3962_, v_a_3963_);
lean_dec(v_a_3963_);
lean_dec_ref(v_a_3962_);
lean_dec(v_a_3961_);
lean_dec_ref(v_a_3960_);
lean_dec(v_a_3959_);
lean_dec_ref(v_a_3958_);
lean_dec(v_a_3957_);
lean_dec_ref(v_a_3956_);
lean_dec(v_a_3955_);
return v_res_3966_;
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
