// Lean compiler output
// Module: Lean.Meta.Tactic.Induction
// Imports: public import Lean.Meta.RecursorInfo public import Lean.Meta.SynthInstance public import Lean.Meta.Tactic.Revert public import Lean.Meta.Tactic.Intro public import Lean.Meta.Tactic.FVarSubst import Lean.Meta.WHNF import Init.Omega
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
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Meta_throwTacticEx___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_normalizeLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_Meta_whnfUntil(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_synthInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Expr_abstractM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLambda(lean_object*, uint8_t, lean_object*, lean_object*);
uint8_t l_Lean_Level_isZero(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_Meta_mkTacticExMsg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_tagWithErrorName(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Lean_Expr_isHeadBetaTarget(lean_object*, uint8_t);
lean_object* l_Lean_Expr_headBeta(lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_introNCore(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_FVarSubst_insert(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_MVarId_tryClear(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_synthInstance_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_BinderInfo_isInstImplicit(uint8_t);
lean_object* l_Lean_Name_eraseMacroScopes(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_RecursorInfo_firstIndexPos(lean_object*);
lean_object* l_Lean_MVarId_getTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t l_Lean_Expr_isForall(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_revert(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_intro1Core(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_checkNotAssigned(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkRecursorInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTargetArity(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "induction"};
static const lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 130, 81, 169, 97, 77, 195, 126)}};
static const lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 49, .m_capacity = 49, .m_length = 48, .m_data = "failed to generate type class instance parameter"};
static const lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__2_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__3_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__4;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__5;
static const lean_string_object l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "ill-formed recursor"};
static const lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__6_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__6_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__7_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__8;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_instInhabitedInductionSubgoal_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_instInhabitedInductionSubgoal_default___closed__0 = (const lean_object*)&l_Lean_Meta_instInhabitedInductionSubgoal_default___closed__0_value;
static const lean_ctor_object l_Lean_Meta_instInhabitedInductionSubgoal_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_instInhabitedInductionSubgoal_default___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_instInhabitedInductionSubgoal_default___closed__1 = (const lean_object*)&l_Lean_Meta_instInhabitedInductionSubgoal_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_instInhabitedInductionSubgoal_default = (const lean_object*)&l_Lean_Meta_instInhabitedInductionSubgoal_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_instInhabitedInductionSubgoal = (const lean_object*)&l_Lean_Meta_instInhabitedInductionSubgoal_default___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTypeBody(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTypeBody___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_instInhabitedAltVarNames_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Meta_instInhabitedAltVarNames_default___closed__0 = (const lean_object*)&l_Lean_Meta_instInhabitedAltVarNames_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_instInhabitedAltVarNames_default = (const lean_object*)&l_Lean_Meta_instInhabitedAltVarNames_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_instInhabitedAltVarNames = (const lean_object*)&l_Lean_Meta_instInhabitedAltVarNames_default___closed__0_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instInhabitedMetaM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__4___closed__0 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__4___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__5(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__8_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__8___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__9___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__3(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__0_value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__1_value),LEAN_SCALAR_PTR_LITERAL(194, 95, 140, 15, 16, 100, 236, 219)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__0_value),LEAN_SCALAR_PTR_LITERAL(27, 58, 44, 222, 146, 107, 234, 180)}};
static const lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__4_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5;
static const lean_string_object l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "finalize loop is done, "};
static const lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__6_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__7;
static const lean_string_object l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = " subgoals"};
static const lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__8_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__9;
static const lean_string_object l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "name of major premise: "};
static const lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__10_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__11;
static const lean_string_object l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "Lean.Meta.Tactic.Induction"};
static const lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__12_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 62, .m_capacity = 62, .m_length = 61, .m_data = "_private.Lean.Meta.Tactic.Induction.0.Lean.Meta.finalize.loop"};
static const lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__13_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__14 = (const lean_object*)&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__14_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__15;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__9(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__8_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "unexpected major premise type"};
static const lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___lam__1___boxed(lean_object*);
static const lean_closure_object l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__0_value;
static lean_once_cell_t l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__1;
static lean_once_cell_t l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__2;
static lean_once_cell_t l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_Meta_getMajorTypeIndices_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_Meta_getMajorTypeIndices_spec__1___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1;
static const lean_string_object l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 80, .m_capacity = 80, .m_length = 79, .m_data = "' is an index in major premise, but it depends on index occurring at position #"};
static const lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__2 = (const lean_object*)&l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__3;
static const lean_string_object l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "' is an index in major premise, but it occurs in previous arguments"};
static const lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__4 = (const lean_object*)&l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__4_value;
static lean_once_cell_t l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__5;
static const lean_string_object l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 61, .m_capacity = 61, .m_length = 60, .m_data = "' is an index in major premise, but it occurs more than once"};
static const lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__6 = (const lean_object*)&l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__6_value;
static lean_once_cell_t l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__7;
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "major premise type index "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__1;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = " is not a variable"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__3;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "major premise type is ill-formed"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__4_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__5;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_getMajorTypeIndices___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_getMajorTypeIndices___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_getMajorTypeIndices(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMajorTypeIndices___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Meta_mkRecursorAppPrefix_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Meta_mkRecursorAppPrefix_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__0 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__0_value;
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__1 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__1_value;
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "x"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__2 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__2_value;
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__2_value),LEAN_SCALAR_PTR_LITERAL(243, 101, 181, 186, 114, 114, 131, 189)}};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__3 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__3_value;
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__4 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__4_value;
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "propRecLargeElim"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__5 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__5_value;
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__4_value),LEAN_SCALAR_PTR_LITERAL(43, 31, 155, 49, 49, 182, 172, 127)}};
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__6_value_aux_0),((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__5_value),LEAN_SCALAR_PTR_LITERAL(247, 150, 90, 37, 93, 225, 222, 61)}};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__6 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__6_value;
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "recursor `"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__7 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__7_value;
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__8;
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "` can only eliminate into `Prop`"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__9 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__9_value;
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__10;
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "major premise is not of the form (C ...)"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__11 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__11_value;
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__11_value)}};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__12 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__12_value;
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__13;
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__14;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkRecursorAppPrefix(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkRecursorAppPrefix___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_induction_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_induction_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_induction_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_induction_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_MVarId_induction_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_MVarId_induction_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "after revert&intro\n"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__0 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__0_value;
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__1;
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "recursor '"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__2 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__2_value;
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__3;
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 82, .m_capacity = 82, .m_length = 81, .m_data = "' does not support dependent elimination, but conclusion depends on major premise"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__4 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__4_value;
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__5;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_MVarId_induction___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "initial\n"};
static const lean_object* l_Lean_MVarId_induction___lam__0___closed__0 = (const lean_object*)&l_Lean_MVarId_induction___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_MVarId_induction___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_induction___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_MVarId_induction___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_induction___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_induction(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_induction___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__0_value),LEAN_SCALAR_PTR_LITERAL(30, 196, 118, 96, 111, 225, 34, 188)}};
static const lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__1_value),LEAN_SCALAR_PTR_LITERAL(195, 68, 87, 56, 63, 220, 109, 253)}};
static const lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Induction"};
static const lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(200, 161, 153, 93, 172, 95, 141, 251)}};
static const lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(33, 195, 219, 148, 137, 228, 88, 235)}};
static const lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(68, 113, 129, 206, 9, 87, 13, 178)}};
static const lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__0_value),LEAN_SCALAR_PTR_LITERAL(152, 143, 189, 240, 107, 203, 213, 249)}};
static const lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(85, 74, 162, 121, 91, 90, 201, 140)}};
static const lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(232, 112, 100, 153, 45, 77, 246, 77)}};
static const lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(65, 136, 94, 243, 100, 124, 110, 115)}};
static const lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__0_value),LEAN_SCALAR_PTR_LITERAL(129, 114, 213, 115, 63, 176, 63, 0)}};
static const lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__1_value),LEAN_SCALAR_PTR_LITERAL(136, 188, 18, 124, 108, 218, 130, 11)}};
static const lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(31, 31, 91, 195, 199, 49, 171, 123)}};
static const lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTargetArity(lean_object* v_x_1_){
_start:
{
switch(lean_obj_tag(v_x_1_))
{
case 10:
{
lean_object* v_expr_2_; 
v_expr_2_ = lean_ctor_get(v_x_1_, 1);
lean_inc_ref(v_expr_2_);
lean_dec_ref_known(v_x_1_, 2);
v_x_1_ = v_expr_2_;
goto _start;
}
case 7:
{
lean_object* v_body_4_; lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; 
v_body_4_ = lean_ctor_get(v_x_1_, 2);
lean_inc_ref(v_body_4_);
lean_dec_ref_known(v_x_1_, 3);
v___x_5_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTargetArity(v_body_4_);
v___x_6_ = lean_unsigned_to_nat(1u);
v___x_7_ = lean_nat_add(v___x_5_, v___x_6_);
lean_dec(v___x_5_);
return v___x_7_;
}
default: 
{
uint8_t v___x_8_; uint8_t v___x_9_; 
v___x_8_ = 0;
v___x_9_ = l_Lean_Expr_isHeadBetaTarget(v_x_1_, v___x_8_);
if (v___x_9_ == 0)
{
lean_object* v___x_10_; 
lean_dec_ref(v_x_1_);
v___x_10_ = lean_unsigned_to_nat(0u);
return v___x_10_;
}
else
{
lean_object* v___x_11_; 
v___x_11_ = l_Lean_Expr_headBeta(v_x_1_);
v_x_1_ = v___x_11_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__4(void){
_start:
{
lean_object* v___x_19_; lean_object* v___x_20_; 
v___x_19_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__3));
v___x_20_ = l_Lean_MessageData_ofFormat(v___x_19_);
return v___x_20_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__5(void){
_start:
{
lean_object* v___x_21_; lean_object* v___x_22_; 
v___x_21_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__4, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__4_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__4);
v___x_22_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_22_, 0, v___x_21_);
return v___x_22_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__8(void){
_start:
{
lean_object* v___x_26_; lean_object* v___x_27_; 
v___x_26_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__7));
v___x_27_ = l_Lean_MessageData_ofFormat(v___x_26_);
return v___x_27_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9(void){
_start:
{
lean_object* v___x_28_; lean_object* v___x_29_; 
v___x_28_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__8, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__8_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__8);
v___x_29_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_29_, 0, v___x_28_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams(lean_object* v_mvarId_30_, lean_object* v_majorTypeArgs_31_, lean_object* v_x_32_, lean_object* v_x_33_, lean_object* v_a_34_, lean_object* v_a_35_, lean_object* v_a_36_, lean_object* v_a_37_){
_start:
{
if (lean_obj_tag(v_x_32_) == 0)
{
lean_object* v___x_39_; 
lean_dec(v_mvarId_30_);
v___x_39_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_39_, 0, v_x_33_);
return v___x_39_;
}
else
{
lean_object* v_head_40_; lean_object* v_tail_41_; lean_object* v___y_43_; 
v_head_40_ = lean_ctor_get(v_x_32_, 0);
lean_inc(v_head_40_);
v_tail_41_ = lean_ctor_get(v_x_32_, 1);
lean_inc(v_tail_41_);
lean_dec_ref_known(v_x_32_, 2);
if (lean_obj_tag(v_head_40_) == 0)
{
lean_object* v___x_47_; 
lean_inc(v_a_37_);
lean_inc_ref(v_a_36_);
lean_inc(v_a_35_);
lean_inc_ref(v_a_34_);
lean_inc_ref(v_x_33_);
v___x_47_ = lean_infer_type(v_x_33_, v_a_34_, v_a_35_, v_a_36_, v_a_37_);
if (lean_obj_tag(v___x_47_) == 0)
{
lean_object* v_a_48_; lean_object* v___x_49_; 
v_a_48_ = lean_ctor_get(v___x_47_, 0);
lean_inc(v_a_48_);
lean_dec_ref_known(v___x_47_, 1);
v___x_49_ = l_Lean_Meta_whnfForall(v_a_48_, v_a_34_, v_a_35_, v_a_36_, v_a_37_);
if (lean_obj_tag(v___x_49_) == 0)
{
lean_object* v_a_50_; 
v_a_50_ = lean_ctor_get(v___x_49_, 0);
lean_inc(v_a_50_);
lean_dec_ref_known(v___x_49_, 1);
if (lean_obj_tag(v_a_50_) == 7)
{
lean_object* v_binderType_51_; lean_object* v___x_52_; 
v_binderType_51_ = lean_ctor_get(v_a_50_, 1);
lean_inc_ref(v_binderType_51_);
lean_dec_ref_known(v_a_50_, 3);
v___x_52_ = l_Lean_Meta_synthInstance(v_binderType_51_, v_head_40_, v_a_34_, v_a_35_, v_a_36_, v_a_37_);
if (lean_obj_tag(v___x_52_) == 0)
{
v___y_43_ = v___x_52_;
goto v___jp_42_;
}
else
{
lean_object* v_a_53_; uint8_t v___y_55_; uint8_t v___x_59_; 
v_a_53_ = lean_ctor_get(v___x_52_, 0);
lean_inc(v_a_53_);
v___x_59_ = l_Lean_Exception_isInterrupt(v_a_53_);
if (v___x_59_ == 0)
{
uint8_t v___x_60_; 
v___x_60_ = l_Lean_Exception_isRuntime(v_a_53_);
v___y_55_ = v___x_60_;
goto v___jp_54_;
}
else
{
lean_dec(v_a_53_);
v___y_55_ = v___x_59_;
goto v___jp_54_;
}
v___jp_54_:
{
if (v___y_55_ == 0)
{
lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; 
lean_dec_ref_known(v___x_52_, 1);
v___x_56_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1));
v___x_57_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__5, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__5_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__5);
lean_inc(v_mvarId_30_);
v___x_58_ = l_Lean_Meta_throwTacticEx___redArg(v___x_56_, v_mvarId_30_, v___x_57_, v_a_34_, v_a_35_, v_a_36_, v_a_37_);
v___y_43_ = v___x_58_;
goto v___jp_42_;
}
else
{
v___y_43_ = v___x_52_;
goto v___jp_42_;
}
}
}
}
else
{
lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; 
lean_dec(v_a_50_);
lean_dec(v_tail_41_);
lean_dec_ref(v_x_33_);
v___x_61_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1));
v___x_62_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9);
v___x_63_ = l_Lean_Meta_throwTacticEx___redArg(v___x_61_, v_mvarId_30_, v___x_62_, v_a_34_, v_a_35_, v_a_36_, v_a_37_);
return v___x_63_;
}
}
else
{
lean_dec(v_tail_41_);
lean_dec_ref(v_x_33_);
lean_dec(v_mvarId_30_);
return v___x_49_;
}
}
else
{
lean_dec(v_tail_41_);
lean_dec_ref(v_x_33_);
lean_dec(v_mvarId_30_);
return v___x_47_;
}
}
else
{
lean_object* v_val_64_; lean_object* v___x_65_; uint8_t v___x_66_; 
v_val_64_ = lean_ctor_get(v_head_40_, 0);
lean_inc(v_val_64_);
lean_dec_ref_known(v_head_40_, 1);
v___x_65_ = lean_array_get_size(v_majorTypeArgs_31_);
v___x_66_ = lean_nat_dec_lt(v_val_64_, v___x_65_);
if (v___x_66_ == 0)
{
lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; 
lean_dec(v_val_64_);
lean_dec(v_tail_41_);
lean_dec_ref(v_x_33_);
v___x_67_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1));
v___x_68_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9);
v___x_69_ = l_Lean_Meta_throwTacticEx___redArg(v___x_67_, v_mvarId_30_, v___x_68_, v_a_34_, v_a_35_, v_a_36_, v_a_37_);
return v___x_69_;
}
else
{
lean_object* v___x_70_; lean_object* v___x_71_; 
v___x_70_ = lean_array_fget_borrowed(v_majorTypeArgs_31_, v_val_64_);
lean_dec(v_val_64_);
lean_inc(v___x_70_);
v___x_71_ = l_Lean_Expr_app___override(v_x_33_, v___x_70_);
v_x_32_ = v_tail_41_;
v_x_33_ = v___x_71_;
goto _start;
}
}
v___jp_42_:
{
if (lean_obj_tag(v___y_43_) == 0)
{
lean_object* v_a_44_; lean_object* v___x_45_; 
v_a_44_ = lean_ctor_get(v___y_43_, 0);
lean_inc(v_a_44_);
lean_dec_ref_known(v___y_43_, 1);
v___x_45_ = l_Lean_Expr_app___override(v_x_33_, v_a_44_);
v_x_32_ = v_tail_41_;
v_x_33_ = v___x_45_;
goto _start;
}
else
{
lean_dec(v_tail_41_);
lean_dec_ref(v_x_33_);
lean_dec(v_mvarId_30_);
return v___y_43_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___boxed(lean_object* v_mvarId_73_, lean_object* v_majorTypeArgs_74_, lean_object* v_x_75_, lean_object* v_x_76_, lean_object* v_a_77_, lean_object* v_a_78_, lean_object* v_a_79_, lean_object* v_a_80_, lean_object* v_a_81_){
_start:
{
lean_object* v_res_82_; 
v_res_82_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams(v_mvarId_73_, v_majorTypeArgs_74_, v_x_75_, v_x_76_, v_a_77_, v_a_78_, v_a_79_, v_a_80_);
lean_dec(v_a_80_);
lean_dec_ref(v_a_79_);
lean_dec(v_a_78_);
lean_dec_ref(v_a_77_);
lean_dec_ref(v_majorTypeArgs_74_);
return v_res_82_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTypeBody(lean_object* v_mvarId_91_, lean_object* v_type_92_, lean_object* v_x_93_, lean_object* v_a_94_, lean_object* v_a_95_, lean_object* v_a_96_, lean_object* v_a_97_){
_start:
{
lean_object* v___x_99_; 
v___x_99_ = l_Lean_Meta_whnfForall(v_type_92_, v_a_94_, v_a_95_, v_a_96_, v_a_97_);
if (lean_obj_tag(v___x_99_) == 0)
{
lean_object* v_a_100_; lean_object* v___x_102_; uint8_t v_isShared_103_; uint8_t v_isSharedCheck_112_; 
v_a_100_ = lean_ctor_get(v___x_99_, 0);
v_isSharedCheck_112_ = !lean_is_exclusive(v___x_99_);
if (v_isSharedCheck_112_ == 0)
{
v___x_102_ = v___x_99_;
v_isShared_103_ = v_isSharedCheck_112_;
goto v_resetjp_101_;
}
else
{
lean_inc(v_a_100_);
lean_dec(v___x_99_);
v___x_102_ = lean_box(0);
v_isShared_103_ = v_isSharedCheck_112_;
goto v_resetjp_101_;
}
v_resetjp_101_:
{
if (lean_obj_tag(v_a_100_) == 7)
{
lean_object* v_body_104_; lean_object* v___x_105_; lean_object* v___x_107_; 
lean_dec(v_mvarId_91_);
v_body_104_ = lean_ctor_get(v_a_100_, 2);
lean_inc_ref(v_body_104_);
lean_dec_ref_known(v_a_100_, 3);
v___x_105_ = lean_expr_instantiate1(v_body_104_, v_x_93_);
lean_dec_ref(v_body_104_);
if (v_isShared_103_ == 0)
{
lean_ctor_set(v___x_102_, 0, v___x_105_);
v___x_107_ = v___x_102_;
goto v_reusejp_106_;
}
else
{
lean_object* v_reuseFailAlloc_108_; 
v_reuseFailAlloc_108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_108_, 0, v___x_105_);
v___x_107_ = v_reuseFailAlloc_108_;
goto v_reusejp_106_;
}
v_reusejp_106_:
{
return v___x_107_;
}
}
else
{
lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; 
lean_del_object(v___x_102_);
lean_dec(v_a_100_);
v___x_109_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1));
v___x_110_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9);
v___x_111_ = l_Lean_Meta_throwTacticEx___redArg(v___x_109_, v_mvarId_91_, v___x_110_, v_a_94_, v_a_95_, v_a_96_, v_a_97_);
return v___x_111_;
}
}
}
else
{
lean_dec(v_mvarId_91_);
return v___x_99_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTypeBody___boxed(lean_object* v_mvarId_113_, lean_object* v_type_114_, lean_object* v_x_115_, lean_object* v_a_116_, lean_object* v_a_117_, lean_object* v_a_118_, lean_object* v_a_119_, lean_object* v_a_120_){
_start:
{
lean_object* v_res_121_; 
v_res_121_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTypeBody(v_mvarId_113_, v_type_114_, v_x_115_, v_a_116_, v_a_117_, v_a_118_, v_a_119_);
lean_dec(v_a_119_);
lean_dec_ref(v_a_118_);
lean_dec(v_a_117_);
lean_dec_ref(v_a_116_);
lean_dec_ref(v_x_115_);
return v_res_121_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__4(lean_object* v_msg_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_){
_start:
{
lean_object* v___f_134_; lean_object* v___x_8870__overap_135_; lean_object* v___x_136_; 
v___f_134_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__4___closed__0));
v___x_8870__overap_135_ = lean_panic_fn_borrowed(v___f_134_, v_msg_128_);
lean_inc(v___y_132_);
lean_inc_ref(v___y_131_);
lean_inc(v___y_130_);
lean_inc_ref(v___y_129_);
v___x_136_ = lean_apply_5(v___x_8870__overap_135_, v___y_129_, v___y_130_, v___y_131_, v___y_132_, lean_box(0));
return v___x_136_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__4___boxed(lean_object* v_msg_137_, lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_){
_start:
{
lean_object* v_res_143_; 
v_res_143_ = l_panic___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__4(v_msg_137_, v___y_138_, v___y_139_, v___y_140_, v___y_141_);
lean_dec(v___y_141_);
lean_dec_ref(v___y_140_);
lean_dec(v___y_139_);
lean_dec_ref(v___y_138_);
return v_res_143_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__2___redArg(lean_object* v___x_144_, lean_object* v_reverted_145_, lean_object* v_fst_146_, lean_object* v_n_147_, lean_object* v_j_148_, lean_object* v_a_149_){
_start:
{
lean_object* v_zero_150_; uint8_t v_isZero_151_; 
v_zero_150_ = lean_unsigned_to_nat(0u);
v_isZero_151_ = lean_nat_dec_eq(v_j_148_, v_zero_150_);
if (v_isZero_151_ == 1)
{
lean_dec(v_j_148_);
return v_a_149_;
}
else
{
lean_object* v___x_152_; lean_object* v_n_153_; lean_object* v___x_154_; lean_object* v___x_155_; uint8_t v___x_156_; 
v___x_152_ = lean_unsigned_to_nat(1u);
v_n_153_ = lean_nat_sub(v_j_148_, v___x_152_);
v___x_154_ = lean_nat_sub(v_n_147_, v_j_148_);
lean_dec(v_j_148_);
v___x_155_ = lean_nat_add(v___x_144_, v___x_152_);
v___x_156_ = lean_nat_dec_lt(v___x_154_, v___x_155_);
lean_dec(v___x_155_);
if (v___x_156_ == 0)
{
lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; 
v___x_157_ = lean_array_fget_borrowed(v_reverted_145_, v___x_154_);
v___x_158_ = lean_box(0);
v___x_159_ = lean_nat_sub(v___x_154_, v___x_144_);
lean_dec(v___x_154_);
v___x_160_ = lean_nat_sub(v___x_159_, v___x_152_);
lean_dec(v___x_159_);
v___x_161_ = lean_array_get_borrowed(v___x_158_, v_fst_146_, v___x_160_);
lean_dec(v___x_160_);
lean_inc(v___x_161_);
v___x_162_ = l_Lean_mkFVar(v___x_161_);
lean_inc(v___x_157_);
v___x_163_ = l_Lean_Meta_FVarSubst_insert(v_a_149_, v___x_157_, v___x_162_);
v_j_148_ = v_n_153_;
v_a_149_ = v___x_163_;
goto _start;
}
else
{
lean_dec(v___x_154_);
v_j_148_ = v_n_153_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__2___redArg___boxed(lean_object* v___x_166_, lean_object* v_reverted_167_, lean_object* v_fst_168_, lean_object* v_n_169_, lean_object* v_j_170_, lean_object* v_a_171_){
_start:
{
lean_object* v_res_172_; 
v_res_172_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__2___redArg(v___x_166_, v_reverted_167_, v_fst_168_, v_n_169_, v_j_170_, v_a_171_);
lean_dec(v_n_169_);
lean_dec_ref(v_fst_168_);
lean_dec_ref(v_reverted_167_);
lean_dec(v___x_166_);
return v_res_172_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__5(lean_object* v_mvarId_173_, lean_object* v_as_174_, size_t v_i_175_, size_t v_stop_176_, lean_object* v_b_177_, lean_object* v___y_178_, lean_object* v___y_179_, lean_object* v___y_180_, lean_object* v___y_181_){
_start:
{
uint8_t v___x_183_; 
v___x_183_ = lean_usize_dec_eq(v_i_175_, v_stop_176_);
if (v___x_183_ == 0)
{
lean_object* v_fst_184_; lean_object* v_snd_185_; lean_object* v___x_187_; uint8_t v_isShared_188_; uint8_t v_isSharedCheck_207_; 
v_fst_184_ = lean_ctor_get(v_b_177_, 0);
v_snd_185_ = lean_ctor_get(v_b_177_, 1);
v_isSharedCheck_207_ = !lean_is_exclusive(v_b_177_);
if (v_isSharedCheck_207_ == 0)
{
v___x_187_ = v_b_177_;
v_isShared_188_ = v_isSharedCheck_207_;
goto v_resetjp_186_;
}
else
{
lean_inc(v_snd_185_);
lean_inc(v_fst_184_);
lean_dec(v_b_177_);
v___x_187_ = lean_box(0);
v_isShared_188_ = v_isSharedCheck_207_;
goto v_resetjp_186_;
}
v_resetjp_186_:
{
lean_object* v___x_189_; lean_object* v___x_190_; 
v___x_189_ = lean_array_uget_borrowed(v_as_174_, v_i_175_);
lean_inc(v_mvarId_173_);
v___x_190_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTypeBody(v_mvarId_173_, v_snd_185_, v___x_189_, v___y_178_, v___y_179_, v___y_180_, v___y_181_);
if (lean_obj_tag(v___x_190_) == 0)
{
lean_object* v_a_191_; lean_object* v___x_192_; lean_object* v___x_194_; 
v_a_191_ = lean_ctor_get(v___x_190_, 0);
lean_inc(v_a_191_);
lean_dec_ref_known(v___x_190_, 1);
lean_inc(v___x_189_);
v___x_192_ = l_Lean_Expr_app___override(v_fst_184_, v___x_189_);
if (v_isShared_188_ == 0)
{
lean_ctor_set(v___x_187_, 1, v_a_191_);
lean_ctor_set(v___x_187_, 0, v___x_192_);
v___x_194_ = v___x_187_;
goto v_reusejp_193_;
}
else
{
lean_object* v_reuseFailAlloc_198_; 
v_reuseFailAlloc_198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_198_, 0, v___x_192_);
lean_ctor_set(v_reuseFailAlloc_198_, 1, v_a_191_);
v___x_194_ = v_reuseFailAlloc_198_;
goto v_reusejp_193_;
}
v_reusejp_193_:
{
size_t v___x_195_; size_t v___x_196_; 
v___x_195_ = ((size_t)1ULL);
v___x_196_ = lean_usize_add(v_i_175_, v___x_195_);
v_i_175_ = v___x_196_;
v_b_177_ = v___x_194_;
goto _start;
}
}
else
{
lean_object* v_a_199_; lean_object* v___x_201_; uint8_t v_isShared_202_; uint8_t v_isSharedCheck_206_; 
lean_del_object(v___x_187_);
lean_dec(v_fst_184_);
lean_dec(v_mvarId_173_);
v_a_199_ = lean_ctor_get(v___x_190_, 0);
v_isSharedCheck_206_ = !lean_is_exclusive(v___x_190_);
if (v_isSharedCheck_206_ == 0)
{
v___x_201_ = v___x_190_;
v_isShared_202_ = v_isSharedCheck_206_;
goto v_resetjp_200_;
}
else
{
lean_inc(v_a_199_);
lean_dec(v___x_190_);
v___x_201_ = lean_box(0);
v_isShared_202_ = v_isSharedCheck_206_;
goto v_resetjp_200_;
}
v_resetjp_200_:
{
lean_object* v___x_204_; 
if (v_isShared_202_ == 0)
{
v___x_204_ = v___x_201_;
goto v_reusejp_203_;
}
else
{
lean_object* v_reuseFailAlloc_205_; 
v_reuseFailAlloc_205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_205_, 0, v_a_199_);
v___x_204_ = v_reuseFailAlloc_205_;
goto v_reusejp_203_;
}
v_reusejp_203_:
{
return v___x_204_;
}
}
}
}
}
else
{
lean_object* v___x_208_; 
lean_dec(v_mvarId_173_);
v___x_208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_208_, 0, v_b_177_);
return v___x_208_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__5___boxed(lean_object* v_mvarId_209_, lean_object* v_as_210_, lean_object* v_i_211_, lean_object* v_stop_212_, lean_object* v_b_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_){
_start:
{
size_t v_i_boxed_219_; size_t v_stop_boxed_220_; lean_object* v_res_221_; 
v_i_boxed_219_ = lean_unbox_usize(v_i_211_);
lean_dec(v_i_211_);
v_stop_boxed_220_ = lean_unbox_usize(v_stop_212_);
lean_dec(v_stop_212_);
v_res_221_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__5(v_mvarId_209_, v_as_210_, v_i_boxed_219_, v_stop_boxed_220_, v_b_213_, v___y_214_, v___y_215_, v___y_216_, v___y_217_);
lean_dec(v___y_217_);
lean_dec_ref(v___y_216_);
lean_dec(v___y_215_);
lean_dec_ref(v___y_214_);
lean_dec_ref(v_as_210_);
return v_res_221_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__8_spec__9___redArg(lean_object* v_x_222_, lean_object* v_x_223_, lean_object* v_x_224_, lean_object* v_x_225_){
_start:
{
lean_object* v_ks_226_; lean_object* v_vs_227_; lean_object* v___x_229_; uint8_t v_isShared_230_; uint8_t v_isSharedCheck_251_; 
v_ks_226_ = lean_ctor_get(v_x_222_, 0);
v_vs_227_ = lean_ctor_get(v_x_222_, 1);
v_isSharedCheck_251_ = !lean_is_exclusive(v_x_222_);
if (v_isSharedCheck_251_ == 0)
{
v___x_229_ = v_x_222_;
v_isShared_230_ = v_isSharedCheck_251_;
goto v_resetjp_228_;
}
else
{
lean_inc(v_vs_227_);
lean_inc(v_ks_226_);
lean_dec(v_x_222_);
v___x_229_ = lean_box(0);
v_isShared_230_ = v_isSharedCheck_251_;
goto v_resetjp_228_;
}
v_resetjp_228_:
{
lean_object* v___x_231_; uint8_t v___x_232_; 
v___x_231_ = lean_array_get_size(v_ks_226_);
v___x_232_ = lean_nat_dec_lt(v_x_223_, v___x_231_);
if (v___x_232_ == 0)
{
lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_236_; 
lean_dec(v_x_223_);
v___x_233_ = lean_array_push(v_ks_226_, v_x_224_);
v___x_234_ = lean_array_push(v_vs_227_, v_x_225_);
if (v_isShared_230_ == 0)
{
lean_ctor_set(v___x_229_, 1, v___x_234_);
lean_ctor_set(v___x_229_, 0, v___x_233_);
v___x_236_ = v___x_229_;
goto v_reusejp_235_;
}
else
{
lean_object* v_reuseFailAlloc_237_; 
v_reuseFailAlloc_237_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_237_, 0, v___x_233_);
lean_ctor_set(v_reuseFailAlloc_237_, 1, v___x_234_);
v___x_236_ = v_reuseFailAlloc_237_;
goto v_reusejp_235_;
}
v_reusejp_235_:
{
return v___x_236_;
}
}
else
{
lean_object* v_k_x27_238_; uint8_t v___x_239_; 
v_k_x27_238_ = lean_array_fget_borrowed(v_ks_226_, v_x_223_);
v___x_239_ = l_Lean_instBEqMVarId_beq(v_x_224_, v_k_x27_238_);
if (v___x_239_ == 0)
{
lean_object* v___x_241_; 
if (v_isShared_230_ == 0)
{
v___x_241_ = v___x_229_;
goto v_reusejp_240_;
}
else
{
lean_object* v_reuseFailAlloc_245_; 
v_reuseFailAlloc_245_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_245_, 0, v_ks_226_);
lean_ctor_set(v_reuseFailAlloc_245_, 1, v_vs_227_);
v___x_241_ = v_reuseFailAlloc_245_;
goto v_reusejp_240_;
}
v_reusejp_240_:
{
lean_object* v___x_242_; lean_object* v___x_243_; 
v___x_242_ = lean_unsigned_to_nat(1u);
v___x_243_ = lean_nat_add(v_x_223_, v___x_242_);
lean_dec(v_x_223_);
v_x_222_ = v___x_241_;
v_x_223_ = v___x_243_;
goto _start;
}
}
else
{
lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_249_; 
v___x_246_ = lean_array_fset(v_ks_226_, v_x_223_, v_x_224_);
v___x_247_ = lean_array_fset(v_vs_227_, v_x_223_, v_x_225_);
lean_dec(v_x_223_);
if (v_isShared_230_ == 0)
{
lean_ctor_set(v___x_229_, 1, v___x_247_);
lean_ctor_set(v___x_229_, 0, v___x_246_);
v___x_249_ = v___x_229_;
goto v_reusejp_248_;
}
else
{
lean_object* v_reuseFailAlloc_250_; 
v_reuseFailAlloc_250_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_250_, 0, v___x_246_);
lean_ctor_set(v_reuseFailAlloc_250_, 1, v___x_247_);
v___x_249_ = v_reuseFailAlloc_250_;
goto v_reusejp_248_;
}
v_reusejp_248_:
{
return v___x_249_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__8___redArg(lean_object* v_n_252_, lean_object* v_k_253_, lean_object* v_v_254_){
_start:
{
lean_object* v___x_255_; lean_object* v___x_256_; 
v___x_255_ = lean_unsigned_to_nat(0u);
v___x_256_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__8_spec__9___redArg(v_n_252_, v___x_255_, v_k_253_, v_v_254_);
return v___x_256_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_257_; 
v___x_257_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_257_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2___redArg(lean_object* v_x_258_, size_t v_x_259_, size_t v_x_260_, lean_object* v_x_261_, lean_object* v_x_262_){
_start:
{
if (lean_obj_tag(v_x_258_) == 0)
{
lean_object* v_es_263_; size_t v___x_264_; size_t v___x_265_; lean_object* v_j_266_; lean_object* v___x_267_; uint8_t v___x_268_; 
v_es_263_ = lean_ctor_get(v_x_258_, 0);
v___x_264_ = ((size_t)31ULL);
v___x_265_ = lean_usize_land(v_x_259_, v___x_264_);
v_j_266_ = lean_usize_to_nat(v___x_265_);
v___x_267_ = lean_array_get_size(v_es_263_);
v___x_268_ = lean_nat_dec_lt(v_j_266_, v___x_267_);
if (v___x_268_ == 0)
{
lean_dec(v_j_266_);
lean_dec(v_x_262_);
lean_dec(v_x_261_);
return v_x_258_;
}
else
{
lean_object* v___x_270_; uint8_t v_isShared_271_; uint8_t v_isSharedCheck_307_; 
lean_inc_ref(v_es_263_);
v_isSharedCheck_307_ = !lean_is_exclusive(v_x_258_);
if (v_isSharedCheck_307_ == 0)
{
lean_object* v_unused_308_; 
v_unused_308_ = lean_ctor_get(v_x_258_, 0);
lean_dec(v_unused_308_);
v___x_270_ = v_x_258_;
v_isShared_271_ = v_isSharedCheck_307_;
goto v_resetjp_269_;
}
else
{
lean_dec(v_x_258_);
v___x_270_ = lean_box(0);
v_isShared_271_ = v_isSharedCheck_307_;
goto v_resetjp_269_;
}
v_resetjp_269_:
{
lean_object* v_v_272_; lean_object* v___x_273_; lean_object* v_xs_x27_274_; lean_object* v___y_276_; 
v_v_272_ = lean_array_fget(v_es_263_, v_j_266_);
v___x_273_ = lean_box(0);
v_xs_x27_274_ = lean_array_fset(v_es_263_, v_j_266_, v___x_273_);
switch(lean_obj_tag(v_v_272_))
{
case 0:
{
lean_object* v_key_281_; lean_object* v_val_282_; lean_object* v___x_284_; uint8_t v_isShared_285_; uint8_t v_isSharedCheck_292_; 
v_key_281_ = lean_ctor_get(v_v_272_, 0);
v_val_282_ = lean_ctor_get(v_v_272_, 1);
v_isSharedCheck_292_ = !lean_is_exclusive(v_v_272_);
if (v_isSharedCheck_292_ == 0)
{
v___x_284_ = v_v_272_;
v_isShared_285_ = v_isSharedCheck_292_;
goto v_resetjp_283_;
}
else
{
lean_inc(v_val_282_);
lean_inc(v_key_281_);
lean_dec(v_v_272_);
v___x_284_ = lean_box(0);
v_isShared_285_ = v_isSharedCheck_292_;
goto v_resetjp_283_;
}
v_resetjp_283_:
{
uint8_t v___x_286_; 
v___x_286_ = l_Lean_instBEqMVarId_beq(v_x_261_, v_key_281_);
if (v___x_286_ == 0)
{
lean_object* v___x_287_; lean_object* v___x_288_; 
lean_del_object(v___x_284_);
v___x_287_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_281_, v_val_282_, v_x_261_, v_x_262_);
v___x_288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_288_, 0, v___x_287_);
v___y_276_ = v___x_288_;
goto v___jp_275_;
}
else
{
lean_object* v___x_290_; 
lean_dec(v_val_282_);
lean_dec(v_key_281_);
if (v_isShared_285_ == 0)
{
lean_ctor_set(v___x_284_, 1, v_x_262_);
lean_ctor_set(v___x_284_, 0, v_x_261_);
v___x_290_ = v___x_284_;
goto v_reusejp_289_;
}
else
{
lean_object* v_reuseFailAlloc_291_; 
v_reuseFailAlloc_291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_291_, 0, v_x_261_);
lean_ctor_set(v_reuseFailAlloc_291_, 1, v_x_262_);
v___x_290_ = v_reuseFailAlloc_291_;
goto v_reusejp_289_;
}
v_reusejp_289_:
{
v___y_276_ = v___x_290_;
goto v___jp_275_;
}
}
}
}
case 1:
{
lean_object* v_node_293_; lean_object* v___x_295_; uint8_t v_isShared_296_; uint8_t v_isSharedCheck_305_; 
v_node_293_ = lean_ctor_get(v_v_272_, 0);
v_isSharedCheck_305_ = !lean_is_exclusive(v_v_272_);
if (v_isSharedCheck_305_ == 0)
{
v___x_295_ = v_v_272_;
v_isShared_296_ = v_isSharedCheck_305_;
goto v_resetjp_294_;
}
else
{
lean_inc(v_node_293_);
lean_dec(v_v_272_);
v___x_295_ = lean_box(0);
v_isShared_296_ = v_isSharedCheck_305_;
goto v_resetjp_294_;
}
v_resetjp_294_:
{
size_t v___x_297_; size_t v___x_298_; size_t v___x_299_; size_t v___x_300_; lean_object* v___x_301_; lean_object* v___x_303_; 
v___x_297_ = ((size_t)5ULL);
v___x_298_ = lean_usize_shift_right(v_x_259_, v___x_297_);
v___x_299_ = ((size_t)1ULL);
v___x_300_ = lean_usize_add(v_x_260_, v___x_299_);
v___x_301_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2___redArg(v_node_293_, v___x_298_, v___x_300_, v_x_261_, v_x_262_);
if (v_isShared_296_ == 0)
{
lean_ctor_set(v___x_295_, 0, v___x_301_);
v___x_303_ = v___x_295_;
goto v_reusejp_302_;
}
else
{
lean_object* v_reuseFailAlloc_304_; 
v_reuseFailAlloc_304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_304_, 0, v___x_301_);
v___x_303_ = v_reuseFailAlloc_304_;
goto v_reusejp_302_;
}
v_reusejp_302_:
{
v___y_276_ = v___x_303_;
goto v___jp_275_;
}
}
}
default: 
{
lean_object* v___x_306_; 
v___x_306_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_306_, 0, v_x_261_);
lean_ctor_set(v___x_306_, 1, v_x_262_);
v___y_276_ = v___x_306_;
goto v___jp_275_;
}
}
v___jp_275_:
{
lean_object* v___x_277_; lean_object* v___x_279_; 
v___x_277_ = lean_array_fset(v_xs_x27_274_, v_j_266_, v___y_276_);
lean_dec(v_j_266_);
if (v_isShared_271_ == 0)
{
lean_ctor_set(v___x_270_, 0, v___x_277_);
v___x_279_ = v___x_270_;
goto v_reusejp_278_;
}
else
{
lean_object* v_reuseFailAlloc_280_; 
v_reuseFailAlloc_280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_280_, 0, v___x_277_);
v___x_279_ = v_reuseFailAlloc_280_;
goto v_reusejp_278_;
}
v_reusejp_278_:
{
return v___x_279_;
}
}
}
}
}
else
{
lean_object* v_ks_309_; lean_object* v_vs_310_; lean_object* v___x_312_; uint8_t v_isShared_313_; uint8_t v_isSharedCheck_330_; 
v_ks_309_ = lean_ctor_get(v_x_258_, 0);
v_vs_310_ = lean_ctor_get(v_x_258_, 1);
v_isSharedCheck_330_ = !lean_is_exclusive(v_x_258_);
if (v_isSharedCheck_330_ == 0)
{
v___x_312_ = v_x_258_;
v_isShared_313_ = v_isSharedCheck_330_;
goto v_resetjp_311_;
}
else
{
lean_inc(v_vs_310_);
lean_inc(v_ks_309_);
lean_dec(v_x_258_);
v___x_312_ = lean_box(0);
v_isShared_313_ = v_isSharedCheck_330_;
goto v_resetjp_311_;
}
v_resetjp_311_:
{
lean_object* v___x_315_; 
if (v_isShared_313_ == 0)
{
v___x_315_ = v___x_312_;
goto v_reusejp_314_;
}
else
{
lean_object* v_reuseFailAlloc_329_; 
v_reuseFailAlloc_329_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_329_, 0, v_ks_309_);
lean_ctor_set(v_reuseFailAlloc_329_, 1, v_vs_310_);
v___x_315_ = v_reuseFailAlloc_329_;
goto v_reusejp_314_;
}
v_reusejp_314_:
{
lean_object* v_newNode_316_; uint8_t v___y_318_; size_t v___x_324_; uint8_t v___x_325_; 
v_newNode_316_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__8___redArg(v___x_315_, v_x_261_, v_x_262_);
v___x_324_ = ((size_t)7ULL);
v___x_325_ = lean_usize_dec_le(v___x_324_, v_x_260_);
if (v___x_325_ == 0)
{
lean_object* v___x_326_; lean_object* v___x_327_; uint8_t v___x_328_; 
v___x_326_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_316_);
v___x_327_ = lean_unsigned_to_nat(4u);
v___x_328_ = lean_nat_dec_lt(v___x_326_, v___x_327_);
lean_dec(v___x_326_);
v___y_318_ = v___x_328_;
goto v___jp_317_;
}
else
{
v___y_318_ = v___x_325_;
goto v___jp_317_;
}
v___jp_317_:
{
if (v___y_318_ == 0)
{
lean_object* v_ks_319_; lean_object* v_vs_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; 
v_ks_319_ = lean_ctor_get(v_newNode_316_, 0);
lean_inc_ref(v_ks_319_);
v_vs_320_ = lean_ctor_get(v_newNode_316_, 1);
lean_inc_ref(v_vs_320_);
lean_dec_ref(v_newNode_316_);
v___x_321_ = lean_unsigned_to_nat(0u);
v___x_322_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2___redArg___closed__0);
v___x_323_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__9___redArg(v_x_260_, v_ks_319_, v_vs_320_, v___x_321_, v___x_322_);
lean_dec_ref(v_vs_320_);
lean_dec_ref(v_ks_319_);
return v___x_323_;
}
else
{
return v_newNode_316_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__9___redArg(size_t v_depth_331_, lean_object* v_keys_332_, lean_object* v_vals_333_, lean_object* v_i_334_, lean_object* v_entries_335_){
_start:
{
lean_object* v___x_336_; uint8_t v___x_337_; 
v___x_336_ = lean_array_get_size(v_keys_332_);
v___x_337_ = lean_nat_dec_lt(v_i_334_, v___x_336_);
if (v___x_337_ == 0)
{
lean_dec(v_i_334_);
return v_entries_335_;
}
else
{
lean_object* v_k_338_; lean_object* v_v_339_; uint64_t v___x_340_; size_t v_h_341_; size_t v___x_342_; lean_object* v___x_343_; size_t v___x_344_; size_t v___x_345_; size_t v___x_346_; size_t v_h_347_; lean_object* v___x_348_; lean_object* v___x_349_; 
v_k_338_ = lean_array_fget_borrowed(v_keys_332_, v_i_334_);
v_v_339_ = lean_array_fget_borrowed(v_vals_333_, v_i_334_);
v___x_340_ = l_Lean_instHashableMVarId_hash(v_k_338_);
v_h_341_ = lean_uint64_to_usize(v___x_340_);
v___x_342_ = ((size_t)5ULL);
v___x_343_ = lean_unsigned_to_nat(1u);
v___x_344_ = ((size_t)1ULL);
v___x_345_ = lean_usize_sub(v_depth_331_, v___x_344_);
v___x_346_ = lean_usize_mul(v___x_342_, v___x_345_);
v_h_347_ = lean_usize_shift_right(v_h_341_, v___x_346_);
v___x_348_ = lean_nat_add(v_i_334_, v___x_343_);
lean_dec(v_i_334_);
lean_inc(v_v_339_);
lean_inc(v_k_338_);
v___x_349_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2___redArg(v_entries_335_, v_h_347_, v_depth_331_, v_k_338_, v_v_339_);
v_i_334_ = v___x_348_;
v_entries_335_ = v___x_349_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__9___redArg___boxed(lean_object* v_depth_351_, lean_object* v_keys_352_, lean_object* v_vals_353_, lean_object* v_i_354_, lean_object* v_entries_355_){
_start:
{
size_t v_depth_boxed_356_; lean_object* v_res_357_; 
v_depth_boxed_356_ = lean_unbox_usize(v_depth_351_);
lean_dec(v_depth_351_);
v_res_357_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__9___redArg(v_depth_boxed_356_, v_keys_352_, v_vals_353_, v_i_354_, v_entries_355_);
lean_dec_ref(v_vals_353_);
lean_dec_ref(v_keys_352_);
return v_res_357_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_x_358_, lean_object* v_x_359_, lean_object* v_x_360_, lean_object* v_x_361_, lean_object* v_x_362_){
_start:
{
size_t v_x_10127__boxed_363_; size_t v_x_10128__boxed_364_; lean_object* v_res_365_; 
v_x_10127__boxed_363_ = lean_unbox_usize(v_x_359_);
lean_dec(v_x_359_);
v_x_10128__boxed_364_ = lean_unbox_usize(v_x_360_);
lean_dec(v_x_360_);
v_res_365_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2___redArg(v_x_358_, v_x_10127__boxed_363_, v_x_10128__boxed_364_, v_x_361_, v_x_362_);
return v_res_365_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0___redArg(lean_object* v_x_366_, lean_object* v_x_367_, lean_object* v_x_368_){
_start:
{
uint64_t v___x_369_; size_t v___x_370_; size_t v___x_371_; lean_object* v___x_372_; 
v___x_369_ = l_Lean_instHashableMVarId_hash(v_x_367_);
v___x_370_ = lean_uint64_to_usize(v___x_369_);
v___x_371_ = ((size_t)1ULL);
v___x_372_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2___redArg(v_x_366_, v___x_370_, v___x_371_, v_x_367_, v_x_368_);
return v___x_372_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0___redArg(lean_object* v_mvarId_373_, lean_object* v_val_374_, lean_object* v___y_375_){
_start:
{
lean_object* v___x_377_; lean_object* v_mctx_378_; lean_object* v_cache_379_; lean_object* v_zetaDeltaFVarIds_380_; lean_object* v_postponed_381_; lean_object* v_diag_382_; lean_object* v___x_384_; uint8_t v_isShared_385_; uint8_t v_isSharedCheck_411_; 
v___x_377_ = lean_st_ref_take(v___y_375_);
v_mctx_378_ = lean_ctor_get(v___x_377_, 0);
v_cache_379_ = lean_ctor_get(v___x_377_, 1);
v_zetaDeltaFVarIds_380_ = lean_ctor_get(v___x_377_, 2);
v_postponed_381_ = lean_ctor_get(v___x_377_, 3);
v_diag_382_ = lean_ctor_get(v___x_377_, 4);
v_isSharedCheck_411_ = !lean_is_exclusive(v___x_377_);
if (v_isSharedCheck_411_ == 0)
{
v___x_384_ = v___x_377_;
v_isShared_385_ = v_isSharedCheck_411_;
goto v_resetjp_383_;
}
else
{
lean_inc(v_diag_382_);
lean_inc(v_postponed_381_);
lean_inc(v_zetaDeltaFVarIds_380_);
lean_inc(v_cache_379_);
lean_inc(v_mctx_378_);
lean_dec(v___x_377_);
v___x_384_ = lean_box(0);
v_isShared_385_ = v_isSharedCheck_411_;
goto v_resetjp_383_;
}
v_resetjp_383_:
{
lean_object* v_depth_386_; lean_object* v_levelAssignDepth_387_; lean_object* v_lmvarCounter_388_; lean_object* v_mvarCounter_389_; lean_object* v_lDecls_390_; lean_object* v_decls_391_; lean_object* v_userNames_392_; lean_object* v_lAssignment_393_; lean_object* v_eAssignment_394_; lean_object* v_dAssignment_395_; lean_object* v_instanceTypedMVars_396_; lean_object* v___x_398_; uint8_t v_isShared_399_; uint8_t v_isSharedCheck_410_; 
v_depth_386_ = lean_ctor_get(v_mctx_378_, 0);
v_levelAssignDepth_387_ = lean_ctor_get(v_mctx_378_, 1);
v_lmvarCounter_388_ = lean_ctor_get(v_mctx_378_, 2);
v_mvarCounter_389_ = lean_ctor_get(v_mctx_378_, 3);
v_lDecls_390_ = lean_ctor_get(v_mctx_378_, 4);
v_decls_391_ = lean_ctor_get(v_mctx_378_, 5);
v_userNames_392_ = lean_ctor_get(v_mctx_378_, 6);
v_lAssignment_393_ = lean_ctor_get(v_mctx_378_, 7);
v_eAssignment_394_ = lean_ctor_get(v_mctx_378_, 8);
v_dAssignment_395_ = lean_ctor_get(v_mctx_378_, 9);
v_instanceTypedMVars_396_ = lean_ctor_get(v_mctx_378_, 10);
v_isSharedCheck_410_ = !lean_is_exclusive(v_mctx_378_);
if (v_isSharedCheck_410_ == 0)
{
v___x_398_ = v_mctx_378_;
v_isShared_399_ = v_isSharedCheck_410_;
goto v_resetjp_397_;
}
else
{
lean_inc(v_instanceTypedMVars_396_);
lean_inc(v_dAssignment_395_);
lean_inc(v_eAssignment_394_);
lean_inc(v_lAssignment_393_);
lean_inc(v_userNames_392_);
lean_inc(v_decls_391_);
lean_inc(v_lDecls_390_);
lean_inc(v_mvarCounter_389_);
lean_inc(v_lmvarCounter_388_);
lean_inc(v_levelAssignDepth_387_);
lean_inc(v_depth_386_);
lean_dec(v_mctx_378_);
v___x_398_ = lean_box(0);
v_isShared_399_ = v_isSharedCheck_410_;
goto v_resetjp_397_;
}
v_resetjp_397_:
{
lean_object* v___x_400_; lean_object* v___x_402_; 
v___x_400_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0___redArg(v_eAssignment_394_, v_mvarId_373_, v_val_374_);
if (v_isShared_399_ == 0)
{
lean_ctor_set(v___x_398_, 8, v___x_400_);
v___x_402_ = v___x_398_;
goto v_reusejp_401_;
}
else
{
lean_object* v_reuseFailAlloc_409_; 
v_reuseFailAlloc_409_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_409_, 0, v_depth_386_);
lean_ctor_set(v_reuseFailAlloc_409_, 1, v_levelAssignDepth_387_);
lean_ctor_set(v_reuseFailAlloc_409_, 2, v_lmvarCounter_388_);
lean_ctor_set(v_reuseFailAlloc_409_, 3, v_mvarCounter_389_);
lean_ctor_set(v_reuseFailAlloc_409_, 4, v_lDecls_390_);
lean_ctor_set(v_reuseFailAlloc_409_, 5, v_decls_391_);
lean_ctor_set(v_reuseFailAlloc_409_, 6, v_userNames_392_);
lean_ctor_set(v_reuseFailAlloc_409_, 7, v_lAssignment_393_);
lean_ctor_set(v_reuseFailAlloc_409_, 8, v___x_400_);
lean_ctor_set(v_reuseFailAlloc_409_, 9, v_dAssignment_395_);
lean_ctor_set(v_reuseFailAlloc_409_, 10, v_instanceTypedMVars_396_);
v___x_402_ = v_reuseFailAlloc_409_;
goto v_reusejp_401_;
}
v_reusejp_401_:
{
lean_object* v___x_404_; 
if (v_isShared_385_ == 0)
{
lean_ctor_set(v___x_384_, 0, v___x_402_);
v___x_404_ = v___x_384_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_408_; 
v_reuseFailAlloc_408_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_408_, 0, v___x_402_);
lean_ctor_set(v_reuseFailAlloc_408_, 1, v_cache_379_);
lean_ctor_set(v_reuseFailAlloc_408_, 2, v_zetaDeltaFVarIds_380_);
lean_ctor_set(v_reuseFailAlloc_408_, 3, v_postponed_381_);
lean_ctor_set(v_reuseFailAlloc_408_, 4, v_diag_382_);
v___x_404_ = v_reuseFailAlloc_408_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; 
v___x_405_ = lean_st_ref_put(v___y_375_, v___x_404_);
v___x_406_ = lean_box(0);
v___x_407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_407_, 0, v___x_406_);
return v___x_407_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0___redArg___boxed(lean_object* v_mvarId_412_, lean_object* v_val_413_, lean_object* v___y_414_, lean_object* v___y_415_){
_start:
{
lean_object* v_res_416_; 
v_res_416_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0___redArg(v_mvarId_412_, v_val_413_, v___y_414_);
lean_dec(v___y_414_);
return v_res_416_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__3(size_t v_sz_417_, size_t v_i_418_, lean_object* v_bs_419_){
_start:
{
uint8_t v___x_420_; 
v___x_420_ = lean_usize_dec_lt(v_i_418_, v_sz_417_);
if (v___x_420_ == 0)
{
return v_bs_419_;
}
else
{
lean_object* v_v_421_; lean_object* v___x_422_; lean_object* v_bs_x27_423_; lean_object* v___x_424_; size_t v___x_425_; size_t v___x_426_; lean_object* v___x_427_; 
v_v_421_ = lean_array_uget(v_bs_419_, v_i_418_);
v___x_422_ = lean_unsigned_to_nat(0u);
v_bs_x27_423_ = lean_array_uset(v_bs_419_, v_i_418_, v___x_422_);
v___x_424_ = l_Lean_mkFVar(v_v_421_);
v___x_425_ = ((size_t)1ULL);
v___x_426_ = lean_usize_add(v_i_418_, v___x_425_);
v___x_427_ = lean_array_uset(v_bs_x27_423_, v_i_418_, v___x_424_);
v_i_418_ = v___x_426_;
v_bs_419_ = v___x_427_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__3___boxed(lean_object* v_sz_429_, lean_object* v_i_430_, lean_object* v_bs_431_){
_start:
{
size_t v_sz_boxed_432_; size_t v_i_boxed_433_; lean_object* v_res_434_; 
v_sz_boxed_432_ = lean_unbox_usize(v_sz_429_);
lean_dec(v_sz_429_);
v_i_boxed_433_ = lean_unbox_usize(v_i_430_);
lean_dec(v_i_430_);
v_res_434_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__3(v_sz_boxed_432_, v_i_boxed_433_, v_bs_431_);
return v_res_434_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1_spec__2(lean_object* v_msgData_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_){
_start:
{
lean_object* v___x_441_; lean_object* v_env_442_; lean_object* v___x_443_; lean_object* v_mctx_444_; lean_object* v_lctx_445_; lean_object* v_options_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; 
v___x_441_ = lean_st_ref_get(v___y_439_);
v_env_442_ = lean_ctor_get(v___x_441_, 0);
lean_inc_ref(v_env_442_);
lean_dec(v___x_441_);
v___x_443_ = lean_st_ref_get(v___y_437_);
v_mctx_444_ = lean_ctor_get(v___x_443_, 0);
lean_inc_ref(v_mctx_444_);
lean_dec(v___x_443_);
v_lctx_445_ = lean_ctor_get(v___y_436_, 2);
v_options_446_ = lean_ctor_get(v___y_438_, 2);
lean_inc_ref(v_options_446_);
lean_inc_ref(v_lctx_445_);
v___x_447_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_447_, 0, v_env_442_);
lean_ctor_set(v___x_447_, 1, v_mctx_444_);
lean_ctor_set(v___x_447_, 2, v_lctx_445_);
lean_ctor_set(v___x_447_, 3, v_options_446_);
v___x_448_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_448_, 0, v___x_447_);
lean_ctor_set(v___x_448_, 1, v_msgData_435_);
v___x_449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_449_, 0, v___x_448_);
return v___x_449_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1_spec__2___boxed(lean_object* v_msgData_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_){
_start:
{
lean_object* v_res_456_; 
v_res_456_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1_spec__2(v_msgData_450_, v___y_451_, v___y_452_, v___y_453_, v___y_454_);
lean_dec(v___y_454_);
lean_dec_ref(v___y_453_);
lean_dec(v___y_452_);
lean_dec_ref(v___y_451_);
return v_res_456_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1___closed__0(void){
_start:
{
lean_object* v___x_457_; double v___x_458_; 
v___x_457_ = lean_unsigned_to_nat(0u);
v___x_458_ = lean_float_of_nat(v___x_457_);
return v___x_458_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1(lean_object* v_cls_462_, lean_object* v_msg_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_){
_start:
{
lean_object* v_ref_469_; lean_object* v___x_470_; lean_object* v_a_471_; lean_object* v___x_473_; uint8_t v_isShared_474_; uint8_t v_isSharedCheck_515_; 
v_ref_469_ = lean_ctor_get(v___y_466_, 5);
v___x_470_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1_spec__2(v_msg_463_, v___y_464_, v___y_465_, v___y_466_, v___y_467_);
v_a_471_ = lean_ctor_get(v___x_470_, 0);
v_isSharedCheck_515_ = !lean_is_exclusive(v___x_470_);
if (v_isSharedCheck_515_ == 0)
{
v___x_473_ = v___x_470_;
v_isShared_474_ = v_isSharedCheck_515_;
goto v_resetjp_472_;
}
else
{
lean_inc(v_a_471_);
lean_dec(v___x_470_);
v___x_473_ = lean_box(0);
v_isShared_474_ = v_isSharedCheck_515_;
goto v_resetjp_472_;
}
v_resetjp_472_:
{
lean_object* v___x_475_; lean_object* v_traceState_476_; lean_object* v_env_477_; lean_object* v_nextMacroScope_478_; lean_object* v_ngen_479_; lean_object* v_auxDeclNGen_480_; lean_object* v_cache_481_; lean_object* v_messages_482_; lean_object* v_infoState_483_; lean_object* v_snapshotTasks_484_; lean_object* v___x_486_; uint8_t v_isShared_487_; uint8_t v_isSharedCheck_514_; 
v___x_475_ = lean_st_ref_take(v___y_467_);
v_traceState_476_ = lean_ctor_get(v___x_475_, 4);
v_env_477_ = lean_ctor_get(v___x_475_, 0);
v_nextMacroScope_478_ = lean_ctor_get(v___x_475_, 1);
v_ngen_479_ = lean_ctor_get(v___x_475_, 2);
v_auxDeclNGen_480_ = lean_ctor_get(v___x_475_, 3);
v_cache_481_ = lean_ctor_get(v___x_475_, 5);
v_messages_482_ = lean_ctor_get(v___x_475_, 6);
v_infoState_483_ = lean_ctor_get(v___x_475_, 7);
v_snapshotTasks_484_ = lean_ctor_get(v___x_475_, 8);
v_isSharedCheck_514_ = !lean_is_exclusive(v___x_475_);
if (v_isSharedCheck_514_ == 0)
{
v___x_486_ = v___x_475_;
v_isShared_487_ = v_isSharedCheck_514_;
goto v_resetjp_485_;
}
else
{
lean_inc(v_snapshotTasks_484_);
lean_inc(v_infoState_483_);
lean_inc(v_messages_482_);
lean_inc(v_cache_481_);
lean_inc(v_traceState_476_);
lean_inc(v_auxDeclNGen_480_);
lean_inc(v_ngen_479_);
lean_inc(v_nextMacroScope_478_);
lean_inc(v_env_477_);
lean_dec(v___x_475_);
v___x_486_ = lean_box(0);
v_isShared_487_ = v_isSharedCheck_514_;
goto v_resetjp_485_;
}
v_resetjp_485_:
{
uint64_t v_tid_488_; lean_object* v_traces_489_; lean_object* v___x_491_; uint8_t v_isShared_492_; uint8_t v_isSharedCheck_513_; 
v_tid_488_ = lean_ctor_get_uint64(v_traceState_476_, sizeof(void*)*1);
v_traces_489_ = lean_ctor_get(v_traceState_476_, 0);
v_isSharedCheck_513_ = !lean_is_exclusive(v_traceState_476_);
if (v_isSharedCheck_513_ == 0)
{
v___x_491_ = v_traceState_476_;
v_isShared_492_ = v_isSharedCheck_513_;
goto v_resetjp_490_;
}
else
{
lean_inc(v_traces_489_);
lean_dec(v_traceState_476_);
v___x_491_ = lean_box(0);
v_isShared_492_ = v_isSharedCheck_513_;
goto v_resetjp_490_;
}
v_resetjp_490_:
{
lean_object* v___x_493_; double v___x_494_; uint8_t v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_503_; 
v___x_493_ = lean_box(0);
v___x_494_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1___closed__0);
v___x_495_ = 0;
v___x_496_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1___closed__1));
v___x_497_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_497_, 0, v_cls_462_);
lean_ctor_set(v___x_497_, 1, v___x_493_);
lean_ctor_set(v___x_497_, 2, v___x_496_);
lean_ctor_set_float(v___x_497_, sizeof(void*)*3, v___x_494_);
lean_ctor_set_float(v___x_497_, sizeof(void*)*3 + 8, v___x_494_);
lean_ctor_set_uint8(v___x_497_, sizeof(void*)*3 + 16, v___x_495_);
v___x_498_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1___closed__2));
v___x_499_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_499_, 0, v___x_497_);
lean_ctor_set(v___x_499_, 1, v_a_471_);
lean_ctor_set(v___x_499_, 2, v___x_498_);
lean_inc(v_ref_469_);
v___x_500_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_500_, 0, v_ref_469_);
lean_ctor_set(v___x_500_, 1, v___x_499_);
v___x_501_ = l_Lean_PersistentArray_push___redArg(v_traces_489_, v___x_500_);
if (v_isShared_492_ == 0)
{
lean_ctor_set(v___x_491_, 0, v___x_501_);
v___x_503_ = v___x_491_;
goto v_reusejp_502_;
}
else
{
lean_object* v_reuseFailAlloc_512_; 
v_reuseFailAlloc_512_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_512_, 0, v___x_501_);
lean_ctor_set_uint64(v_reuseFailAlloc_512_, sizeof(void*)*1, v_tid_488_);
v___x_503_ = v_reuseFailAlloc_512_;
goto v_reusejp_502_;
}
v_reusejp_502_:
{
lean_object* v___x_505_; 
if (v_isShared_487_ == 0)
{
lean_ctor_set(v___x_486_, 4, v___x_503_);
v___x_505_ = v___x_486_;
goto v_reusejp_504_;
}
else
{
lean_object* v_reuseFailAlloc_511_; 
v_reuseFailAlloc_511_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_511_, 0, v_env_477_);
lean_ctor_set(v_reuseFailAlloc_511_, 1, v_nextMacroScope_478_);
lean_ctor_set(v_reuseFailAlloc_511_, 2, v_ngen_479_);
lean_ctor_set(v_reuseFailAlloc_511_, 3, v_auxDeclNGen_480_);
lean_ctor_set(v_reuseFailAlloc_511_, 4, v___x_503_);
lean_ctor_set(v_reuseFailAlloc_511_, 5, v_cache_481_);
lean_ctor_set(v_reuseFailAlloc_511_, 6, v_messages_482_);
lean_ctor_set(v_reuseFailAlloc_511_, 7, v_infoState_483_);
lean_ctor_set(v_reuseFailAlloc_511_, 8, v_snapshotTasks_484_);
v___x_505_ = v_reuseFailAlloc_511_;
goto v_reusejp_504_;
}
v_reusejp_504_:
{
lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_509_; 
v___x_506_ = lean_st_ref_put(v___y_467_, v___x_505_);
v___x_507_ = lean_box(0);
if (v_isShared_474_ == 0)
{
lean_ctor_set(v___x_473_, 0, v___x_507_);
v___x_509_ = v___x_473_;
goto v_reusejp_508_;
}
else
{
lean_object* v_reuseFailAlloc_510_; 
v_reuseFailAlloc_510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_510_, 0, v___x_507_);
v___x_509_ = v_reuseFailAlloc_510_;
goto v_reusejp_508_;
}
v_reusejp_508_:
{
return v___x_509_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1___boxed(lean_object* v_cls_516_, lean_object* v_msg_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_){
_start:
{
lean_object* v_res_523_; 
v_res_523_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1(v_cls_516_, v_msg_517_, v___y_518_, v___y_519_, v___y_520_, v___y_521_);
lean_dec(v___y_521_);
lean_dec_ref(v___y_520_);
lean_dec(v___y_519_);
lean_dec_ref(v___y_518_);
return v_res_523_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5(void){
_start:
{
lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; 
v___x_533_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__2));
v___x_534_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__4));
v___x_535_ = l_Lean_Name_append(v___x_534_, v___x_533_);
return v___x_535_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__7(void){
_start:
{
lean_object* v___x_537_; lean_object* v___x_538_; 
v___x_537_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__6));
v___x_538_ = l_Lean_stringToMessageData(v___x_537_);
return v___x_538_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__9(void){
_start:
{
lean_object* v___x_540_; lean_object* v___x_541_; 
v___x_540_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__8));
v___x_541_ = l_Lean_stringToMessageData(v___x_540_);
return v___x_541_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__11(void){
_start:
{
lean_object* v___x_543_; lean_object* v___x_544_; 
v___x_543_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__10));
v___x_544_ = l_Lean_stringToMessageData(v___x_543_);
return v___x_544_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__15(void){
_start:
{
lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; 
v___x_548_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__14));
v___x_549_ = lean_unsigned_to_nat(15u);
v___x_550_ = lean_unsigned_to_nat(120u);
v___x_551_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__13));
v___x_552_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__12));
v___x_553_ = l_mkPanicMessageWithDecl(v___x_552_, v___x_551_, v___x_550_, v___x_549_, v___x_548_);
return v___x_553_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop(lean_object* v_mvarId_554_, lean_object* v_givenNames_555_, lean_object* v_recursorInfo_556_, lean_object* v_reverted_557_, lean_object* v_major_558_, lean_object* v_indices_559_, lean_object* v_baseSubst_560_, lean_object* v_initialArity_561_, lean_object* v_numMinors_562_, lean_object* v_pos_563_, lean_object* v_minorIdx_564_, lean_object* v_recursor_565_, lean_object* v_recursorType_566_, uint8_t v_consumedMajor_567_, lean_object* v_subgoals_568_, lean_object* v_a_569_, lean_object* v_a_570_, lean_object* v_a_571_, lean_object* v_a_572_){
_start:
{
lean_object* v___y_575_; lean_object* v___y_576_; lean_object* v___y_577_; lean_object* v___y_578_; lean_object* v___y_631_; lean_object* v___y_632_; lean_object* v___y_633_; uint8_t v___y_634_; lean_object* v___y_635_; lean_object* v___y_636_; uint8_t v___y_637_; lean_object* v___y_638_; lean_object* v___y_639_; lean_object* v___y_640_; lean_object* v___y_641_; lean_object* v___y_642_; lean_object* v___y_643_; lean_object* v___y_644_; lean_object* v___y_645_; uint8_t v___y_646_; lean_object* v___y_682_; lean_object* v___y_683_; lean_object* v___y_684_; uint8_t v___y_685_; lean_object* v___y_686_; lean_object* v___y_687_; uint8_t v___y_688_; lean_object* v___y_689_; lean_object* v___y_690_; lean_object* v___y_691_; lean_object* v___y_692_; lean_object* v___y_693_; lean_object* v___y_694_; lean_object* v___y_695_; lean_object* v___y_696_; uint8_t v___y_714_; lean_object* v___y_715_; lean_object* v_fst_716_; lean_object* v_snd_717_; uint8_t v___y_734_; lean_object* v___y_735_; lean_object* v___y_736_; lean_object* v___x_748_; 
v___x_748_ = l_Lean_Meta_whnfForall(v_recursorType_566_, v_a_569_, v_a_570_, v_a_571_, v_a_572_);
if (lean_obj_tag(v___x_748_) == 0)
{
lean_object* v_a_749_; lean_object* v___y_751_; lean_object* v___y_752_; lean_object* v___y_753_; uint8_t v___y_754_; lean_object* v___y_755_; lean_object* v___y_756_; uint8_t v___y_757_; lean_object* v___y_758_; lean_object* v___y_759_; lean_object* v___y_760_; lean_object* v___y_761_; lean_object* v___y_762_; lean_object* v___y_763_; lean_object* v___y_764_; lean_object* v___y_806_; lean_object* v___y_807_; uint8_t v___y_808_; uint8_t v___y_809_; lean_object* v___y_810_; lean_object* v___y_811_; lean_object* v___y_812_; lean_object* v___y_813_; lean_object* v___y_814_; lean_object* v___y_815_; lean_object* v___y_827_; lean_object* v___y_828_; lean_object* v___y_829_; uint8_t v___y_830_; lean_object* v___y_831_; lean_object* v___y_832_; lean_object* v___y_833_; lean_object* v___y_834_; uint8_t v___y_835_; lean_object* v___y_905_; lean_object* v___y_906_; lean_object* v___y_907_; uint8_t v___y_908_; lean_object* v___y_909_; lean_object* v___y_910_; lean_object* v___y_911_; uint8_t v___y_912_; lean_object* v___y_913_; lean_object* v___y_919_; uint8_t v___y_920_; lean_object* v___y_921_; lean_object* v___y_922_; lean_object* v___y_923_; lean_object* v___y_924_; uint8_t v___y_936_; uint8_t v___x_983_; 
v_a_749_ = lean_ctor_get(v___x_748_, 0);
lean_inc(v_a_749_);
lean_dec_ref_known(v___x_748_, 1);
v___x_983_ = l_Lean_Expr_isForall(v_a_749_);
if (v___x_983_ == 0)
{
v___y_936_ = v___x_983_;
goto v___jp_935_;
}
else
{
lean_object* v_numArgs_984_; uint8_t v___x_985_; 
v_numArgs_984_ = lean_ctor_get(v_recursorInfo_556_, 3);
v___x_985_ = lean_nat_dec_lt(v_pos_563_, v_numArgs_984_);
v___y_936_ = v___x_985_;
goto v___jp_935_;
}
v___jp_750_:
{
lean_object* v___x_765_; 
v___x_765_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___y_751_, v___y_762_, v___y_759_, v___y_755_, v___y_760_, v___y_756_);
if (lean_obj_tag(v___x_765_) == 0)
{
lean_object* v_a_766_; lean_object* v___x_767_; 
v_a_766_ = lean_ctor_get(v___x_765_, 0);
lean_inc(v_a_766_);
lean_dec_ref_known(v___x_765_, 1);
lean_inc(v_mvarId_554_);
v___x_767_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTypeBody(v_mvarId_554_, v_a_749_, v_a_766_, v___y_759_, v___y_755_, v___y_760_, v___y_756_);
if (lean_obj_tag(v___x_767_) == 0)
{
lean_object* v_options_768_; lean_object* v_a_769_; lean_object* v_inheritedTraceOptions_770_; uint8_t v_hasTrace_771_; lean_object* v___x_772_; 
v_options_768_ = lean_ctor_get(v___y_760_, 2);
v_a_769_ = lean_ctor_get(v___x_767_, 0);
lean_inc(v_a_769_);
lean_dec_ref_known(v___x_767_, 1);
v_inheritedTraceOptions_770_ = lean_ctor_get(v___y_760_, 13);
v_hasTrace_771_ = lean_ctor_get_uint8(v_options_768_, sizeof(void*)*1);
lean_inc(v_a_766_);
v___x_772_ = l_Lean_Expr_app___override(v_recursor_565_, v_a_766_);
if (v_hasTrace_771_ == 0)
{
v___y_682_ = v___y_764_;
v___y_683_ = v___y_752_;
v___y_684_ = v___y_753_;
v___y_685_ = v___y_754_;
v___y_686_ = v___x_772_;
v___y_687_ = v_a_766_;
v___y_688_ = v___y_757_;
v___y_689_ = v___y_761_;
v___y_690_ = v___y_758_;
v___y_691_ = v_a_769_;
v___y_692_ = v___y_763_;
v___y_693_ = v___y_759_;
v___y_694_ = v___y_755_;
v___y_695_ = v___y_760_;
v___y_696_ = v___y_756_;
goto v___jp_681_;
}
else
{
lean_object* v___x_773_; lean_object* v___x_774_; uint8_t v___x_775_; 
v___x_773_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__2));
v___x_774_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5);
v___x_775_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_770_, v_options_768_, v___x_774_);
if (v___x_775_ == 0)
{
v___y_682_ = v___y_764_;
v___y_683_ = v___y_752_;
v___y_684_ = v___y_753_;
v___y_685_ = v___y_754_;
v___y_686_ = v___x_772_;
v___y_687_ = v_a_766_;
v___y_688_ = v___y_757_;
v___y_689_ = v___y_761_;
v___y_690_ = v___y_758_;
v___y_691_ = v_a_769_;
v___y_692_ = v___y_763_;
v___y_693_ = v___y_759_;
v___y_694_ = v___y_755_;
v___y_695_ = v___y_760_;
v___y_696_ = v___y_756_;
goto v___jp_681_;
}
else
{
lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; 
v___x_776_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__11, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__11_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__11);
v___x_777_ = l_Lean_Expr_fvarId_x21(v_major_558_);
v___x_778_ = l_Lean_MessageData_ofName(v___x_777_);
v___x_779_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_779_, 0, v___x_776_);
lean_ctor_set(v___x_779_, 1, v___x_778_);
v___x_780_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1(v___x_773_, v___x_779_, v___y_759_, v___y_755_, v___y_760_, v___y_756_);
if (lean_obj_tag(v___x_780_) == 0)
{
lean_dec_ref_known(v___x_780_, 1);
v___y_682_ = v___y_764_;
v___y_683_ = v___y_752_;
v___y_684_ = v___y_753_;
v___y_685_ = v___y_754_;
v___y_686_ = v___x_772_;
v___y_687_ = v_a_766_;
v___y_688_ = v___y_757_;
v___y_689_ = v___y_761_;
v___y_690_ = v___y_758_;
v___y_691_ = v_a_769_;
v___y_692_ = v___y_763_;
v___y_693_ = v___y_759_;
v___y_694_ = v___y_755_;
v___y_695_ = v___y_760_;
v___y_696_ = v___y_756_;
goto v___jp_681_;
}
else
{
lean_object* v_a_781_; lean_object* v___x_783_; uint8_t v_isShared_784_; uint8_t v_isSharedCheck_788_; 
lean_dec_ref(v___x_772_);
lean_dec(v_a_769_);
lean_dec(v_a_766_);
lean_dec_ref(v___y_764_);
lean_dec(v___y_761_);
lean_dec(v___y_758_);
lean_dec(v___y_753_);
lean_dec(v___y_752_);
lean_dec_ref(v_subgoals_568_);
lean_dec(v_minorIdx_564_);
lean_dec(v_pos_563_);
lean_dec(v_baseSubst_560_);
lean_dec_ref(v_major_558_);
lean_dec(v_mvarId_554_);
v_a_781_ = lean_ctor_get(v___x_780_, 0);
v_isSharedCheck_788_ = !lean_is_exclusive(v___x_780_);
if (v_isSharedCheck_788_ == 0)
{
v___x_783_ = v___x_780_;
v_isShared_784_ = v_isSharedCheck_788_;
goto v_resetjp_782_;
}
else
{
lean_inc(v_a_781_);
lean_dec(v___x_780_);
v___x_783_ = lean_box(0);
v_isShared_784_ = v_isSharedCheck_788_;
goto v_resetjp_782_;
}
v_resetjp_782_:
{
lean_object* v___x_786_; 
if (v_isShared_784_ == 0)
{
v___x_786_ = v___x_783_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_787_; 
v_reuseFailAlloc_787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_787_, 0, v_a_781_);
v___x_786_ = v_reuseFailAlloc_787_;
goto v_reusejp_785_;
}
v_reusejp_785_:
{
return v___x_786_;
}
}
}
}
}
}
else
{
lean_object* v_a_789_; lean_object* v___x_791_; uint8_t v_isShared_792_; uint8_t v_isSharedCheck_796_; 
lean_dec(v_a_766_);
lean_dec_ref(v___y_764_);
lean_dec(v___y_761_);
lean_dec(v___y_758_);
lean_dec(v___y_753_);
lean_dec(v___y_752_);
lean_dec_ref(v_subgoals_568_);
lean_dec_ref(v_recursor_565_);
lean_dec(v_minorIdx_564_);
lean_dec(v_pos_563_);
lean_dec(v_baseSubst_560_);
lean_dec_ref(v_major_558_);
lean_dec(v_mvarId_554_);
v_a_789_ = lean_ctor_get(v___x_767_, 0);
v_isSharedCheck_796_ = !lean_is_exclusive(v___x_767_);
if (v_isSharedCheck_796_ == 0)
{
v___x_791_ = v___x_767_;
v_isShared_792_ = v_isSharedCheck_796_;
goto v_resetjp_790_;
}
else
{
lean_inc(v_a_789_);
lean_dec(v___x_767_);
v___x_791_ = lean_box(0);
v_isShared_792_ = v_isSharedCheck_796_;
goto v_resetjp_790_;
}
v_resetjp_790_:
{
lean_object* v___x_794_; 
if (v_isShared_792_ == 0)
{
v___x_794_ = v___x_791_;
goto v_reusejp_793_;
}
else
{
lean_object* v_reuseFailAlloc_795_; 
v_reuseFailAlloc_795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_795_, 0, v_a_789_);
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
else
{
lean_object* v_a_797_; lean_object* v___x_799_; uint8_t v_isShared_800_; uint8_t v_isSharedCheck_804_; 
lean_dec_ref(v___y_764_);
lean_dec(v___y_761_);
lean_dec(v___y_758_);
lean_dec(v___y_753_);
lean_dec(v___y_752_);
lean_dec(v_a_749_);
lean_dec_ref(v_subgoals_568_);
lean_dec_ref(v_recursor_565_);
lean_dec(v_minorIdx_564_);
lean_dec(v_pos_563_);
lean_dec(v_baseSubst_560_);
lean_dec_ref(v_major_558_);
lean_dec(v_mvarId_554_);
v_a_797_ = lean_ctor_get(v___x_765_, 0);
v_isSharedCheck_804_ = !lean_is_exclusive(v___x_765_);
if (v_isSharedCheck_804_ == 0)
{
v___x_799_ = v___x_765_;
v_isShared_800_ = v_isSharedCheck_804_;
goto v_resetjp_798_;
}
else
{
lean_inc(v_a_797_);
lean_dec(v___x_765_);
v___x_799_ = lean_box(0);
v_isShared_800_ = v_isSharedCheck_804_;
goto v_resetjp_798_;
}
v_resetjp_798_:
{
lean_object* v___x_802_; 
if (v_isShared_800_ == 0)
{
v___x_802_ = v___x_799_;
goto v_reusejp_801_;
}
else
{
lean_object* v_reuseFailAlloc_803_; 
v_reuseFailAlloc_803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_803_, 0, v_a_797_);
v___x_802_ = v_reuseFailAlloc_803_;
goto v_reusejp_801_;
}
v_reusejp_801_:
{
return v___x_802_;
}
}
}
}
v___jp_805_:
{
lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; uint8_t v___x_822_; 
v___x_816_ = lean_nat_sub(v___y_806_, v_initialArity_561_);
lean_dec(v___y_806_);
v___x_817_ = lean_array_get_size(v_reverted_557_);
v___x_818_ = lean_array_get_size(v_indices_559_);
v___x_819_ = lean_nat_sub(v___x_817_, v___x_818_);
v___x_820_ = lean_nat_sub(v___x_819_, v___y_811_);
lean_dec(v___x_819_);
v___x_821_ = lean_array_get_size(v_givenNames_555_);
v___x_822_ = lean_nat_dec_lt(v_minorIdx_564_, v___x_821_);
if (v___x_822_ == 0)
{
lean_object* v___x_823_; lean_object* v___x_824_; 
v___x_823_ = lean_box(0);
v___x_824_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_824_, 0, v___x_823_);
lean_ctor_set_uint8(v___x_824_, sizeof(void*)*1, v___y_808_);
v___y_751_ = v___y_807_;
v___y_752_ = v___x_820_;
v___y_753_ = v___x_816_;
v___y_754_ = v___y_808_;
v___y_755_ = v___y_813_;
v___y_756_ = v___y_815_;
v___y_757_ = v___y_809_;
v___y_758_ = v___x_818_;
v___y_759_ = v___y_812_;
v___y_760_ = v___y_814_;
v___y_761_ = v___x_817_;
v___y_762_ = v___y_810_;
v___y_763_ = v___y_811_;
v___y_764_ = v___x_824_;
goto v___jp_750_;
}
else
{
lean_object* v___x_825_; 
v___x_825_ = lean_array_fget_borrowed(v_givenNames_555_, v_minorIdx_564_);
lean_inc(v___x_825_);
v___y_751_ = v___y_807_;
v___y_752_ = v___x_820_;
v___y_753_ = v___x_816_;
v___y_754_ = v___y_808_;
v___y_755_ = v___y_813_;
v___y_756_ = v___y_815_;
v___y_757_ = v___y_809_;
v___y_758_ = v___x_818_;
v___y_759_ = v___y_812_;
v___y_760_ = v___y_814_;
v___y_761_ = v___x_817_;
v___y_762_ = v___y_810_;
v___y_763_ = v___y_811_;
v___y_764_ = v___x_825_;
goto v___jp_750_;
}
}
v___jp_826_:
{
if (v___y_835_ == 0)
{
lean_object* v___x_836_; uint8_t v___x_837_; 
lean_inc_ref(v___y_827_);
v___x_836_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTargetArity(v___y_827_);
v___x_837_ = lean_nat_dec_lt(v___x_836_, v_initialArity_561_);
if (v___x_837_ == 0)
{
v___y_806_ = v___x_836_;
v___y_807_ = v___y_827_;
v___y_808_ = v___y_835_;
v___y_809_ = v___y_830_;
v___y_810_ = v___y_831_;
v___y_811_ = v___y_833_;
v___y_812_ = v___y_828_;
v___y_813_ = v___y_832_;
v___y_814_ = v___y_829_;
v___y_815_ = v___y_834_;
goto v___jp_805_;
}
else
{
lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; 
v___x_838_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1));
v___x_839_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9);
lean_inc(v_mvarId_554_);
v___x_840_ = l_Lean_Meta_throwTacticEx___redArg(v___x_838_, v_mvarId_554_, v___x_839_, v___y_828_, v___y_832_, v___y_829_, v___y_834_);
if (lean_obj_tag(v___x_840_) == 0)
{
lean_dec_ref_known(v___x_840_, 1);
v___y_806_ = v___x_836_;
v___y_807_ = v___y_827_;
v___y_808_ = v___y_835_;
v___y_809_ = v___y_830_;
v___y_810_ = v___y_831_;
v___y_811_ = v___y_833_;
v___y_812_ = v___y_828_;
v___y_813_ = v___y_832_;
v___y_814_ = v___y_829_;
v___y_815_ = v___y_834_;
goto v___jp_805_;
}
else
{
lean_object* v_a_841_; lean_object* v___x_843_; uint8_t v_isShared_844_; uint8_t v_isSharedCheck_848_; 
lean_dec(v___x_836_);
lean_dec(v___y_831_);
lean_dec_ref(v___y_827_);
lean_dec(v_a_749_);
lean_dec_ref(v_subgoals_568_);
lean_dec_ref(v_recursor_565_);
lean_dec(v_minorIdx_564_);
lean_dec(v_pos_563_);
lean_dec(v_baseSubst_560_);
lean_dec_ref(v_major_558_);
lean_dec(v_mvarId_554_);
v_a_841_ = lean_ctor_get(v___x_840_, 0);
v_isSharedCheck_848_ = !lean_is_exclusive(v___x_840_);
if (v_isSharedCheck_848_ == 0)
{
v___x_843_ = v___x_840_;
v_isShared_844_ = v_isSharedCheck_848_;
goto v_resetjp_842_;
}
else
{
lean_inc(v_a_841_);
lean_dec(v___x_840_);
v___x_843_ = lean_box(0);
v_isShared_844_ = v_isSharedCheck_848_;
goto v_resetjp_842_;
}
v_resetjp_842_:
{
lean_object* v___x_846_; 
if (v_isShared_844_ == 0)
{
v___x_846_ = v___x_843_;
goto v_reusejp_845_;
}
else
{
lean_object* v_reuseFailAlloc_847_; 
v_reuseFailAlloc_847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_847_, 0, v_a_841_);
v___x_846_ = v_reuseFailAlloc_847_;
goto v_reusejp_845_;
}
v_reusejp_845_:
{
return v___x_846_;
}
}
}
}
}
else
{
lean_object* v___x_849_; lean_object* v___x_850_; 
v___x_849_ = lean_box(0);
lean_inc_ref(v___y_827_);
v___x_850_ = l_Lean_Meta_synthInstance_x3f(v___y_827_, v___x_849_, v___y_828_, v___y_832_, v___y_829_, v___y_834_);
if (lean_obj_tag(v___x_850_) == 0)
{
lean_object* v_a_851_; 
v_a_851_ = lean_ctor_get(v___x_850_, 0);
lean_inc(v_a_851_);
lean_dec_ref_known(v___x_850_, 1);
if (lean_obj_tag(v_a_851_) == 0)
{
lean_object* v___x_852_; 
v___x_852_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___y_827_, v___y_831_, v___y_828_, v___y_832_, v___y_829_, v___y_834_);
if (lean_obj_tag(v___x_852_) == 0)
{
lean_object* v_a_853_; lean_object* v___x_854_; 
v_a_853_ = lean_ctor_get(v___x_852_, 0);
lean_inc(v_a_853_);
lean_dec_ref_known(v___x_852_, 1);
lean_inc(v_mvarId_554_);
v___x_854_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTypeBody(v_mvarId_554_, v_a_749_, v_a_853_, v___y_828_, v___y_832_, v___y_829_, v___y_834_);
if (lean_obj_tag(v___x_854_) == 0)
{
lean_object* v_a_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; 
v_a_855_ = lean_ctor_get(v___x_854_, 0);
lean_inc(v_a_855_);
lean_dec_ref_known(v___x_854_, 1);
lean_inc(v_a_853_);
v___x_856_ = l_Lean_Expr_app___override(v_recursor_565_, v_a_853_);
v___x_857_ = lean_nat_add(v_pos_563_, v___y_833_);
lean_dec(v_pos_563_);
v___x_858_ = lean_nat_add(v_minorIdx_564_, v___y_833_);
lean_dec(v_minorIdx_564_);
v___x_859_ = l_Lean_Expr_mvarId_x21(v_a_853_);
lean_dec(v_a_853_);
v___x_860_ = ((lean_object*)(l_Lean_Meta_instInhabitedInductionSubgoal_default___closed__0));
v___x_861_ = lean_box(0);
v___x_862_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_862_, 0, v___x_859_);
lean_ctor_set(v___x_862_, 1, v___x_860_);
lean_ctor_set(v___x_862_, 2, v___x_861_);
v___x_863_ = lean_array_push(v_subgoals_568_, v___x_862_);
v_pos_563_ = v___x_857_;
v_minorIdx_564_ = v___x_858_;
v_recursor_565_ = v___x_856_;
v_recursorType_566_ = v_a_855_;
v_subgoals_568_ = v___x_863_;
v_a_569_ = v___y_828_;
v_a_570_ = v___y_832_;
v_a_571_ = v___y_829_;
v_a_572_ = v___y_834_;
goto _start;
}
else
{
lean_object* v_a_865_; lean_object* v___x_867_; uint8_t v_isShared_868_; uint8_t v_isSharedCheck_872_; 
lean_dec(v_a_853_);
lean_dec_ref(v_subgoals_568_);
lean_dec_ref(v_recursor_565_);
lean_dec(v_minorIdx_564_);
lean_dec(v_pos_563_);
lean_dec(v_baseSubst_560_);
lean_dec_ref(v_major_558_);
lean_dec(v_mvarId_554_);
v_a_865_ = lean_ctor_get(v___x_854_, 0);
v_isSharedCheck_872_ = !lean_is_exclusive(v___x_854_);
if (v_isSharedCheck_872_ == 0)
{
v___x_867_ = v___x_854_;
v_isShared_868_ = v_isSharedCheck_872_;
goto v_resetjp_866_;
}
else
{
lean_inc(v_a_865_);
lean_dec(v___x_854_);
v___x_867_ = lean_box(0);
v_isShared_868_ = v_isSharedCheck_872_;
goto v_resetjp_866_;
}
v_resetjp_866_:
{
lean_object* v___x_870_; 
if (v_isShared_868_ == 0)
{
v___x_870_ = v___x_867_;
goto v_reusejp_869_;
}
else
{
lean_object* v_reuseFailAlloc_871_; 
v_reuseFailAlloc_871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_871_, 0, v_a_865_);
v___x_870_ = v_reuseFailAlloc_871_;
goto v_reusejp_869_;
}
v_reusejp_869_:
{
return v___x_870_;
}
}
}
}
else
{
lean_object* v_a_873_; lean_object* v___x_875_; uint8_t v_isShared_876_; uint8_t v_isSharedCheck_880_; 
lean_dec(v_a_749_);
lean_dec_ref(v_subgoals_568_);
lean_dec_ref(v_recursor_565_);
lean_dec(v_minorIdx_564_);
lean_dec(v_pos_563_);
lean_dec(v_baseSubst_560_);
lean_dec_ref(v_major_558_);
lean_dec(v_mvarId_554_);
v_a_873_ = lean_ctor_get(v___x_852_, 0);
v_isSharedCheck_880_ = !lean_is_exclusive(v___x_852_);
if (v_isSharedCheck_880_ == 0)
{
v___x_875_ = v___x_852_;
v_isShared_876_ = v_isSharedCheck_880_;
goto v_resetjp_874_;
}
else
{
lean_inc(v_a_873_);
lean_dec(v___x_852_);
v___x_875_ = lean_box(0);
v_isShared_876_ = v_isSharedCheck_880_;
goto v_resetjp_874_;
}
v_resetjp_874_:
{
lean_object* v___x_878_; 
if (v_isShared_876_ == 0)
{
v___x_878_ = v___x_875_;
goto v_reusejp_877_;
}
else
{
lean_object* v_reuseFailAlloc_879_; 
v_reuseFailAlloc_879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_879_, 0, v_a_873_);
v___x_878_ = v_reuseFailAlloc_879_;
goto v_reusejp_877_;
}
v_reusejp_877_:
{
return v___x_878_;
}
}
}
}
else
{
lean_object* v_val_881_; lean_object* v___x_882_; 
lean_dec(v___y_831_);
lean_dec_ref(v___y_827_);
v_val_881_ = lean_ctor_get(v_a_851_, 0);
lean_inc(v_val_881_);
lean_dec_ref_known(v_a_851_, 1);
lean_inc(v_mvarId_554_);
v___x_882_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTypeBody(v_mvarId_554_, v_a_749_, v_val_881_, v___y_828_, v___y_832_, v___y_829_, v___y_834_);
if (lean_obj_tag(v___x_882_) == 0)
{
lean_object* v_a_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; 
v_a_883_ = lean_ctor_get(v___x_882_, 0);
lean_inc(v_a_883_);
lean_dec_ref_known(v___x_882_, 1);
v___x_884_ = l_Lean_Expr_app___override(v_recursor_565_, v_val_881_);
v___x_885_ = lean_nat_add(v_pos_563_, v___y_833_);
lean_dec(v_pos_563_);
v___x_886_ = lean_nat_add(v_minorIdx_564_, v___y_833_);
lean_dec(v_minorIdx_564_);
v_pos_563_ = v___x_885_;
v_minorIdx_564_ = v___x_886_;
v_recursor_565_ = v___x_884_;
v_recursorType_566_ = v_a_883_;
v_a_569_ = v___y_828_;
v_a_570_ = v___y_832_;
v_a_571_ = v___y_829_;
v_a_572_ = v___y_834_;
goto _start;
}
else
{
lean_object* v_a_888_; lean_object* v___x_890_; uint8_t v_isShared_891_; uint8_t v_isSharedCheck_895_; 
lean_dec(v_val_881_);
lean_dec_ref(v_subgoals_568_);
lean_dec_ref(v_recursor_565_);
lean_dec(v_minorIdx_564_);
lean_dec(v_pos_563_);
lean_dec(v_baseSubst_560_);
lean_dec_ref(v_major_558_);
lean_dec(v_mvarId_554_);
v_a_888_ = lean_ctor_get(v___x_882_, 0);
v_isSharedCheck_895_ = !lean_is_exclusive(v___x_882_);
if (v_isSharedCheck_895_ == 0)
{
v___x_890_ = v___x_882_;
v_isShared_891_ = v_isSharedCheck_895_;
goto v_resetjp_889_;
}
else
{
lean_inc(v_a_888_);
lean_dec(v___x_882_);
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
else
{
lean_object* v_a_896_; lean_object* v___x_898_; uint8_t v_isShared_899_; uint8_t v_isSharedCheck_903_; 
lean_dec(v___y_831_);
lean_dec_ref(v___y_827_);
lean_dec(v_a_749_);
lean_dec_ref(v_subgoals_568_);
lean_dec_ref(v_recursor_565_);
lean_dec(v_minorIdx_564_);
lean_dec(v_pos_563_);
lean_dec(v_baseSubst_560_);
lean_dec_ref(v_major_558_);
lean_dec(v_mvarId_554_);
v_a_896_ = lean_ctor_get(v___x_850_, 0);
v_isSharedCheck_903_ = !lean_is_exclusive(v___x_850_);
if (v_isSharedCheck_903_ == 0)
{
v___x_898_ = v___x_850_;
v_isShared_899_ = v_isSharedCheck_903_;
goto v_resetjp_897_;
}
else
{
lean_inc(v_a_896_);
lean_dec(v___x_850_);
v___x_898_ = lean_box(0);
v_isShared_899_ = v_isSharedCheck_903_;
goto v_resetjp_897_;
}
v_resetjp_897_:
{
lean_object* v___x_901_; 
if (v_isShared_899_ == 0)
{
v___x_901_ = v___x_898_;
goto v_reusejp_900_;
}
else
{
lean_object* v_reuseFailAlloc_902_; 
v_reuseFailAlloc_902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_902_, 0, v_a_896_);
v___x_901_ = v_reuseFailAlloc_902_;
goto v_reusejp_900_;
}
v_reusejp_900_:
{
return v___x_901_;
}
}
}
}
}
v___jp_904_:
{
uint8_t v___x_914_; 
v___x_914_ = l_Lean_BinderInfo_isInstImplicit(v___y_912_);
if (v___x_914_ == 0)
{
v___y_827_ = v___y_905_;
v___y_828_ = v___y_906_;
v___y_829_ = v___y_907_;
v___y_830_ = v___y_908_;
v___y_831_ = v___y_913_;
v___y_832_ = v___y_909_;
v___y_833_ = v___y_910_;
v___y_834_ = v___y_911_;
v___y_835_ = v___x_914_;
goto v___jp_826_;
}
else
{
lean_object* v___x_915_; lean_object* v___x_916_; uint8_t v___x_917_; 
v___x_915_ = lean_array_get_size(v_givenNames_555_);
v___x_916_ = lean_unsigned_to_nat(0u);
v___x_917_ = lean_nat_dec_eq(v___x_915_, v___x_916_);
v___y_827_ = v___y_905_;
v___y_828_ = v___y_906_;
v___y_829_ = v___y_907_;
v___y_830_ = v___y_908_;
v___y_831_ = v___y_913_;
v___y_832_ = v___y_909_;
v___y_833_ = v___y_910_;
v___y_834_ = v___y_911_;
v___y_835_ = v___x_917_;
goto v___jp_826_;
}
}
v___jp_918_:
{
if (lean_obj_tag(v_a_749_) == 7)
{
lean_object* v_binderName_925_; lean_object* v_binderType_926_; uint8_t v_binderInfo_927_; lean_object* v___x_928_; lean_object* v___x_929_; uint8_t v___x_930_; 
v_binderName_925_ = lean_ctor_get(v_a_749_, 0);
v_binderType_926_ = lean_ctor_get(v_a_749_, 1);
v_binderInfo_927_ = lean_ctor_get_uint8(v_a_749_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_926_);
v___x_928_ = l_Lean_Expr_headBeta(v_binderType_926_);
v___x_929_ = lean_unsigned_to_nat(1u);
v___x_930_ = lean_nat_dec_eq(v_numMinors_562_, v___x_929_);
if (v___x_930_ == 0)
{
lean_object* v___x_931_; lean_object* v___x_932_; 
v___x_931_ = l_Lean_Name_eraseMacroScopes(v_binderName_925_);
v___x_932_ = l_Lean_Name_append(v___y_919_, v___x_931_);
v___y_905_ = v___x_928_;
v___y_906_ = v___y_921_;
v___y_907_ = v___y_923_;
v___y_908_ = v___y_920_;
v___y_909_ = v___y_922_;
v___y_910_ = v___x_929_;
v___y_911_ = v___y_924_;
v___y_912_ = v_binderInfo_927_;
v___y_913_ = v___x_932_;
goto v___jp_904_;
}
else
{
v___y_905_ = v___x_928_;
v___y_906_ = v___y_921_;
v___y_907_ = v___y_923_;
v___y_908_ = v___y_920_;
v___y_909_ = v___y_922_;
v___y_910_ = v___x_929_;
v___y_911_ = v___y_924_;
v___y_912_ = v_binderInfo_927_;
v___y_913_ = v___y_919_;
goto v___jp_904_;
}
}
else
{
lean_object* v___x_933_; lean_object* v___x_934_; 
lean_dec(v___y_919_);
lean_dec(v_a_749_);
lean_dec_ref(v_subgoals_568_);
lean_dec_ref(v_recursor_565_);
lean_dec(v_minorIdx_564_);
lean_dec(v_pos_563_);
lean_dec(v_baseSubst_560_);
lean_dec_ref(v_major_558_);
lean_dec(v_mvarId_554_);
v___x_933_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__15, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__15_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__15);
v___x_934_ = l_panic___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__4(v___x_933_, v___y_921_, v___y_922_, v___y_923_, v___y_924_);
return v___x_934_;
}
}
v___jp_935_:
{
if (v___y_936_ == 0)
{
lean_dec(v_a_749_);
lean_dec(v_minorIdx_564_);
lean_dec(v_pos_563_);
lean_dec(v_baseSubst_560_);
lean_dec_ref(v_major_558_);
if (v_consumedMajor_567_ == 0)
{
lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; 
v___x_937_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1));
v___x_938_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9);
lean_inc(v_mvarId_554_);
v___x_939_ = l_Lean_Meta_throwTacticEx___redArg(v___x_937_, v_mvarId_554_, v___x_938_, v_a_569_, v_a_570_, v_a_571_, v_a_572_);
if (lean_obj_tag(v___x_939_) == 0)
{
lean_dec_ref_known(v___x_939_, 1);
v___y_575_ = v_a_569_;
v___y_576_ = v_a_570_;
v___y_577_ = v_a_571_;
v___y_578_ = v_a_572_;
goto v___jp_574_;
}
else
{
lean_object* v_a_940_; lean_object* v___x_942_; uint8_t v_isShared_943_; uint8_t v_isSharedCheck_947_; 
lean_dec_ref(v_subgoals_568_);
lean_dec_ref(v_recursor_565_);
lean_dec(v_mvarId_554_);
v_a_940_ = lean_ctor_get(v___x_939_, 0);
v_isSharedCheck_947_ = !lean_is_exclusive(v___x_939_);
if (v_isSharedCheck_947_ == 0)
{
v___x_942_ = v___x_939_;
v_isShared_943_ = v_isSharedCheck_947_;
goto v_resetjp_941_;
}
else
{
lean_inc(v_a_940_);
lean_dec(v___x_939_);
v___x_942_ = lean_box(0);
v_isShared_943_ = v_isSharedCheck_947_;
goto v_resetjp_941_;
}
v_resetjp_941_:
{
lean_object* v___x_945_; 
if (v_isShared_943_ == 0)
{
v___x_945_ = v___x_942_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v_a_940_);
v___x_945_ = v_reuseFailAlloc_946_;
goto v_reusejp_944_;
}
v_reusejp_944_:
{
return v___x_945_;
}
}
}
}
else
{
v___y_575_ = v_a_569_;
v___y_576_ = v_a_570_;
v___y_577_ = v_a_571_;
v___y_578_ = v_a_572_;
goto v___jp_574_;
}
}
else
{
lean_object* v___x_948_; uint8_t v___x_949_; 
v___x_948_ = l_Lean_Meta_RecursorInfo_firstIndexPos(v_recursorInfo_556_);
v___x_949_ = lean_nat_dec_eq(v_pos_563_, v___x_948_);
lean_dec(v___x_948_);
if (v___x_949_ == 0)
{
lean_object* v___x_950_; 
lean_inc(v_mvarId_554_);
v___x_950_ = l_Lean_MVarId_getTag(v_mvarId_554_, v_a_569_, v_a_570_, v_a_571_, v_a_572_);
if (lean_obj_tag(v___x_950_) == 0)
{
lean_object* v_a_951_; uint8_t v___x_952_; 
v_a_951_ = lean_ctor_get(v___x_950_, 0);
lean_inc(v_a_951_);
lean_dec_ref_known(v___x_950_, 1);
v___x_952_ = lean_nat_dec_le(v_numMinors_562_, v_minorIdx_564_);
if (v___x_952_ == 0)
{
v___y_919_ = v_a_951_;
v___y_920_ = v___y_936_;
v___y_921_ = v_a_569_;
v___y_922_ = v_a_570_;
v___y_923_ = v_a_571_;
v___y_924_ = v_a_572_;
goto v___jp_918_;
}
else
{
lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; 
v___x_953_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1));
v___x_954_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9);
lean_inc(v_mvarId_554_);
v___x_955_ = l_Lean_Meta_throwTacticEx___redArg(v___x_953_, v_mvarId_554_, v___x_954_, v_a_569_, v_a_570_, v_a_571_, v_a_572_);
if (lean_obj_tag(v___x_955_) == 0)
{
lean_dec_ref_known(v___x_955_, 1);
v___y_919_ = v_a_951_;
v___y_920_ = v___y_936_;
v___y_921_ = v_a_569_;
v___y_922_ = v_a_570_;
v___y_923_ = v_a_571_;
v___y_924_ = v_a_572_;
goto v___jp_918_;
}
else
{
lean_object* v_a_956_; lean_object* v___x_958_; uint8_t v_isShared_959_; uint8_t v_isSharedCheck_963_; 
lean_dec(v_a_951_);
lean_dec(v_a_749_);
lean_dec_ref(v_subgoals_568_);
lean_dec_ref(v_recursor_565_);
lean_dec(v_minorIdx_564_);
lean_dec(v_pos_563_);
lean_dec(v_baseSubst_560_);
lean_dec_ref(v_major_558_);
lean_dec(v_mvarId_554_);
v_a_956_ = lean_ctor_get(v___x_955_, 0);
v_isSharedCheck_963_ = !lean_is_exclusive(v___x_955_);
if (v_isSharedCheck_963_ == 0)
{
v___x_958_ = v___x_955_;
v_isShared_959_ = v_isSharedCheck_963_;
goto v_resetjp_957_;
}
else
{
lean_inc(v_a_956_);
lean_dec(v___x_955_);
v___x_958_ = lean_box(0);
v_isShared_959_ = v_isSharedCheck_963_;
goto v_resetjp_957_;
}
v_resetjp_957_:
{
lean_object* v___x_961_; 
if (v_isShared_959_ == 0)
{
v___x_961_ = v___x_958_;
goto v_reusejp_960_;
}
else
{
lean_object* v_reuseFailAlloc_962_; 
v_reuseFailAlloc_962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_962_, 0, v_a_956_);
v___x_961_ = v_reuseFailAlloc_962_;
goto v_reusejp_960_;
}
v_reusejp_960_:
{
return v___x_961_;
}
}
}
}
}
else
{
lean_object* v_a_964_; lean_object* v___x_966_; uint8_t v_isShared_967_; uint8_t v_isSharedCheck_971_; 
lean_dec(v_a_749_);
lean_dec_ref(v_subgoals_568_);
lean_dec_ref(v_recursor_565_);
lean_dec(v_minorIdx_564_);
lean_dec(v_pos_563_);
lean_dec(v_baseSubst_560_);
lean_dec_ref(v_major_558_);
lean_dec(v_mvarId_554_);
v_a_964_ = lean_ctor_get(v___x_950_, 0);
v_isSharedCheck_971_ = !lean_is_exclusive(v___x_950_);
if (v_isSharedCheck_971_ == 0)
{
v___x_966_ = v___x_950_;
v_isShared_967_ = v_isSharedCheck_971_;
goto v_resetjp_965_;
}
else
{
lean_inc(v_a_964_);
lean_dec(v___x_950_);
v___x_966_ = lean_box(0);
v_isShared_967_ = v_isSharedCheck_971_;
goto v_resetjp_965_;
}
v_resetjp_965_:
{
lean_object* v___x_969_; 
if (v_isShared_967_ == 0)
{
v___x_969_ = v___x_966_;
goto v_reusejp_968_;
}
else
{
lean_object* v_reuseFailAlloc_970_; 
v_reuseFailAlloc_970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_970_, 0, v_a_964_);
v___x_969_ = v_reuseFailAlloc_970_;
goto v_reusejp_968_;
}
v_reusejp_968_:
{
return v___x_969_;
}
}
}
}
else
{
lean_object* v___x_972_; lean_object* v___x_973_; uint8_t v___x_974_; 
v___x_972_ = lean_unsigned_to_nat(0u);
v___x_973_ = lean_array_get_size(v_indices_559_);
v___x_974_ = lean_nat_dec_lt(v___x_972_, v___x_973_);
if (v___x_974_ == 0)
{
v___y_714_ = v___x_949_;
v___y_715_ = v___x_973_;
v_fst_716_ = v_recursor_565_;
v_snd_717_ = v_a_749_;
goto v___jp_713_;
}
else
{
lean_object* v___x_975_; uint8_t v___x_976_; 
lean_inc(v_a_749_);
lean_inc_ref(v_recursor_565_);
v___x_975_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_975_, 0, v_recursor_565_);
lean_ctor_set(v___x_975_, 1, v_a_749_);
v___x_976_ = lean_nat_dec_le(v___x_973_, v___x_973_);
if (v___x_976_ == 0)
{
if (v___x_974_ == 0)
{
lean_dec_ref_known(v___x_975_, 2);
v___y_714_ = v___x_949_;
v___y_715_ = v___x_973_;
v_fst_716_ = v_recursor_565_;
v_snd_717_ = v_a_749_;
goto v___jp_713_;
}
else
{
size_t v___x_977_; size_t v___x_978_; lean_object* v___x_979_; 
lean_dec(v_a_749_);
lean_dec_ref(v_recursor_565_);
v___x_977_ = ((size_t)0ULL);
v___x_978_ = lean_usize_of_nat(v___x_973_);
lean_inc(v_mvarId_554_);
v___x_979_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__5(v_mvarId_554_, v_indices_559_, v___x_977_, v___x_978_, v___x_975_, v_a_569_, v_a_570_, v_a_571_, v_a_572_);
v___y_734_ = v___x_949_;
v___y_735_ = v___x_973_;
v___y_736_ = v___x_979_;
goto v___jp_733_;
}
}
else
{
size_t v___x_980_; size_t v___x_981_; lean_object* v___x_982_; 
lean_dec(v_a_749_);
lean_dec_ref(v_recursor_565_);
v___x_980_ = ((size_t)0ULL);
v___x_981_ = lean_usize_of_nat(v___x_973_);
lean_inc(v_mvarId_554_);
v___x_982_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__5(v_mvarId_554_, v_indices_559_, v___x_980_, v___x_981_, v___x_975_, v_a_569_, v_a_570_, v_a_571_, v_a_572_);
v___y_734_ = v___x_949_;
v___y_735_ = v___x_973_;
v___y_736_ = v___x_982_;
goto v___jp_733_;
}
}
}
}
}
}
else
{
lean_object* v_a_986_; lean_object* v___x_988_; uint8_t v_isShared_989_; uint8_t v_isSharedCheck_993_; 
lean_dec_ref(v_subgoals_568_);
lean_dec_ref(v_recursor_565_);
lean_dec(v_minorIdx_564_);
lean_dec(v_pos_563_);
lean_dec(v_baseSubst_560_);
lean_dec_ref(v_major_558_);
lean_dec(v_mvarId_554_);
v_a_986_ = lean_ctor_get(v___x_748_, 0);
v_isSharedCheck_993_ = !lean_is_exclusive(v___x_748_);
if (v_isSharedCheck_993_ == 0)
{
v___x_988_ = v___x_748_;
v_isShared_989_ = v_isSharedCheck_993_;
goto v_resetjp_987_;
}
else
{
lean_inc(v_a_986_);
lean_dec(v___x_748_);
v___x_988_ = lean_box(0);
v_isShared_989_ = v_isSharedCheck_993_;
goto v_resetjp_987_;
}
v_resetjp_987_:
{
lean_object* v___x_991_; 
if (v_isShared_989_ == 0)
{
v___x_991_ = v___x_988_;
goto v_reusejp_990_;
}
else
{
lean_object* v_reuseFailAlloc_992_; 
v_reuseFailAlloc_992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_992_, 0, v_a_986_);
v___x_991_ = v_reuseFailAlloc_992_;
goto v_reusejp_990_;
}
v_reusejp_990_:
{
return v___x_991_;
}
}
}
v___jp_574_:
{
lean_object* v___x_579_; 
v___x_579_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0___redArg(v_mvarId_554_, v_recursor_565_, v___y_576_);
if (lean_obj_tag(v___x_579_) == 0)
{
lean_object* v___x_581_; uint8_t v_isShared_582_; uint8_t v_isSharedCheck_620_; 
v_isSharedCheck_620_ = !lean_is_exclusive(v___x_579_);
if (v_isSharedCheck_620_ == 0)
{
lean_object* v_unused_621_; 
v_unused_621_ = lean_ctor_get(v___x_579_, 0);
lean_dec(v_unused_621_);
v___x_581_ = v___x_579_;
v_isShared_582_ = v_isSharedCheck_620_;
goto v_resetjp_580_;
}
else
{
lean_dec(v___x_579_);
v___x_581_ = lean_box(0);
v_isShared_582_ = v_isSharedCheck_620_;
goto v_resetjp_580_;
}
v_resetjp_580_:
{
lean_object* v_options_583_; uint8_t v_hasTrace_584_; 
v_options_583_ = lean_ctor_get(v___y_577_, 2);
v_hasTrace_584_ = lean_ctor_get_uint8(v_options_583_, sizeof(void*)*1);
if (v_hasTrace_584_ == 0)
{
lean_object* v___x_586_; 
if (v_isShared_582_ == 0)
{
lean_ctor_set(v___x_581_, 0, v_subgoals_568_);
v___x_586_ = v___x_581_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_587_; 
v_reuseFailAlloc_587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_587_, 0, v_subgoals_568_);
v___x_586_ = v_reuseFailAlloc_587_;
goto v_reusejp_585_;
}
v_reusejp_585_:
{
return v___x_586_;
}
}
else
{
lean_object* v_inheritedTraceOptions_588_; lean_object* v___x_589_; lean_object* v___x_590_; uint8_t v___x_591_; 
v_inheritedTraceOptions_588_ = lean_ctor_get(v___y_577_, 13);
v___x_589_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__2));
v___x_590_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5);
v___x_591_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_588_, v_options_583_, v___x_590_);
if (v___x_591_ == 0)
{
lean_object* v___x_593_; 
if (v_isShared_582_ == 0)
{
lean_ctor_set(v___x_581_, 0, v_subgoals_568_);
v___x_593_ = v___x_581_;
goto v_reusejp_592_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v_subgoals_568_);
v___x_593_ = v_reuseFailAlloc_594_;
goto v_reusejp_592_;
}
v_reusejp_592_:
{
return v___x_593_;
}
}
else
{
lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; 
lean_del_object(v___x_581_);
v___x_595_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__7, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__7_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__7);
v___x_596_ = lean_array_get_size(v_subgoals_568_);
v___x_597_ = l_Nat_reprFast(v___x_596_);
v___x_598_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_598_, 0, v___x_597_);
v___x_599_ = l_Lean_MessageData_ofFormat(v___x_598_);
v___x_600_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_600_, 0, v___x_595_);
lean_ctor_set(v___x_600_, 1, v___x_599_);
v___x_601_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__9, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__9_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__9);
v___x_602_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_602_, 0, v___x_600_);
lean_ctor_set(v___x_602_, 1, v___x_601_);
v___x_603_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1(v___x_589_, v___x_602_, v___y_575_, v___y_576_, v___y_577_, v___y_578_);
if (lean_obj_tag(v___x_603_) == 0)
{
lean_object* v___x_605_; uint8_t v_isShared_606_; uint8_t v_isSharedCheck_610_; 
v_isSharedCheck_610_ = !lean_is_exclusive(v___x_603_);
if (v_isSharedCheck_610_ == 0)
{
lean_object* v_unused_611_; 
v_unused_611_ = lean_ctor_get(v___x_603_, 0);
lean_dec(v_unused_611_);
v___x_605_ = v___x_603_;
v_isShared_606_ = v_isSharedCheck_610_;
goto v_resetjp_604_;
}
else
{
lean_dec(v___x_603_);
v___x_605_ = lean_box(0);
v_isShared_606_ = v_isSharedCheck_610_;
goto v_resetjp_604_;
}
v_resetjp_604_:
{
lean_object* v___x_608_; 
if (v_isShared_606_ == 0)
{
lean_ctor_set(v___x_605_, 0, v_subgoals_568_);
v___x_608_ = v___x_605_;
goto v_reusejp_607_;
}
else
{
lean_object* v_reuseFailAlloc_609_; 
v_reuseFailAlloc_609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v_subgoals_568_);
v___x_608_ = v_reuseFailAlloc_609_;
goto v_reusejp_607_;
}
v_reusejp_607_:
{
return v___x_608_;
}
}
}
else
{
lean_object* v_a_612_; lean_object* v___x_614_; uint8_t v_isShared_615_; uint8_t v_isSharedCheck_619_; 
lean_dec_ref(v_subgoals_568_);
v_a_612_ = lean_ctor_get(v___x_603_, 0);
v_isSharedCheck_619_ = !lean_is_exclusive(v___x_603_);
if (v_isSharedCheck_619_ == 0)
{
v___x_614_ = v___x_603_;
v_isShared_615_ = v_isSharedCheck_619_;
goto v_resetjp_613_;
}
else
{
lean_inc(v_a_612_);
lean_dec(v___x_603_);
v___x_614_ = lean_box(0);
v_isShared_615_ = v_isSharedCheck_619_;
goto v_resetjp_613_;
}
v_resetjp_613_:
{
lean_object* v___x_617_; 
if (v_isShared_615_ == 0)
{
v___x_617_ = v___x_614_;
goto v_reusejp_616_;
}
else
{
lean_object* v_reuseFailAlloc_618_; 
v_reuseFailAlloc_618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_618_, 0, v_a_612_);
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
else
{
lean_object* v_a_622_; lean_object* v___x_624_; uint8_t v_isShared_625_; uint8_t v_isSharedCheck_629_; 
lean_dec_ref(v_subgoals_568_);
v_a_622_ = lean_ctor_get(v___x_579_, 0);
v_isSharedCheck_629_ = !lean_is_exclusive(v___x_579_);
if (v_isSharedCheck_629_ == 0)
{
v___x_624_ = v___x_579_;
v_isShared_625_ = v_isSharedCheck_629_;
goto v_resetjp_623_;
}
else
{
lean_inc(v_a_622_);
lean_dec(v___x_579_);
v___x_624_ = lean_box(0);
v_isShared_625_ = v_isSharedCheck_629_;
goto v_resetjp_623_;
}
v_resetjp_623_:
{
lean_object* v___x_627_; 
if (v_isShared_625_ == 0)
{
v___x_627_ = v___x_624_;
goto v_reusejp_626_;
}
else
{
lean_object* v_reuseFailAlloc_628_; 
v_reuseFailAlloc_628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_628_, 0, v_a_622_);
v___x_627_ = v_reuseFailAlloc_628_;
goto v_reusejp_626_;
}
v_reusejp_626_:
{
return v___x_627_;
}
}
}
}
v___jp_630_:
{
lean_object* v___x_647_; 
v___x_647_ = l_Lean_Meta_introNCore(v___y_640_, v___y_632_, v___y_633_, v___y_646_, v___y_634_, v___y_643_, v___y_635_, v___y_636_, v___y_644_);
if (lean_obj_tag(v___x_647_) == 0)
{
lean_object* v_a_648_; lean_object* v_fst_649_; lean_object* v_snd_650_; lean_object* v___x_651_; lean_object* v___x_652_; 
v_a_648_ = lean_ctor_get(v___x_647_, 0);
lean_inc(v_a_648_);
lean_dec_ref_known(v___x_647_, 1);
v_fst_649_ = lean_ctor_get(v_a_648_, 0);
lean_inc(v_fst_649_);
v_snd_650_ = lean_ctor_get(v_a_648_, 1);
lean_inc(v_snd_650_);
lean_dec(v_a_648_);
v___x_651_ = lean_box(0);
v___x_652_ = l_Lean_Meta_introNCore(v_snd_650_, v___y_631_, v___x_651_, v___y_634_, v___y_637_, v___y_643_, v___y_635_, v___y_636_, v___y_644_);
if (lean_obj_tag(v___x_652_) == 0)
{
lean_object* v_a_653_; lean_object* v_fst_654_; lean_object* v_snd_655_; lean_object* v___x_656_; size_t v_sz_657_; size_t v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; 
v_a_653_ = lean_ctor_get(v___x_652_, 0);
lean_inc(v_a_653_);
lean_dec_ref_known(v___x_652_, 1);
v_fst_654_ = lean_ctor_get(v_a_653_, 0);
lean_inc(v_fst_654_);
v_snd_655_ = lean_ctor_get(v_a_653_, 1);
lean_inc(v_snd_655_);
lean_dec(v_a_653_);
lean_inc(v_baseSubst_560_);
lean_inc(v___y_642_);
v___x_656_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__2___redArg(v___y_638_, v_reverted_557_, v_fst_654_, v___y_642_, v___y_642_, v_baseSubst_560_);
lean_dec(v___y_642_);
lean_dec(v_fst_654_);
lean_dec(v___y_638_);
v_sz_657_ = lean_array_size(v_fst_649_);
v___x_658_ = ((size_t)0ULL);
v___x_659_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__3(v_sz_657_, v___x_658_, v_fst_649_);
v___x_660_ = lean_nat_add(v_pos_563_, v___y_645_);
lean_dec(v_pos_563_);
v___x_661_ = lean_nat_add(v_minorIdx_564_, v___y_645_);
lean_dec(v_minorIdx_564_);
v___x_662_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_662_, 0, v_snd_655_);
lean_ctor_set(v___x_662_, 1, v___x_659_);
lean_ctor_set(v___x_662_, 2, v___x_656_);
v___x_663_ = lean_array_push(v_subgoals_568_, v___x_662_);
v_pos_563_ = v___x_660_;
v_minorIdx_564_ = v___x_661_;
v_recursor_565_ = v___y_641_;
v_recursorType_566_ = v___y_639_;
v_subgoals_568_ = v___x_663_;
v_a_569_ = v___y_643_;
v_a_570_ = v___y_635_;
v_a_571_ = v___y_636_;
v_a_572_ = v___y_644_;
goto _start;
}
else
{
lean_object* v_a_665_; lean_object* v___x_667_; uint8_t v_isShared_668_; uint8_t v_isSharedCheck_672_; 
lean_dec(v_fst_649_);
lean_dec(v___y_642_);
lean_dec_ref(v___y_641_);
lean_dec_ref(v___y_639_);
lean_dec(v___y_638_);
lean_dec_ref(v_subgoals_568_);
lean_dec(v_minorIdx_564_);
lean_dec(v_pos_563_);
lean_dec(v_baseSubst_560_);
lean_dec_ref(v_major_558_);
lean_dec(v_mvarId_554_);
v_a_665_ = lean_ctor_get(v___x_652_, 0);
v_isSharedCheck_672_ = !lean_is_exclusive(v___x_652_);
if (v_isSharedCheck_672_ == 0)
{
v___x_667_ = v___x_652_;
v_isShared_668_ = v_isSharedCheck_672_;
goto v_resetjp_666_;
}
else
{
lean_inc(v_a_665_);
lean_dec(v___x_652_);
v___x_667_ = lean_box(0);
v_isShared_668_ = v_isSharedCheck_672_;
goto v_resetjp_666_;
}
v_resetjp_666_:
{
lean_object* v___x_670_; 
if (v_isShared_668_ == 0)
{
v___x_670_ = v___x_667_;
goto v_reusejp_669_;
}
else
{
lean_object* v_reuseFailAlloc_671_; 
v_reuseFailAlloc_671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_671_, 0, v_a_665_);
v___x_670_ = v_reuseFailAlloc_671_;
goto v_reusejp_669_;
}
v_reusejp_669_:
{
return v___x_670_;
}
}
}
}
else
{
lean_object* v_a_673_; lean_object* v___x_675_; uint8_t v_isShared_676_; uint8_t v_isSharedCheck_680_; 
lean_dec(v___y_642_);
lean_dec_ref(v___y_641_);
lean_dec_ref(v___y_639_);
lean_dec(v___y_638_);
lean_dec(v___y_631_);
lean_dec_ref(v_subgoals_568_);
lean_dec(v_minorIdx_564_);
lean_dec(v_pos_563_);
lean_dec(v_baseSubst_560_);
lean_dec_ref(v_major_558_);
lean_dec(v_mvarId_554_);
v_a_673_ = lean_ctor_get(v___x_647_, 0);
v_isSharedCheck_680_ = !lean_is_exclusive(v___x_647_);
if (v_isSharedCheck_680_ == 0)
{
v___x_675_ = v___x_647_;
v_isShared_676_ = v_isSharedCheck_680_;
goto v_resetjp_674_;
}
else
{
lean_inc(v_a_673_);
lean_dec(v___x_647_);
v___x_675_ = lean_box(0);
v_isShared_676_ = v_isSharedCheck_680_;
goto v_resetjp_674_;
}
v_resetjp_674_:
{
lean_object* v___x_678_; 
if (v_isShared_676_ == 0)
{
v___x_678_ = v___x_675_;
goto v_reusejp_677_;
}
else
{
lean_object* v_reuseFailAlloc_679_; 
v_reuseFailAlloc_679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_679_, 0, v_a_673_);
v___x_678_ = v_reuseFailAlloc_679_;
goto v_reusejp_677_;
}
v_reusejp_677_:
{
return v___x_678_;
}
}
}
}
v___jp_681_:
{
lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; 
v___x_697_ = l_Lean_Expr_mvarId_x21(v___y_687_);
lean_dec_ref(v___y_687_);
v___x_698_ = l_Lean_Expr_fvarId_x21(v_major_558_);
v___x_699_ = l_Lean_MVarId_tryClear(v___x_697_, v___x_698_, v___y_693_, v___y_694_, v___y_695_, v___y_696_);
if (lean_obj_tag(v___x_699_) == 0)
{
uint8_t v_explicit_700_; 
v_explicit_700_ = lean_ctor_get_uint8(v___y_682_, sizeof(void*)*1);
if (v_explicit_700_ == 0)
{
lean_object* v_a_701_; lean_object* v_varNames_702_; 
v_a_701_ = lean_ctor_get(v___x_699_, 0);
lean_inc(v_a_701_);
lean_dec_ref_known(v___x_699_, 1);
v_varNames_702_ = lean_ctor_get(v___y_682_, 0);
lean_inc(v_varNames_702_);
lean_dec_ref(v___y_682_);
v___y_631_ = v___y_683_;
v___y_632_ = v___y_684_;
v___y_633_ = v_varNames_702_;
v___y_634_ = v___y_685_;
v___y_635_ = v___y_694_;
v___y_636_ = v___y_695_;
v___y_637_ = v___y_688_;
v___y_638_ = v___y_690_;
v___y_639_ = v___y_691_;
v___y_640_ = v_a_701_;
v___y_641_ = v___y_686_;
v___y_642_ = v___y_689_;
v___y_643_ = v___y_693_;
v___y_644_ = v___y_696_;
v___y_645_ = v___y_692_;
v___y_646_ = v___y_688_;
goto v___jp_630_;
}
else
{
lean_object* v_a_703_; lean_object* v_varNames_704_; 
v_a_703_ = lean_ctor_get(v___x_699_, 0);
lean_inc(v_a_703_);
lean_dec_ref_known(v___x_699_, 1);
v_varNames_704_ = lean_ctor_get(v___y_682_, 0);
lean_inc(v_varNames_704_);
lean_dec_ref(v___y_682_);
v___y_631_ = v___y_683_;
v___y_632_ = v___y_684_;
v___y_633_ = v_varNames_704_;
v___y_634_ = v___y_685_;
v___y_635_ = v___y_694_;
v___y_636_ = v___y_695_;
v___y_637_ = v___y_688_;
v___y_638_ = v___y_690_;
v___y_639_ = v___y_691_;
v___y_640_ = v_a_703_;
v___y_641_ = v___y_686_;
v___y_642_ = v___y_689_;
v___y_643_ = v___y_693_;
v___y_644_ = v___y_696_;
v___y_645_ = v___y_692_;
v___y_646_ = v___y_685_;
goto v___jp_630_;
}
}
else
{
lean_object* v_a_705_; lean_object* v___x_707_; uint8_t v_isShared_708_; uint8_t v_isSharedCheck_712_; 
lean_dec_ref(v___y_691_);
lean_dec(v___y_690_);
lean_dec(v___y_689_);
lean_dec_ref(v___y_686_);
lean_dec(v___y_684_);
lean_dec(v___y_683_);
lean_dec_ref(v___y_682_);
lean_dec_ref(v_subgoals_568_);
lean_dec(v_minorIdx_564_);
lean_dec(v_pos_563_);
lean_dec(v_baseSubst_560_);
lean_dec_ref(v_major_558_);
lean_dec(v_mvarId_554_);
v_a_705_ = lean_ctor_get(v___x_699_, 0);
v_isSharedCheck_712_ = !lean_is_exclusive(v___x_699_);
if (v_isSharedCheck_712_ == 0)
{
v___x_707_ = v___x_699_;
v_isShared_708_ = v_isSharedCheck_712_;
goto v_resetjp_706_;
}
else
{
lean_inc(v_a_705_);
lean_dec(v___x_699_);
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
v___jp_713_:
{
lean_object* v___x_718_; 
lean_inc(v_mvarId_554_);
v___x_718_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTypeBody(v_mvarId_554_, v_snd_717_, v_major_558_, v_a_569_, v_a_570_, v_a_571_, v_a_572_);
if (lean_obj_tag(v___x_718_) == 0)
{
lean_object* v_a_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; 
v_a_719_ = lean_ctor_get(v___x_718_, 0);
lean_inc(v_a_719_);
lean_dec_ref_known(v___x_718_, 1);
lean_inc_ref(v_major_558_);
v___x_720_ = l_Lean_Expr_app___override(v_fst_716_, v_major_558_);
v___x_721_ = lean_unsigned_to_nat(1u);
v___x_722_ = lean_nat_add(v_pos_563_, v___x_721_);
lean_dec(v_pos_563_);
v___x_723_ = lean_nat_add(v___x_722_, v___y_715_);
lean_dec(v___y_715_);
lean_dec(v___x_722_);
v_pos_563_ = v___x_723_;
v_recursor_565_ = v___x_720_;
v_recursorType_566_ = v_a_719_;
v_consumedMajor_567_ = v___y_714_;
goto _start;
}
else
{
lean_object* v_a_725_; lean_object* v___x_727_; uint8_t v_isShared_728_; uint8_t v_isSharedCheck_732_; 
lean_dec_ref(v_fst_716_);
lean_dec(v___y_715_);
lean_dec_ref(v_subgoals_568_);
lean_dec(v_minorIdx_564_);
lean_dec(v_pos_563_);
lean_dec(v_baseSubst_560_);
lean_dec_ref(v_major_558_);
lean_dec(v_mvarId_554_);
v_a_725_ = lean_ctor_get(v___x_718_, 0);
v_isSharedCheck_732_ = !lean_is_exclusive(v___x_718_);
if (v_isSharedCheck_732_ == 0)
{
v___x_727_ = v___x_718_;
v_isShared_728_ = v_isSharedCheck_732_;
goto v_resetjp_726_;
}
else
{
lean_inc(v_a_725_);
lean_dec(v___x_718_);
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
v___jp_733_:
{
if (lean_obj_tag(v___y_736_) == 0)
{
lean_object* v_a_737_; lean_object* v_fst_738_; lean_object* v_snd_739_; 
v_a_737_ = lean_ctor_get(v___y_736_, 0);
lean_inc(v_a_737_);
lean_dec_ref_known(v___y_736_, 1);
v_fst_738_ = lean_ctor_get(v_a_737_, 0);
lean_inc(v_fst_738_);
v_snd_739_ = lean_ctor_get(v_a_737_, 1);
lean_inc(v_snd_739_);
lean_dec(v_a_737_);
v___y_714_ = v___y_734_;
v___y_715_ = v___y_735_;
v_fst_716_ = v_fst_738_;
v_snd_717_ = v_snd_739_;
goto v___jp_713_;
}
else
{
lean_object* v_a_740_; lean_object* v___x_742_; uint8_t v_isShared_743_; uint8_t v_isSharedCheck_747_; 
lean_dec(v___y_735_);
lean_dec_ref(v_subgoals_568_);
lean_dec(v_minorIdx_564_);
lean_dec(v_pos_563_);
lean_dec(v_baseSubst_560_);
lean_dec_ref(v_major_558_);
lean_dec(v_mvarId_554_);
v_a_740_ = lean_ctor_get(v___y_736_, 0);
v_isSharedCheck_747_ = !lean_is_exclusive(v___y_736_);
if (v_isSharedCheck_747_ == 0)
{
v___x_742_ = v___y_736_;
v_isShared_743_ = v_isSharedCheck_747_;
goto v_resetjp_741_;
}
else
{
lean_inc(v_a_740_);
lean_dec(v___y_736_);
v___x_742_ = lean_box(0);
v_isShared_743_ = v_isSharedCheck_747_;
goto v_resetjp_741_;
}
v_resetjp_741_:
{
lean_object* v___x_745_; 
if (v_isShared_743_ == 0)
{
v___x_745_ = v___x_742_;
goto v_reusejp_744_;
}
else
{
lean_object* v_reuseFailAlloc_746_; 
v_reuseFailAlloc_746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_746_, 0, v_a_740_);
v___x_745_ = v_reuseFailAlloc_746_;
goto v_reusejp_744_;
}
v_reusejp_744_:
{
return v___x_745_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___boxed(lean_object** _args){
lean_object* v_mvarId_994_ = _args[0];
lean_object* v_givenNames_995_ = _args[1];
lean_object* v_recursorInfo_996_ = _args[2];
lean_object* v_reverted_997_ = _args[3];
lean_object* v_major_998_ = _args[4];
lean_object* v_indices_999_ = _args[5];
lean_object* v_baseSubst_1000_ = _args[6];
lean_object* v_initialArity_1001_ = _args[7];
lean_object* v_numMinors_1002_ = _args[8];
lean_object* v_pos_1003_ = _args[9];
lean_object* v_minorIdx_1004_ = _args[10];
lean_object* v_recursor_1005_ = _args[11];
lean_object* v_recursorType_1006_ = _args[12];
lean_object* v_consumedMajor_1007_ = _args[13];
lean_object* v_subgoals_1008_ = _args[14];
lean_object* v_a_1009_ = _args[15];
lean_object* v_a_1010_ = _args[16];
lean_object* v_a_1011_ = _args[17];
lean_object* v_a_1012_ = _args[18];
lean_object* v_a_1013_ = _args[19];
_start:
{
uint8_t v_consumedMajor_boxed_1014_; lean_object* v_res_1015_; 
v_consumedMajor_boxed_1014_ = lean_unbox(v_consumedMajor_1007_);
v_res_1015_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop(v_mvarId_994_, v_givenNames_995_, v_recursorInfo_996_, v_reverted_997_, v_major_998_, v_indices_999_, v_baseSubst_1000_, v_initialArity_1001_, v_numMinors_1002_, v_pos_1003_, v_minorIdx_1004_, v_recursor_1005_, v_recursorType_1006_, v_consumedMajor_boxed_1014_, v_subgoals_1008_, v_a_1009_, v_a_1010_, v_a_1011_, v_a_1012_);
lean_dec(v_a_1012_);
lean_dec_ref(v_a_1011_);
lean_dec(v_a_1010_);
lean_dec_ref(v_a_1009_);
lean_dec(v_numMinors_1002_);
lean_dec(v_initialArity_1001_);
lean_dec_ref(v_indices_999_);
lean_dec_ref(v_reverted_997_);
lean_dec_ref(v_recursorInfo_996_);
lean_dec_ref(v_givenNames_995_);
return v_res_1015_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0(lean_object* v_mvarId_1016_, lean_object* v_val_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_){
_start:
{
lean_object* v___x_1023_; 
v___x_1023_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0___redArg(v_mvarId_1016_, v_val_1017_, v___y_1019_);
return v___x_1023_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0___boxed(lean_object* v_mvarId_1024_, lean_object* v_val_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_){
_start:
{
lean_object* v_res_1031_; 
v_res_1031_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0(v_mvarId_1024_, v_val_1025_, v___y_1026_, v___y_1027_, v___y_1028_, v___y_1029_);
lean_dec(v___y_1029_);
lean_dec_ref(v___y_1028_);
lean_dec(v___y_1027_);
lean_dec_ref(v___y_1026_);
return v_res_1031_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__2(lean_object* v___x_1032_, lean_object* v_reverted_1033_, lean_object* v_fst_1034_, lean_object* v_n_1035_, lean_object* v_j_1036_, lean_object* v_a_1037_, lean_object* v_a_1038_){
_start:
{
lean_object* v___x_1039_; 
v___x_1039_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__2___redArg(v___x_1032_, v_reverted_1033_, v_fst_1034_, v_n_1035_, v_j_1036_, v_a_1038_);
return v___x_1039_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__2___boxed(lean_object* v___x_1040_, lean_object* v_reverted_1041_, lean_object* v_fst_1042_, lean_object* v_n_1043_, lean_object* v_j_1044_, lean_object* v_a_1045_, lean_object* v_a_1046_){
_start:
{
lean_object* v_res_1047_; 
v_res_1047_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__2(v___x_1040_, v_reverted_1041_, v_fst_1042_, v_n_1043_, v_j_1044_, v_a_1045_, v_a_1046_);
lean_dec(v_n_1043_);
lean_dec_ref(v_fst_1042_);
lean_dec_ref(v_reverted_1041_);
lean_dec(v___x_1040_);
return v_res_1047_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0(lean_object* v_00_u03b2_1048_, lean_object* v_x_1049_, lean_object* v_x_1050_, lean_object* v_x_1051_){
_start:
{
lean_object* v___x_1052_; 
v___x_1052_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0___redArg(v_x_1049_, v_x_1050_, v_x_1051_);
return v___x_1052_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1053_, lean_object* v_x_1054_, size_t v_x_1055_, size_t v_x_1056_, lean_object* v_x_1057_, lean_object* v_x_1058_){
_start:
{
lean_object* v___x_1059_; 
v___x_1059_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2___redArg(v_x_1054_, v_x_1055_, v_x_1056_, v_x_1057_, v_x_1058_);
return v___x_1059_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1060_, lean_object* v_x_1061_, lean_object* v_x_1062_, lean_object* v_x_1063_, lean_object* v_x_1064_, lean_object* v_x_1065_){
_start:
{
size_t v_x_11483__boxed_1066_; size_t v_x_11484__boxed_1067_; lean_object* v_res_1068_; 
v_x_11483__boxed_1066_ = lean_unbox_usize(v_x_1062_);
lean_dec(v_x_1062_);
v_x_11484__boxed_1067_ = lean_unbox_usize(v_x_1063_);
lean_dec(v_x_1063_);
v_res_1068_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2(v_00_u03b2_1060_, v_x_1061_, v_x_11483__boxed_1066_, v_x_11484__boxed_1067_, v_x_1064_, v_x_1065_);
return v_res_1068_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__8(lean_object* v_00_u03b2_1069_, lean_object* v_n_1070_, lean_object* v_k_1071_, lean_object* v_v_1072_){
_start:
{
lean_object* v___x_1073_; 
v___x_1073_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__8___redArg(v_n_1070_, v_k_1071_, v_v_1072_);
return v___x_1073_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__9(lean_object* v_00_u03b2_1074_, size_t v_depth_1075_, lean_object* v_keys_1076_, lean_object* v_vals_1077_, lean_object* v_heq_1078_, lean_object* v_i_1079_, lean_object* v_entries_1080_){
_start:
{
lean_object* v___x_1081_; 
v___x_1081_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__9___redArg(v_depth_1075_, v_keys_1076_, v_vals_1077_, v_i_1079_, v_entries_1080_);
return v___x_1081_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__9___boxed(lean_object* v_00_u03b2_1082_, lean_object* v_depth_1083_, lean_object* v_keys_1084_, lean_object* v_vals_1085_, lean_object* v_heq_1086_, lean_object* v_i_1087_, lean_object* v_entries_1088_){
_start:
{
size_t v_depth_boxed_1089_; lean_object* v_res_1090_; 
v_depth_boxed_1089_ = lean_unbox_usize(v_depth_1083_);
lean_dec(v_depth_1083_);
v_res_1090_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__9(v_00_u03b2_1082_, v_depth_boxed_1089_, v_keys_1084_, v_vals_1085_, v_heq_1086_, v_i_1087_, v_entries_1088_);
lean_dec_ref(v_vals_1085_);
lean_dec_ref(v_keys_1084_);
return v_res_1090_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__8_spec__9(lean_object* v_00_u03b2_1091_, lean_object* v_x_1092_, lean_object* v_x_1093_, lean_object* v_x_1094_, lean_object* v_x_1095_){
_start:
{
lean_object* v___x_1096_; 
v___x_1096_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__8_spec__9___redArg(v_x_1092_, v_x_1093_, v_x_1094_, v_x_1095_);
return v___x_1096_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize(lean_object* v_mvarId_1099_, lean_object* v_givenNames_1100_, lean_object* v_recursorInfo_1101_, lean_object* v_reverted_1102_, lean_object* v_major_1103_, lean_object* v_indices_1104_, lean_object* v_baseSubst_1105_, lean_object* v_recursor_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_){
_start:
{
lean_object* v___x_1112_; 
lean_inc(v_mvarId_1099_);
v___x_1112_ = l_Lean_MVarId_getType(v_mvarId_1099_, v_a_1107_, v_a_1108_, v_a_1109_, v_a_1110_);
if (lean_obj_tag(v___x_1112_) == 0)
{
lean_object* v_a_1113_; lean_object* v___x_1114_; 
v_a_1113_ = lean_ctor_get(v___x_1112_, 0);
lean_inc(v_a_1113_);
lean_dec_ref_known(v___x_1112_, 1);
lean_inc(v_a_1110_);
lean_inc_ref(v_a_1109_);
lean_inc(v_a_1108_);
lean_inc_ref(v_a_1107_);
lean_inc_ref(v_recursor_1106_);
v___x_1114_ = lean_infer_type(v_recursor_1106_, v_a_1107_, v_a_1108_, v_a_1109_, v_a_1110_);
if (lean_obj_tag(v___x_1114_) == 0)
{
lean_object* v_a_1115_; lean_object* v_paramsPos_1116_; lean_object* v_produceMotive_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; uint8_t v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; 
v_a_1115_ = lean_ctor_get(v___x_1114_, 0);
lean_inc(v_a_1115_);
lean_dec_ref_known(v___x_1114_, 1);
v_paramsPos_1116_ = lean_ctor_get(v_recursorInfo_1101_, 5);
v_produceMotive_1117_ = lean_ctor_get(v_recursorInfo_1101_, 7);
v___x_1118_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTargetArity(v_a_1113_);
v___x_1119_ = l_List_lengthTR___redArg(v_produceMotive_1117_);
v___x_1120_ = l_List_lengthTR___redArg(v_paramsPos_1116_);
v___x_1121_ = lean_unsigned_to_nat(1u);
v___x_1122_ = lean_nat_add(v___x_1120_, v___x_1121_);
lean_dec(v___x_1120_);
v___x_1123_ = lean_unsigned_to_nat(0u);
v___x_1124_ = 0;
v___x_1125_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize___closed__0));
v___x_1126_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop(v_mvarId_1099_, v_givenNames_1100_, v_recursorInfo_1101_, v_reverted_1102_, v_major_1103_, v_indices_1104_, v_baseSubst_1105_, v___x_1118_, v___x_1119_, v___x_1122_, v___x_1123_, v_recursor_1106_, v_a_1115_, v___x_1124_, v___x_1125_, v_a_1107_, v_a_1108_, v_a_1109_, v_a_1110_);
lean_dec(v___x_1119_);
lean_dec(v___x_1118_);
return v___x_1126_;
}
else
{
lean_object* v_a_1127_; lean_object* v___x_1129_; uint8_t v_isShared_1130_; uint8_t v_isSharedCheck_1134_; 
lean_dec(v_a_1113_);
lean_dec_ref(v_recursor_1106_);
lean_dec(v_baseSubst_1105_);
lean_dec_ref(v_major_1103_);
lean_dec(v_mvarId_1099_);
v_a_1127_ = lean_ctor_get(v___x_1114_, 0);
v_isSharedCheck_1134_ = !lean_is_exclusive(v___x_1114_);
if (v_isSharedCheck_1134_ == 0)
{
v___x_1129_ = v___x_1114_;
v_isShared_1130_ = v_isSharedCheck_1134_;
goto v_resetjp_1128_;
}
else
{
lean_inc(v_a_1127_);
lean_dec(v___x_1114_);
v___x_1129_ = lean_box(0);
v_isShared_1130_ = v_isSharedCheck_1134_;
goto v_resetjp_1128_;
}
v_resetjp_1128_:
{
lean_object* v___x_1132_; 
if (v_isShared_1130_ == 0)
{
v___x_1132_ = v___x_1129_;
goto v_reusejp_1131_;
}
else
{
lean_object* v_reuseFailAlloc_1133_; 
v_reuseFailAlloc_1133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1133_, 0, v_a_1127_);
v___x_1132_ = v_reuseFailAlloc_1133_;
goto v_reusejp_1131_;
}
v_reusejp_1131_:
{
return v___x_1132_;
}
}
}
}
else
{
lean_object* v_a_1135_; lean_object* v___x_1137_; uint8_t v_isShared_1138_; uint8_t v_isSharedCheck_1142_; 
lean_dec_ref(v_recursor_1106_);
lean_dec(v_baseSubst_1105_);
lean_dec_ref(v_major_1103_);
lean_dec(v_mvarId_1099_);
v_a_1135_ = lean_ctor_get(v___x_1112_, 0);
v_isSharedCheck_1142_ = !lean_is_exclusive(v___x_1112_);
if (v_isSharedCheck_1142_ == 0)
{
v___x_1137_ = v___x_1112_;
v_isShared_1138_ = v_isSharedCheck_1142_;
goto v_resetjp_1136_;
}
else
{
lean_inc(v_a_1135_);
lean_dec(v___x_1112_);
v___x_1137_ = lean_box(0);
v_isShared_1138_ = v_isSharedCheck_1142_;
goto v_resetjp_1136_;
}
v_resetjp_1136_:
{
lean_object* v___x_1140_; 
if (v_isShared_1138_ == 0)
{
v___x_1140_ = v___x_1137_;
goto v_reusejp_1139_;
}
else
{
lean_object* v_reuseFailAlloc_1141_; 
v_reuseFailAlloc_1141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1141_, 0, v_a_1135_);
v___x_1140_ = v_reuseFailAlloc_1141_;
goto v_reusejp_1139_;
}
v_reusejp_1139_:
{
return v___x_1140_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize___boxed(lean_object* v_mvarId_1143_, lean_object* v_givenNames_1144_, lean_object* v_recursorInfo_1145_, lean_object* v_reverted_1146_, lean_object* v_major_1147_, lean_object* v_indices_1148_, lean_object* v_baseSubst_1149_, lean_object* v_recursor_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_){
_start:
{
lean_object* v_res_1156_; 
v_res_1156_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize(v_mvarId_1143_, v_givenNames_1144_, v_recursorInfo_1145_, v_reverted_1146_, v_major_1147_, v_indices_1148_, v_baseSubst_1149_, v_recursor_1150_, v_a_1151_, v_a_1152_, v_a_1153_, v_a_1154_);
lean_dec(v_a_1154_);
lean_dec_ref(v_a_1153_);
lean_dec(v_a_1152_);
lean_dec_ref(v_a_1151_);
lean_dec_ref(v_indices_1148_);
lean_dec_ref(v_reverted_1146_);
lean_dec_ref(v_recursorInfo_1145_);
lean_dec_ref(v_givenNames_1144_);
return v_res_1156_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg___closed__1(void){
_start:
{
lean_object* v___x_1158_; lean_object* v___x_1159_; 
v___x_1158_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg___closed__0));
v___x_1159_ = l_Lean_stringToMessageData(v___x_1158_);
return v___x_1159_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg(lean_object* v_tacticName_1160_, lean_object* v_mvarId_1161_, lean_object* v_majorType_1162_, lean_object* v_a_1163_, lean_object* v_a_1164_, lean_object* v_a_1165_, lean_object* v_a_1166_){
_start:
{
lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; 
v___x_1168_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg___closed__1, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg___closed__1);
v___x_1169_ = l_Lean_indentExpr(v_majorType_1162_);
v___x_1170_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1170_, 0, v___x_1168_);
lean_ctor_set(v___x_1170_, 1, v___x_1169_);
v___x_1171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1171_, 0, v___x_1170_);
v___x_1172_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1160_, v_mvarId_1161_, v___x_1171_, v_a_1163_, v_a_1164_, v_a_1165_, v_a_1166_);
return v___x_1172_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg___boxed(lean_object* v_tacticName_1173_, lean_object* v_mvarId_1174_, lean_object* v_majorType_1175_, lean_object* v_a_1176_, lean_object* v_a_1177_, lean_object* v_a_1178_, lean_object* v_a_1179_, lean_object* v_a_1180_){
_start:
{
lean_object* v_res_1181_; 
v_res_1181_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg(v_tacticName_1173_, v_mvarId_1174_, v_majorType_1175_, v_a_1176_, v_a_1177_, v_a_1178_, v_a_1179_);
lean_dec(v_a_1179_);
lean_dec_ref(v_a_1178_);
lean_dec(v_a_1177_);
lean_dec_ref(v_a_1176_);
return v_res_1181_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType(lean_object* v_00_u03b1_1182_, lean_object* v_tacticName_1183_, lean_object* v_mvarId_1184_, lean_object* v_majorType_1185_, lean_object* v_a_1186_, lean_object* v_a_1187_, lean_object* v_a_1188_, lean_object* v_a_1189_){
_start:
{
lean_object* v___x_1191_; 
v___x_1191_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg(v_tacticName_1183_, v_mvarId_1184_, v_majorType_1185_, v_a_1186_, v_a_1187_, v_a_1188_, v_a_1189_);
return v___x_1191_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___boxed(lean_object* v_00_u03b1_1192_, lean_object* v_tacticName_1193_, lean_object* v_mvarId_1194_, lean_object* v_majorType_1195_, lean_object* v_a_1196_, lean_object* v_a_1197_, lean_object* v_a_1198_, lean_object* v_a_1199_, lean_object* v_a_1200_){
_start:
{
lean_object* v_res_1201_; 
v_res_1201_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType(v_00_u03b1_1192_, v_tacticName_1193_, v_mvarId_1194_, v_majorType_1195_, v_a_1196_, v_a_1197_, v_a_1198_, v_a_1199_);
lean_dec(v_a_1199_);
lean_dec_ref(v_a_1198_);
lean_dec(v_a_1197_);
lean_dec_ref(v_a_1196_);
return v_res_1201_;
}
}
LEAN_EXPORT uint8_t l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___lam__0(lean_object* v_fvarId_1202_, lean_object* v_x_1203_){
_start:
{
uint8_t v___x_1204_; 
v___x_1204_ = l_Lean_instBEqFVarId_beq(v_fvarId_1202_, v_x_1203_);
return v___x_1204_;
}
}
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___lam__0___boxed(lean_object* v_fvarId_1205_, lean_object* v_x_1206_){
_start:
{
uint8_t v_res_1207_; lean_object* v_r_1208_; 
v_res_1207_ = l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___lam__0(v_fvarId_1205_, v_x_1206_);
lean_dec(v_x_1206_);
lean_dec(v_fvarId_1205_);
v_r_1208_ = lean_box(v_res_1207_);
return v_r_1208_;
}
}
LEAN_EXPORT uint8_t l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___lam__1(lean_object* v_x_1209_){
_start:
{
uint8_t v___x_1210_; 
v___x_1210_ = 0;
return v___x_1210_;
}
}
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___lam__1___boxed(lean_object* v_x_1211_){
_start:
{
uint8_t v_res_1212_; lean_object* v_r_1213_; 
v_res_1212_ = l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___lam__1(v_x_1211_);
lean_dec(v_x_1211_);
v_r_1213_ = lean_box(v_res_1212_);
return v_r_1213_;
}
}
static lean_object* _init_l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v_cellCount_1215_; lean_object* v___x_1216_; 
v_cellCount_1215_ = lean_unsigned_to_nat(16u);
v___x_1216_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_1215_);
return v___x_1216_;
}
}
static lean_object* _init_l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v_cellCount_1217_; lean_object* v___x_1218_; 
v_cellCount_1217_ = lean_unsigned_to_nat(16u);
v___x_1218_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_1217_);
return v___x_1218_;
}
}
static lean_object* _init_l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; 
v___x_1219_ = lean_obj_once(&l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__2, &l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__2_once, _init_l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__2);
v___x_1220_ = lean_obj_once(&l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__1, &l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__1_once, _init_l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__1);
v___x_1221_ = lean_unsigned_to_nat(0u);
v___x_1222_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1222_, 0, v___x_1221_);
lean_ctor_set(v___x_1222_, 1, v___x_1220_);
lean_ctor_set(v___x_1222_, 2, v___x_1219_);
return v___x_1222_;
}
}
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg(lean_object* v_localDecl_1223_, lean_object* v_fvarId_1224_, uint8_t v_generalizeNondepLet_1225_, lean_object* v___y_1226_){
_start:
{
uint8_t v_fst_1229_; lean_object* v_snd_1230_; lean_object* v___y_1249_; lean_object* v___f_1253_; lean_object* v___f_1254_; 
v___f_1253_ = lean_alloc_closure((void*)(l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1253_, 0, v_fvarId_1224_);
v___f_1254_ = ((lean_object*)(l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__0));
if (lean_obj_tag(v_localDecl_1223_) == 0)
{
lean_object* v_type_1255_; lean_object* v___x_1256_; uint8_t v_fst_1258_; lean_object* v_mctx_1259_; lean_object* v___y_1277_; lean_object* v_mctx_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; uint8_t v___x_1285_; 
v_type_1255_ = lean_ctor_get(v_localDecl_1223_, 3);
lean_inc_ref(v_type_1255_);
lean_dec_ref_known(v_localDecl_1223_, 4);
v___x_1256_ = lean_st_ref_get(v___y_1226_);
v_mctx_1282_ = lean_ctor_get(v___x_1256_, 0);
lean_inc_ref_n(v_mctx_1282_, 2);
lean_dec(v___x_1256_);
v___x_1283_ = lean_obj_once(&l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__3, &l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__3_once, _init_l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__3);
v___x_1284_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1284_, 0, v___x_1283_);
lean_ctor_set(v___x_1284_, 1, v_mctx_1282_);
v___x_1285_ = l_Lean_Expr_hasFVar(v_type_1255_);
if (v___x_1285_ == 0)
{
uint8_t v___x_1286_; 
v___x_1286_ = l_Lean_Expr_hasMVar(v_type_1255_);
if (v___x_1286_ == 0)
{
lean_dec_ref_known(v___x_1284_, 2);
lean_dec_ref(v_type_1255_);
lean_dec_ref(v___f_1253_);
v_fst_1258_ = v___x_1286_;
v_mctx_1259_ = v_mctx_1282_;
goto v___jp_1257_;
}
else
{
lean_object* v___x_1287_; 
lean_dec_ref(v_mctx_1282_);
v___x_1287_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1253_, v___f_1254_, v_type_1255_, v___x_1284_);
v___y_1277_ = v___x_1287_;
goto v___jp_1276_;
}
}
else
{
lean_object* v___x_1288_; 
lean_dec_ref(v_mctx_1282_);
v___x_1288_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1253_, v___f_1254_, v_type_1255_, v___x_1284_);
v___y_1277_ = v___x_1288_;
goto v___jp_1276_;
}
v___jp_1257_:
{
lean_object* v___x_1260_; lean_object* v_cache_1261_; lean_object* v_zetaDeltaFVarIds_1262_; lean_object* v_postponed_1263_; lean_object* v_diag_1264_; lean_object* v___x_1266_; uint8_t v_isShared_1267_; uint8_t v_isSharedCheck_1274_; 
v___x_1260_ = lean_st_ref_take(v___y_1226_);
v_cache_1261_ = lean_ctor_get(v___x_1260_, 1);
v_zetaDeltaFVarIds_1262_ = lean_ctor_get(v___x_1260_, 2);
v_postponed_1263_ = lean_ctor_get(v___x_1260_, 3);
v_diag_1264_ = lean_ctor_get(v___x_1260_, 4);
v_isSharedCheck_1274_ = !lean_is_exclusive(v___x_1260_);
if (v_isSharedCheck_1274_ == 0)
{
lean_object* v_unused_1275_; 
v_unused_1275_ = lean_ctor_get(v___x_1260_, 0);
lean_dec(v_unused_1275_);
v___x_1266_ = v___x_1260_;
v_isShared_1267_ = v_isSharedCheck_1274_;
goto v_resetjp_1265_;
}
else
{
lean_inc(v_diag_1264_);
lean_inc(v_postponed_1263_);
lean_inc(v_zetaDeltaFVarIds_1262_);
lean_inc(v_cache_1261_);
lean_dec(v___x_1260_);
v___x_1266_ = lean_box(0);
v_isShared_1267_ = v_isSharedCheck_1274_;
goto v_resetjp_1265_;
}
v_resetjp_1265_:
{
lean_object* v___x_1269_; 
if (v_isShared_1267_ == 0)
{
lean_ctor_set(v___x_1266_, 0, v_mctx_1259_);
v___x_1269_ = v___x_1266_;
goto v_reusejp_1268_;
}
else
{
lean_object* v_reuseFailAlloc_1273_; 
v_reuseFailAlloc_1273_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1273_, 0, v_mctx_1259_);
lean_ctor_set(v_reuseFailAlloc_1273_, 1, v_cache_1261_);
lean_ctor_set(v_reuseFailAlloc_1273_, 2, v_zetaDeltaFVarIds_1262_);
lean_ctor_set(v_reuseFailAlloc_1273_, 3, v_postponed_1263_);
lean_ctor_set(v_reuseFailAlloc_1273_, 4, v_diag_1264_);
v___x_1269_ = v_reuseFailAlloc_1273_;
goto v_reusejp_1268_;
}
v_reusejp_1268_:
{
lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; 
v___x_1270_ = lean_st_ref_put(v___y_1226_, v___x_1269_);
v___x_1271_ = lean_box(v_fst_1258_);
v___x_1272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1272_, 0, v___x_1271_);
return v___x_1272_;
}
}
}
v___jp_1276_:
{
lean_object* v_snd_1278_; lean_object* v_fst_1279_; lean_object* v_mctx_1280_; uint8_t v___x_1281_; 
v_snd_1278_ = lean_ctor_get(v___y_1277_, 1);
lean_inc(v_snd_1278_);
v_fst_1279_ = lean_ctor_get(v___y_1277_, 0);
lean_inc(v_fst_1279_);
lean_dec_ref(v___y_1277_);
v_mctx_1280_ = lean_ctor_get(v_snd_1278_, 1);
lean_inc_ref(v_mctx_1280_);
lean_dec(v_snd_1278_);
v___x_1281_ = lean_unbox(v_fst_1279_);
lean_dec(v_fst_1279_);
v_fst_1258_ = v___x_1281_;
v_mctx_1259_ = v_mctx_1280_;
goto v___jp_1257_;
}
}
else
{
lean_object* v_type_1289_; lean_object* v_value_1290_; uint8_t v_nondep_1291_; uint8_t v_fst_1293_; lean_object* v_snd_1294_; lean_object* v___y_1300_; 
v_type_1289_ = lean_ctor_get(v_localDecl_1223_, 3);
lean_inc_ref(v_type_1289_);
v_value_1290_ = lean_ctor_get(v_localDecl_1223_, 4);
lean_inc_ref(v_value_1290_);
v_nondep_1291_ = lean_ctor_get_uint8(v_localDecl_1223_, sizeof(void*)*5);
lean_dec_ref_known(v_localDecl_1223_, 5);
if (v_generalizeNondepLet_1225_ == 0)
{
goto v___jp_1304_;
}
else
{
if (v_nondep_1291_ == 0)
{
goto v___jp_1304_;
}
else
{
lean_object* v___x_1313_; uint8_t v_fst_1315_; lean_object* v_mctx_1316_; lean_object* v___y_1334_; lean_object* v_mctx_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; uint8_t v___x_1342_; 
lean_dec_ref(v_value_1290_);
v___x_1313_ = lean_st_ref_get(v___y_1226_);
v_mctx_1339_ = lean_ctor_get(v___x_1313_, 0);
lean_inc_ref_n(v_mctx_1339_, 2);
lean_dec(v___x_1313_);
v___x_1340_ = lean_obj_once(&l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__3, &l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__3_once, _init_l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__3);
v___x_1341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1341_, 0, v___x_1340_);
lean_ctor_set(v___x_1341_, 1, v_mctx_1339_);
v___x_1342_ = l_Lean_Expr_hasFVar(v_type_1289_);
if (v___x_1342_ == 0)
{
uint8_t v___x_1343_; 
v___x_1343_ = l_Lean_Expr_hasMVar(v_type_1289_);
if (v___x_1343_ == 0)
{
lean_dec_ref_known(v___x_1341_, 2);
lean_dec_ref(v_type_1289_);
lean_dec_ref(v___f_1253_);
v_fst_1315_ = v___x_1343_;
v_mctx_1316_ = v_mctx_1339_;
goto v___jp_1314_;
}
else
{
lean_object* v___x_1344_; 
lean_dec_ref(v_mctx_1339_);
v___x_1344_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1253_, v___f_1254_, v_type_1289_, v___x_1341_);
v___y_1334_ = v___x_1344_;
goto v___jp_1333_;
}
}
else
{
lean_object* v___x_1345_; 
lean_dec_ref(v_mctx_1339_);
v___x_1345_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1253_, v___f_1254_, v_type_1289_, v___x_1341_);
v___y_1334_ = v___x_1345_;
goto v___jp_1333_;
}
v___jp_1314_:
{
lean_object* v___x_1317_; lean_object* v_cache_1318_; lean_object* v_zetaDeltaFVarIds_1319_; lean_object* v_postponed_1320_; lean_object* v_diag_1321_; lean_object* v___x_1323_; uint8_t v_isShared_1324_; uint8_t v_isSharedCheck_1331_; 
v___x_1317_ = lean_st_ref_take(v___y_1226_);
v_cache_1318_ = lean_ctor_get(v___x_1317_, 1);
v_zetaDeltaFVarIds_1319_ = lean_ctor_get(v___x_1317_, 2);
v_postponed_1320_ = lean_ctor_get(v___x_1317_, 3);
v_diag_1321_ = lean_ctor_get(v___x_1317_, 4);
v_isSharedCheck_1331_ = !lean_is_exclusive(v___x_1317_);
if (v_isSharedCheck_1331_ == 0)
{
lean_object* v_unused_1332_; 
v_unused_1332_ = lean_ctor_get(v___x_1317_, 0);
lean_dec(v_unused_1332_);
v___x_1323_ = v___x_1317_;
v_isShared_1324_ = v_isSharedCheck_1331_;
goto v_resetjp_1322_;
}
else
{
lean_inc(v_diag_1321_);
lean_inc(v_postponed_1320_);
lean_inc(v_zetaDeltaFVarIds_1319_);
lean_inc(v_cache_1318_);
lean_dec(v___x_1317_);
v___x_1323_ = lean_box(0);
v_isShared_1324_ = v_isSharedCheck_1331_;
goto v_resetjp_1322_;
}
v_resetjp_1322_:
{
lean_object* v___x_1326_; 
if (v_isShared_1324_ == 0)
{
lean_ctor_set(v___x_1323_, 0, v_mctx_1316_);
v___x_1326_ = v___x_1323_;
goto v_reusejp_1325_;
}
else
{
lean_object* v_reuseFailAlloc_1330_; 
v_reuseFailAlloc_1330_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1330_, 0, v_mctx_1316_);
lean_ctor_set(v_reuseFailAlloc_1330_, 1, v_cache_1318_);
lean_ctor_set(v_reuseFailAlloc_1330_, 2, v_zetaDeltaFVarIds_1319_);
lean_ctor_set(v_reuseFailAlloc_1330_, 3, v_postponed_1320_);
lean_ctor_set(v_reuseFailAlloc_1330_, 4, v_diag_1321_);
v___x_1326_ = v_reuseFailAlloc_1330_;
goto v_reusejp_1325_;
}
v_reusejp_1325_:
{
lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; 
v___x_1327_ = lean_st_ref_put(v___y_1226_, v___x_1326_);
v___x_1328_ = lean_box(v_fst_1315_);
v___x_1329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1329_, 0, v___x_1328_);
return v___x_1329_;
}
}
}
v___jp_1333_:
{
lean_object* v_snd_1335_; lean_object* v_fst_1336_; lean_object* v_mctx_1337_; uint8_t v___x_1338_; 
v_snd_1335_ = lean_ctor_get(v___y_1334_, 1);
lean_inc(v_snd_1335_);
v_fst_1336_ = lean_ctor_get(v___y_1334_, 0);
lean_inc(v_fst_1336_);
lean_dec_ref(v___y_1334_);
v_mctx_1337_ = lean_ctor_get(v_snd_1335_, 1);
lean_inc_ref(v_mctx_1337_);
lean_dec(v_snd_1335_);
v___x_1338_ = lean_unbox(v_fst_1336_);
lean_dec(v_fst_1336_);
v_fst_1315_ = v___x_1338_;
v_mctx_1316_ = v_mctx_1337_;
goto v___jp_1314_;
}
}
}
v___jp_1292_:
{
if (v_fst_1293_ == 0)
{
uint8_t v___x_1295_; 
v___x_1295_ = l_Lean_Expr_hasFVar(v_value_1290_);
if (v___x_1295_ == 0)
{
uint8_t v___x_1296_; 
v___x_1296_ = l_Lean_Expr_hasMVar(v_value_1290_);
if (v___x_1296_ == 0)
{
lean_dec_ref(v_value_1290_);
lean_dec_ref(v___f_1253_);
v_fst_1229_ = v___x_1296_;
v_snd_1230_ = v_snd_1294_;
goto v___jp_1228_;
}
else
{
lean_object* v___x_1297_; 
v___x_1297_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1253_, v___f_1254_, v_value_1290_, v_snd_1294_);
v___y_1249_ = v___x_1297_;
goto v___jp_1248_;
}
}
else
{
lean_object* v___x_1298_; 
v___x_1298_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1253_, v___f_1254_, v_value_1290_, v_snd_1294_);
v___y_1249_ = v___x_1298_;
goto v___jp_1248_;
}
}
else
{
lean_dec_ref(v_value_1290_);
lean_dec_ref(v___f_1253_);
v_fst_1229_ = v_fst_1293_;
v_snd_1230_ = v_snd_1294_;
goto v___jp_1228_;
}
}
v___jp_1299_:
{
lean_object* v_fst_1301_; lean_object* v_snd_1302_; uint8_t v___x_1303_; 
v_fst_1301_ = lean_ctor_get(v___y_1300_, 0);
lean_inc(v_fst_1301_);
v_snd_1302_ = lean_ctor_get(v___y_1300_, 1);
lean_inc(v_snd_1302_);
lean_dec_ref(v___y_1300_);
v___x_1303_ = lean_unbox(v_fst_1301_);
lean_dec(v_fst_1301_);
v_fst_1293_ = v___x_1303_;
v_snd_1294_ = v_snd_1302_;
goto v___jp_1292_;
}
v___jp_1304_:
{
lean_object* v___x_1305_; lean_object* v_mctx_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; uint8_t v___x_1309_; 
v___x_1305_ = lean_st_ref_get(v___y_1226_);
v_mctx_1306_ = lean_ctor_get(v___x_1305_, 0);
lean_inc_ref(v_mctx_1306_);
lean_dec(v___x_1305_);
v___x_1307_ = lean_obj_once(&l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__3, &l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__3_once, _init_l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__3);
v___x_1308_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1308_, 0, v___x_1307_);
lean_ctor_set(v___x_1308_, 1, v_mctx_1306_);
v___x_1309_ = l_Lean_Expr_hasFVar(v_type_1289_);
if (v___x_1309_ == 0)
{
uint8_t v___x_1310_; 
v___x_1310_ = l_Lean_Expr_hasMVar(v_type_1289_);
if (v___x_1310_ == 0)
{
lean_dec_ref(v_type_1289_);
v_fst_1293_ = v___x_1310_;
v_snd_1294_ = v___x_1308_;
goto v___jp_1292_;
}
else
{
lean_object* v___x_1311_; 
lean_inc_ref(v___f_1253_);
v___x_1311_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1253_, v___f_1254_, v_type_1289_, v___x_1308_);
v___y_1300_ = v___x_1311_;
goto v___jp_1299_;
}
}
else
{
lean_object* v___x_1312_; 
lean_inc_ref(v___f_1253_);
v___x_1312_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1253_, v___f_1254_, v_type_1289_, v___x_1308_);
v___y_1300_ = v___x_1312_;
goto v___jp_1299_;
}
}
}
v___jp_1228_:
{
lean_object* v_mctx_1231_; lean_object* v___x_1232_; lean_object* v_cache_1233_; lean_object* v_zetaDeltaFVarIds_1234_; lean_object* v_postponed_1235_; lean_object* v_diag_1236_; lean_object* v___x_1238_; uint8_t v_isShared_1239_; uint8_t v_isSharedCheck_1246_; 
v_mctx_1231_ = lean_ctor_get(v_snd_1230_, 1);
lean_inc_ref(v_mctx_1231_);
lean_dec_ref(v_snd_1230_);
v___x_1232_ = lean_st_ref_take(v___y_1226_);
v_cache_1233_ = lean_ctor_get(v___x_1232_, 1);
v_zetaDeltaFVarIds_1234_ = lean_ctor_get(v___x_1232_, 2);
v_postponed_1235_ = lean_ctor_get(v___x_1232_, 3);
v_diag_1236_ = lean_ctor_get(v___x_1232_, 4);
v_isSharedCheck_1246_ = !lean_is_exclusive(v___x_1232_);
if (v_isSharedCheck_1246_ == 0)
{
lean_object* v_unused_1247_; 
v_unused_1247_ = lean_ctor_get(v___x_1232_, 0);
lean_dec(v_unused_1247_);
v___x_1238_ = v___x_1232_;
v_isShared_1239_ = v_isSharedCheck_1246_;
goto v_resetjp_1237_;
}
else
{
lean_inc(v_diag_1236_);
lean_inc(v_postponed_1235_);
lean_inc(v_zetaDeltaFVarIds_1234_);
lean_inc(v_cache_1233_);
lean_dec(v___x_1232_);
v___x_1238_ = lean_box(0);
v_isShared_1239_ = v_isSharedCheck_1246_;
goto v_resetjp_1237_;
}
v_resetjp_1237_:
{
lean_object* v___x_1241_; 
if (v_isShared_1239_ == 0)
{
lean_ctor_set(v___x_1238_, 0, v_mctx_1231_);
v___x_1241_ = v___x_1238_;
goto v_reusejp_1240_;
}
else
{
lean_object* v_reuseFailAlloc_1245_; 
v_reuseFailAlloc_1245_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1245_, 0, v_mctx_1231_);
lean_ctor_set(v_reuseFailAlloc_1245_, 1, v_cache_1233_);
lean_ctor_set(v_reuseFailAlloc_1245_, 2, v_zetaDeltaFVarIds_1234_);
lean_ctor_set(v_reuseFailAlloc_1245_, 3, v_postponed_1235_);
lean_ctor_set(v_reuseFailAlloc_1245_, 4, v_diag_1236_);
v___x_1241_ = v_reuseFailAlloc_1245_;
goto v_reusejp_1240_;
}
v_reusejp_1240_:
{
lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; 
v___x_1242_ = lean_st_ref_put(v___y_1226_, v___x_1241_);
v___x_1243_ = lean_box(v_fst_1229_);
v___x_1244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1244_, 0, v___x_1243_);
return v___x_1244_;
}
}
}
v___jp_1248_:
{
lean_object* v_fst_1250_; lean_object* v_snd_1251_; uint8_t v___x_1252_; 
v_fst_1250_ = lean_ctor_get(v___y_1249_, 0);
lean_inc(v_fst_1250_);
v_snd_1251_ = lean_ctor_get(v___y_1249_, 1);
lean_inc(v_snd_1251_);
lean_dec_ref(v___y_1249_);
v___x_1252_ = lean_unbox(v_fst_1250_);
lean_dec(v_fst_1250_);
v_fst_1229_ = v___x_1252_;
v_snd_1230_ = v_snd_1251_;
goto v___jp_1228_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___boxed(lean_object* v_localDecl_1346_, lean_object* v_fvarId_1347_, lean_object* v_generalizeNondepLet_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_){
_start:
{
uint8_t v_generalizeNondepLet_boxed_1351_; lean_object* v_res_1352_; 
v_generalizeNondepLet_boxed_1351_ = lean_unbox(v_generalizeNondepLet_1348_);
v_res_1352_ = l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg(v_localDecl_1346_, v_fvarId_1347_, v_generalizeNondepLet_boxed_1351_, v___y_1349_);
lean_dec(v___y_1349_);
return v_res_1352_;
}
}
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0(lean_object* v_localDecl_1353_, lean_object* v_fvarId_1354_, uint8_t v_generalizeNondepLet_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_){
_start:
{
lean_object* v___x_1361_; 
v___x_1361_ = l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg(v_localDecl_1353_, v_fvarId_1354_, v_generalizeNondepLet_1355_, v___y_1357_);
return v___x_1361_;
}
}
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___boxed(lean_object* v_localDecl_1362_, lean_object* v_fvarId_1363_, lean_object* v_generalizeNondepLet_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_){
_start:
{
uint8_t v_generalizeNondepLet_boxed_1370_; lean_object* v_res_1371_; 
v_generalizeNondepLet_boxed_1370_ = lean_unbox(v_generalizeNondepLet_1364_);
v_res_1371_ = l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0(v_localDecl_1362_, v_fvarId_1363_, v_generalizeNondepLet_boxed_1370_, v___y_1365_, v___y_1366_, v___y_1367_, v___y_1368_);
lean_dec(v___y_1368_);
lean_dec_ref(v___y_1367_);
lean_dec(v___y_1366_);
lean_dec_ref(v___y_1365_);
return v_res_1371_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2___redArg(lean_object* v_e_1372_, lean_object* v_fvarId_1373_, lean_object* v___y_1374_){
_start:
{
lean_object* v___x_1376_; uint8_t v_fst_1378_; lean_object* v_mctx_1379_; lean_object* v___y_1397_; lean_object* v_mctx_1402_; lean_object* v___f_1403_; lean_object* v___f_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; uint8_t v___x_1407_; 
v___x_1376_ = lean_st_ref_get(v___y_1374_);
v_mctx_1402_ = lean_ctor_get(v___x_1376_, 0);
lean_inc_ref_n(v_mctx_1402_, 2);
lean_dec(v___x_1376_);
v___f_1403_ = ((lean_object*)(l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__0));
v___f_1404_ = lean_alloc_closure((void*)(l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1404_, 0, v_fvarId_1373_);
v___x_1405_ = lean_obj_once(&l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__3, &l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__3_once, _init_l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__3);
v___x_1406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1406_, 0, v___x_1405_);
lean_ctor_set(v___x_1406_, 1, v_mctx_1402_);
v___x_1407_ = l_Lean_Expr_hasFVar(v_e_1372_);
if (v___x_1407_ == 0)
{
uint8_t v___x_1408_; 
v___x_1408_ = l_Lean_Expr_hasMVar(v_e_1372_);
if (v___x_1408_ == 0)
{
lean_dec_ref_known(v___x_1406_, 2);
lean_dec_ref(v___f_1404_);
lean_dec_ref(v_e_1372_);
v_fst_1378_ = v___x_1408_;
v_mctx_1379_ = v_mctx_1402_;
goto v___jp_1377_;
}
else
{
lean_object* v___x_1409_; 
lean_dec_ref(v_mctx_1402_);
v___x_1409_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1404_, v___f_1403_, v_e_1372_, v___x_1406_);
v___y_1397_ = v___x_1409_;
goto v___jp_1396_;
}
}
else
{
lean_object* v___x_1410_; 
lean_dec_ref(v_mctx_1402_);
v___x_1410_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1404_, v___f_1403_, v_e_1372_, v___x_1406_);
v___y_1397_ = v___x_1410_;
goto v___jp_1396_;
}
v___jp_1377_:
{
lean_object* v___x_1380_; lean_object* v_cache_1381_; lean_object* v_zetaDeltaFVarIds_1382_; lean_object* v_postponed_1383_; lean_object* v_diag_1384_; lean_object* v___x_1386_; uint8_t v_isShared_1387_; uint8_t v_isSharedCheck_1394_; 
v___x_1380_ = lean_st_ref_take(v___y_1374_);
v_cache_1381_ = lean_ctor_get(v___x_1380_, 1);
v_zetaDeltaFVarIds_1382_ = lean_ctor_get(v___x_1380_, 2);
v_postponed_1383_ = lean_ctor_get(v___x_1380_, 3);
v_diag_1384_ = lean_ctor_get(v___x_1380_, 4);
v_isSharedCheck_1394_ = !lean_is_exclusive(v___x_1380_);
if (v_isSharedCheck_1394_ == 0)
{
lean_object* v_unused_1395_; 
v_unused_1395_ = lean_ctor_get(v___x_1380_, 0);
lean_dec(v_unused_1395_);
v___x_1386_ = v___x_1380_;
v_isShared_1387_ = v_isSharedCheck_1394_;
goto v_resetjp_1385_;
}
else
{
lean_inc(v_diag_1384_);
lean_inc(v_postponed_1383_);
lean_inc(v_zetaDeltaFVarIds_1382_);
lean_inc(v_cache_1381_);
lean_dec(v___x_1380_);
v___x_1386_ = lean_box(0);
v_isShared_1387_ = v_isSharedCheck_1394_;
goto v_resetjp_1385_;
}
v_resetjp_1385_:
{
lean_object* v___x_1389_; 
if (v_isShared_1387_ == 0)
{
lean_ctor_set(v___x_1386_, 0, v_mctx_1379_);
v___x_1389_ = v___x_1386_;
goto v_reusejp_1388_;
}
else
{
lean_object* v_reuseFailAlloc_1393_; 
v_reuseFailAlloc_1393_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1393_, 0, v_mctx_1379_);
lean_ctor_set(v_reuseFailAlloc_1393_, 1, v_cache_1381_);
lean_ctor_set(v_reuseFailAlloc_1393_, 2, v_zetaDeltaFVarIds_1382_);
lean_ctor_set(v_reuseFailAlloc_1393_, 3, v_postponed_1383_);
lean_ctor_set(v_reuseFailAlloc_1393_, 4, v_diag_1384_);
v___x_1389_ = v_reuseFailAlloc_1393_;
goto v_reusejp_1388_;
}
v_reusejp_1388_:
{
lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; 
v___x_1390_ = lean_st_ref_put(v___y_1374_, v___x_1389_);
v___x_1391_ = lean_box(v_fst_1378_);
v___x_1392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1392_, 0, v___x_1391_);
return v___x_1392_;
}
}
}
v___jp_1396_:
{
lean_object* v_snd_1398_; lean_object* v_fst_1399_; lean_object* v_mctx_1400_; uint8_t v___x_1401_; 
v_snd_1398_ = lean_ctor_get(v___y_1397_, 1);
lean_inc(v_snd_1398_);
v_fst_1399_ = lean_ctor_get(v___y_1397_, 0);
lean_inc(v_fst_1399_);
lean_dec_ref(v___y_1397_);
v_mctx_1400_ = lean_ctor_get(v_snd_1398_, 1);
lean_inc_ref(v_mctx_1400_);
lean_dec(v_snd_1398_);
v___x_1401_ = lean_unbox(v_fst_1399_);
lean_dec(v_fst_1399_);
v_fst_1378_ = v___x_1401_;
v_mctx_1379_ = v_mctx_1400_;
goto v___jp_1377_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2___redArg___boxed(lean_object* v_e_1411_, lean_object* v_fvarId_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_){
_start:
{
lean_object* v_res_1415_; 
v_res_1415_ = l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2___redArg(v_e_1411_, v_fvarId_1412_, v___y_1413_);
lean_dec(v___y_1413_);
return v_res_1415_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2(lean_object* v_e_1416_, lean_object* v_fvarId_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_){
_start:
{
lean_object* v___x_1423_; 
v___x_1423_ = l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2___redArg(v_e_1416_, v_fvarId_1417_, v___y_1419_);
return v___x_1423_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2___boxed(lean_object* v_e_1424_, lean_object* v_fvarId_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_){
_start:
{
lean_object* v_res_1431_; 
v_res_1431_ = l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2(v_e_1424_, v_fvarId_1425_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_);
lean_dec(v___y_1429_);
lean_dec_ref(v___y_1428_);
lean_dec(v___y_1427_);
lean_dec_ref(v___y_1426_);
return v_res_1431_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_Meta_getMajorTypeIndices_spec__1(lean_object* v_a_1432_, lean_object* v_x_1433_){
_start:
{
if (lean_obj_tag(v_x_1433_) == 0)
{
uint8_t v___x_1434_; 
v___x_1434_ = 0;
return v___x_1434_;
}
else
{
lean_object* v_head_1435_; lean_object* v_tail_1436_; uint8_t v___x_1437_; 
v_head_1435_ = lean_ctor_get(v_x_1433_, 0);
v_tail_1436_ = lean_ctor_get(v_x_1433_, 1);
v___x_1437_ = lean_nat_dec_eq(v_a_1432_, v_head_1435_);
if (v___x_1437_ == 0)
{
v_x_1433_ = v_tail_1436_;
goto _start;
}
else
{
return v___x_1437_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_Meta_getMajorTypeIndices_spec__1___boxed(lean_object* v_a_1439_, lean_object* v_x_1440_){
_start:
{
uint8_t v_res_1441_; lean_object* v_r_1442_; 
v_res_1441_ = l_List_elem___at___00Lean_Meta_getMajorTypeIndices_spec__1(v_a_1439_, v_x_1440_);
lean_dec(v_x_1440_);
lean_dec(v_a_1439_);
v_r_1442_ = lean_box(v_res_1441_);
return v_r_1442_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_1444_; lean_object* v___x_1445_; 
v___x_1444_ = ((lean_object*)(l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__0));
v___x_1445_ = l_Lean_stringToMessageData(v___x_1444_);
return v___x_1445_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_1447_; lean_object* v___x_1448_; 
v___x_1447_ = ((lean_object*)(l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__2));
v___x_1448_ = l_Lean_stringToMessageData(v___x_1447_);
return v___x_1448_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__5(void){
_start:
{
lean_object* v___x_1450_; lean_object* v___x_1451_; 
v___x_1450_ = ((lean_object*)(l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__4));
v___x_1451_ = l_Lean_stringToMessageData(v___x_1450_);
return v___x_1451_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__7(void){
_start:
{
lean_object* v___x_1453_; lean_object* v___x_1454_; 
v___x_1453_ = ((lean_object*)(l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__6));
v___x_1454_ = l_Lean_stringToMessageData(v___x_1453_);
return v___x_1454_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg(lean_object* v_majorTypeArgs_1455_, lean_object* v_idx_1456_, lean_object* v_tacticName_1457_, lean_object* v_mvarId_1458_, lean_object* v_idxPos_1459_, lean_object* v_recursorInfo_1460_, lean_object* v_majorType_1461_, lean_object* v_n_1462_, lean_object* v_i_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_){
_start:
{
lean_object* v_zero_1469_; uint8_t v_isZero_1470_; 
v_zero_1469_ = lean_unsigned_to_nat(0u);
v_isZero_1470_ = lean_nat_dec_eq(v_i_1463_, v_zero_1469_);
if (v_isZero_1470_ == 1)
{
lean_object* v___x_1471_; lean_object* v___x_1472_; 
lean_dec(v_i_1463_);
lean_dec_ref(v_majorType_1461_);
lean_dec(v_mvarId_1458_);
lean_dec(v_tacticName_1457_);
lean_dec_ref(v_idx_1456_);
v___x_1471_ = lean_box(0);
v___x_1472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1472_, 0, v___x_1471_);
return v___x_1472_;
}
else
{
lean_object* v_one_1473_; lean_object* v_n_1474_; lean_object* v___y_1476_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v_arg_1480_; lean_object* v___y_1482_; lean_object* v___y_1483_; lean_object* v___y_1484_; lean_object* v___y_1485_; uint8_t v___y_1486_; lean_object* v___y_1525_; lean_object* v___y_1526_; lean_object* v___y_1527_; lean_object* v___y_1528_; lean_object* v___y_1533_; lean_object* v___y_1534_; lean_object* v___y_1535_; lean_object* v___y_1536_; uint8_t v___x_1557_; 
v_one_1473_ = lean_unsigned_to_nat(1u);
v_n_1474_ = lean_nat_sub(v_i_1463_, v_one_1473_);
lean_dec(v_i_1463_);
v___x_1478_ = lean_nat_sub(v_n_1462_, v_n_1474_);
v___x_1479_ = lean_nat_sub(v___x_1478_, v_one_1473_);
lean_dec(v___x_1478_);
v_arg_1480_ = lean_array_fget_borrowed(v_majorTypeArgs_1455_, v___x_1479_);
v___x_1557_ = lean_nat_dec_eq(v___x_1479_, v_idxPos_1459_);
if (v___x_1557_ == 0)
{
uint8_t v___x_1558_; 
v___x_1558_ = lean_expr_eqv(v_arg_1480_, v_idx_1456_);
if (v___x_1558_ == 0)
{
v___y_1533_ = v___y_1464_;
v___y_1534_ = v___y_1465_;
v___y_1535_ = v___y_1466_;
v___y_1536_ = v___y_1467_;
goto v___jp_1532_;
}
else
{
lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; 
v___x_1559_ = lean_obj_once(&l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1, &l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1_once, _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1);
lean_inc_ref(v_idx_1456_);
v___x_1560_ = l_Lean_MessageData_ofExpr(v_idx_1456_);
v___x_1561_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1561_, 0, v___x_1559_);
lean_ctor_set(v___x_1561_, 1, v___x_1560_);
v___x_1562_ = lean_obj_once(&l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__7, &l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__7_once, _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__7);
v___x_1563_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1563_, 0, v___x_1561_);
lean_ctor_set(v___x_1563_, 1, v___x_1562_);
lean_inc_ref(v_majorType_1461_);
v___x_1564_ = l_Lean_indentExpr(v_majorType_1461_);
v___x_1565_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1565_, 0, v___x_1563_);
lean_ctor_set(v___x_1565_, 1, v___x_1564_);
v___x_1566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1566_, 0, v___x_1565_);
lean_inc(v_mvarId_1458_);
lean_inc(v_tacticName_1457_);
v___x_1567_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1457_, v_mvarId_1458_, v___x_1566_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1467_);
if (lean_obj_tag(v___x_1567_) == 0)
{
lean_dec_ref_known(v___x_1567_, 1);
v___y_1533_ = v___y_1464_;
v___y_1534_ = v___y_1465_;
v___y_1535_ = v___y_1466_;
v___y_1536_ = v___y_1467_;
goto v___jp_1532_;
}
else
{
lean_dec(v___x_1479_);
v___y_1476_ = v___x_1567_;
goto v___jp_1475_;
}
}
}
else
{
v___y_1533_ = v___y_1464_;
v___y_1534_ = v___y_1465_;
v___y_1535_ = v___y_1466_;
v___y_1536_ = v___y_1467_;
goto v___jp_1532_;
}
v___jp_1475_:
{
if (lean_obj_tag(v___y_1476_) == 0)
{
lean_dec_ref_known(v___y_1476_, 1);
v_i_1463_ = v_n_1474_;
goto _start;
}
else
{
lean_dec(v_n_1474_);
lean_dec_ref(v_majorType_1461_);
lean_dec(v_mvarId_1458_);
lean_dec(v_tacticName_1457_);
lean_dec_ref(v_idx_1456_);
return v___y_1476_;
}
}
v___jp_1481_:
{
if (v___y_1486_ == 0)
{
lean_dec(v___x_1479_);
v_i_1463_ = v_n_1474_;
goto _start;
}
else
{
uint8_t v___x_1488_; 
v___x_1488_ = l_Lean_Expr_isFVar(v_arg_1480_);
if (v___x_1488_ == 0)
{
lean_dec(v___x_1479_);
v_i_1463_ = v_n_1474_;
goto _start;
}
else
{
lean_object* v___x_1490_; lean_object* v___x_1491_; 
v___x_1490_ = l_Lean_Expr_fvarId_x21(v_idx_1456_);
v___x_1491_ = l_Lean_FVarId_getDecl___redArg(v___x_1490_, v___y_1484_, v___y_1483_, v___y_1485_);
if (lean_obj_tag(v___x_1491_) == 0)
{
lean_object* v_a_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v_a_1495_; lean_object* v___x_1497_; uint8_t v_isShared_1498_; uint8_t v_isSharedCheck_1515_; 
v_a_1492_ = lean_ctor_get(v___x_1491_, 0);
lean_inc(v_a_1492_);
lean_dec_ref_known(v___x_1491_, 1);
v___x_1493_ = l_Lean_Expr_fvarId_x21(v_arg_1480_);
v___x_1494_ = l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg(v_a_1492_, v___x_1493_, v___y_1486_, v___y_1482_);
v_a_1495_ = lean_ctor_get(v___x_1494_, 0);
v_isSharedCheck_1515_ = !lean_is_exclusive(v___x_1494_);
if (v_isSharedCheck_1515_ == 0)
{
v___x_1497_ = v___x_1494_;
v_isShared_1498_ = v_isSharedCheck_1515_;
goto v_resetjp_1496_;
}
else
{
lean_inc(v_a_1495_);
lean_dec(v___x_1494_);
v___x_1497_ = lean_box(0);
v_isShared_1498_ = v_isSharedCheck_1515_;
goto v_resetjp_1496_;
}
v_resetjp_1496_:
{
uint8_t v___x_1499_; 
v___x_1499_ = lean_unbox(v_a_1495_);
lean_dec(v_a_1495_);
if (v___x_1499_ == 0)
{
lean_del_object(v___x_1497_);
lean_dec(v___x_1479_);
v_i_1463_ = v_n_1474_;
goto _start;
}
else
{
lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1509_; 
v___x_1501_ = lean_obj_once(&l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1, &l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1_once, _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1);
lean_inc_ref(v_idx_1456_);
v___x_1502_ = l_Lean_MessageData_ofExpr(v_idx_1456_);
v___x_1503_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1503_, 0, v___x_1501_);
lean_ctor_set(v___x_1503_, 1, v___x_1502_);
v___x_1504_ = lean_obj_once(&l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__3, &l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__3_once, _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__3);
v___x_1505_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1505_, 0, v___x_1503_);
lean_ctor_set(v___x_1505_, 1, v___x_1504_);
v___x_1506_ = lean_nat_add(v___x_1479_, v_one_1473_);
lean_dec(v___x_1479_);
v___x_1507_ = l_Nat_reprFast(v___x_1506_);
if (v_isShared_1498_ == 0)
{
lean_ctor_set_tag(v___x_1497_, 3);
lean_ctor_set(v___x_1497_, 0, v___x_1507_);
v___x_1509_ = v___x_1497_;
goto v_reusejp_1508_;
}
else
{
lean_object* v_reuseFailAlloc_1514_; 
v_reuseFailAlloc_1514_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1514_, 0, v___x_1507_);
v___x_1509_ = v_reuseFailAlloc_1514_;
goto v_reusejp_1508_;
}
v_reusejp_1508_:
{
lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; 
v___x_1510_ = l_Lean_MessageData_ofFormat(v___x_1509_);
v___x_1511_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1511_, 0, v___x_1505_);
lean_ctor_set(v___x_1511_, 1, v___x_1510_);
v___x_1512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1512_, 0, v___x_1511_);
lean_inc(v_mvarId_1458_);
lean_inc(v_tacticName_1457_);
v___x_1513_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1457_, v_mvarId_1458_, v___x_1512_, v___y_1484_, v___y_1482_, v___y_1483_, v___y_1485_);
v___y_1476_ = v___x_1513_;
goto v___jp_1475_;
}
}
}
}
else
{
lean_object* v_a_1516_; lean_object* v___x_1518_; uint8_t v_isShared_1519_; uint8_t v_isSharedCheck_1523_; 
lean_dec(v___x_1479_);
lean_dec(v_n_1474_);
lean_dec_ref(v_majorType_1461_);
lean_dec(v_mvarId_1458_);
lean_dec(v_tacticName_1457_);
lean_dec_ref(v_idx_1456_);
v_a_1516_ = lean_ctor_get(v___x_1491_, 0);
v_isSharedCheck_1523_ = !lean_is_exclusive(v___x_1491_);
if (v_isSharedCheck_1523_ == 0)
{
v___x_1518_ = v___x_1491_;
v_isShared_1519_ = v_isSharedCheck_1523_;
goto v_resetjp_1517_;
}
else
{
lean_inc(v_a_1516_);
lean_dec(v___x_1491_);
v___x_1518_ = lean_box(0);
v_isShared_1519_ = v_isSharedCheck_1523_;
goto v_resetjp_1517_;
}
v_resetjp_1517_:
{
lean_object* v___x_1521_; 
if (v_isShared_1519_ == 0)
{
v___x_1521_ = v___x_1518_;
goto v_reusejp_1520_;
}
else
{
lean_object* v_reuseFailAlloc_1522_; 
v_reuseFailAlloc_1522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1522_, 0, v_a_1516_);
v___x_1521_ = v_reuseFailAlloc_1522_;
goto v_reusejp_1520_;
}
v_reusejp_1520_:
{
return v___x_1521_;
}
}
}
}
}
}
v___jp_1524_:
{
uint8_t v___x_1529_; 
v___x_1529_ = lean_nat_dec_lt(v_idxPos_1459_, v___x_1479_);
if (v___x_1529_ == 0)
{
v___y_1482_ = v___y_1526_;
v___y_1483_ = v___y_1527_;
v___y_1484_ = v___y_1525_;
v___y_1485_ = v___y_1528_;
v___y_1486_ = v___x_1529_;
goto v___jp_1481_;
}
else
{
lean_object* v_indicesPos_1530_; uint8_t v___x_1531_; 
v_indicesPos_1530_ = lean_ctor_get(v_recursorInfo_1460_, 6);
v___x_1531_ = l_List_elem___at___00Lean_Meta_getMajorTypeIndices_spec__1(v___x_1479_, v_indicesPos_1530_);
v___y_1482_ = v___y_1526_;
v___y_1483_ = v___y_1527_;
v___y_1484_ = v___y_1525_;
v___y_1485_ = v___y_1528_;
v___y_1486_ = v___x_1531_;
goto v___jp_1481_;
}
}
v___jp_1532_:
{
uint8_t v___x_1537_; 
v___x_1537_ = lean_nat_dec_lt(v___x_1479_, v_idxPos_1459_);
if (v___x_1537_ == 0)
{
v___y_1525_ = v___y_1533_;
v___y_1526_ = v___y_1534_;
v___y_1527_ = v___y_1535_;
v___y_1528_ = v___y_1536_;
goto v___jp_1524_;
}
else
{
lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v_a_1540_; lean_object* v___x_1542_; uint8_t v_isShared_1543_; uint8_t v_isSharedCheck_1556_; 
v___x_1538_ = l_Lean_Expr_fvarId_x21(v_idx_1456_);
lean_inc(v_arg_1480_);
v___x_1539_ = l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2___redArg(v_arg_1480_, v___x_1538_, v___y_1534_);
v_a_1540_ = lean_ctor_get(v___x_1539_, 0);
v_isSharedCheck_1556_ = !lean_is_exclusive(v___x_1539_);
if (v_isSharedCheck_1556_ == 0)
{
v___x_1542_ = v___x_1539_;
v_isShared_1543_ = v_isSharedCheck_1556_;
goto v_resetjp_1541_;
}
else
{
lean_inc(v_a_1540_);
lean_dec(v___x_1539_);
v___x_1542_ = lean_box(0);
v_isShared_1543_ = v_isSharedCheck_1556_;
goto v_resetjp_1541_;
}
v_resetjp_1541_:
{
uint8_t v___x_1544_; 
v___x_1544_ = lean_unbox(v_a_1540_);
lean_dec(v_a_1540_);
if (v___x_1544_ == 0)
{
lean_del_object(v___x_1542_);
v___y_1525_ = v___y_1533_;
v___y_1526_ = v___y_1534_;
v___y_1527_ = v___y_1535_;
v___y_1528_ = v___y_1536_;
goto v___jp_1524_;
}
else
{
lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1553_; 
v___x_1545_ = lean_obj_once(&l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1, &l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1_once, _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1);
lean_inc_ref(v_idx_1456_);
v___x_1546_ = l_Lean_MessageData_ofExpr(v_idx_1456_);
v___x_1547_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1547_, 0, v___x_1545_);
lean_ctor_set(v___x_1547_, 1, v___x_1546_);
v___x_1548_ = lean_obj_once(&l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__5, &l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__5_once, _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__5);
v___x_1549_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1549_, 0, v___x_1547_);
lean_ctor_set(v___x_1549_, 1, v___x_1548_);
lean_inc_ref(v_majorType_1461_);
v___x_1550_ = l_Lean_indentExpr(v_majorType_1461_);
v___x_1551_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1551_, 0, v___x_1549_);
lean_ctor_set(v___x_1551_, 1, v___x_1550_);
if (v_isShared_1543_ == 0)
{
lean_ctor_set_tag(v___x_1542_, 1);
lean_ctor_set(v___x_1542_, 0, v___x_1551_);
v___x_1553_ = v___x_1542_;
goto v_reusejp_1552_;
}
else
{
lean_object* v_reuseFailAlloc_1555_; 
v_reuseFailAlloc_1555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1555_, 0, v___x_1551_);
v___x_1553_ = v_reuseFailAlloc_1555_;
goto v_reusejp_1552_;
}
v_reusejp_1552_:
{
lean_object* v___x_1554_; 
lean_inc(v_mvarId_1458_);
lean_inc(v_tacticName_1457_);
v___x_1554_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1457_, v_mvarId_1458_, v___x_1553_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_);
if (lean_obj_tag(v___x_1554_) == 0)
{
lean_dec_ref_known(v___x_1554_, 1);
v___y_1525_ = v___y_1533_;
v___y_1526_ = v___y_1534_;
v___y_1527_ = v___y_1535_;
v___y_1528_ = v___y_1536_;
goto v___jp_1524_;
}
else
{
lean_dec(v___x_1479_);
v___y_1476_ = v___x_1554_;
goto v___jp_1475_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___boxed(lean_object* v_majorTypeArgs_1568_, lean_object* v_idx_1569_, lean_object* v_tacticName_1570_, lean_object* v_mvarId_1571_, lean_object* v_idxPos_1572_, lean_object* v_recursorInfo_1573_, lean_object* v_majorType_1574_, lean_object* v_n_1575_, lean_object* v_i_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_){
_start:
{
lean_object* v_res_1582_; 
v_res_1582_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg(v_majorTypeArgs_1568_, v_idx_1569_, v_tacticName_1570_, v_mvarId_1571_, v_idxPos_1572_, v_recursorInfo_1573_, v_majorType_1574_, v_n_1575_, v_i_1576_, v___y_1577_, v___y_1578_, v___y_1579_, v___y_1580_);
lean_dec(v___y_1580_);
lean_dec_ref(v___y_1579_);
lean_dec(v___y_1578_);
lean_dec_ref(v___y_1577_);
lean_dec(v_n_1575_);
lean_dec_ref(v_recursorInfo_1573_);
lean_dec(v_idxPos_1572_);
lean_dec_ref(v_majorTypeArgs_1568_);
return v_res_1582_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__1(void){
_start:
{
lean_object* v___x_1584_; lean_object* v___x_1585_; 
v___x_1584_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__0));
v___x_1585_ = l_Lean_stringToMessageData(v___x_1584_);
return v___x_1585_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__3(void){
_start:
{
lean_object* v___x_1587_; lean_object* v___x_1588_; 
v___x_1587_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__2));
v___x_1588_ = l_Lean_stringToMessageData(v___x_1587_);
return v___x_1588_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__5(void){
_start:
{
lean_object* v___x_1590_; lean_object* v___x_1591_; 
v___x_1590_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__4));
v___x_1591_ = l_Lean_stringToMessageData(v___x_1590_);
return v___x_1591_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4(lean_object* v_majorTypeArgs_1592_, lean_object* v_tacticName_1593_, lean_object* v_mvarId_1594_, lean_object* v_recursorInfo_1595_, lean_object* v_majorType_1596_, size_t v_sz_1597_, size_t v_i_1598_, lean_object* v_bs_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_){
_start:
{
uint8_t v___x_1605_; 
v___x_1605_ = lean_usize_dec_lt(v_i_1598_, v_sz_1597_);
if (v___x_1605_ == 0)
{
lean_object* v___x_1606_; 
lean_dec_ref(v_majorType_1596_);
lean_dec(v_mvarId_1594_);
lean_dec(v_tacticName_1593_);
v___x_1606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1606_, 0, v_bs_1599_);
return v___x_1606_;
}
else
{
lean_object* v_v_1607_; lean_object* v___x_1608_; lean_object* v_bs_x27_1609_; lean_object* v_a_1611_; lean_object* v___x_1616_; uint8_t v___x_1617_; 
v_v_1607_ = lean_array_uget(v_bs_1599_, v_i_1598_);
v___x_1608_ = lean_unsigned_to_nat(0u);
v_bs_x27_1609_ = lean_array_uset(v_bs_1599_, v_i_1598_, v___x_1608_);
v___x_1616_ = lean_array_get_size(v_majorTypeArgs_1592_);
v___x_1617_ = lean_nat_dec_le(v___x_1616_, v_v_1607_);
if (v___x_1617_ == 0)
{
lean_object* v_idx_1618_; lean_object* v___y_1620_; lean_object* v___y_1621_; lean_object* v___y_1622_; lean_object* v___y_1623_; uint8_t v___x_1633_; 
v_idx_1618_ = lean_array_fget_borrowed(v_majorTypeArgs_1592_, v_v_1607_);
v___x_1633_ = l_Lean_Expr_isFVar(v_idx_1618_);
if (v___x_1633_ == 0)
{
lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; 
v___x_1634_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__1);
lean_inc(v_idx_1618_);
v___x_1635_ = l_Lean_MessageData_ofExpr(v_idx_1618_);
v___x_1636_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1636_, 0, v___x_1634_);
lean_ctor_set(v___x_1636_, 1, v___x_1635_);
v___x_1637_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__3);
v___x_1638_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1638_, 0, v___x_1636_);
lean_ctor_set(v___x_1638_, 1, v___x_1637_);
lean_inc_ref(v_majorType_1596_);
v___x_1639_ = l_Lean_indentExpr(v_majorType_1596_);
v___x_1640_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1640_, 0, v___x_1638_);
lean_ctor_set(v___x_1640_, 1, v___x_1639_);
v___x_1641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1641_, 0, v___x_1640_);
lean_inc(v_mvarId_1594_);
lean_inc(v_tacticName_1593_);
v___x_1642_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1593_, v_mvarId_1594_, v___x_1641_, v___y_1600_, v___y_1601_, v___y_1602_, v___y_1603_);
if (lean_obj_tag(v___x_1642_) == 0)
{
lean_dec_ref_known(v___x_1642_, 1);
v___y_1620_ = v___y_1600_;
v___y_1621_ = v___y_1601_;
v___y_1622_ = v___y_1602_;
v___y_1623_ = v___y_1603_;
goto v___jp_1619_;
}
else
{
lean_object* v_a_1643_; lean_object* v___x_1645_; uint8_t v_isShared_1646_; uint8_t v_isSharedCheck_1650_; 
lean_dec_ref(v_bs_x27_1609_);
lean_dec(v_v_1607_);
lean_dec_ref(v_majorType_1596_);
lean_dec(v_mvarId_1594_);
lean_dec(v_tacticName_1593_);
v_a_1643_ = lean_ctor_get(v___x_1642_, 0);
v_isSharedCheck_1650_ = !lean_is_exclusive(v___x_1642_);
if (v_isSharedCheck_1650_ == 0)
{
v___x_1645_ = v___x_1642_;
v_isShared_1646_ = v_isSharedCheck_1650_;
goto v_resetjp_1644_;
}
else
{
lean_inc(v_a_1643_);
lean_dec(v___x_1642_);
v___x_1645_ = lean_box(0);
v_isShared_1646_ = v_isSharedCheck_1650_;
goto v_resetjp_1644_;
}
v_resetjp_1644_:
{
lean_object* v___x_1648_; 
if (v_isShared_1646_ == 0)
{
v___x_1648_ = v___x_1645_;
goto v_reusejp_1647_;
}
else
{
lean_object* v_reuseFailAlloc_1649_; 
v_reuseFailAlloc_1649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1649_, 0, v_a_1643_);
v___x_1648_ = v_reuseFailAlloc_1649_;
goto v_reusejp_1647_;
}
v_reusejp_1647_:
{
return v___x_1648_;
}
}
}
}
else
{
v___y_1620_ = v___y_1600_;
v___y_1621_ = v___y_1601_;
v___y_1622_ = v___y_1602_;
v___y_1623_ = v___y_1603_;
goto v___jp_1619_;
}
v___jp_1619_:
{
lean_object* v___x_1624_; 
lean_inc_ref(v_majorType_1596_);
lean_inc(v_mvarId_1594_);
lean_inc(v_tacticName_1593_);
lean_inc(v_idx_1618_);
v___x_1624_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg(v_majorTypeArgs_1592_, v_idx_1618_, v_tacticName_1593_, v_mvarId_1594_, v_v_1607_, v_recursorInfo_1595_, v_majorType_1596_, v___x_1616_, v___x_1616_, v___y_1620_, v___y_1621_, v___y_1622_, v___y_1623_);
lean_dec(v_v_1607_);
if (lean_obj_tag(v___x_1624_) == 0)
{
lean_dec_ref_known(v___x_1624_, 1);
lean_inc(v_idx_1618_);
v_a_1611_ = v_idx_1618_;
goto v___jp_1610_;
}
else
{
lean_object* v_a_1625_; lean_object* v___x_1627_; uint8_t v_isShared_1628_; uint8_t v_isSharedCheck_1632_; 
lean_dec_ref(v_bs_x27_1609_);
lean_dec_ref(v_majorType_1596_);
lean_dec(v_mvarId_1594_);
lean_dec(v_tacticName_1593_);
v_a_1625_ = lean_ctor_get(v___x_1624_, 0);
v_isSharedCheck_1632_ = !lean_is_exclusive(v___x_1624_);
if (v_isSharedCheck_1632_ == 0)
{
v___x_1627_ = v___x_1624_;
v_isShared_1628_ = v_isSharedCheck_1632_;
goto v_resetjp_1626_;
}
else
{
lean_inc(v_a_1625_);
lean_dec(v___x_1624_);
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
else
{
lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; 
lean_dec(v_v_1607_);
v___x_1651_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__5, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__5);
lean_inc_ref(v_majorType_1596_);
v___x_1652_ = l_Lean_indentExpr(v_majorType_1596_);
v___x_1653_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1653_, 0, v___x_1651_);
lean_ctor_set(v___x_1653_, 1, v___x_1652_);
v___x_1654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1654_, 0, v___x_1653_);
lean_inc(v_mvarId_1594_);
lean_inc(v_tacticName_1593_);
v___x_1655_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1593_, v_mvarId_1594_, v___x_1654_, v___y_1600_, v___y_1601_, v___y_1602_, v___y_1603_);
if (lean_obj_tag(v___x_1655_) == 0)
{
lean_object* v_a_1656_; 
v_a_1656_ = lean_ctor_get(v___x_1655_, 0);
lean_inc(v_a_1656_);
lean_dec_ref_known(v___x_1655_, 1);
v_a_1611_ = v_a_1656_;
goto v___jp_1610_;
}
else
{
lean_object* v_a_1657_; lean_object* v___x_1659_; uint8_t v_isShared_1660_; uint8_t v_isSharedCheck_1664_; 
lean_dec_ref(v_bs_x27_1609_);
lean_dec_ref(v_majorType_1596_);
lean_dec(v_mvarId_1594_);
lean_dec(v_tacticName_1593_);
v_a_1657_ = lean_ctor_get(v___x_1655_, 0);
v_isSharedCheck_1664_ = !lean_is_exclusive(v___x_1655_);
if (v_isSharedCheck_1664_ == 0)
{
v___x_1659_ = v___x_1655_;
v_isShared_1660_ = v_isSharedCheck_1664_;
goto v_resetjp_1658_;
}
else
{
lean_inc(v_a_1657_);
lean_dec(v___x_1655_);
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
v___jp_1610_:
{
size_t v___x_1612_; size_t v___x_1613_; lean_object* v___x_1614_; 
v___x_1612_ = ((size_t)1ULL);
v___x_1613_ = lean_usize_add(v_i_1598_, v___x_1612_);
v___x_1614_ = lean_array_uset(v_bs_x27_1609_, v_i_1598_, v_a_1611_);
v_i_1598_ = v___x_1613_;
v_bs_1599_ = v___x_1614_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___boxed(lean_object* v_majorTypeArgs_1665_, lean_object* v_tacticName_1666_, lean_object* v_mvarId_1667_, lean_object* v_recursorInfo_1668_, lean_object* v_majorType_1669_, lean_object* v_sz_1670_, lean_object* v_i_1671_, lean_object* v_bs_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_){
_start:
{
size_t v_sz_boxed_1678_; size_t v_i_boxed_1679_; lean_object* v_res_1680_; 
v_sz_boxed_1678_ = lean_unbox_usize(v_sz_1670_);
lean_dec(v_sz_1670_);
v_i_boxed_1679_ = lean_unbox_usize(v_i_1671_);
lean_dec(v_i_1671_);
v_res_1680_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4(v_majorTypeArgs_1665_, v_tacticName_1666_, v_mvarId_1667_, v_recursorInfo_1668_, v_majorType_1669_, v_sz_boxed_1678_, v_i_boxed_1679_, v_bs_1672_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_);
lean_dec(v___y_1676_);
lean_dec_ref(v___y_1675_);
lean_dec(v___y_1674_);
lean_dec_ref(v___y_1673_);
lean_dec_ref(v_recursorInfo_1668_);
lean_dec_ref(v_majorTypeArgs_1665_);
return v_res_1680_;
}
}
static lean_object* _init_l_Lean_Meta_getMajorTypeIndices___closed__0(void){
_start:
{
lean_object* v___x_1681_; lean_object* v_dummy_1682_; 
v___x_1681_ = lean_box(0);
v_dummy_1682_ = l_Lean_Expr_sort___override(v___x_1681_);
return v_dummy_1682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMajorTypeIndices(lean_object* v_mvarId_1683_, lean_object* v_tacticName_1684_, lean_object* v_recursorInfo_1685_, lean_object* v_majorType_1686_, lean_object* v_a_1687_, lean_object* v_a_1688_, lean_object* v_a_1689_, lean_object* v_a_1690_){
_start:
{
lean_object* v_indicesPos_1692_; lean_object* v_nargs_1693_; lean_object* v_dummy_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v_majorTypeArgs_1698_; lean_object* v___x_1699_; size_t v_sz_1700_; size_t v___x_1701_; lean_object* v___x_1702_; 
v_indicesPos_1692_ = lean_ctor_get(v_recursorInfo_1685_, 6);
v_nargs_1693_ = l_Lean_Expr_getAppNumArgs(v_majorType_1686_);
v_dummy_1694_ = lean_obj_once(&l_Lean_Meta_getMajorTypeIndices___closed__0, &l_Lean_Meta_getMajorTypeIndices___closed__0_once, _init_l_Lean_Meta_getMajorTypeIndices___closed__0);
lean_inc(v_nargs_1693_);
v___x_1695_ = lean_mk_array(v_nargs_1693_, v_dummy_1694_);
v___x_1696_ = lean_unsigned_to_nat(1u);
v___x_1697_ = lean_nat_sub(v_nargs_1693_, v___x_1696_);
lean_dec(v_nargs_1693_);
lean_inc_ref(v_majorType_1686_);
v_majorTypeArgs_1698_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_majorType_1686_, v___x_1695_, v___x_1697_);
lean_inc(v_indicesPos_1692_);
v___x_1699_ = lean_array_mk(v_indicesPos_1692_);
v_sz_1700_ = lean_array_size(v___x_1699_);
v___x_1701_ = ((size_t)0ULL);
v___x_1702_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4(v_majorTypeArgs_1698_, v_tacticName_1684_, v_mvarId_1683_, v_recursorInfo_1685_, v_majorType_1686_, v_sz_1700_, v___x_1701_, v___x_1699_, v_a_1687_, v_a_1688_, v_a_1689_, v_a_1690_);
lean_dec_ref(v_recursorInfo_1685_);
lean_dec_ref(v_majorTypeArgs_1698_);
return v___x_1702_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMajorTypeIndices___boxed(lean_object* v_mvarId_1703_, lean_object* v_tacticName_1704_, lean_object* v_recursorInfo_1705_, lean_object* v_majorType_1706_, lean_object* v_a_1707_, lean_object* v_a_1708_, lean_object* v_a_1709_, lean_object* v_a_1710_, lean_object* v_a_1711_){
_start:
{
lean_object* v_res_1712_; 
v_res_1712_ = l_Lean_Meta_getMajorTypeIndices(v_mvarId_1703_, v_tacticName_1704_, v_recursorInfo_1705_, v_majorType_1706_, v_a_1707_, v_a_1708_, v_a_1709_, v_a_1710_);
lean_dec(v_a_1710_);
lean_dec_ref(v_a_1709_);
lean_dec(v_a_1708_);
lean_dec_ref(v_a_1707_);
return v_res_1712_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3(lean_object* v_majorTypeArgs_1713_, lean_object* v_idx_1714_, lean_object* v_tacticName_1715_, lean_object* v_mvarId_1716_, lean_object* v_idxPos_1717_, lean_object* v_recursorInfo_1718_, lean_object* v_majorType_1719_, lean_object* v_n_1720_, lean_object* v_i_1721_, lean_object* v_a_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_){
_start:
{
lean_object* v___x_1728_; 
v___x_1728_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg(v_majorTypeArgs_1713_, v_idx_1714_, v_tacticName_1715_, v_mvarId_1716_, v_idxPos_1717_, v_recursorInfo_1718_, v_majorType_1719_, v_n_1720_, v_i_1721_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_);
return v___x_1728_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___boxed(lean_object* v_majorTypeArgs_1729_, lean_object* v_idx_1730_, lean_object* v_tacticName_1731_, lean_object* v_mvarId_1732_, lean_object* v_idxPos_1733_, lean_object* v_recursorInfo_1734_, lean_object* v_majorType_1735_, lean_object* v_n_1736_, lean_object* v_i_1737_, lean_object* v_a_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_){
_start:
{
lean_object* v_res_1744_; 
v_res_1744_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3(v_majorTypeArgs_1729_, v_idx_1730_, v_tacticName_1731_, v_mvarId_1732_, v_idxPos_1733_, v_recursorInfo_1734_, v_majorType_1735_, v_n_1736_, v_i_1737_, v_a_1738_, v___y_1739_, v___y_1740_, v___y_1741_, v___y_1742_);
lean_dec(v___y_1742_);
lean_dec_ref(v___y_1741_);
lean_dec(v___y_1740_);
lean_dec_ref(v___y_1739_);
lean_dec(v_n_1736_);
lean_dec_ref(v_recursorInfo_1734_);
lean_dec(v_idxPos_1733_);
lean_dec_ref(v_majorTypeArgs_1729_);
return v_res_1744_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1___redArg(lean_object* v_name_1745_, lean_object* v_msg_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_){
_start:
{
lean_object* v_ref_1752_; lean_object* v_msg_1753_; lean_object* v___x_1754_; lean_object* v_a_1755_; lean_object* v___x_1757_; uint8_t v_isShared_1758_; uint8_t v_isSharedCheck_1763_; 
v_ref_1752_ = lean_ctor_get(v___y_1749_, 5);
v_msg_1753_ = l_Lean_MessageData_tagWithErrorName(v_msg_1746_, v_name_1745_);
v___x_1754_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1_spec__2(v_msg_1753_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_);
v_a_1755_ = lean_ctor_get(v___x_1754_, 0);
v_isSharedCheck_1763_ = !lean_is_exclusive(v___x_1754_);
if (v_isSharedCheck_1763_ == 0)
{
v___x_1757_ = v___x_1754_;
v_isShared_1758_ = v_isSharedCheck_1763_;
goto v_resetjp_1756_;
}
else
{
lean_inc(v_a_1755_);
lean_dec(v___x_1754_);
v___x_1757_ = lean_box(0);
v_isShared_1758_ = v_isSharedCheck_1763_;
goto v_resetjp_1756_;
}
v_resetjp_1756_:
{
lean_object* v___x_1759_; lean_object* v___x_1761_; 
lean_inc(v_ref_1752_);
v___x_1759_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1759_, 0, v_ref_1752_);
lean_ctor_set(v___x_1759_, 1, v_a_1755_);
if (v_isShared_1758_ == 0)
{
lean_ctor_set_tag(v___x_1757_, 1);
lean_ctor_set(v___x_1757_, 0, v___x_1759_);
v___x_1761_ = v___x_1757_;
goto v_reusejp_1760_;
}
else
{
lean_object* v_reuseFailAlloc_1762_; 
v_reuseFailAlloc_1762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1762_, 0, v___x_1759_);
v___x_1761_ = v_reuseFailAlloc_1762_;
goto v_reusejp_1760_;
}
v_reusejp_1760_:
{
return v___x_1761_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1___redArg___boxed(lean_object* v_name_1764_, lean_object* v_msg_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_){
_start:
{
lean_object* v_res_1771_; 
v_res_1771_ = l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1___redArg(v_name_1764_, v_msg_1765_, v___y_1766_, v___y_1767_, v___y_1768_, v___y_1769_);
lean_dec(v___y_1769_);
lean_dec_ref(v___y_1768_);
lean_dec(v___y_1767_);
lean_dec_ref(v___y_1766_);
return v_res_1771_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Meta_mkRecursorAppPrefix_spec__0(lean_object* v_a_1772_, lean_object* v___x_1773_, lean_object* v_tacticName_1774_, lean_object* v_mvarId_1775_, lean_object* v_x_1776_, lean_object* v_x_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_){
_start:
{
if (lean_obj_tag(v_x_1777_) == 0)
{
lean_object* v___x_1783_; 
lean_dec(v_mvarId_1775_);
lean_dec(v_tacticName_1774_);
lean_dec(v_a_1772_);
v___x_1783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1783_, 0, v_x_1776_);
return v___x_1783_;
}
else
{
lean_object* v_head_1784_; 
v_head_1784_ = lean_ctor_get(v_x_1777_, 0);
if (lean_obj_tag(v_head_1784_) == 0)
{
lean_object* v_tail_1785_; lean_object* v_fst_1786_; lean_object* v___x_1788_; uint8_t v_isShared_1789_; uint8_t v_isSharedCheck_1797_; 
v_tail_1785_ = lean_ctor_get(v_x_1777_, 1);
v_fst_1786_ = lean_ctor_get(v_x_1776_, 0);
v_isSharedCheck_1797_ = !lean_is_exclusive(v_x_1776_);
if (v_isSharedCheck_1797_ == 0)
{
lean_object* v_unused_1798_; 
v_unused_1798_ = lean_ctor_get(v_x_1776_, 1);
lean_dec(v_unused_1798_);
v___x_1788_ = v_x_1776_;
v_isShared_1789_ = v_isSharedCheck_1797_;
goto v_resetjp_1787_;
}
else
{
lean_inc(v_fst_1786_);
lean_dec(v_x_1776_);
v___x_1788_ = lean_box(0);
v_isShared_1789_ = v_isSharedCheck_1797_;
goto v_resetjp_1787_;
}
v_resetjp_1787_:
{
lean_object* v___x_1790_; uint8_t v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1794_; 
lean_inc(v_a_1772_);
v___x_1790_ = lean_array_push(v_fst_1786_, v_a_1772_);
v___x_1791_ = 1;
v___x_1792_ = lean_box(v___x_1791_);
if (v_isShared_1789_ == 0)
{
lean_ctor_set(v___x_1788_, 1, v___x_1792_);
lean_ctor_set(v___x_1788_, 0, v___x_1790_);
v___x_1794_ = v___x_1788_;
goto v_reusejp_1793_;
}
else
{
lean_object* v_reuseFailAlloc_1796_; 
v_reuseFailAlloc_1796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1796_, 0, v___x_1790_);
lean_ctor_set(v_reuseFailAlloc_1796_, 1, v___x_1792_);
v___x_1794_ = v_reuseFailAlloc_1796_;
goto v_reusejp_1793_;
}
v_reusejp_1793_:
{
v_x_1776_ = v___x_1794_;
v_x_1777_ = v_tail_1785_;
goto _start;
}
}
}
else
{
lean_object* v_tail_1799_; lean_object* v_fst_1800_; lean_object* v_snd_1801_; lean_object* v___x_1803_; uint8_t v_isShared_1804_; uint8_t v_isSharedCheck_1818_; 
v_tail_1799_ = lean_ctor_get(v_x_1777_, 1);
v_fst_1800_ = lean_ctor_get(v_x_1776_, 0);
v_snd_1801_ = lean_ctor_get(v_x_1776_, 1);
v_isSharedCheck_1818_ = !lean_is_exclusive(v_x_1776_);
if (v_isSharedCheck_1818_ == 0)
{
v___x_1803_ = v_x_1776_;
v_isShared_1804_ = v_isSharedCheck_1818_;
goto v_resetjp_1802_;
}
else
{
lean_inc(v_snd_1801_);
lean_inc(v_fst_1800_);
lean_dec(v_x_1776_);
v___x_1803_ = lean_box(0);
v_isShared_1804_ = v_isSharedCheck_1818_;
goto v_resetjp_1802_;
}
v_resetjp_1802_:
{
lean_object* v_idx_1805_; lean_object* v___x_1806_; uint8_t v___x_1807_; 
v_idx_1805_ = lean_ctor_get(v_head_1784_, 0);
v___x_1806_ = lean_array_get_size(v___x_1773_);
v___x_1807_ = lean_nat_dec_le(v___x_1806_, v_idx_1805_);
if (v___x_1807_ == 0)
{
lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1811_; 
v___x_1808_ = lean_array_fget_borrowed(v___x_1773_, v_idx_1805_);
lean_inc(v___x_1808_);
v___x_1809_ = lean_array_push(v_fst_1800_, v___x_1808_);
if (v_isShared_1804_ == 0)
{
lean_ctor_set(v___x_1803_, 0, v___x_1809_);
v___x_1811_ = v___x_1803_;
goto v_reusejp_1810_;
}
else
{
lean_object* v_reuseFailAlloc_1813_; 
v_reuseFailAlloc_1813_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1813_, 0, v___x_1809_);
lean_ctor_set(v_reuseFailAlloc_1813_, 1, v_snd_1801_);
v___x_1811_ = v_reuseFailAlloc_1813_;
goto v_reusejp_1810_;
}
v_reusejp_1810_:
{
v_x_1776_ = v___x_1811_;
v_x_1777_ = v_tail_1799_;
goto _start;
}
}
else
{
lean_object* v___x_1814_; lean_object* v___x_1815_; 
lean_del_object(v___x_1803_);
lean_dec(v_snd_1801_);
lean_dec(v_fst_1800_);
v___x_1814_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9);
lean_inc(v_mvarId_1775_);
lean_inc(v_tacticName_1774_);
v___x_1815_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1774_, v_mvarId_1775_, v___x_1814_, v___y_1778_, v___y_1779_, v___y_1780_, v___y_1781_);
if (lean_obj_tag(v___x_1815_) == 0)
{
lean_object* v_a_1816_; 
v_a_1816_ = lean_ctor_get(v___x_1815_, 0);
lean_inc(v_a_1816_);
lean_dec_ref_known(v___x_1815_, 1);
v_x_1776_ = v_a_1816_;
v_x_1777_ = v_tail_1799_;
goto _start;
}
else
{
lean_dec(v_mvarId_1775_);
lean_dec(v_tacticName_1774_);
lean_dec(v_a_1772_);
return v___x_1815_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Meta_mkRecursorAppPrefix_spec__0___boxed(lean_object* v_a_1819_, lean_object* v___x_1820_, lean_object* v_tacticName_1821_, lean_object* v_mvarId_1822_, lean_object* v_x_1823_, lean_object* v_x_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_){
_start:
{
lean_object* v_res_1830_; 
v_res_1830_ = l_List_foldlM___at___00Lean_Meta_mkRecursorAppPrefix_spec__0(v_a_1819_, v___x_1820_, v_tacticName_1821_, v_mvarId_1822_, v_x_1823_, v_x_1824_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_);
lean_dec(v___y_1828_);
lean_dec_ref(v___y_1827_);
lean_dec(v___y_1826_);
lean_dec_ref(v___y_1825_);
lean_dec(v_x_1824_);
lean_dec_ref(v___x_1820_);
return v_res_1830_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__8(void){
_start:
{
lean_object* v___x_1846_; lean_object* v___x_1847_; 
v___x_1846_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__7));
v___x_1847_ = l_Lean_stringToMessageData(v___x_1846_);
return v___x_1847_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__10(void){
_start:
{
lean_object* v___x_1849_; lean_object* v___x_1850_; 
v___x_1849_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__9));
v___x_1850_ = l_Lean_stringToMessageData(v___x_1849_);
return v___x_1850_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__13(void){
_start:
{
lean_object* v___x_1854_; lean_object* v___x_1855_; 
v___x_1854_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__12));
v___x_1855_ = l_Lean_MessageData_ofFormat(v___x_1854_);
return v___x_1855_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__14(void){
_start:
{
lean_object* v___x_1856_; lean_object* v___x_1857_; 
v___x_1856_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__13, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__13_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__13);
v___x_1857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1857_, 0, v___x_1856_);
return v___x_1857_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2(lean_object* v_recursorInfo_1858_, lean_object* v_a_1859_, lean_object* v_tacticName_1860_, lean_object* v_mvarId_1861_, lean_object* v_indices_1862_, lean_object* v_a_1863_, lean_object* v_major_1864_, lean_object* v_x_1865_, lean_object* v_x_1866_, lean_object* v_x_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_){
_start:
{
if (lean_obj_tag(v_x_1865_) == 5)
{
lean_object* v_fn_1873_; lean_object* v_arg_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; 
v_fn_1873_ = lean_ctor_get(v_x_1865_, 0);
lean_inc_ref(v_fn_1873_);
v_arg_1874_ = lean_ctor_get(v_x_1865_, 1);
lean_inc_ref(v_arg_1874_);
lean_dec_ref_known(v_x_1865_, 2);
v___x_1875_ = lean_array_set(v_x_1866_, v_x_1867_, v_arg_1874_);
v___x_1876_ = lean_unsigned_to_nat(1u);
v___x_1877_ = lean_nat_sub(v_x_1867_, v___x_1876_);
lean_dec(v_x_1867_);
v_x_1865_ = v_fn_1873_;
v_x_1866_ = v___x_1875_;
v_x_1867_ = v___x_1877_;
goto _start;
}
else
{
lean_dec(v_x_1867_);
if (lean_obj_tag(v_x_1865_) == 4)
{
lean_object* v_us_1879_; lean_object* v_recursorName_1880_; lean_object* v_univLevelPos_1881_; uint8_t v_depElim_1882_; lean_object* v_paramsPos_1883_; lean_object* v___x_1884_; uint8_t v___x_1885_; lean_object* v___y_1887_; lean_object* v_motive_1888_; lean_object* v___y_1889_; lean_object* v___y_1890_; lean_object* v___y_1891_; lean_object* v___y_1892_; lean_object* v___x_1905_; lean_object* v___x_1906_; 
v_us_1879_ = lean_ctor_get(v_x_1865_, 1);
lean_inc(v_us_1879_);
lean_dec_ref_known(v_x_1865_, 2);
v_recursorName_1880_ = lean_ctor_get(v_recursorInfo_1858_, 0);
lean_inc(v_recursorName_1880_);
v_univLevelPos_1881_ = lean_ctor_get(v_recursorInfo_1858_, 2);
lean_inc(v_univLevelPos_1881_);
v_depElim_1882_ = lean_ctor_get_uint8(v_recursorInfo_1858_, sizeof(void*)*8);
v_paramsPos_1883_ = lean_ctor_get(v_recursorInfo_1858_, 5);
lean_inc(v_paramsPos_1883_);
lean_dec_ref(v_recursorInfo_1858_);
v___x_1884_ = lean_array_mk(v_us_1879_);
v___x_1885_ = 0;
v___x_1905_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__1));
lean_inc(v_mvarId_1861_);
lean_inc(v_tacticName_1860_);
lean_inc(v_a_1859_);
v___x_1906_ = l_List_foldlM___at___00Lean_Meta_mkRecursorAppPrefix_spec__0(v_a_1859_, v___x_1884_, v_tacticName_1860_, v_mvarId_1861_, v___x_1905_, v_univLevelPos_1881_, v___y_1868_, v___y_1869_, v___y_1870_, v___y_1871_);
lean_dec(v_univLevelPos_1881_);
lean_dec_ref(v___x_1884_);
if (lean_obj_tag(v___x_1906_) == 0)
{
lean_object* v_a_1907_; lean_object* v_fst_1908_; lean_object* v_snd_1909_; lean_object* v___x_1911_; uint8_t v_isShared_1912_; uint8_t v_isSharedCheck_1953_; 
v_a_1907_ = lean_ctor_get(v___x_1906_, 0);
lean_inc(v_a_1907_);
lean_dec_ref_known(v___x_1906_, 1);
v_fst_1908_ = lean_ctor_get(v_a_1907_, 0);
v_snd_1909_ = lean_ctor_get(v_a_1907_, 1);
v_isSharedCheck_1953_ = !lean_is_exclusive(v_a_1907_);
if (v_isSharedCheck_1953_ == 0)
{
v___x_1911_ = v_a_1907_;
v_isShared_1912_ = v_isSharedCheck_1953_;
goto v_resetjp_1910_;
}
else
{
lean_inc(v_snd_1909_);
lean_inc(v_fst_1908_);
lean_dec(v_a_1907_);
v___x_1911_ = lean_box(0);
v_isShared_1912_ = v_isSharedCheck_1953_;
goto v_resetjp_1910_;
}
v_resetjp_1910_:
{
lean_object* v___y_1914_; lean_object* v___y_1915_; lean_object* v___y_1916_; lean_object* v___y_1917_; uint8_t v___x_1933_; 
v___x_1933_ = lean_unbox(v_snd_1909_);
lean_dec(v_snd_1909_);
if (v___x_1933_ == 0)
{
uint8_t v___x_1934_; 
v___x_1934_ = l_Lean_Level_isZero(v_a_1859_);
lean_dec(v_a_1859_);
if (v___x_1934_ == 0)
{
lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1939_; 
lean_dec(v_fst_1908_);
lean_dec(v_paramsPos_1883_);
lean_dec_ref(v_x_1866_);
lean_dec_ref(v_major_1864_);
lean_dec_ref(v_a_1863_);
v___x_1935_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__6));
v___x_1936_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__8, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__8_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__8);
v___x_1937_ = l_Lean_MessageData_ofName(v_recursorName_1880_);
if (v_isShared_1912_ == 0)
{
lean_ctor_set_tag(v___x_1911_, 7);
lean_ctor_set(v___x_1911_, 1, v___x_1937_);
lean_ctor_set(v___x_1911_, 0, v___x_1936_);
v___x_1939_ = v___x_1911_;
goto v_reusejp_1938_;
}
else
{
lean_object* v_reuseFailAlloc_1952_; 
v_reuseFailAlloc_1952_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1952_, 0, v___x_1936_);
lean_ctor_set(v_reuseFailAlloc_1952_, 1, v___x_1937_);
v___x_1939_ = v_reuseFailAlloc_1952_;
goto v_reusejp_1938_;
}
v_reusejp_1938_:
{
lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v_a_1944_; lean_object* v___x_1946_; uint8_t v_isShared_1947_; uint8_t v_isSharedCheck_1951_; 
v___x_1940_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__10, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__10_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__10);
v___x_1941_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1941_, 0, v___x_1939_);
lean_ctor_set(v___x_1941_, 1, v___x_1940_);
v___x_1942_ = l_Lean_Meta_mkTacticExMsg(v_tacticName_1860_, v_mvarId_1861_, v___x_1941_);
v___x_1943_ = l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1___redArg(v___x_1935_, v___x_1942_, v___y_1868_, v___y_1869_, v___y_1870_, v___y_1871_);
v_a_1944_ = lean_ctor_get(v___x_1943_, 0);
v_isSharedCheck_1951_ = !lean_is_exclusive(v___x_1943_);
if (v_isSharedCheck_1951_ == 0)
{
v___x_1946_ = v___x_1943_;
v_isShared_1947_ = v_isSharedCheck_1951_;
goto v_resetjp_1945_;
}
else
{
lean_inc(v_a_1944_);
lean_dec(v___x_1943_);
v___x_1946_ = lean_box(0);
v_isShared_1947_ = v_isSharedCheck_1951_;
goto v_resetjp_1945_;
}
v_resetjp_1945_:
{
lean_object* v___x_1949_; 
if (v_isShared_1947_ == 0)
{
v___x_1949_ = v___x_1946_;
goto v_reusejp_1948_;
}
else
{
lean_object* v_reuseFailAlloc_1950_; 
v_reuseFailAlloc_1950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1950_, 0, v_a_1944_);
v___x_1949_ = v_reuseFailAlloc_1950_;
goto v_reusejp_1948_;
}
v_reusejp_1948_:
{
return v___x_1949_;
}
}
}
}
else
{
lean_del_object(v___x_1911_);
lean_dec(v_tacticName_1860_);
v___y_1914_ = v___y_1868_;
v___y_1915_ = v___y_1869_;
v___y_1916_ = v___y_1870_;
v___y_1917_ = v___y_1871_;
goto v___jp_1913_;
}
}
else
{
lean_del_object(v___x_1911_);
lean_dec(v_tacticName_1860_);
lean_dec(v_a_1859_);
v___y_1914_ = v___y_1868_;
v___y_1915_ = v___y_1869_;
v___y_1916_ = v___y_1870_;
v___y_1917_ = v___y_1871_;
goto v___jp_1913_;
}
v___jp_1913_:
{
lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; 
v___x_1918_ = lean_array_to_list(v_fst_1908_);
v___x_1919_ = l_Lean_mkConst(v_recursorName_1880_, v___x_1918_);
v___x_1920_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams(v_mvarId_1861_, v_x_1866_, v_paramsPos_1883_, v___x_1919_, v___y_1914_, v___y_1915_, v___y_1916_, v___y_1917_);
lean_dec_ref(v_x_1866_);
if (lean_obj_tag(v___x_1920_) == 0)
{
if (v_depElim_1882_ == 0)
{
lean_object* v_a_1921_; 
lean_dec_ref(v_major_1864_);
v_a_1921_ = lean_ctor_get(v___x_1920_, 0);
lean_inc(v_a_1921_);
lean_dec_ref_known(v___x_1920_, 1);
v___y_1887_ = v_a_1921_;
v_motive_1888_ = v_a_1863_;
v___y_1889_ = v___y_1914_;
v___y_1890_ = v___y_1915_;
v___y_1891_ = v___y_1916_;
v___y_1892_ = v___y_1917_;
goto v___jp_1886_;
}
else
{
lean_object* v_a_1922_; lean_object* v___x_1923_; 
v_a_1922_ = lean_ctor_get(v___x_1920_, 0);
lean_inc(v_a_1922_);
lean_dec_ref_known(v___x_1920_, 1);
lean_inc(v___y_1917_);
lean_inc_ref(v___y_1916_);
lean_inc(v___y_1915_);
lean_inc_ref(v___y_1914_);
lean_inc_ref(v_major_1864_);
v___x_1923_ = lean_infer_type(v_major_1864_, v___y_1914_, v___y_1915_, v___y_1916_, v___y_1917_);
if (lean_obj_tag(v___x_1923_) == 0)
{
lean_object* v_a_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; 
v_a_1924_ = lean_ctor_get(v___x_1923_, 0);
lean_inc(v_a_1924_);
lean_dec_ref_known(v___x_1923_, 1);
v___x_1925_ = lean_unsigned_to_nat(1u);
v___x_1926_ = lean_mk_empty_array_with_capacity(v___x_1925_);
v___x_1927_ = lean_array_push(v___x_1926_, v_major_1864_);
v___x_1928_ = l_Lean_Expr_abstractM(v_a_1863_, v___x_1927_, v___y_1914_, v___y_1915_, v___y_1916_, v___y_1917_);
lean_dec_ref(v___x_1927_);
if (lean_obj_tag(v___x_1928_) == 0)
{
lean_object* v_a_1929_; lean_object* v___x_1930_; uint8_t v___x_1931_; lean_object* v___x_1932_; 
v_a_1929_ = lean_ctor_get(v___x_1928_, 0);
lean_inc(v_a_1929_);
lean_dec_ref_known(v___x_1928_, 1);
v___x_1930_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__3));
v___x_1931_ = 0;
v___x_1932_ = l_Lean_mkLambda(v___x_1930_, v___x_1931_, v_a_1924_, v_a_1929_);
v___y_1887_ = v_a_1922_;
v_motive_1888_ = v___x_1932_;
v___y_1889_ = v___y_1914_;
v___y_1890_ = v___y_1915_;
v___y_1891_ = v___y_1916_;
v___y_1892_ = v___y_1917_;
goto v___jp_1886_;
}
else
{
lean_dec(v_a_1924_);
lean_dec(v_a_1922_);
return v___x_1928_;
}
}
else
{
lean_dec(v_a_1922_);
lean_dec_ref(v_major_1864_);
lean_dec_ref(v_a_1863_);
return v___x_1923_;
}
}
}
else
{
lean_dec_ref(v_major_1864_);
lean_dec_ref(v_a_1863_);
return v___x_1920_;
}
}
}
}
else
{
lean_object* v_a_1954_; lean_object* v___x_1956_; uint8_t v_isShared_1957_; uint8_t v_isSharedCheck_1961_; 
lean_dec(v_paramsPos_1883_);
lean_dec(v_recursorName_1880_);
lean_dec_ref(v_x_1866_);
lean_dec_ref(v_major_1864_);
lean_dec_ref(v_a_1863_);
lean_dec(v_mvarId_1861_);
lean_dec(v_tacticName_1860_);
lean_dec(v_a_1859_);
v_a_1954_ = lean_ctor_get(v___x_1906_, 0);
v_isSharedCheck_1961_ = !lean_is_exclusive(v___x_1906_);
if (v_isSharedCheck_1961_ == 0)
{
v___x_1956_ = v___x_1906_;
v_isShared_1957_ = v_isSharedCheck_1961_;
goto v_resetjp_1955_;
}
else
{
lean_inc(v_a_1954_);
lean_dec(v___x_1906_);
v___x_1956_ = lean_box(0);
v_isShared_1957_ = v_isSharedCheck_1961_;
goto v_resetjp_1955_;
}
v_resetjp_1955_:
{
lean_object* v___x_1959_; 
if (v_isShared_1957_ == 0)
{
v___x_1959_ = v___x_1956_;
goto v_reusejp_1958_;
}
else
{
lean_object* v_reuseFailAlloc_1960_; 
v_reuseFailAlloc_1960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1960_, 0, v_a_1954_);
v___x_1959_ = v_reuseFailAlloc_1960_;
goto v_reusejp_1958_;
}
v_reusejp_1958_:
{
return v___x_1959_;
}
}
}
v___jp_1886_:
{
uint8_t v___x_1893_; uint8_t v___x_1894_; lean_object* v___x_1895_; 
v___x_1893_ = 1;
v___x_1894_ = 1;
v___x_1895_ = l_Lean_Meta_mkLambdaFVars(v_indices_1862_, v_motive_1888_, v___x_1885_, v___x_1893_, v___x_1885_, v___x_1893_, v___x_1894_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_);
if (lean_obj_tag(v___x_1895_) == 0)
{
lean_object* v_a_1896_; lean_object* v___x_1898_; uint8_t v_isShared_1899_; uint8_t v_isSharedCheck_1904_; 
v_a_1896_ = lean_ctor_get(v___x_1895_, 0);
v_isSharedCheck_1904_ = !lean_is_exclusive(v___x_1895_);
if (v_isSharedCheck_1904_ == 0)
{
v___x_1898_ = v___x_1895_;
v_isShared_1899_ = v_isSharedCheck_1904_;
goto v_resetjp_1897_;
}
else
{
lean_inc(v_a_1896_);
lean_dec(v___x_1895_);
v___x_1898_ = lean_box(0);
v_isShared_1899_ = v_isSharedCheck_1904_;
goto v_resetjp_1897_;
}
v_resetjp_1897_:
{
lean_object* v___x_1900_; lean_object* v___x_1902_; 
v___x_1900_ = l_Lean_Expr_app___override(v___y_1887_, v_a_1896_);
if (v_isShared_1899_ == 0)
{
lean_ctor_set(v___x_1898_, 0, v___x_1900_);
v___x_1902_ = v___x_1898_;
goto v_reusejp_1901_;
}
else
{
lean_object* v_reuseFailAlloc_1903_; 
v_reuseFailAlloc_1903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1903_, 0, v___x_1900_);
v___x_1902_ = v_reuseFailAlloc_1903_;
goto v_reusejp_1901_;
}
v_reusejp_1901_:
{
return v___x_1902_;
}
}
}
else
{
lean_dec_ref(v___y_1887_);
return v___x_1895_;
}
}
}
else
{
lean_object* v___x_1962_; lean_object* v___x_1963_; 
lean_dec_ref(v_x_1866_);
lean_dec_ref(v_x_1865_);
lean_dec_ref(v_major_1864_);
lean_dec_ref(v_a_1863_);
lean_dec(v_a_1859_);
lean_dec_ref(v_recursorInfo_1858_);
v___x_1962_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__14, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__14_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__14);
v___x_1963_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1860_, v_mvarId_1861_, v___x_1962_, v___y_1868_, v___y_1869_, v___y_1870_, v___y_1871_);
return v___x_1963_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___boxed(lean_object* v_recursorInfo_1964_, lean_object* v_a_1965_, lean_object* v_tacticName_1966_, lean_object* v_mvarId_1967_, lean_object* v_indices_1968_, lean_object* v_a_1969_, lean_object* v_major_1970_, lean_object* v_x_1971_, lean_object* v_x_1972_, lean_object* v_x_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_){
_start:
{
lean_object* v_res_1979_; 
v_res_1979_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2(v_recursorInfo_1964_, v_a_1965_, v_tacticName_1966_, v_mvarId_1967_, v_indices_1968_, v_a_1969_, v_major_1970_, v_x_1971_, v_x_1972_, v_x_1973_, v___y_1974_, v___y_1975_, v___y_1976_, v___y_1977_);
lean_dec(v___y_1977_);
lean_dec_ref(v___y_1976_);
lean_dec(v___y_1975_);
lean_dec_ref(v___y_1974_);
lean_dec_ref(v_indices_1968_);
return v_res_1979_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2(lean_object* v_a_1980_, lean_object* v_tacticName_1981_, lean_object* v_mvarId_1982_, lean_object* v_recursorInfo_1983_, lean_object* v_indices_1984_, lean_object* v_a_1985_, lean_object* v_major_1986_, lean_object* v_x_1987_, lean_object* v_x_1988_, lean_object* v_x_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_){
_start:
{
if (lean_obj_tag(v_x_1987_) == 5)
{
lean_object* v_fn_1995_; lean_object* v_arg_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; 
v_fn_1995_ = lean_ctor_get(v_x_1987_, 0);
lean_inc_ref(v_fn_1995_);
v_arg_1996_ = lean_ctor_get(v_x_1987_, 1);
lean_inc_ref(v_arg_1996_);
lean_dec_ref_known(v_x_1987_, 2);
v___x_1997_ = lean_array_set(v_x_1988_, v_x_1989_, v_arg_1996_);
v___x_1998_ = lean_unsigned_to_nat(1u);
v___x_1999_ = lean_nat_sub(v_x_1989_, v___x_1998_);
v___x_2000_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2(v_recursorInfo_1983_, v_a_1980_, v_tacticName_1981_, v_mvarId_1982_, v_indices_1984_, v_a_1985_, v_major_1986_, v_fn_1995_, v___x_1997_, v___x_1999_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_);
return v___x_2000_;
}
else
{
if (lean_obj_tag(v_x_1987_) == 4)
{
lean_object* v_us_2001_; lean_object* v_recursorName_2002_; lean_object* v_univLevelPos_2003_; uint8_t v_depElim_2004_; lean_object* v_paramsPos_2005_; lean_object* v___x_2006_; uint8_t v___x_2007_; lean_object* v___y_2009_; lean_object* v_motive_2010_; lean_object* v___y_2011_; lean_object* v___y_2012_; lean_object* v___y_2013_; lean_object* v___y_2014_; lean_object* v___x_2027_; lean_object* v___x_2028_; 
v_us_2001_ = lean_ctor_get(v_x_1987_, 1);
lean_inc(v_us_2001_);
lean_dec_ref_known(v_x_1987_, 2);
v_recursorName_2002_ = lean_ctor_get(v_recursorInfo_1983_, 0);
lean_inc(v_recursorName_2002_);
v_univLevelPos_2003_ = lean_ctor_get(v_recursorInfo_1983_, 2);
lean_inc(v_univLevelPos_2003_);
v_depElim_2004_ = lean_ctor_get_uint8(v_recursorInfo_1983_, sizeof(void*)*8);
v_paramsPos_2005_ = lean_ctor_get(v_recursorInfo_1983_, 5);
lean_inc(v_paramsPos_2005_);
lean_dec_ref(v_recursorInfo_1983_);
v___x_2006_ = lean_array_mk(v_us_2001_);
v___x_2007_ = 0;
v___x_2027_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__1));
lean_inc(v_mvarId_1982_);
lean_inc(v_tacticName_1981_);
lean_inc(v_a_1980_);
v___x_2028_ = l_List_foldlM___at___00Lean_Meta_mkRecursorAppPrefix_spec__0(v_a_1980_, v___x_2006_, v_tacticName_1981_, v_mvarId_1982_, v___x_2027_, v_univLevelPos_2003_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_);
lean_dec(v_univLevelPos_2003_);
lean_dec_ref(v___x_2006_);
if (lean_obj_tag(v___x_2028_) == 0)
{
lean_object* v_a_2029_; lean_object* v_fst_2030_; lean_object* v_snd_2031_; lean_object* v___x_2033_; uint8_t v_isShared_2034_; uint8_t v_isSharedCheck_2075_; 
v_a_2029_ = lean_ctor_get(v___x_2028_, 0);
lean_inc(v_a_2029_);
lean_dec_ref_known(v___x_2028_, 1);
v_fst_2030_ = lean_ctor_get(v_a_2029_, 0);
v_snd_2031_ = lean_ctor_get(v_a_2029_, 1);
v_isSharedCheck_2075_ = !lean_is_exclusive(v_a_2029_);
if (v_isSharedCheck_2075_ == 0)
{
v___x_2033_ = v_a_2029_;
v_isShared_2034_ = v_isSharedCheck_2075_;
goto v_resetjp_2032_;
}
else
{
lean_inc(v_snd_2031_);
lean_inc(v_fst_2030_);
lean_dec(v_a_2029_);
v___x_2033_ = lean_box(0);
v_isShared_2034_ = v_isSharedCheck_2075_;
goto v_resetjp_2032_;
}
v_resetjp_2032_:
{
lean_object* v___y_2036_; lean_object* v___y_2037_; lean_object* v___y_2038_; lean_object* v___y_2039_; uint8_t v___x_2055_; 
v___x_2055_ = lean_unbox(v_snd_2031_);
lean_dec(v_snd_2031_);
if (v___x_2055_ == 0)
{
uint8_t v___x_2056_; 
v___x_2056_ = l_Lean_Level_isZero(v_a_1980_);
lean_dec(v_a_1980_);
if (v___x_2056_ == 0)
{
lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2061_; 
lean_dec(v_fst_2030_);
lean_dec(v_paramsPos_2005_);
lean_dec_ref(v_x_1988_);
lean_dec_ref(v_major_1986_);
lean_dec_ref(v_a_1985_);
v___x_2057_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__6));
v___x_2058_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__8, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__8_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__8);
v___x_2059_ = l_Lean_MessageData_ofName(v_recursorName_2002_);
if (v_isShared_2034_ == 0)
{
lean_ctor_set_tag(v___x_2033_, 7);
lean_ctor_set(v___x_2033_, 1, v___x_2059_);
lean_ctor_set(v___x_2033_, 0, v___x_2058_);
v___x_2061_ = v___x_2033_;
goto v_reusejp_2060_;
}
else
{
lean_object* v_reuseFailAlloc_2074_; 
v_reuseFailAlloc_2074_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2074_, 0, v___x_2058_);
lean_ctor_set(v_reuseFailAlloc_2074_, 1, v___x_2059_);
v___x_2061_ = v_reuseFailAlloc_2074_;
goto v_reusejp_2060_;
}
v_reusejp_2060_:
{
lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v_a_2066_; lean_object* v___x_2068_; uint8_t v_isShared_2069_; uint8_t v_isSharedCheck_2073_; 
v___x_2062_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__10, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__10_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__10);
v___x_2063_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2063_, 0, v___x_2061_);
lean_ctor_set(v___x_2063_, 1, v___x_2062_);
v___x_2064_ = l_Lean_Meta_mkTacticExMsg(v_tacticName_1981_, v_mvarId_1982_, v___x_2063_);
v___x_2065_ = l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1___redArg(v___x_2057_, v___x_2064_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_);
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
else
{
lean_del_object(v___x_2033_);
lean_dec(v_tacticName_1981_);
v___y_2036_ = v___y_1990_;
v___y_2037_ = v___y_1991_;
v___y_2038_ = v___y_1992_;
v___y_2039_ = v___y_1993_;
goto v___jp_2035_;
}
}
else
{
lean_del_object(v___x_2033_);
lean_dec(v_tacticName_1981_);
lean_dec(v_a_1980_);
v___y_2036_ = v___y_1990_;
v___y_2037_ = v___y_1991_;
v___y_2038_ = v___y_1992_;
v___y_2039_ = v___y_1993_;
goto v___jp_2035_;
}
v___jp_2035_:
{
lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; 
v___x_2040_ = lean_array_to_list(v_fst_2030_);
v___x_2041_ = l_Lean_mkConst(v_recursorName_2002_, v___x_2040_);
v___x_2042_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams(v_mvarId_1982_, v_x_1988_, v_paramsPos_2005_, v___x_2041_, v___y_2036_, v___y_2037_, v___y_2038_, v___y_2039_);
lean_dec_ref(v_x_1988_);
if (lean_obj_tag(v___x_2042_) == 0)
{
if (v_depElim_2004_ == 0)
{
lean_object* v_a_2043_; 
lean_dec_ref(v_major_1986_);
v_a_2043_ = lean_ctor_get(v___x_2042_, 0);
lean_inc(v_a_2043_);
lean_dec_ref_known(v___x_2042_, 1);
v___y_2009_ = v_a_2043_;
v_motive_2010_ = v_a_1985_;
v___y_2011_ = v___y_2036_;
v___y_2012_ = v___y_2037_;
v___y_2013_ = v___y_2038_;
v___y_2014_ = v___y_2039_;
goto v___jp_2008_;
}
else
{
lean_object* v_a_2044_; lean_object* v___x_2045_; 
v_a_2044_ = lean_ctor_get(v___x_2042_, 0);
lean_inc(v_a_2044_);
lean_dec_ref_known(v___x_2042_, 1);
lean_inc(v___y_2039_);
lean_inc_ref(v___y_2038_);
lean_inc(v___y_2037_);
lean_inc_ref(v___y_2036_);
lean_inc_ref(v_major_1986_);
v___x_2045_ = lean_infer_type(v_major_1986_, v___y_2036_, v___y_2037_, v___y_2038_, v___y_2039_);
if (lean_obj_tag(v___x_2045_) == 0)
{
lean_object* v_a_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; 
v_a_2046_ = lean_ctor_get(v___x_2045_, 0);
lean_inc(v_a_2046_);
lean_dec_ref_known(v___x_2045_, 1);
v___x_2047_ = lean_unsigned_to_nat(1u);
v___x_2048_ = lean_mk_empty_array_with_capacity(v___x_2047_);
v___x_2049_ = lean_array_push(v___x_2048_, v_major_1986_);
v___x_2050_ = l_Lean_Expr_abstractM(v_a_1985_, v___x_2049_, v___y_2036_, v___y_2037_, v___y_2038_, v___y_2039_);
lean_dec_ref(v___x_2049_);
if (lean_obj_tag(v___x_2050_) == 0)
{
lean_object* v_a_2051_; lean_object* v___x_2052_; uint8_t v___x_2053_; lean_object* v___x_2054_; 
v_a_2051_ = lean_ctor_get(v___x_2050_, 0);
lean_inc(v_a_2051_);
lean_dec_ref_known(v___x_2050_, 1);
v___x_2052_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__3));
v___x_2053_ = 0;
v___x_2054_ = l_Lean_mkLambda(v___x_2052_, v___x_2053_, v_a_2046_, v_a_2051_);
v___y_2009_ = v_a_2044_;
v_motive_2010_ = v___x_2054_;
v___y_2011_ = v___y_2036_;
v___y_2012_ = v___y_2037_;
v___y_2013_ = v___y_2038_;
v___y_2014_ = v___y_2039_;
goto v___jp_2008_;
}
else
{
lean_dec(v_a_2046_);
lean_dec(v_a_2044_);
return v___x_2050_;
}
}
else
{
lean_dec(v_a_2044_);
lean_dec_ref(v_major_1986_);
lean_dec_ref(v_a_1985_);
return v___x_2045_;
}
}
}
else
{
lean_dec_ref(v_major_1986_);
lean_dec_ref(v_a_1985_);
return v___x_2042_;
}
}
}
}
else
{
lean_object* v_a_2076_; lean_object* v___x_2078_; uint8_t v_isShared_2079_; uint8_t v_isSharedCheck_2083_; 
lean_dec(v_paramsPos_2005_);
lean_dec(v_recursorName_2002_);
lean_dec_ref(v_x_1988_);
lean_dec_ref(v_major_1986_);
lean_dec_ref(v_a_1985_);
lean_dec(v_mvarId_1982_);
lean_dec(v_tacticName_1981_);
lean_dec(v_a_1980_);
v_a_2076_ = lean_ctor_get(v___x_2028_, 0);
v_isSharedCheck_2083_ = !lean_is_exclusive(v___x_2028_);
if (v_isSharedCheck_2083_ == 0)
{
v___x_2078_ = v___x_2028_;
v_isShared_2079_ = v_isSharedCheck_2083_;
goto v_resetjp_2077_;
}
else
{
lean_inc(v_a_2076_);
lean_dec(v___x_2028_);
v___x_2078_ = lean_box(0);
v_isShared_2079_ = v_isSharedCheck_2083_;
goto v_resetjp_2077_;
}
v_resetjp_2077_:
{
lean_object* v___x_2081_; 
if (v_isShared_2079_ == 0)
{
v___x_2081_ = v___x_2078_;
goto v_reusejp_2080_;
}
else
{
lean_object* v_reuseFailAlloc_2082_; 
v_reuseFailAlloc_2082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2082_, 0, v_a_2076_);
v___x_2081_ = v_reuseFailAlloc_2082_;
goto v_reusejp_2080_;
}
v_reusejp_2080_:
{
return v___x_2081_;
}
}
}
v___jp_2008_:
{
uint8_t v___x_2015_; uint8_t v___x_2016_; lean_object* v___x_2017_; 
v___x_2015_ = 1;
v___x_2016_ = 1;
v___x_2017_ = l_Lean_Meta_mkLambdaFVars(v_indices_1984_, v_motive_2010_, v___x_2007_, v___x_2015_, v___x_2007_, v___x_2015_, v___x_2016_, v___y_2011_, v___y_2012_, v___y_2013_, v___y_2014_);
if (lean_obj_tag(v___x_2017_) == 0)
{
lean_object* v_a_2018_; lean_object* v___x_2020_; uint8_t v_isShared_2021_; uint8_t v_isSharedCheck_2026_; 
v_a_2018_ = lean_ctor_get(v___x_2017_, 0);
v_isSharedCheck_2026_ = !lean_is_exclusive(v___x_2017_);
if (v_isSharedCheck_2026_ == 0)
{
v___x_2020_ = v___x_2017_;
v_isShared_2021_ = v_isSharedCheck_2026_;
goto v_resetjp_2019_;
}
else
{
lean_inc(v_a_2018_);
lean_dec(v___x_2017_);
v___x_2020_ = lean_box(0);
v_isShared_2021_ = v_isSharedCheck_2026_;
goto v_resetjp_2019_;
}
v_resetjp_2019_:
{
lean_object* v___x_2022_; lean_object* v___x_2024_; 
v___x_2022_ = l_Lean_Expr_app___override(v___y_2009_, v_a_2018_);
if (v_isShared_2021_ == 0)
{
lean_ctor_set(v___x_2020_, 0, v___x_2022_);
v___x_2024_ = v___x_2020_;
goto v_reusejp_2023_;
}
else
{
lean_object* v_reuseFailAlloc_2025_; 
v_reuseFailAlloc_2025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2025_, 0, v___x_2022_);
v___x_2024_ = v_reuseFailAlloc_2025_;
goto v_reusejp_2023_;
}
v_reusejp_2023_:
{
return v___x_2024_;
}
}
}
else
{
lean_dec_ref(v___y_2009_);
return v___x_2017_;
}
}
}
else
{
lean_object* v___x_2084_; lean_object* v___x_2085_; 
lean_dec_ref(v_x_1988_);
lean_dec_ref(v_x_1987_);
lean_dec_ref(v_major_1986_);
lean_dec_ref(v_a_1985_);
lean_dec_ref(v_recursorInfo_1983_);
lean_dec(v_a_1980_);
v___x_2084_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__14, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__14_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__14);
v___x_2085_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1981_, v_mvarId_1982_, v___x_2084_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_);
return v___x_2085_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2___boxed(lean_object* v_a_2086_, lean_object* v_tacticName_2087_, lean_object* v_mvarId_2088_, lean_object* v_recursorInfo_2089_, lean_object* v_indices_2090_, lean_object* v_a_2091_, lean_object* v_major_2092_, lean_object* v_x_2093_, lean_object* v_x_2094_, lean_object* v_x_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_){
_start:
{
lean_object* v_res_2101_; 
v_res_2101_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2(v_a_2086_, v_tacticName_2087_, v_mvarId_2088_, v_recursorInfo_2089_, v_indices_2090_, v_a_2091_, v_major_2092_, v_x_2093_, v_x_2094_, v_x_2095_, v___y_2096_, v___y_2097_, v___y_2098_, v___y_2099_);
lean_dec(v___y_2099_);
lean_dec_ref(v___y_2098_);
lean_dec(v___y_2097_);
lean_dec_ref(v___y_2096_);
lean_dec(v_x_2095_);
lean_dec_ref(v_indices_2090_);
return v_res_2101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkRecursorAppPrefix(lean_object* v_mvarId_2102_, lean_object* v_tacticName_2103_, lean_object* v_majorFVarId_2104_, lean_object* v_recursorInfo_2105_, lean_object* v_indices_2106_, lean_object* v_a_2107_, lean_object* v_a_2108_, lean_object* v_a_2109_, lean_object* v_a_2110_){
_start:
{
lean_object* v___x_2112_; 
lean_inc(v_mvarId_2102_);
v___x_2112_ = l_Lean_MVarId_getType(v_mvarId_2102_, v_a_2107_, v_a_2108_, v_a_2109_, v_a_2110_);
if (lean_obj_tag(v___x_2112_) == 0)
{
lean_object* v_a_2113_; lean_object* v___x_2114_; 
v_a_2113_ = lean_ctor_get(v___x_2112_, 0);
lean_inc_n(v_a_2113_, 2);
lean_dec_ref_known(v___x_2112_, 1);
v___x_2114_ = l_Lean_Meta_getLevel(v_a_2113_, v_a_2107_, v_a_2108_, v_a_2109_, v_a_2110_);
if (lean_obj_tag(v___x_2114_) == 0)
{
lean_object* v_a_2115_; lean_object* v___x_2116_; 
v_a_2115_ = lean_ctor_get(v___x_2114_, 0);
lean_inc(v_a_2115_);
lean_dec_ref_known(v___x_2114_, 1);
v___x_2116_ = l_Lean_Meta_normalizeLevel(v_a_2115_, v_a_2107_, v_a_2108_, v_a_2109_, v_a_2110_);
if (lean_obj_tag(v___x_2116_) == 0)
{
lean_object* v_a_2117_; lean_object* v_major_2118_; lean_object* v___x_2119_; 
v_a_2117_ = lean_ctor_get(v___x_2116_, 0);
lean_inc(v_a_2117_);
lean_dec_ref_known(v___x_2116_, 1);
lean_inc(v_majorFVarId_2104_);
v_major_2118_ = l_Lean_mkFVar(v_majorFVarId_2104_);
v___x_2119_ = l_Lean_FVarId_getDecl___redArg(v_majorFVarId_2104_, v_a_2107_, v_a_2109_, v_a_2110_);
if (lean_obj_tag(v___x_2119_) == 0)
{
lean_object* v_a_2120_; lean_object* v_typeName_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; 
v_a_2120_ = lean_ctor_get(v___x_2119_, 0);
lean_inc(v_a_2120_);
lean_dec_ref_known(v___x_2119_, 1);
v_typeName_2121_ = lean_ctor_get(v_recursorInfo_2105_, 1);
v___x_2122_ = l_Lean_LocalDecl_type(v_a_2120_);
lean_dec(v_a_2120_);
lean_inc_ref(v___x_2122_);
v___x_2123_ = l_Lean_Meta_whnfUntil(v___x_2122_, v_typeName_2121_, v_a_2107_, v_a_2108_, v_a_2109_, v_a_2110_);
if (lean_obj_tag(v___x_2123_) == 0)
{
lean_object* v_a_2124_; 
v_a_2124_ = lean_ctor_get(v___x_2123_, 0);
lean_inc(v_a_2124_);
lean_dec_ref_known(v___x_2123_, 1);
if (lean_obj_tag(v_a_2124_) == 1)
{
lean_object* v_val_2125_; lean_object* v_dummy_2126_; lean_object* v_nargs_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; 
lean_dec_ref(v___x_2122_);
v_val_2125_ = lean_ctor_get(v_a_2124_, 0);
lean_inc(v_val_2125_);
lean_dec_ref_known(v_a_2124_, 1);
v_dummy_2126_ = lean_obj_once(&l_Lean_Meta_getMajorTypeIndices___closed__0, &l_Lean_Meta_getMajorTypeIndices___closed__0_once, _init_l_Lean_Meta_getMajorTypeIndices___closed__0);
v_nargs_2127_ = l_Lean_Expr_getAppNumArgs(v_val_2125_);
lean_inc(v_nargs_2127_);
v___x_2128_ = lean_mk_array(v_nargs_2127_, v_dummy_2126_);
v___x_2129_ = lean_unsigned_to_nat(1u);
v___x_2130_ = lean_nat_sub(v_nargs_2127_, v___x_2129_);
lean_dec(v_nargs_2127_);
v___x_2131_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2(v_a_2117_, v_tacticName_2103_, v_mvarId_2102_, v_recursorInfo_2105_, v_indices_2106_, v_a_2113_, v_major_2118_, v_val_2125_, v___x_2128_, v___x_2130_, v_a_2107_, v_a_2108_, v_a_2109_, v_a_2110_);
lean_dec(v___x_2130_);
return v___x_2131_;
}
else
{
lean_object* v___x_2132_; 
lean_dec(v_a_2124_);
lean_dec_ref(v_major_2118_);
lean_dec(v_a_2117_);
lean_dec(v_a_2113_);
lean_dec_ref(v_recursorInfo_2105_);
v___x_2132_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg(v_tacticName_2103_, v_mvarId_2102_, v___x_2122_, v_a_2107_, v_a_2108_, v_a_2109_, v_a_2110_);
return v___x_2132_;
}
}
else
{
lean_object* v_a_2133_; lean_object* v___x_2135_; uint8_t v_isShared_2136_; uint8_t v_isSharedCheck_2140_; 
lean_dec_ref(v___x_2122_);
lean_dec_ref(v_major_2118_);
lean_dec(v_a_2117_);
lean_dec(v_a_2113_);
lean_dec_ref(v_recursorInfo_2105_);
lean_dec(v_tacticName_2103_);
lean_dec(v_mvarId_2102_);
v_a_2133_ = lean_ctor_get(v___x_2123_, 0);
v_isSharedCheck_2140_ = !lean_is_exclusive(v___x_2123_);
if (v_isSharedCheck_2140_ == 0)
{
v___x_2135_ = v___x_2123_;
v_isShared_2136_ = v_isSharedCheck_2140_;
goto v_resetjp_2134_;
}
else
{
lean_inc(v_a_2133_);
lean_dec(v___x_2123_);
v___x_2135_ = lean_box(0);
v_isShared_2136_ = v_isSharedCheck_2140_;
goto v_resetjp_2134_;
}
v_resetjp_2134_:
{
lean_object* v___x_2138_; 
if (v_isShared_2136_ == 0)
{
v___x_2138_ = v___x_2135_;
goto v_reusejp_2137_;
}
else
{
lean_object* v_reuseFailAlloc_2139_; 
v_reuseFailAlloc_2139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2139_, 0, v_a_2133_);
v___x_2138_ = v_reuseFailAlloc_2139_;
goto v_reusejp_2137_;
}
v_reusejp_2137_:
{
return v___x_2138_;
}
}
}
}
else
{
lean_object* v_a_2141_; lean_object* v___x_2143_; uint8_t v_isShared_2144_; uint8_t v_isSharedCheck_2148_; 
lean_dec_ref(v_major_2118_);
lean_dec(v_a_2117_);
lean_dec(v_a_2113_);
lean_dec_ref(v_recursorInfo_2105_);
lean_dec(v_tacticName_2103_);
lean_dec(v_mvarId_2102_);
v_a_2141_ = lean_ctor_get(v___x_2119_, 0);
v_isSharedCheck_2148_ = !lean_is_exclusive(v___x_2119_);
if (v_isSharedCheck_2148_ == 0)
{
v___x_2143_ = v___x_2119_;
v_isShared_2144_ = v_isSharedCheck_2148_;
goto v_resetjp_2142_;
}
else
{
lean_inc(v_a_2141_);
lean_dec(v___x_2119_);
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
else
{
lean_object* v_a_2149_; lean_object* v___x_2151_; uint8_t v_isShared_2152_; uint8_t v_isSharedCheck_2156_; 
lean_dec(v_a_2113_);
lean_dec_ref(v_recursorInfo_2105_);
lean_dec(v_majorFVarId_2104_);
lean_dec(v_tacticName_2103_);
lean_dec(v_mvarId_2102_);
v_a_2149_ = lean_ctor_get(v___x_2116_, 0);
v_isSharedCheck_2156_ = !lean_is_exclusive(v___x_2116_);
if (v_isSharedCheck_2156_ == 0)
{
v___x_2151_ = v___x_2116_;
v_isShared_2152_ = v_isSharedCheck_2156_;
goto v_resetjp_2150_;
}
else
{
lean_inc(v_a_2149_);
lean_dec(v___x_2116_);
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
lean_dec(v_a_2113_);
lean_dec_ref(v_recursorInfo_2105_);
lean_dec(v_majorFVarId_2104_);
lean_dec(v_tacticName_2103_);
lean_dec(v_mvarId_2102_);
v_a_2157_ = lean_ctor_get(v___x_2114_, 0);
v_isSharedCheck_2164_ = !lean_is_exclusive(v___x_2114_);
if (v_isSharedCheck_2164_ == 0)
{
v___x_2159_ = v___x_2114_;
v_isShared_2160_ = v_isSharedCheck_2164_;
goto v_resetjp_2158_;
}
else
{
lean_inc(v_a_2157_);
lean_dec(v___x_2114_);
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
else
{
lean_dec_ref(v_recursorInfo_2105_);
lean_dec(v_majorFVarId_2104_);
lean_dec(v_tacticName_2103_);
lean_dec(v_mvarId_2102_);
return v___x_2112_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkRecursorAppPrefix___boxed(lean_object* v_mvarId_2165_, lean_object* v_tacticName_2166_, lean_object* v_majorFVarId_2167_, lean_object* v_recursorInfo_2168_, lean_object* v_indices_2169_, lean_object* v_a_2170_, lean_object* v_a_2171_, lean_object* v_a_2172_, lean_object* v_a_2173_, lean_object* v_a_2174_){
_start:
{
lean_object* v_res_2175_; 
v_res_2175_ = l_Lean_Meta_mkRecursorAppPrefix(v_mvarId_2165_, v_tacticName_2166_, v_majorFVarId_2167_, v_recursorInfo_2168_, v_indices_2169_, v_a_2170_, v_a_2171_, v_a_2172_, v_a_2173_);
lean_dec(v_a_2173_);
lean_dec_ref(v_a_2172_);
lean_dec(v_a_2171_);
lean_dec_ref(v_a_2170_);
lean_dec_ref(v_indices_2169_);
return v_res_2175_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1(lean_object* v_00_u03b1_2176_, lean_object* v_name_2177_, lean_object* v_msg_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_){
_start:
{
lean_object* v___x_2184_; 
v___x_2184_ = l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1___redArg(v_name_2177_, v_msg_2178_, v___y_2179_, v___y_2180_, v___y_2181_, v___y_2182_);
return v___x_2184_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1___boxed(lean_object* v_00_u03b1_2185_, lean_object* v_name_2186_, lean_object* v_msg_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_){
_start:
{
lean_object* v_res_2193_; 
v_res_2193_ = l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1(v_00_u03b1_2185_, v_name_2186_, v_msg_2187_, v___y_2188_, v___y_2189_, v___y_2190_, v___y_2191_);
lean_dec(v___y_2191_);
lean_dec_ref(v___y_2190_);
lean_dec(v___y_2189_);
lean_dec_ref(v___y_2188_);
return v_res_2193_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___redArg(lean_object* v_mvarId_2194_, lean_object* v_x_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_){
_start:
{
lean_object* v___x_2201_; 
v___x_2201_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_2194_, v_x_2195_, v___y_2196_, v___y_2197_, v___y_2198_, v___y_2199_);
if (lean_obj_tag(v___x_2201_) == 0)
{
lean_object* v_a_2202_; lean_object* v___x_2204_; uint8_t v_isShared_2205_; uint8_t v_isSharedCheck_2209_; 
v_a_2202_ = lean_ctor_get(v___x_2201_, 0);
v_isSharedCheck_2209_ = !lean_is_exclusive(v___x_2201_);
if (v_isSharedCheck_2209_ == 0)
{
v___x_2204_ = v___x_2201_;
v_isShared_2205_ = v_isSharedCheck_2209_;
goto v_resetjp_2203_;
}
else
{
lean_inc(v_a_2202_);
lean_dec(v___x_2201_);
v___x_2204_ = lean_box(0);
v_isShared_2205_ = v_isSharedCheck_2209_;
goto v_resetjp_2203_;
}
v_resetjp_2203_:
{
lean_object* v___x_2207_; 
if (v_isShared_2205_ == 0)
{
v___x_2207_ = v___x_2204_;
goto v_reusejp_2206_;
}
else
{
lean_object* v_reuseFailAlloc_2208_; 
v_reuseFailAlloc_2208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2208_, 0, v_a_2202_);
v___x_2207_ = v_reuseFailAlloc_2208_;
goto v_reusejp_2206_;
}
v_reusejp_2206_:
{
return v___x_2207_;
}
}
}
else
{
lean_object* v_a_2210_; lean_object* v___x_2212_; uint8_t v_isShared_2213_; uint8_t v_isSharedCheck_2217_; 
v_a_2210_ = lean_ctor_get(v___x_2201_, 0);
v_isSharedCheck_2217_ = !lean_is_exclusive(v___x_2201_);
if (v_isSharedCheck_2217_ == 0)
{
v___x_2212_ = v___x_2201_;
v_isShared_2213_ = v_isSharedCheck_2217_;
goto v_resetjp_2211_;
}
else
{
lean_inc(v_a_2210_);
lean_dec(v___x_2201_);
v___x_2212_ = lean_box(0);
v_isShared_2213_ = v_isSharedCheck_2217_;
goto v_resetjp_2211_;
}
v_resetjp_2211_:
{
lean_object* v___x_2215_; 
if (v_isShared_2213_ == 0)
{
v___x_2215_ = v___x_2212_;
goto v_reusejp_2214_;
}
else
{
lean_object* v_reuseFailAlloc_2216_; 
v_reuseFailAlloc_2216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2216_, 0, v_a_2210_);
v___x_2215_ = v_reuseFailAlloc_2216_;
goto v_reusejp_2214_;
}
v_reusejp_2214_:
{
return v___x_2215_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___redArg___boxed(lean_object* v_mvarId_2218_, lean_object* v_x_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_){
_start:
{
lean_object* v_res_2225_; 
v_res_2225_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___redArg(v_mvarId_2218_, v_x_2219_, v___y_2220_, v___y_2221_, v___y_2222_, v___y_2223_);
lean_dec(v___y_2223_);
lean_dec_ref(v___y_2222_);
lean_dec(v___y_2221_);
lean_dec_ref(v___y_2220_);
return v_res_2225_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3(lean_object* v_00_u03b1_2226_, lean_object* v_mvarId_2227_, lean_object* v_x_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_){
_start:
{
lean_object* v___x_2234_; 
v___x_2234_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___redArg(v_mvarId_2227_, v_x_2228_, v___y_2229_, v___y_2230_, v___y_2231_, v___y_2232_);
return v___x_2234_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___boxed(lean_object* v_00_u03b1_2235_, lean_object* v_mvarId_2236_, lean_object* v_x_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_){
_start:
{
lean_object* v_res_2243_; 
v_res_2243_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3(v_00_u03b1_2235_, v_mvarId_2236_, v_x_2237_, v___y_2238_, v___y_2239_, v___y_2240_, v___y_2241_);
lean_dec(v___y_2241_);
lean_dec_ref(v___y_2240_);
lean_dec(v___y_2239_);
lean_dec_ref(v___y_2238_);
return v_res_2243_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_induction_spec__2(lean_object* v_fst_2244_, lean_object* v_as_2245_, size_t v_sz_2246_, size_t v_i_2247_, lean_object* v_b_2248_){
_start:
{
uint8_t v___x_2249_; 
v___x_2249_ = lean_usize_dec_lt(v_i_2247_, v_sz_2246_);
if (v___x_2249_ == 0)
{
return v_b_2248_;
}
else
{
lean_object* v_fst_2250_; lean_object* v_snd_2251_; lean_object* v___x_2253_; uint8_t v_isShared_2254_; uint8_t v_isSharedCheck_2269_; 
v_fst_2250_ = lean_ctor_get(v_b_2248_, 0);
v_snd_2251_ = lean_ctor_get(v_b_2248_, 1);
v_isSharedCheck_2269_ = !lean_is_exclusive(v_b_2248_);
if (v_isSharedCheck_2269_ == 0)
{
v___x_2253_ = v_b_2248_;
v_isShared_2254_ = v_isSharedCheck_2269_;
goto v_resetjp_2252_;
}
else
{
lean_inc(v_snd_2251_);
lean_inc(v_fst_2250_);
lean_dec(v_b_2248_);
v___x_2253_ = lean_box(0);
v_isShared_2254_ = v_isSharedCheck_2269_;
goto v_resetjp_2252_;
}
v_resetjp_2252_:
{
lean_object* v___x_2255_; lean_object* v_a_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2264_; 
v___x_2255_ = lean_box(0);
v_a_2256_ = lean_array_uget_borrowed(v_as_2245_, v_i_2247_);
v___x_2257_ = l_Lean_Expr_fvarId_x21(v_a_2256_);
v___x_2258_ = lean_array_get_borrowed(v___x_2255_, v_fst_2244_, v_snd_2251_);
lean_inc(v___x_2258_);
v___x_2259_ = l_Lean_mkFVar(v___x_2258_);
v___x_2260_ = l_Lean_Meta_FVarSubst_insert(v_fst_2250_, v___x_2257_, v___x_2259_);
v___x_2261_ = lean_unsigned_to_nat(1u);
v___x_2262_ = lean_nat_add(v_snd_2251_, v___x_2261_);
lean_dec(v_snd_2251_);
if (v_isShared_2254_ == 0)
{
lean_ctor_set(v___x_2253_, 1, v___x_2262_);
lean_ctor_set(v___x_2253_, 0, v___x_2260_);
v___x_2264_ = v___x_2253_;
goto v_reusejp_2263_;
}
else
{
lean_object* v_reuseFailAlloc_2268_; 
v_reuseFailAlloc_2268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2268_, 0, v___x_2260_);
lean_ctor_set(v_reuseFailAlloc_2268_, 1, v___x_2262_);
v___x_2264_ = v_reuseFailAlloc_2268_;
goto v_reusejp_2263_;
}
v_reusejp_2263_:
{
size_t v___x_2265_; size_t v___x_2266_; 
v___x_2265_ = ((size_t)1ULL);
v___x_2266_ = lean_usize_add(v_i_2247_, v___x_2265_);
v_i_2247_ = v___x_2266_;
v_b_2248_ = v___x_2264_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_induction_spec__2___boxed(lean_object* v_fst_2270_, lean_object* v_as_2271_, lean_object* v_sz_2272_, lean_object* v_i_2273_, lean_object* v_b_2274_){
_start:
{
size_t v_sz_boxed_2275_; size_t v_i_boxed_2276_; lean_object* v_res_2277_; 
v_sz_boxed_2275_ = lean_unbox_usize(v_sz_2272_);
lean_dec(v_sz_2272_);
v_i_boxed_2276_ = lean_unbox_usize(v_i_2273_);
lean_dec(v_i_2273_);
v_res_2277_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_induction_spec__2(v_fst_2270_, v_as_2271_, v_sz_boxed_2275_, v_i_boxed_2276_, v_b_2274_);
lean_dec_ref(v_as_2271_);
lean_dec_ref(v_fst_2270_);
return v_res_2277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4___lam__0(lean_object* v_snd_2278_, lean_object* v___x_2279_, lean_object* v_fst_2280_, lean_object* v_a_2281_, lean_object* v___x_2282_, lean_object* v_givenNames_2283_, lean_object* v_fst_2284_, lean_object* v___x_2285_, lean_object* v_fst_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_){
_start:
{
lean_object* v___x_2292_; 
lean_inc_ref(v_a_2281_);
lean_inc(v_snd_2278_);
v___x_2292_ = l_Lean_Meta_mkRecursorAppPrefix(v_snd_2278_, v___x_2279_, v_fst_2280_, v_a_2281_, v___x_2282_, v___y_2287_, v___y_2288_, v___y_2289_, v___y_2290_);
if (lean_obj_tag(v___x_2292_) == 0)
{
lean_object* v_a_2293_; lean_object* v___x_2294_; 
v_a_2293_ = lean_ctor_get(v___x_2292_, 0);
lean_inc(v_a_2293_);
lean_dec_ref_known(v___x_2292_, 1);
v___x_2294_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize(v_snd_2278_, v_givenNames_2283_, v_a_2281_, v_fst_2284_, v___x_2285_, v___x_2282_, v_fst_2286_, v_a_2293_, v___y_2287_, v___y_2288_, v___y_2289_, v___y_2290_);
lean_dec_ref(v_a_2281_);
return v___x_2294_;
}
else
{
lean_object* v_a_2295_; lean_object* v___x_2297_; uint8_t v_isShared_2298_; uint8_t v_isSharedCheck_2302_; 
lean_dec(v_fst_2286_);
lean_dec_ref(v___x_2285_);
lean_dec_ref(v_a_2281_);
lean_dec(v_snd_2278_);
v_a_2295_ = lean_ctor_get(v___x_2292_, 0);
v_isSharedCheck_2302_ = !lean_is_exclusive(v___x_2292_);
if (v_isSharedCheck_2302_ == 0)
{
v___x_2297_ = v___x_2292_;
v_isShared_2298_ = v_isSharedCheck_2302_;
goto v_resetjp_2296_;
}
else
{
lean_inc(v_a_2295_);
lean_dec(v___x_2292_);
v___x_2297_ = lean_box(0);
v_isShared_2298_ = v_isSharedCheck_2302_;
goto v_resetjp_2296_;
}
v_resetjp_2296_:
{
lean_object* v___x_2300_; 
if (v_isShared_2298_ == 0)
{
v___x_2300_ = v___x_2297_;
goto v_reusejp_2299_;
}
else
{
lean_object* v_reuseFailAlloc_2301_; 
v_reuseFailAlloc_2301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2301_, 0, v_a_2295_);
v___x_2300_ = v_reuseFailAlloc_2301_;
goto v_reusejp_2299_;
}
v_reusejp_2299_:
{
return v___x_2300_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4___lam__0___boxed(lean_object* v_snd_2303_, lean_object* v___x_2304_, lean_object* v_fst_2305_, lean_object* v_a_2306_, lean_object* v___x_2307_, lean_object* v_givenNames_2308_, lean_object* v_fst_2309_, lean_object* v___x_2310_, lean_object* v_fst_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_){
_start:
{
lean_object* v_res_2317_; 
v_res_2317_ = l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4___lam__0(v_snd_2303_, v___x_2304_, v_fst_2305_, v_a_2306_, v___x_2307_, v_givenNames_2308_, v_fst_2309_, v___x_2310_, v_fst_2311_, v___y_2312_, v___y_2313_, v___y_2314_, v___y_2315_);
lean_dec(v___y_2315_);
lean_dec_ref(v___y_2314_);
lean_dec(v___y_2313_);
lean_dec_ref(v___y_2312_);
lean_dec_ref(v_fst_2309_);
lean_dec_ref(v_givenNames_2308_);
lean_dec_ref(v___x_2307_);
return v_res_2317_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_induction_spec__1(size_t v_sz_2318_, size_t v_i_2319_, lean_object* v_bs_2320_){
_start:
{
uint8_t v___x_2321_; 
v___x_2321_ = lean_usize_dec_lt(v_i_2319_, v_sz_2318_);
if (v___x_2321_ == 0)
{
return v_bs_2320_;
}
else
{
lean_object* v_v_2322_; lean_object* v___x_2323_; lean_object* v_bs_x27_2324_; lean_object* v___x_2325_; size_t v___x_2326_; size_t v___x_2327_; lean_object* v___x_2328_; 
v_v_2322_ = lean_array_uget(v_bs_2320_, v_i_2319_);
v___x_2323_ = lean_unsigned_to_nat(0u);
v_bs_x27_2324_ = lean_array_uset(v_bs_2320_, v_i_2319_, v___x_2323_);
v___x_2325_ = l_Lean_Expr_fvarId_x21(v_v_2322_);
lean_dec(v_v_2322_);
v___x_2326_ = ((size_t)1ULL);
v___x_2327_ = lean_usize_add(v_i_2319_, v___x_2326_);
v___x_2328_ = lean_array_uset(v_bs_x27_2324_, v_i_2319_, v___x_2325_);
v_i_2319_ = v___x_2327_;
v_bs_2320_ = v___x_2328_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_induction_spec__1___boxed(lean_object* v_sz_2330_, lean_object* v_i_2331_, lean_object* v_bs_2332_){
_start:
{
size_t v_sz_boxed_2333_; size_t v_i_boxed_2334_; lean_object* v_res_2335_; 
v_sz_boxed_2333_ = lean_unbox_usize(v_sz_2330_);
lean_dec(v_sz_2330_);
v_i_boxed_2334_ = lean_unbox_usize(v_i_2331_);
lean_dec(v_i_2331_);
v_res_2335_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_induction_spec__1(v_sz_boxed_2333_, v_i_boxed_2334_, v_bs_2332_);
return v_res_2335_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_MVarId_induction_spec__0(lean_object* v_majorTypeArgs_2336_, lean_object* v_val_2337_, lean_object* v_mvarId_2338_, lean_object* v_as_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_){
_start:
{
if (lean_obj_tag(v_as_2339_) == 0)
{
lean_object* v___x_2345_; lean_object* v___x_2346_; 
lean_dec(v_mvarId_2338_);
lean_dec_ref(v_val_2337_);
v___x_2345_ = lean_box(0);
v___x_2346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2346_, 0, v___x_2345_);
return v___x_2346_;
}
else
{
lean_object* v_head_2347_; 
v_head_2347_ = lean_ctor_get(v_as_2339_, 0);
lean_inc(v_head_2347_);
if (lean_obj_tag(v_head_2347_) == 0)
{
lean_object* v_tail_2348_; 
v_tail_2348_ = lean_ctor_get(v_as_2339_, 1);
lean_inc(v_tail_2348_);
lean_dec_ref_known(v_as_2339_, 2);
v_as_2339_ = v_tail_2348_;
goto _start;
}
else
{
lean_object* v_tail_2350_; lean_object* v___x_2352_; uint8_t v_isShared_2353_; uint8_t v_isSharedCheck_2373_; 
v_tail_2350_ = lean_ctor_get(v_as_2339_, 1);
v_isSharedCheck_2373_ = !lean_is_exclusive(v_as_2339_);
if (v_isSharedCheck_2373_ == 0)
{
lean_object* v_unused_2374_; 
v_unused_2374_ = lean_ctor_get(v_as_2339_, 0);
lean_dec(v_unused_2374_);
v___x_2352_ = v_as_2339_;
v_isShared_2353_ = v_isSharedCheck_2373_;
goto v_resetjp_2351_;
}
else
{
lean_inc(v_tail_2350_);
lean_dec(v_as_2339_);
v___x_2352_ = lean_box(0);
v_isShared_2353_ = v_isSharedCheck_2373_;
goto v_resetjp_2351_;
}
v_resetjp_2351_:
{
lean_object* v_val_2354_; lean_object* v___x_2356_; uint8_t v_isShared_2357_; uint8_t v_isSharedCheck_2372_; 
v_val_2354_ = lean_ctor_get(v_head_2347_, 0);
v_isSharedCheck_2372_ = !lean_is_exclusive(v_head_2347_);
if (v_isSharedCheck_2372_ == 0)
{
v___x_2356_ = v_head_2347_;
v_isShared_2357_ = v_isSharedCheck_2372_;
goto v_resetjp_2355_;
}
else
{
lean_inc(v_val_2354_);
lean_dec(v_head_2347_);
v___x_2356_ = lean_box(0);
v_isShared_2357_ = v_isSharedCheck_2372_;
goto v_resetjp_2355_;
}
v_resetjp_2355_:
{
lean_object* v___x_2358_; uint8_t v___x_2359_; 
v___x_2358_ = lean_array_get_size(v_majorTypeArgs_2336_);
v___x_2359_ = lean_nat_dec_le(v___x_2358_, v_val_2354_);
lean_dec(v_val_2354_);
if (v___x_2359_ == 0)
{
lean_del_object(v___x_2356_);
lean_del_object(v___x_2352_);
v_as_2339_ = v_tail_2350_;
goto _start;
}
else
{
lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2365_; 
v___x_2361_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1));
v___x_2362_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__5, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__5);
lean_inc_ref(v_val_2337_);
v___x_2363_ = l_Lean_indentExpr(v_val_2337_);
if (v_isShared_2353_ == 0)
{
lean_ctor_set_tag(v___x_2352_, 7);
lean_ctor_set(v___x_2352_, 1, v___x_2363_);
lean_ctor_set(v___x_2352_, 0, v___x_2362_);
v___x_2365_ = v___x_2352_;
goto v_reusejp_2364_;
}
else
{
lean_object* v_reuseFailAlloc_2371_; 
v_reuseFailAlloc_2371_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2371_, 0, v___x_2362_);
lean_ctor_set(v_reuseFailAlloc_2371_, 1, v___x_2363_);
v___x_2365_ = v_reuseFailAlloc_2371_;
goto v_reusejp_2364_;
}
v_reusejp_2364_:
{
lean_object* v___x_2367_; 
if (v_isShared_2357_ == 0)
{
lean_ctor_set(v___x_2356_, 0, v___x_2365_);
v___x_2367_ = v___x_2356_;
goto v_reusejp_2366_;
}
else
{
lean_object* v_reuseFailAlloc_2370_; 
v_reuseFailAlloc_2370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2370_, 0, v___x_2365_);
v___x_2367_ = v_reuseFailAlloc_2370_;
goto v_reusejp_2366_;
}
v_reusejp_2366_:
{
lean_object* v___x_2368_; 
lean_inc(v_mvarId_2338_);
v___x_2368_ = l_Lean_Meta_throwTacticEx___redArg(v___x_2361_, v_mvarId_2338_, v___x_2367_, v___y_2340_, v___y_2341_, v___y_2342_, v___y_2343_);
if (lean_obj_tag(v___x_2368_) == 0)
{
lean_dec_ref_known(v___x_2368_, 1);
v_as_2339_ = v_tail_2350_;
goto _start;
}
else
{
lean_dec(v_tail_2350_);
lean_dec(v_mvarId_2338_);
lean_dec_ref(v_val_2337_);
return v___x_2368_;
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
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_MVarId_induction_spec__0___boxed(lean_object* v_majorTypeArgs_2375_, lean_object* v_val_2376_, lean_object* v_mvarId_2377_, lean_object* v_as_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_){
_start:
{
lean_object* v_res_2384_; 
v_res_2384_ = l_List_forM___at___00Lean_MVarId_induction_spec__0(v_majorTypeArgs_2375_, v_val_2376_, v_mvarId_2377_, v_as_2378_, v___y_2379_, v___y_2380_, v___y_2381_, v___y_2382_);
lean_dec(v___y_2382_);
lean_dec_ref(v___y_2381_);
lean_dec(v___y_2380_);
lean_dec_ref(v___y_2379_);
lean_dec_ref(v_majorTypeArgs_2375_);
return v_res_2384_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__1(void){
_start:
{
lean_object* v___x_2386_; lean_object* v___x_2387_; 
v___x_2386_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__0));
v___x_2387_ = l_Lean_stringToMessageData(v___x_2386_);
return v___x_2387_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__3(void){
_start:
{
lean_object* v___x_2389_; lean_object* v___x_2390_; 
v___x_2389_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__2));
v___x_2390_ = l_Lean_stringToMessageData(v___x_2389_);
return v___x_2390_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__5(void){
_start:
{
lean_object* v___x_2392_; lean_object* v___x_2393_; 
v___x_2392_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__4));
v___x_2393_ = l_Lean_stringToMessageData(v___x_2392_);
return v___x_2393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4(lean_object* v_a_2394_, lean_object* v_val_2395_, lean_object* v_mvarId_2396_, lean_object* v_majorFVarId_2397_, lean_object* v_givenNames_2398_, lean_object* v_recursorName_2399_, lean_object* v_x_2400_, lean_object* v_x_2401_, lean_object* v_x_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_){
_start:
{
if (lean_obj_tag(v_x_2400_) == 5)
{
lean_object* v_fn_2408_; lean_object* v_arg_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; 
v_fn_2408_ = lean_ctor_get(v_x_2400_, 0);
lean_inc_ref(v_fn_2408_);
v_arg_2409_ = lean_ctor_get(v_x_2400_, 1);
lean_inc_ref(v_arg_2409_);
lean_dec_ref_known(v_x_2400_, 2);
v___x_2410_ = lean_array_set(v_x_2401_, v_x_2402_, v_arg_2409_);
v___x_2411_ = lean_unsigned_to_nat(1u);
v___x_2412_ = lean_nat_sub(v_x_2402_, v___x_2411_);
lean_dec(v_x_2402_);
v_x_2400_ = v_fn_2408_;
v_x_2401_ = v___x_2410_;
v_x_2402_ = v___x_2412_;
goto _start;
}
else
{
uint8_t v_depElim_2414_; lean_object* v_paramsPos_2415_; lean_object* v___x_2416_; 
lean_dec(v_x_2402_);
lean_dec_ref(v_x_2400_);
v_depElim_2414_ = lean_ctor_get_uint8(v_a_2394_, sizeof(void*)*8);
v_paramsPos_2415_ = lean_ctor_get(v_a_2394_, 5);
lean_inc(v_paramsPos_2415_);
lean_inc(v_mvarId_2396_);
lean_inc_ref(v_val_2395_);
v___x_2416_ = l_List_forM___at___00Lean_MVarId_induction_spec__0(v_x_2401_, v_val_2395_, v_mvarId_2396_, v_paramsPos_2415_, v___y_2403_, v___y_2404_, v___y_2405_, v___y_2406_);
lean_dec_ref(v_x_2401_);
if (lean_obj_tag(v___x_2416_) == 0)
{
lean_object* v___x_2417_; lean_object* v___y_2419_; lean_object* v___y_2420_; lean_object* v___y_2421_; lean_object* v___y_2422_; lean_object* v___y_2423_; lean_object* v___y_2424_; lean_object* v___y_2425_; size_t v___y_2426_; lean_object* v___y_2427_; lean_object* v___y_2428_; lean_object* v___y_2429_; lean_object* v___y_2430_; lean_object* v___x_2435_; 
lean_dec_ref_known(v___x_2416_, 1);
v___x_2417_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1));
lean_inc_ref(v_a_2394_);
lean_inc(v_mvarId_2396_);
v___x_2435_ = l_Lean_Meta_getMajorTypeIndices(v_mvarId_2396_, v___x_2417_, v_a_2394_, v_val_2395_, v___y_2403_, v___y_2404_, v___y_2405_, v___y_2406_);
if (lean_obj_tag(v___x_2435_) == 0)
{
lean_object* v_a_2436_; lean_object* v___x_2437_; 
v_a_2436_ = lean_ctor_get(v___x_2435_, 0);
lean_inc(v_a_2436_);
lean_dec_ref_known(v___x_2435_, 1);
lean_inc(v_mvarId_2396_);
v___x_2437_ = l_Lean_MVarId_getType(v_mvarId_2396_, v___y_2403_, v___y_2404_, v___y_2405_, v___y_2406_);
if (lean_obj_tag(v___x_2437_) == 0)
{
lean_object* v_a_2438_; lean_object* v_cls_2439_; lean_object* v___y_2441_; lean_object* v___y_2442_; lean_object* v___y_2443_; lean_object* v___y_2444_; 
v_a_2438_ = lean_ctor_get(v___x_2437_, 0);
lean_inc(v_a_2438_);
lean_dec_ref_known(v___x_2437_, 1);
v_cls_2439_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__2));
if (v_depElim_2414_ == 0)
{
lean_object* v___x_2527_; lean_object* v_a_2528_; lean_object* v___x_2530_; uint8_t v_isShared_2531_; uint8_t v_isSharedCheck_2550_; 
lean_inc(v_majorFVarId_2397_);
v___x_2527_ = l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2___redArg(v_a_2438_, v_majorFVarId_2397_, v___y_2404_);
v_a_2528_ = lean_ctor_get(v___x_2527_, 0);
v_isSharedCheck_2550_ = !lean_is_exclusive(v___x_2527_);
if (v_isSharedCheck_2550_ == 0)
{
v___x_2530_ = v___x_2527_;
v_isShared_2531_ = v_isSharedCheck_2550_;
goto v_resetjp_2529_;
}
else
{
lean_inc(v_a_2528_);
lean_dec(v___x_2527_);
v___x_2530_ = lean_box(0);
v_isShared_2531_ = v_isSharedCheck_2550_;
goto v_resetjp_2529_;
}
v_resetjp_2529_:
{
uint8_t v___x_2532_; 
v___x_2532_ = lean_unbox(v_a_2528_);
lean_dec(v_a_2528_);
if (v___x_2532_ == 0)
{
lean_del_object(v___x_2530_);
lean_dec(v_recursorName_2399_);
v___y_2441_ = v___y_2403_;
v___y_2442_ = v___y_2404_;
v___y_2443_ = v___y_2405_;
v___y_2444_ = v___y_2406_;
goto v___jp_2440_;
}
else
{
lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2539_; 
v___x_2533_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__3, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__3);
v___x_2534_ = l_Lean_MessageData_ofName(v_recursorName_2399_);
v___x_2535_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2535_, 0, v___x_2533_);
lean_ctor_set(v___x_2535_, 1, v___x_2534_);
v___x_2536_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__5, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__5_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__5);
v___x_2537_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2537_, 0, v___x_2535_);
lean_ctor_set(v___x_2537_, 1, v___x_2536_);
if (v_isShared_2531_ == 0)
{
lean_ctor_set_tag(v___x_2530_, 1);
lean_ctor_set(v___x_2530_, 0, v___x_2537_);
v___x_2539_ = v___x_2530_;
goto v_reusejp_2538_;
}
else
{
lean_object* v_reuseFailAlloc_2549_; 
v_reuseFailAlloc_2549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2549_, 0, v___x_2537_);
v___x_2539_ = v_reuseFailAlloc_2549_;
goto v_reusejp_2538_;
}
v_reusejp_2538_:
{
lean_object* v___x_2540_; 
lean_inc(v_mvarId_2396_);
v___x_2540_ = l_Lean_Meta_throwTacticEx___redArg(v___x_2417_, v_mvarId_2396_, v___x_2539_, v___y_2403_, v___y_2404_, v___y_2405_, v___y_2406_);
if (lean_obj_tag(v___x_2540_) == 0)
{
lean_dec_ref_known(v___x_2540_, 1);
v___y_2441_ = v___y_2403_;
v___y_2442_ = v___y_2404_;
v___y_2443_ = v___y_2405_;
v___y_2444_ = v___y_2406_;
goto v___jp_2440_;
}
else
{
lean_object* v_a_2541_; lean_object* v___x_2543_; uint8_t v_isShared_2544_; uint8_t v_isSharedCheck_2548_; 
lean_dec(v_a_2436_);
lean_dec_ref(v_givenNames_2398_);
lean_dec(v_majorFVarId_2397_);
lean_dec(v_mvarId_2396_);
lean_dec_ref(v_a_2394_);
v_a_2541_ = lean_ctor_get(v___x_2540_, 0);
v_isSharedCheck_2548_ = !lean_is_exclusive(v___x_2540_);
if (v_isSharedCheck_2548_ == 0)
{
v___x_2543_ = v___x_2540_;
v_isShared_2544_ = v_isSharedCheck_2548_;
goto v_resetjp_2542_;
}
else
{
lean_inc(v_a_2541_);
lean_dec(v___x_2540_);
v___x_2543_ = lean_box(0);
v_isShared_2544_ = v_isSharedCheck_2548_;
goto v_resetjp_2542_;
}
v_resetjp_2542_:
{
lean_object* v___x_2546_; 
if (v_isShared_2544_ == 0)
{
v___x_2546_ = v___x_2543_;
goto v_reusejp_2545_;
}
else
{
lean_object* v_reuseFailAlloc_2547_; 
v_reuseFailAlloc_2547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2547_, 0, v_a_2541_);
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
}
}
}
else
{
lean_dec(v_a_2438_);
lean_dec(v_recursorName_2399_);
v___y_2441_ = v___y_2403_;
v___y_2442_ = v___y_2404_;
v___y_2443_ = v___y_2405_;
v___y_2444_ = v___y_2406_;
goto v___jp_2440_;
}
v___jp_2440_:
{
size_t v_sz_2445_; size_t v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; uint8_t v___x_2449_; uint8_t v___x_2450_; lean_object* v___x_2451_; 
v_sz_2445_ = lean_array_size(v_a_2436_);
v___x_2446_ = ((size_t)0ULL);
lean_inc(v_a_2436_);
v___x_2447_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_induction_spec__1(v_sz_2445_, v___x_2446_, v_a_2436_);
lean_inc(v_majorFVarId_2397_);
v___x_2448_ = lean_array_push(v___x_2447_, v_majorFVarId_2397_);
v___x_2449_ = 1;
v___x_2450_ = 0;
v___x_2451_ = l_Lean_MVarId_revert(v_mvarId_2396_, v___x_2448_, v___x_2449_, v___x_2450_, v___y_2441_, v___y_2442_, v___y_2443_, v___y_2444_);
if (lean_obj_tag(v___x_2451_) == 0)
{
lean_object* v_a_2452_; lean_object* v_fst_2453_; lean_object* v_snd_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; 
v_a_2452_ = lean_ctor_get(v___x_2451_, 0);
lean_inc(v_a_2452_);
lean_dec_ref_known(v___x_2451_, 1);
v_fst_2453_ = lean_ctor_get(v_a_2452_, 0);
lean_inc(v_fst_2453_);
v_snd_2454_ = lean_ctor_get(v_a_2452_, 1);
lean_inc(v_snd_2454_);
lean_dec(v_a_2452_);
v___x_2455_ = lean_array_get_size(v_a_2436_);
v___x_2456_ = lean_box(0);
v___x_2457_ = l_Lean_Meta_introNCore(v_snd_2454_, v___x_2455_, v___x_2456_, v___x_2450_, v___x_2449_, v___y_2441_, v___y_2442_, v___y_2443_, v___y_2444_);
if (lean_obj_tag(v___x_2457_) == 0)
{
lean_object* v_a_2458_; lean_object* v_fst_2459_; lean_object* v_snd_2460_; lean_object* v___x_2461_; 
v_a_2458_ = lean_ctor_get(v___x_2457_, 0);
lean_inc(v_a_2458_);
lean_dec_ref_known(v___x_2457_, 1);
v_fst_2459_ = lean_ctor_get(v_a_2458_, 0);
lean_inc(v_fst_2459_);
v_snd_2460_ = lean_ctor_get(v_a_2458_, 1);
lean_inc(v_snd_2460_);
lean_dec(v_a_2458_);
v___x_2461_ = l_Lean_Meta_intro1Core(v_snd_2460_, v___x_2449_, v___y_2441_, v___y_2442_, v___y_2443_, v___y_2444_);
if (lean_obj_tag(v___x_2461_) == 0)
{
lean_object* v_a_2462_; lean_object* v_fst_2463_; lean_object* v_snd_2464_; lean_object* v___x_2466_; uint8_t v_isShared_2467_; uint8_t v_isSharedCheck_2502_; 
v_a_2462_ = lean_ctor_get(v___x_2461_, 0);
lean_inc(v_a_2462_);
lean_dec_ref_known(v___x_2461_, 1);
v_fst_2463_ = lean_ctor_get(v_a_2462_, 0);
v_snd_2464_ = lean_ctor_get(v_a_2462_, 1);
v_isSharedCheck_2502_ = !lean_is_exclusive(v_a_2462_);
if (v_isSharedCheck_2502_ == 0)
{
v___x_2466_ = v_a_2462_;
v_isShared_2467_ = v_isSharedCheck_2502_;
goto v_resetjp_2465_;
}
else
{
lean_inc(v_snd_2464_);
lean_inc(v_fst_2463_);
lean_dec(v_a_2462_);
v___x_2466_ = lean_box(0);
v_isShared_2467_ = v_isSharedCheck_2502_;
goto v_resetjp_2465_;
}
v_resetjp_2465_:
{
lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2473_; 
v___x_2468_ = lean_box(0);
lean_inc(v_fst_2463_);
v___x_2469_ = l_Lean_mkFVar(v_fst_2463_);
lean_inc_ref(v___x_2469_);
v___x_2470_ = l_Lean_Meta_FVarSubst_insert(v___x_2468_, v_majorFVarId_2397_, v___x_2469_);
v___x_2471_ = lean_unsigned_to_nat(0u);
if (v_isShared_2467_ == 0)
{
lean_ctor_set(v___x_2466_, 1, v___x_2471_);
lean_ctor_set(v___x_2466_, 0, v___x_2470_);
v___x_2473_ = v___x_2466_;
goto v_reusejp_2472_;
}
else
{
lean_object* v_reuseFailAlloc_2501_; 
v_reuseFailAlloc_2501_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2501_, 0, v___x_2470_);
lean_ctor_set(v_reuseFailAlloc_2501_, 1, v___x_2471_);
v___x_2473_ = v_reuseFailAlloc_2501_;
goto v_reusejp_2472_;
}
v_reusejp_2472_:
{
lean_object* v___x_2474_; lean_object* v_options_2475_; uint8_t v_hasTrace_2476_; 
v___x_2474_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_induction_spec__2(v_fst_2459_, v_a_2436_, v_sz_2445_, v___x_2446_, v___x_2473_);
lean_dec(v_a_2436_);
v_options_2475_ = lean_ctor_get(v___y_2443_, 2);
v_hasTrace_2476_ = lean_ctor_get_uint8(v_options_2475_, sizeof(void*)*1);
if (v_hasTrace_2476_ == 0)
{
lean_object* v_fst_2477_; 
v_fst_2477_ = lean_ctor_get(v___x_2474_, 0);
lean_inc(v_fst_2477_);
lean_dec_ref(v___x_2474_);
lean_inc(v_snd_2464_);
v___y_2419_ = v_snd_2464_;
v___y_2420_ = v_fst_2477_;
v___y_2421_ = v_fst_2463_;
v___y_2422_ = v_fst_2453_;
v___y_2423_ = v___x_2469_;
v___y_2424_ = v_snd_2464_;
v___y_2425_ = v_fst_2459_;
v___y_2426_ = v___x_2446_;
v___y_2427_ = v___y_2441_;
v___y_2428_ = v___y_2442_;
v___y_2429_ = v___y_2443_;
v___y_2430_ = v___y_2444_;
goto v___jp_2418_;
}
else
{
lean_object* v_fst_2478_; lean_object* v___x_2480_; uint8_t v_isShared_2481_; uint8_t v_isSharedCheck_2499_; 
v_fst_2478_ = lean_ctor_get(v___x_2474_, 0);
v_isSharedCheck_2499_ = !lean_is_exclusive(v___x_2474_);
if (v_isSharedCheck_2499_ == 0)
{
lean_object* v_unused_2500_; 
v_unused_2500_ = lean_ctor_get(v___x_2474_, 1);
lean_dec(v_unused_2500_);
v___x_2480_ = v___x_2474_;
v_isShared_2481_ = v_isSharedCheck_2499_;
goto v_resetjp_2479_;
}
else
{
lean_inc(v_fst_2478_);
lean_dec(v___x_2474_);
v___x_2480_ = lean_box(0);
v_isShared_2481_ = v_isSharedCheck_2499_;
goto v_resetjp_2479_;
}
v_resetjp_2479_:
{
lean_object* v_inheritedTraceOptions_2482_; lean_object* v___x_2483_; uint8_t v___x_2484_; 
v_inheritedTraceOptions_2482_ = lean_ctor_get(v___y_2443_, 13);
v___x_2483_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5);
v___x_2484_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2482_, v_options_2475_, v___x_2483_);
if (v___x_2484_ == 0)
{
lean_del_object(v___x_2480_);
lean_inc(v_snd_2464_);
v___y_2419_ = v_snd_2464_;
v___y_2420_ = v_fst_2478_;
v___y_2421_ = v_fst_2463_;
v___y_2422_ = v_fst_2453_;
v___y_2423_ = v___x_2469_;
v___y_2424_ = v_snd_2464_;
v___y_2425_ = v_fst_2459_;
v___y_2426_ = v___x_2446_;
v___y_2427_ = v___y_2441_;
v___y_2428_ = v___y_2442_;
v___y_2429_ = v___y_2443_;
v___y_2430_ = v___y_2444_;
goto v___jp_2418_;
}
else
{
lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2488_; 
v___x_2485_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__1);
lean_inc(v_snd_2464_);
v___x_2486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2486_, 0, v_snd_2464_);
if (v_isShared_2481_ == 0)
{
lean_ctor_set_tag(v___x_2480_, 7);
lean_ctor_set(v___x_2480_, 1, v___x_2486_);
lean_ctor_set(v___x_2480_, 0, v___x_2485_);
v___x_2488_ = v___x_2480_;
goto v_reusejp_2487_;
}
else
{
lean_object* v_reuseFailAlloc_2498_; 
v_reuseFailAlloc_2498_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2498_, 0, v___x_2485_);
lean_ctor_set(v_reuseFailAlloc_2498_, 1, v___x_2486_);
v___x_2488_ = v_reuseFailAlloc_2498_;
goto v_reusejp_2487_;
}
v_reusejp_2487_:
{
lean_object* v___x_2489_; 
v___x_2489_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1(v_cls_2439_, v___x_2488_, v___y_2441_, v___y_2442_, v___y_2443_, v___y_2444_);
if (lean_obj_tag(v___x_2489_) == 0)
{
lean_dec_ref_known(v___x_2489_, 1);
lean_inc(v_snd_2464_);
v___y_2419_ = v_snd_2464_;
v___y_2420_ = v_fst_2478_;
v___y_2421_ = v_fst_2463_;
v___y_2422_ = v_fst_2453_;
v___y_2423_ = v___x_2469_;
v___y_2424_ = v_snd_2464_;
v___y_2425_ = v_fst_2459_;
v___y_2426_ = v___x_2446_;
v___y_2427_ = v___y_2441_;
v___y_2428_ = v___y_2442_;
v___y_2429_ = v___y_2443_;
v___y_2430_ = v___y_2444_;
goto v___jp_2418_;
}
else
{
lean_object* v_a_2490_; lean_object* v___x_2492_; uint8_t v_isShared_2493_; uint8_t v_isSharedCheck_2497_; 
lean_dec(v_fst_2478_);
lean_dec_ref(v___x_2469_);
lean_dec(v_snd_2464_);
lean_dec(v_fst_2463_);
lean_dec(v_fst_2459_);
lean_dec(v_fst_2453_);
lean_dec_ref(v_givenNames_2398_);
lean_dec_ref(v_a_2394_);
v_a_2490_ = lean_ctor_get(v___x_2489_, 0);
v_isSharedCheck_2497_ = !lean_is_exclusive(v___x_2489_);
if (v_isSharedCheck_2497_ == 0)
{
v___x_2492_ = v___x_2489_;
v_isShared_2493_ = v_isSharedCheck_2497_;
goto v_resetjp_2491_;
}
else
{
lean_inc(v_a_2490_);
lean_dec(v___x_2489_);
v___x_2492_ = lean_box(0);
v_isShared_2493_ = v_isSharedCheck_2497_;
goto v_resetjp_2491_;
}
v_resetjp_2491_:
{
lean_object* v___x_2495_; 
if (v_isShared_2493_ == 0)
{
v___x_2495_ = v___x_2492_;
goto v_reusejp_2494_;
}
else
{
lean_object* v_reuseFailAlloc_2496_; 
v_reuseFailAlloc_2496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2496_, 0, v_a_2490_);
v___x_2495_ = v_reuseFailAlloc_2496_;
goto v_reusejp_2494_;
}
v_reusejp_2494_:
{
return v___x_2495_;
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
lean_object* v_a_2503_; lean_object* v___x_2505_; uint8_t v_isShared_2506_; uint8_t v_isSharedCheck_2510_; 
lean_dec(v_fst_2459_);
lean_dec(v_fst_2453_);
lean_dec(v_a_2436_);
lean_dec_ref(v_givenNames_2398_);
lean_dec(v_majorFVarId_2397_);
lean_dec_ref(v_a_2394_);
v_a_2503_ = lean_ctor_get(v___x_2461_, 0);
v_isSharedCheck_2510_ = !lean_is_exclusive(v___x_2461_);
if (v_isSharedCheck_2510_ == 0)
{
v___x_2505_ = v___x_2461_;
v_isShared_2506_ = v_isSharedCheck_2510_;
goto v_resetjp_2504_;
}
else
{
lean_inc(v_a_2503_);
lean_dec(v___x_2461_);
v___x_2505_ = lean_box(0);
v_isShared_2506_ = v_isSharedCheck_2510_;
goto v_resetjp_2504_;
}
v_resetjp_2504_:
{
lean_object* v___x_2508_; 
if (v_isShared_2506_ == 0)
{
v___x_2508_ = v___x_2505_;
goto v_reusejp_2507_;
}
else
{
lean_object* v_reuseFailAlloc_2509_; 
v_reuseFailAlloc_2509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2509_, 0, v_a_2503_);
v___x_2508_ = v_reuseFailAlloc_2509_;
goto v_reusejp_2507_;
}
v_reusejp_2507_:
{
return v___x_2508_;
}
}
}
}
else
{
lean_object* v_a_2511_; lean_object* v___x_2513_; uint8_t v_isShared_2514_; uint8_t v_isSharedCheck_2518_; 
lean_dec(v_fst_2453_);
lean_dec(v_a_2436_);
lean_dec_ref(v_givenNames_2398_);
lean_dec(v_majorFVarId_2397_);
lean_dec_ref(v_a_2394_);
v_a_2511_ = lean_ctor_get(v___x_2457_, 0);
v_isSharedCheck_2518_ = !lean_is_exclusive(v___x_2457_);
if (v_isSharedCheck_2518_ == 0)
{
v___x_2513_ = v___x_2457_;
v_isShared_2514_ = v_isSharedCheck_2518_;
goto v_resetjp_2512_;
}
else
{
lean_inc(v_a_2511_);
lean_dec(v___x_2457_);
v___x_2513_ = lean_box(0);
v_isShared_2514_ = v_isSharedCheck_2518_;
goto v_resetjp_2512_;
}
v_resetjp_2512_:
{
lean_object* v___x_2516_; 
if (v_isShared_2514_ == 0)
{
v___x_2516_ = v___x_2513_;
goto v_reusejp_2515_;
}
else
{
lean_object* v_reuseFailAlloc_2517_; 
v_reuseFailAlloc_2517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2517_, 0, v_a_2511_);
v___x_2516_ = v_reuseFailAlloc_2517_;
goto v_reusejp_2515_;
}
v_reusejp_2515_:
{
return v___x_2516_;
}
}
}
}
else
{
lean_object* v_a_2519_; lean_object* v___x_2521_; uint8_t v_isShared_2522_; uint8_t v_isSharedCheck_2526_; 
lean_dec(v_a_2436_);
lean_dec_ref(v_givenNames_2398_);
lean_dec(v_majorFVarId_2397_);
lean_dec_ref(v_a_2394_);
v_a_2519_ = lean_ctor_get(v___x_2451_, 0);
v_isSharedCheck_2526_ = !lean_is_exclusive(v___x_2451_);
if (v_isSharedCheck_2526_ == 0)
{
v___x_2521_ = v___x_2451_;
v_isShared_2522_ = v_isSharedCheck_2526_;
goto v_resetjp_2520_;
}
else
{
lean_inc(v_a_2519_);
lean_dec(v___x_2451_);
v___x_2521_ = lean_box(0);
v_isShared_2522_ = v_isSharedCheck_2526_;
goto v_resetjp_2520_;
}
v_resetjp_2520_:
{
lean_object* v___x_2524_; 
if (v_isShared_2522_ == 0)
{
v___x_2524_ = v___x_2521_;
goto v_reusejp_2523_;
}
else
{
lean_object* v_reuseFailAlloc_2525_; 
v_reuseFailAlloc_2525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2525_, 0, v_a_2519_);
v___x_2524_ = v_reuseFailAlloc_2525_;
goto v_reusejp_2523_;
}
v_reusejp_2523_:
{
return v___x_2524_;
}
}
}
}
}
else
{
lean_object* v_a_2551_; lean_object* v___x_2553_; uint8_t v_isShared_2554_; uint8_t v_isSharedCheck_2558_; 
lean_dec(v_a_2436_);
lean_dec(v_recursorName_2399_);
lean_dec_ref(v_givenNames_2398_);
lean_dec(v_majorFVarId_2397_);
lean_dec(v_mvarId_2396_);
lean_dec_ref(v_a_2394_);
v_a_2551_ = lean_ctor_get(v___x_2437_, 0);
v_isSharedCheck_2558_ = !lean_is_exclusive(v___x_2437_);
if (v_isSharedCheck_2558_ == 0)
{
v___x_2553_ = v___x_2437_;
v_isShared_2554_ = v_isSharedCheck_2558_;
goto v_resetjp_2552_;
}
else
{
lean_inc(v_a_2551_);
lean_dec(v___x_2437_);
v___x_2553_ = lean_box(0);
v_isShared_2554_ = v_isSharedCheck_2558_;
goto v_resetjp_2552_;
}
v_resetjp_2552_:
{
lean_object* v___x_2556_; 
if (v_isShared_2554_ == 0)
{
v___x_2556_ = v___x_2553_;
goto v_reusejp_2555_;
}
else
{
lean_object* v_reuseFailAlloc_2557_; 
v_reuseFailAlloc_2557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2557_, 0, v_a_2551_);
v___x_2556_ = v_reuseFailAlloc_2557_;
goto v_reusejp_2555_;
}
v_reusejp_2555_:
{
return v___x_2556_;
}
}
}
}
else
{
lean_object* v_a_2559_; lean_object* v___x_2561_; uint8_t v_isShared_2562_; uint8_t v_isSharedCheck_2566_; 
lean_dec(v_recursorName_2399_);
lean_dec_ref(v_givenNames_2398_);
lean_dec(v_majorFVarId_2397_);
lean_dec(v_mvarId_2396_);
lean_dec_ref(v_a_2394_);
v_a_2559_ = lean_ctor_get(v___x_2435_, 0);
v_isSharedCheck_2566_ = !lean_is_exclusive(v___x_2435_);
if (v_isSharedCheck_2566_ == 0)
{
v___x_2561_ = v___x_2435_;
v_isShared_2562_ = v_isSharedCheck_2566_;
goto v_resetjp_2560_;
}
else
{
lean_inc(v_a_2559_);
lean_dec(v___x_2435_);
v___x_2561_ = lean_box(0);
v_isShared_2562_ = v_isSharedCheck_2566_;
goto v_resetjp_2560_;
}
v_resetjp_2560_:
{
lean_object* v___x_2564_; 
if (v_isShared_2562_ == 0)
{
v___x_2564_ = v___x_2561_;
goto v_reusejp_2563_;
}
else
{
lean_object* v_reuseFailAlloc_2565_; 
v_reuseFailAlloc_2565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2565_, 0, v_a_2559_);
v___x_2564_ = v_reuseFailAlloc_2565_;
goto v_reusejp_2563_;
}
v_reusejp_2563_:
{
return v___x_2564_;
}
}
}
v___jp_2418_:
{
size_t v_sz_2431_; lean_object* v___x_2432_; lean_object* v___f_2433_; lean_object* v___x_2434_; 
v_sz_2431_ = lean_array_size(v___y_2425_);
v___x_2432_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__3(v_sz_2431_, v___y_2426_, v___y_2425_);
v___f_2433_ = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4___lam__0___boxed), 14, 9);
lean_closure_set(v___f_2433_, 0, v___y_2419_);
lean_closure_set(v___f_2433_, 1, v___x_2417_);
lean_closure_set(v___f_2433_, 2, v___y_2421_);
lean_closure_set(v___f_2433_, 3, v_a_2394_);
lean_closure_set(v___f_2433_, 4, v___x_2432_);
lean_closure_set(v___f_2433_, 5, v_givenNames_2398_);
lean_closure_set(v___f_2433_, 6, v___y_2422_);
lean_closure_set(v___f_2433_, 7, v___y_2423_);
lean_closure_set(v___f_2433_, 8, v___y_2420_);
v___x_2434_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___redArg(v___y_2424_, v___f_2433_, v___y_2427_, v___y_2428_, v___y_2429_, v___y_2430_);
return v___x_2434_;
}
}
else
{
lean_object* v_a_2567_; lean_object* v___x_2569_; uint8_t v_isShared_2570_; uint8_t v_isSharedCheck_2574_; 
lean_dec(v_recursorName_2399_);
lean_dec_ref(v_givenNames_2398_);
lean_dec(v_majorFVarId_2397_);
lean_dec(v_mvarId_2396_);
lean_dec_ref(v_val_2395_);
lean_dec_ref(v_a_2394_);
v_a_2567_ = lean_ctor_get(v___x_2416_, 0);
v_isSharedCheck_2574_ = !lean_is_exclusive(v___x_2416_);
if (v_isSharedCheck_2574_ == 0)
{
v___x_2569_ = v___x_2416_;
v_isShared_2570_ = v_isSharedCheck_2574_;
goto v_resetjp_2568_;
}
else
{
lean_inc(v_a_2567_);
lean_dec(v___x_2416_);
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
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___boxed(lean_object* v_a_2575_, lean_object* v_val_2576_, lean_object* v_mvarId_2577_, lean_object* v_majorFVarId_2578_, lean_object* v_givenNames_2579_, lean_object* v_recursorName_2580_, lean_object* v_x_2581_, lean_object* v_x_2582_, lean_object* v_x_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_, lean_object* v___y_2587_, lean_object* v___y_2588_){
_start:
{
lean_object* v_res_2589_; 
v_res_2589_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4(v_a_2575_, v_val_2576_, v_mvarId_2577_, v_majorFVarId_2578_, v_givenNames_2579_, v_recursorName_2580_, v_x_2581_, v_x_2582_, v_x_2583_, v___y_2584_, v___y_2585_, v___y_2586_, v___y_2587_);
lean_dec(v___y_2587_);
lean_dec_ref(v___y_2586_);
lean_dec(v___y_2585_);
lean_dec_ref(v___y_2584_);
return v_res_2589_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4(lean_object* v_val_2590_, lean_object* v_mvarId_2591_, lean_object* v_a_2592_, lean_object* v_majorFVarId_2593_, lean_object* v_givenNames_2594_, lean_object* v_recursorName_2595_, lean_object* v_x_2596_, lean_object* v_x_2597_, lean_object* v_x_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_){
_start:
{
if (lean_obj_tag(v_x_2596_) == 5)
{
lean_object* v_fn_2604_; lean_object* v_arg_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; 
v_fn_2604_ = lean_ctor_get(v_x_2596_, 0);
lean_inc_ref(v_fn_2604_);
v_arg_2605_ = lean_ctor_get(v_x_2596_, 1);
lean_inc_ref(v_arg_2605_);
lean_dec_ref_known(v_x_2596_, 2);
v___x_2606_ = lean_array_set(v_x_2597_, v_x_2598_, v_arg_2605_);
v___x_2607_ = lean_unsigned_to_nat(1u);
v___x_2608_ = lean_nat_sub(v_x_2598_, v___x_2607_);
v___x_2609_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4(v_a_2592_, v_val_2590_, v_mvarId_2591_, v_majorFVarId_2593_, v_givenNames_2594_, v_recursorName_2595_, v_fn_2604_, v___x_2606_, v___x_2608_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_);
return v___x_2609_;
}
else
{
uint8_t v_depElim_2610_; lean_object* v_paramsPos_2611_; lean_object* v___x_2612_; 
lean_dec_ref(v_x_2596_);
v_depElim_2610_ = lean_ctor_get_uint8(v_a_2592_, sizeof(void*)*8);
v_paramsPos_2611_ = lean_ctor_get(v_a_2592_, 5);
lean_inc(v_paramsPos_2611_);
lean_inc(v_mvarId_2591_);
lean_inc_ref(v_val_2590_);
v___x_2612_ = l_List_forM___at___00Lean_MVarId_induction_spec__0(v_x_2597_, v_val_2590_, v_mvarId_2591_, v_paramsPos_2611_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_);
lean_dec_ref(v_x_2597_);
if (lean_obj_tag(v___x_2612_) == 0)
{
lean_object* v___x_2613_; lean_object* v___y_2615_; lean_object* v___y_2616_; lean_object* v___y_2617_; lean_object* v___y_2618_; lean_object* v___y_2619_; size_t v___y_2620_; lean_object* v___y_2621_; lean_object* v___y_2622_; lean_object* v___y_2623_; lean_object* v___y_2624_; lean_object* v___y_2625_; lean_object* v___y_2626_; lean_object* v___x_2631_; 
lean_dec_ref_known(v___x_2612_, 1);
v___x_2613_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1));
lean_inc_ref(v_a_2592_);
lean_inc(v_mvarId_2591_);
v___x_2631_ = l_Lean_Meta_getMajorTypeIndices(v_mvarId_2591_, v___x_2613_, v_a_2592_, v_val_2590_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_);
if (lean_obj_tag(v___x_2631_) == 0)
{
lean_object* v_a_2632_; lean_object* v___x_2633_; 
v_a_2632_ = lean_ctor_get(v___x_2631_, 0);
lean_inc(v_a_2632_);
lean_dec_ref_known(v___x_2631_, 1);
lean_inc(v_mvarId_2591_);
v___x_2633_ = l_Lean_MVarId_getType(v_mvarId_2591_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_);
if (lean_obj_tag(v___x_2633_) == 0)
{
lean_object* v_a_2634_; lean_object* v_cls_2635_; lean_object* v___y_2637_; lean_object* v___y_2638_; lean_object* v___y_2639_; lean_object* v___y_2640_; 
v_a_2634_ = lean_ctor_get(v___x_2633_, 0);
lean_inc(v_a_2634_);
lean_dec_ref_known(v___x_2633_, 1);
v_cls_2635_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__2));
if (v_depElim_2610_ == 0)
{
lean_object* v___x_2723_; lean_object* v_a_2724_; lean_object* v___x_2726_; uint8_t v_isShared_2727_; uint8_t v_isSharedCheck_2746_; 
lean_inc(v_majorFVarId_2593_);
v___x_2723_ = l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2___redArg(v_a_2634_, v_majorFVarId_2593_, v___y_2600_);
v_a_2724_ = lean_ctor_get(v___x_2723_, 0);
v_isSharedCheck_2746_ = !lean_is_exclusive(v___x_2723_);
if (v_isSharedCheck_2746_ == 0)
{
v___x_2726_ = v___x_2723_;
v_isShared_2727_ = v_isSharedCheck_2746_;
goto v_resetjp_2725_;
}
else
{
lean_inc(v_a_2724_);
lean_dec(v___x_2723_);
v___x_2726_ = lean_box(0);
v_isShared_2727_ = v_isSharedCheck_2746_;
goto v_resetjp_2725_;
}
v_resetjp_2725_:
{
uint8_t v___x_2728_; 
v___x_2728_ = lean_unbox(v_a_2724_);
lean_dec(v_a_2724_);
if (v___x_2728_ == 0)
{
lean_del_object(v___x_2726_);
lean_dec(v_recursorName_2595_);
v___y_2637_ = v___y_2599_;
v___y_2638_ = v___y_2600_;
v___y_2639_ = v___y_2601_;
v___y_2640_ = v___y_2602_;
goto v___jp_2636_;
}
else
{
lean_object* v___x_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2735_; 
v___x_2729_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__3, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__3);
v___x_2730_ = l_Lean_MessageData_ofName(v_recursorName_2595_);
v___x_2731_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2731_, 0, v___x_2729_);
lean_ctor_set(v___x_2731_, 1, v___x_2730_);
v___x_2732_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__5, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__5_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__5);
v___x_2733_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2733_, 0, v___x_2731_);
lean_ctor_set(v___x_2733_, 1, v___x_2732_);
if (v_isShared_2727_ == 0)
{
lean_ctor_set_tag(v___x_2726_, 1);
lean_ctor_set(v___x_2726_, 0, v___x_2733_);
v___x_2735_ = v___x_2726_;
goto v_reusejp_2734_;
}
else
{
lean_object* v_reuseFailAlloc_2745_; 
v_reuseFailAlloc_2745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2745_, 0, v___x_2733_);
v___x_2735_ = v_reuseFailAlloc_2745_;
goto v_reusejp_2734_;
}
v_reusejp_2734_:
{
lean_object* v___x_2736_; 
lean_inc(v_mvarId_2591_);
v___x_2736_ = l_Lean_Meta_throwTacticEx___redArg(v___x_2613_, v_mvarId_2591_, v___x_2735_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_);
if (lean_obj_tag(v___x_2736_) == 0)
{
lean_dec_ref_known(v___x_2736_, 1);
v___y_2637_ = v___y_2599_;
v___y_2638_ = v___y_2600_;
v___y_2639_ = v___y_2601_;
v___y_2640_ = v___y_2602_;
goto v___jp_2636_;
}
else
{
lean_object* v_a_2737_; lean_object* v___x_2739_; uint8_t v_isShared_2740_; uint8_t v_isSharedCheck_2744_; 
lean_dec(v_a_2632_);
lean_dec_ref(v_givenNames_2594_);
lean_dec(v_majorFVarId_2593_);
lean_dec_ref(v_a_2592_);
lean_dec(v_mvarId_2591_);
v_a_2737_ = lean_ctor_get(v___x_2736_, 0);
v_isSharedCheck_2744_ = !lean_is_exclusive(v___x_2736_);
if (v_isSharedCheck_2744_ == 0)
{
v___x_2739_ = v___x_2736_;
v_isShared_2740_ = v_isSharedCheck_2744_;
goto v_resetjp_2738_;
}
else
{
lean_inc(v_a_2737_);
lean_dec(v___x_2736_);
v___x_2739_ = lean_box(0);
v_isShared_2740_ = v_isSharedCheck_2744_;
goto v_resetjp_2738_;
}
v_resetjp_2738_:
{
lean_object* v___x_2742_; 
if (v_isShared_2740_ == 0)
{
v___x_2742_ = v___x_2739_;
goto v_reusejp_2741_;
}
else
{
lean_object* v_reuseFailAlloc_2743_; 
v_reuseFailAlloc_2743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2743_, 0, v_a_2737_);
v___x_2742_ = v_reuseFailAlloc_2743_;
goto v_reusejp_2741_;
}
v_reusejp_2741_:
{
return v___x_2742_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_2634_);
lean_dec(v_recursorName_2595_);
v___y_2637_ = v___y_2599_;
v___y_2638_ = v___y_2600_;
v___y_2639_ = v___y_2601_;
v___y_2640_ = v___y_2602_;
goto v___jp_2636_;
}
v___jp_2636_:
{
size_t v_sz_2641_; size_t v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; uint8_t v___x_2645_; uint8_t v___x_2646_; lean_object* v___x_2647_; 
v_sz_2641_ = lean_array_size(v_a_2632_);
v___x_2642_ = ((size_t)0ULL);
lean_inc(v_a_2632_);
v___x_2643_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_induction_spec__1(v_sz_2641_, v___x_2642_, v_a_2632_);
lean_inc(v_majorFVarId_2593_);
v___x_2644_ = lean_array_push(v___x_2643_, v_majorFVarId_2593_);
v___x_2645_ = 1;
v___x_2646_ = 0;
v___x_2647_ = l_Lean_MVarId_revert(v_mvarId_2591_, v___x_2644_, v___x_2645_, v___x_2646_, v___y_2637_, v___y_2638_, v___y_2639_, v___y_2640_);
if (lean_obj_tag(v___x_2647_) == 0)
{
lean_object* v_a_2648_; lean_object* v_fst_2649_; lean_object* v_snd_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; 
v_a_2648_ = lean_ctor_get(v___x_2647_, 0);
lean_inc(v_a_2648_);
lean_dec_ref_known(v___x_2647_, 1);
v_fst_2649_ = lean_ctor_get(v_a_2648_, 0);
lean_inc(v_fst_2649_);
v_snd_2650_ = lean_ctor_get(v_a_2648_, 1);
lean_inc(v_snd_2650_);
lean_dec(v_a_2648_);
v___x_2651_ = lean_array_get_size(v_a_2632_);
v___x_2652_ = lean_box(0);
v___x_2653_ = l_Lean_Meta_introNCore(v_snd_2650_, v___x_2651_, v___x_2652_, v___x_2646_, v___x_2645_, v___y_2637_, v___y_2638_, v___y_2639_, v___y_2640_);
if (lean_obj_tag(v___x_2653_) == 0)
{
lean_object* v_a_2654_; lean_object* v_fst_2655_; lean_object* v_snd_2656_; lean_object* v___x_2657_; 
v_a_2654_ = lean_ctor_get(v___x_2653_, 0);
lean_inc(v_a_2654_);
lean_dec_ref_known(v___x_2653_, 1);
v_fst_2655_ = lean_ctor_get(v_a_2654_, 0);
lean_inc(v_fst_2655_);
v_snd_2656_ = lean_ctor_get(v_a_2654_, 1);
lean_inc(v_snd_2656_);
lean_dec(v_a_2654_);
v___x_2657_ = l_Lean_Meta_intro1Core(v_snd_2656_, v___x_2645_, v___y_2637_, v___y_2638_, v___y_2639_, v___y_2640_);
if (lean_obj_tag(v___x_2657_) == 0)
{
lean_object* v_a_2658_; lean_object* v_fst_2659_; lean_object* v_snd_2660_; lean_object* v___x_2662_; uint8_t v_isShared_2663_; uint8_t v_isSharedCheck_2698_; 
v_a_2658_ = lean_ctor_get(v___x_2657_, 0);
lean_inc(v_a_2658_);
lean_dec_ref_known(v___x_2657_, 1);
v_fst_2659_ = lean_ctor_get(v_a_2658_, 0);
v_snd_2660_ = lean_ctor_get(v_a_2658_, 1);
v_isSharedCheck_2698_ = !lean_is_exclusive(v_a_2658_);
if (v_isSharedCheck_2698_ == 0)
{
v___x_2662_ = v_a_2658_;
v_isShared_2663_ = v_isSharedCheck_2698_;
goto v_resetjp_2661_;
}
else
{
lean_inc(v_snd_2660_);
lean_inc(v_fst_2659_);
lean_dec(v_a_2658_);
v___x_2662_ = lean_box(0);
v_isShared_2663_ = v_isSharedCheck_2698_;
goto v_resetjp_2661_;
}
v_resetjp_2661_:
{
lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2669_; 
v___x_2664_ = lean_box(0);
lean_inc(v_fst_2659_);
v___x_2665_ = l_Lean_mkFVar(v_fst_2659_);
lean_inc_ref(v___x_2665_);
v___x_2666_ = l_Lean_Meta_FVarSubst_insert(v___x_2664_, v_majorFVarId_2593_, v___x_2665_);
v___x_2667_ = lean_unsigned_to_nat(0u);
if (v_isShared_2663_ == 0)
{
lean_ctor_set(v___x_2662_, 1, v___x_2667_);
lean_ctor_set(v___x_2662_, 0, v___x_2666_);
v___x_2669_ = v___x_2662_;
goto v_reusejp_2668_;
}
else
{
lean_object* v_reuseFailAlloc_2697_; 
v_reuseFailAlloc_2697_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2697_, 0, v___x_2666_);
lean_ctor_set(v_reuseFailAlloc_2697_, 1, v___x_2667_);
v___x_2669_ = v_reuseFailAlloc_2697_;
goto v_reusejp_2668_;
}
v_reusejp_2668_:
{
lean_object* v___x_2670_; lean_object* v_options_2671_; uint8_t v_hasTrace_2672_; 
v___x_2670_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_induction_spec__2(v_fst_2655_, v_a_2632_, v_sz_2641_, v___x_2642_, v___x_2669_);
lean_dec(v_a_2632_);
v_options_2671_ = lean_ctor_get(v___y_2639_, 2);
v_hasTrace_2672_ = lean_ctor_get_uint8(v_options_2671_, sizeof(void*)*1);
if (v_hasTrace_2672_ == 0)
{
lean_object* v_fst_2673_; 
v_fst_2673_ = lean_ctor_get(v___x_2670_, 0);
lean_inc(v_fst_2673_);
lean_dec_ref(v___x_2670_);
lean_inc(v_snd_2660_);
v___y_2615_ = v_fst_2649_;
v___y_2616_ = v_fst_2673_;
v___y_2617_ = v_snd_2660_;
v___y_2618_ = v_fst_2659_;
v___y_2619_ = v___x_2665_;
v___y_2620_ = v___x_2642_;
v___y_2621_ = v_snd_2660_;
v___y_2622_ = v_fst_2655_;
v___y_2623_ = v___y_2637_;
v___y_2624_ = v___y_2638_;
v___y_2625_ = v___y_2639_;
v___y_2626_ = v___y_2640_;
goto v___jp_2614_;
}
else
{
lean_object* v_fst_2674_; lean_object* v___x_2676_; uint8_t v_isShared_2677_; uint8_t v_isSharedCheck_2695_; 
v_fst_2674_ = lean_ctor_get(v___x_2670_, 0);
v_isSharedCheck_2695_ = !lean_is_exclusive(v___x_2670_);
if (v_isSharedCheck_2695_ == 0)
{
lean_object* v_unused_2696_; 
v_unused_2696_ = lean_ctor_get(v___x_2670_, 1);
lean_dec(v_unused_2696_);
v___x_2676_ = v___x_2670_;
v_isShared_2677_ = v_isSharedCheck_2695_;
goto v_resetjp_2675_;
}
else
{
lean_inc(v_fst_2674_);
lean_dec(v___x_2670_);
v___x_2676_ = lean_box(0);
v_isShared_2677_ = v_isSharedCheck_2695_;
goto v_resetjp_2675_;
}
v_resetjp_2675_:
{
lean_object* v_inheritedTraceOptions_2678_; lean_object* v___x_2679_; uint8_t v___x_2680_; 
v_inheritedTraceOptions_2678_ = lean_ctor_get(v___y_2639_, 13);
v___x_2679_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5);
v___x_2680_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2678_, v_options_2671_, v___x_2679_);
if (v___x_2680_ == 0)
{
lean_del_object(v___x_2676_);
lean_inc(v_snd_2660_);
v___y_2615_ = v_fst_2649_;
v___y_2616_ = v_fst_2674_;
v___y_2617_ = v_snd_2660_;
v___y_2618_ = v_fst_2659_;
v___y_2619_ = v___x_2665_;
v___y_2620_ = v___x_2642_;
v___y_2621_ = v_snd_2660_;
v___y_2622_ = v_fst_2655_;
v___y_2623_ = v___y_2637_;
v___y_2624_ = v___y_2638_;
v___y_2625_ = v___y_2639_;
v___y_2626_ = v___y_2640_;
goto v___jp_2614_;
}
else
{
lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2684_; 
v___x_2681_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__1);
lean_inc(v_snd_2660_);
v___x_2682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2682_, 0, v_snd_2660_);
if (v_isShared_2677_ == 0)
{
lean_ctor_set_tag(v___x_2676_, 7);
lean_ctor_set(v___x_2676_, 1, v___x_2682_);
lean_ctor_set(v___x_2676_, 0, v___x_2681_);
v___x_2684_ = v___x_2676_;
goto v_reusejp_2683_;
}
else
{
lean_object* v_reuseFailAlloc_2694_; 
v_reuseFailAlloc_2694_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2694_, 0, v___x_2681_);
lean_ctor_set(v_reuseFailAlloc_2694_, 1, v___x_2682_);
v___x_2684_ = v_reuseFailAlloc_2694_;
goto v_reusejp_2683_;
}
v_reusejp_2683_:
{
lean_object* v___x_2685_; 
v___x_2685_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1(v_cls_2635_, v___x_2684_, v___y_2637_, v___y_2638_, v___y_2639_, v___y_2640_);
if (lean_obj_tag(v___x_2685_) == 0)
{
lean_dec_ref_known(v___x_2685_, 1);
lean_inc(v_snd_2660_);
v___y_2615_ = v_fst_2649_;
v___y_2616_ = v_fst_2674_;
v___y_2617_ = v_snd_2660_;
v___y_2618_ = v_fst_2659_;
v___y_2619_ = v___x_2665_;
v___y_2620_ = v___x_2642_;
v___y_2621_ = v_snd_2660_;
v___y_2622_ = v_fst_2655_;
v___y_2623_ = v___y_2637_;
v___y_2624_ = v___y_2638_;
v___y_2625_ = v___y_2639_;
v___y_2626_ = v___y_2640_;
goto v___jp_2614_;
}
else
{
lean_object* v_a_2686_; lean_object* v___x_2688_; uint8_t v_isShared_2689_; uint8_t v_isSharedCheck_2693_; 
lean_dec(v_fst_2674_);
lean_dec_ref(v___x_2665_);
lean_dec(v_snd_2660_);
lean_dec(v_fst_2659_);
lean_dec(v_fst_2655_);
lean_dec(v_fst_2649_);
lean_dec_ref(v_givenNames_2594_);
lean_dec_ref(v_a_2592_);
v_a_2686_ = lean_ctor_get(v___x_2685_, 0);
v_isSharedCheck_2693_ = !lean_is_exclusive(v___x_2685_);
if (v_isSharedCheck_2693_ == 0)
{
v___x_2688_ = v___x_2685_;
v_isShared_2689_ = v_isSharedCheck_2693_;
goto v_resetjp_2687_;
}
else
{
lean_inc(v_a_2686_);
lean_dec(v___x_2685_);
v___x_2688_ = lean_box(0);
v_isShared_2689_ = v_isSharedCheck_2693_;
goto v_resetjp_2687_;
}
v_resetjp_2687_:
{
lean_object* v___x_2691_; 
if (v_isShared_2689_ == 0)
{
v___x_2691_ = v___x_2688_;
goto v_reusejp_2690_;
}
else
{
lean_object* v_reuseFailAlloc_2692_; 
v_reuseFailAlloc_2692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2692_, 0, v_a_2686_);
v___x_2691_ = v_reuseFailAlloc_2692_;
goto v_reusejp_2690_;
}
v_reusejp_2690_:
{
return v___x_2691_;
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
lean_object* v_a_2699_; lean_object* v___x_2701_; uint8_t v_isShared_2702_; uint8_t v_isSharedCheck_2706_; 
lean_dec(v_fst_2655_);
lean_dec(v_fst_2649_);
lean_dec(v_a_2632_);
lean_dec_ref(v_givenNames_2594_);
lean_dec(v_majorFVarId_2593_);
lean_dec_ref(v_a_2592_);
v_a_2699_ = lean_ctor_get(v___x_2657_, 0);
v_isSharedCheck_2706_ = !lean_is_exclusive(v___x_2657_);
if (v_isSharedCheck_2706_ == 0)
{
v___x_2701_ = v___x_2657_;
v_isShared_2702_ = v_isSharedCheck_2706_;
goto v_resetjp_2700_;
}
else
{
lean_inc(v_a_2699_);
lean_dec(v___x_2657_);
v___x_2701_ = lean_box(0);
v_isShared_2702_ = v_isSharedCheck_2706_;
goto v_resetjp_2700_;
}
v_resetjp_2700_:
{
lean_object* v___x_2704_; 
if (v_isShared_2702_ == 0)
{
v___x_2704_ = v___x_2701_;
goto v_reusejp_2703_;
}
else
{
lean_object* v_reuseFailAlloc_2705_; 
v_reuseFailAlloc_2705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2705_, 0, v_a_2699_);
v___x_2704_ = v_reuseFailAlloc_2705_;
goto v_reusejp_2703_;
}
v_reusejp_2703_:
{
return v___x_2704_;
}
}
}
}
else
{
lean_object* v_a_2707_; lean_object* v___x_2709_; uint8_t v_isShared_2710_; uint8_t v_isSharedCheck_2714_; 
lean_dec(v_fst_2649_);
lean_dec(v_a_2632_);
lean_dec_ref(v_givenNames_2594_);
lean_dec(v_majorFVarId_2593_);
lean_dec_ref(v_a_2592_);
v_a_2707_ = lean_ctor_get(v___x_2653_, 0);
v_isSharedCheck_2714_ = !lean_is_exclusive(v___x_2653_);
if (v_isSharedCheck_2714_ == 0)
{
v___x_2709_ = v___x_2653_;
v_isShared_2710_ = v_isSharedCheck_2714_;
goto v_resetjp_2708_;
}
else
{
lean_inc(v_a_2707_);
lean_dec(v___x_2653_);
v___x_2709_ = lean_box(0);
v_isShared_2710_ = v_isSharedCheck_2714_;
goto v_resetjp_2708_;
}
v_resetjp_2708_:
{
lean_object* v___x_2712_; 
if (v_isShared_2710_ == 0)
{
v___x_2712_ = v___x_2709_;
goto v_reusejp_2711_;
}
else
{
lean_object* v_reuseFailAlloc_2713_; 
v_reuseFailAlloc_2713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2713_, 0, v_a_2707_);
v___x_2712_ = v_reuseFailAlloc_2713_;
goto v_reusejp_2711_;
}
v_reusejp_2711_:
{
return v___x_2712_;
}
}
}
}
else
{
lean_object* v_a_2715_; lean_object* v___x_2717_; uint8_t v_isShared_2718_; uint8_t v_isSharedCheck_2722_; 
lean_dec(v_a_2632_);
lean_dec_ref(v_givenNames_2594_);
lean_dec(v_majorFVarId_2593_);
lean_dec_ref(v_a_2592_);
v_a_2715_ = lean_ctor_get(v___x_2647_, 0);
v_isSharedCheck_2722_ = !lean_is_exclusive(v___x_2647_);
if (v_isSharedCheck_2722_ == 0)
{
v___x_2717_ = v___x_2647_;
v_isShared_2718_ = v_isSharedCheck_2722_;
goto v_resetjp_2716_;
}
else
{
lean_inc(v_a_2715_);
lean_dec(v___x_2647_);
v___x_2717_ = lean_box(0);
v_isShared_2718_ = v_isSharedCheck_2722_;
goto v_resetjp_2716_;
}
v_resetjp_2716_:
{
lean_object* v___x_2720_; 
if (v_isShared_2718_ == 0)
{
v___x_2720_ = v___x_2717_;
goto v_reusejp_2719_;
}
else
{
lean_object* v_reuseFailAlloc_2721_; 
v_reuseFailAlloc_2721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2721_, 0, v_a_2715_);
v___x_2720_ = v_reuseFailAlloc_2721_;
goto v_reusejp_2719_;
}
v_reusejp_2719_:
{
return v___x_2720_;
}
}
}
}
}
else
{
lean_object* v_a_2747_; lean_object* v___x_2749_; uint8_t v_isShared_2750_; uint8_t v_isSharedCheck_2754_; 
lean_dec(v_a_2632_);
lean_dec(v_recursorName_2595_);
lean_dec_ref(v_givenNames_2594_);
lean_dec(v_majorFVarId_2593_);
lean_dec_ref(v_a_2592_);
lean_dec(v_mvarId_2591_);
v_a_2747_ = lean_ctor_get(v___x_2633_, 0);
v_isSharedCheck_2754_ = !lean_is_exclusive(v___x_2633_);
if (v_isSharedCheck_2754_ == 0)
{
v___x_2749_ = v___x_2633_;
v_isShared_2750_ = v_isSharedCheck_2754_;
goto v_resetjp_2748_;
}
else
{
lean_inc(v_a_2747_);
lean_dec(v___x_2633_);
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
else
{
lean_object* v_a_2755_; lean_object* v___x_2757_; uint8_t v_isShared_2758_; uint8_t v_isSharedCheck_2762_; 
lean_dec(v_recursorName_2595_);
lean_dec_ref(v_givenNames_2594_);
lean_dec(v_majorFVarId_2593_);
lean_dec_ref(v_a_2592_);
lean_dec(v_mvarId_2591_);
v_a_2755_ = lean_ctor_get(v___x_2631_, 0);
v_isSharedCheck_2762_ = !lean_is_exclusive(v___x_2631_);
if (v_isSharedCheck_2762_ == 0)
{
v___x_2757_ = v___x_2631_;
v_isShared_2758_ = v_isSharedCheck_2762_;
goto v_resetjp_2756_;
}
else
{
lean_inc(v_a_2755_);
lean_dec(v___x_2631_);
v___x_2757_ = lean_box(0);
v_isShared_2758_ = v_isSharedCheck_2762_;
goto v_resetjp_2756_;
}
v_resetjp_2756_:
{
lean_object* v___x_2760_; 
if (v_isShared_2758_ == 0)
{
v___x_2760_ = v___x_2757_;
goto v_reusejp_2759_;
}
else
{
lean_object* v_reuseFailAlloc_2761_; 
v_reuseFailAlloc_2761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2761_, 0, v_a_2755_);
v___x_2760_ = v_reuseFailAlloc_2761_;
goto v_reusejp_2759_;
}
v_reusejp_2759_:
{
return v___x_2760_;
}
}
}
v___jp_2614_:
{
size_t v_sz_2627_; lean_object* v___x_2628_; lean_object* v___f_2629_; lean_object* v___x_2630_; 
v_sz_2627_ = lean_array_size(v___y_2622_);
v___x_2628_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__3(v_sz_2627_, v___y_2620_, v___y_2622_);
v___f_2629_ = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4___lam__0___boxed), 14, 9);
lean_closure_set(v___f_2629_, 0, v___y_2617_);
lean_closure_set(v___f_2629_, 1, v___x_2613_);
lean_closure_set(v___f_2629_, 2, v___y_2618_);
lean_closure_set(v___f_2629_, 3, v_a_2592_);
lean_closure_set(v___f_2629_, 4, v___x_2628_);
lean_closure_set(v___f_2629_, 5, v_givenNames_2594_);
lean_closure_set(v___f_2629_, 6, v___y_2615_);
lean_closure_set(v___f_2629_, 7, v___y_2619_);
lean_closure_set(v___f_2629_, 8, v___y_2616_);
v___x_2630_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___redArg(v___y_2621_, v___f_2629_, v___y_2623_, v___y_2624_, v___y_2625_, v___y_2626_);
return v___x_2630_;
}
}
else
{
lean_object* v_a_2763_; lean_object* v___x_2765_; uint8_t v_isShared_2766_; uint8_t v_isSharedCheck_2770_; 
lean_dec(v_recursorName_2595_);
lean_dec_ref(v_givenNames_2594_);
lean_dec(v_majorFVarId_2593_);
lean_dec_ref(v_a_2592_);
lean_dec(v_mvarId_2591_);
lean_dec_ref(v_val_2590_);
v_a_2763_ = lean_ctor_get(v___x_2612_, 0);
v_isSharedCheck_2770_ = !lean_is_exclusive(v___x_2612_);
if (v_isSharedCheck_2770_ == 0)
{
v___x_2765_ = v___x_2612_;
v_isShared_2766_ = v_isSharedCheck_2770_;
goto v_resetjp_2764_;
}
else
{
lean_inc(v_a_2763_);
lean_dec(v___x_2612_);
v___x_2765_ = lean_box(0);
v_isShared_2766_ = v_isSharedCheck_2770_;
goto v_resetjp_2764_;
}
v_resetjp_2764_:
{
lean_object* v___x_2768_; 
if (v_isShared_2766_ == 0)
{
v___x_2768_ = v___x_2765_;
goto v_reusejp_2767_;
}
else
{
lean_object* v_reuseFailAlloc_2769_; 
v_reuseFailAlloc_2769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2769_, 0, v_a_2763_);
v___x_2768_ = v_reuseFailAlloc_2769_;
goto v_reusejp_2767_;
}
v_reusejp_2767_:
{
return v___x_2768_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4___boxed(lean_object* v_val_2771_, lean_object* v_mvarId_2772_, lean_object* v_a_2773_, lean_object* v_majorFVarId_2774_, lean_object* v_givenNames_2775_, lean_object* v_recursorName_2776_, lean_object* v_x_2777_, lean_object* v_x_2778_, lean_object* v_x_2779_, lean_object* v___y_2780_, lean_object* v___y_2781_, lean_object* v___y_2782_, lean_object* v___y_2783_, lean_object* v___y_2784_){
_start:
{
lean_object* v_res_2785_; 
v_res_2785_ = l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4(v_val_2771_, v_mvarId_2772_, v_a_2773_, v_majorFVarId_2774_, v_givenNames_2775_, v_recursorName_2776_, v_x_2777_, v_x_2778_, v_x_2779_, v___y_2780_, v___y_2781_, v___y_2782_, v___y_2783_);
lean_dec(v___y_2783_);
lean_dec_ref(v___y_2782_);
lean_dec(v___y_2781_);
lean_dec_ref(v___y_2780_);
lean_dec(v_x_2779_);
return v_res_2785_;
}
}
static lean_object* _init_l_Lean_MVarId_induction___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2787_; lean_object* v___x_2788_; 
v___x_2787_ = ((lean_object*)(l_Lean_MVarId_induction___lam__0___closed__0));
v___x_2788_ = l_Lean_stringToMessageData(v___x_2787_);
return v___x_2788_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_induction___lam__0(lean_object* v___x_2789_, lean_object* v_mvarId_2790_, lean_object* v_majorFVarId_2791_, lean_object* v_recursorName_2792_, lean_object* v_givenNames_2793_, lean_object* v_cls_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_){
_start:
{
lean_object* v___y_2801_; lean_object* v___y_2802_; lean_object* v___y_2803_; lean_object* v___y_2804_; lean_object* v_options_2856_; uint8_t v_hasTrace_2857_; 
v_options_2856_ = lean_ctor_get(v___y_2797_, 2);
v_hasTrace_2857_ = lean_ctor_get_uint8(v_options_2856_, sizeof(void*)*1);
if (v_hasTrace_2857_ == 0)
{
lean_dec(v_cls_2794_);
v___y_2801_ = v___y_2795_;
v___y_2802_ = v___y_2796_;
v___y_2803_ = v___y_2797_;
v___y_2804_ = v___y_2798_;
goto v___jp_2800_;
}
else
{
lean_object* v_inheritedTraceOptions_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; uint8_t v___x_2861_; 
v_inheritedTraceOptions_2858_ = lean_ctor_get(v___y_2797_, 13);
v___x_2859_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__4));
lean_inc(v_cls_2794_);
v___x_2860_ = l_Lean_Name_append(v___x_2859_, v_cls_2794_);
v___x_2861_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2858_, v_options_2856_, v___x_2860_);
lean_dec(v___x_2860_);
if (v___x_2861_ == 0)
{
lean_dec(v_cls_2794_);
v___y_2801_ = v___y_2795_;
v___y_2802_ = v___y_2796_;
v___y_2803_ = v___y_2797_;
v___y_2804_ = v___y_2798_;
goto v___jp_2800_;
}
else
{
lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; 
v___x_2862_ = lean_obj_once(&l_Lean_MVarId_induction___lam__0___closed__1, &l_Lean_MVarId_induction___lam__0___closed__1_once, _init_l_Lean_MVarId_induction___lam__0___closed__1);
lean_inc(v_mvarId_2790_);
v___x_2863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2863_, 0, v_mvarId_2790_);
v___x_2864_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2864_, 0, v___x_2862_);
lean_ctor_set(v___x_2864_, 1, v___x_2863_);
v___x_2865_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1(v_cls_2794_, v___x_2864_, v___y_2795_, v___y_2796_, v___y_2797_, v___y_2798_);
if (lean_obj_tag(v___x_2865_) == 0)
{
lean_dec_ref_known(v___x_2865_, 1);
v___y_2801_ = v___y_2795_;
v___y_2802_ = v___y_2796_;
v___y_2803_ = v___y_2797_;
v___y_2804_ = v___y_2798_;
goto v___jp_2800_;
}
else
{
lean_object* v_a_2866_; lean_object* v___x_2868_; uint8_t v_isShared_2869_; uint8_t v_isSharedCheck_2873_; 
lean_dec_ref(v_givenNames_2793_);
lean_dec(v_recursorName_2792_);
lean_dec(v_majorFVarId_2791_);
lean_dec(v_mvarId_2790_);
lean_dec_ref(v___x_2789_);
v_a_2866_ = lean_ctor_get(v___x_2865_, 0);
v_isSharedCheck_2873_ = !lean_is_exclusive(v___x_2865_);
if (v_isSharedCheck_2873_ == 0)
{
v___x_2868_ = v___x_2865_;
v_isShared_2869_ = v_isSharedCheck_2873_;
goto v_resetjp_2867_;
}
else
{
lean_inc(v_a_2866_);
lean_dec(v___x_2865_);
v___x_2868_ = lean_box(0);
v_isShared_2869_ = v_isSharedCheck_2873_;
goto v_resetjp_2867_;
}
v_resetjp_2867_:
{
lean_object* v___x_2871_; 
if (v_isShared_2869_ == 0)
{
v___x_2871_ = v___x_2868_;
goto v_reusejp_2870_;
}
else
{
lean_object* v_reuseFailAlloc_2872_; 
v_reuseFailAlloc_2872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2872_, 0, v_a_2866_);
v___x_2871_ = v_reuseFailAlloc_2872_;
goto v_reusejp_2870_;
}
v_reusejp_2870_:
{
return v___x_2871_;
}
}
}
}
}
v___jp_2800_:
{
lean_object* v___x_2805_; lean_object* v___x_2806_; 
v___x_2805_ = l_Lean_Name_mkStr1(v___x_2789_);
lean_inc(v___x_2805_);
lean_inc(v_mvarId_2790_);
v___x_2806_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_2790_, v___x_2805_, v___y_2801_, v___y_2802_, v___y_2803_, v___y_2804_);
if (lean_obj_tag(v___x_2806_) == 0)
{
lean_object* v___x_2807_; 
lean_dec_ref_known(v___x_2806_, 1);
lean_inc(v_majorFVarId_2791_);
v___x_2807_ = l_Lean_FVarId_getDecl___redArg(v_majorFVarId_2791_, v___y_2801_, v___y_2803_, v___y_2804_);
if (lean_obj_tag(v___x_2807_) == 0)
{
lean_object* v_a_2808_; lean_object* v___x_2809_; lean_object* v___x_2810_; 
v_a_2808_ = lean_ctor_get(v___x_2807_, 0);
lean_inc(v_a_2808_);
lean_dec_ref_known(v___x_2807_, 1);
v___x_2809_ = lean_box(0);
lean_inc(v_recursorName_2792_);
v___x_2810_ = l_Lean_Meta_mkRecursorInfo(v_recursorName_2792_, v___x_2809_, v___y_2801_, v___y_2802_, v___y_2803_, v___y_2804_);
if (lean_obj_tag(v___x_2810_) == 0)
{
lean_object* v_a_2811_; lean_object* v_typeName_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; 
v_a_2811_ = lean_ctor_get(v___x_2810_, 0);
lean_inc(v_a_2811_);
lean_dec_ref_known(v___x_2810_, 1);
v_typeName_2812_ = lean_ctor_get(v_a_2811_, 1);
v___x_2813_ = l_Lean_LocalDecl_type(v_a_2808_);
lean_dec(v_a_2808_);
lean_inc_ref(v___x_2813_);
v___x_2814_ = l_Lean_Meta_whnfUntil(v___x_2813_, v_typeName_2812_, v___y_2801_, v___y_2802_, v___y_2803_, v___y_2804_);
if (lean_obj_tag(v___x_2814_) == 0)
{
lean_object* v_a_2815_; 
v_a_2815_ = lean_ctor_get(v___x_2814_, 0);
lean_inc(v_a_2815_);
lean_dec_ref_known(v___x_2814_, 1);
if (lean_obj_tag(v_a_2815_) == 1)
{
lean_object* v_val_2816_; lean_object* v_dummy_2817_; lean_object* v_nargs_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; 
lean_dec_ref(v___x_2813_);
lean_dec(v___x_2805_);
v_val_2816_ = lean_ctor_get(v_a_2815_, 0);
lean_inc_n(v_val_2816_, 2);
lean_dec_ref_known(v_a_2815_, 1);
v_dummy_2817_ = lean_obj_once(&l_Lean_Meta_getMajorTypeIndices___closed__0, &l_Lean_Meta_getMajorTypeIndices___closed__0_once, _init_l_Lean_Meta_getMajorTypeIndices___closed__0);
v_nargs_2818_ = l_Lean_Expr_getAppNumArgs(v_val_2816_);
lean_inc(v_nargs_2818_);
v___x_2819_ = lean_mk_array(v_nargs_2818_, v_dummy_2817_);
v___x_2820_ = lean_unsigned_to_nat(1u);
v___x_2821_ = lean_nat_sub(v_nargs_2818_, v___x_2820_);
lean_dec(v_nargs_2818_);
v___x_2822_ = l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4(v_val_2816_, v_mvarId_2790_, v_a_2811_, v_majorFVarId_2791_, v_givenNames_2793_, v_recursorName_2792_, v_val_2816_, v___x_2819_, v___x_2821_, v___y_2801_, v___y_2802_, v___y_2803_, v___y_2804_);
lean_dec(v___x_2821_);
return v___x_2822_;
}
else
{
lean_object* v___x_2823_; 
lean_dec(v_a_2815_);
lean_dec(v_a_2811_);
lean_dec_ref(v_givenNames_2793_);
lean_dec(v_recursorName_2792_);
lean_dec(v_majorFVarId_2791_);
v___x_2823_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg(v___x_2805_, v_mvarId_2790_, v___x_2813_, v___y_2801_, v___y_2802_, v___y_2803_, v___y_2804_);
return v___x_2823_;
}
}
else
{
lean_object* v_a_2824_; lean_object* v___x_2826_; uint8_t v_isShared_2827_; uint8_t v_isSharedCheck_2831_; 
lean_dec_ref(v___x_2813_);
lean_dec(v_a_2811_);
lean_dec(v___x_2805_);
lean_dec_ref(v_givenNames_2793_);
lean_dec(v_recursorName_2792_);
lean_dec(v_majorFVarId_2791_);
lean_dec(v_mvarId_2790_);
v_a_2824_ = lean_ctor_get(v___x_2814_, 0);
v_isSharedCheck_2831_ = !lean_is_exclusive(v___x_2814_);
if (v_isSharedCheck_2831_ == 0)
{
v___x_2826_ = v___x_2814_;
v_isShared_2827_ = v_isSharedCheck_2831_;
goto v_resetjp_2825_;
}
else
{
lean_inc(v_a_2824_);
lean_dec(v___x_2814_);
v___x_2826_ = lean_box(0);
v_isShared_2827_ = v_isSharedCheck_2831_;
goto v_resetjp_2825_;
}
v_resetjp_2825_:
{
lean_object* v___x_2829_; 
if (v_isShared_2827_ == 0)
{
v___x_2829_ = v___x_2826_;
goto v_reusejp_2828_;
}
else
{
lean_object* v_reuseFailAlloc_2830_; 
v_reuseFailAlloc_2830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2830_, 0, v_a_2824_);
v___x_2829_ = v_reuseFailAlloc_2830_;
goto v_reusejp_2828_;
}
v_reusejp_2828_:
{
return v___x_2829_;
}
}
}
}
else
{
lean_object* v_a_2832_; lean_object* v___x_2834_; uint8_t v_isShared_2835_; uint8_t v_isSharedCheck_2839_; 
lean_dec(v_a_2808_);
lean_dec(v___x_2805_);
lean_dec_ref(v_givenNames_2793_);
lean_dec(v_recursorName_2792_);
lean_dec(v_majorFVarId_2791_);
lean_dec(v_mvarId_2790_);
v_a_2832_ = lean_ctor_get(v___x_2810_, 0);
v_isSharedCheck_2839_ = !lean_is_exclusive(v___x_2810_);
if (v_isSharedCheck_2839_ == 0)
{
v___x_2834_ = v___x_2810_;
v_isShared_2835_ = v_isSharedCheck_2839_;
goto v_resetjp_2833_;
}
else
{
lean_inc(v_a_2832_);
lean_dec(v___x_2810_);
v___x_2834_ = lean_box(0);
v_isShared_2835_ = v_isSharedCheck_2839_;
goto v_resetjp_2833_;
}
v_resetjp_2833_:
{
lean_object* v___x_2837_; 
if (v_isShared_2835_ == 0)
{
v___x_2837_ = v___x_2834_;
goto v_reusejp_2836_;
}
else
{
lean_object* v_reuseFailAlloc_2838_; 
v_reuseFailAlloc_2838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2838_, 0, v_a_2832_);
v___x_2837_ = v_reuseFailAlloc_2838_;
goto v_reusejp_2836_;
}
v_reusejp_2836_:
{
return v___x_2837_;
}
}
}
}
else
{
lean_object* v_a_2840_; lean_object* v___x_2842_; uint8_t v_isShared_2843_; uint8_t v_isSharedCheck_2847_; 
lean_dec(v___x_2805_);
lean_dec_ref(v_givenNames_2793_);
lean_dec(v_recursorName_2792_);
lean_dec(v_majorFVarId_2791_);
lean_dec(v_mvarId_2790_);
v_a_2840_ = lean_ctor_get(v___x_2807_, 0);
v_isSharedCheck_2847_ = !lean_is_exclusive(v___x_2807_);
if (v_isSharedCheck_2847_ == 0)
{
v___x_2842_ = v___x_2807_;
v_isShared_2843_ = v_isSharedCheck_2847_;
goto v_resetjp_2841_;
}
else
{
lean_inc(v_a_2840_);
lean_dec(v___x_2807_);
v___x_2842_ = lean_box(0);
v_isShared_2843_ = v_isSharedCheck_2847_;
goto v_resetjp_2841_;
}
v_resetjp_2841_:
{
lean_object* v___x_2845_; 
if (v_isShared_2843_ == 0)
{
v___x_2845_ = v___x_2842_;
goto v_reusejp_2844_;
}
else
{
lean_object* v_reuseFailAlloc_2846_; 
v_reuseFailAlloc_2846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2846_, 0, v_a_2840_);
v___x_2845_ = v_reuseFailAlloc_2846_;
goto v_reusejp_2844_;
}
v_reusejp_2844_:
{
return v___x_2845_;
}
}
}
}
else
{
lean_object* v_a_2848_; lean_object* v___x_2850_; uint8_t v_isShared_2851_; uint8_t v_isSharedCheck_2855_; 
lean_dec(v___x_2805_);
lean_dec_ref(v_givenNames_2793_);
lean_dec(v_recursorName_2792_);
lean_dec(v_majorFVarId_2791_);
lean_dec(v_mvarId_2790_);
v_a_2848_ = lean_ctor_get(v___x_2806_, 0);
v_isSharedCheck_2855_ = !lean_is_exclusive(v___x_2806_);
if (v_isSharedCheck_2855_ == 0)
{
v___x_2850_ = v___x_2806_;
v_isShared_2851_ = v_isSharedCheck_2855_;
goto v_resetjp_2849_;
}
else
{
lean_inc(v_a_2848_);
lean_dec(v___x_2806_);
v___x_2850_ = lean_box(0);
v_isShared_2851_ = v_isSharedCheck_2855_;
goto v_resetjp_2849_;
}
v_resetjp_2849_:
{
lean_object* v___x_2853_; 
if (v_isShared_2851_ == 0)
{
v___x_2853_ = v___x_2850_;
goto v_reusejp_2852_;
}
else
{
lean_object* v_reuseFailAlloc_2854_; 
v_reuseFailAlloc_2854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2854_, 0, v_a_2848_);
v___x_2853_ = v_reuseFailAlloc_2854_;
goto v_reusejp_2852_;
}
v_reusejp_2852_:
{
return v___x_2853_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_induction___lam__0___boxed(lean_object* v___x_2874_, lean_object* v_mvarId_2875_, lean_object* v_majorFVarId_2876_, lean_object* v_recursorName_2877_, lean_object* v_givenNames_2878_, lean_object* v_cls_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_, lean_object* v___y_2884_){
_start:
{
lean_object* v_res_2885_; 
v_res_2885_ = l_Lean_MVarId_induction___lam__0(v___x_2874_, v_mvarId_2875_, v_majorFVarId_2876_, v_recursorName_2877_, v_givenNames_2878_, v_cls_2879_, v___y_2880_, v___y_2881_, v___y_2882_, v___y_2883_);
lean_dec(v___y_2883_);
lean_dec_ref(v___y_2882_);
lean_dec(v___y_2881_);
lean_dec_ref(v___y_2880_);
return v_res_2885_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_induction(lean_object* v_mvarId_2886_, lean_object* v_majorFVarId_2887_, lean_object* v_recursorName_2888_, lean_object* v_givenNames_2889_, lean_object* v_a_2890_, lean_object* v_a_2891_, lean_object* v_a_2892_, lean_object* v_a_2893_){
_start:
{
lean_object* v___x_2895_; lean_object* v_cls_2896_; lean_object* v___f_2897_; lean_object* v___x_2898_; 
v___x_2895_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__0));
v_cls_2896_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__2));
lean_inc(v_mvarId_2886_);
v___f_2897_ = lean_alloc_closure((void*)(l_Lean_MVarId_induction___lam__0___boxed), 11, 6);
lean_closure_set(v___f_2897_, 0, v___x_2895_);
lean_closure_set(v___f_2897_, 1, v_mvarId_2886_);
lean_closure_set(v___f_2897_, 2, v_majorFVarId_2887_);
lean_closure_set(v___f_2897_, 3, v_recursorName_2888_);
lean_closure_set(v___f_2897_, 4, v_givenNames_2889_);
lean_closure_set(v___f_2897_, 5, v_cls_2896_);
v___x_2898_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___redArg(v_mvarId_2886_, v___f_2897_, v_a_2890_, v_a_2891_, v_a_2892_, v_a_2893_);
return v___x_2898_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_induction___boxed(lean_object* v_mvarId_2899_, lean_object* v_majorFVarId_2900_, lean_object* v_recursorName_2901_, lean_object* v_givenNames_2902_, lean_object* v_a_2903_, lean_object* v_a_2904_, lean_object* v_a_2905_, lean_object* v_a_2906_, lean_object* v_a_2907_){
_start:
{
lean_object* v_res_2908_; 
v_res_2908_ = l_Lean_MVarId_induction(v_mvarId_2899_, v_majorFVarId_2900_, v_recursorName_2901_, v_givenNames_2902_, v_a_2903_, v_a_2904_, v_a_2905_, v_a_2906_);
lean_dec(v_a_2906_);
lean_dec_ref(v_a_2905_);
lean_dec(v_a_2904_);
lean_dec_ref(v_a_2903_);
return v_res_2908_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; 
v___x_2956_ = lean_unsigned_to_nat(2221195325u);
v___x_2957_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_));
v___x_2958_ = l_Lean_Name_num___override(v___x_2957_, v___x_2956_);
return v___x_2958_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; 
v___x_2960_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_));
v___x_2961_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_);
v___x_2962_ = l_Lean_Name_str___override(v___x_2961_, v___x_2960_);
return v___x_2962_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; 
v___x_2964_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_));
v___x_2965_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_);
v___x_2966_ = l_Lean_Name_str___override(v___x_2965_, v___x_2964_);
return v___x_2966_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; 
v___x_2967_ = lean_unsigned_to_nat(2u);
v___x_2968_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_);
v___x_2969_ = l_Lean_Name_num___override(v___x_2968_, v___x_2967_);
return v___x_2969_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2971_; uint8_t v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; 
v___x_2971_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__2));
v___x_2972_ = 0;
v___x_2973_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_);
v___x_2974_ = l_Lean_registerTraceClass(v___x_2971_, v___x_2972_, v___x_2973_);
return v___x_2974_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2____boxed(lean_object* v_a_2975_){
_start:
{
lean_object* v_res_2976_; 
v_res_2976_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_();
return v_res_2976_;
}
}
lean_object* runtime_initialize_Lean_Meta_RecursorInfo(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_SynthInstance(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Revert(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Intro(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_FVarSubst(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_WHNF(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Induction(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_RecursorInfo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_SynthInstance(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Revert(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Intro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_FVarSubst(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_WHNF(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Induction(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_RecursorInfo(uint8_t builtin);
lean_object* initialize_Lean_Meta_SynthInstance(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Revert(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Intro(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_FVarSubst(uint8_t builtin);
lean_object* initialize_Lean_Meta_WHNF(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Induction(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_RecursorInfo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_SynthInstance(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Revert(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Intro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_FVarSubst(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_WHNF(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Induction(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Induction(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Induction(builtin);
}
#ifdef __cplusplus
}
#endif
