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
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Meta_throwTacticEx___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_Meta_mkTacticExMsg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_tagWithErrorName(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_indentExpr(lean_object*);
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
uint8_t l_Lean_Expr_isForall(lean_object*);
lean_object* l_Lean_Meta_introNCore(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_FVarSubst_insert(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_MVarId_tryClear(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
uint8_t l_Lean_BinderInfo_isInstImplicit(uint8_t);
lean_object* l_Lean_Meta_synthInstance_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_RecursorInfo_firstIndexPos(lean_object*);
lean_object* l_Lean_MVarId_getTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_eraseMacroScopes(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
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
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instInhabitedMetaM___redArg___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
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
LEAN_EXPORT uint8_t l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___lam__1___boxed(lean_object*);
static const lean_closure_object l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__0_value;
static lean_once_cell_t l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__1;
static lean_once_cell_t l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_Meta_getMajorTypeIndices_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_Meta_getMajorTypeIndices_spec__0___boxed(lean_object*, lean_object*);
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
lean_object* v_head_40_; lean_object* v_tail_41_; lean_object* v_a_43_; 
v_head_40_ = lean_ctor_get(v_x_32_, 0);
lean_inc(v_head_40_);
v_tail_41_ = lean_ctor_get(v_x_32_, 1);
lean_inc(v_tail_41_);
lean_dec_ref_known(v_x_32_, 2);
if (lean_obj_tag(v_head_40_) == 0)
{
lean_object* v___x_46_; 
lean_inc(v_a_37_);
lean_inc_ref(v_a_36_);
lean_inc(v_a_35_);
lean_inc_ref(v_a_34_);
lean_inc_ref(v_x_33_);
v___x_46_ = lean_infer_type(v_x_33_, v_a_34_, v_a_35_, v_a_36_, v_a_37_);
if (lean_obj_tag(v___x_46_) == 0)
{
lean_object* v_a_47_; lean_object* v___x_48_; 
v_a_47_ = lean_ctor_get(v___x_46_, 0);
lean_inc(v_a_47_);
lean_dec_ref_known(v___x_46_, 1);
v___x_48_ = l_Lean_Meta_whnfForall(v_a_47_, v_a_34_, v_a_35_, v_a_36_, v_a_37_);
if (lean_obj_tag(v___x_48_) == 0)
{
lean_object* v_a_49_; 
v_a_49_ = lean_ctor_get(v___x_48_, 0);
lean_inc(v_a_49_);
lean_dec_ref_known(v___x_48_, 1);
if (lean_obj_tag(v_a_49_) == 7)
{
lean_object* v_binderType_50_; lean_object* v___x_51_; 
v_binderType_50_ = lean_ctor_get(v_a_49_, 1);
lean_inc_ref(v_binderType_50_);
lean_dec_ref_known(v_a_49_, 3);
v___x_51_ = l_Lean_Meta_synthInstance(v_binderType_50_, v_head_40_, v_a_34_, v_a_35_, v_a_36_, v_a_37_);
if (lean_obj_tag(v___x_51_) == 0)
{
lean_object* v_a_52_; 
v_a_52_ = lean_ctor_get(v___x_51_, 0);
lean_inc(v_a_52_);
lean_dec_ref_known(v___x_51_, 1);
v_a_43_ = v_a_52_;
goto v___jp_42_;
}
else
{
lean_object* v_a_53_; uint8_t v___x_54_; 
v_a_53_ = lean_ctor_get(v___x_51_, 0);
v___x_54_ = l_Lean_Exception_isInterrupt(v_a_53_);
if (v___x_54_ == 0)
{
uint8_t v___x_55_; 
lean_inc(v_a_53_);
v___x_55_ = l_Lean_Exception_isRuntime(v_a_53_);
if (v___x_55_ == 0)
{
lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; 
lean_dec_ref_known(v___x_51_, 1);
v___x_56_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1));
v___x_57_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__5, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__5_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__5);
lean_inc(v_mvarId_30_);
v___x_58_ = l_Lean_Meta_throwTacticEx___redArg(v___x_56_, v_mvarId_30_, v___x_57_, v_a_34_, v_a_35_, v_a_36_, v_a_37_);
if (lean_obj_tag(v___x_58_) == 0)
{
lean_object* v_a_59_; 
v_a_59_ = lean_ctor_get(v___x_58_, 0);
lean_inc(v_a_59_);
lean_dec_ref_known(v___x_58_, 1);
v_a_43_ = v_a_59_;
goto v___jp_42_;
}
else
{
lean_dec(v_tail_41_);
lean_dec_ref(v_x_33_);
lean_dec(v_mvarId_30_);
return v___x_58_;
}
}
else
{
lean_dec(v_tail_41_);
lean_dec_ref(v_x_33_);
lean_dec(v_mvarId_30_);
return v___x_51_;
}
}
else
{
lean_dec(v_tail_41_);
lean_dec_ref(v_x_33_);
lean_dec(v_mvarId_30_);
return v___x_51_;
}
}
}
else
{
lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; 
lean_dec(v_a_49_);
lean_dec(v_tail_41_);
lean_dec_ref(v_x_33_);
v___x_60_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1));
v___x_61_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9);
v___x_62_ = l_Lean_Meta_throwTacticEx___redArg(v___x_60_, v_mvarId_30_, v___x_61_, v_a_34_, v_a_35_, v_a_36_, v_a_37_);
return v___x_62_;
}
}
else
{
lean_dec(v_tail_41_);
lean_dec_ref(v_x_33_);
lean_dec(v_mvarId_30_);
return v___x_48_;
}
}
else
{
lean_dec(v_tail_41_);
lean_dec_ref(v_x_33_);
lean_dec(v_mvarId_30_);
return v___x_46_;
}
}
else
{
lean_object* v_val_63_; lean_object* v___x_64_; uint8_t v___x_65_; 
v_val_63_ = lean_ctor_get(v_head_40_, 0);
lean_inc(v_val_63_);
lean_dec_ref_known(v_head_40_, 1);
v___x_64_ = lean_array_get_size(v_majorTypeArgs_31_);
v___x_65_ = lean_nat_dec_lt(v_val_63_, v___x_64_);
if (v___x_65_ == 0)
{
lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; 
lean_dec(v_val_63_);
lean_dec(v_tail_41_);
lean_dec_ref(v_x_33_);
v___x_66_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1));
v___x_67_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9);
v___x_68_ = l_Lean_Meta_throwTacticEx___redArg(v___x_66_, v_mvarId_30_, v___x_67_, v_a_34_, v_a_35_, v_a_36_, v_a_37_);
return v___x_68_;
}
else
{
lean_object* v___x_69_; lean_object* v___x_70_; 
v___x_69_ = lean_array_fget_borrowed(v_majorTypeArgs_31_, v_val_63_);
lean_dec(v_val_63_);
lean_inc(v___x_69_);
v___x_70_ = l_Lean_Expr_app___override(v_x_33_, v___x_69_);
v_x_32_ = v_tail_41_;
v_x_33_ = v___x_70_;
goto _start;
}
}
v___jp_42_:
{
lean_object* v___x_44_; 
v___x_44_ = l_Lean_Expr_app___override(v_x_33_, v_a_43_);
v_x_32_ = v_tail_41_;
v_x_33_ = v___x_44_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___boxed(lean_object* v_mvarId_72_, lean_object* v_majorTypeArgs_73_, lean_object* v_x_74_, lean_object* v_x_75_, lean_object* v_a_76_, lean_object* v_a_77_, lean_object* v_a_78_, lean_object* v_a_79_, lean_object* v_a_80_){
_start:
{
lean_object* v_res_81_; 
v_res_81_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams(v_mvarId_72_, v_majorTypeArgs_73_, v_x_74_, v_x_75_, v_a_76_, v_a_77_, v_a_78_, v_a_79_);
lean_dec(v_a_79_);
lean_dec_ref(v_a_78_);
lean_dec(v_a_77_);
lean_dec_ref(v_a_76_);
lean_dec_ref(v_majorTypeArgs_73_);
return v_res_81_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTypeBody(lean_object* v_mvarId_90_, lean_object* v_type_91_, lean_object* v_x_92_, lean_object* v_a_93_, lean_object* v_a_94_, lean_object* v_a_95_, lean_object* v_a_96_){
_start:
{
lean_object* v___x_98_; 
v___x_98_ = l_Lean_Meta_whnfForall(v_type_91_, v_a_93_, v_a_94_, v_a_95_, v_a_96_);
if (lean_obj_tag(v___x_98_) == 0)
{
lean_object* v_a_99_; lean_object* v___x_101_; uint8_t v_isShared_102_; uint8_t v_isSharedCheck_111_; 
v_a_99_ = lean_ctor_get(v___x_98_, 0);
v_isSharedCheck_111_ = !lean_is_exclusive(v___x_98_);
if (v_isSharedCheck_111_ == 0)
{
v___x_101_ = v___x_98_;
v_isShared_102_ = v_isSharedCheck_111_;
goto v_resetjp_100_;
}
else
{
lean_inc(v_a_99_);
lean_dec(v___x_98_);
v___x_101_ = lean_box(0);
v_isShared_102_ = v_isSharedCheck_111_;
goto v_resetjp_100_;
}
v_resetjp_100_:
{
if (lean_obj_tag(v_a_99_) == 7)
{
lean_object* v_body_103_; lean_object* v___x_104_; lean_object* v___x_106_; 
lean_dec(v_mvarId_90_);
v_body_103_ = lean_ctor_get(v_a_99_, 2);
lean_inc_ref(v_body_103_);
lean_dec_ref_known(v_a_99_, 3);
v___x_104_ = lean_expr_instantiate1(v_body_103_, v_x_92_);
lean_dec_ref(v_body_103_);
if (v_isShared_102_ == 0)
{
lean_ctor_set(v___x_101_, 0, v___x_104_);
v___x_106_ = v___x_101_;
goto v_reusejp_105_;
}
else
{
lean_object* v_reuseFailAlloc_107_; 
v_reuseFailAlloc_107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_107_, 0, v___x_104_);
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
lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; 
lean_del_object(v___x_101_);
lean_dec(v_a_99_);
v___x_108_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1));
v___x_109_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9);
v___x_110_ = l_Lean_Meta_throwTacticEx___redArg(v___x_108_, v_mvarId_90_, v___x_109_, v_a_93_, v_a_94_, v_a_95_, v_a_96_);
return v___x_110_;
}
}
}
else
{
lean_dec(v_mvarId_90_);
return v___x_98_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTypeBody___boxed(lean_object* v_mvarId_112_, lean_object* v_type_113_, lean_object* v_x_114_, lean_object* v_a_115_, lean_object* v_a_116_, lean_object* v_a_117_, lean_object* v_a_118_, lean_object* v_a_119_){
_start:
{
lean_object* v_res_120_; 
v_res_120_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTypeBody(v_mvarId_112_, v_type_113_, v_x_114_, v_a_115_, v_a_116_, v_a_117_, v_a_118_);
lean_dec(v_a_118_);
lean_dec_ref(v_a_117_);
lean_dec(v_a_116_);
lean_dec_ref(v_a_115_);
lean_dec_ref(v_x_114_);
return v_res_120_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__4(lean_object* v_msg_127_, lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_){
_start:
{
lean_object* v___f_133_; lean_object* v___x_6942__overap_134_; lean_object* v___x_135_; 
v___f_133_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__4___closed__0));
v___x_6942__overap_134_ = lean_panic_fn_borrowed(v___f_133_, v_msg_127_);
lean_inc(v___y_131_);
lean_inc_ref(v___y_130_);
lean_inc(v___y_129_);
lean_inc_ref(v___y_128_);
v___x_135_ = lean_apply_5(v___x_6942__overap_134_, v___y_128_, v___y_129_, v___y_130_, v___y_131_, lean_box(0));
return v___x_135_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__4___boxed(lean_object* v_msg_136_, lean_object* v___y_137_, lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_, lean_object* v___y_141_){
_start:
{
lean_object* v_res_142_; 
v_res_142_ = l_panic___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__4(v_msg_136_, v___y_137_, v___y_138_, v___y_139_, v___y_140_);
lean_dec(v___y_140_);
lean_dec_ref(v___y_139_);
lean_dec(v___y_138_);
lean_dec_ref(v___y_137_);
return v_res_142_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__2___redArg(lean_object* v___x_143_, lean_object* v_reverted_144_, lean_object* v_fst_145_, lean_object* v_n_146_, lean_object* v_j_147_, lean_object* v_a_148_){
_start:
{
lean_object* v_zero_149_; uint8_t v_isZero_150_; 
v_zero_149_ = lean_unsigned_to_nat(0u);
v_isZero_150_ = lean_nat_dec_eq(v_j_147_, v_zero_149_);
if (v_isZero_150_ == 1)
{
lean_dec(v_j_147_);
return v_a_148_;
}
else
{
lean_object* v___x_151_; lean_object* v_n_152_; lean_object* v___x_153_; lean_object* v___x_154_; uint8_t v___x_155_; 
v___x_151_ = lean_unsigned_to_nat(1u);
v_n_152_ = lean_nat_sub(v_j_147_, v___x_151_);
v___x_153_ = lean_nat_sub(v_n_146_, v_j_147_);
lean_dec(v_j_147_);
v___x_154_ = lean_nat_add(v___x_143_, v___x_151_);
v___x_155_ = lean_nat_dec_lt(v___x_153_, v___x_154_);
lean_dec(v___x_154_);
if (v___x_155_ == 0)
{
lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; 
v___x_156_ = lean_box(0);
v___x_157_ = lean_array_fget_borrowed(v_reverted_144_, v___x_153_);
v___x_158_ = lean_nat_sub(v___x_153_, v___x_143_);
lean_dec(v___x_153_);
v___x_159_ = lean_nat_sub(v___x_158_, v___x_151_);
lean_dec(v___x_158_);
v___x_160_ = lean_array_get_borrowed(v___x_156_, v_fst_145_, v___x_159_);
lean_dec(v___x_159_);
lean_inc(v___x_160_);
v___x_161_ = l_Lean_mkFVar(v___x_160_);
lean_inc(v___x_157_);
v___x_162_ = l_Lean_Meta_FVarSubst_insert(v_a_148_, v___x_157_, v___x_161_);
v_j_147_ = v_n_152_;
v_a_148_ = v___x_162_;
goto _start;
}
else
{
lean_dec(v___x_153_);
v_j_147_ = v_n_152_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__2___redArg___boxed(lean_object* v___x_165_, lean_object* v_reverted_166_, lean_object* v_fst_167_, lean_object* v_n_168_, lean_object* v_j_169_, lean_object* v_a_170_){
_start:
{
lean_object* v_res_171_; 
v_res_171_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__2___redArg(v___x_165_, v_reverted_166_, v_fst_167_, v_n_168_, v_j_169_, v_a_170_);
lean_dec(v_n_168_);
lean_dec_ref(v_fst_167_);
lean_dec_ref(v_reverted_166_);
lean_dec(v___x_165_);
return v_res_171_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__5(lean_object* v_mvarId_172_, lean_object* v_as_173_, size_t v_i_174_, size_t v_stop_175_, lean_object* v_b_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_, lean_object* v___y_180_){
_start:
{
uint8_t v___x_182_; 
v___x_182_ = lean_usize_dec_eq(v_i_174_, v_stop_175_);
if (v___x_182_ == 0)
{
lean_object* v_fst_183_; lean_object* v_snd_184_; lean_object* v___x_186_; uint8_t v_isShared_187_; uint8_t v_isSharedCheck_206_; 
v_fst_183_ = lean_ctor_get(v_b_176_, 0);
v_snd_184_ = lean_ctor_get(v_b_176_, 1);
v_isSharedCheck_206_ = !lean_is_exclusive(v_b_176_);
if (v_isSharedCheck_206_ == 0)
{
v___x_186_ = v_b_176_;
v_isShared_187_ = v_isSharedCheck_206_;
goto v_resetjp_185_;
}
else
{
lean_inc(v_snd_184_);
lean_inc(v_fst_183_);
lean_dec(v_b_176_);
v___x_186_ = lean_box(0);
v_isShared_187_ = v_isSharedCheck_206_;
goto v_resetjp_185_;
}
v_resetjp_185_:
{
lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; 
v___x_188_ = lean_array_uget_borrowed(v_as_173_, v_i_174_);
lean_inc(v___x_188_);
v___x_189_ = l_Lean_Expr_app___override(v_fst_183_, v___x_188_);
lean_inc(v_mvarId_172_);
v___x_190_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTypeBody(v_mvarId_172_, v_snd_184_, v___x_188_, v___y_177_, v___y_178_, v___y_179_, v___y_180_);
if (lean_obj_tag(v___x_190_) == 0)
{
lean_object* v_a_191_; lean_object* v___x_193_; 
v_a_191_ = lean_ctor_get(v___x_190_, 0);
lean_inc(v_a_191_);
lean_dec_ref_known(v___x_190_, 1);
if (v_isShared_187_ == 0)
{
lean_ctor_set(v___x_186_, 1, v_a_191_);
lean_ctor_set(v___x_186_, 0, v___x_189_);
v___x_193_ = v___x_186_;
goto v_reusejp_192_;
}
else
{
lean_object* v_reuseFailAlloc_197_; 
v_reuseFailAlloc_197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_197_, 0, v___x_189_);
lean_ctor_set(v_reuseFailAlloc_197_, 1, v_a_191_);
v___x_193_ = v_reuseFailAlloc_197_;
goto v_reusejp_192_;
}
v_reusejp_192_:
{
size_t v___x_194_; size_t v___x_195_; 
v___x_194_ = ((size_t)1ULL);
v___x_195_ = lean_usize_add(v_i_174_, v___x_194_);
v_i_174_ = v___x_195_;
v_b_176_ = v___x_193_;
goto _start;
}
}
else
{
lean_object* v_a_198_; lean_object* v___x_200_; uint8_t v_isShared_201_; uint8_t v_isSharedCheck_205_; 
lean_dec_ref(v___x_189_);
lean_del_object(v___x_186_);
lean_dec(v_mvarId_172_);
v_a_198_ = lean_ctor_get(v___x_190_, 0);
v_isSharedCheck_205_ = !lean_is_exclusive(v___x_190_);
if (v_isSharedCheck_205_ == 0)
{
v___x_200_ = v___x_190_;
v_isShared_201_ = v_isSharedCheck_205_;
goto v_resetjp_199_;
}
else
{
lean_inc(v_a_198_);
lean_dec(v___x_190_);
v___x_200_ = lean_box(0);
v_isShared_201_ = v_isSharedCheck_205_;
goto v_resetjp_199_;
}
v_resetjp_199_:
{
lean_object* v___x_203_; 
if (v_isShared_201_ == 0)
{
v___x_203_ = v___x_200_;
goto v_reusejp_202_;
}
else
{
lean_object* v_reuseFailAlloc_204_; 
v_reuseFailAlloc_204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_204_, 0, v_a_198_);
v___x_203_ = v_reuseFailAlloc_204_;
goto v_reusejp_202_;
}
v_reusejp_202_:
{
return v___x_203_;
}
}
}
}
}
else
{
lean_object* v___x_207_; 
lean_dec(v_mvarId_172_);
v___x_207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_207_, 0, v_b_176_);
return v___x_207_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__5___boxed(lean_object* v_mvarId_208_, lean_object* v_as_209_, lean_object* v_i_210_, lean_object* v_stop_211_, lean_object* v_b_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_){
_start:
{
size_t v_i_boxed_218_; size_t v_stop_boxed_219_; lean_object* v_res_220_; 
v_i_boxed_218_ = lean_unbox_usize(v_i_210_);
lean_dec(v_i_210_);
v_stop_boxed_219_ = lean_unbox_usize(v_stop_211_);
lean_dec(v_stop_211_);
v_res_220_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__5(v_mvarId_208_, v_as_209_, v_i_boxed_218_, v_stop_boxed_219_, v_b_212_, v___y_213_, v___y_214_, v___y_215_, v___y_216_);
lean_dec(v___y_216_);
lean_dec_ref(v___y_215_);
lean_dec(v___y_214_);
lean_dec_ref(v___y_213_);
lean_dec_ref(v_as_209_);
return v_res_220_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__8_spec__9___redArg(lean_object* v_x_221_, lean_object* v_x_222_, lean_object* v_x_223_, lean_object* v_x_224_){
_start:
{
lean_object* v_ks_225_; lean_object* v_vs_226_; lean_object* v___x_228_; uint8_t v_isShared_229_; uint8_t v_isSharedCheck_250_; 
v_ks_225_ = lean_ctor_get(v_x_221_, 0);
v_vs_226_ = lean_ctor_get(v_x_221_, 1);
v_isSharedCheck_250_ = !lean_is_exclusive(v_x_221_);
if (v_isSharedCheck_250_ == 0)
{
v___x_228_ = v_x_221_;
v_isShared_229_ = v_isSharedCheck_250_;
goto v_resetjp_227_;
}
else
{
lean_inc(v_vs_226_);
lean_inc(v_ks_225_);
lean_dec(v_x_221_);
v___x_228_ = lean_box(0);
v_isShared_229_ = v_isSharedCheck_250_;
goto v_resetjp_227_;
}
v_resetjp_227_:
{
lean_object* v___x_230_; uint8_t v___x_231_; 
v___x_230_ = lean_array_get_size(v_ks_225_);
v___x_231_ = lean_nat_dec_lt(v_x_222_, v___x_230_);
if (v___x_231_ == 0)
{
lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_235_; 
lean_dec(v_x_222_);
v___x_232_ = lean_array_push(v_ks_225_, v_x_223_);
v___x_233_ = lean_array_push(v_vs_226_, v_x_224_);
if (v_isShared_229_ == 0)
{
lean_ctor_set(v___x_228_, 1, v___x_233_);
lean_ctor_set(v___x_228_, 0, v___x_232_);
v___x_235_ = v___x_228_;
goto v_reusejp_234_;
}
else
{
lean_object* v_reuseFailAlloc_236_; 
v_reuseFailAlloc_236_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_236_, 0, v___x_232_);
lean_ctor_set(v_reuseFailAlloc_236_, 1, v___x_233_);
v___x_235_ = v_reuseFailAlloc_236_;
goto v_reusejp_234_;
}
v_reusejp_234_:
{
return v___x_235_;
}
}
else
{
lean_object* v_k_x27_237_; uint8_t v___x_238_; 
v_k_x27_237_ = lean_array_fget_borrowed(v_ks_225_, v_x_222_);
v___x_238_ = l_Lean_instBEqMVarId_beq(v_x_223_, v_k_x27_237_);
if (v___x_238_ == 0)
{
lean_object* v___x_240_; 
if (v_isShared_229_ == 0)
{
v___x_240_ = v___x_228_;
goto v_reusejp_239_;
}
else
{
lean_object* v_reuseFailAlloc_244_; 
v_reuseFailAlloc_244_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_244_, 0, v_ks_225_);
lean_ctor_set(v_reuseFailAlloc_244_, 1, v_vs_226_);
v___x_240_ = v_reuseFailAlloc_244_;
goto v_reusejp_239_;
}
v_reusejp_239_:
{
lean_object* v___x_241_; lean_object* v___x_242_; 
v___x_241_ = lean_unsigned_to_nat(1u);
v___x_242_ = lean_nat_add(v_x_222_, v___x_241_);
lean_dec(v_x_222_);
v_x_221_ = v___x_240_;
v_x_222_ = v___x_242_;
goto _start;
}
}
else
{
lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_248_; 
v___x_245_ = lean_array_fset(v_ks_225_, v_x_222_, v_x_223_);
v___x_246_ = lean_array_fset(v_vs_226_, v_x_222_, v_x_224_);
lean_dec(v_x_222_);
if (v_isShared_229_ == 0)
{
lean_ctor_set(v___x_228_, 1, v___x_246_);
lean_ctor_set(v___x_228_, 0, v___x_245_);
v___x_248_ = v___x_228_;
goto v_reusejp_247_;
}
else
{
lean_object* v_reuseFailAlloc_249_; 
v_reuseFailAlloc_249_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_249_, 0, v___x_245_);
lean_ctor_set(v_reuseFailAlloc_249_, 1, v___x_246_);
v___x_248_ = v_reuseFailAlloc_249_;
goto v_reusejp_247_;
}
v_reusejp_247_:
{
return v___x_248_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__8___redArg(lean_object* v_n_251_, lean_object* v_k_252_, lean_object* v_v_253_){
_start:
{
lean_object* v___x_254_; lean_object* v___x_255_; 
v___x_254_ = lean_unsigned_to_nat(0u);
v___x_255_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__8_spec__9___redArg(v_n_251_, v___x_254_, v_k_252_, v_v_253_);
return v___x_255_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_256_; 
v___x_256_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_256_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2___redArg(lean_object* v_x_257_, size_t v_x_258_, size_t v_x_259_, lean_object* v_x_260_, lean_object* v_x_261_){
_start:
{
if (lean_obj_tag(v_x_257_) == 0)
{
lean_object* v_es_262_; size_t v___x_263_; size_t v___x_264_; lean_object* v_j_265_; lean_object* v___x_266_; uint8_t v___x_267_; 
v_es_262_ = lean_ctor_get(v_x_257_, 0);
v___x_263_ = ((size_t)31ULL);
v___x_264_ = lean_usize_land(v_x_258_, v___x_263_);
v_j_265_ = lean_usize_to_nat(v___x_264_);
v___x_266_ = lean_array_get_size(v_es_262_);
v___x_267_ = lean_nat_dec_lt(v_j_265_, v___x_266_);
if (v___x_267_ == 0)
{
lean_dec(v_j_265_);
lean_dec(v_x_261_);
lean_dec(v_x_260_);
return v_x_257_;
}
else
{
lean_object* v___x_269_; uint8_t v_isShared_270_; uint8_t v_isSharedCheck_306_; 
lean_inc_ref(v_es_262_);
v_isSharedCheck_306_ = !lean_is_exclusive(v_x_257_);
if (v_isSharedCheck_306_ == 0)
{
lean_object* v_unused_307_; 
v_unused_307_ = lean_ctor_get(v_x_257_, 0);
lean_dec(v_unused_307_);
v___x_269_ = v_x_257_;
v_isShared_270_ = v_isSharedCheck_306_;
goto v_resetjp_268_;
}
else
{
lean_dec(v_x_257_);
v___x_269_ = lean_box(0);
v_isShared_270_ = v_isSharedCheck_306_;
goto v_resetjp_268_;
}
v_resetjp_268_:
{
lean_object* v_v_271_; lean_object* v___x_272_; lean_object* v_xs_x27_273_; lean_object* v___y_275_; 
v_v_271_ = lean_array_fget(v_es_262_, v_j_265_);
v___x_272_ = lean_box(0);
v_xs_x27_273_ = lean_array_fset(v_es_262_, v_j_265_, v___x_272_);
switch(lean_obj_tag(v_v_271_))
{
case 0:
{
lean_object* v_key_280_; lean_object* v_val_281_; lean_object* v___x_283_; uint8_t v_isShared_284_; uint8_t v_isSharedCheck_291_; 
v_key_280_ = lean_ctor_get(v_v_271_, 0);
v_val_281_ = lean_ctor_get(v_v_271_, 1);
v_isSharedCheck_291_ = !lean_is_exclusive(v_v_271_);
if (v_isSharedCheck_291_ == 0)
{
v___x_283_ = v_v_271_;
v_isShared_284_ = v_isSharedCheck_291_;
goto v_resetjp_282_;
}
else
{
lean_inc(v_val_281_);
lean_inc(v_key_280_);
lean_dec(v_v_271_);
v___x_283_ = lean_box(0);
v_isShared_284_ = v_isSharedCheck_291_;
goto v_resetjp_282_;
}
v_resetjp_282_:
{
uint8_t v___x_285_; 
v___x_285_ = l_Lean_instBEqMVarId_beq(v_x_260_, v_key_280_);
if (v___x_285_ == 0)
{
lean_object* v___x_286_; lean_object* v___x_287_; 
lean_del_object(v___x_283_);
v___x_286_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_280_, v_val_281_, v_x_260_, v_x_261_);
v___x_287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_287_, 0, v___x_286_);
v___y_275_ = v___x_287_;
goto v___jp_274_;
}
else
{
lean_object* v___x_289_; 
lean_dec(v_val_281_);
lean_dec(v_key_280_);
if (v_isShared_284_ == 0)
{
lean_ctor_set(v___x_283_, 1, v_x_261_);
lean_ctor_set(v___x_283_, 0, v_x_260_);
v___x_289_ = v___x_283_;
goto v_reusejp_288_;
}
else
{
lean_object* v_reuseFailAlloc_290_; 
v_reuseFailAlloc_290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_290_, 0, v_x_260_);
lean_ctor_set(v_reuseFailAlloc_290_, 1, v_x_261_);
v___x_289_ = v_reuseFailAlloc_290_;
goto v_reusejp_288_;
}
v_reusejp_288_:
{
v___y_275_ = v___x_289_;
goto v___jp_274_;
}
}
}
}
case 1:
{
lean_object* v_node_292_; lean_object* v___x_294_; uint8_t v_isShared_295_; uint8_t v_isSharedCheck_304_; 
v_node_292_ = lean_ctor_get(v_v_271_, 0);
v_isSharedCheck_304_ = !lean_is_exclusive(v_v_271_);
if (v_isSharedCheck_304_ == 0)
{
v___x_294_ = v_v_271_;
v_isShared_295_ = v_isSharedCheck_304_;
goto v_resetjp_293_;
}
else
{
lean_inc(v_node_292_);
lean_dec(v_v_271_);
v___x_294_ = lean_box(0);
v_isShared_295_ = v_isSharedCheck_304_;
goto v_resetjp_293_;
}
v_resetjp_293_:
{
size_t v___x_296_; size_t v___x_297_; size_t v___x_298_; size_t v___x_299_; lean_object* v___x_300_; lean_object* v___x_302_; 
v___x_296_ = ((size_t)5ULL);
v___x_297_ = lean_usize_shift_right(v_x_258_, v___x_296_);
v___x_298_ = ((size_t)1ULL);
v___x_299_ = lean_usize_add(v_x_259_, v___x_298_);
v___x_300_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2___redArg(v_node_292_, v___x_297_, v___x_299_, v_x_260_, v_x_261_);
if (v_isShared_295_ == 0)
{
lean_ctor_set(v___x_294_, 0, v___x_300_);
v___x_302_ = v___x_294_;
goto v_reusejp_301_;
}
else
{
lean_object* v_reuseFailAlloc_303_; 
v_reuseFailAlloc_303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_303_, 0, v___x_300_);
v___x_302_ = v_reuseFailAlloc_303_;
goto v_reusejp_301_;
}
v_reusejp_301_:
{
v___y_275_ = v___x_302_;
goto v___jp_274_;
}
}
}
default: 
{
lean_object* v___x_305_; 
v___x_305_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_305_, 0, v_x_260_);
lean_ctor_set(v___x_305_, 1, v_x_261_);
v___y_275_ = v___x_305_;
goto v___jp_274_;
}
}
v___jp_274_:
{
lean_object* v___x_276_; lean_object* v___x_278_; 
v___x_276_ = lean_array_fset(v_xs_x27_273_, v_j_265_, v___y_275_);
lean_dec(v_j_265_);
if (v_isShared_270_ == 0)
{
lean_ctor_set(v___x_269_, 0, v___x_276_);
v___x_278_ = v___x_269_;
goto v_reusejp_277_;
}
else
{
lean_object* v_reuseFailAlloc_279_; 
v_reuseFailAlloc_279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_279_, 0, v___x_276_);
v___x_278_ = v_reuseFailAlloc_279_;
goto v_reusejp_277_;
}
v_reusejp_277_:
{
return v___x_278_;
}
}
}
}
}
else
{
lean_object* v_ks_308_; lean_object* v_vs_309_; lean_object* v___x_311_; uint8_t v_isShared_312_; uint8_t v_isSharedCheck_327_; 
v_ks_308_ = lean_ctor_get(v_x_257_, 0);
v_vs_309_ = lean_ctor_get(v_x_257_, 1);
v_isSharedCheck_327_ = !lean_is_exclusive(v_x_257_);
if (v_isSharedCheck_327_ == 0)
{
v___x_311_ = v_x_257_;
v_isShared_312_ = v_isSharedCheck_327_;
goto v_resetjp_310_;
}
else
{
lean_inc(v_vs_309_);
lean_inc(v_ks_308_);
lean_dec(v_x_257_);
v___x_311_ = lean_box(0);
v_isShared_312_ = v_isSharedCheck_327_;
goto v_resetjp_310_;
}
v_resetjp_310_:
{
lean_object* v___x_314_; 
if (v_isShared_312_ == 0)
{
v___x_314_ = v___x_311_;
goto v_reusejp_313_;
}
else
{
lean_object* v_reuseFailAlloc_326_; 
v_reuseFailAlloc_326_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_326_, 0, v_ks_308_);
lean_ctor_set(v_reuseFailAlloc_326_, 1, v_vs_309_);
v___x_314_ = v_reuseFailAlloc_326_;
goto v_reusejp_313_;
}
v_reusejp_313_:
{
lean_object* v_newNode_315_; size_t v___x_316_; uint8_t v___x_317_; 
v_newNode_315_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__8___redArg(v___x_314_, v_x_260_, v_x_261_);
v___x_316_ = ((size_t)7ULL);
v___x_317_ = lean_usize_dec_le(v___x_316_, v_x_259_);
if (v___x_317_ == 0)
{
lean_object* v___x_318_; lean_object* v___x_319_; uint8_t v___x_320_; 
v___x_318_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_315_);
v___x_319_ = lean_unsigned_to_nat(4u);
v___x_320_ = lean_nat_dec_lt(v___x_318_, v___x_319_);
lean_dec(v___x_318_);
if (v___x_320_ == 0)
{
lean_object* v_ks_321_; lean_object* v_vs_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; 
v_ks_321_ = lean_ctor_get(v_newNode_315_, 0);
lean_inc_ref(v_ks_321_);
v_vs_322_ = lean_ctor_get(v_newNode_315_, 1);
lean_inc_ref(v_vs_322_);
lean_dec_ref(v_newNode_315_);
v___x_323_ = lean_unsigned_to_nat(0u);
v___x_324_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2___redArg___closed__0);
v___x_325_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__9___redArg(v_x_259_, v_ks_321_, v_vs_322_, v___x_323_, v___x_324_);
lean_dec_ref(v_vs_322_);
lean_dec_ref(v_ks_321_);
return v___x_325_;
}
else
{
return v_newNode_315_;
}
}
else
{
return v_newNode_315_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__9___redArg(size_t v_depth_328_, lean_object* v_keys_329_, lean_object* v_vals_330_, lean_object* v_i_331_, lean_object* v_entries_332_){
_start:
{
lean_object* v___x_333_; uint8_t v___x_334_; 
v___x_333_ = lean_array_get_size(v_keys_329_);
v___x_334_ = lean_nat_dec_lt(v_i_331_, v___x_333_);
if (v___x_334_ == 0)
{
lean_dec(v_i_331_);
return v_entries_332_;
}
else
{
lean_object* v_k_335_; lean_object* v_v_336_; uint64_t v___x_337_; size_t v_h_338_; size_t v___x_339_; lean_object* v___x_340_; size_t v___x_341_; size_t v___x_342_; size_t v___x_343_; size_t v_h_344_; lean_object* v___x_345_; lean_object* v___x_346_; 
v_k_335_ = lean_array_fget_borrowed(v_keys_329_, v_i_331_);
v_v_336_ = lean_array_fget_borrowed(v_vals_330_, v_i_331_);
v___x_337_ = l_Lean_instHashableMVarId_hash(v_k_335_);
v_h_338_ = lean_uint64_to_usize(v___x_337_);
v___x_339_ = ((size_t)5ULL);
v___x_340_ = lean_unsigned_to_nat(1u);
v___x_341_ = ((size_t)1ULL);
v___x_342_ = lean_usize_sub(v_depth_328_, v___x_341_);
v___x_343_ = lean_usize_mul(v___x_339_, v___x_342_);
v_h_344_ = lean_usize_shift_right(v_h_338_, v___x_343_);
v___x_345_ = lean_nat_add(v_i_331_, v___x_340_);
lean_dec(v_i_331_);
lean_inc(v_v_336_);
lean_inc(v_k_335_);
v___x_346_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2___redArg(v_entries_332_, v_h_344_, v_depth_328_, v_k_335_, v_v_336_);
v_i_331_ = v___x_345_;
v_entries_332_ = v___x_346_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__9___redArg___boxed(lean_object* v_depth_348_, lean_object* v_keys_349_, lean_object* v_vals_350_, lean_object* v_i_351_, lean_object* v_entries_352_){
_start:
{
size_t v_depth_boxed_353_; lean_object* v_res_354_; 
v_depth_boxed_353_ = lean_unbox_usize(v_depth_348_);
lean_dec(v_depth_348_);
v_res_354_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__9___redArg(v_depth_boxed_353_, v_keys_349_, v_vals_350_, v_i_351_, v_entries_352_);
lean_dec_ref(v_vals_350_);
lean_dec_ref(v_keys_349_);
return v_res_354_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_x_355_, lean_object* v_x_356_, lean_object* v_x_357_, lean_object* v_x_358_, lean_object* v_x_359_){
_start:
{
size_t v_x_8248__boxed_360_; size_t v_x_8249__boxed_361_; lean_object* v_res_362_; 
v_x_8248__boxed_360_ = lean_unbox_usize(v_x_356_);
lean_dec(v_x_356_);
v_x_8249__boxed_361_ = lean_unbox_usize(v_x_357_);
lean_dec(v_x_357_);
v_res_362_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2___redArg(v_x_355_, v_x_8248__boxed_360_, v_x_8249__boxed_361_, v_x_358_, v_x_359_);
return v_res_362_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0___redArg(lean_object* v_x_363_, lean_object* v_x_364_, lean_object* v_x_365_){
_start:
{
uint64_t v___x_366_; size_t v___x_367_; size_t v___x_368_; lean_object* v___x_369_; 
v___x_366_ = l_Lean_instHashableMVarId_hash(v_x_364_);
v___x_367_ = lean_uint64_to_usize(v___x_366_);
v___x_368_ = ((size_t)1ULL);
v___x_369_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2___redArg(v_x_363_, v___x_367_, v___x_368_, v_x_364_, v_x_365_);
return v___x_369_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0___redArg(lean_object* v_mvarId_370_, lean_object* v_val_371_, lean_object* v___y_372_){
_start:
{
lean_object* v___x_374_; lean_object* v_mctx_375_; lean_object* v_cache_376_; lean_object* v_zetaDeltaFVarIds_377_; lean_object* v_postponed_378_; lean_object* v_diag_379_; lean_object* v___x_381_; uint8_t v_isShared_382_; uint8_t v_isSharedCheck_409_; 
v___x_374_ = lean_st_ref_take(v___y_372_);
v_mctx_375_ = lean_ctor_get(v___x_374_, 0);
v_cache_376_ = lean_ctor_get(v___x_374_, 1);
v_zetaDeltaFVarIds_377_ = lean_ctor_get(v___x_374_, 2);
v_postponed_378_ = lean_ctor_get(v___x_374_, 3);
v_diag_379_ = lean_ctor_get(v___x_374_, 4);
v_isSharedCheck_409_ = !lean_is_exclusive(v___x_374_);
if (v_isSharedCheck_409_ == 0)
{
v___x_381_ = v___x_374_;
v_isShared_382_ = v_isSharedCheck_409_;
goto v_resetjp_380_;
}
else
{
lean_inc(v_diag_379_);
lean_inc(v_postponed_378_);
lean_inc(v_zetaDeltaFVarIds_377_);
lean_inc(v_cache_376_);
lean_inc(v_mctx_375_);
lean_dec(v___x_374_);
v___x_381_ = lean_box(0);
v_isShared_382_ = v_isSharedCheck_409_;
goto v_resetjp_380_;
}
v_resetjp_380_:
{
lean_object* v_depth_383_; lean_object* v_levelAssignDepth_384_; lean_object* v_lmvarCounter_385_; lean_object* v_mvarCounter_386_; lean_object* v_lDecls_387_; lean_object* v_decls_388_; lean_object* v_userNames_389_; lean_object* v_lAssignment_390_; lean_object* v_eAssignment_391_; lean_object* v_dAssignment_392_; lean_object* v_instanceTypedMVars_393_; lean_object* v_synthNormMemo_394_; lean_object* v___x_396_; uint8_t v_isShared_397_; uint8_t v_isSharedCheck_408_; 
v_depth_383_ = lean_ctor_get(v_mctx_375_, 0);
v_levelAssignDepth_384_ = lean_ctor_get(v_mctx_375_, 1);
v_lmvarCounter_385_ = lean_ctor_get(v_mctx_375_, 2);
v_mvarCounter_386_ = lean_ctor_get(v_mctx_375_, 3);
v_lDecls_387_ = lean_ctor_get(v_mctx_375_, 4);
v_decls_388_ = lean_ctor_get(v_mctx_375_, 5);
v_userNames_389_ = lean_ctor_get(v_mctx_375_, 6);
v_lAssignment_390_ = lean_ctor_get(v_mctx_375_, 7);
v_eAssignment_391_ = lean_ctor_get(v_mctx_375_, 8);
v_dAssignment_392_ = lean_ctor_get(v_mctx_375_, 9);
v_instanceTypedMVars_393_ = lean_ctor_get(v_mctx_375_, 10);
v_synthNormMemo_394_ = lean_ctor_get(v_mctx_375_, 11);
v_isSharedCheck_408_ = !lean_is_exclusive(v_mctx_375_);
if (v_isSharedCheck_408_ == 0)
{
v___x_396_ = v_mctx_375_;
v_isShared_397_ = v_isSharedCheck_408_;
goto v_resetjp_395_;
}
else
{
lean_inc(v_synthNormMemo_394_);
lean_inc(v_instanceTypedMVars_393_);
lean_inc(v_dAssignment_392_);
lean_inc(v_eAssignment_391_);
lean_inc(v_lAssignment_390_);
lean_inc(v_userNames_389_);
lean_inc(v_decls_388_);
lean_inc(v_lDecls_387_);
lean_inc(v_mvarCounter_386_);
lean_inc(v_lmvarCounter_385_);
lean_inc(v_levelAssignDepth_384_);
lean_inc(v_depth_383_);
lean_dec(v_mctx_375_);
v___x_396_ = lean_box(0);
v_isShared_397_ = v_isSharedCheck_408_;
goto v_resetjp_395_;
}
v_resetjp_395_:
{
lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_401_; 
v___x_398_ = lean_box(0);
v___x_399_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0___redArg(v_eAssignment_391_, v_mvarId_370_, v_val_371_);
if (v_isShared_397_ == 0)
{
lean_ctor_set(v___x_396_, 8, v___x_399_);
v___x_401_ = v___x_396_;
goto v_reusejp_400_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_407_, 0, v_depth_383_);
lean_ctor_set(v_reuseFailAlloc_407_, 1, v_levelAssignDepth_384_);
lean_ctor_set(v_reuseFailAlloc_407_, 2, v_lmvarCounter_385_);
lean_ctor_set(v_reuseFailAlloc_407_, 3, v_mvarCounter_386_);
lean_ctor_set(v_reuseFailAlloc_407_, 4, v_lDecls_387_);
lean_ctor_set(v_reuseFailAlloc_407_, 5, v_decls_388_);
lean_ctor_set(v_reuseFailAlloc_407_, 6, v_userNames_389_);
lean_ctor_set(v_reuseFailAlloc_407_, 7, v_lAssignment_390_);
lean_ctor_set(v_reuseFailAlloc_407_, 8, v___x_399_);
lean_ctor_set(v_reuseFailAlloc_407_, 9, v_dAssignment_392_);
lean_ctor_set(v_reuseFailAlloc_407_, 10, v_instanceTypedMVars_393_);
lean_ctor_set(v_reuseFailAlloc_407_, 11, v_synthNormMemo_394_);
v___x_401_ = v_reuseFailAlloc_407_;
goto v_reusejp_400_;
}
v_reusejp_400_:
{
lean_object* v___x_403_; 
if (v_isShared_382_ == 0)
{
lean_ctor_set(v___x_381_, 0, v___x_401_);
v___x_403_ = v___x_381_;
goto v_reusejp_402_;
}
else
{
lean_object* v_reuseFailAlloc_406_; 
v_reuseFailAlloc_406_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_406_, 0, v___x_401_);
lean_ctor_set(v_reuseFailAlloc_406_, 1, v_cache_376_);
lean_ctor_set(v_reuseFailAlloc_406_, 2, v_zetaDeltaFVarIds_377_);
lean_ctor_set(v_reuseFailAlloc_406_, 3, v_postponed_378_);
lean_ctor_set(v_reuseFailAlloc_406_, 4, v_diag_379_);
v___x_403_ = v_reuseFailAlloc_406_;
goto v_reusejp_402_;
}
v_reusejp_402_:
{
lean_object* v___x_404_; lean_object* v___x_405_; 
v___x_404_ = lean_st_ref_put(v___y_372_, v___x_403_);
v___x_405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_405_, 0, v___x_398_);
return v___x_405_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0___redArg___boxed(lean_object* v_mvarId_410_, lean_object* v_val_411_, lean_object* v___y_412_, lean_object* v___y_413_){
_start:
{
lean_object* v_res_414_; 
v_res_414_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0___redArg(v_mvarId_410_, v_val_411_, v___y_412_);
lean_dec(v___y_412_);
return v_res_414_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__3(size_t v_sz_415_, size_t v_i_416_, lean_object* v_bs_417_){
_start:
{
uint8_t v___x_418_; 
v___x_418_ = lean_usize_dec_lt(v_i_416_, v_sz_415_);
if (v___x_418_ == 0)
{
return v_bs_417_;
}
else
{
lean_object* v_v_419_; lean_object* v___x_420_; lean_object* v_bs_x27_421_; lean_object* v___x_422_; size_t v___x_423_; size_t v___x_424_; lean_object* v___x_425_; 
v_v_419_ = lean_array_uget(v_bs_417_, v_i_416_);
v___x_420_ = lean_unsigned_to_nat(0u);
v_bs_x27_421_ = lean_array_uset(v_bs_417_, v_i_416_, v___x_420_);
v___x_422_ = l_Lean_mkFVar(v_v_419_);
v___x_423_ = ((size_t)1ULL);
v___x_424_ = lean_usize_add(v_i_416_, v___x_423_);
v___x_425_ = lean_array_uset(v_bs_x27_421_, v_i_416_, v___x_422_);
v_i_416_ = v___x_424_;
v_bs_417_ = v___x_425_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__3___boxed(lean_object* v_sz_427_, lean_object* v_i_428_, lean_object* v_bs_429_){
_start:
{
size_t v_sz_boxed_430_; size_t v_i_boxed_431_; lean_object* v_res_432_; 
v_sz_boxed_430_ = lean_unbox_usize(v_sz_427_);
lean_dec(v_sz_427_);
v_i_boxed_431_ = lean_unbox_usize(v_i_428_);
lean_dec(v_i_428_);
v_res_432_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__3(v_sz_boxed_430_, v_i_boxed_431_, v_bs_429_);
return v_res_432_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1_spec__2(lean_object* v_msgData_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_){
_start:
{
lean_object* v___x_439_; lean_object* v_env_440_; uint8_t v___x_441_; lean_object* v_env_442_; lean_object* v___x_443_; lean_object* v_toCold_444_; lean_object* v_mctx_445_; lean_object* v_lctx_446_; lean_object* v_options_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; 
v___x_439_ = lean_st_ref_get(v___y_437_);
v_env_440_ = lean_ctor_get(v___x_439_, 0);
lean_inc_ref(v_env_440_);
lean_dec(v___x_439_);
v___x_441_ = 0;
v_env_442_ = l_Lean_Environment_setRecordingDeps(v_env_440_, v___x_441_);
v___x_443_ = lean_st_ref_get(v___y_435_);
v_toCold_444_ = lean_ctor_get(v___y_436_, 0);
v_mctx_445_ = lean_ctor_get(v___x_443_, 0);
lean_inc_ref(v_mctx_445_);
lean_dec(v___x_443_);
v_lctx_446_ = lean_ctor_get(v___y_434_, 2);
v_options_447_ = lean_ctor_get(v_toCold_444_, 2);
lean_inc_ref(v_options_447_);
lean_inc_ref(v_lctx_446_);
v___x_448_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_448_, 0, v_env_442_);
lean_ctor_set(v___x_448_, 1, v_mctx_445_);
lean_ctor_set(v___x_448_, 2, v_lctx_446_);
lean_ctor_set(v___x_448_, 3, v_options_447_);
v___x_449_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_449_, 0, v___x_448_);
lean_ctor_set(v___x_449_, 1, v_msgData_433_);
v___x_450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_450_, 0, v___x_449_);
return v___x_450_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1_spec__2___boxed(lean_object* v_msgData_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_){
_start:
{
lean_object* v_res_457_; 
v_res_457_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1_spec__2(v_msgData_451_, v___y_452_, v___y_453_, v___y_454_, v___y_455_);
lean_dec(v___y_455_);
lean_dec_ref(v___y_454_);
lean_dec(v___y_453_);
lean_dec_ref(v___y_452_);
return v_res_457_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1___closed__0(void){
_start:
{
lean_object* v___x_458_; double v___x_459_; 
v___x_458_ = lean_unsigned_to_nat(0u);
v___x_459_ = lean_float_of_nat(v___x_458_);
return v___x_459_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1(lean_object* v_cls_463_, lean_object* v_msg_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_){
_start:
{
lean_object* v_ref_470_; lean_object* v___x_471_; lean_object* v_a_472_; lean_object* v___x_474_; uint8_t v_isShared_475_; uint8_t v_isSharedCheck_517_; 
v_ref_470_ = lean_ctor_get(v___y_467_, 2);
v___x_471_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1_spec__2(v_msg_464_, v___y_465_, v___y_466_, v___y_467_, v___y_468_);
v_a_472_ = lean_ctor_get(v___x_471_, 0);
v_isSharedCheck_517_ = !lean_is_exclusive(v___x_471_);
if (v_isSharedCheck_517_ == 0)
{
v___x_474_ = v___x_471_;
v_isShared_475_ = v_isSharedCheck_517_;
goto v_resetjp_473_;
}
else
{
lean_inc(v_a_472_);
lean_dec(v___x_471_);
v___x_474_ = lean_box(0);
v_isShared_475_ = v_isSharedCheck_517_;
goto v_resetjp_473_;
}
v_resetjp_473_:
{
lean_object* v___x_476_; lean_object* v_traceState_477_; lean_object* v_env_478_; lean_object* v_nextMacroScope_479_; lean_object* v_ngen_480_; lean_object* v_auxDeclNGen_481_; lean_object* v_cache_482_; lean_object* v_recordedDeps_483_; lean_object* v_messages_484_; lean_object* v_infoState_485_; lean_object* v_snapshotTasks_486_; lean_object* v___x_488_; uint8_t v_isShared_489_; uint8_t v_isSharedCheck_516_; 
v___x_476_ = lean_st_ref_take(v___y_468_);
v_traceState_477_ = lean_ctor_get(v___x_476_, 4);
v_env_478_ = lean_ctor_get(v___x_476_, 0);
v_nextMacroScope_479_ = lean_ctor_get(v___x_476_, 1);
v_ngen_480_ = lean_ctor_get(v___x_476_, 2);
v_auxDeclNGen_481_ = lean_ctor_get(v___x_476_, 3);
v_cache_482_ = lean_ctor_get(v___x_476_, 5);
v_recordedDeps_483_ = lean_ctor_get(v___x_476_, 6);
v_messages_484_ = lean_ctor_get(v___x_476_, 7);
v_infoState_485_ = lean_ctor_get(v___x_476_, 8);
v_snapshotTasks_486_ = lean_ctor_get(v___x_476_, 9);
v_isSharedCheck_516_ = !lean_is_exclusive(v___x_476_);
if (v_isSharedCheck_516_ == 0)
{
v___x_488_ = v___x_476_;
v_isShared_489_ = v_isSharedCheck_516_;
goto v_resetjp_487_;
}
else
{
lean_inc(v_snapshotTasks_486_);
lean_inc(v_infoState_485_);
lean_inc(v_messages_484_);
lean_inc(v_recordedDeps_483_);
lean_inc(v_cache_482_);
lean_inc(v_traceState_477_);
lean_inc(v_auxDeclNGen_481_);
lean_inc(v_ngen_480_);
lean_inc(v_nextMacroScope_479_);
lean_inc(v_env_478_);
lean_dec(v___x_476_);
v___x_488_ = lean_box(0);
v_isShared_489_ = v_isSharedCheck_516_;
goto v_resetjp_487_;
}
v_resetjp_487_:
{
uint64_t v_tid_490_; lean_object* v_traces_491_; lean_object* v___x_493_; uint8_t v_isShared_494_; uint8_t v_isSharedCheck_515_; 
v_tid_490_ = lean_ctor_get_uint64(v_traceState_477_, sizeof(void*)*1);
v_traces_491_ = lean_ctor_get(v_traceState_477_, 0);
v_isSharedCheck_515_ = !lean_is_exclusive(v_traceState_477_);
if (v_isSharedCheck_515_ == 0)
{
v___x_493_ = v_traceState_477_;
v_isShared_494_ = v_isSharedCheck_515_;
goto v_resetjp_492_;
}
else
{
lean_inc(v_traces_491_);
lean_dec(v_traceState_477_);
v___x_493_ = lean_box(0);
v_isShared_494_ = v_isSharedCheck_515_;
goto v_resetjp_492_;
}
v_resetjp_492_:
{
lean_object* v___x_495_; lean_object* v___x_496_; double v___x_497_; uint8_t v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_506_; 
v___x_495_ = lean_box(0);
v___x_496_ = lean_box(0);
v___x_497_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1___closed__0);
v___x_498_ = 0;
v___x_499_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1___closed__1));
v___x_500_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_500_, 0, v_cls_463_);
lean_ctor_set(v___x_500_, 1, v___x_496_);
lean_ctor_set(v___x_500_, 2, v___x_499_);
lean_ctor_set_float(v___x_500_, sizeof(void*)*3, v___x_497_);
lean_ctor_set_float(v___x_500_, sizeof(void*)*3 + 8, v___x_497_);
lean_ctor_set_uint8(v___x_500_, sizeof(void*)*3 + 16, v___x_498_);
v___x_501_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1___closed__2));
v___x_502_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_502_, 0, v___x_500_);
lean_ctor_set(v___x_502_, 1, v_a_472_);
lean_ctor_set(v___x_502_, 2, v___x_501_);
lean_inc(v_ref_470_);
v___x_503_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_503_, 0, v_ref_470_);
lean_ctor_set(v___x_503_, 1, v___x_502_);
v___x_504_ = l_Lean_PersistentArray_push___redArg(v_traces_491_, v___x_503_);
if (v_isShared_494_ == 0)
{
lean_ctor_set(v___x_493_, 0, v___x_504_);
v___x_506_ = v___x_493_;
goto v_reusejp_505_;
}
else
{
lean_object* v_reuseFailAlloc_514_; 
v_reuseFailAlloc_514_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_514_, 0, v___x_504_);
lean_ctor_set_uint64(v_reuseFailAlloc_514_, sizeof(void*)*1, v_tid_490_);
v___x_506_ = v_reuseFailAlloc_514_;
goto v_reusejp_505_;
}
v_reusejp_505_:
{
lean_object* v___x_508_; 
if (v_isShared_489_ == 0)
{
lean_ctor_set(v___x_488_, 4, v___x_506_);
v___x_508_ = v___x_488_;
goto v_reusejp_507_;
}
else
{
lean_object* v_reuseFailAlloc_513_; 
v_reuseFailAlloc_513_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_513_, 0, v_env_478_);
lean_ctor_set(v_reuseFailAlloc_513_, 1, v_nextMacroScope_479_);
lean_ctor_set(v_reuseFailAlloc_513_, 2, v_ngen_480_);
lean_ctor_set(v_reuseFailAlloc_513_, 3, v_auxDeclNGen_481_);
lean_ctor_set(v_reuseFailAlloc_513_, 4, v___x_506_);
lean_ctor_set(v_reuseFailAlloc_513_, 5, v_cache_482_);
lean_ctor_set(v_reuseFailAlloc_513_, 6, v_recordedDeps_483_);
lean_ctor_set(v_reuseFailAlloc_513_, 7, v_messages_484_);
lean_ctor_set(v_reuseFailAlloc_513_, 8, v_infoState_485_);
lean_ctor_set(v_reuseFailAlloc_513_, 9, v_snapshotTasks_486_);
v___x_508_ = v_reuseFailAlloc_513_;
goto v_reusejp_507_;
}
v_reusejp_507_:
{
lean_object* v___x_509_; lean_object* v___x_511_; 
v___x_509_ = lean_st_ref_put(v___y_468_, v___x_508_);
if (v_isShared_475_ == 0)
{
lean_ctor_set(v___x_474_, 0, v___x_495_);
v___x_511_ = v___x_474_;
goto v_reusejp_510_;
}
else
{
lean_object* v_reuseFailAlloc_512_; 
v_reuseFailAlloc_512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_512_, 0, v___x_495_);
v___x_511_ = v_reuseFailAlloc_512_;
goto v_reusejp_510_;
}
v_reusejp_510_:
{
return v___x_511_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1___boxed(lean_object* v_cls_518_, lean_object* v_msg_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_){
_start:
{
lean_object* v_res_525_; 
v_res_525_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1(v_cls_518_, v_msg_519_, v___y_520_, v___y_521_, v___y_522_, v___y_523_);
lean_dec(v___y_523_);
lean_dec_ref(v___y_522_);
lean_dec(v___y_521_);
lean_dec_ref(v___y_520_);
return v_res_525_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5(void){
_start:
{
lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; 
v___x_535_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__2));
v___x_536_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__4));
v___x_537_ = l_Lean_Name_append(v___x_536_, v___x_535_);
return v___x_537_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__7(void){
_start:
{
lean_object* v___x_539_; lean_object* v___x_540_; 
v___x_539_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__6));
v___x_540_ = l_Lean_stringToMessageData(v___x_539_);
return v___x_540_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__9(void){
_start:
{
lean_object* v___x_542_; lean_object* v___x_543_; 
v___x_542_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__8));
v___x_543_ = l_Lean_stringToMessageData(v___x_542_);
return v___x_543_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__11(void){
_start:
{
lean_object* v___x_545_; lean_object* v___x_546_; 
v___x_545_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__10));
v___x_546_ = l_Lean_stringToMessageData(v___x_545_);
return v___x_546_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__15(void){
_start:
{
lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; 
v___x_550_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__14));
v___x_551_ = lean_unsigned_to_nat(15u);
v___x_552_ = lean_unsigned_to_nat(120u);
v___x_553_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__13));
v___x_554_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__12));
v___x_555_ = l_mkPanicMessageWithDecl(v___x_554_, v___x_553_, v___x_552_, v___x_551_, v___x_550_);
return v___x_555_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop(lean_object* v_mvarId_556_, lean_object* v_givenNames_557_, lean_object* v_recursorInfo_558_, lean_object* v_reverted_559_, lean_object* v_major_560_, lean_object* v_indices_561_, lean_object* v_baseSubst_562_, lean_object* v_initialArity_563_, lean_object* v_numMinors_564_, lean_object* v_pos_565_, lean_object* v_minorIdx_566_, lean_object* v_recursor_567_, lean_object* v_recursorType_568_, uint8_t v_consumedMajor_569_, lean_object* v_subgoals_570_, lean_object* v_a_571_, lean_object* v_a_572_, lean_object* v_a_573_, lean_object* v_a_574_){
_start:
{
lean_object* v___y_577_; lean_object* v___y_578_; lean_object* v___y_579_; lean_object* v___y_580_; lean_object* v___x_633_; 
v___x_633_ = l_Lean_Meta_whnfForall(v_recursorType_568_, v_a_571_, v_a_572_, v_a_573_, v_a_574_);
if (lean_obj_tag(v___x_633_) == 0)
{
lean_object* v_a_634_; uint8_t v___x_647_; 
v_a_634_ = lean_ctor_get(v___x_633_, 0);
lean_inc(v_a_634_);
lean_dec_ref_known(v___x_633_, 1);
v___x_647_ = l_Lean_Expr_isForall(v_a_634_);
if (v___x_647_ == 0)
{
lean_dec(v_a_634_);
lean_dec(v_minorIdx_566_);
lean_dec(v_pos_565_);
lean_dec(v_baseSubst_562_);
lean_dec_ref(v_major_560_);
goto v___jp_635_;
}
else
{
lean_object* v_numArgs_648_; uint8_t v___x_649_; uint8_t v___y_651_; lean_object* v___y_652_; lean_object* v___y_653_; lean_object* v___y_654_; lean_object* v___y_655_; lean_object* v___y_656_; lean_object* v___y_657_; lean_object* v___y_658_; lean_object* v___y_659_; lean_object* v___y_660_; lean_object* v___y_661_; lean_object* v___y_662_; lean_object* v___y_663_; lean_object* v___y_664_; uint8_t v___y_665_; lean_object* v___y_701_; lean_object* v___y_702_; uint8_t v___y_703_; lean_object* v___y_704_; lean_object* v___y_705_; lean_object* v___y_706_; lean_object* v___y_707_; lean_object* v___y_708_; lean_object* v___y_709_; lean_object* v___y_710_; lean_object* v___y_711_; lean_object* v___y_712_; lean_object* v___y_713_; lean_object* v___y_714_; lean_object* v___y_732_; uint8_t v___y_733_; lean_object* v___y_734_; lean_object* v___y_735_; lean_object* v___y_736_; lean_object* v___y_737_; lean_object* v___y_738_; lean_object* v___y_739_; lean_object* v___y_740_; lean_object* v___y_741_; lean_object* v___y_742_; lean_object* v___y_743_; lean_object* v___y_744_; lean_object* v___y_788_; lean_object* v___y_789_; uint8_t v___y_790_; lean_object* v___y_791_; lean_object* v___y_792_; lean_object* v___y_793_; lean_object* v___y_794_; lean_object* v___y_795_; lean_object* v___y_796_; lean_object* v___y_808_; lean_object* v___y_809_; lean_object* v___y_810_; lean_object* v___y_811_; lean_object* v___y_812_; lean_object* v___y_813_; lean_object* v___y_814_; uint8_t v___y_815_; uint8_t v___y_830_; lean_object* v___y_831_; lean_object* v___y_832_; lean_object* v___y_833_; lean_object* v___y_834_; lean_object* v___y_835_; lean_object* v___y_836_; lean_object* v___y_837_; 
v_numArgs_648_ = lean_ctor_get(v_recursorInfo_558_, 3);
v___x_649_ = lean_nat_dec_lt(v_pos_565_, v_numArgs_648_);
if (v___x_649_ == 0)
{
lean_dec(v_a_634_);
lean_dec(v_minorIdx_566_);
lean_dec(v_pos_565_);
lean_dec(v_baseSubst_562_);
lean_dec_ref(v_major_560_);
goto v___jp_635_;
}
else
{
lean_object* v___x_897_; uint8_t v___x_898_; 
v___x_897_ = l_Lean_Meta_RecursorInfo_firstIndexPos(v_recursorInfo_558_);
v___x_898_ = lean_nat_dec_eq(v_pos_565_, v___x_897_);
lean_dec(v___x_897_);
if (v___x_898_ == 0)
{
lean_object* v___x_899_; 
lean_inc(v_mvarId_556_);
v___x_899_ = l_Lean_MVarId_getTag(v_mvarId_556_, v_a_571_, v_a_572_, v_a_573_, v_a_574_);
if (lean_obj_tag(v___x_899_) == 0)
{
lean_object* v_a_900_; lean_object* v___y_902_; lean_object* v___y_903_; lean_object* v___y_904_; lean_object* v___y_905_; uint8_t v___x_916_; 
v_a_900_ = lean_ctor_get(v___x_899_, 0);
lean_inc(v_a_900_);
lean_dec_ref_known(v___x_899_, 1);
v___x_916_ = lean_nat_dec_le(v_numMinors_564_, v_minorIdx_566_);
if (v___x_916_ == 0)
{
v___y_902_ = v_a_571_;
v___y_903_ = v_a_572_;
v___y_904_ = v_a_573_;
v___y_905_ = v_a_574_;
goto v___jp_901_;
}
else
{
lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; 
v___x_917_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1));
v___x_918_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9);
lean_inc(v_mvarId_556_);
v___x_919_ = l_Lean_Meta_throwTacticEx___redArg(v___x_917_, v_mvarId_556_, v___x_918_, v_a_571_, v_a_572_, v_a_573_, v_a_574_);
if (lean_obj_tag(v___x_919_) == 0)
{
lean_dec_ref_known(v___x_919_, 1);
v___y_902_ = v_a_571_;
v___y_903_ = v_a_572_;
v___y_904_ = v_a_573_;
v___y_905_ = v_a_574_;
goto v___jp_901_;
}
else
{
lean_object* v_a_920_; lean_object* v___x_922_; uint8_t v_isShared_923_; uint8_t v_isSharedCheck_927_; 
lean_dec(v_a_900_);
lean_dec(v_a_634_);
lean_dec_ref(v_subgoals_570_);
lean_dec_ref(v_recursor_567_);
lean_dec(v_minorIdx_566_);
lean_dec(v_pos_565_);
lean_dec(v_baseSubst_562_);
lean_dec_ref(v_major_560_);
lean_dec(v_mvarId_556_);
v_a_920_ = lean_ctor_get(v___x_919_, 0);
v_isSharedCheck_927_ = !lean_is_exclusive(v___x_919_);
if (v_isSharedCheck_927_ == 0)
{
v___x_922_ = v___x_919_;
v_isShared_923_ = v_isSharedCheck_927_;
goto v_resetjp_921_;
}
else
{
lean_inc(v_a_920_);
lean_dec(v___x_919_);
v___x_922_ = lean_box(0);
v_isShared_923_ = v_isSharedCheck_927_;
goto v_resetjp_921_;
}
v_resetjp_921_:
{
lean_object* v___x_925_; 
if (v_isShared_923_ == 0)
{
v___x_925_ = v___x_922_;
goto v_reusejp_924_;
}
else
{
lean_object* v_reuseFailAlloc_926_; 
v_reuseFailAlloc_926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_926_, 0, v_a_920_);
v___x_925_ = v_reuseFailAlloc_926_;
goto v_reusejp_924_;
}
v_reusejp_924_:
{
return v___x_925_;
}
}
}
}
v___jp_901_:
{
if (lean_obj_tag(v_a_634_) == 7)
{
lean_object* v_binderName_906_; lean_object* v_binderType_907_; uint8_t v_binderInfo_908_; lean_object* v___x_909_; lean_object* v___x_910_; uint8_t v___x_911_; 
v_binderName_906_ = lean_ctor_get(v_a_634_, 0);
v_binderType_907_ = lean_ctor_get(v_a_634_, 1);
v_binderInfo_908_ = lean_ctor_get_uint8(v_a_634_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_907_);
v___x_909_ = l_Lean_Expr_headBeta(v_binderType_907_);
v___x_910_ = lean_unsigned_to_nat(1u);
v___x_911_ = lean_nat_dec_eq(v_numMinors_564_, v___x_910_);
if (v___x_911_ == 0)
{
lean_object* v___x_912_; lean_object* v___x_913_; 
v___x_912_ = l_Lean_Name_eraseMacroScopes(v_binderName_906_);
v___x_913_ = l_Lean_Name_append(v_a_900_, v___x_912_);
v___y_830_ = v_binderInfo_908_;
v___y_831_ = v___y_902_;
v___y_832_ = v___y_904_;
v___y_833_ = v___x_909_;
v___y_834_ = v___x_910_;
v___y_835_ = v___y_903_;
v___y_836_ = v___y_905_;
v___y_837_ = v___x_913_;
goto v___jp_829_;
}
else
{
v___y_830_ = v_binderInfo_908_;
v___y_831_ = v___y_902_;
v___y_832_ = v___y_904_;
v___y_833_ = v___x_909_;
v___y_834_ = v___x_910_;
v___y_835_ = v___y_903_;
v___y_836_ = v___y_905_;
v___y_837_ = v_a_900_;
goto v___jp_829_;
}
}
else
{
lean_object* v___x_914_; lean_object* v___x_915_; 
lean_dec(v_a_900_);
lean_dec(v_a_634_);
lean_dec_ref(v_subgoals_570_);
lean_dec_ref(v_recursor_567_);
lean_dec(v_minorIdx_566_);
lean_dec(v_pos_565_);
lean_dec(v_baseSubst_562_);
lean_dec_ref(v_major_560_);
lean_dec(v_mvarId_556_);
v___x_914_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__15, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__15_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__15);
v___x_915_ = l_panic___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__4(v___x_914_, v___y_902_, v___y_903_, v___y_904_, v___y_905_);
return v___x_915_;
}
}
}
else
{
lean_object* v_a_928_; lean_object* v___x_930_; uint8_t v_isShared_931_; uint8_t v_isSharedCheck_935_; 
lean_dec(v_a_634_);
lean_dec_ref(v_subgoals_570_);
lean_dec_ref(v_recursor_567_);
lean_dec(v_minorIdx_566_);
lean_dec(v_pos_565_);
lean_dec(v_baseSubst_562_);
lean_dec_ref(v_major_560_);
lean_dec(v_mvarId_556_);
v_a_928_ = lean_ctor_get(v___x_899_, 0);
v_isSharedCheck_935_ = !lean_is_exclusive(v___x_899_);
if (v_isSharedCheck_935_ == 0)
{
v___x_930_ = v___x_899_;
v_isShared_931_ = v_isSharedCheck_935_;
goto v_resetjp_929_;
}
else
{
lean_inc(v_a_928_);
lean_dec(v___x_899_);
v___x_930_ = lean_box(0);
v_isShared_931_ = v_isSharedCheck_935_;
goto v_resetjp_929_;
}
v_resetjp_929_:
{
lean_object* v___x_933_; 
if (v_isShared_931_ == 0)
{
v___x_933_ = v___x_930_;
goto v_reusejp_932_;
}
else
{
lean_object* v_reuseFailAlloc_934_; 
v_reuseFailAlloc_934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_934_, 0, v_a_928_);
v___x_933_ = v_reuseFailAlloc_934_;
goto v_reusejp_932_;
}
v_reusejp_932_:
{
return v___x_933_;
}
}
}
}
else
{
lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v_fst_939_; lean_object* v_snd_940_; uint8_t v___x_956_; 
v___x_936_ = lean_unsigned_to_nat(0u);
v___x_937_ = lean_array_get_size(v_indices_561_);
v___x_956_ = lean_nat_dec_lt(v___x_936_, v___x_937_);
if (v___x_956_ == 0)
{
v_fst_939_ = v_recursor_567_;
v_snd_940_ = v_a_634_;
goto v___jp_938_;
}
else
{
lean_object* v___x_957_; size_t v___x_958_; size_t v___x_959_; lean_object* v___x_960_; 
v___x_957_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_957_, 0, v_recursor_567_);
lean_ctor_set(v___x_957_, 1, v_a_634_);
v___x_958_ = ((size_t)0ULL);
v___x_959_ = lean_usize_of_nat(v___x_937_);
lean_inc(v_mvarId_556_);
v___x_960_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__5(v_mvarId_556_, v_indices_561_, v___x_958_, v___x_959_, v___x_957_, v_a_571_, v_a_572_, v_a_573_, v_a_574_);
if (lean_obj_tag(v___x_960_) == 0)
{
lean_object* v_a_961_; lean_object* v_fst_962_; lean_object* v_snd_963_; 
v_a_961_ = lean_ctor_get(v___x_960_, 0);
lean_inc(v_a_961_);
lean_dec_ref_known(v___x_960_, 1);
v_fst_962_ = lean_ctor_get(v_a_961_, 0);
lean_inc(v_fst_962_);
v_snd_963_ = lean_ctor_get(v_a_961_, 1);
lean_inc(v_snd_963_);
lean_dec(v_a_961_);
v_fst_939_ = v_fst_962_;
v_snd_940_ = v_snd_963_;
goto v___jp_938_;
}
else
{
lean_object* v_a_964_; lean_object* v___x_966_; uint8_t v_isShared_967_; uint8_t v_isSharedCheck_971_; 
lean_dec_ref(v_subgoals_570_);
lean_dec(v_minorIdx_566_);
lean_dec(v_pos_565_);
lean_dec(v_baseSubst_562_);
lean_dec_ref(v_major_560_);
lean_dec(v_mvarId_556_);
v_a_964_ = lean_ctor_get(v___x_960_, 0);
v_isSharedCheck_971_ = !lean_is_exclusive(v___x_960_);
if (v_isSharedCheck_971_ == 0)
{
v___x_966_ = v___x_960_;
v_isShared_967_ = v_isSharedCheck_971_;
goto v_resetjp_965_;
}
else
{
lean_inc(v_a_964_);
lean_dec(v___x_960_);
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
v___jp_938_:
{
lean_object* v___x_941_; lean_object* v___x_942_; 
lean_inc_ref(v_major_560_);
v___x_941_ = l_Lean_Expr_app___override(v_fst_939_, v_major_560_);
lean_inc(v_mvarId_556_);
v___x_942_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTypeBody(v_mvarId_556_, v_snd_940_, v_major_560_, v_a_571_, v_a_572_, v_a_573_, v_a_574_);
if (lean_obj_tag(v___x_942_) == 0)
{
lean_object* v_a_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; 
v_a_943_ = lean_ctor_get(v___x_942_, 0);
lean_inc(v_a_943_);
lean_dec_ref_known(v___x_942_, 1);
v___x_944_ = lean_unsigned_to_nat(1u);
v___x_945_ = lean_nat_add(v_pos_565_, v___x_944_);
lean_dec(v_pos_565_);
v___x_946_ = lean_nat_add(v___x_945_, v___x_937_);
lean_dec(v___x_945_);
v_pos_565_ = v___x_946_;
v_recursor_567_ = v___x_941_;
v_recursorType_568_ = v_a_943_;
v_consumedMajor_569_ = v___x_647_;
goto _start;
}
else
{
lean_object* v_a_948_; lean_object* v___x_950_; uint8_t v_isShared_951_; uint8_t v_isSharedCheck_955_; 
lean_dec_ref(v___x_941_);
lean_dec_ref(v_subgoals_570_);
lean_dec(v_minorIdx_566_);
lean_dec(v_pos_565_);
lean_dec(v_baseSubst_562_);
lean_dec_ref(v_major_560_);
lean_dec(v_mvarId_556_);
v_a_948_ = lean_ctor_get(v___x_942_, 0);
v_isSharedCheck_955_ = !lean_is_exclusive(v___x_942_);
if (v_isSharedCheck_955_ == 0)
{
v___x_950_ = v___x_942_;
v_isShared_951_ = v_isSharedCheck_955_;
goto v_resetjp_949_;
}
else
{
lean_inc(v_a_948_);
lean_dec(v___x_942_);
v___x_950_ = lean_box(0);
v_isShared_951_ = v_isSharedCheck_955_;
goto v_resetjp_949_;
}
v_resetjp_949_:
{
lean_object* v___x_953_; 
if (v_isShared_951_ == 0)
{
v___x_953_ = v___x_950_;
goto v_reusejp_952_;
}
else
{
lean_object* v_reuseFailAlloc_954_; 
v_reuseFailAlloc_954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_954_, 0, v_a_948_);
v___x_953_ = v_reuseFailAlloc_954_;
goto v_reusejp_952_;
}
v_reusejp_952_:
{
return v___x_953_;
}
}
}
}
}
}
v___jp_650_:
{
lean_object* v___x_666_; 
v___x_666_ = l_Lean_Meta_introNCore(v___y_664_, v___y_658_, v___y_661_, v___y_665_, v___y_651_, v___y_656_, v___y_659_, v___y_655_, v___y_657_);
if (lean_obj_tag(v___x_666_) == 0)
{
lean_object* v_a_667_; lean_object* v_fst_668_; lean_object* v_snd_669_; lean_object* v___x_670_; lean_object* v___x_671_; 
v_a_667_ = lean_ctor_get(v___x_666_, 0);
lean_inc(v_a_667_);
lean_dec_ref_known(v___x_666_, 1);
v_fst_668_ = lean_ctor_get(v_a_667_, 0);
lean_inc(v_fst_668_);
v_snd_669_ = lean_ctor_get(v_a_667_, 1);
lean_inc(v_snd_669_);
lean_dec(v_a_667_);
v___x_670_ = lean_box(0);
v___x_671_ = l_Lean_Meta_introNCore(v_snd_669_, v___y_654_, v___x_670_, v___y_651_, v___x_649_, v___y_656_, v___y_659_, v___y_655_, v___y_657_);
if (lean_obj_tag(v___x_671_) == 0)
{
lean_object* v_a_672_; lean_object* v_fst_673_; lean_object* v_snd_674_; lean_object* v___x_675_; size_t v_sz_676_; size_t v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; 
v_a_672_ = lean_ctor_get(v___x_671_, 0);
lean_inc(v_a_672_);
lean_dec_ref_known(v___x_671_, 1);
v_fst_673_ = lean_ctor_get(v_a_672_, 0);
lean_inc(v_fst_673_);
v_snd_674_ = lean_ctor_get(v_a_672_, 1);
lean_inc(v_snd_674_);
lean_dec(v_a_672_);
lean_inc(v_baseSubst_562_);
lean_inc(v___y_660_);
v___x_675_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__2___redArg(v___y_653_, v_reverted_559_, v_fst_673_, v___y_660_, v___y_660_, v_baseSubst_562_);
lean_dec(v___y_660_);
lean_dec(v_fst_673_);
lean_dec(v___y_653_);
v_sz_676_ = lean_array_size(v_fst_668_);
v___x_677_ = ((size_t)0ULL);
v___x_678_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__3(v_sz_676_, v___x_677_, v_fst_668_);
v___x_679_ = lean_nat_add(v_pos_565_, v___y_652_);
lean_dec(v_pos_565_);
v___x_680_ = lean_nat_add(v_minorIdx_566_, v___y_652_);
lean_dec(v_minorIdx_566_);
v___x_681_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_681_, 0, v_snd_674_);
lean_ctor_set(v___x_681_, 1, v___x_678_);
lean_ctor_set(v___x_681_, 2, v___x_675_);
v___x_682_ = lean_array_push(v_subgoals_570_, v___x_681_);
v_pos_565_ = v___x_679_;
v_minorIdx_566_ = v___x_680_;
v_recursor_567_ = v___y_662_;
v_recursorType_568_ = v___y_663_;
v_subgoals_570_ = v___x_682_;
v_a_571_ = v___y_656_;
v_a_572_ = v___y_659_;
v_a_573_ = v___y_655_;
v_a_574_ = v___y_657_;
goto _start;
}
else
{
lean_object* v_a_684_; lean_object* v___x_686_; uint8_t v_isShared_687_; uint8_t v_isSharedCheck_691_; 
lean_dec(v_fst_668_);
lean_dec_ref(v___y_663_);
lean_dec_ref(v___y_662_);
lean_dec(v___y_660_);
lean_dec(v___y_653_);
lean_dec_ref(v_subgoals_570_);
lean_dec(v_minorIdx_566_);
lean_dec(v_pos_565_);
lean_dec(v_baseSubst_562_);
lean_dec_ref(v_major_560_);
lean_dec(v_mvarId_556_);
v_a_684_ = lean_ctor_get(v___x_671_, 0);
v_isSharedCheck_691_ = !lean_is_exclusive(v___x_671_);
if (v_isSharedCheck_691_ == 0)
{
v___x_686_ = v___x_671_;
v_isShared_687_ = v_isSharedCheck_691_;
goto v_resetjp_685_;
}
else
{
lean_inc(v_a_684_);
lean_dec(v___x_671_);
v___x_686_ = lean_box(0);
v_isShared_687_ = v_isSharedCheck_691_;
goto v_resetjp_685_;
}
v_resetjp_685_:
{
lean_object* v___x_689_; 
if (v_isShared_687_ == 0)
{
v___x_689_ = v___x_686_;
goto v_reusejp_688_;
}
else
{
lean_object* v_reuseFailAlloc_690_; 
v_reuseFailAlloc_690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_690_, 0, v_a_684_);
v___x_689_ = v_reuseFailAlloc_690_;
goto v_reusejp_688_;
}
v_reusejp_688_:
{
return v___x_689_;
}
}
}
}
else
{
lean_object* v_a_692_; lean_object* v___x_694_; uint8_t v_isShared_695_; uint8_t v_isSharedCheck_699_; 
lean_dec_ref(v___y_663_);
lean_dec_ref(v___y_662_);
lean_dec(v___y_660_);
lean_dec(v___y_654_);
lean_dec(v___y_653_);
lean_dec_ref(v_subgoals_570_);
lean_dec(v_minorIdx_566_);
lean_dec(v_pos_565_);
lean_dec(v_baseSubst_562_);
lean_dec_ref(v_major_560_);
lean_dec(v_mvarId_556_);
v_a_692_ = lean_ctor_get(v___x_666_, 0);
v_isSharedCheck_699_ = !lean_is_exclusive(v___x_666_);
if (v_isSharedCheck_699_ == 0)
{
v___x_694_ = v___x_666_;
v_isShared_695_ = v_isSharedCheck_699_;
goto v_resetjp_693_;
}
else
{
lean_inc(v_a_692_);
lean_dec(v___x_666_);
v___x_694_ = lean_box(0);
v_isShared_695_ = v_isSharedCheck_699_;
goto v_resetjp_693_;
}
v_resetjp_693_:
{
lean_object* v___x_697_; 
if (v_isShared_695_ == 0)
{
v___x_697_ = v___x_694_;
goto v_reusejp_696_;
}
else
{
lean_object* v_reuseFailAlloc_698_; 
v_reuseFailAlloc_698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_698_, 0, v_a_692_);
v___x_697_ = v_reuseFailAlloc_698_;
goto v_reusejp_696_;
}
v_reusejp_696_:
{
return v___x_697_;
}
}
}
}
v___jp_700_:
{
lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; 
v___x_715_ = l_Lean_Expr_mvarId_x21(v___y_701_);
lean_dec_ref(v___y_701_);
v___x_716_ = l_Lean_Expr_fvarId_x21(v_major_560_);
v___x_717_ = l_Lean_MVarId_tryClear(v___x_715_, v___x_716_, v___y_711_, v___y_712_, v___y_713_, v___y_714_);
if (lean_obj_tag(v___x_717_) == 0)
{
uint8_t v_explicit_718_; 
v_explicit_718_ = lean_ctor_get_uint8(v___y_710_, sizeof(void*)*1);
if (v_explicit_718_ == 0)
{
lean_object* v_a_719_; lean_object* v_varNames_720_; 
v_a_719_ = lean_ctor_get(v___x_717_, 0);
lean_inc(v_a_719_);
lean_dec_ref_known(v___x_717_, 1);
v_varNames_720_ = lean_ctor_get(v___y_710_, 0);
lean_inc(v_varNames_720_);
lean_dec_ref(v___y_710_);
v___y_651_ = v___y_703_;
v___y_652_ = v___y_704_;
v___y_653_ = v___y_706_;
v___y_654_ = v___y_709_;
v___y_655_ = v___y_713_;
v___y_656_ = v___y_711_;
v___y_657_ = v___y_714_;
v___y_658_ = v___y_702_;
v___y_659_ = v___y_712_;
v___y_660_ = v___y_705_;
v___y_661_ = v_varNames_720_;
v___y_662_ = v___y_707_;
v___y_663_ = v___y_708_;
v___y_664_ = v_a_719_;
v___y_665_ = v___x_649_;
goto v___jp_650_;
}
else
{
lean_object* v_a_721_; lean_object* v_varNames_722_; 
v_a_721_ = lean_ctor_get(v___x_717_, 0);
lean_inc(v_a_721_);
lean_dec_ref_known(v___x_717_, 1);
v_varNames_722_ = lean_ctor_get(v___y_710_, 0);
lean_inc(v_varNames_722_);
lean_dec_ref(v___y_710_);
v___y_651_ = v___y_703_;
v___y_652_ = v___y_704_;
v___y_653_ = v___y_706_;
v___y_654_ = v___y_709_;
v___y_655_ = v___y_713_;
v___y_656_ = v___y_711_;
v___y_657_ = v___y_714_;
v___y_658_ = v___y_702_;
v___y_659_ = v___y_712_;
v___y_660_ = v___y_705_;
v___y_661_ = v_varNames_722_;
v___y_662_ = v___y_707_;
v___y_663_ = v___y_708_;
v___y_664_ = v_a_721_;
v___y_665_ = v___y_703_;
goto v___jp_650_;
}
}
else
{
lean_object* v_a_723_; lean_object* v___x_725_; uint8_t v_isShared_726_; uint8_t v_isSharedCheck_730_; 
lean_dec_ref(v___y_710_);
lean_dec(v___y_709_);
lean_dec_ref(v___y_708_);
lean_dec_ref(v___y_707_);
lean_dec(v___y_706_);
lean_dec(v___y_705_);
lean_dec(v___y_702_);
lean_dec_ref(v_subgoals_570_);
lean_dec(v_minorIdx_566_);
lean_dec(v_pos_565_);
lean_dec(v_baseSubst_562_);
lean_dec_ref(v_major_560_);
lean_dec(v_mvarId_556_);
v_a_723_ = lean_ctor_get(v___x_717_, 0);
v_isSharedCheck_730_ = !lean_is_exclusive(v___x_717_);
if (v_isSharedCheck_730_ == 0)
{
v___x_725_ = v___x_717_;
v_isShared_726_ = v_isSharedCheck_730_;
goto v_resetjp_724_;
}
else
{
lean_inc(v_a_723_);
lean_dec(v___x_717_);
v___x_725_ = lean_box(0);
v_isShared_726_ = v_isSharedCheck_730_;
goto v_resetjp_724_;
}
v_resetjp_724_:
{
lean_object* v___x_728_; 
if (v_isShared_726_ == 0)
{
v___x_728_ = v___x_725_;
goto v_reusejp_727_;
}
else
{
lean_object* v_reuseFailAlloc_729_; 
v_reuseFailAlloc_729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_729_, 0, v_a_723_);
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
v___jp_731_:
{
lean_object* v___x_745_; 
v___x_745_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___y_735_, v___y_732_, v___y_739_, v___y_743_, v___y_740_, v___y_734_);
if (lean_obj_tag(v___x_745_) == 0)
{
lean_object* v_a_746_; lean_object* v___x_747_; lean_object* v___x_748_; 
v_a_746_ = lean_ctor_get(v___x_745_, 0);
lean_inc_n(v_a_746_, 2);
lean_dec_ref_known(v___x_745_, 1);
v___x_747_ = l_Lean_Expr_app___override(v_recursor_567_, v_a_746_);
lean_inc(v_mvarId_556_);
v___x_748_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTypeBody(v_mvarId_556_, v_a_634_, v_a_746_, v___y_739_, v___y_743_, v___y_740_, v___y_734_);
if (lean_obj_tag(v___x_748_) == 0)
{
lean_object* v_toCold_749_; lean_object* v_options_750_; uint8_t v_hasTrace_751_; 
v_toCold_749_ = lean_ctor_get(v___y_740_, 0);
v_options_750_ = lean_ctor_get(v_toCold_749_, 2);
v_hasTrace_751_ = lean_ctor_get_uint8(v_options_750_, sizeof(void*)*1);
if (v_hasTrace_751_ == 0)
{
lean_object* v_a_752_; 
v_a_752_ = lean_ctor_get(v___x_748_, 0);
lean_inc(v_a_752_);
lean_dec_ref_known(v___x_748_, 1);
v___y_701_ = v_a_746_;
v___y_702_ = v___y_741_;
v___y_703_ = v___y_733_;
v___y_704_ = v___y_736_;
v___y_705_ = v___y_742_;
v___y_706_ = v___y_737_;
v___y_707_ = v___x_747_;
v___y_708_ = v_a_752_;
v___y_709_ = v___y_738_;
v___y_710_ = v___y_744_;
v___y_711_ = v___y_739_;
v___y_712_ = v___y_743_;
v___y_713_ = v___y_740_;
v___y_714_ = v___y_734_;
goto v___jp_700_;
}
else
{
lean_object* v_a_753_; lean_object* v_inheritedTraceOptions_754_; lean_object* v___x_755_; lean_object* v___x_756_; uint8_t v___x_757_; 
v_a_753_ = lean_ctor_get(v___x_748_, 0);
lean_inc(v_a_753_);
lean_dec_ref_known(v___x_748_, 1);
v_inheritedTraceOptions_754_ = lean_ctor_get(v_toCold_749_, 11);
v___x_755_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__2));
v___x_756_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5);
v___x_757_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_754_, v_options_750_, v___x_756_);
if (v___x_757_ == 0)
{
v___y_701_ = v_a_746_;
v___y_702_ = v___y_741_;
v___y_703_ = v___y_733_;
v___y_704_ = v___y_736_;
v___y_705_ = v___y_742_;
v___y_706_ = v___y_737_;
v___y_707_ = v___x_747_;
v___y_708_ = v_a_753_;
v___y_709_ = v___y_738_;
v___y_710_ = v___y_744_;
v___y_711_ = v___y_739_;
v___y_712_ = v___y_743_;
v___y_713_ = v___y_740_;
v___y_714_ = v___y_734_;
goto v___jp_700_;
}
else
{
lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; 
v___x_758_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__11, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__11_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__11);
v___x_759_ = l_Lean_Expr_fvarId_x21(v_major_560_);
v___x_760_ = l_Lean_MessageData_ofName(v___x_759_);
v___x_761_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_761_, 0, v___x_758_);
lean_ctor_set(v___x_761_, 1, v___x_760_);
v___x_762_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1(v___x_755_, v___x_761_, v___y_739_, v___y_743_, v___y_740_, v___y_734_);
if (lean_obj_tag(v___x_762_) == 0)
{
lean_dec_ref_known(v___x_762_, 1);
v___y_701_ = v_a_746_;
v___y_702_ = v___y_741_;
v___y_703_ = v___y_733_;
v___y_704_ = v___y_736_;
v___y_705_ = v___y_742_;
v___y_706_ = v___y_737_;
v___y_707_ = v___x_747_;
v___y_708_ = v_a_753_;
v___y_709_ = v___y_738_;
v___y_710_ = v___y_744_;
v___y_711_ = v___y_739_;
v___y_712_ = v___y_743_;
v___y_713_ = v___y_740_;
v___y_714_ = v___y_734_;
goto v___jp_700_;
}
else
{
lean_object* v_a_763_; lean_object* v___x_765_; uint8_t v_isShared_766_; uint8_t v_isSharedCheck_770_; 
lean_dec(v_a_753_);
lean_dec_ref(v___x_747_);
lean_dec(v_a_746_);
lean_dec_ref(v___y_744_);
lean_dec(v___y_742_);
lean_dec(v___y_741_);
lean_dec(v___y_738_);
lean_dec(v___y_737_);
lean_dec_ref(v_subgoals_570_);
lean_dec(v_minorIdx_566_);
lean_dec(v_pos_565_);
lean_dec(v_baseSubst_562_);
lean_dec_ref(v_major_560_);
lean_dec(v_mvarId_556_);
v_a_763_ = lean_ctor_get(v___x_762_, 0);
v_isSharedCheck_770_ = !lean_is_exclusive(v___x_762_);
if (v_isSharedCheck_770_ == 0)
{
v___x_765_ = v___x_762_;
v_isShared_766_ = v_isSharedCheck_770_;
goto v_resetjp_764_;
}
else
{
lean_inc(v_a_763_);
lean_dec(v___x_762_);
v___x_765_ = lean_box(0);
v_isShared_766_ = v_isSharedCheck_770_;
goto v_resetjp_764_;
}
v_resetjp_764_:
{
lean_object* v___x_768_; 
if (v_isShared_766_ == 0)
{
v___x_768_ = v___x_765_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v_a_763_);
v___x_768_ = v_reuseFailAlloc_769_;
goto v_reusejp_767_;
}
v_reusejp_767_:
{
return v___x_768_;
}
}
}
}
}
}
else
{
lean_object* v_a_771_; lean_object* v___x_773_; uint8_t v_isShared_774_; uint8_t v_isSharedCheck_778_; 
lean_dec_ref(v___x_747_);
lean_dec(v_a_746_);
lean_dec_ref(v___y_744_);
lean_dec(v___y_742_);
lean_dec(v___y_741_);
lean_dec(v___y_738_);
lean_dec(v___y_737_);
lean_dec_ref(v_subgoals_570_);
lean_dec(v_minorIdx_566_);
lean_dec(v_pos_565_);
lean_dec(v_baseSubst_562_);
lean_dec_ref(v_major_560_);
lean_dec(v_mvarId_556_);
v_a_771_ = lean_ctor_get(v___x_748_, 0);
v_isSharedCheck_778_ = !lean_is_exclusive(v___x_748_);
if (v_isSharedCheck_778_ == 0)
{
v___x_773_ = v___x_748_;
v_isShared_774_ = v_isSharedCheck_778_;
goto v_resetjp_772_;
}
else
{
lean_inc(v_a_771_);
lean_dec(v___x_748_);
v___x_773_ = lean_box(0);
v_isShared_774_ = v_isSharedCheck_778_;
goto v_resetjp_772_;
}
v_resetjp_772_:
{
lean_object* v___x_776_; 
if (v_isShared_774_ == 0)
{
v___x_776_ = v___x_773_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v_a_771_);
v___x_776_ = v_reuseFailAlloc_777_;
goto v_reusejp_775_;
}
v_reusejp_775_:
{
return v___x_776_;
}
}
}
}
else
{
lean_object* v_a_779_; lean_object* v___x_781_; uint8_t v_isShared_782_; uint8_t v_isSharedCheck_786_; 
lean_dec_ref(v___y_744_);
lean_dec(v___y_742_);
lean_dec(v___y_741_);
lean_dec(v___y_738_);
lean_dec(v___y_737_);
lean_dec(v_a_634_);
lean_dec_ref(v_subgoals_570_);
lean_dec_ref(v_recursor_567_);
lean_dec(v_minorIdx_566_);
lean_dec(v_pos_565_);
lean_dec(v_baseSubst_562_);
lean_dec_ref(v_major_560_);
lean_dec(v_mvarId_556_);
v_a_779_ = lean_ctor_get(v___x_745_, 0);
v_isSharedCheck_786_ = !lean_is_exclusive(v___x_745_);
if (v_isSharedCheck_786_ == 0)
{
v___x_781_ = v___x_745_;
v_isShared_782_ = v_isSharedCheck_786_;
goto v_resetjp_780_;
}
else
{
lean_inc(v_a_779_);
lean_dec(v___x_745_);
v___x_781_ = lean_box(0);
v_isShared_782_ = v_isSharedCheck_786_;
goto v_resetjp_780_;
}
v_resetjp_780_:
{
lean_object* v___x_784_; 
if (v_isShared_782_ == 0)
{
v___x_784_ = v___x_781_;
goto v_reusejp_783_;
}
else
{
lean_object* v_reuseFailAlloc_785_; 
v_reuseFailAlloc_785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_785_, 0, v_a_779_);
v___x_784_ = v_reuseFailAlloc_785_;
goto v_reusejp_783_;
}
v_reusejp_783_:
{
return v___x_784_;
}
}
}
}
v___jp_787_:
{
lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; uint8_t v___x_803_; 
v___x_797_ = lean_nat_sub(v___y_789_, v_initialArity_563_);
lean_dec(v___y_789_);
v___x_798_ = lean_array_get_size(v_reverted_559_);
v___x_799_ = lean_array_get_size(v_indices_561_);
v___x_800_ = lean_nat_sub(v___x_798_, v___x_799_);
v___x_801_ = lean_nat_sub(v___x_800_, v___y_792_);
lean_dec(v___x_800_);
v___x_802_ = lean_array_get_size(v_givenNames_557_);
v___x_803_ = lean_nat_dec_lt(v_minorIdx_566_, v___x_802_);
if (v___x_803_ == 0)
{
lean_object* v___x_804_; lean_object* v___x_805_; 
v___x_804_ = lean_box(0);
v___x_805_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_805_, 0, v___x_804_);
lean_ctor_set_uint8(v___x_805_, sizeof(void*)*1, v___x_803_);
v___y_732_ = v___y_788_;
v___y_733_ = v___y_790_;
v___y_734_ = v___y_796_;
v___y_735_ = v___y_791_;
v___y_736_ = v___y_792_;
v___y_737_ = v___x_799_;
v___y_738_ = v___x_801_;
v___y_739_ = v___y_793_;
v___y_740_ = v___y_795_;
v___y_741_ = v___x_797_;
v___y_742_ = v___x_798_;
v___y_743_ = v___y_794_;
v___y_744_ = v___x_805_;
goto v___jp_731_;
}
else
{
lean_object* v___x_806_; 
v___x_806_ = lean_array_fget_borrowed(v_givenNames_557_, v_minorIdx_566_);
lean_inc(v___x_806_);
v___y_732_ = v___y_788_;
v___y_733_ = v___y_790_;
v___y_734_ = v___y_796_;
v___y_735_ = v___y_791_;
v___y_736_ = v___y_792_;
v___y_737_ = v___x_799_;
v___y_738_ = v___x_801_;
v___y_739_ = v___y_793_;
v___y_740_ = v___y_795_;
v___y_741_ = v___x_797_;
v___y_742_ = v___x_798_;
v___y_743_ = v___y_794_;
v___y_744_ = v___x_806_;
goto v___jp_731_;
}
}
v___jp_807_:
{
lean_object* v___x_816_; uint8_t v___x_817_; 
lean_inc_ref(v___y_813_);
v___x_816_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTargetArity(v___y_813_);
v___x_817_ = lean_nat_dec_lt(v___x_816_, v_initialArity_563_);
if (v___x_817_ == 0)
{
v___y_788_ = v___y_808_;
v___y_789_ = v___x_816_;
v___y_790_ = v___y_815_;
v___y_791_ = v___y_813_;
v___y_792_ = v___y_812_;
v___y_793_ = v___y_810_;
v___y_794_ = v___y_811_;
v___y_795_ = v___y_809_;
v___y_796_ = v___y_814_;
goto v___jp_787_;
}
else
{
lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; 
v___x_818_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1));
v___x_819_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9);
lean_inc(v_mvarId_556_);
v___x_820_ = l_Lean_Meta_throwTacticEx___redArg(v___x_818_, v_mvarId_556_, v___x_819_, v___y_810_, v___y_811_, v___y_809_, v___y_814_);
if (lean_obj_tag(v___x_820_) == 0)
{
lean_dec_ref_known(v___x_820_, 1);
v___y_788_ = v___y_808_;
v___y_789_ = v___x_816_;
v___y_790_ = v___y_815_;
v___y_791_ = v___y_813_;
v___y_792_ = v___y_812_;
v___y_793_ = v___y_810_;
v___y_794_ = v___y_811_;
v___y_795_ = v___y_809_;
v___y_796_ = v___y_814_;
goto v___jp_787_;
}
else
{
lean_object* v_a_821_; lean_object* v___x_823_; uint8_t v_isShared_824_; uint8_t v_isSharedCheck_828_; 
lean_dec(v___x_816_);
lean_dec_ref(v___y_813_);
lean_dec(v___y_808_);
lean_dec(v_a_634_);
lean_dec_ref(v_subgoals_570_);
lean_dec_ref(v_recursor_567_);
lean_dec(v_minorIdx_566_);
lean_dec(v_pos_565_);
lean_dec(v_baseSubst_562_);
lean_dec_ref(v_major_560_);
lean_dec(v_mvarId_556_);
v_a_821_ = lean_ctor_get(v___x_820_, 0);
v_isSharedCheck_828_ = !lean_is_exclusive(v___x_820_);
if (v_isSharedCheck_828_ == 0)
{
v___x_823_ = v___x_820_;
v_isShared_824_ = v_isSharedCheck_828_;
goto v_resetjp_822_;
}
else
{
lean_inc(v_a_821_);
lean_dec(v___x_820_);
v___x_823_ = lean_box(0);
v_isShared_824_ = v_isSharedCheck_828_;
goto v_resetjp_822_;
}
v_resetjp_822_:
{
lean_object* v___x_826_; 
if (v_isShared_824_ == 0)
{
v___x_826_ = v___x_823_;
goto v_reusejp_825_;
}
else
{
lean_object* v_reuseFailAlloc_827_; 
v_reuseFailAlloc_827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_827_, 0, v_a_821_);
v___x_826_ = v_reuseFailAlloc_827_;
goto v_reusejp_825_;
}
v_reusejp_825_:
{
return v___x_826_;
}
}
}
}
}
v___jp_829_:
{
uint8_t v___x_838_; 
v___x_838_ = l_Lean_BinderInfo_isInstImplicit(v___y_830_);
if (v___x_838_ == 0)
{
v___y_808_ = v___y_837_;
v___y_809_ = v___y_832_;
v___y_810_ = v___y_831_;
v___y_811_ = v___y_835_;
v___y_812_ = v___y_834_;
v___y_813_ = v___y_833_;
v___y_814_ = v___y_836_;
v___y_815_ = v___x_838_;
goto v___jp_807_;
}
else
{
lean_object* v___x_839_; lean_object* v___x_840_; uint8_t v___x_841_; 
v___x_839_ = lean_array_get_size(v_givenNames_557_);
v___x_840_ = lean_unsigned_to_nat(0u);
v___x_841_ = lean_nat_dec_eq(v___x_839_, v___x_840_);
if (v___x_841_ == 0)
{
v___y_808_ = v___y_837_;
v___y_809_ = v___y_832_;
v___y_810_ = v___y_831_;
v___y_811_ = v___y_835_;
v___y_812_ = v___y_834_;
v___y_813_ = v___y_833_;
v___y_814_ = v___y_836_;
v___y_815_ = v___x_841_;
goto v___jp_807_;
}
else
{
lean_object* v___x_842_; lean_object* v___x_843_; 
v___x_842_ = lean_box(0);
lean_inc_ref(v___y_833_);
v___x_843_ = l_Lean_Meta_synthInstance_x3f(v___y_833_, v___x_842_, v___y_831_, v___y_835_, v___y_832_, v___y_836_);
if (lean_obj_tag(v___x_843_) == 0)
{
lean_object* v_a_844_; 
v_a_844_ = lean_ctor_get(v___x_843_, 0);
lean_inc(v_a_844_);
lean_dec_ref_known(v___x_843_, 1);
if (lean_obj_tag(v_a_844_) == 0)
{
lean_object* v___x_845_; 
v___x_845_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___y_833_, v___y_837_, v___y_831_, v___y_835_, v___y_832_, v___y_836_);
if (lean_obj_tag(v___x_845_) == 0)
{
lean_object* v_a_846_; lean_object* v___x_847_; lean_object* v___x_848_; 
v_a_846_ = lean_ctor_get(v___x_845_, 0);
lean_inc_n(v_a_846_, 2);
lean_dec_ref_known(v___x_845_, 1);
v___x_847_ = l_Lean_Expr_app___override(v_recursor_567_, v_a_846_);
lean_inc(v_mvarId_556_);
v___x_848_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTypeBody(v_mvarId_556_, v_a_634_, v_a_846_, v___y_831_, v___y_835_, v___y_832_, v___y_836_);
if (lean_obj_tag(v___x_848_) == 0)
{
lean_object* v_a_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; 
v_a_849_ = lean_ctor_get(v___x_848_, 0);
lean_inc(v_a_849_);
lean_dec_ref_known(v___x_848_, 1);
v___x_850_ = lean_nat_add(v_pos_565_, v___y_834_);
lean_dec(v_pos_565_);
v___x_851_ = lean_nat_add(v_minorIdx_566_, v___y_834_);
lean_dec(v_minorIdx_566_);
v___x_852_ = l_Lean_Expr_mvarId_x21(v_a_846_);
lean_dec(v_a_846_);
v___x_853_ = ((lean_object*)(l_Lean_Meta_instInhabitedInductionSubgoal_default___closed__0));
v___x_854_ = lean_box(0);
v___x_855_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_855_, 0, v___x_852_);
lean_ctor_set(v___x_855_, 1, v___x_853_);
lean_ctor_set(v___x_855_, 2, v___x_854_);
v___x_856_ = lean_array_push(v_subgoals_570_, v___x_855_);
v_pos_565_ = v___x_850_;
v_minorIdx_566_ = v___x_851_;
v_recursor_567_ = v___x_847_;
v_recursorType_568_ = v_a_849_;
v_subgoals_570_ = v___x_856_;
v_a_571_ = v___y_831_;
v_a_572_ = v___y_835_;
v_a_573_ = v___y_832_;
v_a_574_ = v___y_836_;
goto _start;
}
else
{
lean_object* v_a_858_; lean_object* v___x_860_; uint8_t v_isShared_861_; uint8_t v_isSharedCheck_865_; 
lean_dec_ref(v___x_847_);
lean_dec(v_a_846_);
lean_dec_ref(v_subgoals_570_);
lean_dec(v_minorIdx_566_);
lean_dec(v_pos_565_);
lean_dec(v_baseSubst_562_);
lean_dec_ref(v_major_560_);
lean_dec(v_mvarId_556_);
v_a_858_ = lean_ctor_get(v___x_848_, 0);
v_isSharedCheck_865_ = !lean_is_exclusive(v___x_848_);
if (v_isSharedCheck_865_ == 0)
{
v___x_860_ = v___x_848_;
v_isShared_861_ = v_isSharedCheck_865_;
goto v_resetjp_859_;
}
else
{
lean_inc(v_a_858_);
lean_dec(v___x_848_);
v___x_860_ = lean_box(0);
v_isShared_861_ = v_isSharedCheck_865_;
goto v_resetjp_859_;
}
v_resetjp_859_:
{
lean_object* v___x_863_; 
if (v_isShared_861_ == 0)
{
v___x_863_ = v___x_860_;
goto v_reusejp_862_;
}
else
{
lean_object* v_reuseFailAlloc_864_; 
v_reuseFailAlloc_864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_864_, 0, v_a_858_);
v___x_863_ = v_reuseFailAlloc_864_;
goto v_reusejp_862_;
}
v_reusejp_862_:
{
return v___x_863_;
}
}
}
}
else
{
lean_object* v_a_866_; lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_873_; 
lean_dec(v_a_634_);
lean_dec_ref(v_subgoals_570_);
lean_dec_ref(v_recursor_567_);
lean_dec(v_minorIdx_566_);
lean_dec(v_pos_565_);
lean_dec(v_baseSubst_562_);
lean_dec_ref(v_major_560_);
lean_dec(v_mvarId_556_);
v_a_866_ = lean_ctor_get(v___x_845_, 0);
v_isSharedCheck_873_ = !lean_is_exclusive(v___x_845_);
if (v_isSharedCheck_873_ == 0)
{
v___x_868_ = v___x_845_;
v_isShared_869_ = v_isSharedCheck_873_;
goto v_resetjp_867_;
}
else
{
lean_inc(v_a_866_);
lean_dec(v___x_845_);
v___x_868_ = lean_box(0);
v_isShared_869_ = v_isSharedCheck_873_;
goto v_resetjp_867_;
}
v_resetjp_867_:
{
lean_object* v___x_871_; 
if (v_isShared_869_ == 0)
{
v___x_871_ = v___x_868_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v_a_866_);
v___x_871_ = v_reuseFailAlloc_872_;
goto v_reusejp_870_;
}
v_reusejp_870_:
{
return v___x_871_;
}
}
}
}
else
{
lean_object* v_val_874_; lean_object* v___x_875_; lean_object* v___x_876_; 
lean_dec(v___y_837_);
lean_dec_ref(v___y_833_);
v_val_874_ = lean_ctor_get(v_a_844_, 0);
lean_inc_n(v_val_874_, 2);
lean_dec_ref_known(v_a_844_, 1);
v___x_875_ = l_Lean_Expr_app___override(v_recursor_567_, v_val_874_);
lean_inc(v_mvarId_556_);
v___x_876_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTypeBody(v_mvarId_556_, v_a_634_, v_val_874_, v___y_831_, v___y_835_, v___y_832_, v___y_836_);
lean_dec(v_val_874_);
if (lean_obj_tag(v___x_876_) == 0)
{
lean_object* v_a_877_; lean_object* v___x_878_; lean_object* v___x_879_; 
v_a_877_ = lean_ctor_get(v___x_876_, 0);
lean_inc(v_a_877_);
lean_dec_ref_known(v___x_876_, 1);
v___x_878_ = lean_nat_add(v_pos_565_, v___y_834_);
lean_dec(v_pos_565_);
v___x_879_ = lean_nat_add(v_minorIdx_566_, v___y_834_);
lean_dec(v_minorIdx_566_);
v_pos_565_ = v___x_878_;
v_minorIdx_566_ = v___x_879_;
v_recursor_567_ = v___x_875_;
v_recursorType_568_ = v_a_877_;
v_a_571_ = v___y_831_;
v_a_572_ = v___y_835_;
v_a_573_ = v___y_832_;
v_a_574_ = v___y_836_;
goto _start;
}
else
{
lean_object* v_a_881_; lean_object* v___x_883_; uint8_t v_isShared_884_; uint8_t v_isSharedCheck_888_; 
lean_dec_ref(v___x_875_);
lean_dec_ref(v_subgoals_570_);
lean_dec(v_minorIdx_566_);
lean_dec(v_pos_565_);
lean_dec(v_baseSubst_562_);
lean_dec_ref(v_major_560_);
lean_dec(v_mvarId_556_);
v_a_881_ = lean_ctor_get(v___x_876_, 0);
v_isSharedCheck_888_ = !lean_is_exclusive(v___x_876_);
if (v_isSharedCheck_888_ == 0)
{
v___x_883_ = v___x_876_;
v_isShared_884_ = v_isSharedCheck_888_;
goto v_resetjp_882_;
}
else
{
lean_inc(v_a_881_);
lean_dec(v___x_876_);
v___x_883_ = lean_box(0);
v_isShared_884_ = v_isSharedCheck_888_;
goto v_resetjp_882_;
}
v_resetjp_882_:
{
lean_object* v___x_886_; 
if (v_isShared_884_ == 0)
{
v___x_886_ = v___x_883_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v_a_881_);
v___x_886_ = v_reuseFailAlloc_887_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
return v___x_886_;
}
}
}
}
}
else
{
lean_object* v_a_889_; lean_object* v___x_891_; uint8_t v_isShared_892_; uint8_t v_isSharedCheck_896_; 
lean_dec(v___y_837_);
lean_dec_ref(v___y_833_);
lean_dec(v_a_634_);
lean_dec_ref(v_subgoals_570_);
lean_dec_ref(v_recursor_567_);
lean_dec(v_minorIdx_566_);
lean_dec(v_pos_565_);
lean_dec(v_baseSubst_562_);
lean_dec_ref(v_major_560_);
lean_dec(v_mvarId_556_);
v_a_889_ = lean_ctor_get(v___x_843_, 0);
v_isSharedCheck_896_ = !lean_is_exclusive(v___x_843_);
if (v_isSharedCheck_896_ == 0)
{
v___x_891_ = v___x_843_;
v_isShared_892_ = v_isSharedCheck_896_;
goto v_resetjp_890_;
}
else
{
lean_inc(v_a_889_);
lean_dec(v___x_843_);
v___x_891_ = lean_box(0);
v_isShared_892_ = v_isSharedCheck_896_;
goto v_resetjp_890_;
}
v_resetjp_890_:
{
lean_object* v___x_894_; 
if (v_isShared_892_ == 0)
{
v___x_894_ = v___x_891_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_895_; 
v_reuseFailAlloc_895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_895_, 0, v_a_889_);
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
}
}
}
v___jp_635_:
{
if (v_consumedMajor_569_ == 0)
{
lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; 
v___x_636_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1));
v___x_637_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9);
lean_inc(v_mvarId_556_);
v___x_638_ = l_Lean_Meta_throwTacticEx___redArg(v___x_636_, v_mvarId_556_, v___x_637_, v_a_571_, v_a_572_, v_a_573_, v_a_574_);
if (lean_obj_tag(v___x_638_) == 0)
{
lean_dec_ref_known(v___x_638_, 1);
v___y_577_ = v_a_571_;
v___y_578_ = v_a_572_;
v___y_579_ = v_a_573_;
v___y_580_ = v_a_574_;
goto v___jp_576_;
}
else
{
lean_object* v_a_639_; lean_object* v___x_641_; uint8_t v_isShared_642_; uint8_t v_isSharedCheck_646_; 
lean_dec_ref(v_subgoals_570_);
lean_dec_ref(v_recursor_567_);
lean_dec(v_mvarId_556_);
v_a_639_ = lean_ctor_get(v___x_638_, 0);
v_isSharedCheck_646_ = !lean_is_exclusive(v___x_638_);
if (v_isSharedCheck_646_ == 0)
{
v___x_641_ = v___x_638_;
v_isShared_642_ = v_isSharedCheck_646_;
goto v_resetjp_640_;
}
else
{
lean_inc(v_a_639_);
lean_dec(v___x_638_);
v___x_641_ = lean_box(0);
v_isShared_642_ = v_isSharedCheck_646_;
goto v_resetjp_640_;
}
v_resetjp_640_:
{
lean_object* v___x_644_; 
if (v_isShared_642_ == 0)
{
v___x_644_ = v___x_641_;
goto v_reusejp_643_;
}
else
{
lean_object* v_reuseFailAlloc_645_; 
v_reuseFailAlloc_645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_645_, 0, v_a_639_);
v___x_644_ = v_reuseFailAlloc_645_;
goto v_reusejp_643_;
}
v_reusejp_643_:
{
return v___x_644_;
}
}
}
}
else
{
v___y_577_ = v_a_571_;
v___y_578_ = v_a_572_;
v___y_579_ = v_a_573_;
v___y_580_ = v_a_574_;
goto v___jp_576_;
}
}
}
else
{
lean_object* v_a_972_; lean_object* v___x_974_; uint8_t v_isShared_975_; uint8_t v_isSharedCheck_979_; 
lean_dec_ref(v_subgoals_570_);
lean_dec_ref(v_recursor_567_);
lean_dec(v_minorIdx_566_);
lean_dec(v_pos_565_);
lean_dec(v_baseSubst_562_);
lean_dec_ref(v_major_560_);
lean_dec(v_mvarId_556_);
v_a_972_ = lean_ctor_get(v___x_633_, 0);
v_isSharedCheck_979_ = !lean_is_exclusive(v___x_633_);
if (v_isSharedCheck_979_ == 0)
{
v___x_974_ = v___x_633_;
v_isShared_975_ = v_isSharedCheck_979_;
goto v_resetjp_973_;
}
else
{
lean_inc(v_a_972_);
lean_dec(v___x_633_);
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
v___jp_576_:
{
lean_object* v___x_581_; 
v___x_581_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0___redArg(v_mvarId_556_, v_recursor_567_, v___y_578_);
if (lean_obj_tag(v___x_581_) == 0)
{
lean_object* v___x_583_; uint8_t v_isShared_584_; uint8_t v_isSharedCheck_623_; 
v_isSharedCheck_623_ = !lean_is_exclusive(v___x_581_);
if (v_isSharedCheck_623_ == 0)
{
lean_object* v_unused_624_; 
v_unused_624_ = lean_ctor_get(v___x_581_, 0);
lean_dec(v_unused_624_);
v___x_583_ = v___x_581_;
v_isShared_584_ = v_isSharedCheck_623_;
goto v_resetjp_582_;
}
else
{
lean_dec(v___x_581_);
v___x_583_ = lean_box(0);
v_isShared_584_ = v_isSharedCheck_623_;
goto v_resetjp_582_;
}
v_resetjp_582_:
{
lean_object* v_toCold_585_; lean_object* v_options_586_; uint8_t v_hasTrace_587_; 
v_toCold_585_ = lean_ctor_get(v___y_579_, 0);
v_options_586_ = lean_ctor_get(v_toCold_585_, 2);
v_hasTrace_587_ = lean_ctor_get_uint8(v_options_586_, sizeof(void*)*1);
if (v_hasTrace_587_ == 0)
{
lean_object* v___x_589_; 
if (v_isShared_584_ == 0)
{
lean_ctor_set(v___x_583_, 0, v_subgoals_570_);
v___x_589_ = v___x_583_;
goto v_reusejp_588_;
}
else
{
lean_object* v_reuseFailAlloc_590_; 
v_reuseFailAlloc_590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_590_, 0, v_subgoals_570_);
v___x_589_ = v_reuseFailAlloc_590_;
goto v_reusejp_588_;
}
v_reusejp_588_:
{
return v___x_589_;
}
}
else
{
lean_object* v_inheritedTraceOptions_591_; lean_object* v___x_592_; lean_object* v___x_593_; uint8_t v___x_594_; 
v_inheritedTraceOptions_591_ = lean_ctor_get(v_toCold_585_, 11);
v___x_592_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__2));
v___x_593_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5);
v___x_594_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_591_, v_options_586_, v___x_593_);
if (v___x_594_ == 0)
{
lean_object* v___x_596_; 
if (v_isShared_584_ == 0)
{
lean_ctor_set(v___x_583_, 0, v_subgoals_570_);
v___x_596_ = v___x_583_;
goto v_reusejp_595_;
}
else
{
lean_object* v_reuseFailAlloc_597_; 
v_reuseFailAlloc_597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_597_, 0, v_subgoals_570_);
v___x_596_ = v_reuseFailAlloc_597_;
goto v_reusejp_595_;
}
v_reusejp_595_:
{
return v___x_596_;
}
}
else
{
lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; 
lean_del_object(v___x_583_);
v___x_598_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__7, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__7_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__7);
v___x_599_ = lean_array_get_size(v_subgoals_570_);
v___x_600_ = l_Nat_reprFast(v___x_599_);
v___x_601_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_601_, 0, v___x_600_);
v___x_602_ = l_Lean_MessageData_ofFormat(v___x_601_);
v___x_603_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_603_, 0, v___x_598_);
lean_ctor_set(v___x_603_, 1, v___x_602_);
v___x_604_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__9, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__9_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__9);
v___x_605_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_605_, 0, v___x_603_);
lean_ctor_set(v___x_605_, 1, v___x_604_);
v___x_606_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1(v___x_592_, v___x_605_, v___y_577_, v___y_578_, v___y_579_, v___y_580_);
if (lean_obj_tag(v___x_606_) == 0)
{
lean_object* v___x_608_; uint8_t v_isShared_609_; uint8_t v_isSharedCheck_613_; 
v_isSharedCheck_613_ = !lean_is_exclusive(v___x_606_);
if (v_isSharedCheck_613_ == 0)
{
lean_object* v_unused_614_; 
v_unused_614_ = lean_ctor_get(v___x_606_, 0);
lean_dec(v_unused_614_);
v___x_608_ = v___x_606_;
v_isShared_609_ = v_isSharedCheck_613_;
goto v_resetjp_607_;
}
else
{
lean_dec(v___x_606_);
v___x_608_ = lean_box(0);
v_isShared_609_ = v_isSharedCheck_613_;
goto v_resetjp_607_;
}
v_resetjp_607_:
{
lean_object* v___x_611_; 
if (v_isShared_609_ == 0)
{
lean_ctor_set(v___x_608_, 0, v_subgoals_570_);
v___x_611_ = v___x_608_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v_subgoals_570_);
v___x_611_ = v_reuseFailAlloc_612_;
goto v_reusejp_610_;
}
v_reusejp_610_:
{
return v___x_611_;
}
}
}
else
{
lean_object* v_a_615_; lean_object* v___x_617_; uint8_t v_isShared_618_; uint8_t v_isSharedCheck_622_; 
lean_dec_ref(v_subgoals_570_);
v_a_615_ = lean_ctor_get(v___x_606_, 0);
v_isSharedCheck_622_ = !lean_is_exclusive(v___x_606_);
if (v_isSharedCheck_622_ == 0)
{
v___x_617_ = v___x_606_;
v_isShared_618_ = v_isSharedCheck_622_;
goto v_resetjp_616_;
}
else
{
lean_inc(v_a_615_);
lean_dec(v___x_606_);
v___x_617_ = lean_box(0);
v_isShared_618_ = v_isSharedCheck_622_;
goto v_resetjp_616_;
}
v_resetjp_616_:
{
lean_object* v___x_620_; 
if (v_isShared_618_ == 0)
{
v___x_620_ = v___x_617_;
goto v_reusejp_619_;
}
else
{
lean_object* v_reuseFailAlloc_621_; 
v_reuseFailAlloc_621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_621_, 0, v_a_615_);
v___x_620_ = v_reuseFailAlloc_621_;
goto v_reusejp_619_;
}
v_reusejp_619_:
{
return v___x_620_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_625_; lean_object* v___x_627_; uint8_t v_isShared_628_; uint8_t v_isSharedCheck_632_; 
lean_dec_ref(v_subgoals_570_);
v_a_625_ = lean_ctor_get(v___x_581_, 0);
v_isSharedCheck_632_ = !lean_is_exclusive(v___x_581_);
if (v_isSharedCheck_632_ == 0)
{
v___x_627_ = v___x_581_;
v_isShared_628_ = v_isSharedCheck_632_;
goto v_resetjp_626_;
}
else
{
lean_inc(v_a_625_);
lean_dec(v___x_581_);
v___x_627_ = lean_box(0);
v_isShared_628_ = v_isSharedCheck_632_;
goto v_resetjp_626_;
}
v_resetjp_626_:
{
lean_object* v___x_630_; 
if (v_isShared_628_ == 0)
{
v___x_630_ = v___x_627_;
goto v_reusejp_629_;
}
else
{
lean_object* v_reuseFailAlloc_631_; 
v_reuseFailAlloc_631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_631_, 0, v_a_625_);
v___x_630_ = v_reuseFailAlloc_631_;
goto v_reusejp_629_;
}
v_reusejp_629_:
{
return v___x_630_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___boxed(lean_object** _args){
lean_object* v_mvarId_980_ = _args[0];
lean_object* v_givenNames_981_ = _args[1];
lean_object* v_recursorInfo_982_ = _args[2];
lean_object* v_reverted_983_ = _args[3];
lean_object* v_major_984_ = _args[4];
lean_object* v_indices_985_ = _args[5];
lean_object* v_baseSubst_986_ = _args[6];
lean_object* v_initialArity_987_ = _args[7];
lean_object* v_numMinors_988_ = _args[8];
lean_object* v_pos_989_ = _args[9];
lean_object* v_minorIdx_990_ = _args[10];
lean_object* v_recursor_991_ = _args[11];
lean_object* v_recursorType_992_ = _args[12];
lean_object* v_consumedMajor_993_ = _args[13];
lean_object* v_subgoals_994_ = _args[14];
lean_object* v_a_995_ = _args[15];
lean_object* v_a_996_ = _args[16];
lean_object* v_a_997_ = _args[17];
lean_object* v_a_998_ = _args[18];
lean_object* v_a_999_ = _args[19];
_start:
{
uint8_t v_consumedMajor_boxed_1000_; lean_object* v_res_1001_; 
v_consumedMajor_boxed_1000_ = lean_unbox(v_consumedMajor_993_);
v_res_1001_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop(v_mvarId_980_, v_givenNames_981_, v_recursorInfo_982_, v_reverted_983_, v_major_984_, v_indices_985_, v_baseSubst_986_, v_initialArity_987_, v_numMinors_988_, v_pos_989_, v_minorIdx_990_, v_recursor_991_, v_recursorType_992_, v_consumedMajor_boxed_1000_, v_subgoals_994_, v_a_995_, v_a_996_, v_a_997_, v_a_998_);
lean_dec(v_a_998_);
lean_dec_ref(v_a_997_);
lean_dec(v_a_996_);
lean_dec_ref(v_a_995_);
lean_dec(v_numMinors_988_);
lean_dec(v_initialArity_987_);
lean_dec_ref(v_indices_985_);
lean_dec_ref(v_reverted_983_);
lean_dec_ref(v_recursorInfo_982_);
lean_dec_ref(v_givenNames_981_);
return v_res_1001_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0(lean_object* v_mvarId_1002_, lean_object* v_val_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_){
_start:
{
lean_object* v___x_1009_; 
v___x_1009_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0___redArg(v_mvarId_1002_, v_val_1003_, v___y_1005_);
return v___x_1009_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0___boxed(lean_object* v_mvarId_1010_, lean_object* v_val_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_){
_start:
{
lean_object* v_res_1017_; 
v_res_1017_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0(v_mvarId_1010_, v_val_1011_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_);
lean_dec(v___y_1015_);
lean_dec_ref(v___y_1014_);
lean_dec(v___y_1013_);
lean_dec_ref(v___y_1012_);
return v_res_1017_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__2(lean_object* v___x_1018_, lean_object* v_reverted_1019_, lean_object* v_fst_1020_, lean_object* v_n_1021_, lean_object* v_j_1022_, lean_object* v_a_1023_, lean_object* v_a_1024_){
_start:
{
lean_object* v___x_1025_; 
v___x_1025_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__2___redArg(v___x_1018_, v_reverted_1019_, v_fst_1020_, v_n_1021_, v_j_1022_, v_a_1024_);
return v___x_1025_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__2___boxed(lean_object* v___x_1026_, lean_object* v_reverted_1027_, lean_object* v_fst_1028_, lean_object* v_n_1029_, lean_object* v_j_1030_, lean_object* v_a_1031_, lean_object* v_a_1032_){
_start:
{
lean_object* v_res_1033_; 
v_res_1033_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__2(v___x_1026_, v_reverted_1027_, v_fst_1028_, v_n_1029_, v_j_1030_, v_a_1031_, v_a_1032_);
lean_dec(v_n_1029_);
lean_dec_ref(v_fst_1028_);
lean_dec_ref(v_reverted_1027_);
lean_dec(v___x_1026_);
return v_res_1033_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0(lean_object* v_00_u03b2_1034_, lean_object* v_x_1035_, lean_object* v_x_1036_, lean_object* v_x_1037_){
_start:
{
lean_object* v___x_1038_; 
v___x_1038_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0___redArg(v_x_1035_, v_x_1036_, v_x_1037_);
return v___x_1038_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1039_, lean_object* v_x_1040_, size_t v_x_1041_, size_t v_x_1042_, lean_object* v_x_1043_, lean_object* v_x_1044_){
_start:
{
lean_object* v___x_1045_; 
v___x_1045_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2___redArg(v_x_1040_, v_x_1041_, v_x_1042_, v_x_1043_, v_x_1044_);
return v___x_1045_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1046_, lean_object* v_x_1047_, lean_object* v_x_1048_, lean_object* v_x_1049_, lean_object* v_x_1050_, lean_object* v_x_1051_){
_start:
{
size_t v_x_9566__boxed_1052_; size_t v_x_9567__boxed_1053_; lean_object* v_res_1054_; 
v_x_9566__boxed_1052_ = lean_unbox_usize(v_x_1048_);
lean_dec(v_x_1048_);
v_x_9567__boxed_1053_ = lean_unbox_usize(v_x_1049_);
lean_dec(v_x_1049_);
v_res_1054_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2(v_00_u03b2_1046_, v_x_1047_, v_x_9566__boxed_1052_, v_x_9567__boxed_1053_, v_x_1050_, v_x_1051_);
return v_res_1054_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__8(lean_object* v_00_u03b2_1055_, lean_object* v_n_1056_, lean_object* v_k_1057_, lean_object* v_v_1058_){
_start:
{
lean_object* v___x_1059_; 
v___x_1059_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__8___redArg(v_n_1056_, v_k_1057_, v_v_1058_);
return v___x_1059_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__9(lean_object* v_00_u03b2_1060_, size_t v_depth_1061_, lean_object* v_keys_1062_, lean_object* v_vals_1063_, lean_object* v_heq_1064_, lean_object* v_i_1065_, lean_object* v_entries_1066_){
_start:
{
lean_object* v___x_1067_; 
v___x_1067_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__9___redArg(v_depth_1061_, v_keys_1062_, v_vals_1063_, v_i_1065_, v_entries_1066_);
return v___x_1067_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__9___boxed(lean_object* v_00_u03b2_1068_, lean_object* v_depth_1069_, lean_object* v_keys_1070_, lean_object* v_vals_1071_, lean_object* v_heq_1072_, lean_object* v_i_1073_, lean_object* v_entries_1074_){
_start:
{
size_t v_depth_boxed_1075_; lean_object* v_res_1076_; 
v_depth_boxed_1075_ = lean_unbox_usize(v_depth_1069_);
lean_dec(v_depth_1069_);
v_res_1076_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__9(v_00_u03b2_1068_, v_depth_boxed_1075_, v_keys_1070_, v_vals_1071_, v_heq_1072_, v_i_1073_, v_entries_1074_);
lean_dec_ref(v_vals_1071_);
lean_dec_ref(v_keys_1070_);
return v_res_1076_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__8_spec__9(lean_object* v_00_u03b2_1077_, lean_object* v_x_1078_, lean_object* v_x_1079_, lean_object* v_x_1080_, lean_object* v_x_1081_){
_start:
{
lean_object* v___x_1082_; 
v___x_1082_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__8_spec__9___redArg(v_x_1078_, v_x_1079_, v_x_1080_, v_x_1081_);
return v___x_1082_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize(lean_object* v_mvarId_1085_, lean_object* v_givenNames_1086_, lean_object* v_recursorInfo_1087_, lean_object* v_reverted_1088_, lean_object* v_major_1089_, lean_object* v_indices_1090_, lean_object* v_baseSubst_1091_, lean_object* v_recursor_1092_, lean_object* v_a_1093_, lean_object* v_a_1094_, lean_object* v_a_1095_, lean_object* v_a_1096_){
_start:
{
lean_object* v___x_1098_; 
lean_inc(v_mvarId_1085_);
v___x_1098_ = l_Lean_MVarId_getType(v_mvarId_1085_, v_a_1093_, v_a_1094_, v_a_1095_, v_a_1096_);
if (lean_obj_tag(v___x_1098_) == 0)
{
lean_object* v_a_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; 
v_a_1099_ = lean_ctor_get(v___x_1098_, 0);
lean_inc(v_a_1099_);
lean_dec_ref_known(v___x_1098_, 1);
v___x_1100_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTargetArity(v_a_1099_);
lean_inc(v_a_1096_);
lean_inc_ref(v_a_1095_);
lean_inc(v_a_1094_);
lean_inc_ref(v_a_1093_);
lean_inc_ref(v_recursor_1092_);
v___x_1101_ = lean_infer_type(v_recursor_1092_, v_a_1093_, v_a_1094_, v_a_1095_, v_a_1096_);
if (lean_obj_tag(v___x_1101_) == 0)
{
lean_object* v_a_1102_; lean_object* v_paramsPos_1103_; lean_object* v_produceMotive_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; uint8_t v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; 
v_a_1102_ = lean_ctor_get(v___x_1101_, 0);
lean_inc(v_a_1102_);
lean_dec_ref_known(v___x_1101_, 1);
v_paramsPos_1103_ = lean_ctor_get(v_recursorInfo_1087_, 5);
v_produceMotive_1104_ = lean_ctor_get(v_recursorInfo_1087_, 7);
v___x_1105_ = l_List_lengthTR___redArg(v_produceMotive_1104_);
v___x_1106_ = l_List_lengthTR___redArg(v_paramsPos_1103_);
v___x_1107_ = lean_unsigned_to_nat(1u);
v___x_1108_ = lean_nat_add(v___x_1106_, v___x_1107_);
lean_dec(v___x_1106_);
v___x_1109_ = lean_unsigned_to_nat(0u);
v___x_1110_ = 0;
v___x_1111_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize___closed__0));
v___x_1112_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop(v_mvarId_1085_, v_givenNames_1086_, v_recursorInfo_1087_, v_reverted_1088_, v_major_1089_, v_indices_1090_, v_baseSubst_1091_, v___x_1100_, v___x_1105_, v___x_1108_, v___x_1109_, v_recursor_1092_, v_a_1102_, v___x_1110_, v___x_1111_, v_a_1093_, v_a_1094_, v_a_1095_, v_a_1096_);
lean_dec(v___x_1105_);
lean_dec(v___x_1100_);
return v___x_1112_;
}
else
{
lean_object* v_a_1113_; lean_object* v___x_1115_; uint8_t v_isShared_1116_; uint8_t v_isSharedCheck_1120_; 
lean_dec(v___x_1100_);
lean_dec_ref(v_recursor_1092_);
lean_dec(v_baseSubst_1091_);
lean_dec_ref(v_major_1089_);
lean_dec(v_mvarId_1085_);
v_a_1113_ = lean_ctor_get(v___x_1101_, 0);
v_isSharedCheck_1120_ = !lean_is_exclusive(v___x_1101_);
if (v_isSharedCheck_1120_ == 0)
{
v___x_1115_ = v___x_1101_;
v_isShared_1116_ = v_isSharedCheck_1120_;
goto v_resetjp_1114_;
}
else
{
lean_inc(v_a_1113_);
lean_dec(v___x_1101_);
v___x_1115_ = lean_box(0);
v_isShared_1116_ = v_isSharedCheck_1120_;
goto v_resetjp_1114_;
}
v_resetjp_1114_:
{
lean_object* v___x_1118_; 
if (v_isShared_1116_ == 0)
{
v___x_1118_ = v___x_1115_;
goto v_reusejp_1117_;
}
else
{
lean_object* v_reuseFailAlloc_1119_; 
v_reuseFailAlloc_1119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1119_, 0, v_a_1113_);
v___x_1118_ = v_reuseFailAlloc_1119_;
goto v_reusejp_1117_;
}
v_reusejp_1117_:
{
return v___x_1118_;
}
}
}
}
else
{
lean_object* v_a_1121_; lean_object* v___x_1123_; uint8_t v_isShared_1124_; uint8_t v_isSharedCheck_1128_; 
lean_dec_ref(v_recursor_1092_);
lean_dec(v_baseSubst_1091_);
lean_dec_ref(v_major_1089_);
lean_dec(v_mvarId_1085_);
v_a_1121_ = lean_ctor_get(v___x_1098_, 0);
v_isSharedCheck_1128_ = !lean_is_exclusive(v___x_1098_);
if (v_isSharedCheck_1128_ == 0)
{
v___x_1123_ = v___x_1098_;
v_isShared_1124_ = v_isSharedCheck_1128_;
goto v_resetjp_1122_;
}
else
{
lean_inc(v_a_1121_);
lean_dec(v___x_1098_);
v___x_1123_ = lean_box(0);
v_isShared_1124_ = v_isSharedCheck_1128_;
goto v_resetjp_1122_;
}
v_resetjp_1122_:
{
lean_object* v___x_1126_; 
if (v_isShared_1124_ == 0)
{
v___x_1126_ = v___x_1123_;
goto v_reusejp_1125_;
}
else
{
lean_object* v_reuseFailAlloc_1127_; 
v_reuseFailAlloc_1127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1127_, 0, v_a_1121_);
v___x_1126_ = v_reuseFailAlloc_1127_;
goto v_reusejp_1125_;
}
v_reusejp_1125_:
{
return v___x_1126_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize___boxed(lean_object* v_mvarId_1129_, lean_object* v_givenNames_1130_, lean_object* v_recursorInfo_1131_, lean_object* v_reverted_1132_, lean_object* v_major_1133_, lean_object* v_indices_1134_, lean_object* v_baseSubst_1135_, lean_object* v_recursor_1136_, lean_object* v_a_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_, lean_object* v_a_1141_){
_start:
{
lean_object* v_res_1142_; 
v_res_1142_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize(v_mvarId_1129_, v_givenNames_1130_, v_recursorInfo_1131_, v_reverted_1132_, v_major_1133_, v_indices_1134_, v_baseSubst_1135_, v_recursor_1136_, v_a_1137_, v_a_1138_, v_a_1139_, v_a_1140_);
lean_dec(v_a_1140_);
lean_dec_ref(v_a_1139_);
lean_dec(v_a_1138_);
lean_dec_ref(v_a_1137_);
lean_dec_ref(v_indices_1134_);
lean_dec_ref(v_reverted_1132_);
lean_dec_ref(v_recursorInfo_1131_);
lean_dec_ref(v_givenNames_1130_);
return v_res_1142_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg___closed__1(void){
_start:
{
lean_object* v___x_1144_; lean_object* v___x_1145_; 
v___x_1144_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg___closed__0));
v___x_1145_ = l_Lean_stringToMessageData(v___x_1144_);
return v___x_1145_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg(lean_object* v_tacticName_1146_, lean_object* v_mvarId_1147_, lean_object* v_majorType_1148_, lean_object* v_a_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_){
_start:
{
lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; 
v___x_1154_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg___closed__1, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg___closed__1);
v___x_1155_ = l_Lean_indentExpr(v_majorType_1148_);
v___x_1156_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1156_, 0, v___x_1154_);
lean_ctor_set(v___x_1156_, 1, v___x_1155_);
v___x_1157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1157_, 0, v___x_1156_);
v___x_1158_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1146_, v_mvarId_1147_, v___x_1157_, v_a_1149_, v_a_1150_, v_a_1151_, v_a_1152_);
return v___x_1158_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg___boxed(lean_object* v_tacticName_1159_, lean_object* v_mvarId_1160_, lean_object* v_majorType_1161_, lean_object* v_a_1162_, lean_object* v_a_1163_, lean_object* v_a_1164_, lean_object* v_a_1165_, lean_object* v_a_1166_){
_start:
{
lean_object* v_res_1167_; 
v_res_1167_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg(v_tacticName_1159_, v_mvarId_1160_, v_majorType_1161_, v_a_1162_, v_a_1163_, v_a_1164_, v_a_1165_);
lean_dec(v_a_1165_);
lean_dec_ref(v_a_1164_);
lean_dec(v_a_1163_);
lean_dec_ref(v_a_1162_);
return v_res_1167_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType(lean_object* v_00_u03b1_1168_, lean_object* v_tacticName_1169_, lean_object* v_mvarId_1170_, lean_object* v_majorType_1171_, lean_object* v_a_1172_, lean_object* v_a_1173_, lean_object* v_a_1174_, lean_object* v_a_1175_){
_start:
{
lean_object* v___x_1177_; 
v___x_1177_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg(v_tacticName_1169_, v_mvarId_1170_, v_majorType_1171_, v_a_1172_, v_a_1173_, v_a_1174_, v_a_1175_);
return v___x_1177_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___boxed(lean_object* v_00_u03b1_1178_, lean_object* v_tacticName_1179_, lean_object* v_mvarId_1180_, lean_object* v_majorType_1181_, lean_object* v_a_1182_, lean_object* v_a_1183_, lean_object* v_a_1184_, lean_object* v_a_1185_, lean_object* v_a_1186_){
_start:
{
lean_object* v_res_1187_; 
v_res_1187_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType(v_00_u03b1_1178_, v_tacticName_1179_, v_mvarId_1180_, v_majorType_1181_, v_a_1182_, v_a_1183_, v_a_1184_, v_a_1185_);
lean_dec(v_a_1185_);
lean_dec_ref(v_a_1184_);
lean_dec(v_a_1183_);
lean_dec_ref(v_a_1182_);
return v_res_1187_;
}
}
LEAN_EXPORT uint8_t l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___lam__0(lean_object* v_fvarId_1188_, lean_object* v_x_1189_){
_start:
{
uint8_t v___x_1190_; 
v___x_1190_ = l_Lean_instBEqFVarId_beq(v_fvarId_1188_, v_x_1189_);
return v___x_1190_;
}
}
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___lam__0___boxed(lean_object* v_fvarId_1191_, lean_object* v_x_1192_){
_start:
{
uint8_t v_res_1193_; lean_object* v_r_1194_; 
v_res_1193_ = l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___lam__0(v_fvarId_1191_, v_x_1192_);
lean_dec(v_x_1192_);
lean_dec(v_fvarId_1191_);
v_r_1194_ = lean_box(v_res_1193_);
return v_r_1194_;
}
}
LEAN_EXPORT uint8_t l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___lam__1(lean_object* v_x_1195_){
_start:
{
uint8_t v___x_1196_; 
v___x_1196_ = 0;
return v___x_1196_;
}
}
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___lam__1___boxed(lean_object* v_x_1197_){
_start:
{
uint8_t v_res_1198_; lean_object* v_r_1199_; 
v_res_1198_ = l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___lam__1(v_x_1197_);
lean_dec(v_x_1197_);
v_r_1199_ = lean_box(v_res_1198_);
return v_r_1199_;
}
}
static lean_object* _init_l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; 
v___x_1201_ = lean_box(0);
v___x_1202_ = lean_unsigned_to_nat(16u);
v___x_1203_ = lean_mk_array(v___x_1202_, v___x_1201_);
return v___x_1203_;
}
}
static lean_object* _init_l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; 
v___x_1204_ = lean_obj_once(&l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__1, &l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__1_once, _init_l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__1);
v___x_1205_ = lean_unsigned_to_nat(0u);
v___x_1206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1206_, 0, v___x_1205_);
lean_ctor_set(v___x_1206_, 1, v___x_1204_);
return v___x_1206_;
}
}
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg(lean_object* v_localDecl_1207_, lean_object* v_fvarId_1208_, uint8_t v_generalizeNondepLet_1209_, lean_object* v___y_1210_){
_start:
{
uint8_t v_fst_1213_; lean_object* v_snd_1214_; lean_object* v___y_1233_; lean_object* v___f_1237_; lean_object* v___f_1238_; 
v___f_1237_ = lean_alloc_closure((void*)(l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1237_, 0, v_fvarId_1208_);
v___f_1238_ = ((lean_object*)(l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__0));
if (lean_obj_tag(v_localDecl_1207_) == 0)
{
lean_object* v_type_1239_; lean_object* v___x_1240_; uint8_t v_fst_1242_; lean_object* v_mctx_1243_; lean_object* v___y_1261_; lean_object* v_mctx_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; uint8_t v___x_1269_; 
v_type_1239_ = lean_ctor_get(v_localDecl_1207_, 3);
lean_inc_ref(v_type_1239_);
lean_dec_ref_known(v_localDecl_1207_, 4);
v___x_1240_ = lean_st_ref_get(v___y_1210_);
v_mctx_1266_ = lean_ctor_get(v___x_1240_, 0);
lean_inc_ref_n(v_mctx_1266_, 2);
lean_dec(v___x_1240_);
v___x_1267_ = lean_obj_once(&l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__2, &l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__2_once, _init_l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__2);
v___x_1268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1268_, 0, v___x_1267_);
lean_ctor_set(v___x_1268_, 1, v_mctx_1266_);
v___x_1269_ = l_Lean_Expr_hasFVar(v_type_1239_);
if (v___x_1269_ == 0)
{
uint8_t v___x_1270_; 
v___x_1270_ = l_Lean_Expr_hasMVar(v_type_1239_);
if (v___x_1270_ == 0)
{
lean_dec_ref_known(v___x_1268_, 2);
lean_dec_ref(v_type_1239_);
lean_dec_ref(v___f_1237_);
v_fst_1242_ = v___x_1270_;
v_mctx_1243_ = v_mctx_1266_;
goto v___jp_1241_;
}
else
{
lean_object* v___x_1271_; 
lean_dec_ref(v_mctx_1266_);
v___x_1271_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1237_, v___f_1238_, v_type_1239_, v___x_1268_);
v___y_1261_ = v___x_1271_;
goto v___jp_1260_;
}
}
else
{
lean_object* v___x_1272_; 
lean_dec_ref(v_mctx_1266_);
v___x_1272_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1237_, v___f_1238_, v_type_1239_, v___x_1268_);
v___y_1261_ = v___x_1272_;
goto v___jp_1260_;
}
v___jp_1241_:
{
lean_object* v___x_1244_; lean_object* v_cache_1245_; lean_object* v_zetaDeltaFVarIds_1246_; lean_object* v_postponed_1247_; lean_object* v_diag_1248_; lean_object* v___x_1250_; uint8_t v_isShared_1251_; uint8_t v_isSharedCheck_1258_; 
v___x_1244_ = lean_st_ref_take(v___y_1210_);
v_cache_1245_ = lean_ctor_get(v___x_1244_, 1);
v_zetaDeltaFVarIds_1246_ = lean_ctor_get(v___x_1244_, 2);
v_postponed_1247_ = lean_ctor_get(v___x_1244_, 3);
v_diag_1248_ = lean_ctor_get(v___x_1244_, 4);
v_isSharedCheck_1258_ = !lean_is_exclusive(v___x_1244_);
if (v_isSharedCheck_1258_ == 0)
{
lean_object* v_unused_1259_; 
v_unused_1259_ = lean_ctor_get(v___x_1244_, 0);
lean_dec(v_unused_1259_);
v___x_1250_ = v___x_1244_;
v_isShared_1251_ = v_isSharedCheck_1258_;
goto v_resetjp_1249_;
}
else
{
lean_inc(v_diag_1248_);
lean_inc(v_postponed_1247_);
lean_inc(v_zetaDeltaFVarIds_1246_);
lean_inc(v_cache_1245_);
lean_dec(v___x_1244_);
v___x_1250_ = lean_box(0);
v_isShared_1251_ = v_isSharedCheck_1258_;
goto v_resetjp_1249_;
}
v_resetjp_1249_:
{
lean_object* v___x_1253_; 
if (v_isShared_1251_ == 0)
{
lean_ctor_set(v___x_1250_, 0, v_mctx_1243_);
v___x_1253_ = v___x_1250_;
goto v_reusejp_1252_;
}
else
{
lean_object* v_reuseFailAlloc_1257_; 
v_reuseFailAlloc_1257_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1257_, 0, v_mctx_1243_);
lean_ctor_set(v_reuseFailAlloc_1257_, 1, v_cache_1245_);
lean_ctor_set(v_reuseFailAlloc_1257_, 2, v_zetaDeltaFVarIds_1246_);
lean_ctor_set(v_reuseFailAlloc_1257_, 3, v_postponed_1247_);
lean_ctor_set(v_reuseFailAlloc_1257_, 4, v_diag_1248_);
v___x_1253_ = v_reuseFailAlloc_1257_;
goto v_reusejp_1252_;
}
v_reusejp_1252_:
{
lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; 
v___x_1254_ = lean_st_ref_put(v___y_1210_, v___x_1253_);
v___x_1255_ = lean_box(v_fst_1242_);
v___x_1256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1256_, 0, v___x_1255_);
return v___x_1256_;
}
}
}
v___jp_1260_:
{
lean_object* v_snd_1262_; lean_object* v_fst_1263_; lean_object* v_mctx_1264_; uint8_t v___x_1265_; 
v_snd_1262_ = lean_ctor_get(v___y_1261_, 1);
lean_inc(v_snd_1262_);
v_fst_1263_ = lean_ctor_get(v___y_1261_, 0);
lean_inc(v_fst_1263_);
lean_dec_ref(v___y_1261_);
v_mctx_1264_ = lean_ctor_get(v_snd_1262_, 1);
lean_inc_ref(v_mctx_1264_);
lean_dec(v_snd_1262_);
v___x_1265_ = lean_unbox(v_fst_1263_);
lean_dec(v_fst_1263_);
v_fst_1242_ = v___x_1265_;
v_mctx_1243_ = v_mctx_1264_;
goto v___jp_1241_;
}
}
else
{
lean_object* v_type_1273_; lean_object* v_value_1274_; uint8_t v_nondep_1275_; lean_object* v_snd_1277_; lean_object* v___y_1283_; 
v_type_1273_ = lean_ctor_get(v_localDecl_1207_, 3);
lean_inc_ref(v_type_1273_);
v_value_1274_ = lean_ctor_get(v_localDecl_1207_, 4);
lean_inc_ref(v_value_1274_);
v_nondep_1275_ = lean_ctor_get_uint8(v_localDecl_1207_, sizeof(void*)*5);
lean_dec_ref_known(v_localDecl_1207_, 5);
if (v_generalizeNondepLet_1209_ == 0)
{
goto v___jp_1289_;
}
else
{
if (v_nondep_1275_ == 0)
{
goto v___jp_1289_;
}
else
{
lean_object* v___x_1298_; uint8_t v_fst_1300_; lean_object* v_mctx_1301_; lean_object* v___y_1319_; lean_object* v_mctx_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; uint8_t v___x_1327_; 
lean_dec_ref(v_value_1274_);
v___x_1298_ = lean_st_ref_get(v___y_1210_);
v_mctx_1324_ = lean_ctor_get(v___x_1298_, 0);
lean_inc_ref_n(v_mctx_1324_, 2);
lean_dec(v___x_1298_);
v___x_1325_ = lean_obj_once(&l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__2, &l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__2_once, _init_l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__2);
v___x_1326_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1326_, 0, v___x_1325_);
lean_ctor_set(v___x_1326_, 1, v_mctx_1324_);
v___x_1327_ = l_Lean_Expr_hasFVar(v_type_1273_);
if (v___x_1327_ == 0)
{
uint8_t v___x_1328_; 
v___x_1328_ = l_Lean_Expr_hasMVar(v_type_1273_);
if (v___x_1328_ == 0)
{
lean_dec_ref_known(v___x_1326_, 2);
lean_dec_ref(v_type_1273_);
lean_dec_ref(v___f_1237_);
v_fst_1300_ = v___x_1328_;
v_mctx_1301_ = v_mctx_1324_;
goto v___jp_1299_;
}
else
{
lean_object* v___x_1329_; 
lean_dec_ref(v_mctx_1324_);
v___x_1329_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1237_, v___f_1238_, v_type_1273_, v___x_1326_);
v___y_1319_ = v___x_1329_;
goto v___jp_1318_;
}
}
else
{
lean_object* v___x_1330_; 
lean_dec_ref(v_mctx_1324_);
v___x_1330_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1237_, v___f_1238_, v_type_1273_, v___x_1326_);
v___y_1319_ = v___x_1330_;
goto v___jp_1318_;
}
v___jp_1299_:
{
lean_object* v___x_1302_; lean_object* v_cache_1303_; lean_object* v_zetaDeltaFVarIds_1304_; lean_object* v_postponed_1305_; lean_object* v_diag_1306_; lean_object* v___x_1308_; uint8_t v_isShared_1309_; uint8_t v_isSharedCheck_1316_; 
v___x_1302_ = lean_st_ref_take(v___y_1210_);
v_cache_1303_ = lean_ctor_get(v___x_1302_, 1);
v_zetaDeltaFVarIds_1304_ = lean_ctor_get(v___x_1302_, 2);
v_postponed_1305_ = lean_ctor_get(v___x_1302_, 3);
v_diag_1306_ = lean_ctor_get(v___x_1302_, 4);
v_isSharedCheck_1316_ = !lean_is_exclusive(v___x_1302_);
if (v_isSharedCheck_1316_ == 0)
{
lean_object* v_unused_1317_; 
v_unused_1317_ = lean_ctor_get(v___x_1302_, 0);
lean_dec(v_unused_1317_);
v___x_1308_ = v___x_1302_;
v_isShared_1309_ = v_isSharedCheck_1316_;
goto v_resetjp_1307_;
}
else
{
lean_inc(v_diag_1306_);
lean_inc(v_postponed_1305_);
lean_inc(v_zetaDeltaFVarIds_1304_);
lean_inc(v_cache_1303_);
lean_dec(v___x_1302_);
v___x_1308_ = lean_box(0);
v_isShared_1309_ = v_isSharedCheck_1316_;
goto v_resetjp_1307_;
}
v_resetjp_1307_:
{
lean_object* v___x_1311_; 
if (v_isShared_1309_ == 0)
{
lean_ctor_set(v___x_1308_, 0, v_mctx_1301_);
v___x_1311_ = v___x_1308_;
goto v_reusejp_1310_;
}
else
{
lean_object* v_reuseFailAlloc_1315_; 
v_reuseFailAlloc_1315_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1315_, 0, v_mctx_1301_);
lean_ctor_set(v_reuseFailAlloc_1315_, 1, v_cache_1303_);
lean_ctor_set(v_reuseFailAlloc_1315_, 2, v_zetaDeltaFVarIds_1304_);
lean_ctor_set(v_reuseFailAlloc_1315_, 3, v_postponed_1305_);
lean_ctor_set(v_reuseFailAlloc_1315_, 4, v_diag_1306_);
v___x_1311_ = v_reuseFailAlloc_1315_;
goto v_reusejp_1310_;
}
v_reusejp_1310_:
{
lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; 
v___x_1312_ = lean_st_ref_put(v___y_1210_, v___x_1311_);
v___x_1313_ = lean_box(v_fst_1300_);
v___x_1314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1314_, 0, v___x_1313_);
return v___x_1314_;
}
}
}
v___jp_1318_:
{
lean_object* v_snd_1320_; lean_object* v_fst_1321_; lean_object* v_mctx_1322_; uint8_t v___x_1323_; 
v_snd_1320_ = lean_ctor_get(v___y_1319_, 1);
lean_inc(v_snd_1320_);
v_fst_1321_ = lean_ctor_get(v___y_1319_, 0);
lean_inc(v_fst_1321_);
lean_dec_ref(v___y_1319_);
v_mctx_1322_ = lean_ctor_get(v_snd_1320_, 1);
lean_inc_ref(v_mctx_1322_);
lean_dec(v_snd_1320_);
v___x_1323_ = lean_unbox(v_fst_1321_);
lean_dec(v_fst_1321_);
v_fst_1300_ = v___x_1323_;
v_mctx_1301_ = v_mctx_1322_;
goto v___jp_1299_;
}
}
}
v___jp_1276_:
{
uint8_t v___x_1278_; 
v___x_1278_ = l_Lean_Expr_hasFVar(v_value_1274_);
if (v___x_1278_ == 0)
{
uint8_t v___x_1279_; 
v___x_1279_ = l_Lean_Expr_hasMVar(v_value_1274_);
if (v___x_1279_ == 0)
{
lean_dec_ref(v_value_1274_);
lean_dec_ref(v___f_1237_);
v_fst_1213_ = v___x_1279_;
v_snd_1214_ = v_snd_1277_;
goto v___jp_1212_;
}
else
{
lean_object* v___x_1280_; 
v___x_1280_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1237_, v___f_1238_, v_value_1274_, v_snd_1277_);
v___y_1233_ = v___x_1280_;
goto v___jp_1232_;
}
}
else
{
lean_object* v___x_1281_; 
v___x_1281_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1237_, v___f_1238_, v_value_1274_, v_snd_1277_);
v___y_1233_ = v___x_1281_;
goto v___jp_1232_;
}
}
v___jp_1282_:
{
lean_object* v_fst_1284_; uint8_t v___x_1285_; 
v_fst_1284_ = lean_ctor_get(v___y_1283_, 0);
v___x_1285_ = lean_unbox(v_fst_1284_);
if (v___x_1285_ == 0)
{
lean_object* v_snd_1286_; 
v_snd_1286_ = lean_ctor_get(v___y_1283_, 1);
lean_inc(v_snd_1286_);
lean_dec_ref(v___y_1283_);
v_snd_1277_ = v_snd_1286_;
goto v___jp_1276_;
}
else
{
lean_object* v_snd_1287_; uint8_t v___x_1288_; 
lean_inc(v_fst_1284_);
lean_dec_ref(v_value_1274_);
lean_dec_ref(v___f_1237_);
v_snd_1287_ = lean_ctor_get(v___y_1283_, 1);
lean_inc(v_snd_1287_);
lean_dec_ref(v___y_1283_);
v___x_1288_ = lean_unbox(v_fst_1284_);
lean_dec(v_fst_1284_);
v_fst_1213_ = v___x_1288_;
v_snd_1214_ = v_snd_1287_;
goto v___jp_1212_;
}
}
v___jp_1289_:
{
lean_object* v___x_1290_; lean_object* v_mctx_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; uint8_t v___x_1294_; 
v___x_1290_ = lean_st_ref_get(v___y_1210_);
v_mctx_1291_ = lean_ctor_get(v___x_1290_, 0);
lean_inc_ref(v_mctx_1291_);
lean_dec(v___x_1290_);
v___x_1292_ = lean_obj_once(&l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__2, &l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__2_once, _init_l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__2);
v___x_1293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1293_, 0, v___x_1292_);
lean_ctor_set(v___x_1293_, 1, v_mctx_1291_);
v___x_1294_ = l_Lean_Expr_hasFVar(v_type_1273_);
if (v___x_1294_ == 0)
{
uint8_t v___x_1295_; 
v___x_1295_ = l_Lean_Expr_hasMVar(v_type_1273_);
if (v___x_1295_ == 0)
{
lean_dec_ref(v_type_1273_);
v_snd_1277_ = v___x_1293_;
goto v___jp_1276_;
}
else
{
lean_object* v___x_1296_; 
lean_inc_ref(v___f_1237_);
v___x_1296_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1237_, v___f_1238_, v_type_1273_, v___x_1293_);
v___y_1283_ = v___x_1296_;
goto v___jp_1282_;
}
}
else
{
lean_object* v___x_1297_; 
lean_inc_ref(v___f_1237_);
v___x_1297_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1237_, v___f_1238_, v_type_1273_, v___x_1293_);
v___y_1283_ = v___x_1297_;
goto v___jp_1282_;
}
}
}
v___jp_1212_:
{
lean_object* v_mctx_1215_; lean_object* v___x_1216_; lean_object* v_cache_1217_; lean_object* v_zetaDeltaFVarIds_1218_; lean_object* v_postponed_1219_; lean_object* v_diag_1220_; lean_object* v___x_1222_; uint8_t v_isShared_1223_; uint8_t v_isSharedCheck_1230_; 
v_mctx_1215_ = lean_ctor_get(v_snd_1214_, 1);
lean_inc_ref(v_mctx_1215_);
lean_dec_ref(v_snd_1214_);
v___x_1216_ = lean_st_ref_take(v___y_1210_);
v_cache_1217_ = lean_ctor_get(v___x_1216_, 1);
v_zetaDeltaFVarIds_1218_ = lean_ctor_get(v___x_1216_, 2);
v_postponed_1219_ = lean_ctor_get(v___x_1216_, 3);
v_diag_1220_ = lean_ctor_get(v___x_1216_, 4);
v_isSharedCheck_1230_ = !lean_is_exclusive(v___x_1216_);
if (v_isSharedCheck_1230_ == 0)
{
lean_object* v_unused_1231_; 
v_unused_1231_ = lean_ctor_get(v___x_1216_, 0);
lean_dec(v_unused_1231_);
v___x_1222_ = v___x_1216_;
v_isShared_1223_ = v_isSharedCheck_1230_;
goto v_resetjp_1221_;
}
else
{
lean_inc(v_diag_1220_);
lean_inc(v_postponed_1219_);
lean_inc(v_zetaDeltaFVarIds_1218_);
lean_inc(v_cache_1217_);
lean_dec(v___x_1216_);
v___x_1222_ = lean_box(0);
v_isShared_1223_ = v_isSharedCheck_1230_;
goto v_resetjp_1221_;
}
v_resetjp_1221_:
{
lean_object* v___x_1225_; 
if (v_isShared_1223_ == 0)
{
lean_ctor_set(v___x_1222_, 0, v_mctx_1215_);
v___x_1225_ = v___x_1222_;
goto v_reusejp_1224_;
}
else
{
lean_object* v_reuseFailAlloc_1229_; 
v_reuseFailAlloc_1229_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1229_, 0, v_mctx_1215_);
lean_ctor_set(v_reuseFailAlloc_1229_, 1, v_cache_1217_);
lean_ctor_set(v_reuseFailAlloc_1229_, 2, v_zetaDeltaFVarIds_1218_);
lean_ctor_set(v_reuseFailAlloc_1229_, 3, v_postponed_1219_);
lean_ctor_set(v_reuseFailAlloc_1229_, 4, v_diag_1220_);
v___x_1225_ = v_reuseFailAlloc_1229_;
goto v_reusejp_1224_;
}
v_reusejp_1224_:
{
lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; 
v___x_1226_ = lean_st_ref_put(v___y_1210_, v___x_1225_);
v___x_1227_ = lean_box(v_fst_1213_);
v___x_1228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1228_, 0, v___x_1227_);
return v___x_1228_;
}
}
}
v___jp_1232_:
{
lean_object* v_fst_1234_; lean_object* v_snd_1235_; uint8_t v___x_1236_; 
v_fst_1234_ = lean_ctor_get(v___y_1233_, 0);
lean_inc(v_fst_1234_);
v_snd_1235_ = lean_ctor_get(v___y_1233_, 1);
lean_inc(v_snd_1235_);
lean_dec_ref(v___y_1233_);
v___x_1236_ = lean_unbox(v_fst_1234_);
lean_dec(v_fst_1234_);
v_fst_1213_ = v___x_1236_;
v_snd_1214_ = v_snd_1235_;
goto v___jp_1212_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___boxed(lean_object* v_localDecl_1331_, lean_object* v_fvarId_1332_, lean_object* v_generalizeNondepLet_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_){
_start:
{
uint8_t v_generalizeNondepLet_boxed_1336_; lean_object* v_res_1337_; 
v_generalizeNondepLet_boxed_1336_ = lean_unbox(v_generalizeNondepLet_1333_);
v_res_1337_ = l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg(v_localDecl_1331_, v_fvarId_1332_, v_generalizeNondepLet_boxed_1336_, v___y_1334_);
lean_dec(v___y_1334_);
return v_res_1337_;
}
}
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1(lean_object* v_localDecl_1338_, lean_object* v_fvarId_1339_, uint8_t v_generalizeNondepLet_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_){
_start:
{
lean_object* v___x_1346_; 
v___x_1346_ = l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg(v_localDecl_1338_, v_fvarId_1339_, v_generalizeNondepLet_1340_, v___y_1342_);
return v___x_1346_;
}
}
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___boxed(lean_object* v_localDecl_1347_, lean_object* v_fvarId_1348_, lean_object* v_generalizeNondepLet_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_){
_start:
{
uint8_t v_generalizeNondepLet_boxed_1355_; lean_object* v_res_1356_; 
v_generalizeNondepLet_boxed_1355_ = lean_unbox(v_generalizeNondepLet_1349_);
v_res_1356_ = l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1(v_localDecl_1347_, v_fvarId_1348_, v_generalizeNondepLet_boxed_1355_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_);
lean_dec(v___y_1353_);
lean_dec_ref(v___y_1352_);
lean_dec(v___y_1351_);
lean_dec_ref(v___y_1350_);
return v_res_1356_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2___redArg(lean_object* v_e_1357_, lean_object* v_fvarId_1358_, lean_object* v___y_1359_){
_start:
{
lean_object* v___f_1361_; lean_object* v___f_1362_; lean_object* v___x_1363_; uint8_t v_fst_1365_; lean_object* v_mctx_1366_; lean_object* v___y_1384_; lean_object* v_mctx_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; uint8_t v___x_1392_; 
v___f_1361_ = ((lean_object*)(l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__0));
v___f_1362_ = lean_alloc_closure((void*)(l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1362_, 0, v_fvarId_1358_);
v___x_1363_ = lean_st_ref_get(v___y_1359_);
v_mctx_1389_ = lean_ctor_get(v___x_1363_, 0);
lean_inc_ref_n(v_mctx_1389_, 2);
lean_dec(v___x_1363_);
v___x_1390_ = lean_obj_once(&l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__2, &l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__2_once, _init_l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__2);
v___x_1391_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1391_, 0, v___x_1390_);
lean_ctor_set(v___x_1391_, 1, v_mctx_1389_);
v___x_1392_ = l_Lean_Expr_hasFVar(v_e_1357_);
if (v___x_1392_ == 0)
{
uint8_t v___x_1393_; 
v___x_1393_ = l_Lean_Expr_hasMVar(v_e_1357_);
if (v___x_1393_ == 0)
{
lean_dec_ref_known(v___x_1391_, 2);
lean_dec_ref(v___f_1362_);
lean_dec_ref(v_e_1357_);
v_fst_1365_ = v___x_1393_;
v_mctx_1366_ = v_mctx_1389_;
goto v___jp_1364_;
}
else
{
lean_object* v___x_1394_; 
lean_dec_ref(v_mctx_1389_);
v___x_1394_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1362_, v___f_1361_, v_e_1357_, v___x_1391_);
v___y_1384_ = v___x_1394_;
goto v___jp_1383_;
}
}
else
{
lean_object* v___x_1395_; 
lean_dec_ref(v_mctx_1389_);
v___x_1395_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1362_, v___f_1361_, v_e_1357_, v___x_1391_);
v___y_1384_ = v___x_1395_;
goto v___jp_1383_;
}
v___jp_1364_:
{
lean_object* v___x_1367_; lean_object* v_cache_1368_; lean_object* v_zetaDeltaFVarIds_1369_; lean_object* v_postponed_1370_; lean_object* v_diag_1371_; lean_object* v___x_1373_; uint8_t v_isShared_1374_; uint8_t v_isSharedCheck_1381_; 
v___x_1367_ = lean_st_ref_take(v___y_1359_);
v_cache_1368_ = lean_ctor_get(v___x_1367_, 1);
v_zetaDeltaFVarIds_1369_ = lean_ctor_get(v___x_1367_, 2);
v_postponed_1370_ = lean_ctor_get(v___x_1367_, 3);
v_diag_1371_ = lean_ctor_get(v___x_1367_, 4);
v_isSharedCheck_1381_ = !lean_is_exclusive(v___x_1367_);
if (v_isSharedCheck_1381_ == 0)
{
lean_object* v_unused_1382_; 
v_unused_1382_ = lean_ctor_get(v___x_1367_, 0);
lean_dec(v_unused_1382_);
v___x_1373_ = v___x_1367_;
v_isShared_1374_ = v_isSharedCheck_1381_;
goto v_resetjp_1372_;
}
else
{
lean_inc(v_diag_1371_);
lean_inc(v_postponed_1370_);
lean_inc(v_zetaDeltaFVarIds_1369_);
lean_inc(v_cache_1368_);
lean_dec(v___x_1367_);
v___x_1373_ = lean_box(0);
v_isShared_1374_ = v_isSharedCheck_1381_;
goto v_resetjp_1372_;
}
v_resetjp_1372_:
{
lean_object* v___x_1376_; 
if (v_isShared_1374_ == 0)
{
lean_ctor_set(v___x_1373_, 0, v_mctx_1366_);
v___x_1376_ = v___x_1373_;
goto v_reusejp_1375_;
}
else
{
lean_object* v_reuseFailAlloc_1380_; 
v_reuseFailAlloc_1380_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1380_, 0, v_mctx_1366_);
lean_ctor_set(v_reuseFailAlloc_1380_, 1, v_cache_1368_);
lean_ctor_set(v_reuseFailAlloc_1380_, 2, v_zetaDeltaFVarIds_1369_);
lean_ctor_set(v_reuseFailAlloc_1380_, 3, v_postponed_1370_);
lean_ctor_set(v_reuseFailAlloc_1380_, 4, v_diag_1371_);
v___x_1376_ = v_reuseFailAlloc_1380_;
goto v_reusejp_1375_;
}
v_reusejp_1375_:
{
lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; 
v___x_1377_ = lean_st_ref_put(v___y_1359_, v___x_1376_);
v___x_1378_ = lean_box(v_fst_1365_);
v___x_1379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1379_, 0, v___x_1378_);
return v___x_1379_;
}
}
}
v___jp_1383_:
{
lean_object* v_snd_1385_; lean_object* v_fst_1386_; lean_object* v_mctx_1387_; uint8_t v___x_1388_; 
v_snd_1385_ = lean_ctor_get(v___y_1384_, 1);
lean_inc(v_snd_1385_);
v_fst_1386_ = lean_ctor_get(v___y_1384_, 0);
lean_inc(v_fst_1386_);
lean_dec_ref(v___y_1384_);
v_mctx_1387_ = lean_ctor_get(v_snd_1385_, 1);
lean_inc_ref(v_mctx_1387_);
lean_dec(v_snd_1385_);
v___x_1388_ = lean_unbox(v_fst_1386_);
lean_dec(v_fst_1386_);
v_fst_1365_ = v___x_1388_;
v_mctx_1366_ = v_mctx_1387_;
goto v___jp_1364_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2___redArg___boxed(lean_object* v_e_1396_, lean_object* v_fvarId_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_){
_start:
{
lean_object* v_res_1400_; 
v_res_1400_ = l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2___redArg(v_e_1396_, v_fvarId_1397_, v___y_1398_);
lean_dec(v___y_1398_);
return v_res_1400_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2(lean_object* v_e_1401_, lean_object* v_fvarId_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_){
_start:
{
lean_object* v___x_1408_; 
v___x_1408_ = l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2___redArg(v_e_1401_, v_fvarId_1402_, v___y_1404_);
return v___x_1408_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2___boxed(lean_object* v_e_1409_, lean_object* v_fvarId_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_){
_start:
{
lean_object* v_res_1416_; 
v_res_1416_ = l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2(v_e_1409_, v_fvarId_1410_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_);
lean_dec(v___y_1414_);
lean_dec_ref(v___y_1413_);
lean_dec(v___y_1412_);
lean_dec_ref(v___y_1411_);
return v_res_1416_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_Meta_getMajorTypeIndices_spec__0(lean_object* v_a_1417_, lean_object* v_x_1418_){
_start:
{
if (lean_obj_tag(v_x_1418_) == 0)
{
uint8_t v___x_1419_; 
v___x_1419_ = 0;
return v___x_1419_;
}
else
{
lean_object* v_head_1420_; lean_object* v_tail_1421_; uint8_t v___x_1422_; 
v_head_1420_ = lean_ctor_get(v_x_1418_, 0);
v_tail_1421_ = lean_ctor_get(v_x_1418_, 1);
v___x_1422_ = lean_nat_dec_eq(v_a_1417_, v_head_1420_);
if (v___x_1422_ == 0)
{
v_x_1418_ = v_tail_1421_;
goto _start;
}
else
{
return v___x_1422_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_Meta_getMajorTypeIndices_spec__0___boxed(lean_object* v_a_1424_, lean_object* v_x_1425_){
_start:
{
uint8_t v_res_1426_; lean_object* v_r_1427_; 
v_res_1426_ = l_List_elem___at___00Lean_Meta_getMajorTypeIndices_spec__0(v_a_1424_, v_x_1425_);
lean_dec(v_x_1425_);
lean_dec(v_a_1424_);
v_r_1427_ = lean_box(v_res_1426_);
return v_r_1427_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_1429_; lean_object* v___x_1430_; 
v___x_1429_ = ((lean_object*)(l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__0));
v___x_1430_ = l_Lean_stringToMessageData(v___x_1429_);
return v___x_1430_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_1432_; lean_object* v___x_1433_; 
v___x_1432_ = ((lean_object*)(l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__2));
v___x_1433_ = l_Lean_stringToMessageData(v___x_1432_);
return v___x_1433_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__5(void){
_start:
{
lean_object* v___x_1435_; lean_object* v___x_1436_; 
v___x_1435_ = ((lean_object*)(l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__4));
v___x_1436_ = l_Lean_stringToMessageData(v___x_1435_);
return v___x_1436_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__7(void){
_start:
{
lean_object* v___x_1438_; lean_object* v___x_1439_; 
v___x_1438_ = ((lean_object*)(l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__6));
v___x_1439_ = l_Lean_stringToMessageData(v___x_1438_);
return v___x_1439_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg(lean_object* v_majorTypeArgs_1440_, lean_object* v_idxPos_1441_, lean_object* v_recursorInfo_1442_, lean_object* v_idx_1443_, lean_object* v_tacticName_1444_, lean_object* v_mvarId_1445_, lean_object* v_majorType_1446_, lean_object* v_n_1447_, lean_object* v_i_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_){
_start:
{
lean_object* v_zero_1454_; uint8_t v_isZero_1455_; 
v_zero_1454_ = lean_unsigned_to_nat(0u);
v_isZero_1455_ = lean_nat_dec_eq(v_i_1448_, v_zero_1454_);
if (v_isZero_1455_ == 1)
{
lean_object* v___x_1456_; lean_object* v___x_1457_; 
lean_dec(v_i_1448_);
lean_dec_ref(v_majorType_1446_);
lean_dec(v_mvarId_1445_);
lean_dec(v_tacticName_1444_);
lean_dec_ref(v_idx_1443_);
v___x_1456_ = lean_box(0);
v___x_1457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1457_, 0, v___x_1456_);
return v___x_1457_;
}
else
{
lean_object* v_one_1458_; lean_object* v_n_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v_arg_1462_; lean_object* v___y_1464_; lean_object* v___y_1465_; lean_object* v___y_1466_; lean_object* v___y_1467_; lean_object* v___y_1511_; lean_object* v___y_1512_; lean_object* v___y_1513_; lean_object* v___y_1514_; uint8_t v___x_1535_; 
v_one_1458_ = lean_unsigned_to_nat(1u);
v_n_1459_ = lean_nat_sub(v_i_1448_, v_one_1458_);
lean_dec(v_i_1448_);
v___x_1460_ = lean_nat_sub(v_n_1447_, v_n_1459_);
v___x_1461_ = lean_nat_sub(v___x_1460_, v_one_1458_);
lean_dec(v___x_1460_);
v_arg_1462_ = lean_array_fget_borrowed(v_majorTypeArgs_1440_, v___x_1461_);
v___x_1535_ = lean_nat_dec_eq(v___x_1461_, v_idxPos_1441_);
if (v___x_1535_ == 0)
{
uint8_t v___x_1536_; 
v___x_1536_ = lean_expr_eqv(v_arg_1462_, v_idx_1443_);
if (v___x_1536_ == 0)
{
v___y_1511_ = v___y_1449_;
v___y_1512_ = v___y_1450_;
v___y_1513_ = v___y_1451_;
v___y_1514_ = v___y_1452_;
goto v___jp_1510_;
}
else
{
lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; 
v___x_1537_ = lean_obj_once(&l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1, &l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1_once, _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1);
lean_inc_ref(v_idx_1443_);
v___x_1538_ = l_Lean_MessageData_ofExpr(v_idx_1443_);
v___x_1539_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1539_, 0, v___x_1537_);
lean_ctor_set(v___x_1539_, 1, v___x_1538_);
v___x_1540_ = lean_obj_once(&l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__7, &l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__7_once, _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__7);
v___x_1541_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1541_, 0, v___x_1539_);
lean_ctor_set(v___x_1541_, 1, v___x_1540_);
lean_inc_ref(v_majorType_1446_);
v___x_1542_ = l_Lean_indentExpr(v_majorType_1446_);
v___x_1543_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1543_, 0, v___x_1541_);
lean_ctor_set(v___x_1543_, 1, v___x_1542_);
v___x_1544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1544_, 0, v___x_1543_);
lean_inc(v_mvarId_1445_);
lean_inc(v_tacticName_1444_);
v___x_1545_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1444_, v_mvarId_1445_, v___x_1544_, v___y_1449_, v___y_1450_, v___y_1451_, v___y_1452_);
if (lean_obj_tag(v___x_1545_) == 0)
{
lean_dec_ref_known(v___x_1545_, 1);
v___y_1511_ = v___y_1449_;
v___y_1512_ = v___y_1450_;
v___y_1513_ = v___y_1451_;
v___y_1514_ = v___y_1452_;
goto v___jp_1510_;
}
else
{
lean_dec(v___x_1461_);
lean_dec(v_n_1459_);
lean_dec_ref(v_majorType_1446_);
lean_dec(v_mvarId_1445_);
lean_dec(v_tacticName_1444_);
lean_dec_ref(v_idx_1443_);
return v___x_1545_;
}
}
}
else
{
v___y_1511_ = v___y_1449_;
v___y_1512_ = v___y_1450_;
v___y_1513_ = v___y_1451_;
v___y_1514_ = v___y_1452_;
goto v___jp_1510_;
}
v___jp_1463_:
{
uint8_t v___x_1468_; 
v___x_1468_ = lean_nat_dec_lt(v_idxPos_1441_, v___x_1461_);
if (v___x_1468_ == 0)
{
lean_dec(v___x_1461_);
v_i_1448_ = v_n_1459_;
goto _start;
}
else
{
lean_object* v_indicesPos_1470_; uint8_t v___x_1471_; 
v_indicesPos_1470_ = lean_ctor_get(v_recursorInfo_1442_, 6);
v___x_1471_ = l_List_elem___at___00Lean_Meta_getMajorTypeIndices_spec__0(v___x_1461_, v_indicesPos_1470_);
if (v___x_1471_ == 0)
{
lean_dec(v___x_1461_);
v_i_1448_ = v_n_1459_;
goto _start;
}
else
{
uint8_t v___x_1473_; 
v___x_1473_ = l_Lean_Expr_isFVar(v_arg_1462_);
if (v___x_1473_ == 0)
{
lean_dec(v___x_1461_);
v_i_1448_ = v_n_1459_;
goto _start;
}
else
{
lean_object* v___x_1475_; lean_object* v___x_1476_; 
v___x_1475_ = l_Lean_Expr_fvarId_x21(v_idx_1443_);
v___x_1476_ = l_Lean_FVarId_getDecl___redArg(v___x_1475_, v___y_1464_, v___y_1466_, v___y_1467_);
if (lean_obj_tag(v___x_1476_) == 0)
{
lean_object* v_a_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v_a_1480_; lean_object* v___x_1482_; uint8_t v_isShared_1483_; uint8_t v_isSharedCheck_1501_; 
v_a_1477_ = lean_ctor_get(v___x_1476_, 0);
lean_inc(v_a_1477_);
lean_dec_ref_known(v___x_1476_, 1);
v___x_1478_ = l_Lean_Expr_fvarId_x21(v_arg_1462_);
v___x_1479_ = l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg(v_a_1477_, v___x_1478_, v___x_1471_, v___y_1465_);
v_a_1480_ = lean_ctor_get(v___x_1479_, 0);
v_isSharedCheck_1501_ = !lean_is_exclusive(v___x_1479_);
if (v_isSharedCheck_1501_ == 0)
{
v___x_1482_ = v___x_1479_;
v_isShared_1483_ = v_isSharedCheck_1501_;
goto v_resetjp_1481_;
}
else
{
lean_inc(v_a_1480_);
lean_dec(v___x_1479_);
v___x_1482_ = lean_box(0);
v_isShared_1483_ = v_isSharedCheck_1501_;
goto v_resetjp_1481_;
}
v_resetjp_1481_:
{
uint8_t v___x_1484_; 
v___x_1484_ = lean_unbox(v_a_1480_);
lean_dec(v_a_1480_);
if (v___x_1484_ == 0)
{
lean_del_object(v___x_1482_);
lean_dec(v___x_1461_);
v_i_1448_ = v_n_1459_;
goto _start;
}
else
{
lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1494_; 
v___x_1486_ = lean_obj_once(&l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1, &l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1_once, _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1);
lean_inc_ref(v_idx_1443_);
v___x_1487_ = l_Lean_MessageData_ofExpr(v_idx_1443_);
v___x_1488_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1488_, 0, v___x_1486_);
lean_ctor_set(v___x_1488_, 1, v___x_1487_);
v___x_1489_ = lean_obj_once(&l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__3, &l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__3_once, _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__3);
v___x_1490_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1490_, 0, v___x_1488_);
lean_ctor_set(v___x_1490_, 1, v___x_1489_);
v___x_1491_ = lean_nat_add(v___x_1461_, v_one_1458_);
lean_dec(v___x_1461_);
v___x_1492_ = l_Nat_reprFast(v___x_1491_);
if (v_isShared_1483_ == 0)
{
lean_ctor_set_tag(v___x_1482_, 3);
lean_ctor_set(v___x_1482_, 0, v___x_1492_);
v___x_1494_ = v___x_1482_;
goto v_reusejp_1493_;
}
else
{
lean_object* v_reuseFailAlloc_1500_; 
v_reuseFailAlloc_1500_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1500_, 0, v___x_1492_);
v___x_1494_ = v_reuseFailAlloc_1500_;
goto v_reusejp_1493_;
}
v_reusejp_1493_:
{
lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; 
v___x_1495_ = l_Lean_MessageData_ofFormat(v___x_1494_);
v___x_1496_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1496_, 0, v___x_1490_);
lean_ctor_set(v___x_1496_, 1, v___x_1495_);
v___x_1497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1497_, 0, v___x_1496_);
lean_inc(v_mvarId_1445_);
lean_inc(v_tacticName_1444_);
v___x_1498_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1444_, v_mvarId_1445_, v___x_1497_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1467_);
if (lean_obj_tag(v___x_1498_) == 0)
{
lean_dec_ref_known(v___x_1498_, 1);
v_i_1448_ = v_n_1459_;
goto _start;
}
else
{
lean_dec(v_n_1459_);
lean_dec_ref(v_majorType_1446_);
lean_dec(v_mvarId_1445_);
lean_dec(v_tacticName_1444_);
lean_dec_ref(v_idx_1443_);
return v___x_1498_;
}
}
}
}
}
else
{
lean_object* v_a_1502_; lean_object* v___x_1504_; uint8_t v_isShared_1505_; uint8_t v_isSharedCheck_1509_; 
lean_dec(v___x_1461_);
lean_dec(v_n_1459_);
lean_dec_ref(v_majorType_1446_);
lean_dec(v_mvarId_1445_);
lean_dec(v_tacticName_1444_);
lean_dec_ref(v_idx_1443_);
v_a_1502_ = lean_ctor_get(v___x_1476_, 0);
v_isSharedCheck_1509_ = !lean_is_exclusive(v___x_1476_);
if (v_isSharedCheck_1509_ == 0)
{
v___x_1504_ = v___x_1476_;
v_isShared_1505_ = v_isSharedCheck_1509_;
goto v_resetjp_1503_;
}
else
{
lean_inc(v_a_1502_);
lean_dec(v___x_1476_);
v___x_1504_ = lean_box(0);
v_isShared_1505_ = v_isSharedCheck_1509_;
goto v_resetjp_1503_;
}
v_resetjp_1503_:
{
lean_object* v___x_1507_; 
if (v_isShared_1505_ == 0)
{
v___x_1507_ = v___x_1504_;
goto v_reusejp_1506_;
}
else
{
lean_object* v_reuseFailAlloc_1508_; 
v_reuseFailAlloc_1508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1508_, 0, v_a_1502_);
v___x_1507_ = v_reuseFailAlloc_1508_;
goto v_reusejp_1506_;
}
v_reusejp_1506_:
{
return v___x_1507_;
}
}
}
}
}
}
}
v___jp_1510_:
{
uint8_t v___x_1515_; 
v___x_1515_ = lean_nat_dec_lt(v___x_1461_, v_idxPos_1441_);
if (v___x_1515_ == 0)
{
v___y_1464_ = v___y_1511_;
v___y_1465_ = v___y_1512_;
v___y_1466_ = v___y_1513_;
v___y_1467_ = v___y_1514_;
goto v___jp_1463_;
}
else
{
lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v_a_1518_; lean_object* v___x_1520_; uint8_t v_isShared_1521_; uint8_t v_isSharedCheck_1534_; 
v___x_1516_ = l_Lean_Expr_fvarId_x21(v_idx_1443_);
lean_inc(v_arg_1462_);
v___x_1517_ = l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2___redArg(v_arg_1462_, v___x_1516_, v___y_1512_);
v_a_1518_ = lean_ctor_get(v___x_1517_, 0);
v_isSharedCheck_1534_ = !lean_is_exclusive(v___x_1517_);
if (v_isSharedCheck_1534_ == 0)
{
v___x_1520_ = v___x_1517_;
v_isShared_1521_ = v_isSharedCheck_1534_;
goto v_resetjp_1519_;
}
else
{
lean_inc(v_a_1518_);
lean_dec(v___x_1517_);
v___x_1520_ = lean_box(0);
v_isShared_1521_ = v_isSharedCheck_1534_;
goto v_resetjp_1519_;
}
v_resetjp_1519_:
{
uint8_t v___x_1522_; 
v___x_1522_ = lean_unbox(v_a_1518_);
lean_dec(v_a_1518_);
if (v___x_1522_ == 0)
{
lean_del_object(v___x_1520_);
v___y_1464_ = v___y_1511_;
v___y_1465_ = v___y_1512_;
v___y_1466_ = v___y_1513_;
v___y_1467_ = v___y_1514_;
goto v___jp_1463_;
}
else
{
lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1531_; 
v___x_1523_ = lean_obj_once(&l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1, &l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1_once, _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1);
lean_inc_ref(v_idx_1443_);
v___x_1524_ = l_Lean_MessageData_ofExpr(v_idx_1443_);
v___x_1525_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1525_, 0, v___x_1523_);
lean_ctor_set(v___x_1525_, 1, v___x_1524_);
v___x_1526_ = lean_obj_once(&l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__5, &l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__5_once, _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__5);
v___x_1527_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1527_, 0, v___x_1525_);
lean_ctor_set(v___x_1527_, 1, v___x_1526_);
lean_inc_ref(v_majorType_1446_);
v___x_1528_ = l_Lean_indentExpr(v_majorType_1446_);
v___x_1529_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1529_, 0, v___x_1527_);
lean_ctor_set(v___x_1529_, 1, v___x_1528_);
if (v_isShared_1521_ == 0)
{
lean_ctor_set_tag(v___x_1520_, 1);
lean_ctor_set(v___x_1520_, 0, v___x_1529_);
v___x_1531_ = v___x_1520_;
goto v_reusejp_1530_;
}
else
{
lean_object* v_reuseFailAlloc_1533_; 
v_reuseFailAlloc_1533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1533_, 0, v___x_1529_);
v___x_1531_ = v_reuseFailAlloc_1533_;
goto v_reusejp_1530_;
}
v_reusejp_1530_:
{
lean_object* v___x_1532_; 
lean_inc(v_mvarId_1445_);
lean_inc(v_tacticName_1444_);
v___x_1532_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1444_, v_mvarId_1445_, v___x_1531_, v___y_1511_, v___y_1512_, v___y_1513_, v___y_1514_);
if (lean_obj_tag(v___x_1532_) == 0)
{
lean_dec_ref_known(v___x_1532_, 1);
v___y_1464_ = v___y_1511_;
v___y_1465_ = v___y_1512_;
v___y_1466_ = v___y_1513_;
v___y_1467_ = v___y_1514_;
goto v___jp_1463_;
}
else
{
lean_dec(v___x_1461_);
lean_dec(v_n_1459_);
lean_dec_ref(v_majorType_1446_);
lean_dec(v_mvarId_1445_);
lean_dec(v_tacticName_1444_);
lean_dec_ref(v_idx_1443_);
return v___x_1532_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___boxed(lean_object* v_majorTypeArgs_1546_, lean_object* v_idxPos_1547_, lean_object* v_recursorInfo_1548_, lean_object* v_idx_1549_, lean_object* v_tacticName_1550_, lean_object* v_mvarId_1551_, lean_object* v_majorType_1552_, lean_object* v_n_1553_, lean_object* v_i_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_){
_start:
{
lean_object* v_res_1560_; 
v_res_1560_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg(v_majorTypeArgs_1546_, v_idxPos_1547_, v_recursorInfo_1548_, v_idx_1549_, v_tacticName_1550_, v_mvarId_1551_, v_majorType_1552_, v_n_1553_, v_i_1554_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_);
lean_dec(v___y_1558_);
lean_dec_ref(v___y_1557_);
lean_dec(v___y_1556_);
lean_dec_ref(v___y_1555_);
lean_dec(v_n_1553_);
lean_dec_ref(v_recursorInfo_1548_);
lean_dec(v_idxPos_1547_);
lean_dec_ref(v_majorTypeArgs_1546_);
return v_res_1560_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__1(void){
_start:
{
lean_object* v___x_1562_; lean_object* v___x_1563_; 
v___x_1562_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__0));
v___x_1563_ = l_Lean_stringToMessageData(v___x_1562_);
return v___x_1563_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__3(void){
_start:
{
lean_object* v___x_1565_; lean_object* v___x_1566_; 
v___x_1565_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__2));
v___x_1566_ = l_Lean_stringToMessageData(v___x_1565_);
return v___x_1566_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__5(void){
_start:
{
lean_object* v___x_1568_; lean_object* v___x_1569_; 
v___x_1568_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__4));
v___x_1569_ = l_Lean_stringToMessageData(v___x_1568_);
return v___x_1569_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4(lean_object* v_majorTypeArgs_1570_, lean_object* v_recursorInfo_1571_, lean_object* v_tacticName_1572_, lean_object* v_mvarId_1573_, lean_object* v_majorType_1574_, size_t v_sz_1575_, size_t v_i_1576_, lean_object* v_bs_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_){
_start:
{
uint8_t v___x_1583_; 
v___x_1583_ = lean_usize_dec_lt(v_i_1576_, v_sz_1575_);
if (v___x_1583_ == 0)
{
lean_object* v___x_1584_; 
lean_dec_ref(v_majorType_1574_);
lean_dec(v_mvarId_1573_);
lean_dec(v_tacticName_1572_);
v___x_1584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1584_, 0, v_bs_1577_);
return v___x_1584_;
}
else
{
lean_object* v_v_1585_; lean_object* v___x_1586_; lean_object* v_bs_x27_1587_; lean_object* v_a_1589_; lean_object* v___x_1594_; uint8_t v___x_1595_; 
v_v_1585_ = lean_array_uget(v_bs_1577_, v_i_1576_);
v___x_1586_ = lean_unsigned_to_nat(0u);
v_bs_x27_1587_ = lean_array_uset(v_bs_1577_, v_i_1576_, v___x_1586_);
v___x_1594_ = lean_array_get_size(v_majorTypeArgs_1570_);
v___x_1595_ = lean_nat_dec_le(v___x_1594_, v_v_1585_);
if (v___x_1595_ == 0)
{
lean_object* v_idx_1596_; lean_object* v___y_1598_; lean_object* v___y_1599_; lean_object* v___y_1600_; lean_object* v___y_1601_; uint8_t v___x_1611_; 
v_idx_1596_ = lean_array_fget_borrowed(v_majorTypeArgs_1570_, v_v_1585_);
v___x_1611_ = l_Lean_Expr_isFVar(v_idx_1596_);
if (v___x_1611_ == 0)
{
lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; 
v___x_1612_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__1);
lean_inc(v_idx_1596_);
v___x_1613_ = l_Lean_MessageData_ofExpr(v_idx_1596_);
v___x_1614_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1614_, 0, v___x_1612_);
lean_ctor_set(v___x_1614_, 1, v___x_1613_);
v___x_1615_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__3);
v___x_1616_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1616_, 0, v___x_1614_);
lean_ctor_set(v___x_1616_, 1, v___x_1615_);
lean_inc_ref(v_majorType_1574_);
v___x_1617_ = l_Lean_indentExpr(v_majorType_1574_);
v___x_1618_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1618_, 0, v___x_1616_);
lean_ctor_set(v___x_1618_, 1, v___x_1617_);
v___x_1619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1619_, 0, v___x_1618_);
lean_inc(v_mvarId_1573_);
lean_inc(v_tacticName_1572_);
v___x_1620_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1572_, v_mvarId_1573_, v___x_1619_, v___y_1578_, v___y_1579_, v___y_1580_, v___y_1581_);
if (lean_obj_tag(v___x_1620_) == 0)
{
lean_dec_ref_known(v___x_1620_, 1);
v___y_1598_ = v___y_1578_;
v___y_1599_ = v___y_1579_;
v___y_1600_ = v___y_1580_;
v___y_1601_ = v___y_1581_;
goto v___jp_1597_;
}
else
{
lean_object* v_a_1621_; lean_object* v___x_1623_; uint8_t v_isShared_1624_; uint8_t v_isSharedCheck_1628_; 
lean_dec_ref(v_bs_x27_1587_);
lean_dec(v_v_1585_);
lean_dec_ref(v_majorType_1574_);
lean_dec(v_mvarId_1573_);
lean_dec(v_tacticName_1572_);
v_a_1621_ = lean_ctor_get(v___x_1620_, 0);
v_isSharedCheck_1628_ = !lean_is_exclusive(v___x_1620_);
if (v_isSharedCheck_1628_ == 0)
{
v___x_1623_ = v___x_1620_;
v_isShared_1624_ = v_isSharedCheck_1628_;
goto v_resetjp_1622_;
}
else
{
lean_inc(v_a_1621_);
lean_dec(v___x_1620_);
v___x_1623_ = lean_box(0);
v_isShared_1624_ = v_isSharedCheck_1628_;
goto v_resetjp_1622_;
}
v_resetjp_1622_:
{
lean_object* v___x_1626_; 
if (v_isShared_1624_ == 0)
{
v___x_1626_ = v___x_1623_;
goto v_reusejp_1625_;
}
else
{
lean_object* v_reuseFailAlloc_1627_; 
v_reuseFailAlloc_1627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1627_, 0, v_a_1621_);
v___x_1626_ = v_reuseFailAlloc_1627_;
goto v_reusejp_1625_;
}
v_reusejp_1625_:
{
return v___x_1626_;
}
}
}
}
else
{
v___y_1598_ = v___y_1578_;
v___y_1599_ = v___y_1579_;
v___y_1600_ = v___y_1580_;
v___y_1601_ = v___y_1581_;
goto v___jp_1597_;
}
v___jp_1597_:
{
lean_object* v___x_1602_; 
lean_inc_ref(v_majorType_1574_);
lean_inc(v_mvarId_1573_);
lean_inc(v_tacticName_1572_);
lean_inc(v_idx_1596_);
v___x_1602_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg(v_majorTypeArgs_1570_, v_v_1585_, v_recursorInfo_1571_, v_idx_1596_, v_tacticName_1572_, v_mvarId_1573_, v_majorType_1574_, v___x_1594_, v___x_1594_, v___y_1598_, v___y_1599_, v___y_1600_, v___y_1601_);
lean_dec(v_v_1585_);
if (lean_obj_tag(v___x_1602_) == 0)
{
lean_dec_ref_known(v___x_1602_, 1);
lean_inc(v_idx_1596_);
v_a_1589_ = v_idx_1596_;
goto v___jp_1588_;
}
else
{
lean_object* v_a_1603_; lean_object* v___x_1605_; uint8_t v_isShared_1606_; uint8_t v_isSharedCheck_1610_; 
lean_dec_ref(v_bs_x27_1587_);
lean_dec_ref(v_majorType_1574_);
lean_dec(v_mvarId_1573_);
lean_dec(v_tacticName_1572_);
v_a_1603_ = lean_ctor_get(v___x_1602_, 0);
v_isSharedCheck_1610_ = !lean_is_exclusive(v___x_1602_);
if (v_isSharedCheck_1610_ == 0)
{
v___x_1605_ = v___x_1602_;
v_isShared_1606_ = v_isSharedCheck_1610_;
goto v_resetjp_1604_;
}
else
{
lean_inc(v_a_1603_);
lean_dec(v___x_1602_);
v___x_1605_ = lean_box(0);
v_isShared_1606_ = v_isSharedCheck_1610_;
goto v_resetjp_1604_;
}
v_resetjp_1604_:
{
lean_object* v___x_1608_; 
if (v_isShared_1606_ == 0)
{
v___x_1608_ = v___x_1605_;
goto v_reusejp_1607_;
}
else
{
lean_object* v_reuseFailAlloc_1609_; 
v_reuseFailAlloc_1609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1609_, 0, v_a_1603_);
v___x_1608_ = v_reuseFailAlloc_1609_;
goto v_reusejp_1607_;
}
v_reusejp_1607_:
{
return v___x_1608_;
}
}
}
}
}
else
{
lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; 
lean_dec(v_v_1585_);
v___x_1629_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__5, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__5);
lean_inc_ref(v_majorType_1574_);
v___x_1630_ = l_Lean_indentExpr(v_majorType_1574_);
v___x_1631_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1631_, 0, v___x_1629_);
lean_ctor_set(v___x_1631_, 1, v___x_1630_);
v___x_1632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1632_, 0, v___x_1631_);
lean_inc(v_mvarId_1573_);
lean_inc(v_tacticName_1572_);
v___x_1633_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1572_, v_mvarId_1573_, v___x_1632_, v___y_1578_, v___y_1579_, v___y_1580_, v___y_1581_);
if (lean_obj_tag(v___x_1633_) == 0)
{
lean_object* v_a_1634_; 
v_a_1634_ = lean_ctor_get(v___x_1633_, 0);
lean_inc(v_a_1634_);
lean_dec_ref_known(v___x_1633_, 1);
v_a_1589_ = v_a_1634_;
goto v___jp_1588_;
}
else
{
lean_object* v_a_1635_; lean_object* v___x_1637_; uint8_t v_isShared_1638_; uint8_t v_isSharedCheck_1642_; 
lean_dec_ref(v_bs_x27_1587_);
lean_dec_ref(v_majorType_1574_);
lean_dec(v_mvarId_1573_);
lean_dec(v_tacticName_1572_);
v_a_1635_ = lean_ctor_get(v___x_1633_, 0);
v_isSharedCheck_1642_ = !lean_is_exclusive(v___x_1633_);
if (v_isSharedCheck_1642_ == 0)
{
v___x_1637_ = v___x_1633_;
v_isShared_1638_ = v_isSharedCheck_1642_;
goto v_resetjp_1636_;
}
else
{
lean_inc(v_a_1635_);
lean_dec(v___x_1633_);
v___x_1637_ = lean_box(0);
v_isShared_1638_ = v_isSharedCheck_1642_;
goto v_resetjp_1636_;
}
v_resetjp_1636_:
{
lean_object* v___x_1640_; 
if (v_isShared_1638_ == 0)
{
v___x_1640_ = v___x_1637_;
goto v_reusejp_1639_;
}
else
{
lean_object* v_reuseFailAlloc_1641_; 
v_reuseFailAlloc_1641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1641_, 0, v_a_1635_);
v___x_1640_ = v_reuseFailAlloc_1641_;
goto v_reusejp_1639_;
}
v_reusejp_1639_:
{
return v___x_1640_;
}
}
}
}
v___jp_1588_:
{
size_t v___x_1590_; size_t v___x_1591_; lean_object* v___x_1592_; 
v___x_1590_ = ((size_t)1ULL);
v___x_1591_ = lean_usize_add(v_i_1576_, v___x_1590_);
v___x_1592_ = lean_array_uset(v_bs_x27_1587_, v_i_1576_, v_a_1589_);
v_i_1576_ = v___x_1591_;
v_bs_1577_ = v___x_1592_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___boxed(lean_object* v_majorTypeArgs_1643_, lean_object* v_recursorInfo_1644_, lean_object* v_tacticName_1645_, lean_object* v_mvarId_1646_, lean_object* v_majorType_1647_, lean_object* v_sz_1648_, lean_object* v_i_1649_, lean_object* v_bs_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_){
_start:
{
size_t v_sz_boxed_1656_; size_t v_i_boxed_1657_; lean_object* v_res_1658_; 
v_sz_boxed_1656_ = lean_unbox_usize(v_sz_1648_);
lean_dec(v_sz_1648_);
v_i_boxed_1657_ = lean_unbox_usize(v_i_1649_);
lean_dec(v_i_1649_);
v_res_1658_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4(v_majorTypeArgs_1643_, v_recursorInfo_1644_, v_tacticName_1645_, v_mvarId_1646_, v_majorType_1647_, v_sz_boxed_1656_, v_i_boxed_1657_, v_bs_1650_, v___y_1651_, v___y_1652_, v___y_1653_, v___y_1654_);
lean_dec(v___y_1654_);
lean_dec_ref(v___y_1653_);
lean_dec(v___y_1652_);
lean_dec_ref(v___y_1651_);
lean_dec_ref(v_recursorInfo_1644_);
lean_dec_ref(v_majorTypeArgs_1643_);
return v_res_1658_;
}
}
static lean_object* _init_l_Lean_Meta_getMajorTypeIndices___closed__0(void){
_start:
{
lean_object* v___x_1659_; lean_object* v_dummy_1660_; 
v___x_1659_ = lean_box(0);
v_dummy_1660_ = l_Lean_Expr_sort___override(v___x_1659_);
return v_dummy_1660_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMajorTypeIndices(lean_object* v_mvarId_1661_, lean_object* v_tacticName_1662_, lean_object* v_recursorInfo_1663_, lean_object* v_majorType_1664_, lean_object* v_a_1665_, lean_object* v_a_1666_, lean_object* v_a_1667_, lean_object* v_a_1668_){
_start:
{
lean_object* v_indicesPos_1670_; lean_object* v_nargs_1671_; lean_object* v_dummy_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v_majorTypeArgs_1676_; lean_object* v___x_1677_; size_t v_sz_1678_; size_t v___x_1679_; lean_object* v___x_1680_; 
v_indicesPos_1670_ = lean_ctor_get(v_recursorInfo_1663_, 6);
v_nargs_1671_ = l_Lean_Expr_getAppNumArgs(v_majorType_1664_);
v_dummy_1672_ = lean_obj_once(&l_Lean_Meta_getMajorTypeIndices___closed__0, &l_Lean_Meta_getMajorTypeIndices___closed__0_once, _init_l_Lean_Meta_getMajorTypeIndices___closed__0);
lean_inc(v_nargs_1671_);
v___x_1673_ = lean_mk_array(v_nargs_1671_, v_dummy_1672_);
v___x_1674_ = lean_unsigned_to_nat(1u);
v___x_1675_ = lean_nat_sub(v_nargs_1671_, v___x_1674_);
lean_dec(v_nargs_1671_);
lean_inc_ref(v_majorType_1664_);
v_majorTypeArgs_1676_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_majorType_1664_, v___x_1673_, v___x_1675_);
lean_inc(v_indicesPos_1670_);
v___x_1677_ = lean_array_mk(v_indicesPos_1670_);
v_sz_1678_ = lean_array_size(v___x_1677_);
v___x_1679_ = ((size_t)0ULL);
v___x_1680_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4(v_majorTypeArgs_1676_, v_recursorInfo_1663_, v_tacticName_1662_, v_mvarId_1661_, v_majorType_1664_, v_sz_1678_, v___x_1679_, v___x_1677_, v_a_1665_, v_a_1666_, v_a_1667_, v_a_1668_);
lean_dec_ref(v_recursorInfo_1663_);
lean_dec_ref(v_majorTypeArgs_1676_);
return v___x_1680_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMajorTypeIndices___boxed(lean_object* v_mvarId_1681_, lean_object* v_tacticName_1682_, lean_object* v_recursorInfo_1683_, lean_object* v_majorType_1684_, lean_object* v_a_1685_, lean_object* v_a_1686_, lean_object* v_a_1687_, lean_object* v_a_1688_, lean_object* v_a_1689_){
_start:
{
lean_object* v_res_1690_; 
v_res_1690_ = l_Lean_Meta_getMajorTypeIndices(v_mvarId_1681_, v_tacticName_1682_, v_recursorInfo_1683_, v_majorType_1684_, v_a_1685_, v_a_1686_, v_a_1687_, v_a_1688_);
lean_dec(v_a_1688_);
lean_dec_ref(v_a_1687_);
lean_dec(v_a_1686_);
lean_dec_ref(v_a_1685_);
return v_res_1690_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3(lean_object* v_majorTypeArgs_1691_, lean_object* v_idxPos_1692_, lean_object* v_recursorInfo_1693_, lean_object* v_idx_1694_, lean_object* v_tacticName_1695_, lean_object* v_mvarId_1696_, lean_object* v_majorType_1697_, lean_object* v_n_1698_, lean_object* v_i_1699_, lean_object* v_a_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_){
_start:
{
lean_object* v___x_1706_; 
v___x_1706_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg(v_majorTypeArgs_1691_, v_idxPos_1692_, v_recursorInfo_1693_, v_idx_1694_, v_tacticName_1695_, v_mvarId_1696_, v_majorType_1697_, v_n_1698_, v_i_1699_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_);
return v___x_1706_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___boxed(lean_object* v_majorTypeArgs_1707_, lean_object* v_idxPos_1708_, lean_object* v_recursorInfo_1709_, lean_object* v_idx_1710_, lean_object* v_tacticName_1711_, lean_object* v_mvarId_1712_, lean_object* v_majorType_1713_, lean_object* v_n_1714_, lean_object* v_i_1715_, lean_object* v_a_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_){
_start:
{
lean_object* v_res_1722_; 
v_res_1722_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3(v_majorTypeArgs_1707_, v_idxPos_1708_, v_recursorInfo_1709_, v_idx_1710_, v_tacticName_1711_, v_mvarId_1712_, v_majorType_1713_, v_n_1714_, v_i_1715_, v_a_1716_, v___y_1717_, v___y_1718_, v___y_1719_, v___y_1720_);
lean_dec(v___y_1720_);
lean_dec_ref(v___y_1719_);
lean_dec(v___y_1718_);
lean_dec_ref(v___y_1717_);
lean_dec(v_n_1714_);
lean_dec_ref(v_recursorInfo_1709_);
lean_dec(v_idxPos_1708_);
lean_dec_ref(v_majorTypeArgs_1707_);
return v_res_1722_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1___redArg(lean_object* v_name_1723_, lean_object* v_msg_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_){
_start:
{
lean_object* v_ref_1730_; lean_object* v_msg_1731_; lean_object* v___x_1732_; lean_object* v_a_1733_; lean_object* v___x_1735_; uint8_t v_isShared_1736_; uint8_t v_isSharedCheck_1741_; 
v_ref_1730_ = lean_ctor_get(v___y_1727_, 2);
v_msg_1731_ = l_Lean_MessageData_tagWithErrorName(v_msg_1724_, v_name_1723_);
v___x_1732_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1_spec__2(v_msg_1731_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_);
v_a_1733_ = lean_ctor_get(v___x_1732_, 0);
v_isSharedCheck_1741_ = !lean_is_exclusive(v___x_1732_);
if (v_isSharedCheck_1741_ == 0)
{
v___x_1735_ = v___x_1732_;
v_isShared_1736_ = v_isSharedCheck_1741_;
goto v_resetjp_1734_;
}
else
{
lean_inc(v_a_1733_);
lean_dec(v___x_1732_);
v___x_1735_ = lean_box(0);
v_isShared_1736_ = v_isSharedCheck_1741_;
goto v_resetjp_1734_;
}
v_resetjp_1734_:
{
lean_object* v___x_1737_; lean_object* v___x_1739_; 
lean_inc(v_ref_1730_);
v___x_1737_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1737_, 0, v_ref_1730_);
lean_ctor_set(v___x_1737_, 1, v_a_1733_);
if (v_isShared_1736_ == 0)
{
lean_ctor_set_tag(v___x_1735_, 1);
lean_ctor_set(v___x_1735_, 0, v___x_1737_);
v___x_1739_ = v___x_1735_;
goto v_reusejp_1738_;
}
else
{
lean_object* v_reuseFailAlloc_1740_; 
v_reuseFailAlloc_1740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1740_, 0, v___x_1737_);
v___x_1739_ = v_reuseFailAlloc_1740_;
goto v_reusejp_1738_;
}
v_reusejp_1738_:
{
return v___x_1739_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1___redArg___boxed(lean_object* v_name_1742_, lean_object* v_msg_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_){
_start:
{
lean_object* v_res_1749_; 
v_res_1749_ = l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1___redArg(v_name_1742_, v_msg_1743_, v___y_1744_, v___y_1745_, v___y_1746_, v___y_1747_);
lean_dec(v___y_1747_);
lean_dec_ref(v___y_1746_);
lean_dec(v___y_1745_);
lean_dec_ref(v___y_1744_);
return v_res_1749_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Meta_mkRecursorAppPrefix_spec__0(lean_object* v_a_1750_, lean_object* v___x_1751_, lean_object* v_tacticName_1752_, lean_object* v_mvarId_1753_, lean_object* v_x_1754_, lean_object* v_x_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_){
_start:
{
if (lean_obj_tag(v_x_1755_) == 0)
{
lean_object* v___x_1761_; 
lean_dec(v_mvarId_1753_);
lean_dec(v_tacticName_1752_);
lean_dec(v_a_1750_);
v___x_1761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1761_, 0, v_x_1754_);
return v___x_1761_;
}
else
{
lean_object* v_head_1762_; 
v_head_1762_ = lean_ctor_get(v_x_1755_, 0);
if (lean_obj_tag(v_head_1762_) == 0)
{
lean_object* v_tail_1763_; lean_object* v_fst_1764_; lean_object* v___x_1766_; uint8_t v_isShared_1767_; uint8_t v_isSharedCheck_1775_; 
v_tail_1763_ = lean_ctor_get(v_x_1755_, 1);
v_fst_1764_ = lean_ctor_get(v_x_1754_, 0);
v_isSharedCheck_1775_ = !lean_is_exclusive(v_x_1754_);
if (v_isSharedCheck_1775_ == 0)
{
lean_object* v_unused_1776_; 
v_unused_1776_ = lean_ctor_get(v_x_1754_, 1);
lean_dec(v_unused_1776_);
v___x_1766_ = v_x_1754_;
v_isShared_1767_ = v_isSharedCheck_1775_;
goto v_resetjp_1765_;
}
else
{
lean_inc(v_fst_1764_);
lean_dec(v_x_1754_);
v___x_1766_ = lean_box(0);
v_isShared_1767_ = v_isSharedCheck_1775_;
goto v_resetjp_1765_;
}
v_resetjp_1765_:
{
lean_object* v___x_1768_; uint8_t v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1772_; 
lean_inc(v_a_1750_);
v___x_1768_ = lean_array_push(v_fst_1764_, v_a_1750_);
v___x_1769_ = 1;
v___x_1770_ = lean_box(v___x_1769_);
if (v_isShared_1767_ == 0)
{
lean_ctor_set(v___x_1766_, 1, v___x_1770_);
lean_ctor_set(v___x_1766_, 0, v___x_1768_);
v___x_1772_ = v___x_1766_;
goto v_reusejp_1771_;
}
else
{
lean_object* v_reuseFailAlloc_1774_; 
v_reuseFailAlloc_1774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1774_, 0, v___x_1768_);
lean_ctor_set(v_reuseFailAlloc_1774_, 1, v___x_1770_);
v___x_1772_ = v_reuseFailAlloc_1774_;
goto v_reusejp_1771_;
}
v_reusejp_1771_:
{
v_x_1754_ = v___x_1772_;
v_x_1755_ = v_tail_1763_;
goto _start;
}
}
}
else
{
lean_object* v_tail_1777_; lean_object* v_fst_1778_; lean_object* v_snd_1779_; lean_object* v___x_1781_; uint8_t v_isShared_1782_; uint8_t v_isSharedCheck_1796_; 
v_tail_1777_ = lean_ctor_get(v_x_1755_, 1);
v_fst_1778_ = lean_ctor_get(v_x_1754_, 0);
v_snd_1779_ = lean_ctor_get(v_x_1754_, 1);
v_isSharedCheck_1796_ = !lean_is_exclusive(v_x_1754_);
if (v_isSharedCheck_1796_ == 0)
{
v___x_1781_ = v_x_1754_;
v_isShared_1782_ = v_isSharedCheck_1796_;
goto v_resetjp_1780_;
}
else
{
lean_inc(v_snd_1779_);
lean_inc(v_fst_1778_);
lean_dec(v_x_1754_);
v___x_1781_ = lean_box(0);
v_isShared_1782_ = v_isSharedCheck_1796_;
goto v_resetjp_1780_;
}
v_resetjp_1780_:
{
lean_object* v_idx_1783_; lean_object* v___x_1784_; uint8_t v___x_1785_; 
v_idx_1783_ = lean_ctor_get(v_head_1762_, 0);
v___x_1784_ = lean_array_get_size(v___x_1751_);
v___x_1785_ = lean_nat_dec_le(v___x_1784_, v_idx_1783_);
if (v___x_1785_ == 0)
{
lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1789_; 
v___x_1786_ = lean_array_fget_borrowed(v___x_1751_, v_idx_1783_);
lean_inc(v___x_1786_);
v___x_1787_ = lean_array_push(v_fst_1778_, v___x_1786_);
if (v_isShared_1782_ == 0)
{
lean_ctor_set(v___x_1781_, 0, v___x_1787_);
v___x_1789_ = v___x_1781_;
goto v_reusejp_1788_;
}
else
{
lean_object* v_reuseFailAlloc_1791_; 
v_reuseFailAlloc_1791_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1791_, 0, v___x_1787_);
lean_ctor_set(v_reuseFailAlloc_1791_, 1, v_snd_1779_);
v___x_1789_ = v_reuseFailAlloc_1791_;
goto v_reusejp_1788_;
}
v_reusejp_1788_:
{
v_x_1754_ = v___x_1789_;
v_x_1755_ = v_tail_1777_;
goto _start;
}
}
else
{
lean_object* v___x_1792_; lean_object* v___x_1793_; 
lean_del_object(v___x_1781_);
lean_dec(v_snd_1779_);
lean_dec(v_fst_1778_);
v___x_1792_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9);
lean_inc(v_mvarId_1753_);
lean_inc(v_tacticName_1752_);
v___x_1793_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1752_, v_mvarId_1753_, v___x_1792_, v___y_1756_, v___y_1757_, v___y_1758_, v___y_1759_);
if (lean_obj_tag(v___x_1793_) == 0)
{
lean_object* v_a_1794_; 
v_a_1794_ = lean_ctor_get(v___x_1793_, 0);
lean_inc(v_a_1794_);
lean_dec_ref_known(v___x_1793_, 1);
v_x_1754_ = v_a_1794_;
v_x_1755_ = v_tail_1777_;
goto _start;
}
else
{
lean_dec(v_mvarId_1753_);
lean_dec(v_tacticName_1752_);
lean_dec(v_a_1750_);
return v___x_1793_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Meta_mkRecursorAppPrefix_spec__0___boxed(lean_object* v_a_1797_, lean_object* v___x_1798_, lean_object* v_tacticName_1799_, lean_object* v_mvarId_1800_, lean_object* v_x_1801_, lean_object* v_x_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_){
_start:
{
lean_object* v_res_1808_; 
v_res_1808_ = l_List_foldlM___at___00Lean_Meta_mkRecursorAppPrefix_spec__0(v_a_1797_, v___x_1798_, v_tacticName_1799_, v_mvarId_1800_, v_x_1801_, v_x_1802_, v___y_1803_, v___y_1804_, v___y_1805_, v___y_1806_);
lean_dec(v___y_1806_);
lean_dec_ref(v___y_1805_);
lean_dec(v___y_1804_);
lean_dec_ref(v___y_1803_);
lean_dec(v_x_1802_);
lean_dec_ref(v___x_1798_);
return v_res_1808_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__8(void){
_start:
{
lean_object* v___x_1824_; lean_object* v___x_1825_; 
v___x_1824_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__7));
v___x_1825_ = l_Lean_stringToMessageData(v___x_1824_);
return v___x_1825_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__10(void){
_start:
{
lean_object* v___x_1827_; lean_object* v___x_1828_; 
v___x_1827_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__9));
v___x_1828_ = l_Lean_stringToMessageData(v___x_1827_);
return v___x_1828_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__13(void){
_start:
{
lean_object* v___x_1832_; lean_object* v___x_1833_; 
v___x_1832_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__12));
v___x_1833_ = l_Lean_MessageData_ofFormat(v___x_1832_);
return v___x_1833_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__14(void){
_start:
{
lean_object* v___x_1834_; lean_object* v___x_1835_; 
v___x_1834_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__13, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__13_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__13);
v___x_1835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1835_, 0, v___x_1834_);
return v___x_1835_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2(lean_object* v_recursorInfo_1836_, lean_object* v_a_1837_, lean_object* v_tacticName_1838_, lean_object* v_mvarId_1839_, lean_object* v_indices_1840_, lean_object* v_a_1841_, lean_object* v_major_1842_, lean_object* v_x_1843_, lean_object* v_x_1844_, lean_object* v_x_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_){
_start:
{
if (lean_obj_tag(v_x_1843_) == 5)
{
lean_object* v_fn_1851_; lean_object* v_arg_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; 
v_fn_1851_ = lean_ctor_get(v_x_1843_, 0);
lean_inc_ref(v_fn_1851_);
v_arg_1852_ = lean_ctor_get(v_x_1843_, 1);
lean_inc_ref(v_arg_1852_);
lean_dec_ref_known(v_x_1843_, 2);
v___x_1853_ = lean_array_set(v_x_1844_, v_x_1845_, v_arg_1852_);
v___x_1854_ = lean_unsigned_to_nat(1u);
v___x_1855_ = lean_nat_sub(v_x_1845_, v___x_1854_);
lean_dec(v_x_1845_);
v_x_1843_ = v_fn_1851_;
v_x_1844_ = v___x_1853_;
v_x_1845_ = v___x_1855_;
goto _start;
}
else
{
lean_dec(v_x_1845_);
if (lean_obj_tag(v_x_1843_) == 4)
{
lean_object* v_us_1857_; lean_object* v_recursorName_1858_; lean_object* v_univLevelPos_1859_; uint8_t v_depElim_1860_; lean_object* v_paramsPos_1861_; lean_object* v___x_1862_; uint8_t v___x_1863_; lean_object* v___y_1865_; lean_object* v_motive_1866_; lean_object* v___y_1867_; lean_object* v___y_1868_; lean_object* v___y_1869_; lean_object* v___y_1870_; lean_object* v___x_1883_; lean_object* v___x_1884_; 
v_us_1857_ = lean_ctor_get(v_x_1843_, 1);
lean_inc(v_us_1857_);
lean_dec_ref_known(v_x_1843_, 2);
v_recursorName_1858_ = lean_ctor_get(v_recursorInfo_1836_, 0);
lean_inc(v_recursorName_1858_);
v_univLevelPos_1859_ = lean_ctor_get(v_recursorInfo_1836_, 2);
lean_inc(v_univLevelPos_1859_);
v_depElim_1860_ = lean_ctor_get_uint8(v_recursorInfo_1836_, sizeof(void*)*8);
v_paramsPos_1861_ = lean_ctor_get(v_recursorInfo_1836_, 5);
lean_inc(v_paramsPos_1861_);
lean_dec_ref(v_recursorInfo_1836_);
v___x_1862_ = lean_array_mk(v_us_1857_);
v___x_1863_ = 0;
v___x_1883_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__1));
lean_inc(v_mvarId_1839_);
lean_inc(v_tacticName_1838_);
lean_inc(v_a_1837_);
v___x_1884_ = l_List_foldlM___at___00Lean_Meta_mkRecursorAppPrefix_spec__0(v_a_1837_, v___x_1862_, v_tacticName_1838_, v_mvarId_1839_, v___x_1883_, v_univLevelPos_1859_, v___y_1846_, v___y_1847_, v___y_1848_, v___y_1849_);
lean_dec(v_univLevelPos_1859_);
lean_dec_ref(v___x_1862_);
if (lean_obj_tag(v___x_1884_) == 0)
{
lean_object* v_a_1885_; lean_object* v_fst_1886_; lean_object* v_snd_1887_; lean_object* v___x_1889_; uint8_t v_isShared_1890_; uint8_t v_isSharedCheck_1931_; 
v_a_1885_ = lean_ctor_get(v___x_1884_, 0);
lean_inc(v_a_1885_);
lean_dec_ref_known(v___x_1884_, 1);
v_fst_1886_ = lean_ctor_get(v_a_1885_, 0);
v_snd_1887_ = lean_ctor_get(v_a_1885_, 1);
v_isSharedCheck_1931_ = !lean_is_exclusive(v_a_1885_);
if (v_isSharedCheck_1931_ == 0)
{
v___x_1889_ = v_a_1885_;
v_isShared_1890_ = v_isSharedCheck_1931_;
goto v_resetjp_1888_;
}
else
{
lean_inc(v_snd_1887_);
lean_inc(v_fst_1886_);
lean_dec(v_a_1885_);
v___x_1889_ = lean_box(0);
v_isShared_1890_ = v_isSharedCheck_1931_;
goto v_resetjp_1888_;
}
v_resetjp_1888_:
{
lean_object* v___y_1892_; lean_object* v___y_1893_; lean_object* v___y_1894_; lean_object* v___y_1895_; uint8_t v___x_1911_; 
v___x_1911_ = lean_unbox(v_snd_1887_);
lean_dec(v_snd_1887_);
if (v___x_1911_ == 0)
{
uint8_t v___x_1912_; 
v___x_1912_ = l_Lean_Level_isZero(v_a_1837_);
lean_dec(v_a_1837_);
if (v___x_1912_ == 0)
{
lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1917_; 
lean_dec(v_fst_1886_);
lean_dec(v_paramsPos_1861_);
lean_dec_ref(v_x_1844_);
lean_dec_ref(v_major_1842_);
lean_dec_ref(v_a_1841_);
v___x_1913_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__6));
v___x_1914_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__8, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__8_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__8);
v___x_1915_ = l_Lean_MessageData_ofName(v_recursorName_1858_);
if (v_isShared_1890_ == 0)
{
lean_ctor_set_tag(v___x_1889_, 7);
lean_ctor_set(v___x_1889_, 1, v___x_1915_);
lean_ctor_set(v___x_1889_, 0, v___x_1914_);
v___x_1917_ = v___x_1889_;
goto v_reusejp_1916_;
}
else
{
lean_object* v_reuseFailAlloc_1930_; 
v_reuseFailAlloc_1930_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1930_, 0, v___x_1914_);
lean_ctor_set(v_reuseFailAlloc_1930_, 1, v___x_1915_);
v___x_1917_ = v_reuseFailAlloc_1930_;
goto v_reusejp_1916_;
}
v_reusejp_1916_:
{
lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v_a_1922_; lean_object* v___x_1924_; uint8_t v_isShared_1925_; uint8_t v_isSharedCheck_1929_; 
v___x_1918_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__10, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__10_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__10);
v___x_1919_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1919_, 0, v___x_1917_);
lean_ctor_set(v___x_1919_, 1, v___x_1918_);
v___x_1920_ = l_Lean_Meta_mkTacticExMsg(v_tacticName_1838_, v_mvarId_1839_, v___x_1919_);
v___x_1921_ = l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1___redArg(v___x_1913_, v___x_1920_, v___y_1846_, v___y_1847_, v___y_1848_, v___y_1849_);
v_a_1922_ = lean_ctor_get(v___x_1921_, 0);
v_isSharedCheck_1929_ = !lean_is_exclusive(v___x_1921_);
if (v_isSharedCheck_1929_ == 0)
{
v___x_1924_ = v___x_1921_;
v_isShared_1925_ = v_isSharedCheck_1929_;
goto v_resetjp_1923_;
}
else
{
lean_inc(v_a_1922_);
lean_dec(v___x_1921_);
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
lean_del_object(v___x_1889_);
lean_dec(v_tacticName_1838_);
v___y_1892_ = v___y_1846_;
v___y_1893_ = v___y_1847_;
v___y_1894_ = v___y_1848_;
v___y_1895_ = v___y_1849_;
goto v___jp_1891_;
}
}
else
{
lean_del_object(v___x_1889_);
lean_dec(v_tacticName_1838_);
lean_dec(v_a_1837_);
v___y_1892_ = v___y_1846_;
v___y_1893_ = v___y_1847_;
v___y_1894_ = v___y_1848_;
v___y_1895_ = v___y_1849_;
goto v___jp_1891_;
}
v___jp_1891_:
{
lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; 
v___x_1896_ = lean_array_to_list(v_fst_1886_);
v___x_1897_ = l_Lean_mkConst(v_recursorName_1858_, v___x_1896_);
v___x_1898_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams(v_mvarId_1839_, v_x_1844_, v_paramsPos_1861_, v___x_1897_, v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_);
lean_dec_ref(v_x_1844_);
if (lean_obj_tag(v___x_1898_) == 0)
{
if (v_depElim_1860_ == 0)
{
lean_object* v_a_1899_; 
lean_dec_ref(v_major_1842_);
v_a_1899_ = lean_ctor_get(v___x_1898_, 0);
lean_inc(v_a_1899_);
lean_dec_ref_known(v___x_1898_, 1);
v___y_1865_ = v_a_1899_;
v_motive_1866_ = v_a_1841_;
v___y_1867_ = v___y_1892_;
v___y_1868_ = v___y_1893_;
v___y_1869_ = v___y_1894_;
v___y_1870_ = v___y_1895_;
goto v___jp_1864_;
}
else
{
lean_object* v_a_1900_; lean_object* v___x_1901_; 
v_a_1900_ = lean_ctor_get(v___x_1898_, 0);
lean_inc(v_a_1900_);
lean_dec_ref_known(v___x_1898_, 1);
lean_inc(v___y_1895_);
lean_inc_ref(v___y_1894_);
lean_inc(v___y_1893_);
lean_inc_ref(v___y_1892_);
lean_inc_ref(v_major_1842_);
v___x_1901_ = lean_infer_type(v_major_1842_, v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_);
if (lean_obj_tag(v___x_1901_) == 0)
{
lean_object* v_a_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; 
v_a_1902_ = lean_ctor_get(v___x_1901_, 0);
lean_inc(v_a_1902_);
lean_dec_ref_known(v___x_1901_, 1);
v___x_1903_ = lean_unsigned_to_nat(1u);
v___x_1904_ = lean_mk_empty_array_with_capacity(v___x_1903_);
v___x_1905_ = lean_array_push(v___x_1904_, v_major_1842_);
v___x_1906_ = l_Lean_Expr_abstractM(v_a_1841_, v___x_1905_, v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_);
lean_dec_ref(v___x_1905_);
if (lean_obj_tag(v___x_1906_) == 0)
{
lean_object* v_a_1907_; lean_object* v___x_1908_; uint8_t v___x_1909_; lean_object* v___x_1910_; 
v_a_1907_ = lean_ctor_get(v___x_1906_, 0);
lean_inc(v_a_1907_);
lean_dec_ref_known(v___x_1906_, 1);
v___x_1908_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__3));
v___x_1909_ = 0;
v___x_1910_ = l_Lean_mkLambda(v___x_1908_, v___x_1909_, v_a_1902_, v_a_1907_);
v___y_1865_ = v_a_1900_;
v_motive_1866_ = v___x_1910_;
v___y_1867_ = v___y_1892_;
v___y_1868_ = v___y_1893_;
v___y_1869_ = v___y_1894_;
v___y_1870_ = v___y_1895_;
goto v___jp_1864_;
}
else
{
lean_dec(v_a_1902_);
lean_dec(v_a_1900_);
return v___x_1906_;
}
}
else
{
lean_dec(v_a_1900_);
lean_dec_ref(v_major_1842_);
lean_dec_ref(v_a_1841_);
return v___x_1901_;
}
}
}
else
{
lean_dec_ref(v_major_1842_);
lean_dec_ref(v_a_1841_);
return v___x_1898_;
}
}
}
}
else
{
lean_object* v_a_1932_; lean_object* v___x_1934_; uint8_t v_isShared_1935_; uint8_t v_isSharedCheck_1939_; 
lean_dec(v_paramsPos_1861_);
lean_dec(v_recursorName_1858_);
lean_dec_ref(v_x_1844_);
lean_dec_ref(v_major_1842_);
lean_dec_ref(v_a_1841_);
lean_dec(v_mvarId_1839_);
lean_dec(v_tacticName_1838_);
lean_dec(v_a_1837_);
v_a_1932_ = lean_ctor_get(v___x_1884_, 0);
v_isSharedCheck_1939_ = !lean_is_exclusive(v___x_1884_);
if (v_isSharedCheck_1939_ == 0)
{
v___x_1934_ = v___x_1884_;
v_isShared_1935_ = v_isSharedCheck_1939_;
goto v_resetjp_1933_;
}
else
{
lean_inc(v_a_1932_);
lean_dec(v___x_1884_);
v___x_1934_ = lean_box(0);
v_isShared_1935_ = v_isSharedCheck_1939_;
goto v_resetjp_1933_;
}
v_resetjp_1933_:
{
lean_object* v___x_1937_; 
if (v_isShared_1935_ == 0)
{
v___x_1937_ = v___x_1934_;
goto v_reusejp_1936_;
}
else
{
lean_object* v_reuseFailAlloc_1938_; 
v_reuseFailAlloc_1938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1938_, 0, v_a_1932_);
v___x_1937_ = v_reuseFailAlloc_1938_;
goto v_reusejp_1936_;
}
v_reusejp_1936_:
{
return v___x_1937_;
}
}
}
v___jp_1864_:
{
uint8_t v___x_1871_; uint8_t v___x_1872_; lean_object* v___x_1873_; 
v___x_1871_ = 1;
v___x_1872_ = 1;
v___x_1873_ = l_Lean_Meta_mkLambdaFVars(v_indices_1840_, v_motive_1866_, v___x_1863_, v___x_1871_, v___x_1863_, v___x_1871_, v___x_1872_, v___y_1867_, v___y_1868_, v___y_1869_, v___y_1870_);
if (lean_obj_tag(v___x_1873_) == 0)
{
lean_object* v_a_1874_; lean_object* v___x_1876_; uint8_t v_isShared_1877_; uint8_t v_isSharedCheck_1882_; 
v_a_1874_ = lean_ctor_get(v___x_1873_, 0);
v_isSharedCheck_1882_ = !lean_is_exclusive(v___x_1873_);
if (v_isSharedCheck_1882_ == 0)
{
v___x_1876_ = v___x_1873_;
v_isShared_1877_ = v_isSharedCheck_1882_;
goto v_resetjp_1875_;
}
else
{
lean_inc(v_a_1874_);
lean_dec(v___x_1873_);
v___x_1876_ = lean_box(0);
v_isShared_1877_ = v_isSharedCheck_1882_;
goto v_resetjp_1875_;
}
v_resetjp_1875_:
{
lean_object* v___x_1878_; lean_object* v___x_1880_; 
v___x_1878_ = l_Lean_Expr_app___override(v___y_1865_, v_a_1874_);
if (v_isShared_1877_ == 0)
{
lean_ctor_set(v___x_1876_, 0, v___x_1878_);
v___x_1880_ = v___x_1876_;
goto v_reusejp_1879_;
}
else
{
lean_object* v_reuseFailAlloc_1881_; 
v_reuseFailAlloc_1881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1881_, 0, v___x_1878_);
v___x_1880_ = v_reuseFailAlloc_1881_;
goto v_reusejp_1879_;
}
v_reusejp_1879_:
{
return v___x_1880_;
}
}
}
else
{
lean_dec_ref(v___y_1865_);
return v___x_1873_;
}
}
}
else
{
lean_object* v___x_1940_; lean_object* v___x_1941_; 
lean_dec_ref(v_x_1844_);
lean_dec_ref(v_x_1843_);
lean_dec_ref(v_major_1842_);
lean_dec_ref(v_a_1841_);
lean_dec(v_a_1837_);
lean_dec_ref(v_recursorInfo_1836_);
v___x_1940_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__14, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__14_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__14);
v___x_1941_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1838_, v_mvarId_1839_, v___x_1940_, v___y_1846_, v___y_1847_, v___y_1848_, v___y_1849_);
return v___x_1941_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___boxed(lean_object* v_recursorInfo_1942_, lean_object* v_a_1943_, lean_object* v_tacticName_1944_, lean_object* v_mvarId_1945_, lean_object* v_indices_1946_, lean_object* v_a_1947_, lean_object* v_major_1948_, lean_object* v_x_1949_, lean_object* v_x_1950_, lean_object* v_x_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_){
_start:
{
lean_object* v_res_1957_; 
v_res_1957_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2(v_recursorInfo_1942_, v_a_1943_, v_tacticName_1944_, v_mvarId_1945_, v_indices_1946_, v_a_1947_, v_major_1948_, v_x_1949_, v_x_1950_, v_x_1951_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_);
lean_dec(v___y_1955_);
lean_dec_ref(v___y_1954_);
lean_dec(v___y_1953_);
lean_dec_ref(v___y_1952_);
lean_dec_ref(v_indices_1946_);
return v_res_1957_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2(lean_object* v_a_1958_, lean_object* v_tacticName_1959_, lean_object* v_mvarId_1960_, lean_object* v_recursorInfo_1961_, lean_object* v_indices_1962_, lean_object* v_a_1963_, lean_object* v_major_1964_, lean_object* v_x_1965_, lean_object* v_x_1966_, lean_object* v_x_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_){
_start:
{
if (lean_obj_tag(v_x_1965_) == 5)
{
lean_object* v_fn_1973_; lean_object* v_arg_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; 
v_fn_1973_ = lean_ctor_get(v_x_1965_, 0);
lean_inc_ref(v_fn_1973_);
v_arg_1974_ = lean_ctor_get(v_x_1965_, 1);
lean_inc_ref(v_arg_1974_);
lean_dec_ref_known(v_x_1965_, 2);
v___x_1975_ = lean_array_set(v_x_1966_, v_x_1967_, v_arg_1974_);
v___x_1976_ = lean_unsigned_to_nat(1u);
v___x_1977_ = lean_nat_sub(v_x_1967_, v___x_1976_);
v___x_1978_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2(v_recursorInfo_1961_, v_a_1958_, v_tacticName_1959_, v_mvarId_1960_, v_indices_1962_, v_a_1963_, v_major_1964_, v_fn_1973_, v___x_1975_, v___x_1977_, v___y_1968_, v___y_1969_, v___y_1970_, v___y_1971_);
return v___x_1978_;
}
else
{
if (lean_obj_tag(v_x_1965_) == 4)
{
lean_object* v_us_1979_; lean_object* v_recursorName_1980_; lean_object* v_univLevelPos_1981_; uint8_t v_depElim_1982_; lean_object* v_paramsPos_1983_; lean_object* v___x_1984_; uint8_t v___x_1985_; lean_object* v___y_1987_; lean_object* v_motive_1988_; lean_object* v___y_1989_; lean_object* v___y_1990_; lean_object* v___y_1991_; lean_object* v___y_1992_; lean_object* v___x_2005_; lean_object* v___x_2006_; 
v_us_1979_ = lean_ctor_get(v_x_1965_, 1);
lean_inc(v_us_1979_);
lean_dec_ref_known(v_x_1965_, 2);
v_recursorName_1980_ = lean_ctor_get(v_recursorInfo_1961_, 0);
lean_inc(v_recursorName_1980_);
v_univLevelPos_1981_ = lean_ctor_get(v_recursorInfo_1961_, 2);
lean_inc(v_univLevelPos_1981_);
v_depElim_1982_ = lean_ctor_get_uint8(v_recursorInfo_1961_, sizeof(void*)*8);
v_paramsPos_1983_ = lean_ctor_get(v_recursorInfo_1961_, 5);
lean_inc(v_paramsPos_1983_);
lean_dec_ref(v_recursorInfo_1961_);
v___x_1984_ = lean_array_mk(v_us_1979_);
v___x_1985_ = 0;
v___x_2005_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__1));
lean_inc(v_mvarId_1960_);
lean_inc(v_tacticName_1959_);
lean_inc(v_a_1958_);
v___x_2006_ = l_List_foldlM___at___00Lean_Meta_mkRecursorAppPrefix_spec__0(v_a_1958_, v___x_1984_, v_tacticName_1959_, v_mvarId_1960_, v___x_2005_, v_univLevelPos_1981_, v___y_1968_, v___y_1969_, v___y_1970_, v___y_1971_);
lean_dec(v_univLevelPos_1981_);
lean_dec_ref(v___x_1984_);
if (lean_obj_tag(v___x_2006_) == 0)
{
lean_object* v_a_2007_; lean_object* v_fst_2008_; lean_object* v_snd_2009_; lean_object* v___x_2011_; uint8_t v_isShared_2012_; uint8_t v_isSharedCheck_2053_; 
v_a_2007_ = lean_ctor_get(v___x_2006_, 0);
lean_inc(v_a_2007_);
lean_dec_ref_known(v___x_2006_, 1);
v_fst_2008_ = lean_ctor_get(v_a_2007_, 0);
v_snd_2009_ = lean_ctor_get(v_a_2007_, 1);
v_isSharedCheck_2053_ = !lean_is_exclusive(v_a_2007_);
if (v_isSharedCheck_2053_ == 0)
{
v___x_2011_ = v_a_2007_;
v_isShared_2012_ = v_isSharedCheck_2053_;
goto v_resetjp_2010_;
}
else
{
lean_inc(v_snd_2009_);
lean_inc(v_fst_2008_);
lean_dec(v_a_2007_);
v___x_2011_ = lean_box(0);
v_isShared_2012_ = v_isSharedCheck_2053_;
goto v_resetjp_2010_;
}
v_resetjp_2010_:
{
lean_object* v___y_2014_; lean_object* v___y_2015_; lean_object* v___y_2016_; lean_object* v___y_2017_; uint8_t v___x_2033_; 
v___x_2033_ = lean_unbox(v_snd_2009_);
lean_dec(v_snd_2009_);
if (v___x_2033_ == 0)
{
uint8_t v___x_2034_; 
v___x_2034_ = l_Lean_Level_isZero(v_a_1958_);
lean_dec(v_a_1958_);
if (v___x_2034_ == 0)
{
lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2039_; 
lean_dec(v_fst_2008_);
lean_dec(v_paramsPos_1983_);
lean_dec_ref(v_x_1966_);
lean_dec_ref(v_major_1964_);
lean_dec_ref(v_a_1963_);
v___x_2035_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__6));
v___x_2036_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__8, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__8_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__8);
v___x_2037_ = l_Lean_MessageData_ofName(v_recursorName_1980_);
if (v_isShared_2012_ == 0)
{
lean_ctor_set_tag(v___x_2011_, 7);
lean_ctor_set(v___x_2011_, 1, v___x_2037_);
lean_ctor_set(v___x_2011_, 0, v___x_2036_);
v___x_2039_ = v___x_2011_;
goto v_reusejp_2038_;
}
else
{
lean_object* v_reuseFailAlloc_2052_; 
v_reuseFailAlloc_2052_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2052_, 0, v___x_2036_);
lean_ctor_set(v_reuseFailAlloc_2052_, 1, v___x_2037_);
v___x_2039_ = v_reuseFailAlloc_2052_;
goto v_reusejp_2038_;
}
v_reusejp_2038_:
{
lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v_a_2044_; lean_object* v___x_2046_; uint8_t v_isShared_2047_; uint8_t v_isSharedCheck_2051_; 
v___x_2040_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__10, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__10_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__10);
v___x_2041_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2041_, 0, v___x_2039_);
lean_ctor_set(v___x_2041_, 1, v___x_2040_);
v___x_2042_ = l_Lean_Meta_mkTacticExMsg(v_tacticName_1959_, v_mvarId_1960_, v___x_2041_);
v___x_2043_ = l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1___redArg(v___x_2035_, v___x_2042_, v___y_1968_, v___y_1969_, v___y_1970_, v___y_1971_);
v_a_2044_ = lean_ctor_get(v___x_2043_, 0);
v_isSharedCheck_2051_ = !lean_is_exclusive(v___x_2043_);
if (v_isSharedCheck_2051_ == 0)
{
v___x_2046_ = v___x_2043_;
v_isShared_2047_ = v_isSharedCheck_2051_;
goto v_resetjp_2045_;
}
else
{
lean_inc(v_a_2044_);
lean_dec(v___x_2043_);
v___x_2046_ = lean_box(0);
v_isShared_2047_ = v_isSharedCheck_2051_;
goto v_resetjp_2045_;
}
v_resetjp_2045_:
{
lean_object* v___x_2049_; 
if (v_isShared_2047_ == 0)
{
v___x_2049_ = v___x_2046_;
goto v_reusejp_2048_;
}
else
{
lean_object* v_reuseFailAlloc_2050_; 
v_reuseFailAlloc_2050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2050_, 0, v_a_2044_);
v___x_2049_ = v_reuseFailAlloc_2050_;
goto v_reusejp_2048_;
}
v_reusejp_2048_:
{
return v___x_2049_;
}
}
}
}
else
{
lean_del_object(v___x_2011_);
lean_dec(v_tacticName_1959_);
v___y_2014_ = v___y_1968_;
v___y_2015_ = v___y_1969_;
v___y_2016_ = v___y_1970_;
v___y_2017_ = v___y_1971_;
goto v___jp_2013_;
}
}
else
{
lean_del_object(v___x_2011_);
lean_dec(v_tacticName_1959_);
lean_dec(v_a_1958_);
v___y_2014_ = v___y_1968_;
v___y_2015_ = v___y_1969_;
v___y_2016_ = v___y_1970_;
v___y_2017_ = v___y_1971_;
goto v___jp_2013_;
}
v___jp_2013_:
{
lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; 
v___x_2018_ = lean_array_to_list(v_fst_2008_);
v___x_2019_ = l_Lean_mkConst(v_recursorName_1980_, v___x_2018_);
v___x_2020_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams(v_mvarId_1960_, v_x_1966_, v_paramsPos_1983_, v___x_2019_, v___y_2014_, v___y_2015_, v___y_2016_, v___y_2017_);
lean_dec_ref(v_x_1966_);
if (lean_obj_tag(v___x_2020_) == 0)
{
if (v_depElim_1982_ == 0)
{
lean_object* v_a_2021_; 
lean_dec_ref(v_major_1964_);
v_a_2021_ = lean_ctor_get(v___x_2020_, 0);
lean_inc(v_a_2021_);
lean_dec_ref_known(v___x_2020_, 1);
v___y_1987_ = v_a_2021_;
v_motive_1988_ = v_a_1963_;
v___y_1989_ = v___y_2014_;
v___y_1990_ = v___y_2015_;
v___y_1991_ = v___y_2016_;
v___y_1992_ = v___y_2017_;
goto v___jp_1986_;
}
else
{
lean_object* v_a_2022_; lean_object* v___x_2023_; 
v_a_2022_ = lean_ctor_get(v___x_2020_, 0);
lean_inc(v_a_2022_);
lean_dec_ref_known(v___x_2020_, 1);
lean_inc(v___y_2017_);
lean_inc_ref(v___y_2016_);
lean_inc(v___y_2015_);
lean_inc_ref(v___y_2014_);
lean_inc_ref(v_major_1964_);
v___x_2023_ = lean_infer_type(v_major_1964_, v___y_2014_, v___y_2015_, v___y_2016_, v___y_2017_);
if (lean_obj_tag(v___x_2023_) == 0)
{
lean_object* v_a_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; 
v_a_2024_ = lean_ctor_get(v___x_2023_, 0);
lean_inc(v_a_2024_);
lean_dec_ref_known(v___x_2023_, 1);
v___x_2025_ = lean_unsigned_to_nat(1u);
v___x_2026_ = lean_mk_empty_array_with_capacity(v___x_2025_);
v___x_2027_ = lean_array_push(v___x_2026_, v_major_1964_);
v___x_2028_ = l_Lean_Expr_abstractM(v_a_1963_, v___x_2027_, v___y_2014_, v___y_2015_, v___y_2016_, v___y_2017_);
lean_dec_ref(v___x_2027_);
if (lean_obj_tag(v___x_2028_) == 0)
{
lean_object* v_a_2029_; lean_object* v___x_2030_; uint8_t v___x_2031_; lean_object* v___x_2032_; 
v_a_2029_ = lean_ctor_get(v___x_2028_, 0);
lean_inc(v_a_2029_);
lean_dec_ref_known(v___x_2028_, 1);
v___x_2030_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__3));
v___x_2031_ = 0;
v___x_2032_ = l_Lean_mkLambda(v___x_2030_, v___x_2031_, v_a_2024_, v_a_2029_);
v___y_1987_ = v_a_2022_;
v_motive_1988_ = v___x_2032_;
v___y_1989_ = v___y_2014_;
v___y_1990_ = v___y_2015_;
v___y_1991_ = v___y_2016_;
v___y_1992_ = v___y_2017_;
goto v___jp_1986_;
}
else
{
lean_dec(v_a_2024_);
lean_dec(v_a_2022_);
return v___x_2028_;
}
}
else
{
lean_dec(v_a_2022_);
lean_dec_ref(v_major_1964_);
lean_dec_ref(v_a_1963_);
return v___x_2023_;
}
}
}
else
{
lean_dec_ref(v_major_1964_);
lean_dec_ref(v_a_1963_);
return v___x_2020_;
}
}
}
}
else
{
lean_object* v_a_2054_; lean_object* v___x_2056_; uint8_t v_isShared_2057_; uint8_t v_isSharedCheck_2061_; 
lean_dec(v_paramsPos_1983_);
lean_dec(v_recursorName_1980_);
lean_dec_ref(v_x_1966_);
lean_dec_ref(v_major_1964_);
lean_dec_ref(v_a_1963_);
lean_dec(v_mvarId_1960_);
lean_dec(v_tacticName_1959_);
lean_dec(v_a_1958_);
v_a_2054_ = lean_ctor_get(v___x_2006_, 0);
v_isSharedCheck_2061_ = !lean_is_exclusive(v___x_2006_);
if (v_isSharedCheck_2061_ == 0)
{
v___x_2056_ = v___x_2006_;
v_isShared_2057_ = v_isSharedCheck_2061_;
goto v_resetjp_2055_;
}
else
{
lean_inc(v_a_2054_);
lean_dec(v___x_2006_);
v___x_2056_ = lean_box(0);
v_isShared_2057_ = v_isSharedCheck_2061_;
goto v_resetjp_2055_;
}
v_resetjp_2055_:
{
lean_object* v___x_2059_; 
if (v_isShared_2057_ == 0)
{
v___x_2059_ = v___x_2056_;
goto v_reusejp_2058_;
}
else
{
lean_object* v_reuseFailAlloc_2060_; 
v_reuseFailAlloc_2060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2060_, 0, v_a_2054_);
v___x_2059_ = v_reuseFailAlloc_2060_;
goto v_reusejp_2058_;
}
v_reusejp_2058_:
{
return v___x_2059_;
}
}
}
v___jp_1986_:
{
uint8_t v___x_1993_; uint8_t v___x_1994_; lean_object* v___x_1995_; 
v___x_1993_ = 1;
v___x_1994_ = 1;
v___x_1995_ = l_Lean_Meta_mkLambdaFVars(v_indices_1962_, v_motive_1988_, v___x_1985_, v___x_1993_, v___x_1985_, v___x_1993_, v___x_1994_, v___y_1989_, v___y_1990_, v___y_1991_, v___y_1992_);
if (lean_obj_tag(v___x_1995_) == 0)
{
lean_object* v_a_1996_; lean_object* v___x_1998_; uint8_t v_isShared_1999_; uint8_t v_isSharedCheck_2004_; 
v_a_1996_ = lean_ctor_get(v___x_1995_, 0);
v_isSharedCheck_2004_ = !lean_is_exclusive(v___x_1995_);
if (v_isSharedCheck_2004_ == 0)
{
v___x_1998_ = v___x_1995_;
v_isShared_1999_ = v_isSharedCheck_2004_;
goto v_resetjp_1997_;
}
else
{
lean_inc(v_a_1996_);
lean_dec(v___x_1995_);
v___x_1998_ = lean_box(0);
v_isShared_1999_ = v_isSharedCheck_2004_;
goto v_resetjp_1997_;
}
v_resetjp_1997_:
{
lean_object* v___x_2000_; lean_object* v___x_2002_; 
v___x_2000_ = l_Lean_Expr_app___override(v___y_1987_, v_a_1996_);
if (v_isShared_1999_ == 0)
{
lean_ctor_set(v___x_1998_, 0, v___x_2000_);
v___x_2002_ = v___x_1998_;
goto v_reusejp_2001_;
}
else
{
lean_object* v_reuseFailAlloc_2003_; 
v_reuseFailAlloc_2003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2003_, 0, v___x_2000_);
v___x_2002_ = v_reuseFailAlloc_2003_;
goto v_reusejp_2001_;
}
v_reusejp_2001_:
{
return v___x_2002_;
}
}
}
else
{
lean_dec_ref(v___y_1987_);
return v___x_1995_;
}
}
}
else
{
lean_object* v___x_2062_; lean_object* v___x_2063_; 
lean_dec_ref(v_x_1966_);
lean_dec_ref(v_x_1965_);
lean_dec_ref(v_major_1964_);
lean_dec_ref(v_a_1963_);
lean_dec_ref(v_recursorInfo_1961_);
lean_dec(v_a_1958_);
v___x_2062_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__14, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__14_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__14);
v___x_2063_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1959_, v_mvarId_1960_, v___x_2062_, v___y_1968_, v___y_1969_, v___y_1970_, v___y_1971_);
return v___x_2063_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2___boxed(lean_object* v_a_2064_, lean_object* v_tacticName_2065_, lean_object* v_mvarId_2066_, lean_object* v_recursorInfo_2067_, lean_object* v_indices_2068_, lean_object* v_a_2069_, lean_object* v_major_2070_, lean_object* v_x_2071_, lean_object* v_x_2072_, lean_object* v_x_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_){
_start:
{
lean_object* v_res_2079_; 
v_res_2079_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2(v_a_2064_, v_tacticName_2065_, v_mvarId_2066_, v_recursorInfo_2067_, v_indices_2068_, v_a_2069_, v_major_2070_, v_x_2071_, v_x_2072_, v_x_2073_, v___y_2074_, v___y_2075_, v___y_2076_, v___y_2077_);
lean_dec(v___y_2077_);
lean_dec_ref(v___y_2076_);
lean_dec(v___y_2075_);
lean_dec_ref(v___y_2074_);
lean_dec(v_x_2073_);
lean_dec_ref(v_indices_2068_);
return v_res_2079_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkRecursorAppPrefix(lean_object* v_mvarId_2080_, lean_object* v_tacticName_2081_, lean_object* v_majorFVarId_2082_, lean_object* v_recursorInfo_2083_, lean_object* v_indices_2084_, lean_object* v_a_2085_, lean_object* v_a_2086_, lean_object* v_a_2087_, lean_object* v_a_2088_){
_start:
{
lean_object* v_major_2090_; lean_object* v___x_2091_; 
lean_inc(v_majorFVarId_2082_);
v_major_2090_ = l_Lean_mkFVar(v_majorFVarId_2082_);
lean_inc(v_mvarId_2080_);
v___x_2091_ = l_Lean_MVarId_getType(v_mvarId_2080_, v_a_2085_, v_a_2086_, v_a_2087_, v_a_2088_);
if (lean_obj_tag(v___x_2091_) == 0)
{
lean_object* v_a_2092_; lean_object* v___x_2093_; 
v_a_2092_ = lean_ctor_get(v___x_2091_, 0);
lean_inc_n(v_a_2092_, 2);
lean_dec_ref_known(v___x_2091_, 1);
v___x_2093_ = l_Lean_Meta_getLevel(v_a_2092_, v_a_2085_, v_a_2086_, v_a_2087_, v_a_2088_);
if (lean_obj_tag(v___x_2093_) == 0)
{
lean_object* v_a_2094_; lean_object* v___x_2095_; 
v_a_2094_ = lean_ctor_get(v___x_2093_, 0);
lean_inc(v_a_2094_);
lean_dec_ref_known(v___x_2093_, 1);
v___x_2095_ = l_Lean_Meta_normalizeLevel(v_a_2094_, v_a_2085_, v_a_2086_, v_a_2087_, v_a_2088_);
if (lean_obj_tag(v___x_2095_) == 0)
{
lean_object* v_a_2096_; lean_object* v___x_2097_; 
v_a_2096_ = lean_ctor_get(v___x_2095_, 0);
lean_inc(v_a_2096_);
lean_dec_ref_known(v___x_2095_, 1);
v___x_2097_ = l_Lean_FVarId_getDecl___redArg(v_majorFVarId_2082_, v_a_2085_, v_a_2087_, v_a_2088_);
if (lean_obj_tag(v___x_2097_) == 0)
{
lean_object* v_a_2098_; lean_object* v_typeName_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; 
v_a_2098_ = lean_ctor_get(v___x_2097_, 0);
lean_inc(v_a_2098_);
lean_dec_ref_known(v___x_2097_, 1);
v_typeName_2099_ = lean_ctor_get(v_recursorInfo_2083_, 1);
v___x_2100_ = l_Lean_LocalDecl_type(v_a_2098_);
lean_dec(v_a_2098_);
lean_inc_ref(v___x_2100_);
v___x_2101_ = l_Lean_Meta_whnfUntil(v___x_2100_, v_typeName_2099_, v_a_2085_, v_a_2086_, v_a_2087_, v_a_2088_);
if (lean_obj_tag(v___x_2101_) == 0)
{
lean_object* v_a_2102_; 
v_a_2102_ = lean_ctor_get(v___x_2101_, 0);
lean_inc(v_a_2102_);
lean_dec_ref_known(v___x_2101_, 1);
if (lean_obj_tag(v_a_2102_) == 1)
{
lean_object* v_val_2103_; lean_object* v_dummy_2104_; lean_object* v_nargs_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; 
lean_dec_ref(v___x_2100_);
v_val_2103_ = lean_ctor_get(v_a_2102_, 0);
lean_inc(v_val_2103_);
lean_dec_ref_known(v_a_2102_, 1);
v_dummy_2104_ = lean_obj_once(&l_Lean_Meta_getMajorTypeIndices___closed__0, &l_Lean_Meta_getMajorTypeIndices___closed__0_once, _init_l_Lean_Meta_getMajorTypeIndices___closed__0);
v_nargs_2105_ = l_Lean_Expr_getAppNumArgs(v_val_2103_);
lean_inc(v_nargs_2105_);
v___x_2106_ = lean_mk_array(v_nargs_2105_, v_dummy_2104_);
v___x_2107_ = lean_unsigned_to_nat(1u);
v___x_2108_ = lean_nat_sub(v_nargs_2105_, v___x_2107_);
lean_dec(v_nargs_2105_);
v___x_2109_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2(v_a_2096_, v_tacticName_2081_, v_mvarId_2080_, v_recursorInfo_2083_, v_indices_2084_, v_a_2092_, v_major_2090_, v_val_2103_, v___x_2106_, v___x_2108_, v_a_2085_, v_a_2086_, v_a_2087_, v_a_2088_);
lean_dec(v___x_2108_);
return v___x_2109_;
}
else
{
lean_object* v___x_2110_; 
lean_dec(v_a_2102_);
lean_dec(v_a_2096_);
lean_dec(v_a_2092_);
lean_dec_ref(v_major_2090_);
lean_dec_ref(v_recursorInfo_2083_);
v___x_2110_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg(v_tacticName_2081_, v_mvarId_2080_, v___x_2100_, v_a_2085_, v_a_2086_, v_a_2087_, v_a_2088_);
return v___x_2110_;
}
}
else
{
lean_object* v_a_2111_; lean_object* v___x_2113_; uint8_t v_isShared_2114_; uint8_t v_isSharedCheck_2118_; 
lean_dec_ref(v___x_2100_);
lean_dec(v_a_2096_);
lean_dec(v_a_2092_);
lean_dec_ref(v_major_2090_);
lean_dec_ref(v_recursorInfo_2083_);
lean_dec(v_tacticName_2081_);
lean_dec(v_mvarId_2080_);
v_a_2111_ = lean_ctor_get(v___x_2101_, 0);
v_isSharedCheck_2118_ = !lean_is_exclusive(v___x_2101_);
if (v_isSharedCheck_2118_ == 0)
{
v___x_2113_ = v___x_2101_;
v_isShared_2114_ = v_isSharedCheck_2118_;
goto v_resetjp_2112_;
}
else
{
lean_inc(v_a_2111_);
lean_dec(v___x_2101_);
v___x_2113_ = lean_box(0);
v_isShared_2114_ = v_isSharedCheck_2118_;
goto v_resetjp_2112_;
}
v_resetjp_2112_:
{
lean_object* v___x_2116_; 
if (v_isShared_2114_ == 0)
{
v___x_2116_ = v___x_2113_;
goto v_reusejp_2115_;
}
else
{
lean_object* v_reuseFailAlloc_2117_; 
v_reuseFailAlloc_2117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2117_, 0, v_a_2111_);
v___x_2116_ = v_reuseFailAlloc_2117_;
goto v_reusejp_2115_;
}
v_reusejp_2115_:
{
return v___x_2116_;
}
}
}
}
else
{
lean_object* v_a_2119_; lean_object* v___x_2121_; uint8_t v_isShared_2122_; uint8_t v_isSharedCheck_2126_; 
lean_dec(v_a_2096_);
lean_dec(v_a_2092_);
lean_dec_ref(v_major_2090_);
lean_dec_ref(v_recursorInfo_2083_);
lean_dec(v_tacticName_2081_);
lean_dec(v_mvarId_2080_);
v_a_2119_ = lean_ctor_get(v___x_2097_, 0);
v_isSharedCheck_2126_ = !lean_is_exclusive(v___x_2097_);
if (v_isSharedCheck_2126_ == 0)
{
v___x_2121_ = v___x_2097_;
v_isShared_2122_ = v_isSharedCheck_2126_;
goto v_resetjp_2120_;
}
else
{
lean_inc(v_a_2119_);
lean_dec(v___x_2097_);
v___x_2121_ = lean_box(0);
v_isShared_2122_ = v_isSharedCheck_2126_;
goto v_resetjp_2120_;
}
v_resetjp_2120_:
{
lean_object* v___x_2124_; 
if (v_isShared_2122_ == 0)
{
v___x_2124_ = v___x_2121_;
goto v_reusejp_2123_;
}
else
{
lean_object* v_reuseFailAlloc_2125_; 
v_reuseFailAlloc_2125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2125_, 0, v_a_2119_);
v___x_2124_ = v_reuseFailAlloc_2125_;
goto v_reusejp_2123_;
}
v_reusejp_2123_:
{
return v___x_2124_;
}
}
}
}
else
{
lean_object* v_a_2127_; lean_object* v___x_2129_; uint8_t v_isShared_2130_; uint8_t v_isSharedCheck_2134_; 
lean_dec(v_a_2092_);
lean_dec_ref(v_major_2090_);
lean_dec_ref(v_recursorInfo_2083_);
lean_dec(v_majorFVarId_2082_);
lean_dec(v_tacticName_2081_);
lean_dec(v_mvarId_2080_);
v_a_2127_ = lean_ctor_get(v___x_2095_, 0);
v_isSharedCheck_2134_ = !lean_is_exclusive(v___x_2095_);
if (v_isSharedCheck_2134_ == 0)
{
v___x_2129_ = v___x_2095_;
v_isShared_2130_ = v_isSharedCheck_2134_;
goto v_resetjp_2128_;
}
else
{
lean_inc(v_a_2127_);
lean_dec(v___x_2095_);
v___x_2129_ = lean_box(0);
v_isShared_2130_ = v_isSharedCheck_2134_;
goto v_resetjp_2128_;
}
v_resetjp_2128_:
{
lean_object* v___x_2132_; 
if (v_isShared_2130_ == 0)
{
v___x_2132_ = v___x_2129_;
goto v_reusejp_2131_;
}
else
{
lean_object* v_reuseFailAlloc_2133_; 
v_reuseFailAlloc_2133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2133_, 0, v_a_2127_);
v___x_2132_ = v_reuseFailAlloc_2133_;
goto v_reusejp_2131_;
}
v_reusejp_2131_:
{
return v___x_2132_;
}
}
}
}
else
{
lean_object* v_a_2135_; lean_object* v___x_2137_; uint8_t v_isShared_2138_; uint8_t v_isSharedCheck_2142_; 
lean_dec(v_a_2092_);
lean_dec_ref(v_major_2090_);
lean_dec_ref(v_recursorInfo_2083_);
lean_dec(v_majorFVarId_2082_);
lean_dec(v_tacticName_2081_);
lean_dec(v_mvarId_2080_);
v_a_2135_ = lean_ctor_get(v___x_2093_, 0);
v_isSharedCheck_2142_ = !lean_is_exclusive(v___x_2093_);
if (v_isSharedCheck_2142_ == 0)
{
v___x_2137_ = v___x_2093_;
v_isShared_2138_ = v_isSharedCheck_2142_;
goto v_resetjp_2136_;
}
else
{
lean_inc(v_a_2135_);
lean_dec(v___x_2093_);
v___x_2137_ = lean_box(0);
v_isShared_2138_ = v_isSharedCheck_2142_;
goto v_resetjp_2136_;
}
v_resetjp_2136_:
{
lean_object* v___x_2140_; 
if (v_isShared_2138_ == 0)
{
v___x_2140_ = v___x_2137_;
goto v_reusejp_2139_;
}
else
{
lean_object* v_reuseFailAlloc_2141_; 
v_reuseFailAlloc_2141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2141_, 0, v_a_2135_);
v___x_2140_ = v_reuseFailAlloc_2141_;
goto v_reusejp_2139_;
}
v_reusejp_2139_:
{
return v___x_2140_;
}
}
}
}
else
{
lean_dec_ref(v_major_2090_);
lean_dec_ref(v_recursorInfo_2083_);
lean_dec(v_majorFVarId_2082_);
lean_dec(v_tacticName_2081_);
lean_dec(v_mvarId_2080_);
return v___x_2091_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkRecursorAppPrefix___boxed(lean_object* v_mvarId_2143_, lean_object* v_tacticName_2144_, lean_object* v_majorFVarId_2145_, lean_object* v_recursorInfo_2146_, lean_object* v_indices_2147_, lean_object* v_a_2148_, lean_object* v_a_2149_, lean_object* v_a_2150_, lean_object* v_a_2151_, lean_object* v_a_2152_){
_start:
{
lean_object* v_res_2153_; 
v_res_2153_ = l_Lean_Meta_mkRecursorAppPrefix(v_mvarId_2143_, v_tacticName_2144_, v_majorFVarId_2145_, v_recursorInfo_2146_, v_indices_2147_, v_a_2148_, v_a_2149_, v_a_2150_, v_a_2151_);
lean_dec(v_a_2151_);
lean_dec_ref(v_a_2150_);
lean_dec(v_a_2149_);
lean_dec_ref(v_a_2148_);
lean_dec_ref(v_indices_2147_);
return v_res_2153_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1(lean_object* v_00_u03b1_2154_, lean_object* v_name_2155_, lean_object* v_msg_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_){
_start:
{
lean_object* v___x_2162_; 
v___x_2162_ = l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1___redArg(v_name_2155_, v_msg_2156_, v___y_2157_, v___y_2158_, v___y_2159_, v___y_2160_);
return v___x_2162_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1___boxed(lean_object* v_00_u03b1_2163_, lean_object* v_name_2164_, lean_object* v_msg_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_){
_start:
{
lean_object* v_res_2171_; 
v_res_2171_ = l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1(v_00_u03b1_2163_, v_name_2164_, v_msg_2165_, v___y_2166_, v___y_2167_, v___y_2168_, v___y_2169_);
lean_dec(v___y_2169_);
lean_dec_ref(v___y_2168_);
lean_dec(v___y_2167_);
lean_dec_ref(v___y_2166_);
return v_res_2171_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___redArg(lean_object* v_mvarId_2172_, lean_object* v_x_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_){
_start:
{
lean_object* v___x_2179_; 
v___x_2179_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_2172_, v_x_2173_, v___y_2174_, v___y_2175_, v___y_2176_, v___y_2177_);
if (lean_obj_tag(v___x_2179_) == 0)
{
lean_object* v_a_2180_; lean_object* v___x_2182_; uint8_t v_isShared_2183_; uint8_t v_isSharedCheck_2187_; 
v_a_2180_ = lean_ctor_get(v___x_2179_, 0);
v_isSharedCheck_2187_ = !lean_is_exclusive(v___x_2179_);
if (v_isSharedCheck_2187_ == 0)
{
v___x_2182_ = v___x_2179_;
v_isShared_2183_ = v_isSharedCheck_2187_;
goto v_resetjp_2181_;
}
else
{
lean_inc(v_a_2180_);
lean_dec(v___x_2179_);
v___x_2182_ = lean_box(0);
v_isShared_2183_ = v_isSharedCheck_2187_;
goto v_resetjp_2181_;
}
v_resetjp_2181_:
{
lean_object* v___x_2185_; 
if (v_isShared_2183_ == 0)
{
v___x_2185_ = v___x_2182_;
goto v_reusejp_2184_;
}
else
{
lean_object* v_reuseFailAlloc_2186_; 
v_reuseFailAlloc_2186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2186_, 0, v_a_2180_);
v___x_2185_ = v_reuseFailAlloc_2186_;
goto v_reusejp_2184_;
}
v_reusejp_2184_:
{
return v___x_2185_;
}
}
}
else
{
lean_object* v_a_2188_; lean_object* v___x_2190_; uint8_t v_isShared_2191_; uint8_t v_isSharedCheck_2195_; 
v_a_2188_ = lean_ctor_get(v___x_2179_, 0);
v_isSharedCheck_2195_ = !lean_is_exclusive(v___x_2179_);
if (v_isSharedCheck_2195_ == 0)
{
v___x_2190_ = v___x_2179_;
v_isShared_2191_ = v_isSharedCheck_2195_;
goto v_resetjp_2189_;
}
else
{
lean_inc(v_a_2188_);
lean_dec(v___x_2179_);
v___x_2190_ = lean_box(0);
v_isShared_2191_ = v_isSharedCheck_2195_;
goto v_resetjp_2189_;
}
v_resetjp_2189_:
{
lean_object* v___x_2193_; 
if (v_isShared_2191_ == 0)
{
v___x_2193_ = v___x_2190_;
goto v_reusejp_2192_;
}
else
{
lean_object* v_reuseFailAlloc_2194_; 
v_reuseFailAlloc_2194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2194_, 0, v_a_2188_);
v___x_2193_ = v_reuseFailAlloc_2194_;
goto v_reusejp_2192_;
}
v_reusejp_2192_:
{
return v___x_2193_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___redArg___boxed(lean_object* v_mvarId_2196_, lean_object* v_x_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_){
_start:
{
lean_object* v_res_2203_; 
v_res_2203_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___redArg(v_mvarId_2196_, v_x_2197_, v___y_2198_, v___y_2199_, v___y_2200_, v___y_2201_);
lean_dec(v___y_2201_);
lean_dec_ref(v___y_2200_);
lean_dec(v___y_2199_);
lean_dec_ref(v___y_2198_);
return v_res_2203_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3(lean_object* v_00_u03b1_2204_, lean_object* v_mvarId_2205_, lean_object* v_x_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_){
_start:
{
lean_object* v___x_2212_; 
v___x_2212_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___redArg(v_mvarId_2205_, v_x_2206_, v___y_2207_, v___y_2208_, v___y_2209_, v___y_2210_);
return v___x_2212_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___boxed(lean_object* v_00_u03b1_2213_, lean_object* v_mvarId_2214_, lean_object* v_x_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_){
_start:
{
lean_object* v_res_2221_; 
v_res_2221_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3(v_00_u03b1_2213_, v_mvarId_2214_, v_x_2215_, v___y_2216_, v___y_2217_, v___y_2218_, v___y_2219_);
lean_dec(v___y_2219_);
lean_dec_ref(v___y_2218_);
lean_dec(v___y_2217_);
lean_dec_ref(v___y_2216_);
return v_res_2221_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_induction_spec__2(lean_object* v_fst_2222_, lean_object* v_as_2223_, size_t v_sz_2224_, size_t v_i_2225_, lean_object* v_b_2226_){
_start:
{
uint8_t v___x_2227_; 
v___x_2227_ = lean_usize_dec_lt(v_i_2225_, v_sz_2224_);
if (v___x_2227_ == 0)
{
return v_b_2226_;
}
else
{
lean_object* v_fst_2228_; lean_object* v_snd_2229_; lean_object* v___x_2231_; uint8_t v_isShared_2232_; uint8_t v_isSharedCheck_2247_; 
v_fst_2228_ = lean_ctor_get(v_b_2226_, 0);
v_snd_2229_ = lean_ctor_get(v_b_2226_, 1);
v_isSharedCheck_2247_ = !lean_is_exclusive(v_b_2226_);
if (v_isSharedCheck_2247_ == 0)
{
v___x_2231_ = v_b_2226_;
v_isShared_2232_ = v_isSharedCheck_2247_;
goto v_resetjp_2230_;
}
else
{
lean_inc(v_snd_2229_);
lean_inc(v_fst_2228_);
lean_dec(v_b_2226_);
v___x_2231_ = lean_box(0);
v_isShared_2232_ = v_isSharedCheck_2247_;
goto v_resetjp_2230_;
}
v_resetjp_2230_:
{
lean_object* v___x_2233_; lean_object* v_a_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2242_; 
v___x_2233_ = lean_box(0);
v_a_2234_ = lean_array_uget_borrowed(v_as_2223_, v_i_2225_);
v___x_2235_ = l_Lean_Expr_fvarId_x21(v_a_2234_);
v___x_2236_ = lean_array_get_borrowed(v___x_2233_, v_fst_2222_, v_snd_2229_);
lean_inc(v___x_2236_);
v___x_2237_ = l_Lean_mkFVar(v___x_2236_);
v___x_2238_ = l_Lean_Meta_FVarSubst_insert(v_fst_2228_, v___x_2235_, v___x_2237_);
v___x_2239_ = lean_unsigned_to_nat(1u);
v___x_2240_ = lean_nat_add(v_snd_2229_, v___x_2239_);
lean_dec(v_snd_2229_);
if (v_isShared_2232_ == 0)
{
lean_ctor_set(v___x_2231_, 1, v___x_2240_);
lean_ctor_set(v___x_2231_, 0, v___x_2238_);
v___x_2242_ = v___x_2231_;
goto v_reusejp_2241_;
}
else
{
lean_object* v_reuseFailAlloc_2246_; 
v_reuseFailAlloc_2246_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2246_, 0, v___x_2238_);
lean_ctor_set(v_reuseFailAlloc_2246_, 1, v___x_2240_);
v___x_2242_ = v_reuseFailAlloc_2246_;
goto v_reusejp_2241_;
}
v_reusejp_2241_:
{
size_t v___x_2243_; size_t v___x_2244_; 
v___x_2243_ = ((size_t)1ULL);
v___x_2244_ = lean_usize_add(v_i_2225_, v___x_2243_);
v_i_2225_ = v___x_2244_;
v_b_2226_ = v___x_2242_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_induction_spec__2___boxed(lean_object* v_fst_2248_, lean_object* v_as_2249_, lean_object* v_sz_2250_, lean_object* v_i_2251_, lean_object* v_b_2252_){
_start:
{
size_t v_sz_boxed_2253_; size_t v_i_boxed_2254_; lean_object* v_res_2255_; 
v_sz_boxed_2253_ = lean_unbox_usize(v_sz_2250_);
lean_dec(v_sz_2250_);
v_i_boxed_2254_ = lean_unbox_usize(v_i_2251_);
lean_dec(v_i_2251_);
v_res_2255_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_induction_spec__2(v_fst_2248_, v_as_2249_, v_sz_boxed_2253_, v_i_boxed_2254_, v_b_2252_);
lean_dec_ref(v_as_2249_);
lean_dec_ref(v_fst_2248_);
return v_res_2255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4___lam__0(lean_object* v_snd_2256_, lean_object* v___x_2257_, lean_object* v_fst_2258_, lean_object* v_a_2259_, lean_object* v___x_2260_, lean_object* v_givenNames_2261_, lean_object* v_fst_2262_, lean_object* v___x_2263_, lean_object* v_fst_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_){
_start:
{
lean_object* v___x_2270_; 
lean_inc_ref(v_a_2259_);
lean_inc(v_snd_2256_);
v___x_2270_ = l_Lean_Meta_mkRecursorAppPrefix(v_snd_2256_, v___x_2257_, v_fst_2258_, v_a_2259_, v___x_2260_, v___y_2265_, v___y_2266_, v___y_2267_, v___y_2268_);
if (lean_obj_tag(v___x_2270_) == 0)
{
lean_object* v_a_2271_; lean_object* v___x_2272_; 
v_a_2271_ = lean_ctor_get(v___x_2270_, 0);
lean_inc(v_a_2271_);
lean_dec_ref_known(v___x_2270_, 1);
v___x_2272_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize(v_snd_2256_, v_givenNames_2261_, v_a_2259_, v_fst_2262_, v___x_2263_, v___x_2260_, v_fst_2264_, v_a_2271_, v___y_2265_, v___y_2266_, v___y_2267_, v___y_2268_);
lean_dec_ref(v_a_2259_);
return v___x_2272_;
}
else
{
lean_object* v_a_2273_; lean_object* v___x_2275_; uint8_t v_isShared_2276_; uint8_t v_isSharedCheck_2280_; 
lean_dec(v_fst_2264_);
lean_dec_ref(v___x_2263_);
lean_dec_ref(v_a_2259_);
lean_dec(v_snd_2256_);
v_a_2273_ = lean_ctor_get(v___x_2270_, 0);
v_isSharedCheck_2280_ = !lean_is_exclusive(v___x_2270_);
if (v_isSharedCheck_2280_ == 0)
{
v___x_2275_ = v___x_2270_;
v_isShared_2276_ = v_isSharedCheck_2280_;
goto v_resetjp_2274_;
}
else
{
lean_inc(v_a_2273_);
lean_dec(v___x_2270_);
v___x_2275_ = lean_box(0);
v_isShared_2276_ = v_isSharedCheck_2280_;
goto v_resetjp_2274_;
}
v_resetjp_2274_:
{
lean_object* v___x_2278_; 
if (v_isShared_2276_ == 0)
{
v___x_2278_ = v___x_2275_;
goto v_reusejp_2277_;
}
else
{
lean_object* v_reuseFailAlloc_2279_; 
v_reuseFailAlloc_2279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2279_, 0, v_a_2273_);
v___x_2278_ = v_reuseFailAlloc_2279_;
goto v_reusejp_2277_;
}
v_reusejp_2277_:
{
return v___x_2278_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4___lam__0___boxed(lean_object* v_snd_2281_, lean_object* v___x_2282_, lean_object* v_fst_2283_, lean_object* v_a_2284_, lean_object* v___x_2285_, lean_object* v_givenNames_2286_, lean_object* v_fst_2287_, lean_object* v___x_2288_, lean_object* v_fst_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_){
_start:
{
lean_object* v_res_2295_; 
v_res_2295_ = l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4___lam__0(v_snd_2281_, v___x_2282_, v_fst_2283_, v_a_2284_, v___x_2285_, v_givenNames_2286_, v_fst_2287_, v___x_2288_, v_fst_2289_, v___y_2290_, v___y_2291_, v___y_2292_, v___y_2293_);
lean_dec(v___y_2293_);
lean_dec_ref(v___y_2292_);
lean_dec(v___y_2291_);
lean_dec_ref(v___y_2290_);
lean_dec_ref(v_fst_2287_);
lean_dec_ref(v_givenNames_2286_);
lean_dec_ref(v___x_2285_);
return v_res_2295_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_induction_spec__1(size_t v_sz_2296_, size_t v_i_2297_, lean_object* v_bs_2298_){
_start:
{
uint8_t v___x_2299_; 
v___x_2299_ = lean_usize_dec_lt(v_i_2297_, v_sz_2296_);
if (v___x_2299_ == 0)
{
return v_bs_2298_;
}
else
{
lean_object* v_v_2300_; lean_object* v___x_2301_; lean_object* v_bs_x27_2302_; lean_object* v___x_2303_; size_t v___x_2304_; size_t v___x_2305_; lean_object* v___x_2306_; 
v_v_2300_ = lean_array_uget(v_bs_2298_, v_i_2297_);
v___x_2301_ = lean_unsigned_to_nat(0u);
v_bs_x27_2302_ = lean_array_uset(v_bs_2298_, v_i_2297_, v___x_2301_);
v___x_2303_ = l_Lean_Expr_fvarId_x21(v_v_2300_);
lean_dec(v_v_2300_);
v___x_2304_ = ((size_t)1ULL);
v___x_2305_ = lean_usize_add(v_i_2297_, v___x_2304_);
v___x_2306_ = lean_array_uset(v_bs_x27_2302_, v_i_2297_, v___x_2303_);
v_i_2297_ = v___x_2305_;
v_bs_2298_ = v___x_2306_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_induction_spec__1___boxed(lean_object* v_sz_2308_, lean_object* v_i_2309_, lean_object* v_bs_2310_){
_start:
{
size_t v_sz_boxed_2311_; size_t v_i_boxed_2312_; lean_object* v_res_2313_; 
v_sz_boxed_2311_ = lean_unbox_usize(v_sz_2308_);
lean_dec(v_sz_2308_);
v_i_boxed_2312_ = lean_unbox_usize(v_i_2309_);
lean_dec(v_i_2309_);
v_res_2313_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_induction_spec__1(v_sz_boxed_2311_, v_i_boxed_2312_, v_bs_2310_);
return v_res_2313_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_MVarId_induction_spec__0(lean_object* v_majorTypeArgs_2314_, lean_object* v_val_2315_, lean_object* v_mvarId_2316_, lean_object* v_as_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_){
_start:
{
if (lean_obj_tag(v_as_2317_) == 0)
{
lean_object* v___x_2323_; lean_object* v___x_2324_; 
lean_dec(v_mvarId_2316_);
lean_dec_ref(v_val_2315_);
v___x_2323_ = lean_box(0);
v___x_2324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2324_, 0, v___x_2323_);
return v___x_2324_;
}
else
{
lean_object* v_head_2325_; 
v_head_2325_ = lean_ctor_get(v_as_2317_, 0);
lean_inc(v_head_2325_);
if (lean_obj_tag(v_head_2325_) == 0)
{
lean_object* v_tail_2326_; 
v_tail_2326_ = lean_ctor_get(v_as_2317_, 1);
lean_inc(v_tail_2326_);
lean_dec_ref_known(v_as_2317_, 2);
v_as_2317_ = v_tail_2326_;
goto _start;
}
else
{
lean_object* v_tail_2328_; lean_object* v___x_2330_; uint8_t v_isShared_2331_; uint8_t v_isSharedCheck_2351_; 
v_tail_2328_ = lean_ctor_get(v_as_2317_, 1);
v_isSharedCheck_2351_ = !lean_is_exclusive(v_as_2317_);
if (v_isSharedCheck_2351_ == 0)
{
lean_object* v_unused_2352_; 
v_unused_2352_ = lean_ctor_get(v_as_2317_, 0);
lean_dec(v_unused_2352_);
v___x_2330_ = v_as_2317_;
v_isShared_2331_ = v_isSharedCheck_2351_;
goto v_resetjp_2329_;
}
else
{
lean_inc(v_tail_2328_);
lean_dec(v_as_2317_);
v___x_2330_ = lean_box(0);
v_isShared_2331_ = v_isSharedCheck_2351_;
goto v_resetjp_2329_;
}
v_resetjp_2329_:
{
lean_object* v_val_2332_; lean_object* v___x_2334_; uint8_t v_isShared_2335_; uint8_t v_isSharedCheck_2350_; 
v_val_2332_ = lean_ctor_get(v_head_2325_, 0);
v_isSharedCheck_2350_ = !lean_is_exclusive(v_head_2325_);
if (v_isSharedCheck_2350_ == 0)
{
v___x_2334_ = v_head_2325_;
v_isShared_2335_ = v_isSharedCheck_2350_;
goto v_resetjp_2333_;
}
else
{
lean_inc(v_val_2332_);
lean_dec(v_head_2325_);
v___x_2334_ = lean_box(0);
v_isShared_2335_ = v_isSharedCheck_2350_;
goto v_resetjp_2333_;
}
v_resetjp_2333_:
{
lean_object* v___x_2336_; uint8_t v___x_2337_; 
v___x_2336_ = lean_array_get_size(v_majorTypeArgs_2314_);
v___x_2337_ = lean_nat_dec_le(v___x_2336_, v_val_2332_);
lean_dec(v_val_2332_);
if (v___x_2337_ == 0)
{
lean_del_object(v___x_2334_);
lean_del_object(v___x_2330_);
v_as_2317_ = v_tail_2328_;
goto _start;
}
else
{
lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2343_; 
v___x_2339_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1));
v___x_2340_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__5, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__5);
lean_inc_ref(v_val_2315_);
v___x_2341_ = l_Lean_indentExpr(v_val_2315_);
if (v_isShared_2331_ == 0)
{
lean_ctor_set_tag(v___x_2330_, 7);
lean_ctor_set(v___x_2330_, 1, v___x_2341_);
lean_ctor_set(v___x_2330_, 0, v___x_2340_);
v___x_2343_ = v___x_2330_;
goto v_reusejp_2342_;
}
else
{
lean_object* v_reuseFailAlloc_2349_; 
v_reuseFailAlloc_2349_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2349_, 0, v___x_2340_);
lean_ctor_set(v_reuseFailAlloc_2349_, 1, v___x_2341_);
v___x_2343_ = v_reuseFailAlloc_2349_;
goto v_reusejp_2342_;
}
v_reusejp_2342_:
{
lean_object* v___x_2345_; 
if (v_isShared_2335_ == 0)
{
lean_ctor_set(v___x_2334_, 0, v___x_2343_);
v___x_2345_ = v___x_2334_;
goto v_reusejp_2344_;
}
else
{
lean_object* v_reuseFailAlloc_2348_; 
v_reuseFailAlloc_2348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2348_, 0, v___x_2343_);
v___x_2345_ = v_reuseFailAlloc_2348_;
goto v_reusejp_2344_;
}
v_reusejp_2344_:
{
lean_object* v___x_2346_; 
lean_inc(v_mvarId_2316_);
v___x_2346_ = l_Lean_Meta_throwTacticEx___redArg(v___x_2339_, v_mvarId_2316_, v___x_2345_, v___y_2318_, v___y_2319_, v___y_2320_, v___y_2321_);
if (lean_obj_tag(v___x_2346_) == 0)
{
lean_dec_ref_known(v___x_2346_, 1);
v_as_2317_ = v_tail_2328_;
goto _start;
}
else
{
lean_dec(v_tail_2328_);
lean_dec(v_mvarId_2316_);
lean_dec_ref(v_val_2315_);
return v___x_2346_;
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
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_MVarId_induction_spec__0___boxed(lean_object* v_majorTypeArgs_2353_, lean_object* v_val_2354_, lean_object* v_mvarId_2355_, lean_object* v_as_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_){
_start:
{
lean_object* v_res_2362_; 
v_res_2362_ = l_List_forM___at___00Lean_MVarId_induction_spec__0(v_majorTypeArgs_2353_, v_val_2354_, v_mvarId_2355_, v_as_2356_, v___y_2357_, v___y_2358_, v___y_2359_, v___y_2360_);
lean_dec(v___y_2360_);
lean_dec_ref(v___y_2359_);
lean_dec(v___y_2358_);
lean_dec_ref(v___y_2357_);
lean_dec_ref(v_majorTypeArgs_2353_);
return v_res_2362_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__1(void){
_start:
{
lean_object* v___x_2364_; lean_object* v___x_2365_; 
v___x_2364_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__0));
v___x_2365_ = l_Lean_stringToMessageData(v___x_2364_);
return v___x_2365_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__3(void){
_start:
{
lean_object* v___x_2367_; lean_object* v___x_2368_; 
v___x_2367_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__2));
v___x_2368_ = l_Lean_stringToMessageData(v___x_2367_);
return v___x_2368_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__5(void){
_start:
{
lean_object* v___x_2370_; lean_object* v___x_2371_; 
v___x_2370_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__4));
v___x_2371_ = l_Lean_stringToMessageData(v___x_2370_);
return v___x_2371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4(lean_object* v_a_2372_, lean_object* v_val_2373_, lean_object* v_mvarId_2374_, lean_object* v_majorFVarId_2375_, lean_object* v_givenNames_2376_, lean_object* v_recursorName_2377_, lean_object* v_x_2378_, lean_object* v_x_2379_, lean_object* v_x_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_){
_start:
{
if (lean_obj_tag(v_x_2378_) == 5)
{
lean_object* v_fn_2386_; lean_object* v_arg_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; 
v_fn_2386_ = lean_ctor_get(v_x_2378_, 0);
lean_inc_ref(v_fn_2386_);
v_arg_2387_ = lean_ctor_get(v_x_2378_, 1);
lean_inc_ref(v_arg_2387_);
lean_dec_ref_known(v_x_2378_, 2);
v___x_2388_ = lean_array_set(v_x_2379_, v_x_2380_, v_arg_2387_);
v___x_2389_ = lean_unsigned_to_nat(1u);
v___x_2390_ = lean_nat_sub(v_x_2380_, v___x_2389_);
lean_dec(v_x_2380_);
v_x_2378_ = v_fn_2386_;
v_x_2379_ = v___x_2388_;
v_x_2380_ = v___x_2390_;
goto _start;
}
else
{
uint8_t v_depElim_2392_; lean_object* v_paramsPos_2393_; lean_object* v___x_2394_; lean_object* v___y_2396_; lean_object* v___y_2397_; lean_object* v___y_2398_; lean_object* v___y_2399_; lean_object* v___y_2400_; lean_object* v___y_2401_; lean_object* v___y_2402_; size_t v___y_2403_; lean_object* v___y_2404_; lean_object* v___y_2405_; lean_object* v___y_2406_; lean_object* v___y_2407_; lean_object* v_cls_2412_; lean_object* v___x_2413_; 
lean_dec(v_x_2380_);
lean_dec_ref(v_x_2378_);
v_depElim_2392_ = lean_ctor_get_uint8(v_a_2372_, sizeof(void*)*8);
v_paramsPos_2393_ = lean_ctor_get(v_a_2372_, 5);
v___x_2394_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1));
v_cls_2412_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__2));
lean_inc(v_paramsPos_2393_);
lean_inc(v_mvarId_2374_);
lean_inc_ref(v_val_2373_);
v___x_2413_ = l_List_forM___at___00Lean_MVarId_induction_spec__0(v_x_2379_, v_val_2373_, v_mvarId_2374_, v_paramsPos_2393_, v___y_2381_, v___y_2382_, v___y_2383_, v___y_2384_);
lean_dec_ref(v_x_2379_);
if (lean_obj_tag(v___x_2413_) == 0)
{
lean_object* v___x_2414_; 
lean_dec_ref_known(v___x_2413_, 1);
lean_inc_ref(v_a_2372_);
lean_inc(v_mvarId_2374_);
v___x_2414_ = l_Lean_Meta_getMajorTypeIndices(v_mvarId_2374_, v___x_2394_, v_a_2372_, v_val_2373_, v___y_2381_, v___y_2382_, v___y_2383_, v___y_2384_);
if (lean_obj_tag(v___x_2414_) == 0)
{
lean_object* v_a_2415_; lean_object* v___y_2417_; lean_object* v___y_2418_; lean_object* v___y_2419_; lean_object* v___y_2420_; lean_object* v___x_2504_; 
v_a_2415_ = lean_ctor_get(v___x_2414_, 0);
lean_inc(v_a_2415_);
lean_dec_ref_known(v___x_2414_, 1);
lean_inc(v_mvarId_2374_);
v___x_2504_ = l_Lean_MVarId_getType(v_mvarId_2374_, v___y_2381_, v___y_2382_, v___y_2383_, v___y_2384_);
if (lean_obj_tag(v___x_2504_) == 0)
{
if (v_depElim_2392_ == 0)
{
lean_object* v_a_2505_; lean_object* v___x_2506_; lean_object* v_a_2507_; lean_object* v___x_2509_; uint8_t v_isShared_2510_; uint8_t v_isSharedCheck_2529_; 
v_a_2505_ = lean_ctor_get(v___x_2504_, 0);
lean_inc(v_a_2505_);
lean_dec_ref_known(v___x_2504_, 1);
lean_inc(v_majorFVarId_2375_);
v___x_2506_ = l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2___redArg(v_a_2505_, v_majorFVarId_2375_, v___y_2382_);
v_a_2507_ = lean_ctor_get(v___x_2506_, 0);
v_isSharedCheck_2529_ = !lean_is_exclusive(v___x_2506_);
if (v_isSharedCheck_2529_ == 0)
{
v___x_2509_ = v___x_2506_;
v_isShared_2510_ = v_isSharedCheck_2529_;
goto v_resetjp_2508_;
}
else
{
lean_inc(v_a_2507_);
lean_dec(v___x_2506_);
v___x_2509_ = lean_box(0);
v_isShared_2510_ = v_isSharedCheck_2529_;
goto v_resetjp_2508_;
}
v_resetjp_2508_:
{
uint8_t v___x_2511_; 
v___x_2511_ = lean_unbox(v_a_2507_);
lean_dec(v_a_2507_);
if (v___x_2511_ == 0)
{
lean_del_object(v___x_2509_);
lean_dec(v_recursorName_2377_);
v___y_2417_ = v___y_2381_;
v___y_2418_ = v___y_2382_;
v___y_2419_ = v___y_2383_;
v___y_2420_ = v___y_2384_;
goto v___jp_2416_;
}
else
{
lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2518_; 
v___x_2512_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__3, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__3);
v___x_2513_ = l_Lean_MessageData_ofName(v_recursorName_2377_);
v___x_2514_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2514_, 0, v___x_2512_);
lean_ctor_set(v___x_2514_, 1, v___x_2513_);
v___x_2515_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__5, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__5_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__5);
v___x_2516_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2516_, 0, v___x_2514_);
lean_ctor_set(v___x_2516_, 1, v___x_2515_);
if (v_isShared_2510_ == 0)
{
lean_ctor_set_tag(v___x_2509_, 1);
lean_ctor_set(v___x_2509_, 0, v___x_2516_);
v___x_2518_ = v___x_2509_;
goto v_reusejp_2517_;
}
else
{
lean_object* v_reuseFailAlloc_2528_; 
v_reuseFailAlloc_2528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2528_, 0, v___x_2516_);
v___x_2518_ = v_reuseFailAlloc_2528_;
goto v_reusejp_2517_;
}
v_reusejp_2517_:
{
lean_object* v___x_2519_; 
lean_inc(v_mvarId_2374_);
v___x_2519_ = l_Lean_Meta_throwTacticEx___redArg(v___x_2394_, v_mvarId_2374_, v___x_2518_, v___y_2381_, v___y_2382_, v___y_2383_, v___y_2384_);
if (lean_obj_tag(v___x_2519_) == 0)
{
lean_dec_ref_known(v___x_2519_, 1);
v___y_2417_ = v___y_2381_;
v___y_2418_ = v___y_2382_;
v___y_2419_ = v___y_2383_;
v___y_2420_ = v___y_2384_;
goto v___jp_2416_;
}
else
{
lean_object* v_a_2520_; lean_object* v___x_2522_; uint8_t v_isShared_2523_; uint8_t v_isSharedCheck_2527_; 
lean_dec(v_a_2415_);
lean_dec_ref(v_givenNames_2376_);
lean_dec(v_majorFVarId_2375_);
lean_dec(v_mvarId_2374_);
lean_dec_ref(v_a_2372_);
v_a_2520_ = lean_ctor_get(v___x_2519_, 0);
v_isSharedCheck_2527_ = !lean_is_exclusive(v___x_2519_);
if (v_isSharedCheck_2527_ == 0)
{
v___x_2522_ = v___x_2519_;
v_isShared_2523_ = v_isSharedCheck_2527_;
goto v_resetjp_2521_;
}
else
{
lean_inc(v_a_2520_);
lean_dec(v___x_2519_);
v___x_2522_ = lean_box(0);
v_isShared_2523_ = v_isSharedCheck_2527_;
goto v_resetjp_2521_;
}
v_resetjp_2521_:
{
lean_object* v___x_2525_; 
if (v_isShared_2523_ == 0)
{
v___x_2525_ = v___x_2522_;
goto v_reusejp_2524_;
}
else
{
lean_object* v_reuseFailAlloc_2526_; 
v_reuseFailAlloc_2526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2526_, 0, v_a_2520_);
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
}
}
}
else
{
lean_dec_ref_known(v___x_2504_, 1);
lean_dec(v_recursorName_2377_);
v___y_2417_ = v___y_2381_;
v___y_2418_ = v___y_2382_;
v___y_2419_ = v___y_2383_;
v___y_2420_ = v___y_2384_;
goto v___jp_2416_;
}
}
else
{
lean_object* v_a_2530_; lean_object* v___x_2532_; uint8_t v_isShared_2533_; uint8_t v_isSharedCheck_2537_; 
lean_dec(v_a_2415_);
lean_dec(v_recursorName_2377_);
lean_dec_ref(v_givenNames_2376_);
lean_dec(v_majorFVarId_2375_);
lean_dec(v_mvarId_2374_);
lean_dec_ref(v_a_2372_);
v_a_2530_ = lean_ctor_get(v___x_2504_, 0);
v_isSharedCheck_2537_ = !lean_is_exclusive(v___x_2504_);
if (v_isSharedCheck_2537_ == 0)
{
v___x_2532_ = v___x_2504_;
v_isShared_2533_ = v_isSharedCheck_2537_;
goto v_resetjp_2531_;
}
else
{
lean_inc(v_a_2530_);
lean_dec(v___x_2504_);
v___x_2532_ = lean_box(0);
v_isShared_2533_ = v_isSharedCheck_2537_;
goto v_resetjp_2531_;
}
v_resetjp_2531_:
{
lean_object* v___x_2535_; 
if (v_isShared_2533_ == 0)
{
v___x_2535_ = v___x_2532_;
goto v_reusejp_2534_;
}
else
{
lean_object* v_reuseFailAlloc_2536_; 
v_reuseFailAlloc_2536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2536_, 0, v_a_2530_);
v___x_2535_ = v_reuseFailAlloc_2536_;
goto v_reusejp_2534_;
}
v_reusejp_2534_:
{
return v___x_2535_;
}
}
}
v___jp_2416_:
{
size_t v_sz_2421_; size_t v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; uint8_t v___x_2425_; uint8_t v___x_2426_; lean_object* v___x_2427_; 
v_sz_2421_ = lean_array_size(v_a_2415_);
v___x_2422_ = ((size_t)0ULL);
lean_inc(v_a_2415_);
v___x_2423_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_induction_spec__1(v_sz_2421_, v___x_2422_, v_a_2415_);
lean_inc(v_majorFVarId_2375_);
v___x_2424_ = lean_array_push(v___x_2423_, v_majorFVarId_2375_);
v___x_2425_ = 1;
v___x_2426_ = 0;
v___x_2427_ = l_Lean_MVarId_revert(v_mvarId_2374_, v___x_2424_, v___x_2425_, v___x_2426_, v___y_2417_, v___y_2418_, v___y_2419_, v___y_2420_);
if (lean_obj_tag(v___x_2427_) == 0)
{
lean_object* v_a_2428_; lean_object* v_fst_2429_; lean_object* v_snd_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; 
v_a_2428_ = lean_ctor_get(v___x_2427_, 0);
lean_inc(v_a_2428_);
lean_dec_ref_known(v___x_2427_, 1);
v_fst_2429_ = lean_ctor_get(v_a_2428_, 0);
lean_inc(v_fst_2429_);
v_snd_2430_ = lean_ctor_get(v_a_2428_, 1);
lean_inc(v_snd_2430_);
lean_dec(v_a_2428_);
v___x_2431_ = lean_array_get_size(v_a_2415_);
v___x_2432_ = lean_box(0);
v___x_2433_ = l_Lean_Meta_introNCore(v_snd_2430_, v___x_2431_, v___x_2432_, v___x_2426_, v___x_2425_, v___y_2417_, v___y_2418_, v___y_2419_, v___y_2420_);
if (lean_obj_tag(v___x_2433_) == 0)
{
lean_object* v_a_2434_; lean_object* v_fst_2435_; lean_object* v_snd_2436_; lean_object* v___x_2437_; 
v_a_2434_ = lean_ctor_get(v___x_2433_, 0);
lean_inc(v_a_2434_);
lean_dec_ref_known(v___x_2433_, 1);
v_fst_2435_ = lean_ctor_get(v_a_2434_, 0);
lean_inc(v_fst_2435_);
v_snd_2436_ = lean_ctor_get(v_a_2434_, 1);
lean_inc(v_snd_2436_);
lean_dec(v_a_2434_);
v___x_2437_ = l_Lean_Meta_intro1Core(v_snd_2436_, v___x_2425_, v___y_2417_, v___y_2418_, v___y_2419_, v___y_2420_);
if (lean_obj_tag(v___x_2437_) == 0)
{
lean_object* v_a_2438_; lean_object* v_fst_2439_; lean_object* v_snd_2440_; lean_object* v___x_2442_; uint8_t v_isShared_2443_; uint8_t v_isSharedCheck_2479_; 
v_a_2438_ = lean_ctor_get(v___x_2437_, 0);
lean_inc(v_a_2438_);
lean_dec_ref_known(v___x_2437_, 1);
v_fst_2439_ = lean_ctor_get(v_a_2438_, 0);
v_snd_2440_ = lean_ctor_get(v_a_2438_, 1);
v_isSharedCheck_2479_ = !lean_is_exclusive(v_a_2438_);
if (v_isSharedCheck_2479_ == 0)
{
v___x_2442_ = v_a_2438_;
v_isShared_2443_ = v_isSharedCheck_2479_;
goto v_resetjp_2441_;
}
else
{
lean_inc(v_snd_2440_);
lean_inc(v_fst_2439_);
lean_dec(v_a_2438_);
v___x_2442_ = lean_box(0);
v_isShared_2443_ = v_isSharedCheck_2479_;
goto v_resetjp_2441_;
}
v_resetjp_2441_:
{
lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2449_; 
v___x_2444_ = lean_box(0);
lean_inc(v_fst_2439_);
v___x_2445_ = l_Lean_mkFVar(v_fst_2439_);
lean_inc_ref(v___x_2445_);
v___x_2446_ = l_Lean_Meta_FVarSubst_insert(v___x_2444_, v_majorFVarId_2375_, v___x_2445_);
v___x_2447_ = lean_unsigned_to_nat(0u);
if (v_isShared_2443_ == 0)
{
lean_ctor_set(v___x_2442_, 1, v___x_2447_);
lean_ctor_set(v___x_2442_, 0, v___x_2446_);
v___x_2449_ = v___x_2442_;
goto v_reusejp_2448_;
}
else
{
lean_object* v_reuseFailAlloc_2478_; 
v_reuseFailAlloc_2478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2478_, 0, v___x_2446_);
lean_ctor_set(v_reuseFailAlloc_2478_, 1, v___x_2447_);
v___x_2449_ = v_reuseFailAlloc_2478_;
goto v_reusejp_2448_;
}
v_reusejp_2448_:
{
lean_object* v___x_2450_; lean_object* v_toCold_2451_; lean_object* v_options_2452_; uint8_t v_hasTrace_2453_; 
v___x_2450_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_induction_spec__2(v_fst_2435_, v_a_2415_, v_sz_2421_, v___x_2422_, v___x_2449_);
lean_dec(v_a_2415_);
v_toCold_2451_ = lean_ctor_get(v___y_2419_, 0);
v_options_2452_ = lean_ctor_get(v_toCold_2451_, 2);
v_hasTrace_2453_ = lean_ctor_get_uint8(v_options_2452_, sizeof(void*)*1);
if (v_hasTrace_2453_ == 0)
{
lean_object* v_fst_2454_; 
v_fst_2454_ = lean_ctor_get(v___x_2450_, 0);
lean_inc(v_fst_2454_);
lean_dec_ref(v___x_2450_);
lean_inc(v_snd_2440_);
v___y_2396_ = v_fst_2429_;
v___y_2397_ = v_fst_2454_;
v___y_2398_ = v_snd_2440_;
v___y_2399_ = v_fst_2439_;
v___y_2400_ = v___x_2445_;
v___y_2401_ = v_snd_2440_;
v___y_2402_ = v_fst_2435_;
v___y_2403_ = v___x_2422_;
v___y_2404_ = v___y_2417_;
v___y_2405_ = v___y_2418_;
v___y_2406_ = v___y_2419_;
v___y_2407_ = v___y_2420_;
goto v___jp_2395_;
}
else
{
lean_object* v_fst_2455_; lean_object* v___x_2457_; uint8_t v_isShared_2458_; uint8_t v_isSharedCheck_2476_; 
v_fst_2455_ = lean_ctor_get(v___x_2450_, 0);
v_isSharedCheck_2476_ = !lean_is_exclusive(v___x_2450_);
if (v_isSharedCheck_2476_ == 0)
{
lean_object* v_unused_2477_; 
v_unused_2477_ = lean_ctor_get(v___x_2450_, 1);
lean_dec(v_unused_2477_);
v___x_2457_ = v___x_2450_;
v_isShared_2458_ = v_isSharedCheck_2476_;
goto v_resetjp_2456_;
}
else
{
lean_inc(v_fst_2455_);
lean_dec(v___x_2450_);
v___x_2457_ = lean_box(0);
v_isShared_2458_ = v_isSharedCheck_2476_;
goto v_resetjp_2456_;
}
v_resetjp_2456_:
{
lean_object* v_inheritedTraceOptions_2459_; lean_object* v___x_2460_; uint8_t v___x_2461_; 
v_inheritedTraceOptions_2459_ = lean_ctor_get(v_toCold_2451_, 11);
v___x_2460_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5);
v___x_2461_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2459_, v_options_2452_, v___x_2460_);
if (v___x_2461_ == 0)
{
lean_del_object(v___x_2457_);
lean_inc(v_snd_2440_);
v___y_2396_ = v_fst_2429_;
v___y_2397_ = v_fst_2455_;
v___y_2398_ = v_snd_2440_;
v___y_2399_ = v_fst_2439_;
v___y_2400_ = v___x_2445_;
v___y_2401_ = v_snd_2440_;
v___y_2402_ = v_fst_2435_;
v___y_2403_ = v___x_2422_;
v___y_2404_ = v___y_2417_;
v___y_2405_ = v___y_2418_;
v___y_2406_ = v___y_2419_;
v___y_2407_ = v___y_2420_;
goto v___jp_2395_;
}
else
{
lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2465_; 
v___x_2462_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__1);
lean_inc(v_snd_2440_);
v___x_2463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2463_, 0, v_snd_2440_);
if (v_isShared_2458_ == 0)
{
lean_ctor_set_tag(v___x_2457_, 7);
lean_ctor_set(v___x_2457_, 1, v___x_2463_);
lean_ctor_set(v___x_2457_, 0, v___x_2462_);
v___x_2465_ = v___x_2457_;
goto v_reusejp_2464_;
}
else
{
lean_object* v_reuseFailAlloc_2475_; 
v_reuseFailAlloc_2475_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2475_, 0, v___x_2462_);
lean_ctor_set(v_reuseFailAlloc_2475_, 1, v___x_2463_);
v___x_2465_ = v_reuseFailAlloc_2475_;
goto v_reusejp_2464_;
}
v_reusejp_2464_:
{
lean_object* v___x_2466_; 
v___x_2466_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1(v_cls_2412_, v___x_2465_, v___y_2417_, v___y_2418_, v___y_2419_, v___y_2420_);
if (lean_obj_tag(v___x_2466_) == 0)
{
lean_dec_ref_known(v___x_2466_, 1);
lean_inc(v_snd_2440_);
v___y_2396_ = v_fst_2429_;
v___y_2397_ = v_fst_2455_;
v___y_2398_ = v_snd_2440_;
v___y_2399_ = v_fst_2439_;
v___y_2400_ = v___x_2445_;
v___y_2401_ = v_snd_2440_;
v___y_2402_ = v_fst_2435_;
v___y_2403_ = v___x_2422_;
v___y_2404_ = v___y_2417_;
v___y_2405_ = v___y_2418_;
v___y_2406_ = v___y_2419_;
v___y_2407_ = v___y_2420_;
goto v___jp_2395_;
}
else
{
lean_object* v_a_2467_; lean_object* v___x_2469_; uint8_t v_isShared_2470_; uint8_t v_isSharedCheck_2474_; 
lean_dec(v_fst_2455_);
lean_dec_ref(v___x_2445_);
lean_dec(v_snd_2440_);
lean_dec(v_fst_2439_);
lean_dec(v_fst_2435_);
lean_dec(v_fst_2429_);
lean_dec_ref(v_givenNames_2376_);
lean_dec_ref(v_a_2372_);
v_a_2467_ = lean_ctor_get(v___x_2466_, 0);
v_isSharedCheck_2474_ = !lean_is_exclusive(v___x_2466_);
if (v_isSharedCheck_2474_ == 0)
{
v___x_2469_ = v___x_2466_;
v_isShared_2470_ = v_isSharedCheck_2474_;
goto v_resetjp_2468_;
}
else
{
lean_inc(v_a_2467_);
lean_dec(v___x_2466_);
v___x_2469_ = lean_box(0);
v_isShared_2470_ = v_isSharedCheck_2474_;
goto v_resetjp_2468_;
}
v_resetjp_2468_:
{
lean_object* v___x_2472_; 
if (v_isShared_2470_ == 0)
{
v___x_2472_ = v___x_2469_;
goto v_reusejp_2471_;
}
else
{
lean_object* v_reuseFailAlloc_2473_; 
v_reuseFailAlloc_2473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2473_, 0, v_a_2467_);
v___x_2472_ = v_reuseFailAlloc_2473_;
goto v_reusejp_2471_;
}
v_reusejp_2471_:
{
return v___x_2472_;
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
lean_object* v_a_2480_; lean_object* v___x_2482_; uint8_t v_isShared_2483_; uint8_t v_isSharedCheck_2487_; 
lean_dec(v_fst_2435_);
lean_dec(v_fst_2429_);
lean_dec(v_a_2415_);
lean_dec_ref(v_givenNames_2376_);
lean_dec(v_majorFVarId_2375_);
lean_dec_ref(v_a_2372_);
v_a_2480_ = lean_ctor_get(v___x_2437_, 0);
v_isSharedCheck_2487_ = !lean_is_exclusive(v___x_2437_);
if (v_isSharedCheck_2487_ == 0)
{
v___x_2482_ = v___x_2437_;
v_isShared_2483_ = v_isSharedCheck_2487_;
goto v_resetjp_2481_;
}
else
{
lean_inc(v_a_2480_);
lean_dec(v___x_2437_);
v___x_2482_ = lean_box(0);
v_isShared_2483_ = v_isSharedCheck_2487_;
goto v_resetjp_2481_;
}
v_resetjp_2481_:
{
lean_object* v___x_2485_; 
if (v_isShared_2483_ == 0)
{
v___x_2485_ = v___x_2482_;
goto v_reusejp_2484_;
}
else
{
lean_object* v_reuseFailAlloc_2486_; 
v_reuseFailAlloc_2486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2486_, 0, v_a_2480_);
v___x_2485_ = v_reuseFailAlloc_2486_;
goto v_reusejp_2484_;
}
v_reusejp_2484_:
{
return v___x_2485_;
}
}
}
}
else
{
lean_object* v_a_2488_; lean_object* v___x_2490_; uint8_t v_isShared_2491_; uint8_t v_isSharedCheck_2495_; 
lean_dec(v_fst_2429_);
lean_dec(v_a_2415_);
lean_dec_ref(v_givenNames_2376_);
lean_dec(v_majorFVarId_2375_);
lean_dec_ref(v_a_2372_);
v_a_2488_ = lean_ctor_get(v___x_2433_, 0);
v_isSharedCheck_2495_ = !lean_is_exclusive(v___x_2433_);
if (v_isSharedCheck_2495_ == 0)
{
v___x_2490_ = v___x_2433_;
v_isShared_2491_ = v_isSharedCheck_2495_;
goto v_resetjp_2489_;
}
else
{
lean_inc(v_a_2488_);
lean_dec(v___x_2433_);
v___x_2490_ = lean_box(0);
v_isShared_2491_ = v_isSharedCheck_2495_;
goto v_resetjp_2489_;
}
v_resetjp_2489_:
{
lean_object* v___x_2493_; 
if (v_isShared_2491_ == 0)
{
v___x_2493_ = v___x_2490_;
goto v_reusejp_2492_;
}
else
{
lean_object* v_reuseFailAlloc_2494_; 
v_reuseFailAlloc_2494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2494_, 0, v_a_2488_);
v___x_2493_ = v_reuseFailAlloc_2494_;
goto v_reusejp_2492_;
}
v_reusejp_2492_:
{
return v___x_2493_;
}
}
}
}
else
{
lean_object* v_a_2496_; lean_object* v___x_2498_; uint8_t v_isShared_2499_; uint8_t v_isSharedCheck_2503_; 
lean_dec(v_a_2415_);
lean_dec_ref(v_givenNames_2376_);
lean_dec(v_majorFVarId_2375_);
lean_dec_ref(v_a_2372_);
v_a_2496_ = lean_ctor_get(v___x_2427_, 0);
v_isSharedCheck_2503_ = !lean_is_exclusive(v___x_2427_);
if (v_isSharedCheck_2503_ == 0)
{
v___x_2498_ = v___x_2427_;
v_isShared_2499_ = v_isSharedCheck_2503_;
goto v_resetjp_2497_;
}
else
{
lean_inc(v_a_2496_);
lean_dec(v___x_2427_);
v___x_2498_ = lean_box(0);
v_isShared_2499_ = v_isSharedCheck_2503_;
goto v_resetjp_2497_;
}
v_resetjp_2497_:
{
lean_object* v___x_2501_; 
if (v_isShared_2499_ == 0)
{
v___x_2501_ = v___x_2498_;
goto v_reusejp_2500_;
}
else
{
lean_object* v_reuseFailAlloc_2502_; 
v_reuseFailAlloc_2502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2502_, 0, v_a_2496_);
v___x_2501_ = v_reuseFailAlloc_2502_;
goto v_reusejp_2500_;
}
v_reusejp_2500_:
{
return v___x_2501_;
}
}
}
}
}
else
{
lean_object* v_a_2538_; lean_object* v___x_2540_; uint8_t v_isShared_2541_; uint8_t v_isSharedCheck_2545_; 
lean_dec(v_recursorName_2377_);
lean_dec_ref(v_givenNames_2376_);
lean_dec(v_majorFVarId_2375_);
lean_dec(v_mvarId_2374_);
lean_dec_ref(v_a_2372_);
v_a_2538_ = lean_ctor_get(v___x_2414_, 0);
v_isSharedCheck_2545_ = !lean_is_exclusive(v___x_2414_);
if (v_isSharedCheck_2545_ == 0)
{
v___x_2540_ = v___x_2414_;
v_isShared_2541_ = v_isSharedCheck_2545_;
goto v_resetjp_2539_;
}
else
{
lean_inc(v_a_2538_);
lean_dec(v___x_2414_);
v___x_2540_ = lean_box(0);
v_isShared_2541_ = v_isSharedCheck_2545_;
goto v_resetjp_2539_;
}
v_resetjp_2539_:
{
lean_object* v___x_2543_; 
if (v_isShared_2541_ == 0)
{
v___x_2543_ = v___x_2540_;
goto v_reusejp_2542_;
}
else
{
lean_object* v_reuseFailAlloc_2544_; 
v_reuseFailAlloc_2544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2544_, 0, v_a_2538_);
v___x_2543_ = v_reuseFailAlloc_2544_;
goto v_reusejp_2542_;
}
v_reusejp_2542_:
{
return v___x_2543_;
}
}
}
}
else
{
lean_object* v_a_2546_; lean_object* v___x_2548_; uint8_t v_isShared_2549_; uint8_t v_isSharedCheck_2553_; 
lean_dec(v_recursorName_2377_);
lean_dec_ref(v_givenNames_2376_);
lean_dec(v_majorFVarId_2375_);
lean_dec(v_mvarId_2374_);
lean_dec_ref(v_val_2373_);
lean_dec_ref(v_a_2372_);
v_a_2546_ = lean_ctor_get(v___x_2413_, 0);
v_isSharedCheck_2553_ = !lean_is_exclusive(v___x_2413_);
if (v_isSharedCheck_2553_ == 0)
{
v___x_2548_ = v___x_2413_;
v_isShared_2549_ = v_isSharedCheck_2553_;
goto v_resetjp_2547_;
}
else
{
lean_inc(v_a_2546_);
lean_dec(v___x_2413_);
v___x_2548_ = lean_box(0);
v_isShared_2549_ = v_isSharedCheck_2553_;
goto v_resetjp_2547_;
}
v_resetjp_2547_:
{
lean_object* v___x_2551_; 
if (v_isShared_2549_ == 0)
{
v___x_2551_ = v___x_2548_;
goto v_reusejp_2550_;
}
else
{
lean_object* v_reuseFailAlloc_2552_; 
v_reuseFailAlloc_2552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2552_, 0, v_a_2546_);
v___x_2551_ = v_reuseFailAlloc_2552_;
goto v_reusejp_2550_;
}
v_reusejp_2550_:
{
return v___x_2551_;
}
}
}
v___jp_2395_:
{
size_t v_sz_2408_; lean_object* v___x_2409_; lean_object* v___f_2410_; lean_object* v___x_2411_; 
v_sz_2408_ = lean_array_size(v___y_2402_);
v___x_2409_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__3(v_sz_2408_, v___y_2403_, v___y_2402_);
v___f_2410_ = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4___lam__0___boxed), 14, 9);
lean_closure_set(v___f_2410_, 0, v___y_2398_);
lean_closure_set(v___f_2410_, 1, v___x_2394_);
lean_closure_set(v___f_2410_, 2, v___y_2399_);
lean_closure_set(v___f_2410_, 3, v_a_2372_);
lean_closure_set(v___f_2410_, 4, v___x_2409_);
lean_closure_set(v___f_2410_, 5, v_givenNames_2376_);
lean_closure_set(v___f_2410_, 6, v___y_2396_);
lean_closure_set(v___f_2410_, 7, v___y_2400_);
lean_closure_set(v___f_2410_, 8, v___y_2397_);
v___x_2411_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___redArg(v___y_2401_, v___f_2410_, v___y_2404_, v___y_2405_, v___y_2406_, v___y_2407_);
return v___x_2411_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___boxed(lean_object* v_a_2554_, lean_object* v_val_2555_, lean_object* v_mvarId_2556_, lean_object* v_majorFVarId_2557_, lean_object* v_givenNames_2558_, lean_object* v_recursorName_2559_, lean_object* v_x_2560_, lean_object* v_x_2561_, lean_object* v_x_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_){
_start:
{
lean_object* v_res_2568_; 
v_res_2568_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4(v_a_2554_, v_val_2555_, v_mvarId_2556_, v_majorFVarId_2557_, v_givenNames_2558_, v_recursorName_2559_, v_x_2560_, v_x_2561_, v_x_2562_, v___y_2563_, v___y_2564_, v___y_2565_, v___y_2566_);
lean_dec(v___y_2566_);
lean_dec_ref(v___y_2565_);
lean_dec(v___y_2564_);
lean_dec_ref(v___y_2563_);
return v_res_2568_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4(lean_object* v_val_2569_, lean_object* v_mvarId_2570_, lean_object* v_a_2571_, lean_object* v_majorFVarId_2572_, lean_object* v_givenNames_2573_, lean_object* v_recursorName_2574_, lean_object* v_x_2575_, lean_object* v_x_2576_, lean_object* v_x_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_){
_start:
{
if (lean_obj_tag(v_x_2575_) == 5)
{
lean_object* v_fn_2583_; lean_object* v_arg_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; 
v_fn_2583_ = lean_ctor_get(v_x_2575_, 0);
lean_inc_ref(v_fn_2583_);
v_arg_2584_ = lean_ctor_get(v_x_2575_, 1);
lean_inc_ref(v_arg_2584_);
lean_dec_ref_known(v_x_2575_, 2);
v___x_2585_ = lean_array_set(v_x_2576_, v_x_2577_, v_arg_2584_);
v___x_2586_ = lean_unsigned_to_nat(1u);
v___x_2587_ = lean_nat_sub(v_x_2577_, v___x_2586_);
v___x_2588_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4(v_a_2571_, v_val_2569_, v_mvarId_2570_, v_majorFVarId_2572_, v_givenNames_2573_, v_recursorName_2574_, v_fn_2583_, v___x_2585_, v___x_2587_, v___y_2578_, v___y_2579_, v___y_2580_, v___y_2581_);
return v___x_2588_;
}
else
{
uint8_t v_depElim_2589_; lean_object* v_paramsPos_2590_; lean_object* v___x_2591_; lean_object* v___y_2593_; lean_object* v___y_2594_; lean_object* v___y_2595_; lean_object* v___y_2596_; lean_object* v___y_2597_; size_t v___y_2598_; lean_object* v___y_2599_; lean_object* v___y_2600_; lean_object* v___y_2601_; lean_object* v___y_2602_; lean_object* v___y_2603_; lean_object* v___y_2604_; lean_object* v_cls_2609_; lean_object* v___x_2610_; 
lean_dec_ref(v_x_2575_);
v_depElim_2589_ = lean_ctor_get_uint8(v_a_2571_, sizeof(void*)*8);
v_paramsPos_2590_ = lean_ctor_get(v_a_2571_, 5);
v___x_2591_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1));
v_cls_2609_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__2));
lean_inc(v_paramsPos_2590_);
lean_inc(v_mvarId_2570_);
lean_inc_ref(v_val_2569_);
v___x_2610_ = l_List_forM___at___00Lean_MVarId_induction_spec__0(v_x_2576_, v_val_2569_, v_mvarId_2570_, v_paramsPos_2590_, v___y_2578_, v___y_2579_, v___y_2580_, v___y_2581_);
lean_dec_ref(v_x_2576_);
if (lean_obj_tag(v___x_2610_) == 0)
{
lean_object* v___x_2611_; 
lean_dec_ref_known(v___x_2610_, 1);
lean_inc_ref(v_a_2571_);
lean_inc(v_mvarId_2570_);
v___x_2611_ = l_Lean_Meta_getMajorTypeIndices(v_mvarId_2570_, v___x_2591_, v_a_2571_, v_val_2569_, v___y_2578_, v___y_2579_, v___y_2580_, v___y_2581_);
if (lean_obj_tag(v___x_2611_) == 0)
{
lean_object* v_a_2612_; lean_object* v___y_2614_; lean_object* v___y_2615_; lean_object* v___y_2616_; lean_object* v___y_2617_; lean_object* v___x_2701_; 
v_a_2612_ = lean_ctor_get(v___x_2611_, 0);
lean_inc(v_a_2612_);
lean_dec_ref_known(v___x_2611_, 1);
lean_inc(v_mvarId_2570_);
v___x_2701_ = l_Lean_MVarId_getType(v_mvarId_2570_, v___y_2578_, v___y_2579_, v___y_2580_, v___y_2581_);
if (lean_obj_tag(v___x_2701_) == 0)
{
if (v_depElim_2589_ == 0)
{
lean_object* v_a_2702_; lean_object* v___x_2703_; lean_object* v_a_2704_; lean_object* v___x_2706_; uint8_t v_isShared_2707_; uint8_t v_isSharedCheck_2726_; 
v_a_2702_ = lean_ctor_get(v___x_2701_, 0);
lean_inc(v_a_2702_);
lean_dec_ref_known(v___x_2701_, 1);
lean_inc(v_majorFVarId_2572_);
v___x_2703_ = l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2___redArg(v_a_2702_, v_majorFVarId_2572_, v___y_2579_);
v_a_2704_ = lean_ctor_get(v___x_2703_, 0);
v_isSharedCheck_2726_ = !lean_is_exclusive(v___x_2703_);
if (v_isSharedCheck_2726_ == 0)
{
v___x_2706_ = v___x_2703_;
v_isShared_2707_ = v_isSharedCheck_2726_;
goto v_resetjp_2705_;
}
else
{
lean_inc(v_a_2704_);
lean_dec(v___x_2703_);
v___x_2706_ = lean_box(0);
v_isShared_2707_ = v_isSharedCheck_2726_;
goto v_resetjp_2705_;
}
v_resetjp_2705_:
{
uint8_t v___x_2708_; 
v___x_2708_ = lean_unbox(v_a_2704_);
lean_dec(v_a_2704_);
if (v___x_2708_ == 0)
{
lean_del_object(v___x_2706_);
lean_dec(v_recursorName_2574_);
v___y_2614_ = v___y_2578_;
v___y_2615_ = v___y_2579_;
v___y_2616_ = v___y_2580_;
v___y_2617_ = v___y_2581_;
goto v___jp_2613_;
}
else
{
lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2715_; 
v___x_2709_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__3, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__3);
v___x_2710_ = l_Lean_MessageData_ofName(v_recursorName_2574_);
v___x_2711_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2711_, 0, v___x_2709_);
lean_ctor_set(v___x_2711_, 1, v___x_2710_);
v___x_2712_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__5, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__5_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__5);
v___x_2713_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2713_, 0, v___x_2711_);
lean_ctor_set(v___x_2713_, 1, v___x_2712_);
if (v_isShared_2707_ == 0)
{
lean_ctor_set_tag(v___x_2706_, 1);
lean_ctor_set(v___x_2706_, 0, v___x_2713_);
v___x_2715_ = v___x_2706_;
goto v_reusejp_2714_;
}
else
{
lean_object* v_reuseFailAlloc_2725_; 
v_reuseFailAlloc_2725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2725_, 0, v___x_2713_);
v___x_2715_ = v_reuseFailAlloc_2725_;
goto v_reusejp_2714_;
}
v_reusejp_2714_:
{
lean_object* v___x_2716_; 
lean_inc(v_mvarId_2570_);
v___x_2716_ = l_Lean_Meta_throwTacticEx___redArg(v___x_2591_, v_mvarId_2570_, v___x_2715_, v___y_2578_, v___y_2579_, v___y_2580_, v___y_2581_);
if (lean_obj_tag(v___x_2716_) == 0)
{
lean_dec_ref_known(v___x_2716_, 1);
v___y_2614_ = v___y_2578_;
v___y_2615_ = v___y_2579_;
v___y_2616_ = v___y_2580_;
v___y_2617_ = v___y_2581_;
goto v___jp_2613_;
}
else
{
lean_object* v_a_2717_; lean_object* v___x_2719_; uint8_t v_isShared_2720_; uint8_t v_isSharedCheck_2724_; 
lean_dec(v_a_2612_);
lean_dec_ref(v_givenNames_2573_);
lean_dec(v_majorFVarId_2572_);
lean_dec_ref(v_a_2571_);
lean_dec(v_mvarId_2570_);
v_a_2717_ = lean_ctor_get(v___x_2716_, 0);
v_isSharedCheck_2724_ = !lean_is_exclusive(v___x_2716_);
if (v_isSharedCheck_2724_ == 0)
{
v___x_2719_ = v___x_2716_;
v_isShared_2720_ = v_isSharedCheck_2724_;
goto v_resetjp_2718_;
}
else
{
lean_inc(v_a_2717_);
lean_dec(v___x_2716_);
v___x_2719_ = lean_box(0);
v_isShared_2720_ = v_isSharedCheck_2724_;
goto v_resetjp_2718_;
}
v_resetjp_2718_:
{
lean_object* v___x_2722_; 
if (v_isShared_2720_ == 0)
{
v___x_2722_ = v___x_2719_;
goto v_reusejp_2721_;
}
else
{
lean_object* v_reuseFailAlloc_2723_; 
v_reuseFailAlloc_2723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2723_, 0, v_a_2717_);
v___x_2722_ = v_reuseFailAlloc_2723_;
goto v_reusejp_2721_;
}
v_reusejp_2721_:
{
return v___x_2722_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v___x_2701_, 1);
lean_dec(v_recursorName_2574_);
v___y_2614_ = v___y_2578_;
v___y_2615_ = v___y_2579_;
v___y_2616_ = v___y_2580_;
v___y_2617_ = v___y_2581_;
goto v___jp_2613_;
}
}
else
{
lean_object* v_a_2727_; lean_object* v___x_2729_; uint8_t v_isShared_2730_; uint8_t v_isSharedCheck_2734_; 
lean_dec(v_a_2612_);
lean_dec(v_recursorName_2574_);
lean_dec_ref(v_givenNames_2573_);
lean_dec(v_majorFVarId_2572_);
lean_dec_ref(v_a_2571_);
lean_dec(v_mvarId_2570_);
v_a_2727_ = lean_ctor_get(v___x_2701_, 0);
v_isSharedCheck_2734_ = !lean_is_exclusive(v___x_2701_);
if (v_isSharedCheck_2734_ == 0)
{
v___x_2729_ = v___x_2701_;
v_isShared_2730_ = v_isSharedCheck_2734_;
goto v_resetjp_2728_;
}
else
{
lean_inc(v_a_2727_);
lean_dec(v___x_2701_);
v___x_2729_ = lean_box(0);
v_isShared_2730_ = v_isSharedCheck_2734_;
goto v_resetjp_2728_;
}
v_resetjp_2728_:
{
lean_object* v___x_2732_; 
if (v_isShared_2730_ == 0)
{
v___x_2732_ = v___x_2729_;
goto v_reusejp_2731_;
}
else
{
lean_object* v_reuseFailAlloc_2733_; 
v_reuseFailAlloc_2733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2733_, 0, v_a_2727_);
v___x_2732_ = v_reuseFailAlloc_2733_;
goto v_reusejp_2731_;
}
v_reusejp_2731_:
{
return v___x_2732_;
}
}
}
v___jp_2613_:
{
size_t v_sz_2618_; size_t v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; uint8_t v___x_2622_; uint8_t v___x_2623_; lean_object* v___x_2624_; 
v_sz_2618_ = lean_array_size(v_a_2612_);
v___x_2619_ = ((size_t)0ULL);
lean_inc(v_a_2612_);
v___x_2620_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_induction_spec__1(v_sz_2618_, v___x_2619_, v_a_2612_);
lean_inc(v_majorFVarId_2572_);
v___x_2621_ = lean_array_push(v___x_2620_, v_majorFVarId_2572_);
v___x_2622_ = 1;
v___x_2623_ = 0;
v___x_2624_ = l_Lean_MVarId_revert(v_mvarId_2570_, v___x_2621_, v___x_2622_, v___x_2623_, v___y_2614_, v___y_2615_, v___y_2616_, v___y_2617_);
if (lean_obj_tag(v___x_2624_) == 0)
{
lean_object* v_a_2625_; lean_object* v_fst_2626_; lean_object* v_snd_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; 
v_a_2625_ = lean_ctor_get(v___x_2624_, 0);
lean_inc(v_a_2625_);
lean_dec_ref_known(v___x_2624_, 1);
v_fst_2626_ = lean_ctor_get(v_a_2625_, 0);
lean_inc(v_fst_2626_);
v_snd_2627_ = lean_ctor_get(v_a_2625_, 1);
lean_inc(v_snd_2627_);
lean_dec(v_a_2625_);
v___x_2628_ = lean_array_get_size(v_a_2612_);
v___x_2629_ = lean_box(0);
v___x_2630_ = l_Lean_Meta_introNCore(v_snd_2627_, v___x_2628_, v___x_2629_, v___x_2623_, v___x_2622_, v___y_2614_, v___y_2615_, v___y_2616_, v___y_2617_);
if (lean_obj_tag(v___x_2630_) == 0)
{
lean_object* v_a_2631_; lean_object* v_fst_2632_; lean_object* v_snd_2633_; lean_object* v___x_2634_; 
v_a_2631_ = lean_ctor_get(v___x_2630_, 0);
lean_inc(v_a_2631_);
lean_dec_ref_known(v___x_2630_, 1);
v_fst_2632_ = lean_ctor_get(v_a_2631_, 0);
lean_inc(v_fst_2632_);
v_snd_2633_ = lean_ctor_get(v_a_2631_, 1);
lean_inc(v_snd_2633_);
lean_dec(v_a_2631_);
v___x_2634_ = l_Lean_Meta_intro1Core(v_snd_2633_, v___x_2622_, v___y_2614_, v___y_2615_, v___y_2616_, v___y_2617_);
if (lean_obj_tag(v___x_2634_) == 0)
{
lean_object* v_a_2635_; lean_object* v_fst_2636_; lean_object* v_snd_2637_; lean_object* v___x_2639_; uint8_t v_isShared_2640_; uint8_t v_isSharedCheck_2676_; 
v_a_2635_ = lean_ctor_get(v___x_2634_, 0);
lean_inc(v_a_2635_);
lean_dec_ref_known(v___x_2634_, 1);
v_fst_2636_ = lean_ctor_get(v_a_2635_, 0);
v_snd_2637_ = lean_ctor_get(v_a_2635_, 1);
v_isSharedCheck_2676_ = !lean_is_exclusive(v_a_2635_);
if (v_isSharedCheck_2676_ == 0)
{
v___x_2639_ = v_a_2635_;
v_isShared_2640_ = v_isSharedCheck_2676_;
goto v_resetjp_2638_;
}
else
{
lean_inc(v_snd_2637_);
lean_inc(v_fst_2636_);
lean_dec(v_a_2635_);
v___x_2639_ = lean_box(0);
v_isShared_2640_ = v_isSharedCheck_2676_;
goto v_resetjp_2638_;
}
v_resetjp_2638_:
{
lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2646_; 
v___x_2641_ = lean_box(0);
lean_inc(v_fst_2636_);
v___x_2642_ = l_Lean_mkFVar(v_fst_2636_);
lean_inc_ref(v___x_2642_);
v___x_2643_ = l_Lean_Meta_FVarSubst_insert(v___x_2641_, v_majorFVarId_2572_, v___x_2642_);
v___x_2644_ = lean_unsigned_to_nat(0u);
if (v_isShared_2640_ == 0)
{
lean_ctor_set(v___x_2639_, 1, v___x_2644_);
lean_ctor_set(v___x_2639_, 0, v___x_2643_);
v___x_2646_ = v___x_2639_;
goto v_reusejp_2645_;
}
else
{
lean_object* v_reuseFailAlloc_2675_; 
v_reuseFailAlloc_2675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2675_, 0, v___x_2643_);
lean_ctor_set(v_reuseFailAlloc_2675_, 1, v___x_2644_);
v___x_2646_ = v_reuseFailAlloc_2675_;
goto v_reusejp_2645_;
}
v_reusejp_2645_:
{
lean_object* v___x_2647_; lean_object* v_toCold_2648_; lean_object* v_options_2649_; uint8_t v_hasTrace_2650_; 
v___x_2647_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_induction_spec__2(v_fst_2632_, v_a_2612_, v_sz_2618_, v___x_2619_, v___x_2646_);
lean_dec(v_a_2612_);
v_toCold_2648_ = lean_ctor_get(v___y_2616_, 0);
v_options_2649_ = lean_ctor_get(v_toCold_2648_, 2);
v_hasTrace_2650_ = lean_ctor_get_uint8(v_options_2649_, sizeof(void*)*1);
if (v_hasTrace_2650_ == 0)
{
lean_object* v_fst_2651_; 
v_fst_2651_ = lean_ctor_get(v___x_2647_, 0);
lean_inc(v_fst_2651_);
lean_dec_ref(v___x_2647_);
lean_inc(v_snd_2637_);
v___y_2593_ = v_fst_2651_;
v___y_2594_ = v_fst_2636_;
v___y_2595_ = v___x_2642_;
v___y_2596_ = v_fst_2626_;
v___y_2597_ = v_snd_2637_;
v___y_2598_ = v___x_2619_;
v___y_2599_ = v_snd_2637_;
v___y_2600_ = v_fst_2632_;
v___y_2601_ = v___y_2614_;
v___y_2602_ = v___y_2615_;
v___y_2603_ = v___y_2616_;
v___y_2604_ = v___y_2617_;
goto v___jp_2592_;
}
else
{
lean_object* v_fst_2652_; lean_object* v___x_2654_; uint8_t v_isShared_2655_; uint8_t v_isSharedCheck_2673_; 
v_fst_2652_ = lean_ctor_get(v___x_2647_, 0);
v_isSharedCheck_2673_ = !lean_is_exclusive(v___x_2647_);
if (v_isSharedCheck_2673_ == 0)
{
lean_object* v_unused_2674_; 
v_unused_2674_ = lean_ctor_get(v___x_2647_, 1);
lean_dec(v_unused_2674_);
v___x_2654_ = v___x_2647_;
v_isShared_2655_ = v_isSharedCheck_2673_;
goto v_resetjp_2653_;
}
else
{
lean_inc(v_fst_2652_);
lean_dec(v___x_2647_);
v___x_2654_ = lean_box(0);
v_isShared_2655_ = v_isSharedCheck_2673_;
goto v_resetjp_2653_;
}
v_resetjp_2653_:
{
lean_object* v_inheritedTraceOptions_2656_; lean_object* v___x_2657_; uint8_t v___x_2658_; 
v_inheritedTraceOptions_2656_ = lean_ctor_get(v_toCold_2648_, 11);
v___x_2657_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5);
v___x_2658_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2656_, v_options_2649_, v___x_2657_);
if (v___x_2658_ == 0)
{
lean_del_object(v___x_2654_);
lean_inc(v_snd_2637_);
v___y_2593_ = v_fst_2652_;
v___y_2594_ = v_fst_2636_;
v___y_2595_ = v___x_2642_;
v___y_2596_ = v_fst_2626_;
v___y_2597_ = v_snd_2637_;
v___y_2598_ = v___x_2619_;
v___y_2599_ = v_snd_2637_;
v___y_2600_ = v_fst_2632_;
v___y_2601_ = v___y_2614_;
v___y_2602_ = v___y_2615_;
v___y_2603_ = v___y_2616_;
v___y_2604_ = v___y_2617_;
goto v___jp_2592_;
}
else
{
lean_object* v___x_2659_; lean_object* v___x_2660_; lean_object* v___x_2662_; 
v___x_2659_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__1);
lean_inc(v_snd_2637_);
v___x_2660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2660_, 0, v_snd_2637_);
if (v_isShared_2655_ == 0)
{
lean_ctor_set_tag(v___x_2654_, 7);
lean_ctor_set(v___x_2654_, 1, v___x_2660_);
lean_ctor_set(v___x_2654_, 0, v___x_2659_);
v___x_2662_ = v___x_2654_;
goto v_reusejp_2661_;
}
else
{
lean_object* v_reuseFailAlloc_2672_; 
v_reuseFailAlloc_2672_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2672_, 0, v___x_2659_);
lean_ctor_set(v_reuseFailAlloc_2672_, 1, v___x_2660_);
v___x_2662_ = v_reuseFailAlloc_2672_;
goto v_reusejp_2661_;
}
v_reusejp_2661_:
{
lean_object* v___x_2663_; 
v___x_2663_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1(v_cls_2609_, v___x_2662_, v___y_2614_, v___y_2615_, v___y_2616_, v___y_2617_);
if (lean_obj_tag(v___x_2663_) == 0)
{
lean_dec_ref_known(v___x_2663_, 1);
lean_inc(v_snd_2637_);
v___y_2593_ = v_fst_2652_;
v___y_2594_ = v_fst_2636_;
v___y_2595_ = v___x_2642_;
v___y_2596_ = v_fst_2626_;
v___y_2597_ = v_snd_2637_;
v___y_2598_ = v___x_2619_;
v___y_2599_ = v_snd_2637_;
v___y_2600_ = v_fst_2632_;
v___y_2601_ = v___y_2614_;
v___y_2602_ = v___y_2615_;
v___y_2603_ = v___y_2616_;
v___y_2604_ = v___y_2617_;
goto v___jp_2592_;
}
else
{
lean_object* v_a_2664_; lean_object* v___x_2666_; uint8_t v_isShared_2667_; uint8_t v_isSharedCheck_2671_; 
lean_dec(v_fst_2652_);
lean_dec_ref(v___x_2642_);
lean_dec(v_snd_2637_);
lean_dec(v_fst_2636_);
lean_dec(v_fst_2632_);
lean_dec(v_fst_2626_);
lean_dec_ref(v_givenNames_2573_);
lean_dec_ref(v_a_2571_);
v_a_2664_ = lean_ctor_get(v___x_2663_, 0);
v_isSharedCheck_2671_ = !lean_is_exclusive(v___x_2663_);
if (v_isSharedCheck_2671_ == 0)
{
v___x_2666_ = v___x_2663_;
v_isShared_2667_ = v_isSharedCheck_2671_;
goto v_resetjp_2665_;
}
else
{
lean_inc(v_a_2664_);
lean_dec(v___x_2663_);
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
}
}
}
}
}
else
{
lean_object* v_a_2677_; lean_object* v___x_2679_; uint8_t v_isShared_2680_; uint8_t v_isSharedCheck_2684_; 
lean_dec(v_fst_2632_);
lean_dec(v_fst_2626_);
lean_dec(v_a_2612_);
lean_dec_ref(v_givenNames_2573_);
lean_dec(v_majorFVarId_2572_);
lean_dec_ref(v_a_2571_);
v_a_2677_ = lean_ctor_get(v___x_2634_, 0);
v_isSharedCheck_2684_ = !lean_is_exclusive(v___x_2634_);
if (v_isSharedCheck_2684_ == 0)
{
v___x_2679_ = v___x_2634_;
v_isShared_2680_ = v_isSharedCheck_2684_;
goto v_resetjp_2678_;
}
else
{
lean_inc(v_a_2677_);
lean_dec(v___x_2634_);
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
else
{
lean_object* v_a_2685_; lean_object* v___x_2687_; uint8_t v_isShared_2688_; uint8_t v_isSharedCheck_2692_; 
lean_dec(v_fst_2626_);
lean_dec(v_a_2612_);
lean_dec_ref(v_givenNames_2573_);
lean_dec(v_majorFVarId_2572_);
lean_dec_ref(v_a_2571_);
v_a_2685_ = lean_ctor_get(v___x_2630_, 0);
v_isSharedCheck_2692_ = !lean_is_exclusive(v___x_2630_);
if (v_isSharedCheck_2692_ == 0)
{
v___x_2687_ = v___x_2630_;
v_isShared_2688_ = v_isSharedCheck_2692_;
goto v_resetjp_2686_;
}
else
{
lean_inc(v_a_2685_);
lean_dec(v___x_2630_);
v___x_2687_ = lean_box(0);
v_isShared_2688_ = v_isSharedCheck_2692_;
goto v_resetjp_2686_;
}
v_resetjp_2686_:
{
lean_object* v___x_2690_; 
if (v_isShared_2688_ == 0)
{
v___x_2690_ = v___x_2687_;
goto v_reusejp_2689_;
}
else
{
lean_object* v_reuseFailAlloc_2691_; 
v_reuseFailAlloc_2691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2691_, 0, v_a_2685_);
v___x_2690_ = v_reuseFailAlloc_2691_;
goto v_reusejp_2689_;
}
v_reusejp_2689_:
{
return v___x_2690_;
}
}
}
}
else
{
lean_object* v_a_2693_; lean_object* v___x_2695_; uint8_t v_isShared_2696_; uint8_t v_isSharedCheck_2700_; 
lean_dec(v_a_2612_);
lean_dec_ref(v_givenNames_2573_);
lean_dec(v_majorFVarId_2572_);
lean_dec_ref(v_a_2571_);
v_a_2693_ = lean_ctor_get(v___x_2624_, 0);
v_isSharedCheck_2700_ = !lean_is_exclusive(v___x_2624_);
if (v_isSharedCheck_2700_ == 0)
{
v___x_2695_ = v___x_2624_;
v_isShared_2696_ = v_isSharedCheck_2700_;
goto v_resetjp_2694_;
}
else
{
lean_inc(v_a_2693_);
lean_dec(v___x_2624_);
v___x_2695_ = lean_box(0);
v_isShared_2696_ = v_isSharedCheck_2700_;
goto v_resetjp_2694_;
}
v_resetjp_2694_:
{
lean_object* v___x_2698_; 
if (v_isShared_2696_ == 0)
{
v___x_2698_ = v___x_2695_;
goto v_reusejp_2697_;
}
else
{
lean_object* v_reuseFailAlloc_2699_; 
v_reuseFailAlloc_2699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2699_, 0, v_a_2693_);
v___x_2698_ = v_reuseFailAlloc_2699_;
goto v_reusejp_2697_;
}
v_reusejp_2697_:
{
return v___x_2698_;
}
}
}
}
}
else
{
lean_object* v_a_2735_; lean_object* v___x_2737_; uint8_t v_isShared_2738_; uint8_t v_isSharedCheck_2742_; 
lean_dec(v_recursorName_2574_);
lean_dec_ref(v_givenNames_2573_);
lean_dec(v_majorFVarId_2572_);
lean_dec_ref(v_a_2571_);
lean_dec(v_mvarId_2570_);
v_a_2735_ = lean_ctor_get(v___x_2611_, 0);
v_isSharedCheck_2742_ = !lean_is_exclusive(v___x_2611_);
if (v_isSharedCheck_2742_ == 0)
{
v___x_2737_ = v___x_2611_;
v_isShared_2738_ = v_isSharedCheck_2742_;
goto v_resetjp_2736_;
}
else
{
lean_inc(v_a_2735_);
lean_dec(v___x_2611_);
v___x_2737_ = lean_box(0);
v_isShared_2738_ = v_isSharedCheck_2742_;
goto v_resetjp_2736_;
}
v_resetjp_2736_:
{
lean_object* v___x_2740_; 
if (v_isShared_2738_ == 0)
{
v___x_2740_ = v___x_2737_;
goto v_reusejp_2739_;
}
else
{
lean_object* v_reuseFailAlloc_2741_; 
v_reuseFailAlloc_2741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2741_, 0, v_a_2735_);
v___x_2740_ = v_reuseFailAlloc_2741_;
goto v_reusejp_2739_;
}
v_reusejp_2739_:
{
return v___x_2740_;
}
}
}
}
else
{
lean_object* v_a_2743_; lean_object* v___x_2745_; uint8_t v_isShared_2746_; uint8_t v_isSharedCheck_2750_; 
lean_dec(v_recursorName_2574_);
lean_dec_ref(v_givenNames_2573_);
lean_dec(v_majorFVarId_2572_);
lean_dec_ref(v_a_2571_);
lean_dec(v_mvarId_2570_);
lean_dec_ref(v_val_2569_);
v_a_2743_ = lean_ctor_get(v___x_2610_, 0);
v_isSharedCheck_2750_ = !lean_is_exclusive(v___x_2610_);
if (v_isSharedCheck_2750_ == 0)
{
v___x_2745_ = v___x_2610_;
v_isShared_2746_ = v_isSharedCheck_2750_;
goto v_resetjp_2744_;
}
else
{
lean_inc(v_a_2743_);
lean_dec(v___x_2610_);
v___x_2745_ = lean_box(0);
v_isShared_2746_ = v_isSharedCheck_2750_;
goto v_resetjp_2744_;
}
v_resetjp_2744_:
{
lean_object* v___x_2748_; 
if (v_isShared_2746_ == 0)
{
v___x_2748_ = v___x_2745_;
goto v_reusejp_2747_;
}
else
{
lean_object* v_reuseFailAlloc_2749_; 
v_reuseFailAlloc_2749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2749_, 0, v_a_2743_);
v___x_2748_ = v_reuseFailAlloc_2749_;
goto v_reusejp_2747_;
}
v_reusejp_2747_:
{
return v___x_2748_;
}
}
}
v___jp_2592_:
{
size_t v_sz_2605_; lean_object* v___x_2606_; lean_object* v___f_2607_; lean_object* v___x_2608_; 
v_sz_2605_ = lean_array_size(v___y_2600_);
v___x_2606_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__3(v_sz_2605_, v___y_2598_, v___y_2600_);
v___f_2607_ = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4___lam__0___boxed), 14, 9);
lean_closure_set(v___f_2607_, 0, v___y_2597_);
lean_closure_set(v___f_2607_, 1, v___x_2591_);
lean_closure_set(v___f_2607_, 2, v___y_2594_);
lean_closure_set(v___f_2607_, 3, v_a_2571_);
lean_closure_set(v___f_2607_, 4, v___x_2606_);
lean_closure_set(v___f_2607_, 5, v_givenNames_2573_);
lean_closure_set(v___f_2607_, 6, v___y_2596_);
lean_closure_set(v___f_2607_, 7, v___y_2595_);
lean_closure_set(v___f_2607_, 8, v___y_2593_);
v___x_2608_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___redArg(v___y_2599_, v___f_2607_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_);
return v___x_2608_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4___boxed(lean_object* v_val_2751_, lean_object* v_mvarId_2752_, lean_object* v_a_2753_, lean_object* v_majorFVarId_2754_, lean_object* v_givenNames_2755_, lean_object* v_recursorName_2756_, lean_object* v_x_2757_, lean_object* v_x_2758_, lean_object* v_x_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_, lean_object* v___y_2764_){
_start:
{
lean_object* v_res_2765_; 
v_res_2765_ = l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4(v_val_2751_, v_mvarId_2752_, v_a_2753_, v_majorFVarId_2754_, v_givenNames_2755_, v_recursorName_2756_, v_x_2757_, v_x_2758_, v_x_2759_, v___y_2760_, v___y_2761_, v___y_2762_, v___y_2763_);
lean_dec(v___y_2763_);
lean_dec_ref(v___y_2762_);
lean_dec(v___y_2761_);
lean_dec_ref(v___y_2760_);
lean_dec(v_x_2759_);
return v_res_2765_;
}
}
static lean_object* _init_l_Lean_MVarId_induction___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2767_; lean_object* v___x_2768_; 
v___x_2767_ = ((lean_object*)(l_Lean_MVarId_induction___lam__0___closed__0));
v___x_2768_ = l_Lean_stringToMessageData(v___x_2767_);
return v___x_2768_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_induction___lam__0(lean_object* v___x_2769_, lean_object* v_mvarId_2770_, lean_object* v_majorFVarId_2771_, lean_object* v_recursorName_2772_, lean_object* v_givenNames_2773_, lean_object* v_cls_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_){
_start:
{
lean_object* v___y_2781_; lean_object* v___y_2782_; lean_object* v___y_2783_; lean_object* v___y_2784_; lean_object* v_toCold_2836_; lean_object* v_options_2837_; uint8_t v_hasTrace_2838_; 
v_toCold_2836_ = lean_ctor_get(v___y_2777_, 0);
v_options_2837_ = lean_ctor_get(v_toCold_2836_, 2);
v_hasTrace_2838_ = lean_ctor_get_uint8(v_options_2837_, sizeof(void*)*1);
if (v_hasTrace_2838_ == 0)
{
lean_dec(v_cls_2774_);
v___y_2781_ = v___y_2775_;
v___y_2782_ = v___y_2776_;
v___y_2783_ = v___y_2777_;
v___y_2784_ = v___y_2778_;
goto v___jp_2780_;
}
else
{
lean_object* v_inheritedTraceOptions_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; uint8_t v___x_2842_; 
v_inheritedTraceOptions_2839_ = lean_ctor_get(v_toCold_2836_, 11);
v___x_2840_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__4));
lean_inc(v_cls_2774_);
v___x_2841_ = l_Lean_Name_append(v___x_2840_, v_cls_2774_);
v___x_2842_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2839_, v_options_2837_, v___x_2841_);
lean_dec(v___x_2841_);
if (v___x_2842_ == 0)
{
lean_dec(v_cls_2774_);
v___y_2781_ = v___y_2775_;
v___y_2782_ = v___y_2776_;
v___y_2783_ = v___y_2777_;
v___y_2784_ = v___y_2778_;
goto v___jp_2780_;
}
else
{
lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; 
v___x_2843_ = lean_obj_once(&l_Lean_MVarId_induction___lam__0___closed__1, &l_Lean_MVarId_induction___lam__0___closed__1_once, _init_l_Lean_MVarId_induction___lam__0___closed__1);
lean_inc(v_mvarId_2770_);
v___x_2844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2844_, 0, v_mvarId_2770_);
v___x_2845_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2845_, 0, v___x_2843_);
lean_ctor_set(v___x_2845_, 1, v___x_2844_);
v___x_2846_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1(v_cls_2774_, v___x_2845_, v___y_2775_, v___y_2776_, v___y_2777_, v___y_2778_);
if (lean_obj_tag(v___x_2846_) == 0)
{
lean_dec_ref_known(v___x_2846_, 1);
v___y_2781_ = v___y_2775_;
v___y_2782_ = v___y_2776_;
v___y_2783_ = v___y_2777_;
v___y_2784_ = v___y_2778_;
goto v___jp_2780_;
}
else
{
lean_object* v_a_2847_; lean_object* v___x_2849_; uint8_t v_isShared_2850_; uint8_t v_isSharedCheck_2854_; 
lean_dec_ref(v_givenNames_2773_);
lean_dec(v_recursorName_2772_);
lean_dec(v_majorFVarId_2771_);
lean_dec(v_mvarId_2770_);
lean_dec_ref(v___x_2769_);
v_a_2847_ = lean_ctor_get(v___x_2846_, 0);
v_isSharedCheck_2854_ = !lean_is_exclusive(v___x_2846_);
if (v_isSharedCheck_2854_ == 0)
{
v___x_2849_ = v___x_2846_;
v_isShared_2850_ = v_isSharedCheck_2854_;
goto v_resetjp_2848_;
}
else
{
lean_inc(v_a_2847_);
lean_dec(v___x_2846_);
v___x_2849_ = lean_box(0);
v_isShared_2850_ = v_isSharedCheck_2854_;
goto v_resetjp_2848_;
}
v_resetjp_2848_:
{
lean_object* v___x_2852_; 
if (v_isShared_2850_ == 0)
{
v___x_2852_ = v___x_2849_;
goto v_reusejp_2851_;
}
else
{
lean_object* v_reuseFailAlloc_2853_; 
v_reuseFailAlloc_2853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2853_, 0, v_a_2847_);
v___x_2852_ = v_reuseFailAlloc_2853_;
goto v_reusejp_2851_;
}
v_reusejp_2851_:
{
return v___x_2852_;
}
}
}
}
}
v___jp_2780_:
{
lean_object* v___x_2785_; lean_object* v___x_2786_; 
v___x_2785_ = l_Lean_Name_mkStr1(v___x_2769_);
lean_inc(v___x_2785_);
lean_inc(v_mvarId_2770_);
v___x_2786_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_2770_, v___x_2785_, v___y_2781_, v___y_2782_, v___y_2783_, v___y_2784_);
if (lean_obj_tag(v___x_2786_) == 0)
{
lean_object* v___x_2787_; 
lean_dec_ref_known(v___x_2786_, 1);
lean_inc(v_majorFVarId_2771_);
v___x_2787_ = l_Lean_FVarId_getDecl___redArg(v_majorFVarId_2771_, v___y_2781_, v___y_2783_, v___y_2784_);
if (lean_obj_tag(v___x_2787_) == 0)
{
lean_object* v_a_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; 
v_a_2788_ = lean_ctor_get(v___x_2787_, 0);
lean_inc(v_a_2788_);
lean_dec_ref_known(v___x_2787_, 1);
v___x_2789_ = lean_box(0);
lean_inc(v_recursorName_2772_);
v___x_2790_ = l_Lean_Meta_mkRecursorInfo(v_recursorName_2772_, v___x_2789_, v___y_2781_, v___y_2782_, v___y_2783_, v___y_2784_);
if (lean_obj_tag(v___x_2790_) == 0)
{
lean_object* v_a_2791_; lean_object* v_typeName_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; 
v_a_2791_ = lean_ctor_get(v___x_2790_, 0);
lean_inc(v_a_2791_);
lean_dec_ref_known(v___x_2790_, 1);
v_typeName_2792_ = lean_ctor_get(v_a_2791_, 1);
v___x_2793_ = l_Lean_LocalDecl_type(v_a_2788_);
lean_dec(v_a_2788_);
lean_inc_ref(v___x_2793_);
v___x_2794_ = l_Lean_Meta_whnfUntil(v___x_2793_, v_typeName_2792_, v___y_2781_, v___y_2782_, v___y_2783_, v___y_2784_);
if (lean_obj_tag(v___x_2794_) == 0)
{
lean_object* v_a_2795_; 
v_a_2795_ = lean_ctor_get(v___x_2794_, 0);
lean_inc(v_a_2795_);
lean_dec_ref_known(v___x_2794_, 1);
if (lean_obj_tag(v_a_2795_) == 1)
{
lean_object* v_val_2796_; lean_object* v_dummy_2797_; lean_object* v_nargs_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; 
lean_dec_ref(v___x_2793_);
lean_dec(v___x_2785_);
v_val_2796_ = lean_ctor_get(v_a_2795_, 0);
lean_inc_n(v_val_2796_, 2);
lean_dec_ref_known(v_a_2795_, 1);
v_dummy_2797_ = lean_obj_once(&l_Lean_Meta_getMajorTypeIndices___closed__0, &l_Lean_Meta_getMajorTypeIndices___closed__0_once, _init_l_Lean_Meta_getMajorTypeIndices___closed__0);
v_nargs_2798_ = l_Lean_Expr_getAppNumArgs(v_val_2796_);
lean_inc(v_nargs_2798_);
v___x_2799_ = lean_mk_array(v_nargs_2798_, v_dummy_2797_);
v___x_2800_ = lean_unsigned_to_nat(1u);
v___x_2801_ = lean_nat_sub(v_nargs_2798_, v___x_2800_);
lean_dec(v_nargs_2798_);
v___x_2802_ = l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4(v_val_2796_, v_mvarId_2770_, v_a_2791_, v_majorFVarId_2771_, v_givenNames_2773_, v_recursorName_2772_, v_val_2796_, v___x_2799_, v___x_2801_, v___y_2781_, v___y_2782_, v___y_2783_, v___y_2784_);
lean_dec(v___x_2801_);
return v___x_2802_;
}
else
{
lean_object* v___x_2803_; 
lean_dec(v_a_2795_);
lean_dec(v_a_2791_);
lean_dec_ref(v_givenNames_2773_);
lean_dec(v_recursorName_2772_);
lean_dec(v_majorFVarId_2771_);
v___x_2803_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg(v___x_2785_, v_mvarId_2770_, v___x_2793_, v___y_2781_, v___y_2782_, v___y_2783_, v___y_2784_);
return v___x_2803_;
}
}
else
{
lean_object* v_a_2804_; lean_object* v___x_2806_; uint8_t v_isShared_2807_; uint8_t v_isSharedCheck_2811_; 
lean_dec_ref(v___x_2793_);
lean_dec(v_a_2791_);
lean_dec(v___x_2785_);
lean_dec_ref(v_givenNames_2773_);
lean_dec(v_recursorName_2772_);
lean_dec(v_majorFVarId_2771_);
lean_dec(v_mvarId_2770_);
v_a_2804_ = lean_ctor_get(v___x_2794_, 0);
v_isSharedCheck_2811_ = !lean_is_exclusive(v___x_2794_);
if (v_isSharedCheck_2811_ == 0)
{
v___x_2806_ = v___x_2794_;
v_isShared_2807_ = v_isSharedCheck_2811_;
goto v_resetjp_2805_;
}
else
{
lean_inc(v_a_2804_);
lean_dec(v___x_2794_);
v___x_2806_ = lean_box(0);
v_isShared_2807_ = v_isSharedCheck_2811_;
goto v_resetjp_2805_;
}
v_resetjp_2805_:
{
lean_object* v___x_2809_; 
if (v_isShared_2807_ == 0)
{
v___x_2809_ = v___x_2806_;
goto v_reusejp_2808_;
}
else
{
lean_object* v_reuseFailAlloc_2810_; 
v_reuseFailAlloc_2810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2810_, 0, v_a_2804_);
v___x_2809_ = v_reuseFailAlloc_2810_;
goto v_reusejp_2808_;
}
v_reusejp_2808_:
{
return v___x_2809_;
}
}
}
}
else
{
lean_object* v_a_2812_; lean_object* v___x_2814_; uint8_t v_isShared_2815_; uint8_t v_isSharedCheck_2819_; 
lean_dec(v_a_2788_);
lean_dec(v___x_2785_);
lean_dec_ref(v_givenNames_2773_);
lean_dec(v_recursorName_2772_);
lean_dec(v_majorFVarId_2771_);
lean_dec(v_mvarId_2770_);
v_a_2812_ = lean_ctor_get(v___x_2790_, 0);
v_isSharedCheck_2819_ = !lean_is_exclusive(v___x_2790_);
if (v_isSharedCheck_2819_ == 0)
{
v___x_2814_ = v___x_2790_;
v_isShared_2815_ = v_isSharedCheck_2819_;
goto v_resetjp_2813_;
}
else
{
lean_inc(v_a_2812_);
lean_dec(v___x_2790_);
v___x_2814_ = lean_box(0);
v_isShared_2815_ = v_isSharedCheck_2819_;
goto v_resetjp_2813_;
}
v_resetjp_2813_:
{
lean_object* v___x_2817_; 
if (v_isShared_2815_ == 0)
{
v___x_2817_ = v___x_2814_;
goto v_reusejp_2816_;
}
else
{
lean_object* v_reuseFailAlloc_2818_; 
v_reuseFailAlloc_2818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2818_, 0, v_a_2812_);
v___x_2817_ = v_reuseFailAlloc_2818_;
goto v_reusejp_2816_;
}
v_reusejp_2816_:
{
return v___x_2817_;
}
}
}
}
else
{
lean_object* v_a_2820_; lean_object* v___x_2822_; uint8_t v_isShared_2823_; uint8_t v_isSharedCheck_2827_; 
lean_dec(v___x_2785_);
lean_dec_ref(v_givenNames_2773_);
lean_dec(v_recursorName_2772_);
lean_dec(v_majorFVarId_2771_);
lean_dec(v_mvarId_2770_);
v_a_2820_ = lean_ctor_get(v___x_2787_, 0);
v_isSharedCheck_2827_ = !lean_is_exclusive(v___x_2787_);
if (v_isSharedCheck_2827_ == 0)
{
v___x_2822_ = v___x_2787_;
v_isShared_2823_ = v_isSharedCheck_2827_;
goto v_resetjp_2821_;
}
else
{
lean_inc(v_a_2820_);
lean_dec(v___x_2787_);
v___x_2822_ = lean_box(0);
v_isShared_2823_ = v_isSharedCheck_2827_;
goto v_resetjp_2821_;
}
v_resetjp_2821_:
{
lean_object* v___x_2825_; 
if (v_isShared_2823_ == 0)
{
v___x_2825_ = v___x_2822_;
goto v_reusejp_2824_;
}
else
{
lean_object* v_reuseFailAlloc_2826_; 
v_reuseFailAlloc_2826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2826_, 0, v_a_2820_);
v___x_2825_ = v_reuseFailAlloc_2826_;
goto v_reusejp_2824_;
}
v_reusejp_2824_:
{
return v___x_2825_;
}
}
}
}
else
{
lean_object* v_a_2828_; lean_object* v___x_2830_; uint8_t v_isShared_2831_; uint8_t v_isSharedCheck_2835_; 
lean_dec(v___x_2785_);
lean_dec_ref(v_givenNames_2773_);
lean_dec(v_recursorName_2772_);
lean_dec(v_majorFVarId_2771_);
lean_dec(v_mvarId_2770_);
v_a_2828_ = lean_ctor_get(v___x_2786_, 0);
v_isSharedCheck_2835_ = !lean_is_exclusive(v___x_2786_);
if (v_isSharedCheck_2835_ == 0)
{
v___x_2830_ = v___x_2786_;
v_isShared_2831_ = v_isSharedCheck_2835_;
goto v_resetjp_2829_;
}
else
{
lean_inc(v_a_2828_);
lean_dec(v___x_2786_);
v___x_2830_ = lean_box(0);
v_isShared_2831_ = v_isSharedCheck_2835_;
goto v_resetjp_2829_;
}
v_resetjp_2829_:
{
lean_object* v___x_2833_; 
if (v_isShared_2831_ == 0)
{
v___x_2833_ = v___x_2830_;
goto v_reusejp_2832_;
}
else
{
lean_object* v_reuseFailAlloc_2834_; 
v_reuseFailAlloc_2834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2834_, 0, v_a_2828_);
v___x_2833_ = v_reuseFailAlloc_2834_;
goto v_reusejp_2832_;
}
v_reusejp_2832_:
{
return v___x_2833_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_induction___lam__0___boxed(lean_object* v___x_2855_, lean_object* v_mvarId_2856_, lean_object* v_majorFVarId_2857_, lean_object* v_recursorName_2858_, lean_object* v_givenNames_2859_, lean_object* v_cls_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_, lean_object* v___y_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_){
_start:
{
lean_object* v_res_2866_; 
v_res_2866_ = l_Lean_MVarId_induction___lam__0(v___x_2855_, v_mvarId_2856_, v_majorFVarId_2857_, v_recursorName_2858_, v_givenNames_2859_, v_cls_2860_, v___y_2861_, v___y_2862_, v___y_2863_, v___y_2864_);
lean_dec(v___y_2864_);
lean_dec_ref(v___y_2863_);
lean_dec(v___y_2862_);
lean_dec_ref(v___y_2861_);
return v_res_2866_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_induction(lean_object* v_mvarId_2867_, lean_object* v_majorFVarId_2868_, lean_object* v_recursorName_2869_, lean_object* v_givenNames_2870_, lean_object* v_a_2871_, lean_object* v_a_2872_, lean_object* v_a_2873_, lean_object* v_a_2874_){
_start:
{
lean_object* v___x_2876_; lean_object* v_cls_2877_; lean_object* v___f_2878_; lean_object* v___x_2879_; 
v___x_2876_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__0));
v_cls_2877_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__2));
lean_inc(v_mvarId_2867_);
v___f_2878_ = lean_alloc_closure((void*)(l_Lean_MVarId_induction___lam__0___boxed), 11, 6);
lean_closure_set(v___f_2878_, 0, v___x_2876_);
lean_closure_set(v___f_2878_, 1, v_mvarId_2867_);
lean_closure_set(v___f_2878_, 2, v_majorFVarId_2868_);
lean_closure_set(v___f_2878_, 3, v_recursorName_2869_);
lean_closure_set(v___f_2878_, 4, v_givenNames_2870_);
lean_closure_set(v___f_2878_, 5, v_cls_2877_);
v___x_2879_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___redArg(v_mvarId_2867_, v___f_2878_, v_a_2871_, v_a_2872_, v_a_2873_, v_a_2874_);
return v___x_2879_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_induction___boxed(lean_object* v_mvarId_2880_, lean_object* v_majorFVarId_2881_, lean_object* v_recursorName_2882_, lean_object* v_givenNames_2883_, lean_object* v_a_2884_, lean_object* v_a_2885_, lean_object* v_a_2886_, lean_object* v_a_2887_, lean_object* v_a_2888_){
_start:
{
lean_object* v_res_2889_; 
v_res_2889_ = l_Lean_MVarId_induction(v_mvarId_2880_, v_majorFVarId_2881_, v_recursorName_2882_, v_givenNames_2883_, v_a_2884_, v_a_2885_, v_a_2886_, v_a_2887_);
lean_dec(v_a_2887_);
lean_dec_ref(v_a_2886_);
lean_dec(v_a_2885_);
lean_dec_ref(v_a_2884_);
return v_res_2889_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; 
v___x_2937_ = lean_unsigned_to_nat(2221195325u);
v___x_2938_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_));
v___x_2939_ = l_Lean_Name_num___override(v___x_2938_, v___x_2937_);
return v___x_2939_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; 
v___x_2941_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_));
v___x_2942_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_);
v___x_2943_ = l_Lean_Name_str___override(v___x_2942_, v___x_2941_);
return v___x_2943_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; 
v___x_2945_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_));
v___x_2946_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_);
v___x_2947_ = l_Lean_Name_str___override(v___x_2946_, v___x_2945_);
return v___x_2947_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; 
v___x_2948_ = lean_unsigned_to_nat(2u);
v___x_2949_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_);
v___x_2950_ = l_Lean_Name_num___override(v___x_2949_, v___x_2948_);
return v___x_2950_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2952_; uint8_t v___x_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; 
v___x_2952_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__2));
v___x_2953_ = 0;
v___x_2954_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_);
v___x_2955_ = l_Lean_registerTraceClass(v___x_2952_, v___x_2953_, v___x_2954_);
return v___x_2955_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2____boxed(lean_object* v_a_2956_){
_start:
{
lean_object* v_res_2957_; 
v_res_2957_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_();
return v_res_2957_;
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
