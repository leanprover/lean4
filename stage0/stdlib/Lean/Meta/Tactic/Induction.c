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
lean_object* v___f_133_; lean_object* v___x_6938__overap_134_; lean_object* v___x_135_; 
v___f_133_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__4___closed__0));
v___x_6938__overap_134_ = lean_panic_fn_borrowed(v___f_133_, v_msg_127_);
lean_inc(v___y_131_);
lean_inc_ref(v___y_130_);
lean_inc(v___y_129_);
lean_inc_ref(v___y_128_);
v___x_135_ = lean_apply_5(v___x_6938__overap_134_, v___y_128_, v___y_129_, v___y_130_, v___y_131_, lean_box(0));
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
size_t v_x_8244__boxed_360_; size_t v_x_8245__boxed_361_; lean_object* v_res_362_; 
v_x_8244__boxed_360_ = lean_unbox_usize(v_x_356_);
lean_dec(v_x_356_);
v_x_8245__boxed_361_ = lean_unbox_usize(v_x_357_);
lean_dec(v_x_357_);
v_res_362_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2___redArg(v_x_355_, v_x_8244__boxed_360_, v_x_8245__boxed_361_, v_x_358_, v_x_359_);
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
lean_object* v___x_374_; lean_object* v_mctx_375_; lean_object* v_cache_376_; lean_object* v_zetaDeltaFVarIds_377_; lean_object* v_postponed_378_; lean_object* v_diag_379_; lean_object* v___x_381_; uint8_t v_isShared_382_; uint8_t v_isSharedCheck_408_; 
v___x_374_ = lean_st_ref_take(v___y_372_);
v_mctx_375_ = lean_ctor_get(v___x_374_, 0);
v_cache_376_ = lean_ctor_get(v___x_374_, 1);
v_zetaDeltaFVarIds_377_ = lean_ctor_get(v___x_374_, 2);
v_postponed_378_ = lean_ctor_get(v___x_374_, 3);
v_diag_379_ = lean_ctor_get(v___x_374_, 4);
v_isSharedCheck_408_ = !lean_is_exclusive(v___x_374_);
if (v_isSharedCheck_408_ == 0)
{
v___x_381_ = v___x_374_;
v_isShared_382_ = v_isSharedCheck_408_;
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
v_isShared_382_ = v_isSharedCheck_408_;
goto v_resetjp_380_;
}
v_resetjp_380_:
{
lean_object* v_depth_383_; lean_object* v_levelAssignDepth_384_; lean_object* v_lmvarCounter_385_; lean_object* v_mvarCounter_386_; lean_object* v_lDecls_387_; lean_object* v_decls_388_; lean_object* v_userNames_389_; lean_object* v_lAssignment_390_; lean_object* v_eAssignment_391_; lean_object* v_dAssignment_392_; lean_object* v_synthNormMemo_393_; lean_object* v___x_395_; uint8_t v_isShared_396_; uint8_t v_isSharedCheck_407_; 
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
v_synthNormMemo_393_ = lean_ctor_get(v_mctx_375_, 10);
v_isSharedCheck_407_ = !lean_is_exclusive(v_mctx_375_);
if (v_isSharedCheck_407_ == 0)
{
v___x_395_ = v_mctx_375_;
v_isShared_396_ = v_isSharedCheck_407_;
goto v_resetjp_394_;
}
else
{
lean_inc(v_synthNormMemo_393_);
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
v___x_395_ = lean_box(0);
v_isShared_396_ = v_isSharedCheck_407_;
goto v_resetjp_394_;
}
v_resetjp_394_:
{
lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_400_; 
v___x_397_ = lean_box(0);
v___x_398_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0___redArg(v_eAssignment_391_, v_mvarId_370_, v_val_371_);
if (v_isShared_396_ == 0)
{
lean_ctor_set(v___x_395_, 8, v___x_398_);
v___x_400_ = v___x_395_;
goto v_reusejp_399_;
}
else
{
lean_object* v_reuseFailAlloc_406_; 
v_reuseFailAlloc_406_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_406_, 0, v_depth_383_);
lean_ctor_set(v_reuseFailAlloc_406_, 1, v_levelAssignDepth_384_);
lean_ctor_set(v_reuseFailAlloc_406_, 2, v_lmvarCounter_385_);
lean_ctor_set(v_reuseFailAlloc_406_, 3, v_mvarCounter_386_);
lean_ctor_set(v_reuseFailAlloc_406_, 4, v_lDecls_387_);
lean_ctor_set(v_reuseFailAlloc_406_, 5, v_decls_388_);
lean_ctor_set(v_reuseFailAlloc_406_, 6, v_userNames_389_);
lean_ctor_set(v_reuseFailAlloc_406_, 7, v_lAssignment_390_);
lean_ctor_set(v_reuseFailAlloc_406_, 8, v___x_398_);
lean_ctor_set(v_reuseFailAlloc_406_, 9, v_dAssignment_392_);
lean_ctor_set(v_reuseFailAlloc_406_, 10, v_synthNormMemo_393_);
v___x_400_ = v_reuseFailAlloc_406_;
goto v_reusejp_399_;
}
v_reusejp_399_:
{
lean_object* v___x_402_; 
if (v_isShared_382_ == 0)
{
lean_ctor_set(v___x_381_, 0, v___x_400_);
v___x_402_ = v___x_381_;
goto v_reusejp_401_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v___x_400_);
lean_ctor_set(v_reuseFailAlloc_405_, 1, v_cache_376_);
lean_ctor_set(v_reuseFailAlloc_405_, 2, v_zetaDeltaFVarIds_377_);
lean_ctor_set(v_reuseFailAlloc_405_, 3, v_postponed_378_);
lean_ctor_set(v_reuseFailAlloc_405_, 4, v_diag_379_);
v___x_402_ = v_reuseFailAlloc_405_;
goto v_reusejp_401_;
}
v_reusejp_401_:
{
lean_object* v___x_403_; lean_object* v___x_404_; 
v___x_403_ = lean_st_ref_put(v___y_372_, v___x_402_);
v___x_404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_404_, 0, v___x_397_);
return v___x_404_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0___redArg___boxed(lean_object* v_mvarId_409_, lean_object* v_val_410_, lean_object* v___y_411_, lean_object* v___y_412_){
_start:
{
lean_object* v_res_413_; 
v_res_413_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0___redArg(v_mvarId_409_, v_val_410_, v___y_411_);
lean_dec(v___y_411_);
return v_res_413_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__3(size_t v_sz_414_, size_t v_i_415_, lean_object* v_bs_416_){
_start:
{
uint8_t v___x_417_; 
v___x_417_ = lean_usize_dec_lt(v_i_415_, v_sz_414_);
if (v___x_417_ == 0)
{
return v_bs_416_;
}
else
{
lean_object* v_v_418_; lean_object* v___x_419_; lean_object* v_bs_x27_420_; lean_object* v___x_421_; size_t v___x_422_; size_t v___x_423_; lean_object* v___x_424_; 
v_v_418_ = lean_array_uget(v_bs_416_, v_i_415_);
v___x_419_ = lean_unsigned_to_nat(0u);
v_bs_x27_420_ = lean_array_uset(v_bs_416_, v_i_415_, v___x_419_);
v___x_421_ = l_Lean_mkFVar(v_v_418_);
v___x_422_ = ((size_t)1ULL);
v___x_423_ = lean_usize_add(v_i_415_, v___x_422_);
v___x_424_ = lean_array_uset(v_bs_x27_420_, v_i_415_, v___x_421_);
v_i_415_ = v___x_423_;
v_bs_416_ = v___x_424_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__3___boxed(lean_object* v_sz_426_, lean_object* v_i_427_, lean_object* v_bs_428_){
_start:
{
size_t v_sz_boxed_429_; size_t v_i_boxed_430_; lean_object* v_res_431_; 
v_sz_boxed_429_ = lean_unbox_usize(v_sz_426_);
lean_dec(v_sz_426_);
v_i_boxed_430_ = lean_unbox_usize(v_i_427_);
lean_dec(v_i_427_);
v_res_431_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__3(v_sz_boxed_429_, v_i_boxed_430_, v_bs_428_);
return v_res_431_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1_spec__2(lean_object* v_msgData_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_){
_start:
{
lean_object* v___x_438_; lean_object* v_env_439_; uint8_t v___x_440_; lean_object* v_env_441_; lean_object* v___x_442_; lean_object* v_toCold_443_; lean_object* v_mctx_444_; lean_object* v_lctx_445_; lean_object* v_options_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; 
v___x_438_ = lean_st_ref_get(v___y_436_);
v_env_439_ = lean_ctor_get(v___x_438_, 0);
lean_inc_ref(v_env_439_);
lean_dec(v___x_438_);
v___x_440_ = 0;
v_env_441_ = l_Lean_Environment_setRecordingDeps(v_env_439_, v___x_440_);
v___x_442_ = lean_st_ref_get(v___y_434_);
v_toCold_443_ = lean_ctor_get(v___y_435_, 0);
v_mctx_444_ = lean_ctor_get(v___x_442_, 0);
lean_inc_ref(v_mctx_444_);
lean_dec(v___x_442_);
v_lctx_445_ = lean_ctor_get(v___y_433_, 2);
v_options_446_ = lean_ctor_get(v_toCold_443_, 2);
lean_inc_ref(v_options_446_);
lean_inc_ref(v_lctx_445_);
v___x_447_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_447_, 0, v_env_441_);
lean_ctor_set(v___x_447_, 1, v_mctx_444_);
lean_ctor_set(v___x_447_, 2, v_lctx_445_);
lean_ctor_set(v___x_447_, 3, v_options_446_);
v___x_448_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_448_, 0, v___x_447_);
lean_ctor_set(v___x_448_, 1, v_msgData_432_);
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
lean_object* v_ref_469_; lean_object* v___x_470_; lean_object* v_a_471_; lean_object* v___x_473_; uint8_t v_isShared_474_; uint8_t v_isSharedCheck_516_; 
v_ref_469_ = lean_ctor_get(v___y_466_, 2);
v___x_470_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1_spec__2(v_msg_463_, v___y_464_, v___y_465_, v___y_466_, v___y_467_);
v_a_471_ = lean_ctor_get(v___x_470_, 0);
v_isSharedCheck_516_ = !lean_is_exclusive(v___x_470_);
if (v_isSharedCheck_516_ == 0)
{
v___x_473_ = v___x_470_;
v_isShared_474_ = v_isSharedCheck_516_;
goto v_resetjp_472_;
}
else
{
lean_inc(v_a_471_);
lean_dec(v___x_470_);
v___x_473_ = lean_box(0);
v_isShared_474_ = v_isSharedCheck_516_;
goto v_resetjp_472_;
}
v_resetjp_472_:
{
lean_object* v___x_475_; lean_object* v_traceState_476_; lean_object* v_env_477_; lean_object* v_nextMacroScope_478_; lean_object* v_ngen_479_; lean_object* v_auxDeclNGen_480_; lean_object* v_cache_481_; lean_object* v_recordedDeps_482_; lean_object* v_messages_483_; lean_object* v_infoState_484_; lean_object* v_snapshotTasks_485_; lean_object* v___x_487_; uint8_t v_isShared_488_; uint8_t v_isSharedCheck_515_; 
v___x_475_ = lean_st_ref_take(v___y_467_);
v_traceState_476_ = lean_ctor_get(v___x_475_, 4);
v_env_477_ = lean_ctor_get(v___x_475_, 0);
v_nextMacroScope_478_ = lean_ctor_get(v___x_475_, 1);
v_ngen_479_ = lean_ctor_get(v___x_475_, 2);
v_auxDeclNGen_480_ = lean_ctor_get(v___x_475_, 3);
v_cache_481_ = lean_ctor_get(v___x_475_, 5);
v_recordedDeps_482_ = lean_ctor_get(v___x_475_, 6);
v_messages_483_ = lean_ctor_get(v___x_475_, 7);
v_infoState_484_ = lean_ctor_get(v___x_475_, 8);
v_snapshotTasks_485_ = lean_ctor_get(v___x_475_, 9);
v_isSharedCheck_515_ = !lean_is_exclusive(v___x_475_);
if (v_isSharedCheck_515_ == 0)
{
v___x_487_ = v___x_475_;
v_isShared_488_ = v_isSharedCheck_515_;
goto v_resetjp_486_;
}
else
{
lean_inc(v_snapshotTasks_485_);
lean_inc(v_infoState_484_);
lean_inc(v_messages_483_);
lean_inc(v_recordedDeps_482_);
lean_inc(v_cache_481_);
lean_inc(v_traceState_476_);
lean_inc(v_auxDeclNGen_480_);
lean_inc(v_ngen_479_);
lean_inc(v_nextMacroScope_478_);
lean_inc(v_env_477_);
lean_dec(v___x_475_);
v___x_487_ = lean_box(0);
v_isShared_488_ = v_isSharedCheck_515_;
goto v_resetjp_486_;
}
v_resetjp_486_:
{
uint64_t v_tid_489_; lean_object* v_traces_490_; lean_object* v___x_492_; uint8_t v_isShared_493_; uint8_t v_isSharedCheck_514_; 
v_tid_489_ = lean_ctor_get_uint64(v_traceState_476_, sizeof(void*)*1);
v_traces_490_ = lean_ctor_get(v_traceState_476_, 0);
v_isSharedCheck_514_ = !lean_is_exclusive(v_traceState_476_);
if (v_isSharedCheck_514_ == 0)
{
v___x_492_ = v_traceState_476_;
v_isShared_493_ = v_isSharedCheck_514_;
goto v_resetjp_491_;
}
else
{
lean_inc(v_traces_490_);
lean_dec(v_traceState_476_);
v___x_492_ = lean_box(0);
v_isShared_493_ = v_isSharedCheck_514_;
goto v_resetjp_491_;
}
v_resetjp_491_:
{
lean_object* v___x_494_; lean_object* v___x_495_; double v___x_496_; uint8_t v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_505_; 
v___x_494_ = lean_box(0);
v___x_495_ = lean_box(0);
v___x_496_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1___closed__0);
v___x_497_ = 0;
v___x_498_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1___closed__1));
v___x_499_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_499_, 0, v_cls_462_);
lean_ctor_set(v___x_499_, 1, v___x_495_);
lean_ctor_set(v___x_499_, 2, v___x_498_);
lean_ctor_set_float(v___x_499_, sizeof(void*)*3, v___x_496_);
lean_ctor_set_float(v___x_499_, sizeof(void*)*3 + 8, v___x_496_);
lean_ctor_set_uint8(v___x_499_, sizeof(void*)*3 + 16, v___x_497_);
v___x_500_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1___closed__2));
v___x_501_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_501_, 0, v___x_499_);
lean_ctor_set(v___x_501_, 1, v_a_471_);
lean_ctor_set(v___x_501_, 2, v___x_500_);
lean_inc(v_ref_469_);
v___x_502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_502_, 0, v_ref_469_);
lean_ctor_set(v___x_502_, 1, v___x_501_);
v___x_503_ = l_Lean_PersistentArray_push___redArg(v_traces_490_, v___x_502_);
if (v_isShared_493_ == 0)
{
lean_ctor_set(v___x_492_, 0, v___x_503_);
v___x_505_ = v___x_492_;
goto v_reusejp_504_;
}
else
{
lean_object* v_reuseFailAlloc_513_; 
v_reuseFailAlloc_513_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_513_, 0, v___x_503_);
lean_ctor_set_uint64(v_reuseFailAlloc_513_, sizeof(void*)*1, v_tid_489_);
v___x_505_ = v_reuseFailAlloc_513_;
goto v_reusejp_504_;
}
v_reusejp_504_:
{
lean_object* v___x_507_; 
if (v_isShared_488_ == 0)
{
lean_ctor_set(v___x_487_, 4, v___x_505_);
v___x_507_ = v___x_487_;
goto v_reusejp_506_;
}
else
{
lean_object* v_reuseFailAlloc_512_; 
v_reuseFailAlloc_512_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_512_, 0, v_env_477_);
lean_ctor_set(v_reuseFailAlloc_512_, 1, v_nextMacroScope_478_);
lean_ctor_set(v_reuseFailAlloc_512_, 2, v_ngen_479_);
lean_ctor_set(v_reuseFailAlloc_512_, 3, v_auxDeclNGen_480_);
lean_ctor_set(v_reuseFailAlloc_512_, 4, v___x_505_);
lean_ctor_set(v_reuseFailAlloc_512_, 5, v_cache_481_);
lean_ctor_set(v_reuseFailAlloc_512_, 6, v_recordedDeps_482_);
lean_ctor_set(v_reuseFailAlloc_512_, 7, v_messages_483_);
lean_ctor_set(v_reuseFailAlloc_512_, 8, v_infoState_484_);
lean_ctor_set(v_reuseFailAlloc_512_, 9, v_snapshotTasks_485_);
v___x_507_ = v_reuseFailAlloc_512_;
goto v_reusejp_506_;
}
v_reusejp_506_:
{
lean_object* v___x_508_; lean_object* v___x_510_; 
v___x_508_ = lean_st_ref_put(v___y_467_, v___x_507_);
if (v_isShared_474_ == 0)
{
lean_ctor_set(v___x_473_, 0, v___x_494_);
v___x_510_ = v___x_473_;
goto v_reusejp_509_;
}
else
{
lean_object* v_reuseFailAlloc_511_; 
v_reuseFailAlloc_511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_511_, 0, v___x_494_);
v___x_510_ = v_reuseFailAlloc_511_;
goto v_reusejp_509_;
}
v_reusejp_509_:
{
return v___x_510_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1___boxed(lean_object* v_cls_517_, lean_object* v_msg_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_){
_start:
{
lean_object* v_res_524_; 
v_res_524_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1(v_cls_517_, v_msg_518_, v___y_519_, v___y_520_, v___y_521_, v___y_522_);
lean_dec(v___y_522_);
lean_dec_ref(v___y_521_);
lean_dec(v___y_520_);
lean_dec_ref(v___y_519_);
return v_res_524_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5(void){
_start:
{
lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; 
v___x_534_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__2));
v___x_535_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__4));
v___x_536_ = l_Lean_Name_append(v___x_535_, v___x_534_);
return v___x_536_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__7(void){
_start:
{
lean_object* v___x_538_; lean_object* v___x_539_; 
v___x_538_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__6));
v___x_539_ = l_Lean_stringToMessageData(v___x_538_);
return v___x_539_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__9(void){
_start:
{
lean_object* v___x_541_; lean_object* v___x_542_; 
v___x_541_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__8));
v___x_542_ = l_Lean_stringToMessageData(v___x_541_);
return v___x_542_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__11(void){
_start:
{
lean_object* v___x_544_; lean_object* v___x_545_; 
v___x_544_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__10));
v___x_545_ = l_Lean_stringToMessageData(v___x_544_);
return v___x_545_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__15(void){
_start:
{
lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; 
v___x_549_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__14));
v___x_550_ = lean_unsigned_to_nat(15u);
v___x_551_ = lean_unsigned_to_nat(120u);
v___x_552_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__13));
v___x_553_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__12));
v___x_554_ = l_mkPanicMessageWithDecl(v___x_553_, v___x_552_, v___x_551_, v___x_550_, v___x_549_);
return v___x_554_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop(lean_object* v_mvarId_555_, lean_object* v_givenNames_556_, lean_object* v_recursorInfo_557_, lean_object* v_reverted_558_, lean_object* v_major_559_, lean_object* v_indices_560_, lean_object* v_baseSubst_561_, lean_object* v_initialArity_562_, lean_object* v_numMinors_563_, lean_object* v_pos_564_, lean_object* v_minorIdx_565_, lean_object* v_recursor_566_, lean_object* v_recursorType_567_, uint8_t v_consumedMajor_568_, lean_object* v_subgoals_569_, lean_object* v_a_570_, lean_object* v_a_571_, lean_object* v_a_572_, lean_object* v_a_573_){
_start:
{
lean_object* v___y_576_; lean_object* v___y_577_; lean_object* v___y_578_; lean_object* v___y_579_; lean_object* v___x_632_; 
v___x_632_ = l_Lean_Meta_whnfForall(v_recursorType_567_, v_a_570_, v_a_571_, v_a_572_, v_a_573_);
if (lean_obj_tag(v___x_632_) == 0)
{
lean_object* v_a_633_; uint8_t v___x_646_; 
v_a_633_ = lean_ctor_get(v___x_632_, 0);
lean_inc(v_a_633_);
lean_dec_ref_known(v___x_632_, 1);
v___x_646_ = l_Lean_Expr_isForall(v_a_633_);
if (v___x_646_ == 0)
{
lean_dec(v_a_633_);
lean_dec(v_minorIdx_565_);
lean_dec(v_pos_564_);
lean_dec(v_baseSubst_561_);
lean_dec_ref(v_major_559_);
goto v___jp_634_;
}
else
{
lean_object* v_numArgs_647_; uint8_t v___x_648_; uint8_t v___y_650_; lean_object* v___y_651_; lean_object* v___y_652_; lean_object* v___y_653_; lean_object* v___y_654_; lean_object* v___y_655_; lean_object* v___y_656_; lean_object* v___y_657_; lean_object* v___y_658_; lean_object* v___y_659_; lean_object* v___y_660_; lean_object* v___y_661_; lean_object* v___y_662_; lean_object* v___y_663_; uint8_t v___y_664_; lean_object* v___y_700_; lean_object* v___y_701_; uint8_t v___y_702_; lean_object* v___y_703_; lean_object* v___y_704_; lean_object* v___y_705_; lean_object* v___y_706_; lean_object* v___y_707_; lean_object* v___y_708_; lean_object* v___y_709_; lean_object* v___y_710_; lean_object* v___y_711_; lean_object* v___y_712_; lean_object* v___y_713_; lean_object* v___y_731_; uint8_t v___y_732_; lean_object* v___y_733_; lean_object* v___y_734_; lean_object* v___y_735_; lean_object* v___y_736_; lean_object* v___y_737_; lean_object* v___y_738_; lean_object* v___y_739_; lean_object* v___y_740_; lean_object* v___y_741_; lean_object* v___y_742_; lean_object* v___y_743_; lean_object* v___y_787_; lean_object* v___y_788_; uint8_t v___y_789_; lean_object* v___y_790_; lean_object* v___y_791_; lean_object* v___y_792_; lean_object* v___y_793_; lean_object* v___y_794_; lean_object* v___y_795_; lean_object* v___y_807_; lean_object* v___y_808_; lean_object* v___y_809_; lean_object* v___y_810_; lean_object* v___y_811_; lean_object* v___y_812_; lean_object* v___y_813_; uint8_t v___y_814_; uint8_t v___y_829_; lean_object* v___y_830_; lean_object* v___y_831_; lean_object* v___y_832_; lean_object* v___y_833_; lean_object* v___y_834_; lean_object* v___y_835_; lean_object* v___y_836_; 
v_numArgs_647_ = lean_ctor_get(v_recursorInfo_557_, 3);
v___x_648_ = lean_nat_dec_lt(v_pos_564_, v_numArgs_647_);
if (v___x_648_ == 0)
{
lean_dec(v_a_633_);
lean_dec(v_minorIdx_565_);
lean_dec(v_pos_564_);
lean_dec(v_baseSubst_561_);
lean_dec_ref(v_major_559_);
goto v___jp_634_;
}
else
{
lean_object* v___x_896_; uint8_t v___x_897_; 
v___x_896_ = l_Lean_Meta_RecursorInfo_firstIndexPos(v_recursorInfo_557_);
v___x_897_ = lean_nat_dec_eq(v_pos_564_, v___x_896_);
lean_dec(v___x_896_);
if (v___x_897_ == 0)
{
lean_object* v___x_898_; 
lean_inc(v_mvarId_555_);
v___x_898_ = l_Lean_MVarId_getTag(v_mvarId_555_, v_a_570_, v_a_571_, v_a_572_, v_a_573_);
if (lean_obj_tag(v___x_898_) == 0)
{
lean_object* v_a_899_; lean_object* v___y_901_; lean_object* v___y_902_; lean_object* v___y_903_; lean_object* v___y_904_; uint8_t v___x_915_; 
v_a_899_ = lean_ctor_get(v___x_898_, 0);
lean_inc(v_a_899_);
lean_dec_ref_known(v___x_898_, 1);
v___x_915_ = lean_nat_dec_le(v_numMinors_563_, v_minorIdx_565_);
if (v___x_915_ == 0)
{
v___y_901_ = v_a_570_;
v___y_902_ = v_a_571_;
v___y_903_ = v_a_572_;
v___y_904_ = v_a_573_;
goto v___jp_900_;
}
else
{
lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; 
v___x_916_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1));
v___x_917_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9);
lean_inc(v_mvarId_555_);
v___x_918_ = l_Lean_Meta_throwTacticEx___redArg(v___x_916_, v_mvarId_555_, v___x_917_, v_a_570_, v_a_571_, v_a_572_, v_a_573_);
if (lean_obj_tag(v___x_918_) == 0)
{
lean_dec_ref_known(v___x_918_, 1);
v___y_901_ = v_a_570_;
v___y_902_ = v_a_571_;
v___y_903_ = v_a_572_;
v___y_904_ = v_a_573_;
goto v___jp_900_;
}
else
{
lean_object* v_a_919_; lean_object* v___x_921_; uint8_t v_isShared_922_; uint8_t v_isSharedCheck_926_; 
lean_dec(v_a_899_);
lean_dec(v_a_633_);
lean_dec_ref(v_subgoals_569_);
lean_dec_ref(v_recursor_566_);
lean_dec(v_minorIdx_565_);
lean_dec(v_pos_564_);
lean_dec(v_baseSubst_561_);
lean_dec_ref(v_major_559_);
lean_dec(v_mvarId_555_);
v_a_919_ = lean_ctor_get(v___x_918_, 0);
v_isSharedCheck_926_ = !lean_is_exclusive(v___x_918_);
if (v_isSharedCheck_926_ == 0)
{
v___x_921_ = v___x_918_;
v_isShared_922_ = v_isSharedCheck_926_;
goto v_resetjp_920_;
}
else
{
lean_inc(v_a_919_);
lean_dec(v___x_918_);
v___x_921_ = lean_box(0);
v_isShared_922_ = v_isSharedCheck_926_;
goto v_resetjp_920_;
}
v_resetjp_920_:
{
lean_object* v___x_924_; 
if (v_isShared_922_ == 0)
{
v___x_924_ = v___x_921_;
goto v_reusejp_923_;
}
else
{
lean_object* v_reuseFailAlloc_925_; 
v_reuseFailAlloc_925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_925_, 0, v_a_919_);
v___x_924_ = v_reuseFailAlloc_925_;
goto v_reusejp_923_;
}
v_reusejp_923_:
{
return v___x_924_;
}
}
}
}
v___jp_900_:
{
if (lean_obj_tag(v_a_633_) == 7)
{
lean_object* v_binderName_905_; lean_object* v_binderType_906_; uint8_t v_binderInfo_907_; lean_object* v___x_908_; lean_object* v___x_909_; uint8_t v___x_910_; 
v_binderName_905_ = lean_ctor_get(v_a_633_, 0);
v_binderType_906_ = lean_ctor_get(v_a_633_, 1);
v_binderInfo_907_ = lean_ctor_get_uint8(v_a_633_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_906_);
v___x_908_ = l_Lean_Expr_headBeta(v_binderType_906_);
v___x_909_ = lean_unsigned_to_nat(1u);
v___x_910_ = lean_nat_dec_eq(v_numMinors_563_, v___x_909_);
if (v___x_910_ == 0)
{
lean_object* v___x_911_; lean_object* v___x_912_; 
v___x_911_ = l_Lean_Name_eraseMacroScopes(v_binderName_905_);
v___x_912_ = l_Lean_Name_append(v_a_899_, v___x_911_);
v___y_829_ = v_binderInfo_907_;
v___y_830_ = v___y_901_;
v___y_831_ = v___y_903_;
v___y_832_ = v___x_908_;
v___y_833_ = v___x_909_;
v___y_834_ = v___y_902_;
v___y_835_ = v___y_904_;
v___y_836_ = v___x_912_;
goto v___jp_828_;
}
else
{
v___y_829_ = v_binderInfo_907_;
v___y_830_ = v___y_901_;
v___y_831_ = v___y_903_;
v___y_832_ = v___x_908_;
v___y_833_ = v___x_909_;
v___y_834_ = v___y_902_;
v___y_835_ = v___y_904_;
v___y_836_ = v_a_899_;
goto v___jp_828_;
}
}
else
{
lean_object* v___x_913_; lean_object* v___x_914_; 
lean_dec(v_a_899_);
lean_dec(v_a_633_);
lean_dec_ref(v_subgoals_569_);
lean_dec_ref(v_recursor_566_);
lean_dec(v_minorIdx_565_);
lean_dec(v_pos_564_);
lean_dec(v_baseSubst_561_);
lean_dec_ref(v_major_559_);
lean_dec(v_mvarId_555_);
v___x_913_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__15, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__15_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__15);
v___x_914_ = l_panic___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__4(v___x_913_, v___y_901_, v___y_902_, v___y_903_, v___y_904_);
return v___x_914_;
}
}
}
else
{
lean_object* v_a_927_; lean_object* v___x_929_; uint8_t v_isShared_930_; uint8_t v_isSharedCheck_934_; 
lean_dec(v_a_633_);
lean_dec_ref(v_subgoals_569_);
lean_dec_ref(v_recursor_566_);
lean_dec(v_minorIdx_565_);
lean_dec(v_pos_564_);
lean_dec(v_baseSubst_561_);
lean_dec_ref(v_major_559_);
lean_dec(v_mvarId_555_);
v_a_927_ = lean_ctor_get(v___x_898_, 0);
v_isSharedCheck_934_ = !lean_is_exclusive(v___x_898_);
if (v_isSharedCheck_934_ == 0)
{
v___x_929_ = v___x_898_;
v_isShared_930_ = v_isSharedCheck_934_;
goto v_resetjp_928_;
}
else
{
lean_inc(v_a_927_);
lean_dec(v___x_898_);
v___x_929_ = lean_box(0);
v_isShared_930_ = v_isSharedCheck_934_;
goto v_resetjp_928_;
}
v_resetjp_928_:
{
lean_object* v___x_932_; 
if (v_isShared_930_ == 0)
{
v___x_932_ = v___x_929_;
goto v_reusejp_931_;
}
else
{
lean_object* v_reuseFailAlloc_933_; 
v_reuseFailAlloc_933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_933_, 0, v_a_927_);
v___x_932_ = v_reuseFailAlloc_933_;
goto v_reusejp_931_;
}
v_reusejp_931_:
{
return v___x_932_;
}
}
}
}
else
{
lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v_fst_938_; lean_object* v_snd_939_; uint8_t v___x_955_; 
v___x_935_ = lean_unsigned_to_nat(0u);
v___x_936_ = lean_array_get_size(v_indices_560_);
v___x_955_ = lean_nat_dec_lt(v___x_935_, v___x_936_);
if (v___x_955_ == 0)
{
v_fst_938_ = v_recursor_566_;
v_snd_939_ = v_a_633_;
goto v___jp_937_;
}
else
{
lean_object* v___x_956_; size_t v___x_957_; size_t v___x_958_; lean_object* v___x_959_; 
v___x_956_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_956_, 0, v_recursor_566_);
lean_ctor_set(v___x_956_, 1, v_a_633_);
v___x_957_ = ((size_t)0ULL);
v___x_958_ = lean_usize_of_nat(v___x_936_);
lean_inc(v_mvarId_555_);
v___x_959_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__5(v_mvarId_555_, v_indices_560_, v___x_957_, v___x_958_, v___x_956_, v_a_570_, v_a_571_, v_a_572_, v_a_573_);
if (lean_obj_tag(v___x_959_) == 0)
{
lean_object* v_a_960_; lean_object* v_fst_961_; lean_object* v_snd_962_; 
v_a_960_ = lean_ctor_get(v___x_959_, 0);
lean_inc(v_a_960_);
lean_dec_ref_known(v___x_959_, 1);
v_fst_961_ = lean_ctor_get(v_a_960_, 0);
lean_inc(v_fst_961_);
v_snd_962_ = lean_ctor_get(v_a_960_, 1);
lean_inc(v_snd_962_);
lean_dec(v_a_960_);
v_fst_938_ = v_fst_961_;
v_snd_939_ = v_snd_962_;
goto v___jp_937_;
}
else
{
lean_object* v_a_963_; lean_object* v___x_965_; uint8_t v_isShared_966_; uint8_t v_isSharedCheck_970_; 
lean_dec_ref(v_subgoals_569_);
lean_dec(v_minorIdx_565_);
lean_dec(v_pos_564_);
lean_dec(v_baseSubst_561_);
lean_dec_ref(v_major_559_);
lean_dec(v_mvarId_555_);
v_a_963_ = lean_ctor_get(v___x_959_, 0);
v_isSharedCheck_970_ = !lean_is_exclusive(v___x_959_);
if (v_isSharedCheck_970_ == 0)
{
v___x_965_ = v___x_959_;
v_isShared_966_ = v_isSharedCheck_970_;
goto v_resetjp_964_;
}
else
{
lean_inc(v_a_963_);
lean_dec(v___x_959_);
v___x_965_ = lean_box(0);
v_isShared_966_ = v_isSharedCheck_970_;
goto v_resetjp_964_;
}
v_resetjp_964_:
{
lean_object* v___x_968_; 
if (v_isShared_966_ == 0)
{
v___x_968_ = v___x_965_;
goto v_reusejp_967_;
}
else
{
lean_object* v_reuseFailAlloc_969_; 
v_reuseFailAlloc_969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_969_, 0, v_a_963_);
v___x_968_ = v_reuseFailAlloc_969_;
goto v_reusejp_967_;
}
v_reusejp_967_:
{
return v___x_968_;
}
}
}
}
v___jp_937_:
{
lean_object* v___x_940_; lean_object* v___x_941_; 
lean_inc_ref(v_major_559_);
v___x_940_ = l_Lean_Expr_app___override(v_fst_938_, v_major_559_);
lean_inc(v_mvarId_555_);
v___x_941_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTypeBody(v_mvarId_555_, v_snd_939_, v_major_559_, v_a_570_, v_a_571_, v_a_572_, v_a_573_);
if (lean_obj_tag(v___x_941_) == 0)
{
lean_object* v_a_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; 
v_a_942_ = lean_ctor_get(v___x_941_, 0);
lean_inc(v_a_942_);
lean_dec_ref_known(v___x_941_, 1);
v___x_943_ = lean_unsigned_to_nat(1u);
v___x_944_ = lean_nat_add(v_pos_564_, v___x_943_);
lean_dec(v_pos_564_);
v___x_945_ = lean_nat_add(v___x_944_, v___x_936_);
lean_dec(v___x_944_);
v_pos_564_ = v___x_945_;
v_recursor_566_ = v___x_940_;
v_recursorType_567_ = v_a_942_;
v_consumedMajor_568_ = v___x_646_;
goto _start;
}
else
{
lean_object* v_a_947_; lean_object* v___x_949_; uint8_t v_isShared_950_; uint8_t v_isSharedCheck_954_; 
lean_dec_ref(v___x_940_);
lean_dec_ref(v_subgoals_569_);
lean_dec(v_minorIdx_565_);
lean_dec(v_pos_564_);
lean_dec(v_baseSubst_561_);
lean_dec_ref(v_major_559_);
lean_dec(v_mvarId_555_);
v_a_947_ = lean_ctor_get(v___x_941_, 0);
v_isSharedCheck_954_ = !lean_is_exclusive(v___x_941_);
if (v_isSharedCheck_954_ == 0)
{
v___x_949_ = v___x_941_;
v_isShared_950_ = v_isSharedCheck_954_;
goto v_resetjp_948_;
}
else
{
lean_inc(v_a_947_);
lean_dec(v___x_941_);
v___x_949_ = lean_box(0);
v_isShared_950_ = v_isSharedCheck_954_;
goto v_resetjp_948_;
}
v_resetjp_948_:
{
lean_object* v___x_952_; 
if (v_isShared_950_ == 0)
{
v___x_952_ = v___x_949_;
goto v_reusejp_951_;
}
else
{
lean_object* v_reuseFailAlloc_953_; 
v_reuseFailAlloc_953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_953_, 0, v_a_947_);
v___x_952_ = v_reuseFailAlloc_953_;
goto v_reusejp_951_;
}
v_reusejp_951_:
{
return v___x_952_;
}
}
}
}
}
}
v___jp_649_:
{
lean_object* v___x_665_; 
v___x_665_ = l_Lean_Meta_introNCore(v___y_662_, v___y_657_, v___y_663_, v___y_664_, v___y_650_, v___y_655_, v___y_658_, v___y_654_, v___y_656_);
if (lean_obj_tag(v___x_665_) == 0)
{
lean_object* v_a_666_; lean_object* v_fst_667_; lean_object* v_snd_668_; lean_object* v___x_669_; lean_object* v___x_670_; 
v_a_666_ = lean_ctor_get(v___x_665_, 0);
lean_inc(v_a_666_);
lean_dec_ref_known(v___x_665_, 1);
v_fst_667_ = lean_ctor_get(v_a_666_, 0);
lean_inc(v_fst_667_);
v_snd_668_ = lean_ctor_get(v_a_666_, 1);
lean_inc(v_snd_668_);
lean_dec(v_a_666_);
v___x_669_ = lean_box(0);
v___x_670_ = l_Lean_Meta_introNCore(v_snd_668_, v___y_653_, v___x_669_, v___y_650_, v___x_648_, v___y_655_, v___y_658_, v___y_654_, v___y_656_);
if (lean_obj_tag(v___x_670_) == 0)
{
lean_object* v_a_671_; lean_object* v_fst_672_; lean_object* v_snd_673_; lean_object* v___x_674_; size_t v_sz_675_; size_t v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; 
v_a_671_ = lean_ctor_get(v___x_670_, 0);
lean_inc(v_a_671_);
lean_dec_ref_known(v___x_670_, 1);
v_fst_672_ = lean_ctor_get(v_a_671_, 0);
lean_inc(v_fst_672_);
v_snd_673_ = lean_ctor_get(v_a_671_, 1);
lean_inc(v_snd_673_);
lean_dec(v_a_671_);
lean_inc(v_baseSubst_561_);
lean_inc(v___y_659_);
v___x_674_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__2___redArg(v___y_652_, v_reverted_558_, v_fst_672_, v___y_659_, v___y_659_, v_baseSubst_561_);
lean_dec(v___y_659_);
lean_dec(v_fst_672_);
lean_dec(v___y_652_);
v_sz_675_ = lean_array_size(v_fst_667_);
v___x_676_ = ((size_t)0ULL);
v___x_677_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__3(v_sz_675_, v___x_676_, v_fst_667_);
v___x_678_ = lean_nat_add(v_pos_564_, v___y_651_);
lean_dec(v_pos_564_);
v___x_679_ = lean_nat_add(v_minorIdx_565_, v___y_651_);
lean_dec(v_minorIdx_565_);
v___x_680_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_680_, 0, v_snd_673_);
lean_ctor_set(v___x_680_, 1, v___x_677_);
lean_ctor_set(v___x_680_, 2, v___x_674_);
v___x_681_ = lean_array_push(v_subgoals_569_, v___x_680_);
v_pos_564_ = v___x_678_;
v_minorIdx_565_ = v___x_679_;
v_recursor_566_ = v___y_660_;
v_recursorType_567_ = v___y_661_;
v_subgoals_569_ = v___x_681_;
v_a_570_ = v___y_655_;
v_a_571_ = v___y_658_;
v_a_572_ = v___y_654_;
v_a_573_ = v___y_656_;
goto _start;
}
else
{
lean_object* v_a_683_; lean_object* v___x_685_; uint8_t v_isShared_686_; uint8_t v_isSharedCheck_690_; 
lean_dec(v_fst_667_);
lean_dec_ref(v___y_661_);
lean_dec_ref(v___y_660_);
lean_dec(v___y_659_);
lean_dec(v___y_652_);
lean_dec_ref(v_subgoals_569_);
lean_dec(v_minorIdx_565_);
lean_dec(v_pos_564_);
lean_dec(v_baseSubst_561_);
lean_dec_ref(v_major_559_);
lean_dec(v_mvarId_555_);
v_a_683_ = lean_ctor_get(v___x_670_, 0);
v_isSharedCheck_690_ = !lean_is_exclusive(v___x_670_);
if (v_isSharedCheck_690_ == 0)
{
v___x_685_ = v___x_670_;
v_isShared_686_ = v_isSharedCheck_690_;
goto v_resetjp_684_;
}
else
{
lean_inc(v_a_683_);
lean_dec(v___x_670_);
v___x_685_ = lean_box(0);
v_isShared_686_ = v_isSharedCheck_690_;
goto v_resetjp_684_;
}
v_resetjp_684_:
{
lean_object* v___x_688_; 
if (v_isShared_686_ == 0)
{
v___x_688_ = v___x_685_;
goto v_reusejp_687_;
}
else
{
lean_object* v_reuseFailAlloc_689_; 
v_reuseFailAlloc_689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_689_, 0, v_a_683_);
v___x_688_ = v_reuseFailAlloc_689_;
goto v_reusejp_687_;
}
v_reusejp_687_:
{
return v___x_688_;
}
}
}
}
else
{
lean_object* v_a_691_; lean_object* v___x_693_; uint8_t v_isShared_694_; uint8_t v_isSharedCheck_698_; 
lean_dec_ref(v___y_661_);
lean_dec_ref(v___y_660_);
lean_dec(v___y_659_);
lean_dec(v___y_653_);
lean_dec(v___y_652_);
lean_dec_ref(v_subgoals_569_);
lean_dec(v_minorIdx_565_);
lean_dec(v_pos_564_);
lean_dec(v_baseSubst_561_);
lean_dec_ref(v_major_559_);
lean_dec(v_mvarId_555_);
v_a_691_ = lean_ctor_get(v___x_665_, 0);
v_isSharedCheck_698_ = !lean_is_exclusive(v___x_665_);
if (v_isSharedCheck_698_ == 0)
{
v___x_693_ = v___x_665_;
v_isShared_694_ = v_isSharedCheck_698_;
goto v_resetjp_692_;
}
else
{
lean_inc(v_a_691_);
lean_dec(v___x_665_);
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
v___jp_699_:
{
lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; 
v___x_714_ = l_Lean_Expr_mvarId_x21(v___y_700_);
lean_dec_ref(v___y_700_);
v___x_715_ = l_Lean_Expr_fvarId_x21(v_major_559_);
v___x_716_ = l_Lean_MVarId_tryClear(v___x_714_, v___x_715_, v___y_710_, v___y_711_, v___y_712_, v___y_713_);
if (lean_obj_tag(v___x_716_) == 0)
{
uint8_t v_explicit_717_; 
v_explicit_717_ = lean_ctor_get_uint8(v___y_709_, sizeof(void*)*1);
if (v_explicit_717_ == 0)
{
lean_object* v_a_718_; lean_object* v_varNames_719_; 
v_a_718_ = lean_ctor_get(v___x_716_, 0);
lean_inc(v_a_718_);
lean_dec_ref_known(v___x_716_, 1);
v_varNames_719_ = lean_ctor_get(v___y_709_, 0);
lean_inc(v_varNames_719_);
lean_dec_ref(v___y_709_);
v___y_650_ = v___y_702_;
v___y_651_ = v___y_703_;
v___y_652_ = v___y_705_;
v___y_653_ = v___y_708_;
v___y_654_ = v___y_712_;
v___y_655_ = v___y_710_;
v___y_656_ = v___y_713_;
v___y_657_ = v___y_701_;
v___y_658_ = v___y_711_;
v___y_659_ = v___y_704_;
v___y_660_ = v___y_706_;
v___y_661_ = v___y_707_;
v___y_662_ = v_a_718_;
v___y_663_ = v_varNames_719_;
v___y_664_ = v___x_648_;
goto v___jp_649_;
}
else
{
lean_object* v_a_720_; lean_object* v_varNames_721_; 
v_a_720_ = lean_ctor_get(v___x_716_, 0);
lean_inc(v_a_720_);
lean_dec_ref_known(v___x_716_, 1);
v_varNames_721_ = lean_ctor_get(v___y_709_, 0);
lean_inc(v_varNames_721_);
lean_dec_ref(v___y_709_);
v___y_650_ = v___y_702_;
v___y_651_ = v___y_703_;
v___y_652_ = v___y_705_;
v___y_653_ = v___y_708_;
v___y_654_ = v___y_712_;
v___y_655_ = v___y_710_;
v___y_656_ = v___y_713_;
v___y_657_ = v___y_701_;
v___y_658_ = v___y_711_;
v___y_659_ = v___y_704_;
v___y_660_ = v___y_706_;
v___y_661_ = v___y_707_;
v___y_662_ = v_a_720_;
v___y_663_ = v_varNames_721_;
v___y_664_ = v___y_702_;
goto v___jp_649_;
}
}
else
{
lean_object* v_a_722_; lean_object* v___x_724_; uint8_t v_isShared_725_; uint8_t v_isSharedCheck_729_; 
lean_dec_ref(v___y_709_);
lean_dec(v___y_708_);
lean_dec_ref(v___y_707_);
lean_dec_ref(v___y_706_);
lean_dec(v___y_705_);
lean_dec(v___y_704_);
lean_dec(v___y_701_);
lean_dec_ref(v_subgoals_569_);
lean_dec(v_minorIdx_565_);
lean_dec(v_pos_564_);
lean_dec(v_baseSubst_561_);
lean_dec_ref(v_major_559_);
lean_dec(v_mvarId_555_);
v_a_722_ = lean_ctor_get(v___x_716_, 0);
v_isSharedCheck_729_ = !lean_is_exclusive(v___x_716_);
if (v_isSharedCheck_729_ == 0)
{
v___x_724_ = v___x_716_;
v_isShared_725_ = v_isSharedCheck_729_;
goto v_resetjp_723_;
}
else
{
lean_inc(v_a_722_);
lean_dec(v___x_716_);
v___x_724_ = lean_box(0);
v_isShared_725_ = v_isSharedCheck_729_;
goto v_resetjp_723_;
}
v_resetjp_723_:
{
lean_object* v___x_727_; 
if (v_isShared_725_ == 0)
{
v___x_727_ = v___x_724_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_728_; 
v_reuseFailAlloc_728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_728_, 0, v_a_722_);
v___x_727_ = v_reuseFailAlloc_728_;
goto v_reusejp_726_;
}
v_reusejp_726_:
{
return v___x_727_;
}
}
}
}
v___jp_730_:
{
lean_object* v___x_744_; 
v___x_744_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___y_734_, v___y_731_, v___y_738_, v___y_742_, v___y_739_, v___y_733_);
if (lean_obj_tag(v___x_744_) == 0)
{
lean_object* v_a_745_; lean_object* v___x_746_; lean_object* v___x_747_; 
v_a_745_ = lean_ctor_get(v___x_744_, 0);
lean_inc_n(v_a_745_, 2);
lean_dec_ref_known(v___x_744_, 1);
v___x_746_ = l_Lean_Expr_app___override(v_recursor_566_, v_a_745_);
lean_inc(v_mvarId_555_);
v___x_747_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTypeBody(v_mvarId_555_, v_a_633_, v_a_745_, v___y_738_, v___y_742_, v___y_739_, v___y_733_);
if (lean_obj_tag(v___x_747_) == 0)
{
lean_object* v_toCold_748_; lean_object* v_options_749_; uint8_t v_hasTrace_750_; 
v_toCold_748_ = lean_ctor_get(v___y_739_, 0);
v_options_749_ = lean_ctor_get(v_toCold_748_, 2);
v_hasTrace_750_ = lean_ctor_get_uint8(v_options_749_, sizeof(void*)*1);
if (v_hasTrace_750_ == 0)
{
lean_object* v_a_751_; 
v_a_751_ = lean_ctor_get(v___x_747_, 0);
lean_inc(v_a_751_);
lean_dec_ref_known(v___x_747_, 1);
v___y_700_ = v_a_745_;
v___y_701_ = v___y_740_;
v___y_702_ = v___y_732_;
v___y_703_ = v___y_735_;
v___y_704_ = v___y_741_;
v___y_705_ = v___y_736_;
v___y_706_ = v___x_746_;
v___y_707_ = v_a_751_;
v___y_708_ = v___y_737_;
v___y_709_ = v___y_743_;
v___y_710_ = v___y_738_;
v___y_711_ = v___y_742_;
v___y_712_ = v___y_739_;
v___y_713_ = v___y_733_;
goto v___jp_699_;
}
else
{
lean_object* v_a_752_; lean_object* v_inheritedTraceOptions_753_; lean_object* v___x_754_; lean_object* v___x_755_; uint8_t v___x_756_; 
v_a_752_ = lean_ctor_get(v___x_747_, 0);
lean_inc(v_a_752_);
lean_dec_ref_known(v___x_747_, 1);
v_inheritedTraceOptions_753_ = lean_ctor_get(v_toCold_748_, 11);
v___x_754_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__2));
v___x_755_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5);
v___x_756_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_753_, v_options_749_, v___x_755_);
if (v___x_756_ == 0)
{
v___y_700_ = v_a_745_;
v___y_701_ = v___y_740_;
v___y_702_ = v___y_732_;
v___y_703_ = v___y_735_;
v___y_704_ = v___y_741_;
v___y_705_ = v___y_736_;
v___y_706_ = v___x_746_;
v___y_707_ = v_a_752_;
v___y_708_ = v___y_737_;
v___y_709_ = v___y_743_;
v___y_710_ = v___y_738_;
v___y_711_ = v___y_742_;
v___y_712_ = v___y_739_;
v___y_713_ = v___y_733_;
goto v___jp_699_;
}
else
{
lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; 
v___x_757_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__11, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__11_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__11);
v___x_758_ = l_Lean_Expr_fvarId_x21(v_major_559_);
v___x_759_ = l_Lean_MessageData_ofName(v___x_758_);
v___x_760_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_760_, 0, v___x_757_);
lean_ctor_set(v___x_760_, 1, v___x_759_);
v___x_761_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1(v___x_754_, v___x_760_, v___y_738_, v___y_742_, v___y_739_, v___y_733_);
if (lean_obj_tag(v___x_761_) == 0)
{
lean_dec_ref_known(v___x_761_, 1);
v___y_700_ = v_a_745_;
v___y_701_ = v___y_740_;
v___y_702_ = v___y_732_;
v___y_703_ = v___y_735_;
v___y_704_ = v___y_741_;
v___y_705_ = v___y_736_;
v___y_706_ = v___x_746_;
v___y_707_ = v_a_752_;
v___y_708_ = v___y_737_;
v___y_709_ = v___y_743_;
v___y_710_ = v___y_738_;
v___y_711_ = v___y_742_;
v___y_712_ = v___y_739_;
v___y_713_ = v___y_733_;
goto v___jp_699_;
}
else
{
lean_object* v_a_762_; lean_object* v___x_764_; uint8_t v_isShared_765_; uint8_t v_isSharedCheck_769_; 
lean_dec(v_a_752_);
lean_dec_ref(v___x_746_);
lean_dec(v_a_745_);
lean_dec_ref(v___y_743_);
lean_dec(v___y_741_);
lean_dec(v___y_740_);
lean_dec(v___y_737_);
lean_dec(v___y_736_);
lean_dec_ref(v_subgoals_569_);
lean_dec(v_minorIdx_565_);
lean_dec(v_pos_564_);
lean_dec(v_baseSubst_561_);
lean_dec_ref(v_major_559_);
lean_dec(v_mvarId_555_);
v_a_762_ = lean_ctor_get(v___x_761_, 0);
v_isSharedCheck_769_ = !lean_is_exclusive(v___x_761_);
if (v_isSharedCheck_769_ == 0)
{
v___x_764_ = v___x_761_;
v_isShared_765_ = v_isSharedCheck_769_;
goto v_resetjp_763_;
}
else
{
lean_inc(v_a_762_);
lean_dec(v___x_761_);
v___x_764_ = lean_box(0);
v_isShared_765_ = v_isSharedCheck_769_;
goto v_resetjp_763_;
}
v_resetjp_763_:
{
lean_object* v___x_767_; 
if (v_isShared_765_ == 0)
{
v___x_767_ = v___x_764_;
goto v_reusejp_766_;
}
else
{
lean_object* v_reuseFailAlloc_768_; 
v_reuseFailAlloc_768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_768_, 0, v_a_762_);
v___x_767_ = v_reuseFailAlloc_768_;
goto v_reusejp_766_;
}
v_reusejp_766_:
{
return v___x_767_;
}
}
}
}
}
}
else
{
lean_object* v_a_770_; lean_object* v___x_772_; uint8_t v_isShared_773_; uint8_t v_isSharedCheck_777_; 
lean_dec_ref(v___x_746_);
lean_dec(v_a_745_);
lean_dec_ref(v___y_743_);
lean_dec(v___y_741_);
lean_dec(v___y_740_);
lean_dec(v___y_737_);
lean_dec(v___y_736_);
lean_dec_ref(v_subgoals_569_);
lean_dec(v_minorIdx_565_);
lean_dec(v_pos_564_);
lean_dec(v_baseSubst_561_);
lean_dec_ref(v_major_559_);
lean_dec(v_mvarId_555_);
v_a_770_ = lean_ctor_get(v___x_747_, 0);
v_isSharedCheck_777_ = !lean_is_exclusive(v___x_747_);
if (v_isSharedCheck_777_ == 0)
{
v___x_772_ = v___x_747_;
v_isShared_773_ = v_isSharedCheck_777_;
goto v_resetjp_771_;
}
else
{
lean_inc(v_a_770_);
lean_dec(v___x_747_);
v___x_772_ = lean_box(0);
v_isShared_773_ = v_isSharedCheck_777_;
goto v_resetjp_771_;
}
v_resetjp_771_:
{
lean_object* v___x_775_; 
if (v_isShared_773_ == 0)
{
v___x_775_ = v___x_772_;
goto v_reusejp_774_;
}
else
{
lean_object* v_reuseFailAlloc_776_; 
v_reuseFailAlloc_776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_776_, 0, v_a_770_);
v___x_775_ = v_reuseFailAlloc_776_;
goto v_reusejp_774_;
}
v_reusejp_774_:
{
return v___x_775_;
}
}
}
}
else
{
lean_object* v_a_778_; lean_object* v___x_780_; uint8_t v_isShared_781_; uint8_t v_isSharedCheck_785_; 
lean_dec_ref(v___y_743_);
lean_dec(v___y_741_);
lean_dec(v___y_740_);
lean_dec(v___y_737_);
lean_dec(v___y_736_);
lean_dec(v_a_633_);
lean_dec_ref(v_subgoals_569_);
lean_dec_ref(v_recursor_566_);
lean_dec(v_minorIdx_565_);
lean_dec(v_pos_564_);
lean_dec(v_baseSubst_561_);
lean_dec_ref(v_major_559_);
lean_dec(v_mvarId_555_);
v_a_778_ = lean_ctor_get(v___x_744_, 0);
v_isSharedCheck_785_ = !lean_is_exclusive(v___x_744_);
if (v_isSharedCheck_785_ == 0)
{
v___x_780_ = v___x_744_;
v_isShared_781_ = v_isSharedCheck_785_;
goto v_resetjp_779_;
}
else
{
lean_inc(v_a_778_);
lean_dec(v___x_744_);
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
v___jp_786_:
{
lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; uint8_t v___x_802_; 
v___x_796_ = lean_nat_sub(v___y_788_, v_initialArity_562_);
lean_dec(v___y_788_);
v___x_797_ = lean_array_get_size(v_reverted_558_);
v___x_798_ = lean_array_get_size(v_indices_560_);
v___x_799_ = lean_nat_sub(v___x_797_, v___x_798_);
v___x_800_ = lean_nat_sub(v___x_799_, v___y_791_);
lean_dec(v___x_799_);
v___x_801_ = lean_array_get_size(v_givenNames_556_);
v___x_802_ = lean_nat_dec_lt(v_minorIdx_565_, v___x_801_);
if (v___x_802_ == 0)
{
lean_object* v___x_803_; lean_object* v___x_804_; 
v___x_803_ = lean_box(0);
v___x_804_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_804_, 0, v___x_803_);
lean_ctor_set_uint8(v___x_804_, sizeof(void*)*1, v___x_802_);
v___y_731_ = v___y_787_;
v___y_732_ = v___y_789_;
v___y_733_ = v___y_795_;
v___y_734_ = v___y_790_;
v___y_735_ = v___y_791_;
v___y_736_ = v___x_798_;
v___y_737_ = v___x_800_;
v___y_738_ = v___y_792_;
v___y_739_ = v___y_794_;
v___y_740_ = v___x_796_;
v___y_741_ = v___x_797_;
v___y_742_ = v___y_793_;
v___y_743_ = v___x_804_;
goto v___jp_730_;
}
else
{
lean_object* v___x_805_; 
v___x_805_ = lean_array_fget_borrowed(v_givenNames_556_, v_minorIdx_565_);
lean_inc(v___x_805_);
v___y_731_ = v___y_787_;
v___y_732_ = v___y_789_;
v___y_733_ = v___y_795_;
v___y_734_ = v___y_790_;
v___y_735_ = v___y_791_;
v___y_736_ = v___x_798_;
v___y_737_ = v___x_800_;
v___y_738_ = v___y_792_;
v___y_739_ = v___y_794_;
v___y_740_ = v___x_796_;
v___y_741_ = v___x_797_;
v___y_742_ = v___y_793_;
v___y_743_ = v___x_805_;
goto v___jp_730_;
}
}
v___jp_806_:
{
lean_object* v___x_815_; uint8_t v___x_816_; 
lean_inc_ref(v___y_812_);
v___x_815_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTargetArity(v___y_812_);
v___x_816_ = lean_nat_dec_lt(v___x_815_, v_initialArity_562_);
if (v___x_816_ == 0)
{
v___y_787_ = v___y_807_;
v___y_788_ = v___x_815_;
v___y_789_ = v___y_814_;
v___y_790_ = v___y_812_;
v___y_791_ = v___y_811_;
v___y_792_ = v___y_809_;
v___y_793_ = v___y_810_;
v___y_794_ = v___y_808_;
v___y_795_ = v___y_813_;
goto v___jp_786_;
}
else
{
lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; 
v___x_817_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1));
v___x_818_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9);
lean_inc(v_mvarId_555_);
v___x_819_ = l_Lean_Meta_throwTacticEx___redArg(v___x_817_, v_mvarId_555_, v___x_818_, v___y_809_, v___y_810_, v___y_808_, v___y_813_);
if (lean_obj_tag(v___x_819_) == 0)
{
lean_dec_ref_known(v___x_819_, 1);
v___y_787_ = v___y_807_;
v___y_788_ = v___x_815_;
v___y_789_ = v___y_814_;
v___y_790_ = v___y_812_;
v___y_791_ = v___y_811_;
v___y_792_ = v___y_809_;
v___y_793_ = v___y_810_;
v___y_794_ = v___y_808_;
v___y_795_ = v___y_813_;
goto v___jp_786_;
}
else
{
lean_object* v_a_820_; lean_object* v___x_822_; uint8_t v_isShared_823_; uint8_t v_isSharedCheck_827_; 
lean_dec(v___x_815_);
lean_dec_ref(v___y_812_);
lean_dec(v___y_807_);
lean_dec(v_a_633_);
lean_dec_ref(v_subgoals_569_);
lean_dec_ref(v_recursor_566_);
lean_dec(v_minorIdx_565_);
lean_dec(v_pos_564_);
lean_dec(v_baseSubst_561_);
lean_dec_ref(v_major_559_);
lean_dec(v_mvarId_555_);
v_a_820_ = lean_ctor_get(v___x_819_, 0);
v_isSharedCheck_827_ = !lean_is_exclusive(v___x_819_);
if (v_isSharedCheck_827_ == 0)
{
v___x_822_ = v___x_819_;
v_isShared_823_ = v_isSharedCheck_827_;
goto v_resetjp_821_;
}
else
{
lean_inc(v_a_820_);
lean_dec(v___x_819_);
v___x_822_ = lean_box(0);
v_isShared_823_ = v_isSharedCheck_827_;
goto v_resetjp_821_;
}
v_resetjp_821_:
{
lean_object* v___x_825_; 
if (v_isShared_823_ == 0)
{
v___x_825_ = v___x_822_;
goto v_reusejp_824_;
}
else
{
lean_object* v_reuseFailAlloc_826_; 
v_reuseFailAlloc_826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_826_, 0, v_a_820_);
v___x_825_ = v_reuseFailAlloc_826_;
goto v_reusejp_824_;
}
v_reusejp_824_:
{
return v___x_825_;
}
}
}
}
}
v___jp_828_:
{
uint8_t v___x_837_; 
v___x_837_ = l_Lean_BinderInfo_isInstImplicit(v___y_829_);
if (v___x_837_ == 0)
{
v___y_807_ = v___y_836_;
v___y_808_ = v___y_831_;
v___y_809_ = v___y_830_;
v___y_810_ = v___y_834_;
v___y_811_ = v___y_833_;
v___y_812_ = v___y_832_;
v___y_813_ = v___y_835_;
v___y_814_ = v___x_837_;
goto v___jp_806_;
}
else
{
lean_object* v___x_838_; lean_object* v___x_839_; uint8_t v___x_840_; 
v___x_838_ = lean_array_get_size(v_givenNames_556_);
v___x_839_ = lean_unsigned_to_nat(0u);
v___x_840_ = lean_nat_dec_eq(v___x_838_, v___x_839_);
if (v___x_840_ == 0)
{
v___y_807_ = v___y_836_;
v___y_808_ = v___y_831_;
v___y_809_ = v___y_830_;
v___y_810_ = v___y_834_;
v___y_811_ = v___y_833_;
v___y_812_ = v___y_832_;
v___y_813_ = v___y_835_;
v___y_814_ = v___x_840_;
goto v___jp_806_;
}
else
{
lean_object* v___x_841_; lean_object* v___x_842_; 
v___x_841_ = lean_box(0);
lean_inc_ref(v___y_832_);
v___x_842_ = l_Lean_Meta_synthInstance_x3f(v___y_832_, v___x_841_, v___y_830_, v___y_834_, v___y_831_, v___y_835_);
if (lean_obj_tag(v___x_842_) == 0)
{
lean_object* v_a_843_; 
v_a_843_ = lean_ctor_get(v___x_842_, 0);
lean_inc(v_a_843_);
lean_dec_ref_known(v___x_842_, 1);
if (lean_obj_tag(v_a_843_) == 0)
{
lean_object* v___x_844_; 
v___x_844_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___y_832_, v___y_836_, v___y_830_, v___y_834_, v___y_831_, v___y_835_);
if (lean_obj_tag(v___x_844_) == 0)
{
lean_object* v_a_845_; lean_object* v___x_846_; lean_object* v___x_847_; 
v_a_845_ = lean_ctor_get(v___x_844_, 0);
lean_inc_n(v_a_845_, 2);
lean_dec_ref_known(v___x_844_, 1);
v___x_846_ = l_Lean_Expr_app___override(v_recursor_566_, v_a_845_);
lean_inc(v_mvarId_555_);
v___x_847_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTypeBody(v_mvarId_555_, v_a_633_, v_a_845_, v___y_830_, v___y_834_, v___y_831_, v___y_835_);
if (lean_obj_tag(v___x_847_) == 0)
{
lean_object* v_a_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; 
v_a_848_ = lean_ctor_get(v___x_847_, 0);
lean_inc(v_a_848_);
lean_dec_ref_known(v___x_847_, 1);
v___x_849_ = lean_nat_add(v_pos_564_, v___y_833_);
lean_dec(v_pos_564_);
v___x_850_ = lean_nat_add(v_minorIdx_565_, v___y_833_);
lean_dec(v_minorIdx_565_);
v___x_851_ = l_Lean_Expr_mvarId_x21(v_a_845_);
lean_dec(v_a_845_);
v___x_852_ = ((lean_object*)(l_Lean_Meta_instInhabitedInductionSubgoal_default___closed__0));
v___x_853_ = lean_box(0);
v___x_854_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_854_, 0, v___x_851_);
lean_ctor_set(v___x_854_, 1, v___x_852_);
lean_ctor_set(v___x_854_, 2, v___x_853_);
v___x_855_ = lean_array_push(v_subgoals_569_, v___x_854_);
v_pos_564_ = v___x_849_;
v_minorIdx_565_ = v___x_850_;
v_recursor_566_ = v___x_846_;
v_recursorType_567_ = v_a_848_;
v_subgoals_569_ = v___x_855_;
v_a_570_ = v___y_830_;
v_a_571_ = v___y_834_;
v_a_572_ = v___y_831_;
v_a_573_ = v___y_835_;
goto _start;
}
else
{
lean_object* v_a_857_; lean_object* v___x_859_; uint8_t v_isShared_860_; uint8_t v_isSharedCheck_864_; 
lean_dec_ref(v___x_846_);
lean_dec(v_a_845_);
lean_dec_ref(v_subgoals_569_);
lean_dec(v_minorIdx_565_);
lean_dec(v_pos_564_);
lean_dec(v_baseSubst_561_);
lean_dec_ref(v_major_559_);
lean_dec(v_mvarId_555_);
v_a_857_ = lean_ctor_get(v___x_847_, 0);
v_isSharedCheck_864_ = !lean_is_exclusive(v___x_847_);
if (v_isSharedCheck_864_ == 0)
{
v___x_859_ = v___x_847_;
v_isShared_860_ = v_isSharedCheck_864_;
goto v_resetjp_858_;
}
else
{
lean_inc(v_a_857_);
lean_dec(v___x_847_);
v___x_859_ = lean_box(0);
v_isShared_860_ = v_isSharedCheck_864_;
goto v_resetjp_858_;
}
v_resetjp_858_:
{
lean_object* v___x_862_; 
if (v_isShared_860_ == 0)
{
v___x_862_ = v___x_859_;
goto v_reusejp_861_;
}
else
{
lean_object* v_reuseFailAlloc_863_; 
v_reuseFailAlloc_863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_863_, 0, v_a_857_);
v___x_862_ = v_reuseFailAlloc_863_;
goto v_reusejp_861_;
}
v_reusejp_861_:
{
return v___x_862_;
}
}
}
}
else
{
lean_object* v_a_865_; lean_object* v___x_867_; uint8_t v_isShared_868_; uint8_t v_isSharedCheck_872_; 
lean_dec(v_a_633_);
lean_dec_ref(v_subgoals_569_);
lean_dec_ref(v_recursor_566_);
lean_dec(v_minorIdx_565_);
lean_dec(v_pos_564_);
lean_dec(v_baseSubst_561_);
lean_dec_ref(v_major_559_);
lean_dec(v_mvarId_555_);
v_a_865_ = lean_ctor_get(v___x_844_, 0);
v_isSharedCheck_872_ = !lean_is_exclusive(v___x_844_);
if (v_isSharedCheck_872_ == 0)
{
v___x_867_ = v___x_844_;
v_isShared_868_ = v_isSharedCheck_872_;
goto v_resetjp_866_;
}
else
{
lean_inc(v_a_865_);
lean_dec(v___x_844_);
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
lean_object* v_val_873_; lean_object* v___x_874_; lean_object* v___x_875_; 
lean_dec(v___y_836_);
lean_dec_ref(v___y_832_);
v_val_873_ = lean_ctor_get(v_a_843_, 0);
lean_inc_n(v_val_873_, 2);
lean_dec_ref_known(v_a_843_, 1);
v___x_874_ = l_Lean_Expr_app___override(v_recursor_566_, v_val_873_);
lean_inc(v_mvarId_555_);
v___x_875_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTypeBody(v_mvarId_555_, v_a_633_, v_val_873_, v___y_830_, v___y_834_, v___y_831_, v___y_835_);
lean_dec(v_val_873_);
if (lean_obj_tag(v___x_875_) == 0)
{
lean_object* v_a_876_; lean_object* v___x_877_; lean_object* v___x_878_; 
v_a_876_ = lean_ctor_get(v___x_875_, 0);
lean_inc(v_a_876_);
lean_dec_ref_known(v___x_875_, 1);
v___x_877_ = lean_nat_add(v_pos_564_, v___y_833_);
lean_dec(v_pos_564_);
v___x_878_ = lean_nat_add(v_minorIdx_565_, v___y_833_);
lean_dec(v_minorIdx_565_);
v_pos_564_ = v___x_877_;
v_minorIdx_565_ = v___x_878_;
v_recursor_566_ = v___x_874_;
v_recursorType_567_ = v_a_876_;
v_a_570_ = v___y_830_;
v_a_571_ = v___y_834_;
v_a_572_ = v___y_831_;
v_a_573_ = v___y_835_;
goto _start;
}
else
{
lean_object* v_a_880_; lean_object* v___x_882_; uint8_t v_isShared_883_; uint8_t v_isSharedCheck_887_; 
lean_dec_ref(v___x_874_);
lean_dec_ref(v_subgoals_569_);
lean_dec(v_minorIdx_565_);
lean_dec(v_pos_564_);
lean_dec(v_baseSubst_561_);
lean_dec_ref(v_major_559_);
lean_dec(v_mvarId_555_);
v_a_880_ = lean_ctor_get(v___x_875_, 0);
v_isSharedCheck_887_ = !lean_is_exclusive(v___x_875_);
if (v_isSharedCheck_887_ == 0)
{
v___x_882_ = v___x_875_;
v_isShared_883_ = v_isSharedCheck_887_;
goto v_resetjp_881_;
}
else
{
lean_inc(v_a_880_);
lean_dec(v___x_875_);
v___x_882_ = lean_box(0);
v_isShared_883_ = v_isSharedCheck_887_;
goto v_resetjp_881_;
}
v_resetjp_881_:
{
lean_object* v___x_885_; 
if (v_isShared_883_ == 0)
{
v___x_885_ = v___x_882_;
goto v_reusejp_884_;
}
else
{
lean_object* v_reuseFailAlloc_886_; 
v_reuseFailAlloc_886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_886_, 0, v_a_880_);
v___x_885_ = v_reuseFailAlloc_886_;
goto v_reusejp_884_;
}
v_reusejp_884_:
{
return v___x_885_;
}
}
}
}
}
else
{
lean_object* v_a_888_; lean_object* v___x_890_; uint8_t v_isShared_891_; uint8_t v_isSharedCheck_895_; 
lean_dec(v___y_836_);
lean_dec_ref(v___y_832_);
lean_dec(v_a_633_);
lean_dec_ref(v_subgoals_569_);
lean_dec_ref(v_recursor_566_);
lean_dec(v_minorIdx_565_);
lean_dec(v_pos_564_);
lean_dec(v_baseSubst_561_);
lean_dec_ref(v_major_559_);
lean_dec(v_mvarId_555_);
v_a_888_ = lean_ctor_get(v___x_842_, 0);
v_isSharedCheck_895_ = !lean_is_exclusive(v___x_842_);
if (v_isSharedCheck_895_ == 0)
{
v___x_890_ = v___x_842_;
v_isShared_891_ = v_isSharedCheck_895_;
goto v_resetjp_889_;
}
else
{
lean_inc(v_a_888_);
lean_dec(v___x_842_);
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
}
}
v___jp_634_:
{
if (v_consumedMajor_568_ == 0)
{
lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; 
v___x_635_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1));
v___x_636_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9);
lean_inc(v_mvarId_555_);
v___x_637_ = l_Lean_Meta_throwTacticEx___redArg(v___x_635_, v_mvarId_555_, v___x_636_, v_a_570_, v_a_571_, v_a_572_, v_a_573_);
if (lean_obj_tag(v___x_637_) == 0)
{
lean_dec_ref_known(v___x_637_, 1);
v___y_576_ = v_a_570_;
v___y_577_ = v_a_571_;
v___y_578_ = v_a_572_;
v___y_579_ = v_a_573_;
goto v___jp_575_;
}
else
{
lean_object* v_a_638_; lean_object* v___x_640_; uint8_t v_isShared_641_; uint8_t v_isSharedCheck_645_; 
lean_dec_ref(v_subgoals_569_);
lean_dec_ref(v_recursor_566_);
lean_dec(v_mvarId_555_);
v_a_638_ = lean_ctor_get(v___x_637_, 0);
v_isSharedCheck_645_ = !lean_is_exclusive(v___x_637_);
if (v_isSharedCheck_645_ == 0)
{
v___x_640_ = v___x_637_;
v_isShared_641_ = v_isSharedCheck_645_;
goto v_resetjp_639_;
}
else
{
lean_inc(v_a_638_);
lean_dec(v___x_637_);
v___x_640_ = lean_box(0);
v_isShared_641_ = v_isSharedCheck_645_;
goto v_resetjp_639_;
}
v_resetjp_639_:
{
lean_object* v___x_643_; 
if (v_isShared_641_ == 0)
{
v___x_643_ = v___x_640_;
goto v_reusejp_642_;
}
else
{
lean_object* v_reuseFailAlloc_644_; 
v_reuseFailAlloc_644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_644_, 0, v_a_638_);
v___x_643_ = v_reuseFailAlloc_644_;
goto v_reusejp_642_;
}
v_reusejp_642_:
{
return v___x_643_;
}
}
}
}
else
{
v___y_576_ = v_a_570_;
v___y_577_ = v_a_571_;
v___y_578_ = v_a_572_;
v___y_579_ = v_a_573_;
goto v___jp_575_;
}
}
}
else
{
lean_object* v_a_971_; lean_object* v___x_973_; uint8_t v_isShared_974_; uint8_t v_isSharedCheck_978_; 
lean_dec_ref(v_subgoals_569_);
lean_dec_ref(v_recursor_566_);
lean_dec(v_minorIdx_565_);
lean_dec(v_pos_564_);
lean_dec(v_baseSubst_561_);
lean_dec_ref(v_major_559_);
lean_dec(v_mvarId_555_);
v_a_971_ = lean_ctor_get(v___x_632_, 0);
v_isSharedCheck_978_ = !lean_is_exclusive(v___x_632_);
if (v_isSharedCheck_978_ == 0)
{
v___x_973_ = v___x_632_;
v_isShared_974_ = v_isSharedCheck_978_;
goto v_resetjp_972_;
}
else
{
lean_inc(v_a_971_);
lean_dec(v___x_632_);
v___x_973_ = lean_box(0);
v_isShared_974_ = v_isSharedCheck_978_;
goto v_resetjp_972_;
}
v_resetjp_972_:
{
lean_object* v___x_976_; 
if (v_isShared_974_ == 0)
{
v___x_976_ = v___x_973_;
goto v_reusejp_975_;
}
else
{
lean_object* v_reuseFailAlloc_977_; 
v_reuseFailAlloc_977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_977_, 0, v_a_971_);
v___x_976_ = v_reuseFailAlloc_977_;
goto v_reusejp_975_;
}
v_reusejp_975_:
{
return v___x_976_;
}
}
}
v___jp_575_:
{
lean_object* v___x_580_; 
v___x_580_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0___redArg(v_mvarId_555_, v_recursor_566_, v___y_577_);
if (lean_obj_tag(v___x_580_) == 0)
{
lean_object* v___x_582_; uint8_t v_isShared_583_; uint8_t v_isSharedCheck_622_; 
v_isSharedCheck_622_ = !lean_is_exclusive(v___x_580_);
if (v_isSharedCheck_622_ == 0)
{
lean_object* v_unused_623_; 
v_unused_623_ = lean_ctor_get(v___x_580_, 0);
lean_dec(v_unused_623_);
v___x_582_ = v___x_580_;
v_isShared_583_ = v_isSharedCheck_622_;
goto v_resetjp_581_;
}
else
{
lean_dec(v___x_580_);
v___x_582_ = lean_box(0);
v_isShared_583_ = v_isSharedCheck_622_;
goto v_resetjp_581_;
}
v_resetjp_581_:
{
lean_object* v_toCold_584_; lean_object* v_options_585_; uint8_t v_hasTrace_586_; 
v_toCold_584_ = lean_ctor_get(v___y_578_, 0);
v_options_585_ = lean_ctor_get(v_toCold_584_, 2);
v_hasTrace_586_ = lean_ctor_get_uint8(v_options_585_, sizeof(void*)*1);
if (v_hasTrace_586_ == 0)
{
lean_object* v___x_588_; 
if (v_isShared_583_ == 0)
{
lean_ctor_set(v___x_582_, 0, v_subgoals_569_);
v___x_588_ = v___x_582_;
goto v_reusejp_587_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v_subgoals_569_);
v___x_588_ = v_reuseFailAlloc_589_;
goto v_reusejp_587_;
}
v_reusejp_587_:
{
return v___x_588_;
}
}
else
{
lean_object* v_inheritedTraceOptions_590_; lean_object* v___x_591_; lean_object* v___x_592_; uint8_t v___x_593_; 
v_inheritedTraceOptions_590_ = lean_ctor_get(v_toCold_584_, 11);
v___x_591_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__2));
v___x_592_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5);
v___x_593_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_590_, v_options_585_, v___x_592_);
if (v___x_593_ == 0)
{
lean_object* v___x_595_; 
if (v_isShared_583_ == 0)
{
lean_ctor_set(v___x_582_, 0, v_subgoals_569_);
v___x_595_ = v___x_582_;
goto v_reusejp_594_;
}
else
{
lean_object* v_reuseFailAlloc_596_; 
v_reuseFailAlloc_596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_596_, 0, v_subgoals_569_);
v___x_595_ = v_reuseFailAlloc_596_;
goto v_reusejp_594_;
}
v_reusejp_594_:
{
return v___x_595_;
}
}
else
{
lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; 
lean_del_object(v___x_582_);
v___x_597_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__7, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__7_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__7);
v___x_598_ = lean_array_get_size(v_subgoals_569_);
v___x_599_ = l_Nat_reprFast(v___x_598_);
v___x_600_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_600_, 0, v___x_599_);
v___x_601_ = l_Lean_MessageData_ofFormat(v___x_600_);
v___x_602_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_602_, 0, v___x_597_);
lean_ctor_set(v___x_602_, 1, v___x_601_);
v___x_603_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__9, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__9_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__9);
v___x_604_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_604_, 0, v___x_602_);
lean_ctor_set(v___x_604_, 1, v___x_603_);
v___x_605_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1(v___x_591_, v___x_604_, v___y_576_, v___y_577_, v___y_578_, v___y_579_);
if (lean_obj_tag(v___x_605_) == 0)
{
lean_object* v___x_607_; uint8_t v_isShared_608_; uint8_t v_isSharedCheck_612_; 
v_isSharedCheck_612_ = !lean_is_exclusive(v___x_605_);
if (v_isSharedCheck_612_ == 0)
{
lean_object* v_unused_613_; 
v_unused_613_ = lean_ctor_get(v___x_605_, 0);
lean_dec(v_unused_613_);
v___x_607_ = v___x_605_;
v_isShared_608_ = v_isSharedCheck_612_;
goto v_resetjp_606_;
}
else
{
lean_dec(v___x_605_);
v___x_607_ = lean_box(0);
v_isShared_608_ = v_isSharedCheck_612_;
goto v_resetjp_606_;
}
v_resetjp_606_:
{
lean_object* v___x_610_; 
if (v_isShared_608_ == 0)
{
lean_ctor_set(v___x_607_, 0, v_subgoals_569_);
v___x_610_ = v___x_607_;
goto v_reusejp_609_;
}
else
{
lean_object* v_reuseFailAlloc_611_; 
v_reuseFailAlloc_611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_611_, 0, v_subgoals_569_);
v___x_610_ = v_reuseFailAlloc_611_;
goto v_reusejp_609_;
}
v_reusejp_609_:
{
return v___x_610_;
}
}
}
else
{
lean_object* v_a_614_; lean_object* v___x_616_; uint8_t v_isShared_617_; uint8_t v_isSharedCheck_621_; 
lean_dec_ref(v_subgoals_569_);
v_a_614_ = lean_ctor_get(v___x_605_, 0);
v_isSharedCheck_621_ = !lean_is_exclusive(v___x_605_);
if (v_isSharedCheck_621_ == 0)
{
v___x_616_ = v___x_605_;
v_isShared_617_ = v_isSharedCheck_621_;
goto v_resetjp_615_;
}
else
{
lean_inc(v_a_614_);
lean_dec(v___x_605_);
v___x_616_ = lean_box(0);
v_isShared_617_ = v_isSharedCheck_621_;
goto v_resetjp_615_;
}
v_resetjp_615_:
{
lean_object* v___x_619_; 
if (v_isShared_617_ == 0)
{
v___x_619_ = v___x_616_;
goto v_reusejp_618_;
}
else
{
lean_object* v_reuseFailAlloc_620_; 
v_reuseFailAlloc_620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_620_, 0, v_a_614_);
v___x_619_ = v_reuseFailAlloc_620_;
goto v_reusejp_618_;
}
v_reusejp_618_:
{
return v___x_619_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_624_; lean_object* v___x_626_; uint8_t v_isShared_627_; uint8_t v_isSharedCheck_631_; 
lean_dec_ref(v_subgoals_569_);
v_a_624_ = lean_ctor_get(v___x_580_, 0);
v_isSharedCheck_631_ = !lean_is_exclusive(v___x_580_);
if (v_isSharedCheck_631_ == 0)
{
v___x_626_ = v___x_580_;
v_isShared_627_ = v_isSharedCheck_631_;
goto v_resetjp_625_;
}
else
{
lean_inc(v_a_624_);
lean_dec(v___x_580_);
v___x_626_ = lean_box(0);
v_isShared_627_ = v_isSharedCheck_631_;
goto v_resetjp_625_;
}
v_resetjp_625_:
{
lean_object* v___x_629_; 
if (v_isShared_627_ == 0)
{
v___x_629_ = v___x_626_;
goto v_reusejp_628_;
}
else
{
lean_object* v_reuseFailAlloc_630_; 
v_reuseFailAlloc_630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_630_, 0, v_a_624_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___boxed(lean_object** _args){
lean_object* v_mvarId_979_ = _args[0];
lean_object* v_givenNames_980_ = _args[1];
lean_object* v_recursorInfo_981_ = _args[2];
lean_object* v_reverted_982_ = _args[3];
lean_object* v_major_983_ = _args[4];
lean_object* v_indices_984_ = _args[5];
lean_object* v_baseSubst_985_ = _args[6];
lean_object* v_initialArity_986_ = _args[7];
lean_object* v_numMinors_987_ = _args[8];
lean_object* v_pos_988_ = _args[9];
lean_object* v_minorIdx_989_ = _args[10];
lean_object* v_recursor_990_ = _args[11];
lean_object* v_recursorType_991_ = _args[12];
lean_object* v_consumedMajor_992_ = _args[13];
lean_object* v_subgoals_993_ = _args[14];
lean_object* v_a_994_ = _args[15];
lean_object* v_a_995_ = _args[16];
lean_object* v_a_996_ = _args[17];
lean_object* v_a_997_ = _args[18];
lean_object* v_a_998_ = _args[19];
_start:
{
uint8_t v_consumedMajor_boxed_999_; lean_object* v_res_1000_; 
v_consumedMajor_boxed_999_ = lean_unbox(v_consumedMajor_992_);
v_res_1000_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop(v_mvarId_979_, v_givenNames_980_, v_recursorInfo_981_, v_reverted_982_, v_major_983_, v_indices_984_, v_baseSubst_985_, v_initialArity_986_, v_numMinors_987_, v_pos_988_, v_minorIdx_989_, v_recursor_990_, v_recursorType_991_, v_consumedMajor_boxed_999_, v_subgoals_993_, v_a_994_, v_a_995_, v_a_996_, v_a_997_);
lean_dec(v_a_997_);
lean_dec_ref(v_a_996_);
lean_dec(v_a_995_);
lean_dec_ref(v_a_994_);
lean_dec(v_numMinors_987_);
lean_dec(v_initialArity_986_);
lean_dec_ref(v_indices_984_);
lean_dec_ref(v_reverted_982_);
lean_dec_ref(v_recursorInfo_981_);
lean_dec_ref(v_givenNames_980_);
return v_res_1000_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0(lean_object* v_mvarId_1001_, lean_object* v_val_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_){
_start:
{
lean_object* v___x_1008_; 
v___x_1008_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0___redArg(v_mvarId_1001_, v_val_1002_, v___y_1004_);
return v___x_1008_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0___boxed(lean_object* v_mvarId_1009_, lean_object* v_val_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_){
_start:
{
lean_object* v_res_1016_; 
v_res_1016_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0(v_mvarId_1009_, v_val_1010_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_);
lean_dec(v___y_1014_);
lean_dec_ref(v___y_1013_);
lean_dec(v___y_1012_);
lean_dec_ref(v___y_1011_);
return v_res_1016_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__2(lean_object* v___x_1017_, lean_object* v_reverted_1018_, lean_object* v_fst_1019_, lean_object* v_n_1020_, lean_object* v_j_1021_, lean_object* v_a_1022_, lean_object* v_a_1023_){
_start:
{
lean_object* v___x_1024_; 
v___x_1024_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__2___redArg(v___x_1017_, v_reverted_1018_, v_fst_1019_, v_n_1020_, v_j_1021_, v_a_1023_);
return v___x_1024_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__2___boxed(lean_object* v___x_1025_, lean_object* v_reverted_1026_, lean_object* v_fst_1027_, lean_object* v_n_1028_, lean_object* v_j_1029_, lean_object* v_a_1030_, lean_object* v_a_1031_){
_start:
{
lean_object* v_res_1032_; 
v_res_1032_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__2(v___x_1025_, v_reverted_1026_, v_fst_1027_, v_n_1028_, v_j_1029_, v_a_1030_, v_a_1031_);
lean_dec(v_n_1028_);
lean_dec_ref(v_fst_1027_);
lean_dec_ref(v_reverted_1026_);
lean_dec(v___x_1025_);
return v_res_1032_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0(lean_object* v_00_u03b2_1033_, lean_object* v_x_1034_, lean_object* v_x_1035_, lean_object* v_x_1036_){
_start:
{
lean_object* v___x_1037_; 
v___x_1037_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0___redArg(v_x_1034_, v_x_1035_, v_x_1036_);
return v___x_1037_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1038_, lean_object* v_x_1039_, size_t v_x_1040_, size_t v_x_1041_, lean_object* v_x_1042_, lean_object* v_x_1043_){
_start:
{
lean_object* v___x_1044_; 
v___x_1044_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2___redArg(v_x_1039_, v_x_1040_, v_x_1041_, v_x_1042_, v_x_1043_);
return v___x_1044_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1045_, lean_object* v_x_1046_, lean_object* v_x_1047_, lean_object* v_x_1048_, lean_object* v_x_1049_, lean_object* v_x_1050_){
_start:
{
size_t v_x_9562__boxed_1051_; size_t v_x_9563__boxed_1052_; lean_object* v_res_1053_; 
v_x_9562__boxed_1051_ = lean_unbox_usize(v_x_1047_);
lean_dec(v_x_1047_);
v_x_9563__boxed_1052_ = lean_unbox_usize(v_x_1048_);
lean_dec(v_x_1048_);
v_res_1053_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2(v_00_u03b2_1045_, v_x_1046_, v_x_9562__boxed_1051_, v_x_9563__boxed_1052_, v_x_1049_, v_x_1050_);
return v_res_1053_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__8(lean_object* v_00_u03b2_1054_, lean_object* v_n_1055_, lean_object* v_k_1056_, lean_object* v_v_1057_){
_start:
{
lean_object* v___x_1058_; 
v___x_1058_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__8___redArg(v_n_1055_, v_k_1056_, v_v_1057_);
return v___x_1058_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__9(lean_object* v_00_u03b2_1059_, size_t v_depth_1060_, lean_object* v_keys_1061_, lean_object* v_vals_1062_, lean_object* v_heq_1063_, lean_object* v_i_1064_, lean_object* v_entries_1065_){
_start:
{
lean_object* v___x_1066_; 
v___x_1066_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__9___redArg(v_depth_1060_, v_keys_1061_, v_vals_1062_, v_i_1064_, v_entries_1065_);
return v___x_1066_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__9___boxed(lean_object* v_00_u03b2_1067_, lean_object* v_depth_1068_, lean_object* v_keys_1069_, lean_object* v_vals_1070_, lean_object* v_heq_1071_, lean_object* v_i_1072_, lean_object* v_entries_1073_){
_start:
{
size_t v_depth_boxed_1074_; lean_object* v_res_1075_; 
v_depth_boxed_1074_ = lean_unbox_usize(v_depth_1068_);
lean_dec(v_depth_1068_);
v_res_1075_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__9(v_00_u03b2_1067_, v_depth_boxed_1074_, v_keys_1069_, v_vals_1070_, v_heq_1071_, v_i_1072_, v_entries_1073_);
lean_dec_ref(v_vals_1070_);
lean_dec_ref(v_keys_1069_);
return v_res_1075_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__8_spec__9(lean_object* v_00_u03b2_1076_, lean_object* v_x_1077_, lean_object* v_x_1078_, lean_object* v_x_1079_, lean_object* v_x_1080_){
_start:
{
lean_object* v___x_1081_; 
v___x_1081_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__8_spec__9___redArg(v_x_1077_, v_x_1078_, v_x_1079_, v_x_1080_);
return v___x_1081_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize(lean_object* v_mvarId_1084_, lean_object* v_givenNames_1085_, lean_object* v_recursorInfo_1086_, lean_object* v_reverted_1087_, lean_object* v_major_1088_, lean_object* v_indices_1089_, lean_object* v_baseSubst_1090_, lean_object* v_recursor_1091_, lean_object* v_a_1092_, lean_object* v_a_1093_, lean_object* v_a_1094_, lean_object* v_a_1095_){
_start:
{
lean_object* v___x_1097_; 
lean_inc(v_mvarId_1084_);
v___x_1097_ = l_Lean_MVarId_getType(v_mvarId_1084_, v_a_1092_, v_a_1093_, v_a_1094_, v_a_1095_);
if (lean_obj_tag(v___x_1097_) == 0)
{
lean_object* v_a_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; 
v_a_1098_ = lean_ctor_get(v___x_1097_, 0);
lean_inc(v_a_1098_);
lean_dec_ref_known(v___x_1097_, 1);
v___x_1099_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTargetArity(v_a_1098_);
lean_inc(v_a_1095_);
lean_inc_ref(v_a_1094_);
lean_inc(v_a_1093_);
lean_inc_ref(v_a_1092_);
lean_inc_ref(v_recursor_1091_);
v___x_1100_ = lean_infer_type(v_recursor_1091_, v_a_1092_, v_a_1093_, v_a_1094_, v_a_1095_);
if (lean_obj_tag(v___x_1100_) == 0)
{
lean_object* v_a_1101_; lean_object* v_paramsPos_1102_; lean_object* v_produceMotive_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; uint8_t v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; 
v_a_1101_ = lean_ctor_get(v___x_1100_, 0);
lean_inc(v_a_1101_);
lean_dec_ref_known(v___x_1100_, 1);
v_paramsPos_1102_ = lean_ctor_get(v_recursorInfo_1086_, 5);
v_produceMotive_1103_ = lean_ctor_get(v_recursorInfo_1086_, 7);
v___x_1104_ = l_List_lengthTR___redArg(v_produceMotive_1103_);
v___x_1105_ = l_List_lengthTR___redArg(v_paramsPos_1102_);
v___x_1106_ = lean_unsigned_to_nat(1u);
v___x_1107_ = lean_nat_add(v___x_1105_, v___x_1106_);
lean_dec(v___x_1105_);
v___x_1108_ = lean_unsigned_to_nat(0u);
v___x_1109_ = 0;
v___x_1110_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize___closed__0));
v___x_1111_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop(v_mvarId_1084_, v_givenNames_1085_, v_recursorInfo_1086_, v_reverted_1087_, v_major_1088_, v_indices_1089_, v_baseSubst_1090_, v___x_1099_, v___x_1104_, v___x_1107_, v___x_1108_, v_recursor_1091_, v_a_1101_, v___x_1109_, v___x_1110_, v_a_1092_, v_a_1093_, v_a_1094_, v_a_1095_);
lean_dec(v___x_1104_);
lean_dec(v___x_1099_);
return v___x_1111_;
}
else
{
lean_object* v_a_1112_; lean_object* v___x_1114_; uint8_t v_isShared_1115_; uint8_t v_isSharedCheck_1119_; 
lean_dec(v___x_1099_);
lean_dec_ref(v_recursor_1091_);
lean_dec(v_baseSubst_1090_);
lean_dec_ref(v_major_1088_);
lean_dec(v_mvarId_1084_);
v_a_1112_ = lean_ctor_get(v___x_1100_, 0);
v_isSharedCheck_1119_ = !lean_is_exclusive(v___x_1100_);
if (v_isSharedCheck_1119_ == 0)
{
v___x_1114_ = v___x_1100_;
v_isShared_1115_ = v_isSharedCheck_1119_;
goto v_resetjp_1113_;
}
else
{
lean_inc(v_a_1112_);
lean_dec(v___x_1100_);
v___x_1114_ = lean_box(0);
v_isShared_1115_ = v_isSharedCheck_1119_;
goto v_resetjp_1113_;
}
v_resetjp_1113_:
{
lean_object* v___x_1117_; 
if (v_isShared_1115_ == 0)
{
v___x_1117_ = v___x_1114_;
goto v_reusejp_1116_;
}
else
{
lean_object* v_reuseFailAlloc_1118_; 
v_reuseFailAlloc_1118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1118_, 0, v_a_1112_);
v___x_1117_ = v_reuseFailAlloc_1118_;
goto v_reusejp_1116_;
}
v_reusejp_1116_:
{
return v___x_1117_;
}
}
}
}
else
{
lean_object* v_a_1120_; lean_object* v___x_1122_; uint8_t v_isShared_1123_; uint8_t v_isSharedCheck_1127_; 
lean_dec_ref(v_recursor_1091_);
lean_dec(v_baseSubst_1090_);
lean_dec_ref(v_major_1088_);
lean_dec(v_mvarId_1084_);
v_a_1120_ = lean_ctor_get(v___x_1097_, 0);
v_isSharedCheck_1127_ = !lean_is_exclusive(v___x_1097_);
if (v_isSharedCheck_1127_ == 0)
{
v___x_1122_ = v___x_1097_;
v_isShared_1123_ = v_isSharedCheck_1127_;
goto v_resetjp_1121_;
}
else
{
lean_inc(v_a_1120_);
lean_dec(v___x_1097_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize___boxed(lean_object* v_mvarId_1128_, lean_object* v_givenNames_1129_, lean_object* v_recursorInfo_1130_, lean_object* v_reverted_1131_, lean_object* v_major_1132_, lean_object* v_indices_1133_, lean_object* v_baseSubst_1134_, lean_object* v_recursor_1135_, lean_object* v_a_1136_, lean_object* v_a_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_){
_start:
{
lean_object* v_res_1141_; 
v_res_1141_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize(v_mvarId_1128_, v_givenNames_1129_, v_recursorInfo_1130_, v_reverted_1131_, v_major_1132_, v_indices_1133_, v_baseSubst_1134_, v_recursor_1135_, v_a_1136_, v_a_1137_, v_a_1138_, v_a_1139_);
lean_dec(v_a_1139_);
lean_dec_ref(v_a_1138_);
lean_dec(v_a_1137_);
lean_dec_ref(v_a_1136_);
lean_dec_ref(v_indices_1133_);
lean_dec_ref(v_reverted_1131_);
lean_dec_ref(v_recursorInfo_1130_);
lean_dec_ref(v_givenNames_1129_);
return v_res_1141_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg___closed__1(void){
_start:
{
lean_object* v___x_1143_; lean_object* v___x_1144_; 
v___x_1143_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg___closed__0));
v___x_1144_ = l_Lean_stringToMessageData(v___x_1143_);
return v___x_1144_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg(lean_object* v_tacticName_1145_, lean_object* v_mvarId_1146_, lean_object* v_majorType_1147_, lean_object* v_a_1148_, lean_object* v_a_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_){
_start:
{
lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; 
v___x_1153_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg___closed__1, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg___closed__1);
v___x_1154_ = l_Lean_indentExpr(v_majorType_1147_);
v___x_1155_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1155_, 0, v___x_1153_);
lean_ctor_set(v___x_1155_, 1, v___x_1154_);
v___x_1156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1156_, 0, v___x_1155_);
v___x_1157_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1145_, v_mvarId_1146_, v___x_1156_, v_a_1148_, v_a_1149_, v_a_1150_, v_a_1151_);
return v___x_1157_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg___boxed(lean_object* v_tacticName_1158_, lean_object* v_mvarId_1159_, lean_object* v_majorType_1160_, lean_object* v_a_1161_, lean_object* v_a_1162_, lean_object* v_a_1163_, lean_object* v_a_1164_, lean_object* v_a_1165_){
_start:
{
lean_object* v_res_1166_; 
v_res_1166_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg(v_tacticName_1158_, v_mvarId_1159_, v_majorType_1160_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_);
lean_dec(v_a_1164_);
lean_dec_ref(v_a_1163_);
lean_dec(v_a_1162_);
lean_dec_ref(v_a_1161_);
return v_res_1166_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType(lean_object* v_00_u03b1_1167_, lean_object* v_tacticName_1168_, lean_object* v_mvarId_1169_, lean_object* v_majorType_1170_, lean_object* v_a_1171_, lean_object* v_a_1172_, lean_object* v_a_1173_, lean_object* v_a_1174_){
_start:
{
lean_object* v___x_1176_; 
v___x_1176_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg(v_tacticName_1168_, v_mvarId_1169_, v_majorType_1170_, v_a_1171_, v_a_1172_, v_a_1173_, v_a_1174_);
return v___x_1176_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___boxed(lean_object* v_00_u03b1_1177_, lean_object* v_tacticName_1178_, lean_object* v_mvarId_1179_, lean_object* v_majorType_1180_, lean_object* v_a_1181_, lean_object* v_a_1182_, lean_object* v_a_1183_, lean_object* v_a_1184_, lean_object* v_a_1185_){
_start:
{
lean_object* v_res_1186_; 
v_res_1186_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType(v_00_u03b1_1177_, v_tacticName_1178_, v_mvarId_1179_, v_majorType_1180_, v_a_1181_, v_a_1182_, v_a_1183_, v_a_1184_);
lean_dec(v_a_1184_);
lean_dec_ref(v_a_1183_);
lean_dec(v_a_1182_);
lean_dec_ref(v_a_1181_);
return v_res_1186_;
}
}
LEAN_EXPORT uint8_t l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___lam__0(lean_object* v_fvarId_1187_, lean_object* v_x_1188_){
_start:
{
uint8_t v___x_1189_; 
v___x_1189_ = l_Lean_instBEqFVarId_beq(v_fvarId_1187_, v_x_1188_);
return v___x_1189_;
}
}
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___lam__0___boxed(lean_object* v_fvarId_1190_, lean_object* v_x_1191_){
_start:
{
uint8_t v_res_1192_; lean_object* v_r_1193_; 
v_res_1192_ = l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___lam__0(v_fvarId_1190_, v_x_1191_);
lean_dec(v_x_1191_);
lean_dec(v_fvarId_1190_);
v_r_1193_ = lean_box(v_res_1192_);
return v_r_1193_;
}
}
LEAN_EXPORT uint8_t l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___lam__1(lean_object* v_x_1194_){
_start:
{
uint8_t v___x_1195_; 
v___x_1195_ = 0;
return v___x_1195_;
}
}
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___lam__1___boxed(lean_object* v_x_1196_){
_start:
{
uint8_t v_res_1197_; lean_object* v_r_1198_; 
v_res_1197_ = l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___lam__1(v_x_1196_);
lean_dec(v_x_1196_);
v_r_1198_ = lean_box(v_res_1197_);
return v_r_1198_;
}
}
static lean_object* _init_l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; 
v___x_1200_ = lean_box(0);
v___x_1201_ = lean_unsigned_to_nat(16u);
v___x_1202_ = lean_mk_array(v___x_1201_, v___x_1200_);
return v___x_1202_;
}
}
static lean_object* _init_l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; 
v___x_1203_ = lean_obj_once(&l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__1, &l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__1_once, _init_l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__1);
v___x_1204_ = lean_unsigned_to_nat(0u);
v___x_1205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1205_, 0, v___x_1204_);
lean_ctor_set(v___x_1205_, 1, v___x_1203_);
return v___x_1205_;
}
}
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg(lean_object* v_localDecl_1206_, lean_object* v_fvarId_1207_, uint8_t v_generalizeNondepLet_1208_, lean_object* v___y_1209_){
_start:
{
uint8_t v_fst_1212_; lean_object* v_snd_1213_; lean_object* v___y_1232_; lean_object* v___f_1236_; lean_object* v___f_1237_; 
v___f_1236_ = lean_alloc_closure((void*)(l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1236_, 0, v_fvarId_1207_);
v___f_1237_ = ((lean_object*)(l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__0));
if (lean_obj_tag(v_localDecl_1206_) == 0)
{
lean_object* v_type_1238_; lean_object* v___x_1239_; uint8_t v_fst_1241_; lean_object* v_mctx_1242_; lean_object* v___y_1260_; lean_object* v_mctx_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; uint8_t v___x_1268_; 
v_type_1238_ = lean_ctor_get(v_localDecl_1206_, 3);
lean_inc_ref(v_type_1238_);
lean_dec_ref_known(v_localDecl_1206_, 4);
v___x_1239_ = lean_st_ref_get(v___y_1209_);
v_mctx_1265_ = lean_ctor_get(v___x_1239_, 0);
lean_inc_ref_n(v_mctx_1265_, 2);
lean_dec(v___x_1239_);
v___x_1266_ = lean_obj_once(&l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__2, &l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__2_once, _init_l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__2);
v___x_1267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1267_, 0, v___x_1266_);
lean_ctor_set(v___x_1267_, 1, v_mctx_1265_);
v___x_1268_ = l_Lean_Expr_hasFVar(v_type_1238_);
if (v___x_1268_ == 0)
{
uint8_t v___x_1269_; 
v___x_1269_ = l_Lean_Expr_hasMVar(v_type_1238_);
if (v___x_1269_ == 0)
{
lean_dec_ref_known(v___x_1267_, 2);
lean_dec_ref(v_type_1238_);
lean_dec_ref(v___f_1236_);
v_fst_1241_ = v___x_1269_;
v_mctx_1242_ = v_mctx_1265_;
goto v___jp_1240_;
}
else
{
lean_object* v___x_1270_; 
lean_dec_ref(v_mctx_1265_);
v___x_1270_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1236_, v___f_1237_, v_type_1238_, v___x_1267_);
v___y_1260_ = v___x_1270_;
goto v___jp_1259_;
}
}
else
{
lean_object* v___x_1271_; 
lean_dec_ref(v_mctx_1265_);
v___x_1271_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1236_, v___f_1237_, v_type_1238_, v___x_1267_);
v___y_1260_ = v___x_1271_;
goto v___jp_1259_;
}
v___jp_1240_:
{
lean_object* v___x_1243_; lean_object* v_cache_1244_; lean_object* v_zetaDeltaFVarIds_1245_; lean_object* v_postponed_1246_; lean_object* v_diag_1247_; lean_object* v___x_1249_; uint8_t v_isShared_1250_; uint8_t v_isSharedCheck_1257_; 
v___x_1243_ = lean_st_ref_take(v___y_1209_);
v_cache_1244_ = lean_ctor_get(v___x_1243_, 1);
v_zetaDeltaFVarIds_1245_ = lean_ctor_get(v___x_1243_, 2);
v_postponed_1246_ = lean_ctor_get(v___x_1243_, 3);
v_diag_1247_ = lean_ctor_get(v___x_1243_, 4);
v_isSharedCheck_1257_ = !lean_is_exclusive(v___x_1243_);
if (v_isSharedCheck_1257_ == 0)
{
lean_object* v_unused_1258_; 
v_unused_1258_ = lean_ctor_get(v___x_1243_, 0);
lean_dec(v_unused_1258_);
v___x_1249_ = v___x_1243_;
v_isShared_1250_ = v_isSharedCheck_1257_;
goto v_resetjp_1248_;
}
else
{
lean_inc(v_diag_1247_);
lean_inc(v_postponed_1246_);
lean_inc(v_zetaDeltaFVarIds_1245_);
lean_inc(v_cache_1244_);
lean_dec(v___x_1243_);
v___x_1249_ = lean_box(0);
v_isShared_1250_ = v_isSharedCheck_1257_;
goto v_resetjp_1248_;
}
v_resetjp_1248_:
{
lean_object* v___x_1252_; 
if (v_isShared_1250_ == 0)
{
lean_ctor_set(v___x_1249_, 0, v_mctx_1242_);
v___x_1252_ = v___x_1249_;
goto v_reusejp_1251_;
}
else
{
lean_object* v_reuseFailAlloc_1256_; 
v_reuseFailAlloc_1256_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1256_, 0, v_mctx_1242_);
lean_ctor_set(v_reuseFailAlloc_1256_, 1, v_cache_1244_);
lean_ctor_set(v_reuseFailAlloc_1256_, 2, v_zetaDeltaFVarIds_1245_);
lean_ctor_set(v_reuseFailAlloc_1256_, 3, v_postponed_1246_);
lean_ctor_set(v_reuseFailAlloc_1256_, 4, v_diag_1247_);
v___x_1252_ = v_reuseFailAlloc_1256_;
goto v_reusejp_1251_;
}
v_reusejp_1251_:
{
lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; 
v___x_1253_ = lean_st_ref_put(v___y_1209_, v___x_1252_);
v___x_1254_ = lean_box(v_fst_1241_);
v___x_1255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1255_, 0, v___x_1254_);
return v___x_1255_;
}
}
}
v___jp_1259_:
{
lean_object* v_snd_1261_; lean_object* v_fst_1262_; lean_object* v_mctx_1263_; uint8_t v___x_1264_; 
v_snd_1261_ = lean_ctor_get(v___y_1260_, 1);
lean_inc(v_snd_1261_);
v_fst_1262_ = lean_ctor_get(v___y_1260_, 0);
lean_inc(v_fst_1262_);
lean_dec_ref(v___y_1260_);
v_mctx_1263_ = lean_ctor_get(v_snd_1261_, 1);
lean_inc_ref(v_mctx_1263_);
lean_dec(v_snd_1261_);
v___x_1264_ = lean_unbox(v_fst_1262_);
lean_dec(v_fst_1262_);
v_fst_1241_ = v___x_1264_;
v_mctx_1242_ = v_mctx_1263_;
goto v___jp_1240_;
}
}
else
{
lean_object* v_type_1272_; lean_object* v_value_1273_; uint8_t v_nondep_1274_; lean_object* v_snd_1276_; lean_object* v___y_1282_; 
v_type_1272_ = lean_ctor_get(v_localDecl_1206_, 3);
lean_inc_ref(v_type_1272_);
v_value_1273_ = lean_ctor_get(v_localDecl_1206_, 4);
lean_inc_ref(v_value_1273_);
v_nondep_1274_ = lean_ctor_get_uint8(v_localDecl_1206_, sizeof(void*)*5);
lean_dec_ref_known(v_localDecl_1206_, 5);
if (v_generalizeNondepLet_1208_ == 0)
{
goto v___jp_1288_;
}
else
{
if (v_nondep_1274_ == 0)
{
goto v___jp_1288_;
}
else
{
lean_object* v___x_1297_; uint8_t v_fst_1299_; lean_object* v_mctx_1300_; lean_object* v___y_1318_; lean_object* v_mctx_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; uint8_t v___x_1326_; 
lean_dec_ref(v_value_1273_);
v___x_1297_ = lean_st_ref_get(v___y_1209_);
v_mctx_1323_ = lean_ctor_get(v___x_1297_, 0);
lean_inc_ref_n(v_mctx_1323_, 2);
lean_dec(v___x_1297_);
v___x_1324_ = lean_obj_once(&l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__2, &l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__2_once, _init_l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__2);
v___x_1325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1325_, 0, v___x_1324_);
lean_ctor_set(v___x_1325_, 1, v_mctx_1323_);
v___x_1326_ = l_Lean_Expr_hasFVar(v_type_1272_);
if (v___x_1326_ == 0)
{
uint8_t v___x_1327_; 
v___x_1327_ = l_Lean_Expr_hasMVar(v_type_1272_);
if (v___x_1327_ == 0)
{
lean_dec_ref_known(v___x_1325_, 2);
lean_dec_ref(v_type_1272_);
lean_dec_ref(v___f_1236_);
v_fst_1299_ = v___x_1327_;
v_mctx_1300_ = v_mctx_1323_;
goto v___jp_1298_;
}
else
{
lean_object* v___x_1328_; 
lean_dec_ref(v_mctx_1323_);
v___x_1328_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1236_, v___f_1237_, v_type_1272_, v___x_1325_);
v___y_1318_ = v___x_1328_;
goto v___jp_1317_;
}
}
else
{
lean_object* v___x_1329_; 
lean_dec_ref(v_mctx_1323_);
v___x_1329_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1236_, v___f_1237_, v_type_1272_, v___x_1325_);
v___y_1318_ = v___x_1329_;
goto v___jp_1317_;
}
v___jp_1298_:
{
lean_object* v___x_1301_; lean_object* v_cache_1302_; lean_object* v_zetaDeltaFVarIds_1303_; lean_object* v_postponed_1304_; lean_object* v_diag_1305_; lean_object* v___x_1307_; uint8_t v_isShared_1308_; uint8_t v_isSharedCheck_1315_; 
v___x_1301_ = lean_st_ref_take(v___y_1209_);
v_cache_1302_ = lean_ctor_get(v___x_1301_, 1);
v_zetaDeltaFVarIds_1303_ = lean_ctor_get(v___x_1301_, 2);
v_postponed_1304_ = lean_ctor_get(v___x_1301_, 3);
v_diag_1305_ = lean_ctor_get(v___x_1301_, 4);
v_isSharedCheck_1315_ = !lean_is_exclusive(v___x_1301_);
if (v_isSharedCheck_1315_ == 0)
{
lean_object* v_unused_1316_; 
v_unused_1316_ = lean_ctor_get(v___x_1301_, 0);
lean_dec(v_unused_1316_);
v___x_1307_ = v___x_1301_;
v_isShared_1308_ = v_isSharedCheck_1315_;
goto v_resetjp_1306_;
}
else
{
lean_inc(v_diag_1305_);
lean_inc(v_postponed_1304_);
lean_inc(v_zetaDeltaFVarIds_1303_);
lean_inc(v_cache_1302_);
lean_dec(v___x_1301_);
v___x_1307_ = lean_box(0);
v_isShared_1308_ = v_isSharedCheck_1315_;
goto v_resetjp_1306_;
}
v_resetjp_1306_:
{
lean_object* v___x_1310_; 
if (v_isShared_1308_ == 0)
{
lean_ctor_set(v___x_1307_, 0, v_mctx_1300_);
v___x_1310_ = v___x_1307_;
goto v_reusejp_1309_;
}
else
{
lean_object* v_reuseFailAlloc_1314_; 
v_reuseFailAlloc_1314_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1314_, 0, v_mctx_1300_);
lean_ctor_set(v_reuseFailAlloc_1314_, 1, v_cache_1302_);
lean_ctor_set(v_reuseFailAlloc_1314_, 2, v_zetaDeltaFVarIds_1303_);
lean_ctor_set(v_reuseFailAlloc_1314_, 3, v_postponed_1304_);
lean_ctor_set(v_reuseFailAlloc_1314_, 4, v_diag_1305_);
v___x_1310_ = v_reuseFailAlloc_1314_;
goto v_reusejp_1309_;
}
v_reusejp_1309_:
{
lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; 
v___x_1311_ = lean_st_ref_put(v___y_1209_, v___x_1310_);
v___x_1312_ = lean_box(v_fst_1299_);
v___x_1313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1313_, 0, v___x_1312_);
return v___x_1313_;
}
}
}
v___jp_1317_:
{
lean_object* v_snd_1319_; lean_object* v_fst_1320_; lean_object* v_mctx_1321_; uint8_t v___x_1322_; 
v_snd_1319_ = lean_ctor_get(v___y_1318_, 1);
lean_inc(v_snd_1319_);
v_fst_1320_ = lean_ctor_get(v___y_1318_, 0);
lean_inc(v_fst_1320_);
lean_dec_ref(v___y_1318_);
v_mctx_1321_ = lean_ctor_get(v_snd_1319_, 1);
lean_inc_ref(v_mctx_1321_);
lean_dec(v_snd_1319_);
v___x_1322_ = lean_unbox(v_fst_1320_);
lean_dec(v_fst_1320_);
v_fst_1299_ = v___x_1322_;
v_mctx_1300_ = v_mctx_1321_;
goto v___jp_1298_;
}
}
}
v___jp_1275_:
{
uint8_t v___x_1277_; 
v___x_1277_ = l_Lean_Expr_hasFVar(v_value_1273_);
if (v___x_1277_ == 0)
{
uint8_t v___x_1278_; 
v___x_1278_ = l_Lean_Expr_hasMVar(v_value_1273_);
if (v___x_1278_ == 0)
{
lean_dec_ref(v_value_1273_);
lean_dec_ref(v___f_1236_);
v_fst_1212_ = v___x_1278_;
v_snd_1213_ = v_snd_1276_;
goto v___jp_1211_;
}
else
{
lean_object* v___x_1279_; 
v___x_1279_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1236_, v___f_1237_, v_value_1273_, v_snd_1276_);
v___y_1232_ = v___x_1279_;
goto v___jp_1231_;
}
}
else
{
lean_object* v___x_1280_; 
v___x_1280_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1236_, v___f_1237_, v_value_1273_, v_snd_1276_);
v___y_1232_ = v___x_1280_;
goto v___jp_1231_;
}
}
v___jp_1281_:
{
lean_object* v_fst_1283_; uint8_t v___x_1284_; 
v_fst_1283_ = lean_ctor_get(v___y_1282_, 0);
v___x_1284_ = lean_unbox(v_fst_1283_);
if (v___x_1284_ == 0)
{
lean_object* v_snd_1285_; 
v_snd_1285_ = lean_ctor_get(v___y_1282_, 1);
lean_inc(v_snd_1285_);
lean_dec_ref(v___y_1282_);
v_snd_1276_ = v_snd_1285_;
goto v___jp_1275_;
}
else
{
lean_object* v_snd_1286_; uint8_t v___x_1287_; 
lean_inc(v_fst_1283_);
lean_dec_ref(v_value_1273_);
lean_dec_ref(v___f_1236_);
v_snd_1286_ = lean_ctor_get(v___y_1282_, 1);
lean_inc(v_snd_1286_);
lean_dec_ref(v___y_1282_);
v___x_1287_ = lean_unbox(v_fst_1283_);
lean_dec(v_fst_1283_);
v_fst_1212_ = v___x_1287_;
v_snd_1213_ = v_snd_1286_;
goto v___jp_1211_;
}
}
v___jp_1288_:
{
lean_object* v___x_1289_; lean_object* v_mctx_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; uint8_t v___x_1293_; 
v___x_1289_ = lean_st_ref_get(v___y_1209_);
v_mctx_1290_ = lean_ctor_get(v___x_1289_, 0);
lean_inc_ref(v_mctx_1290_);
lean_dec(v___x_1289_);
v___x_1291_ = lean_obj_once(&l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__2, &l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__2_once, _init_l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__2);
v___x_1292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1292_, 0, v___x_1291_);
lean_ctor_set(v___x_1292_, 1, v_mctx_1290_);
v___x_1293_ = l_Lean_Expr_hasFVar(v_type_1272_);
if (v___x_1293_ == 0)
{
uint8_t v___x_1294_; 
v___x_1294_ = l_Lean_Expr_hasMVar(v_type_1272_);
if (v___x_1294_ == 0)
{
lean_dec_ref(v_type_1272_);
v_snd_1276_ = v___x_1292_;
goto v___jp_1275_;
}
else
{
lean_object* v___x_1295_; 
lean_inc_ref(v___f_1236_);
v___x_1295_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1236_, v___f_1237_, v_type_1272_, v___x_1292_);
v___y_1282_ = v___x_1295_;
goto v___jp_1281_;
}
}
else
{
lean_object* v___x_1296_; 
lean_inc_ref(v___f_1236_);
v___x_1296_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1236_, v___f_1237_, v_type_1272_, v___x_1292_);
v___y_1282_ = v___x_1296_;
goto v___jp_1281_;
}
}
}
v___jp_1211_:
{
lean_object* v_mctx_1214_; lean_object* v___x_1215_; lean_object* v_cache_1216_; lean_object* v_zetaDeltaFVarIds_1217_; lean_object* v_postponed_1218_; lean_object* v_diag_1219_; lean_object* v___x_1221_; uint8_t v_isShared_1222_; uint8_t v_isSharedCheck_1229_; 
v_mctx_1214_ = lean_ctor_get(v_snd_1213_, 1);
lean_inc_ref(v_mctx_1214_);
lean_dec_ref(v_snd_1213_);
v___x_1215_ = lean_st_ref_take(v___y_1209_);
v_cache_1216_ = lean_ctor_get(v___x_1215_, 1);
v_zetaDeltaFVarIds_1217_ = lean_ctor_get(v___x_1215_, 2);
v_postponed_1218_ = lean_ctor_get(v___x_1215_, 3);
v_diag_1219_ = lean_ctor_get(v___x_1215_, 4);
v_isSharedCheck_1229_ = !lean_is_exclusive(v___x_1215_);
if (v_isSharedCheck_1229_ == 0)
{
lean_object* v_unused_1230_; 
v_unused_1230_ = lean_ctor_get(v___x_1215_, 0);
lean_dec(v_unused_1230_);
v___x_1221_ = v___x_1215_;
v_isShared_1222_ = v_isSharedCheck_1229_;
goto v_resetjp_1220_;
}
else
{
lean_inc(v_diag_1219_);
lean_inc(v_postponed_1218_);
lean_inc(v_zetaDeltaFVarIds_1217_);
lean_inc(v_cache_1216_);
lean_dec(v___x_1215_);
v___x_1221_ = lean_box(0);
v_isShared_1222_ = v_isSharedCheck_1229_;
goto v_resetjp_1220_;
}
v_resetjp_1220_:
{
lean_object* v___x_1224_; 
if (v_isShared_1222_ == 0)
{
lean_ctor_set(v___x_1221_, 0, v_mctx_1214_);
v___x_1224_ = v___x_1221_;
goto v_reusejp_1223_;
}
else
{
lean_object* v_reuseFailAlloc_1228_; 
v_reuseFailAlloc_1228_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1228_, 0, v_mctx_1214_);
lean_ctor_set(v_reuseFailAlloc_1228_, 1, v_cache_1216_);
lean_ctor_set(v_reuseFailAlloc_1228_, 2, v_zetaDeltaFVarIds_1217_);
lean_ctor_set(v_reuseFailAlloc_1228_, 3, v_postponed_1218_);
lean_ctor_set(v_reuseFailAlloc_1228_, 4, v_diag_1219_);
v___x_1224_ = v_reuseFailAlloc_1228_;
goto v_reusejp_1223_;
}
v_reusejp_1223_:
{
lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; 
v___x_1225_ = lean_st_ref_put(v___y_1209_, v___x_1224_);
v___x_1226_ = lean_box(v_fst_1212_);
v___x_1227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1227_, 0, v___x_1226_);
return v___x_1227_;
}
}
}
v___jp_1231_:
{
lean_object* v_fst_1233_; lean_object* v_snd_1234_; uint8_t v___x_1235_; 
v_fst_1233_ = lean_ctor_get(v___y_1232_, 0);
lean_inc(v_fst_1233_);
v_snd_1234_ = lean_ctor_get(v___y_1232_, 1);
lean_inc(v_snd_1234_);
lean_dec_ref(v___y_1232_);
v___x_1235_ = lean_unbox(v_fst_1233_);
lean_dec(v_fst_1233_);
v_fst_1212_ = v___x_1235_;
v_snd_1213_ = v_snd_1234_;
goto v___jp_1211_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___boxed(lean_object* v_localDecl_1330_, lean_object* v_fvarId_1331_, lean_object* v_generalizeNondepLet_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_){
_start:
{
uint8_t v_generalizeNondepLet_boxed_1335_; lean_object* v_res_1336_; 
v_generalizeNondepLet_boxed_1335_ = lean_unbox(v_generalizeNondepLet_1332_);
v_res_1336_ = l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg(v_localDecl_1330_, v_fvarId_1331_, v_generalizeNondepLet_boxed_1335_, v___y_1333_);
lean_dec(v___y_1333_);
return v_res_1336_;
}
}
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1(lean_object* v_localDecl_1337_, lean_object* v_fvarId_1338_, uint8_t v_generalizeNondepLet_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_){
_start:
{
lean_object* v___x_1345_; 
v___x_1345_ = l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg(v_localDecl_1337_, v_fvarId_1338_, v_generalizeNondepLet_1339_, v___y_1341_);
return v___x_1345_;
}
}
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___boxed(lean_object* v_localDecl_1346_, lean_object* v_fvarId_1347_, lean_object* v_generalizeNondepLet_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_){
_start:
{
uint8_t v_generalizeNondepLet_boxed_1354_; lean_object* v_res_1355_; 
v_generalizeNondepLet_boxed_1354_ = lean_unbox(v_generalizeNondepLet_1348_);
v_res_1355_ = l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1(v_localDecl_1346_, v_fvarId_1347_, v_generalizeNondepLet_boxed_1354_, v___y_1349_, v___y_1350_, v___y_1351_, v___y_1352_);
lean_dec(v___y_1352_);
lean_dec_ref(v___y_1351_);
lean_dec(v___y_1350_);
lean_dec_ref(v___y_1349_);
return v_res_1355_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2___redArg(lean_object* v_e_1356_, lean_object* v_fvarId_1357_, lean_object* v___y_1358_){
_start:
{
lean_object* v___f_1360_; lean_object* v___f_1361_; lean_object* v___x_1362_; uint8_t v_fst_1364_; lean_object* v_mctx_1365_; lean_object* v___y_1383_; lean_object* v_mctx_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; uint8_t v___x_1391_; 
v___f_1360_ = ((lean_object*)(l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__0));
v___f_1361_ = lean_alloc_closure((void*)(l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1361_, 0, v_fvarId_1357_);
v___x_1362_ = lean_st_ref_get(v___y_1358_);
v_mctx_1388_ = lean_ctor_get(v___x_1362_, 0);
lean_inc_ref_n(v_mctx_1388_, 2);
lean_dec(v___x_1362_);
v___x_1389_ = lean_obj_once(&l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__2, &l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__2_once, _init_l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__2);
v___x_1390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1390_, 0, v___x_1389_);
lean_ctor_set(v___x_1390_, 1, v_mctx_1388_);
v___x_1391_ = l_Lean_Expr_hasFVar(v_e_1356_);
if (v___x_1391_ == 0)
{
uint8_t v___x_1392_; 
v___x_1392_ = l_Lean_Expr_hasMVar(v_e_1356_);
if (v___x_1392_ == 0)
{
lean_dec_ref_known(v___x_1390_, 2);
lean_dec_ref(v___f_1361_);
lean_dec_ref(v_e_1356_);
v_fst_1364_ = v___x_1392_;
v_mctx_1365_ = v_mctx_1388_;
goto v___jp_1363_;
}
else
{
lean_object* v___x_1393_; 
lean_dec_ref(v_mctx_1388_);
v___x_1393_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1361_, v___f_1360_, v_e_1356_, v___x_1390_);
v___y_1383_ = v___x_1393_;
goto v___jp_1382_;
}
}
else
{
lean_object* v___x_1394_; 
lean_dec_ref(v_mctx_1388_);
v___x_1394_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1361_, v___f_1360_, v_e_1356_, v___x_1390_);
v___y_1383_ = v___x_1394_;
goto v___jp_1382_;
}
v___jp_1363_:
{
lean_object* v___x_1366_; lean_object* v_cache_1367_; lean_object* v_zetaDeltaFVarIds_1368_; lean_object* v_postponed_1369_; lean_object* v_diag_1370_; lean_object* v___x_1372_; uint8_t v_isShared_1373_; uint8_t v_isSharedCheck_1380_; 
v___x_1366_ = lean_st_ref_take(v___y_1358_);
v_cache_1367_ = lean_ctor_get(v___x_1366_, 1);
v_zetaDeltaFVarIds_1368_ = lean_ctor_get(v___x_1366_, 2);
v_postponed_1369_ = lean_ctor_get(v___x_1366_, 3);
v_diag_1370_ = lean_ctor_get(v___x_1366_, 4);
v_isSharedCheck_1380_ = !lean_is_exclusive(v___x_1366_);
if (v_isSharedCheck_1380_ == 0)
{
lean_object* v_unused_1381_; 
v_unused_1381_ = lean_ctor_get(v___x_1366_, 0);
lean_dec(v_unused_1381_);
v___x_1372_ = v___x_1366_;
v_isShared_1373_ = v_isSharedCheck_1380_;
goto v_resetjp_1371_;
}
else
{
lean_inc(v_diag_1370_);
lean_inc(v_postponed_1369_);
lean_inc(v_zetaDeltaFVarIds_1368_);
lean_inc(v_cache_1367_);
lean_dec(v___x_1366_);
v___x_1372_ = lean_box(0);
v_isShared_1373_ = v_isSharedCheck_1380_;
goto v_resetjp_1371_;
}
v_resetjp_1371_:
{
lean_object* v___x_1375_; 
if (v_isShared_1373_ == 0)
{
lean_ctor_set(v___x_1372_, 0, v_mctx_1365_);
v___x_1375_ = v___x_1372_;
goto v_reusejp_1374_;
}
else
{
lean_object* v_reuseFailAlloc_1379_; 
v_reuseFailAlloc_1379_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1379_, 0, v_mctx_1365_);
lean_ctor_set(v_reuseFailAlloc_1379_, 1, v_cache_1367_);
lean_ctor_set(v_reuseFailAlloc_1379_, 2, v_zetaDeltaFVarIds_1368_);
lean_ctor_set(v_reuseFailAlloc_1379_, 3, v_postponed_1369_);
lean_ctor_set(v_reuseFailAlloc_1379_, 4, v_diag_1370_);
v___x_1375_ = v_reuseFailAlloc_1379_;
goto v_reusejp_1374_;
}
v_reusejp_1374_:
{
lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; 
v___x_1376_ = lean_st_ref_put(v___y_1358_, v___x_1375_);
v___x_1377_ = lean_box(v_fst_1364_);
v___x_1378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1378_, 0, v___x_1377_);
return v___x_1378_;
}
}
}
v___jp_1382_:
{
lean_object* v_snd_1384_; lean_object* v_fst_1385_; lean_object* v_mctx_1386_; uint8_t v___x_1387_; 
v_snd_1384_ = lean_ctor_get(v___y_1383_, 1);
lean_inc(v_snd_1384_);
v_fst_1385_ = lean_ctor_get(v___y_1383_, 0);
lean_inc(v_fst_1385_);
lean_dec_ref(v___y_1383_);
v_mctx_1386_ = lean_ctor_get(v_snd_1384_, 1);
lean_inc_ref(v_mctx_1386_);
lean_dec(v_snd_1384_);
v___x_1387_ = lean_unbox(v_fst_1385_);
lean_dec(v_fst_1385_);
v_fst_1364_ = v___x_1387_;
v_mctx_1365_ = v_mctx_1386_;
goto v___jp_1363_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2___redArg___boxed(lean_object* v_e_1395_, lean_object* v_fvarId_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_){
_start:
{
lean_object* v_res_1399_; 
v_res_1399_ = l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2___redArg(v_e_1395_, v_fvarId_1396_, v___y_1397_);
lean_dec(v___y_1397_);
return v_res_1399_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2(lean_object* v_e_1400_, lean_object* v_fvarId_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_){
_start:
{
lean_object* v___x_1407_; 
v___x_1407_ = l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2___redArg(v_e_1400_, v_fvarId_1401_, v___y_1403_);
return v___x_1407_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2___boxed(lean_object* v_e_1408_, lean_object* v_fvarId_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_){
_start:
{
lean_object* v_res_1415_; 
v_res_1415_ = l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2(v_e_1408_, v_fvarId_1409_, v___y_1410_, v___y_1411_, v___y_1412_, v___y_1413_);
lean_dec(v___y_1413_);
lean_dec_ref(v___y_1412_);
lean_dec(v___y_1411_);
lean_dec_ref(v___y_1410_);
return v_res_1415_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_Meta_getMajorTypeIndices_spec__0(lean_object* v_a_1416_, lean_object* v_x_1417_){
_start:
{
if (lean_obj_tag(v_x_1417_) == 0)
{
uint8_t v___x_1418_; 
v___x_1418_ = 0;
return v___x_1418_;
}
else
{
lean_object* v_head_1419_; lean_object* v_tail_1420_; uint8_t v___x_1421_; 
v_head_1419_ = lean_ctor_get(v_x_1417_, 0);
v_tail_1420_ = lean_ctor_get(v_x_1417_, 1);
v___x_1421_ = lean_nat_dec_eq(v_a_1416_, v_head_1419_);
if (v___x_1421_ == 0)
{
v_x_1417_ = v_tail_1420_;
goto _start;
}
else
{
return v___x_1421_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_Meta_getMajorTypeIndices_spec__0___boxed(lean_object* v_a_1423_, lean_object* v_x_1424_){
_start:
{
uint8_t v_res_1425_; lean_object* v_r_1426_; 
v_res_1425_ = l_List_elem___at___00Lean_Meta_getMajorTypeIndices_spec__0(v_a_1423_, v_x_1424_);
lean_dec(v_x_1424_);
lean_dec(v_a_1423_);
v_r_1426_ = lean_box(v_res_1425_);
return v_r_1426_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_1428_; lean_object* v___x_1429_; 
v___x_1428_ = ((lean_object*)(l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__0));
v___x_1429_ = l_Lean_stringToMessageData(v___x_1428_);
return v___x_1429_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_1431_; lean_object* v___x_1432_; 
v___x_1431_ = ((lean_object*)(l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__2));
v___x_1432_ = l_Lean_stringToMessageData(v___x_1431_);
return v___x_1432_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__5(void){
_start:
{
lean_object* v___x_1434_; lean_object* v___x_1435_; 
v___x_1434_ = ((lean_object*)(l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__4));
v___x_1435_ = l_Lean_stringToMessageData(v___x_1434_);
return v___x_1435_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__7(void){
_start:
{
lean_object* v___x_1437_; lean_object* v___x_1438_; 
v___x_1437_ = ((lean_object*)(l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__6));
v___x_1438_ = l_Lean_stringToMessageData(v___x_1437_);
return v___x_1438_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg(lean_object* v_majorTypeArgs_1439_, lean_object* v_idxPos_1440_, lean_object* v_recursorInfo_1441_, lean_object* v_idx_1442_, lean_object* v_tacticName_1443_, lean_object* v_mvarId_1444_, lean_object* v_majorType_1445_, lean_object* v_n_1446_, lean_object* v_i_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_){
_start:
{
lean_object* v_zero_1453_; uint8_t v_isZero_1454_; 
v_zero_1453_ = lean_unsigned_to_nat(0u);
v_isZero_1454_ = lean_nat_dec_eq(v_i_1447_, v_zero_1453_);
if (v_isZero_1454_ == 1)
{
lean_object* v___x_1455_; lean_object* v___x_1456_; 
lean_dec(v_i_1447_);
lean_dec_ref(v_majorType_1445_);
lean_dec(v_mvarId_1444_);
lean_dec(v_tacticName_1443_);
lean_dec_ref(v_idx_1442_);
v___x_1455_ = lean_box(0);
v___x_1456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1456_, 0, v___x_1455_);
return v___x_1456_;
}
else
{
lean_object* v_one_1457_; lean_object* v_n_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v_arg_1461_; lean_object* v___y_1463_; lean_object* v___y_1464_; lean_object* v___y_1465_; lean_object* v___y_1466_; lean_object* v___y_1510_; lean_object* v___y_1511_; lean_object* v___y_1512_; lean_object* v___y_1513_; uint8_t v___x_1534_; 
v_one_1457_ = lean_unsigned_to_nat(1u);
v_n_1458_ = lean_nat_sub(v_i_1447_, v_one_1457_);
lean_dec(v_i_1447_);
v___x_1459_ = lean_nat_sub(v_n_1446_, v_n_1458_);
v___x_1460_ = lean_nat_sub(v___x_1459_, v_one_1457_);
lean_dec(v___x_1459_);
v_arg_1461_ = lean_array_fget_borrowed(v_majorTypeArgs_1439_, v___x_1460_);
v___x_1534_ = lean_nat_dec_eq(v___x_1460_, v_idxPos_1440_);
if (v___x_1534_ == 0)
{
uint8_t v___x_1535_; 
v___x_1535_ = lean_expr_eqv(v_arg_1461_, v_idx_1442_);
if (v___x_1535_ == 0)
{
v___y_1510_ = v___y_1448_;
v___y_1511_ = v___y_1449_;
v___y_1512_ = v___y_1450_;
v___y_1513_ = v___y_1451_;
goto v___jp_1509_;
}
else
{
lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; 
v___x_1536_ = lean_obj_once(&l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1, &l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1_once, _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1);
lean_inc_ref(v_idx_1442_);
v___x_1537_ = l_Lean_MessageData_ofExpr(v_idx_1442_);
v___x_1538_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1538_, 0, v___x_1536_);
lean_ctor_set(v___x_1538_, 1, v___x_1537_);
v___x_1539_ = lean_obj_once(&l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__7, &l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__7_once, _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__7);
v___x_1540_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1540_, 0, v___x_1538_);
lean_ctor_set(v___x_1540_, 1, v___x_1539_);
lean_inc_ref(v_majorType_1445_);
v___x_1541_ = l_Lean_indentExpr(v_majorType_1445_);
v___x_1542_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1542_, 0, v___x_1540_);
lean_ctor_set(v___x_1542_, 1, v___x_1541_);
v___x_1543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1543_, 0, v___x_1542_);
lean_inc(v_mvarId_1444_);
lean_inc(v_tacticName_1443_);
v___x_1544_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1443_, v_mvarId_1444_, v___x_1543_, v___y_1448_, v___y_1449_, v___y_1450_, v___y_1451_);
if (lean_obj_tag(v___x_1544_) == 0)
{
lean_dec_ref_known(v___x_1544_, 1);
v___y_1510_ = v___y_1448_;
v___y_1511_ = v___y_1449_;
v___y_1512_ = v___y_1450_;
v___y_1513_ = v___y_1451_;
goto v___jp_1509_;
}
else
{
lean_dec(v___x_1460_);
lean_dec(v_n_1458_);
lean_dec_ref(v_majorType_1445_);
lean_dec(v_mvarId_1444_);
lean_dec(v_tacticName_1443_);
lean_dec_ref(v_idx_1442_);
return v___x_1544_;
}
}
}
else
{
v___y_1510_ = v___y_1448_;
v___y_1511_ = v___y_1449_;
v___y_1512_ = v___y_1450_;
v___y_1513_ = v___y_1451_;
goto v___jp_1509_;
}
v___jp_1462_:
{
uint8_t v___x_1467_; 
v___x_1467_ = lean_nat_dec_lt(v_idxPos_1440_, v___x_1460_);
if (v___x_1467_ == 0)
{
lean_dec(v___x_1460_);
v_i_1447_ = v_n_1458_;
goto _start;
}
else
{
lean_object* v_indicesPos_1469_; uint8_t v___x_1470_; 
v_indicesPos_1469_ = lean_ctor_get(v_recursorInfo_1441_, 6);
v___x_1470_ = l_List_elem___at___00Lean_Meta_getMajorTypeIndices_spec__0(v___x_1460_, v_indicesPos_1469_);
if (v___x_1470_ == 0)
{
lean_dec(v___x_1460_);
v_i_1447_ = v_n_1458_;
goto _start;
}
else
{
uint8_t v___x_1472_; 
v___x_1472_ = l_Lean_Expr_isFVar(v_arg_1461_);
if (v___x_1472_ == 0)
{
lean_dec(v___x_1460_);
v_i_1447_ = v_n_1458_;
goto _start;
}
else
{
lean_object* v___x_1474_; lean_object* v___x_1475_; 
v___x_1474_ = l_Lean_Expr_fvarId_x21(v_idx_1442_);
v___x_1475_ = l_Lean_FVarId_getDecl___redArg(v___x_1474_, v___y_1463_, v___y_1465_, v___y_1466_);
if (lean_obj_tag(v___x_1475_) == 0)
{
lean_object* v_a_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v_a_1479_; lean_object* v___x_1481_; uint8_t v_isShared_1482_; uint8_t v_isSharedCheck_1500_; 
v_a_1476_ = lean_ctor_get(v___x_1475_, 0);
lean_inc(v_a_1476_);
lean_dec_ref_known(v___x_1475_, 1);
v___x_1477_ = l_Lean_Expr_fvarId_x21(v_arg_1461_);
v___x_1478_ = l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg(v_a_1476_, v___x_1477_, v___x_1470_, v___y_1464_);
v_a_1479_ = lean_ctor_get(v___x_1478_, 0);
v_isSharedCheck_1500_ = !lean_is_exclusive(v___x_1478_);
if (v_isSharedCheck_1500_ == 0)
{
v___x_1481_ = v___x_1478_;
v_isShared_1482_ = v_isSharedCheck_1500_;
goto v_resetjp_1480_;
}
else
{
lean_inc(v_a_1479_);
lean_dec(v___x_1478_);
v___x_1481_ = lean_box(0);
v_isShared_1482_ = v_isSharedCheck_1500_;
goto v_resetjp_1480_;
}
v_resetjp_1480_:
{
uint8_t v___x_1483_; 
v___x_1483_ = lean_unbox(v_a_1479_);
lean_dec(v_a_1479_);
if (v___x_1483_ == 0)
{
lean_del_object(v___x_1481_);
lean_dec(v___x_1460_);
v_i_1447_ = v_n_1458_;
goto _start;
}
else
{
lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1493_; 
v___x_1485_ = lean_obj_once(&l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1, &l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1_once, _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1);
lean_inc_ref(v_idx_1442_);
v___x_1486_ = l_Lean_MessageData_ofExpr(v_idx_1442_);
v___x_1487_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1487_, 0, v___x_1485_);
lean_ctor_set(v___x_1487_, 1, v___x_1486_);
v___x_1488_ = lean_obj_once(&l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__3, &l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__3_once, _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__3);
v___x_1489_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1489_, 0, v___x_1487_);
lean_ctor_set(v___x_1489_, 1, v___x_1488_);
v___x_1490_ = lean_nat_add(v___x_1460_, v_one_1457_);
lean_dec(v___x_1460_);
v___x_1491_ = l_Nat_reprFast(v___x_1490_);
if (v_isShared_1482_ == 0)
{
lean_ctor_set_tag(v___x_1481_, 3);
lean_ctor_set(v___x_1481_, 0, v___x_1491_);
v___x_1493_ = v___x_1481_;
goto v_reusejp_1492_;
}
else
{
lean_object* v_reuseFailAlloc_1499_; 
v_reuseFailAlloc_1499_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1499_, 0, v___x_1491_);
v___x_1493_ = v_reuseFailAlloc_1499_;
goto v_reusejp_1492_;
}
v_reusejp_1492_:
{
lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; 
v___x_1494_ = l_Lean_MessageData_ofFormat(v___x_1493_);
v___x_1495_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1495_, 0, v___x_1489_);
lean_ctor_set(v___x_1495_, 1, v___x_1494_);
v___x_1496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1496_, 0, v___x_1495_);
lean_inc(v_mvarId_1444_);
lean_inc(v_tacticName_1443_);
v___x_1497_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1443_, v_mvarId_1444_, v___x_1496_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_);
if (lean_obj_tag(v___x_1497_) == 0)
{
lean_dec_ref_known(v___x_1497_, 1);
v_i_1447_ = v_n_1458_;
goto _start;
}
else
{
lean_dec(v_n_1458_);
lean_dec_ref(v_majorType_1445_);
lean_dec(v_mvarId_1444_);
lean_dec(v_tacticName_1443_);
lean_dec_ref(v_idx_1442_);
return v___x_1497_;
}
}
}
}
}
else
{
lean_object* v_a_1501_; lean_object* v___x_1503_; uint8_t v_isShared_1504_; uint8_t v_isSharedCheck_1508_; 
lean_dec(v___x_1460_);
lean_dec(v_n_1458_);
lean_dec_ref(v_majorType_1445_);
lean_dec(v_mvarId_1444_);
lean_dec(v_tacticName_1443_);
lean_dec_ref(v_idx_1442_);
v_a_1501_ = lean_ctor_get(v___x_1475_, 0);
v_isSharedCheck_1508_ = !lean_is_exclusive(v___x_1475_);
if (v_isSharedCheck_1508_ == 0)
{
v___x_1503_ = v___x_1475_;
v_isShared_1504_ = v_isSharedCheck_1508_;
goto v_resetjp_1502_;
}
else
{
lean_inc(v_a_1501_);
lean_dec(v___x_1475_);
v___x_1503_ = lean_box(0);
v_isShared_1504_ = v_isSharedCheck_1508_;
goto v_resetjp_1502_;
}
v_resetjp_1502_:
{
lean_object* v___x_1506_; 
if (v_isShared_1504_ == 0)
{
v___x_1506_ = v___x_1503_;
goto v_reusejp_1505_;
}
else
{
lean_object* v_reuseFailAlloc_1507_; 
v_reuseFailAlloc_1507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1507_, 0, v_a_1501_);
v___x_1506_ = v_reuseFailAlloc_1507_;
goto v_reusejp_1505_;
}
v_reusejp_1505_:
{
return v___x_1506_;
}
}
}
}
}
}
}
v___jp_1509_:
{
uint8_t v___x_1514_; 
v___x_1514_ = lean_nat_dec_lt(v___x_1460_, v_idxPos_1440_);
if (v___x_1514_ == 0)
{
v___y_1463_ = v___y_1510_;
v___y_1464_ = v___y_1511_;
v___y_1465_ = v___y_1512_;
v___y_1466_ = v___y_1513_;
goto v___jp_1462_;
}
else
{
lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v_a_1517_; lean_object* v___x_1519_; uint8_t v_isShared_1520_; uint8_t v_isSharedCheck_1533_; 
v___x_1515_ = l_Lean_Expr_fvarId_x21(v_idx_1442_);
lean_inc(v_arg_1461_);
v___x_1516_ = l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2___redArg(v_arg_1461_, v___x_1515_, v___y_1511_);
v_a_1517_ = lean_ctor_get(v___x_1516_, 0);
v_isSharedCheck_1533_ = !lean_is_exclusive(v___x_1516_);
if (v_isSharedCheck_1533_ == 0)
{
v___x_1519_ = v___x_1516_;
v_isShared_1520_ = v_isSharedCheck_1533_;
goto v_resetjp_1518_;
}
else
{
lean_inc(v_a_1517_);
lean_dec(v___x_1516_);
v___x_1519_ = lean_box(0);
v_isShared_1520_ = v_isSharedCheck_1533_;
goto v_resetjp_1518_;
}
v_resetjp_1518_:
{
uint8_t v___x_1521_; 
v___x_1521_ = lean_unbox(v_a_1517_);
lean_dec(v_a_1517_);
if (v___x_1521_ == 0)
{
lean_del_object(v___x_1519_);
v___y_1463_ = v___y_1510_;
v___y_1464_ = v___y_1511_;
v___y_1465_ = v___y_1512_;
v___y_1466_ = v___y_1513_;
goto v___jp_1462_;
}
else
{
lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1530_; 
v___x_1522_ = lean_obj_once(&l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1, &l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1_once, _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1);
lean_inc_ref(v_idx_1442_);
v___x_1523_ = l_Lean_MessageData_ofExpr(v_idx_1442_);
v___x_1524_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1524_, 0, v___x_1522_);
lean_ctor_set(v___x_1524_, 1, v___x_1523_);
v___x_1525_ = lean_obj_once(&l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__5, &l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__5_once, _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__5);
v___x_1526_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1526_, 0, v___x_1524_);
lean_ctor_set(v___x_1526_, 1, v___x_1525_);
lean_inc_ref(v_majorType_1445_);
v___x_1527_ = l_Lean_indentExpr(v_majorType_1445_);
v___x_1528_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1528_, 0, v___x_1526_);
lean_ctor_set(v___x_1528_, 1, v___x_1527_);
if (v_isShared_1520_ == 0)
{
lean_ctor_set_tag(v___x_1519_, 1);
lean_ctor_set(v___x_1519_, 0, v___x_1528_);
v___x_1530_ = v___x_1519_;
goto v_reusejp_1529_;
}
else
{
lean_object* v_reuseFailAlloc_1532_; 
v_reuseFailAlloc_1532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1532_, 0, v___x_1528_);
v___x_1530_ = v_reuseFailAlloc_1532_;
goto v_reusejp_1529_;
}
v_reusejp_1529_:
{
lean_object* v___x_1531_; 
lean_inc(v_mvarId_1444_);
lean_inc(v_tacticName_1443_);
v___x_1531_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1443_, v_mvarId_1444_, v___x_1530_, v___y_1510_, v___y_1511_, v___y_1512_, v___y_1513_);
if (lean_obj_tag(v___x_1531_) == 0)
{
lean_dec_ref_known(v___x_1531_, 1);
v___y_1463_ = v___y_1510_;
v___y_1464_ = v___y_1511_;
v___y_1465_ = v___y_1512_;
v___y_1466_ = v___y_1513_;
goto v___jp_1462_;
}
else
{
lean_dec(v___x_1460_);
lean_dec(v_n_1458_);
lean_dec_ref(v_majorType_1445_);
lean_dec(v_mvarId_1444_);
lean_dec(v_tacticName_1443_);
lean_dec_ref(v_idx_1442_);
return v___x_1531_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___boxed(lean_object* v_majorTypeArgs_1545_, lean_object* v_idxPos_1546_, lean_object* v_recursorInfo_1547_, lean_object* v_idx_1548_, lean_object* v_tacticName_1549_, lean_object* v_mvarId_1550_, lean_object* v_majorType_1551_, lean_object* v_n_1552_, lean_object* v_i_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_){
_start:
{
lean_object* v_res_1559_; 
v_res_1559_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg(v_majorTypeArgs_1545_, v_idxPos_1546_, v_recursorInfo_1547_, v_idx_1548_, v_tacticName_1549_, v_mvarId_1550_, v_majorType_1551_, v_n_1552_, v_i_1553_, v___y_1554_, v___y_1555_, v___y_1556_, v___y_1557_);
lean_dec(v___y_1557_);
lean_dec_ref(v___y_1556_);
lean_dec(v___y_1555_);
lean_dec_ref(v___y_1554_);
lean_dec(v_n_1552_);
lean_dec_ref(v_recursorInfo_1547_);
lean_dec(v_idxPos_1546_);
lean_dec_ref(v_majorTypeArgs_1545_);
return v_res_1559_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__1(void){
_start:
{
lean_object* v___x_1561_; lean_object* v___x_1562_; 
v___x_1561_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__0));
v___x_1562_ = l_Lean_stringToMessageData(v___x_1561_);
return v___x_1562_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__3(void){
_start:
{
lean_object* v___x_1564_; lean_object* v___x_1565_; 
v___x_1564_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__2));
v___x_1565_ = l_Lean_stringToMessageData(v___x_1564_);
return v___x_1565_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__5(void){
_start:
{
lean_object* v___x_1567_; lean_object* v___x_1568_; 
v___x_1567_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__4));
v___x_1568_ = l_Lean_stringToMessageData(v___x_1567_);
return v___x_1568_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4(lean_object* v_majorTypeArgs_1569_, lean_object* v_recursorInfo_1570_, lean_object* v_tacticName_1571_, lean_object* v_mvarId_1572_, lean_object* v_majorType_1573_, size_t v_sz_1574_, size_t v_i_1575_, lean_object* v_bs_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_){
_start:
{
uint8_t v___x_1582_; 
v___x_1582_ = lean_usize_dec_lt(v_i_1575_, v_sz_1574_);
if (v___x_1582_ == 0)
{
lean_object* v___x_1583_; 
lean_dec_ref(v_majorType_1573_);
lean_dec(v_mvarId_1572_);
lean_dec(v_tacticName_1571_);
v___x_1583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1583_, 0, v_bs_1576_);
return v___x_1583_;
}
else
{
lean_object* v_v_1584_; lean_object* v___x_1585_; lean_object* v_bs_x27_1586_; lean_object* v_a_1588_; lean_object* v___x_1593_; uint8_t v___x_1594_; 
v_v_1584_ = lean_array_uget(v_bs_1576_, v_i_1575_);
v___x_1585_ = lean_unsigned_to_nat(0u);
v_bs_x27_1586_ = lean_array_uset(v_bs_1576_, v_i_1575_, v___x_1585_);
v___x_1593_ = lean_array_get_size(v_majorTypeArgs_1569_);
v___x_1594_ = lean_nat_dec_le(v___x_1593_, v_v_1584_);
if (v___x_1594_ == 0)
{
lean_object* v_idx_1595_; lean_object* v___y_1597_; lean_object* v___y_1598_; lean_object* v___y_1599_; lean_object* v___y_1600_; uint8_t v___x_1610_; 
v_idx_1595_ = lean_array_fget_borrowed(v_majorTypeArgs_1569_, v_v_1584_);
v___x_1610_ = l_Lean_Expr_isFVar(v_idx_1595_);
if (v___x_1610_ == 0)
{
lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; 
v___x_1611_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__1);
lean_inc(v_idx_1595_);
v___x_1612_ = l_Lean_MessageData_ofExpr(v_idx_1595_);
v___x_1613_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1613_, 0, v___x_1611_);
lean_ctor_set(v___x_1613_, 1, v___x_1612_);
v___x_1614_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__3);
v___x_1615_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1615_, 0, v___x_1613_);
lean_ctor_set(v___x_1615_, 1, v___x_1614_);
lean_inc_ref(v_majorType_1573_);
v___x_1616_ = l_Lean_indentExpr(v_majorType_1573_);
v___x_1617_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1617_, 0, v___x_1615_);
lean_ctor_set(v___x_1617_, 1, v___x_1616_);
v___x_1618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1618_, 0, v___x_1617_);
lean_inc(v_mvarId_1572_);
lean_inc(v_tacticName_1571_);
v___x_1619_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1571_, v_mvarId_1572_, v___x_1618_, v___y_1577_, v___y_1578_, v___y_1579_, v___y_1580_);
if (lean_obj_tag(v___x_1619_) == 0)
{
lean_dec_ref_known(v___x_1619_, 1);
v___y_1597_ = v___y_1577_;
v___y_1598_ = v___y_1578_;
v___y_1599_ = v___y_1579_;
v___y_1600_ = v___y_1580_;
goto v___jp_1596_;
}
else
{
lean_object* v_a_1620_; lean_object* v___x_1622_; uint8_t v_isShared_1623_; uint8_t v_isSharedCheck_1627_; 
lean_dec_ref(v_bs_x27_1586_);
lean_dec(v_v_1584_);
lean_dec_ref(v_majorType_1573_);
lean_dec(v_mvarId_1572_);
lean_dec(v_tacticName_1571_);
v_a_1620_ = lean_ctor_get(v___x_1619_, 0);
v_isSharedCheck_1627_ = !lean_is_exclusive(v___x_1619_);
if (v_isSharedCheck_1627_ == 0)
{
v___x_1622_ = v___x_1619_;
v_isShared_1623_ = v_isSharedCheck_1627_;
goto v_resetjp_1621_;
}
else
{
lean_inc(v_a_1620_);
lean_dec(v___x_1619_);
v___x_1622_ = lean_box(0);
v_isShared_1623_ = v_isSharedCheck_1627_;
goto v_resetjp_1621_;
}
v_resetjp_1621_:
{
lean_object* v___x_1625_; 
if (v_isShared_1623_ == 0)
{
v___x_1625_ = v___x_1622_;
goto v_reusejp_1624_;
}
else
{
lean_object* v_reuseFailAlloc_1626_; 
v_reuseFailAlloc_1626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1626_, 0, v_a_1620_);
v___x_1625_ = v_reuseFailAlloc_1626_;
goto v_reusejp_1624_;
}
v_reusejp_1624_:
{
return v___x_1625_;
}
}
}
}
else
{
v___y_1597_ = v___y_1577_;
v___y_1598_ = v___y_1578_;
v___y_1599_ = v___y_1579_;
v___y_1600_ = v___y_1580_;
goto v___jp_1596_;
}
v___jp_1596_:
{
lean_object* v___x_1601_; 
lean_inc_ref(v_majorType_1573_);
lean_inc(v_mvarId_1572_);
lean_inc(v_tacticName_1571_);
lean_inc(v_idx_1595_);
v___x_1601_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg(v_majorTypeArgs_1569_, v_v_1584_, v_recursorInfo_1570_, v_idx_1595_, v_tacticName_1571_, v_mvarId_1572_, v_majorType_1573_, v___x_1593_, v___x_1593_, v___y_1597_, v___y_1598_, v___y_1599_, v___y_1600_);
lean_dec(v_v_1584_);
if (lean_obj_tag(v___x_1601_) == 0)
{
lean_dec_ref_known(v___x_1601_, 1);
lean_inc(v_idx_1595_);
v_a_1588_ = v_idx_1595_;
goto v___jp_1587_;
}
else
{
lean_object* v_a_1602_; lean_object* v___x_1604_; uint8_t v_isShared_1605_; uint8_t v_isSharedCheck_1609_; 
lean_dec_ref(v_bs_x27_1586_);
lean_dec_ref(v_majorType_1573_);
lean_dec(v_mvarId_1572_);
lean_dec(v_tacticName_1571_);
v_a_1602_ = lean_ctor_get(v___x_1601_, 0);
v_isSharedCheck_1609_ = !lean_is_exclusive(v___x_1601_);
if (v_isSharedCheck_1609_ == 0)
{
v___x_1604_ = v___x_1601_;
v_isShared_1605_ = v_isSharedCheck_1609_;
goto v_resetjp_1603_;
}
else
{
lean_inc(v_a_1602_);
lean_dec(v___x_1601_);
v___x_1604_ = lean_box(0);
v_isShared_1605_ = v_isSharedCheck_1609_;
goto v_resetjp_1603_;
}
v_resetjp_1603_:
{
lean_object* v___x_1607_; 
if (v_isShared_1605_ == 0)
{
v___x_1607_ = v___x_1604_;
goto v_reusejp_1606_;
}
else
{
lean_object* v_reuseFailAlloc_1608_; 
v_reuseFailAlloc_1608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1608_, 0, v_a_1602_);
v___x_1607_ = v_reuseFailAlloc_1608_;
goto v_reusejp_1606_;
}
v_reusejp_1606_:
{
return v___x_1607_;
}
}
}
}
}
else
{
lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; 
lean_dec(v_v_1584_);
v___x_1628_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__5, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__5);
lean_inc_ref(v_majorType_1573_);
v___x_1629_ = l_Lean_indentExpr(v_majorType_1573_);
v___x_1630_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1630_, 0, v___x_1628_);
lean_ctor_set(v___x_1630_, 1, v___x_1629_);
v___x_1631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1631_, 0, v___x_1630_);
lean_inc(v_mvarId_1572_);
lean_inc(v_tacticName_1571_);
v___x_1632_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1571_, v_mvarId_1572_, v___x_1631_, v___y_1577_, v___y_1578_, v___y_1579_, v___y_1580_);
if (lean_obj_tag(v___x_1632_) == 0)
{
lean_object* v_a_1633_; 
v_a_1633_ = lean_ctor_get(v___x_1632_, 0);
lean_inc(v_a_1633_);
lean_dec_ref_known(v___x_1632_, 1);
v_a_1588_ = v_a_1633_;
goto v___jp_1587_;
}
else
{
lean_object* v_a_1634_; lean_object* v___x_1636_; uint8_t v_isShared_1637_; uint8_t v_isSharedCheck_1641_; 
lean_dec_ref(v_bs_x27_1586_);
lean_dec_ref(v_majorType_1573_);
lean_dec(v_mvarId_1572_);
lean_dec(v_tacticName_1571_);
v_a_1634_ = lean_ctor_get(v___x_1632_, 0);
v_isSharedCheck_1641_ = !lean_is_exclusive(v___x_1632_);
if (v_isSharedCheck_1641_ == 0)
{
v___x_1636_ = v___x_1632_;
v_isShared_1637_ = v_isSharedCheck_1641_;
goto v_resetjp_1635_;
}
else
{
lean_inc(v_a_1634_);
lean_dec(v___x_1632_);
v___x_1636_ = lean_box(0);
v_isShared_1637_ = v_isSharedCheck_1641_;
goto v_resetjp_1635_;
}
v_resetjp_1635_:
{
lean_object* v___x_1639_; 
if (v_isShared_1637_ == 0)
{
v___x_1639_ = v___x_1636_;
goto v_reusejp_1638_;
}
else
{
lean_object* v_reuseFailAlloc_1640_; 
v_reuseFailAlloc_1640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1640_, 0, v_a_1634_);
v___x_1639_ = v_reuseFailAlloc_1640_;
goto v_reusejp_1638_;
}
v_reusejp_1638_:
{
return v___x_1639_;
}
}
}
}
v___jp_1587_:
{
size_t v___x_1589_; size_t v___x_1590_; lean_object* v___x_1591_; 
v___x_1589_ = ((size_t)1ULL);
v___x_1590_ = lean_usize_add(v_i_1575_, v___x_1589_);
v___x_1591_ = lean_array_uset(v_bs_x27_1586_, v_i_1575_, v_a_1588_);
v_i_1575_ = v___x_1590_;
v_bs_1576_ = v___x_1591_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___boxed(lean_object* v_majorTypeArgs_1642_, lean_object* v_recursorInfo_1643_, lean_object* v_tacticName_1644_, lean_object* v_mvarId_1645_, lean_object* v_majorType_1646_, lean_object* v_sz_1647_, lean_object* v_i_1648_, lean_object* v_bs_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_){
_start:
{
size_t v_sz_boxed_1655_; size_t v_i_boxed_1656_; lean_object* v_res_1657_; 
v_sz_boxed_1655_ = lean_unbox_usize(v_sz_1647_);
lean_dec(v_sz_1647_);
v_i_boxed_1656_ = lean_unbox_usize(v_i_1648_);
lean_dec(v_i_1648_);
v_res_1657_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4(v_majorTypeArgs_1642_, v_recursorInfo_1643_, v_tacticName_1644_, v_mvarId_1645_, v_majorType_1646_, v_sz_boxed_1655_, v_i_boxed_1656_, v_bs_1649_, v___y_1650_, v___y_1651_, v___y_1652_, v___y_1653_);
lean_dec(v___y_1653_);
lean_dec_ref(v___y_1652_);
lean_dec(v___y_1651_);
lean_dec_ref(v___y_1650_);
lean_dec_ref(v_recursorInfo_1643_);
lean_dec_ref(v_majorTypeArgs_1642_);
return v_res_1657_;
}
}
static lean_object* _init_l_Lean_Meta_getMajorTypeIndices___closed__0(void){
_start:
{
lean_object* v___x_1658_; lean_object* v_dummy_1659_; 
v___x_1658_ = lean_box(0);
v_dummy_1659_ = l_Lean_Expr_sort___override(v___x_1658_);
return v_dummy_1659_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMajorTypeIndices(lean_object* v_mvarId_1660_, lean_object* v_tacticName_1661_, lean_object* v_recursorInfo_1662_, lean_object* v_majorType_1663_, lean_object* v_a_1664_, lean_object* v_a_1665_, lean_object* v_a_1666_, lean_object* v_a_1667_){
_start:
{
lean_object* v_indicesPos_1669_; lean_object* v_nargs_1670_; lean_object* v_dummy_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v_majorTypeArgs_1675_; lean_object* v___x_1676_; size_t v_sz_1677_; size_t v___x_1678_; lean_object* v___x_1679_; 
v_indicesPos_1669_ = lean_ctor_get(v_recursorInfo_1662_, 6);
v_nargs_1670_ = l_Lean_Expr_getAppNumArgs(v_majorType_1663_);
v_dummy_1671_ = lean_obj_once(&l_Lean_Meta_getMajorTypeIndices___closed__0, &l_Lean_Meta_getMajorTypeIndices___closed__0_once, _init_l_Lean_Meta_getMajorTypeIndices___closed__0);
lean_inc(v_nargs_1670_);
v___x_1672_ = lean_mk_array(v_nargs_1670_, v_dummy_1671_);
v___x_1673_ = lean_unsigned_to_nat(1u);
v___x_1674_ = lean_nat_sub(v_nargs_1670_, v___x_1673_);
lean_dec(v_nargs_1670_);
lean_inc_ref(v_majorType_1663_);
v_majorTypeArgs_1675_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_majorType_1663_, v___x_1672_, v___x_1674_);
lean_inc(v_indicesPos_1669_);
v___x_1676_ = lean_array_mk(v_indicesPos_1669_);
v_sz_1677_ = lean_array_size(v___x_1676_);
v___x_1678_ = ((size_t)0ULL);
v___x_1679_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4(v_majorTypeArgs_1675_, v_recursorInfo_1662_, v_tacticName_1661_, v_mvarId_1660_, v_majorType_1663_, v_sz_1677_, v___x_1678_, v___x_1676_, v_a_1664_, v_a_1665_, v_a_1666_, v_a_1667_);
lean_dec_ref(v_recursorInfo_1662_);
lean_dec_ref(v_majorTypeArgs_1675_);
return v___x_1679_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMajorTypeIndices___boxed(lean_object* v_mvarId_1680_, lean_object* v_tacticName_1681_, lean_object* v_recursorInfo_1682_, lean_object* v_majorType_1683_, lean_object* v_a_1684_, lean_object* v_a_1685_, lean_object* v_a_1686_, lean_object* v_a_1687_, lean_object* v_a_1688_){
_start:
{
lean_object* v_res_1689_; 
v_res_1689_ = l_Lean_Meta_getMajorTypeIndices(v_mvarId_1680_, v_tacticName_1681_, v_recursorInfo_1682_, v_majorType_1683_, v_a_1684_, v_a_1685_, v_a_1686_, v_a_1687_);
lean_dec(v_a_1687_);
lean_dec_ref(v_a_1686_);
lean_dec(v_a_1685_);
lean_dec_ref(v_a_1684_);
return v_res_1689_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3(lean_object* v_majorTypeArgs_1690_, lean_object* v_idxPos_1691_, lean_object* v_recursorInfo_1692_, lean_object* v_idx_1693_, lean_object* v_tacticName_1694_, lean_object* v_mvarId_1695_, lean_object* v_majorType_1696_, lean_object* v_n_1697_, lean_object* v_i_1698_, lean_object* v_a_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_){
_start:
{
lean_object* v___x_1705_; 
v___x_1705_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg(v_majorTypeArgs_1690_, v_idxPos_1691_, v_recursorInfo_1692_, v_idx_1693_, v_tacticName_1694_, v_mvarId_1695_, v_majorType_1696_, v_n_1697_, v_i_1698_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_);
return v___x_1705_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___boxed(lean_object* v_majorTypeArgs_1706_, lean_object* v_idxPos_1707_, lean_object* v_recursorInfo_1708_, lean_object* v_idx_1709_, lean_object* v_tacticName_1710_, lean_object* v_mvarId_1711_, lean_object* v_majorType_1712_, lean_object* v_n_1713_, lean_object* v_i_1714_, lean_object* v_a_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_){
_start:
{
lean_object* v_res_1721_; 
v_res_1721_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3(v_majorTypeArgs_1706_, v_idxPos_1707_, v_recursorInfo_1708_, v_idx_1709_, v_tacticName_1710_, v_mvarId_1711_, v_majorType_1712_, v_n_1713_, v_i_1714_, v_a_1715_, v___y_1716_, v___y_1717_, v___y_1718_, v___y_1719_);
lean_dec(v___y_1719_);
lean_dec_ref(v___y_1718_);
lean_dec(v___y_1717_);
lean_dec_ref(v___y_1716_);
lean_dec(v_n_1713_);
lean_dec_ref(v_recursorInfo_1708_);
lean_dec(v_idxPos_1707_);
lean_dec_ref(v_majorTypeArgs_1706_);
return v_res_1721_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1___redArg(lean_object* v_name_1722_, lean_object* v_msg_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_){
_start:
{
lean_object* v_ref_1729_; lean_object* v_msg_1730_; lean_object* v___x_1731_; lean_object* v_a_1732_; lean_object* v___x_1734_; uint8_t v_isShared_1735_; uint8_t v_isSharedCheck_1740_; 
v_ref_1729_ = lean_ctor_get(v___y_1726_, 2);
v_msg_1730_ = l_Lean_MessageData_tagWithErrorName(v_msg_1723_, v_name_1722_);
v___x_1731_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1_spec__2(v_msg_1730_, v___y_1724_, v___y_1725_, v___y_1726_, v___y_1727_);
v_a_1732_ = lean_ctor_get(v___x_1731_, 0);
v_isSharedCheck_1740_ = !lean_is_exclusive(v___x_1731_);
if (v_isSharedCheck_1740_ == 0)
{
v___x_1734_ = v___x_1731_;
v_isShared_1735_ = v_isSharedCheck_1740_;
goto v_resetjp_1733_;
}
else
{
lean_inc(v_a_1732_);
lean_dec(v___x_1731_);
v___x_1734_ = lean_box(0);
v_isShared_1735_ = v_isSharedCheck_1740_;
goto v_resetjp_1733_;
}
v_resetjp_1733_:
{
lean_object* v___x_1736_; lean_object* v___x_1738_; 
lean_inc(v_ref_1729_);
v___x_1736_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1736_, 0, v_ref_1729_);
lean_ctor_set(v___x_1736_, 1, v_a_1732_);
if (v_isShared_1735_ == 0)
{
lean_ctor_set_tag(v___x_1734_, 1);
lean_ctor_set(v___x_1734_, 0, v___x_1736_);
v___x_1738_ = v___x_1734_;
goto v_reusejp_1737_;
}
else
{
lean_object* v_reuseFailAlloc_1739_; 
v_reuseFailAlloc_1739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1739_, 0, v___x_1736_);
v___x_1738_ = v_reuseFailAlloc_1739_;
goto v_reusejp_1737_;
}
v_reusejp_1737_:
{
return v___x_1738_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1___redArg___boxed(lean_object* v_name_1741_, lean_object* v_msg_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_){
_start:
{
lean_object* v_res_1748_; 
v_res_1748_ = l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1___redArg(v_name_1741_, v_msg_1742_, v___y_1743_, v___y_1744_, v___y_1745_, v___y_1746_);
lean_dec(v___y_1746_);
lean_dec_ref(v___y_1745_);
lean_dec(v___y_1744_);
lean_dec_ref(v___y_1743_);
return v_res_1748_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Meta_mkRecursorAppPrefix_spec__0(lean_object* v_a_1749_, lean_object* v___x_1750_, lean_object* v_tacticName_1751_, lean_object* v_mvarId_1752_, lean_object* v_x_1753_, lean_object* v_x_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_){
_start:
{
if (lean_obj_tag(v_x_1754_) == 0)
{
lean_object* v___x_1760_; 
lean_dec(v_mvarId_1752_);
lean_dec(v_tacticName_1751_);
lean_dec(v_a_1749_);
v___x_1760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1760_, 0, v_x_1753_);
return v___x_1760_;
}
else
{
lean_object* v_head_1761_; 
v_head_1761_ = lean_ctor_get(v_x_1754_, 0);
if (lean_obj_tag(v_head_1761_) == 0)
{
lean_object* v_tail_1762_; lean_object* v_fst_1763_; lean_object* v___x_1765_; uint8_t v_isShared_1766_; uint8_t v_isSharedCheck_1774_; 
v_tail_1762_ = lean_ctor_get(v_x_1754_, 1);
v_fst_1763_ = lean_ctor_get(v_x_1753_, 0);
v_isSharedCheck_1774_ = !lean_is_exclusive(v_x_1753_);
if (v_isSharedCheck_1774_ == 0)
{
lean_object* v_unused_1775_; 
v_unused_1775_ = lean_ctor_get(v_x_1753_, 1);
lean_dec(v_unused_1775_);
v___x_1765_ = v_x_1753_;
v_isShared_1766_ = v_isSharedCheck_1774_;
goto v_resetjp_1764_;
}
else
{
lean_inc(v_fst_1763_);
lean_dec(v_x_1753_);
v___x_1765_ = lean_box(0);
v_isShared_1766_ = v_isSharedCheck_1774_;
goto v_resetjp_1764_;
}
v_resetjp_1764_:
{
lean_object* v___x_1767_; uint8_t v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1771_; 
lean_inc(v_a_1749_);
v___x_1767_ = lean_array_push(v_fst_1763_, v_a_1749_);
v___x_1768_ = 1;
v___x_1769_ = lean_box(v___x_1768_);
if (v_isShared_1766_ == 0)
{
lean_ctor_set(v___x_1765_, 1, v___x_1769_);
lean_ctor_set(v___x_1765_, 0, v___x_1767_);
v___x_1771_ = v___x_1765_;
goto v_reusejp_1770_;
}
else
{
lean_object* v_reuseFailAlloc_1773_; 
v_reuseFailAlloc_1773_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1773_, 0, v___x_1767_);
lean_ctor_set(v_reuseFailAlloc_1773_, 1, v___x_1769_);
v___x_1771_ = v_reuseFailAlloc_1773_;
goto v_reusejp_1770_;
}
v_reusejp_1770_:
{
v_x_1753_ = v___x_1771_;
v_x_1754_ = v_tail_1762_;
goto _start;
}
}
}
else
{
lean_object* v_tail_1776_; lean_object* v_fst_1777_; lean_object* v_snd_1778_; lean_object* v___x_1780_; uint8_t v_isShared_1781_; uint8_t v_isSharedCheck_1795_; 
v_tail_1776_ = lean_ctor_get(v_x_1754_, 1);
v_fst_1777_ = lean_ctor_get(v_x_1753_, 0);
v_snd_1778_ = lean_ctor_get(v_x_1753_, 1);
v_isSharedCheck_1795_ = !lean_is_exclusive(v_x_1753_);
if (v_isSharedCheck_1795_ == 0)
{
v___x_1780_ = v_x_1753_;
v_isShared_1781_ = v_isSharedCheck_1795_;
goto v_resetjp_1779_;
}
else
{
lean_inc(v_snd_1778_);
lean_inc(v_fst_1777_);
lean_dec(v_x_1753_);
v___x_1780_ = lean_box(0);
v_isShared_1781_ = v_isSharedCheck_1795_;
goto v_resetjp_1779_;
}
v_resetjp_1779_:
{
lean_object* v_idx_1782_; lean_object* v___x_1783_; uint8_t v___x_1784_; 
v_idx_1782_ = lean_ctor_get(v_head_1761_, 0);
v___x_1783_ = lean_array_get_size(v___x_1750_);
v___x_1784_ = lean_nat_dec_le(v___x_1783_, v_idx_1782_);
if (v___x_1784_ == 0)
{
lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1788_; 
v___x_1785_ = lean_array_fget_borrowed(v___x_1750_, v_idx_1782_);
lean_inc(v___x_1785_);
v___x_1786_ = lean_array_push(v_fst_1777_, v___x_1785_);
if (v_isShared_1781_ == 0)
{
lean_ctor_set(v___x_1780_, 0, v___x_1786_);
v___x_1788_ = v___x_1780_;
goto v_reusejp_1787_;
}
else
{
lean_object* v_reuseFailAlloc_1790_; 
v_reuseFailAlloc_1790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1790_, 0, v___x_1786_);
lean_ctor_set(v_reuseFailAlloc_1790_, 1, v_snd_1778_);
v___x_1788_ = v_reuseFailAlloc_1790_;
goto v_reusejp_1787_;
}
v_reusejp_1787_:
{
v_x_1753_ = v___x_1788_;
v_x_1754_ = v_tail_1776_;
goto _start;
}
}
else
{
lean_object* v___x_1791_; lean_object* v___x_1792_; 
lean_del_object(v___x_1780_);
lean_dec(v_snd_1778_);
lean_dec(v_fst_1777_);
v___x_1791_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9);
lean_inc(v_mvarId_1752_);
lean_inc(v_tacticName_1751_);
v___x_1792_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1751_, v_mvarId_1752_, v___x_1791_, v___y_1755_, v___y_1756_, v___y_1757_, v___y_1758_);
if (lean_obj_tag(v___x_1792_) == 0)
{
lean_object* v_a_1793_; 
v_a_1793_ = lean_ctor_get(v___x_1792_, 0);
lean_inc(v_a_1793_);
lean_dec_ref_known(v___x_1792_, 1);
v_x_1753_ = v_a_1793_;
v_x_1754_ = v_tail_1776_;
goto _start;
}
else
{
lean_dec(v_mvarId_1752_);
lean_dec(v_tacticName_1751_);
lean_dec(v_a_1749_);
return v___x_1792_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Meta_mkRecursorAppPrefix_spec__0___boxed(lean_object* v_a_1796_, lean_object* v___x_1797_, lean_object* v_tacticName_1798_, lean_object* v_mvarId_1799_, lean_object* v_x_1800_, lean_object* v_x_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_){
_start:
{
lean_object* v_res_1807_; 
v_res_1807_ = l_List_foldlM___at___00Lean_Meta_mkRecursorAppPrefix_spec__0(v_a_1796_, v___x_1797_, v_tacticName_1798_, v_mvarId_1799_, v_x_1800_, v_x_1801_, v___y_1802_, v___y_1803_, v___y_1804_, v___y_1805_);
lean_dec(v___y_1805_);
lean_dec_ref(v___y_1804_);
lean_dec(v___y_1803_);
lean_dec_ref(v___y_1802_);
lean_dec(v_x_1801_);
lean_dec_ref(v___x_1797_);
return v_res_1807_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__8(void){
_start:
{
lean_object* v___x_1823_; lean_object* v___x_1824_; 
v___x_1823_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__7));
v___x_1824_ = l_Lean_stringToMessageData(v___x_1823_);
return v___x_1824_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__10(void){
_start:
{
lean_object* v___x_1826_; lean_object* v___x_1827_; 
v___x_1826_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__9));
v___x_1827_ = l_Lean_stringToMessageData(v___x_1826_);
return v___x_1827_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__13(void){
_start:
{
lean_object* v___x_1831_; lean_object* v___x_1832_; 
v___x_1831_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__12));
v___x_1832_ = l_Lean_MessageData_ofFormat(v___x_1831_);
return v___x_1832_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__14(void){
_start:
{
lean_object* v___x_1833_; lean_object* v___x_1834_; 
v___x_1833_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__13, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__13_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__13);
v___x_1834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1834_, 0, v___x_1833_);
return v___x_1834_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2(lean_object* v_recursorInfo_1835_, lean_object* v_a_1836_, lean_object* v_tacticName_1837_, lean_object* v_mvarId_1838_, lean_object* v_indices_1839_, lean_object* v_a_1840_, lean_object* v_major_1841_, lean_object* v_x_1842_, lean_object* v_x_1843_, lean_object* v_x_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_){
_start:
{
if (lean_obj_tag(v_x_1842_) == 5)
{
lean_object* v_fn_1850_; lean_object* v_arg_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; 
v_fn_1850_ = lean_ctor_get(v_x_1842_, 0);
lean_inc_ref(v_fn_1850_);
v_arg_1851_ = lean_ctor_get(v_x_1842_, 1);
lean_inc_ref(v_arg_1851_);
lean_dec_ref_known(v_x_1842_, 2);
v___x_1852_ = lean_array_set(v_x_1843_, v_x_1844_, v_arg_1851_);
v___x_1853_ = lean_unsigned_to_nat(1u);
v___x_1854_ = lean_nat_sub(v_x_1844_, v___x_1853_);
lean_dec(v_x_1844_);
v_x_1842_ = v_fn_1850_;
v_x_1843_ = v___x_1852_;
v_x_1844_ = v___x_1854_;
goto _start;
}
else
{
lean_dec(v_x_1844_);
if (lean_obj_tag(v_x_1842_) == 4)
{
lean_object* v_us_1856_; lean_object* v_recursorName_1857_; lean_object* v_univLevelPos_1858_; uint8_t v_depElim_1859_; lean_object* v_paramsPos_1860_; lean_object* v___x_1861_; uint8_t v___x_1862_; lean_object* v___y_1864_; lean_object* v_motive_1865_; lean_object* v___y_1866_; lean_object* v___y_1867_; lean_object* v___y_1868_; lean_object* v___y_1869_; lean_object* v___x_1882_; lean_object* v___x_1883_; 
v_us_1856_ = lean_ctor_get(v_x_1842_, 1);
lean_inc(v_us_1856_);
lean_dec_ref_known(v_x_1842_, 2);
v_recursorName_1857_ = lean_ctor_get(v_recursorInfo_1835_, 0);
lean_inc(v_recursorName_1857_);
v_univLevelPos_1858_ = lean_ctor_get(v_recursorInfo_1835_, 2);
lean_inc(v_univLevelPos_1858_);
v_depElim_1859_ = lean_ctor_get_uint8(v_recursorInfo_1835_, sizeof(void*)*8);
v_paramsPos_1860_ = lean_ctor_get(v_recursorInfo_1835_, 5);
lean_inc(v_paramsPos_1860_);
lean_dec_ref(v_recursorInfo_1835_);
v___x_1861_ = lean_array_mk(v_us_1856_);
v___x_1862_ = 0;
v___x_1882_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__1));
lean_inc(v_mvarId_1838_);
lean_inc(v_tacticName_1837_);
lean_inc(v_a_1836_);
v___x_1883_ = l_List_foldlM___at___00Lean_Meta_mkRecursorAppPrefix_spec__0(v_a_1836_, v___x_1861_, v_tacticName_1837_, v_mvarId_1838_, v___x_1882_, v_univLevelPos_1858_, v___y_1845_, v___y_1846_, v___y_1847_, v___y_1848_);
lean_dec(v_univLevelPos_1858_);
lean_dec_ref(v___x_1861_);
if (lean_obj_tag(v___x_1883_) == 0)
{
lean_object* v_a_1884_; lean_object* v_fst_1885_; lean_object* v_snd_1886_; lean_object* v___x_1888_; uint8_t v_isShared_1889_; uint8_t v_isSharedCheck_1930_; 
v_a_1884_ = lean_ctor_get(v___x_1883_, 0);
lean_inc(v_a_1884_);
lean_dec_ref_known(v___x_1883_, 1);
v_fst_1885_ = lean_ctor_get(v_a_1884_, 0);
v_snd_1886_ = lean_ctor_get(v_a_1884_, 1);
v_isSharedCheck_1930_ = !lean_is_exclusive(v_a_1884_);
if (v_isSharedCheck_1930_ == 0)
{
v___x_1888_ = v_a_1884_;
v_isShared_1889_ = v_isSharedCheck_1930_;
goto v_resetjp_1887_;
}
else
{
lean_inc(v_snd_1886_);
lean_inc(v_fst_1885_);
lean_dec(v_a_1884_);
v___x_1888_ = lean_box(0);
v_isShared_1889_ = v_isSharedCheck_1930_;
goto v_resetjp_1887_;
}
v_resetjp_1887_:
{
lean_object* v___y_1891_; lean_object* v___y_1892_; lean_object* v___y_1893_; lean_object* v___y_1894_; uint8_t v___x_1910_; 
v___x_1910_ = lean_unbox(v_snd_1886_);
lean_dec(v_snd_1886_);
if (v___x_1910_ == 0)
{
uint8_t v___x_1911_; 
v___x_1911_ = l_Lean_Level_isZero(v_a_1836_);
lean_dec(v_a_1836_);
if (v___x_1911_ == 0)
{
lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1916_; 
lean_dec(v_fst_1885_);
lean_dec(v_paramsPos_1860_);
lean_dec_ref(v_x_1843_);
lean_dec_ref(v_major_1841_);
lean_dec_ref(v_a_1840_);
v___x_1912_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__6));
v___x_1913_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__8, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__8_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__8);
v___x_1914_ = l_Lean_MessageData_ofName(v_recursorName_1857_);
if (v_isShared_1889_ == 0)
{
lean_ctor_set_tag(v___x_1888_, 7);
lean_ctor_set(v___x_1888_, 1, v___x_1914_);
lean_ctor_set(v___x_1888_, 0, v___x_1913_);
v___x_1916_ = v___x_1888_;
goto v_reusejp_1915_;
}
else
{
lean_object* v_reuseFailAlloc_1929_; 
v_reuseFailAlloc_1929_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1929_, 0, v___x_1913_);
lean_ctor_set(v_reuseFailAlloc_1929_, 1, v___x_1914_);
v___x_1916_ = v_reuseFailAlloc_1929_;
goto v_reusejp_1915_;
}
v_reusejp_1915_:
{
lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v_a_1921_; lean_object* v___x_1923_; uint8_t v_isShared_1924_; uint8_t v_isSharedCheck_1928_; 
v___x_1917_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__10, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__10_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__10);
v___x_1918_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1918_, 0, v___x_1916_);
lean_ctor_set(v___x_1918_, 1, v___x_1917_);
v___x_1919_ = l_Lean_Meta_mkTacticExMsg(v_tacticName_1837_, v_mvarId_1838_, v___x_1918_);
v___x_1920_ = l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1___redArg(v___x_1912_, v___x_1919_, v___y_1845_, v___y_1846_, v___y_1847_, v___y_1848_);
v_a_1921_ = lean_ctor_get(v___x_1920_, 0);
v_isSharedCheck_1928_ = !lean_is_exclusive(v___x_1920_);
if (v_isSharedCheck_1928_ == 0)
{
v___x_1923_ = v___x_1920_;
v_isShared_1924_ = v_isSharedCheck_1928_;
goto v_resetjp_1922_;
}
else
{
lean_inc(v_a_1921_);
lean_dec(v___x_1920_);
v___x_1923_ = lean_box(0);
v_isShared_1924_ = v_isSharedCheck_1928_;
goto v_resetjp_1922_;
}
v_resetjp_1922_:
{
lean_object* v___x_1926_; 
if (v_isShared_1924_ == 0)
{
v___x_1926_ = v___x_1923_;
goto v_reusejp_1925_;
}
else
{
lean_object* v_reuseFailAlloc_1927_; 
v_reuseFailAlloc_1927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1927_, 0, v_a_1921_);
v___x_1926_ = v_reuseFailAlloc_1927_;
goto v_reusejp_1925_;
}
v_reusejp_1925_:
{
return v___x_1926_;
}
}
}
}
else
{
lean_del_object(v___x_1888_);
lean_dec(v_tacticName_1837_);
v___y_1891_ = v___y_1845_;
v___y_1892_ = v___y_1846_;
v___y_1893_ = v___y_1847_;
v___y_1894_ = v___y_1848_;
goto v___jp_1890_;
}
}
else
{
lean_del_object(v___x_1888_);
lean_dec(v_tacticName_1837_);
lean_dec(v_a_1836_);
v___y_1891_ = v___y_1845_;
v___y_1892_ = v___y_1846_;
v___y_1893_ = v___y_1847_;
v___y_1894_ = v___y_1848_;
goto v___jp_1890_;
}
v___jp_1890_:
{
lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; 
v___x_1895_ = lean_array_to_list(v_fst_1885_);
v___x_1896_ = l_Lean_mkConst(v_recursorName_1857_, v___x_1895_);
v___x_1897_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams(v_mvarId_1838_, v_x_1843_, v_paramsPos_1860_, v___x_1896_, v___y_1891_, v___y_1892_, v___y_1893_, v___y_1894_);
lean_dec_ref(v_x_1843_);
if (lean_obj_tag(v___x_1897_) == 0)
{
if (v_depElim_1859_ == 0)
{
lean_object* v_a_1898_; 
lean_dec_ref(v_major_1841_);
v_a_1898_ = lean_ctor_get(v___x_1897_, 0);
lean_inc(v_a_1898_);
lean_dec_ref_known(v___x_1897_, 1);
v___y_1864_ = v_a_1898_;
v_motive_1865_ = v_a_1840_;
v___y_1866_ = v___y_1891_;
v___y_1867_ = v___y_1892_;
v___y_1868_ = v___y_1893_;
v___y_1869_ = v___y_1894_;
goto v___jp_1863_;
}
else
{
lean_object* v_a_1899_; lean_object* v___x_1900_; 
v_a_1899_ = lean_ctor_get(v___x_1897_, 0);
lean_inc(v_a_1899_);
lean_dec_ref_known(v___x_1897_, 1);
lean_inc(v___y_1894_);
lean_inc_ref(v___y_1893_);
lean_inc(v___y_1892_);
lean_inc_ref(v___y_1891_);
lean_inc_ref(v_major_1841_);
v___x_1900_ = lean_infer_type(v_major_1841_, v___y_1891_, v___y_1892_, v___y_1893_, v___y_1894_);
if (lean_obj_tag(v___x_1900_) == 0)
{
lean_object* v_a_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; 
v_a_1901_ = lean_ctor_get(v___x_1900_, 0);
lean_inc(v_a_1901_);
lean_dec_ref_known(v___x_1900_, 1);
v___x_1902_ = lean_unsigned_to_nat(1u);
v___x_1903_ = lean_mk_empty_array_with_capacity(v___x_1902_);
v___x_1904_ = lean_array_push(v___x_1903_, v_major_1841_);
v___x_1905_ = l_Lean_Expr_abstractM(v_a_1840_, v___x_1904_, v___y_1891_, v___y_1892_, v___y_1893_, v___y_1894_);
lean_dec_ref(v___x_1904_);
if (lean_obj_tag(v___x_1905_) == 0)
{
lean_object* v_a_1906_; lean_object* v___x_1907_; uint8_t v___x_1908_; lean_object* v___x_1909_; 
v_a_1906_ = lean_ctor_get(v___x_1905_, 0);
lean_inc(v_a_1906_);
lean_dec_ref_known(v___x_1905_, 1);
v___x_1907_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__3));
v___x_1908_ = 0;
v___x_1909_ = l_Lean_mkLambda(v___x_1907_, v___x_1908_, v_a_1901_, v_a_1906_);
v___y_1864_ = v_a_1899_;
v_motive_1865_ = v___x_1909_;
v___y_1866_ = v___y_1891_;
v___y_1867_ = v___y_1892_;
v___y_1868_ = v___y_1893_;
v___y_1869_ = v___y_1894_;
goto v___jp_1863_;
}
else
{
lean_dec(v_a_1901_);
lean_dec(v_a_1899_);
return v___x_1905_;
}
}
else
{
lean_dec(v_a_1899_);
lean_dec_ref(v_major_1841_);
lean_dec_ref(v_a_1840_);
return v___x_1900_;
}
}
}
else
{
lean_dec_ref(v_major_1841_);
lean_dec_ref(v_a_1840_);
return v___x_1897_;
}
}
}
}
else
{
lean_object* v_a_1931_; lean_object* v___x_1933_; uint8_t v_isShared_1934_; uint8_t v_isSharedCheck_1938_; 
lean_dec(v_paramsPos_1860_);
lean_dec(v_recursorName_1857_);
lean_dec_ref(v_x_1843_);
lean_dec_ref(v_major_1841_);
lean_dec_ref(v_a_1840_);
lean_dec(v_mvarId_1838_);
lean_dec(v_tacticName_1837_);
lean_dec(v_a_1836_);
v_a_1931_ = lean_ctor_get(v___x_1883_, 0);
v_isSharedCheck_1938_ = !lean_is_exclusive(v___x_1883_);
if (v_isSharedCheck_1938_ == 0)
{
v___x_1933_ = v___x_1883_;
v_isShared_1934_ = v_isSharedCheck_1938_;
goto v_resetjp_1932_;
}
else
{
lean_inc(v_a_1931_);
lean_dec(v___x_1883_);
v___x_1933_ = lean_box(0);
v_isShared_1934_ = v_isSharedCheck_1938_;
goto v_resetjp_1932_;
}
v_resetjp_1932_:
{
lean_object* v___x_1936_; 
if (v_isShared_1934_ == 0)
{
v___x_1936_ = v___x_1933_;
goto v_reusejp_1935_;
}
else
{
lean_object* v_reuseFailAlloc_1937_; 
v_reuseFailAlloc_1937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1937_, 0, v_a_1931_);
v___x_1936_ = v_reuseFailAlloc_1937_;
goto v_reusejp_1935_;
}
v_reusejp_1935_:
{
return v___x_1936_;
}
}
}
v___jp_1863_:
{
uint8_t v___x_1870_; uint8_t v___x_1871_; lean_object* v___x_1872_; 
v___x_1870_ = 1;
v___x_1871_ = 1;
v___x_1872_ = l_Lean_Meta_mkLambdaFVars(v_indices_1839_, v_motive_1865_, v___x_1862_, v___x_1870_, v___x_1862_, v___x_1870_, v___x_1871_, v___y_1866_, v___y_1867_, v___y_1868_, v___y_1869_);
if (lean_obj_tag(v___x_1872_) == 0)
{
lean_object* v_a_1873_; lean_object* v___x_1875_; uint8_t v_isShared_1876_; uint8_t v_isSharedCheck_1881_; 
v_a_1873_ = lean_ctor_get(v___x_1872_, 0);
v_isSharedCheck_1881_ = !lean_is_exclusive(v___x_1872_);
if (v_isSharedCheck_1881_ == 0)
{
v___x_1875_ = v___x_1872_;
v_isShared_1876_ = v_isSharedCheck_1881_;
goto v_resetjp_1874_;
}
else
{
lean_inc(v_a_1873_);
lean_dec(v___x_1872_);
v___x_1875_ = lean_box(0);
v_isShared_1876_ = v_isSharedCheck_1881_;
goto v_resetjp_1874_;
}
v_resetjp_1874_:
{
lean_object* v___x_1877_; lean_object* v___x_1879_; 
v___x_1877_ = l_Lean_Expr_app___override(v___y_1864_, v_a_1873_);
if (v_isShared_1876_ == 0)
{
lean_ctor_set(v___x_1875_, 0, v___x_1877_);
v___x_1879_ = v___x_1875_;
goto v_reusejp_1878_;
}
else
{
lean_object* v_reuseFailAlloc_1880_; 
v_reuseFailAlloc_1880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1880_, 0, v___x_1877_);
v___x_1879_ = v_reuseFailAlloc_1880_;
goto v_reusejp_1878_;
}
v_reusejp_1878_:
{
return v___x_1879_;
}
}
}
else
{
lean_dec_ref(v___y_1864_);
return v___x_1872_;
}
}
}
else
{
lean_object* v___x_1939_; lean_object* v___x_1940_; 
lean_dec_ref(v_x_1843_);
lean_dec_ref(v_x_1842_);
lean_dec_ref(v_major_1841_);
lean_dec_ref(v_a_1840_);
lean_dec(v_a_1836_);
lean_dec_ref(v_recursorInfo_1835_);
v___x_1939_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__14, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__14_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__14);
v___x_1940_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1837_, v_mvarId_1838_, v___x_1939_, v___y_1845_, v___y_1846_, v___y_1847_, v___y_1848_);
return v___x_1940_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___boxed(lean_object* v_recursorInfo_1941_, lean_object* v_a_1942_, lean_object* v_tacticName_1943_, lean_object* v_mvarId_1944_, lean_object* v_indices_1945_, lean_object* v_a_1946_, lean_object* v_major_1947_, lean_object* v_x_1948_, lean_object* v_x_1949_, lean_object* v_x_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_){
_start:
{
lean_object* v_res_1956_; 
v_res_1956_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2(v_recursorInfo_1941_, v_a_1942_, v_tacticName_1943_, v_mvarId_1944_, v_indices_1945_, v_a_1946_, v_major_1947_, v_x_1948_, v_x_1949_, v_x_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_);
lean_dec(v___y_1954_);
lean_dec_ref(v___y_1953_);
lean_dec(v___y_1952_);
lean_dec_ref(v___y_1951_);
lean_dec_ref(v_indices_1945_);
return v_res_1956_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2(lean_object* v_a_1957_, lean_object* v_tacticName_1958_, lean_object* v_mvarId_1959_, lean_object* v_recursorInfo_1960_, lean_object* v_indices_1961_, lean_object* v_a_1962_, lean_object* v_major_1963_, lean_object* v_x_1964_, lean_object* v_x_1965_, lean_object* v_x_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_){
_start:
{
if (lean_obj_tag(v_x_1964_) == 5)
{
lean_object* v_fn_1972_; lean_object* v_arg_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; 
v_fn_1972_ = lean_ctor_get(v_x_1964_, 0);
lean_inc_ref(v_fn_1972_);
v_arg_1973_ = lean_ctor_get(v_x_1964_, 1);
lean_inc_ref(v_arg_1973_);
lean_dec_ref_known(v_x_1964_, 2);
v___x_1974_ = lean_array_set(v_x_1965_, v_x_1966_, v_arg_1973_);
v___x_1975_ = lean_unsigned_to_nat(1u);
v___x_1976_ = lean_nat_sub(v_x_1966_, v___x_1975_);
v___x_1977_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2(v_recursorInfo_1960_, v_a_1957_, v_tacticName_1958_, v_mvarId_1959_, v_indices_1961_, v_a_1962_, v_major_1963_, v_fn_1972_, v___x_1974_, v___x_1976_, v___y_1967_, v___y_1968_, v___y_1969_, v___y_1970_);
return v___x_1977_;
}
else
{
if (lean_obj_tag(v_x_1964_) == 4)
{
lean_object* v_us_1978_; lean_object* v_recursorName_1979_; lean_object* v_univLevelPos_1980_; uint8_t v_depElim_1981_; lean_object* v_paramsPos_1982_; lean_object* v___x_1983_; uint8_t v___x_1984_; lean_object* v___y_1986_; lean_object* v_motive_1987_; lean_object* v___y_1988_; lean_object* v___y_1989_; lean_object* v___y_1990_; lean_object* v___y_1991_; lean_object* v___x_2004_; lean_object* v___x_2005_; 
v_us_1978_ = lean_ctor_get(v_x_1964_, 1);
lean_inc(v_us_1978_);
lean_dec_ref_known(v_x_1964_, 2);
v_recursorName_1979_ = lean_ctor_get(v_recursorInfo_1960_, 0);
lean_inc(v_recursorName_1979_);
v_univLevelPos_1980_ = lean_ctor_get(v_recursorInfo_1960_, 2);
lean_inc(v_univLevelPos_1980_);
v_depElim_1981_ = lean_ctor_get_uint8(v_recursorInfo_1960_, sizeof(void*)*8);
v_paramsPos_1982_ = lean_ctor_get(v_recursorInfo_1960_, 5);
lean_inc(v_paramsPos_1982_);
lean_dec_ref(v_recursorInfo_1960_);
v___x_1983_ = lean_array_mk(v_us_1978_);
v___x_1984_ = 0;
v___x_2004_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__1));
lean_inc(v_mvarId_1959_);
lean_inc(v_tacticName_1958_);
lean_inc(v_a_1957_);
v___x_2005_ = l_List_foldlM___at___00Lean_Meta_mkRecursorAppPrefix_spec__0(v_a_1957_, v___x_1983_, v_tacticName_1958_, v_mvarId_1959_, v___x_2004_, v_univLevelPos_1980_, v___y_1967_, v___y_1968_, v___y_1969_, v___y_1970_);
lean_dec(v_univLevelPos_1980_);
lean_dec_ref(v___x_1983_);
if (lean_obj_tag(v___x_2005_) == 0)
{
lean_object* v_a_2006_; lean_object* v_fst_2007_; lean_object* v_snd_2008_; lean_object* v___x_2010_; uint8_t v_isShared_2011_; uint8_t v_isSharedCheck_2052_; 
v_a_2006_ = lean_ctor_get(v___x_2005_, 0);
lean_inc(v_a_2006_);
lean_dec_ref_known(v___x_2005_, 1);
v_fst_2007_ = lean_ctor_get(v_a_2006_, 0);
v_snd_2008_ = lean_ctor_get(v_a_2006_, 1);
v_isSharedCheck_2052_ = !lean_is_exclusive(v_a_2006_);
if (v_isSharedCheck_2052_ == 0)
{
v___x_2010_ = v_a_2006_;
v_isShared_2011_ = v_isSharedCheck_2052_;
goto v_resetjp_2009_;
}
else
{
lean_inc(v_snd_2008_);
lean_inc(v_fst_2007_);
lean_dec(v_a_2006_);
v___x_2010_ = lean_box(0);
v_isShared_2011_ = v_isSharedCheck_2052_;
goto v_resetjp_2009_;
}
v_resetjp_2009_:
{
lean_object* v___y_2013_; lean_object* v___y_2014_; lean_object* v___y_2015_; lean_object* v___y_2016_; uint8_t v___x_2032_; 
v___x_2032_ = lean_unbox(v_snd_2008_);
lean_dec(v_snd_2008_);
if (v___x_2032_ == 0)
{
uint8_t v___x_2033_; 
v___x_2033_ = l_Lean_Level_isZero(v_a_1957_);
lean_dec(v_a_1957_);
if (v___x_2033_ == 0)
{
lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2038_; 
lean_dec(v_fst_2007_);
lean_dec(v_paramsPos_1982_);
lean_dec_ref(v_x_1965_);
lean_dec_ref(v_major_1963_);
lean_dec_ref(v_a_1962_);
v___x_2034_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__6));
v___x_2035_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__8, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__8_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__8);
v___x_2036_ = l_Lean_MessageData_ofName(v_recursorName_1979_);
if (v_isShared_2011_ == 0)
{
lean_ctor_set_tag(v___x_2010_, 7);
lean_ctor_set(v___x_2010_, 1, v___x_2036_);
lean_ctor_set(v___x_2010_, 0, v___x_2035_);
v___x_2038_ = v___x_2010_;
goto v_reusejp_2037_;
}
else
{
lean_object* v_reuseFailAlloc_2051_; 
v_reuseFailAlloc_2051_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2051_, 0, v___x_2035_);
lean_ctor_set(v_reuseFailAlloc_2051_, 1, v___x_2036_);
v___x_2038_ = v_reuseFailAlloc_2051_;
goto v_reusejp_2037_;
}
v_reusejp_2037_:
{
lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v_a_2043_; lean_object* v___x_2045_; uint8_t v_isShared_2046_; uint8_t v_isSharedCheck_2050_; 
v___x_2039_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__10, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__10_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__10);
v___x_2040_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2040_, 0, v___x_2038_);
lean_ctor_set(v___x_2040_, 1, v___x_2039_);
v___x_2041_ = l_Lean_Meta_mkTacticExMsg(v_tacticName_1958_, v_mvarId_1959_, v___x_2040_);
v___x_2042_ = l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1___redArg(v___x_2034_, v___x_2041_, v___y_1967_, v___y_1968_, v___y_1969_, v___y_1970_);
v_a_2043_ = lean_ctor_get(v___x_2042_, 0);
v_isSharedCheck_2050_ = !lean_is_exclusive(v___x_2042_);
if (v_isSharedCheck_2050_ == 0)
{
v___x_2045_ = v___x_2042_;
v_isShared_2046_ = v_isSharedCheck_2050_;
goto v_resetjp_2044_;
}
else
{
lean_inc(v_a_2043_);
lean_dec(v___x_2042_);
v___x_2045_ = lean_box(0);
v_isShared_2046_ = v_isSharedCheck_2050_;
goto v_resetjp_2044_;
}
v_resetjp_2044_:
{
lean_object* v___x_2048_; 
if (v_isShared_2046_ == 0)
{
v___x_2048_ = v___x_2045_;
goto v_reusejp_2047_;
}
else
{
lean_object* v_reuseFailAlloc_2049_; 
v_reuseFailAlloc_2049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2049_, 0, v_a_2043_);
v___x_2048_ = v_reuseFailAlloc_2049_;
goto v_reusejp_2047_;
}
v_reusejp_2047_:
{
return v___x_2048_;
}
}
}
}
else
{
lean_del_object(v___x_2010_);
lean_dec(v_tacticName_1958_);
v___y_2013_ = v___y_1967_;
v___y_2014_ = v___y_1968_;
v___y_2015_ = v___y_1969_;
v___y_2016_ = v___y_1970_;
goto v___jp_2012_;
}
}
else
{
lean_del_object(v___x_2010_);
lean_dec(v_tacticName_1958_);
lean_dec(v_a_1957_);
v___y_2013_ = v___y_1967_;
v___y_2014_ = v___y_1968_;
v___y_2015_ = v___y_1969_;
v___y_2016_ = v___y_1970_;
goto v___jp_2012_;
}
v___jp_2012_:
{
lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; 
v___x_2017_ = lean_array_to_list(v_fst_2007_);
v___x_2018_ = l_Lean_mkConst(v_recursorName_1979_, v___x_2017_);
v___x_2019_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams(v_mvarId_1959_, v_x_1965_, v_paramsPos_1982_, v___x_2018_, v___y_2013_, v___y_2014_, v___y_2015_, v___y_2016_);
lean_dec_ref(v_x_1965_);
if (lean_obj_tag(v___x_2019_) == 0)
{
if (v_depElim_1981_ == 0)
{
lean_object* v_a_2020_; 
lean_dec_ref(v_major_1963_);
v_a_2020_ = lean_ctor_get(v___x_2019_, 0);
lean_inc(v_a_2020_);
lean_dec_ref_known(v___x_2019_, 1);
v___y_1986_ = v_a_2020_;
v_motive_1987_ = v_a_1962_;
v___y_1988_ = v___y_2013_;
v___y_1989_ = v___y_2014_;
v___y_1990_ = v___y_2015_;
v___y_1991_ = v___y_2016_;
goto v___jp_1985_;
}
else
{
lean_object* v_a_2021_; lean_object* v___x_2022_; 
v_a_2021_ = lean_ctor_get(v___x_2019_, 0);
lean_inc(v_a_2021_);
lean_dec_ref_known(v___x_2019_, 1);
lean_inc(v___y_2016_);
lean_inc_ref(v___y_2015_);
lean_inc(v___y_2014_);
lean_inc_ref(v___y_2013_);
lean_inc_ref(v_major_1963_);
v___x_2022_ = lean_infer_type(v_major_1963_, v___y_2013_, v___y_2014_, v___y_2015_, v___y_2016_);
if (lean_obj_tag(v___x_2022_) == 0)
{
lean_object* v_a_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; 
v_a_2023_ = lean_ctor_get(v___x_2022_, 0);
lean_inc(v_a_2023_);
lean_dec_ref_known(v___x_2022_, 1);
v___x_2024_ = lean_unsigned_to_nat(1u);
v___x_2025_ = lean_mk_empty_array_with_capacity(v___x_2024_);
v___x_2026_ = lean_array_push(v___x_2025_, v_major_1963_);
v___x_2027_ = l_Lean_Expr_abstractM(v_a_1962_, v___x_2026_, v___y_2013_, v___y_2014_, v___y_2015_, v___y_2016_);
lean_dec_ref(v___x_2026_);
if (lean_obj_tag(v___x_2027_) == 0)
{
lean_object* v_a_2028_; lean_object* v___x_2029_; uint8_t v___x_2030_; lean_object* v___x_2031_; 
v_a_2028_ = lean_ctor_get(v___x_2027_, 0);
lean_inc(v_a_2028_);
lean_dec_ref_known(v___x_2027_, 1);
v___x_2029_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__3));
v___x_2030_ = 0;
v___x_2031_ = l_Lean_mkLambda(v___x_2029_, v___x_2030_, v_a_2023_, v_a_2028_);
v___y_1986_ = v_a_2021_;
v_motive_1987_ = v___x_2031_;
v___y_1988_ = v___y_2013_;
v___y_1989_ = v___y_2014_;
v___y_1990_ = v___y_2015_;
v___y_1991_ = v___y_2016_;
goto v___jp_1985_;
}
else
{
lean_dec(v_a_2023_);
lean_dec(v_a_2021_);
return v___x_2027_;
}
}
else
{
lean_dec(v_a_2021_);
lean_dec_ref(v_major_1963_);
lean_dec_ref(v_a_1962_);
return v___x_2022_;
}
}
}
else
{
lean_dec_ref(v_major_1963_);
lean_dec_ref(v_a_1962_);
return v___x_2019_;
}
}
}
}
else
{
lean_object* v_a_2053_; lean_object* v___x_2055_; uint8_t v_isShared_2056_; uint8_t v_isSharedCheck_2060_; 
lean_dec(v_paramsPos_1982_);
lean_dec(v_recursorName_1979_);
lean_dec_ref(v_x_1965_);
lean_dec_ref(v_major_1963_);
lean_dec_ref(v_a_1962_);
lean_dec(v_mvarId_1959_);
lean_dec(v_tacticName_1958_);
lean_dec(v_a_1957_);
v_a_2053_ = lean_ctor_get(v___x_2005_, 0);
v_isSharedCheck_2060_ = !lean_is_exclusive(v___x_2005_);
if (v_isSharedCheck_2060_ == 0)
{
v___x_2055_ = v___x_2005_;
v_isShared_2056_ = v_isSharedCheck_2060_;
goto v_resetjp_2054_;
}
else
{
lean_inc(v_a_2053_);
lean_dec(v___x_2005_);
v___x_2055_ = lean_box(0);
v_isShared_2056_ = v_isSharedCheck_2060_;
goto v_resetjp_2054_;
}
v_resetjp_2054_:
{
lean_object* v___x_2058_; 
if (v_isShared_2056_ == 0)
{
v___x_2058_ = v___x_2055_;
goto v_reusejp_2057_;
}
else
{
lean_object* v_reuseFailAlloc_2059_; 
v_reuseFailAlloc_2059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2059_, 0, v_a_2053_);
v___x_2058_ = v_reuseFailAlloc_2059_;
goto v_reusejp_2057_;
}
v_reusejp_2057_:
{
return v___x_2058_;
}
}
}
v___jp_1985_:
{
uint8_t v___x_1992_; uint8_t v___x_1993_; lean_object* v___x_1994_; 
v___x_1992_ = 1;
v___x_1993_ = 1;
v___x_1994_ = l_Lean_Meta_mkLambdaFVars(v_indices_1961_, v_motive_1987_, v___x_1984_, v___x_1992_, v___x_1984_, v___x_1992_, v___x_1993_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_);
if (lean_obj_tag(v___x_1994_) == 0)
{
lean_object* v_a_1995_; lean_object* v___x_1997_; uint8_t v_isShared_1998_; uint8_t v_isSharedCheck_2003_; 
v_a_1995_ = lean_ctor_get(v___x_1994_, 0);
v_isSharedCheck_2003_ = !lean_is_exclusive(v___x_1994_);
if (v_isSharedCheck_2003_ == 0)
{
v___x_1997_ = v___x_1994_;
v_isShared_1998_ = v_isSharedCheck_2003_;
goto v_resetjp_1996_;
}
else
{
lean_inc(v_a_1995_);
lean_dec(v___x_1994_);
v___x_1997_ = lean_box(0);
v_isShared_1998_ = v_isSharedCheck_2003_;
goto v_resetjp_1996_;
}
v_resetjp_1996_:
{
lean_object* v___x_1999_; lean_object* v___x_2001_; 
v___x_1999_ = l_Lean_Expr_app___override(v___y_1986_, v_a_1995_);
if (v_isShared_1998_ == 0)
{
lean_ctor_set(v___x_1997_, 0, v___x_1999_);
v___x_2001_ = v___x_1997_;
goto v_reusejp_2000_;
}
else
{
lean_object* v_reuseFailAlloc_2002_; 
v_reuseFailAlloc_2002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2002_, 0, v___x_1999_);
v___x_2001_ = v_reuseFailAlloc_2002_;
goto v_reusejp_2000_;
}
v_reusejp_2000_:
{
return v___x_2001_;
}
}
}
else
{
lean_dec_ref(v___y_1986_);
return v___x_1994_;
}
}
}
else
{
lean_object* v___x_2061_; lean_object* v___x_2062_; 
lean_dec_ref(v_x_1965_);
lean_dec_ref(v_x_1964_);
lean_dec_ref(v_major_1963_);
lean_dec_ref(v_a_1962_);
lean_dec_ref(v_recursorInfo_1960_);
lean_dec(v_a_1957_);
v___x_2061_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__14, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__14_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__14);
v___x_2062_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1958_, v_mvarId_1959_, v___x_2061_, v___y_1967_, v___y_1968_, v___y_1969_, v___y_1970_);
return v___x_2062_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2___boxed(lean_object* v_a_2063_, lean_object* v_tacticName_2064_, lean_object* v_mvarId_2065_, lean_object* v_recursorInfo_2066_, lean_object* v_indices_2067_, lean_object* v_a_2068_, lean_object* v_major_2069_, lean_object* v_x_2070_, lean_object* v_x_2071_, lean_object* v_x_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_){
_start:
{
lean_object* v_res_2078_; 
v_res_2078_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2(v_a_2063_, v_tacticName_2064_, v_mvarId_2065_, v_recursorInfo_2066_, v_indices_2067_, v_a_2068_, v_major_2069_, v_x_2070_, v_x_2071_, v_x_2072_, v___y_2073_, v___y_2074_, v___y_2075_, v___y_2076_);
lean_dec(v___y_2076_);
lean_dec_ref(v___y_2075_);
lean_dec(v___y_2074_);
lean_dec_ref(v___y_2073_);
lean_dec(v_x_2072_);
lean_dec_ref(v_indices_2067_);
return v_res_2078_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkRecursorAppPrefix(lean_object* v_mvarId_2079_, lean_object* v_tacticName_2080_, lean_object* v_majorFVarId_2081_, lean_object* v_recursorInfo_2082_, lean_object* v_indices_2083_, lean_object* v_a_2084_, lean_object* v_a_2085_, lean_object* v_a_2086_, lean_object* v_a_2087_){
_start:
{
lean_object* v_major_2089_; lean_object* v___x_2090_; 
lean_inc(v_majorFVarId_2081_);
v_major_2089_ = l_Lean_mkFVar(v_majorFVarId_2081_);
lean_inc(v_mvarId_2079_);
v___x_2090_ = l_Lean_MVarId_getType(v_mvarId_2079_, v_a_2084_, v_a_2085_, v_a_2086_, v_a_2087_);
if (lean_obj_tag(v___x_2090_) == 0)
{
lean_object* v_a_2091_; lean_object* v___x_2092_; 
v_a_2091_ = lean_ctor_get(v___x_2090_, 0);
lean_inc_n(v_a_2091_, 2);
lean_dec_ref_known(v___x_2090_, 1);
v___x_2092_ = l_Lean_Meta_getLevel(v_a_2091_, v_a_2084_, v_a_2085_, v_a_2086_, v_a_2087_);
if (lean_obj_tag(v___x_2092_) == 0)
{
lean_object* v_a_2093_; lean_object* v___x_2094_; 
v_a_2093_ = lean_ctor_get(v___x_2092_, 0);
lean_inc(v_a_2093_);
lean_dec_ref_known(v___x_2092_, 1);
v___x_2094_ = l_Lean_Meta_normalizeLevel(v_a_2093_, v_a_2084_, v_a_2085_, v_a_2086_, v_a_2087_);
if (lean_obj_tag(v___x_2094_) == 0)
{
lean_object* v_a_2095_; lean_object* v___x_2096_; 
v_a_2095_ = lean_ctor_get(v___x_2094_, 0);
lean_inc(v_a_2095_);
lean_dec_ref_known(v___x_2094_, 1);
v___x_2096_ = l_Lean_FVarId_getDecl___redArg(v_majorFVarId_2081_, v_a_2084_, v_a_2086_, v_a_2087_);
if (lean_obj_tag(v___x_2096_) == 0)
{
lean_object* v_a_2097_; lean_object* v_typeName_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; 
v_a_2097_ = lean_ctor_get(v___x_2096_, 0);
lean_inc(v_a_2097_);
lean_dec_ref_known(v___x_2096_, 1);
v_typeName_2098_ = lean_ctor_get(v_recursorInfo_2082_, 1);
v___x_2099_ = l_Lean_LocalDecl_type(v_a_2097_);
lean_dec(v_a_2097_);
lean_inc_ref(v___x_2099_);
v___x_2100_ = l_Lean_Meta_whnfUntil(v___x_2099_, v_typeName_2098_, v_a_2084_, v_a_2085_, v_a_2086_, v_a_2087_);
if (lean_obj_tag(v___x_2100_) == 0)
{
lean_object* v_a_2101_; 
v_a_2101_ = lean_ctor_get(v___x_2100_, 0);
lean_inc(v_a_2101_);
lean_dec_ref_known(v___x_2100_, 1);
if (lean_obj_tag(v_a_2101_) == 1)
{
lean_object* v_val_2102_; lean_object* v_dummy_2103_; lean_object* v_nargs_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; 
lean_dec_ref(v___x_2099_);
v_val_2102_ = lean_ctor_get(v_a_2101_, 0);
lean_inc(v_val_2102_);
lean_dec_ref_known(v_a_2101_, 1);
v_dummy_2103_ = lean_obj_once(&l_Lean_Meta_getMajorTypeIndices___closed__0, &l_Lean_Meta_getMajorTypeIndices___closed__0_once, _init_l_Lean_Meta_getMajorTypeIndices___closed__0);
v_nargs_2104_ = l_Lean_Expr_getAppNumArgs(v_val_2102_);
lean_inc(v_nargs_2104_);
v___x_2105_ = lean_mk_array(v_nargs_2104_, v_dummy_2103_);
v___x_2106_ = lean_unsigned_to_nat(1u);
v___x_2107_ = lean_nat_sub(v_nargs_2104_, v___x_2106_);
lean_dec(v_nargs_2104_);
v___x_2108_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2(v_a_2095_, v_tacticName_2080_, v_mvarId_2079_, v_recursorInfo_2082_, v_indices_2083_, v_a_2091_, v_major_2089_, v_val_2102_, v___x_2105_, v___x_2107_, v_a_2084_, v_a_2085_, v_a_2086_, v_a_2087_);
lean_dec(v___x_2107_);
return v___x_2108_;
}
else
{
lean_object* v___x_2109_; 
lean_dec(v_a_2101_);
lean_dec(v_a_2095_);
lean_dec(v_a_2091_);
lean_dec_ref(v_major_2089_);
lean_dec_ref(v_recursorInfo_2082_);
v___x_2109_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg(v_tacticName_2080_, v_mvarId_2079_, v___x_2099_, v_a_2084_, v_a_2085_, v_a_2086_, v_a_2087_);
return v___x_2109_;
}
}
else
{
lean_object* v_a_2110_; lean_object* v___x_2112_; uint8_t v_isShared_2113_; uint8_t v_isSharedCheck_2117_; 
lean_dec_ref(v___x_2099_);
lean_dec(v_a_2095_);
lean_dec(v_a_2091_);
lean_dec_ref(v_major_2089_);
lean_dec_ref(v_recursorInfo_2082_);
lean_dec(v_tacticName_2080_);
lean_dec(v_mvarId_2079_);
v_a_2110_ = lean_ctor_get(v___x_2100_, 0);
v_isSharedCheck_2117_ = !lean_is_exclusive(v___x_2100_);
if (v_isSharedCheck_2117_ == 0)
{
v___x_2112_ = v___x_2100_;
v_isShared_2113_ = v_isSharedCheck_2117_;
goto v_resetjp_2111_;
}
else
{
lean_inc(v_a_2110_);
lean_dec(v___x_2100_);
v___x_2112_ = lean_box(0);
v_isShared_2113_ = v_isSharedCheck_2117_;
goto v_resetjp_2111_;
}
v_resetjp_2111_:
{
lean_object* v___x_2115_; 
if (v_isShared_2113_ == 0)
{
v___x_2115_ = v___x_2112_;
goto v_reusejp_2114_;
}
else
{
lean_object* v_reuseFailAlloc_2116_; 
v_reuseFailAlloc_2116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2116_, 0, v_a_2110_);
v___x_2115_ = v_reuseFailAlloc_2116_;
goto v_reusejp_2114_;
}
v_reusejp_2114_:
{
return v___x_2115_;
}
}
}
}
else
{
lean_object* v_a_2118_; lean_object* v___x_2120_; uint8_t v_isShared_2121_; uint8_t v_isSharedCheck_2125_; 
lean_dec(v_a_2095_);
lean_dec(v_a_2091_);
lean_dec_ref(v_major_2089_);
lean_dec_ref(v_recursorInfo_2082_);
lean_dec(v_tacticName_2080_);
lean_dec(v_mvarId_2079_);
v_a_2118_ = lean_ctor_get(v___x_2096_, 0);
v_isSharedCheck_2125_ = !lean_is_exclusive(v___x_2096_);
if (v_isSharedCheck_2125_ == 0)
{
v___x_2120_ = v___x_2096_;
v_isShared_2121_ = v_isSharedCheck_2125_;
goto v_resetjp_2119_;
}
else
{
lean_inc(v_a_2118_);
lean_dec(v___x_2096_);
v___x_2120_ = lean_box(0);
v_isShared_2121_ = v_isSharedCheck_2125_;
goto v_resetjp_2119_;
}
v_resetjp_2119_:
{
lean_object* v___x_2123_; 
if (v_isShared_2121_ == 0)
{
v___x_2123_ = v___x_2120_;
goto v_reusejp_2122_;
}
else
{
lean_object* v_reuseFailAlloc_2124_; 
v_reuseFailAlloc_2124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2124_, 0, v_a_2118_);
v___x_2123_ = v_reuseFailAlloc_2124_;
goto v_reusejp_2122_;
}
v_reusejp_2122_:
{
return v___x_2123_;
}
}
}
}
else
{
lean_object* v_a_2126_; lean_object* v___x_2128_; uint8_t v_isShared_2129_; uint8_t v_isSharedCheck_2133_; 
lean_dec(v_a_2091_);
lean_dec_ref(v_major_2089_);
lean_dec_ref(v_recursorInfo_2082_);
lean_dec(v_majorFVarId_2081_);
lean_dec(v_tacticName_2080_);
lean_dec(v_mvarId_2079_);
v_a_2126_ = lean_ctor_get(v___x_2094_, 0);
v_isSharedCheck_2133_ = !lean_is_exclusive(v___x_2094_);
if (v_isSharedCheck_2133_ == 0)
{
v___x_2128_ = v___x_2094_;
v_isShared_2129_ = v_isSharedCheck_2133_;
goto v_resetjp_2127_;
}
else
{
lean_inc(v_a_2126_);
lean_dec(v___x_2094_);
v___x_2128_ = lean_box(0);
v_isShared_2129_ = v_isSharedCheck_2133_;
goto v_resetjp_2127_;
}
v_resetjp_2127_:
{
lean_object* v___x_2131_; 
if (v_isShared_2129_ == 0)
{
v___x_2131_ = v___x_2128_;
goto v_reusejp_2130_;
}
else
{
lean_object* v_reuseFailAlloc_2132_; 
v_reuseFailAlloc_2132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2132_, 0, v_a_2126_);
v___x_2131_ = v_reuseFailAlloc_2132_;
goto v_reusejp_2130_;
}
v_reusejp_2130_:
{
return v___x_2131_;
}
}
}
}
else
{
lean_object* v_a_2134_; lean_object* v___x_2136_; uint8_t v_isShared_2137_; uint8_t v_isSharedCheck_2141_; 
lean_dec(v_a_2091_);
lean_dec_ref(v_major_2089_);
lean_dec_ref(v_recursorInfo_2082_);
lean_dec(v_majorFVarId_2081_);
lean_dec(v_tacticName_2080_);
lean_dec(v_mvarId_2079_);
v_a_2134_ = lean_ctor_get(v___x_2092_, 0);
v_isSharedCheck_2141_ = !lean_is_exclusive(v___x_2092_);
if (v_isSharedCheck_2141_ == 0)
{
v___x_2136_ = v___x_2092_;
v_isShared_2137_ = v_isSharedCheck_2141_;
goto v_resetjp_2135_;
}
else
{
lean_inc(v_a_2134_);
lean_dec(v___x_2092_);
v___x_2136_ = lean_box(0);
v_isShared_2137_ = v_isSharedCheck_2141_;
goto v_resetjp_2135_;
}
v_resetjp_2135_:
{
lean_object* v___x_2139_; 
if (v_isShared_2137_ == 0)
{
v___x_2139_ = v___x_2136_;
goto v_reusejp_2138_;
}
else
{
lean_object* v_reuseFailAlloc_2140_; 
v_reuseFailAlloc_2140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2140_, 0, v_a_2134_);
v___x_2139_ = v_reuseFailAlloc_2140_;
goto v_reusejp_2138_;
}
v_reusejp_2138_:
{
return v___x_2139_;
}
}
}
}
else
{
lean_dec_ref(v_major_2089_);
lean_dec_ref(v_recursorInfo_2082_);
lean_dec(v_majorFVarId_2081_);
lean_dec(v_tacticName_2080_);
lean_dec(v_mvarId_2079_);
return v___x_2090_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkRecursorAppPrefix___boxed(lean_object* v_mvarId_2142_, lean_object* v_tacticName_2143_, lean_object* v_majorFVarId_2144_, lean_object* v_recursorInfo_2145_, lean_object* v_indices_2146_, lean_object* v_a_2147_, lean_object* v_a_2148_, lean_object* v_a_2149_, lean_object* v_a_2150_, lean_object* v_a_2151_){
_start:
{
lean_object* v_res_2152_; 
v_res_2152_ = l_Lean_Meta_mkRecursorAppPrefix(v_mvarId_2142_, v_tacticName_2143_, v_majorFVarId_2144_, v_recursorInfo_2145_, v_indices_2146_, v_a_2147_, v_a_2148_, v_a_2149_, v_a_2150_);
lean_dec(v_a_2150_);
lean_dec_ref(v_a_2149_);
lean_dec(v_a_2148_);
lean_dec_ref(v_a_2147_);
lean_dec_ref(v_indices_2146_);
return v_res_2152_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1(lean_object* v_00_u03b1_2153_, lean_object* v_name_2154_, lean_object* v_msg_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_){
_start:
{
lean_object* v___x_2161_; 
v___x_2161_ = l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1___redArg(v_name_2154_, v_msg_2155_, v___y_2156_, v___y_2157_, v___y_2158_, v___y_2159_);
return v___x_2161_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1___boxed(lean_object* v_00_u03b1_2162_, lean_object* v_name_2163_, lean_object* v_msg_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_){
_start:
{
lean_object* v_res_2170_; 
v_res_2170_ = l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1(v_00_u03b1_2162_, v_name_2163_, v_msg_2164_, v___y_2165_, v___y_2166_, v___y_2167_, v___y_2168_);
lean_dec(v___y_2168_);
lean_dec_ref(v___y_2167_);
lean_dec(v___y_2166_);
lean_dec_ref(v___y_2165_);
return v_res_2170_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___redArg(lean_object* v_mvarId_2171_, lean_object* v_x_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_){
_start:
{
lean_object* v___x_2178_; 
v___x_2178_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_2171_, v_x_2172_, v___y_2173_, v___y_2174_, v___y_2175_, v___y_2176_);
if (lean_obj_tag(v___x_2178_) == 0)
{
lean_object* v_a_2179_; lean_object* v___x_2181_; uint8_t v_isShared_2182_; uint8_t v_isSharedCheck_2186_; 
v_a_2179_ = lean_ctor_get(v___x_2178_, 0);
v_isSharedCheck_2186_ = !lean_is_exclusive(v___x_2178_);
if (v_isSharedCheck_2186_ == 0)
{
v___x_2181_ = v___x_2178_;
v_isShared_2182_ = v_isSharedCheck_2186_;
goto v_resetjp_2180_;
}
else
{
lean_inc(v_a_2179_);
lean_dec(v___x_2178_);
v___x_2181_ = lean_box(0);
v_isShared_2182_ = v_isSharedCheck_2186_;
goto v_resetjp_2180_;
}
v_resetjp_2180_:
{
lean_object* v___x_2184_; 
if (v_isShared_2182_ == 0)
{
v___x_2184_ = v___x_2181_;
goto v_reusejp_2183_;
}
else
{
lean_object* v_reuseFailAlloc_2185_; 
v_reuseFailAlloc_2185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2185_, 0, v_a_2179_);
v___x_2184_ = v_reuseFailAlloc_2185_;
goto v_reusejp_2183_;
}
v_reusejp_2183_:
{
return v___x_2184_;
}
}
}
else
{
lean_object* v_a_2187_; lean_object* v___x_2189_; uint8_t v_isShared_2190_; uint8_t v_isSharedCheck_2194_; 
v_a_2187_ = lean_ctor_get(v___x_2178_, 0);
v_isSharedCheck_2194_ = !lean_is_exclusive(v___x_2178_);
if (v_isSharedCheck_2194_ == 0)
{
v___x_2189_ = v___x_2178_;
v_isShared_2190_ = v_isSharedCheck_2194_;
goto v_resetjp_2188_;
}
else
{
lean_inc(v_a_2187_);
lean_dec(v___x_2178_);
v___x_2189_ = lean_box(0);
v_isShared_2190_ = v_isSharedCheck_2194_;
goto v_resetjp_2188_;
}
v_resetjp_2188_:
{
lean_object* v___x_2192_; 
if (v_isShared_2190_ == 0)
{
v___x_2192_ = v___x_2189_;
goto v_reusejp_2191_;
}
else
{
lean_object* v_reuseFailAlloc_2193_; 
v_reuseFailAlloc_2193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2193_, 0, v_a_2187_);
v___x_2192_ = v_reuseFailAlloc_2193_;
goto v_reusejp_2191_;
}
v_reusejp_2191_:
{
return v___x_2192_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___redArg___boxed(lean_object* v_mvarId_2195_, lean_object* v_x_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_){
_start:
{
lean_object* v_res_2202_; 
v_res_2202_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___redArg(v_mvarId_2195_, v_x_2196_, v___y_2197_, v___y_2198_, v___y_2199_, v___y_2200_);
lean_dec(v___y_2200_);
lean_dec_ref(v___y_2199_);
lean_dec(v___y_2198_);
lean_dec_ref(v___y_2197_);
return v_res_2202_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3(lean_object* v_00_u03b1_2203_, lean_object* v_mvarId_2204_, lean_object* v_x_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_){
_start:
{
lean_object* v___x_2211_; 
v___x_2211_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___redArg(v_mvarId_2204_, v_x_2205_, v___y_2206_, v___y_2207_, v___y_2208_, v___y_2209_);
return v___x_2211_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___boxed(lean_object* v_00_u03b1_2212_, lean_object* v_mvarId_2213_, lean_object* v_x_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_){
_start:
{
lean_object* v_res_2220_; 
v_res_2220_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3(v_00_u03b1_2212_, v_mvarId_2213_, v_x_2214_, v___y_2215_, v___y_2216_, v___y_2217_, v___y_2218_);
lean_dec(v___y_2218_);
lean_dec_ref(v___y_2217_);
lean_dec(v___y_2216_);
lean_dec_ref(v___y_2215_);
return v_res_2220_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_induction_spec__2(lean_object* v_fst_2221_, lean_object* v_as_2222_, size_t v_sz_2223_, size_t v_i_2224_, lean_object* v_b_2225_){
_start:
{
uint8_t v___x_2226_; 
v___x_2226_ = lean_usize_dec_lt(v_i_2224_, v_sz_2223_);
if (v___x_2226_ == 0)
{
return v_b_2225_;
}
else
{
lean_object* v_fst_2227_; lean_object* v_snd_2228_; lean_object* v___x_2230_; uint8_t v_isShared_2231_; uint8_t v_isSharedCheck_2246_; 
v_fst_2227_ = lean_ctor_get(v_b_2225_, 0);
v_snd_2228_ = lean_ctor_get(v_b_2225_, 1);
v_isSharedCheck_2246_ = !lean_is_exclusive(v_b_2225_);
if (v_isSharedCheck_2246_ == 0)
{
v___x_2230_ = v_b_2225_;
v_isShared_2231_ = v_isSharedCheck_2246_;
goto v_resetjp_2229_;
}
else
{
lean_inc(v_snd_2228_);
lean_inc(v_fst_2227_);
lean_dec(v_b_2225_);
v___x_2230_ = lean_box(0);
v_isShared_2231_ = v_isSharedCheck_2246_;
goto v_resetjp_2229_;
}
v_resetjp_2229_:
{
lean_object* v___x_2232_; lean_object* v_a_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2241_; 
v___x_2232_ = lean_box(0);
v_a_2233_ = lean_array_uget_borrowed(v_as_2222_, v_i_2224_);
v___x_2234_ = l_Lean_Expr_fvarId_x21(v_a_2233_);
v___x_2235_ = lean_array_get_borrowed(v___x_2232_, v_fst_2221_, v_snd_2228_);
lean_inc(v___x_2235_);
v___x_2236_ = l_Lean_mkFVar(v___x_2235_);
v___x_2237_ = l_Lean_Meta_FVarSubst_insert(v_fst_2227_, v___x_2234_, v___x_2236_);
v___x_2238_ = lean_unsigned_to_nat(1u);
v___x_2239_ = lean_nat_add(v_snd_2228_, v___x_2238_);
lean_dec(v_snd_2228_);
if (v_isShared_2231_ == 0)
{
lean_ctor_set(v___x_2230_, 1, v___x_2239_);
lean_ctor_set(v___x_2230_, 0, v___x_2237_);
v___x_2241_ = v___x_2230_;
goto v_reusejp_2240_;
}
else
{
lean_object* v_reuseFailAlloc_2245_; 
v_reuseFailAlloc_2245_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2245_, 0, v___x_2237_);
lean_ctor_set(v_reuseFailAlloc_2245_, 1, v___x_2239_);
v___x_2241_ = v_reuseFailAlloc_2245_;
goto v_reusejp_2240_;
}
v_reusejp_2240_:
{
size_t v___x_2242_; size_t v___x_2243_; 
v___x_2242_ = ((size_t)1ULL);
v___x_2243_ = lean_usize_add(v_i_2224_, v___x_2242_);
v_i_2224_ = v___x_2243_;
v_b_2225_ = v___x_2241_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_induction_spec__2___boxed(lean_object* v_fst_2247_, lean_object* v_as_2248_, lean_object* v_sz_2249_, lean_object* v_i_2250_, lean_object* v_b_2251_){
_start:
{
size_t v_sz_boxed_2252_; size_t v_i_boxed_2253_; lean_object* v_res_2254_; 
v_sz_boxed_2252_ = lean_unbox_usize(v_sz_2249_);
lean_dec(v_sz_2249_);
v_i_boxed_2253_ = lean_unbox_usize(v_i_2250_);
lean_dec(v_i_2250_);
v_res_2254_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_induction_spec__2(v_fst_2247_, v_as_2248_, v_sz_boxed_2252_, v_i_boxed_2253_, v_b_2251_);
lean_dec_ref(v_as_2248_);
lean_dec_ref(v_fst_2247_);
return v_res_2254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4___lam__0(lean_object* v_snd_2255_, lean_object* v___x_2256_, lean_object* v_fst_2257_, lean_object* v_a_2258_, lean_object* v___x_2259_, lean_object* v_givenNames_2260_, lean_object* v_fst_2261_, lean_object* v___x_2262_, lean_object* v_fst_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_){
_start:
{
lean_object* v___x_2269_; 
lean_inc_ref(v_a_2258_);
lean_inc(v_snd_2255_);
v___x_2269_ = l_Lean_Meta_mkRecursorAppPrefix(v_snd_2255_, v___x_2256_, v_fst_2257_, v_a_2258_, v___x_2259_, v___y_2264_, v___y_2265_, v___y_2266_, v___y_2267_);
if (lean_obj_tag(v___x_2269_) == 0)
{
lean_object* v_a_2270_; lean_object* v___x_2271_; 
v_a_2270_ = lean_ctor_get(v___x_2269_, 0);
lean_inc(v_a_2270_);
lean_dec_ref_known(v___x_2269_, 1);
v___x_2271_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize(v_snd_2255_, v_givenNames_2260_, v_a_2258_, v_fst_2261_, v___x_2262_, v___x_2259_, v_fst_2263_, v_a_2270_, v___y_2264_, v___y_2265_, v___y_2266_, v___y_2267_);
lean_dec_ref(v_a_2258_);
return v___x_2271_;
}
else
{
lean_object* v_a_2272_; lean_object* v___x_2274_; uint8_t v_isShared_2275_; uint8_t v_isSharedCheck_2279_; 
lean_dec(v_fst_2263_);
lean_dec_ref(v___x_2262_);
lean_dec_ref(v_a_2258_);
lean_dec(v_snd_2255_);
v_a_2272_ = lean_ctor_get(v___x_2269_, 0);
v_isSharedCheck_2279_ = !lean_is_exclusive(v___x_2269_);
if (v_isSharedCheck_2279_ == 0)
{
v___x_2274_ = v___x_2269_;
v_isShared_2275_ = v_isSharedCheck_2279_;
goto v_resetjp_2273_;
}
else
{
lean_inc(v_a_2272_);
lean_dec(v___x_2269_);
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
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4___lam__0___boxed(lean_object* v_snd_2280_, lean_object* v___x_2281_, lean_object* v_fst_2282_, lean_object* v_a_2283_, lean_object* v___x_2284_, lean_object* v_givenNames_2285_, lean_object* v_fst_2286_, lean_object* v___x_2287_, lean_object* v_fst_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_){
_start:
{
lean_object* v_res_2294_; 
v_res_2294_ = l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4___lam__0(v_snd_2280_, v___x_2281_, v_fst_2282_, v_a_2283_, v___x_2284_, v_givenNames_2285_, v_fst_2286_, v___x_2287_, v_fst_2288_, v___y_2289_, v___y_2290_, v___y_2291_, v___y_2292_);
lean_dec(v___y_2292_);
lean_dec_ref(v___y_2291_);
lean_dec(v___y_2290_);
lean_dec_ref(v___y_2289_);
lean_dec_ref(v_fst_2286_);
lean_dec_ref(v_givenNames_2285_);
lean_dec_ref(v___x_2284_);
return v_res_2294_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_induction_spec__1(size_t v_sz_2295_, size_t v_i_2296_, lean_object* v_bs_2297_){
_start:
{
uint8_t v___x_2298_; 
v___x_2298_ = lean_usize_dec_lt(v_i_2296_, v_sz_2295_);
if (v___x_2298_ == 0)
{
return v_bs_2297_;
}
else
{
lean_object* v_v_2299_; lean_object* v___x_2300_; lean_object* v_bs_x27_2301_; lean_object* v___x_2302_; size_t v___x_2303_; size_t v___x_2304_; lean_object* v___x_2305_; 
v_v_2299_ = lean_array_uget(v_bs_2297_, v_i_2296_);
v___x_2300_ = lean_unsigned_to_nat(0u);
v_bs_x27_2301_ = lean_array_uset(v_bs_2297_, v_i_2296_, v___x_2300_);
v___x_2302_ = l_Lean_Expr_fvarId_x21(v_v_2299_);
lean_dec(v_v_2299_);
v___x_2303_ = ((size_t)1ULL);
v___x_2304_ = lean_usize_add(v_i_2296_, v___x_2303_);
v___x_2305_ = lean_array_uset(v_bs_x27_2301_, v_i_2296_, v___x_2302_);
v_i_2296_ = v___x_2304_;
v_bs_2297_ = v___x_2305_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_induction_spec__1___boxed(lean_object* v_sz_2307_, lean_object* v_i_2308_, lean_object* v_bs_2309_){
_start:
{
size_t v_sz_boxed_2310_; size_t v_i_boxed_2311_; lean_object* v_res_2312_; 
v_sz_boxed_2310_ = lean_unbox_usize(v_sz_2307_);
lean_dec(v_sz_2307_);
v_i_boxed_2311_ = lean_unbox_usize(v_i_2308_);
lean_dec(v_i_2308_);
v_res_2312_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_induction_spec__1(v_sz_boxed_2310_, v_i_boxed_2311_, v_bs_2309_);
return v_res_2312_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_MVarId_induction_spec__0(lean_object* v_majorTypeArgs_2313_, lean_object* v_val_2314_, lean_object* v_mvarId_2315_, lean_object* v_as_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_){
_start:
{
if (lean_obj_tag(v_as_2316_) == 0)
{
lean_object* v___x_2322_; lean_object* v___x_2323_; 
lean_dec(v_mvarId_2315_);
lean_dec_ref(v_val_2314_);
v___x_2322_ = lean_box(0);
v___x_2323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2323_, 0, v___x_2322_);
return v___x_2323_;
}
else
{
lean_object* v_head_2324_; 
v_head_2324_ = lean_ctor_get(v_as_2316_, 0);
lean_inc(v_head_2324_);
if (lean_obj_tag(v_head_2324_) == 0)
{
lean_object* v_tail_2325_; 
v_tail_2325_ = lean_ctor_get(v_as_2316_, 1);
lean_inc(v_tail_2325_);
lean_dec_ref_known(v_as_2316_, 2);
v_as_2316_ = v_tail_2325_;
goto _start;
}
else
{
lean_object* v_tail_2327_; lean_object* v___x_2329_; uint8_t v_isShared_2330_; uint8_t v_isSharedCheck_2350_; 
v_tail_2327_ = lean_ctor_get(v_as_2316_, 1);
v_isSharedCheck_2350_ = !lean_is_exclusive(v_as_2316_);
if (v_isSharedCheck_2350_ == 0)
{
lean_object* v_unused_2351_; 
v_unused_2351_ = lean_ctor_get(v_as_2316_, 0);
lean_dec(v_unused_2351_);
v___x_2329_ = v_as_2316_;
v_isShared_2330_ = v_isSharedCheck_2350_;
goto v_resetjp_2328_;
}
else
{
lean_inc(v_tail_2327_);
lean_dec(v_as_2316_);
v___x_2329_ = lean_box(0);
v_isShared_2330_ = v_isSharedCheck_2350_;
goto v_resetjp_2328_;
}
v_resetjp_2328_:
{
lean_object* v_val_2331_; lean_object* v___x_2333_; uint8_t v_isShared_2334_; uint8_t v_isSharedCheck_2349_; 
v_val_2331_ = lean_ctor_get(v_head_2324_, 0);
v_isSharedCheck_2349_ = !lean_is_exclusive(v_head_2324_);
if (v_isSharedCheck_2349_ == 0)
{
v___x_2333_ = v_head_2324_;
v_isShared_2334_ = v_isSharedCheck_2349_;
goto v_resetjp_2332_;
}
else
{
lean_inc(v_val_2331_);
lean_dec(v_head_2324_);
v___x_2333_ = lean_box(0);
v_isShared_2334_ = v_isSharedCheck_2349_;
goto v_resetjp_2332_;
}
v_resetjp_2332_:
{
lean_object* v___x_2335_; uint8_t v___x_2336_; 
v___x_2335_ = lean_array_get_size(v_majorTypeArgs_2313_);
v___x_2336_ = lean_nat_dec_le(v___x_2335_, v_val_2331_);
lean_dec(v_val_2331_);
if (v___x_2336_ == 0)
{
lean_del_object(v___x_2333_);
lean_del_object(v___x_2329_);
v_as_2316_ = v_tail_2327_;
goto _start;
}
else
{
lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2342_; 
v___x_2338_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1));
v___x_2339_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__5, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__5);
lean_inc_ref(v_val_2314_);
v___x_2340_ = l_Lean_indentExpr(v_val_2314_);
if (v_isShared_2330_ == 0)
{
lean_ctor_set_tag(v___x_2329_, 7);
lean_ctor_set(v___x_2329_, 1, v___x_2340_);
lean_ctor_set(v___x_2329_, 0, v___x_2339_);
v___x_2342_ = v___x_2329_;
goto v_reusejp_2341_;
}
else
{
lean_object* v_reuseFailAlloc_2348_; 
v_reuseFailAlloc_2348_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2348_, 0, v___x_2339_);
lean_ctor_set(v_reuseFailAlloc_2348_, 1, v___x_2340_);
v___x_2342_ = v_reuseFailAlloc_2348_;
goto v_reusejp_2341_;
}
v_reusejp_2341_:
{
lean_object* v___x_2344_; 
if (v_isShared_2334_ == 0)
{
lean_ctor_set(v___x_2333_, 0, v___x_2342_);
v___x_2344_ = v___x_2333_;
goto v_reusejp_2343_;
}
else
{
lean_object* v_reuseFailAlloc_2347_; 
v_reuseFailAlloc_2347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2347_, 0, v___x_2342_);
v___x_2344_ = v_reuseFailAlloc_2347_;
goto v_reusejp_2343_;
}
v_reusejp_2343_:
{
lean_object* v___x_2345_; 
lean_inc(v_mvarId_2315_);
v___x_2345_ = l_Lean_Meta_throwTacticEx___redArg(v___x_2338_, v_mvarId_2315_, v___x_2344_, v___y_2317_, v___y_2318_, v___y_2319_, v___y_2320_);
if (lean_obj_tag(v___x_2345_) == 0)
{
lean_dec_ref_known(v___x_2345_, 1);
v_as_2316_ = v_tail_2327_;
goto _start;
}
else
{
lean_dec(v_tail_2327_);
lean_dec(v_mvarId_2315_);
lean_dec_ref(v_val_2314_);
return v___x_2345_;
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
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_MVarId_induction_spec__0___boxed(lean_object* v_majorTypeArgs_2352_, lean_object* v_val_2353_, lean_object* v_mvarId_2354_, lean_object* v_as_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_){
_start:
{
lean_object* v_res_2361_; 
v_res_2361_ = l_List_forM___at___00Lean_MVarId_induction_spec__0(v_majorTypeArgs_2352_, v_val_2353_, v_mvarId_2354_, v_as_2355_, v___y_2356_, v___y_2357_, v___y_2358_, v___y_2359_);
lean_dec(v___y_2359_);
lean_dec_ref(v___y_2358_);
lean_dec(v___y_2357_);
lean_dec_ref(v___y_2356_);
lean_dec_ref(v_majorTypeArgs_2352_);
return v_res_2361_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__1(void){
_start:
{
lean_object* v___x_2363_; lean_object* v___x_2364_; 
v___x_2363_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__0));
v___x_2364_ = l_Lean_stringToMessageData(v___x_2363_);
return v___x_2364_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__3(void){
_start:
{
lean_object* v___x_2366_; lean_object* v___x_2367_; 
v___x_2366_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__2));
v___x_2367_ = l_Lean_stringToMessageData(v___x_2366_);
return v___x_2367_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__5(void){
_start:
{
lean_object* v___x_2369_; lean_object* v___x_2370_; 
v___x_2369_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__4));
v___x_2370_ = l_Lean_stringToMessageData(v___x_2369_);
return v___x_2370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4(lean_object* v_a_2371_, lean_object* v_val_2372_, lean_object* v_mvarId_2373_, lean_object* v_majorFVarId_2374_, lean_object* v_givenNames_2375_, lean_object* v_recursorName_2376_, lean_object* v_x_2377_, lean_object* v_x_2378_, lean_object* v_x_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_){
_start:
{
if (lean_obj_tag(v_x_2377_) == 5)
{
lean_object* v_fn_2385_; lean_object* v_arg_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; 
v_fn_2385_ = lean_ctor_get(v_x_2377_, 0);
lean_inc_ref(v_fn_2385_);
v_arg_2386_ = lean_ctor_get(v_x_2377_, 1);
lean_inc_ref(v_arg_2386_);
lean_dec_ref_known(v_x_2377_, 2);
v___x_2387_ = lean_array_set(v_x_2378_, v_x_2379_, v_arg_2386_);
v___x_2388_ = lean_unsigned_to_nat(1u);
v___x_2389_ = lean_nat_sub(v_x_2379_, v___x_2388_);
lean_dec(v_x_2379_);
v_x_2377_ = v_fn_2385_;
v_x_2378_ = v___x_2387_;
v_x_2379_ = v___x_2389_;
goto _start;
}
else
{
uint8_t v_depElim_2391_; lean_object* v_paramsPos_2392_; lean_object* v___x_2393_; lean_object* v___y_2395_; lean_object* v___y_2396_; lean_object* v___y_2397_; lean_object* v___y_2398_; lean_object* v___y_2399_; lean_object* v___y_2400_; lean_object* v___y_2401_; size_t v___y_2402_; lean_object* v___y_2403_; lean_object* v___y_2404_; lean_object* v___y_2405_; lean_object* v___y_2406_; lean_object* v_cls_2411_; lean_object* v___x_2412_; 
lean_dec(v_x_2379_);
lean_dec_ref(v_x_2377_);
v_depElim_2391_ = lean_ctor_get_uint8(v_a_2371_, sizeof(void*)*8);
v_paramsPos_2392_ = lean_ctor_get(v_a_2371_, 5);
v___x_2393_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1));
v_cls_2411_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__2));
lean_inc(v_paramsPos_2392_);
lean_inc(v_mvarId_2373_);
lean_inc_ref(v_val_2372_);
v___x_2412_ = l_List_forM___at___00Lean_MVarId_induction_spec__0(v_x_2378_, v_val_2372_, v_mvarId_2373_, v_paramsPos_2392_, v___y_2380_, v___y_2381_, v___y_2382_, v___y_2383_);
lean_dec_ref(v_x_2378_);
if (lean_obj_tag(v___x_2412_) == 0)
{
lean_object* v___x_2413_; 
lean_dec_ref_known(v___x_2412_, 1);
lean_inc_ref(v_a_2371_);
lean_inc(v_mvarId_2373_);
v___x_2413_ = l_Lean_Meta_getMajorTypeIndices(v_mvarId_2373_, v___x_2393_, v_a_2371_, v_val_2372_, v___y_2380_, v___y_2381_, v___y_2382_, v___y_2383_);
if (lean_obj_tag(v___x_2413_) == 0)
{
lean_object* v_a_2414_; lean_object* v___y_2416_; lean_object* v___y_2417_; lean_object* v___y_2418_; lean_object* v___y_2419_; lean_object* v___x_2503_; 
v_a_2414_ = lean_ctor_get(v___x_2413_, 0);
lean_inc(v_a_2414_);
lean_dec_ref_known(v___x_2413_, 1);
lean_inc(v_mvarId_2373_);
v___x_2503_ = l_Lean_MVarId_getType(v_mvarId_2373_, v___y_2380_, v___y_2381_, v___y_2382_, v___y_2383_);
if (lean_obj_tag(v___x_2503_) == 0)
{
if (v_depElim_2391_ == 0)
{
lean_object* v_a_2504_; lean_object* v___x_2505_; lean_object* v_a_2506_; lean_object* v___x_2508_; uint8_t v_isShared_2509_; uint8_t v_isSharedCheck_2528_; 
v_a_2504_ = lean_ctor_get(v___x_2503_, 0);
lean_inc(v_a_2504_);
lean_dec_ref_known(v___x_2503_, 1);
lean_inc(v_majorFVarId_2374_);
v___x_2505_ = l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2___redArg(v_a_2504_, v_majorFVarId_2374_, v___y_2381_);
v_a_2506_ = lean_ctor_get(v___x_2505_, 0);
v_isSharedCheck_2528_ = !lean_is_exclusive(v___x_2505_);
if (v_isSharedCheck_2528_ == 0)
{
v___x_2508_ = v___x_2505_;
v_isShared_2509_ = v_isSharedCheck_2528_;
goto v_resetjp_2507_;
}
else
{
lean_inc(v_a_2506_);
lean_dec(v___x_2505_);
v___x_2508_ = lean_box(0);
v_isShared_2509_ = v_isSharedCheck_2528_;
goto v_resetjp_2507_;
}
v_resetjp_2507_:
{
uint8_t v___x_2510_; 
v___x_2510_ = lean_unbox(v_a_2506_);
lean_dec(v_a_2506_);
if (v___x_2510_ == 0)
{
lean_del_object(v___x_2508_);
lean_dec(v_recursorName_2376_);
v___y_2416_ = v___y_2380_;
v___y_2417_ = v___y_2381_;
v___y_2418_ = v___y_2382_;
v___y_2419_ = v___y_2383_;
goto v___jp_2415_;
}
else
{
lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2517_; 
v___x_2511_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__3, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__3);
v___x_2512_ = l_Lean_MessageData_ofName(v_recursorName_2376_);
v___x_2513_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2513_, 0, v___x_2511_);
lean_ctor_set(v___x_2513_, 1, v___x_2512_);
v___x_2514_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__5, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__5_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__5);
v___x_2515_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2515_, 0, v___x_2513_);
lean_ctor_set(v___x_2515_, 1, v___x_2514_);
if (v_isShared_2509_ == 0)
{
lean_ctor_set_tag(v___x_2508_, 1);
lean_ctor_set(v___x_2508_, 0, v___x_2515_);
v___x_2517_ = v___x_2508_;
goto v_reusejp_2516_;
}
else
{
lean_object* v_reuseFailAlloc_2527_; 
v_reuseFailAlloc_2527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2527_, 0, v___x_2515_);
v___x_2517_ = v_reuseFailAlloc_2527_;
goto v_reusejp_2516_;
}
v_reusejp_2516_:
{
lean_object* v___x_2518_; 
lean_inc(v_mvarId_2373_);
v___x_2518_ = l_Lean_Meta_throwTacticEx___redArg(v___x_2393_, v_mvarId_2373_, v___x_2517_, v___y_2380_, v___y_2381_, v___y_2382_, v___y_2383_);
if (lean_obj_tag(v___x_2518_) == 0)
{
lean_dec_ref_known(v___x_2518_, 1);
v___y_2416_ = v___y_2380_;
v___y_2417_ = v___y_2381_;
v___y_2418_ = v___y_2382_;
v___y_2419_ = v___y_2383_;
goto v___jp_2415_;
}
else
{
lean_object* v_a_2519_; lean_object* v___x_2521_; uint8_t v_isShared_2522_; uint8_t v_isSharedCheck_2526_; 
lean_dec(v_a_2414_);
lean_dec_ref(v_givenNames_2375_);
lean_dec(v_majorFVarId_2374_);
lean_dec(v_mvarId_2373_);
lean_dec_ref(v_a_2371_);
v_a_2519_ = lean_ctor_get(v___x_2518_, 0);
v_isSharedCheck_2526_ = !lean_is_exclusive(v___x_2518_);
if (v_isSharedCheck_2526_ == 0)
{
v___x_2521_ = v___x_2518_;
v_isShared_2522_ = v_isSharedCheck_2526_;
goto v_resetjp_2520_;
}
else
{
lean_inc(v_a_2519_);
lean_dec(v___x_2518_);
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
}
}
else
{
lean_dec_ref_known(v___x_2503_, 1);
lean_dec(v_recursorName_2376_);
v___y_2416_ = v___y_2380_;
v___y_2417_ = v___y_2381_;
v___y_2418_ = v___y_2382_;
v___y_2419_ = v___y_2383_;
goto v___jp_2415_;
}
}
else
{
lean_object* v_a_2529_; lean_object* v___x_2531_; uint8_t v_isShared_2532_; uint8_t v_isSharedCheck_2536_; 
lean_dec(v_a_2414_);
lean_dec(v_recursorName_2376_);
lean_dec_ref(v_givenNames_2375_);
lean_dec(v_majorFVarId_2374_);
lean_dec(v_mvarId_2373_);
lean_dec_ref(v_a_2371_);
v_a_2529_ = lean_ctor_get(v___x_2503_, 0);
v_isSharedCheck_2536_ = !lean_is_exclusive(v___x_2503_);
if (v_isSharedCheck_2536_ == 0)
{
v___x_2531_ = v___x_2503_;
v_isShared_2532_ = v_isSharedCheck_2536_;
goto v_resetjp_2530_;
}
else
{
lean_inc(v_a_2529_);
lean_dec(v___x_2503_);
v___x_2531_ = lean_box(0);
v_isShared_2532_ = v_isSharedCheck_2536_;
goto v_resetjp_2530_;
}
v_resetjp_2530_:
{
lean_object* v___x_2534_; 
if (v_isShared_2532_ == 0)
{
v___x_2534_ = v___x_2531_;
goto v_reusejp_2533_;
}
else
{
lean_object* v_reuseFailAlloc_2535_; 
v_reuseFailAlloc_2535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2535_, 0, v_a_2529_);
v___x_2534_ = v_reuseFailAlloc_2535_;
goto v_reusejp_2533_;
}
v_reusejp_2533_:
{
return v___x_2534_;
}
}
}
v___jp_2415_:
{
size_t v_sz_2420_; size_t v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; uint8_t v___x_2424_; uint8_t v___x_2425_; lean_object* v___x_2426_; 
v_sz_2420_ = lean_array_size(v_a_2414_);
v___x_2421_ = ((size_t)0ULL);
lean_inc(v_a_2414_);
v___x_2422_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_induction_spec__1(v_sz_2420_, v___x_2421_, v_a_2414_);
lean_inc(v_majorFVarId_2374_);
v___x_2423_ = lean_array_push(v___x_2422_, v_majorFVarId_2374_);
v___x_2424_ = 1;
v___x_2425_ = 0;
v___x_2426_ = l_Lean_MVarId_revert(v_mvarId_2373_, v___x_2423_, v___x_2424_, v___x_2425_, v___y_2416_, v___y_2417_, v___y_2418_, v___y_2419_);
if (lean_obj_tag(v___x_2426_) == 0)
{
lean_object* v_a_2427_; lean_object* v_fst_2428_; lean_object* v_snd_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; 
v_a_2427_ = lean_ctor_get(v___x_2426_, 0);
lean_inc(v_a_2427_);
lean_dec_ref_known(v___x_2426_, 1);
v_fst_2428_ = lean_ctor_get(v_a_2427_, 0);
lean_inc(v_fst_2428_);
v_snd_2429_ = lean_ctor_get(v_a_2427_, 1);
lean_inc(v_snd_2429_);
lean_dec(v_a_2427_);
v___x_2430_ = lean_array_get_size(v_a_2414_);
v___x_2431_ = lean_box(0);
v___x_2432_ = l_Lean_Meta_introNCore(v_snd_2429_, v___x_2430_, v___x_2431_, v___x_2425_, v___x_2424_, v___y_2416_, v___y_2417_, v___y_2418_, v___y_2419_);
if (lean_obj_tag(v___x_2432_) == 0)
{
lean_object* v_a_2433_; lean_object* v_fst_2434_; lean_object* v_snd_2435_; lean_object* v___x_2436_; 
v_a_2433_ = lean_ctor_get(v___x_2432_, 0);
lean_inc(v_a_2433_);
lean_dec_ref_known(v___x_2432_, 1);
v_fst_2434_ = lean_ctor_get(v_a_2433_, 0);
lean_inc(v_fst_2434_);
v_snd_2435_ = lean_ctor_get(v_a_2433_, 1);
lean_inc(v_snd_2435_);
lean_dec(v_a_2433_);
v___x_2436_ = l_Lean_Meta_intro1Core(v_snd_2435_, v___x_2424_, v___y_2416_, v___y_2417_, v___y_2418_, v___y_2419_);
if (lean_obj_tag(v___x_2436_) == 0)
{
lean_object* v_a_2437_; lean_object* v_fst_2438_; lean_object* v_snd_2439_; lean_object* v___x_2441_; uint8_t v_isShared_2442_; uint8_t v_isSharedCheck_2478_; 
v_a_2437_ = lean_ctor_get(v___x_2436_, 0);
lean_inc(v_a_2437_);
lean_dec_ref_known(v___x_2436_, 1);
v_fst_2438_ = lean_ctor_get(v_a_2437_, 0);
v_snd_2439_ = lean_ctor_get(v_a_2437_, 1);
v_isSharedCheck_2478_ = !lean_is_exclusive(v_a_2437_);
if (v_isSharedCheck_2478_ == 0)
{
v___x_2441_ = v_a_2437_;
v_isShared_2442_ = v_isSharedCheck_2478_;
goto v_resetjp_2440_;
}
else
{
lean_inc(v_snd_2439_);
lean_inc(v_fst_2438_);
lean_dec(v_a_2437_);
v___x_2441_ = lean_box(0);
v_isShared_2442_ = v_isSharedCheck_2478_;
goto v_resetjp_2440_;
}
v_resetjp_2440_:
{
lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2448_; 
v___x_2443_ = lean_box(0);
lean_inc(v_fst_2438_);
v___x_2444_ = l_Lean_mkFVar(v_fst_2438_);
lean_inc_ref(v___x_2444_);
v___x_2445_ = l_Lean_Meta_FVarSubst_insert(v___x_2443_, v_majorFVarId_2374_, v___x_2444_);
v___x_2446_ = lean_unsigned_to_nat(0u);
if (v_isShared_2442_ == 0)
{
lean_ctor_set(v___x_2441_, 1, v___x_2446_);
lean_ctor_set(v___x_2441_, 0, v___x_2445_);
v___x_2448_ = v___x_2441_;
goto v_reusejp_2447_;
}
else
{
lean_object* v_reuseFailAlloc_2477_; 
v_reuseFailAlloc_2477_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2477_, 0, v___x_2445_);
lean_ctor_set(v_reuseFailAlloc_2477_, 1, v___x_2446_);
v___x_2448_ = v_reuseFailAlloc_2477_;
goto v_reusejp_2447_;
}
v_reusejp_2447_:
{
lean_object* v___x_2449_; lean_object* v_toCold_2450_; lean_object* v_options_2451_; uint8_t v_hasTrace_2452_; 
v___x_2449_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_induction_spec__2(v_fst_2434_, v_a_2414_, v_sz_2420_, v___x_2421_, v___x_2448_);
lean_dec(v_a_2414_);
v_toCold_2450_ = lean_ctor_get(v___y_2418_, 0);
v_options_2451_ = lean_ctor_get(v_toCold_2450_, 2);
v_hasTrace_2452_ = lean_ctor_get_uint8(v_options_2451_, sizeof(void*)*1);
if (v_hasTrace_2452_ == 0)
{
lean_object* v_fst_2453_; 
v_fst_2453_ = lean_ctor_get(v___x_2449_, 0);
lean_inc(v_fst_2453_);
lean_dec_ref(v___x_2449_);
lean_inc(v_snd_2439_);
v___y_2395_ = v_fst_2428_;
v___y_2396_ = v_fst_2453_;
v___y_2397_ = v_snd_2439_;
v___y_2398_ = v_fst_2438_;
v___y_2399_ = v___x_2444_;
v___y_2400_ = v_snd_2439_;
v___y_2401_ = v_fst_2434_;
v___y_2402_ = v___x_2421_;
v___y_2403_ = v___y_2416_;
v___y_2404_ = v___y_2417_;
v___y_2405_ = v___y_2418_;
v___y_2406_ = v___y_2419_;
goto v___jp_2394_;
}
else
{
lean_object* v_fst_2454_; lean_object* v___x_2456_; uint8_t v_isShared_2457_; uint8_t v_isSharedCheck_2475_; 
v_fst_2454_ = lean_ctor_get(v___x_2449_, 0);
v_isSharedCheck_2475_ = !lean_is_exclusive(v___x_2449_);
if (v_isSharedCheck_2475_ == 0)
{
lean_object* v_unused_2476_; 
v_unused_2476_ = lean_ctor_get(v___x_2449_, 1);
lean_dec(v_unused_2476_);
v___x_2456_ = v___x_2449_;
v_isShared_2457_ = v_isSharedCheck_2475_;
goto v_resetjp_2455_;
}
else
{
lean_inc(v_fst_2454_);
lean_dec(v___x_2449_);
v___x_2456_ = lean_box(0);
v_isShared_2457_ = v_isSharedCheck_2475_;
goto v_resetjp_2455_;
}
v_resetjp_2455_:
{
lean_object* v_inheritedTraceOptions_2458_; lean_object* v___x_2459_; uint8_t v___x_2460_; 
v_inheritedTraceOptions_2458_ = lean_ctor_get(v_toCold_2450_, 11);
v___x_2459_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5);
v___x_2460_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2458_, v_options_2451_, v___x_2459_);
if (v___x_2460_ == 0)
{
lean_del_object(v___x_2456_);
lean_inc(v_snd_2439_);
v___y_2395_ = v_fst_2428_;
v___y_2396_ = v_fst_2454_;
v___y_2397_ = v_snd_2439_;
v___y_2398_ = v_fst_2438_;
v___y_2399_ = v___x_2444_;
v___y_2400_ = v_snd_2439_;
v___y_2401_ = v_fst_2434_;
v___y_2402_ = v___x_2421_;
v___y_2403_ = v___y_2416_;
v___y_2404_ = v___y_2417_;
v___y_2405_ = v___y_2418_;
v___y_2406_ = v___y_2419_;
goto v___jp_2394_;
}
else
{
lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2464_; 
v___x_2461_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__1);
lean_inc(v_snd_2439_);
v___x_2462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2462_, 0, v_snd_2439_);
if (v_isShared_2457_ == 0)
{
lean_ctor_set_tag(v___x_2456_, 7);
lean_ctor_set(v___x_2456_, 1, v___x_2462_);
lean_ctor_set(v___x_2456_, 0, v___x_2461_);
v___x_2464_ = v___x_2456_;
goto v_reusejp_2463_;
}
else
{
lean_object* v_reuseFailAlloc_2474_; 
v_reuseFailAlloc_2474_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2474_, 0, v___x_2461_);
lean_ctor_set(v_reuseFailAlloc_2474_, 1, v___x_2462_);
v___x_2464_ = v_reuseFailAlloc_2474_;
goto v_reusejp_2463_;
}
v_reusejp_2463_:
{
lean_object* v___x_2465_; 
v___x_2465_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1(v_cls_2411_, v___x_2464_, v___y_2416_, v___y_2417_, v___y_2418_, v___y_2419_);
if (lean_obj_tag(v___x_2465_) == 0)
{
lean_dec_ref_known(v___x_2465_, 1);
lean_inc(v_snd_2439_);
v___y_2395_ = v_fst_2428_;
v___y_2396_ = v_fst_2454_;
v___y_2397_ = v_snd_2439_;
v___y_2398_ = v_fst_2438_;
v___y_2399_ = v___x_2444_;
v___y_2400_ = v_snd_2439_;
v___y_2401_ = v_fst_2434_;
v___y_2402_ = v___x_2421_;
v___y_2403_ = v___y_2416_;
v___y_2404_ = v___y_2417_;
v___y_2405_ = v___y_2418_;
v___y_2406_ = v___y_2419_;
goto v___jp_2394_;
}
else
{
lean_object* v_a_2466_; lean_object* v___x_2468_; uint8_t v_isShared_2469_; uint8_t v_isSharedCheck_2473_; 
lean_dec(v_fst_2454_);
lean_dec_ref(v___x_2444_);
lean_dec(v_snd_2439_);
lean_dec(v_fst_2438_);
lean_dec(v_fst_2434_);
lean_dec(v_fst_2428_);
lean_dec_ref(v_givenNames_2375_);
lean_dec_ref(v_a_2371_);
v_a_2466_ = lean_ctor_get(v___x_2465_, 0);
v_isSharedCheck_2473_ = !lean_is_exclusive(v___x_2465_);
if (v_isSharedCheck_2473_ == 0)
{
v___x_2468_ = v___x_2465_;
v_isShared_2469_ = v_isSharedCheck_2473_;
goto v_resetjp_2467_;
}
else
{
lean_inc(v_a_2466_);
lean_dec(v___x_2465_);
v___x_2468_ = lean_box(0);
v_isShared_2469_ = v_isSharedCheck_2473_;
goto v_resetjp_2467_;
}
v_resetjp_2467_:
{
lean_object* v___x_2471_; 
if (v_isShared_2469_ == 0)
{
v___x_2471_ = v___x_2468_;
goto v_reusejp_2470_;
}
else
{
lean_object* v_reuseFailAlloc_2472_; 
v_reuseFailAlloc_2472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2472_, 0, v_a_2466_);
v___x_2471_ = v_reuseFailAlloc_2472_;
goto v_reusejp_2470_;
}
v_reusejp_2470_:
{
return v___x_2471_;
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
lean_object* v_a_2479_; lean_object* v___x_2481_; uint8_t v_isShared_2482_; uint8_t v_isSharedCheck_2486_; 
lean_dec(v_fst_2434_);
lean_dec(v_fst_2428_);
lean_dec(v_a_2414_);
lean_dec_ref(v_givenNames_2375_);
lean_dec(v_majorFVarId_2374_);
lean_dec_ref(v_a_2371_);
v_a_2479_ = lean_ctor_get(v___x_2436_, 0);
v_isSharedCheck_2486_ = !lean_is_exclusive(v___x_2436_);
if (v_isSharedCheck_2486_ == 0)
{
v___x_2481_ = v___x_2436_;
v_isShared_2482_ = v_isSharedCheck_2486_;
goto v_resetjp_2480_;
}
else
{
lean_inc(v_a_2479_);
lean_dec(v___x_2436_);
v___x_2481_ = lean_box(0);
v_isShared_2482_ = v_isSharedCheck_2486_;
goto v_resetjp_2480_;
}
v_resetjp_2480_:
{
lean_object* v___x_2484_; 
if (v_isShared_2482_ == 0)
{
v___x_2484_ = v___x_2481_;
goto v_reusejp_2483_;
}
else
{
lean_object* v_reuseFailAlloc_2485_; 
v_reuseFailAlloc_2485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2485_, 0, v_a_2479_);
v___x_2484_ = v_reuseFailAlloc_2485_;
goto v_reusejp_2483_;
}
v_reusejp_2483_:
{
return v___x_2484_;
}
}
}
}
else
{
lean_object* v_a_2487_; lean_object* v___x_2489_; uint8_t v_isShared_2490_; uint8_t v_isSharedCheck_2494_; 
lean_dec(v_fst_2428_);
lean_dec(v_a_2414_);
lean_dec_ref(v_givenNames_2375_);
lean_dec(v_majorFVarId_2374_);
lean_dec_ref(v_a_2371_);
v_a_2487_ = lean_ctor_get(v___x_2432_, 0);
v_isSharedCheck_2494_ = !lean_is_exclusive(v___x_2432_);
if (v_isSharedCheck_2494_ == 0)
{
v___x_2489_ = v___x_2432_;
v_isShared_2490_ = v_isSharedCheck_2494_;
goto v_resetjp_2488_;
}
else
{
lean_inc(v_a_2487_);
lean_dec(v___x_2432_);
v___x_2489_ = lean_box(0);
v_isShared_2490_ = v_isSharedCheck_2494_;
goto v_resetjp_2488_;
}
v_resetjp_2488_:
{
lean_object* v___x_2492_; 
if (v_isShared_2490_ == 0)
{
v___x_2492_ = v___x_2489_;
goto v_reusejp_2491_;
}
else
{
lean_object* v_reuseFailAlloc_2493_; 
v_reuseFailAlloc_2493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2493_, 0, v_a_2487_);
v___x_2492_ = v_reuseFailAlloc_2493_;
goto v_reusejp_2491_;
}
v_reusejp_2491_:
{
return v___x_2492_;
}
}
}
}
else
{
lean_object* v_a_2495_; lean_object* v___x_2497_; uint8_t v_isShared_2498_; uint8_t v_isSharedCheck_2502_; 
lean_dec(v_a_2414_);
lean_dec_ref(v_givenNames_2375_);
lean_dec(v_majorFVarId_2374_);
lean_dec_ref(v_a_2371_);
v_a_2495_ = lean_ctor_get(v___x_2426_, 0);
v_isSharedCheck_2502_ = !lean_is_exclusive(v___x_2426_);
if (v_isSharedCheck_2502_ == 0)
{
v___x_2497_ = v___x_2426_;
v_isShared_2498_ = v_isSharedCheck_2502_;
goto v_resetjp_2496_;
}
else
{
lean_inc(v_a_2495_);
lean_dec(v___x_2426_);
v___x_2497_ = lean_box(0);
v_isShared_2498_ = v_isSharedCheck_2502_;
goto v_resetjp_2496_;
}
v_resetjp_2496_:
{
lean_object* v___x_2500_; 
if (v_isShared_2498_ == 0)
{
v___x_2500_ = v___x_2497_;
goto v_reusejp_2499_;
}
else
{
lean_object* v_reuseFailAlloc_2501_; 
v_reuseFailAlloc_2501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2501_, 0, v_a_2495_);
v___x_2500_ = v_reuseFailAlloc_2501_;
goto v_reusejp_2499_;
}
v_reusejp_2499_:
{
return v___x_2500_;
}
}
}
}
}
else
{
lean_object* v_a_2537_; lean_object* v___x_2539_; uint8_t v_isShared_2540_; uint8_t v_isSharedCheck_2544_; 
lean_dec(v_recursorName_2376_);
lean_dec_ref(v_givenNames_2375_);
lean_dec(v_majorFVarId_2374_);
lean_dec(v_mvarId_2373_);
lean_dec_ref(v_a_2371_);
v_a_2537_ = lean_ctor_get(v___x_2413_, 0);
v_isSharedCheck_2544_ = !lean_is_exclusive(v___x_2413_);
if (v_isSharedCheck_2544_ == 0)
{
v___x_2539_ = v___x_2413_;
v_isShared_2540_ = v_isSharedCheck_2544_;
goto v_resetjp_2538_;
}
else
{
lean_inc(v_a_2537_);
lean_dec(v___x_2413_);
v___x_2539_ = lean_box(0);
v_isShared_2540_ = v_isSharedCheck_2544_;
goto v_resetjp_2538_;
}
v_resetjp_2538_:
{
lean_object* v___x_2542_; 
if (v_isShared_2540_ == 0)
{
v___x_2542_ = v___x_2539_;
goto v_reusejp_2541_;
}
else
{
lean_object* v_reuseFailAlloc_2543_; 
v_reuseFailAlloc_2543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2543_, 0, v_a_2537_);
v___x_2542_ = v_reuseFailAlloc_2543_;
goto v_reusejp_2541_;
}
v_reusejp_2541_:
{
return v___x_2542_;
}
}
}
}
else
{
lean_object* v_a_2545_; lean_object* v___x_2547_; uint8_t v_isShared_2548_; uint8_t v_isSharedCheck_2552_; 
lean_dec(v_recursorName_2376_);
lean_dec_ref(v_givenNames_2375_);
lean_dec(v_majorFVarId_2374_);
lean_dec(v_mvarId_2373_);
lean_dec_ref(v_val_2372_);
lean_dec_ref(v_a_2371_);
v_a_2545_ = lean_ctor_get(v___x_2412_, 0);
v_isSharedCheck_2552_ = !lean_is_exclusive(v___x_2412_);
if (v_isSharedCheck_2552_ == 0)
{
v___x_2547_ = v___x_2412_;
v_isShared_2548_ = v_isSharedCheck_2552_;
goto v_resetjp_2546_;
}
else
{
lean_inc(v_a_2545_);
lean_dec(v___x_2412_);
v___x_2547_ = lean_box(0);
v_isShared_2548_ = v_isSharedCheck_2552_;
goto v_resetjp_2546_;
}
v_resetjp_2546_:
{
lean_object* v___x_2550_; 
if (v_isShared_2548_ == 0)
{
v___x_2550_ = v___x_2547_;
goto v_reusejp_2549_;
}
else
{
lean_object* v_reuseFailAlloc_2551_; 
v_reuseFailAlloc_2551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2551_, 0, v_a_2545_);
v___x_2550_ = v_reuseFailAlloc_2551_;
goto v_reusejp_2549_;
}
v_reusejp_2549_:
{
return v___x_2550_;
}
}
}
v___jp_2394_:
{
size_t v_sz_2407_; lean_object* v___x_2408_; lean_object* v___f_2409_; lean_object* v___x_2410_; 
v_sz_2407_ = lean_array_size(v___y_2401_);
v___x_2408_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__3(v_sz_2407_, v___y_2402_, v___y_2401_);
v___f_2409_ = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4___lam__0___boxed), 14, 9);
lean_closure_set(v___f_2409_, 0, v___y_2397_);
lean_closure_set(v___f_2409_, 1, v___x_2393_);
lean_closure_set(v___f_2409_, 2, v___y_2398_);
lean_closure_set(v___f_2409_, 3, v_a_2371_);
lean_closure_set(v___f_2409_, 4, v___x_2408_);
lean_closure_set(v___f_2409_, 5, v_givenNames_2375_);
lean_closure_set(v___f_2409_, 6, v___y_2395_);
lean_closure_set(v___f_2409_, 7, v___y_2399_);
lean_closure_set(v___f_2409_, 8, v___y_2396_);
v___x_2410_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___redArg(v___y_2400_, v___f_2409_, v___y_2403_, v___y_2404_, v___y_2405_, v___y_2406_);
return v___x_2410_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___boxed(lean_object* v_a_2553_, lean_object* v_val_2554_, lean_object* v_mvarId_2555_, lean_object* v_majorFVarId_2556_, lean_object* v_givenNames_2557_, lean_object* v_recursorName_2558_, lean_object* v_x_2559_, lean_object* v_x_2560_, lean_object* v_x_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_){
_start:
{
lean_object* v_res_2567_; 
v_res_2567_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4(v_a_2553_, v_val_2554_, v_mvarId_2555_, v_majorFVarId_2556_, v_givenNames_2557_, v_recursorName_2558_, v_x_2559_, v_x_2560_, v_x_2561_, v___y_2562_, v___y_2563_, v___y_2564_, v___y_2565_);
lean_dec(v___y_2565_);
lean_dec_ref(v___y_2564_);
lean_dec(v___y_2563_);
lean_dec_ref(v___y_2562_);
return v_res_2567_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4(lean_object* v_val_2568_, lean_object* v_mvarId_2569_, lean_object* v_a_2570_, lean_object* v_majorFVarId_2571_, lean_object* v_givenNames_2572_, lean_object* v_recursorName_2573_, lean_object* v_x_2574_, lean_object* v_x_2575_, lean_object* v_x_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_){
_start:
{
if (lean_obj_tag(v_x_2574_) == 5)
{
lean_object* v_fn_2582_; lean_object* v_arg_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; 
v_fn_2582_ = lean_ctor_get(v_x_2574_, 0);
lean_inc_ref(v_fn_2582_);
v_arg_2583_ = lean_ctor_get(v_x_2574_, 1);
lean_inc_ref(v_arg_2583_);
lean_dec_ref_known(v_x_2574_, 2);
v___x_2584_ = lean_array_set(v_x_2575_, v_x_2576_, v_arg_2583_);
v___x_2585_ = lean_unsigned_to_nat(1u);
v___x_2586_ = lean_nat_sub(v_x_2576_, v___x_2585_);
v___x_2587_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4(v_a_2570_, v_val_2568_, v_mvarId_2569_, v_majorFVarId_2571_, v_givenNames_2572_, v_recursorName_2573_, v_fn_2582_, v___x_2584_, v___x_2586_, v___y_2577_, v___y_2578_, v___y_2579_, v___y_2580_);
return v___x_2587_;
}
else
{
uint8_t v_depElim_2588_; lean_object* v_paramsPos_2589_; lean_object* v___x_2590_; lean_object* v___y_2592_; lean_object* v___y_2593_; lean_object* v___y_2594_; lean_object* v___y_2595_; lean_object* v___y_2596_; size_t v___y_2597_; lean_object* v___y_2598_; lean_object* v___y_2599_; lean_object* v___y_2600_; lean_object* v___y_2601_; lean_object* v___y_2602_; lean_object* v___y_2603_; lean_object* v_cls_2608_; lean_object* v___x_2609_; 
lean_dec_ref(v_x_2574_);
v_depElim_2588_ = lean_ctor_get_uint8(v_a_2570_, sizeof(void*)*8);
v_paramsPos_2589_ = lean_ctor_get(v_a_2570_, 5);
v___x_2590_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1));
v_cls_2608_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__2));
lean_inc(v_paramsPos_2589_);
lean_inc(v_mvarId_2569_);
lean_inc_ref(v_val_2568_);
v___x_2609_ = l_List_forM___at___00Lean_MVarId_induction_spec__0(v_x_2575_, v_val_2568_, v_mvarId_2569_, v_paramsPos_2589_, v___y_2577_, v___y_2578_, v___y_2579_, v___y_2580_);
lean_dec_ref(v_x_2575_);
if (lean_obj_tag(v___x_2609_) == 0)
{
lean_object* v___x_2610_; 
lean_dec_ref_known(v___x_2609_, 1);
lean_inc_ref(v_a_2570_);
lean_inc(v_mvarId_2569_);
v___x_2610_ = l_Lean_Meta_getMajorTypeIndices(v_mvarId_2569_, v___x_2590_, v_a_2570_, v_val_2568_, v___y_2577_, v___y_2578_, v___y_2579_, v___y_2580_);
if (lean_obj_tag(v___x_2610_) == 0)
{
lean_object* v_a_2611_; lean_object* v___y_2613_; lean_object* v___y_2614_; lean_object* v___y_2615_; lean_object* v___y_2616_; lean_object* v___x_2700_; 
v_a_2611_ = lean_ctor_get(v___x_2610_, 0);
lean_inc(v_a_2611_);
lean_dec_ref_known(v___x_2610_, 1);
lean_inc(v_mvarId_2569_);
v___x_2700_ = l_Lean_MVarId_getType(v_mvarId_2569_, v___y_2577_, v___y_2578_, v___y_2579_, v___y_2580_);
if (lean_obj_tag(v___x_2700_) == 0)
{
if (v_depElim_2588_ == 0)
{
lean_object* v_a_2701_; lean_object* v___x_2702_; lean_object* v_a_2703_; lean_object* v___x_2705_; uint8_t v_isShared_2706_; uint8_t v_isSharedCheck_2725_; 
v_a_2701_ = lean_ctor_get(v___x_2700_, 0);
lean_inc(v_a_2701_);
lean_dec_ref_known(v___x_2700_, 1);
lean_inc(v_majorFVarId_2571_);
v___x_2702_ = l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2___redArg(v_a_2701_, v_majorFVarId_2571_, v___y_2578_);
v_a_2703_ = lean_ctor_get(v___x_2702_, 0);
v_isSharedCheck_2725_ = !lean_is_exclusive(v___x_2702_);
if (v_isSharedCheck_2725_ == 0)
{
v___x_2705_ = v___x_2702_;
v_isShared_2706_ = v_isSharedCheck_2725_;
goto v_resetjp_2704_;
}
else
{
lean_inc(v_a_2703_);
lean_dec(v___x_2702_);
v___x_2705_ = lean_box(0);
v_isShared_2706_ = v_isSharedCheck_2725_;
goto v_resetjp_2704_;
}
v_resetjp_2704_:
{
uint8_t v___x_2707_; 
v___x_2707_ = lean_unbox(v_a_2703_);
lean_dec(v_a_2703_);
if (v___x_2707_ == 0)
{
lean_del_object(v___x_2705_);
lean_dec(v_recursorName_2573_);
v___y_2613_ = v___y_2577_;
v___y_2614_ = v___y_2578_;
v___y_2615_ = v___y_2579_;
v___y_2616_ = v___y_2580_;
goto v___jp_2612_;
}
else
{
lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2714_; 
v___x_2708_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__3, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__3);
v___x_2709_ = l_Lean_MessageData_ofName(v_recursorName_2573_);
v___x_2710_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2710_, 0, v___x_2708_);
lean_ctor_set(v___x_2710_, 1, v___x_2709_);
v___x_2711_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__5, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__5_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__5);
v___x_2712_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2712_, 0, v___x_2710_);
lean_ctor_set(v___x_2712_, 1, v___x_2711_);
if (v_isShared_2706_ == 0)
{
lean_ctor_set_tag(v___x_2705_, 1);
lean_ctor_set(v___x_2705_, 0, v___x_2712_);
v___x_2714_ = v___x_2705_;
goto v_reusejp_2713_;
}
else
{
lean_object* v_reuseFailAlloc_2724_; 
v_reuseFailAlloc_2724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2724_, 0, v___x_2712_);
v___x_2714_ = v_reuseFailAlloc_2724_;
goto v_reusejp_2713_;
}
v_reusejp_2713_:
{
lean_object* v___x_2715_; 
lean_inc(v_mvarId_2569_);
v___x_2715_ = l_Lean_Meta_throwTacticEx___redArg(v___x_2590_, v_mvarId_2569_, v___x_2714_, v___y_2577_, v___y_2578_, v___y_2579_, v___y_2580_);
if (lean_obj_tag(v___x_2715_) == 0)
{
lean_dec_ref_known(v___x_2715_, 1);
v___y_2613_ = v___y_2577_;
v___y_2614_ = v___y_2578_;
v___y_2615_ = v___y_2579_;
v___y_2616_ = v___y_2580_;
goto v___jp_2612_;
}
else
{
lean_object* v_a_2716_; lean_object* v___x_2718_; uint8_t v_isShared_2719_; uint8_t v_isSharedCheck_2723_; 
lean_dec(v_a_2611_);
lean_dec_ref(v_givenNames_2572_);
lean_dec(v_majorFVarId_2571_);
lean_dec_ref(v_a_2570_);
lean_dec(v_mvarId_2569_);
v_a_2716_ = lean_ctor_get(v___x_2715_, 0);
v_isSharedCheck_2723_ = !lean_is_exclusive(v___x_2715_);
if (v_isSharedCheck_2723_ == 0)
{
v___x_2718_ = v___x_2715_;
v_isShared_2719_ = v_isSharedCheck_2723_;
goto v_resetjp_2717_;
}
else
{
lean_inc(v_a_2716_);
lean_dec(v___x_2715_);
v___x_2718_ = lean_box(0);
v_isShared_2719_ = v_isSharedCheck_2723_;
goto v_resetjp_2717_;
}
v_resetjp_2717_:
{
lean_object* v___x_2721_; 
if (v_isShared_2719_ == 0)
{
v___x_2721_ = v___x_2718_;
goto v_reusejp_2720_;
}
else
{
lean_object* v_reuseFailAlloc_2722_; 
v_reuseFailAlloc_2722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2722_, 0, v_a_2716_);
v___x_2721_ = v_reuseFailAlloc_2722_;
goto v_reusejp_2720_;
}
v_reusejp_2720_:
{
return v___x_2721_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v___x_2700_, 1);
lean_dec(v_recursorName_2573_);
v___y_2613_ = v___y_2577_;
v___y_2614_ = v___y_2578_;
v___y_2615_ = v___y_2579_;
v___y_2616_ = v___y_2580_;
goto v___jp_2612_;
}
}
else
{
lean_object* v_a_2726_; lean_object* v___x_2728_; uint8_t v_isShared_2729_; uint8_t v_isSharedCheck_2733_; 
lean_dec(v_a_2611_);
lean_dec(v_recursorName_2573_);
lean_dec_ref(v_givenNames_2572_);
lean_dec(v_majorFVarId_2571_);
lean_dec_ref(v_a_2570_);
lean_dec(v_mvarId_2569_);
v_a_2726_ = lean_ctor_get(v___x_2700_, 0);
v_isSharedCheck_2733_ = !lean_is_exclusive(v___x_2700_);
if (v_isSharedCheck_2733_ == 0)
{
v___x_2728_ = v___x_2700_;
v_isShared_2729_ = v_isSharedCheck_2733_;
goto v_resetjp_2727_;
}
else
{
lean_inc(v_a_2726_);
lean_dec(v___x_2700_);
v___x_2728_ = lean_box(0);
v_isShared_2729_ = v_isSharedCheck_2733_;
goto v_resetjp_2727_;
}
v_resetjp_2727_:
{
lean_object* v___x_2731_; 
if (v_isShared_2729_ == 0)
{
v___x_2731_ = v___x_2728_;
goto v_reusejp_2730_;
}
else
{
lean_object* v_reuseFailAlloc_2732_; 
v_reuseFailAlloc_2732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2732_, 0, v_a_2726_);
v___x_2731_ = v_reuseFailAlloc_2732_;
goto v_reusejp_2730_;
}
v_reusejp_2730_:
{
return v___x_2731_;
}
}
}
v___jp_2612_:
{
size_t v_sz_2617_; size_t v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; uint8_t v___x_2621_; uint8_t v___x_2622_; lean_object* v___x_2623_; 
v_sz_2617_ = lean_array_size(v_a_2611_);
v___x_2618_ = ((size_t)0ULL);
lean_inc(v_a_2611_);
v___x_2619_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_induction_spec__1(v_sz_2617_, v___x_2618_, v_a_2611_);
lean_inc(v_majorFVarId_2571_);
v___x_2620_ = lean_array_push(v___x_2619_, v_majorFVarId_2571_);
v___x_2621_ = 1;
v___x_2622_ = 0;
v___x_2623_ = l_Lean_MVarId_revert(v_mvarId_2569_, v___x_2620_, v___x_2621_, v___x_2622_, v___y_2613_, v___y_2614_, v___y_2615_, v___y_2616_);
if (lean_obj_tag(v___x_2623_) == 0)
{
lean_object* v_a_2624_; lean_object* v_fst_2625_; lean_object* v_snd_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; 
v_a_2624_ = lean_ctor_get(v___x_2623_, 0);
lean_inc(v_a_2624_);
lean_dec_ref_known(v___x_2623_, 1);
v_fst_2625_ = lean_ctor_get(v_a_2624_, 0);
lean_inc(v_fst_2625_);
v_snd_2626_ = lean_ctor_get(v_a_2624_, 1);
lean_inc(v_snd_2626_);
lean_dec(v_a_2624_);
v___x_2627_ = lean_array_get_size(v_a_2611_);
v___x_2628_ = lean_box(0);
v___x_2629_ = l_Lean_Meta_introNCore(v_snd_2626_, v___x_2627_, v___x_2628_, v___x_2622_, v___x_2621_, v___y_2613_, v___y_2614_, v___y_2615_, v___y_2616_);
if (lean_obj_tag(v___x_2629_) == 0)
{
lean_object* v_a_2630_; lean_object* v_fst_2631_; lean_object* v_snd_2632_; lean_object* v___x_2633_; 
v_a_2630_ = lean_ctor_get(v___x_2629_, 0);
lean_inc(v_a_2630_);
lean_dec_ref_known(v___x_2629_, 1);
v_fst_2631_ = lean_ctor_get(v_a_2630_, 0);
lean_inc(v_fst_2631_);
v_snd_2632_ = lean_ctor_get(v_a_2630_, 1);
lean_inc(v_snd_2632_);
lean_dec(v_a_2630_);
v___x_2633_ = l_Lean_Meta_intro1Core(v_snd_2632_, v___x_2621_, v___y_2613_, v___y_2614_, v___y_2615_, v___y_2616_);
if (lean_obj_tag(v___x_2633_) == 0)
{
lean_object* v_a_2634_; lean_object* v_fst_2635_; lean_object* v_snd_2636_; lean_object* v___x_2638_; uint8_t v_isShared_2639_; uint8_t v_isSharedCheck_2675_; 
v_a_2634_ = lean_ctor_get(v___x_2633_, 0);
lean_inc(v_a_2634_);
lean_dec_ref_known(v___x_2633_, 1);
v_fst_2635_ = lean_ctor_get(v_a_2634_, 0);
v_snd_2636_ = lean_ctor_get(v_a_2634_, 1);
v_isSharedCheck_2675_ = !lean_is_exclusive(v_a_2634_);
if (v_isSharedCheck_2675_ == 0)
{
v___x_2638_ = v_a_2634_;
v_isShared_2639_ = v_isSharedCheck_2675_;
goto v_resetjp_2637_;
}
else
{
lean_inc(v_snd_2636_);
lean_inc(v_fst_2635_);
lean_dec(v_a_2634_);
v___x_2638_ = lean_box(0);
v_isShared_2639_ = v_isSharedCheck_2675_;
goto v_resetjp_2637_;
}
v_resetjp_2637_:
{
lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2645_; 
v___x_2640_ = lean_box(0);
lean_inc(v_fst_2635_);
v___x_2641_ = l_Lean_mkFVar(v_fst_2635_);
lean_inc_ref(v___x_2641_);
v___x_2642_ = l_Lean_Meta_FVarSubst_insert(v___x_2640_, v_majorFVarId_2571_, v___x_2641_);
v___x_2643_ = lean_unsigned_to_nat(0u);
if (v_isShared_2639_ == 0)
{
lean_ctor_set(v___x_2638_, 1, v___x_2643_);
lean_ctor_set(v___x_2638_, 0, v___x_2642_);
v___x_2645_ = v___x_2638_;
goto v_reusejp_2644_;
}
else
{
lean_object* v_reuseFailAlloc_2674_; 
v_reuseFailAlloc_2674_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2674_, 0, v___x_2642_);
lean_ctor_set(v_reuseFailAlloc_2674_, 1, v___x_2643_);
v___x_2645_ = v_reuseFailAlloc_2674_;
goto v_reusejp_2644_;
}
v_reusejp_2644_:
{
lean_object* v___x_2646_; lean_object* v_toCold_2647_; lean_object* v_options_2648_; uint8_t v_hasTrace_2649_; 
v___x_2646_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_induction_spec__2(v_fst_2631_, v_a_2611_, v_sz_2617_, v___x_2618_, v___x_2645_);
lean_dec(v_a_2611_);
v_toCold_2647_ = lean_ctor_get(v___y_2615_, 0);
v_options_2648_ = lean_ctor_get(v_toCold_2647_, 2);
v_hasTrace_2649_ = lean_ctor_get_uint8(v_options_2648_, sizeof(void*)*1);
if (v_hasTrace_2649_ == 0)
{
lean_object* v_fst_2650_; 
v_fst_2650_ = lean_ctor_get(v___x_2646_, 0);
lean_inc(v_fst_2650_);
lean_dec_ref(v___x_2646_);
lean_inc(v_snd_2636_);
v___y_2592_ = v_fst_2650_;
v___y_2593_ = v_fst_2635_;
v___y_2594_ = v___x_2641_;
v___y_2595_ = v_fst_2625_;
v___y_2596_ = v_snd_2636_;
v___y_2597_ = v___x_2618_;
v___y_2598_ = v_snd_2636_;
v___y_2599_ = v_fst_2631_;
v___y_2600_ = v___y_2613_;
v___y_2601_ = v___y_2614_;
v___y_2602_ = v___y_2615_;
v___y_2603_ = v___y_2616_;
goto v___jp_2591_;
}
else
{
lean_object* v_fst_2651_; lean_object* v___x_2653_; uint8_t v_isShared_2654_; uint8_t v_isSharedCheck_2672_; 
v_fst_2651_ = lean_ctor_get(v___x_2646_, 0);
v_isSharedCheck_2672_ = !lean_is_exclusive(v___x_2646_);
if (v_isSharedCheck_2672_ == 0)
{
lean_object* v_unused_2673_; 
v_unused_2673_ = lean_ctor_get(v___x_2646_, 1);
lean_dec(v_unused_2673_);
v___x_2653_ = v___x_2646_;
v_isShared_2654_ = v_isSharedCheck_2672_;
goto v_resetjp_2652_;
}
else
{
lean_inc(v_fst_2651_);
lean_dec(v___x_2646_);
v___x_2653_ = lean_box(0);
v_isShared_2654_ = v_isSharedCheck_2672_;
goto v_resetjp_2652_;
}
v_resetjp_2652_:
{
lean_object* v_inheritedTraceOptions_2655_; lean_object* v___x_2656_; uint8_t v___x_2657_; 
v_inheritedTraceOptions_2655_ = lean_ctor_get(v_toCold_2647_, 11);
v___x_2656_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5);
v___x_2657_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2655_, v_options_2648_, v___x_2656_);
if (v___x_2657_ == 0)
{
lean_del_object(v___x_2653_);
lean_inc(v_snd_2636_);
v___y_2592_ = v_fst_2651_;
v___y_2593_ = v_fst_2635_;
v___y_2594_ = v___x_2641_;
v___y_2595_ = v_fst_2625_;
v___y_2596_ = v_snd_2636_;
v___y_2597_ = v___x_2618_;
v___y_2598_ = v_snd_2636_;
v___y_2599_ = v_fst_2631_;
v___y_2600_ = v___y_2613_;
v___y_2601_ = v___y_2614_;
v___y_2602_ = v___y_2615_;
v___y_2603_ = v___y_2616_;
goto v___jp_2591_;
}
else
{
lean_object* v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_2661_; 
v___x_2658_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__1);
lean_inc(v_snd_2636_);
v___x_2659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2659_, 0, v_snd_2636_);
if (v_isShared_2654_ == 0)
{
lean_ctor_set_tag(v___x_2653_, 7);
lean_ctor_set(v___x_2653_, 1, v___x_2659_);
lean_ctor_set(v___x_2653_, 0, v___x_2658_);
v___x_2661_ = v___x_2653_;
goto v_reusejp_2660_;
}
else
{
lean_object* v_reuseFailAlloc_2671_; 
v_reuseFailAlloc_2671_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2671_, 0, v___x_2658_);
lean_ctor_set(v_reuseFailAlloc_2671_, 1, v___x_2659_);
v___x_2661_ = v_reuseFailAlloc_2671_;
goto v_reusejp_2660_;
}
v_reusejp_2660_:
{
lean_object* v___x_2662_; 
v___x_2662_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1(v_cls_2608_, v___x_2661_, v___y_2613_, v___y_2614_, v___y_2615_, v___y_2616_);
if (lean_obj_tag(v___x_2662_) == 0)
{
lean_dec_ref_known(v___x_2662_, 1);
lean_inc(v_snd_2636_);
v___y_2592_ = v_fst_2651_;
v___y_2593_ = v_fst_2635_;
v___y_2594_ = v___x_2641_;
v___y_2595_ = v_fst_2625_;
v___y_2596_ = v_snd_2636_;
v___y_2597_ = v___x_2618_;
v___y_2598_ = v_snd_2636_;
v___y_2599_ = v_fst_2631_;
v___y_2600_ = v___y_2613_;
v___y_2601_ = v___y_2614_;
v___y_2602_ = v___y_2615_;
v___y_2603_ = v___y_2616_;
goto v___jp_2591_;
}
else
{
lean_object* v_a_2663_; lean_object* v___x_2665_; uint8_t v_isShared_2666_; uint8_t v_isSharedCheck_2670_; 
lean_dec(v_fst_2651_);
lean_dec_ref(v___x_2641_);
lean_dec(v_snd_2636_);
lean_dec(v_fst_2635_);
lean_dec(v_fst_2631_);
lean_dec(v_fst_2625_);
lean_dec_ref(v_givenNames_2572_);
lean_dec_ref(v_a_2570_);
v_a_2663_ = lean_ctor_get(v___x_2662_, 0);
v_isSharedCheck_2670_ = !lean_is_exclusive(v___x_2662_);
if (v_isSharedCheck_2670_ == 0)
{
v___x_2665_ = v___x_2662_;
v_isShared_2666_ = v_isSharedCheck_2670_;
goto v_resetjp_2664_;
}
else
{
lean_inc(v_a_2663_);
lean_dec(v___x_2662_);
v___x_2665_ = lean_box(0);
v_isShared_2666_ = v_isSharedCheck_2670_;
goto v_resetjp_2664_;
}
v_resetjp_2664_:
{
lean_object* v___x_2668_; 
if (v_isShared_2666_ == 0)
{
v___x_2668_ = v___x_2665_;
goto v_reusejp_2667_;
}
else
{
lean_object* v_reuseFailAlloc_2669_; 
v_reuseFailAlloc_2669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2669_, 0, v_a_2663_);
v___x_2668_ = v_reuseFailAlloc_2669_;
goto v_reusejp_2667_;
}
v_reusejp_2667_:
{
return v___x_2668_;
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
lean_object* v_a_2676_; lean_object* v___x_2678_; uint8_t v_isShared_2679_; uint8_t v_isSharedCheck_2683_; 
lean_dec(v_fst_2631_);
lean_dec(v_fst_2625_);
lean_dec(v_a_2611_);
lean_dec_ref(v_givenNames_2572_);
lean_dec(v_majorFVarId_2571_);
lean_dec_ref(v_a_2570_);
v_a_2676_ = lean_ctor_get(v___x_2633_, 0);
v_isSharedCheck_2683_ = !lean_is_exclusive(v___x_2633_);
if (v_isSharedCheck_2683_ == 0)
{
v___x_2678_ = v___x_2633_;
v_isShared_2679_ = v_isSharedCheck_2683_;
goto v_resetjp_2677_;
}
else
{
lean_inc(v_a_2676_);
lean_dec(v___x_2633_);
v___x_2678_ = lean_box(0);
v_isShared_2679_ = v_isSharedCheck_2683_;
goto v_resetjp_2677_;
}
v_resetjp_2677_:
{
lean_object* v___x_2681_; 
if (v_isShared_2679_ == 0)
{
v___x_2681_ = v___x_2678_;
goto v_reusejp_2680_;
}
else
{
lean_object* v_reuseFailAlloc_2682_; 
v_reuseFailAlloc_2682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2682_, 0, v_a_2676_);
v___x_2681_ = v_reuseFailAlloc_2682_;
goto v_reusejp_2680_;
}
v_reusejp_2680_:
{
return v___x_2681_;
}
}
}
}
else
{
lean_object* v_a_2684_; lean_object* v___x_2686_; uint8_t v_isShared_2687_; uint8_t v_isSharedCheck_2691_; 
lean_dec(v_fst_2625_);
lean_dec(v_a_2611_);
lean_dec_ref(v_givenNames_2572_);
lean_dec(v_majorFVarId_2571_);
lean_dec_ref(v_a_2570_);
v_a_2684_ = lean_ctor_get(v___x_2629_, 0);
v_isSharedCheck_2691_ = !lean_is_exclusive(v___x_2629_);
if (v_isSharedCheck_2691_ == 0)
{
v___x_2686_ = v___x_2629_;
v_isShared_2687_ = v_isSharedCheck_2691_;
goto v_resetjp_2685_;
}
else
{
lean_inc(v_a_2684_);
lean_dec(v___x_2629_);
v___x_2686_ = lean_box(0);
v_isShared_2687_ = v_isSharedCheck_2691_;
goto v_resetjp_2685_;
}
v_resetjp_2685_:
{
lean_object* v___x_2689_; 
if (v_isShared_2687_ == 0)
{
v___x_2689_ = v___x_2686_;
goto v_reusejp_2688_;
}
else
{
lean_object* v_reuseFailAlloc_2690_; 
v_reuseFailAlloc_2690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2690_, 0, v_a_2684_);
v___x_2689_ = v_reuseFailAlloc_2690_;
goto v_reusejp_2688_;
}
v_reusejp_2688_:
{
return v___x_2689_;
}
}
}
}
else
{
lean_object* v_a_2692_; lean_object* v___x_2694_; uint8_t v_isShared_2695_; uint8_t v_isSharedCheck_2699_; 
lean_dec(v_a_2611_);
lean_dec_ref(v_givenNames_2572_);
lean_dec(v_majorFVarId_2571_);
lean_dec_ref(v_a_2570_);
v_a_2692_ = lean_ctor_get(v___x_2623_, 0);
v_isSharedCheck_2699_ = !lean_is_exclusive(v___x_2623_);
if (v_isSharedCheck_2699_ == 0)
{
v___x_2694_ = v___x_2623_;
v_isShared_2695_ = v_isSharedCheck_2699_;
goto v_resetjp_2693_;
}
else
{
lean_inc(v_a_2692_);
lean_dec(v___x_2623_);
v___x_2694_ = lean_box(0);
v_isShared_2695_ = v_isSharedCheck_2699_;
goto v_resetjp_2693_;
}
v_resetjp_2693_:
{
lean_object* v___x_2697_; 
if (v_isShared_2695_ == 0)
{
v___x_2697_ = v___x_2694_;
goto v_reusejp_2696_;
}
else
{
lean_object* v_reuseFailAlloc_2698_; 
v_reuseFailAlloc_2698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2698_, 0, v_a_2692_);
v___x_2697_ = v_reuseFailAlloc_2698_;
goto v_reusejp_2696_;
}
v_reusejp_2696_:
{
return v___x_2697_;
}
}
}
}
}
else
{
lean_object* v_a_2734_; lean_object* v___x_2736_; uint8_t v_isShared_2737_; uint8_t v_isSharedCheck_2741_; 
lean_dec(v_recursorName_2573_);
lean_dec_ref(v_givenNames_2572_);
lean_dec(v_majorFVarId_2571_);
lean_dec_ref(v_a_2570_);
lean_dec(v_mvarId_2569_);
v_a_2734_ = lean_ctor_get(v___x_2610_, 0);
v_isSharedCheck_2741_ = !lean_is_exclusive(v___x_2610_);
if (v_isSharedCheck_2741_ == 0)
{
v___x_2736_ = v___x_2610_;
v_isShared_2737_ = v_isSharedCheck_2741_;
goto v_resetjp_2735_;
}
else
{
lean_inc(v_a_2734_);
lean_dec(v___x_2610_);
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
else
{
lean_object* v_a_2742_; lean_object* v___x_2744_; uint8_t v_isShared_2745_; uint8_t v_isSharedCheck_2749_; 
lean_dec(v_recursorName_2573_);
lean_dec_ref(v_givenNames_2572_);
lean_dec(v_majorFVarId_2571_);
lean_dec_ref(v_a_2570_);
lean_dec(v_mvarId_2569_);
lean_dec_ref(v_val_2568_);
v_a_2742_ = lean_ctor_get(v___x_2609_, 0);
v_isSharedCheck_2749_ = !lean_is_exclusive(v___x_2609_);
if (v_isSharedCheck_2749_ == 0)
{
v___x_2744_ = v___x_2609_;
v_isShared_2745_ = v_isSharedCheck_2749_;
goto v_resetjp_2743_;
}
else
{
lean_inc(v_a_2742_);
lean_dec(v___x_2609_);
v___x_2744_ = lean_box(0);
v_isShared_2745_ = v_isSharedCheck_2749_;
goto v_resetjp_2743_;
}
v_resetjp_2743_:
{
lean_object* v___x_2747_; 
if (v_isShared_2745_ == 0)
{
v___x_2747_ = v___x_2744_;
goto v_reusejp_2746_;
}
else
{
lean_object* v_reuseFailAlloc_2748_; 
v_reuseFailAlloc_2748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2748_, 0, v_a_2742_);
v___x_2747_ = v_reuseFailAlloc_2748_;
goto v_reusejp_2746_;
}
v_reusejp_2746_:
{
return v___x_2747_;
}
}
}
v___jp_2591_:
{
size_t v_sz_2604_; lean_object* v___x_2605_; lean_object* v___f_2606_; lean_object* v___x_2607_; 
v_sz_2604_ = lean_array_size(v___y_2599_);
v___x_2605_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__3(v_sz_2604_, v___y_2597_, v___y_2599_);
v___f_2606_ = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4___lam__0___boxed), 14, 9);
lean_closure_set(v___f_2606_, 0, v___y_2596_);
lean_closure_set(v___f_2606_, 1, v___x_2590_);
lean_closure_set(v___f_2606_, 2, v___y_2593_);
lean_closure_set(v___f_2606_, 3, v_a_2570_);
lean_closure_set(v___f_2606_, 4, v___x_2605_);
lean_closure_set(v___f_2606_, 5, v_givenNames_2572_);
lean_closure_set(v___f_2606_, 6, v___y_2595_);
lean_closure_set(v___f_2606_, 7, v___y_2594_);
lean_closure_set(v___f_2606_, 8, v___y_2592_);
v___x_2607_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___redArg(v___y_2598_, v___f_2606_, v___y_2600_, v___y_2601_, v___y_2602_, v___y_2603_);
return v___x_2607_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4___boxed(lean_object* v_val_2750_, lean_object* v_mvarId_2751_, lean_object* v_a_2752_, lean_object* v_majorFVarId_2753_, lean_object* v_givenNames_2754_, lean_object* v_recursorName_2755_, lean_object* v_x_2756_, lean_object* v_x_2757_, lean_object* v_x_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_){
_start:
{
lean_object* v_res_2764_; 
v_res_2764_ = l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4(v_val_2750_, v_mvarId_2751_, v_a_2752_, v_majorFVarId_2753_, v_givenNames_2754_, v_recursorName_2755_, v_x_2756_, v_x_2757_, v_x_2758_, v___y_2759_, v___y_2760_, v___y_2761_, v___y_2762_);
lean_dec(v___y_2762_);
lean_dec_ref(v___y_2761_);
lean_dec(v___y_2760_);
lean_dec_ref(v___y_2759_);
lean_dec(v_x_2758_);
return v_res_2764_;
}
}
static lean_object* _init_l_Lean_MVarId_induction___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2766_; lean_object* v___x_2767_; 
v___x_2766_ = ((lean_object*)(l_Lean_MVarId_induction___lam__0___closed__0));
v___x_2767_ = l_Lean_stringToMessageData(v___x_2766_);
return v___x_2767_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_induction___lam__0(lean_object* v___x_2768_, lean_object* v_mvarId_2769_, lean_object* v_majorFVarId_2770_, lean_object* v_recursorName_2771_, lean_object* v_givenNames_2772_, lean_object* v_cls_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_){
_start:
{
lean_object* v___y_2780_; lean_object* v___y_2781_; lean_object* v___y_2782_; lean_object* v___y_2783_; lean_object* v_toCold_2835_; lean_object* v_options_2836_; uint8_t v_hasTrace_2837_; 
v_toCold_2835_ = lean_ctor_get(v___y_2776_, 0);
v_options_2836_ = lean_ctor_get(v_toCold_2835_, 2);
v_hasTrace_2837_ = lean_ctor_get_uint8(v_options_2836_, sizeof(void*)*1);
if (v_hasTrace_2837_ == 0)
{
lean_dec(v_cls_2773_);
v___y_2780_ = v___y_2774_;
v___y_2781_ = v___y_2775_;
v___y_2782_ = v___y_2776_;
v___y_2783_ = v___y_2777_;
goto v___jp_2779_;
}
else
{
lean_object* v_inheritedTraceOptions_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; uint8_t v___x_2841_; 
v_inheritedTraceOptions_2838_ = lean_ctor_get(v_toCold_2835_, 11);
v___x_2839_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__4));
lean_inc(v_cls_2773_);
v___x_2840_ = l_Lean_Name_append(v___x_2839_, v_cls_2773_);
v___x_2841_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2838_, v_options_2836_, v___x_2840_);
lean_dec(v___x_2840_);
if (v___x_2841_ == 0)
{
lean_dec(v_cls_2773_);
v___y_2780_ = v___y_2774_;
v___y_2781_ = v___y_2775_;
v___y_2782_ = v___y_2776_;
v___y_2783_ = v___y_2777_;
goto v___jp_2779_;
}
else
{
lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; 
v___x_2842_ = lean_obj_once(&l_Lean_MVarId_induction___lam__0___closed__1, &l_Lean_MVarId_induction___lam__0___closed__1_once, _init_l_Lean_MVarId_induction___lam__0___closed__1);
lean_inc(v_mvarId_2769_);
v___x_2843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2843_, 0, v_mvarId_2769_);
v___x_2844_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2844_, 0, v___x_2842_);
lean_ctor_set(v___x_2844_, 1, v___x_2843_);
v___x_2845_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1(v_cls_2773_, v___x_2844_, v___y_2774_, v___y_2775_, v___y_2776_, v___y_2777_);
if (lean_obj_tag(v___x_2845_) == 0)
{
lean_dec_ref_known(v___x_2845_, 1);
v___y_2780_ = v___y_2774_;
v___y_2781_ = v___y_2775_;
v___y_2782_ = v___y_2776_;
v___y_2783_ = v___y_2777_;
goto v___jp_2779_;
}
else
{
lean_object* v_a_2846_; lean_object* v___x_2848_; uint8_t v_isShared_2849_; uint8_t v_isSharedCheck_2853_; 
lean_dec_ref(v_givenNames_2772_);
lean_dec(v_recursorName_2771_);
lean_dec(v_majorFVarId_2770_);
lean_dec(v_mvarId_2769_);
lean_dec_ref(v___x_2768_);
v_a_2846_ = lean_ctor_get(v___x_2845_, 0);
v_isSharedCheck_2853_ = !lean_is_exclusive(v___x_2845_);
if (v_isSharedCheck_2853_ == 0)
{
v___x_2848_ = v___x_2845_;
v_isShared_2849_ = v_isSharedCheck_2853_;
goto v_resetjp_2847_;
}
else
{
lean_inc(v_a_2846_);
lean_dec(v___x_2845_);
v___x_2848_ = lean_box(0);
v_isShared_2849_ = v_isSharedCheck_2853_;
goto v_resetjp_2847_;
}
v_resetjp_2847_:
{
lean_object* v___x_2851_; 
if (v_isShared_2849_ == 0)
{
v___x_2851_ = v___x_2848_;
goto v_reusejp_2850_;
}
else
{
lean_object* v_reuseFailAlloc_2852_; 
v_reuseFailAlloc_2852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2852_, 0, v_a_2846_);
v___x_2851_ = v_reuseFailAlloc_2852_;
goto v_reusejp_2850_;
}
v_reusejp_2850_:
{
return v___x_2851_;
}
}
}
}
}
v___jp_2779_:
{
lean_object* v___x_2784_; lean_object* v___x_2785_; 
v___x_2784_ = l_Lean_Name_mkStr1(v___x_2768_);
lean_inc(v___x_2784_);
lean_inc(v_mvarId_2769_);
v___x_2785_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_2769_, v___x_2784_, v___y_2780_, v___y_2781_, v___y_2782_, v___y_2783_);
if (lean_obj_tag(v___x_2785_) == 0)
{
lean_object* v___x_2786_; 
lean_dec_ref_known(v___x_2785_, 1);
lean_inc(v_majorFVarId_2770_);
v___x_2786_ = l_Lean_FVarId_getDecl___redArg(v_majorFVarId_2770_, v___y_2780_, v___y_2782_, v___y_2783_);
if (lean_obj_tag(v___x_2786_) == 0)
{
lean_object* v_a_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; 
v_a_2787_ = lean_ctor_get(v___x_2786_, 0);
lean_inc(v_a_2787_);
lean_dec_ref_known(v___x_2786_, 1);
v___x_2788_ = lean_box(0);
lean_inc(v_recursorName_2771_);
v___x_2789_ = l_Lean_Meta_mkRecursorInfo(v_recursorName_2771_, v___x_2788_, v___y_2780_, v___y_2781_, v___y_2782_, v___y_2783_);
if (lean_obj_tag(v___x_2789_) == 0)
{
lean_object* v_a_2790_; lean_object* v_typeName_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; 
v_a_2790_ = lean_ctor_get(v___x_2789_, 0);
lean_inc(v_a_2790_);
lean_dec_ref_known(v___x_2789_, 1);
v_typeName_2791_ = lean_ctor_get(v_a_2790_, 1);
v___x_2792_ = l_Lean_LocalDecl_type(v_a_2787_);
lean_dec(v_a_2787_);
lean_inc_ref(v___x_2792_);
v___x_2793_ = l_Lean_Meta_whnfUntil(v___x_2792_, v_typeName_2791_, v___y_2780_, v___y_2781_, v___y_2782_, v___y_2783_);
if (lean_obj_tag(v___x_2793_) == 0)
{
lean_object* v_a_2794_; 
v_a_2794_ = lean_ctor_get(v___x_2793_, 0);
lean_inc(v_a_2794_);
lean_dec_ref_known(v___x_2793_, 1);
if (lean_obj_tag(v_a_2794_) == 1)
{
lean_object* v_val_2795_; lean_object* v_dummy_2796_; lean_object* v_nargs_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; 
lean_dec_ref(v___x_2792_);
lean_dec(v___x_2784_);
v_val_2795_ = lean_ctor_get(v_a_2794_, 0);
lean_inc_n(v_val_2795_, 2);
lean_dec_ref_known(v_a_2794_, 1);
v_dummy_2796_ = lean_obj_once(&l_Lean_Meta_getMajorTypeIndices___closed__0, &l_Lean_Meta_getMajorTypeIndices___closed__0_once, _init_l_Lean_Meta_getMajorTypeIndices___closed__0);
v_nargs_2797_ = l_Lean_Expr_getAppNumArgs(v_val_2795_);
lean_inc(v_nargs_2797_);
v___x_2798_ = lean_mk_array(v_nargs_2797_, v_dummy_2796_);
v___x_2799_ = lean_unsigned_to_nat(1u);
v___x_2800_ = lean_nat_sub(v_nargs_2797_, v___x_2799_);
lean_dec(v_nargs_2797_);
v___x_2801_ = l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4(v_val_2795_, v_mvarId_2769_, v_a_2790_, v_majorFVarId_2770_, v_givenNames_2772_, v_recursorName_2771_, v_val_2795_, v___x_2798_, v___x_2800_, v___y_2780_, v___y_2781_, v___y_2782_, v___y_2783_);
lean_dec(v___x_2800_);
return v___x_2801_;
}
else
{
lean_object* v___x_2802_; 
lean_dec(v_a_2794_);
lean_dec(v_a_2790_);
lean_dec_ref(v_givenNames_2772_);
lean_dec(v_recursorName_2771_);
lean_dec(v_majorFVarId_2770_);
v___x_2802_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg(v___x_2784_, v_mvarId_2769_, v___x_2792_, v___y_2780_, v___y_2781_, v___y_2782_, v___y_2783_);
return v___x_2802_;
}
}
else
{
lean_object* v_a_2803_; lean_object* v___x_2805_; uint8_t v_isShared_2806_; uint8_t v_isSharedCheck_2810_; 
lean_dec_ref(v___x_2792_);
lean_dec(v_a_2790_);
lean_dec(v___x_2784_);
lean_dec_ref(v_givenNames_2772_);
lean_dec(v_recursorName_2771_);
lean_dec(v_majorFVarId_2770_);
lean_dec(v_mvarId_2769_);
v_a_2803_ = lean_ctor_get(v___x_2793_, 0);
v_isSharedCheck_2810_ = !lean_is_exclusive(v___x_2793_);
if (v_isSharedCheck_2810_ == 0)
{
v___x_2805_ = v___x_2793_;
v_isShared_2806_ = v_isSharedCheck_2810_;
goto v_resetjp_2804_;
}
else
{
lean_inc(v_a_2803_);
lean_dec(v___x_2793_);
v___x_2805_ = lean_box(0);
v_isShared_2806_ = v_isSharedCheck_2810_;
goto v_resetjp_2804_;
}
v_resetjp_2804_:
{
lean_object* v___x_2808_; 
if (v_isShared_2806_ == 0)
{
v___x_2808_ = v___x_2805_;
goto v_reusejp_2807_;
}
else
{
lean_object* v_reuseFailAlloc_2809_; 
v_reuseFailAlloc_2809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2809_, 0, v_a_2803_);
v___x_2808_ = v_reuseFailAlloc_2809_;
goto v_reusejp_2807_;
}
v_reusejp_2807_:
{
return v___x_2808_;
}
}
}
}
else
{
lean_object* v_a_2811_; lean_object* v___x_2813_; uint8_t v_isShared_2814_; uint8_t v_isSharedCheck_2818_; 
lean_dec(v_a_2787_);
lean_dec(v___x_2784_);
lean_dec_ref(v_givenNames_2772_);
lean_dec(v_recursorName_2771_);
lean_dec(v_majorFVarId_2770_);
lean_dec(v_mvarId_2769_);
v_a_2811_ = lean_ctor_get(v___x_2789_, 0);
v_isSharedCheck_2818_ = !lean_is_exclusive(v___x_2789_);
if (v_isSharedCheck_2818_ == 0)
{
v___x_2813_ = v___x_2789_;
v_isShared_2814_ = v_isSharedCheck_2818_;
goto v_resetjp_2812_;
}
else
{
lean_inc(v_a_2811_);
lean_dec(v___x_2789_);
v___x_2813_ = lean_box(0);
v_isShared_2814_ = v_isSharedCheck_2818_;
goto v_resetjp_2812_;
}
v_resetjp_2812_:
{
lean_object* v___x_2816_; 
if (v_isShared_2814_ == 0)
{
v___x_2816_ = v___x_2813_;
goto v_reusejp_2815_;
}
else
{
lean_object* v_reuseFailAlloc_2817_; 
v_reuseFailAlloc_2817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2817_, 0, v_a_2811_);
v___x_2816_ = v_reuseFailAlloc_2817_;
goto v_reusejp_2815_;
}
v_reusejp_2815_:
{
return v___x_2816_;
}
}
}
}
else
{
lean_object* v_a_2819_; lean_object* v___x_2821_; uint8_t v_isShared_2822_; uint8_t v_isSharedCheck_2826_; 
lean_dec(v___x_2784_);
lean_dec_ref(v_givenNames_2772_);
lean_dec(v_recursorName_2771_);
lean_dec(v_majorFVarId_2770_);
lean_dec(v_mvarId_2769_);
v_a_2819_ = lean_ctor_get(v___x_2786_, 0);
v_isSharedCheck_2826_ = !lean_is_exclusive(v___x_2786_);
if (v_isSharedCheck_2826_ == 0)
{
v___x_2821_ = v___x_2786_;
v_isShared_2822_ = v_isSharedCheck_2826_;
goto v_resetjp_2820_;
}
else
{
lean_inc(v_a_2819_);
lean_dec(v___x_2786_);
v___x_2821_ = lean_box(0);
v_isShared_2822_ = v_isSharedCheck_2826_;
goto v_resetjp_2820_;
}
v_resetjp_2820_:
{
lean_object* v___x_2824_; 
if (v_isShared_2822_ == 0)
{
v___x_2824_ = v___x_2821_;
goto v_reusejp_2823_;
}
else
{
lean_object* v_reuseFailAlloc_2825_; 
v_reuseFailAlloc_2825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2825_, 0, v_a_2819_);
v___x_2824_ = v_reuseFailAlloc_2825_;
goto v_reusejp_2823_;
}
v_reusejp_2823_:
{
return v___x_2824_;
}
}
}
}
else
{
lean_object* v_a_2827_; lean_object* v___x_2829_; uint8_t v_isShared_2830_; uint8_t v_isSharedCheck_2834_; 
lean_dec(v___x_2784_);
lean_dec_ref(v_givenNames_2772_);
lean_dec(v_recursorName_2771_);
lean_dec(v_majorFVarId_2770_);
lean_dec(v_mvarId_2769_);
v_a_2827_ = lean_ctor_get(v___x_2785_, 0);
v_isSharedCheck_2834_ = !lean_is_exclusive(v___x_2785_);
if (v_isSharedCheck_2834_ == 0)
{
v___x_2829_ = v___x_2785_;
v_isShared_2830_ = v_isSharedCheck_2834_;
goto v_resetjp_2828_;
}
else
{
lean_inc(v_a_2827_);
lean_dec(v___x_2785_);
v___x_2829_ = lean_box(0);
v_isShared_2830_ = v_isSharedCheck_2834_;
goto v_resetjp_2828_;
}
v_resetjp_2828_:
{
lean_object* v___x_2832_; 
if (v_isShared_2830_ == 0)
{
v___x_2832_ = v___x_2829_;
goto v_reusejp_2831_;
}
else
{
lean_object* v_reuseFailAlloc_2833_; 
v_reuseFailAlloc_2833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2833_, 0, v_a_2827_);
v___x_2832_ = v_reuseFailAlloc_2833_;
goto v_reusejp_2831_;
}
v_reusejp_2831_:
{
return v___x_2832_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_induction___lam__0___boxed(lean_object* v___x_2854_, lean_object* v_mvarId_2855_, lean_object* v_majorFVarId_2856_, lean_object* v_recursorName_2857_, lean_object* v_givenNames_2858_, lean_object* v_cls_2859_, lean_object* v___y_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_, lean_object* v___y_2863_, lean_object* v___y_2864_){
_start:
{
lean_object* v_res_2865_; 
v_res_2865_ = l_Lean_MVarId_induction___lam__0(v___x_2854_, v_mvarId_2855_, v_majorFVarId_2856_, v_recursorName_2857_, v_givenNames_2858_, v_cls_2859_, v___y_2860_, v___y_2861_, v___y_2862_, v___y_2863_);
lean_dec(v___y_2863_);
lean_dec_ref(v___y_2862_);
lean_dec(v___y_2861_);
lean_dec_ref(v___y_2860_);
return v_res_2865_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_induction(lean_object* v_mvarId_2866_, lean_object* v_majorFVarId_2867_, lean_object* v_recursorName_2868_, lean_object* v_givenNames_2869_, lean_object* v_a_2870_, lean_object* v_a_2871_, lean_object* v_a_2872_, lean_object* v_a_2873_){
_start:
{
lean_object* v___x_2875_; lean_object* v_cls_2876_; lean_object* v___f_2877_; lean_object* v___x_2878_; 
v___x_2875_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__0));
v_cls_2876_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__2));
lean_inc(v_mvarId_2866_);
v___f_2877_ = lean_alloc_closure((void*)(l_Lean_MVarId_induction___lam__0___boxed), 11, 6);
lean_closure_set(v___f_2877_, 0, v___x_2875_);
lean_closure_set(v___f_2877_, 1, v_mvarId_2866_);
lean_closure_set(v___f_2877_, 2, v_majorFVarId_2867_);
lean_closure_set(v___f_2877_, 3, v_recursorName_2868_);
lean_closure_set(v___f_2877_, 4, v_givenNames_2869_);
lean_closure_set(v___f_2877_, 5, v_cls_2876_);
v___x_2878_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___redArg(v_mvarId_2866_, v___f_2877_, v_a_2870_, v_a_2871_, v_a_2872_, v_a_2873_);
return v___x_2878_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_induction___boxed(lean_object* v_mvarId_2879_, lean_object* v_majorFVarId_2880_, lean_object* v_recursorName_2881_, lean_object* v_givenNames_2882_, lean_object* v_a_2883_, lean_object* v_a_2884_, lean_object* v_a_2885_, lean_object* v_a_2886_, lean_object* v_a_2887_){
_start:
{
lean_object* v_res_2888_; 
v_res_2888_ = l_Lean_MVarId_induction(v_mvarId_2879_, v_majorFVarId_2880_, v_recursorName_2881_, v_givenNames_2882_, v_a_2883_, v_a_2884_, v_a_2885_, v_a_2886_);
lean_dec(v_a_2886_);
lean_dec_ref(v_a_2885_);
lean_dec(v_a_2884_);
lean_dec_ref(v_a_2883_);
return v_res_2888_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; 
v___x_2936_ = lean_unsigned_to_nat(2221195325u);
v___x_2937_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_));
v___x_2938_ = l_Lean_Name_num___override(v___x_2937_, v___x_2936_);
return v___x_2938_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; 
v___x_2940_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_));
v___x_2941_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_);
v___x_2942_ = l_Lean_Name_str___override(v___x_2941_, v___x_2940_);
return v___x_2942_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; 
v___x_2944_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_));
v___x_2945_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_);
v___x_2946_ = l_Lean_Name_str___override(v___x_2945_, v___x_2944_);
return v___x_2946_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; 
v___x_2947_ = lean_unsigned_to_nat(2u);
v___x_2948_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_);
v___x_2949_ = l_Lean_Name_num___override(v___x_2948_, v___x_2947_);
return v___x_2949_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2951_; uint8_t v___x_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; 
v___x_2951_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__2));
v___x_2952_ = 0;
v___x_2953_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_);
v___x_2954_ = l_Lean_registerTraceClass(v___x_2951_, v___x_2952_, v___x_2953_);
return v___x_2954_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2____boxed(lean_object* v_a_2955_){
_start:
{
lean_object* v_res_2956_; 
v_res_2956_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_();
return v_res_2956_;
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
