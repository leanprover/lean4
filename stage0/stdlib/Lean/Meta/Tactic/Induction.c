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
lean_object* v___f_133_; lean_object* v___x_6935__overap_134_; lean_object* v___x_135_; 
v___f_133_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__4___closed__0));
v___x_6935__overap_134_ = lean_panic_fn_borrowed(v___f_133_, v_msg_127_);
lean_inc(v___y_131_);
lean_inc_ref(v___y_130_);
lean_inc(v___y_129_);
lean_inc_ref(v___y_128_);
v___x_135_ = lean_apply_5(v___x_6935__overap_134_, v___y_128_, v___y_129_, v___y_130_, v___y_131_, lean_box(0));
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
size_t v_x_8253__boxed_360_; size_t v_x_8254__boxed_361_; lean_object* v_res_362_; 
v_x_8253__boxed_360_ = lean_unbox_usize(v_x_356_);
lean_dec(v_x_356_);
v_x_8254__boxed_361_ = lean_unbox_usize(v_x_357_);
lean_dec(v_x_357_);
v_res_362_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2___redArg(v_x_355_, v_x_8253__boxed_360_, v_x_8254__boxed_361_, v_x_358_, v_x_359_);
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
lean_object* v___x_374_; lean_object* v_mctx_375_; lean_object* v_cache_376_; lean_object* v_zetaDeltaFVarIds_377_; lean_object* v_postponed_378_; lean_object* v_diag_379_; lean_object* v___x_381_; uint8_t v_isShared_382_; uint8_t v_isSharedCheck_407_; 
v___x_374_ = lean_st_ref_take(v___y_372_);
v_mctx_375_ = lean_ctor_get(v___x_374_, 0);
v_cache_376_ = lean_ctor_get(v___x_374_, 1);
v_zetaDeltaFVarIds_377_ = lean_ctor_get(v___x_374_, 2);
v_postponed_378_ = lean_ctor_get(v___x_374_, 3);
v_diag_379_ = lean_ctor_get(v___x_374_, 4);
v_isSharedCheck_407_ = !lean_is_exclusive(v___x_374_);
if (v_isSharedCheck_407_ == 0)
{
v___x_381_ = v___x_374_;
v_isShared_382_ = v_isSharedCheck_407_;
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
v_isShared_382_ = v_isSharedCheck_407_;
goto v_resetjp_380_;
}
v_resetjp_380_:
{
lean_object* v_depth_383_; lean_object* v_levelAssignDepth_384_; lean_object* v_lmvarCounter_385_; lean_object* v_mvarCounter_386_; lean_object* v_lDecls_387_; lean_object* v_decls_388_; lean_object* v_userNames_389_; lean_object* v_lAssignment_390_; lean_object* v_eAssignment_391_; lean_object* v_dAssignment_392_; lean_object* v___x_394_; uint8_t v_isShared_395_; uint8_t v_isSharedCheck_406_; 
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
v_isSharedCheck_406_ = !lean_is_exclusive(v_mctx_375_);
if (v_isSharedCheck_406_ == 0)
{
v___x_394_ = v_mctx_375_;
v_isShared_395_ = v_isSharedCheck_406_;
goto v_resetjp_393_;
}
else
{
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
v___x_394_ = lean_box(0);
v_isShared_395_ = v_isSharedCheck_406_;
goto v_resetjp_393_;
}
v_resetjp_393_:
{
lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_399_; 
v___x_396_ = lean_box(0);
v___x_397_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0___redArg(v_eAssignment_391_, v_mvarId_370_, v_val_371_);
if (v_isShared_395_ == 0)
{
lean_ctor_set(v___x_394_, 8, v___x_397_);
v___x_399_ = v___x_394_;
goto v_reusejp_398_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v_depth_383_);
lean_ctor_set(v_reuseFailAlloc_405_, 1, v_levelAssignDepth_384_);
lean_ctor_set(v_reuseFailAlloc_405_, 2, v_lmvarCounter_385_);
lean_ctor_set(v_reuseFailAlloc_405_, 3, v_mvarCounter_386_);
lean_ctor_set(v_reuseFailAlloc_405_, 4, v_lDecls_387_);
lean_ctor_set(v_reuseFailAlloc_405_, 5, v_decls_388_);
lean_ctor_set(v_reuseFailAlloc_405_, 6, v_userNames_389_);
lean_ctor_set(v_reuseFailAlloc_405_, 7, v_lAssignment_390_);
lean_ctor_set(v_reuseFailAlloc_405_, 8, v___x_397_);
lean_ctor_set(v_reuseFailAlloc_405_, 9, v_dAssignment_392_);
v___x_399_ = v_reuseFailAlloc_405_;
goto v_reusejp_398_;
}
v_reusejp_398_:
{
lean_object* v___x_401_; 
if (v_isShared_382_ == 0)
{
lean_ctor_set(v___x_381_, 0, v___x_399_);
v___x_401_ = v___x_381_;
goto v_reusejp_400_;
}
else
{
lean_object* v_reuseFailAlloc_404_; 
v_reuseFailAlloc_404_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_404_, 0, v___x_399_);
lean_ctor_set(v_reuseFailAlloc_404_, 1, v_cache_376_);
lean_ctor_set(v_reuseFailAlloc_404_, 2, v_zetaDeltaFVarIds_377_);
lean_ctor_set(v_reuseFailAlloc_404_, 3, v_postponed_378_);
lean_ctor_set(v_reuseFailAlloc_404_, 4, v_diag_379_);
v___x_401_ = v_reuseFailAlloc_404_;
goto v_reusejp_400_;
}
v_reusejp_400_:
{
lean_object* v___x_402_; lean_object* v___x_403_; 
v___x_402_ = lean_st_ref_put(v___y_372_, v___x_401_);
v___x_403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_403_, 0, v___x_396_);
return v___x_403_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0___redArg___boxed(lean_object* v_mvarId_408_, lean_object* v_val_409_, lean_object* v___y_410_, lean_object* v___y_411_){
_start:
{
lean_object* v_res_412_; 
v_res_412_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0___redArg(v_mvarId_408_, v_val_409_, v___y_410_);
lean_dec(v___y_410_);
return v_res_412_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__3(size_t v_sz_413_, size_t v_i_414_, lean_object* v_bs_415_){
_start:
{
uint8_t v___x_416_; 
v___x_416_ = lean_usize_dec_lt(v_i_414_, v_sz_413_);
if (v___x_416_ == 0)
{
return v_bs_415_;
}
else
{
lean_object* v_v_417_; lean_object* v___x_418_; lean_object* v_bs_x27_419_; lean_object* v___x_420_; size_t v___x_421_; size_t v___x_422_; lean_object* v___x_423_; 
v_v_417_ = lean_array_uget(v_bs_415_, v_i_414_);
v___x_418_ = lean_unsigned_to_nat(0u);
v_bs_x27_419_ = lean_array_uset(v_bs_415_, v_i_414_, v___x_418_);
v___x_420_ = l_Lean_mkFVar(v_v_417_);
v___x_421_ = ((size_t)1ULL);
v___x_422_ = lean_usize_add(v_i_414_, v___x_421_);
v___x_423_ = lean_array_uset(v_bs_x27_419_, v_i_414_, v___x_420_);
v_i_414_ = v___x_422_;
v_bs_415_ = v___x_423_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__3___boxed(lean_object* v_sz_425_, lean_object* v_i_426_, lean_object* v_bs_427_){
_start:
{
size_t v_sz_boxed_428_; size_t v_i_boxed_429_; lean_object* v_res_430_; 
v_sz_boxed_428_ = lean_unbox_usize(v_sz_425_);
lean_dec(v_sz_425_);
v_i_boxed_429_ = lean_unbox_usize(v_i_426_);
lean_dec(v_i_426_);
v_res_430_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__3(v_sz_boxed_428_, v_i_boxed_429_, v_bs_427_);
return v_res_430_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1_spec__2(lean_object* v_msgData_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_){
_start:
{
lean_object* v___x_437_; lean_object* v_env_438_; uint8_t v___x_439_; lean_object* v_env_440_; lean_object* v___x_441_; lean_object* v_toCold_442_; lean_object* v_mctx_443_; lean_object* v_lctx_444_; lean_object* v_options_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; 
v___x_437_ = lean_st_ref_get(v___y_435_);
v_env_438_ = lean_ctor_get(v___x_437_, 0);
lean_inc_ref(v_env_438_);
lean_dec(v___x_437_);
v___x_439_ = 0;
v_env_440_ = l_Lean_Environment_setRecordingDeps(v_env_438_, v___x_439_);
v___x_441_ = lean_st_ref_get(v___y_433_);
v_toCold_442_ = lean_ctor_get(v___y_434_, 0);
v_mctx_443_ = lean_ctor_get(v___x_441_, 0);
lean_inc_ref(v_mctx_443_);
lean_dec(v___x_441_);
v_lctx_444_ = lean_ctor_get(v___y_432_, 2);
v_options_445_ = lean_ctor_get(v_toCold_442_, 2);
lean_inc_ref(v_options_445_);
lean_inc_ref(v_lctx_444_);
v___x_446_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_446_, 0, v_env_440_);
lean_ctor_set(v___x_446_, 1, v_mctx_443_);
lean_ctor_set(v___x_446_, 2, v_lctx_444_);
lean_ctor_set(v___x_446_, 3, v_options_445_);
v___x_447_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_447_, 0, v___x_446_);
lean_ctor_set(v___x_447_, 1, v_msgData_431_);
v___x_448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_448_, 0, v___x_447_);
return v___x_448_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1_spec__2___boxed(lean_object* v_msgData_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_){
_start:
{
lean_object* v_res_455_; 
v_res_455_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1_spec__2(v_msgData_449_, v___y_450_, v___y_451_, v___y_452_, v___y_453_);
lean_dec(v___y_453_);
lean_dec_ref(v___y_452_);
lean_dec(v___y_451_);
lean_dec_ref(v___y_450_);
return v_res_455_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1___closed__0(void){
_start:
{
lean_object* v___x_456_; double v___x_457_; 
v___x_456_ = lean_unsigned_to_nat(0u);
v___x_457_ = lean_float_of_nat(v___x_456_);
return v___x_457_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1(lean_object* v_cls_461_, lean_object* v_msg_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_){
_start:
{
lean_object* v_ref_468_; lean_object* v___x_469_; lean_object* v_a_470_; lean_object* v___x_472_; uint8_t v_isShared_473_; uint8_t v_isSharedCheck_515_; 
v_ref_468_ = lean_ctor_get(v___y_465_, 2);
v___x_469_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1_spec__2(v_msg_462_, v___y_463_, v___y_464_, v___y_465_, v___y_466_);
v_a_470_ = lean_ctor_get(v___x_469_, 0);
v_isSharedCheck_515_ = !lean_is_exclusive(v___x_469_);
if (v_isSharedCheck_515_ == 0)
{
v___x_472_ = v___x_469_;
v_isShared_473_ = v_isSharedCheck_515_;
goto v_resetjp_471_;
}
else
{
lean_inc(v_a_470_);
lean_dec(v___x_469_);
v___x_472_ = lean_box(0);
v_isShared_473_ = v_isSharedCheck_515_;
goto v_resetjp_471_;
}
v_resetjp_471_:
{
lean_object* v___x_474_; lean_object* v_traceState_475_; lean_object* v_env_476_; lean_object* v_nextMacroScope_477_; lean_object* v_ngen_478_; lean_object* v_auxDeclNGen_479_; lean_object* v_cache_480_; lean_object* v_recordedDeps_481_; lean_object* v_messages_482_; lean_object* v_infoState_483_; lean_object* v_snapshotTasks_484_; lean_object* v___x_486_; uint8_t v_isShared_487_; uint8_t v_isSharedCheck_514_; 
v___x_474_ = lean_st_ref_take(v___y_466_);
v_traceState_475_ = lean_ctor_get(v___x_474_, 4);
v_env_476_ = lean_ctor_get(v___x_474_, 0);
v_nextMacroScope_477_ = lean_ctor_get(v___x_474_, 1);
v_ngen_478_ = lean_ctor_get(v___x_474_, 2);
v_auxDeclNGen_479_ = lean_ctor_get(v___x_474_, 3);
v_cache_480_ = lean_ctor_get(v___x_474_, 5);
v_recordedDeps_481_ = lean_ctor_get(v___x_474_, 6);
v_messages_482_ = lean_ctor_get(v___x_474_, 7);
v_infoState_483_ = lean_ctor_get(v___x_474_, 8);
v_snapshotTasks_484_ = lean_ctor_get(v___x_474_, 9);
v_isSharedCheck_514_ = !lean_is_exclusive(v___x_474_);
if (v_isSharedCheck_514_ == 0)
{
v___x_486_ = v___x_474_;
v_isShared_487_ = v_isSharedCheck_514_;
goto v_resetjp_485_;
}
else
{
lean_inc(v_snapshotTasks_484_);
lean_inc(v_infoState_483_);
lean_inc(v_messages_482_);
lean_inc(v_recordedDeps_481_);
lean_inc(v_cache_480_);
lean_inc(v_traceState_475_);
lean_inc(v_auxDeclNGen_479_);
lean_inc(v_ngen_478_);
lean_inc(v_nextMacroScope_477_);
lean_inc(v_env_476_);
lean_dec(v___x_474_);
v___x_486_ = lean_box(0);
v_isShared_487_ = v_isSharedCheck_514_;
goto v_resetjp_485_;
}
v_resetjp_485_:
{
uint64_t v_tid_488_; lean_object* v_traces_489_; lean_object* v___x_491_; uint8_t v_isShared_492_; uint8_t v_isSharedCheck_513_; 
v_tid_488_ = lean_ctor_get_uint64(v_traceState_475_, sizeof(void*)*1);
v_traces_489_ = lean_ctor_get(v_traceState_475_, 0);
v_isSharedCheck_513_ = !lean_is_exclusive(v_traceState_475_);
if (v_isSharedCheck_513_ == 0)
{
v___x_491_ = v_traceState_475_;
v_isShared_492_ = v_isSharedCheck_513_;
goto v_resetjp_490_;
}
else
{
lean_inc(v_traces_489_);
lean_dec(v_traceState_475_);
v___x_491_ = lean_box(0);
v_isShared_492_ = v_isSharedCheck_513_;
goto v_resetjp_490_;
}
v_resetjp_490_:
{
lean_object* v___x_493_; lean_object* v___x_494_; double v___x_495_; uint8_t v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_504_; 
v___x_493_ = lean_box(0);
v___x_494_ = lean_box(0);
v___x_495_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1___closed__0);
v___x_496_ = 0;
v___x_497_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1___closed__1));
v___x_498_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_498_, 0, v_cls_461_);
lean_ctor_set(v___x_498_, 1, v___x_494_);
lean_ctor_set(v___x_498_, 2, v___x_497_);
lean_ctor_set_float(v___x_498_, sizeof(void*)*3, v___x_495_);
lean_ctor_set_float(v___x_498_, sizeof(void*)*3 + 8, v___x_495_);
lean_ctor_set_uint8(v___x_498_, sizeof(void*)*3 + 16, v___x_496_);
v___x_499_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1___closed__2));
v___x_500_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_500_, 0, v___x_498_);
lean_ctor_set(v___x_500_, 1, v_a_470_);
lean_ctor_set(v___x_500_, 2, v___x_499_);
lean_inc(v_ref_468_);
v___x_501_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_501_, 0, v_ref_468_);
lean_ctor_set(v___x_501_, 1, v___x_500_);
v___x_502_ = l_Lean_PersistentArray_push___redArg(v_traces_489_, v___x_501_);
if (v_isShared_492_ == 0)
{
lean_ctor_set(v___x_491_, 0, v___x_502_);
v___x_504_ = v___x_491_;
goto v_reusejp_503_;
}
else
{
lean_object* v_reuseFailAlloc_512_; 
v_reuseFailAlloc_512_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_512_, 0, v___x_502_);
lean_ctor_set_uint64(v_reuseFailAlloc_512_, sizeof(void*)*1, v_tid_488_);
v___x_504_ = v_reuseFailAlloc_512_;
goto v_reusejp_503_;
}
v_reusejp_503_:
{
lean_object* v___x_506_; 
if (v_isShared_487_ == 0)
{
lean_ctor_set(v___x_486_, 4, v___x_504_);
v___x_506_ = v___x_486_;
goto v_reusejp_505_;
}
else
{
lean_object* v_reuseFailAlloc_511_; 
v_reuseFailAlloc_511_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_511_, 0, v_env_476_);
lean_ctor_set(v_reuseFailAlloc_511_, 1, v_nextMacroScope_477_);
lean_ctor_set(v_reuseFailAlloc_511_, 2, v_ngen_478_);
lean_ctor_set(v_reuseFailAlloc_511_, 3, v_auxDeclNGen_479_);
lean_ctor_set(v_reuseFailAlloc_511_, 4, v___x_504_);
lean_ctor_set(v_reuseFailAlloc_511_, 5, v_cache_480_);
lean_ctor_set(v_reuseFailAlloc_511_, 6, v_recordedDeps_481_);
lean_ctor_set(v_reuseFailAlloc_511_, 7, v_messages_482_);
lean_ctor_set(v_reuseFailAlloc_511_, 8, v_infoState_483_);
lean_ctor_set(v_reuseFailAlloc_511_, 9, v_snapshotTasks_484_);
v___x_506_ = v_reuseFailAlloc_511_;
goto v_reusejp_505_;
}
v_reusejp_505_:
{
lean_object* v___x_507_; lean_object* v___x_509_; 
v___x_507_ = lean_st_ref_put(v___y_466_, v___x_506_);
if (v_isShared_473_ == 0)
{
lean_ctor_set(v___x_472_, 0, v___x_493_);
v___x_509_ = v___x_472_;
goto v_reusejp_508_;
}
else
{
lean_object* v_reuseFailAlloc_510_; 
v_reuseFailAlloc_510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_510_, 0, v___x_493_);
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
lean_object* v___y_575_; lean_object* v___y_576_; lean_object* v___y_577_; lean_object* v___y_578_; lean_object* v___x_631_; 
v___x_631_ = l_Lean_Meta_whnfForall(v_recursorType_566_, v_a_569_, v_a_570_, v_a_571_, v_a_572_);
if (lean_obj_tag(v___x_631_) == 0)
{
lean_object* v_a_632_; uint8_t v___x_645_; 
v_a_632_ = lean_ctor_get(v___x_631_, 0);
lean_inc(v_a_632_);
lean_dec_ref_known(v___x_631_, 1);
v___x_645_ = l_Lean_Expr_isForall(v_a_632_);
if (v___x_645_ == 0)
{
lean_dec(v_a_632_);
lean_dec(v_minorIdx_564_);
lean_dec(v_pos_563_);
lean_dec(v_baseSubst_560_);
lean_dec_ref(v_major_558_);
goto v___jp_633_;
}
else
{
lean_object* v_numArgs_646_; uint8_t v___x_647_; lean_object* v___y_649_; lean_object* v___y_650_; lean_object* v___y_651_; lean_object* v___y_652_; lean_object* v___y_653_; uint8_t v___y_654_; lean_object* v___y_655_; lean_object* v___y_656_; lean_object* v___y_657_; lean_object* v___y_658_; lean_object* v___y_659_; lean_object* v___y_660_; lean_object* v___y_661_; lean_object* v___y_662_; uint8_t v___y_663_; lean_object* v___y_699_; lean_object* v___y_700_; lean_object* v___y_701_; lean_object* v___y_702_; lean_object* v___y_703_; lean_object* v___y_704_; lean_object* v___y_705_; lean_object* v___y_706_; lean_object* v___y_707_; uint8_t v___y_708_; lean_object* v___y_709_; lean_object* v___y_710_; lean_object* v___y_711_; lean_object* v___y_712_; lean_object* v___y_730_; lean_object* v___y_731_; lean_object* v___y_732_; uint8_t v___y_733_; lean_object* v___y_734_; lean_object* v___y_735_; lean_object* v___y_736_; lean_object* v___y_737_; lean_object* v___y_738_; lean_object* v___y_739_; lean_object* v___y_740_; lean_object* v___y_741_; lean_object* v___y_742_; lean_object* v___y_786_; lean_object* v___y_787_; lean_object* v___y_788_; uint8_t v___y_789_; lean_object* v___y_790_; lean_object* v___y_791_; lean_object* v___y_792_; lean_object* v___y_793_; lean_object* v___y_794_; lean_object* v___y_806_; lean_object* v___y_807_; lean_object* v___y_808_; lean_object* v___y_809_; lean_object* v___y_810_; lean_object* v___y_811_; lean_object* v___y_812_; uint8_t v___y_813_; uint8_t v___y_828_; lean_object* v___y_829_; lean_object* v___y_830_; lean_object* v___y_831_; lean_object* v___y_832_; lean_object* v___y_833_; lean_object* v___y_834_; lean_object* v___y_835_; 
v_numArgs_646_ = lean_ctor_get(v_recursorInfo_556_, 3);
v___x_647_ = lean_nat_dec_lt(v_pos_563_, v_numArgs_646_);
if (v___x_647_ == 0)
{
lean_dec(v_a_632_);
lean_dec(v_minorIdx_564_);
lean_dec(v_pos_563_);
lean_dec(v_baseSubst_560_);
lean_dec_ref(v_major_558_);
goto v___jp_633_;
}
else
{
lean_object* v___x_895_; uint8_t v___x_896_; 
v___x_895_ = l_Lean_Meta_RecursorInfo_firstIndexPos(v_recursorInfo_556_);
v___x_896_ = lean_nat_dec_eq(v_pos_563_, v___x_895_);
lean_dec(v___x_895_);
if (v___x_896_ == 0)
{
lean_object* v___x_897_; 
lean_inc(v_mvarId_554_);
v___x_897_ = l_Lean_MVarId_getTag(v_mvarId_554_, v_a_569_, v_a_570_, v_a_571_, v_a_572_);
if (lean_obj_tag(v___x_897_) == 0)
{
lean_object* v_a_898_; lean_object* v___y_900_; lean_object* v___y_901_; lean_object* v___y_902_; lean_object* v___y_903_; uint8_t v___x_914_; 
v_a_898_ = lean_ctor_get(v___x_897_, 0);
lean_inc(v_a_898_);
lean_dec_ref_known(v___x_897_, 1);
v___x_914_ = lean_nat_dec_le(v_numMinors_562_, v_minorIdx_564_);
if (v___x_914_ == 0)
{
v___y_900_ = v_a_569_;
v___y_901_ = v_a_570_;
v___y_902_ = v_a_571_;
v___y_903_ = v_a_572_;
goto v___jp_899_;
}
else
{
lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; 
v___x_915_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1));
v___x_916_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9);
lean_inc(v_mvarId_554_);
v___x_917_ = l_Lean_Meta_throwTacticEx___redArg(v___x_915_, v_mvarId_554_, v___x_916_, v_a_569_, v_a_570_, v_a_571_, v_a_572_);
if (lean_obj_tag(v___x_917_) == 0)
{
lean_dec_ref_known(v___x_917_, 1);
v___y_900_ = v_a_569_;
v___y_901_ = v_a_570_;
v___y_902_ = v_a_571_;
v___y_903_ = v_a_572_;
goto v___jp_899_;
}
else
{
lean_object* v_a_918_; lean_object* v___x_920_; uint8_t v_isShared_921_; uint8_t v_isSharedCheck_925_; 
lean_dec(v_a_898_);
lean_dec(v_a_632_);
lean_dec_ref(v_subgoals_568_);
lean_dec_ref(v_recursor_565_);
lean_dec(v_minorIdx_564_);
lean_dec(v_pos_563_);
lean_dec(v_baseSubst_560_);
lean_dec_ref(v_major_558_);
lean_dec(v_mvarId_554_);
v_a_918_ = lean_ctor_get(v___x_917_, 0);
v_isSharedCheck_925_ = !lean_is_exclusive(v___x_917_);
if (v_isSharedCheck_925_ == 0)
{
v___x_920_ = v___x_917_;
v_isShared_921_ = v_isSharedCheck_925_;
goto v_resetjp_919_;
}
else
{
lean_inc(v_a_918_);
lean_dec(v___x_917_);
v___x_920_ = lean_box(0);
v_isShared_921_ = v_isSharedCheck_925_;
goto v_resetjp_919_;
}
v_resetjp_919_:
{
lean_object* v___x_923_; 
if (v_isShared_921_ == 0)
{
v___x_923_ = v___x_920_;
goto v_reusejp_922_;
}
else
{
lean_object* v_reuseFailAlloc_924_; 
v_reuseFailAlloc_924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_924_, 0, v_a_918_);
v___x_923_ = v_reuseFailAlloc_924_;
goto v_reusejp_922_;
}
v_reusejp_922_:
{
return v___x_923_;
}
}
}
}
v___jp_899_:
{
if (lean_obj_tag(v_a_632_) == 7)
{
lean_object* v_binderName_904_; lean_object* v_binderType_905_; uint8_t v_binderInfo_906_; lean_object* v___x_907_; lean_object* v___x_908_; uint8_t v___x_909_; 
v_binderName_904_ = lean_ctor_get(v_a_632_, 0);
v_binderType_905_ = lean_ctor_get(v_a_632_, 1);
v_binderInfo_906_ = lean_ctor_get_uint8(v_a_632_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_905_);
v___x_907_ = l_Lean_Expr_headBeta(v_binderType_905_);
v___x_908_ = lean_unsigned_to_nat(1u);
v___x_909_ = lean_nat_dec_eq(v_numMinors_562_, v___x_908_);
if (v___x_909_ == 0)
{
lean_object* v___x_910_; lean_object* v___x_911_; 
v___x_910_ = l_Lean_Name_eraseMacroScopes(v_binderName_904_);
v___x_911_ = l_Lean_Name_append(v_a_898_, v___x_910_);
v___y_828_ = v_binderInfo_906_;
v___y_829_ = v___x_907_;
v___y_830_ = v___y_901_;
v___y_831_ = v___y_902_;
v___y_832_ = v___x_908_;
v___y_833_ = v___y_900_;
v___y_834_ = v___y_903_;
v___y_835_ = v___x_911_;
goto v___jp_827_;
}
else
{
v___y_828_ = v_binderInfo_906_;
v___y_829_ = v___x_907_;
v___y_830_ = v___y_901_;
v___y_831_ = v___y_902_;
v___y_832_ = v___x_908_;
v___y_833_ = v___y_900_;
v___y_834_ = v___y_903_;
v___y_835_ = v_a_898_;
goto v___jp_827_;
}
}
else
{
lean_object* v___x_912_; lean_object* v___x_913_; 
lean_dec(v_a_898_);
lean_dec(v_a_632_);
lean_dec_ref(v_subgoals_568_);
lean_dec_ref(v_recursor_565_);
lean_dec(v_minorIdx_564_);
lean_dec(v_pos_563_);
lean_dec(v_baseSubst_560_);
lean_dec_ref(v_major_558_);
lean_dec(v_mvarId_554_);
v___x_912_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__15, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__15_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__15);
v___x_913_ = l_panic___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__4(v___x_912_, v___y_900_, v___y_901_, v___y_902_, v___y_903_);
return v___x_913_;
}
}
}
else
{
lean_object* v_a_926_; lean_object* v___x_928_; uint8_t v_isShared_929_; uint8_t v_isSharedCheck_933_; 
lean_dec(v_a_632_);
lean_dec_ref(v_subgoals_568_);
lean_dec_ref(v_recursor_565_);
lean_dec(v_minorIdx_564_);
lean_dec(v_pos_563_);
lean_dec(v_baseSubst_560_);
lean_dec_ref(v_major_558_);
lean_dec(v_mvarId_554_);
v_a_926_ = lean_ctor_get(v___x_897_, 0);
v_isSharedCheck_933_ = !lean_is_exclusive(v___x_897_);
if (v_isSharedCheck_933_ == 0)
{
v___x_928_ = v___x_897_;
v_isShared_929_ = v_isSharedCheck_933_;
goto v_resetjp_927_;
}
else
{
lean_inc(v_a_926_);
lean_dec(v___x_897_);
v___x_928_ = lean_box(0);
v_isShared_929_ = v_isSharedCheck_933_;
goto v_resetjp_927_;
}
v_resetjp_927_:
{
lean_object* v___x_931_; 
if (v_isShared_929_ == 0)
{
v___x_931_ = v___x_928_;
goto v_reusejp_930_;
}
else
{
lean_object* v_reuseFailAlloc_932_; 
v_reuseFailAlloc_932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_932_, 0, v_a_926_);
v___x_931_ = v_reuseFailAlloc_932_;
goto v_reusejp_930_;
}
v_reusejp_930_:
{
return v___x_931_;
}
}
}
}
else
{
lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v_fst_937_; lean_object* v_snd_938_; uint8_t v___x_954_; 
v___x_934_ = lean_unsigned_to_nat(0u);
v___x_935_ = lean_array_get_size(v_indices_559_);
v___x_954_ = lean_nat_dec_lt(v___x_934_, v___x_935_);
if (v___x_954_ == 0)
{
v_fst_937_ = v_recursor_565_;
v_snd_938_ = v_a_632_;
goto v___jp_936_;
}
else
{
lean_object* v___x_955_; size_t v___x_956_; size_t v___x_957_; lean_object* v___x_958_; 
v___x_955_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_955_, 0, v_recursor_565_);
lean_ctor_set(v___x_955_, 1, v_a_632_);
v___x_956_ = ((size_t)0ULL);
v___x_957_ = lean_usize_of_nat(v___x_935_);
lean_inc(v_mvarId_554_);
v___x_958_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__5(v_mvarId_554_, v_indices_559_, v___x_956_, v___x_957_, v___x_955_, v_a_569_, v_a_570_, v_a_571_, v_a_572_);
if (lean_obj_tag(v___x_958_) == 0)
{
lean_object* v_a_959_; lean_object* v_fst_960_; lean_object* v_snd_961_; 
v_a_959_ = lean_ctor_get(v___x_958_, 0);
lean_inc(v_a_959_);
lean_dec_ref_known(v___x_958_, 1);
v_fst_960_ = lean_ctor_get(v_a_959_, 0);
lean_inc(v_fst_960_);
v_snd_961_ = lean_ctor_get(v_a_959_, 1);
lean_inc(v_snd_961_);
lean_dec(v_a_959_);
v_fst_937_ = v_fst_960_;
v_snd_938_ = v_snd_961_;
goto v___jp_936_;
}
else
{
lean_object* v_a_962_; lean_object* v___x_964_; uint8_t v_isShared_965_; uint8_t v_isSharedCheck_969_; 
lean_dec_ref(v_subgoals_568_);
lean_dec(v_minorIdx_564_);
lean_dec(v_pos_563_);
lean_dec(v_baseSubst_560_);
lean_dec_ref(v_major_558_);
lean_dec(v_mvarId_554_);
v_a_962_ = lean_ctor_get(v___x_958_, 0);
v_isSharedCheck_969_ = !lean_is_exclusive(v___x_958_);
if (v_isSharedCheck_969_ == 0)
{
v___x_964_ = v___x_958_;
v_isShared_965_ = v_isSharedCheck_969_;
goto v_resetjp_963_;
}
else
{
lean_inc(v_a_962_);
lean_dec(v___x_958_);
v___x_964_ = lean_box(0);
v_isShared_965_ = v_isSharedCheck_969_;
goto v_resetjp_963_;
}
v_resetjp_963_:
{
lean_object* v___x_967_; 
if (v_isShared_965_ == 0)
{
v___x_967_ = v___x_964_;
goto v_reusejp_966_;
}
else
{
lean_object* v_reuseFailAlloc_968_; 
v_reuseFailAlloc_968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_968_, 0, v_a_962_);
v___x_967_ = v_reuseFailAlloc_968_;
goto v_reusejp_966_;
}
v_reusejp_966_:
{
return v___x_967_;
}
}
}
}
v___jp_936_:
{
lean_object* v___x_939_; lean_object* v___x_940_; 
lean_inc_ref(v_major_558_);
v___x_939_ = l_Lean_Expr_app___override(v_fst_937_, v_major_558_);
lean_inc(v_mvarId_554_);
v___x_940_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTypeBody(v_mvarId_554_, v_snd_938_, v_major_558_, v_a_569_, v_a_570_, v_a_571_, v_a_572_);
if (lean_obj_tag(v___x_940_) == 0)
{
lean_object* v_a_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; 
v_a_941_ = lean_ctor_get(v___x_940_, 0);
lean_inc(v_a_941_);
lean_dec_ref_known(v___x_940_, 1);
v___x_942_ = lean_unsigned_to_nat(1u);
v___x_943_ = lean_nat_add(v_pos_563_, v___x_942_);
lean_dec(v_pos_563_);
v___x_944_ = lean_nat_add(v___x_943_, v___x_935_);
lean_dec(v___x_943_);
v_pos_563_ = v___x_944_;
v_recursor_565_ = v___x_939_;
v_recursorType_566_ = v_a_941_;
v_consumedMajor_567_ = v___x_645_;
goto _start;
}
else
{
lean_object* v_a_946_; lean_object* v___x_948_; uint8_t v_isShared_949_; uint8_t v_isSharedCheck_953_; 
lean_dec_ref(v___x_939_);
lean_dec_ref(v_subgoals_568_);
lean_dec(v_minorIdx_564_);
lean_dec(v_pos_563_);
lean_dec(v_baseSubst_560_);
lean_dec_ref(v_major_558_);
lean_dec(v_mvarId_554_);
v_a_946_ = lean_ctor_get(v___x_940_, 0);
v_isSharedCheck_953_ = !lean_is_exclusive(v___x_940_);
if (v_isSharedCheck_953_ == 0)
{
v___x_948_ = v___x_940_;
v_isShared_949_ = v_isSharedCheck_953_;
goto v_resetjp_947_;
}
else
{
lean_inc(v_a_946_);
lean_dec(v___x_940_);
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
}
}
v___jp_648_:
{
lean_object* v___x_664_; 
v___x_664_ = l_Lean_Meta_introNCore(v___y_652_, v___y_655_, v___y_657_, v___y_663_, v___y_654_, v___y_660_, v___y_658_, v___y_649_, v___y_659_);
if (lean_obj_tag(v___x_664_) == 0)
{
lean_object* v_a_665_; lean_object* v_fst_666_; lean_object* v_snd_667_; lean_object* v___x_668_; lean_object* v___x_669_; 
v_a_665_ = lean_ctor_get(v___x_664_, 0);
lean_inc(v_a_665_);
lean_dec_ref_known(v___x_664_, 1);
v_fst_666_ = lean_ctor_get(v_a_665_, 0);
lean_inc(v_fst_666_);
v_snd_667_ = lean_ctor_get(v_a_665_, 1);
lean_inc(v_snd_667_);
lean_dec(v_a_665_);
v___x_668_ = lean_box(0);
v___x_669_ = l_Lean_Meta_introNCore(v_snd_667_, v___y_651_, v___x_668_, v___y_654_, v___x_647_, v___y_660_, v___y_658_, v___y_649_, v___y_659_);
if (lean_obj_tag(v___x_669_) == 0)
{
lean_object* v_a_670_; lean_object* v_fst_671_; lean_object* v_snd_672_; lean_object* v___x_673_; size_t v_sz_674_; size_t v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; 
v_a_670_ = lean_ctor_get(v___x_669_, 0);
lean_inc(v_a_670_);
lean_dec_ref_known(v___x_669_, 1);
v_fst_671_ = lean_ctor_get(v_a_670_, 0);
lean_inc(v_fst_671_);
v_snd_672_ = lean_ctor_get(v_a_670_, 1);
lean_inc(v_snd_672_);
lean_dec(v_a_670_);
lean_inc(v_baseSubst_560_);
lean_inc(v___y_656_);
v___x_673_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__2___redArg(v___y_650_, v_reverted_557_, v_fst_671_, v___y_656_, v___y_656_, v_baseSubst_560_);
lean_dec(v___y_656_);
lean_dec(v_fst_671_);
lean_dec(v___y_650_);
v_sz_674_ = lean_array_size(v_fst_666_);
v___x_675_ = ((size_t)0ULL);
v___x_676_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__3(v_sz_674_, v___x_675_, v_fst_666_);
v___x_677_ = lean_nat_add(v_pos_563_, v___y_661_);
lean_dec(v_pos_563_);
v___x_678_ = lean_nat_add(v_minorIdx_564_, v___y_661_);
lean_dec(v_minorIdx_564_);
v___x_679_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_679_, 0, v_snd_672_);
lean_ctor_set(v___x_679_, 1, v___x_676_);
lean_ctor_set(v___x_679_, 2, v___x_673_);
v___x_680_ = lean_array_push(v_subgoals_568_, v___x_679_);
v_pos_563_ = v___x_677_;
v_minorIdx_564_ = v___x_678_;
v_recursor_565_ = v___y_653_;
v_recursorType_566_ = v___y_662_;
v_subgoals_568_ = v___x_680_;
v_a_569_ = v___y_660_;
v_a_570_ = v___y_658_;
v_a_571_ = v___y_649_;
v_a_572_ = v___y_659_;
goto _start;
}
else
{
lean_object* v_a_682_; lean_object* v___x_684_; uint8_t v_isShared_685_; uint8_t v_isSharedCheck_689_; 
lean_dec(v_fst_666_);
lean_dec_ref(v___y_662_);
lean_dec(v___y_656_);
lean_dec_ref(v___y_653_);
lean_dec(v___y_650_);
lean_dec_ref(v_subgoals_568_);
lean_dec(v_minorIdx_564_);
lean_dec(v_pos_563_);
lean_dec(v_baseSubst_560_);
lean_dec_ref(v_major_558_);
lean_dec(v_mvarId_554_);
v_a_682_ = lean_ctor_get(v___x_669_, 0);
v_isSharedCheck_689_ = !lean_is_exclusive(v___x_669_);
if (v_isSharedCheck_689_ == 0)
{
v___x_684_ = v___x_669_;
v_isShared_685_ = v_isSharedCheck_689_;
goto v_resetjp_683_;
}
else
{
lean_inc(v_a_682_);
lean_dec(v___x_669_);
v___x_684_ = lean_box(0);
v_isShared_685_ = v_isSharedCheck_689_;
goto v_resetjp_683_;
}
v_resetjp_683_:
{
lean_object* v___x_687_; 
if (v_isShared_685_ == 0)
{
v___x_687_ = v___x_684_;
goto v_reusejp_686_;
}
else
{
lean_object* v_reuseFailAlloc_688_; 
v_reuseFailAlloc_688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_688_, 0, v_a_682_);
v___x_687_ = v_reuseFailAlloc_688_;
goto v_reusejp_686_;
}
v_reusejp_686_:
{
return v___x_687_;
}
}
}
}
else
{
lean_object* v_a_690_; lean_object* v___x_692_; uint8_t v_isShared_693_; uint8_t v_isSharedCheck_697_; 
lean_dec_ref(v___y_662_);
lean_dec(v___y_656_);
lean_dec_ref(v___y_653_);
lean_dec(v___y_651_);
lean_dec(v___y_650_);
lean_dec_ref(v_subgoals_568_);
lean_dec(v_minorIdx_564_);
lean_dec(v_pos_563_);
lean_dec(v_baseSubst_560_);
lean_dec_ref(v_major_558_);
lean_dec(v_mvarId_554_);
v_a_690_ = lean_ctor_get(v___x_664_, 0);
v_isSharedCheck_697_ = !lean_is_exclusive(v___x_664_);
if (v_isSharedCheck_697_ == 0)
{
v___x_692_ = v___x_664_;
v_isShared_693_ = v_isSharedCheck_697_;
goto v_resetjp_691_;
}
else
{
lean_inc(v_a_690_);
lean_dec(v___x_664_);
v___x_692_ = lean_box(0);
v_isShared_693_ = v_isSharedCheck_697_;
goto v_resetjp_691_;
}
v_resetjp_691_:
{
lean_object* v___x_695_; 
if (v_isShared_693_ == 0)
{
v___x_695_ = v___x_692_;
goto v_reusejp_694_;
}
else
{
lean_object* v_reuseFailAlloc_696_; 
v_reuseFailAlloc_696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_696_, 0, v_a_690_);
v___x_695_ = v_reuseFailAlloc_696_;
goto v_reusejp_694_;
}
v_reusejp_694_:
{
return v___x_695_;
}
}
}
}
v___jp_698_:
{
lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; 
v___x_713_ = l_Lean_Expr_mvarId_x21(v___y_701_);
lean_dec_ref(v___y_701_);
v___x_714_ = l_Lean_Expr_fvarId_x21(v_major_558_);
v___x_715_ = l_Lean_MVarId_tryClear(v___x_713_, v___x_714_, v___y_709_, v___y_710_, v___y_711_, v___y_712_);
if (lean_obj_tag(v___x_715_) == 0)
{
uint8_t v_explicit_716_; 
v_explicit_716_ = lean_ctor_get_uint8(v___y_705_, sizeof(void*)*1);
if (v_explicit_716_ == 0)
{
lean_object* v_a_717_; lean_object* v_varNames_718_; 
v_a_717_ = lean_ctor_get(v___x_715_, 0);
lean_inc(v_a_717_);
lean_dec_ref_known(v___x_715_, 1);
v_varNames_718_ = lean_ctor_get(v___y_705_, 0);
lean_inc(v_varNames_718_);
lean_dec_ref(v___y_705_);
v___y_649_ = v___y_711_;
v___y_650_ = v___y_702_;
v___y_651_ = v___y_704_;
v___y_652_ = v_a_717_;
v___y_653_ = v___y_706_;
v___y_654_ = v___y_708_;
v___y_655_ = v___y_700_;
v___y_656_ = v___y_699_;
v___y_657_ = v_varNames_718_;
v___y_658_ = v___y_710_;
v___y_659_ = v___y_712_;
v___y_660_ = v___y_709_;
v___y_661_ = v___y_703_;
v___y_662_ = v___y_707_;
v___y_663_ = v___x_647_;
goto v___jp_648_;
}
else
{
lean_object* v_a_719_; lean_object* v_varNames_720_; 
v_a_719_ = lean_ctor_get(v___x_715_, 0);
lean_inc(v_a_719_);
lean_dec_ref_known(v___x_715_, 1);
v_varNames_720_ = lean_ctor_get(v___y_705_, 0);
lean_inc(v_varNames_720_);
lean_dec_ref(v___y_705_);
v___y_649_ = v___y_711_;
v___y_650_ = v___y_702_;
v___y_651_ = v___y_704_;
v___y_652_ = v_a_719_;
v___y_653_ = v___y_706_;
v___y_654_ = v___y_708_;
v___y_655_ = v___y_700_;
v___y_656_ = v___y_699_;
v___y_657_ = v_varNames_720_;
v___y_658_ = v___y_710_;
v___y_659_ = v___y_712_;
v___y_660_ = v___y_709_;
v___y_661_ = v___y_703_;
v___y_662_ = v___y_707_;
v___y_663_ = v___y_708_;
goto v___jp_648_;
}
}
else
{
lean_object* v_a_721_; lean_object* v___x_723_; uint8_t v_isShared_724_; uint8_t v_isSharedCheck_728_; 
lean_dec_ref(v___y_707_);
lean_dec_ref(v___y_706_);
lean_dec_ref(v___y_705_);
lean_dec(v___y_704_);
lean_dec(v___y_702_);
lean_dec(v___y_700_);
lean_dec(v___y_699_);
lean_dec_ref(v_subgoals_568_);
lean_dec(v_minorIdx_564_);
lean_dec(v_pos_563_);
lean_dec(v_baseSubst_560_);
lean_dec_ref(v_major_558_);
lean_dec(v_mvarId_554_);
v_a_721_ = lean_ctor_get(v___x_715_, 0);
v_isSharedCheck_728_ = !lean_is_exclusive(v___x_715_);
if (v_isSharedCheck_728_ == 0)
{
v___x_723_ = v___x_715_;
v_isShared_724_ = v_isSharedCheck_728_;
goto v_resetjp_722_;
}
else
{
lean_inc(v_a_721_);
lean_dec(v___x_715_);
v___x_723_ = lean_box(0);
v_isShared_724_ = v_isSharedCheck_728_;
goto v_resetjp_722_;
}
v_resetjp_722_:
{
lean_object* v___x_726_; 
if (v_isShared_724_ == 0)
{
v___x_726_ = v___x_723_;
goto v_reusejp_725_;
}
else
{
lean_object* v_reuseFailAlloc_727_; 
v_reuseFailAlloc_727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_727_, 0, v_a_721_);
v___x_726_ = v_reuseFailAlloc_727_;
goto v_reusejp_725_;
}
v_reusejp_725_:
{
return v___x_726_;
}
}
}
}
v___jp_729_:
{
lean_object* v___x_743_; 
v___x_743_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___y_735_, v___y_734_, v___y_738_, v___y_741_, v___y_740_, v___y_732_);
if (lean_obj_tag(v___x_743_) == 0)
{
lean_object* v_a_744_; lean_object* v___x_745_; lean_object* v___x_746_; 
v_a_744_ = lean_ctor_get(v___x_743_, 0);
lean_inc_n(v_a_744_, 2);
lean_dec_ref_known(v___x_743_, 1);
v___x_745_ = l_Lean_Expr_app___override(v_recursor_565_, v_a_744_);
lean_inc(v_mvarId_554_);
v___x_746_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTypeBody(v_mvarId_554_, v_a_632_, v_a_744_, v___y_738_, v___y_741_, v___y_740_, v___y_732_);
if (lean_obj_tag(v___x_746_) == 0)
{
lean_object* v_toCold_747_; lean_object* v_options_748_; uint8_t v_hasTrace_749_; 
v_toCold_747_ = lean_ctor_get(v___y_740_, 0);
v_options_748_ = lean_ctor_get(v_toCold_747_, 2);
v_hasTrace_749_ = lean_ctor_get_uint8(v_options_748_, sizeof(void*)*1);
if (v_hasTrace_749_ == 0)
{
lean_object* v_a_750_; 
v_a_750_ = lean_ctor_get(v___x_746_, 0);
lean_inc(v_a_750_);
lean_dec_ref_known(v___x_746_, 1);
v___y_699_ = v___y_736_;
v___y_700_ = v___y_737_;
v___y_701_ = v_a_744_;
v___y_702_ = v___y_730_;
v___y_703_ = v___y_739_;
v___y_704_ = v___y_731_;
v___y_705_ = v___y_742_;
v___y_706_ = v___x_745_;
v___y_707_ = v_a_750_;
v___y_708_ = v___y_733_;
v___y_709_ = v___y_738_;
v___y_710_ = v___y_741_;
v___y_711_ = v___y_740_;
v___y_712_ = v___y_732_;
goto v___jp_698_;
}
else
{
lean_object* v_a_751_; lean_object* v_inheritedTraceOptions_752_; lean_object* v___x_753_; lean_object* v___x_754_; uint8_t v___x_755_; 
v_a_751_ = lean_ctor_get(v___x_746_, 0);
lean_inc(v_a_751_);
lean_dec_ref_known(v___x_746_, 1);
v_inheritedTraceOptions_752_ = lean_ctor_get(v_toCold_747_, 11);
v___x_753_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__2));
v___x_754_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5);
v___x_755_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_752_, v_options_748_, v___x_754_);
if (v___x_755_ == 0)
{
v___y_699_ = v___y_736_;
v___y_700_ = v___y_737_;
v___y_701_ = v_a_744_;
v___y_702_ = v___y_730_;
v___y_703_ = v___y_739_;
v___y_704_ = v___y_731_;
v___y_705_ = v___y_742_;
v___y_706_ = v___x_745_;
v___y_707_ = v_a_751_;
v___y_708_ = v___y_733_;
v___y_709_ = v___y_738_;
v___y_710_ = v___y_741_;
v___y_711_ = v___y_740_;
v___y_712_ = v___y_732_;
goto v___jp_698_;
}
else
{
lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; 
v___x_756_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__11, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__11_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__11);
v___x_757_ = l_Lean_Expr_fvarId_x21(v_major_558_);
v___x_758_ = l_Lean_MessageData_ofName(v___x_757_);
v___x_759_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_759_, 0, v___x_756_);
lean_ctor_set(v___x_759_, 1, v___x_758_);
v___x_760_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1(v___x_753_, v___x_759_, v___y_738_, v___y_741_, v___y_740_, v___y_732_);
if (lean_obj_tag(v___x_760_) == 0)
{
lean_dec_ref_known(v___x_760_, 1);
v___y_699_ = v___y_736_;
v___y_700_ = v___y_737_;
v___y_701_ = v_a_744_;
v___y_702_ = v___y_730_;
v___y_703_ = v___y_739_;
v___y_704_ = v___y_731_;
v___y_705_ = v___y_742_;
v___y_706_ = v___x_745_;
v___y_707_ = v_a_751_;
v___y_708_ = v___y_733_;
v___y_709_ = v___y_738_;
v___y_710_ = v___y_741_;
v___y_711_ = v___y_740_;
v___y_712_ = v___y_732_;
goto v___jp_698_;
}
else
{
lean_object* v_a_761_; lean_object* v___x_763_; uint8_t v_isShared_764_; uint8_t v_isSharedCheck_768_; 
lean_dec(v_a_751_);
lean_dec_ref(v___x_745_);
lean_dec(v_a_744_);
lean_dec_ref(v___y_742_);
lean_dec(v___y_737_);
lean_dec(v___y_736_);
lean_dec(v___y_731_);
lean_dec(v___y_730_);
lean_dec_ref(v_subgoals_568_);
lean_dec(v_minorIdx_564_);
lean_dec(v_pos_563_);
lean_dec(v_baseSubst_560_);
lean_dec_ref(v_major_558_);
lean_dec(v_mvarId_554_);
v_a_761_ = lean_ctor_get(v___x_760_, 0);
v_isSharedCheck_768_ = !lean_is_exclusive(v___x_760_);
if (v_isSharedCheck_768_ == 0)
{
v___x_763_ = v___x_760_;
v_isShared_764_ = v_isSharedCheck_768_;
goto v_resetjp_762_;
}
else
{
lean_inc(v_a_761_);
lean_dec(v___x_760_);
v___x_763_ = lean_box(0);
v_isShared_764_ = v_isSharedCheck_768_;
goto v_resetjp_762_;
}
v_resetjp_762_:
{
lean_object* v___x_766_; 
if (v_isShared_764_ == 0)
{
v___x_766_ = v___x_763_;
goto v_reusejp_765_;
}
else
{
lean_object* v_reuseFailAlloc_767_; 
v_reuseFailAlloc_767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_767_, 0, v_a_761_);
v___x_766_ = v_reuseFailAlloc_767_;
goto v_reusejp_765_;
}
v_reusejp_765_:
{
return v___x_766_;
}
}
}
}
}
}
else
{
lean_object* v_a_769_; lean_object* v___x_771_; uint8_t v_isShared_772_; uint8_t v_isSharedCheck_776_; 
lean_dec_ref(v___x_745_);
lean_dec(v_a_744_);
lean_dec_ref(v___y_742_);
lean_dec(v___y_737_);
lean_dec(v___y_736_);
lean_dec(v___y_731_);
lean_dec(v___y_730_);
lean_dec_ref(v_subgoals_568_);
lean_dec(v_minorIdx_564_);
lean_dec(v_pos_563_);
lean_dec(v_baseSubst_560_);
lean_dec_ref(v_major_558_);
lean_dec(v_mvarId_554_);
v_a_769_ = lean_ctor_get(v___x_746_, 0);
v_isSharedCheck_776_ = !lean_is_exclusive(v___x_746_);
if (v_isSharedCheck_776_ == 0)
{
v___x_771_ = v___x_746_;
v_isShared_772_ = v_isSharedCheck_776_;
goto v_resetjp_770_;
}
else
{
lean_inc(v_a_769_);
lean_dec(v___x_746_);
v___x_771_ = lean_box(0);
v_isShared_772_ = v_isSharedCheck_776_;
goto v_resetjp_770_;
}
v_resetjp_770_:
{
lean_object* v___x_774_; 
if (v_isShared_772_ == 0)
{
v___x_774_ = v___x_771_;
goto v_reusejp_773_;
}
else
{
lean_object* v_reuseFailAlloc_775_; 
v_reuseFailAlloc_775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_775_, 0, v_a_769_);
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
else
{
lean_object* v_a_777_; lean_object* v___x_779_; uint8_t v_isShared_780_; uint8_t v_isSharedCheck_784_; 
lean_dec_ref(v___y_742_);
lean_dec(v___y_737_);
lean_dec(v___y_736_);
lean_dec(v___y_731_);
lean_dec(v___y_730_);
lean_dec(v_a_632_);
lean_dec_ref(v_subgoals_568_);
lean_dec_ref(v_recursor_565_);
lean_dec(v_minorIdx_564_);
lean_dec(v_pos_563_);
lean_dec(v_baseSubst_560_);
lean_dec_ref(v_major_558_);
lean_dec(v_mvarId_554_);
v_a_777_ = lean_ctor_get(v___x_743_, 0);
v_isSharedCheck_784_ = !lean_is_exclusive(v___x_743_);
if (v_isSharedCheck_784_ == 0)
{
v___x_779_ = v___x_743_;
v_isShared_780_ = v_isSharedCheck_784_;
goto v_resetjp_778_;
}
else
{
lean_inc(v_a_777_);
lean_dec(v___x_743_);
v___x_779_ = lean_box(0);
v_isShared_780_ = v_isSharedCheck_784_;
goto v_resetjp_778_;
}
v_resetjp_778_:
{
lean_object* v___x_782_; 
if (v_isShared_780_ == 0)
{
v___x_782_ = v___x_779_;
goto v_reusejp_781_;
}
else
{
lean_object* v_reuseFailAlloc_783_; 
v_reuseFailAlloc_783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_783_, 0, v_a_777_);
v___x_782_ = v_reuseFailAlloc_783_;
goto v_reusejp_781_;
}
v_reusejp_781_:
{
return v___x_782_;
}
}
}
}
v___jp_785_:
{
lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; uint8_t v___x_801_; 
v___x_795_ = lean_nat_sub(v___y_788_, v_initialArity_561_);
lean_dec(v___y_788_);
v___x_796_ = lean_array_get_size(v_reverted_557_);
v___x_797_ = lean_array_get_size(v_indices_559_);
v___x_798_ = lean_nat_sub(v___x_796_, v___x_797_);
v___x_799_ = lean_nat_sub(v___x_798_, v___y_787_);
lean_dec(v___x_798_);
v___x_800_ = lean_array_get_size(v_givenNames_555_);
v___x_801_ = lean_nat_dec_lt(v_minorIdx_564_, v___x_800_);
if (v___x_801_ == 0)
{
lean_object* v___x_802_; lean_object* v___x_803_; 
v___x_802_ = lean_box(0);
v___x_803_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_803_, 0, v___x_802_);
lean_ctor_set_uint8(v___x_803_, sizeof(void*)*1, v___x_801_);
v___y_730_ = v___x_797_;
v___y_731_ = v___x_799_;
v___y_732_ = v___y_794_;
v___y_733_ = v___y_789_;
v___y_734_ = v___y_790_;
v___y_735_ = v___y_786_;
v___y_736_ = v___x_796_;
v___y_737_ = v___x_795_;
v___y_738_ = v___y_791_;
v___y_739_ = v___y_787_;
v___y_740_ = v___y_793_;
v___y_741_ = v___y_792_;
v___y_742_ = v___x_803_;
goto v___jp_729_;
}
else
{
lean_object* v___x_804_; 
v___x_804_ = lean_array_fget_borrowed(v_givenNames_555_, v_minorIdx_564_);
lean_inc(v___x_804_);
v___y_730_ = v___x_797_;
v___y_731_ = v___x_799_;
v___y_732_ = v___y_794_;
v___y_733_ = v___y_789_;
v___y_734_ = v___y_790_;
v___y_735_ = v___y_786_;
v___y_736_ = v___x_796_;
v___y_737_ = v___x_795_;
v___y_738_ = v___y_791_;
v___y_739_ = v___y_787_;
v___y_740_ = v___y_793_;
v___y_741_ = v___y_792_;
v___y_742_ = v___x_804_;
goto v___jp_729_;
}
}
v___jp_805_:
{
lean_object* v___x_814_; uint8_t v___x_815_; 
lean_inc_ref(v___y_806_);
v___x_814_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTargetArity(v___y_806_);
v___x_815_ = lean_nat_dec_lt(v___x_814_, v_initialArity_561_);
if (v___x_815_ == 0)
{
v___y_786_ = v___y_806_;
v___y_787_ = v___y_809_;
v___y_788_ = v___x_814_;
v___y_789_ = v___y_813_;
v___y_790_ = v___y_812_;
v___y_791_ = v___y_810_;
v___y_792_ = v___y_807_;
v___y_793_ = v___y_808_;
v___y_794_ = v___y_811_;
goto v___jp_785_;
}
else
{
lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; 
v___x_816_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1));
v___x_817_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9);
lean_inc(v_mvarId_554_);
v___x_818_ = l_Lean_Meta_throwTacticEx___redArg(v___x_816_, v_mvarId_554_, v___x_817_, v___y_810_, v___y_807_, v___y_808_, v___y_811_);
if (lean_obj_tag(v___x_818_) == 0)
{
lean_dec_ref_known(v___x_818_, 1);
v___y_786_ = v___y_806_;
v___y_787_ = v___y_809_;
v___y_788_ = v___x_814_;
v___y_789_ = v___y_813_;
v___y_790_ = v___y_812_;
v___y_791_ = v___y_810_;
v___y_792_ = v___y_807_;
v___y_793_ = v___y_808_;
v___y_794_ = v___y_811_;
goto v___jp_785_;
}
else
{
lean_object* v_a_819_; lean_object* v___x_821_; uint8_t v_isShared_822_; uint8_t v_isSharedCheck_826_; 
lean_dec(v___x_814_);
lean_dec(v___y_812_);
lean_dec_ref(v___y_806_);
lean_dec(v_a_632_);
lean_dec_ref(v_subgoals_568_);
lean_dec_ref(v_recursor_565_);
lean_dec(v_minorIdx_564_);
lean_dec(v_pos_563_);
lean_dec(v_baseSubst_560_);
lean_dec_ref(v_major_558_);
lean_dec(v_mvarId_554_);
v_a_819_ = lean_ctor_get(v___x_818_, 0);
v_isSharedCheck_826_ = !lean_is_exclusive(v___x_818_);
if (v_isSharedCheck_826_ == 0)
{
v___x_821_ = v___x_818_;
v_isShared_822_ = v_isSharedCheck_826_;
goto v_resetjp_820_;
}
else
{
lean_inc(v_a_819_);
lean_dec(v___x_818_);
v___x_821_ = lean_box(0);
v_isShared_822_ = v_isSharedCheck_826_;
goto v_resetjp_820_;
}
v_resetjp_820_:
{
lean_object* v___x_824_; 
if (v_isShared_822_ == 0)
{
v___x_824_ = v___x_821_;
goto v_reusejp_823_;
}
else
{
lean_object* v_reuseFailAlloc_825_; 
v_reuseFailAlloc_825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_825_, 0, v_a_819_);
v___x_824_ = v_reuseFailAlloc_825_;
goto v_reusejp_823_;
}
v_reusejp_823_:
{
return v___x_824_;
}
}
}
}
}
v___jp_827_:
{
uint8_t v___x_836_; 
v___x_836_ = l_Lean_BinderInfo_isInstImplicit(v___y_828_);
if (v___x_836_ == 0)
{
v___y_806_ = v___y_829_;
v___y_807_ = v___y_830_;
v___y_808_ = v___y_831_;
v___y_809_ = v___y_832_;
v___y_810_ = v___y_833_;
v___y_811_ = v___y_834_;
v___y_812_ = v___y_835_;
v___y_813_ = v___x_836_;
goto v___jp_805_;
}
else
{
lean_object* v___x_837_; lean_object* v___x_838_; uint8_t v___x_839_; 
v___x_837_ = lean_array_get_size(v_givenNames_555_);
v___x_838_ = lean_unsigned_to_nat(0u);
v___x_839_ = lean_nat_dec_eq(v___x_837_, v___x_838_);
if (v___x_839_ == 0)
{
v___y_806_ = v___y_829_;
v___y_807_ = v___y_830_;
v___y_808_ = v___y_831_;
v___y_809_ = v___y_832_;
v___y_810_ = v___y_833_;
v___y_811_ = v___y_834_;
v___y_812_ = v___y_835_;
v___y_813_ = v___x_839_;
goto v___jp_805_;
}
else
{
lean_object* v___x_840_; lean_object* v___x_841_; 
v___x_840_ = lean_box(0);
lean_inc_ref(v___y_829_);
v___x_841_ = l_Lean_Meta_synthInstance_x3f(v___y_829_, v___x_840_, v___y_833_, v___y_830_, v___y_831_, v___y_834_);
if (lean_obj_tag(v___x_841_) == 0)
{
lean_object* v_a_842_; 
v_a_842_ = lean_ctor_get(v___x_841_, 0);
lean_inc(v_a_842_);
lean_dec_ref_known(v___x_841_, 1);
if (lean_obj_tag(v_a_842_) == 0)
{
lean_object* v___x_843_; 
v___x_843_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___y_829_, v___y_835_, v___y_833_, v___y_830_, v___y_831_, v___y_834_);
if (lean_obj_tag(v___x_843_) == 0)
{
lean_object* v_a_844_; lean_object* v___x_845_; lean_object* v___x_846_; 
v_a_844_ = lean_ctor_get(v___x_843_, 0);
lean_inc_n(v_a_844_, 2);
lean_dec_ref_known(v___x_843_, 1);
v___x_845_ = l_Lean_Expr_app___override(v_recursor_565_, v_a_844_);
lean_inc(v_mvarId_554_);
v___x_846_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTypeBody(v_mvarId_554_, v_a_632_, v_a_844_, v___y_833_, v___y_830_, v___y_831_, v___y_834_);
if (lean_obj_tag(v___x_846_) == 0)
{
lean_object* v_a_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; 
v_a_847_ = lean_ctor_get(v___x_846_, 0);
lean_inc(v_a_847_);
lean_dec_ref_known(v___x_846_, 1);
v___x_848_ = lean_nat_add(v_pos_563_, v___y_832_);
lean_dec(v_pos_563_);
v___x_849_ = lean_nat_add(v_minorIdx_564_, v___y_832_);
lean_dec(v_minorIdx_564_);
v___x_850_ = l_Lean_Expr_mvarId_x21(v_a_844_);
lean_dec(v_a_844_);
v___x_851_ = ((lean_object*)(l_Lean_Meta_instInhabitedInductionSubgoal_default___closed__0));
v___x_852_ = lean_box(0);
v___x_853_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_853_, 0, v___x_850_);
lean_ctor_set(v___x_853_, 1, v___x_851_);
lean_ctor_set(v___x_853_, 2, v___x_852_);
v___x_854_ = lean_array_push(v_subgoals_568_, v___x_853_);
v_pos_563_ = v___x_848_;
v_minorIdx_564_ = v___x_849_;
v_recursor_565_ = v___x_845_;
v_recursorType_566_ = v_a_847_;
v_subgoals_568_ = v___x_854_;
v_a_569_ = v___y_833_;
v_a_570_ = v___y_830_;
v_a_571_ = v___y_831_;
v_a_572_ = v___y_834_;
goto _start;
}
else
{
lean_object* v_a_856_; lean_object* v___x_858_; uint8_t v_isShared_859_; uint8_t v_isSharedCheck_863_; 
lean_dec_ref(v___x_845_);
lean_dec(v_a_844_);
lean_dec_ref(v_subgoals_568_);
lean_dec(v_minorIdx_564_);
lean_dec(v_pos_563_);
lean_dec(v_baseSubst_560_);
lean_dec_ref(v_major_558_);
lean_dec(v_mvarId_554_);
v_a_856_ = lean_ctor_get(v___x_846_, 0);
v_isSharedCheck_863_ = !lean_is_exclusive(v___x_846_);
if (v_isSharedCheck_863_ == 0)
{
v___x_858_ = v___x_846_;
v_isShared_859_ = v_isSharedCheck_863_;
goto v_resetjp_857_;
}
else
{
lean_inc(v_a_856_);
lean_dec(v___x_846_);
v___x_858_ = lean_box(0);
v_isShared_859_ = v_isSharedCheck_863_;
goto v_resetjp_857_;
}
v_resetjp_857_:
{
lean_object* v___x_861_; 
if (v_isShared_859_ == 0)
{
v___x_861_ = v___x_858_;
goto v_reusejp_860_;
}
else
{
lean_object* v_reuseFailAlloc_862_; 
v_reuseFailAlloc_862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_862_, 0, v_a_856_);
v___x_861_ = v_reuseFailAlloc_862_;
goto v_reusejp_860_;
}
v_reusejp_860_:
{
return v___x_861_;
}
}
}
}
else
{
lean_object* v_a_864_; lean_object* v___x_866_; uint8_t v_isShared_867_; uint8_t v_isSharedCheck_871_; 
lean_dec(v_a_632_);
lean_dec_ref(v_subgoals_568_);
lean_dec_ref(v_recursor_565_);
lean_dec(v_minorIdx_564_);
lean_dec(v_pos_563_);
lean_dec(v_baseSubst_560_);
lean_dec_ref(v_major_558_);
lean_dec(v_mvarId_554_);
v_a_864_ = lean_ctor_get(v___x_843_, 0);
v_isSharedCheck_871_ = !lean_is_exclusive(v___x_843_);
if (v_isSharedCheck_871_ == 0)
{
v___x_866_ = v___x_843_;
v_isShared_867_ = v_isSharedCheck_871_;
goto v_resetjp_865_;
}
else
{
lean_inc(v_a_864_);
lean_dec(v___x_843_);
v___x_866_ = lean_box(0);
v_isShared_867_ = v_isSharedCheck_871_;
goto v_resetjp_865_;
}
v_resetjp_865_:
{
lean_object* v___x_869_; 
if (v_isShared_867_ == 0)
{
v___x_869_ = v___x_866_;
goto v_reusejp_868_;
}
else
{
lean_object* v_reuseFailAlloc_870_; 
v_reuseFailAlloc_870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_870_, 0, v_a_864_);
v___x_869_ = v_reuseFailAlloc_870_;
goto v_reusejp_868_;
}
v_reusejp_868_:
{
return v___x_869_;
}
}
}
}
else
{
lean_object* v_val_872_; lean_object* v___x_873_; lean_object* v___x_874_; 
lean_dec(v___y_835_);
lean_dec_ref(v___y_829_);
v_val_872_ = lean_ctor_get(v_a_842_, 0);
lean_inc_n(v_val_872_, 2);
lean_dec_ref_known(v_a_842_, 1);
v___x_873_ = l_Lean_Expr_app___override(v_recursor_565_, v_val_872_);
lean_inc(v_mvarId_554_);
v___x_874_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTypeBody(v_mvarId_554_, v_a_632_, v_val_872_, v___y_833_, v___y_830_, v___y_831_, v___y_834_);
lean_dec(v_val_872_);
if (lean_obj_tag(v___x_874_) == 0)
{
lean_object* v_a_875_; lean_object* v___x_876_; lean_object* v___x_877_; 
v_a_875_ = lean_ctor_get(v___x_874_, 0);
lean_inc(v_a_875_);
lean_dec_ref_known(v___x_874_, 1);
v___x_876_ = lean_nat_add(v_pos_563_, v___y_832_);
lean_dec(v_pos_563_);
v___x_877_ = lean_nat_add(v_minorIdx_564_, v___y_832_);
lean_dec(v_minorIdx_564_);
v_pos_563_ = v___x_876_;
v_minorIdx_564_ = v___x_877_;
v_recursor_565_ = v___x_873_;
v_recursorType_566_ = v_a_875_;
v_a_569_ = v___y_833_;
v_a_570_ = v___y_830_;
v_a_571_ = v___y_831_;
v_a_572_ = v___y_834_;
goto _start;
}
else
{
lean_object* v_a_879_; lean_object* v___x_881_; uint8_t v_isShared_882_; uint8_t v_isSharedCheck_886_; 
lean_dec_ref(v___x_873_);
lean_dec_ref(v_subgoals_568_);
lean_dec(v_minorIdx_564_);
lean_dec(v_pos_563_);
lean_dec(v_baseSubst_560_);
lean_dec_ref(v_major_558_);
lean_dec(v_mvarId_554_);
v_a_879_ = lean_ctor_get(v___x_874_, 0);
v_isSharedCheck_886_ = !lean_is_exclusive(v___x_874_);
if (v_isSharedCheck_886_ == 0)
{
v___x_881_ = v___x_874_;
v_isShared_882_ = v_isSharedCheck_886_;
goto v_resetjp_880_;
}
else
{
lean_inc(v_a_879_);
lean_dec(v___x_874_);
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
else
{
lean_object* v_a_887_; lean_object* v___x_889_; uint8_t v_isShared_890_; uint8_t v_isSharedCheck_894_; 
lean_dec(v___y_835_);
lean_dec_ref(v___y_829_);
lean_dec(v_a_632_);
lean_dec_ref(v_subgoals_568_);
lean_dec_ref(v_recursor_565_);
lean_dec(v_minorIdx_564_);
lean_dec(v_pos_563_);
lean_dec(v_baseSubst_560_);
lean_dec_ref(v_major_558_);
lean_dec(v_mvarId_554_);
v_a_887_ = lean_ctor_get(v___x_841_, 0);
v_isSharedCheck_894_ = !lean_is_exclusive(v___x_841_);
if (v_isSharedCheck_894_ == 0)
{
v___x_889_ = v___x_841_;
v_isShared_890_ = v_isSharedCheck_894_;
goto v_resetjp_888_;
}
else
{
lean_inc(v_a_887_);
lean_dec(v___x_841_);
v___x_889_ = lean_box(0);
v_isShared_890_ = v_isSharedCheck_894_;
goto v_resetjp_888_;
}
v_resetjp_888_:
{
lean_object* v___x_892_; 
if (v_isShared_890_ == 0)
{
v___x_892_ = v___x_889_;
goto v_reusejp_891_;
}
else
{
lean_object* v_reuseFailAlloc_893_; 
v_reuseFailAlloc_893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_893_, 0, v_a_887_);
v___x_892_ = v_reuseFailAlloc_893_;
goto v_reusejp_891_;
}
v_reusejp_891_:
{
return v___x_892_;
}
}
}
}
}
}
}
v___jp_633_:
{
if (v_consumedMajor_567_ == 0)
{
lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; 
v___x_634_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1));
v___x_635_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9);
lean_inc(v_mvarId_554_);
v___x_636_ = l_Lean_Meta_throwTacticEx___redArg(v___x_634_, v_mvarId_554_, v___x_635_, v_a_569_, v_a_570_, v_a_571_, v_a_572_);
if (lean_obj_tag(v___x_636_) == 0)
{
lean_dec_ref_known(v___x_636_, 1);
v___y_575_ = v_a_569_;
v___y_576_ = v_a_570_;
v___y_577_ = v_a_571_;
v___y_578_ = v_a_572_;
goto v___jp_574_;
}
else
{
lean_object* v_a_637_; lean_object* v___x_639_; uint8_t v_isShared_640_; uint8_t v_isSharedCheck_644_; 
lean_dec_ref(v_subgoals_568_);
lean_dec_ref(v_recursor_565_);
lean_dec(v_mvarId_554_);
v_a_637_ = lean_ctor_get(v___x_636_, 0);
v_isSharedCheck_644_ = !lean_is_exclusive(v___x_636_);
if (v_isSharedCheck_644_ == 0)
{
v___x_639_ = v___x_636_;
v_isShared_640_ = v_isSharedCheck_644_;
goto v_resetjp_638_;
}
else
{
lean_inc(v_a_637_);
lean_dec(v___x_636_);
v___x_639_ = lean_box(0);
v_isShared_640_ = v_isSharedCheck_644_;
goto v_resetjp_638_;
}
v_resetjp_638_:
{
lean_object* v___x_642_; 
if (v_isShared_640_ == 0)
{
v___x_642_ = v___x_639_;
goto v_reusejp_641_;
}
else
{
lean_object* v_reuseFailAlloc_643_; 
v_reuseFailAlloc_643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_643_, 0, v_a_637_);
v___x_642_ = v_reuseFailAlloc_643_;
goto v_reusejp_641_;
}
v_reusejp_641_:
{
return v___x_642_;
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
}
else
{
lean_object* v_a_970_; lean_object* v___x_972_; uint8_t v_isShared_973_; uint8_t v_isSharedCheck_977_; 
lean_dec_ref(v_subgoals_568_);
lean_dec_ref(v_recursor_565_);
lean_dec(v_minorIdx_564_);
lean_dec(v_pos_563_);
lean_dec(v_baseSubst_560_);
lean_dec_ref(v_major_558_);
lean_dec(v_mvarId_554_);
v_a_970_ = lean_ctor_get(v___x_631_, 0);
v_isSharedCheck_977_ = !lean_is_exclusive(v___x_631_);
if (v_isSharedCheck_977_ == 0)
{
v___x_972_ = v___x_631_;
v_isShared_973_ = v_isSharedCheck_977_;
goto v_resetjp_971_;
}
else
{
lean_inc(v_a_970_);
lean_dec(v___x_631_);
v___x_972_ = lean_box(0);
v_isShared_973_ = v_isSharedCheck_977_;
goto v_resetjp_971_;
}
v_resetjp_971_:
{
lean_object* v___x_975_; 
if (v_isShared_973_ == 0)
{
v___x_975_ = v___x_972_;
goto v_reusejp_974_;
}
else
{
lean_object* v_reuseFailAlloc_976_; 
v_reuseFailAlloc_976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_976_, 0, v_a_970_);
v___x_975_ = v_reuseFailAlloc_976_;
goto v_reusejp_974_;
}
v_reusejp_974_:
{
return v___x_975_;
}
}
}
v___jp_574_:
{
lean_object* v___x_579_; 
v___x_579_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0___redArg(v_mvarId_554_, v_recursor_565_, v___y_576_);
if (lean_obj_tag(v___x_579_) == 0)
{
lean_object* v___x_581_; uint8_t v_isShared_582_; uint8_t v_isSharedCheck_621_; 
v_isSharedCheck_621_ = !lean_is_exclusive(v___x_579_);
if (v_isSharedCheck_621_ == 0)
{
lean_object* v_unused_622_; 
v_unused_622_ = lean_ctor_get(v___x_579_, 0);
lean_dec(v_unused_622_);
v___x_581_ = v___x_579_;
v_isShared_582_ = v_isSharedCheck_621_;
goto v_resetjp_580_;
}
else
{
lean_dec(v___x_579_);
v___x_581_ = lean_box(0);
v_isShared_582_ = v_isSharedCheck_621_;
goto v_resetjp_580_;
}
v_resetjp_580_:
{
lean_object* v_toCold_583_; lean_object* v_options_584_; uint8_t v_hasTrace_585_; 
v_toCold_583_ = lean_ctor_get(v___y_577_, 0);
v_options_584_ = lean_ctor_get(v_toCold_583_, 2);
v_hasTrace_585_ = lean_ctor_get_uint8(v_options_584_, sizeof(void*)*1);
if (v_hasTrace_585_ == 0)
{
lean_object* v___x_587_; 
if (v_isShared_582_ == 0)
{
lean_ctor_set(v___x_581_, 0, v_subgoals_568_);
v___x_587_ = v___x_581_;
goto v_reusejp_586_;
}
else
{
lean_object* v_reuseFailAlloc_588_; 
v_reuseFailAlloc_588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_588_, 0, v_subgoals_568_);
v___x_587_ = v_reuseFailAlloc_588_;
goto v_reusejp_586_;
}
v_reusejp_586_:
{
return v___x_587_;
}
}
else
{
lean_object* v_inheritedTraceOptions_589_; lean_object* v___x_590_; lean_object* v___x_591_; uint8_t v___x_592_; 
v_inheritedTraceOptions_589_ = lean_ctor_get(v_toCold_583_, 11);
v___x_590_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__2));
v___x_591_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5);
v___x_592_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_589_, v_options_584_, v___x_591_);
if (v___x_592_ == 0)
{
lean_object* v___x_594_; 
if (v_isShared_582_ == 0)
{
lean_ctor_set(v___x_581_, 0, v_subgoals_568_);
v___x_594_ = v___x_581_;
goto v_reusejp_593_;
}
else
{
lean_object* v_reuseFailAlloc_595_; 
v_reuseFailAlloc_595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_595_, 0, v_subgoals_568_);
v___x_594_ = v_reuseFailAlloc_595_;
goto v_reusejp_593_;
}
v_reusejp_593_:
{
return v___x_594_;
}
}
else
{
lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; 
lean_del_object(v___x_581_);
v___x_596_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__7, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__7_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__7);
v___x_597_ = lean_array_get_size(v_subgoals_568_);
v___x_598_ = l_Nat_reprFast(v___x_597_);
v___x_599_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_599_, 0, v___x_598_);
v___x_600_ = l_Lean_MessageData_ofFormat(v___x_599_);
v___x_601_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_601_, 0, v___x_596_);
lean_ctor_set(v___x_601_, 1, v___x_600_);
v___x_602_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__9, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__9_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__9);
v___x_603_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_603_, 0, v___x_601_);
lean_ctor_set(v___x_603_, 1, v___x_602_);
v___x_604_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1(v___x_590_, v___x_603_, v___y_575_, v___y_576_, v___y_577_, v___y_578_);
if (lean_obj_tag(v___x_604_) == 0)
{
lean_object* v___x_606_; uint8_t v_isShared_607_; uint8_t v_isSharedCheck_611_; 
v_isSharedCheck_611_ = !lean_is_exclusive(v___x_604_);
if (v_isSharedCheck_611_ == 0)
{
lean_object* v_unused_612_; 
v_unused_612_ = lean_ctor_get(v___x_604_, 0);
lean_dec(v_unused_612_);
v___x_606_ = v___x_604_;
v_isShared_607_ = v_isSharedCheck_611_;
goto v_resetjp_605_;
}
else
{
lean_dec(v___x_604_);
v___x_606_ = lean_box(0);
v_isShared_607_ = v_isSharedCheck_611_;
goto v_resetjp_605_;
}
v_resetjp_605_:
{
lean_object* v___x_609_; 
if (v_isShared_607_ == 0)
{
lean_ctor_set(v___x_606_, 0, v_subgoals_568_);
v___x_609_ = v___x_606_;
goto v_reusejp_608_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v_subgoals_568_);
v___x_609_ = v_reuseFailAlloc_610_;
goto v_reusejp_608_;
}
v_reusejp_608_:
{
return v___x_609_;
}
}
}
else
{
lean_object* v_a_613_; lean_object* v___x_615_; uint8_t v_isShared_616_; uint8_t v_isSharedCheck_620_; 
lean_dec_ref(v_subgoals_568_);
v_a_613_ = lean_ctor_get(v___x_604_, 0);
v_isSharedCheck_620_ = !lean_is_exclusive(v___x_604_);
if (v_isSharedCheck_620_ == 0)
{
v___x_615_ = v___x_604_;
v_isShared_616_ = v_isSharedCheck_620_;
goto v_resetjp_614_;
}
else
{
lean_inc(v_a_613_);
lean_dec(v___x_604_);
v___x_615_ = lean_box(0);
v_isShared_616_ = v_isSharedCheck_620_;
goto v_resetjp_614_;
}
v_resetjp_614_:
{
lean_object* v___x_618_; 
if (v_isShared_616_ == 0)
{
v___x_618_ = v___x_615_;
goto v_reusejp_617_;
}
else
{
lean_object* v_reuseFailAlloc_619_; 
v_reuseFailAlloc_619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_619_, 0, v_a_613_);
v___x_618_ = v_reuseFailAlloc_619_;
goto v_reusejp_617_;
}
v_reusejp_617_:
{
return v___x_618_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_623_; lean_object* v___x_625_; uint8_t v_isShared_626_; uint8_t v_isSharedCheck_630_; 
lean_dec_ref(v_subgoals_568_);
v_a_623_ = lean_ctor_get(v___x_579_, 0);
v_isSharedCheck_630_ = !lean_is_exclusive(v___x_579_);
if (v_isSharedCheck_630_ == 0)
{
v___x_625_ = v___x_579_;
v_isShared_626_ = v_isSharedCheck_630_;
goto v_resetjp_624_;
}
else
{
lean_inc(v_a_623_);
lean_dec(v___x_579_);
v___x_625_ = lean_box(0);
v_isShared_626_ = v_isSharedCheck_630_;
goto v_resetjp_624_;
}
v_resetjp_624_:
{
lean_object* v___x_628_; 
if (v_isShared_626_ == 0)
{
v___x_628_ = v___x_625_;
goto v_reusejp_627_;
}
else
{
lean_object* v_reuseFailAlloc_629_; 
v_reuseFailAlloc_629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_629_, 0, v_a_623_);
v___x_628_ = v_reuseFailAlloc_629_;
goto v_reusejp_627_;
}
v_reusejp_627_:
{
return v___x_628_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___boxed(lean_object** _args){
lean_object* v_mvarId_978_ = _args[0];
lean_object* v_givenNames_979_ = _args[1];
lean_object* v_recursorInfo_980_ = _args[2];
lean_object* v_reverted_981_ = _args[3];
lean_object* v_major_982_ = _args[4];
lean_object* v_indices_983_ = _args[5];
lean_object* v_baseSubst_984_ = _args[6];
lean_object* v_initialArity_985_ = _args[7];
lean_object* v_numMinors_986_ = _args[8];
lean_object* v_pos_987_ = _args[9];
lean_object* v_minorIdx_988_ = _args[10];
lean_object* v_recursor_989_ = _args[11];
lean_object* v_recursorType_990_ = _args[12];
lean_object* v_consumedMajor_991_ = _args[13];
lean_object* v_subgoals_992_ = _args[14];
lean_object* v_a_993_ = _args[15];
lean_object* v_a_994_ = _args[16];
lean_object* v_a_995_ = _args[17];
lean_object* v_a_996_ = _args[18];
lean_object* v_a_997_ = _args[19];
_start:
{
uint8_t v_consumedMajor_boxed_998_; lean_object* v_res_999_; 
v_consumedMajor_boxed_998_ = lean_unbox(v_consumedMajor_991_);
v_res_999_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop(v_mvarId_978_, v_givenNames_979_, v_recursorInfo_980_, v_reverted_981_, v_major_982_, v_indices_983_, v_baseSubst_984_, v_initialArity_985_, v_numMinors_986_, v_pos_987_, v_minorIdx_988_, v_recursor_989_, v_recursorType_990_, v_consumedMajor_boxed_998_, v_subgoals_992_, v_a_993_, v_a_994_, v_a_995_, v_a_996_);
lean_dec(v_a_996_);
lean_dec_ref(v_a_995_);
lean_dec(v_a_994_);
lean_dec_ref(v_a_993_);
lean_dec(v_numMinors_986_);
lean_dec(v_initialArity_985_);
lean_dec_ref(v_indices_983_);
lean_dec_ref(v_reverted_981_);
lean_dec_ref(v_recursorInfo_980_);
lean_dec_ref(v_givenNames_979_);
return v_res_999_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0(lean_object* v_mvarId_1000_, lean_object* v_val_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_){
_start:
{
lean_object* v___x_1007_; 
v___x_1007_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0___redArg(v_mvarId_1000_, v_val_1001_, v___y_1003_);
return v___x_1007_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0___boxed(lean_object* v_mvarId_1008_, lean_object* v_val_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_){
_start:
{
lean_object* v_res_1015_; 
v_res_1015_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0(v_mvarId_1008_, v_val_1009_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_);
lean_dec(v___y_1013_);
lean_dec_ref(v___y_1012_);
lean_dec(v___y_1011_);
lean_dec_ref(v___y_1010_);
return v_res_1015_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__2(lean_object* v___x_1016_, lean_object* v_reverted_1017_, lean_object* v_fst_1018_, lean_object* v_n_1019_, lean_object* v_j_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_){
_start:
{
lean_object* v___x_1023_; 
v___x_1023_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__2___redArg(v___x_1016_, v_reverted_1017_, v_fst_1018_, v_n_1019_, v_j_1020_, v_a_1022_);
return v___x_1023_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__2___boxed(lean_object* v___x_1024_, lean_object* v_reverted_1025_, lean_object* v_fst_1026_, lean_object* v_n_1027_, lean_object* v_j_1028_, lean_object* v_a_1029_, lean_object* v_a_1030_){
_start:
{
lean_object* v_res_1031_; 
v_res_1031_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__2(v___x_1024_, v_reverted_1025_, v_fst_1026_, v_n_1027_, v_j_1028_, v_a_1029_, v_a_1030_);
lean_dec(v_n_1027_);
lean_dec_ref(v_fst_1026_);
lean_dec_ref(v_reverted_1025_);
lean_dec(v___x_1024_);
return v_res_1031_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0(lean_object* v_00_u03b2_1032_, lean_object* v_x_1033_, lean_object* v_x_1034_, lean_object* v_x_1035_){
_start:
{
lean_object* v___x_1036_; 
v___x_1036_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0___redArg(v_x_1033_, v_x_1034_, v_x_1035_);
return v___x_1036_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1037_, lean_object* v_x_1038_, size_t v_x_1039_, size_t v_x_1040_, lean_object* v_x_1041_, lean_object* v_x_1042_){
_start:
{
lean_object* v___x_1043_; 
v___x_1043_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2___redArg(v_x_1038_, v_x_1039_, v_x_1040_, v_x_1041_, v_x_1042_);
return v___x_1043_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1044_, lean_object* v_x_1045_, lean_object* v_x_1046_, lean_object* v_x_1047_, lean_object* v_x_1048_, lean_object* v_x_1049_){
_start:
{
size_t v_x_9571__boxed_1050_; size_t v_x_9572__boxed_1051_; lean_object* v_res_1052_; 
v_x_9571__boxed_1050_ = lean_unbox_usize(v_x_1046_);
lean_dec(v_x_1046_);
v_x_9572__boxed_1051_ = lean_unbox_usize(v_x_1047_);
lean_dec(v_x_1047_);
v_res_1052_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2(v_00_u03b2_1044_, v_x_1045_, v_x_9571__boxed_1050_, v_x_9572__boxed_1051_, v_x_1048_, v_x_1049_);
return v_res_1052_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__8(lean_object* v_00_u03b2_1053_, lean_object* v_n_1054_, lean_object* v_k_1055_, lean_object* v_v_1056_){
_start:
{
lean_object* v___x_1057_; 
v___x_1057_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__8___redArg(v_n_1054_, v_k_1055_, v_v_1056_);
return v___x_1057_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__9(lean_object* v_00_u03b2_1058_, size_t v_depth_1059_, lean_object* v_keys_1060_, lean_object* v_vals_1061_, lean_object* v_heq_1062_, lean_object* v_i_1063_, lean_object* v_entries_1064_){
_start:
{
lean_object* v___x_1065_; 
v___x_1065_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__9___redArg(v_depth_1059_, v_keys_1060_, v_vals_1061_, v_i_1063_, v_entries_1064_);
return v___x_1065_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__9___boxed(lean_object* v_00_u03b2_1066_, lean_object* v_depth_1067_, lean_object* v_keys_1068_, lean_object* v_vals_1069_, lean_object* v_heq_1070_, lean_object* v_i_1071_, lean_object* v_entries_1072_){
_start:
{
size_t v_depth_boxed_1073_; lean_object* v_res_1074_; 
v_depth_boxed_1073_ = lean_unbox_usize(v_depth_1067_);
lean_dec(v_depth_1067_);
v_res_1074_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__9(v_00_u03b2_1066_, v_depth_boxed_1073_, v_keys_1068_, v_vals_1069_, v_heq_1070_, v_i_1071_, v_entries_1072_);
lean_dec_ref(v_vals_1069_);
lean_dec_ref(v_keys_1068_);
return v_res_1074_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__8_spec__9(lean_object* v_00_u03b2_1075_, lean_object* v_x_1076_, lean_object* v_x_1077_, lean_object* v_x_1078_, lean_object* v_x_1079_){
_start:
{
lean_object* v___x_1080_; 
v___x_1080_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__8_spec__9___redArg(v_x_1076_, v_x_1077_, v_x_1078_, v_x_1079_);
return v___x_1080_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize(lean_object* v_mvarId_1083_, lean_object* v_givenNames_1084_, lean_object* v_recursorInfo_1085_, lean_object* v_reverted_1086_, lean_object* v_major_1087_, lean_object* v_indices_1088_, lean_object* v_baseSubst_1089_, lean_object* v_recursor_1090_, lean_object* v_a_1091_, lean_object* v_a_1092_, lean_object* v_a_1093_, lean_object* v_a_1094_){
_start:
{
lean_object* v___x_1096_; 
lean_inc(v_mvarId_1083_);
v___x_1096_ = l_Lean_MVarId_getType(v_mvarId_1083_, v_a_1091_, v_a_1092_, v_a_1093_, v_a_1094_);
if (lean_obj_tag(v___x_1096_) == 0)
{
lean_object* v_a_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; 
v_a_1097_ = lean_ctor_get(v___x_1096_, 0);
lean_inc(v_a_1097_);
lean_dec_ref_known(v___x_1096_, 1);
v___x_1098_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTargetArity(v_a_1097_);
lean_inc(v_a_1094_);
lean_inc_ref(v_a_1093_);
lean_inc(v_a_1092_);
lean_inc_ref(v_a_1091_);
lean_inc_ref(v_recursor_1090_);
v___x_1099_ = lean_infer_type(v_recursor_1090_, v_a_1091_, v_a_1092_, v_a_1093_, v_a_1094_);
if (lean_obj_tag(v___x_1099_) == 0)
{
lean_object* v_a_1100_; lean_object* v_paramsPos_1101_; lean_object* v_produceMotive_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; uint8_t v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; 
v_a_1100_ = lean_ctor_get(v___x_1099_, 0);
lean_inc(v_a_1100_);
lean_dec_ref_known(v___x_1099_, 1);
v_paramsPos_1101_ = lean_ctor_get(v_recursorInfo_1085_, 5);
v_produceMotive_1102_ = lean_ctor_get(v_recursorInfo_1085_, 7);
v___x_1103_ = l_List_lengthTR___redArg(v_produceMotive_1102_);
v___x_1104_ = l_List_lengthTR___redArg(v_paramsPos_1101_);
v___x_1105_ = lean_unsigned_to_nat(1u);
v___x_1106_ = lean_nat_add(v___x_1104_, v___x_1105_);
lean_dec(v___x_1104_);
v___x_1107_ = lean_unsigned_to_nat(0u);
v___x_1108_ = 0;
v___x_1109_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize___closed__0));
v___x_1110_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop(v_mvarId_1083_, v_givenNames_1084_, v_recursorInfo_1085_, v_reverted_1086_, v_major_1087_, v_indices_1088_, v_baseSubst_1089_, v___x_1098_, v___x_1103_, v___x_1106_, v___x_1107_, v_recursor_1090_, v_a_1100_, v___x_1108_, v___x_1109_, v_a_1091_, v_a_1092_, v_a_1093_, v_a_1094_);
lean_dec(v___x_1103_);
lean_dec(v___x_1098_);
return v___x_1110_;
}
else
{
lean_object* v_a_1111_; lean_object* v___x_1113_; uint8_t v_isShared_1114_; uint8_t v_isSharedCheck_1118_; 
lean_dec(v___x_1098_);
lean_dec_ref(v_recursor_1090_);
lean_dec(v_baseSubst_1089_);
lean_dec_ref(v_major_1087_);
lean_dec(v_mvarId_1083_);
v_a_1111_ = lean_ctor_get(v___x_1099_, 0);
v_isSharedCheck_1118_ = !lean_is_exclusive(v___x_1099_);
if (v_isSharedCheck_1118_ == 0)
{
v___x_1113_ = v___x_1099_;
v_isShared_1114_ = v_isSharedCheck_1118_;
goto v_resetjp_1112_;
}
else
{
lean_inc(v_a_1111_);
lean_dec(v___x_1099_);
v___x_1113_ = lean_box(0);
v_isShared_1114_ = v_isSharedCheck_1118_;
goto v_resetjp_1112_;
}
v_resetjp_1112_:
{
lean_object* v___x_1116_; 
if (v_isShared_1114_ == 0)
{
v___x_1116_ = v___x_1113_;
goto v_reusejp_1115_;
}
else
{
lean_object* v_reuseFailAlloc_1117_; 
v_reuseFailAlloc_1117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1117_, 0, v_a_1111_);
v___x_1116_ = v_reuseFailAlloc_1117_;
goto v_reusejp_1115_;
}
v_reusejp_1115_:
{
return v___x_1116_;
}
}
}
}
else
{
lean_object* v_a_1119_; lean_object* v___x_1121_; uint8_t v_isShared_1122_; uint8_t v_isSharedCheck_1126_; 
lean_dec_ref(v_recursor_1090_);
lean_dec(v_baseSubst_1089_);
lean_dec_ref(v_major_1087_);
lean_dec(v_mvarId_1083_);
v_a_1119_ = lean_ctor_get(v___x_1096_, 0);
v_isSharedCheck_1126_ = !lean_is_exclusive(v___x_1096_);
if (v_isSharedCheck_1126_ == 0)
{
v___x_1121_ = v___x_1096_;
v_isShared_1122_ = v_isSharedCheck_1126_;
goto v_resetjp_1120_;
}
else
{
lean_inc(v_a_1119_);
lean_dec(v___x_1096_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize___boxed(lean_object* v_mvarId_1127_, lean_object* v_givenNames_1128_, lean_object* v_recursorInfo_1129_, lean_object* v_reverted_1130_, lean_object* v_major_1131_, lean_object* v_indices_1132_, lean_object* v_baseSubst_1133_, lean_object* v_recursor_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_, lean_object* v_a_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_){
_start:
{
lean_object* v_res_1140_; 
v_res_1140_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize(v_mvarId_1127_, v_givenNames_1128_, v_recursorInfo_1129_, v_reverted_1130_, v_major_1131_, v_indices_1132_, v_baseSubst_1133_, v_recursor_1134_, v_a_1135_, v_a_1136_, v_a_1137_, v_a_1138_);
lean_dec(v_a_1138_);
lean_dec_ref(v_a_1137_);
lean_dec(v_a_1136_);
lean_dec_ref(v_a_1135_);
lean_dec_ref(v_indices_1132_);
lean_dec_ref(v_reverted_1130_);
lean_dec_ref(v_recursorInfo_1129_);
lean_dec_ref(v_givenNames_1128_);
return v_res_1140_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg___closed__1(void){
_start:
{
lean_object* v___x_1142_; lean_object* v___x_1143_; 
v___x_1142_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg___closed__0));
v___x_1143_ = l_Lean_stringToMessageData(v___x_1142_);
return v___x_1143_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg(lean_object* v_tacticName_1144_, lean_object* v_mvarId_1145_, lean_object* v_majorType_1146_, lean_object* v_a_1147_, lean_object* v_a_1148_, lean_object* v_a_1149_, lean_object* v_a_1150_){
_start:
{
lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; 
v___x_1152_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg___closed__1, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg___closed__1);
v___x_1153_ = l_Lean_indentExpr(v_majorType_1146_);
v___x_1154_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1154_, 0, v___x_1152_);
lean_ctor_set(v___x_1154_, 1, v___x_1153_);
v___x_1155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1155_, 0, v___x_1154_);
v___x_1156_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1144_, v_mvarId_1145_, v___x_1155_, v_a_1147_, v_a_1148_, v_a_1149_, v_a_1150_);
return v___x_1156_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg___boxed(lean_object* v_tacticName_1157_, lean_object* v_mvarId_1158_, lean_object* v_majorType_1159_, lean_object* v_a_1160_, lean_object* v_a_1161_, lean_object* v_a_1162_, lean_object* v_a_1163_, lean_object* v_a_1164_){
_start:
{
lean_object* v_res_1165_; 
v_res_1165_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg(v_tacticName_1157_, v_mvarId_1158_, v_majorType_1159_, v_a_1160_, v_a_1161_, v_a_1162_, v_a_1163_);
lean_dec(v_a_1163_);
lean_dec_ref(v_a_1162_);
lean_dec(v_a_1161_);
lean_dec_ref(v_a_1160_);
return v_res_1165_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType(lean_object* v_00_u03b1_1166_, lean_object* v_tacticName_1167_, lean_object* v_mvarId_1168_, lean_object* v_majorType_1169_, lean_object* v_a_1170_, lean_object* v_a_1171_, lean_object* v_a_1172_, lean_object* v_a_1173_){
_start:
{
lean_object* v___x_1175_; 
v___x_1175_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg(v_tacticName_1167_, v_mvarId_1168_, v_majorType_1169_, v_a_1170_, v_a_1171_, v_a_1172_, v_a_1173_);
return v___x_1175_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___boxed(lean_object* v_00_u03b1_1176_, lean_object* v_tacticName_1177_, lean_object* v_mvarId_1178_, lean_object* v_majorType_1179_, lean_object* v_a_1180_, lean_object* v_a_1181_, lean_object* v_a_1182_, lean_object* v_a_1183_, lean_object* v_a_1184_){
_start:
{
lean_object* v_res_1185_; 
v_res_1185_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType(v_00_u03b1_1176_, v_tacticName_1177_, v_mvarId_1178_, v_majorType_1179_, v_a_1180_, v_a_1181_, v_a_1182_, v_a_1183_);
lean_dec(v_a_1183_);
lean_dec_ref(v_a_1182_);
lean_dec(v_a_1181_);
lean_dec_ref(v_a_1180_);
return v_res_1185_;
}
}
LEAN_EXPORT uint8_t l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___lam__0(lean_object* v_fvarId_1186_, lean_object* v_x_1187_){
_start:
{
uint8_t v___x_1188_; 
v___x_1188_ = l_Lean_instBEqFVarId_beq(v_fvarId_1186_, v_x_1187_);
return v___x_1188_;
}
}
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___lam__0___boxed(lean_object* v_fvarId_1189_, lean_object* v_x_1190_){
_start:
{
uint8_t v_res_1191_; lean_object* v_r_1192_; 
v_res_1191_ = l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___lam__0(v_fvarId_1189_, v_x_1190_);
lean_dec(v_x_1190_);
lean_dec(v_fvarId_1189_);
v_r_1192_ = lean_box(v_res_1191_);
return v_r_1192_;
}
}
LEAN_EXPORT uint8_t l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___lam__1(lean_object* v_x_1193_){
_start:
{
uint8_t v___x_1194_; 
v___x_1194_ = 0;
return v___x_1194_;
}
}
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___lam__1___boxed(lean_object* v_x_1195_){
_start:
{
uint8_t v_res_1196_; lean_object* v_r_1197_; 
v_res_1196_ = l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___lam__1(v_x_1195_);
lean_dec(v_x_1195_);
v_r_1197_ = lean_box(v_res_1196_);
return v_r_1197_;
}
}
static lean_object* _init_l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; 
v___x_1199_ = lean_box(0);
v___x_1200_ = lean_unsigned_to_nat(16u);
v___x_1201_ = lean_mk_array(v___x_1200_, v___x_1199_);
return v___x_1201_;
}
}
static lean_object* _init_l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; 
v___x_1202_ = lean_obj_once(&l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__1, &l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__1_once, _init_l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__1);
v___x_1203_ = lean_unsigned_to_nat(0u);
v___x_1204_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1204_, 0, v___x_1203_);
lean_ctor_set(v___x_1204_, 1, v___x_1202_);
return v___x_1204_;
}
}
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg(lean_object* v_localDecl_1205_, lean_object* v_fvarId_1206_, uint8_t v_generalizeNondepLet_1207_, lean_object* v___y_1208_){
_start:
{
uint8_t v_fst_1211_; lean_object* v_snd_1212_; lean_object* v___y_1231_; lean_object* v___f_1235_; lean_object* v___f_1236_; 
v___f_1235_ = lean_alloc_closure((void*)(l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1235_, 0, v_fvarId_1206_);
v___f_1236_ = ((lean_object*)(l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__0));
if (lean_obj_tag(v_localDecl_1205_) == 0)
{
lean_object* v_type_1237_; lean_object* v___x_1238_; uint8_t v_fst_1240_; lean_object* v_mctx_1241_; lean_object* v___y_1259_; lean_object* v_mctx_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; uint8_t v___x_1267_; 
v_type_1237_ = lean_ctor_get(v_localDecl_1205_, 3);
lean_inc_ref(v_type_1237_);
lean_dec_ref_known(v_localDecl_1205_, 4);
v___x_1238_ = lean_st_ref_get(v___y_1208_);
v_mctx_1264_ = lean_ctor_get(v___x_1238_, 0);
lean_inc_ref_n(v_mctx_1264_, 2);
lean_dec(v___x_1238_);
v___x_1265_ = lean_obj_once(&l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__2, &l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__2_once, _init_l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__2);
v___x_1266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1266_, 0, v___x_1265_);
lean_ctor_set(v___x_1266_, 1, v_mctx_1264_);
v___x_1267_ = l_Lean_Expr_hasFVar(v_type_1237_);
if (v___x_1267_ == 0)
{
uint8_t v___x_1268_; 
v___x_1268_ = l_Lean_Expr_hasMVar(v_type_1237_);
if (v___x_1268_ == 0)
{
lean_dec_ref_known(v___x_1266_, 2);
lean_dec_ref(v_type_1237_);
lean_dec_ref(v___f_1235_);
v_fst_1240_ = v___x_1268_;
v_mctx_1241_ = v_mctx_1264_;
goto v___jp_1239_;
}
else
{
lean_object* v___x_1269_; 
lean_dec_ref(v_mctx_1264_);
v___x_1269_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1235_, v___f_1236_, v_type_1237_, v___x_1266_);
v___y_1259_ = v___x_1269_;
goto v___jp_1258_;
}
}
else
{
lean_object* v___x_1270_; 
lean_dec_ref(v_mctx_1264_);
v___x_1270_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1235_, v___f_1236_, v_type_1237_, v___x_1266_);
v___y_1259_ = v___x_1270_;
goto v___jp_1258_;
}
v___jp_1239_:
{
lean_object* v___x_1242_; lean_object* v_cache_1243_; lean_object* v_zetaDeltaFVarIds_1244_; lean_object* v_postponed_1245_; lean_object* v_diag_1246_; lean_object* v___x_1248_; uint8_t v_isShared_1249_; uint8_t v_isSharedCheck_1256_; 
v___x_1242_ = lean_st_ref_take(v___y_1208_);
v_cache_1243_ = lean_ctor_get(v___x_1242_, 1);
v_zetaDeltaFVarIds_1244_ = lean_ctor_get(v___x_1242_, 2);
v_postponed_1245_ = lean_ctor_get(v___x_1242_, 3);
v_diag_1246_ = lean_ctor_get(v___x_1242_, 4);
v_isSharedCheck_1256_ = !lean_is_exclusive(v___x_1242_);
if (v_isSharedCheck_1256_ == 0)
{
lean_object* v_unused_1257_; 
v_unused_1257_ = lean_ctor_get(v___x_1242_, 0);
lean_dec(v_unused_1257_);
v___x_1248_ = v___x_1242_;
v_isShared_1249_ = v_isSharedCheck_1256_;
goto v_resetjp_1247_;
}
else
{
lean_inc(v_diag_1246_);
lean_inc(v_postponed_1245_);
lean_inc(v_zetaDeltaFVarIds_1244_);
lean_inc(v_cache_1243_);
lean_dec(v___x_1242_);
v___x_1248_ = lean_box(0);
v_isShared_1249_ = v_isSharedCheck_1256_;
goto v_resetjp_1247_;
}
v_resetjp_1247_:
{
lean_object* v___x_1251_; 
if (v_isShared_1249_ == 0)
{
lean_ctor_set(v___x_1248_, 0, v_mctx_1241_);
v___x_1251_ = v___x_1248_;
goto v_reusejp_1250_;
}
else
{
lean_object* v_reuseFailAlloc_1255_; 
v_reuseFailAlloc_1255_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1255_, 0, v_mctx_1241_);
lean_ctor_set(v_reuseFailAlloc_1255_, 1, v_cache_1243_);
lean_ctor_set(v_reuseFailAlloc_1255_, 2, v_zetaDeltaFVarIds_1244_);
lean_ctor_set(v_reuseFailAlloc_1255_, 3, v_postponed_1245_);
lean_ctor_set(v_reuseFailAlloc_1255_, 4, v_diag_1246_);
v___x_1251_ = v_reuseFailAlloc_1255_;
goto v_reusejp_1250_;
}
v_reusejp_1250_:
{
lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; 
v___x_1252_ = lean_st_ref_put(v___y_1208_, v___x_1251_);
v___x_1253_ = lean_box(v_fst_1240_);
v___x_1254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1254_, 0, v___x_1253_);
return v___x_1254_;
}
}
}
v___jp_1258_:
{
lean_object* v_snd_1260_; lean_object* v_fst_1261_; lean_object* v_mctx_1262_; uint8_t v___x_1263_; 
v_snd_1260_ = lean_ctor_get(v___y_1259_, 1);
lean_inc(v_snd_1260_);
v_fst_1261_ = lean_ctor_get(v___y_1259_, 0);
lean_inc(v_fst_1261_);
lean_dec_ref(v___y_1259_);
v_mctx_1262_ = lean_ctor_get(v_snd_1260_, 1);
lean_inc_ref(v_mctx_1262_);
lean_dec(v_snd_1260_);
v___x_1263_ = lean_unbox(v_fst_1261_);
lean_dec(v_fst_1261_);
v_fst_1240_ = v___x_1263_;
v_mctx_1241_ = v_mctx_1262_;
goto v___jp_1239_;
}
}
else
{
lean_object* v_type_1271_; lean_object* v_value_1272_; uint8_t v_nondep_1273_; lean_object* v_snd_1275_; lean_object* v___y_1281_; 
v_type_1271_ = lean_ctor_get(v_localDecl_1205_, 3);
lean_inc_ref(v_type_1271_);
v_value_1272_ = lean_ctor_get(v_localDecl_1205_, 4);
lean_inc_ref(v_value_1272_);
v_nondep_1273_ = lean_ctor_get_uint8(v_localDecl_1205_, sizeof(void*)*5);
lean_dec_ref_known(v_localDecl_1205_, 5);
if (v_generalizeNondepLet_1207_ == 0)
{
goto v___jp_1287_;
}
else
{
if (v_nondep_1273_ == 0)
{
goto v___jp_1287_;
}
else
{
lean_object* v___x_1296_; uint8_t v_fst_1298_; lean_object* v_mctx_1299_; lean_object* v___y_1317_; lean_object* v_mctx_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; uint8_t v___x_1325_; 
lean_dec_ref(v_value_1272_);
v___x_1296_ = lean_st_ref_get(v___y_1208_);
v_mctx_1322_ = lean_ctor_get(v___x_1296_, 0);
lean_inc_ref_n(v_mctx_1322_, 2);
lean_dec(v___x_1296_);
v___x_1323_ = lean_obj_once(&l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__2, &l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__2_once, _init_l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__2);
v___x_1324_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1324_, 0, v___x_1323_);
lean_ctor_set(v___x_1324_, 1, v_mctx_1322_);
v___x_1325_ = l_Lean_Expr_hasFVar(v_type_1271_);
if (v___x_1325_ == 0)
{
uint8_t v___x_1326_; 
v___x_1326_ = l_Lean_Expr_hasMVar(v_type_1271_);
if (v___x_1326_ == 0)
{
lean_dec_ref_known(v___x_1324_, 2);
lean_dec_ref(v_type_1271_);
lean_dec_ref(v___f_1235_);
v_fst_1298_ = v___x_1326_;
v_mctx_1299_ = v_mctx_1322_;
goto v___jp_1297_;
}
else
{
lean_object* v___x_1327_; 
lean_dec_ref(v_mctx_1322_);
v___x_1327_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1235_, v___f_1236_, v_type_1271_, v___x_1324_);
v___y_1317_ = v___x_1327_;
goto v___jp_1316_;
}
}
else
{
lean_object* v___x_1328_; 
lean_dec_ref(v_mctx_1322_);
v___x_1328_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1235_, v___f_1236_, v_type_1271_, v___x_1324_);
v___y_1317_ = v___x_1328_;
goto v___jp_1316_;
}
v___jp_1297_:
{
lean_object* v___x_1300_; lean_object* v_cache_1301_; lean_object* v_zetaDeltaFVarIds_1302_; lean_object* v_postponed_1303_; lean_object* v_diag_1304_; lean_object* v___x_1306_; uint8_t v_isShared_1307_; uint8_t v_isSharedCheck_1314_; 
v___x_1300_ = lean_st_ref_take(v___y_1208_);
v_cache_1301_ = lean_ctor_get(v___x_1300_, 1);
v_zetaDeltaFVarIds_1302_ = lean_ctor_get(v___x_1300_, 2);
v_postponed_1303_ = lean_ctor_get(v___x_1300_, 3);
v_diag_1304_ = lean_ctor_get(v___x_1300_, 4);
v_isSharedCheck_1314_ = !lean_is_exclusive(v___x_1300_);
if (v_isSharedCheck_1314_ == 0)
{
lean_object* v_unused_1315_; 
v_unused_1315_ = lean_ctor_get(v___x_1300_, 0);
lean_dec(v_unused_1315_);
v___x_1306_ = v___x_1300_;
v_isShared_1307_ = v_isSharedCheck_1314_;
goto v_resetjp_1305_;
}
else
{
lean_inc(v_diag_1304_);
lean_inc(v_postponed_1303_);
lean_inc(v_zetaDeltaFVarIds_1302_);
lean_inc(v_cache_1301_);
lean_dec(v___x_1300_);
v___x_1306_ = lean_box(0);
v_isShared_1307_ = v_isSharedCheck_1314_;
goto v_resetjp_1305_;
}
v_resetjp_1305_:
{
lean_object* v___x_1309_; 
if (v_isShared_1307_ == 0)
{
lean_ctor_set(v___x_1306_, 0, v_mctx_1299_);
v___x_1309_ = v___x_1306_;
goto v_reusejp_1308_;
}
else
{
lean_object* v_reuseFailAlloc_1313_; 
v_reuseFailAlloc_1313_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1313_, 0, v_mctx_1299_);
lean_ctor_set(v_reuseFailAlloc_1313_, 1, v_cache_1301_);
lean_ctor_set(v_reuseFailAlloc_1313_, 2, v_zetaDeltaFVarIds_1302_);
lean_ctor_set(v_reuseFailAlloc_1313_, 3, v_postponed_1303_);
lean_ctor_set(v_reuseFailAlloc_1313_, 4, v_diag_1304_);
v___x_1309_ = v_reuseFailAlloc_1313_;
goto v_reusejp_1308_;
}
v_reusejp_1308_:
{
lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; 
v___x_1310_ = lean_st_ref_put(v___y_1208_, v___x_1309_);
v___x_1311_ = lean_box(v_fst_1298_);
v___x_1312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1312_, 0, v___x_1311_);
return v___x_1312_;
}
}
}
v___jp_1316_:
{
lean_object* v_snd_1318_; lean_object* v_fst_1319_; lean_object* v_mctx_1320_; uint8_t v___x_1321_; 
v_snd_1318_ = lean_ctor_get(v___y_1317_, 1);
lean_inc(v_snd_1318_);
v_fst_1319_ = lean_ctor_get(v___y_1317_, 0);
lean_inc(v_fst_1319_);
lean_dec_ref(v___y_1317_);
v_mctx_1320_ = lean_ctor_get(v_snd_1318_, 1);
lean_inc_ref(v_mctx_1320_);
lean_dec(v_snd_1318_);
v___x_1321_ = lean_unbox(v_fst_1319_);
lean_dec(v_fst_1319_);
v_fst_1298_ = v___x_1321_;
v_mctx_1299_ = v_mctx_1320_;
goto v___jp_1297_;
}
}
}
v___jp_1274_:
{
uint8_t v___x_1276_; 
v___x_1276_ = l_Lean_Expr_hasFVar(v_value_1272_);
if (v___x_1276_ == 0)
{
uint8_t v___x_1277_; 
v___x_1277_ = l_Lean_Expr_hasMVar(v_value_1272_);
if (v___x_1277_ == 0)
{
lean_dec_ref(v_value_1272_);
lean_dec_ref(v___f_1235_);
v_fst_1211_ = v___x_1277_;
v_snd_1212_ = v_snd_1275_;
goto v___jp_1210_;
}
else
{
lean_object* v___x_1278_; 
v___x_1278_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1235_, v___f_1236_, v_value_1272_, v_snd_1275_);
v___y_1231_ = v___x_1278_;
goto v___jp_1230_;
}
}
else
{
lean_object* v___x_1279_; 
v___x_1279_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1235_, v___f_1236_, v_value_1272_, v_snd_1275_);
v___y_1231_ = v___x_1279_;
goto v___jp_1230_;
}
}
v___jp_1280_:
{
lean_object* v_fst_1282_; uint8_t v___x_1283_; 
v_fst_1282_ = lean_ctor_get(v___y_1281_, 0);
v___x_1283_ = lean_unbox(v_fst_1282_);
if (v___x_1283_ == 0)
{
lean_object* v_snd_1284_; 
v_snd_1284_ = lean_ctor_get(v___y_1281_, 1);
lean_inc(v_snd_1284_);
lean_dec_ref(v___y_1281_);
v_snd_1275_ = v_snd_1284_;
goto v___jp_1274_;
}
else
{
lean_object* v_snd_1285_; uint8_t v___x_1286_; 
lean_inc(v_fst_1282_);
lean_dec_ref(v_value_1272_);
lean_dec_ref(v___f_1235_);
v_snd_1285_ = lean_ctor_get(v___y_1281_, 1);
lean_inc(v_snd_1285_);
lean_dec_ref(v___y_1281_);
v___x_1286_ = lean_unbox(v_fst_1282_);
lean_dec(v_fst_1282_);
v_fst_1211_ = v___x_1286_;
v_snd_1212_ = v_snd_1285_;
goto v___jp_1210_;
}
}
v___jp_1287_:
{
lean_object* v___x_1288_; lean_object* v_mctx_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; uint8_t v___x_1292_; 
v___x_1288_ = lean_st_ref_get(v___y_1208_);
v_mctx_1289_ = lean_ctor_get(v___x_1288_, 0);
lean_inc_ref(v_mctx_1289_);
lean_dec(v___x_1288_);
v___x_1290_ = lean_obj_once(&l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__2, &l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__2_once, _init_l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__2);
v___x_1291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1291_, 0, v___x_1290_);
lean_ctor_set(v___x_1291_, 1, v_mctx_1289_);
v___x_1292_ = l_Lean_Expr_hasFVar(v_type_1271_);
if (v___x_1292_ == 0)
{
uint8_t v___x_1293_; 
v___x_1293_ = l_Lean_Expr_hasMVar(v_type_1271_);
if (v___x_1293_ == 0)
{
lean_dec_ref(v_type_1271_);
v_snd_1275_ = v___x_1291_;
goto v___jp_1274_;
}
else
{
lean_object* v___x_1294_; 
lean_inc_ref(v___f_1235_);
v___x_1294_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1235_, v___f_1236_, v_type_1271_, v___x_1291_);
v___y_1281_ = v___x_1294_;
goto v___jp_1280_;
}
}
else
{
lean_object* v___x_1295_; 
lean_inc_ref(v___f_1235_);
v___x_1295_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1235_, v___f_1236_, v_type_1271_, v___x_1291_);
v___y_1281_ = v___x_1295_;
goto v___jp_1280_;
}
}
}
v___jp_1210_:
{
lean_object* v_mctx_1213_; lean_object* v___x_1214_; lean_object* v_cache_1215_; lean_object* v_zetaDeltaFVarIds_1216_; lean_object* v_postponed_1217_; lean_object* v_diag_1218_; lean_object* v___x_1220_; uint8_t v_isShared_1221_; uint8_t v_isSharedCheck_1228_; 
v_mctx_1213_ = lean_ctor_get(v_snd_1212_, 1);
lean_inc_ref(v_mctx_1213_);
lean_dec_ref(v_snd_1212_);
v___x_1214_ = lean_st_ref_take(v___y_1208_);
v_cache_1215_ = lean_ctor_get(v___x_1214_, 1);
v_zetaDeltaFVarIds_1216_ = lean_ctor_get(v___x_1214_, 2);
v_postponed_1217_ = lean_ctor_get(v___x_1214_, 3);
v_diag_1218_ = lean_ctor_get(v___x_1214_, 4);
v_isSharedCheck_1228_ = !lean_is_exclusive(v___x_1214_);
if (v_isSharedCheck_1228_ == 0)
{
lean_object* v_unused_1229_; 
v_unused_1229_ = lean_ctor_get(v___x_1214_, 0);
lean_dec(v_unused_1229_);
v___x_1220_ = v___x_1214_;
v_isShared_1221_ = v_isSharedCheck_1228_;
goto v_resetjp_1219_;
}
else
{
lean_inc(v_diag_1218_);
lean_inc(v_postponed_1217_);
lean_inc(v_zetaDeltaFVarIds_1216_);
lean_inc(v_cache_1215_);
lean_dec(v___x_1214_);
v___x_1220_ = lean_box(0);
v_isShared_1221_ = v_isSharedCheck_1228_;
goto v_resetjp_1219_;
}
v_resetjp_1219_:
{
lean_object* v___x_1223_; 
if (v_isShared_1221_ == 0)
{
lean_ctor_set(v___x_1220_, 0, v_mctx_1213_);
v___x_1223_ = v___x_1220_;
goto v_reusejp_1222_;
}
else
{
lean_object* v_reuseFailAlloc_1227_; 
v_reuseFailAlloc_1227_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1227_, 0, v_mctx_1213_);
lean_ctor_set(v_reuseFailAlloc_1227_, 1, v_cache_1215_);
lean_ctor_set(v_reuseFailAlloc_1227_, 2, v_zetaDeltaFVarIds_1216_);
lean_ctor_set(v_reuseFailAlloc_1227_, 3, v_postponed_1217_);
lean_ctor_set(v_reuseFailAlloc_1227_, 4, v_diag_1218_);
v___x_1223_ = v_reuseFailAlloc_1227_;
goto v_reusejp_1222_;
}
v_reusejp_1222_:
{
lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; 
v___x_1224_ = lean_st_ref_put(v___y_1208_, v___x_1223_);
v___x_1225_ = lean_box(v_fst_1211_);
v___x_1226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1226_, 0, v___x_1225_);
return v___x_1226_;
}
}
}
v___jp_1230_:
{
lean_object* v_fst_1232_; lean_object* v_snd_1233_; uint8_t v___x_1234_; 
v_fst_1232_ = lean_ctor_get(v___y_1231_, 0);
lean_inc(v_fst_1232_);
v_snd_1233_ = lean_ctor_get(v___y_1231_, 1);
lean_inc(v_snd_1233_);
lean_dec_ref(v___y_1231_);
v___x_1234_ = lean_unbox(v_fst_1232_);
lean_dec(v_fst_1232_);
v_fst_1211_ = v___x_1234_;
v_snd_1212_ = v_snd_1233_;
goto v___jp_1210_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___boxed(lean_object* v_localDecl_1329_, lean_object* v_fvarId_1330_, lean_object* v_generalizeNondepLet_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_){
_start:
{
uint8_t v_generalizeNondepLet_boxed_1334_; lean_object* v_res_1335_; 
v_generalizeNondepLet_boxed_1334_ = lean_unbox(v_generalizeNondepLet_1331_);
v_res_1335_ = l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg(v_localDecl_1329_, v_fvarId_1330_, v_generalizeNondepLet_boxed_1334_, v___y_1332_);
lean_dec(v___y_1332_);
return v_res_1335_;
}
}
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1(lean_object* v_localDecl_1336_, lean_object* v_fvarId_1337_, uint8_t v_generalizeNondepLet_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_){
_start:
{
lean_object* v___x_1344_; 
v___x_1344_ = l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg(v_localDecl_1336_, v_fvarId_1337_, v_generalizeNondepLet_1338_, v___y_1340_);
return v___x_1344_;
}
}
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___boxed(lean_object* v_localDecl_1345_, lean_object* v_fvarId_1346_, lean_object* v_generalizeNondepLet_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_){
_start:
{
uint8_t v_generalizeNondepLet_boxed_1353_; lean_object* v_res_1354_; 
v_generalizeNondepLet_boxed_1353_ = lean_unbox(v_generalizeNondepLet_1347_);
v_res_1354_ = l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1(v_localDecl_1345_, v_fvarId_1346_, v_generalizeNondepLet_boxed_1353_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_);
lean_dec(v___y_1351_);
lean_dec_ref(v___y_1350_);
lean_dec(v___y_1349_);
lean_dec_ref(v___y_1348_);
return v_res_1354_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2___redArg(lean_object* v_e_1355_, lean_object* v_fvarId_1356_, lean_object* v___y_1357_){
_start:
{
lean_object* v___f_1359_; lean_object* v___f_1360_; lean_object* v___x_1361_; uint8_t v_fst_1363_; lean_object* v_mctx_1364_; lean_object* v___y_1382_; lean_object* v_mctx_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; uint8_t v___x_1390_; 
v___f_1359_ = ((lean_object*)(l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__0));
v___f_1360_ = lean_alloc_closure((void*)(l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1360_, 0, v_fvarId_1356_);
v___x_1361_ = lean_st_ref_get(v___y_1357_);
v_mctx_1387_ = lean_ctor_get(v___x_1361_, 0);
lean_inc_ref_n(v_mctx_1387_, 2);
lean_dec(v___x_1361_);
v___x_1388_ = lean_obj_once(&l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__2, &l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__2_once, _init_l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__2);
v___x_1389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1389_, 0, v___x_1388_);
lean_ctor_set(v___x_1389_, 1, v_mctx_1387_);
v___x_1390_ = l_Lean_Expr_hasFVar(v_e_1355_);
if (v___x_1390_ == 0)
{
uint8_t v___x_1391_; 
v___x_1391_ = l_Lean_Expr_hasMVar(v_e_1355_);
if (v___x_1391_ == 0)
{
lean_dec_ref_known(v___x_1389_, 2);
lean_dec_ref(v___f_1360_);
lean_dec_ref(v_e_1355_);
v_fst_1363_ = v___x_1391_;
v_mctx_1364_ = v_mctx_1387_;
goto v___jp_1362_;
}
else
{
lean_object* v___x_1392_; 
lean_dec_ref(v_mctx_1387_);
v___x_1392_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1360_, v___f_1359_, v_e_1355_, v___x_1389_);
v___y_1382_ = v___x_1392_;
goto v___jp_1381_;
}
}
else
{
lean_object* v___x_1393_; 
lean_dec_ref(v_mctx_1387_);
v___x_1393_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1360_, v___f_1359_, v_e_1355_, v___x_1389_);
v___y_1382_ = v___x_1393_;
goto v___jp_1381_;
}
v___jp_1362_:
{
lean_object* v___x_1365_; lean_object* v_cache_1366_; lean_object* v_zetaDeltaFVarIds_1367_; lean_object* v_postponed_1368_; lean_object* v_diag_1369_; lean_object* v___x_1371_; uint8_t v_isShared_1372_; uint8_t v_isSharedCheck_1379_; 
v___x_1365_ = lean_st_ref_take(v___y_1357_);
v_cache_1366_ = lean_ctor_get(v___x_1365_, 1);
v_zetaDeltaFVarIds_1367_ = lean_ctor_get(v___x_1365_, 2);
v_postponed_1368_ = lean_ctor_get(v___x_1365_, 3);
v_diag_1369_ = lean_ctor_get(v___x_1365_, 4);
v_isSharedCheck_1379_ = !lean_is_exclusive(v___x_1365_);
if (v_isSharedCheck_1379_ == 0)
{
lean_object* v_unused_1380_; 
v_unused_1380_ = lean_ctor_get(v___x_1365_, 0);
lean_dec(v_unused_1380_);
v___x_1371_ = v___x_1365_;
v_isShared_1372_ = v_isSharedCheck_1379_;
goto v_resetjp_1370_;
}
else
{
lean_inc(v_diag_1369_);
lean_inc(v_postponed_1368_);
lean_inc(v_zetaDeltaFVarIds_1367_);
lean_inc(v_cache_1366_);
lean_dec(v___x_1365_);
v___x_1371_ = lean_box(0);
v_isShared_1372_ = v_isSharedCheck_1379_;
goto v_resetjp_1370_;
}
v_resetjp_1370_:
{
lean_object* v___x_1374_; 
if (v_isShared_1372_ == 0)
{
lean_ctor_set(v___x_1371_, 0, v_mctx_1364_);
v___x_1374_ = v___x_1371_;
goto v_reusejp_1373_;
}
else
{
lean_object* v_reuseFailAlloc_1378_; 
v_reuseFailAlloc_1378_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1378_, 0, v_mctx_1364_);
lean_ctor_set(v_reuseFailAlloc_1378_, 1, v_cache_1366_);
lean_ctor_set(v_reuseFailAlloc_1378_, 2, v_zetaDeltaFVarIds_1367_);
lean_ctor_set(v_reuseFailAlloc_1378_, 3, v_postponed_1368_);
lean_ctor_set(v_reuseFailAlloc_1378_, 4, v_diag_1369_);
v___x_1374_ = v_reuseFailAlloc_1378_;
goto v_reusejp_1373_;
}
v_reusejp_1373_:
{
lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; 
v___x_1375_ = lean_st_ref_put(v___y_1357_, v___x_1374_);
v___x_1376_ = lean_box(v_fst_1363_);
v___x_1377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1377_, 0, v___x_1376_);
return v___x_1377_;
}
}
}
v___jp_1381_:
{
lean_object* v_snd_1383_; lean_object* v_fst_1384_; lean_object* v_mctx_1385_; uint8_t v___x_1386_; 
v_snd_1383_ = lean_ctor_get(v___y_1382_, 1);
lean_inc(v_snd_1383_);
v_fst_1384_ = lean_ctor_get(v___y_1382_, 0);
lean_inc(v_fst_1384_);
lean_dec_ref(v___y_1382_);
v_mctx_1385_ = lean_ctor_get(v_snd_1383_, 1);
lean_inc_ref(v_mctx_1385_);
lean_dec(v_snd_1383_);
v___x_1386_ = lean_unbox(v_fst_1384_);
lean_dec(v_fst_1384_);
v_fst_1363_ = v___x_1386_;
v_mctx_1364_ = v_mctx_1385_;
goto v___jp_1362_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2___redArg___boxed(lean_object* v_e_1394_, lean_object* v_fvarId_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_){
_start:
{
lean_object* v_res_1398_; 
v_res_1398_ = l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2___redArg(v_e_1394_, v_fvarId_1395_, v___y_1396_);
lean_dec(v___y_1396_);
return v_res_1398_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2(lean_object* v_e_1399_, lean_object* v_fvarId_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_){
_start:
{
lean_object* v___x_1406_; 
v___x_1406_ = l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2___redArg(v_e_1399_, v_fvarId_1400_, v___y_1402_);
return v___x_1406_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2___boxed(lean_object* v_e_1407_, lean_object* v_fvarId_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_){
_start:
{
lean_object* v_res_1414_; 
v_res_1414_ = l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2(v_e_1407_, v_fvarId_1408_, v___y_1409_, v___y_1410_, v___y_1411_, v___y_1412_);
lean_dec(v___y_1412_);
lean_dec_ref(v___y_1411_);
lean_dec(v___y_1410_);
lean_dec_ref(v___y_1409_);
return v_res_1414_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_Meta_getMajorTypeIndices_spec__0(lean_object* v_a_1415_, lean_object* v_x_1416_){
_start:
{
if (lean_obj_tag(v_x_1416_) == 0)
{
uint8_t v___x_1417_; 
v___x_1417_ = 0;
return v___x_1417_;
}
else
{
lean_object* v_head_1418_; lean_object* v_tail_1419_; uint8_t v___x_1420_; 
v_head_1418_ = lean_ctor_get(v_x_1416_, 0);
v_tail_1419_ = lean_ctor_get(v_x_1416_, 1);
v___x_1420_ = lean_nat_dec_eq(v_a_1415_, v_head_1418_);
if (v___x_1420_ == 0)
{
v_x_1416_ = v_tail_1419_;
goto _start;
}
else
{
return v___x_1420_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_Meta_getMajorTypeIndices_spec__0___boxed(lean_object* v_a_1422_, lean_object* v_x_1423_){
_start:
{
uint8_t v_res_1424_; lean_object* v_r_1425_; 
v_res_1424_ = l_List_elem___at___00Lean_Meta_getMajorTypeIndices_spec__0(v_a_1422_, v_x_1423_);
lean_dec(v_x_1423_);
lean_dec(v_a_1422_);
v_r_1425_ = lean_box(v_res_1424_);
return v_r_1425_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_1427_; lean_object* v___x_1428_; 
v___x_1427_ = ((lean_object*)(l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__0));
v___x_1428_ = l_Lean_stringToMessageData(v___x_1427_);
return v___x_1428_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_1430_; lean_object* v___x_1431_; 
v___x_1430_ = ((lean_object*)(l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__2));
v___x_1431_ = l_Lean_stringToMessageData(v___x_1430_);
return v___x_1431_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__5(void){
_start:
{
lean_object* v___x_1433_; lean_object* v___x_1434_; 
v___x_1433_ = ((lean_object*)(l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__4));
v___x_1434_ = l_Lean_stringToMessageData(v___x_1433_);
return v___x_1434_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__7(void){
_start:
{
lean_object* v___x_1436_; lean_object* v___x_1437_; 
v___x_1436_ = ((lean_object*)(l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__6));
v___x_1437_ = l_Lean_stringToMessageData(v___x_1436_);
return v___x_1437_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg(lean_object* v_majorTypeArgs_1438_, lean_object* v_idxPos_1439_, lean_object* v_recursorInfo_1440_, lean_object* v_idx_1441_, lean_object* v_tacticName_1442_, lean_object* v_mvarId_1443_, lean_object* v_majorType_1444_, lean_object* v_n_1445_, lean_object* v_i_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_){
_start:
{
lean_object* v_zero_1452_; uint8_t v_isZero_1453_; 
v_zero_1452_ = lean_unsigned_to_nat(0u);
v_isZero_1453_ = lean_nat_dec_eq(v_i_1446_, v_zero_1452_);
if (v_isZero_1453_ == 1)
{
lean_object* v___x_1454_; lean_object* v___x_1455_; 
lean_dec(v_i_1446_);
lean_dec_ref(v_majorType_1444_);
lean_dec(v_mvarId_1443_);
lean_dec(v_tacticName_1442_);
lean_dec_ref(v_idx_1441_);
v___x_1454_ = lean_box(0);
v___x_1455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1455_, 0, v___x_1454_);
return v___x_1455_;
}
else
{
lean_object* v_one_1456_; lean_object* v_n_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v_arg_1460_; lean_object* v___y_1462_; lean_object* v___y_1463_; lean_object* v___y_1464_; lean_object* v___y_1465_; lean_object* v___y_1509_; lean_object* v___y_1510_; lean_object* v___y_1511_; lean_object* v___y_1512_; uint8_t v___x_1533_; 
v_one_1456_ = lean_unsigned_to_nat(1u);
v_n_1457_ = lean_nat_sub(v_i_1446_, v_one_1456_);
lean_dec(v_i_1446_);
v___x_1458_ = lean_nat_sub(v_n_1445_, v_n_1457_);
v___x_1459_ = lean_nat_sub(v___x_1458_, v_one_1456_);
lean_dec(v___x_1458_);
v_arg_1460_ = lean_array_fget_borrowed(v_majorTypeArgs_1438_, v___x_1459_);
v___x_1533_ = lean_nat_dec_eq(v___x_1459_, v_idxPos_1439_);
if (v___x_1533_ == 0)
{
uint8_t v___x_1534_; 
v___x_1534_ = lean_expr_eqv(v_arg_1460_, v_idx_1441_);
if (v___x_1534_ == 0)
{
v___y_1509_ = v___y_1447_;
v___y_1510_ = v___y_1448_;
v___y_1511_ = v___y_1449_;
v___y_1512_ = v___y_1450_;
goto v___jp_1508_;
}
else
{
lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; 
v___x_1535_ = lean_obj_once(&l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1, &l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1_once, _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1);
lean_inc_ref(v_idx_1441_);
v___x_1536_ = l_Lean_MessageData_ofExpr(v_idx_1441_);
v___x_1537_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1537_, 0, v___x_1535_);
lean_ctor_set(v___x_1537_, 1, v___x_1536_);
v___x_1538_ = lean_obj_once(&l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__7, &l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__7_once, _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__7);
v___x_1539_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1539_, 0, v___x_1537_);
lean_ctor_set(v___x_1539_, 1, v___x_1538_);
lean_inc_ref(v_majorType_1444_);
v___x_1540_ = l_Lean_indentExpr(v_majorType_1444_);
v___x_1541_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1541_, 0, v___x_1539_);
lean_ctor_set(v___x_1541_, 1, v___x_1540_);
v___x_1542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1542_, 0, v___x_1541_);
lean_inc(v_mvarId_1443_);
lean_inc(v_tacticName_1442_);
v___x_1543_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1442_, v_mvarId_1443_, v___x_1542_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_);
if (lean_obj_tag(v___x_1543_) == 0)
{
lean_dec_ref_known(v___x_1543_, 1);
v___y_1509_ = v___y_1447_;
v___y_1510_ = v___y_1448_;
v___y_1511_ = v___y_1449_;
v___y_1512_ = v___y_1450_;
goto v___jp_1508_;
}
else
{
lean_dec(v___x_1459_);
lean_dec(v_n_1457_);
lean_dec_ref(v_majorType_1444_);
lean_dec(v_mvarId_1443_);
lean_dec(v_tacticName_1442_);
lean_dec_ref(v_idx_1441_);
return v___x_1543_;
}
}
}
else
{
v___y_1509_ = v___y_1447_;
v___y_1510_ = v___y_1448_;
v___y_1511_ = v___y_1449_;
v___y_1512_ = v___y_1450_;
goto v___jp_1508_;
}
v___jp_1461_:
{
uint8_t v___x_1466_; 
v___x_1466_ = lean_nat_dec_lt(v_idxPos_1439_, v___x_1459_);
if (v___x_1466_ == 0)
{
lean_dec(v___x_1459_);
v_i_1446_ = v_n_1457_;
goto _start;
}
else
{
lean_object* v_indicesPos_1468_; uint8_t v___x_1469_; 
v_indicesPos_1468_ = lean_ctor_get(v_recursorInfo_1440_, 6);
v___x_1469_ = l_List_elem___at___00Lean_Meta_getMajorTypeIndices_spec__0(v___x_1459_, v_indicesPos_1468_);
if (v___x_1469_ == 0)
{
lean_dec(v___x_1459_);
v_i_1446_ = v_n_1457_;
goto _start;
}
else
{
uint8_t v___x_1471_; 
v___x_1471_ = l_Lean_Expr_isFVar(v_arg_1460_);
if (v___x_1471_ == 0)
{
lean_dec(v___x_1459_);
v_i_1446_ = v_n_1457_;
goto _start;
}
else
{
lean_object* v___x_1473_; lean_object* v___x_1474_; 
v___x_1473_ = l_Lean_Expr_fvarId_x21(v_idx_1441_);
v___x_1474_ = l_Lean_FVarId_getDecl___redArg(v___x_1473_, v___y_1462_, v___y_1464_, v___y_1465_);
if (lean_obj_tag(v___x_1474_) == 0)
{
lean_object* v_a_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v_a_1478_; lean_object* v___x_1480_; uint8_t v_isShared_1481_; uint8_t v_isSharedCheck_1499_; 
v_a_1475_ = lean_ctor_get(v___x_1474_, 0);
lean_inc(v_a_1475_);
lean_dec_ref_known(v___x_1474_, 1);
v___x_1476_ = l_Lean_Expr_fvarId_x21(v_arg_1460_);
v___x_1477_ = l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg(v_a_1475_, v___x_1476_, v___x_1469_, v___y_1463_);
v_a_1478_ = lean_ctor_get(v___x_1477_, 0);
v_isSharedCheck_1499_ = !lean_is_exclusive(v___x_1477_);
if (v_isSharedCheck_1499_ == 0)
{
v___x_1480_ = v___x_1477_;
v_isShared_1481_ = v_isSharedCheck_1499_;
goto v_resetjp_1479_;
}
else
{
lean_inc(v_a_1478_);
lean_dec(v___x_1477_);
v___x_1480_ = lean_box(0);
v_isShared_1481_ = v_isSharedCheck_1499_;
goto v_resetjp_1479_;
}
v_resetjp_1479_:
{
uint8_t v___x_1482_; 
v___x_1482_ = lean_unbox(v_a_1478_);
lean_dec(v_a_1478_);
if (v___x_1482_ == 0)
{
lean_del_object(v___x_1480_);
lean_dec(v___x_1459_);
v_i_1446_ = v_n_1457_;
goto _start;
}
else
{
lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1492_; 
v___x_1484_ = lean_obj_once(&l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1, &l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1_once, _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1);
lean_inc_ref(v_idx_1441_);
v___x_1485_ = l_Lean_MessageData_ofExpr(v_idx_1441_);
v___x_1486_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1486_, 0, v___x_1484_);
lean_ctor_set(v___x_1486_, 1, v___x_1485_);
v___x_1487_ = lean_obj_once(&l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__3, &l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__3_once, _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__3);
v___x_1488_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1488_, 0, v___x_1486_);
lean_ctor_set(v___x_1488_, 1, v___x_1487_);
v___x_1489_ = lean_nat_add(v___x_1459_, v_one_1456_);
lean_dec(v___x_1459_);
v___x_1490_ = l_Nat_reprFast(v___x_1489_);
if (v_isShared_1481_ == 0)
{
lean_ctor_set_tag(v___x_1480_, 3);
lean_ctor_set(v___x_1480_, 0, v___x_1490_);
v___x_1492_ = v___x_1480_;
goto v_reusejp_1491_;
}
else
{
lean_object* v_reuseFailAlloc_1498_; 
v_reuseFailAlloc_1498_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1498_, 0, v___x_1490_);
v___x_1492_ = v_reuseFailAlloc_1498_;
goto v_reusejp_1491_;
}
v_reusejp_1491_:
{
lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; 
v___x_1493_ = l_Lean_MessageData_ofFormat(v___x_1492_);
v___x_1494_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1494_, 0, v___x_1488_);
lean_ctor_set(v___x_1494_, 1, v___x_1493_);
v___x_1495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1495_, 0, v___x_1494_);
lean_inc(v_mvarId_1443_);
lean_inc(v_tacticName_1442_);
v___x_1496_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1442_, v_mvarId_1443_, v___x_1495_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_);
if (lean_obj_tag(v___x_1496_) == 0)
{
lean_dec_ref_known(v___x_1496_, 1);
v_i_1446_ = v_n_1457_;
goto _start;
}
else
{
lean_dec(v_n_1457_);
lean_dec_ref(v_majorType_1444_);
lean_dec(v_mvarId_1443_);
lean_dec(v_tacticName_1442_);
lean_dec_ref(v_idx_1441_);
return v___x_1496_;
}
}
}
}
}
else
{
lean_object* v_a_1500_; lean_object* v___x_1502_; uint8_t v_isShared_1503_; uint8_t v_isSharedCheck_1507_; 
lean_dec(v___x_1459_);
lean_dec(v_n_1457_);
lean_dec_ref(v_majorType_1444_);
lean_dec(v_mvarId_1443_);
lean_dec(v_tacticName_1442_);
lean_dec_ref(v_idx_1441_);
v_a_1500_ = lean_ctor_get(v___x_1474_, 0);
v_isSharedCheck_1507_ = !lean_is_exclusive(v___x_1474_);
if (v_isSharedCheck_1507_ == 0)
{
v___x_1502_ = v___x_1474_;
v_isShared_1503_ = v_isSharedCheck_1507_;
goto v_resetjp_1501_;
}
else
{
lean_inc(v_a_1500_);
lean_dec(v___x_1474_);
v___x_1502_ = lean_box(0);
v_isShared_1503_ = v_isSharedCheck_1507_;
goto v_resetjp_1501_;
}
v_resetjp_1501_:
{
lean_object* v___x_1505_; 
if (v_isShared_1503_ == 0)
{
v___x_1505_ = v___x_1502_;
goto v_reusejp_1504_;
}
else
{
lean_object* v_reuseFailAlloc_1506_; 
v_reuseFailAlloc_1506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1506_, 0, v_a_1500_);
v___x_1505_ = v_reuseFailAlloc_1506_;
goto v_reusejp_1504_;
}
v_reusejp_1504_:
{
return v___x_1505_;
}
}
}
}
}
}
}
v___jp_1508_:
{
uint8_t v___x_1513_; 
v___x_1513_ = lean_nat_dec_lt(v___x_1459_, v_idxPos_1439_);
if (v___x_1513_ == 0)
{
v___y_1462_ = v___y_1509_;
v___y_1463_ = v___y_1510_;
v___y_1464_ = v___y_1511_;
v___y_1465_ = v___y_1512_;
goto v___jp_1461_;
}
else
{
lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v_a_1516_; lean_object* v___x_1518_; uint8_t v_isShared_1519_; uint8_t v_isSharedCheck_1532_; 
v___x_1514_ = l_Lean_Expr_fvarId_x21(v_idx_1441_);
lean_inc(v_arg_1460_);
v___x_1515_ = l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2___redArg(v_arg_1460_, v___x_1514_, v___y_1510_);
v_a_1516_ = lean_ctor_get(v___x_1515_, 0);
v_isSharedCheck_1532_ = !lean_is_exclusive(v___x_1515_);
if (v_isSharedCheck_1532_ == 0)
{
v___x_1518_ = v___x_1515_;
v_isShared_1519_ = v_isSharedCheck_1532_;
goto v_resetjp_1517_;
}
else
{
lean_inc(v_a_1516_);
lean_dec(v___x_1515_);
v___x_1518_ = lean_box(0);
v_isShared_1519_ = v_isSharedCheck_1532_;
goto v_resetjp_1517_;
}
v_resetjp_1517_:
{
uint8_t v___x_1520_; 
v___x_1520_ = lean_unbox(v_a_1516_);
lean_dec(v_a_1516_);
if (v___x_1520_ == 0)
{
lean_del_object(v___x_1518_);
v___y_1462_ = v___y_1509_;
v___y_1463_ = v___y_1510_;
v___y_1464_ = v___y_1511_;
v___y_1465_ = v___y_1512_;
goto v___jp_1461_;
}
else
{
lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1529_; 
v___x_1521_ = lean_obj_once(&l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1, &l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1_once, _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1);
lean_inc_ref(v_idx_1441_);
v___x_1522_ = l_Lean_MessageData_ofExpr(v_idx_1441_);
v___x_1523_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1523_, 0, v___x_1521_);
lean_ctor_set(v___x_1523_, 1, v___x_1522_);
v___x_1524_ = lean_obj_once(&l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__5, &l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__5_once, _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__5);
v___x_1525_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1525_, 0, v___x_1523_);
lean_ctor_set(v___x_1525_, 1, v___x_1524_);
lean_inc_ref(v_majorType_1444_);
v___x_1526_ = l_Lean_indentExpr(v_majorType_1444_);
v___x_1527_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1527_, 0, v___x_1525_);
lean_ctor_set(v___x_1527_, 1, v___x_1526_);
if (v_isShared_1519_ == 0)
{
lean_ctor_set_tag(v___x_1518_, 1);
lean_ctor_set(v___x_1518_, 0, v___x_1527_);
v___x_1529_ = v___x_1518_;
goto v_reusejp_1528_;
}
else
{
lean_object* v_reuseFailAlloc_1531_; 
v_reuseFailAlloc_1531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1531_, 0, v___x_1527_);
v___x_1529_ = v_reuseFailAlloc_1531_;
goto v_reusejp_1528_;
}
v_reusejp_1528_:
{
lean_object* v___x_1530_; 
lean_inc(v_mvarId_1443_);
lean_inc(v_tacticName_1442_);
v___x_1530_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1442_, v_mvarId_1443_, v___x_1529_, v___y_1509_, v___y_1510_, v___y_1511_, v___y_1512_);
if (lean_obj_tag(v___x_1530_) == 0)
{
lean_dec_ref_known(v___x_1530_, 1);
v___y_1462_ = v___y_1509_;
v___y_1463_ = v___y_1510_;
v___y_1464_ = v___y_1511_;
v___y_1465_ = v___y_1512_;
goto v___jp_1461_;
}
else
{
lean_dec(v___x_1459_);
lean_dec(v_n_1457_);
lean_dec_ref(v_majorType_1444_);
lean_dec(v_mvarId_1443_);
lean_dec(v_tacticName_1442_);
lean_dec_ref(v_idx_1441_);
return v___x_1530_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___boxed(lean_object* v_majorTypeArgs_1544_, lean_object* v_idxPos_1545_, lean_object* v_recursorInfo_1546_, lean_object* v_idx_1547_, lean_object* v_tacticName_1548_, lean_object* v_mvarId_1549_, lean_object* v_majorType_1550_, lean_object* v_n_1551_, lean_object* v_i_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_){
_start:
{
lean_object* v_res_1558_; 
v_res_1558_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg(v_majorTypeArgs_1544_, v_idxPos_1545_, v_recursorInfo_1546_, v_idx_1547_, v_tacticName_1548_, v_mvarId_1549_, v_majorType_1550_, v_n_1551_, v_i_1552_, v___y_1553_, v___y_1554_, v___y_1555_, v___y_1556_);
lean_dec(v___y_1556_);
lean_dec_ref(v___y_1555_);
lean_dec(v___y_1554_);
lean_dec_ref(v___y_1553_);
lean_dec(v_n_1551_);
lean_dec_ref(v_recursorInfo_1546_);
lean_dec(v_idxPos_1545_);
lean_dec_ref(v_majorTypeArgs_1544_);
return v_res_1558_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__1(void){
_start:
{
lean_object* v___x_1560_; lean_object* v___x_1561_; 
v___x_1560_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__0));
v___x_1561_ = l_Lean_stringToMessageData(v___x_1560_);
return v___x_1561_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__3(void){
_start:
{
lean_object* v___x_1563_; lean_object* v___x_1564_; 
v___x_1563_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__2));
v___x_1564_ = l_Lean_stringToMessageData(v___x_1563_);
return v___x_1564_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__5(void){
_start:
{
lean_object* v___x_1566_; lean_object* v___x_1567_; 
v___x_1566_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__4));
v___x_1567_ = l_Lean_stringToMessageData(v___x_1566_);
return v___x_1567_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4(lean_object* v_majorTypeArgs_1568_, lean_object* v_recursorInfo_1569_, lean_object* v_tacticName_1570_, lean_object* v_mvarId_1571_, lean_object* v_majorType_1572_, size_t v_sz_1573_, size_t v_i_1574_, lean_object* v_bs_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_){
_start:
{
uint8_t v___x_1581_; 
v___x_1581_ = lean_usize_dec_lt(v_i_1574_, v_sz_1573_);
if (v___x_1581_ == 0)
{
lean_object* v___x_1582_; 
lean_dec_ref(v_majorType_1572_);
lean_dec(v_mvarId_1571_);
lean_dec(v_tacticName_1570_);
v___x_1582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1582_, 0, v_bs_1575_);
return v___x_1582_;
}
else
{
lean_object* v_v_1583_; lean_object* v___x_1584_; lean_object* v_bs_x27_1585_; lean_object* v_a_1587_; lean_object* v___x_1592_; uint8_t v___x_1593_; 
v_v_1583_ = lean_array_uget(v_bs_1575_, v_i_1574_);
v___x_1584_ = lean_unsigned_to_nat(0u);
v_bs_x27_1585_ = lean_array_uset(v_bs_1575_, v_i_1574_, v___x_1584_);
v___x_1592_ = lean_array_get_size(v_majorTypeArgs_1568_);
v___x_1593_ = lean_nat_dec_le(v___x_1592_, v_v_1583_);
if (v___x_1593_ == 0)
{
lean_object* v_idx_1594_; lean_object* v___y_1596_; lean_object* v___y_1597_; lean_object* v___y_1598_; lean_object* v___y_1599_; uint8_t v___x_1609_; 
v_idx_1594_ = lean_array_fget_borrowed(v_majorTypeArgs_1568_, v_v_1583_);
v___x_1609_ = l_Lean_Expr_isFVar(v_idx_1594_);
if (v___x_1609_ == 0)
{
lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; 
v___x_1610_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__1);
lean_inc(v_idx_1594_);
v___x_1611_ = l_Lean_MessageData_ofExpr(v_idx_1594_);
v___x_1612_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1612_, 0, v___x_1610_);
lean_ctor_set(v___x_1612_, 1, v___x_1611_);
v___x_1613_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__3);
v___x_1614_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1614_, 0, v___x_1612_);
lean_ctor_set(v___x_1614_, 1, v___x_1613_);
lean_inc_ref(v_majorType_1572_);
v___x_1615_ = l_Lean_indentExpr(v_majorType_1572_);
v___x_1616_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1616_, 0, v___x_1614_);
lean_ctor_set(v___x_1616_, 1, v___x_1615_);
v___x_1617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1617_, 0, v___x_1616_);
lean_inc(v_mvarId_1571_);
lean_inc(v_tacticName_1570_);
v___x_1618_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1570_, v_mvarId_1571_, v___x_1617_, v___y_1576_, v___y_1577_, v___y_1578_, v___y_1579_);
if (lean_obj_tag(v___x_1618_) == 0)
{
lean_dec_ref_known(v___x_1618_, 1);
v___y_1596_ = v___y_1576_;
v___y_1597_ = v___y_1577_;
v___y_1598_ = v___y_1578_;
v___y_1599_ = v___y_1579_;
goto v___jp_1595_;
}
else
{
lean_object* v_a_1619_; lean_object* v___x_1621_; uint8_t v_isShared_1622_; uint8_t v_isSharedCheck_1626_; 
lean_dec_ref(v_bs_x27_1585_);
lean_dec(v_v_1583_);
lean_dec_ref(v_majorType_1572_);
lean_dec(v_mvarId_1571_);
lean_dec(v_tacticName_1570_);
v_a_1619_ = lean_ctor_get(v___x_1618_, 0);
v_isSharedCheck_1626_ = !lean_is_exclusive(v___x_1618_);
if (v_isSharedCheck_1626_ == 0)
{
v___x_1621_ = v___x_1618_;
v_isShared_1622_ = v_isSharedCheck_1626_;
goto v_resetjp_1620_;
}
else
{
lean_inc(v_a_1619_);
lean_dec(v___x_1618_);
v___x_1621_ = lean_box(0);
v_isShared_1622_ = v_isSharedCheck_1626_;
goto v_resetjp_1620_;
}
v_resetjp_1620_:
{
lean_object* v___x_1624_; 
if (v_isShared_1622_ == 0)
{
v___x_1624_ = v___x_1621_;
goto v_reusejp_1623_;
}
else
{
lean_object* v_reuseFailAlloc_1625_; 
v_reuseFailAlloc_1625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1625_, 0, v_a_1619_);
v___x_1624_ = v_reuseFailAlloc_1625_;
goto v_reusejp_1623_;
}
v_reusejp_1623_:
{
return v___x_1624_;
}
}
}
}
else
{
v___y_1596_ = v___y_1576_;
v___y_1597_ = v___y_1577_;
v___y_1598_ = v___y_1578_;
v___y_1599_ = v___y_1579_;
goto v___jp_1595_;
}
v___jp_1595_:
{
lean_object* v___x_1600_; 
lean_inc_ref(v_majorType_1572_);
lean_inc(v_mvarId_1571_);
lean_inc(v_tacticName_1570_);
lean_inc(v_idx_1594_);
v___x_1600_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg(v_majorTypeArgs_1568_, v_v_1583_, v_recursorInfo_1569_, v_idx_1594_, v_tacticName_1570_, v_mvarId_1571_, v_majorType_1572_, v___x_1592_, v___x_1592_, v___y_1596_, v___y_1597_, v___y_1598_, v___y_1599_);
lean_dec(v_v_1583_);
if (lean_obj_tag(v___x_1600_) == 0)
{
lean_dec_ref_known(v___x_1600_, 1);
lean_inc(v_idx_1594_);
v_a_1587_ = v_idx_1594_;
goto v___jp_1586_;
}
else
{
lean_object* v_a_1601_; lean_object* v___x_1603_; uint8_t v_isShared_1604_; uint8_t v_isSharedCheck_1608_; 
lean_dec_ref(v_bs_x27_1585_);
lean_dec_ref(v_majorType_1572_);
lean_dec(v_mvarId_1571_);
lean_dec(v_tacticName_1570_);
v_a_1601_ = lean_ctor_get(v___x_1600_, 0);
v_isSharedCheck_1608_ = !lean_is_exclusive(v___x_1600_);
if (v_isSharedCheck_1608_ == 0)
{
v___x_1603_ = v___x_1600_;
v_isShared_1604_ = v_isSharedCheck_1608_;
goto v_resetjp_1602_;
}
else
{
lean_inc(v_a_1601_);
lean_dec(v___x_1600_);
v___x_1603_ = lean_box(0);
v_isShared_1604_ = v_isSharedCheck_1608_;
goto v_resetjp_1602_;
}
v_resetjp_1602_:
{
lean_object* v___x_1606_; 
if (v_isShared_1604_ == 0)
{
v___x_1606_ = v___x_1603_;
goto v_reusejp_1605_;
}
else
{
lean_object* v_reuseFailAlloc_1607_; 
v_reuseFailAlloc_1607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1607_, 0, v_a_1601_);
v___x_1606_ = v_reuseFailAlloc_1607_;
goto v_reusejp_1605_;
}
v_reusejp_1605_:
{
return v___x_1606_;
}
}
}
}
}
else
{
lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; 
lean_dec(v_v_1583_);
v___x_1627_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__5, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__5);
lean_inc_ref(v_majorType_1572_);
v___x_1628_ = l_Lean_indentExpr(v_majorType_1572_);
v___x_1629_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1629_, 0, v___x_1627_);
lean_ctor_set(v___x_1629_, 1, v___x_1628_);
v___x_1630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1630_, 0, v___x_1629_);
lean_inc(v_mvarId_1571_);
lean_inc(v_tacticName_1570_);
v___x_1631_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1570_, v_mvarId_1571_, v___x_1630_, v___y_1576_, v___y_1577_, v___y_1578_, v___y_1579_);
if (lean_obj_tag(v___x_1631_) == 0)
{
lean_object* v_a_1632_; 
v_a_1632_ = lean_ctor_get(v___x_1631_, 0);
lean_inc(v_a_1632_);
lean_dec_ref_known(v___x_1631_, 1);
v_a_1587_ = v_a_1632_;
goto v___jp_1586_;
}
else
{
lean_object* v_a_1633_; lean_object* v___x_1635_; uint8_t v_isShared_1636_; uint8_t v_isSharedCheck_1640_; 
lean_dec_ref(v_bs_x27_1585_);
lean_dec_ref(v_majorType_1572_);
lean_dec(v_mvarId_1571_);
lean_dec(v_tacticName_1570_);
v_a_1633_ = lean_ctor_get(v___x_1631_, 0);
v_isSharedCheck_1640_ = !lean_is_exclusive(v___x_1631_);
if (v_isSharedCheck_1640_ == 0)
{
v___x_1635_ = v___x_1631_;
v_isShared_1636_ = v_isSharedCheck_1640_;
goto v_resetjp_1634_;
}
else
{
lean_inc(v_a_1633_);
lean_dec(v___x_1631_);
v___x_1635_ = lean_box(0);
v_isShared_1636_ = v_isSharedCheck_1640_;
goto v_resetjp_1634_;
}
v_resetjp_1634_:
{
lean_object* v___x_1638_; 
if (v_isShared_1636_ == 0)
{
v___x_1638_ = v___x_1635_;
goto v_reusejp_1637_;
}
else
{
lean_object* v_reuseFailAlloc_1639_; 
v_reuseFailAlloc_1639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1639_, 0, v_a_1633_);
v___x_1638_ = v_reuseFailAlloc_1639_;
goto v_reusejp_1637_;
}
v_reusejp_1637_:
{
return v___x_1638_;
}
}
}
}
v___jp_1586_:
{
size_t v___x_1588_; size_t v___x_1589_; lean_object* v___x_1590_; 
v___x_1588_ = ((size_t)1ULL);
v___x_1589_ = lean_usize_add(v_i_1574_, v___x_1588_);
v___x_1590_ = lean_array_uset(v_bs_x27_1585_, v_i_1574_, v_a_1587_);
v_i_1574_ = v___x_1589_;
v_bs_1575_ = v___x_1590_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___boxed(lean_object* v_majorTypeArgs_1641_, lean_object* v_recursorInfo_1642_, lean_object* v_tacticName_1643_, lean_object* v_mvarId_1644_, lean_object* v_majorType_1645_, lean_object* v_sz_1646_, lean_object* v_i_1647_, lean_object* v_bs_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_){
_start:
{
size_t v_sz_boxed_1654_; size_t v_i_boxed_1655_; lean_object* v_res_1656_; 
v_sz_boxed_1654_ = lean_unbox_usize(v_sz_1646_);
lean_dec(v_sz_1646_);
v_i_boxed_1655_ = lean_unbox_usize(v_i_1647_);
lean_dec(v_i_1647_);
v_res_1656_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4(v_majorTypeArgs_1641_, v_recursorInfo_1642_, v_tacticName_1643_, v_mvarId_1644_, v_majorType_1645_, v_sz_boxed_1654_, v_i_boxed_1655_, v_bs_1648_, v___y_1649_, v___y_1650_, v___y_1651_, v___y_1652_);
lean_dec(v___y_1652_);
lean_dec_ref(v___y_1651_);
lean_dec(v___y_1650_);
lean_dec_ref(v___y_1649_);
lean_dec_ref(v_recursorInfo_1642_);
lean_dec_ref(v_majorTypeArgs_1641_);
return v_res_1656_;
}
}
static lean_object* _init_l_Lean_Meta_getMajorTypeIndices___closed__0(void){
_start:
{
lean_object* v___x_1657_; lean_object* v_dummy_1658_; 
v___x_1657_ = lean_box(0);
v_dummy_1658_ = l_Lean_Expr_sort___override(v___x_1657_);
return v_dummy_1658_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMajorTypeIndices(lean_object* v_mvarId_1659_, lean_object* v_tacticName_1660_, lean_object* v_recursorInfo_1661_, lean_object* v_majorType_1662_, lean_object* v_a_1663_, lean_object* v_a_1664_, lean_object* v_a_1665_, lean_object* v_a_1666_){
_start:
{
lean_object* v_indicesPos_1668_; lean_object* v_nargs_1669_; lean_object* v_dummy_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v_majorTypeArgs_1674_; lean_object* v___x_1675_; size_t v_sz_1676_; size_t v___x_1677_; lean_object* v___x_1678_; 
v_indicesPos_1668_ = lean_ctor_get(v_recursorInfo_1661_, 6);
v_nargs_1669_ = l_Lean_Expr_getAppNumArgs(v_majorType_1662_);
v_dummy_1670_ = lean_obj_once(&l_Lean_Meta_getMajorTypeIndices___closed__0, &l_Lean_Meta_getMajorTypeIndices___closed__0_once, _init_l_Lean_Meta_getMajorTypeIndices___closed__0);
lean_inc(v_nargs_1669_);
v___x_1671_ = lean_mk_array(v_nargs_1669_, v_dummy_1670_);
v___x_1672_ = lean_unsigned_to_nat(1u);
v___x_1673_ = lean_nat_sub(v_nargs_1669_, v___x_1672_);
lean_dec(v_nargs_1669_);
lean_inc_ref(v_majorType_1662_);
v_majorTypeArgs_1674_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_majorType_1662_, v___x_1671_, v___x_1673_);
lean_inc(v_indicesPos_1668_);
v___x_1675_ = lean_array_mk(v_indicesPos_1668_);
v_sz_1676_ = lean_array_size(v___x_1675_);
v___x_1677_ = ((size_t)0ULL);
v___x_1678_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4(v_majorTypeArgs_1674_, v_recursorInfo_1661_, v_tacticName_1660_, v_mvarId_1659_, v_majorType_1662_, v_sz_1676_, v___x_1677_, v___x_1675_, v_a_1663_, v_a_1664_, v_a_1665_, v_a_1666_);
lean_dec_ref(v_recursorInfo_1661_);
lean_dec_ref(v_majorTypeArgs_1674_);
return v___x_1678_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMajorTypeIndices___boxed(lean_object* v_mvarId_1679_, lean_object* v_tacticName_1680_, lean_object* v_recursorInfo_1681_, lean_object* v_majorType_1682_, lean_object* v_a_1683_, lean_object* v_a_1684_, lean_object* v_a_1685_, lean_object* v_a_1686_, lean_object* v_a_1687_){
_start:
{
lean_object* v_res_1688_; 
v_res_1688_ = l_Lean_Meta_getMajorTypeIndices(v_mvarId_1679_, v_tacticName_1680_, v_recursorInfo_1681_, v_majorType_1682_, v_a_1683_, v_a_1684_, v_a_1685_, v_a_1686_);
lean_dec(v_a_1686_);
lean_dec_ref(v_a_1685_);
lean_dec(v_a_1684_);
lean_dec_ref(v_a_1683_);
return v_res_1688_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3(lean_object* v_majorTypeArgs_1689_, lean_object* v_idxPos_1690_, lean_object* v_recursorInfo_1691_, lean_object* v_idx_1692_, lean_object* v_tacticName_1693_, lean_object* v_mvarId_1694_, lean_object* v_majorType_1695_, lean_object* v_n_1696_, lean_object* v_i_1697_, lean_object* v_a_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_){
_start:
{
lean_object* v___x_1704_; 
v___x_1704_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg(v_majorTypeArgs_1689_, v_idxPos_1690_, v_recursorInfo_1691_, v_idx_1692_, v_tacticName_1693_, v_mvarId_1694_, v_majorType_1695_, v_n_1696_, v_i_1697_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_);
return v___x_1704_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___boxed(lean_object* v_majorTypeArgs_1705_, lean_object* v_idxPos_1706_, lean_object* v_recursorInfo_1707_, lean_object* v_idx_1708_, lean_object* v_tacticName_1709_, lean_object* v_mvarId_1710_, lean_object* v_majorType_1711_, lean_object* v_n_1712_, lean_object* v_i_1713_, lean_object* v_a_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_){
_start:
{
lean_object* v_res_1720_; 
v_res_1720_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3(v_majorTypeArgs_1705_, v_idxPos_1706_, v_recursorInfo_1707_, v_idx_1708_, v_tacticName_1709_, v_mvarId_1710_, v_majorType_1711_, v_n_1712_, v_i_1713_, v_a_1714_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_);
lean_dec(v___y_1718_);
lean_dec_ref(v___y_1717_);
lean_dec(v___y_1716_);
lean_dec_ref(v___y_1715_);
lean_dec(v_n_1712_);
lean_dec_ref(v_recursorInfo_1707_);
lean_dec(v_idxPos_1706_);
lean_dec_ref(v_majorTypeArgs_1705_);
return v_res_1720_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1___redArg(lean_object* v_name_1721_, lean_object* v_msg_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_){
_start:
{
lean_object* v_ref_1728_; lean_object* v_msg_1729_; lean_object* v___x_1730_; lean_object* v_a_1731_; lean_object* v___x_1733_; uint8_t v_isShared_1734_; uint8_t v_isSharedCheck_1739_; 
v_ref_1728_ = lean_ctor_get(v___y_1725_, 2);
v_msg_1729_ = l_Lean_MessageData_tagWithErrorName(v_msg_1722_, v_name_1721_);
v___x_1730_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1_spec__2(v_msg_1729_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_);
v_a_1731_ = lean_ctor_get(v___x_1730_, 0);
v_isSharedCheck_1739_ = !lean_is_exclusive(v___x_1730_);
if (v_isSharedCheck_1739_ == 0)
{
v___x_1733_ = v___x_1730_;
v_isShared_1734_ = v_isSharedCheck_1739_;
goto v_resetjp_1732_;
}
else
{
lean_inc(v_a_1731_);
lean_dec(v___x_1730_);
v___x_1733_ = lean_box(0);
v_isShared_1734_ = v_isSharedCheck_1739_;
goto v_resetjp_1732_;
}
v_resetjp_1732_:
{
lean_object* v___x_1735_; lean_object* v___x_1737_; 
lean_inc(v_ref_1728_);
v___x_1735_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1735_, 0, v_ref_1728_);
lean_ctor_set(v___x_1735_, 1, v_a_1731_);
if (v_isShared_1734_ == 0)
{
lean_ctor_set_tag(v___x_1733_, 1);
lean_ctor_set(v___x_1733_, 0, v___x_1735_);
v___x_1737_ = v___x_1733_;
goto v_reusejp_1736_;
}
else
{
lean_object* v_reuseFailAlloc_1738_; 
v_reuseFailAlloc_1738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1738_, 0, v___x_1735_);
v___x_1737_ = v_reuseFailAlloc_1738_;
goto v_reusejp_1736_;
}
v_reusejp_1736_:
{
return v___x_1737_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1___redArg___boxed(lean_object* v_name_1740_, lean_object* v_msg_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_){
_start:
{
lean_object* v_res_1747_; 
v_res_1747_ = l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1___redArg(v_name_1740_, v_msg_1741_, v___y_1742_, v___y_1743_, v___y_1744_, v___y_1745_);
lean_dec(v___y_1745_);
lean_dec_ref(v___y_1744_);
lean_dec(v___y_1743_);
lean_dec_ref(v___y_1742_);
return v_res_1747_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Meta_mkRecursorAppPrefix_spec__0(lean_object* v_a_1748_, lean_object* v___x_1749_, lean_object* v_tacticName_1750_, lean_object* v_mvarId_1751_, lean_object* v_x_1752_, lean_object* v_x_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_){
_start:
{
if (lean_obj_tag(v_x_1753_) == 0)
{
lean_object* v___x_1759_; 
lean_dec(v_mvarId_1751_);
lean_dec(v_tacticName_1750_);
lean_dec(v_a_1748_);
v___x_1759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1759_, 0, v_x_1752_);
return v___x_1759_;
}
else
{
lean_object* v_head_1760_; 
v_head_1760_ = lean_ctor_get(v_x_1753_, 0);
if (lean_obj_tag(v_head_1760_) == 0)
{
lean_object* v_tail_1761_; lean_object* v_fst_1762_; lean_object* v___x_1764_; uint8_t v_isShared_1765_; uint8_t v_isSharedCheck_1773_; 
v_tail_1761_ = lean_ctor_get(v_x_1753_, 1);
v_fst_1762_ = lean_ctor_get(v_x_1752_, 0);
v_isSharedCheck_1773_ = !lean_is_exclusive(v_x_1752_);
if (v_isSharedCheck_1773_ == 0)
{
lean_object* v_unused_1774_; 
v_unused_1774_ = lean_ctor_get(v_x_1752_, 1);
lean_dec(v_unused_1774_);
v___x_1764_ = v_x_1752_;
v_isShared_1765_ = v_isSharedCheck_1773_;
goto v_resetjp_1763_;
}
else
{
lean_inc(v_fst_1762_);
lean_dec(v_x_1752_);
v___x_1764_ = lean_box(0);
v_isShared_1765_ = v_isSharedCheck_1773_;
goto v_resetjp_1763_;
}
v_resetjp_1763_:
{
lean_object* v___x_1766_; uint8_t v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1770_; 
lean_inc(v_a_1748_);
v___x_1766_ = lean_array_push(v_fst_1762_, v_a_1748_);
v___x_1767_ = 1;
v___x_1768_ = lean_box(v___x_1767_);
if (v_isShared_1765_ == 0)
{
lean_ctor_set(v___x_1764_, 1, v___x_1768_);
lean_ctor_set(v___x_1764_, 0, v___x_1766_);
v___x_1770_ = v___x_1764_;
goto v_reusejp_1769_;
}
else
{
lean_object* v_reuseFailAlloc_1772_; 
v_reuseFailAlloc_1772_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1772_, 0, v___x_1766_);
lean_ctor_set(v_reuseFailAlloc_1772_, 1, v___x_1768_);
v___x_1770_ = v_reuseFailAlloc_1772_;
goto v_reusejp_1769_;
}
v_reusejp_1769_:
{
v_x_1752_ = v___x_1770_;
v_x_1753_ = v_tail_1761_;
goto _start;
}
}
}
else
{
lean_object* v_tail_1775_; lean_object* v_fst_1776_; lean_object* v_snd_1777_; lean_object* v___x_1779_; uint8_t v_isShared_1780_; uint8_t v_isSharedCheck_1794_; 
v_tail_1775_ = lean_ctor_get(v_x_1753_, 1);
v_fst_1776_ = lean_ctor_get(v_x_1752_, 0);
v_snd_1777_ = lean_ctor_get(v_x_1752_, 1);
v_isSharedCheck_1794_ = !lean_is_exclusive(v_x_1752_);
if (v_isSharedCheck_1794_ == 0)
{
v___x_1779_ = v_x_1752_;
v_isShared_1780_ = v_isSharedCheck_1794_;
goto v_resetjp_1778_;
}
else
{
lean_inc(v_snd_1777_);
lean_inc(v_fst_1776_);
lean_dec(v_x_1752_);
v___x_1779_ = lean_box(0);
v_isShared_1780_ = v_isSharedCheck_1794_;
goto v_resetjp_1778_;
}
v_resetjp_1778_:
{
lean_object* v_idx_1781_; lean_object* v___x_1782_; uint8_t v___x_1783_; 
v_idx_1781_ = lean_ctor_get(v_head_1760_, 0);
v___x_1782_ = lean_array_get_size(v___x_1749_);
v___x_1783_ = lean_nat_dec_le(v___x_1782_, v_idx_1781_);
if (v___x_1783_ == 0)
{
lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1787_; 
v___x_1784_ = lean_array_fget_borrowed(v___x_1749_, v_idx_1781_);
lean_inc(v___x_1784_);
v___x_1785_ = lean_array_push(v_fst_1776_, v___x_1784_);
if (v_isShared_1780_ == 0)
{
lean_ctor_set(v___x_1779_, 0, v___x_1785_);
v___x_1787_ = v___x_1779_;
goto v_reusejp_1786_;
}
else
{
lean_object* v_reuseFailAlloc_1789_; 
v_reuseFailAlloc_1789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1789_, 0, v___x_1785_);
lean_ctor_set(v_reuseFailAlloc_1789_, 1, v_snd_1777_);
v___x_1787_ = v_reuseFailAlloc_1789_;
goto v_reusejp_1786_;
}
v_reusejp_1786_:
{
v_x_1752_ = v___x_1787_;
v_x_1753_ = v_tail_1775_;
goto _start;
}
}
else
{
lean_object* v___x_1790_; lean_object* v___x_1791_; 
lean_del_object(v___x_1779_);
lean_dec(v_snd_1777_);
lean_dec(v_fst_1776_);
v___x_1790_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9);
lean_inc(v_mvarId_1751_);
lean_inc(v_tacticName_1750_);
v___x_1791_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1750_, v_mvarId_1751_, v___x_1790_, v___y_1754_, v___y_1755_, v___y_1756_, v___y_1757_);
if (lean_obj_tag(v___x_1791_) == 0)
{
lean_object* v_a_1792_; 
v_a_1792_ = lean_ctor_get(v___x_1791_, 0);
lean_inc(v_a_1792_);
lean_dec_ref_known(v___x_1791_, 1);
v_x_1752_ = v_a_1792_;
v_x_1753_ = v_tail_1775_;
goto _start;
}
else
{
lean_dec(v_mvarId_1751_);
lean_dec(v_tacticName_1750_);
lean_dec(v_a_1748_);
return v___x_1791_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Meta_mkRecursorAppPrefix_spec__0___boxed(lean_object* v_a_1795_, lean_object* v___x_1796_, lean_object* v_tacticName_1797_, lean_object* v_mvarId_1798_, lean_object* v_x_1799_, lean_object* v_x_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_){
_start:
{
lean_object* v_res_1806_; 
v_res_1806_ = l_List_foldlM___at___00Lean_Meta_mkRecursorAppPrefix_spec__0(v_a_1795_, v___x_1796_, v_tacticName_1797_, v_mvarId_1798_, v_x_1799_, v_x_1800_, v___y_1801_, v___y_1802_, v___y_1803_, v___y_1804_);
lean_dec(v___y_1804_);
lean_dec_ref(v___y_1803_);
lean_dec(v___y_1802_);
lean_dec_ref(v___y_1801_);
lean_dec(v_x_1800_);
lean_dec_ref(v___x_1796_);
return v_res_1806_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__8(void){
_start:
{
lean_object* v___x_1822_; lean_object* v___x_1823_; 
v___x_1822_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__7));
v___x_1823_ = l_Lean_stringToMessageData(v___x_1822_);
return v___x_1823_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__10(void){
_start:
{
lean_object* v___x_1825_; lean_object* v___x_1826_; 
v___x_1825_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__9));
v___x_1826_ = l_Lean_stringToMessageData(v___x_1825_);
return v___x_1826_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__13(void){
_start:
{
lean_object* v___x_1830_; lean_object* v___x_1831_; 
v___x_1830_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__12));
v___x_1831_ = l_Lean_MessageData_ofFormat(v___x_1830_);
return v___x_1831_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__14(void){
_start:
{
lean_object* v___x_1832_; lean_object* v___x_1833_; 
v___x_1832_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__13, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__13_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__13);
v___x_1833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1833_, 0, v___x_1832_);
return v___x_1833_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2(lean_object* v_recursorInfo_1834_, lean_object* v_a_1835_, lean_object* v_tacticName_1836_, lean_object* v_mvarId_1837_, lean_object* v_indices_1838_, lean_object* v_a_1839_, lean_object* v_major_1840_, lean_object* v_x_1841_, lean_object* v_x_1842_, lean_object* v_x_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_){
_start:
{
if (lean_obj_tag(v_x_1841_) == 5)
{
lean_object* v_fn_1849_; lean_object* v_arg_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; 
v_fn_1849_ = lean_ctor_get(v_x_1841_, 0);
lean_inc_ref(v_fn_1849_);
v_arg_1850_ = lean_ctor_get(v_x_1841_, 1);
lean_inc_ref(v_arg_1850_);
lean_dec_ref_known(v_x_1841_, 2);
v___x_1851_ = lean_array_set(v_x_1842_, v_x_1843_, v_arg_1850_);
v___x_1852_ = lean_unsigned_to_nat(1u);
v___x_1853_ = lean_nat_sub(v_x_1843_, v___x_1852_);
lean_dec(v_x_1843_);
v_x_1841_ = v_fn_1849_;
v_x_1842_ = v___x_1851_;
v_x_1843_ = v___x_1853_;
goto _start;
}
else
{
lean_dec(v_x_1843_);
if (lean_obj_tag(v_x_1841_) == 4)
{
lean_object* v_us_1855_; lean_object* v_recursorName_1856_; lean_object* v_univLevelPos_1857_; uint8_t v_depElim_1858_; lean_object* v_paramsPos_1859_; lean_object* v___x_1860_; uint8_t v___x_1861_; lean_object* v___y_1863_; lean_object* v_motive_1864_; lean_object* v___y_1865_; lean_object* v___y_1866_; lean_object* v___y_1867_; lean_object* v___y_1868_; lean_object* v___x_1881_; lean_object* v___x_1882_; 
v_us_1855_ = lean_ctor_get(v_x_1841_, 1);
lean_inc(v_us_1855_);
lean_dec_ref_known(v_x_1841_, 2);
v_recursorName_1856_ = lean_ctor_get(v_recursorInfo_1834_, 0);
lean_inc(v_recursorName_1856_);
v_univLevelPos_1857_ = lean_ctor_get(v_recursorInfo_1834_, 2);
lean_inc(v_univLevelPos_1857_);
v_depElim_1858_ = lean_ctor_get_uint8(v_recursorInfo_1834_, sizeof(void*)*8);
v_paramsPos_1859_ = lean_ctor_get(v_recursorInfo_1834_, 5);
lean_inc(v_paramsPos_1859_);
lean_dec_ref(v_recursorInfo_1834_);
v___x_1860_ = lean_array_mk(v_us_1855_);
v___x_1861_ = 0;
v___x_1881_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__1));
lean_inc(v_mvarId_1837_);
lean_inc(v_tacticName_1836_);
lean_inc(v_a_1835_);
v___x_1882_ = l_List_foldlM___at___00Lean_Meta_mkRecursorAppPrefix_spec__0(v_a_1835_, v___x_1860_, v_tacticName_1836_, v_mvarId_1837_, v___x_1881_, v_univLevelPos_1857_, v___y_1844_, v___y_1845_, v___y_1846_, v___y_1847_);
lean_dec(v_univLevelPos_1857_);
lean_dec_ref(v___x_1860_);
if (lean_obj_tag(v___x_1882_) == 0)
{
lean_object* v_a_1883_; lean_object* v_fst_1884_; lean_object* v_snd_1885_; lean_object* v___x_1887_; uint8_t v_isShared_1888_; uint8_t v_isSharedCheck_1929_; 
v_a_1883_ = lean_ctor_get(v___x_1882_, 0);
lean_inc(v_a_1883_);
lean_dec_ref_known(v___x_1882_, 1);
v_fst_1884_ = lean_ctor_get(v_a_1883_, 0);
v_snd_1885_ = lean_ctor_get(v_a_1883_, 1);
v_isSharedCheck_1929_ = !lean_is_exclusive(v_a_1883_);
if (v_isSharedCheck_1929_ == 0)
{
v___x_1887_ = v_a_1883_;
v_isShared_1888_ = v_isSharedCheck_1929_;
goto v_resetjp_1886_;
}
else
{
lean_inc(v_snd_1885_);
lean_inc(v_fst_1884_);
lean_dec(v_a_1883_);
v___x_1887_ = lean_box(0);
v_isShared_1888_ = v_isSharedCheck_1929_;
goto v_resetjp_1886_;
}
v_resetjp_1886_:
{
lean_object* v___y_1890_; lean_object* v___y_1891_; lean_object* v___y_1892_; lean_object* v___y_1893_; uint8_t v___x_1909_; 
v___x_1909_ = lean_unbox(v_snd_1885_);
lean_dec(v_snd_1885_);
if (v___x_1909_ == 0)
{
uint8_t v___x_1910_; 
v___x_1910_ = l_Lean_Level_isZero(v_a_1835_);
lean_dec(v_a_1835_);
if (v___x_1910_ == 0)
{
lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1915_; 
lean_dec(v_fst_1884_);
lean_dec(v_paramsPos_1859_);
lean_dec_ref(v_x_1842_);
lean_dec_ref(v_major_1840_);
lean_dec_ref(v_a_1839_);
v___x_1911_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__6));
v___x_1912_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__8, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__8_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__8);
v___x_1913_ = l_Lean_MessageData_ofName(v_recursorName_1856_);
if (v_isShared_1888_ == 0)
{
lean_ctor_set_tag(v___x_1887_, 7);
lean_ctor_set(v___x_1887_, 1, v___x_1913_);
lean_ctor_set(v___x_1887_, 0, v___x_1912_);
v___x_1915_ = v___x_1887_;
goto v_reusejp_1914_;
}
else
{
lean_object* v_reuseFailAlloc_1928_; 
v_reuseFailAlloc_1928_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1928_, 0, v___x_1912_);
lean_ctor_set(v_reuseFailAlloc_1928_, 1, v___x_1913_);
v___x_1915_ = v_reuseFailAlloc_1928_;
goto v_reusejp_1914_;
}
v_reusejp_1914_:
{
lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v_a_1920_; lean_object* v___x_1922_; uint8_t v_isShared_1923_; uint8_t v_isSharedCheck_1927_; 
v___x_1916_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__10, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__10_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__10);
v___x_1917_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1917_, 0, v___x_1915_);
lean_ctor_set(v___x_1917_, 1, v___x_1916_);
v___x_1918_ = l_Lean_Meta_mkTacticExMsg(v_tacticName_1836_, v_mvarId_1837_, v___x_1917_);
v___x_1919_ = l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1___redArg(v___x_1911_, v___x_1918_, v___y_1844_, v___y_1845_, v___y_1846_, v___y_1847_);
v_a_1920_ = lean_ctor_get(v___x_1919_, 0);
v_isSharedCheck_1927_ = !lean_is_exclusive(v___x_1919_);
if (v_isSharedCheck_1927_ == 0)
{
v___x_1922_ = v___x_1919_;
v_isShared_1923_ = v_isSharedCheck_1927_;
goto v_resetjp_1921_;
}
else
{
lean_inc(v_a_1920_);
lean_dec(v___x_1919_);
v___x_1922_ = lean_box(0);
v_isShared_1923_ = v_isSharedCheck_1927_;
goto v_resetjp_1921_;
}
v_resetjp_1921_:
{
lean_object* v___x_1925_; 
if (v_isShared_1923_ == 0)
{
v___x_1925_ = v___x_1922_;
goto v_reusejp_1924_;
}
else
{
lean_object* v_reuseFailAlloc_1926_; 
v_reuseFailAlloc_1926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1926_, 0, v_a_1920_);
v___x_1925_ = v_reuseFailAlloc_1926_;
goto v_reusejp_1924_;
}
v_reusejp_1924_:
{
return v___x_1925_;
}
}
}
}
else
{
lean_del_object(v___x_1887_);
lean_dec(v_tacticName_1836_);
v___y_1890_ = v___y_1844_;
v___y_1891_ = v___y_1845_;
v___y_1892_ = v___y_1846_;
v___y_1893_ = v___y_1847_;
goto v___jp_1889_;
}
}
else
{
lean_del_object(v___x_1887_);
lean_dec(v_tacticName_1836_);
lean_dec(v_a_1835_);
v___y_1890_ = v___y_1844_;
v___y_1891_ = v___y_1845_;
v___y_1892_ = v___y_1846_;
v___y_1893_ = v___y_1847_;
goto v___jp_1889_;
}
v___jp_1889_:
{
lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; 
v___x_1894_ = lean_array_to_list(v_fst_1884_);
v___x_1895_ = l_Lean_mkConst(v_recursorName_1856_, v___x_1894_);
v___x_1896_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams(v_mvarId_1837_, v_x_1842_, v_paramsPos_1859_, v___x_1895_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_);
lean_dec_ref(v_x_1842_);
if (lean_obj_tag(v___x_1896_) == 0)
{
if (v_depElim_1858_ == 0)
{
lean_object* v_a_1897_; 
lean_dec_ref(v_major_1840_);
v_a_1897_ = lean_ctor_get(v___x_1896_, 0);
lean_inc(v_a_1897_);
lean_dec_ref_known(v___x_1896_, 1);
v___y_1863_ = v_a_1897_;
v_motive_1864_ = v_a_1839_;
v___y_1865_ = v___y_1890_;
v___y_1866_ = v___y_1891_;
v___y_1867_ = v___y_1892_;
v___y_1868_ = v___y_1893_;
goto v___jp_1862_;
}
else
{
lean_object* v_a_1898_; lean_object* v___x_1899_; 
v_a_1898_ = lean_ctor_get(v___x_1896_, 0);
lean_inc(v_a_1898_);
lean_dec_ref_known(v___x_1896_, 1);
lean_inc(v___y_1893_);
lean_inc_ref(v___y_1892_);
lean_inc(v___y_1891_);
lean_inc_ref(v___y_1890_);
lean_inc_ref(v_major_1840_);
v___x_1899_ = lean_infer_type(v_major_1840_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_);
if (lean_obj_tag(v___x_1899_) == 0)
{
lean_object* v_a_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; 
v_a_1900_ = lean_ctor_get(v___x_1899_, 0);
lean_inc(v_a_1900_);
lean_dec_ref_known(v___x_1899_, 1);
v___x_1901_ = lean_unsigned_to_nat(1u);
v___x_1902_ = lean_mk_empty_array_with_capacity(v___x_1901_);
v___x_1903_ = lean_array_push(v___x_1902_, v_major_1840_);
v___x_1904_ = l_Lean_Expr_abstractM(v_a_1839_, v___x_1903_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_);
lean_dec_ref(v___x_1903_);
if (lean_obj_tag(v___x_1904_) == 0)
{
lean_object* v_a_1905_; lean_object* v___x_1906_; uint8_t v___x_1907_; lean_object* v___x_1908_; 
v_a_1905_ = lean_ctor_get(v___x_1904_, 0);
lean_inc(v_a_1905_);
lean_dec_ref_known(v___x_1904_, 1);
v___x_1906_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__3));
v___x_1907_ = 0;
v___x_1908_ = l_Lean_mkLambda(v___x_1906_, v___x_1907_, v_a_1900_, v_a_1905_);
v___y_1863_ = v_a_1898_;
v_motive_1864_ = v___x_1908_;
v___y_1865_ = v___y_1890_;
v___y_1866_ = v___y_1891_;
v___y_1867_ = v___y_1892_;
v___y_1868_ = v___y_1893_;
goto v___jp_1862_;
}
else
{
lean_dec(v_a_1900_);
lean_dec(v_a_1898_);
return v___x_1904_;
}
}
else
{
lean_dec(v_a_1898_);
lean_dec_ref(v_major_1840_);
lean_dec_ref(v_a_1839_);
return v___x_1899_;
}
}
}
else
{
lean_dec_ref(v_major_1840_);
lean_dec_ref(v_a_1839_);
return v___x_1896_;
}
}
}
}
else
{
lean_object* v_a_1930_; lean_object* v___x_1932_; uint8_t v_isShared_1933_; uint8_t v_isSharedCheck_1937_; 
lean_dec(v_paramsPos_1859_);
lean_dec(v_recursorName_1856_);
lean_dec_ref(v_x_1842_);
lean_dec_ref(v_major_1840_);
lean_dec_ref(v_a_1839_);
lean_dec(v_mvarId_1837_);
lean_dec(v_tacticName_1836_);
lean_dec(v_a_1835_);
v_a_1930_ = lean_ctor_get(v___x_1882_, 0);
v_isSharedCheck_1937_ = !lean_is_exclusive(v___x_1882_);
if (v_isSharedCheck_1937_ == 0)
{
v___x_1932_ = v___x_1882_;
v_isShared_1933_ = v_isSharedCheck_1937_;
goto v_resetjp_1931_;
}
else
{
lean_inc(v_a_1930_);
lean_dec(v___x_1882_);
v___x_1932_ = lean_box(0);
v_isShared_1933_ = v_isSharedCheck_1937_;
goto v_resetjp_1931_;
}
v_resetjp_1931_:
{
lean_object* v___x_1935_; 
if (v_isShared_1933_ == 0)
{
v___x_1935_ = v___x_1932_;
goto v_reusejp_1934_;
}
else
{
lean_object* v_reuseFailAlloc_1936_; 
v_reuseFailAlloc_1936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1936_, 0, v_a_1930_);
v___x_1935_ = v_reuseFailAlloc_1936_;
goto v_reusejp_1934_;
}
v_reusejp_1934_:
{
return v___x_1935_;
}
}
}
v___jp_1862_:
{
uint8_t v___x_1869_; uint8_t v___x_1870_; lean_object* v___x_1871_; 
v___x_1869_ = 1;
v___x_1870_ = 1;
v___x_1871_ = l_Lean_Meta_mkLambdaFVars(v_indices_1838_, v_motive_1864_, v___x_1861_, v___x_1869_, v___x_1861_, v___x_1869_, v___x_1870_, v___y_1865_, v___y_1866_, v___y_1867_, v___y_1868_);
if (lean_obj_tag(v___x_1871_) == 0)
{
lean_object* v_a_1872_; lean_object* v___x_1874_; uint8_t v_isShared_1875_; uint8_t v_isSharedCheck_1880_; 
v_a_1872_ = lean_ctor_get(v___x_1871_, 0);
v_isSharedCheck_1880_ = !lean_is_exclusive(v___x_1871_);
if (v_isSharedCheck_1880_ == 0)
{
v___x_1874_ = v___x_1871_;
v_isShared_1875_ = v_isSharedCheck_1880_;
goto v_resetjp_1873_;
}
else
{
lean_inc(v_a_1872_);
lean_dec(v___x_1871_);
v___x_1874_ = lean_box(0);
v_isShared_1875_ = v_isSharedCheck_1880_;
goto v_resetjp_1873_;
}
v_resetjp_1873_:
{
lean_object* v___x_1876_; lean_object* v___x_1878_; 
v___x_1876_ = l_Lean_Expr_app___override(v___y_1863_, v_a_1872_);
if (v_isShared_1875_ == 0)
{
lean_ctor_set(v___x_1874_, 0, v___x_1876_);
v___x_1878_ = v___x_1874_;
goto v_reusejp_1877_;
}
else
{
lean_object* v_reuseFailAlloc_1879_; 
v_reuseFailAlloc_1879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1879_, 0, v___x_1876_);
v___x_1878_ = v_reuseFailAlloc_1879_;
goto v_reusejp_1877_;
}
v_reusejp_1877_:
{
return v___x_1878_;
}
}
}
else
{
lean_dec_ref(v___y_1863_);
return v___x_1871_;
}
}
}
else
{
lean_object* v___x_1938_; lean_object* v___x_1939_; 
lean_dec_ref(v_x_1842_);
lean_dec_ref(v_x_1841_);
lean_dec_ref(v_major_1840_);
lean_dec_ref(v_a_1839_);
lean_dec(v_a_1835_);
lean_dec_ref(v_recursorInfo_1834_);
v___x_1938_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__14, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__14_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__14);
v___x_1939_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1836_, v_mvarId_1837_, v___x_1938_, v___y_1844_, v___y_1845_, v___y_1846_, v___y_1847_);
return v___x_1939_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___boxed(lean_object* v_recursorInfo_1940_, lean_object* v_a_1941_, lean_object* v_tacticName_1942_, lean_object* v_mvarId_1943_, lean_object* v_indices_1944_, lean_object* v_a_1945_, lean_object* v_major_1946_, lean_object* v_x_1947_, lean_object* v_x_1948_, lean_object* v_x_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_){
_start:
{
lean_object* v_res_1955_; 
v_res_1955_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2(v_recursorInfo_1940_, v_a_1941_, v_tacticName_1942_, v_mvarId_1943_, v_indices_1944_, v_a_1945_, v_major_1946_, v_x_1947_, v_x_1948_, v_x_1949_, v___y_1950_, v___y_1951_, v___y_1952_, v___y_1953_);
lean_dec(v___y_1953_);
lean_dec_ref(v___y_1952_);
lean_dec(v___y_1951_);
lean_dec_ref(v___y_1950_);
lean_dec_ref(v_indices_1944_);
return v_res_1955_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2(lean_object* v_a_1956_, lean_object* v_tacticName_1957_, lean_object* v_mvarId_1958_, lean_object* v_recursorInfo_1959_, lean_object* v_indices_1960_, lean_object* v_a_1961_, lean_object* v_major_1962_, lean_object* v_x_1963_, lean_object* v_x_1964_, lean_object* v_x_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_){
_start:
{
if (lean_obj_tag(v_x_1963_) == 5)
{
lean_object* v_fn_1971_; lean_object* v_arg_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; 
v_fn_1971_ = lean_ctor_get(v_x_1963_, 0);
lean_inc_ref(v_fn_1971_);
v_arg_1972_ = lean_ctor_get(v_x_1963_, 1);
lean_inc_ref(v_arg_1972_);
lean_dec_ref_known(v_x_1963_, 2);
v___x_1973_ = lean_array_set(v_x_1964_, v_x_1965_, v_arg_1972_);
v___x_1974_ = lean_unsigned_to_nat(1u);
v___x_1975_ = lean_nat_sub(v_x_1965_, v___x_1974_);
v___x_1976_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2(v_recursorInfo_1959_, v_a_1956_, v_tacticName_1957_, v_mvarId_1958_, v_indices_1960_, v_a_1961_, v_major_1962_, v_fn_1971_, v___x_1973_, v___x_1975_, v___y_1966_, v___y_1967_, v___y_1968_, v___y_1969_);
return v___x_1976_;
}
else
{
if (lean_obj_tag(v_x_1963_) == 4)
{
lean_object* v_us_1977_; lean_object* v_recursorName_1978_; lean_object* v_univLevelPos_1979_; uint8_t v_depElim_1980_; lean_object* v_paramsPos_1981_; lean_object* v___x_1982_; uint8_t v___x_1983_; lean_object* v___y_1985_; lean_object* v_motive_1986_; lean_object* v___y_1987_; lean_object* v___y_1988_; lean_object* v___y_1989_; lean_object* v___y_1990_; lean_object* v___x_2003_; lean_object* v___x_2004_; 
v_us_1977_ = lean_ctor_get(v_x_1963_, 1);
lean_inc(v_us_1977_);
lean_dec_ref_known(v_x_1963_, 2);
v_recursorName_1978_ = lean_ctor_get(v_recursorInfo_1959_, 0);
lean_inc(v_recursorName_1978_);
v_univLevelPos_1979_ = lean_ctor_get(v_recursorInfo_1959_, 2);
lean_inc(v_univLevelPos_1979_);
v_depElim_1980_ = lean_ctor_get_uint8(v_recursorInfo_1959_, sizeof(void*)*8);
v_paramsPos_1981_ = lean_ctor_get(v_recursorInfo_1959_, 5);
lean_inc(v_paramsPos_1981_);
lean_dec_ref(v_recursorInfo_1959_);
v___x_1982_ = lean_array_mk(v_us_1977_);
v___x_1983_ = 0;
v___x_2003_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__1));
lean_inc(v_mvarId_1958_);
lean_inc(v_tacticName_1957_);
lean_inc(v_a_1956_);
v___x_2004_ = l_List_foldlM___at___00Lean_Meta_mkRecursorAppPrefix_spec__0(v_a_1956_, v___x_1982_, v_tacticName_1957_, v_mvarId_1958_, v___x_2003_, v_univLevelPos_1979_, v___y_1966_, v___y_1967_, v___y_1968_, v___y_1969_);
lean_dec(v_univLevelPos_1979_);
lean_dec_ref(v___x_1982_);
if (lean_obj_tag(v___x_2004_) == 0)
{
lean_object* v_a_2005_; lean_object* v_fst_2006_; lean_object* v_snd_2007_; lean_object* v___x_2009_; uint8_t v_isShared_2010_; uint8_t v_isSharedCheck_2051_; 
v_a_2005_ = lean_ctor_get(v___x_2004_, 0);
lean_inc(v_a_2005_);
lean_dec_ref_known(v___x_2004_, 1);
v_fst_2006_ = lean_ctor_get(v_a_2005_, 0);
v_snd_2007_ = lean_ctor_get(v_a_2005_, 1);
v_isSharedCheck_2051_ = !lean_is_exclusive(v_a_2005_);
if (v_isSharedCheck_2051_ == 0)
{
v___x_2009_ = v_a_2005_;
v_isShared_2010_ = v_isSharedCheck_2051_;
goto v_resetjp_2008_;
}
else
{
lean_inc(v_snd_2007_);
lean_inc(v_fst_2006_);
lean_dec(v_a_2005_);
v___x_2009_ = lean_box(0);
v_isShared_2010_ = v_isSharedCheck_2051_;
goto v_resetjp_2008_;
}
v_resetjp_2008_:
{
lean_object* v___y_2012_; lean_object* v___y_2013_; lean_object* v___y_2014_; lean_object* v___y_2015_; uint8_t v___x_2031_; 
v___x_2031_ = lean_unbox(v_snd_2007_);
lean_dec(v_snd_2007_);
if (v___x_2031_ == 0)
{
uint8_t v___x_2032_; 
v___x_2032_ = l_Lean_Level_isZero(v_a_1956_);
lean_dec(v_a_1956_);
if (v___x_2032_ == 0)
{
lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2037_; 
lean_dec(v_fst_2006_);
lean_dec(v_paramsPos_1981_);
lean_dec_ref(v_x_1964_);
lean_dec_ref(v_major_1962_);
lean_dec_ref(v_a_1961_);
v___x_2033_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__6));
v___x_2034_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__8, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__8_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__8);
v___x_2035_ = l_Lean_MessageData_ofName(v_recursorName_1978_);
if (v_isShared_2010_ == 0)
{
lean_ctor_set_tag(v___x_2009_, 7);
lean_ctor_set(v___x_2009_, 1, v___x_2035_);
lean_ctor_set(v___x_2009_, 0, v___x_2034_);
v___x_2037_ = v___x_2009_;
goto v_reusejp_2036_;
}
else
{
lean_object* v_reuseFailAlloc_2050_; 
v_reuseFailAlloc_2050_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2050_, 0, v___x_2034_);
lean_ctor_set(v_reuseFailAlloc_2050_, 1, v___x_2035_);
v___x_2037_ = v_reuseFailAlloc_2050_;
goto v_reusejp_2036_;
}
v_reusejp_2036_:
{
lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v_a_2042_; lean_object* v___x_2044_; uint8_t v_isShared_2045_; uint8_t v_isSharedCheck_2049_; 
v___x_2038_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__10, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__10_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__10);
v___x_2039_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2039_, 0, v___x_2037_);
lean_ctor_set(v___x_2039_, 1, v___x_2038_);
v___x_2040_ = l_Lean_Meta_mkTacticExMsg(v_tacticName_1957_, v_mvarId_1958_, v___x_2039_);
v___x_2041_ = l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1___redArg(v___x_2033_, v___x_2040_, v___y_1966_, v___y_1967_, v___y_1968_, v___y_1969_);
v_a_2042_ = lean_ctor_get(v___x_2041_, 0);
v_isSharedCheck_2049_ = !lean_is_exclusive(v___x_2041_);
if (v_isSharedCheck_2049_ == 0)
{
v___x_2044_ = v___x_2041_;
v_isShared_2045_ = v_isSharedCheck_2049_;
goto v_resetjp_2043_;
}
else
{
lean_inc(v_a_2042_);
lean_dec(v___x_2041_);
v___x_2044_ = lean_box(0);
v_isShared_2045_ = v_isSharedCheck_2049_;
goto v_resetjp_2043_;
}
v_resetjp_2043_:
{
lean_object* v___x_2047_; 
if (v_isShared_2045_ == 0)
{
v___x_2047_ = v___x_2044_;
goto v_reusejp_2046_;
}
else
{
lean_object* v_reuseFailAlloc_2048_; 
v_reuseFailAlloc_2048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2048_, 0, v_a_2042_);
v___x_2047_ = v_reuseFailAlloc_2048_;
goto v_reusejp_2046_;
}
v_reusejp_2046_:
{
return v___x_2047_;
}
}
}
}
else
{
lean_del_object(v___x_2009_);
lean_dec(v_tacticName_1957_);
v___y_2012_ = v___y_1966_;
v___y_2013_ = v___y_1967_;
v___y_2014_ = v___y_1968_;
v___y_2015_ = v___y_1969_;
goto v___jp_2011_;
}
}
else
{
lean_del_object(v___x_2009_);
lean_dec(v_tacticName_1957_);
lean_dec(v_a_1956_);
v___y_2012_ = v___y_1966_;
v___y_2013_ = v___y_1967_;
v___y_2014_ = v___y_1968_;
v___y_2015_ = v___y_1969_;
goto v___jp_2011_;
}
v___jp_2011_:
{
lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; 
v___x_2016_ = lean_array_to_list(v_fst_2006_);
v___x_2017_ = l_Lean_mkConst(v_recursorName_1978_, v___x_2016_);
v___x_2018_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams(v_mvarId_1958_, v_x_1964_, v_paramsPos_1981_, v___x_2017_, v___y_2012_, v___y_2013_, v___y_2014_, v___y_2015_);
lean_dec_ref(v_x_1964_);
if (lean_obj_tag(v___x_2018_) == 0)
{
if (v_depElim_1980_ == 0)
{
lean_object* v_a_2019_; 
lean_dec_ref(v_major_1962_);
v_a_2019_ = lean_ctor_get(v___x_2018_, 0);
lean_inc(v_a_2019_);
lean_dec_ref_known(v___x_2018_, 1);
v___y_1985_ = v_a_2019_;
v_motive_1986_ = v_a_1961_;
v___y_1987_ = v___y_2012_;
v___y_1988_ = v___y_2013_;
v___y_1989_ = v___y_2014_;
v___y_1990_ = v___y_2015_;
goto v___jp_1984_;
}
else
{
lean_object* v_a_2020_; lean_object* v___x_2021_; 
v_a_2020_ = lean_ctor_get(v___x_2018_, 0);
lean_inc(v_a_2020_);
lean_dec_ref_known(v___x_2018_, 1);
lean_inc(v___y_2015_);
lean_inc_ref(v___y_2014_);
lean_inc(v___y_2013_);
lean_inc_ref(v___y_2012_);
lean_inc_ref(v_major_1962_);
v___x_2021_ = lean_infer_type(v_major_1962_, v___y_2012_, v___y_2013_, v___y_2014_, v___y_2015_);
if (lean_obj_tag(v___x_2021_) == 0)
{
lean_object* v_a_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; 
v_a_2022_ = lean_ctor_get(v___x_2021_, 0);
lean_inc(v_a_2022_);
lean_dec_ref_known(v___x_2021_, 1);
v___x_2023_ = lean_unsigned_to_nat(1u);
v___x_2024_ = lean_mk_empty_array_with_capacity(v___x_2023_);
v___x_2025_ = lean_array_push(v___x_2024_, v_major_1962_);
v___x_2026_ = l_Lean_Expr_abstractM(v_a_1961_, v___x_2025_, v___y_2012_, v___y_2013_, v___y_2014_, v___y_2015_);
lean_dec_ref(v___x_2025_);
if (lean_obj_tag(v___x_2026_) == 0)
{
lean_object* v_a_2027_; lean_object* v___x_2028_; uint8_t v___x_2029_; lean_object* v___x_2030_; 
v_a_2027_ = lean_ctor_get(v___x_2026_, 0);
lean_inc(v_a_2027_);
lean_dec_ref_known(v___x_2026_, 1);
v___x_2028_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__3));
v___x_2029_ = 0;
v___x_2030_ = l_Lean_mkLambda(v___x_2028_, v___x_2029_, v_a_2022_, v_a_2027_);
v___y_1985_ = v_a_2020_;
v_motive_1986_ = v___x_2030_;
v___y_1987_ = v___y_2012_;
v___y_1988_ = v___y_2013_;
v___y_1989_ = v___y_2014_;
v___y_1990_ = v___y_2015_;
goto v___jp_1984_;
}
else
{
lean_dec(v_a_2022_);
lean_dec(v_a_2020_);
return v___x_2026_;
}
}
else
{
lean_dec(v_a_2020_);
lean_dec_ref(v_major_1962_);
lean_dec_ref(v_a_1961_);
return v___x_2021_;
}
}
}
else
{
lean_dec_ref(v_major_1962_);
lean_dec_ref(v_a_1961_);
return v___x_2018_;
}
}
}
}
else
{
lean_object* v_a_2052_; lean_object* v___x_2054_; uint8_t v_isShared_2055_; uint8_t v_isSharedCheck_2059_; 
lean_dec(v_paramsPos_1981_);
lean_dec(v_recursorName_1978_);
lean_dec_ref(v_x_1964_);
lean_dec_ref(v_major_1962_);
lean_dec_ref(v_a_1961_);
lean_dec(v_mvarId_1958_);
lean_dec(v_tacticName_1957_);
lean_dec(v_a_1956_);
v_a_2052_ = lean_ctor_get(v___x_2004_, 0);
v_isSharedCheck_2059_ = !lean_is_exclusive(v___x_2004_);
if (v_isSharedCheck_2059_ == 0)
{
v___x_2054_ = v___x_2004_;
v_isShared_2055_ = v_isSharedCheck_2059_;
goto v_resetjp_2053_;
}
else
{
lean_inc(v_a_2052_);
lean_dec(v___x_2004_);
v___x_2054_ = lean_box(0);
v_isShared_2055_ = v_isSharedCheck_2059_;
goto v_resetjp_2053_;
}
v_resetjp_2053_:
{
lean_object* v___x_2057_; 
if (v_isShared_2055_ == 0)
{
v___x_2057_ = v___x_2054_;
goto v_reusejp_2056_;
}
else
{
lean_object* v_reuseFailAlloc_2058_; 
v_reuseFailAlloc_2058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2058_, 0, v_a_2052_);
v___x_2057_ = v_reuseFailAlloc_2058_;
goto v_reusejp_2056_;
}
v_reusejp_2056_:
{
return v___x_2057_;
}
}
}
v___jp_1984_:
{
uint8_t v___x_1991_; uint8_t v___x_1992_; lean_object* v___x_1993_; 
v___x_1991_ = 1;
v___x_1992_ = 1;
v___x_1993_ = l_Lean_Meta_mkLambdaFVars(v_indices_1960_, v_motive_1986_, v___x_1983_, v___x_1991_, v___x_1983_, v___x_1991_, v___x_1992_, v___y_1987_, v___y_1988_, v___y_1989_, v___y_1990_);
if (lean_obj_tag(v___x_1993_) == 0)
{
lean_object* v_a_1994_; lean_object* v___x_1996_; uint8_t v_isShared_1997_; uint8_t v_isSharedCheck_2002_; 
v_a_1994_ = lean_ctor_get(v___x_1993_, 0);
v_isSharedCheck_2002_ = !lean_is_exclusive(v___x_1993_);
if (v_isSharedCheck_2002_ == 0)
{
v___x_1996_ = v___x_1993_;
v_isShared_1997_ = v_isSharedCheck_2002_;
goto v_resetjp_1995_;
}
else
{
lean_inc(v_a_1994_);
lean_dec(v___x_1993_);
v___x_1996_ = lean_box(0);
v_isShared_1997_ = v_isSharedCheck_2002_;
goto v_resetjp_1995_;
}
v_resetjp_1995_:
{
lean_object* v___x_1998_; lean_object* v___x_2000_; 
v___x_1998_ = l_Lean_Expr_app___override(v___y_1985_, v_a_1994_);
if (v_isShared_1997_ == 0)
{
lean_ctor_set(v___x_1996_, 0, v___x_1998_);
v___x_2000_ = v___x_1996_;
goto v_reusejp_1999_;
}
else
{
lean_object* v_reuseFailAlloc_2001_; 
v_reuseFailAlloc_2001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2001_, 0, v___x_1998_);
v___x_2000_ = v_reuseFailAlloc_2001_;
goto v_reusejp_1999_;
}
v_reusejp_1999_:
{
return v___x_2000_;
}
}
}
else
{
lean_dec_ref(v___y_1985_);
return v___x_1993_;
}
}
}
else
{
lean_object* v___x_2060_; lean_object* v___x_2061_; 
lean_dec_ref(v_x_1964_);
lean_dec_ref(v_x_1963_);
lean_dec_ref(v_major_1962_);
lean_dec_ref(v_a_1961_);
lean_dec_ref(v_recursorInfo_1959_);
lean_dec(v_a_1956_);
v___x_2060_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__14, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__14_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__14);
v___x_2061_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1957_, v_mvarId_1958_, v___x_2060_, v___y_1966_, v___y_1967_, v___y_1968_, v___y_1969_);
return v___x_2061_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2___boxed(lean_object* v_a_2062_, lean_object* v_tacticName_2063_, lean_object* v_mvarId_2064_, lean_object* v_recursorInfo_2065_, lean_object* v_indices_2066_, lean_object* v_a_2067_, lean_object* v_major_2068_, lean_object* v_x_2069_, lean_object* v_x_2070_, lean_object* v_x_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_){
_start:
{
lean_object* v_res_2077_; 
v_res_2077_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2(v_a_2062_, v_tacticName_2063_, v_mvarId_2064_, v_recursorInfo_2065_, v_indices_2066_, v_a_2067_, v_major_2068_, v_x_2069_, v_x_2070_, v_x_2071_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_);
lean_dec(v___y_2075_);
lean_dec_ref(v___y_2074_);
lean_dec(v___y_2073_);
lean_dec_ref(v___y_2072_);
lean_dec(v_x_2071_);
lean_dec_ref(v_indices_2066_);
return v_res_2077_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkRecursorAppPrefix(lean_object* v_mvarId_2078_, lean_object* v_tacticName_2079_, lean_object* v_majorFVarId_2080_, lean_object* v_recursorInfo_2081_, lean_object* v_indices_2082_, lean_object* v_a_2083_, lean_object* v_a_2084_, lean_object* v_a_2085_, lean_object* v_a_2086_){
_start:
{
lean_object* v_major_2088_; lean_object* v___x_2089_; 
lean_inc(v_majorFVarId_2080_);
v_major_2088_ = l_Lean_mkFVar(v_majorFVarId_2080_);
lean_inc(v_mvarId_2078_);
v___x_2089_ = l_Lean_MVarId_getType(v_mvarId_2078_, v_a_2083_, v_a_2084_, v_a_2085_, v_a_2086_);
if (lean_obj_tag(v___x_2089_) == 0)
{
lean_object* v_a_2090_; lean_object* v___x_2091_; 
v_a_2090_ = lean_ctor_get(v___x_2089_, 0);
lean_inc_n(v_a_2090_, 2);
lean_dec_ref_known(v___x_2089_, 1);
v___x_2091_ = l_Lean_Meta_getLevel(v_a_2090_, v_a_2083_, v_a_2084_, v_a_2085_, v_a_2086_);
if (lean_obj_tag(v___x_2091_) == 0)
{
lean_object* v_a_2092_; lean_object* v___x_2093_; 
v_a_2092_ = lean_ctor_get(v___x_2091_, 0);
lean_inc(v_a_2092_);
lean_dec_ref_known(v___x_2091_, 1);
v___x_2093_ = l_Lean_Meta_normalizeLevel(v_a_2092_, v_a_2083_, v_a_2084_, v_a_2085_, v_a_2086_);
if (lean_obj_tag(v___x_2093_) == 0)
{
lean_object* v_a_2094_; lean_object* v___x_2095_; 
v_a_2094_ = lean_ctor_get(v___x_2093_, 0);
lean_inc(v_a_2094_);
lean_dec_ref_known(v___x_2093_, 1);
v___x_2095_ = l_Lean_FVarId_getDecl___redArg(v_majorFVarId_2080_, v_a_2083_, v_a_2085_, v_a_2086_);
if (lean_obj_tag(v___x_2095_) == 0)
{
lean_object* v_a_2096_; lean_object* v_typeName_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; 
v_a_2096_ = lean_ctor_get(v___x_2095_, 0);
lean_inc(v_a_2096_);
lean_dec_ref_known(v___x_2095_, 1);
v_typeName_2097_ = lean_ctor_get(v_recursorInfo_2081_, 1);
v___x_2098_ = l_Lean_LocalDecl_type(v_a_2096_);
lean_dec(v_a_2096_);
lean_inc_ref(v___x_2098_);
v___x_2099_ = l_Lean_Meta_whnfUntil(v___x_2098_, v_typeName_2097_, v_a_2083_, v_a_2084_, v_a_2085_, v_a_2086_);
if (lean_obj_tag(v___x_2099_) == 0)
{
lean_object* v_a_2100_; 
v_a_2100_ = lean_ctor_get(v___x_2099_, 0);
lean_inc(v_a_2100_);
lean_dec_ref_known(v___x_2099_, 1);
if (lean_obj_tag(v_a_2100_) == 1)
{
lean_object* v_val_2101_; lean_object* v_dummy_2102_; lean_object* v_nargs_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; 
lean_dec_ref(v___x_2098_);
v_val_2101_ = lean_ctor_get(v_a_2100_, 0);
lean_inc(v_val_2101_);
lean_dec_ref_known(v_a_2100_, 1);
v_dummy_2102_ = lean_obj_once(&l_Lean_Meta_getMajorTypeIndices___closed__0, &l_Lean_Meta_getMajorTypeIndices___closed__0_once, _init_l_Lean_Meta_getMajorTypeIndices___closed__0);
v_nargs_2103_ = l_Lean_Expr_getAppNumArgs(v_val_2101_);
lean_inc(v_nargs_2103_);
v___x_2104_ = lean_mk_array(v_nargs_2103_, v_dummy_2102_);
v___x_2105_ = lean_unsigned_to_nat(1u);
v___x_2106_ = lean_nat_sub(v_nargs_2103_, v___x_2105_);
lean_dec(v_nargs_2103_);
v___x_2107_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2(v_a_2094_, v_tacticName_2079_, v_mvarId_2078_, v_recursorInfo_2081_, v_indices_2082_, v_a_2090_, v_major_2088_, v_val_2101_, v___x_2104_, v___x_2106_, v_a_2083_, v_a_2084_, v_a_2085_, v_a_2086_);
lean_dec(v___x_2106_);
return v___x_2107_;
}
else
{
lean_object* v___x_2108_; 
lean_dec(v_a_2100_);
lean_dec(v_a_2094_);
lean_dec(v_a_2090_);
lean_dec_ref(v_major_2088_);
lean_dec_ref(v_recursorInfo_2081_);
v___x_2108_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg(v_tacticName_2079_, v_mvarId_2078_, v___x_2098_, v_a_2083_, v_a_2084_, v_a_2085_, v_a_2086_);
return v___x_2108_;
}
}
else
{
lean_object* v_a_2109_; lean_object* v___x_2111_; uint8_t v_isShared_2112_; uint8_t v_isSharedCheck_2116_; 
lean_dec_ref(v___x_2098_);
lean_dec(v_a_2094_);
lean_dec(v_a_2090_);
lean_dec_ref(v_major_2088_);
lean_dec_ref(v_recursorInfo_2081_);
lean_dec(v_tacticName_2079_);
lean_dec(v_mvarId_2078_);
v_a_2109_ = lean_ctor_get(v___x_2099_, 0);
v_isSharedCheck_2116_ = !lean_is_exclusive(v___x_2099_);
if (v_isSharedCheck_2116_ == 0)
{
v___x_2111_ = v___x_2099_;
v_isShared_2112_ = v_isSharedCheck_2116_;
goto v_resetjp_2110_;
}
else
{
lean_inc(v_a_2109_);
lean_dec(v___x_2099_);
v___x_2111_ = lean_box(0);
v_isShared_2112_ = v_isSharedCheck_2116_;
goto v_resetjp_2110_;
}
v_resetjp_2110_:
{
lean_object* v___x_2114_; 
if (v_isShared_2112_ == 0)
{
v___x_2114_ = v___x_2111_;
goto v_reusejp_2113_;
}
else
{
lean_object* v_reuseFailAlloc_2115_; 
v_reuseFailAlloc_2115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2115_, 0, v_a_2109_);
v___x_2114_ = v_reuseFailAlloc_2115_;
goto v_reusejp_2113_;
}
v_reusejp_2113_:
{
return v___x_2114_;
}
}
}
}
else
{
lean_object* v_a_2117_; lean_object* v___x_2119_; uint8_t v_isShared_2120_; uint8_t v_isSharedCheck_2124_; 
lean_dec(v_a_2094_);
lean_dec(v_a_2090_);
lean_dec_ref(v_major_2088_);
lean_dec_ref(v_recursorInfo_2081_);
lean_dec(v_tacticName_2079_);
lean_dec(v_mvarId_2078_);
v_a_2117_ = lean_ctor_get(v___x_2095_, 0);
v_isSharedCheck_2124_ = !lean_is_exclusive(v___x_2095_);
if (v_isSharedCheck_2124_ == 0)
{
v___x_2119_ = v___x_2095_;
v_isShared_2120_ = v_isSharedCheck_2124_;
goto v_resetjp_2118_;
}
else
{
lean_inc(v_a_2117_);
lean_dec(v___x_2095_);
v___x_2119_ = lean_box(0);
v_isShared_2120_ = v_isSharedCheck_2124_;
goto v_resetjp_2118_;
}
v_resetjp_2118_:
{
lean_object* v___x_2122_; 
if (v_isShared_2120_ == 0)
{
v___x_2122_ = v___x_2119_;
goto v_reusejp_2121_;
}
else
{
lean_object* v_reuseFailAlloc_2123_; 
v_reuseFailAlloc_2123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2123_, 0, v_a_2117_);
v___x_2122_ = v_reuseFailAlloc_2123_;
goto v_reusejp_2121_;
}
v_reusejp_2121_:
{
return v___x_2122_;
}
}
}
}
else
{
lean_object* v_a_2125_; lean_object* v___x_2127_; uint8_t v_isShared_2128_; uint8_t v_isSharedCheck_2132_; 
lean_dec(v_a_2090_);
lean_dec_ref(v_major_2088_);
lean_dec_ref(v_recursorInfo_2081_);
lean_dec(v_majorFVarId_2080_);
lean_dec(v_tacticName_2079_);
lean_dec(v_mvarId_2078_);
v_a_2125_ = lean_ctor_get(v___x_2093_, 0);
v_isSharedCheck_2132_ = !lean_is_exclusive(v___x_2093_);
if (v_isSharedCheck_2132_ == 0)
{
v___x_2127_ = v___x_2093_;
v_isShared_2128_ = v_isSharedCheck_2132_;
goto v_resetjp_2126_;
}
else
{
lean_inc(v_a_2125_);
lean_dec(v___x_2093_);
v___x_2127_ = lean_box(0);
v_isShared_2128_ = v_isSharedCheck_2132_;
goto v_resetjp_2126_;
}
v_resetjp_2126_:
{
lean_object* v___x_2130_; 
if (v_isShared_2128_ == 0)
{
v___x_2130_ = v___x_2127_;
goto v_reusejp_2129_;
}
else
{
lean_object* v_reuseFailAlloc_2131_; 
v_reuseFailAlloc_2131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2131_, 0, v_a_2125_);
v___x_2130_ = v_reuseFailAlloc_2131_;
goto v_reusejp_2129_;
}
v_reusejp_2129_:
{
return v___x_2130_;
}
}
}
}
else
{
lean_object* v_a_2133_; lean_object* v___x_2135_; uint8_t v_isShared_2136_; uint8_t v_isSharedCheck_2140_; 
lean_dec(v_a_2090_);
lean_dec_ref(v_major_2088_);
lean_dec_ref(v_recursorInfo_2081_);
lean_dec(v_majorFVarId_2080_);
lean_dec(v_tacticName_2079_);
lean_dec(v_mvarId_2078_);
v_a_2133_ = lean_ctor_get(v___x_2091_, 0);
v_isSharedCheck_2140_ = !lean_is_exclusive(v___x_2091_);
if (v_isSharedCheck_2140_ == 0)
{
v___x_2135_ = v___x_2091_;
v_isShared_2136_ = v_isSharedCheck_2140_;
goto v_resetjp_2134_;
}
else
{
lean_inc(v_a_2133_);
lean_dec(v___x_2091_);
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
lean_dec_ref(v_major_2088_);
lean_dec_ref(v_recursorInfo_2081_);
lean_dec(v_majorFVarId_2080_);
lean_dec(v_tacticName_2079_);
lean_dec(v_mvarId_2078_);
return v___x_2089_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkRecursorAppPrefix___boxed(lean_object* v_mvarId_2141_, lean_object* v_tacticName_2142_, lean_object* v_majorFVarId_2143_, lean_object* v_recursorInfo_2144_, lean_object* v_indices_2145_, lean_object* v_a_2146_, lean_object* v_a_2147_, lean_object* v_a_2148_, lean_object* v_a_2149_, lean_object* v_a_2150_){
_start:
{
lean_object* v_res_2151_; 
v_res_2151_ = l_Lean_Meta_mkRecursorAppPrefix(v_mvarId_2141_, v_tacticName_2142_, v_majorFVarId_2143_, v_recursorInfo_2144_, v_indices_2145_, v_a_2146_, v_a_2147_, v_a_2148_, v_a_2149_);
lean_dec(v_a_2149_);
lean_dec_ref(v_a_2148_);
lean_dec(v_a_2147_);
lean_dec_ref(v_a_2146_);
lean_dec_ref(v_indices_2145_);
return v_res_2151_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1(lean_object* v_00_u03b1_2152_, lean_object* v_name_2153_, lean_object* v_msg_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_){
_start:
{
lean_object* v___x_2160_; 
v___x_2160_ = l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1___redArg(v_name_2153_, v_msg_2154_, v___y_2155_, v___y_2156_, v___y_2157_, v___y_2158_);
return v___x_2160_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1___boxed(lean_object* v_00_u03b1_2161_, lean_object* v_name_2162_, lean_object* v_msg_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_){
_start:
{
lean_object* v_res_2169_; 
v_res_2169_ = l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1(v_00_u03b1_2161_, v_name_2162_, v_msg_2163_, v___y_2164_, v___y_2165_, v___y_2166_, v___y_2167_);
lean_dec(v___y_2167_);
lean_dec_ref(v___y_2166_);
lean_dec(v___y_2165_);
lean_dec_ref(v___y_2164_);
return v_res_2169_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___redArg(lean_object* v_mvarId_2170_, lean_object* v_x_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_){
_start:
{
lean_object* v___x_2177_; 
v___x_2177_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_2170_, v_x_2171_, v___y_2172_, v___y_2173_, v___y_2174_, v___y_2175_);
if (lean_obj_tag(v___x_2177_) == 0)
{
lean_object* v_a_2178_; lean_object* v___x_2180_; uint8_t v_isShared_2181_; uint8_t v_isSharedCheck_2185_; 
v_a_2178_ = lean_ctor_get(v___x_2177_, 0);
v_isSharedCheck_2185_ = !lean_is_exclusive(v___x_2177_);
if (v_isSharedCheck_2185_ == 0)
{
v___x_2180_ = v___x_2177_;
v_isShared_2181_ = v_isSharedCheck_2185_;
goto v_resetjp_2179_;
}
else
{
lean_inc(v_a_2178_);
lean_dec(v___x_2177_);
v___x_2180_ = lean_box(0);
v_isShared_2181_ = v_isSharedCheck_2185_;
goto v_resetjp_2179_;
}
v_resetjp_2179_:
{
lean_object* v___x_2183_; 
if (v_isShared_2181_ == 0)
{
v___x_2183_ = v___x_2180_;
goto v_reusejp_2182_;
}
else
{
lean_object* v_reuseFailAlloc_2184_; 
v_reuseFailAlloc_2184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2184_, 0, v_a_2178_);
v___x_2183_ = v_reuseFailAlloc_2184_;
goto v_reusejp_2182_;
}
v_reusejp_2182_:
{
return v___x_2183_;
}
}
}
else
{
lean_object* v_a_2186_; lean_object* v___x_2188_; uint8_t v_isShared_2189_; uint8_t v_isSharedCheck_2193_; 
v_a_2186_ = lean_ctor_get(v___x_2177_, 0);
v_isSharedCheck_2193_ = !lean_is_exclusive(v___x_2177_);
if (v_isSharedCheck_2193_ == 0)
{
v___x_2188_ = v___x_2177_;
v_isShared_2189_ = v_isSharedCheck_2193_;
goto v_resetjp_2187_;
}
else
{
lean_inc(v_a_2186_);
lean_dec(v___x_2177_);
v___x_2188_ = lean_box(0);
v_isShared_2189_ = v_isSharedCheck_2193_;
goto v_resetjp_2187_;
}
v_resetjp_2187_:
{
lean_object* v___x_2191_; 
if (v_isShared_2189_ == 0)
{
v___x_2191_ = v___x_2188_;
goto v_reusejp_2190_;
}
else
{
lean_object* v_reuseFailAlloc_2192_; 
v_reuseFailAlloc_2192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2192_, 0, v_a_2186_);
v___x_2191_ = v_reuseFailAlloc_2192_;
goto v_reusejp_2190_;
}
v_reusejp_2190_:
{
return v___x_2191_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___redArg___boxed(lean_object* v_mvarId_2194_, lean_object* v_x_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_){
_start:
{
lean_object* v_res_2201_; 
v_res_2201_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___redArg(v_mvarId_2194_, v_x_2195_, v___y_2196_, v___y_2197_, v___y_2198_, v___y_2199_);
lean_dec(v___y_2199_);
lean_dec_ref(v___y_2198_);
lean_dec(v___y_2197_);
lean_dec_ref(v___y_2196_);
return v_res_2201_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3(lean_object* v_00_u03b1_2202_, lean_object* v_mvarId_2203_, lean_object* v_x_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_){
_start:
{
lean_object* v___x_2210_; 
v___x_2210_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___redArg(v_mvarId_2203_, v_x_2204_, v___y_2205_, v___y_2206_, v___y_2207_, v___y_2208_);
return v___x_2210_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___boxed(lean_object* v_00_u03b1_2211_, lean_object* v_mvarId_2212_, lean_object* v_x_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_){
_start:
{
lean_object* v_res_2219_; 
v_res_2219_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3(v_00_u03b1_2211_, v_mvarId_2212_, v_x_2213_, v___y_2214_, v___y_2215_, v___y_2216_, v___y_2217_);
lean_dec(v___y_2217_);
lean_dec_ref(v___y_2216_);
lean_dec(v___y_2215_);
lean_dec_ref(v___y_2214_);
return v_res_2219_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_induction_spec__2(lean_object* v_fst_2220_, lean_object* v_as_2221_, size_t v_sz_2222_, size_t v_i_2223_, lean_object* v_b_2224_){
_start:
{
uint8_t v___x_2225_; 
v___x_2225_ = lean_usize_dec_lt(v_i_2223_, v_sz_2222_);
if (v___x_2225_ == 0)
{
return v_b_2224_;
}
else
{
lean_object* v_fst_2226_; lean_object* v_snd_2227_; lean_object* v___x_2229_; uint8_t v_isShared_2230_; uint8_t v_isSharedCheck_2245_; 
v_fst_2226_ = lean_ctor_get(v_b_2224_, 0);
v_snd_2227_ = lean_ctor_get(v_b_2224_, 1);
v_isSharedCheck_2245_ = !lean_is_exclusive(v_b_2224_);
if (v_isSharedCheck_2245_ == 0)
{
v___x_2229_ = v_b_2224_;
v_isShared_2230_ = v_isSharedCheck_2245_;
goto v_resetjp_2228_;
}
else
{
lean_inc(v_snd_2227_);
lean_inc(v_fst_2226_);
lean_dec(v_b_2224_);
v___x_2229_ = lean_box(0);
v_isShared_2230_ = v_isSharedCheck_2245_;
goto v_resetjp_2228_;
}
v_resetjp_2228_:
{
lean_object* v___x_2231_; lean_object* v_a_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2240_; 
v___x_2231_ = lean_box(0);
v_a_2232_ = lean_array_uget_borrowed(v_as_2221_, v_i_2223_);
v___x_2233_ = l_Lean_Expr_fvarId_x21(v_a_2232_);
v___x_2234_ = lean_array_get_borrowed(v___x_2231_, v_fst_2220_, v_snd_2227_);
lean_inc(v___x_2234_);
v___x_2235_ = l_Lean_mkFVar(v___x_2234_);
v___x_2236_ = l_Lean_Meta_FVarSubst_insert(v_fst_2226_, v___x_2233_, v___x_2235_);
v___x_2237_ = lean_unsigned_to_nat(1u);
v___x_2238_ = lean_nat_add(v_snd_2227_, v___x_2237_);
lean_dec(v_snd_2227_);
if (v_isShared_2230_ == 0)
{
lean_ctor_set(v___x_2229_, 1, v___x_2238_);
lean_ctor_set(v___x_2229_, 0, v___x_2236_);
v___x_2240_ = v___x_2229_;
goto v_reusejp_2239_;
}
else
{
lean_object* v_reuseFailAlloc_2244_; 
v_reuseFailAlloc_2244_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2244_, 0, v___x_2236_);
lean_ctor_set(v_reuseFailAlloc_2244_, 1, v___x_2238_);
v___x_2240_ = v_reuseFailAlloc_2244_;
goto v_reusejp_2239_;
}
v_reusejp_2239_:
{
size_t v___x_2241_; size_t v___x_2242_; 
v___x_2241_ = ((size_t)1ULL);
v___x_2242_ = lean_usize_add(v_i_2223_, v___x_2241_);
v_i_2223_ = v___x_2242_;
v_b_2224_ = v___x_2240_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_induction_spec__2___boxed(lean_object* v_fst_2246_, lean_object* v_as_2247_, lean_object* v_sz_2248_, lean_object* v_i_2249_, lean_object* v_b_2250_){
_start:
{
size_t v_sz_boxed_2251_; size_t v_i_boxed_2252_; lean_object* v_res_2253_; 
v_sz_boxed_2251_ = lean_unbox_usize(v_sz_2248_);
lean_dec(v_sz_2248_);
v_i_boxed_2252_ = lean_unbox_usize(v_i_2249_);
lean_dec(v_i_2249_);
v_res_2253_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_induction_spec__2(v_fst_2246_, v_as_2247_, v_sz_boxed_2251_, v_i_boxed_2252_, v_b_2250_);
lean_dec_ref(v_as_2247_);
lean_dec_ref(v_fst_2246_);
return v_res_2253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4___lam__0(lean_object* v_snd_2254_, lean_object* v___x_2255_, lean_object* v_fst_2256_, lean_object* v_a_2257_, lean_object* v___x_2258_, lean_object* v_givenNames_2259_, lean_object* v_fst_2260_, lean_object* v___x_2261_, lean_object* v_fst_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_){
_start:
{
lean_object* v___x_2268_; 
lean_inc_ref(v_a_2257_);
lean_inc(v_snd_2254_);
v___x_2268_ = l_Lean_Meta_mkRecursorAppPrefix(v_snd_2254_, v___x_2255_, v_fst_2256_, v_a_2257_, v___x_2258_, v___y_2263_, v___y_2264_, v___y_2265_, v___y_2266_);
if (lean_obj_tag(v___x_2268_) == 0)
{
lean_object* v_a_2269_; lean_object* v___x_2270_; 
v_a_2269_ = lean_ctor_get(v___x_2268_, 0);
lean_inc(v_a_2269_);
lean_dec_ref_known(v___x_2268_, 1);
v___x_2270_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize(v_snd_2254_, v_givenNames_2259_, v_a_2257_, v_fst_2260_, v___x_2261_, v___x_2258_, v_fst_2262_, v_a_2269_, v___y_2263_, v___y_2264_, v___y_2265_, v___y_2266_);
lean_dec_ref(v_a_2257_);
return v___x_2270_;
}
else
{
lean_object* v_a_2271_; lean_object* v___x_2273_; uint8_t v_isShared_2274_; uint8_t v_isSharedCheck_2278_; 
lean_dec(v_fst_2262_);
lean_dec_ref(v___x_2261_);
lean_dec_ref(v_a_2257_);
lean_dec(v_snd_2254_);
v_a_2271_ = lean_ctor_get(v___x_2268_, 0);
v_isSharedCheck_2278_ = !lean_is_exclusive(v___x_2268_);
if (v_isSharedCheck_2278_ == 0)
{
v___x_2273_ = v___x_2268_;
v_isShared_2274_ = v_isSharedCheck_2278_;
goto v_resetjp_2272_;
}
else
{
lean_inc(v_a_2271_);
lean_dec(v___x_2268_);
v___x_2273_ = lean_box(0);
v_isShared_2274_ = v_isSharedCheck_2278_;
goto v_resetjp_2272_;
}
v_resetjp_2272_:
{
lean_object* v___x_2276_; 
if (v_isShared_2274_ == 0)
{
v___x_2276_ = v___x_2273_;
goto v_reusejp_2275_;
}
else
{
lean_object* v_reuseFailAlloc_2277_; 
v_reuseFailAlloc_2277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2277_, 0, v_a_2271_);
v___x_2276_ = v_reuseFailAlloc_2277_;
goto v_reusejp_2275_;
}
v_reusejp_2275_:
{
return v___x_2276_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4___lam__0___boxed(lean_object* v_snd_2279_, lean_object* v___x_2280_, lean_object* v_fst_2281_, lean_object* v_a_2282_, lean_object* v___x_2283_, lean_object* v_givenNames_2284_, lean_object* v_fst_2285_, lean_object* v___x_2286_, lean_object* v_fst_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_){
_start:
{
lean_object* v_res_2293_; 
v_res_2293_ = l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4___lam__0(v_snd_2279_, v___x_2280_, v_fst_2281_, v_a_2282_, v___x_2283_, v_givenNames_2284_, v_fst_2285_, v___x_2286_, v_fst_2287_, v___y_2288_, v___y_2289_, v___y_2290_, v___y_2291_);
lean_dec(v___y_2291_);
lean_dec_ref(v___y_2290_);
lean_dec(v___y_2289_);
lean_dec_ref(v___y_2288_);
lean_dec_ref(v_fst_2285_);
lean_dec_ref(v_givenNames_2284_);
lean_dec_ref(v___x_2283_);
return v_res_2293_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_induction_spec__1(size_t v_sz_2294_, size_t v_i_2295_, lean_object* v_bs_2296_){
_start:
{
uint8_t v___x_2297_; 
v___x_2297_ = lean_usize_dec_lt(v_i_2295_, v_sz_2294_);
if (v___x_2297_ == 0)
{
return v_bs_2296_;
}
else
{
lean_object* v_v_2298_; lean_object* v___x_2299_; lean_object* v_bs_x27_2300_; lean_object* v___x_2301_; size_t v___x_2302_; size_t v___x_2303_; lean_object* v___x_2304_; 
v_v_2298_ = lean_array_uget(v_bs_2296_, v_i_2295_);
v___x_2299_ = lean_unsigned_to_nat(0u);
v_bs_x27_2300_ = lean_array_uset(v_bs_2296_, v_i_2295_, v___x_2299_);
v___x_2301_ = l_Lean_Expr_fvarId_x21(v_v_2298_);
lean_dec(v_v_2298_);
v___x_2302_ = ((size_t)1ULL);
v___x_2303_ = lean_usize_add(v_i_2295_, v___x_2302_);
v___x_2304_ = lean_array_uset(v_bs_x27_2300_, v_i_2295_, v___x_2301_);
v_i_2295_ = v___x_2303_;
v_bs_2296_ = v___x_2304_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_induction_spec__1___boxed(lean_object* v_sz_2306_, lean_object* v_i_2307_, lean_object* v_bs_2308_){
_start:
{
size_t v_sz_boxed_2309_; size_t v_i_boxed_2310_; lean_object* v_res_2311_; 
v_sz_boxed_2309_ = lean_unbox_usize(v_sz_2306_);
lean_dec(v_sz_2306_);
v_i_boxed_2310_ = lean_unbox_usize(v_i_2307_);
lean_dec(v_i_2307_);
v_res_2311_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_induction_spec__1(v_sz_boxed_2309_, v_i_boxed_2310_, v_bs_2308_);
return v_res_2311_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_MVarId_induction_spec__0(lean_object* v_majorTypeArgs_2312_, lean_object* v_val_2313_, lean_object* v_mvarId_2314_, lean_object* v_as_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_){
_start:
{
if (lean_obj_tag(v_as_2315_) == 0)
{
lean_object* v___x_2321_; lean_object* v___x_2322_; 
lean_dec(v_mvarId_2314_);
lean_dec_ref(v_val_2313_);
v___x_2321_ = lean_box(0);
v___x_2322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2322_, 0, v___x_2321_);
return v___x_2322_;
}
else
{
lean_object* v_head_2323_; 
v_head_2323_ = lean_ctor_get(v_as_2315_, 0);
lean_inc(v_head_2323_);
if (lean_obj_tag(v_head_2323_) == 0)
{
lean_object* v_tail_2324_; 
v_tail_2324_ = lean_ctor_get(v_as_2315_, 1);
lean_inc(v_tail_2324_);
lean_dec_ref_known(v_as_2315_, 2);
v_as_2315_ = v_tail_2324_;
goto _start;
}
else
{
lean_object* v_tail_2326_; lean_object* v___x_2328_; uint8_t v_isShared_2329_; uint8_t v_isSharedCheck_2349_; 
v_tail_2326_ = lean_ctor_get(v_as_2315_, 1);
v_isSharedCheck_2349_ = !lean_is_exclusive(v_as_2315_);
if (v_isSharedCheck_2349_ == 0)
{
lean_object* v_unused_2350_; 
v_unused_2350_ = lean_ctor_get(v_as_2315_, 0);
lean_dec(v_unused_2350_);
v___x_2328_ = v_as_2315_;
v_isShared_2329_ = v_isSharedCheck_2349_;
goto v_resetjp_2327_;
}
else
{
lean_inc(v_tail_2326_);
lean_dec(v_as_2315_);
v___x_2328_ = lean_box(0);
v_isShared_2329_ = v_isSharedCheck_2349_;
goto v_resetjp_2327_;
}
v_resetjp_2327_:
{
lean_object* v_val_2330_; lean_object* v___x_2332_; uint8_t v_isShared_2333_; uint8_t v_isSharedCheck_2348_; 
v_val_2330_ = lean_ctor_get(v_head_2323_, 0);
v_isSharedCheck_2348_ = !lean_is_exclusive(v_head_2323_);
if (v_isSharedCheck_2348_ == 0)
{
v___x_2332_ = v_head_2323_;
v_isShared_2333_ = v_isSharedCheck_2348_;
goto v_resetjp_2331_;
}
else
{
lean_inc(v_val_2330_);
lean_dec(v_head_2323_);
v___x_2332_ = lean_box(0);
v_isShared_2333_ = v_isSharedCheck_2348_;
goto v_resetjp_2331_;
}
v_resetjp_2331_:
{
lean_object* v___x_2334_; uint8_t v___x_2335_; 
v___x_2334_ = lean_array_get_size(v_majorTypeArgs_2312_);
v___x_2335_ = lean_nat_dec_le(v___x_2334_, v_val_2330_);
lean_dec(v_val_2330_);
if (v___x_2335_ == 0)
{
lean_del_object(v___x_2332_);
lean_del_object(v___x_2328_);
v_as_2315_ = v_tail_2326_;
goto _start;
}
else
{
lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2341_; 
v___x_2337_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1));
v___x_2338_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__5, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__5);
lean_inc_ref(v_val_2313_);
v___x_2339_ = l_Lean_indentExpr(v_val_2313_);
if (v_isShared_2329_ == 0)
{
lean_ctor_set_tag(v___x_2328_, 7);
lean_ctor_set(v___x_2328_, 1, v___x_2339_);
lean_ctor_set(v___x_2328_, 0, v___x_2338_);
v___x_2341_ = v___x_2328_;
goto v_reusejp_2340_;
}
else
{
lean_object* v_reuseFailAlloc_2347_; 
v_reuseFailAlloc_2347_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2347_, 0, v___x_2338_);
lean_ctor_set(v_reuseFailAlloc_2347_, 1, v___x_2339_);
v___x_2341_ = v_reuseFailAlloc_2347_;
goto v_reusejp_2340_;
}
v_reusejp_2340_:
{
lean_object* v___x_2343_; 
if (v_isShared_2333_ == 0)
{
lean_ctor_set(v___x_2332_, 0, v___x_2341_);
v___x_2343_ = v___x_2332_;
goto v_reusejp_2342_;
}
else
{
lean_object* v_reuseFailAlloc_2346_; 
v_reuseFailAlloc_2346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2346_, 0, v___x_2341_);
v___x_2343_ = v_reuseFailAlloc_2346_;
goto v_reusejp_2342_;
}
v_reusejp_2342_:
{
lean_object* v___x_2344_; 
lean_inc(v_mvarId_2314_);
v___x_2344_ = l_Lean_Meta_throwTacticEx___redArg(v___x_2337_, v_mvarId_2314_, v___x_2343_, v___y_2316_, v___y_2317_, v___y_2318_, v___y_2319_);
if (lean_obj_tag(v___x_2344_) == 0)
{
lean_dec_ref_known(v___x_2344_, 1);
v_as_2315_ = v_tail_2326_;
goto _start;
}
else
{
lean_dec(v_tail_2326_);
lean_dec(v_mvarId_2314_);
lean_dec_ref(v_val_2313_);
return v___x_2344_;
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
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_MVarId_induction_spec__0___boxed(lean_object* v_majorTypeArgs_2351_, lean_object* v_val_2352_, lean_object* v_mvarId_2353_, lean_object* v_as_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_){
_start:
{
lean_object* v_res_2360_; 
v_res_2360_ = l_List_forM___at___00Lean_MVarId_induction_spec__0(v_majorTypeArgs_2351_, v_val_2352_, v_mvarId_2353_, v_as_2354_, v___y_2355_, v___y_2356_, v___y_2357_, v___y_2358_);
lean_dec(v___y_2358_);
lean_dec_ref(v___y_2357_);
lean_dec(v___y_2356_);
lean_dec_ref(v___y_2355_);
lean_dec_ref(v_majorTypeArgs_2351_);
return v_res_2360_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__1(void){
_start:
{
lean_object* v___x_2362_; lean_object* v___x_2363_; 
v___x_2362_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__0));
v___x_2363_ = l_Lean_stringToMessageData(v___x_2362_);
return v___x_2363_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__3(void){
_start:
{
lean_object* v___x_2365_; lean_object* v___x_2366_; 
v___x_2365_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__2));
v___x_2366_ = l_Lean_stringToMessageData(v___x_2365_);
return v___x_2366_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__5(void){
_start:
{
lean_object* v___x_2368_; lean_object* v___x_2369_; 
v___x_2368_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__4));
v___x_2369_ = l_Lean_stringToMessageData(v___x_2368_);
return v___x_2369_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4(lean_object* v_a_2370_, lean_object* v_val_2371_, lean_object* v_mvarId_2372_, lean_object* v_majorFVarId_2373_, lean_object* v_givenNames_2374_, lean_object* v_recursorName_2375_, lean_object* v_x_2376_, lean_object* v_x_2377_, lean_object* v_x_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_){
_start:
{
if (lean_obj_tag(v_x_2376_) == 5)
{
lean_object* v_fn_2384_; lean_object* v_arg_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; 
v_fn_2384_ = lean_ctor_get(v_x_2376_, 0);
lean_inc_ref(v_fn_2384_);
v_arg_2385_ = lean_ctor_get(v_x_2376_, 1);
lean_inc_ref(v_arg_2385_);
lean_dec_ref_known(v_x_2376_, 2);
v___x_2386_ = lean_array_set(v_x_2377_, v_x_2378_, v_arg_2385_);
v___x_2387_ = lean_unsigned_to_nat(1u);
v___x_2388_ = lean_nat_sub(v_x_2378_, v___x_2387_);
lean_dec(v_x_2378_);
v_x_2376_ = v_fn_2384_;
v_x_2377_ = v___x_2386_;
v_x_2378_ = v___x_2388_;
goto _start;
}
else
{
uint8_t v_depElim_2390_; lean_object* v_paramsPos_2391_; lean_object* v___x_2392_; lean_object* v___y_2394_; lean_object* v___y_2395_; lean_object* v___y_2396_; lean_object* v___y_2397_; lean_object* v___y_2398_; size_t v___y_2399_; lean_object* v___y_2400_; lean_object* v___y_2401_; lean_object* v___y_2402_; lean_object* v___y_2403_; lean_object* v___y_2404_; lean_object* v___y_2405_; lean_object* v_cls_2410_; lean_object* v___x_2411_; 
lean_dec(v_x_2378_);
lean_dec_ref(v_x_2376_);
v_depElim_2390_ = lean_ctor_get_uint8(v_a_2370_, sizeof(void*)*8);
v_paramsPos_2391_ = lean_ctor_get(v_a_2370_, 5);
v___x_2392_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1));
v_cls_2410_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__2));
lean_inc(v_paramsPos_2391_);
lean_inc(v_mvarId_2372_);
lean_inc_ref(v_val_2371_);
v___x_2411_ = l_List_forM___at___00Lean_MVarId_induction_spec__0(v_x_2377_, v_val_2371_, v_mvarId_2372_, v_paramsPos_2391_, v___y_2379_, v___y_2380_, v___y_2381_, v___y_2382_);
lean_dec_ref(v_x_2377_);
if (lean_obj_tag(v___x_2411_) == 0)
{
lean_object* v___x_2412_; 
lean_dec_ref_known(v___x_2411_, 1);
lean_inc_ref(v_a_2370_);
lean_inc(v_mvarId_2372_);
v___x_2412_ = l_Lean_Meta_getMajorTypeIndices(v_mvarId_2372_, v___x_2392_, v_a_2370_, v_val_2371_, v___y_2379_, v___y_2380_, v___y_2381_, v___y_2382_);
if (lean_obj_tag(v___x_2412_) == 0)
{
lean_object* v_a_2413_; lean_object* v___y_2415_; lean_object* v___y_2416_; lean_object* v___y_2417_; lean_object* v___y_2418_; lean_object* v___x_2502_; 
v_a_2413_ = lean_ctor_get(v___x_2412_, 0);
lean_inc(v_a_2413_);
lean_dec_ref_known(v___x_2412_, 1);
lean_inc(v_mvarId_2372_);
v___x_2502_ = l_Lean_MVarId_getType(v_mvarId_2372_, v___y_2379_, v___y_2380_, v___y_2381_, v___y_2382_);
if (lean_obj_tag(v___x_2502_) == 0)
{
if (v_depElim_2390_ == 0)
{
lean_object* v_a_2503_; lean_object* v___x_2504_; lean_object* v_a_2505_; lean_object* v___x_2507_; uint8_t v_isShared_2508_; uint8_t v_isSharedCheck_2527_; 
v_a_2503_ = lean_ctor_get(v___x_2502_, 0);
lean_inc(v_a_2503_);
lean_dec_ref_known(v___x_2502_, 1);
lean_inc(v_majorFVarId_2373_);
v___x_2504_ = l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2___redArg(v_a_2503_, v_majorFVarId_2373_, v___y_2380_);
v_a_2505_ = lean_ctor_get(v___x_2504_, 0);
v_isSharedCheck_2527_ = !lean_is_exclusive(v___x_2504_);
if (v_isSharedCheck_2527_ == 0)
{
v___x_2507_ = v___x_2504_;
v_isShared_2508_ = v_isSharedCheck_2527_;
goto v_resetjp_2506_;
}
else
{
lean_inc(v_a_2505_);
lean_dec(v___x_2504_);
v___x_2507_ = lean_box(0);
v_isShared_2508_ = v_isSharedCheck_2527_;
goto v_resetjp_2506_;
}
v_resetjp_2506_:
{
uint8_t v___x_2509_; 
v___x_2509_ = lean_unbox(v_a_2505_);
lean_dec(v_a_2505_);
if (v___x_2509_ == 0)
{
lean_del_object(v___x_2507_);
lean_dec(v_recursorName_2375_);
v___y_2415_ = v___y_2379_;
v___y_2416_ = v___y_2380_;
v___y_2417_ = v___y_2381_;
v___y_2418_ = v___y_2382_;
goto v___jp_2414_;
}
else
{
lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2516_; 
v___x_2510_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__3, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__3);
v___x_2511_ = l_Lean_MessageData_ofName(v_recursorName_2375_);
v___x_2512_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2512_, 0, v___x_2510_);
lean_ctor_set(v___x_2512_, 1, v___x_2511_);
v___x_2513_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__5, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__5_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__5);
v___x_2514_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2514_, 0, v___x_2512_);
lean_ctor_set(v___x_2514_, 1, v___x_2513_);
if (v_isShared_2508_ == 0)
{
lean_ctor_set_tag(v___x_2507_, 1);
lean_ctor_set(v___x_2507_, 0, v___x_2514_);
v___x_2516_ = v___x_2507_;
goto v_reusejp_2515_;
}
else
{
lean_object* v_reuseFailAlloc_2526_; 
v_reuseFailAlloc_2526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2526_, 0, v___x_2514_);
v___x_2516_ = v_reuseFailAlloc_2526_;
goto v_reusejp_2515_;
}
v_reusejp_2515_:
{
lean_object* v___x_2517_; 
lean_inc(v_mvarId_2372_);
v___x_2517_ = l_Lean_Meta_throwTacticEx___redArg(v___x_2392_, v_mvarId_2372_, v___x_2516_, v___y_2379_, v___y_2380_, v___y_2381_, v___y_2382_);
if (lean_obj_tag(v___x_2517_) == 0)
{
lean_dec_ref_known(v___x_2517_, 1);
v___y_2415_ = v___y_2379_;
v___y_2416_ = v___y_2380_;
v___y_2417_ = v___y_2381_;
v___y_2418_ = v___y_2382_;
goto v___jp_2414_;
}
else
{
lean_object* v_a_2518_; lean_object* v___x_2520_; uint8_t v_isShared_2521_; uint8_t v_isSharedCheck_2525_; 
lean_dec(v_a_2413_);
lean_dec_ref(v_givenNames_2374_);
lean_dec(v_majorFVarId_2373_);
lean_dec(v_mvarId_2372_);
lean_dec_ref(v_a_2370_);
v_a_2518_ = lean_ctor_get(v___x_2517_, 0);
v_isSharedCheck_2525_ = !lean_is_exclusive(v___x_2517_);
if (v_isSharedCheck_2525_ == 0)
{
v___x_2520_ = v___x_2517_;
v_isShared_2521_ = v_isSharedCheck_2525_;
goto v_resetjp_2519_;
}
else
{
lean_inc(v_a_2518_);
lean_dec(v___x_2517_);
v___x_2520_ = lean_box(0);
v_isShared_2521_ = v_isSharedCheck_2525_;
goto v_resetjp_2519_;
}
v_resetjp_2519_:
{
lean_object* v___x_2523_; 
if (v_isShared_2521_ == 0)
{
v___x_2523_ = v___x_2520_;
goto v_reusejp_2522_;
}
else
{
lean_object* v_reuseFailAlloc_2524_; 
v_reuseFailAlloc_2524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2524_, 0, v_a_2518_);
v___x_2523_ = v_reuseFailAlloc_2524_;
goto v_reusejp_2522_;
}
v_reusejp_2522_:
{
return v___x_2523_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v___x_2502_, 1);
lean_dec(v_recursorName_2375_);
v___y_2415_ = v___y_2379_;
v___y_2416_ = v___y_2380_;
v___y_2417_ = v___y_2381_;
v___y_2418_ = v___y_2382_;
goto v___jp_2414_;
}
}
else
{
lean_object* v_a_2528_; lean_object* v___x_2530_; uint8_t v_isShared_2531_; uint8_t v_isSharedCheck_2535_; 
lean_dec(v_a_2413_);
lean_dec(v_recursorName_2375_);
lean_dec_ref(v_givenNames_2374_);
lean_dec(v_majorFVarId_2373_);
lean_dec(v_mvarId_2372_);
lean_dec_ref(v_a_2370_);
v_a_2528_ = lean_ctor_get(v___x_2502_, 0);
v_isSharedCheck_2535_ = !lean_is_exclusive(v___x_2502_);
if (v_isSharedCheck_2535_ == 0)
{
v___x_2530_ = v___x_2502_;
v_isShared_2531_ = v_isSharedCheck_2535_;
goto v_resetjp_2529_;
}
else
{
lean_inc(v_a_2528_);
lean_dec(v___x_2502_);
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
v___jp_2414_:
{
size_t v_sz_2419_; size_t v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; uint8_t v___x_2423_; uint8_t v___x_2424_; lean_object* v___x_2425_; 
v_sz_2419_ = lean_array_size(v_a_2413_);
v___x_2420_ = ((size_t)0ULL);
lean_inc(v_a_2413_);
v___x_2421_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_induction_spec__1(v_sz_2419_, v___x_2420_, v_a_2413_);
lean_inc(v_majorFVarId_2373_);
v___x_2422_ = lean_array_push(v___x_2421_, v_majorFVarId_2373_);
v___x_2423_ = 1;
v___x_2424_ = 0;
v___x_2425_ = l_Lean_MVarId_revert(v_mvarId_2372_, v___x_2422_, v___x_2423_, v___x_2424_, v___y_2415_, v___y_2416_, v___y_2417_, v___y_2418_);
if (lean_obj_tag(v___x_2425_) == 0)
{
lean_object* v_a_2426_; lean_object* v_fst_2427_; lean_object* v_snd_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; 
v_a_2426_ = lean_ctor_get(v___x_2425_, 0);
lean_inc(v_a_2426_);
lean_dec_ref_known(v___x_2425_, 1);
v_fst_2427_ = lean_ctor_get(v_a_2426_, 0);
lean_inc(v_fst_2427_);
v_snd_2428_ = lean_ctor_get(v_a_2426_, 1);
lean_inc(v_snd_2428_);
lean_dec(v_a_2426_);
v___x_2429_ = lean_array_get_size(v_a_2413_);
v___x_2430_ = lean_box(0);
v___x_2431_ = l_Lean_Meta_introNCore(v_snd_2428_, v___x_2429_, v___x_2430_, v___x_2424_, v___x_2423_, v___y_2415_, v___y_2416_, v___y_2417_, v___y_2418_);
if (lean_obj_tag(v___x_2431_) == 0)
{
lean_object* v_a_2432_; lean_object* v_fst_2433_; lean_object* v_snd_2434_; lean_object* v___x_2435_; 
v_a_2432_ = lean_ctor_get(v___x_2431_, 0);
lean_inc(v_a_2432_);
lean_dec_ref_known(v___x_2431_, 1);
v_fst_2433_ = lean_ctor_get(v_a_2432_, 0);
lean_inc(v_fst_2433_);
v_snd_2434_ = lean_ctor_get(v_a_2432_, 1);
lean_inc(v_snd_2434_);
lean_dec(v_a_2432_);
v___x_2435_ = l_Lean_Meta_intro1Core(v_snd_2434_, v___x_2423_, v___y_2415_, v___y_2416_, v___y_2417_, v___y_2418_);
if (lean_obj_tag(v___x_2435_) == 0)
{
lean_object* v_a_2436_; lean_object* v_fst_2437_; lean_object* v_snd_2438_; lean_object* v___x_2440_; uint8_t v_isShared_2441_; uint8_t v_isSharedCheck_2477_; 
v_a_2436_ = lean_ctor_get(v___x_2435_, 0);
lean_inc(v_a_2436_);
lean_dec_ref_known(v___x_2435_, 1);
v_fst_2437_ = lean_ctor_get(v_a_2436_, 0);
v_snd_2438_ = lean_ctor_get(v_a_2436_, 1);
v_isSharedCheck_2477_ = !lean_is_exclusive(v_a_2436_);
if (v_isSharedCheck_2477_ == 0)
{
v___x_2440_ = v_a_2436_;
v_isShared_2441_ = v_isSharedCheck_2477_;
goto v_resetjp_2439_;
}
else
{
lean_inc(v_snd_2438_);
lean_inc(v_fst_2437_);
lean_dec(v_a_2436_);
v___x_2440_ = lean_box(0);
v_isShared_2441_ = v_isSharedCheck_2477_;
goto v_resetjp_2439_;
}
v_resetjp_2439_:
{
lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2447_; 
v___x_2442_ = lean_box(0);
lean_inc(v_fst_2437_);
v___x_2443_ = l_Lean_mkFVar(v_fst_2437_);
lean_inc_ref(v___x_2443_);
v___x_2444_ = l_Lean_Meta_FVarSubst_insert(v___x_2442_, v_majorFVarId_2373_, v___x_2443_);
v___x_2445_ = lean_unsigned_to_nat(0u);
if (v_isShared_2441_ == 0)
{
lean_ctor_set(v___x_2440_, 1, v___x_2445_);
lean_ctor_set(v___x_2440_, 0, v___x_2444_);
v___x_2447_ = v___x_2440_;
goto v_reusejp_2446_;
}
else
{
lean_object* v_reuseFailAlloc_2476_; 
v_reuseFailAlloc_2476_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2476_, 0, v___x_2444_);
lean_ctor_set(v_reuseFailAlloc_2476_, 1, v___x_2445_);
v___x_2447_ = v_reuseFailAlloc_2476_;
goto v_reusejp_2446_;
}
v_reusejp_2446_:
{
lean_object* v___x_2448_; lean_object* v_toCold_2449_; lean_object* v_options_2450_; uint8_t v_hasTrace_2451_; 
v___x_2448_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_induction_spec__2(v_fst_2433_, v_a_2413_, v_sz_2419_, v___x_2420_, v___x_2447_);
lean_dec(v_a_2413_);
v_toCold_2449_ = lean_ctor_get(v___y_2417_, 0);
v_options_2450_ = lean_ctor_get(v_toCold_2449_, 2);
v_hasTrace_2451_ = lean_ctor_get_uint8(v_options_2450_, sizeof(void*)*1);
if (v_hasTrace_2451_ == 0)
{
lean_object* v_fst_2452_; 
v_fst_2452_ = lean_ctor_get(v___x_2448_, 0);
lean_inc(v_fst_2452_);
lean_dec_ref(v___x_2448_);
lean_inc(v_snd_2438_);
v___y_2394_ = v___x_2443_;
v___y_2395_ = v_fst_2427_;
v___y_2396_ = v_fst_2437_;
v___y_2397_ = v_fst_2452_;
v___y_2398_ = v_snd_2438_;
v___y_2399_ = v___x_2420_;
v___y_2400_ = v_fst_2433_;
v___y_2401_ = v_snd_2438_;
v___y_2402_ = v___y_2415_;
v___y_2403_ = v___y_2416_;
v___y_2404_ = v___y_2417_;
v___y_2405_ = v___y_2418_;
goto v___jp_2393_;
}
else
{
lean_object* v_fst_2453_; lean_object* v___x_2455_; uint8_t v_isShared_2456_; uint8_t v_isSharedCheck_2474_; 
v_fst_2453_ = lean_ctor_get(v___x_2448_, 0);
v_isSharedCheck_2474_ = !lean_is_exclusive(v___x_2448_);
if (v_isSharedCheck_2474_ == 0)
{
lean_object* v_unused_2475_; 
v_unused_2475_ = lean_ctor_get(v___x_2448_, 1);
lean_dec(v_unused_2475_);
v___x_2455_ = v___x_2448_;
v_isShared_2456_ = v_isSharedCheck_2474_;
goto v_resetjp_2454_;
}
else
{
lean_inc(v_fst_2453_);
lean_dec(v___x_2448_);
v___x_2455_ = lean_box(0);
v_isShared_2456_ = v_isSharedCheck_2474_;
goto v_resetjp_2454_;
}
v_resetjp_2454_:
{
lean_object* v_inheritedTraceOptions_2457_; lean_object* v___x_2458_; uint8_t v___x_2459_; 
v_inheritedTraceOptions_2457_ = lean_ctor_get(v_toCold_2449_, 11);
v___x_2458_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5);
v___x_2459_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2457_, v_options_2450_, v___x_2458_);
if (v___x_2459_ == 0)
{
lean_del_object(v___x_2455_);
lean_inc(v_snd_2438_);
v___y_2394_ = v___x_2443_;
v___y_2395_ = v_fst_2427_;
v___y_2396_ = v_fst_2437_;
v___y_2397_ = v_fst_2453_;
v___y_2398_ = v_snd_2438_;
v___y_2399_ = v___x_2420_;
v___y_2400_ = v_fst_2433_;
v___y_2401_ = v_snd_2438_;
v___y_2402_ = v___y_2415_;
v___y_2403_ = v___y_2416_;
v___y_2404_ = v___y_2417_;
v___y_2405_ = v___y_2418_;
goto v___jp_2393_;
}
else
{
lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2463_; 
v___x_2460_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__1);
lean_inc(v_snd_2438_);
v___x_2461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2461_, 0, v_snd_2438_);
if (v_isShared_2456_ == 0)
{
lean_ctor_set_tag(v___x_2455_, 7);
lean_ctor_set(v___x_2455_, 1, v___x_2461_);
lean_ctor_set(v___x_2455_, 0, v___x_2460_);
v___x_2463_ = v___x_2455_;
goto v_reusejp_2462_;
}
else
{
lean_object* v_reuseFailAlloc_2473_; 
v_reuseFailAlloc_2473_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2473_, 0, v___x_2460_);
lean_ctor_set(v_reuseFailAlloc_2473_, 1, v___x_2461_);
v___x_2463_ = v_reuseFailAlloc_2473_;
goto v_reusejp_2462_;
}
v_reusejp_2462_:
{
lean_object* v___x_2464_; 
v___x_2464_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1(v_cls_2410_, v___x_2463_, v___y_2415_, v___y_2416_, v___y_2417_, v___y_2418_);
if (lean_obj_tag(v___x_2464_) == 0)
{
lean_dec_ref_known(v___x_2464_, 1);
lean_inc(v_snd_2438_);
v___y_2394_ = v___x_2443_;
v___y_2395_ = v_fst_2427_;
v___y_2396_ = v_fst_2437_;
v___y_2397_ = v_fst_2453_;
v___y_2398_ = v_snd_2438_;
v___y_2399_ = v___x_2420_;
v___y_2400_ = v_fst_2433_;
v___y_2401_ = v_snd_2438_;
v___y_2402_ = v___y_2415_;
v___y_2403_ = v___y_2416_;
v___y_2404_ = v___y_2417_;
v___y_2405_ = v___y_2418_;
goto v___jp_2393_;
}
else
{
lean_object* v_a_2465_; lean_object* v___x_2467_; uint8_t v_isShared_2468_; uint8_t v_isSharedCheck_2472_; 
lean_dec(v_fst_2453_);
lean_dec_ref(v___x_2443_);
lean_dec(v_snd_2438_);
lean_dec(v_fst_2437_);
lean_dec(v_fst_2433_);
lean_dec(v_fst_2427_);
lean_dec_ref(v_givenNames_2374_);
lean_dec_ref(v_a_2370_);
v_a_2465_ = lean_ctor_get(v___x_2464_, 0);
v_isSharedCheck_2472_ = !lean_is_exclusive(v___x_2464_);
if (v_isSharedCheck_2472_ == 0)
{
v___x_2467_ = v___x_2464_;
v_isShared_2468_ = v_isSharedCheck_2472_;
goto v_resetjp_2466_;
}
else
{
lean_inc(v_a_2465_);
lean_dec(v___x_2464_);
v___x_2467_ = lean_box(0);
v_isShared_2468_ = v_isSharedCheck_2472_;
goto v_resetjp_2466_;
}
v_resetjp_2466_:
{
lean_object* v___x_2470_; 
if (v_isShared_2468_ == 0)
{
v___x_2470_ = v___x_2467_;
goto v_reusejp_2469_;
}
else
{
lean_object* v_reuseFailAlloc_2471_; 
v_reuseFailAlloc_2471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2471_, 0, v_a_2465_);
v___x_2470_ = v_reuseFailAlloc_2471_;
goto v_reusejp_2469_;
}
v_reusejp_2469_:
{
return v___x_2470_;
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
lean_object* v_a_2478_; lean_object* v___x_2480_; uint8_t v_isShared_2481_; uint8_t v_isSharedCheck_2485_; 
lean_dec(v_fst_2433_);
lean_dec(v_fst_2427_);
lean_dec(v_a_2413_);
lean_dec_ref(v_givenNames_2374_);
lean_dec(v_majorFVarId_2373_);
lean_dec_ref(v_a_2370_);
v_a_2478_ = lean_ctor_get(v___x_2435_, 0);
v_isSharedCheck_2485_ = !lean_is_exclusive(v___x_2435_);
if (v_isSharedCheck_2485_ == 0)
{
v___x_2480_ = v___x_2435_;
v_isShared_2481_ = v_isSharedCheck_2485_;
goto v_resetjp_2479_;
}
else
{
lean_inc(v_a_2478_);
lean_dec(v___x_2435_);
v___x_2480_ = lean_box(0);
v_isShared_2481_ = v_isSharedCheck_2485_;
goto v_resetjp_2479_;
}
v_resetjp_2479_:
{
lean_object* v___x_2483_; 
if (v_isShared_2481_ == 0)
{
v___x_2483_ = v___x_2480_;
goto v_reusejp_2482_;
}
else
{
lean_object* v_reuseFailAlloc_2484_; 
v_reuseFailAlloc_2484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2484_, 0, v_a_2478_);
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
lean_dec(v_fst_2427_);
lean_dec(v_a_2413_);
lean_dec_ref(v_givenNames_2374_);
lean_dec(v_majorFVarId_2373_);
lean_dec_ref(v_a_2370_);
v_a_2486_ = lean_ctor_get(v___x_2431_, 0);
v_isSharedCheck_2493_ = !lean_is_exclusive(v___x_2431_);
if (v_isSharedCheck_2493_ == 0)
{
v___x_2488_ = v___x_2431_;
v_isShared_2489_ = v_isSharedCheck_2493_;
goto v_resetjp_2487_;
}
else
{
lean_inc(v_a_2486_);
lean_dec(v___x_2431_);
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
lean_object* v_a_2494_; lean_object* v___x_2496_; uint8_t v_isShared_2497_; uint8_t v_isSharedCheck_2501_; 
lean_dec(v_a_2413_);
lean_dec_ref(v_givenNames_2374_);
lean_dec(v_majorFVarId_2373_);
lean_dec_ref(v_a_2370_);
v_a_2494_ = lean_ctor_get(v___x_2425_, 0);
v_isSharedCheck_2501_ = !lean_is_exclusive(v___x_2425_);
if (v_isSharedCheck_2501_ == 0)
{
v___x_2496_ = v___x_2425_;
v_isShared_2497_ = v_isSharedCheck_2501_;
goto v_resetjp_2495_;
}
else
{
lean_inc(v_a_2494_);
lean_dec(v___x_2425_);
v___x_2496_ = lean_box(0);
v_isShared_2497_ = v_isSharedCheck_2501_;
goto v_resetjp_2495_;
}
v_resetjp_2495_:
{
lean_object* v___x_2499_; 
if (v_isShared_2497_ == 0)
{
v___x_2499_ = v___x_2496_;
goto v_reusejp_2498_;
}
else
{
lean_object* v_reuseFailAlloc_2500_; 
v_reuseFailAlloc_2500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2500_, 0, v_a_2494_);
v___x_2499_ = v_reuseFailAlloc_2500_;
goto v_reusejp_2498_;
}
v_reusejp_2498_:
{
return v___x_2499_;
}
}
}
}
}
else
{
lean_object* v_a_2536_; lean_object* v___x_2538_; uint8_t v_isShared_2539_; uint8_t v_isSharedCheck_2543_; 
lean_dec(v_recursorName_2375_);
lean_dec_ref(v_givenNames_2374_);
lean_dec(v_majorFVarId_2373_);
lean_dec(v_mvarId_2372_);
lean_dec_ref(v_a_2370_);
v_a_2536_ = lean_ctor_get(v___x_2412_, 0);
v_isSharedCheck_2543_ = !lean_is_exclusive(v___x_2412_);
if (v_isSharedCheck_2543_ == 0)
{
v___x_2538_ = v___x_2412_;
v_isShared_2539_ = v_isSharedCheck_2543_;
goto v_resetjp_2537_;
}
else
{
lean_inc(v_a_2536_);
lean_dec(v___x_2412_);
v___x_2538_ = lean_box(0);
v_isShared_2539_ = v_isSharedCheck_2543_;
goto v_resetjp_2537_;
}
v_resetjp_2537_:
{
lean_object* v___x_2541_; 
if (v_isShared_2539_ == 0)
{
v___x_2541_ = v___x_2538_;
goto v_reusejp_2540_;
}
else
{
lean_object* v_reuseFailAlloc_2542_; 
v_reuseFailAlloc_2542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2542_, 0, v_a_2536_);
v___x_2541_ = v_reuseFailAlloc_2542_;
goto v_reusejp_2540_;
}
v_reusejp_2540_:
{
return v___x_2541_;
}
}
}
}
else
{
lean_object* v_a_2544_; lean_object* v___x_2546_; uint8_t v_isShared_2547_; uint8_t v_isSharedCheck_2551_; 
lean_dec(v_recursorName_2375_);
lean_dec_ref(v_givenNames_2374_);
lean_dec(v_majorFVarId_2373_);
lean_dec(v_mvarId_2372_);
lean_dec_ref(v_val_2371_);
lean_dec_ref(v_a_2370_);
v_a_2544_ = lean_ctor_get(v___x_2411_, 0);
v_isSharedCheck_2551_ = !lean_is_exclusive(v___x_2411_);
if (v_isSharedCheck_2551_ == 0)
{
v___x_2546_ = v___x_2411_;
v_isShared_2547_ = v_isSharedCheck_2551_;
goto v_resetjp_2545_;
}
else
{
lean_inc(v_a_2544_);
lean_dec(v___x_2411_);
v___x_2546_ = lean_box(0);
v_isShared_2547_ = v_isSharedCheck_2551_;
goto v_resetjp_2545_;
}
v_resetjp_2545_:
{
lean_object* v___x_2549_; 
if (v_isShared_2547_ == 0)
{
v___x_2549_ = v___x_2546_;
goto v_reusejp_2548_;
}
else
{
lean_object* v_reuseFailAlloc_2550_; 
v_reuseFailAlloc_2550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2550_, 0, v_a_2544_);
v___x_2549_ = v_reuseFailAlloc_2550_;
goto v_reusejp_2548_;
}
v_reusejp_2548_:
{
return v___x_2549_;
}
}
}
v___jp_2393_:
{
size_t v_sz_2406_; lean_object* v___x_2407_; lean_object* v___f_2408_; lean_object* v___x_2409_; 
v_sz_2406_ = lean_array_size(v___y_2400_);
v___x_2407_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__3(v_sz_2406_, v___y_2399_, v___y_2400_);
v___f_2408_ = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4___lam__0___boxed), 14, 9);
lean_closure_set(v___f_2408_, 0, v___y_2398_);
lean_closure_set(v___f_2408_, 1, v___x_2392_);
lean_closure_set(v___f_2408_, 2, v___y_2396_);
lean_closure_set(v___f_2408_, 3, v_a_2370_);
lean_closure_set(v___f_2408_, 4, v___x_2407_);
lean_closure_set(v___f_2408_, 5, v_givenNames_2374_);
lean_closure_set(v___f_2408_, 6, v___y_2395_);
lean_closure_set(v___f_2408_, 7, v___y_2394_);
lean_closure_set(v___f_2408_, 8, v___y_2397_);
v___x_2409_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___redArg(v___y_2401_, v___f_2408_, v___y_2402_, v___y_2403_, v___y_2404_, v___y_2405_);
return v___x_2409_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___boxed(lean_object* v_a_2552_, lean_object* v_val_2553_, lean_object* v_mvarId_2554_, lean_object* v_majorFVarId_2555_, lean_object* v_givenNames_2556_, lean_object* v_recursorName_2557_, lean_object* v_x_2558_, lean_object* v_x_2559_, lean_object* v_x_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_){
_start:
{
lean_object* v_res_2566_; 
v_res_2566_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4(v_a_2552_, v_val_2553_, v_mvarId_2554_, v_majorFVarId_2555_, v_givenNames_2556_, v_recursorName_2557_, v_x_2558_, v_x_2559_, v_x_2560_, v___y_2561_, v___y_2562_, v___y_2563_, v___y_2564_);
lean_dec(v___y_2564_);
lean_dec_ref(v___y_2563_);
lean_dec(v___y_2562_);
lean_dec_ref(v___y_2561_);
return v_res_2566_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4(lean_object* v_val_2567_, lean_object* v_mvarId_2568_, lean_object* v_a_2569_, lean_object* v_majorFVarId_2570_, lean_object* v_givenNames_2571_, lean_object* v_recursorName_2572_, lean_object* v_x_2573_, lean_object* v_x_2574_, lean_object* v_x_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_){
_start:
{
if (lean_obj_tag(v_x_2573_) == 5)
{
lean_object* v_fn_2581_; lean_object* v_arg_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; 
v_fn_2581_ = lean_ctor_get(v_x_2573_, 0);
lean_inc_ref(v_fn_2581_);
v_arg_2582_ = lean_ctor_get(v_x_2573_, 1);
lean_inc_ref(v_arg_2582_);
lean_dec_ref_known(v_x_2573_, 2);
v___x_2583_ = lean_array_set(v_x_2574_, v_x_2575_, v_arg_2582_);
v___x_2584_ = lean_unsigned_to_nat(1u);
v___x_2585_ = lean_nat_sub(v_x_2575_, v___x_2584_);
v___x_2586_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4(v_a_2569_, v_val_2567_, v_mvarId_2568_, v_majorFVarId_2570_, v_givenNames_2571_, v_recursorName_2572_, v_fn_2581_, v___x_2583_, v___x_2585_, v___y_2576_, v___y_2577_, v___y_2578_, v___y_2579_);
return v___x_2586_;
}
else
{
uint8_t v_depElim_2587_; lean_object* v_paramsPos_2588_; lean_object* v___x_2589_; lean_object* v___y_2591_; lean_object* v___y_2592_; lean_object* v___y_2593_; lean_object* v___y_2594_; lean_object* v___y_2595_; lean_object* v___y_2596_; size_t v___y_2597_; lean_object* v___y_2598_; lean_object* v___y_2599_; lean_object* v___y_2600_; lean_object* v___y_2601_; lean_object* v___y_2602_; lean_object* v_cls_2607_; lean_object* v___x_2608_; 
lean_dec_ref(v_x_2573_);
v_depElim_2587_ = lean_ctor_get_uint8(v_a_2569_, sizeof(void*)*8);
v_paramsPos_2588_ = lean_ctor_get(v_a_2569_, 5);
v___x_2589_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1));
v_cls_2607_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__2));
lean_inc(v_paramsPos_2588_);
lean_inc(v_mvarId_2568_);
lean_inc_ref(v_val_2567_);
v___x_2608_ = l_List_forM___at___00Lean_MVarId_induction_spec__0(v_x_2574_, v_val_2567_, v_mvarId_2568_, v_paramsPos_2588_, v___y_2576_, v___y_2577_, v___y_2578_, v___y_2579_);
lean_dec_ref(v_x_2574_);
if (lean_obj_tag(v___x_2608_) == 0)
{
lean_object* v___x_2609_; 
lean_dec_ref_known(v___x_2608_, 1);
lean_inc_ref(v_a_2569_);
lean_inc(v_mvarId_2568_);
v___x_2609_ = l_Lean_Meta_getMajorTypeIndices(v_mvarId_2568_, v___x_2589_, v_a_2569_, v_val_2567_, v___y_2576_, v___y_2577_, v___y_2578_, v___y_2579_);
if (lean_obj_tag(v___x_2609_) == 0)
{
lean_object* v_a_2610_; lean_object* v___y_2612_; lean_object* v___y_2613_; lean_object* v___y_2614_; lean_object* v___y_2615_; lean_object* v___x_2699_; 
v_a_2610_ = lean_ctor_get(v___x_2609_, 0);
lean_inc(v_a_2610_);
lean_dec_ref_known(v___x_2609_, 1);
lean_inc(v_mvarId_2568_);
v___x_2699_ = l_Lean_MVarId_getType(v_mvarId_2568_, v___y_2576_, v___y_2577_, v___y_2578_, v___y_2579_);
if (lean_obj_tag(v___x_2699_) == 0)
{
if (v_depElim_2587_ == 0)
{
lean_object* v_a_2700_; lean_object* v___x_2701_; lean_object* v_a_2702_; lean_object* v___x_2704_; uint8_t v_isShared_2705_; uint8_t v_isSharedCheck_2724_; 
v_a_2700_ = lean_ctor_get(v___x_2699_, 0);
lean_inc(v_a_2700_);
lean_dec_ref_known(v___x_2699_, 1);
lean_inc(v_majorFVarId_2570_);
v___x_2701_ = l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2___redArg(v_a_2700_, v_majorFVarId_2570_, v___y_2577_);
v_a_2702_ = lean_ctor_get(v___x_2701_, 0);
v_isSharedCheck_2724_ = !lean_is_exclusive(v___x_2701_);
if (v_isSharedCheck_2724_ == 0)
{
v___x_2704_ = v___x_2701_;
v_isShared_2705_ = v_isSharedCheck_2724_;
goto v_resetjp_2703_;
}
else
{
lean_inc(v_a_2702_);
lean_dec(v___x_2701_);
v___x_2704_ = lean_box(0);
v_isShared_2705_ = v_isSharedCheck_2724_;
goto v_resetjp_2703_;
}
v_resetjp_2703_:
{
uint8_t v___x_2706_; 
v___x_2706_ = lean_unbox(v_a_2702_);
lean_dec(v_a_2702_);
if (v___x_2706_ == 0)
{
lean_del_object(v___x_2704_);
lean_dec(v_recursorName_2572_);
v___y_2612_ = v___y_2576_;
v___y_2613_ = v___y_2577_;
v___y_2614_ = v___y_2578_;
v___y_2615_ = v___y_2579_;
goto v___jp_2611_;
}
else
{
lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2713_; 
v___x_2707_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__3, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__3);
v___x_2708_ = l_Lean_MessageData_ofName(v_recursorName_2572_);
v___x_2709_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2709_, 0, v___x_2707_);
lean_ctor_set(v___x_2709_, 1, v___x_2708_);
v___x_2710_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__5, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__5_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__5);
v___x_2711_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2711_, 0, v___x_2709_);
lean_ctor_set(v___x_2711_, 1, v___x_2710_);
if (v_isShared_2705_ == 0)
{
lean_ctor_set_tag(v___x_2704_, 1);
lean_ctor_set(v___x_2704_, 0, v___x_2711_);
v___x_2713_ = v___x_2704_;
goto v_reusejp_2712_;
}
else
{
lean_object* v_reuseFailAlloc_2723_; 
v_reuseFailAlloc_2723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2723_, 0, v___x_2711_);
v___x_2713_ = v_reuseFailAlloc_2723_;
goto v_reusejp_2712_;
}
v_reusejp_2712_:
{
lean_object* v___x_2714_; 
lean_inc(v_mvarId_2568_);
v___x_2714_ = l_Lean_Meta_throwTacticEx___redArg(v___x_2589_, v_mvarId_2568_, v___x_2713_, v___y_2576_, v___y_2577_, v___y_2578_, v___y_2579_);
if (lean_obj_tag(v___x_2714_) == 0)
{
lean_dec_ref_known(v___x_2714_, 1);
v___y_2612_ = v___y_2576_;
v___y_2613_ = v___y_2577_;
v___y_2614_ = v___y_2578_;
v___y_2615_ = v___y_2579_;
goto v___jp_2611_;
}
else
{
lean_object* v_a_2715_; lean_object* v___x_2717_; uint8_t v_isShared_2718_; uint8_t v_isSharedCheck_2722_; 
lean_dec(v_a_2610_);
lean_dec_ref(v_givenNames_2571_);
lean_dec(v_majorFVarId_2570_);
lean_dec_ref(v_a_2569_);
lean_dec(v_mvarId_2568_);
v_a_2715_ = lean_ctor_get(v___x_2714_, 0);
v_isSharedCheck_2722_ = !lean_is_exclusive(v___x_2714_);
if (v_isSharedCheck_2722_ == 0)
{
v___x_2717_ = v___x_2714_;
v_isShared_2718_ = v_isSharedCheck_2722_;
goto v_resetjp_2716_;
}
else
{
lean_inc(v_a_2715_);
lean_dec(v___x_2714_);
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
}
}
else
{
lean_dec_ref_known(v___x_2699_, 1);
lean_dec(v_recursorName_2572_);
v___y_2612_ = v___y_2576_;
v___y_2613_ = v___y_2577_;
v___y_2614_ = v___y_2578_;
v___y_2615_ = v___y_2579_;
goto v___jp_2611_;
}
}
else
{
lean_object* v_a_2725_; lean_object* v___x_2727_; uint8_t v_isShared_2728_; uint8_t v_isSharedCheck_2732_; 
lean_dec(v_a_2610_);
lean_dec(v_recursorName_2572_);
lean_dec_ref(v_givenNames_2571_);
lean_dec(v_majorFVarId_2570_);
lean_dec_ref(v_a_2569_);
lean_dec(v_mvarId_2568_);
v_a_2725_ = lean_ctor_get(v___x_2699_, 0);
v_isSharedCheck_2732_ = !lean_is_exclusive(v___x_2699_);
if (v_isSharedCheck_2732_ == 0)
{
v___x_2727_ = v___x_2699_;
v_isShared_2728_ = v_isSharedCheck_2732_;
goto v_resetjp_2726_;
}
else
{
lean_inc(v_a_2725_);
lean_dec(v___x_2699_);
v___x_2727_ = lean_box(0);
v_isShared_2728_ = v_isSharedCheck_2732_;
goto v_resetjp_2726_;
}
v_resetjp_2726_:
{
lean_object* v___x_2730_; 
if (v_isShared_2728_ == 0)
{
v___x_2730_ = v___x_2727_;
goto v_reusejp_2729_;
}
else
{
lean_object* v_reuseFailAlloc_2731_; 
v_reuseFailAlloc_2731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2731_, 0, v_a_2725_);
v___x_2730_ = v_reuseFailAlloc_2731_;
goto v_reusejp_2729_;
}
v_reusejp_2729_:
{
return v___x_2730_;
}
}
}
v___jp_2611_:
{
size_t v_sz_2616_; size_t v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; uint8_t v___x_2620_; uint8_t v___x_2621_; lean_object* v___x_2622_; 
v_sz_2616_ = lean_array_size(v_a_2610_);
v___x_2617_ = ((size_t)0ULL);
lean_inc(v_a_2610_);
v___x_2618_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_induction_spec__1(v_sz_2616_, v___x_2617_, v_a_2610_);
lean_inc(v_majorFVarId_2570_);
v___x_2619_ = lean_array_push(v___x_2618_, v_majorFVarId_2570_);
v___x_2620_ = 1;
v___x_2621_ = 0;
v___x_2622_ = l_Lean_MVarId_revert(v_mvarId_2568_, v___x_2619_, v___x_2620_, v___x_2621_, v___y_2612_, v___y_2613_, v___y_2614_, v___y_2615_);
if (lean_obj_tag(v___x_2622_) == 0)
{
lean_object* v_a_2623_; lean_object* v_fst_2624_; lean_object* v_snd_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; 
v_a_2623_ = lean_ctor_get(v___x_2622_, 0);
lean_inc(v_a_2623_);
lean_dec_ref_known(v___x_2622_, 1);
v_fst_2624_ = lean_ctor_get(v_a_2623_, 0);
lean_inc(v_fst_2624_);
v_snd_2625_ = lean_ctor_get(v_a_2623_, 1);
lean_inc(v_snd_2625_);
lean_dec(v_a_2623_);
v___x_2626_ = lean_array_get_size(v_a_2610_);
v___x_2627_ = lean_box(0);
v___x_2628_ = l_Lean_Meta_introNCore(v_snd_2625_, v___x_2626_, v___x_2627_, v___x_2621_, v___x_2620_, v___y_2612_, v___y_2613_, v___y_2614_, v___y_2615_);
if (lean_obj_tag(v___x_2628_) == 0)
{
lean_object* v_a_2629_; lean_object* v_fst_2630_; lean_object* v_snd_2631_; lean_object* v___x_2632_; 
v_a_2629_ = lean_ctor_get(v___x_2628_, 0);
lean_inc(v_a_2629_);
lean_dec_ref_known(v___x_2628_, 1);
v_fst_2630_ = lean_ctor_get(v_a_2629_, 0);
lean_inc(v_fst_2630_);
v_snd_2631_ = lean_ctor_get(v_a_2629_, 1);
lean_inc(v_snd_2631_);
lean_dec(v_a_2629_);
v___x_2632_ = l_Lean_Meta_intro1Core(v_snd_2631_, v___x_2620_, v___y_2612_, v___y_2613_, v___y_2614_, v___y_2615_);
if (lean_obj_tag(v___x_2632_) == 0)
{
lean_object* v_a_2633_; lean_object* v_fst_2634_; lean_object* v_snd_2635_; lean_object* v___x_2637_; uint8_t v_isShared_2638_; uint8_t v_isSharedCheck_2674_; 
v_a_2633_ = lean_ctor_get(v___x_2632_, 0);
lean_inc(v_a_2633_);
lean_dec_ref_known(v___x_2632_, 1);
v_fst_2634_ = lean_ctor_get(v_a_2633_, 0);
v_snd_2635_ = lean_ctor_get(v_a_2633_, 1);
v_isSharedCheck_2674_ = !lean_is_exclusive(v_a_2633_);
if (v_isSharedCheck_2674_ == 0)
{
v___x_2637_ = v_a_2633_;
v_isShared_2638_ = v_isSharedCheck_2674_;
goto v_resetjp_2636_;
}
else
{
lean_inc(v_snd_2635_);
lean_inc(v_fst_2634_);
lean_dec(v_a_2633_);
v___x_2637_ = lean_box(0);
v_isShared_2638_ = v_isSharedCheck_2674_;
goto v_resetjp_2636_;
}
v_resetjp_2636_:
{
lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2644_; 
v___x_2639_ = lean_box(0);
lean_inc(v_fst_2634_);
v___x_2640_ = l_Lean_mkFVar(v_fst_2634_);
lean_inc_ref(v___x_2640_);
v___x_2641_ = l_Lean_Meta_FVarSubst_insert(v___x_2639_, v_majorFVarId_2570_, v___x_2640_);
v___x_2642_ = lean_unsigned_to_nat(0u);
if (v_isShared_2638_ == 0)
{
lean_ctor_set(v___x_2637_, 1, v___x_2642_);
lean_ctor_set(v___x_2637_, 0, v___x_2641_);
v___x_2644_ = v___x_2637_;
goto v_reusejp_2643_;
}
else
{
lean_object* v_reuseFailAlloc_2673_; 
v_reuseFailAlloc_2673_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2673_, 0, v___x_2641_);
lean_ctor_set(v_reuseFailAlloc_2673_, 1, v___x_2642_);
v___x_2644_ = v_reuseFailAlloc_2673_;
goto v_reusejp_2643_;
}
v_reusejp_2643_:
{
lean_object* v___x_2645_; lean_object* v_toCold_2646_; lean_object* v_options_2647_; uint8_t v_hasTrace_2648_; 
v___x_2645_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_induction_spec__2(v_fst_2630_, v_a_2610_, v_sz_2616_, v___x_2617_, v___x_2644_);
lean_dec(v_a_2610_);
v_toCold_2646_ = lean_ctor_get(v___y_2614_, 0);
v_options_2647_ = lean_ctor_get(v_toCold_2646_, 2);
v_hasTrace_2648_ = lean_ctor_get_uint8(v_options_2647_, sizeof(void*)*1);
if (v_hasTrace_2648_ == 0)
{
lean_object* v_fst_2649_; 
v_fst_2649_ = lean_ctor_get(v___x_2645_, 0);
lean_inc(v_fst_2649_);
lean_dec_ref(v___x_2645_);
lean_inc(v_snd_2635_);
v___y_2591_ = v_fst_2649_;
v___y_2592_ = v_snd_2635_;
v___y_2593_ = v_fst_2634_;
v___y_2594_ = v___x_2640_;
v___y_2595_ = v_fst_2624_;
v___y_2596_ = v_snd_2635_;
v___y_2597_ = v___x_2617_;
v___y_2598_ = v_fst_2630_;
v___y_2599_ = v___y_2612_;
v___y_2600_ = v___y_2613_;
v___y_2601_ = v___y_2614_;
v___y_2602_ = v___y_2615_;
goto v___jp_2590_;
}
else
{
lean_object* v_fst_2650_; lean_object* v___x_2652_; uint8_t v_isShared_2653_; uint8_t v_isSharedCheck_2671_; 
v_fst_2650_ = lean_ctor_get(v___x_2645_, 0);
v_isSharedCheck_2671_ = !lean_is_exclusive(v___x_2645_);
if (v_isSharedCheck_2671_ == 0)
{
lean_object* v_unused_2672_; 
v_unused_2672_ = lean_ctor_get(v___x_2645_, 1);
lean_dec(v_unused_2672_);
v___x_2652_ = v___x_2645_;
v_isShared_2653_ = v_isSharedCheck_2671_;
goto v_resetjp_2651_;
}
else
{
lean_inc(v_fst_2650_);
lean_dec(v___x_2645_);
v___x_2652_ = lean_box(0);
v_isShared_2653_ = v_isSharedCheck_2671_;
goto v_resetjp_2651_;
}
v_resetjp_2651_:
{
lean_object* v_inheritedTraceOptions_2654_; lean_object* v___x_2655_; uint8_t v___x_2656_; 
v_inheritedTraceOptions_2654_ = lean_ctor_get(v_toCold_2646_, 11);
v___x_2655_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5);
v___x_2656_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2654_, v_options_2647_, v___x_2655_);
if (v___x_2656_ == 0)
{
lean_del_object(v___x_2652_);
lean_inc(v_snd_2635_);
v___y_2591_ = v_fst_2650_;
v___y_2592_ = v_snd_2635_;
v___y_2593_ = v_fst_2634_;
v___y_2594_ = v___x_2640_;
v___y_2595_ = v_fst_2624_;
v___y_2596_ = v_snd_2635_;
v___y_2597_ = v___x_2617_;
v___y_2598_ = v_fst_2630_;
v___y_2599_ = v___y_2612_;
v___y_2600_ = v___y_2613_;
v___y_2601_ = v___y_2614_;
v___y_2602_ = v___y_2615_;
goto v___jp_2590_;
}
else
{
lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2660_; 
v___x_2657_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__1);
lean_inc(v_snd_2635_);
v___x_2658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2658_, 0, v_snd_2635_);
if (v_isShared_2653_ == 0)
{
lean_ctor_set_tag(v___x_2652_, 7);
lean_ctor_set(v___x_2652_, 1, v___x_2658_);
lean_ctor_set(v___x_2652_, 0, v___x_2657_);
v___x_2660_ = v___x_2652_;
goto v_reusejp_2659_;
}
else
{
lean_object* v_reuseFailAlloc_2670_; 
v_reuseFailAlloc_2670_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2670_, 0, v___x_2657_);
lean_ctor_set(v_reuseFailAlloc_2670_, 1, v___x_2658_);
v___x_2660_ = v_reuseFailAlloc_2670_;
goto v_reusejp_2659_;
}
v_reusejp_2659_:
{
lean_object* v___x_2661_; 
v___x_2661_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1(v_cls_2607_, v___x_2660_, v___y_2612_, v___y_2613_, v___y_2614_, v___y_2615_);
if (lean_obj_tag(v___x_2661_) == 0)
{
lean_dec_ref_known(v___x_2661_, 1);
lean_inc(v_snd_2635_);
v___y_2591_ = v_fst_2650_;
v___y_2592_ = v_snd_2635_;
v___y_2593_ = v_fst_2634_;
v___y_2594_ = v___x_2640_;
v___y_2595_ = v_fst_2624_;
v___y_2596_ = v_snd_2635_;
v___y_2597_ = v___x_2617_;
v___y_2598_ = v_fst_2630_;
v___y_2599_ = v___y_2612_;
v___y_2600_ = v___y_2613_;
v___y_2601_ = v___y_2614_;
v___y_2602_ = v___y_2615_;
goto v___jp_2590_;
}
else
{
lean_object* v_a_2662_; lean_object* v___x_2664_; uint8_t v_isShared_2665_; uint8_t v_isSharedCheck_2669_; 
lean_dec(v_fst_2650_);
lean_dec_ref(v___x_2640_);
lean_dec(v_snd_2635_);
lean_dec(v_fst_2634_);
lean_dec(v_fst_2630_);
lean_dec(v_fst_2624_);
lean_dec_ref(v_givenNames_2571_);
lean_dec_ref(v_a_2569_);
v_a_2662_ = lean_ctor_get(v___x_2661_, 0);
v_isSharedCheck_2669_ = !lean_is_exclusive(v___x_2661_);
if (v_isSharedCheck_2669_ == 0)
{
v___x_2664_ = v___x_2661_;
v_isShared_2665_ = v_isSharedCheck_2669_;
goto v_resetjp_2663_;
}
else
{
lean_inc(v_a_2662_);
lean_dec(v___x_2661_);
v___x_2664_ = lean_box(0);
v_isShared_2665_ = v_isSharedCheck_2669_;
goto v_resetjp_2663_;
}
v_resetjp_2663_:
{
lean_object* v___x_2667_; 
if (v_isShared_2665_ == 0)
{
v___x_2667_ = v___x_2664_;
goto v_reusejp_2666_;
}
else
{
lean_object* v_reuseFailAlloc_2668_; 
v_reuseFailAlloc_2668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2668_, 0, v_a_2662_);
v___x_2667_ = v_reuseFailAlloc_2668_;
goto v_reusejp_2666_;
}
v_reusejp_2666_:
{
return v___x_2667_;
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
lean_object* v_a_2675_; lean_object* v___x_2677_; uint8_t v_isShared_2678_; uint8_t v_isSharedCheck_2682_; 
lean_dec(v_fst_2630_);
lean_dec(v_fst_2624_);
lean_dec(v_a_2610_);
lean_dec_ref(v_givenNames_2571_);
lean_dec(v_majorFVarId_2570_);
lean_dec_ref(v_a_2569_);
v_a_2675_ = lean_ctor_get(v___x_2632_, 0);
v_isSharedCheck_2682_ = !lean_is_exclusive(v___x_2632_);
if (v_isSharedCheck_2682_ == 0)
{
v___x_2677_ = v___x_2632_;
v_isShared_2678_ = v_isSharedCheck_2682_;
goto v_resetjp_2676_;
}
else
{
lean_inc(v_a_2675_);
lean_dec(v___x_2632_);
v___x_2677_ = lean_box(0);
v_isShared_2678_ = v_isSharedCheck_2682_;
goto v_resetjp_2676_;
}
v_resetjp_2676_:
{
lean_object* v___x_2680_; 
if (v_isShared_2678_ == 0)
{
v___x_2680_ = v___x_2677_;
goto v_reusejp_2679_;
}
else
{
lean_object* v_reuseFailAlloc_2681_; 
v_reuseFailAlloc_2681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2681_, 0, v_a_2675_);
v___x_2680_ = v_reuseFailAlloc_2681_;
goto v_reusejp_2679_;
}
v_reusejp_2679_:
{
return v___x_2680_;
}
}
}
}
else
{
lean_object* v_a_2683_; lean_object* v___x_2685_; uint8_t v_isShared_2686_; uint8_t v_isSharedCheck_2690_; 
lean_dec(v_fst_2624_);
lean_dec(v_a_2610_);
lean_dec_ref(v_givenNames_2571_);
lean_dec(v_majorFVarId_2570_);
lean_dec_ref(v_a_2569_);
v_a_2683_ = lean_ctor_get(v___x_2628_, 0);
v_isSharedCheck_2690_ = !lean_is_exclusive(v___x_2628_);
if (v_isSharedCheck_2690_ == 0)
{
v___x_2685_ = v___x_2628_;
v_isShared_2686_ = v_isSharedCheck_2690_;
goto v_resetjp_2684_;
}
else
{
lean_inc(v_a_2683_);
lean_dec(v___x_2628_);
v___x_2685_ = lean_box(0);
v_isShared_2686_ = v_isSharedCheck_2690_;
goto v_resetjp_2684_;
}
v_resetjp_2684_:
{
lean_object* v___x_2688_; 
if (v_isShared_2686_ == 0)
{
v___x_2688_ = v___x_2685_;
goto v_reusejp_2687_;
}
else
{
lean_object* v_reuseFailAlloc_2689_; 
v_reuseFailAlloc_2689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2689_, 0, v_a_2683_);
v___x_2688_ = v_reuseFailAlloc_2689_;
goto v_reusejp_2687_;
}
v_reusejp_2687_:
{
return v___x_2688_;
}
}
}
}
else
{
lean_object* v_a_2691_; lean_object* v___x_2693_; uint8_t v_isShared_2694_; uint8_t v_isSharedCheck_2698_; 
lean_dec(v_a_2610_);
lean_dec_ref(v_givenNames_2571_);
lean_dec(v_majorFVarId_2570_);
lean_dec_ref(v_a_2569_);
v_a_2691_ = lean_ctor_get(v___x_2622_, 0);
v_isSharedCheck_2698_ = !lean_is_exclusive(v___x_2622_);
if (v_isSharedCheck_2698_ == 0)
{
v___x_2693_ = v___x_2622_;
v_isShared_2694_ = v_isSharedCheck_2698_;
goto v_resetjp_2692_;
}
else
{
lean_inc(v_a_2691_);
lean_dec(v___x_2622_);
v___x_2693_ = lean_box(0);
v_isShared_2694_ = v_isSharedCheck_2698_;
goto v_resetjp_2692_;
}
v_resetjp_2692_:
{
lean_object* v___x_2696_; 
if (v_isShared_2694_ == 0)
{
v___x_2696_ = v___x_2693_;
goto v_reusejp_2695_;
}
else
{
lean_object* v_reuseFailAlloc_2697_; 
v_reuseFailAlloc_2697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2697_, 0, v_a_2691_);
v___x_2696_ = v_reuseFailAlloc_2697_;
goto v_reusejp_2695_;
}
v_reusejp_2695_:
{
return v___x_2696_;
}
}
}
}
}
else
{
lean_object* v_a_2733_; lean_object* v___x_2735_; uint8_t v_isShared_2736_; uint8_t v_isSharedCheck_2740_; 
lean_dec(v_recursorName_2572_);
lean_dec_ref(v_givenNames_2571_);
lean_dec(v_majorFVarId_2570_);
lean_dec_ref(v_a_2569_);
lean_dec(v_mvarId_2568_);
v_a_2733_ = lean_ctor_get(v___x_2609_, 0);
v_isSharedCheck_2740_ = !lean_is_exclusive(v___x_2609_);
if (v_isSharedCheck_2740_ == 0)
{
v___x_2735_ = v___x_2609_;
v_isShared_2736_ = v_isSharedCheck_2740_;
goto v_resetjp_2734_;
}
else
{
lean_inc(v_a_2733_);
lean_dec(v___x_2609_);
v___x_2735_ = lean_box(0);
v_isShared_2736_ = v_isSharedCheck_2740_;
goto v_resetjp_2734_;
}
v_resetjp_2734_:
{
lean_object* v___x_2738_; 
if (v_isShared_2736_ == 0)
{
v___x_2738_ = v___x_2735_;
goto v_reusejp_2737_;
}
else
{
lean_object* v_reuseFailAlloc_2739_; 
v_reuseFailAlloc_2739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2739_, 0, v_a_2733_);
v___x_2738_ = v_reuseFailAlloc_2739_;
goto v_reusejp_2737_;
}
v_reusejp_2737_:
{
return v___x_2738_;
}
}
}
}
else
{
lean_object* v_a_2741_; lean_object* v___x_2743_; uint8_t v_isShared_2744_; uint8_t v_isSharedCheck_2748_; 
lean_dec(v_recursorName_2572_);
lean_dec_ref(v_givenNames_2571_);
lean_dec(v_majorFVarId_2570_);
lean_dec_ref(v_a_2569_);
lean_dec(v_mvarId_2568_);
lean_dec_ref(v_val_2567_);
v_a_2741_ = lean_ctor_get(v___x_2608_, 0);
v_isSharedCheck_2748_ = !lean_is_exclusive(v___x_2608_);
if (v_isSharedCheck_2748_ == 0)
{
v___x_2743_ = v___x_2608_;
v_isShared_2744_ = v_isSharedCheck_2748_;
goto v_resetjp_2742_;
}
else
{
lean_inc(v_a_2741_);
lean_dec(v___x_2608_);
v___x_2743_ = lean_box(0);
v_isShared_2744_ = v_isSharedCheck_2748_;
goto v_resetjp_2742_;
}
v_resetjp_2742_:
{
lean_object* v___x_2746_; 
if (v_isShared_2744_ == 0)
{
v___x_2746_ = v___x_2743_;
goto v_reusejp_2745_;
}
else
{
lean_object* v_reuseFailAlloc_2747_; 
v_reuseFailAlloc_2747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2747_, 0, v_a_2741_);
v___x_2746_ = v_reuseFailAlloc_2747_;
goto v_reusejp_2745_;
}
v_reusejp_2745_:
{
return v___x_2746_;
}
}
}
v___jp_2590_:
{
size_t v_sz_2603_; lean_object* v___x_2604_; lean_object* v___f_2605_; lean_object* v___x_2606_; 
v_sz_2603_ = lean_array_size(v___y_2598_);
v___x_2604_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__3(v_sz_2603_, v___y_2597_, v___y_2598_);
v___f_2605_ = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4___lam__0___boxed), 14, 9);
lean_closure_set(v___f_2605_, 0, v___y_2592_);
lean_closure_set(v___f_2605_, 1, v___x_2589_);
lean_closure_set(v___f_2605_, 2, v___y_2593_);
lean_closure_set(v___f_2605_, 3, v_a_2569_);
lean_closure_set(v___f_2605_, 4, v___x_2604_);
lean_closure_set(v___f_2605_, 5, v_givenNames_2571_);
lean_closure_set(v___f_2605_, 6, v___y_2595_);
lean_closure_set(v___f_2605_, 7, v___y_2594_);
lean_closure_set(v___f_2605_, 8, v___y_2591_);
v___x_2606_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___redArg(v___y_2596_, v___f_2605_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_);
return v___x_2606_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4___boxed(lean_object* v_val_2749_, lean_object* v_mvarId_2750_, lean_object* v_a_2751_, lean_object* v_majorFVarId_2752_, lean_object* v_givenNames_2753_, lean_object* v_recursorName_2754_, lean_object* v_x_2755_, lean_object* v_x_2756_, lean_object* v_x_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_, lean_object* v___y_2762_){
_start:
{
lean_object* v_res_2763_; 
v_res_2763_ = l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4(v_val_2749_, v_mvarId_2750_, v_a_2751_, v_majorFVarId_2752_, v_givenNames_2753_, v_recursorName_2754_, v_x_2755_, v_x_2756_, v_x_2757_, v___y_2758_, v___y_2759_, v___y_2760_, v___y_2761_);
lean_dec(v___y_2761_);
lean_dec_ref(v___y_2760_);
lean_dec(v___y_2759_);
lean_dec_ref(v___y_2758_);
lean_dec(v_x_2757_);
return v_res_2763_;
}
}
static lean_object* _init_l_Lean_MVarId_induction___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2765_; lean_object* v___x_2766_; 
v___x_2765_ = ((lean_object*)(l_Lean_MVarId_induction___lam__0___closed__0));
v___x_2766_ = l_Lean_stringToMessageData(v___x_2765_);
return v___x_2766_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_induction___lam__0(lean_object* v___x_2767_, lean_object* v_mvarId_2768_, lean_object* v_majorFVarId_2769_, lean_object* v_recursorName_2770_, lean_object* v_givenNames_2771_, lean_object* v_cls_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_){
_start:
{
lean_object* v___y_2779_; lean_object* v___y_2780_; lean_object* v___y_2781_; lean_object* v___y_2782_; lean_object* v_toCold_2834_; lean_object* v_options_2835_; uint8_t v_hasTrace_2836_; 
v_toCold_2834_ = lean_ctor_get(v___y_2775_, 0);
v_options_2835_ = lean_ctor_get(v_toCold_2834_, 2);
v_hasTrace_2836_ = lean_ctor_get_uint8(v_options_2835_, sizeof(void*)*1);
if (v_hasTrace_2836_ == 0)
{
lean_dec(v_cls_2772_);
v___y_2779_ = v___y_2773_;
v___y_2780_ = v___y_2774_;
v___y_2781_ = v___y_2775_;
v___y_2782_ = v___y_2776_;
goto v___jp_2778_;
}
else
{
lean_object* v_inheritedTraceOptions_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; uint8_t v___x_2840_; 
v_inheritedTraceOptions_2837_ = lean_ctor_get(v_toCold_2834_, 11);
v___x_2838_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__4));
lean_inc(v_cls_2772_);
v___x_2839_ = l_Lean_Name_append(v___x_2838_, v_cls_2772_);
v___x_2840_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2837_, v_options_2835_, v___x_2839_);
lean_dec(v___x_2839_);
if (v___x_2840_ == 0)
{
lean_dec(v_cls_2772_);
v___y_2779_ = v___y_2773_;
v___y_2780_ = v___y_2774_;
v___y_2781_ = v___y_2775_;
v___y_2782_ = v___y_2776_;
goto v___jp_2778_;
}
else
{
lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; 
v___x_2841_ = lean_obj_once(&l_Lean_MVarId_induction___lam__0___closed__1, &l_Lean_MVarId_induction___lam__0___closed__1_once, _init_l_Lean_MVarId_induction___lam__0___closed__1);
lean_inc(v_mvarId_2768_);
v___x_2842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2842_, 0, v_mvarId_2768_);
v___x_2843_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2843_, 0, v___x_2841_);
lean_ctor_set(v___x_2843_, 1, v___x_2842_);
v___x_2844_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1(v_cls_2772_, v___x_2843_, v___y_2773_, v___y_2774_, v___y_2775_, v___y_2776_);
if (lean_obj_tag(v___x_2844_) == 0)
{
lean_dec_ref_known(v___x_2844_, 1);
v___y_2779_ = v___y_2773_;
v___y_2780_ = v___y_2774_;
v___y_2781_ = v___y_2775_;
v___y_2782_ = v___y_2776_;
goto v___jp_2778_;
}
else
{
lean_object* v_a_2845_; lean_object* v___x_2847_; uint8_t v_isShared_2848_; uint8_t v_isSharedCheck_2852_; 
lean_dec_ref(v_givenNames_2771_);
lean_dec(v_recursorName_2770_);
lean_dec(v_majorFVarId_2769_);
lean_dec(v_mvarId_2768_);
lean_dec_ref(v___x_2767_);
v_a_2845_ = lean_ctor_get(v___x_2844_, 0);
v_isSharedCheck_2852_ = !lean_is_exclusive(v___x_2844_);
if (v_isSharedCheck_2852_ == 0)
{
v___x_2847_ = v___x_2844_;
v_isShared_2848_ = v_isSharedCheck_2852_;
goto v_resetjp_2846_;
}
else
{
lean_inc(v_a_2845_);
lean_dec(v___x_2844_);
v___x_2847_ = lean_box(0);
v_isShared_2848_ = v_isSharedCheck_2852_;
goto v_resetjp_2846_;
}
v_resetjp_2846_:
{
lean_object* v___x_2850_; 
if (v_isShared_2848_ == 0)
{
v___x_2850_ = v___x_2847_;
goto v_reusejp_2849_;
}
else
{
lean_object* v_reuseFailAlloc_2851_; 
v_reuseFailAlloc_2851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2851_, 0, v_a_2845_);
v___x_2850_ = v_reuseFailAlloc_2851_;
goto v_reusejp_2849_;
}
v_reusejp_2849_:
{
return v___x_2850_;
}
}
}
}
}
v___jp_2778_:
{
lean_object* v___x_2783_; lean_object* v___x_2784_; 
v___x_2783_ = l_Lean_Name_mkStr1(v___x_2767_);
lean_inc(v___x_2783_);
lean_inc(v_mvarId_2768_);
v___x_2784_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_2768_, v___x_2783_, v___y_2779_, v___y_2780_, v___y_2781_, v___y_2782_);
if (lean_obj_tag(v___x_2784_) == 0)
{
lean_object* v___x_2785_; 
lean_dec_ref_known(v___x_2784_, 1);
lean_inc(v_majorFVarId_2769_);
v___x_2785_ = l_Lean_FVarId_getDecl___redArg(v_majorFVarId_2769_, v___y_2779_, v___y_2781_, v___y_2782_);
if (lean_obj_tag(v___x_2785_) == 0)
{
lean_object* v_a_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; 
v_a_2786_ = lean_ctor_get(v___x_2785_, 0);
lean_inc(v_a_2786_);
lean_dec_ref_known(v___x_2785_, 1);
v___x_2787_ = lean_box(0);
lean_inc(v_recursorName_2770_);
v___x_2788_ = l_Lean_Meta_mkRecursorInfo(v_recursorName_2770_, v___x_2787_, v___y_2779_, v___y_2780_, v___y_2781_, v___y_2782_);
if (lean_obj_tag(v___x_2788_) == 0)
{
lean_object* v_a_2789_; lean_object* v_typeName_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; 
v_a_2789_ = lean_ctor_get(v___x_2788_, 0);
lean_inc(v_a_2789_);
lean_dec_ref_known(v___x_2788_, 1);
v_typeName_2790_ = lean_ctor_get(v_a_2789_, 1);
v___x_2791_ = l_Lean_LocalDecl_type(v_a_2786_);
lean_dec(v_a_2786_);
lean_inc_ref(v___x_2791_);
v___x_2792_ = l_Lean_Meta_whnfUntil(v___x_2791_, v_typeName_2790_, v___y_2779_, v___y_2780_, v___y_2781_, v___y_2782_);
if (lean_obj_tag(v___x_2792_) == 0)
{
lean_object* v_a_2793_; 
v_a_2793_ = lean_ctor_get(v___x_2792_, 0);
lean_inc(v_a_2793_);
lean_dec_ref_known(v___x_2792_, 1);
if (lean_obj_tag(v_a_2793_) == 1)
{
lean_object* v_val_2794_; lean_object* v_dummy_2795_; lean_object* v_nargs_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; 
lean_dec_ref(v___x_2791_);
lean_dec(v___x_2783_);
v_val_2794_ = lean_ctor_get(v_a_2793_, 0);
lean_inc_n(v_val_2794_, 2);
lean_dec_ref_known(v_a_2793_, 1);
v_dummy_2795_ = lean_obj_once(&l_Lean_Meta_getMajorTypeIndices___closed__0, &l_Lean_Meta_getMajorTypeIndices___closed__0_once, _init_l_Lean_Meta_getMajorTypeIndices___closed__0);
v_nargs_2796_ = l_Lean_Expr_getAppNumArgs(v_val_2794_);
lean_inc(v_nargs_2796_);
v___x_2797_ = lean_mk_array(v_nargs_2796_, v_dummy_2795_);
v___x_2798_ = lean_unsigned_to_nat(1u);
v___x_2799_ = lean_nat_sub(v_nargs_2796_, v___x_2798_);
lean_dec(v_nargs_2796_);
v___x_2800_ = l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4(v_val_2794_, v_mvarId_2768_, v_a_2789_, v_majorFVarId_2769_, v_givenNames_2771_, v_recursorName_2770_, v_val_2794_, v___x_2797_, v___x_2799_, v___y_2779_, v___y_2780_, v___y_2781_, v___y_2782_);
lean_dec(v___x_2799_);
return v___x_2800_;
}
else
{
lean_object* v___x_2801_; 
lean_dec(v_a_2793_);
lean_dec(v_a_2789_);
lean_dec_ref(v_givenNames_2771_);
lean_dec(v_recursorName_2770_);
lean_dec(v_majorFVarId_2769_);
v___x_2801_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg(v___x_2783_, v_mvarId_2768_, v___x_2791_, v___y_2779_, v___y_2780_, v___y_2781_, v___y_2782_);
return v___x_2801_;
}
}
else
{
lean_object* v_a_2802_; lean_object* v___x_2804_; uint8_t v_isShared_2805_; uint8_t v_isSharedCheck_2809_; 
lean_dec_ref(v___x_2791_);
lean_dec(v_a_2789_);
lean_dec(v___x_2783_);
lean_dec_ref(v_givenNames_2771_);
lean_dec(v_recursorName_2770_);
lean_dec(v_majorFVarId_2769_);
lean_dec(v_mvarId_2768_);
v_a_2802_ = lean_ctor_get(v___x_2792_, 0);
v_isSharedCheck_2809_ = !lean_is_exclusive(v___x_2792_);
if (v_isSharedCheck_2809_ == 0)
{
v___x_2804_ = v___x_2792_;
v_isShared_2805_ = v_isSharedCheck_2809_;
goto v_resetjp_2803_;
}
else
{
lean_inc(v_a_2802_);
lean_dec(v___x_2792_);
v___x_2804_ = lean_box(0);
v_isShared_2805_ = v_isSharedCheck_2809_;
goto v_resetjp_2803_;
}
v_resetjp_2803_:
{
lean_object* v___x_2807_; 
if (v_isShared_2805_ == 0)
{
v___x_2807_ = v___x_2804_;
goto v_reusejp_2806_;
}
else
{
lean_object* v_reuseFailAlloc_2808_; 
v_reuseFailAlloc_2808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2808_, 0, v_a_2802_);
v___x_2807_ = v_reuseFailAlloc_2808_;
goto v_reusejp_2806_;
}
v_reusejp_2806_:
{
return v___x_2807_;
}
}
}
}
else
{
lean_object* v_a_2810_; lean_object* v___x_2812_; uint8_t v_isShared_2813_; uint8_t v_isSharedCheck_2817_; 
lean_dec(v_a_2786_);
lean_dec(v___x_2783_);
lean_dec_ref(v_givenNames_2771_);
lean_dec(v_recursorName_2770_);
lean_dec(v_majorFVarId_2769_);
lean_dec(v_mvarId_2768_);
v_a_2810_ = lean_ctor_get(v___x_2788_, 0);
v_isSharedCheck_2817_ = !lean_is_exclusive(v___x_2788_);
if (v_isSharedCheck_2817_ == 0)
{
v___x_2812_ = v___x_2788_;
v_isShared_2813_ = v_isSharedCheck_2817_;
goto v_resetjp_2811_;
}
else
{
lean_inc(v_a_2810_);
lean_dec(v___x_2788_);
v___x_2812_ = lean_box(0);
v_isShared_2813_ = v_isSharedCheck_2817_;
goto v_resetjp_2811_;
}
v_resetjp_2811_:
{
lean_object* v___x_2815_; 
if (v_isShared_2813_ == 0)
{
v___x_2815_ = v___x_2812_;
goto v_reusejp_2814_;
}
else
{
lean_object* v_reuseFailAlloc_2816_; 
v_reuseFailAlloc_2816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2816_, 0, v_a_2810_);
v___x_2815_ = v_reuseFailAlloc_2816_;
goto v_reusejp_2814_;
}
v_reusejp_2814_:
{
return v___x_2815_;
}
}
}
}
else
{
lean_object* v_a_2818_; lean_object* v___x_2820_; uint8_t v_isShared_2821_; uint8_t v_isSharedCheck_2825_; 
lean_dec(v___x_2783_);
lean_dec_ref(v_givenNames_2771_);
lean_dec(v_recursorName_2770_);
lean_dec(v_majorFVarId_2769_);
lean_dec(v_mvarId_2768_);
v_a_2818_ = lean_ctor_get(v___x_2785_, 0);
v_isSharedCheck_2825_ = !lean_is_exclusive(v___x_2785_);
if (v_isSharedCheck_2825_ == 0)
{
v___x_2820_ = v___x_2785_;
v_isShared_2821_ = v_isSharedCheck_2825_;
goto v_resetjp_2819_;
}
else
{
lean_inc(v_a_2818_);
lean_dec(v___x_2785_);
v___x_2820_ = lean_box(0);
v_isShared_2821_ = v_isSharedCheck_2825_;
goto v_resetjp_2819_;
}
v_resetjp_2819_:
{
lean_object* v___x_2823_; 
if (v_isShared_2821_ == 0)
{
v___x_2823_ = v___x_2820_;
goto v_reusejp_2822_;
}
else
{
lean_object* v_reuseFailAlloc_2824_; 
v_reuseFailAlloc_2824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2824_, 0, v_a_2818_);
v___x_2823_ = v_reuseFailAlloc_2824_;
goto v_reusejp_2822_;
}
v_reusejp_2822_:
{
return v___x_2823_;
}
}
}
}
else
{
lean_object* v_a_2826_; lean_object* v___x_2828_; uint8_t v_isShared_2829_; uint8_t v_isSharedCheck_2833_; 
lean_dec(v___x_2783_);
lean_dec_ref(v_givenNames_2771_);
lean_dec(v_recursorName_2770_);
lean_dec(v_majorFVarId_2769_);
lean_dec(v_mvarId_2768_);
v_a_2826_ = lean_ctor_get(v___x_2784_, 0);
v_isSharedCheck_2833_ = !lean_is_exclusive(v___x_2784_);
if (v_isSharedCheck_2833_ == 0)
{
v___x_2828_ = v___x_2784_;
v_isShared_2829_ = v_isSharedCheck_2833_;
goto v_resetjp_2827_;
}
else
{
lean_inc(v_a_2826_);
lean_dec(v___x_2784_);
v___x_2828_ = lean_box(0);
v_isShared_2829_ = v_isSharedCheck_2833_;
goto v_resetjp_2827_;
}
v_resetjp_2827_:
{
lean_object* v___x_2831_; 
if (v_isShared_2829_ == 0)
{
v___x_2831_ = v___x_2828_;
goto v_reusejp_2830_;
}
else
{
lean_object* v_reuseFailAlloc_2832_; 
v_reuseFailAlloc_2832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2832_, 0, v_a_2826_);
v___x_2831_ = v_reuseFailAlloc_2832_;
goto v_reusejp_2830_;
}
v_reusejp_2830_:
{
return v___x_2831_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_induction___lam__0___boxed(lean_object* v___x_2853_, lean_object* v_mvarId_2854_, lean_object* v_majorFVarId_2855_, lean_object* v_recursorName_2856_, lean_object* v_givenNames_2857_, lean_object* v_cls_2858_, lean_object* v___y_2859_, lean_object* v___y_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_, lean_object* v___y_2863_){
_start:
{
lean_object* v_res_2864_; 
v_res_2864_ = l_Lean_MVarId_induction___lam__0(v___x_2853_, v_mvarId_2854_, v_majorFVarId_2855_, v_recursorName_2856_, v_givenNames_2857_, v_cls_2858_, v___y_2859_, v___y_2860_, v___y_2861_, v___y_2862_);
lean_dec(v___y_2862_);
lean_dec_ref(v___y_2861_);
lean_dec(v___y_2860_);
lean_dec_ref(v___y_2859_);
return v_res_2864_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_induction(lean_object* v_mvarId_2865_, lean_object* v_majorFVarId_2866_, lean_object* v_recursorName_2867_, lean_object* v_givenNames_2868_, lean_object* v_a_2869_, lean_object* v_a_2870_, lean_object* v_a_2871_, lean_object* v_a_2872_){
_start:
{
lean_object* v___x_2874_; lean_object* v_cls_2875_; lean_object* v___f_2876_; lean_object* v___x_2877_; 
v___x_2874_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__0));
v_cls_2875_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__2));
lean_inc(v_mvarId_2865_);
v___f_2876_ = lean_alloc_closure((void*)(l_Lean_MVarId_induction___lam__0___boxed), 11, 6);
lean_closure_set(v___f_2876_, 0, v___x_2874_);
lean_closure_set(v___f_2876_, 1, v_mvarId_2865_);
lean_closure_set(v___f_2876_, 2, v_majorFVarId_2866_);
lean_closure_set(v___f_2876_, 3, v_recursorName_2867_);
lean_closure_set(v___f_2876_, 4, v_givenNames_2868_);
lean_closure_set(v___f_2876_, 5, v_cls_2875_);
v___x_2877_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___redArg(v_mvarId_2865_, v___f_2876_, v_a_2869_, v_a_2870_, v_a_2871_, v_a_2872_);
return v___x_2877_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_induction___boxed(lean_object* v_mvarId_2878_, lean_object* v_majorFVarId_2879_, lean_object* v_recursorName_2880_, lean_object* v_givenNames_2881_, lean_object* v_a_2882_, lean_object* v_a_2883_, lean_object* v_a_2884_, lean_object* v_a_2885_, lean_object* v_a_2886_){
_start:
{
lean_object* v_res_2887_; 
v_res_2887_ = l_Lean_MVarId_induction(v_mvarId_2878_, v_majorFVarId_2879_, v_recursorName_2880_, v_givenNames_2881_, v_a_2882_, v_a_2883_, v_a_2884_, v_a_2885_);
lean_dec(v_a_2885_);
lean_dec_ref(v_a_2884_);
lean_dec(v_a_2883_);
lean_dec_ref(v_a_2882_);
return v_res_2887_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; 
v___x_2935_ = lean_unsigned_to_nat(2221195325u);
v___x_2936_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_));
v___x_2937_ = l_Lean_Name_num___override(v___x_2936_, v___x_2935_);
return v___x_2937_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; 
v___x_2939_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_));
v___x_2940_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_);
v___x_2941_ = l_Lean_Name_str___override(v___x_2940_, v___x_2939_);
return v___x_2941_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; 
v___x_2943_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_));
v___x_2944_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_);
v___x_2945_ = l_Lean_Name_str___override(v___x_2944_, v___x_2943_);
return v___x_2945_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; 
v___x_2946_ = lean_unsigned_to_nat(2u);
v___x_2947_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_);
v___x_2948_ = l_Lean_Name_num___override(v___x_2947_, v___x_2946_);
return v___x_2948_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2950_; uint8_t v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; 
v___x_2950_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__2));
v___x_2951_ = 0;
v___x_2952_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_);
v___x_2953_ = l_Lean_registerTraceClass(v___x_2950_, v___x_2951_, v___x_2952_);
return v___x_2953_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2____boxed(lean_object* v_a_2954_){
_start:
{
lean_object* v_res_2955_; 
v_res_2955_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_();
return v_res_2955_;
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
