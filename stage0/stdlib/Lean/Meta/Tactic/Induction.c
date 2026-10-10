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
lean_object* l_Lean_Meta_instInhabitedMetaM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__3(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__3___boxed(lean_object*, lean_object*, lean_object*);
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
lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams(lean_object* v_mvarId_30_, lean_object* v_majorTypeArgs_31_, lean_object* v_x_32_, lean_object* v_x_33_, lean_object* v_a_34_, lean_object* v_a_35_, lean_object* v_a_36_, lean_object* v_a_37_){
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
v___x_59_ = l_Lean_Exception_isInterrupt(v_a_53_);
if (v___x_59_ == 0)
{
uint8_t v___x_60_; 
lean_inc(v_a_53_);
v___x_60_ = l_Lean_Exception_isRuntime(v_a_53_);
v___y_55_ = v___x_60_;
goto v___jp_54_;
}
else
{
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
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_30_ = stack[0].m_obj;
lean_object* v_majorTypeArgs_31_ = stack[1].m_obj;
lean_object* v_x_32_ = stack[2].m_obj;
lean_object* v_x_33_ = stack[3].m_obj;
lean_object* v_a_34_ = stack[4].m_obj;
lean_object* v_a_35_ = stack[5].m_obj;
lean_object* v_a_36_ = stack[6].m_obj;
lean_object* v_a_37_ = stack[7].m_obj;
lean_object* v_res_73_;
v_res_73_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams(v_mvarId_30_, v_majorTypeArgs_31_, v_x_32_, v_x_33_, v_a_34_, v_a_35_, v_a_36_, v_a_37_);
stack->m_obj
 = v_res_73_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___boxed(lean_object* v_mvarId_74_, lean_object* v_majorTypeArgs_75_, lean_object* v_x_76_, lean_object* v_x_77_, lean_object* v_a_78_, lean_object* v_a_79_, lean_object* v_a_80_, lean_object* v_a_81_, lean_object* v_a_82_){
_start:
{
lean_object* v_res_83_; 
v_res_83_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams(v_mvarId_74_, v_majorTypeArgs_75_, v_x_76_, v_x_77_, v_a_78_, v_a_79_, v_a_80_, v_a_81_);
lean_dec(v_a_81_);
lean_dec_ref(v_a_80_);
lean_dec(v_a_79_);
lean_dec_ref(v_a_78_);
lean_dec_ref(v_majorTypeArgs_75_);
return v_res_83_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTypeBody(lean_object* v_mvarId_92_, lean_object* v_type_93_, lean_object* v_x_94_, lean_object* v_a_95_, lean_object* v_a_96_, lean_object* v_a_97_, lean_object* v_a_98_){
_start:
{
lean_object* v___x_100_; 
v___x_100_ = l_Lean_Meta_whnfForall(v_type_93_, v_a_95_, v_a_96_, v_a_97_, v_a_98_);
if (lean_obj_tag(v___x_100_) == 0)
{
lean_object* v_a_101_; lean_object* v___x_103_; uint8_t v_isShared_104_; uint8_t v_isSharedCheck_113_; 
v_a_101_ = lean_ctor_get(v___x_100_, 0);
v_isSharedCheck_113_ = !lean_is_exclusive(v___x_100_);
if (v_isSharedCheck_113_ == 0)
{
v___x_103_ = v___x_100_;
v_isShared_104_ = v_isSharedCheck_113_;
goto v_resetjp_102_;
}
else
{
lean_inc(v_a_101_);
lean_dec(v___x_100_);
v___x_103_ = lean_box(0);
v_isShared_104_ = v_isSharedCheck_113_;
goto v_resetjp_102_;
}
v_resetjp_102_:
{
if (lean_obj_tag(v_a_101_) == 7)
{
lean_object* v_body_105_; lean_object* v___x_106_; lean_object* v___x_108_; 
lean_dec(v_mvarId_92_);
v_body_105_ = lean_ctor_get(v_a_101_, 2);
lean_inc_ref(v_body_105_);
lean_dec_ref_known(v_a_101_, 3);
v___x_106_ = lean_expr_instantiate1(v_body_105_, v_x_94_);
lean_dec_ref(v_body_105_);
if (v_isShared_104_ == 0)
{
lean_ctor_set(v___x_103_, 0, v___x_106_);
v___x_108_ = v___x_103_;
goto v_reusejp_107_;
}
else
{
lean_object* v_reuseFailAlloc_109_; 
v_reuseFailAlloc_109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_109_, 0, v___x_106_);
v___x_108_ = v_reuseFailAlloc_109_;
goto v_reusejp_107_;
}
v_reusejp_107_:
{
return v___x_108_;
}
}
else
{
lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; 
lean_del_object(v___x_103_);
lean_dec(v_a_101_);
v___x_110_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1));
v___x_111_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9);
v___x_112_ = l_Lean_Meta_throwTacticEx___redArg(v___x_110_, v_mvarId_92_, v___x_111_, v_a_95_, v_a_96_, v_a_97_, v_a_98_);
return v___x_112_;
}
}
}
else
{
lean_dec(v_mvarId_92_);
return v___x_100_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTypeBody_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_92_ = stack[0].m_obj;
lean_object* v_type_93_ = stack[1].m_obj;
lean_object* v_x_94_ = stack[2].m_obj;
lean_object* v_a_95_ = stack[3].m_obj;
lean_object* v_a_96_ = stack[4].m_obj;
lean_object* v_a_97_ = stack[5].m_obj;
lean_object* v_a_98_ = stack[6].m_obj;
lean_object* v_res_114_;
v_res_114_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTypeBody(v_mvarId_92_, v_type_93_, v_x_94_, v_a_95_, v_a_96_, v_a_97_, v_a_98_);
stack->m_obj
 = v_res_114_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTypeBody___boxed(lean_object* v_mvarId_115_, lean_object* v_type_116_, lean_object* v_x_117_, lean_object* v_a_118_, lean_object* v_a_119_, lean_object* v_a_120_, lean_object* v_a_121_, lean_object* v_a_122_){
_start:
{
lean_object* v_res_123_; 
v_res_123_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTypeBody(v_mvarId_115_, v_type_116_, v_x_117_, v_a_118_, v_a_119_, v_a_120_, v_a_121_);
lean_dec(v_a_121_);
lean_dec_ref(v_a_120_);
lean_dec(v_a_119_);
lean_dec_ref(v_a_118_);
lean_dec_ref(v_x_117_);
return v_res_123_;
}
}
lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__4(lean_object* v_msg_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_){
_start:
{
lean_object* v___f_136_; lean_object* v___x_6375__overap_137_; lean_object* v___x_138_; 
v___f_136_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__4___closed__0));
v___x_6375__overap_137_ = lean_panic_fn_borrowed(v___f_136_, v_msg_130_);
lean_inc(v___y_134_);
lean_inc_ref(v___y_133_);
lean_inc(v___y_132_);
lean_inc_ref(v___y_131_);
v___x_138_ = lean_apply_5(v___x_6375__overap_137_, v___y_131_, v___y_132_, v___y_133_, v___y_134_, lean_box(0));
return v___x_138_;
}
}
LEAN_EXPORT void l_panic___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_130_ = stack[0].m_obj;
lean_object* v___y_131_ = stack[1].m_obj;
lean_object* v___y_132_ = stack[2].m_obj;
lean_object* v___y_133_ = stack[3].m_obj;
lean_object* v___y_134_ = stack[4].m_obj;
lean_object* v_res_139_;
v_res_139_ = l_panic___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__4(v_msg_130_, v___y_131_, v___y_132_, v___y_133_, v___y_134_);
stack->m_obj
 = v_res_139_;
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__4___boxed(lean_object* v_msg_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_){
_start:
{
lean_object* v_res_146_; 
v_res_146_ = l_panic___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__4(v_msg_140_, v___y_141_, v___y_142_, v___y_143_, v___y_144_);
lean_dec(v___y_144_);
lean_dec_ref(v___y_143_);
lean_dec(v___y_142_);
lean_dec_ref(v___y_141_);
return v_res_146_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__2___redArg(lean_object* v___x_147_, lean_object* v_reverted_148_, lean_object* v_fst_149_, lean_object* v_n_150_, lean_object* v_j_151_, lean_object* v_a_152_){
_start:
{
lean_object* v_zero_153_; uint8_t v_isZero_154_; 
v_zero_153_ = lean_unsigned_to_nat(0u);
v_isZero_154_ = lean_nat_dec_eq(v_j_151_, v_zero_153_);
if (v_isZero_154_ == 1)
{
lean_dec(v_j_151_);
return v_a_152_;
}
else
{
lean_object* v___x_155_; lean_object* v_n_156_; lean_object* v___x_157_; lean_object* v___x_158_; uint8_t v___x_159_; 
v___x_155_ = lean_unsigned_to_nat(1u);
v_n_156_ = lean_nat_sub(v_j_151_, v___x_155_);
v___x_157_ = lean_nat_sub(v_n_150_, v_j_151_);
lean_dec(v_j_151_);
v___x_158_ = lean_nat_add(v___x_147_, v___x_155_);
v___x_159_ = lean_nat_dec_lt(v___x_157_, v___x_158_);
lean_dec(v___x_158_);
if (v___x_159_ == 0)
{
lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; 
v___x_160_ = lean_box(0);
v___x_161_ = lean_array_fget_borrowed(v_reverted_148_, v___x_157_);
v___x_162_ = lean_nat_sub(v___x_157_, v___x_147_);
lean_dec(v___x_157_);
v___x_163_ = lean_nat_sub(v___x_162_, v___x_155_);
lean_dec(v___x_162_);
v___x_164_ = lean_array_get_borrowed(v___x_160_, v_fst_149_, v___x_163_);
lean_dec(v___x_163_);
lean_inc(v___x_164_);
v___x_165_ = l_Lean_mkFVar(v___x_164_);
lean_inc(v___x_161_);
v___x_166_ = l_Lean_Meta_FVarSubst_insert(v_a_152_, v___x_161_, v___x_165_);
v_j_151_ = v_n_156_;
v_a_152_ = v___x_166_;
goto _start;
}
else
{
lean_dec(v___x_157_);
v_j_151_ = v_n_156_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__2___redArg___boxed(lean_object* v___x_169_, lean_object* v_reverted_170_, lean_object* v_fst_171_, lean_object* v_n_172_, lean_object* v_j_173_, lean_object* v_a_174_){
_start:
{
lean_object* v_res_175_; 
v_res_175_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__2___redArg(v___x_169_, v_reverted_170_, v_fst_171_, v_n_172_, v_j_173_, v_a_174_);
lean_dec(v_n_172_);
lean_dec_ref(v_fst_171_);
lean_dec_ref(v_reverted_170_);
lean_dec(v___x_169_);
return v_res_175_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__5(lean_object* v_mvarId_176_, lean_object* v_as_177_, size_t v_i_178_, size_t v_stop_179_, lean_object* v_b_180_, lean_object* v___y_181_, lean_object* v___y_182_, lean_object* v___y_183_, lean_object* v___y_184_){
_start:
{
uint8_t v___x_186_; 
v___x_186_ = lean_usize_dec_eq(v_i_178_, v_stop_179_);
if (v___x_186_ == 0)
{
lean_object* v_fst_187_; lean_object* v_snd_188_; lean_object* v___x_190_; uint8_t v_isShared_191_; uint8_t v_isSharedCheck_210_; 
v_fst_187_ = lean_ctor_get(v_b_180_, 0);
v_snd_188_ = lean_ctor_get(v_b_180_, 1);
v_isSharedCheck_210_ = !lean_is_exclusive(v_b_180_);
if (v_isSharedCheck_210_ == 0)
{
v___x_190_ = v_b_180_;
v_isShared_191_ = v_isSharedCheck_210_;
goto v_resetjp_189_;
}
else
{
lean_inc(v_snd_188_);
lean_inc(v_fst_187_);
lean_dec(v_b_180_);
v___x_190_ = lean_box(0);
v_isShared_191_ = v_isSharedCheck_210_;
goto v_resetjp_189_;
}
v_resetjp_189_:
{
lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; 
v___x_192_ = lean_array_uget_borrowed(v_as_177_, v_i_178_);
lean_inc(v___x_192_);
v___x_193_ = l_Lean_Expr_app___override(v_fst_187_, v___x_192_);
lean_inc(v_mvarId_176_);
v___x_194_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTypeBody(v_mvarId_176_, v_snd_188_, v___x_192_, v___y_181_, v___y_182_, v___y_183_, v___y_184_);
if (lean_obj_tag(v___x_194_) == 0)
{
lean_object* v_a_195_; lean_object* v___x_197_; 
v_a_195_ = lean_ctor_get(v___x_194_, 0);
lean_inc(v_a_195_);
lean_dec_ref_known(v___x_194_, 1);
if (v_isShared_191_ == 0)
{
lean_ctor_set(v___x_190_, 1, v_a_195_);
lean_ctor_set(v___x_190_, 0, v___x_193_);
v___x_197_ = v___x_190_;
goto v_reusejp_196_;
}
else
{
lean_object* v_reuseFailAlloc_201_; 
v_reuseFailAlloc_201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_201_, 0, v___x_193_);
lean_ctor_set(v_reuseFailAlloc_201_, 1, v_a_195_);
v___x_197_ = v_reuseFailAlloc_201_;
goto v_reusejp_196_;
}
v_reusejp_196_:
{
size_t v___x_198_; size_t v___x_199_; 
v___x_198_ = ((size_t)1ULL);
v___x_199_ = lean_usize_add(v_i_178_, v___x_198_);
v_i_178_ = v___x_199_;
v_b_180_ = v___x_197_;
goto _start;
}
}
else
{
lean_object* v_a_202_; lean_object* v___x_204_; uint8_t v_isShared_205_; uint8_t v_isSharedCheck_209_; 
lean_dec_ref(v___x_193_);
lean_del_object(v___x_190_);
lean_dec(v_mvarId_176_);
v_a_202_ = lean_ctor_get(v___x_194_, 0);
v_isSharedCheck_209_ = !lean_is_exclusive(v___x_194_);
if (v_isSharedCheck_209_ == 0)
{
v___x_204_ = v___x_194_;
v_isShared_205_ = v_isSharedCheck_209_;
goto v_resetjp_203_;
}
else
{
lean_inc(v_a_202_);
lean_dec(v___x_194_);
v___x_204_ = lean_box(0);
v_isShared_205_ = v_isSharedCheck_209_;
goto v_resetjp_203_;
}
v_resetjp_203_:
{
lean_object* v___x_207_; 
if (v_isShared_205_ == 0)
{
v___x_207_ = v___x_204_;
goto v_reusejp_206_;
}
else
{
lean_object* v_reuseFailAlloc_208_; 
v_reuseFailAlloc_208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_208_, 0, v_a_202_);
v___x_207_ = v_reuseFailAlloc_208_;
goto v_reusejp_206_;
}
v_reusejp_206_:
{
return v___x_207_;
}
}
}
}
}
else
{
lean_object* v___x_211_; 
lean_dec(v_mvarId_176_);
v___x_211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_211_, 0, v_b_180_);
return v___x_211_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_176_ = stack[0].m_obj;
lean_object* v_as_177_ = stack[1].m_obj;
size_t v_i_178_ = stack[2].m_num;
size_t v_stop_179_ = stack[3].m_num;
lean_object* v_b_180_ = stack[4].m_obj;
lean_object* v___y_181_ = stack[5].m_obj;
lean_object* v___y_182_ = stack[6].m_obj;
lean_object* v___y_183_ = stack[7].m_obj;
lean_object* v___y_184_ = stack[8].m_obj;
lean_object* v_res_212_;
v_res_212_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__5(v_mvarId_176_, v_as_177_, v_i_178_, v_stop_179_, v_b_180_, v___y_181_, v___y_182_, v___y_183_, v___y_184_);
stack->m_obj
 = v_res_212_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__5___boxed(lean_object* v_mvarId_213_, lean_object* v_as_214_, lean_object* v_i_215_, lean_object* v_stop_216_, lean_object* v_b_217_, lean_object* v___y_218_, lean_object* v___y_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_){
_start:
{
size_t v_i_boxed_223_; size_t v_stop_boxed_224_; lean_object* v_res_225_; 
v_i_boxed_223_ = lean_unbox_usize(v_i_215_);
lean_dec(v_i_215_);
v_stop_boxed_224_ = lean_unbox_usize(v_stop_216_);
lean_dec(v_stop_216_);
v_res_225_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__5(v_mvarId_213_, v_as_214_, v_i_boxed_223_, v_stop_boxed_224_, v_b_217_, v___y_218_, v___y_219_, v___y_220_, v___y_221_);
lean_dec(v___y_221_);
lean_dec_ref(v___y_220_);
lean_dec(v___y_219_);
lean_dec_ref(v___y_218_);
lean_dec_ref(v_as_214_);
return v_res_225_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__8_spec__9___redArg(lean_object* v_x_226_, lean_object* v_x_227_, lean_object* v_x_228_, lean_object* v_x_229_){
_start:
{
lean_object* v_ks_230_; lean_object* v_vs_231_; lean_object* v___x_233_; uint8_t v_isShared_234_; uint8_t v_isSharedCheck_255_; 
v_ks_230_ = lean_ctor_get(v_x_226_, 0);
v_vs_231_ = lean_ctor_get(v_x_226_, 1);
v_isSharedCheck_255_ = !lean_is_exclusive(v_x_226_);
if (v_isSharedCheck_255_ == 0)
{
v___x_233_ = v_x_226_;
v_isShared_234_ = v_isSharedCheck_255_;
goto v_resetjp_232_;
}
else
{
lean_inc(v_vs_231_);
lean_inc(v_ks_230_);
lean_dec(v_x_226_);
v___x_233_ = lean_box(0);
v_isShared_234_ = v_isSharedCheck_255_;
goto v_resetjp_232_;
}
v_resetjp_232_:
{
lean_object* v___x_235_; uint8_t v___x_236_; 
v___x_235_ = lean_array_get_size(v_ks_230_);
v___x_236_ = lean_nat_dec_lt(v_x_227_, v___x_235_);
if (v___x_236_ == 0)
{
lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_240_; 
lean_dec(v_x_227_);
v___x_237_ = lean_array_push(v_ks_230_, v_x_228_);
v___x_238_ = lean_array_push(v_vs_231_, v_x_229_);
if (v_isShared_234_ == 0)
{
lean_ctor_set(v___x_233_, 1, v___x_238_);
lean_ctor_set(v___x_233_, 0, v___x_237_);
v___x_240_ = v___x_233_;
goto v_reusejp_239_;
}
else
{
lean_object* v_reuseFailAlloc_241_; 
v_reuseFailAlloc_241_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_241_, 0, v___x_237_);
lean_ctor_set(v_reuseFailAlloc_241_, 1, v___x_238_);
v___x_240_ = v_reuseFailAlloc_241_;
goto v_reusejp_239_;
}
v_reusejp_239_:
{
return v___x_240_;
}
}
else
{
lean_object* v_k_x27_242_; uint8_t v___x_243_; 
v_k_x27_242_ = lean_array_fget_borrowed(v_ks_230_, v_x_227_);
v___x_243_ = l_Lean_instBEqMVarId_beq(v_x_228_, v_k_x27_242_);
if (v___x_243_ == 0)
{
lean_object* v___x_245_; 
if (v_isShared_234_ == 0)
{
v___x_245_ = v___x_233_;
goto v_reusejp_244_;
}
else
{
lean_object* v_reuseFailAlloc_249_; 
v_reuseFailAlloc_249_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_249_, 0, v_ks_230_);
lean_ctor_set(v_reuseFailAlloc_249_, 1, v_vs_231_);
v___x_245_ = v_reuseFailAlloc_249_;
goto v_reusejp_244_;
}
v_reusejp_244_:
{
lean_object* v___x_246_; lean_object* v___x_247_; 
v___x_246_ = lean_unsigned_to_nat(1u);
v___x_247_ = lean_nat_add(v_x_227_, v___x_246_);
lean_dec(v_x_227_);
v_x_226_ = v___x_245_;
v_x_227_ = v___x_247_;
goto _start;
}
}
else
{
lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_253_; 
v___x_250_ = lean_array_fset(v_ks_230_, v_x_227_, v_x_228_);
v___x_251_ = lean_array_fset(v_vs_231_, v_x_227_, v_x_229_);
lean_dec(v_x_227_);
if (v_isShared_234_ == 0)
{
lean_ctor_set(v___x_233_, 1, v___x_251_);
lean_ctor_set(v___x_233_, 0, v___x_250_);
v___x_253_ = v___x_233_;
goto v_reusejp_252_;
}
else
{
lean_object* v_reuseFailAlloc_254_; 
v_reuseFailAlloc_254_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_254_, 0, v___x_250_);
lean_ctor_set(v_reuseFailAlloc_254_, 1, v___x_251_);
v___x_253_ = v_reuseFailAlloc_254_;
goto v_reusejp_252_;
}
v_reusejp_252_:
{
return v___x_253_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__8___redArg(lean_object* v_n_256_, lean_object* v_k_257_, lean_object* v_v_258_){
_start:
{
lean_object* v___x_259_; lean_object* v___x_260_; 
v___x_259_ = lean_unsigned_to_nat(0u);
v___x_260_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__8_spec__9___redArg(v_n_256_, v___x_259_, v_k_257_, v_v_258_);
return v___x_260_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_261_; 
v___x_261_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_261_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2___redArg(lean_object* v_x_262_, size_t v_x_263_, size_t v_x_264_, lean_object* v_x_265_, lean_object* v_x_266_){
_start:
{
if (lean_obj_tag(v_x_262_) == 0)
{
lean_object* v_es_267_; size_t v___x_268_; size_t v___x_269_; lean_object* v_j_270_; lean_object* v___x_271_; uint8_t v___x_272_; 
v_es_267_ = lean_ctor_get(v_x_262_, 0);
v___x_268_ = ((size_t)31ULL);
v___x_269_ = lean_usize_land(v_x_263_, v___x_268_);
v_j_270_ = lean_usize_to_nat(v___x_269_);
v___x_271_ = lean_array_get_size(v_es_267_);
v___x_272_ = lean_nat_dec_lt(v_j_270_, v___x_271_);
if (v___x_272_ == 0)
{
lean_dec(v_j_270_);
lean_dec(v_x_266_);
lean_dec(v_x_265_);
return v_x_262_;
}
else
{
lean_object* v___x_274_; uint8_t v_isShared_275_; uint8_t v_isSharedCheck_311_; 
lean_inc_ref(v_es_267_);
v_isSharedCheck_311_ = !lean_is_exclusive(v_x_262_);
if (v_isSharedCheck_311_ == 0)
{
lean_object* v_unused_312_; 
v_unused_312_ = lean_ctor_get(v_x_262_, 0);
lean_dec(v_unused_312_);
v___x_274_ = v_x_262_;
v_isShared_275_ = v_isSharedCheck_311_;
goto v_resetjp_273_;
}
else
{
lean_dec(v_x_262_);
v___x_274_ = lean_box(0);
v_isShared_275_ = v_isSharedCheck_311_;
goto v_resetjp_273_;
}
v_resetjp_273_:
{
lean_object* v_v_276_; lean_object* v___x_277_; lean_object* v_xs_x27_278_; lean_object* v___y_280_; 
v_v_276_ = lean_array_fget(v_es_267_, v_j_270_);
v___x_277_ = lean_box(0);
v_xs_x27_278_ = lean_array_fset(v_es_267_, v_j_270_, v___x_277_);
switch(lean_obj_tag(v_v_276_))
{
case 0:
{
lean_object* v_key_285_; lean_object* v_val_286_; lean_object* v___x_288_; uint8_t v_isShared_289_; uint8_t v_isSharedCheck_296_; 
v_key_285_ = lean_ctor_get(v_v_276_, 0);
v_val_286_ = lean_ctor_get(v_v_276_, 1);
v_isSharedCheck_296_ = !lean_is_exclusive(v_v_276_);
if (v_isSharedCheck_296_ == 0)
{
v___x_288_ = v_v_276_;
v_isShared_289_ = v_isSharedCheck_296_;
goto v_resetjp_287_;
}
else
{
lean_inc(v_val_286_);
lean_inc(v_key_285_);
lean_dec(v_v_276_);
v___x_288_ = lean_box(0);
v_isShared_289_ = v_isSharedCheck_296_;
goto v_resetjp_287_;
}
v_resetjp_287_:
{
uint8_t v___x_290_; 
v___x_290_ = l_Lean_instBEqMVarId_beq(v_x_265_, v_key_285_);
if (v___x_290_ == 0)
{
lean_object* v___x_291_; lean_object* v___x_292_; 
lean_del_object(v___x_288_);
v___x_291_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_285_, v_val_286_, v_x_265_, v_x_266_);
v___x_292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_292_, 0, v___x_291_);
v___y_280_ = v___x_292_;
goto v___jp_279_;
}
else
{
lean_object* v___x_294_; 
lean_dec(v_val_286_);
lean_dec(v_key_285_);
if (v_isShared_289_ == 0)
{
lean_ctor_set(v___x_288_, 1, v_x_266_);
lean_ctor_set(v___x_288_, 0, v_x_265_);
v___x_294_ = v___x_288_;
goto v_reusejp_293_;
}
else
{
lean_object* v_reuseFailAlloc_295_; 
v_reuseFailAlloc_295_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_295_, 0, v_x_265_);
lean_ctor_set(v_reuseFailAlloc_295_, 1, v_x_266_);
v___x_294_ = v_reuseFailAlloc_295_;
goto v_reusejp_293_;
}
v_reusejp_293_:
{
v___y_280_ = v___x_294_;
goto v___jp_279_;
}
}
}
}
case 1:
{
lean_object* v_node_297_; lean_object* v___x_299_; uint8_t v_isShared_300_; uint8_t v_isSharedCheck_309_; 
v_node_297_ = lean_ctor_get(v_v_276_, 0);
v_isSharedCheck_309_ = !lean_is_exclusive(v_v_276_);
if (v_isSharedCheck_309_ == 0)
{
v___x_299_ = v_v_276_;
v_isShared_300_ = v_isSharedCheck_309_;
goto v_resetjp_298_;
}
else
{
lean_inc(v_node_297_);
lean_dec(v_v_276_);
v___x_299_ = lean_box(0);
v_isShared_300_ = v_isSharedCheck_309_;
goto v_resetjp_298_;
}
v_resetjp_298_:
{
size_t v___x_301_; size_t v___x_302_; size_t v___x_303_; size_t v___x_304_; lean_object* v___x_305_; lean_object* v___x_307_; 
v___x_301_ = ((size_t)5ULL);
v___x_302_ = lean_usize_shift_right(v_x_263_, v___x_301_);
v___x_303_ = ((size_t)1ULL);
v___x_304_ = lean_usize_add(v_x_264_, v___x_303_);
v___x_305_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2___redArg(v_node_297_, v___x_302_, v___x_304_, v_x_265_, v_x_266_);
if (v_isShared_300_ == 0)
{
lean_ctor_set(v___x_299_, 0, v___x_305_);
v___x_307_ = v___x_299_;
goto v_reusejp_306_;
}
else
{
lean_object* v_reuseFailAlloc_308_; 
v_reuseFailAlloc_308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_308_, 0, v___x_305_);
v___x_307_ = v_reuseFailAlloc_308_;
goto v_reusejp_306_;
}
v_reusejp_306_:
{
v___y_280_ = v___x_307_;
goto v___jp_279_;
}
}
}
default: 
{
lean_object* v___x_310_; 
v___x_310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_310_, 0, v_x_265_);
lean_ctor_set(v___x_310_, 1, v_x_266_);
v___y_280_ = v___x_310_;
goto v___jp_279_;
}
}
v___jp_279_:
{
lean_object* v___x_281_; lean_object* v___x_283_; 
v___x_281_ = lean_array_fset(v_xs_x27_278_, v_j_270_, v___y_280_);
lean_dec(v_j_270_);
if (v_isShared_275_ == 0)
{
lean_ctor_set(v___x_274_, 0, v___x_281_);
v___x_283_ = v___x_274_;
goto v_reusejp_282_;
}
else
{
lean_object* v_reuseFailAlloc_284_; 
v_reuseFailAlloc_284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_284_, 0, v___x_281_);
v___x_283_ = v_reuseFailAlloc_284_;
goto v_reusejp_282_;
}
v_reusejp_282_:
{
return v___x_283_;
}
}
}
}
}
else
{
lean_object* v_ks_313_; lean_object* v_vs_314_; lean_object* v___x_316_; uint8_t v_isShared_317_; uint8_t v_isSharedCheck_332_; 
v_ks_313_ = lean_ctor_get(v_x_262_, 0);
v_vs_314_ = lean_ctor_get(v_x_262_, 1);
v_isSharedCheck_332_ = !lean_is_exclusive(v_x_262_);
if (v_isSharedCheck_332_ == 0)
{
v___x_316_ = v_x_262_;
v_isShared_317_ = v_isSharedCheck_332_;
goto v_resetjp_315_;
}
else
{
lean_inc(v_vs_314_);
lean_inc(v_ks_313_);
lean_dec(v_x_262_);
v___x_316_ = lean_box(0);
v_isShared_317_ = v_isSharedCheck_332_;
goto v_resetjp_315_;
}
v_resetjp_315_:
{
lean_object* v___x_319_; 
if (v_isShared_317_ == 0)
{
v___x_319_ = v___x_316_;
goto v_reusejp_318_;
}
else
{
lean_object* v_reuseFailAlloc_331_; 
v_reuseFailAlloc_331_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_331_, 0, v_ks_313_);
lean_ctor_set(v_reuseFailAlloc_331_, 1, v_vs_314_);
v___x_319_ = v_reuseFailAlloc_331_;
goto v_reusejp_318_;
}
v_reusejp_318_:
{
lean_object* v_newNode_320_; size_t v___x_321_; uint8_t v___x_322_; 
v_newNode_320_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__8___redArg(v___x_319_, v_x_265_, v_x_266_);
v___x_321_ = ((size_t)7ULL);
v___x_322_ = lean_usize_dec_le(v___x_321_, v_x_264_);
if (v___x_322_ == 0)
{
lean_object* v___x_323_; lean_object* v___x_324_; uint8_t v___x_325_; 
v___x_323_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_320_);
v___x_324_ = lean_unsigned_to_nat(4u);
v___x_325_ = lean_nat_dec_lt(v___x_323_, v___x_324_);
lean_dec(v___x_323_);
if (v___x_325_ == 0)
{
lean_object* v_ks_326_; lean_object* v_vs_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; 
v_ks_326_ = lean_ctor_get(v_newNode_320_, 0);
lean_inc_ref(v_ks_326_);
v_vs_327_ = lean_ctor_get(v_newNode_320_, 1);
lean_inc_ref(v_vs_327_);
lean_dec_ref(v_newNode_320_);
v___x_328_ = lean_unsigned_to_nat(0u);
v___x_329_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2___redArg___closed__0);
v___x_330_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__9___redArg(v_x_264_, v_ks_326_, v_vs_327_, v___x_328_, v___x_329_);
lean_dec_ref(v_vs_327_);
lean_dec_ref(v_ks_326_);
return v___x_330_;
}
else
{
return v_newNode_320_;
}
}
else
{
return v_newNode_320_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_262_ = stack[0].m_obj;
size_t v_x_263_ = stack[1].m_num;
size_t v_x_264_ = stack[2].m_num;
lean_object* v_x_265_ = stack[3].m_obj;
lean_object* v_x_266_ = stack[4].m_obj;
lean_object* v_res_333_;
v_res_333_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2___redArg(v_x_262_, v_x_263_, v_x_264_, v_x_265_, v_x_266_);
stack->m_obj
 = v_res_333_;
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__9___redArg(size_t v_depth_334_, lean_object* v_keys_335_, lean_object* v_vals_336_, lean_object* v_i_337_, lean_object* v_entries_338_){
_start:
{
lean_object* v___x_339_; uint8_t v___x_340_; 
v___x_339_ = lean_array_get_size(v_keys_335_);
v___x_340_ = lean_nat_dec_lt(v_i_337_, v___x_339_);
if (v___x_340_ == 0)
{
lean_dec(v_i_337_);
return v_entries_338_;
}
else
{
lean_object* v_k_341_; lean_object* v_v_342_; uint64_t v___x_343_; size_t v_h_344_; size_t v___x_345_; lean_object* v___x_346_; size_t v___x_347_; size_t v___x_348_; size_t v___x_349_; size_t v_h_350_; lean_object* v___x_351_; lean_object* v___x_352_; 
v_k_341_ = lean_array_fget_borrowed(v_keys_335_, v_i_337_);
v_v_342_ = lean_array_fget_borrowed(v_vals_336_, v_i_337_);
v___x_343_ = l_Lean_instHashableMVarId_hash(v_k_341_);
v_h_344_ = lean_uint64_to_usize(v___x_343_);
v___x_345_ = ((size_t)5ULL);
v___x_346_ = lean_unsigned_to_nat(1u);
v___x_347_ = ((size_t)1ULL);
v___x_348_ = lean_usize_sub(v_depth_334_, v___x_347_);
v___x_349_ = lean_usize_mul(v___x_345_, v___x_348_);
v_h_350_ = lean_usize_shift_right(v_h_344_, v___x_349_);
v___x_351_ = lean_nat_add(v_i_337_, v___x_346_);
lean_dec(v_i_337_);
lean_inc(v_v_342_);
lean_inc(v_k_341_);
v___x_352_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2___redArg(v_entries_338_, v_h_350_, v_depth_334_, v_k_341_, v_v_342_);
v_i_337_ = v___x_351_;
v_entries_338_ = v___x_352_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__9___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_depth_334_ = stack[0].m_num;
lean_object* v_keys_335_ = stack[1].m_obj;
lean_object* v_vals_336_ = stack[2].m_obj;
lean_object* v_i_337_ = stack[3].m_obj;
lean_object* v_entries_338_ = stack[4].m_obj;
lean_object* v_res_354_;
v_res_354_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__9___redArg(v_depth_334_, v_keys_335_, v_vals_336_, v_i_337_, v_entries_338_);
stack->m_obj
 = v_res_354_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__9___redArg___boxed(lean_object* v_depth_355_, lean_object* v_keys_356_, lean_object* v_vals_357_, lean_object* v_i_358_, lean_object* v_entries_359_){
_start:
{
size_t v_depth_boxed_360_; lean_object* v_res_361_; 
v_depth_boxed_360_ = lean_unbox_usize(v_depth_355_);
lean_dec(v_depth_355_);
v_res_361_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__9___redArg(v_depth_boxed_360_, v_keys_356_, v_vals_357_, v_i_358_, v_entries_359_);
lean_dec_ref(v_vals_357_);
lean_dec_ref(v_keys_356_);
return v_res_361_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_x_362_, lean_object* v_x_363_, lean_object* v_x_364_, lean_object* v_x_365_, lean_object* v_x_366_){
_start:
{
size_t v_x_7786__boxed_367_; size_t v_x_7787__boxed_368_; lean_object* v_res_369_; 
v_x_7786__boxed_367_ = lean_unbox_usize(v_x_363_);
lean_dec(v_x_363_);
v_x_7787__boxed_368_ = lean_unbox_usize(v_x_364_);
lean_dec(v_x_364_);
v_res_369_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2___redArg(v_x_362_, v_x_7786__boxed_367_, v_x_7787__boxed_368_, v_x_365_, v_x_366_);
return v_res_369_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0___redArg(lean_object* v_x_370_, lean_object* v_x_371_, lean_object* v_x_372_){
_start:
{
uint64_t v___x_373_; size_t v___x_374_; size_t v___x_375_; lean_object* v___x_376_; 
v___x_373_ = l_Lean_instHashableMVarId_hash(v_x_371_);
v___x_374_ = lean_uint64_to_usize(v___x_373_);
v___x_375_ = ((size_t)1ULL);
v___x_376_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2___redArg(v_x_370_, v___x_374_, v___x_375_, v_x_371_, v_x_372_);
return v___x_376_;
}
}
lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0___redArg(lean_object* v_mvarId_377_, lean_object* v_val_378_, lean_object* v___y_379_){
_start:
{
lean_object* v___x_381_; lean_object* v_mctx_382_; lean_object* v_cache_383_; lean_object* v_zetaDeltaFVarIds_384_; lean_object* v_postponed_385_; lean_object* v_diag_386_; lean_object* v___x_388_; uint8_t v_isShared_389_; uint8_t v_isSharedCheck_416_; 
v___x_381_ = lean_st_ref_take(v___y_379_);
v_mctx_382_ = lean_ctor_get(v___x_381_, 0);
v_cache_383_ = lean_ctor_get(v___x_381_, 1);
v_zetaDeltaFVarIds_384_ = lean_ctor_get(v___x_381_, 2);
v_postponed_385_ = lean_ctor_get(v___x_381_, 3);
v_diag_386_ = lean_ctor_get(v___x_381_, 4);
v_isSharedCheck_416_ = !lean_is_exclusive(v___x_381_);
if (v_isSharedCheck_416_ == 0)
{
v___x_388_ = v___x_381_;
v_isShared_389_ = v_isSharedCheck_416_;
goto v_resetjp_387_;
}
else
{
lean_inc(v_diag_386_);
lean_inc(v_postponed_385_);
lean_inc(v_zetaDeltaFVarIds_384_);
lean_inc(v_cache_383_);
lean_inc(v_mctx_382_);
lean_dec(v___x_381_);
v___x_388_ = lean_box(0);
v_isShared_389_ = v_isSharedCheck_416_;
goto v_resetjp_387_;
}
v_resetjp_387_:
{
lean_object* v_depth_390_; lean_object* v_levelAssignDepth_391_; lean_object* v_lmvarCounter_392_; lean_object* v_mvarCounter_393_; lean_object* v_lDecls_394_; lean_object* v_decls_395_; lean_object* v_userNames_396_; lean_object* v_lAssignment_397_; lean_object* v_eAssignment_398_; lean_object* v_dAssignment_399_; lean_object* v_instanceTypedMVars_400_; lean_object* v_synthNormMemo_401_; lean_object* v___x_403_; uint8_t v_isShared_404_; uint8_t v_isSharedCheck_415_; 
v_depth_390_ = lean_ctor_get(v_mctx_382_, 0);
v_levelAssignDepth_391_ = lean_ctor_get(v_mctx_382_, 1);
v_lmvarCounter_392_ = lean_ctor_get(v_mctx_382_, 2);
v_mvarCounter_393_ = lean_ctor_get(v_mctx_382_, 3);
v_lDecls_394_ = lean_ctor_get(v_mctx_382_, 4);
v_decls_395_ = lean_ctor_get(v_mctx_382_, 5);
v_userNames_396_ = lean_ctor_get(v_mctx_382_, 6);
v_lAssignment_397_ = lean_ctor_get(v_mctx_382_, 7);
v_eAssignment_398_ = lean_ctor_get(v_mctx_382_, 8);
v_dAssignment_399_ = lean_ctor_get(v_mctx_382_, 9);
v_instanceTypedMVars_400_ = lean_ctor_get(v_mctx_382_, 10);
v_synthNormMemo_401_ = lean_ctor_get(v_mctx_382_, 11);
v_isSharedCheck_415_ = !lean_is_exclusive(v_mctx_382_);
if (v_isSharedCheck_415_ == 0)
{
v___x_403_ = v_mctx_382_;
v_isShared_404_ = v_isSharedCheck_415_;
goto v_resetjp_402_;
}
else
{
lean_inc(v_synthNormMemo_401_);
lean_inc(v_instanceTypedMVars_400_);
lean_inc(v_dAssignment_399_);
lean_inc(v_eAssignment_398_);
lean_inc(v_lAssignment_397_);
lean_inc(v_userNames_396_);
lean_inc(v_decls_395_);
lean_inc(v_lDecls_394_);
lean_inc(v_mvarCounter_393_);
lean_inc(v_lmvarCounter_392_);
lean_inc(v_levelAssignDepth_391_);
lean_inc(v_depth_390_);
lean_dec(v_mctx_382_);
v___x_403_ = lean_box(0);
v_isShared_404_ = v_isSharedCheck_415_;
goto v_resetjp_402_;
}
v_resetjp_402_:
{
lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_408_; 
v___x_405_ = lean_box(0);
v___x_406_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0___redArg(v_eAssignment_398_, v_mvarId_377_, v_val_378_);
if (v_isShared_404_ == 0)
{
lean_ctor_set(v___x_403_, 8, v___x_406_);
v___x_408_ = v___x_403_;
goto v_reusejp_407_;
}
else
{
lean_object* v_reuseFailAlloc_414_; 
v_reuseFailAlloc_414_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_414_, 0, v_depth_390_);
lean_ctor_set(v_reuseFailAlloc_414_, 1, v_levelAssignDepth_391_);
lean_ctor_set(v_reuseFailAlloc_414_, 2, v_lmvarCounter_392_);
lean_ctor_set(v_reuseFailAlloc_414_, 3, v_mvarCounter_393_);
lean_ctor_set(v_reuseFailAlloc_414_, 4, v_lDecls_394_);
lean_ctor_set(v_reuseFailAlloc_414_, 5, v_decls_395_);
lean_ctor_set(v_reuseFailAlloc_414_, 6, v_userNames_396_);
lean_ctor_set(v_reuseFailAlloc_414_, 7, v_lAssignment_397_);
lean_ctor_set(v_reuseFailAlloc_414_, 8, v___x_406_);
lean_ctor_set(v_reuseFailAlloc_414_, 9, v_dAssignment_399_);
lean_ctor_set(v_reuseFailAlloc_414_, 10, v_instanceTypedMVars_400_);
lean_ctor_set(v_reuseFailAlloc_414_, 11, v_synthNormMemo_401_);
v___x_408_ = v_reuseFailAlloc_414_;
goto v_reusejp_407_;
}
v_reusejp_407_:
{
lean_object* v___x_410_; 
if (v_isShared_389_ == 0)
{
lean_ctor_set(v___x_388_, 0, v___x_408_);
v___x_410_ = v___x_388_;
goto v_reusejp_409_;
}
else
{
lean_object* v_reuseFailAlloc_413_; 
v_reuseFailAlloc_413_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_413_, 0, v___x_408_);
lean_ctor_set(v_reuseFailAlloc_413_, 1, v_cache_383_);
lean_ctor_set(v_reuseFailAlloc_413_, 2, v_zetaDeltaFVarIds_384_);
lean_ctor_set(v_reuseFailAlloc_413_, 3, v_postponed_385_);
lean_ctor_set(v_reuseFailAlloc_413_, 4, v_diag_386_);
v___x_410_ = v_reuseFailAlloc_413_;
goto v_reusejp_409_;
}
v_reusejp_409_:
{
lean_object* v___x_411_; lean_object* v___x_412_; 
v___x_411_ = lean_st_ref_put(v___y_379_, v___x_410_);
v___x_412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_412_, 0, v___x_405_);
return v___x_412_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_377_ = stack[0].m_obj;
lean_object* v_val_378_ = stack[1].m_obj;
lean_object* v___y_379_ = stack[2].m_obj;
lean_object* v_res_417_;
v_res_417_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0___redArg(v_mvarId_377_, v_val_378_, v___y_379_);
stack->m_obj
 = v_res_417_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0___redArg___boxed(lean_object* v_mvarId_418_, lean_object* v_val_419_, lean_object* v___y_420_, lean_object* v___y_421_){
_start:
{
lean_object* v_res_422_; 
v_res_422_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0___redArg(v_mvarId_418_, v_val_419_, v___y_420_);
lean_dec(v___y_420_);
return v_res_422_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1_spec__2(lean_object* v_msgData_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_){
_start:
{
lean_object* v___x_429_; lean_object* v_env_430_; uint8_t v___x_431_; lean_object* v_env_432_; lean_object* v___x_433_; lean_object* v_toCold_434_; lean_object* v_mctx_435_; lean_object* v_lctx_436_; lean_object* v_options_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; 
v___x_429_ = lean_st_ref_get(v___y_427_);
v_env_430_ = lean_ctor_get(v___x_429_, 0);
lean_inc_ref(v_env_430_);
lean_dec(v___x_429_);
v___x_431_ = 0;
v_env_432_ = l_Lean_Environment_setRecordingDeps(v_env_430_, v___x_431_);
v___x_433_ = lean_st_ref_get(v___y_425_);
v_toCold_434_ = lean_ctor_get(v___y_426_, 0);
v_mctx_435_ = lean_ctor_get(v___x_433_, 0);
lean_inc_ref(v_mctx_435_);
lean_dec(v___x_433_);
v_lctx_436_ = lean_ctor_get(v___y_424_, 2);
v_options_437_ = lean_ctor_get(v_toCold_434_, 2);
lean_inc_ref(v_options_437_);
lean_inc_ref(v_lctx_436_);
v___x_438_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_438_, 0, v_env_432_);
lean_ctor_set(v___x_438_, 1, v_mctx_435_);
lean_ctor_set(v___x_438_, 2, v_lctx_436_);
lean_ctor_set(v___x_438_, 3, v_options_437_);
v___x_439_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_439_, 0, v___x_438_);
lean_ctor_set(v___x_439_, 1, v_msgData_423_);
v___x_440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_440_, 0, v___x_439_);
return v___x_440_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_423_ = stack[0].m_obj;
lean_object* v___y_424_ = stack[1].m_obj;
lean_object* v___y_425_ = stack[2].m_obj;
lean_object* v___y_426_ = stack[3].m_obj;
lean_object* v___y_427_ = stack[4].m_obj;
lean_object* v_res_441_;
v_res_441_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1_spec__2(v_msgData_423_, v___y_424_, v___y_425_, v___y_426_, v___y_427_);
stack->m_obj
 = v_res_441_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1_spec__2___boxed(lean_object* v_msgData_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_){
_start:
{
lean_object* v_res_448_; 
v_res_448_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1_spec__2(v_msgData_442_, v___y_443_, v___y_444_, v___y_445_, v___y_446_);
lean_dec(v___y_446_);
lean_dec_ref(v___y_445_);
lean_dec(v___y_444_);
lean_dec_ref(v___y_443_);
return v_res_448_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1___closed__0(void){
_start:
{
lean_object* v___x_449_; double v___x_450_; 
v___x_449_ = lean_unsigned_to_nat(0u);
v___x_450_ = lean_float_of_nat(v___x_449_);
return v___x_450_;
}
}
lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1(lean_object* v_cls_454_, lean_object* v_msg_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_){
_start:
{
lean_object* v_ref_461_; lean_object* v___x_462_; lean_object* v_a_463_; lean_object* v___x_465_; uint8_t v_isShared_466_; uint8_t v_isSharedCheck_508_; 
v_ref_461_ = lean_ctor_get(v___y_458_, 2);
v___x_462_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1_spec__2(v_msg_455_, v___y_456_, v___y_457_, v___y_458_, v___y_459_);
v_a_463_ = lean_ctor_get(v___x_462_, 0);
v_isSharedCheck_508_ = !lean_is_exclusive(v___x_462_);
if (v_isSharedCheck_508_ == 0)
{
v___x_465_ = v___x_462_;
v_isShared_466_ = v_isSharedCheck_508_;
goto v_resetjp_464_;
}
else
{
lean_inc(v_a_463_);
lean_dec(v___x_462_);
v___x_465_ = lean_box(0);
v_isShared_466_ = v_isSharedCheck_508_;
goto v_resetjp_464_;
}
v_resetjp_464_:
{
lean_object* v___x_467_; lean_object* v_traceState_468_; lean_object* v_env_469_; lean_object* v_nextMacroScope_470_; lean_object* v_ngen_471_; lean_object* v_auxDeclNGen_472_; lean_object* v_cache_473_; lean_object* v_recordedDeps_474_; lean_object* v_messages_475_; lean_object* v_infoState_476_; lean_object* v_snapshotTasks_477_; lean_object* v___x_479_; uint8_t v_isShared_480_; uint8_t v_isSharedCheck_507_; 
v___x_467_ = lean_st_ref_take(v___y_459_);
v_traceState_468_ = lean_ctor_get(v___x_467_, 4);
v_env_469_ = lean_ctor_get(v___x_467_, 0);
v_nextMacroScope_470_ = lean_ctor_get(v___x_467_, 1);
v_ngen_471_ = lean_ctor_get(v___x_467_, 2);
v_auxDeclNGen_472_ = lean_ctor_get(v___x_467_, 3);
v_cache_473_ = lean_ctor_get(v___x_467_, 5);
v_recordedDeps_474_ = lean_ctor_get(v___x_467_, 6);
v_messages_475_ = lean_ctor_get(v___x_467_, 7);
v_infoState_476_ = lean_ctor_get(v___x_467_, 8);
v_snapshotTasks_477_ = lean_ctor_get(v___x_467_, 9);
v_isSharedCheck_507_ = !lean_is_exclusive(v___x_467_);
if (v_isSharedCheck_507_ == 0)
{
v___x_479_ = v___x_467_;
v_isShared_480_ = v_isSharedCheck_507_;
goto v_resetjp_478_;
}
else
{
lean_inc(v_snapshotTasks_477_);
lean_inc(v_infoState_476_);
lean_inc(v_messages_475_);
lean_inc(v_recordedDeps_474_);
lean_inc(v_cache_473_);
lean_inc(v_traceState_468_);
lean_inc(v_auxDeclNGen_472_);
lean_inc(v_ngen_471_);
lean_inc(v_nextMacroScope_470_);
lean_inc(v_env_469_);
lean_dec(v___x_467_);
v___x_479_ = lean_box(0);
v_isShared_480_ = v_isSharedCheck_507_;
goto v_resetjp_478_;
}
v_resetjp_478_:
{
uint64_t v_tid_481_; lean_object* v_traces_482_; lean_object* v___x_484_; uint8_t v_isShared_485_; uint8_t v_isSharedCheck_506_; 
v_tid_481_ = lean_ctor_get_uint64(v_traceState_468_, sizeof(void*)*1);
v_traces_482_ = lean_ctor_get(v_traceState_468_, 0);
v_isSharedCheck_506_ = !lean_is_exclusive(v_traceState_468_);
if (v_isSharedCheck_506_ == 0)
{
v___x_484_ = v_traceState_468_;
v_isShared_485_ = v_isSharedCheck_506_;
goto v_resetjp_483_;
}
else
{
lean_inc(v_traces_482_);
lean_dec(v_traceState_468_);
v___x_484_ = lean_box(0);
v_isShared_485_ = v_isSharedCheck_506_;
goto v_resetjp_483_;
}
v_resetjp_483_:
{
lean_object* v___x_486_; lean_object* v___x_487_; double v___x_488_; uint8_t v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_497_; 
v___x_486_ = lean_box(0);
v___x_487_ = lean_box(0);
v___x_488_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1___closed__0);
v___x_489_ = 0;
v___x_490_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1___closed__1));
v___x_491_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_491_, 0, v_cls_454_);
lean_ctor_set(v___x_491_, 1, v___x_487_);
lean_ctor_set(v___x_491_, 2, v___x_490_);
lean_ctor_set_float(v___x_491_, sizeof(void*)*3, v___x_488_);
lean_ctor_set_float(v___x_491_, sizeof(void*)*3 + 8, v___x_488_);
lean_ctor_set_uint8(v___x_491_, sizeof(void*)*3 + 16, v___x_489_);
v___x_492_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1___closed__2));
v___x_493_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_493_, 0, v___x_491_);
lean_ctor_set(v___x_493_, 1, v_a_463_);
lean_ctor_set(v___x_493_, 2, v___x_492_);
lean_inc(v_ref_461_);
v___x_494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_494_, 0, v_ref_461_);
lean_ctor_set(v___x_494_, 1, v___x_493_);
v___x_495_ = l_Lean_PersistentArray_push___redArg(v_traces_482_, v___x_494_);
if (v_isShared_485_ == 0)
{
lean_ctor_set(v___x_484_, 0, v___x_495_);
v___x_497_ = v___x_484_;
goto v_reusejp_496_;
}
else
{
lean_object* v_reuseFailAlloc_505_; 
v_reuseFailAlloc_505_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_505_, 0, v___x_495_);
lean_ctor_set_uint64(v_reuseFailAlloc_505_, sizeof(void*)*1, v_tid_481_);
v___x_497_ = v_reuseFailAlloc_505_;
goto v_reusejp_496_;
}
v_reusejp_496_:
{
lean_object* v___x_499_; 
if (v_isShared_480_ == 0)
{
lean_ctor_set(v___x_479_, 4, v___x_497_);
v___x_499_ = v___x_479_;
goto v_reusejp_498_;
}
else
{
lean_object* v_reuseFailAlloc_504_; 
v_reuseFailAlloc_504_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_504_, 0, v_env_469_);
lean_ctor_set(v_reuseFailAlloc_504_, 1, v_nextMacroScope_470_);
lean_ctor_set(v_reuseFailAlloc_504_, 2, v_ngen_471_);
lean_ctor_set(v_reuseFailAlloc_504_, 3, v_auxDeclNGen_472_);
lean_ctor_set(v_reuseFailAlloc_504_, 4, v___x_497_);
lean_ctor_set(v_reuseFailAlloc_504_, 5, v_cache_473_);
lean_ctor_set(v_reuseFailAlloc_504_, 6, v_recordedDeps_474_);
lean_ctor_set(v_reuseFailAlloc_504_, 7, v_messages_475_);
lean_ctor_set(v_reuseFailAlloc_504_, 8, v_infoState_476_);
lean_ctor_set(v_reuseFailAlloc_504_, 9, v_snapshotTasks_477_);
v___x_499_ = v_reuseFailAlloc_504_;
goto v_reusejp_498_;
}
v_reusejp_498_:
{
lean_object* v___x_500_; lean_object* v___x_502_; 
v___x_500_ = lean_st_ref_put(v___y_459_, v___x_499_);
if (v_isShared_466_ == 0)
{
lean_ctor_set(v___x_465_, 0, v___x_486_);
v___x_502_ = v___x_465_;
goto v_reusejp_501_;
}
else
{
lean_object* v_reuseFailAlloc_503_; 
v_reuseFailAlloc_503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_503_, 0, v___x_486_);
v___x_502_ = v_reuseFailAlloc_503_;
goto v_reusejp_501_;
}
v_reusejp_501_:
{
return v___x_502_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_454_ = stack[0].m_obj;
lean_object* v_msg_455_ = stack[1].m_obj;
lean_object* v___y_456_ = stack[2].m_obj;
lean_object* v___y_457_ = stack[3].m_obj;
lean_object* v___y_458_ = stack[4].m_obj;
lean_object* v___y_459_ = stack[5].m_obj;
lean_object* v_res_509_;
v_res_509_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1(v_cls_454_, v_msg_455_, v___y_456_, v___y_457_, v___y_458_, v___y_459_);
stack->m_obj
 = v_res_509_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1___boxed(lean_object* v_cls_510_, lean_object* v_msg_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_){
_start:
{
lean_object* v_res_517_; 
v_res_517_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1(v_cls_510_, v_msg_511_, v___y_512_, v___y_513_, v___y_514_, v___y_515_);
lean_dec(v___y_515_);
lean_dec_ref(v___y_514_);
lean_dec(v___y_513_);
lean_dec_ref(v___y_512_);
return v_res_517_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__3(size_t v_sz_518_, size_t v_i_519_, lean_object* v_bs_520_){
_start:
{
uint8_t v___x_521_; 
v___x_521_ = lean_usize_dec_lt(v_i_519_, v_sz_518_);
if (v___x_521_ == 0)
{
return v_bs_520_;
}
else
{
lean_object* v_v_522_; lean_object* v___x_523_; lean_object* v_bs_x27_524_; lean_object* v___x_525_; size_t v___x_526_; size_t v___x_527_; lean_object* v___x_528_; 
v_v_522_ = lean_array_uget(v_bs_520_, v_i_519_);
v___x_523_ = lean_unsigned_to_nat(0u);
v_bs_x27_524_ = lean_array_uset(v_bs_520_, v_i_519_, v___x_523_);
v___x_525_ = l_Lean_mkFVar(v_v_522_);
v___x_526_ = ((size_t)1ULL);
v___x_527_ = lean_usize_add(v_i_519_, v___x_526_);
v___x_528_ = lean_array_uset(v_bs_x27_524_, v_i_519_, v___x_525_);
v_i_519_ = v___x_527_;
v_bs_520_ = v___x_528_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__3_0interp(lean_interpreter_value* stack)
{
size_t v_sz_518_ = stack[0].m_num;
size_t v_i_519_ = stack[1].m_num;
lean_object* v_bs_520_ = stack[2].m_obj;
lean_object* v_res_530_;
v_res_530_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__3(v_sz_518_, v_i_519_, v_bs_520_);
stack->m_obj
 = v_res_530_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__3___boxed(lean_object* v_sz_531_, lean_object* v_i_532_, lean_object* v_bs_533_){
_start:
{
size_t v_sz_boxed_534_; size_t v_i_boxed_535_; lean_object* v_res_536_; 
v_sz_boxed_534_ = lean_unbox_usize(v_sz_531_);
lean_dec(v_sz_531_);
v_i_boxed_535_ = lean_unbox_usize(v_i_532_);
lean_dec(v_i_532_);
v_res_536_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__3(v_sz_boxed_534_, v_i_boxed_535_, v_bs_533_);
return v_res_536_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5(void){
_start:
{
lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; 
v___x_546_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__2));
v___x_547_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__4));
v___x_548_ = l_Lean_Name_append(v___x_547_, v___x_546_);
return v___x_548_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__7(void){
_start:
{
lean_object* v___x_550_; lean_object* v___x_551_; 
v___x_550_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__6));
v___x_551_ = l_Lean_stringToMessageData(v___x_550_);
return v___x_551_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__9(void){
_start:
{
lean_object* v___x_553_; lean_object* v___x_554_; 
v___x_553_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__8));
v___x_554_ = l_Lean_stringToMessageData(v___x_553_);
return v___x_554_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__11(void){
_start:
{
lean_object* v___x_556_; lean_object* v___x_557_; 
v___x_556_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__10));
v___x_557_ = l_Lean_stringToMessageData(v___x_556_);
return v___x_557_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__15(void){
_start:
{
lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; 
v___x_561_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__14));
v___x_562_ = lean_unsigned_to_nat(15u);
v___x_563_ = lean_unsigned_to_nat(120u);
v___x_564_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__13));
v___x_565_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__12));
v___x_566_ = l_mkPanicMessageWithDecl(v___x_565_, v___x_564_, v___x_563_, v___x_562_, v___x_561_);
return v___x_566_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop(lean_object* v_mvarId_567_, lean_object* v_givenNames_568_, lean_object* v_recursorInfo_569_, lean_object* v_reverted_570_, lean_object* v_major_571_, lean_object* v_indices_572_, lean_object* v_baseSubst_573_, lean_object* v_initialArity_574_, lean_object* v_numMinors_575_, lean_object* v_pos_576_, lean_object* v_minorIdx_577_, lean_object* v_recursor_578_, lean_object* v_recursorType_579_, uint8_t v_consumedMajor_580_, lean_object* v_subgoals_581_, lean_object* v_a_582_, lean_object* v_a_583_, lean_object* v_a_584_, lean_object* v_a_585_){
_start:
{
lean_object* v___y_588_; lean_object* v___y_589_; lean_object* v___y_590_; lean_object* v___y_591_; lean_object* v___y_645_; lean_object* v___y_646_; uint8_t v___y_647_; lean_object* v___y_648_; lean_object* v___y_649_; lean_object* v___y_650_; lean_object* v___y_651_; lean_object* v___y_652_; lean_object* v___y_653_; lean_object* v___y_654_; uint8_t v___y_655_; lean_object* v___y_656_; lean_object* v___y_657_; lean_object* v___y_658_; lean_object* v___y_659_; uint8_t v___y_660_; uint8_t v___y_696_; uint8_t v___y_697_; lean_object* v___y_698_; lean_object* v___y_699_; lean_object* v___y_700_; lean_object* v___y_701_; lean_object* v___y_702_; lean_object* v___y_703_; lean_object* v___y_704_; lean_object* v___y_705_; lean_object* v___y_706_; lean_object* v___y_707_; lean_object* v___y_708_; lean_object* v___y_709_; lean_object* v___y_710_; uint8_t v___y_728_; lean_object* v___y_729_; lean_object* v_fst_730_; lean_object* v_snd_731_; lean_object* v___y_748_; uint8_t v___y_749_; lean_object* v___y_750_; lean_object* v___x_762_; 
v___x_762_ = l_Lean_Meta_whnfForall(v_recursorType_579_, v_a_582_, v_a_583_, v_a_584_, v_a_585_);
if (lean_obj_tag(v___x_762_) == 0)
{
lean_object* v_a_763_; lean_object* v___y_765_; uint8_t v___y_766_; lean_object* v___y_767_; lean_object* v___y_768_; lean_object* v___y_769_; lean_object* v___y_770_; lean_object* v___y_771_; uint8_t v___y_772_; lean_object* v___y_773_; lean_object* v___y_774_; lean_object* v___y_775_; lean_object* v___y_776_; lean_object* v___y_777_; lean_object* v___y_778_; uint8_t v___y_822_; uint8_t v___y_823_; lean_object* v___y_824_; lean_object* v___y_825_; lean_object* v___y_826_; lean_object* v___y_827_; lean_object* v___y_828_; lean_object* v___y_829_; lean_object* v___y_830_; lean_object* v___y_831_; uint8_t v___y_843_; lean_object* v___y_844_; lean_object* v___y_845_; lean_object* v___y_846_; lean_object* v___y_847_; lean_object* v___y_848_; lean_object* v___y_849_; lean_object* v___y_850_; uint8_t v___y_851_; uint8_t v___y_921_; lean_object* v___y_922_; lean_object* v___y_923_; uint8_t v___y_924_; lean_object* v___y_925_; lean_object* v___y_926_; lean_object* v___y_927_; lean_object* v___y_928_; lean_object* v___y_929_; lean_object* v___y_935_; uint8_t v___y_936_; lean_object* v___y_937_; lean_object* v___y_938_; lean_object* v___y_939_; lean_object* v___y_940_; uint8_t v___y_952_; uint8_t v___x_999_; 
v_a_763_ = lean_ctor_get(v___x_762_, 0);
lean_inc(v_a_763_);
lean_dec_ref_known(v___x_762_, 1);
v___x_999_ = l_Lean_Expr_isForall(v_a_763_);
if (v___x_999_ == 0)
{
v___y_952_ = v___x_999_;
goto v___jp_951_;
}
else
{
lean_object* v_numArgs_1000_; uint8_t v___x_1001_; 
v_numArgs_1000_ = lean_ctor_get(v_recursorInfo_569_, 3);
v___x_1001_ = lean_nat_dec_lt(v_pos_576_, v_numArgs_1000_);
v___y_952_ = v___x_1001_;
goto v___jp_951_;
}
v___jp_764_:
{
lean_object* v___x_779_; 
v___x_779_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___y_770_, v___y_769_, v___y_765_, v___y_774_, v___y_767_, v___y_777_);
if (lean_obj_tag(v___x_779_) == 0)
{
lean_object* v_a_780_; lean_object* v___x_781_; lean_object* v___x_782_; 
v_a_780_ = lean_ctor_get(v___x_779_, 0);
lean_inc_n(v_a_780_, 2);
lean_dec_ref_known(v___x_779_, 1);
v___x_781_ = l_Lean_Expr_app___override(v_recursor_578_, v_a_780_);
lean_inc(v_mvarId_567_);
v___x_782_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTypeBody(v_mvarId_567_, v_a_763_, v_a_780_, v___y_765_, v___y_774_, v___y_767_, v___y_777_);
if (lean_obj_tag(v___x_782_) == 0)
{
lean_object* v_toCold_783_; lean_object* v_options_784_; uint8_t v_hasTrace_785_; 
v_toCold_783_ = lean_ctor_get(v___y_767_, 0);
v_options_784_ = lean_ctor_get(v_toCold_783_, 2);
v_hasTrace_785_ = lean_ctor_get_uint8(v_options_784_, sizeof(void*)*1);
if (v_hasTrace_785_ == 0)
{
lean_object* v_a_786_; 
v_a_786_ = lean_ctor_get(v___x_782_, 0);
lean_inc(v_a_786_);
lean_dec_ref_known(v___x_782_, 1);
v___y_696_ = v___y_772_;
v___y_697_ = v___y_766_;
v___y_698_ = v___y_773_;
v___y_699_ = v_a_786_;
v___y_700_ = v___x_781_;
v___y_701_ = v___y_778_;
v___y_702_ = v_a_780_;
v___y_703_ = v___y_768_;
v___y_704_ = v___y_775_;
v___y_705_ = v___y_776_;
v___y_706_ = v___y_771_;
v___y_707_ = v___y_765_;
v___y_708_ = v___y_774_;
v___y_709_ = v___y_767_;
v___y_710_ = v___y_777_;
goto v___jp_695_;
}
else
{
lean_object* v_a_787_; lean_object* v_inheritedTraceOptions_788_; lean_object* v___x_789_; lean_object* v___x_790_; uint8_t v___x_791_; 
v_a_787_ = lean_ctor_get(v___x_782_, 0);
lean_inc(v_a_787_);
lean_dec_ref_known(v___x_782_, 1);
v_inheritedTraceOptions_788_ = lean_ctor_get(v_toCold_783_, 11);
v___x_789_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__2));
v___x_790_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5);
v___x_791_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_788_, v_options_784_, v___x_790_);
if (v___x_791_ == 0)
{
v___y_696_ = v___y_772_;
v___y_697_ = v___y_766_;
v___y_698_ = v___y_773_;
v___y_699_ = v_a_787_;
v___y_700_ = v___x_781_;
v___y_701_ = v___y_778_;
v___y_702_ = v_a_780_;
v___y_703_ = v___y_768_;
v___y_704_ = v___y_775_;
v___y_705_ = v___y_776_;
v___y_706_ = v___y_771_;
v___y_707_ = v___y_765_;
v___y_708_ = v___y_774_;
v___y_709_ = v___y_767_;
v___y_710_ = v___y_777_;
goto v___jp_695_;
}
else
{
lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; 
v___x_792_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__11, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__11_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__11);
v___x_793_ = l_Lean_Expr_fvarId_x21(v_major_571_);
v___x_794_ = l_Lean_MessageData_ofName(v___x_793_);
v___x_795_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_795_, 0, v___x_792_);
lean_ctor_set(v___x_795_, 1, v___x_794_);
v___x_796_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1(v___x_789_, v___x_795_, v___y_765_, v___y_774_, v___y_767_, v___y_777_);
if (lean_obj_tag(v___x_796_) == 0)
{
lean_dec_ref_known(v___x_796_, 1);
v___y_696_ = v___y_772_;
v___y_697_ = v___y_766_;
v___y_698_ = v___y_773_;
v___y_699_ = v_a_787_;
v___y_700_ = v___x_781_;
v___y_701_ = v___y_778_;
v___y_702_ = v_a_780_;
v___y_703_ = v___y_768_;
v___y_704_ = v___y_775_;
v___y_705_ = v___y_776_;
v___y_706_ = v___y_771_;
v___y_707_ = v___y_765_;
v___y_708_ = v___y_774_;
v___y_709_ = v___y_767_;
v___y_710_ = v___y_777_;
goto v___jp_695_;
}
else
{
lean_object* v_a_797_; lean_object* v___x_799_; uint8_t v_isShared_800_; uint8_t v_isSharedCheck_804_; 
lean_dec(v_a_787_);
lean_dec_ref(v___x_781_);
lean_dec(v_a_780_);
lean_dec_ref(v___y_778_);
lean_dec(v___y_776_);
lean_dec(v___y_775_);
lean_dec(v___y_771_);
lean_dec(v___y_768_);
lean_dec_ref(v_subgoals_581_);
lean_dec(v_minorIdx_577_);
lean_dec(v_pos_576_);
lean_dec(v_baseSubst_573_);
lean_dec_ref(v_major_571_);
lean_dec(v_mvarId_567_);
v_a_797_ = lean_ctor_get(v___x_796_, 0);
v_isSharedCheck_804_ = !lean_is_exclusive(v___x_796_);
if (v_isSharedCheck_804_ == 0)
{
v___x_799_ = v___x_796_;
v_isShared_800_ = v_isSharedCheck_804_;
goto v_resetjp_798_;
}
else
{
lean_inc(v_a_797_);
lean_dec(v___x_796_);
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
}
}
else
{
lean_object* v_a_805_; lean_object* v___x_807_; uint8_t v_isShared_808_; uint8_t v_isSharedCheck_812_; 
lean_dec_ref(v___x_781_);
lean_dec(v_a_780_);
lean_dec_ref(v___y_778_);
lean_dec(v___y_776_);
lean_dec(v___y_775_);
lean_dec(v___y_771_);
lean_dec(v___y_768_);
lean_dec_ref(v_subgoals_581_);
lean_dec(v_minorIdx_577_);
lean_dec(v_pos_576_);
lean_dec(v_baseSubst_573_);
lean_dec_ref(v_major_571_);
lean_dec(v_mvarId_567_);
v_a_805_ = lean_ctor_get(v___x_782_, 0);
v_isSharedCheck_812_ = !lean_is_exclusive(v___x_782_);
if (v_isSharedCheck_812_ == 0)
{
v___x_807_ = v___x_782_;
v_isShared_808_ = v_isSharedCheck_812_;
goto v_resetjp_806_;
}
else
{
lean_inc(v_a_805_);
lean_dec(v___x_782_);
v___x_807_ = lean_box(0);
v_isShared_808_ = v_isSharedCheck_812_;
goto v_resetjp_806_;
}
v_resetjp_806_:
{
lean_object* v___x_810_; 
if (v_isShared_808_ == 0)
{
v___x_810_ = v___x_807_;
goto v_reusejp_809_;
}
else
{
lean_object* v_reuseFailAlloc_811_; 
v_reuseFailAlloc_811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_811_, 0, v_a_805_);
v___x_810_ = v_reuseFailAlloc_811_;
goto v_reusejp_809_;
}
v_reusejp_809_:
{
return v___x_810_;
}
}
}
}
else
{
lean_object* v_a_813_; lean_object* v___x_815_; uint8_t v_isShared_816_; uint8_t v_isSharedCheck_820_; 
lean_dec_ref(v___y_778_);
lean_dec(v___y_776_);
lean_dec(v___y_775_);
lean_dec(v___y_771_);
lean_dec(v___y_768_);
lean_dec(v_a_763_);
lean_dec_ref(v_subgoals_581_);
lean_dec_ref(v_recursor_578_);
lean_dec(v_minorIdx_577_);
lean_dec(v_pos_576_);
lean_dec(v_baseSubst_573_);
lean_dec_ref(v_major_571_);
lean_dec(v_mvarId_567_);
v_a_813_ = lean_ctor_get(v___x_779_, 0);
v_isSharedCheck_820_ = !lean_is_exclusive(v___x_779_);
if (v_isSharedCheck_820_ == 0)
{
v___x_815_ = v___x_779_;
v_isShared_816_ = v_isSharedCheck_820_;
goto v_resetjp_814_;
}
else
{
lean_inc(v_a_813_);
lean_dec(v___x_779_);
v___x_815_ = lean_box(0);
v_isShared_816_ = v_isSharedCheck_820_;
goto v_resetjp_814_;
}
v_resetjp_814_:
{
lean_object* v___x_818_; 
if (v_isShared_816_ == 0)
{
v___x_818_ = v___x_815_;
goto v_reusejp_817_;
}
else
{
lean_object* v_reuseFailAlloc_819_; 
v_reuseFailAlloc_819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_819_, 0, v_a_813_);
v___x_818_ = v_reuseFailAlloc_819_;
goto v_reusejp_817_;
}
v_reusejp_817_:
{
return v___x_818_;
}
}
}
}
v___jp_821_:
{
lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; uint8_t v___x_838_; 
v___x_832_ = lean_nat_sub(v___y_825_, v_initialArity_574_);
lean_dec(v___y_825_);
v___x_833_ = lean_array_get_size(v_reverted_570_);
v___x_834_ = lean_array_get_size(v_indices_572_);
v___x_835_ = lean_nat_sub(v___x_833_, v___x_834_);
v___x_836_ = lean_nat_sub(v___x_835_, v___y_824_);
lean_dec(v___x_835_);
v___x_837_ = lean_array_get_size(v_givenNames_568_);
v___x_838_ = lean_nat_dec_lt(v_minorIdx_577_, v___x_837_);
if (v___x_838_ == 0)
{
lean_object* v___x_839_; lean_object* v___x_840_; 
v___x_839_ = lean_box(0);
v___x_840_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_840_, 0, v___x_839_);
lean_ctor_set_uint8(v___x_840_, sizeof(void*)*1, v___x_838_);
v___y_765_ = v___y_828_;
v___y_766_ = v___y_823_;
v___y_767_ = v___y_830_;
v___y_768_ = v___x_833_;
v___y_769_ = v___y_826_;
v___y_770_ = v___y_827_;
v___y_771_ = v___x_836_;
v___y_772_ = v___y_822_;
v___y_773_ = v___y_824_;
v___y_774_ = v___y_829_;
v___y_775_ = v___x_832_;
v___y_776_ = v___x_834_;
v___y_777_ = v___y_831_;
v___y_778_ = v___x_840_;
goto v___jp_764_;
}
else
{
lean_object* v___x_841_; 
v___x_841_ = lean_array_fget_borrowed(v_givenNames_568_, v_minorIdx_577_);
lean_inc(v___x_841_);
v___y_765_ = v___y_828_;
v___y_766_ = v___y_823_;
v___y_767_ = v___y_830_;
v___y_768_ = v___x_833_;
v___y_769_ = v___y_826_;
v___y_770_ = v___y_827_;
v___y_771_ = v___x_836_;
v___y_772_ = v___y_822_;
v___y_773_ = v___y_824_;
v___y_774_ = v___y_829_;
v___y_775_ = v___x_832_;
v___y_776_ = v___x_834_;
v___y_777_ = v___y_831_;
v___y_778_ = v___x_841_;
goto v___jp_764_;
}
}
v___jp_842_:
{
if (v___y_851_ == 0)
{
lean_object* v___x_852_; uint8_t v___x_853_; 
lean_inc_ref(v___y_846_);
v___x_852_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTargetArity(v___y_846_);
v___x_853_ = lean_nat_dec_lt(v___x_852_, v_initialArity_574_);
if (v___x_853_ == 0)
{
v___y_822_ = v___y_843_;
v___y_823_ = v___y_851_;
v___y_824_ = v___y_844_;
v___y_825_ = v___x_852_;
v___y_826_ = v___y_845_;
v___y_827_ = v___y_846_;
v___y_828_ = v___y_848_;
v___y_829_ = v___y_847_;
v___y_830_ = v___y_850_;
v___y_831_ = v___y_849_;
goto v___jp_821_;
}
else
{
lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; 
v___x_854_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1));
v___x_855_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9);
lean_inc(v_mvarId_567_);
v___x_856_ = l_Lean_Meta_throwTacticEx___redArg(v___x_854_, v_mvarId_567_, v___x_855_, v___y_848_, v___y_847_, v___y_850_, v___y_849_);
if (lean_obj_tag(v___x_856_) == 0)
{
lean_dec_ref_known(v___x_856_, 1);
v___y_822_ = v___y_843_;
v___y_823_ = v___y_851_;
v___y_824_ = v___y_844_;
v___y_825_ = v___x_852_;
v___y_826_ = v___y_845_;
v___y_827_ = v___y_846_;
v___y_828_ = v___y_848_;
v___y_829_ = v___y_847_;
v___y_830_ = v___y_850_;
v___y_831_ = v___y_849_;
goto v___jp_821_;
}
else
{
lean_object* v_a_857_; lean_object* v___x_859_; uint8_t v_isShared_860_; uint8_t v_isSharedCheck_864_; 
lean_dec(v___x_852_);
lean_dec_ref(v___y_846_);
lean_dec(v___y_845_);
lean_dec(v_a_763_);
lean_dec_ref(v_subgoals_581_);
lean_dec_ref(v_recursor_578_);
lean_dec(v_minorIdx_577_);
lean_dec(v_pos_576_);
lean_dec(v_baseSubst_573_);
lean_dec_ref(v_major_571_);
lean_dec(v_mvarId_567_);
v_a_857_ = lean_ctor_get(v___x_856_, 0);
v_isSharedCheck_864_ = !lean_is_exclusive(v___x_856_);
if (v_isSharedCheck_864_ == 0)
{
v___x_859_ = v___x_856_;
v_isShared_860_ = v_isSharedCheck_864_;
goto v_resetjp_858_;
}
else
{
lean_inc(v_a_857_);
lean_dec(v___x_856_);
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
}
else
{
lean_object* v___x_865_; lean_object* v___x_866_; 
v___x_865_ = lean_box(0);
lean_inc_ref(v___y_846_);
v___x_866_ = l_Lean_Meta_synthInstance_x3f(v___y_846_, v___x_865_, v___y_848_, v___y_847_, v___y_850_, v___y_849_);
if (lean_obj_tag(v___x_866_) == 0)
{
lean_object* v_a_867_; 
v_a_867_ = lean_ctor_get(v___x_866_, 0);
lean_inc(v_a_867_);
lean_dec_ref_known(v___x_866_, 1);
if (lean_obj_tag(v_a_867_) == 0)
{
lean_object* v___x_868_; 
v___x_868_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___y_846_, v___y_845_, v___y_848_, v___y_847_, v___y_850_, v___y_849_);
if (lean_obj_tag(v___x_868_) == 0)
{
lean_object* v_a_869_; lean_object* v___x_870_; lean_object* v___x_871_; 
v_a_869_ = lean_ctor_get(v___x_868_, 0);
lean_inc_n(v_a_869_, 2);
lean_dec_ref_known(v___x_868_, 1);
v___x_870_ = l_Lean_Expr_app___override(v_recursor_578_, v_a_869_);
lean_inc(v_mvarId_567_);
v___x_871_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTypeBody(v_mvarId_567_, v_a_763_, v_a_869_, v___y_848_, v___y_847_, v___y_850_, v___y_849_);
if (lean_obj_tag(v___x_871_) == 0)
{
lean_object* v_a_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; 
v_a_872_ = lean_ctor_get(v___x_871_, 0);
lean_inc(v_a_872_);
lean_dec_ref_known(v___x_871_, 1);
v___x_873_ = lean_nat_add(v_pos_576_, v___y_844_);
lean_dec(v_pos_576_);
v___x_874_ = lean_nat_add(v_minorIdx_577_, v___y_844_);
lean_dec(v_minorIdx_577_);
v___x_875_ = l_Lean_Expr_mvarId_x21(v_a_869_);
lean_dec(v_a_869_);
v___x_876_ = ((lean_object*)(l_Lean_Meta_instInhabitedInductionSubgoal_default___closed__0));
v___x_877_ = lean_box(0);
v___x_878_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_878_, 0, v___x_875_);
lean_ctor_set(v___x_878_, 1, v___x_876_);
lean_ctor_set(v___x_878_, 2, v___x_877_);
v___x_879_ = lean_array_push(v_subgoals_581_, v___x_878_);
v_pos_576_ = v___x_873_;
v_minorIdx_577_ = v___x_874_;
v_recursor_578_ = v___x_870_;
v_recursorType_579_ = v_a_872_;
v_subgoals_581_ = v___x_879_;
v_a_582_ = v___y_848_;
v_a_583_ = v___y_847_;
v_a_584_ = v___y_850_;
v_a_585_ = v___y_849_;
goto _start;
}
else
{
lean_object* v_a_881_; lean_object* v___x_883_; uint8_t v_isShared_884_; uint8_t v_isSharedCheck_888_; 
lean_dec_ref(v___x_870_);
lean_dec(v_a_869_);
lean_dec_ref(v_subgoals_581_);
lean_dec(v_minorIdx_577_);
lean_dec(v_pos_576_);
lean_dec(v_baseSubst_573_);
lean_dec_ref(v_major_571_);
lean_dec(v_mvarId_567_);
v_a_881_ = lean_ctor_get(v___x_871_, 0);
v_isSharedCheck_888_ = !lean_is_exclusive(v___x_871_);
if (v_isSharedCheck_888_ == 0)
{
v___x_883_ = v___x_871_;
v_isShared_884_ = v_isSharedCheck_888_;
goto v_resetjp_882_;
}
else
{
lean_inc(v_a_881_);
lean_dec(v___x_871_);
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
else
{
lean_object* v_a_889_; lean_object* v___x_891_; uint8_t v_isShared_892_; uint8_t v_isSharedCheck_896_; 
lean_dec(v_a_763_);
lean_dec_ref(v_subgoals_581_);
lean_dec_ref(v_recursor_578_);
lean_dec(v_minorIdx_577_);
lean_dec(v_pos_576_);
lean_dec(v_baseSubst_573_);
lean_dec_ref(v_major_571_);
lean_dec(v_mvarId_567_);
v_a_889_ = lean_ctor_get(v___x_868_, 0);
v_isSharedCheck_896_ = !lean_is_exclusive(v___x_868_);
if (v_isSharedCheck_896_ == 0)
{
v___x_891_ = v___x_868_;
v_isShared_892_ = v_isSharedCheck_896_;
goto v_resetjp_890_;
}
else
{
lean_inc(v_a_889_);
lean_dec(v___x_868_);
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
else
{
lean_object* v_val_897_; lean_object* v___x_898_; lean_object* v___x_899_; 
lean_dec_ref(v___y_846_);
lean_dec(v___y_845_);
v_val_897_ = lean_ctor_get(v_a_867_, 0);
lean_inc_n(v_val_897_, 2);
lean_dec_ref_known(v_a_867_, 1);
v___x_898_ = l_Lean_Expr_app___override(v_recursor_578_, v_val_897_);
lean_inc(v_mvarId_567_);
v___x_899_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTypeBody(v_mvarId_567_, v_a_763_, v_val_897_, v___y_848_, v___y_847_, v___y_850_, v___y_849_);
lean_dec(v_val_897_);
if (lean_obj_tag(v___x_899_) == 0)
{
lean_object* v_a_900_; lean_object* v___x_901_; lean_object* v___x_902_; 
v_a_900_ = lean_ctor_get(v___x_899_, 0);
lean_inc(v_a_900_);
lean_dec_ref_known(v___x_899_, 1);
v___x_901_ = lean_nat_add(v_pos_576_, v___y_844_);
lean_dec(v_pos_576_);
v___x_902_ = lean_nat_add(v_minorIdx_577_, v___y_844_);
lean_dec(v_minorIdx_577_);
v_pos_576_ = v___x_901_;
v_minorIdx_577_ = v___x_902_;
v_recursor_578_ = v___x_898_;
v_recursorType_579_ = v_a_900_;
v_a_582_ = v___y_848_;
v_a_583_ = v___y_847_;
v_a_584_ = v___y_850_;
v_a_585_ = v___y_849_;
goto _start;
}
else
{
lean_object* v_a_904_; lean_object* v___x_906_; uint8_t v_isShared_907_; uint8_t v_isSharedCheck_911_; 
lean_dec_ref(v___x_898_);
lean_dec_ref(v_subgoals_581_);
lean_dec(v_minorIdx_577_);
lean_dec(v_pos_576_);
lean_dec(v_baseSubst_573_);
lean_dec_ref(v_major_571_);
lean_dec(v_mvarId_567_);
v_a_904_ = lean_ctor_get(v___x_899_, 0);
v_isSharedCheck_911_ = !lean_is_exclusive(v___x_899_);
if (v_isSharedCheck_911_ == 0)
{
v___x_906_ = v___x_899_;
v_isShared_907_ = v_isSharedCheck_911_;
goto v_resetjp_905_;
}
else
{
lean_inc(v_a_904_);
lean_dec(v___x_899_);
v___x_906_ = lean_box(0);
v_isShared_907_ = v_isSharedCheck_911_;
goto v_resetjp_905_;
}
v_resetjp_905_:
{
lean_object* v___x_909_; 
if (v_isShared_907_ == 0)
{
v___x_909_ = v___x_906_;
goto v_reusejp_908_;
}
else
{
lean_object* v_reuseFailAlloc_910_; 
v_reuseFailAlloc_910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_910_, 0, v_a_904_);
v___x_909_ = v_reuseFailAlloc_910_;
goto v_reusejp_908_;
}
v_reusejp_908_:
{
return v___x_909_;
}
}
}
}
}
else
{
lean_object* v_a_912_; lean_object* v___x_914_; uint8_t v_isShared_915_; uint8_t v_isSharedCheck_919_; 
lean_dec_ref(v___y_846_);
lean_dec(v___y_845_);
lean_dec(v_a_763_);
lean_dec_ref(v_subgoals_581_);
lean_dec_ref(v_recursor_578_);
lean_dec(v_minorIdx_577_);
lean_dec(v_pos_576_);
lean_dec(v_baseSubst_573_);
lean_dec_ref(v_major_571_);
lean_dec(v_mvarId_567_);
v_a_912_ = lean_ctor_get(v___x_866_, 0);
v_isSharedCheck_919_ = !lean_is_exclusive(v___x_866_);
if (v_isSharedCheck_919_ == 0)
{
v___x_914_ = v___x_866_;
v_isShared_915_ = v_isSharedCheck_919_;
goto v_resetjp_913_;
}
else
{
lean_inc(v_a_912_);
lean_dec(v___x_866_);
v___x_914_ = lean_box(0);
v_isShared_915_ = v_isSharedCheck_919_;
goto v_resetjp_913_;
}
v_resetjp_913_:
{
lean_object* v___x_917_; 
if (v_isShared_915_ == 0)
{
v___x_917_ = v___x_914_;
goto v_reusejp_916_;
}
else
{
lean_object* v_reuseFailAlloc_918_; 
v_reuseFailAlloc_918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_918_, 0, v_a_912_);
v___x_917_ = v_reuseFailAlloc_918_;
goto v_reusejp_916_;
}
v_reusejp_916_:
{
return v___x_917_;
}
}
}
}
}
v___jp_920_:
{
uint8_t v___x_930_; 
v___x_930_ = l_Lean_BinderInfo_isInstImplicit(v___y_924_);
if (v___x_930_ == 0)
{
v___y_843_ = v___y_921_;
v___y_844_ = v___y_922_;
v___y_845_ = v___y_929_;
v___y_846_ = v___y_923_;
v___y_847_ = v___y_925_;
v___y_848_ = v___y_926_;
v___y_849_ = v___y_927_;
v___y_850_ = v___y_928_;
v___y_851_ = v___x_930_;
goto v___jp_842_;
}
else
{
lean_object* v___x_931_; lean_object* v___x_932_; uint8_t v___x_933_; 
v___x_931_ = lean_array_get_size(v_givenNames_568_);
v___x_932_ = lean_unsigned_to_nat(0u);
v___x_933_ = lean_nat_dec_eq(v___x_931_, v___x_932_);
v___y_843_ = v___y_921_;
v___y_844_ = v___y_922_;
v___y_845_ = v___y_929_;
v___y_846_ = v___y_923_;
v___y_847_ = v___y_925_;
v___y_848_ = v___y_926_;
v___y_849_ = v___y_927_;
v___y_850_ = v___y_928_;
v___y_851_ = v___x_933_;
goto v___jp_842_;
}
}
v___jp_934_:
{
if (lean_obj_tag(v_a_763_) == 7)
{
lean_object* v_binderName_941_; lean_object* v_binderType_942_; uint8_t v_binderInfo_943_; lean_object* v___x_944_; lean_object* v___x_945_; uint8_t v___x_946_; 
v_binderName_941_ = lean_ctor_get(v_a_763_, 0);
v_binderType_942_ = lean_ctor_get(v_a_763_, 1);
v_binderInfo_943_ = lean_ctor_get_uint8(v_a_763_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_942_);
v___x_944_ = l_Lean_Expr_headBeta(v_binderType_942_);
v___x_945_ = lean_unsigned_to_nat(1u);
v___x_946_ = lean_nat_dec_eq(v_numMinors_575_, v___x_945_);
if (v___x_946_ == 0)
{
lean_object* v___x_947_; lean_object* v___x_948_; 
v___x_947_ = l_Lean_Name_eraseMacroScopes(v_binderName_941_);
v___x_948_ = l_Lean_Name_append(v___y_935_, v___x_947_);
v___y_921_ = v___y_936_;
v___y_922_ = v___x_945_;
v___y_923_ = v___x_944_;
v___y_924_ = v_binderInfo_943_;
v___y_925_ = v___y_938_;
v___y_926_ = v___y_937_;
v___y_927_ = v___y_940_;
v___y_928_ = v___y_939_;
v___y_929_ = v___x_948_;
goto v___jp_920_;
}
else
{
v___y_921_ = v___y_936_;
v___y_922_ = v___x_945_;
v___y_923_ = v___x_944_;
v___y_924_ = v_binderInfo_943_;
v___y_925_ = v___y_938_;
v___y_926_ = v___y_937_;
v___y_927_ = v___y_940_;
v___y_928_ = v___y_939_;
v___y_929_ = v___y_935_;
goto v___jp_920_;
}
}
else
{
lean_object* v___x_949_; lean_object* v___x_950_; 
lean_dec(v___y_935_);
lean_dec(v_a_763_);
lean_dec_ref(v_subgoals_581_);
lean_dec_ref(v_recursor_578_);
lean_dec(v_minorIdx_577_);
lean_dec(v_pos_576_);
lean_dec(v_baseSubst_573_);
lean_dec_ref(v_major_571_);
lean_dec(v_mvarId_567_);
v___x_949_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__15, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__15_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__15);
v___x_950_ = l_panic___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__4(v___x_949_, v___y_937_, v___y_938_, v___y_939_, v___y_940_);
return v___x_950_;
}
}
v___jp_951_:
{
if (v___y_952_ == 0)
{
lean_dec(v_a_763_);
lean_dec(v_minorIdx_577_);
lean_dec(v_pos_576_);
lean_dec(v_baseSubst_573_);
lean_dec_ref(v_major_571_);
if (v_consumedMajor_580_ == 0)
{
lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; 
v___x_953_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1));
v___x_954_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9);
lean_inc(v_mvarId_567_);
v___x_955_ = l_Lean_Meta_throwTacticEx___redArg(v___x_953_, v_mvarId_567_, v___x_954_, v_a_582_, v_a_583_, v_a_584_, v_a_585_);
if (lean_obj_tag(v___x_955_) == 0)
{
lean_dec_ref_known(v___x_955_, 1);
v___y_588_ = v_a_582_;
v___y_589_ = v_a_583_;
v___y_590_ = v_a_584_;
v___y_591_ = v_a_585_;
goto v___jp_587_;
}
else
{
lean_object* v_a_956_; lean_object* v___x_958_; uint8_t v_isShared_959_; uint8_t v_isSharedCheck_963_; 
lean_dec_ref(v_subgoals_581_);
lean_dec_ref(v_recursor_578_);
lean_dec(v_mvarId_567_);
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
else
{
v___y_588_ = v_a_582_;
v___y_589_ = v_a_583_;
v___y_590_ = v_a_584_;
v___y_591_ = v_a_585_;
goto v___jp_587_;
}
}
else
{
lean_object* v___x_964_; uint8_t v___x_965_; 
v___x_964_ = l_Lean_Meta_RecursorInfo_firstIndexPos(v_recursorInfo_569_);
v___x_965_ = lean_nat_dec_eq(v_pos_576_, v___x_964_);
lean_dec(v___x_964_);
if (v___x_965_ == 0)
{
lean_object* v___x_966_; 
lean_inc(v_mvarId_567_);
v___x_966_ = l_Lean_MVarId_getTag(v_mvarId_567_, v_a_582_, v_a_583_, v_a_584_, v_a_585_);
if (lean_obj_tag(v___x_966_) == 0)
{
lean_object* v_a_967_; uint8_t v___x_968_; 
v_a_967_ = lean_ctor_get(v___x_966_, 0);
lean_inc(v_a_967_);
lean_dec_ref_known(v___x_966_, 1);
v___x_968_ = lean_nat_dec_le(v_numMinors_575_, v_minorIdx_577_);
if (v___x_968_ == 0)
{
v___y_935_ = v_a_967_;
v___y_936_ = v___y_952_;
v___y_937_ = v_a_582_;
v___y_938_ = v_a_583_;
v___y_939_ = v_a_584_;
v___y_940_ = v_a_585_;
goto v___jp_934_;
}
else
{
lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; 
v___x_969_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1));
v___x_970_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9);
lean_inc(v_mvarId_567_);
v___x_971_ = l_Lean_Meta_throwTacticEx___redArg(v___x_969_, v_mvarId_567_, v___x_970_, v_a_582_, v_a_583_, v_a_584_, v_a_585_);
if (lean_obj_tag(v___x_971_) == 0)
{
lean_dec_ref_known(v___x_971_, 1);
v___y_935_ = v_a_967_;
v___y_936_ = v___y_952_;
v___y_937_ = v_a_582_;
v___y_938_ = v_a_583_;
v___y_939_ = v_a_584_;
v___y_940_ = v_a_585_;
goto v___jp_934_;
}
else
{
lean_object* v_a_972_; lean_object* v___x_974_; uint8_t v_isShared_975_; uint8_t v_isSharedCheck_979_; 
lean_dec(v_a_967_);
lean_dec(v_a_763_);
lean_dec_ref(v_subgoals_581_);
lean_dec_ref(v_recursor_578_);
lean_dec(v_minorIdx_577_);
lean_dec(v_pos_576_);
lean_dec(v_baseSubst_573_);
lean_dec_ref(v_major_571_);
lean_dec(v_mvarId_567_);
v_a_972_ = lean_ctor_get(v___x_971_, 0);
v_isSharedCheck_979_ = !lean_is_exclusive(v___x_971_);
if (v_isSharedCheck_979_ == 0)
{
v___x_974_ = v___x_971_;
v_isShared_975_ = v_isSharedCheck_979_;
goto v_resetjp_973_;
}
else
{
lean_inc(v_a_972_);
lean_dec(v___x_971_);
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
}
else
{
lean_object* v_a_980_; lean_object* v___x_982_; uint8_t v_isShared_983_; uint8_t v_isSharedCheck_987_; 
lean_dec(v_a_763_);
lean_dec_ref(v_subgoals_581_);
lean_dec_ref(v_recursor_578_);
lean_dec(v_minorIdx_577_);
lean_dec(v_pos_576_);
lean_dec(v_baseSubst_573_);
lean_dec_ref(v_major_571_);
lean_dec(v_mvarId_567_);
v_a_980_ = lean_ctor_get(v___x_966_, 0);
v_isSharedCheck_987_ = !lean_is_exclusive(v___x_966_);
if (v_isSharedCheck_987_ == 0)
{
v___x_982_ = v___x_966_;
v_isShared_983_ = v_isSharedCheck_987_;
goto v_resetjp_981_;
}
else
{
lean_inc(v_a_980_);
lean_dec(v___x_966_);
v___x_982_ = lean_box(0);
v_isShared_983_ = v_isSharedCheck_987_;
goto v_resetjp_981_;
}
v_resetjp_981_:
{
lean_object* v___x_985_; 
if (v_isShared_983_ == 0)
{
v___x_985_ = v___x_982_;
goto v_reusejp_984_;
}
else
{
lean_object* v_reuseFailAlloc_986_; 
v_reuseFailAlloc_986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_986_, 0, v_a_980_);
v___x_985_ = v_reuseFailAlloc_986_;
goto v_reusejp_984_;
}
v_reusejp_984_:
{
return v___x_985_;
}
}
}
}
else
{
lean_object* v___x_988_; lean_object* v___x_989_; uint8_t v___x_990_; 
v___x_988_ = lean_unsigned_to_nat(0u);
v___x_989_ = lean_array_get_size(v_indices_572_);
v___x_990_ = lean_nat_dec_lt(v___x_988_, v___x_989_);
if (v___x_990_ == 0)
{
v___y_728_ = v___x_965_;
v___y_729_ = v___x_989_;
v_fst_730_ = v_recursor_578_;
v_snd_731_ = v_a_763_;
goto v___jp_727_;
}
else
{
lean_object* v___x_991_; uint8_t v___x_992_; 
lean_inc(v_a_763_);
lean_inc_ref(v_recursor_578_);
v___x_991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_991_, 0, v_recursor_578_);
lean_ctor_set(v___x_991_, 1, v_a_763_);
v___x_992_ = lean_nat_dec_le(v___x_989_, v___x_989_);
if (v___x_992_ == 0)
{
if (v___x_990_ == 0)
{
lean_dec_ref_known(v___x_991_, 2);
v___y_728_ = v___x_965_;
v___y_729_ = v___x_989_;
v_fst_730_ = v_recursor_578_;
v_snd_731_ = v_a_763_;
goto v___jp_727_;
}
else
{
size_t v___x_993_; size_t v___x_994_; lean_object* v___x_995_; 
lean_dec(v_a_763_);
lean_dec_ref(v_recursor_578_);
v___x_993_ = ((size_t)0ULL);
v___x_994_ = lean_usize_of_nat(v___x_989_);
lean_inc(v_mvarId_567_);
v___x_995_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__5(v_mvarId_567_, v_indices_572_, v___x_993_, v___x_994_, v___x_991_, v_a_582_, v_a_583_, v_a_584_, v_a_585_);
v___y_748_ = v___x_989_;
v___y_749_ = v___x_965_;
v___y_750_ = v___x_995_;
goto v___jp_747_;
}
}
else
{
size_t v___x_996_; size_t v___x_997_; lean_object* v___x_998_; 
lean_dec(v_a_763_);
lean_dec_ref(v_recursor_578_);
v___x_996_ = ((size_t)0ULL);
v___x_997_ = lean_usize_of_nat(v___x_989_);
lean_inc(v_mvarId_567_);
v___x_998_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__5(v_mvarId_567_, v_indices_572_, v___x_996_, v___x_997_, v___x_991_, v_a_582_, v_a_583_, v_a_584_, v_a_585_);
v___y_748_ = v___x_989_;
v___y_749_ = v___x_965_;
v___y_750_ = v___x_998_;
goto v___jp_747_;
}
}
}
}
}
}
else
{
lean_object* v_a_1002_; lean_object* v___x_1004_; uint8_t v_isShared_1005_; uint8_t v_isSharedCheck_1009_; 
lean_dec_ref(v_subgoals_581_);
lean_dec_ref(v_recursor_578_);
lean_dec(v_minorIdx_577_);
lean_dec(v_pos_576_);
lean_dec(v_baseSubst_573_);
lean_dec_ref(v_major_571_);
lean_dec(v_mvarId_567_);
v_a_1002_ = lean_ctor_get(v___x_762_, 0);
v_isSharedCheck_1009_ = !lean_is_exclusive(v___x_762_);
if (v_isSharedCheck_1009_ == 0)
{
v___x_1004_ = v___x_762_;
v_isShared_1005_ = v_isSharedCheck_1009_;
goto v_resetjp_1003_;
}
else
{
lean_inc(v_a_1002_);
lean_dec(v___x_762_);
v___x_1004_ = lean_box(0);
v_isShared_1005_ = v_isSharedCheck_1009_;
goto v_resetjp_1003_;
}
v_resetjp_1003_:
{
lean_object* v___x_1007_; 
if (v_isShared_1005_ == 0)
{
v___x_1007_ = v___x_1004_;
goto v_reusejp_1006_;
}
else
{
lean_object* v_reuseFailAlloc_1008_; 
v_reuseFailAlloc_1008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1008_, 0, v_a_1002_);
v___x_1007_ = v_reuseFailAlloc_1008_;
goto v_reusejp_1006_;
}
v_reusejp_1006_:
{
return v___x_1007_;
}
}
}
v___jp_587_:
{
lean_object* v___x_592_; 
v___x_592_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0___redArg(v_mvarId_567_, v_recursor_578_, v___y_589_);
if (lean_obj_tag(v___x_592_) == 0)
{
lean_object* v___x_594_; uint8_t v_isShared_595_; uint8_t v_isSharedCheck_634_; 
v_isSharedCheck_634_ = !lean_is_exclusive(v___x_592_);
if (v_isSharedCheck_634_ == 0)
{
lean_object* v_unused_635_; 
v_unused_635_ = lean_ctor_get(v___x_592_, 0);
lean_dec(v_unused_635_);
v___x_594_ = v___x_592_;
v_isShared_595_ = v_isSharedCheck_634_;
goto v_resetjp_593_;
}
else
{
lean_dec(v___x_592_);
v___x_594_ = lean_box(0);
v_isShared_595_ = v_isSharedCheck_634_;
goto v_resetjp_593_;
}
v_resetjp_593_:
{
lean_object* v_toCold_596_; lean_object* v_options_597_; uint8_t v_hasTrace_598_; 
v_toCold_596_ = lean_ctor_get(v___y_590_, 0);
v_options_597_ = lean_ctor_get(v_toCold_596_, 2);
v_hasTrace_598_ = lean_ctor_get_uint8(v_options_597_, sizeof(void*)*1);
if (v_hasTrace_598_ == 0)
{
lean_object* v___x_600_; 
if (v_isShared_595_ == 0)
{
lean_ctor_set(v___x_594_, 0, v_subgoals_581_);
v___x_600_ = v___x_594_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_601_; 
v_reuseFailAlloc_601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_601_, 0, v_subgoals_581_);
v___x_600_ = v_reuseFailAlloc_601_;
goto v_reusejp_599_;
}
v_reusejp_599_:
{
return v___x_600_;
}
}
else
{
lean_object* v_inheritedTraceOptions_602_; lean_object* v___x_603_; lean_object* v___x_604_; uint8_t v___x_605_; 
v_inheritedTraceOptions_602_ = lean_ctor_get(v_toCold_596_, 11);
v___x_603_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__2));
v___x_604_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5);
v___x_605_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_602_, v_options_597_, v___x_604_);
if (v___x_605_ == 0)
{
lean_object* v___x_607_; 
if (v_isShared_595_ == 0)
{
lean_ctor_set(v___x_594_, 0, v_subgoals_581_);
v___x_607_ = v___x_594_;
goto v_reusejp_606_;
}
else
{
lean_object* v_reuseFailAlloc_608_; 
v_reuseFailAlloc_608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_608_, 0, v_subgoals_581_);
v___x_607_ = v_reuseFailAlloc_608_;
goto v_reusejp_606_;
}
v_reusejp_606_:
{
return v___x_607_;
}
}
else
{
lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; 
lean_del_object(v___x_594_);
v___x_609_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__7, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__7_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__7);
v___x_610_ = lean_array_get_size(v_subgoals_581_);
v___x_611_ = l_Nat_reprFast(v___x_610_);
v___x_612_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_612_, 0, v___x_611_);
v___x_613_ = l_Lean_MessageData_ofFormat(v___x_612_);
v___x_614_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_614_, 0, v___x_609_);
lean_ctor_set(v___x_614_, 1, v___x_613_);
v___x_615_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__9, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__9_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__9);
v___x_616_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_616_, 0, v___x_614_);
lean_ctor_set(v___x_616_, 1, v___x_615_);
v___x_617_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1(v___x_603_, v___x_616_, v___y_588_, v___y_589_, v___y_590_, v___y_591_);
if (lean_obj_tag(v___x_617_) == 0)
{
lean_object* v___x_619_; uint8_t v_isShared_620_; uint8_t v_isSharedCheck_624_; 
v_isSharedCheck_624_ = !lean_is_exclusive(v___x_617_);
if (v_isSharedCheck_624_ == 0)
{
lean_object* v_unused_625_; 
v_unused_625_ = lean_ctor_get(v___x_617_, 0);
lean_dec(v_unused_625_);
v___x_619_ = v___x_617_;
v_isShared_620_ = v_isSharedCheck_624_;
goto v_resetjp_618_;
}
else
{
lean_dec(v___x_617_);
v___x_619_ = lean_box(0);
v_isShared_620_ = v_isSharedCheck_624_;
goto v_resetjp_618_;
}
v_resetjp_618_:
{
lean_object* v___x_622_; 
if (v_isShared_620_ == 0)
{
lean_ctor_set(v___x_619_, 0, v_subgoals_581_);
v___x_622_ = v___x_619_;
goto v_reusejp_621_;
}
else
{
lean_object* v_reuseFailAlloc_623_; 
v_reuseFailAlloc_623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_623_, 0, v_subgoals_581_);
v___x_622_ = v_reuseFailAlloc_623_;
goto v_reusejp_621_;
}
v_reusejp_621_:
{
return v___x_622_;
}
}
}
else
{
lean_object* v_a_626_; lean_object* v___x_628_; uint8_t v_isShared_629_; uint8_t v_isSharedCheck_633_; 
lean_dec_ref(v_subgoals_581_);
v_a_626_ = lean_ctor_get(v___x_617_, 0);
v_isSharedCheck_633_ = !lean_is_exclusive(v___x_617_);
if (v_isSharedCheck_633_ == 0)
{
v___x_628_ = v___x_617_;
v_isShared_629_ = v_isSharedCheck_633_;
goto v_resetjp_627_;
}
else
{
lean_inc(v_a_626_);
lean_dec(v___x_617_);
v___x_628_ = lean_box(0);
v_isShared_629_ = v_isSharedCheck_633_;
goto v_resetjp_627_;
}
v_resetjp_627_:
{
lean_object* v___x_631_; 
if (v_isShared_629_ == 0)
{
v___x_631_ = v___x_628_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_632_; 
v_reuseFailAlloc_632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_632_, 0, v_a_626_);
v___x_631_ = v_reuseFailAlloc_632_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
return v___x_631_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_636_; lean_object* v___x_638_; uint8_t v_isShared_639_; uint8_t v_isSharedCheck_643_; 
lean_dec_ref(v_subgoals_581_);
v_a_636_ = lean_ctor_get(v___x_592_, 0);
v_isSharedCheck_643_ = !lean_is_exclusive(v___x_592_);
if (v_isSharedCheck_643_ == 0)
{
v___x_638_ = v___x_592_;
v_isShared_639_ = v_isSharedCheck_643_;
goto v_resetjp_637_;
}
else
{
lean_inc(v_a_636_);
lean_dec(v___x_592_);
v___x_638_ = lean_box(0);
v_isShared_639_ = v_isSharedCheck_643_;
goto v_resetjp_637_;
}
v_resetjp_637_:
{
lean_object* v___x_641_; 
if (v_isShared_639_ == 0)
{
v___x_641_ = v___x_638_;
goto v_reusejp_640_;
}
else
{
lean_object* v_reuseFailAlloc_642_; 
v_reuseFailAlloc_642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_642_, 0, v_a_636_);
v___x_641_ = v_reuseFailAlloc_642_;
goto v_reusejp_640_;
}
v_reusejp_640_:
{
return v___x_641_;
}
}
}
}
v___jp_644_:
{
lean_object* v___x_661_; 
v___x_661_ = l_Lean_Meta_introNCore(v___y_653_, v___y_658_, v___y_654_, v___y_660_, v___y_647_, v___y_657_, v___y_646_, v___y_652_, v___y_645_);
if (lean_obj_tag(v___x_661_) == 0)
{
lean_object* v_a_662_; lean_object* v_fst_663_; lean_object* v_snd_664_; lean_object* v___x_665_; lean_object* v___x_666_; 
v_a_662_ = lean_ctor_get(v___x_661_, 0);
lean_inc(v_a_662_);
lean_dec_ref_known(v___x_661_, 1);
v_fst_663_ = lean_ctor_get(v_a_662_, 0);
lean_inc(v_fst_663_);
v_snd_664_ = lean_ctor_get(v_a_662_, 1);
lean_inc(v_snd_664_);
lean_dec(v_a_662_);
v___x_665_ = lean_box(0);
v___x_666_ = l_Lean_Meta_introNCore(v_snd_664_, v___y_651_, v___x_665_, v___y_647_, v___y_655_, v___y_657_, v___y_646_, v___y_652_, v___y_645_);
if (lean_obj_tag(v___x_666_) == 0)
{
lean_object* v_a_667_; lean_object* v_fst_668_; lean_object* v_snd_669_; lean_object* v___x_670_; size_t v_sz_671_; size_t v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; 
v_a_667_ = lean_ctor_get(v___x_666_, 0);
lean_inc(v_a_667_);
lean_dec_ref_known(v___x_666_, 1);
v_fst_668_ = lean_ctor_get(v_a_667_, 0);
lean_inc(v_fst_668_);
v_snd_669_ = lean_ctor_get(v_a_667_, 1);
lean_inc(v_snd_669_);
lean_dec(v_a_667_);
lean_inc(v_baseSubst_573_);
lean_inc(v___y_650_);
v___x_670_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__2___redArg(v___y_659_, v_reverted_570_, v_fst_668_, v___y_650_, v___y_650_, v_baseSubst_573_);
lean_dec(v___y_650_);
lean_dec(v_fst_668_);
lean_dec(v___y_659_);
v_sz_671_ = lean_array_size(v_fst_663_);
v___x_672_ = ((size_t)0ULL);
v___x_673_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__3(v_sz_671_, v___x_672_, v_fst_663_);
v___x_674_ = lean_nat_add(v_pos_576_, v___y_656_);
lean_dec(v_pos_576_);
v___x_675_ = lean_nat_add(v_minorIdx_577_, v___y_656_);
lean_dec(v_minorIdx_577_);
v___x_676_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_676_, 0, v_snd_669_);
lean_ctor_set(v___x_676_, 1, v___x_673_);
lean_ctor_set(v___x_676_, 2, v___x_670_);
v___x_677_ = lean_array_push(v_subgoals_581_, v___x_676_);
v_pos_576_ = v___x_674_;
v_minorIdx_577_ = v___x_675_;
v_recursor_578_ = v___y_649_;
v_recursorType_579_ = v___y_648_;
v_subgoals_581_ = v___x_677_;
v_a_582_ = v___y_657_;
v_a_583_ = v___y_646_;
v_a_584_ = v___y_652_;
v_a_585_ = v___y_645_;
goto _start;
}
else
{
lean_object* v_a_679_; lean_object* v___x_681_; uint8_t v_isShared_682_; uint8_t v_isSharedCheck_686_; 
lean_dec(v_fst_663_);
lean_dec(v___y_659_);
lean_dec(v___y_650_);
lean_dec_ref(v___y_649_);
lean_dec_ref(v___y_648_);
lean_dec_ref(v_subgoals_581_);
lean_dec(v_minorIdx_577_);
lean_dec(v_pos_576_);
lean_dec(v_baseSubst_573_);
lean_dec_ref(v_major_571_);
lean_dec(v_mvarId_567_);
v_a_679_ = lean_ctor_get(v___x_666_, 0);
v_isSharedCheck_686_ = !lean_is_exclusive(v___x_666_);
if (v_isSharedCheck_686_ == 0)
{
v___x_681_ = v___x_666_;
v_isShared_682_ = v_isSharedCheck_686_;
goto v_resetjp_680_;
}
else
{
lean_inc(v_a_679_);
lean_dec(v___x_666_);
v___x_681_ = lean_box(0);
v_isShared_682_ = v_isSharedCheck_686_;
goto v_resetjp_680_;
}
v_resetjp_680_:
{
lean_object* v___x_684_; 
if (v_isShared_682_ == 0)
{
v___x_684_ = v___x_681_;
goto v_reusejp_683_;
}
else
{
lean_object* v_reuseFailAlloc_685_; 
v_reuseFailAlloc_685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_685_, 0, v_a_679_);
v___x_684_ = v_reuseFailAlloc_685_;
goto v_reusejp_683_;
}
v_reusejp_683_:
{
return v___x_684_;
}
}
}
}
else
{
lean_object* v_a_687_; lean_object* v___x_689_; uint8_t v_isShared_690_; uint8_t v_isSharedCheck_694_; 
lean_dec(v___y_659_);
lean_dec(v___y_651_);
lean_dec(v___y_650_);
lean_dec_ref(v___y_649_);
lean_dec_ref(v___y_648_);
lean_dec_ref(v_subgoals_581_);
lean_dec(v_minorIdx_577_);
lean_dec(v_pos_576_);
lean_dec(v_baseSubst_573_);
lean_dec_ref(v_major_571_);
lean_dec(v_mvarId_567_);
v_a_687_ = lean_ctor_get(v___x_661_, 0);
v_isSharedCheck_694_ = !lean_is_exclusive(v___x_661_);
if (v_isSharedCheck_694_ == 0)
{
v___x_689_ = v___x_661_;
v_isShared_690_ = v_isSharedCheck_694_;
goto v_resetjp_688_;
}
else
{
lean_inc(v_a_687_);
lean_dec(v___x_661_);
v___x_689_ = lean_box(0);
v_isShared_690_ = v_isSharedCheck_694_;
goto v_resetjp_688_;
}
v_resetjp_688_:
{
lean_object* v___x_692_; 
if (v_isShared_690_ == 0)
{
v___x_692_ = v___x_689_;
goto v_reusejp_691_;
}
else
{
lean_object* v_reuseFailAlloc_693_; 
v_reuseFailAlloc_693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_693_, 0, v_a_687_);
v___x_692_ = v_reuseFailAlloc_693_;
goto v_reusejp_691_;
}
v_reusejp_691_:
{
return v___x_692_;
}
}
}
}
v___jp_695_:
{
lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; 
v___x_711_ = l_Lean_Expr_mvarId_x21(v___y_702_);
lean_dec_ref(v___y_702_);
v___x_712_ = l_Lean_Expr_fvarId_x21(v_major_571_);
v___x_713_ = l_Lean_MVarId_tryClear(v___x_711_, v___x_712_, v___y_707_, v___y_708_, v___y_709_, v___y_710_);
if (lean_obj_tag(v___x_713_) == 0)
{
uint8_t v_explicit_714_; 
v_explicit_714_ = lean_ctor_get_uint8(v___y_701_, sizeof(void*)*1);
if (v_explicit_714_ == 0)
{
lean_object* v_a_715_; lean_object* v_varNames_716_; 
v_a_715_ = lean_ctor_get(v___x_713_, 0);
lean_inc(v_a_715_);
lean_dec_ref_known(v___x_713_, 1);
v_varNames_716_ = lean_ctor_get(v___y_701_, 0);
lean_inc(v_varNames_716_);
lean_dec_ref(v___y_701_);
v___y_645_ = v___y_710_;
v___y_646_ = v___y_708_;
v___y_647_ = v___y_697_;
v___y_648_ = v___y_699_;
v___y_649_ = v___y_700_;
v___y_650_ = v___y_703_;
v___y_651_ = v___y_706_;
v___y_652_ = v___y_709_;
v___y_653_ = v_a_715_;
v___y_654_ = v_varNames_716_;
v___y_655_ = v___y_696_;
v___y_656_ = v___y_698_;
v___y_657_ = v___y_707_;
v___y_658_ = v___y_704_;
v___y_659_ = v___y_705_;
v___y_660_ = v___y_696_;
goto v___jp_644_;
}
else
{
lean_object* v_a_717_; lean_object* v_varNames_718_; 
v_a_717_ = lean_ctor_get(v___x_713_, 0);
lean_inc(v_a_717_);
lean_dec_ref_known(v___x_713_, 1);
v_varNames_718_ = lean_ctor_get(v___y_701_, 0);
lean_inc(v_varNames_718_);
lean_dec_ref(v___y_701_);
v___y_645_ = v___y_710_;
v___y_646_ = v___y_708_;
v___y_647_ = v___y_697_;
v___y_648_ = v___y_699_;
v___y_649_ = v___y_700_;
v___y_650_ = v___y_703_;
v___y_651_ = v___y_706_;
v___y_652_ = v___y_709_;
v___y_653_ = v_a_717_;
v___y_654_ = v_varNames_718_;
v___y_655_ = v___y_696_;
v___y_656_ = v___y_698_;
v___y_657_ = v___y_707_;
v___y_658_ = v___y_704_;
v___y_659_ = v___y_705_;
v___y_660_ = v___y_697_;
goto v___jp_644_;
}
}
else
{
lean_object* v_a_719_; lean_object* v___x_721_; uint8_t v_isShared_722_; uint8_t v_isSharedCheck_726_; 
lean_dec(v___y_706_);
lean_dec(v___y_705_);
lean_dec(v___y_704_);
lean_dec(v___y_703_);
lean_dec_ref(v___y_701_);
lean_dec_ref(v___y_700_);
lean_dec_ref(v___y_699_);
lean_dec_ref(v_subgoals_581_);
lean_dec(v_minorIdx_577_);
lean_dec(v_pos_576_);
lean_dec(v_baseSubst_573_);
lean_dec_ref(v_major_571_);
lean_dec(v_mvarId_567_);
v_a_719_ = lean_ctor_get(v___x_713_, 0);
v_isSharedCheck_726_ = !lean_is_exclusive(v___x_713_);
if (v_isSharedCheck_726_ == 0)
{
v___x_721_ = v___x_713_;
v_isShared_722_ = v_isSharedCheck_726_;
goto v_resetjp_720_;
}
else
{
lean_inc(v_a_719_);
lean_dec(v___x_713_);
v___x_721_ = lean_box(0);
v_isShared_722_ = v_isSharedCheck_726_;
goto v_resetjp_720_;
}
v_resetjp_720_:
{
lean_object* v___x_724_; 
if (v_isShared_722_ == 0)
{
v___x_724_ = v___x_721_;
goto v_reusejp_723_;
}
else
{
lean_object* v_reuseFailAlloc_725_; 
v_reuseFailAlloc_725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_725_, 0, v_a_719_);
v___x_724_ = v_reuseFailAlloc_725_;
goto v_reusejp_723_;
}
v_reusejp_723_:
{
return v___x_724_;
}
}
}
}
v___jp_727_:
{
lean_object* v___x_732_; lean_object* v___x_733_; 
lean_inc_ref(v_major_571_);
v___x_732_ = l_Lean_Expr_app___override(v_fst_730_, v_major_571_);
lean_inc(v_mvarId_567_);
v___x_733_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTypeBody(v_mvarId_567_, v_snd_731_, v_major_571_, v_a_582_, v_a_583_, v_a_584_, v_a_585_);
if (lean_obj_tag(v___x_733_) == 0)
{
lean_object* v_a_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; 
v_a_734_ = lean_ctor_get(v___x_733_, 0);
lean_inc(v_a_734_);
lean_dec_ref_known(v___x_733_, 1);
v___x_735_ = lean_unsigned_to_nat(1u);
v___x_736_ = lean_nat_add(v_pos_576_, v___x_735_);
lean_dec(v_pos_576_);
v___x_737_ = lean_nat_add(v___x_736_, v___y_729_);
lean_dec(v___y_729_);
lean_dec(v___x_736_);
v_pos_576_ = v___x_737_;
v_recursor_578_ = v___x_732_;
v_recursorType_579_ = v_a_734_;
v_consumedMajor_580_ = v___y_728_;
goto _start;
}
else
{
lean_object* v_a_739_; lean_object* v___x_741_; uint8_t v_isShared_742_; uint8_t v_isSharedCheck_746_; 
lean_dec_ref(v___x_732_);
lean_dec(v___y_729_);
lean_dec_ref(v_subgoals_581_);
lean_dec(v_minorIdx_577_);
lean_dec(v_pos_576_);
lean_dec(v_baseSubst_573_);
lean_dec_ref(v_major_571_);
lean_dec(v_mvarId_567_);
v_a_739_ = lean_ctor_get(v___x_733_, 0);
v_isSharedCheck_746_ = !lean_is_exclusive(v___x_733_);
if (v_isSharedCheck_746_ == 0)
{
v___x_741_ = v___x_733_;
v_isShared_742_ = v_isSharedCheck_746_;
goto v_resetjp_740_;
}
else
{
lean_inc(v_a_739_);
lean_dec(v___x_733_);
v___x_741_ = lean_box(0);
v_isShared_742_ = v_isSharedCheck_746_;
goto v_resetjp_740_;
}
v_resetjp_740_:
{
lean_object* v___x_744_; 
if (v_isShared_742_ == 0)
{
v___x_744_ = v___x_741_;
goto v_reusejp_743_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v_a_739_);
v___x_744_ = v_reuseFailAlloc_745_;
goto v_reusejp_743_;
}
v_reusejp_743_:
{
return v___x_744_;
}
}
}
}
v___jp_747_:
{
if (lean_obj_tag(v___y_750_) == 0)
{
lean_object* v_a_751_; lean_object* v_fst_752_; lean_object* v_snd_753_; 
v_a_751_ = lean_ctor_get(v___y_750_, 0);
lean_inc(v_a_751_);
lean_dec_ref_known(v___y_750_, 1);
v_fst_752_ = lean_ctor_get(v_a_751_, 0);
lean_inc(v_fst_752_);
v_snd_753_ = lean_ctor_get(v_a_751_, 1);
lean_inc(v_snd_753_);
lean_dec(v_a_751_);
v___y_728_ = v___y_749_;
v___y_729_ = v___y_748_;
v_fst_730_ = v_fst_752_;
v_snd_731_ = v_snd_753_;
goto v___jp_727_;
}
else
{
lean_object* v_a_754_; lean_object* v___x_756_; uint8_t v_isShared_757_; uint8_t v_isSharedCheck_761_; 
lean_dec(v___y_748_);
lean_dec_ref(v_subgoals_581_);
lean_dec(v_minorIdx_577_);
lean_dec(v_pos_576_);
lean_dec(v_baseSubst_573_);
lean_dec_ref(v_major_571_);
lean_dec(v_mvarId_567_);
v_a_754_ = lean_ctor_get(v___y_750_, 0);
v_isSharedCheck_761_ = !lean_is_exclusive(v___y_750_);
if (v_isSharedCheck_761_ == 0)
{
v___x_756_ = v___y_750_;
v_isShared_757_ = v_isSharedCheck_761_;
goto v_resetjp_755_;
}
else
{
lean_inc(v_a_754_);
lean_dec(v___y_750_);
v___x_756_ = lean_box(0);
v_isShared_757_ = v_isSharedCheck_761_;
goto v_resetjp_755_;
}
v_resetjp_755_:
{
lean_object* v___x_759_; 
if (v_isShared_757_ == 0)
{
v___x_759_ = v___x_756_;
goto v_reusejp_758_;
}
else
{
lean_object* v_reuseFailAlloc_760_; 
v_reuseFailAlloc_760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_760_, 0, v_a_754_);
v___x_759_ = v_reuseFailAlloc_760_;
goto v_reusejp_758_;
}
v_reusejp_758_:
{
return v___x_759_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_567_ = stack[0].m_obj;
lean_object* v_givenNames_568_ = stack[1].m_obj;
lean_object* v_recursorInfo_569_ = stack[2].m_obj;
lean_object* v_reverted_570_ = stack[3].m_obj;
lean_object* v_major_571_ = stack[4].m_obj;
lean_object* v_indices_572_ = stack[5].m_obj;
lean_object* v_baseSubst_573_ = stack[6].m_obj;
lean_object* v_initialArity_574_ = stack[7].m_obj;
lean_object* v_numMinors_575_ = stack[8].m_obj;
lean_object* v_pos_576_ = stack[9].m_obj;
lean_object* v_minorIdx_577_ = stack[10].m_obj;
lean_object* v_recursor_578_ = stack[11].m_obj;
lean_object* v_recursorType_579_ = stack[12].m_obj;
uint8_t v_consumedMajor_580_ = stack[13].m_num;
lean_object* v_subgoals_581_ = stack[14].m_obj;
lean_object* v_a_582_ = stack[15].m_obj;
lean_object* v_a_583_ = stack[16].m_obj;
lean_object* v_a_584_ = stack[17].m_obj;
lean_object* v_a_585_ = stack[18].m_obj;
lean_object* v_res_1010_;
v_res_1010_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop(v_mvarId_567_, v_givenNames_568_, v_recursorInfo_569_, v_reverted_570_, v_major_571_, v_indices_572_, v_baseSubst_573_, v_initialArity_574_, v_numMinors_575_, v_pos_576_, v_minorIdx_577_, v_recursor_578_, v_recursorType_579_, v_consumedMajor_580_, v_subgoals_581_, v_a_582_, v_a_583_, v_a_584_, v_a_585_);
stack->m_obj
 = v_res_1010_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___boxed(lean_object** _args){
lean_object* v_mvarId_1011_ = _args[0];
lean_object* v_givenNames_1012_ = _args[1];
lean_object* v_recursorInfo_1013_ = _args[2];
lean_object* v_reverted_1014_ = _args[3];
lean_object* v_major_1015_ = _args[4];
lean_object* v_indices_1016_ = _args[5];
lean_object* v_baseSubst_1017_ = _args[6];
lean_object* v_initialArity_1018_ = _args[7];
lean_object* v_numMinors_1019_ = _args[8];
lean_object* v_pos_1020_ = _args[9];
lean_object* v_minorIdx_1021_ = _args[10];
lean_object* v_recursor_1022_ = _args[11];
lean_object* v_recursorType_1023_ = _args[12];
lean_object* v_consumedMajor_1024_ = _args[13];
lean_object* v_subgoals_1025_ = _args[14];
lean_object* v_a_1026_ = _args[15];
lean_object* v_a_1027_ = _args[16];
lean_object* v_a_1028_ = _args[17];
lean_object* v_a_1029_ = _args[18];
lean_object* v_a_1030_ = _args[19];
_start:
{
uint8_t v_consumedMajor_boxed_1031_; lean_object* v_res_1032_; 
v_consumedMajor_boxed_1031_ = lean_unbox(v_consumedMajor_1024_);
v_res_1032_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop(v_mvarId_1011_, v_givenNames_1012_, v_recursorInfo_1013_, v_reverted_1014_, v_major_1015_, v_indices_1016_, v_baseSubst_1017_, v_initialArity_1018_, v_numMinors_1019_, v_pos_1020_, v_minorIdx_1021_, v_recursor_1022_, v_recursorType_1023_, v_consumedMajor_boxed_1031_, v_subgoals_1025_, v_a_1026_, v_a_1027_, v_a_1028_, v_a_1029_);
lean_dec(v_a_1029_);
lean_dec_ref(v_a_1028_);
lean_dec(v_a_1027_);
lean_dec_ref(v_a_1026_);
lean_dec(v_numMinors_1019_);
lean_dec(v_initialArity_1018_);
lean_dec_ref(v_indices_1016_);
lean_dec_ref(v_reverted_1014_);
lean_dec_ref(v_recursorInfo_1013_);
lean_dec_ref(v_givenNames_1012_);
return v_res_1032_;
}
}
lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0(lean_object* v_mvarId_1033_, lean_object* v_val_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_){
_start:
{
lean_object* v___x_1040_; 
v___x_1040_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0___redArg(v_mvarId_1033_, v_val_1034_, v___y_1036_);
return v___x_1040_;
}
}
LEAN_EXPORT void l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1033_ = stack[0].m_obj;
lean_object* v_val_1034_ = stack[1].m_obj;
lean_object* v___y_1035_ = stack[2].m_obj;
lean_object* v___y_1036_ = stack[3].m_obj;
lean_object* v___y_1037_ = stack[4].m_obj;
lean_object* v___y_1038_ = stack[5].m_obj;
lean_object* v_res_1041_;
v_res_1041_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0(v_mvarId_1033_, v_val_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_);
stack->m_obj
 = v_res_1041_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0___boxed(lean_object* v_mvarId_1042_, lean_object* v_val_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_){
_start:
{
lean_object* v_res_1049_; 
v_res_1049_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0(v_mvarId_1042_, v_val_1043_, v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_);
lean_dec(v___y_1047_);
lean_dec_ref(v___y_1046_);
lean_dec(v___y_1045_);
lean_dec_ref(v___y_1044_);
return v_res_1049_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__2(lean_object* v___x_1050_, lean_object* v_reverted_1051_, lean_object* v_fst_1052_, lean_object* v_n_1053_, lean_object* v_j_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_){
_start:
{
lean_object* v___x_1057_; 
v___x_1057_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__2___redArg(v___x_1050_, v_reverted_1051_, v_fst_1052_, v_n_1053_, v_j_1054_, v_a_1056_);
return v___x_1057_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__2___boxed(lean_object* v___x_1058_, lean_object* v_reverted_1059_, lean_object* v_fst_1060_, lean_object* v_n_1061_, lean_object* v_j_1062_, lean_object* v_a_1063_, lean_object* v_a_1064_){
_start:
{
lean_object* v_res_1065_; 
v_res_1065_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__2(v___x_1058_, v_reverted_1059_, v_fst_1060_, v_n_1061_, v_j_1062_, v_a_1063_, v_a_1064_);
lean_dec(v_n_1061_);
lean_dec_ref(v_fst_1060_);
lean_dec_ref(v_reverted_1059_);
lean_dec(v___x_1058_);
return v_res_1065_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0(lean_object* v_00_u03b2_1066_, lean_object* v_x_1067_, lean_object* v_x_1068_, lean_object* v_x_1069_){
_start:
{
lean_object* v___x_1070_; 
v___x_1070_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0___redArg(v_x_1067_, v_x_1068_, v_x_1069_);
return v___x_1070_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1071_, lean_object* v_x_1072_, size_t v_x_1073_, size_t v_x_1074_, lean_object* v_x_1075_, lean_object* v_x_1076_){
_start:
{
lean_object* v___x_1077_; 
v___x_1077_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2___redArg(v_x_1072_, v_x_1073_, v_x_1074_, v_x_1075_, v_x_1076_);
return v___x_1077_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1072_ = stack[1].m_obj;
size_t v_x_1073_ = stack[2].m_num;
size_t v_x_1074_ = stack[3].m_num;
lean_object* v_x_1075_ = stack[4].m_obj;
lean_object* v_x_1076_ = stack[5].m_obj;
lean_object* v_res_1078_;
v_res_1078_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2(lean_box(0), v_x_1072_, v_x_1073_, v_x_1074_, v_x_1075_, v_x_1076_);
stack->m_obj
 = v_res_1078_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1079_, lean_object* v_x_1080_, lean_object* v_x_1081_, lean_object* v_x_1082_, lean_object* v_x_1083_, lean_object* v_x_1084_){
_start:
{
size_t v_x_9795__boxed_1085_; size_t v_x_9796__boxed_1086_; lean_object* v_res_1087_; 
v_x_9795__boxed_1085_ = lean_unbox_usize(v_x_1081_);
lean_dec(v_x_1081_);
v_x_9796__boxed_1086_ = lean_unbox_usize(v_x_1082_);
lean_dec(v_x_1082_);
v_res_1087_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2(v_00_u03b2_1079_, v_x_1080_, v_x_9795__boxed_1085_, v_x_9796__boxed_1086_, v_x_1083_, v_x_1084_);
return v_res_1087_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__8(lean_object* v_00_u03b2_1088_, lean_object* v_n_1089_, lean_object* v_k_1090_, lean_object* v_v_1091_){
_start:
{
lean_object* v___x_1092_; 
v___x_1092_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__8___redArg(v_n_1089_, v_k_1090_, v_v_1091_);
return v___x_1092_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__9(lean_object* v_00_u03b2_1093_, size_t v_depth_1094_, lean_object* v_keys_1095_, lean_object* v_vals_1096_, lean_object* v_heq_1097_, lean_object* v_i_1098_, lean_object* v_entries_1099_){
_start:
{
lean_object* v___x_1100_; 
v___x_1100_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__9___redArg(v_depth_1094_, v_keys_1095_, v_vals_1096_, v_i_1098_, v_entries_1099_);
return v___x_1100_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__9_0interp(lean_interpreter_value* stack)
{
size_t v_depth_1094_ = stack[1].m_num;
lean_object* v_keys_1095_ = stack[2].m_obj;
lean_object* v_vals_1096_ = stack[3].m_obj;
lean_object* v_i_1098_ = stack[5].m_obj;
lean_object* v_entries_1099_ = stack[6].m_obj;
lean_object* v_res_1101_;
v_res_1101_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__9(lean_box(0), v_depth_1094_, v_keys_1095_, v_vals_1096_, lean_box(0), v_i_1098_, v_entries_1099_);
stack->m_obj
 = v_res_1101_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__9___boxed(lean_object* v_00_u03b2_1102_, lean_object* v_depth_1103_, lean_object* v_keys_1104_, lean_object* v_vals_1105_, lean_object* v_heq_1106_, lean_object* v_i_1107_, lean_object* v_entries_1108_){
_start:
{
size_t v_depth_boxed_1109_; lean_object* v_res_1110_; 
v_depth_boxed_1109_ = lean_unbox_usize(v_depth_1103_);
lean_dec(v_depth_1103_);
v_res_1110_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__9(v_00_u03b2_1102_, v_depth_boxed_1109_, v_keys_1104_, v_vals_1105_, v_heq_1106_, v_i_1107_, v_entries_1108_);
lean_dec_ref(v_vals_1105_);
lean_dec_ref(v_keys_1104_);
return v_res_1110_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__8_spec__9(lean_object* v_00_u03b2_1111_, lean_object* v_x_1112_, lean_object* v_x_1113_, lean_object* v_x_1114_, lean_object* v_x_1115_){
_start:
{
lean_object* v___x_1116_; 
v___x_1116_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__8_spec__9___redArg(v_x_1112_, v_x_1113_, v_x_1114_, v_x_1115_);
return v___x_1116_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize(lean_object* v_mvarId_1119_, lean_object* v_givenNames_1120_, lean_object* v_recursorInfo_1121_, lean_object* v_reverted_1122_, lean_object* v_major_1123_, lean_object* v_indices_1124_, lean_object* v_baseSubst_1125_, lean_object* v_recursor_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_){
_start:
{
lean_object* v___x_1132_; 
lean_inc(v_mvarId_1119_);
v___x_1132_ = l_Lean_MVarId_getType(v_mvarId_1119_, v_a_1127_, v_a_1128_, v_a_1129_, v_a_1130_);
if (lean_obj_tag(v___x_1132_) == 0)
{
lean_object* v_a_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; 
v_a_1133_ = lean_ctor_get(v___x_1132_, 0);
lean_inc(v_a_1133_);
lean_dec_ref_known(v___x_1132_, 1);
v___x_1134_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTargetArity(v_a_1133_);
lean_inc(v_a_1130_);
lean_inc_ref(v_a_1129_);
lean_inc(v_a_1128_);
lean_inc_ref(v_a_1127_);
lean_inc_ref(v_recursor_1126_);
v___x_1135_ = lean_infer_type(v_recursor_1126_, v_a_1127_, v_a_1128_, v_a_1129_, v_a_1130_);
if (lean_obj_tag(v___x_1135_) == 0)
{
lean_object* v_a_1136_; lean_object* v_paramsPos_1137_; lean_object* v_produceMotive_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; uint8_t v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; 
v_a_1136_ = lean_ctor_get(v___x_1135_, 0);
lean_inc(v_a_1136_);
lean_dec_ref_known(v___x_1135_, 1);
v_paramsPos_1137_ = lean_ctor_get(v_recursorInfo_1121_, 5);
v_produceMotive_1138_ = lean_ctor_get(v_recursorInfo_1121_, 7);
v___x_1139_ = l_List_lengthTR___redArg(v_produceMotive_1138_);
v___x_1140_ = l_List_lengthTR___redArg(v_paramsPos_1137_);
v___x_1141_ = lean_unsigned_to_nat(1u);
v___x_1142_ = lean_nat_add(v___x_1140_, v___x_1141_);
lean_dec(v___x_1140_);
v___x_1143_ = lean_unsigned_to_nat(0u);
v___x_1144_ = 0;
v___x_1145_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize___closed__0));
v___x_1146_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop(v_mvarId_1119_, v_givenNames_1120_, v_recursorInfo_1121_, v_reverted_1122_, v_major_1123_, v_indices_1124_, v_baseSubst_1125_, v___x_1134_, v___x_1139_, v___x_1142_, v___x_1143_, v_recursor_1126_, v_a_1136_, v___x_1144_, v___x_1145_, v_a_1127_, v_a_1128_, v_a_1129_, v_a_1130_);
lean_dec(v___x_1139_);
lean_dec(v___x_1134_);
return v___x_1146_;
}
else
{
lean_object* v_a_1147_; lean_object* v___x_1149_; uint8_t v_isShared_1150_; uint8_t v_isSharedCheck_1154_; 
lean_dec(v___x_1134_);
lean_dec_ref(v_recursor_1126_);
lean_dec(v_baseSubst_1125_);
lean_dec_ref(v_major_1123_);
lean_dec(v_mvarId_1119_);
v_a_1147_ = lean_ctor_get(v___x_1135_, 0);
v_isSharedCheck_1154_ = !lean_is_exclusive(v___x_1135_);
if (v_isSharedCheck_1154_ == 0)
{
v___x_1149_ = v___x_1135_;
v_isShared_1150_ = v_isSharedCheck_1154_;
goto v_resetjp_1148_;
}
else
{
lean_inc(v_a_1147_);
lean_dec(v___x_1135_);
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
lean_object* v_a_1155_; lean_object* v___x_1157_; uint8_t v_isShared_1158_; uint8_t v_isSharedCheck_1162_; 
lean_dec_ref(v_recursor_1126_);
lean_dec(v_baseSubst_1125_);
lean_dec_ref(v_major_1123_);
lean_dec(v_mvarId_1119_);
v_a_1155_ = lean_ctor_get(v___x_1132_, 0);
v_isSharedCheck_1162_ = !lean_is_exclusive(v___x_1132_);
if (v_isSharedCheck_1162_ == 0)
{
v___x_1157_ = v___x_1132_;
v_isShared_1158_ = v_isSharedCheck_1162_;
goto v_resetjp_1156_;
}
else
{
lean_inc(v_a_1155_);
lean_dec(v___x_1132_);
v___x_1157_ = lean_box(0);
v_isShared_1158_ = v_isSharedCheck_1162_;
goto v_resetjp_1156_;
}
v_resetjp_1156_:
{
lean_object* v___x_1160_; 
if (v_isShared_1158_ == 0)
{
v___x_1160_ = v___x_1157_;
goto v_reusejp_1159_;
}
else
{
lean_object* v_reuseFailAlloc_1161_; 
v_reuseFailAlloc_1161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1161_, 0, v_a_1155_);
v___x_1160_ = v_reuseFailAlloc_1161_;
goto v_reusejp_1159_;
}
v_reusejp_1159_:
{
return v___x_1160_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1119_ = stack[0].m_obj;
lean_object* v_givenNames_1120_ = stack[1].m_obj;
lean_object* v_recursorInfo_1121_ = stack[2].m_obj;
lean_object* v_reverted_1122_ = stack[3].m_obj;
lean_object* v_major_1123_ = stack[4].m_obj;
lean_object* v_indices_1124_ = stack[5].m_obj;
lean_object* v_baseSubst_1125_ = stack[6].m_obj;
lean_object* v_recursor_1126_ = stack[7].m_obj;
lean_object* v_a_1127_ = stack[8].m_obj;
lean_object* v_a_1128_ = stack[9].m_obj;
lean_object* v_a_1129_ = stack[10].m_obj;
lean_object* v_a_1130_ = stack[11].m_obj;
lean_object* v_res_1163_;
v_res_1163_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize(v_mvarId_1119_, v_givenNames_1120_, v_recursorInfo_1121_, v_reverted_1122_, v_major_1123_, v_indices_1124_, v_baseSubst_1125_, v_recursor_1126_, v_a_1127_, v_a_1128_, v_a_1129_, v_a_1130_);
stack->m_obj
 = v_res_1163_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize___boxed(lean_object* v_mvarId_1164_, lean_object* v_givenNames_1165_, lean_object* v_recursorInfo_1166_, lean_object* v_reverted_1167_, lean_object* v_major_1168_, lean_object* v_indices_1169_, lean_object* v_baseSubst_1170_, lean_object* v_recursor_1171_, lean_object* v_a_1172_, lean_object* v_a_1173_, lean_object* v_a_1174_, lean_object* v_a_1175_, lean_object* v_a_1176_){
_start:
{
lean_object* v_res_1177_; 
v_res_1177_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize(v_mvarId_1164_, v_givenNames_1165_, v_recursorInfo_1166_, v_reverted_1167_, v_major_1168_, v_indices_1169_, v_baseSubst_1170_, v_recursor_1171_, v_a_1172_, v_a_1173_, v_a_1174_, v_a_1175_);
lean_dec(v_a_1175_);
lean_dec_ref(v_a_1174_);
lean_dec(v_a_1173_);
lean_dec_ref(v_a_1172_);
lean_dec_ref(v_indices_1169_);
lean_dec_ref(v_reverted_1167_);
lean_dec_ref(v_recursorInfo_1166_);
lean_dec_ref(v_givenNames_1165_);
return v_res_1177_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg___closed__1(void){
_start:
{
lean_object* v___x_1179_; lean_object* v___x_1180_; 
v___x_1179_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg___closed__0));
v___x_1180_ = l_Lean_stringToMessageData(v___x_1179_);
return v___x_1180_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg(lean_object* v_tacticName_1181_, lean_object* v_mvarId_1182_, lean_object* v_majorType_1183_, lean_object* v_a_1184_, lean_object* v_a_1185_, lean_object* v_a_1186_, lean_object* v_a_1187_){
_start:
{
lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; 
v___x_1189_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg___closed__1, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg___closed__1);
v___x_1190_ = l_Lean_indentExpr(v_majorType_1183_);
v___x_1191_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1191_, 0, v___x_1189_);
lean_ctor_set(v___x_1191_, 1, v___x_1190_);
v___x_1192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1192_, 0, v___x_1191_);
v___x_1193_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1181_, v_mvarId_1182_, v___x_1192_, v_a_1184_, v_a_1185_, v_a_1186_, v_a_1187_);
return v___x_1193_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_tacticName_1181_ = stack[0].m_obj;
lean_object* v_mvarId_1182_ = stack[1].m_obj;
lean_object* v_majorType_1183_ = stack[2].m_obj;
lean_object* v_a_1184_ = stack[3].m_obj;
lean_object* v_a_1185_ = stack[4].m_obj;
lean_object* v_a_1186_ = stack[5].m_obj;
lean_object* v_a_1187_ = stack[6].m_obj;
lean_object* v_res_1194_;
v_res_1194_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg(v_tacticName_1181_, v_mvarId_1182_, v_majorType_1183_, v_a_1184_, v_a_1185_, v_a_1186_, v_a_1187_);
stack->m_obj
 = v_res_1194_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg___boxed(lean_object* v_tacticName_1195_, lean_object* v_mvarId_1196_, lean_object* v_majorType_1197_, lean_object* v_a_1198_, lean_object* v_a_1199_, lean_object* v_a_1200_, lean_object* v_a_1201_, lean_object* v_a_1202_){
_start:
{
lean_object* v_res_1203_; 
v_res_1203_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg(v_tacticName_1195_, v_mvarId_1196_, v_majorType_1197_, v_a_1198_, v_a_1199_, v_a_1200_, v_a_1201_);
lean_dec(v_a_1201_);
lean_dec_ref(v_a_1200_);
lean_dec(v_a_1199_);
lean_dec_ref(v_a_1198_);
return v_res_1203_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType(lean_object* v_00_u03b1_1204_, lean_object* v_tacticName_1205_, lean_object* v_mvarId_1206_, lean_object* v_majorType_1207_, lean_object* v_a_1208_, lean_object* v_a_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_){
_start:
{
lean_object* v___x_1213_; 
v___x_1213_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg(v_tacticName_1205_, v_mvarId_1206_, v_majorType_1207_, v_a_1208_, v_a_1209_, v_a_1210_, v_a_1211_);
return v___x_1213_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType_0interp(lean_interpreter_value* stack)
{
lean_object* v_tacticName_1205_ = stack[1].m_obj;
lean_object* v_mvarId_1206_ = stack[2].m_obj;
lean_object* v_majorType_1207_ = stack[3].m_obj;
lean_object* v_a_1208_ = stack[4].m_obj;
lean_object* v_a_1209_ = stack[5].m_obj;
lean_object* v_a_1210_ = stack[6].m_obj;
lean_object* v_a_1211_ = stack[7].m_obj;
lean_object* v_res_1214_;
v_res_1214_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType(lean_box(0), v_tacticName_1205_, v_mvarId_1206_, v_majorType_1207_, v_a_1208_, v_a_1209_, v_a_1210_, v_a_1211_);
stack->m_obj
 = v_res_1214_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___boxed(lean_object* v_00_u03b1_1215_, lean_object* v_tacticName_1216_, lean_object* v_mvarId_1217_, lean_object* v_majorType_1218_, lean_object* v_a_1219_, lean_object* v_a_1220_, lean_object* v_a_1221_, lean_object* v_a_1222_, lean_object* v_a_1223_){
_start:
{
lean_object* v_res_1224_; 
v_res_1224_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType(v_00_u03b1_1215_, v_tacticName_1216_, v_mvarId_1217_, v_majorType_1218_, v_a_1219_, v_a_1220_, v_a_1221_, v_a_1222_);
lean_dec(v_a_1222_);
lean_dec_ref(v_a_1221_);
lean_dec(v_a_1220_);
lean_dec_ref(v_a_1219_);
return v_res_1224_;
}
}
uint8_t l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___lam__0(lean_object* v_fvarId_1225_, lean_object* v_x_1226_){
_start:
{
uint8_t v___x_1227_; 
v___x_1227_ = l_Lean_instBEqFVarId_beq(v_fvarId_1225_, v_x_1226_);
return v___x_1227_;
}
}
LEAN_EXPORT void l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_1225_ = stack[0].m_obj;
lean_object* v_x_1226_ = stack[1].m_obj;
uint8_t v_res_1228_;
v_res_1228_ = l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___lam__0(v_fvarId_1225_, v_x_1226_);
stack->m_num = v_res_1228_;
}
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___lam__0___boxed(lean_object* v_fvarId_1229_, lean_object* v_x_1230_){
_start:
{
uint8_t v_res_1231_; lean_object* v_r_1232_; 
v_res_1231_ = l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___lam__0(v_fvarId_1229_, v_x_1230_);
lean_dec(v_x_1230_);
lean_dec(v_fvarId_1229_);
v_r_1232_ = lean_box(v_res_1231_);
return v_r_1232_;
}
}
uint8_t l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___lam__1(lean_object* v_x_1233_){
_start:
{
uint8_t v___x_1234_; 
v___x_1234_ = 0;
return v___x_1234_;
}
}
LEAN_EXPORT void l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1233_ = stack[0].m_obj;
uint8_t v_res_1235_;
v_res_1235_ = l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___lam__1(v_x_1233_);
stack->m_num = v_res_1235_;
}
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___lam__1___boxed(lean_object* v_x_1236_){
_start:
{
uint8_t v_res_1237_; lean_object* v_r_1238_; 
v_res_1237_ = l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___lam__1(v_x_1236_);
lean_dec(v_x_1236_);
v_r_1238_ = lean_box(v_res_1237_);
return v_r_1238_;
}
}
static lean_object* _init_l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; 
v___x_1240_ = lean_box(0);
v___x_1241_ = lean_unsigned_to_nat(16u);
v___x_1242_ = lean_mk_array(v___x_1241_, v___x_1240_);
return v___x_1242_;
}
}
static lean_object* _init_l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; 
v___x_1243_ = lean_obj_once(&l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__1, &l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__1_once, _init_l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__1);
v___x_1244_ = lean_unsigned_to_nat(0u);
v___x_1245_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1245_, 0, v___x_1244_);
lean_ctor_set(v___x_1245_, 1, v___x_1243_);
return v___x_1245_;
}
}
lean_object* l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg(lean_object* v_localDecl_1246_, lean_object* v_fvarId_1247_, uint8_t v_generalizeNondepLet_1248_, lean_object* v___y_1249_){
_start:
{
uint8_t v_fst_1252_; lean_object* v_snd_1253_; lean_object* v___y_1272_; lean_object* v___f_1276_; lean_object* v___f_1277_; 
v___f_1276_ = lean_alloc_closure((void*)(l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1276_, 0, v_fvarId_1247_);
v___f_1277_ = ((lean_object*)(l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__0));
if (lean_obj_tag(v_localDecl_1246_) == 0)
{
lean_object* v_type_1278_; lean_object* v___x_1279_; uint8_t v_fst_1281_; lean_object* v_mctx_1282_; lean_object* v___y_1300_; lean_object* v_mctx_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; uint8_t v___x_1308_; 
v_type_1278_ = lean_ctor_get(v_localDecl_1246_, 3);
lean_inc_ref(v_type_1278_);
lean_dec_ref_known(v_localDecl_1246_, 4);
v___x_1279_ = lean_st_ref_get(v___y_1249_);
v_mctx_1305_ = lean_ctor_get(v___x_1279_, 0);
lean_inc_ref_n(v_mctx_1305_, 2);
lean_dec(v___x_1279_);
v___x_1306_ = lean_obj_once(&l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__2, &l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__2_once, _init_l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__2);
v___x_1307_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1307_, 0, v___x_1306_);
lean_ctor_set(v___x_1307_, 1, v_mctx_1305_);
v___x_1308_ = l_Lean_Expr_hasFVar(v_type_1278_);
if (v___x_1308_ == 0)
{
uint8_t v___x_1309_; 
v___x_1309_ = l_Lean_Expr_hasMVar(v_type_1278_);
if (v___x_1309_ == 0)
{
lean_dec_ref_known(v___x_1307_, 2);
lean_dec_ref(v_type_1278_);
lean_dec_ref(v___f_1276_);
v_fst_1281_ = v___x_1309_;
v_mctx_1282_ = v_mctx_1305_;
goto v___jp_1280_;
}
else
{
lean_object* v___x_1310_; 
lean_dec_ref(v_mctx_1305_);
v___x_1310_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1276_, v___f_1277_, v_type_1278_, v___x_1307_);
v___y_1300_ = v___x_1310_;
goto v___jp_1299_;
}
}
else
{
lean_object* v___x_1311_; 
lean_dec_ref(v_mctx_1305_);
v___x_1311_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1276_, v___f_1277_, v_type_1278_, v___x_1307_);
v___y_1300_ = v___x_1311_;
goto v___jp_1299_;
}
v___jp_1280_:
{
lean_object* v___x_1283_; lean_object* v_cache_1284_; lean_object* v_zetaDeltaFVarIds_1285_; lean_object* v_postponed_1286_; lean_object* v_diag_1287_; lean_object* v___x_1289_; uint8_t v_isShared_1290_; uint8_t v_isSharedCheck_1297_; 
v___x_1283_ = lean_st_ref_take(v___y_1249_);
v_cache_1284_ = lean_ctor_get(v___x_1283_, 1);
v_zetaDeltaFVarIds_1285_ = lean_ctor_get(v___x_1283_, 2);
v_postponed_1286_ = lean_ctor_get(v___x_1283_, 3);
v_diag_1287_ = lean_ctor_get(v___x_1283_, 4);
v_isSharedCheck_1297_ = !lean_is_exclusive(v___x_1283_);
if (v_isSharedCheck_1297_ == 0)
{
lean_object* v_unused_1298_; 
v_unused_1298_ = lean_ctor_get(v___x_1283_, 0);
lean_dec(v_unused_1298_);
v___x_1289_ = v___x_1283_;
v_isShared_1290_ = v_isSharedCheck_1297_;
goto v_resetjp_1288_;
}
else
{
lean_inc(v_diag_1287_);
lean_inc(v_postponed_1286_);
lean_inc(v_zetaDeltaFVarIds_1285_);
lean_inc(v_cache_1284_);
lean_dec(v___x_1283_);
v___x_1289_ = lean_box(0);
v_isShared_1290_ = v_isSharedCheck_1297_;
goto v_resetjp_1288_;
}
v_resetjp_1288_:
{
lean_object* v___x_1292_; 
if (v_isShared_1290_ == 0)
{
lean_ctor_set(v___x_1289_, 0, v_mctx_1282_);
v___x_1292_ = v___x_1289_;
goto v_reusejp_1291_;
}
else
{
lean_object* v_reuseFailAlloc_1296_; 
v_reuseFailAlloc_1296_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1296_, 0, v_mctx_1282_);
lean_ctor_set(v_reuseFailAlloc_1296_, 1, v_cache_1284_);
lean_ctor_set(v_reuseFailAlloc_1296_, 2, v_zetaDeltaFVarIds_1285_);
lean_ctor_set(v_reuseFailAlloc_1296_, 3, v_postponed_1286_);
lean_ctor_set(v_reuseFailAlloc_1296_, 4, v_diag_1287_);
v___x_1292_ = v_reuseFailAlloc_1296_;
goto v_reusejp_1291_;
}
v_reusejp_1291_:
{
lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; 
v___x_1293_ = lean_st_ref_put(v___y_1249_, v___x_1292_);
v___x_1294_ = lean_box(v_fst_1281_);
v___x_1295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1295_, 0, v___x_1294_);
return v___x_1295_;
}
}
}
v___jp_1299_:
{
lean_object* v_snd_1301_; lean_object* v_fst_1302_; lean_object* v_mctx_1303_; uint8_t v___x_1304_; 
v_snd_1301_ = lean_ctor_get(v___y_1300_, 1);
lean_inc(v_snd_1301_);
v_fst_1302_ = lean_ctor_get(v___y_1300_, 0);
lean_inc(v_fst_1302_);
lean_dec_ref(v___y_1300_);
v_mctx_1303_ = lean_ctor_get(v_snd_1301_, 1);
lean_inc_ref(v_mctx_1303_);
lean_dec(v_snd_1301_);
v___x_1304_ = lean_unbox(v_fst_1302_);
lean_dec(v_fst_1302_);
v_fst_1281_ = v___x_1304_;
v_mctx_1282_ = v_mctx_1303_;
goto v___jp_1280_;
}
}
else
{
lean_object* v_type_1312_; lean_object* v_value_1313_; uint8_t v_nondep_1314_; uint8_t v_fst_1316_; lean_object* v_snd_1317_; lean_object* v___y_1323_; 
v_type_1312_ = lean_ctor_get(v_localDecl_1246_, 3);
lean_inc_ref(v_type_1312_);
v_value_1313_ = lean_ctor_get(v_localDecl_1246_, 4);
lean_inc_ref(v_value_1313_);
v_nondep_1314_ = lean_ctor_get_uint8(v_localDecl_1246_, sizeof(void*)*5);
lean_dec_ref_known(v_localDecl_1246_, 5);
if (v_generalizeNondepLet_1248_ == 0)
{
goto v___jp_1327_;
}
else
{
if (v_nondep_1314_ == 0)
{
goto v___jp_1327_;
}
else
{
lean_object* v___x_1336_; uint8_t v_fst_1338_; lean_object* v_mctx_1339_; lean_object* v___y_1357_; lean_object* v_mctx_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; uint8_t v___x_1365_; 
lean_dec_ref(v_value_1313_);
v___x_1336_ = lean_st_ref_get(v___y_1249_);
v_mctx_1362_ = lean_ctor_get(v___x_1336_, 0);
lean_inc_ref_n(v_mctx_1362_, 2);
lean_dec(v___x_1336_);
v___x_1363_ = lean_obj_once(&l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__2, &l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__2_once, _init_l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__2);
v___x_1364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1364_, 0, v___x_1363_);
lean_ctor_set(v___x_1364_, 1, v_mctx_1362_);
v___x_1365_ = l_Lean_Expr_hasFVar(v_type_1312_);
if (v___x_1365_ == 0)
{
uint8_t v___x_1366_; 
v___x_1366_ = l_Lean_Expr_hasMVar(v_type_1312_);
if (v___x_1366_ == 0)
{
lean_dec_ref_known(v___x_1364_, 2);
lean_dec_ref(v_type_1312_);
lean_dec_ref(v___f_1276_);
v_fst_1338_ = v___x_1366_;
v_mctx_1339_ = v_mctx_1362_;
goto v___jp_1337_;
}
else
{
lean_object* v___x_1367_; 
lean_dec_ref(v_mctx_1362_);
v___x_1367_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1276_, v___f_1277_, v_type_1312_, v___x_1364_);
v___y_1357_ = v___x_1367_;
goto v___jp_1356_;
}
}
else
{
lean_object* v___x_1368_; 
lean_dec_ref(v_mctx_1362_);
v___x_1368_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1276_, v___f_1277_, v_type_1312_, v___x_1364_);
v___y_1357_ = v___x_1368_;
goto v___jp_1356_;
}
v___jp_1337_:
{
lean_object* v___x_1340_; lean_object* v_cache_1341_; lean_object* v_zetaDeltaFVarIds_1342_; lean_object* v_postponed_1343_; lean_object* v_diag_1344_; lean_object* v___x_1346_; uint8_t v_isShared_1347_; uint8_t v_isSharedCheck_1354_; 
v___x_1340_ = lean_st_ref_take(v___y_1249_);
v_cache_1341_ = lean_ctor_get(v___x_1340_, 1);
v_zetaDeltaFVarIds_1342_ = lean_ctor_get(v___x_1340_, 2);
v_postponed_1343_ = lean_ctor_get(v___x_1340_, 3);
v_diag_1344_ = lean_ctor_get(v___x_1340_, 4);
v_isSharedCheck_1354_ = !lean_is_exclusive(v___x_1340_);
if (v_isSharedCheck_1354_ == 0)
{
lean_object* v_unused_1355_; 
v_unused_1355_ = lean_ctor_get(v___x_1340_, 0);
lean_dec(v_unused_1355_);
v___x_1346_ = v___x_1340_;
v_isShared_1347_ = v_isSharedCheck_1354_;
goto v_resetjp_1345_;
}
else
{
lean_inc(v_diag_1344_);
lean_inc(v_postponed_1343_);
lean_inc(v_zetaDeltaFVarIds_1342_);
lean_inc(v_cache_1341_);
lean_dec(v___x_1340_);
v___x_1346_ = lean_box(0);
v_isShared_1347_ = v_isSharedCheck_1354_;
goto v_resetjp_1345_;
}
v_resetjp_1345_:
{
lean_object* v___x_1349_; 
if (v_isShared_1347_ == 0)
{
lean_ctor_set(v___x_1346_, 0, v_mctx_1339_);
v___x_1349_ = v___x_1346_;
goto v_reusejp_1348_;
}
else
{
lean_object* v_reuseFailAlloc_1353_; 
v_reuseFailAlloc_1353_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1353_, 0, v_mctx_1339_);
lean_ctor_set(v_reuseFailAlloc_1353_, 1, v_cache_1341_);
lean_ctor_set(v_reuseFailAlloc_1353_, 2, v_zetaDeltaFVarIds_1342_);
lean_ctor_set(v_reuseFailAlloc_1353_, 3, v_postponed_1343_);
lean_ctor_set(v_reuseFailAlloc_1353_, 4, v_diag_1344_);
v___x_1349_ = v_reuseFailAlloc_1353_;
goto v_reusejp_1348_;
}
v_reusejp_1348_:
{
lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; 
v___x_1350_ = lean_st_ref_put(v___y_1249_, v___x_1349_);
v___x_1351_ = lean_box(v_fst_1338_);
v___x_1352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1352_, 0, v___x_1351_);
return v___x_1352_;
}
}
}
v___jp_1356_:
{
lean_object* v_snd_1358_; lean_object* v_fst_1359_; lean_object* v_mctx_1360_; uint8_t v___x_1361_; 
v_snd_1358_ = lean_ctor_get(v___y_1357_, 1);
lean_inc(v_snd_1358_);
v_fst_1359_ = lean_ctor_get(v___y_1357_, 0);
lean_inc(v_fst_1359_);
lean_dec_ref(v___y_1357_);
v_mctx_1360_ = lean_ctor_get(v_snd_1358_, 1);
lean_inc_ref(v_mctx_1360_);
lean_dec(v_snd_1358_);
v___x_1361_ = lean_unbox(v_fst_1359_);
lean_dec(v_fst_1359_);
v_fst_1338_ = v___x_1361_;
v_mctx_1339_ = v_mctx_1360_;
goto v___jp_1337_;
}
}
}
v___jp_1315_:
{
if (v_fst_1316_ == 0)
{
uint8_t v___x_1318_; 
v___x_1318_ = l_Lean_Expr_hasFVar(v_value_1313_);
if (v___x_1318_ == 0)
{
uint8_t v___x_1319_; 
v___x_1319_ = l_Lean_Expr_hasMVar(v_value_1313_);
if (v___x_1319_ == 0)
{
lean_dec_ref(v_value_1313_);
lean_dec_ref(v___f_1276_);
v_fst_1252_ = v___x_1319_;
v_snd_1253_ = v_snd_1317_;
goto v___jp_1251_;
}
else
{
lean_object* v___x_1320_; 
v___x_1320_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1276_, v___f_1277_, v_value_1313_, v_snd_1317_);
v___y_1272_ = v___x_1320_;
goto v___jp_1271_;
}
}
else
{
lean_object* v___x_1321_; 
v___x_1321_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1276_, v___f_1277_, v_value_1313_, v_snd_1317_);
v___y_1272_ = v___x_1321_;
goto v___jp_1271_;
}
}
else
{
lean_dec_ref(v_value_1313_);
lean_dec_ref(v___f_1276_);
v_fst_1252_ = v_fst_1316_;
v_snd_1253_ = v_snd_1317_;
goto v___jp_1251_;
}
}
v___jp_1322_:
{
lean_object* v_fst_1324_; lean_object* v_snd_1325_; uint8_t v___x_1326_; 
v_fst_1324_ = lean_ctor_get(v___y_1323_, 0);
lean_inc(v_fst_1324_);
v_snd_1325_ = lean_ctor_get(v___y_1323_, 1);
lean_inc(v_snd_1325_);
lean_dec_ref(v___y_1323_);
v___x_1326_ = lean_unbox(v_fst_1324_);
lean_dec(v_fst_1324_);
v_fst_1316_ = v___x_1326_;
v_snd_1317_ = v_snd_1325_;
goto v___jp_1315_;
}
v___jp_1327_:
{
lean_object* v___x_1328_; lean_object* v_mctx_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; uint8_t v___x_1332_; 
v___x_1328_ = lean_st_ref_get(v___y_1249_);
v_mctx_1329_ = lean_ctor_get(v___x_1328_, 0);
lean_inc_ref(v_mctx_1329_);
lean_dec(v___x_1328_);
v___x_1330_ = lean_obj_once(&l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__2, &l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__2_once, _init_l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__2);
v___x_1331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1331_, 0, v___x_1330_);
lean_ctor_set(v___x_1331_, 1, v_mctx_1329_);
v___x_1332_ = l_Lean_Expr_hasFVar(v_type_1312_);
if (v___x_1332_ == 0)
{
uint8_t v___x_1333_; 
v___x_1333_ = l_Lean_Expr_hasMVar(v_type_1312_);
if (v___x_1333_ == 0)
{
lean_dec_ref(v_type_1312_);
v_fst_1316_ = v___x_1333_;
v_snd_1317_ = v___x_1331_;
goto v___jp_1315_;
}
else
{
lean_object* v___x_1334_; 
lean_inc_ref(v___f_1276_);
v___x_1334_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1276_, v___f_1277_, v_type_1312_, v___x_1331_);
v___y_1323_ = v___x_1334_;
goto v___jp_1322_;
}
}
else
{
lean_object* v___x_1335_; 
lean_inc_ref(v___f_1276_);
v___x_1335_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1276_, v___f_1277_, v_type_1312_, v___x_1331_);
v___y_1323_ = v___x_1335_;
goto v___jp_1322_;
}
}
}
v___jp_1251_:
{
lean_object* v_mctx_1254_; lean_object* v___x_1255_; lean_object* v_cache_1256_; lean_object* v_zetaDeltaFVarIds_1257_; lean_object* v_postponed_1258_; lean_object* v_diag_1259_; lean_object* v___x_1261_; uint8_t v_isShared_1262_; uint8_t v_isSharedCheck_1269_; 
v_mctx_1254_ = lean_ctor_get(v_snd_1253_, 1);
lean_inc_ref(v_mctx_1254_);
lean_dec_ref(v_snd_1253_);
v___x_1255_ = lean_st_ref_take(v___y_1249_);
v_cache_1256_ = lean_ctor_get(v___x_1255_, 1);
v_zetaDeltaFVarIds_1257_ = lean_ctor_get(v___x_1255_, 2);
v_postponed_1258_ = lean_ctor_get(v___x_1255_, 3);
v_diag_1259_ = lean_ctor_get(v___x_1255_, 4);
v_isSharedCheck_1269_ = !lean_is_exclusive(v___x_1255_);
if (v_isSharedCheck_1269_ == 0)
{
lean_object* v_unused_1270_; 
v_unused_1270_ = lean_ctor_get(v___x_1255_, 0);
lean_dec(v_unused_1270_);
v___x_1261_ = v___x_1255_;
v_isShared_1262_ = v_isSharedCheck_1269_;
goto v_resetjp_1260_;
}
else
{
lean_inc(v_diag_1259_);
lean_inc(v_postponed_1258_);
lean_inc(v_zetaDeltaFVarIds_1257_);
lean_inc(v_cache_1256_);
lean_dec(v___x_1255_);
v___x_1261_ = lean_box(0);
v_isShared_1262_ = v_isSharedCheck_1269_;
goto v_resetjp_1260_;
}
v_resetjp_1260_:
{
lean_object* v___x_1264_; 
if (v_isShared_1262_ == 0)
{
lean_ctor_set(v___x_1261_, 0, v_mctx_1254_);
v___x_1264_ = v___x_1261_;
goto v_reusejp_1263_;
}
else
{
lean_object* v_reuseFailAlloc_1268_; 
v_reuseFailAlloc_1268_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1268_, 0, v_mctx_1254_);
lean_ctor_set(v_reuseFailAlloc_1268_, 1, v_cache_1256_);
lean_ctor_set(v_reuseFailAlloc_1268_, 2, v_zetaDeltaFVarIds_1257_);
lean_ctor_set(v_reuseFailAlloc_1268_, 3, v_postponed_1258_);
lean_ctor_set(v_reuseFailAlloc_1268_, 4, v_diag_1259_);
v___x_1264_ = v_reuseFailAlloc_1268_;
goto v_reusejp_1263_;
}
v_reusejp_1263_:
{
lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; 
v___x_1265_ = lean_st_ref_put(v___y_1249_, v___x_1264_);
v___x_1266_ = lean_box(v_fst_1252_);
v___x_1267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1267_, 0, v___x_1266_);
return v___x_1267_;
}
}
}
v___jp_1271_:
{
lean_object* v_fst_1273_; lean_object* v_snd_1274_; uint8_t v___x_1275_; 
v_fst_1273_ = lean_ctor_get(v___y_1272_, 0);
lean_inc(v_fst_1273_);
v_snd_1274_ = lean_ctor_get(v___y_1272_, 1);
lean_inc(v_snd_1274_);
lean_dec_ref(v___y_1272_);
v___x_1275_ = lean_unbox(v_fst_1273_);
lean_dec(v_fst_1273_);
v_fst_1252_ = v___x_1275_;
v_snd_1253_ = v_snd_1274_;
goto v___jp_1251_;
}
}
}
LEAN_EXPORT void l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_localDecl_1246_ = stack[0].m_obj;
lean_object* v_fvarId_1247_ = stack[1].m_obj;
uint8_t v_generalizeNondepLet_1248_ = stack[2].m_num;
lean_object* v___y_1249_ = stack[3].m_obj;
lean_object* v_res_1369_;
v_res_1369_ = l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg(v_localDecl_1246_, v_fvarId_1247_, v_generalizeNondepLet_1248_, v___y_1249_);
stack->m_obj
 = v_res_1369_;
}
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___boxed(lean_object* v_localDecl_1370_, lean_object* v_fvarId_1371_, lean_object* v_generalizeNondepLet_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_){
_start:
{
uint8_t v_generalizeNondepLet_boxed_1375_; lean_object* v_res_1376_; 
v_generalizeNondepLet_boxed_1375_ = lean_unbox(v_generalizeNondepLet_1372_);
v_res_1376_ = l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg(v_localDecl_1370_, v_fvarId_1371_, v_generalizeNondepLet_boxed_1375_, v___y_1373_);
lean_dec(v___y_1373_);
return v_res_1376_;
}
}
lean_object* l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1(lean_object* v_localDecl_1377_, lean_object* v_fvarId_1378_, uint8_t v_generalizeNondepLet_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_){
_start:
{
lean_object* v___x_1385_; 
v___x_1385_ = l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg(v_localDecl_1377_, v_fvarId_1378_, v_generalizeNondepLet_1379_, v___y_1381_);
return v___x_1385_;
}
}
LEAN_EXPORT void l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_localDecl_1377_ = stack[0].m_obj;
lean_object* v_fvarId_1378_ = stack[1].m_obj;
uint8_t v_generalizeNondepLet_1379_ = stack[2].m_num;
lean_object* v___y_1380_ = stack[3].m_obj;
lean_object* v___y_1381_ = stack[4].m_obj;
lean_object* v___y_1382_ = stack[5].m_obj;
lean_object* v___y_1383_ = stack[6].m_obj;
lean_object* v_res_1386_;
v_res_1386_ = l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1(v_localDecl_1377_, v_fvarId_1378_, v_generalizeNondepLet_1379_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_);
stack->m_obj
 = v_res_1386_;
}
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___boxed(lean_object* v_localDecl_1387_, lean_object* v_fvarId_1388_, lean_object* v_generalizeNondepLet_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_){
_start:
{
uint8_t v_generalizeNondepLet_boxed_1395_; lean_object* v_res_1396_; 
v_generalizeNondepLet_boxed_1395_ = lean_unbox(v_generalizeNondepLet_1389_);
v_res_1396_ = l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1(v_localDecl_1387_, v_fvarId_1388_, v_generalizeNondepLet_boxed_1395_, v___y_1390_, v___y_1391_, v___y_1392_, v___y_1393_);
lean_dec(v___y_1393_);
lean_dec_ref(v___y_1392_);
lean_dec(v___y_1391_);
lean_dec_ref(v___y_1390_);
return v_res_1396_;
}
}
lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2___redArg(lean_object* v_e_1397_, lean_object* v_fvarId_1398_, lean_object* v___y_1399_){
_start:
{
lean_object* v___f_1401_; lean_object* v___f_1402_; lean_object* v___x_1403_; uint8_t v_fst_1405_; lean_object* v_mctx_1406_; lean_object* v___y_1424_; lean_object* v_mctx_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; uint8_t v___x_1432_; 
v___f_1401_ = ((lean_object*)(l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__0));
v___f_1402_ = lean_alloc_closure((void*)(l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1402_, 0, v_fvarId_1398_);
v___x_1403_ = lean_st_ref_get(v___y_1399_);
v_mctx_1429_ = lean_ctor_get(v___x_1403_, 0);
lean_inc_ref_n(v_mctx_1429_, 2);
lean_dec(v___x_1403_);
v___x_1430_ = lean_obj_once(&l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__2, &l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__2_once, _init_l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__2);
v___x_1431_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1431_, 0, v___x_1430_);
lean_ctor_set(v___x_1431_, 1, v_mctx_1429_);
v___x_1432_ = l_Lean_Expr_hasFVar(v_e_1397_);
if (v___x_1432_ == 0)
{
uint8_t v___x_1433_; 
v___x_1433_ = l_Lean_Expr_hasMVar(v_e_1397_);
if (v___x_1433_ == 0)
{
lean_dec_ref_known(v___x_1431_, 2);
lean_dec_ref(v___f_1402_);
lean_dec_ref(v_e_1397_);
v_fst_1405_ = v___x_1433_;
v_mctx_1406_ = v_mctx_1429_;
goto v___jp_1404_;
}
else
{
lean_object* v___x_1434_; 
lean_dec_ref(v_mctx_1429_);
v___x_1434_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1402_, v___f_1401_, v_e_1397_, v___x_1431_);
v___y_1424_ = v___x_1434_;
goto v___jp_1423_;
}
}
else
{
lean_object* v___x_1435_; 
lean_dec_ref(v_mctx_1429_);
v___x_1435_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1402_, v___f_1401_, v_e_1397_, v___x_1431_);
v___y_1424_ = v___x_1435_;
goto v___jp_1423_;
}
v___jp_1404_:
{
lean_object* v___x_1407_; lean_object* v_cache_1408_; lean_object* v_zetaDeltaFVarIds_1409_; lean_object* v_postponed_1410_; lean_object* v_diag_1411_; lean_object* v___x_1413_; uint8_t v_isShared_1414_; uint8_t v_isSharedCheck_1421_; 
v___x_1407_ = lean_st_ref_take(v___y_1399_);
v_cache_1408_ = lean_ctor_get(v___x_1407_, 1);
v_zetaDeltaFVarIds_1409_ = lean_ctor_get(v___x_1407_, 2);
v_postponed_1410_ = lean_ctor_get(v___x_1407_, 3);
v_diag_1411_ = lean_ctor_get(v___x_1407_, 4);
v_isSharedCheck_1421_ = !lean_is_exclusive(v___x_1407_);
if (v_isSharedCheck_1421_ == 0)
{
lean_object* v_unused_1422_; 
v_unused_1422_ = lean_ctor_get(v___x_1407_, 0);
lean_dec(v_unused_1422_);
v___x_1413_ = v___x_1407_;
v_isShared_1414_ = v_isSharedCheck_1421_;
goto v_resetjp_1412_;
}
else
{
lean_inc(v_diag_1411_);
lean_inc(v_postponed_1410_);
lean_inc(v_zetaDeltaFVarIds_1409_);
lean_inc(v_cache_1408_);
lean_dec(v___x_1407_);
v___x_1413_ = lean_box(0);
v_isShared_1414_ = v_isSharedCheck_1421_;
goto v_resetjp_1412_;
}
v_resetjp_1412_:
{
lean_object* v___x_1416_; 
if (v_isShared_1414_ == 0)
{
lean_ctor_set(v___x_1413_, 0, v_mctx_1406_);
v___x_1416_ = v___x_1413_;
goto v_reusejp_1415_;
}
else
{
lean_object* v_reuseFailAlloc_1420_; 
v_reuseFailAlloc_1420_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1420_, 0, v_mctx_1406_);
lean_ctor_set(v_reuseFailAlloc_1420_, 1, v_cache_1408_);
lean_ctor_set(v_reuseFailAlloc_1420_, 2, v_zetaDeltaFVarIds_1409_);
lean_ctor_set(v_reuseFailAlloc_1420_, 3, v_postponed_1410_);
lean_ctor_set(v_reuseFailAlloc_1420_, 4, v_diag_1411_);
v___x_1416_ = v_reuseFailAlloc_1420_;
goto v_reusejp_1415_;
}
v_reusejp_1415_:
{
lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; 
v___x_1417_ = lean_st_ref_put(v___y_1399_, v___x_1416_);
v___x_1418_ = lean_box(v_fst_1405_);
v___x_1419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1419_, 0, v___x_1418_);
return v___x_1419_;
}
}
}
v___jp_1423_:
{
lean_object* v_snd_1425_; lean_object* v_fst_1426_; lean_object* v_mctx_1427_; uint8_t v___x_1428_; 
v_snd_1425_ = lean_ctor_get(v___y_1424_, 1);
lean_inc(v_snd_1425_);
v_fst_1426_ = lean_ctor_get(v___y_1424_, 0);
lean_inc(v_fst_1426_);
lean_dec_ref(v___y_1424_);
v_mctx_1427_ = lean_ctor_get(v_snd_1425_, 1);
lean_inc_ref(v_mctx_1427_);
lean_dec(v_snd_1425_);
v___x_1428_ = lean_unbox(v_fst_1426_);
lean_dec(v_fst_1426_);
v_fst_1405_ = v___x_1428_;
v_mctx_1406_ = v_mctx_1427_;
goto v___jp_1404_;
}
}
}
LEAN_EXPORT void l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1397_ = stack[0].m_obj;
lean_object* v_fvarId_1398_ = stack[1].m_obj;
lean_object* v___y_1399_ = stack[2].m_obj;
lean_object* v_res_1436_;
v_res_1436_ = l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2___redArg(v_e_1397_, v_fvarId_1398_, v___y_1399_);
stack->m_obj
 = v_res_1436_;
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2___redArg___boxed(lean_object* v_e_1437_, lean_object* v_fvarId_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_){
_start:
{
lean_object* v_res_1441_; 
v_res_1441_ = l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2___redArg(v_e_1437_, v_fvarId_1438_, v___y_1439_);
lean_dec(v___y_1439_);
return v_res_1441_;
}
}
lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2(lean_object* v_e_1442_, lean_object* v_fvarId_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_){
_start:
{
lean_object* v___x_1449_; 
v___x_1449_ = l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2___redArg(v_e_1442_, v_fvarId_1443_, v___y_1445_);
return v___x_1449_;
}
}
LEAN_EXPORT void l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1442_ = stack[0].m_obj;
lean_object* v_fvarId_1443_ = stack[1].m_obj;
lean_object* v___y_1444_ = stack[2].m_obj;
lean_object* v___y_1445_ = stack[3].m_obj;
lean_object* v___y_1446_ = stack[4].m_obj;
lean_object* v___y_1447_ = stack[5].m_obj;
lean_object* v_res_1450_;
v_res_1450_ = l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2(v_e_1442_, v_fvarId_1443_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_);
stack->m_obj
 = v_res_1450_;
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2___boxed(lean_object* v_e_1451_, lean_object* v_fvarId_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_){
_start:
{
lean_object* v_res_1458_; 
v_res_1458_ = l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2(v_e_1451_, v_fvarId_1452_, v___y_1453_, v___y_1454_, v___y_1455_, v___y_1456_);
lean_dec(v___y_1456_);
lean_dec_ref(v___y_1455_);
lean_dec(v___y_1454_);
lean_dec_ref(v___y_1453_);
return v_res_1458_;
}
}
uint8_t l_List_elem___at___00Lean_Meta_getMajorTypeIndices_spec__0(lean_object* v_a_1459_, lean_object* v_x_1460_){
_start:
{
if (lean_obj_tag(v_x_1460_) == 0)
{
uint8_t v___x_1461_; 
v___x_1461_ = 0;
return v___x_1461_;
}
else
{
lean_object* v_head_1462_; lean_object* v_tail_1463_; uint8_t v___x_1464_; 
v_head_1462_ = lean_ctor_get(v_x_1460_, 0);
v_tail_1463_ = lean_ctor_get(v_x_1460_, 1);
v___x_1464_ = lean_nat_dec_eq(v_a_1459_, v_head_1462_);
if (v___x_1464_ == 0)
{
v_x_1460_ = v_tail_1463_;
goto _start;
}
else
{
return v___x_1464_;
}
}
}
}
LEAN_EXPORT void l_List_elem___at___00Lean_Meta_getMajorTypeIndices_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1459_ = stack[0].m_obj;
lean_object* v_x_1460_ = stack[1].m_obj;
uint8_t v_res_1466_;
v_res_1466_ = l_List_elem___at___00Lean_Meta_getMajorTypeIndices_spec__0(v_a_1459_, v_x_1460_);
stack->m_num = v_res_1466_;
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_Meta_getMajorTypeIndices_spec__0___boxed(lean_object* v_a_1467_, lean_object* v_x_1468_){
_start:
{
uint8_t v_res_1469_; lean_object* v_r_1470_; 
v_res_1469_ = l_List_elem___at___00Lean_Meta_getMajorTypeIndices_spec__0(v_a_1467_, v_x_1468_);
lean_dec(v_x_1468_);
lean_dec(v_a_1467_);
v_r_1470_ = lean_box(v_res_1469_);
return v_r_1470_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_1472_; lean_object* v___x_1473_; 
v___x_1472_ = ((lean_object*)(l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__0));
v___x_1473_ = l_Lean_stringToMessageData(v___x_1472_);
return v___x_1473_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_1475_; lean_object* v___x_1476_; 
v___x_1475_ = ((lean_object*)(l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__2));
v___x_1476_ = l_Lean_stringToMessageData(v___x_1475_);
return v___x_1476_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__5(void){
_start:
{
lean_object* v___x_1478_; lean_object* v___x_1479_; 
v___x_1478_ = ((lean_object*)(l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__4));
v___x_1479_ = l_Lean_stringToMessageData(v___x_1478_);
return v___x_1479_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__7(void){
_start:
{
lean_object* v___x_1481_; lean_object* v___x_1482_; 
v___x_1481_ = ((lean_object*)(l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__6));
v___x_1482_ = l_Lean_stringToMessageData(v___x_1481_);
return v___x_1482_;
}
}
lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg(lean_object* v_majorTypeArgs_1483_, lean_object* v_idxPos_1484_, lean_object* v_recursorInfo_1485_, lean_object* v_idx_1486_, lean_object* v_tacticName_1487_, lean_object* v_mvarId_1488_, lean_object* v_majorType_1489_, lean_object* v_n_1490_, lean_object* v_i_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_){
_start:
{
lean_object* v_zero_1497_; uint8_t v_isZero_1498_; 
v_zero_1497_ = lean_unsigned_to_nat(0u);
v_isZero_1498_ = lean_nat_dec_eq(v_i_1491_, v_zero_1497_);
if (v_isZero_1498_ == 1)
{
lean_object* v___x_1499_; lean_object* v___x_1500_; 
lean_dec(v_i_1491_);
lean_dec_ref(v_majorType_1489_);
lean_dec(v_mvarId_1488_);
lean_dec(v_tacticName_1487_);
lean_dec_ref(v_idx_1486_);
v___x_1499_ = lean_box(0);
v___x_1500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1500_, 0, v___x_1499_);
return v___x_1500_;
}
else
{
lean_object* v_one_1501_; lean_object* v_n_1502_; lean_object* v___y_1504_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v_arg_1508_; lean_object* v___y_1510_; lean_object* v___y_1511_; lean_object* v___y_1512_; lean_object* v___y_1513_; lean_object* v___y_1556_; lean_object* v___y_1557_; lean_object* v___y_1558_; lean_object* v___y_1559_; uint8_t v___x_1580_; 
v_one_1501_ = lean_unsigned_to_nat(1u);
v_n_1502_ = lean_nat_sub(v_i_1491_, v_one_1501_);
lean_dec(v_i_1491_);
v___x_1506_ = lean_nat_sub(v_n_1490_, v_n_1502_);
v___x_1507_ = lean_nat_sub(v___x_1506_, v_one_1501_);
lean_dec(v___x_1506_);
v_arg_1508_ = lean_array_fget_borrowed(v_majorTypeArgs_1483_, v___x_1507_);
v___x_1580_ = lean_nat_dec_eq(v___x_1507_, v_idxPos_1484_);
if (v___x_1580_ == 0)
{
uint8_t v___x_1581_; 
v___x_1581_ = lean_expr_eqv(v_arg_1508_, v_idx_1486_);
if (v___x_1581_ == 0)
{
v___y_1556_ = v___y_1492_;
v___y_1557_ = v___y_1493_;
v___y_1558_ = v___y_1494_;
v___y_1559_ = v___y_1495_;
goto v___jp_1555_;
}
else
{
lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; 
v___x_1582_ = lean_obj_once(&l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1, &l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1_once, _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1);
lean_inc_ref(v_idx_1486_);
v___x_1583_ = l_Lean_MessageData_ofExpr(v_idx_1486_);
v___x_1584_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1584_, 0, v___x_1582_);
lean_ctor_set(v___x_1584_, 1, v___x_1583_);
v___x_1585_ = lean_obj_once(&l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__7, &l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__7_once, _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__7);
v___x_1586_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1586_, 0, v___x_1584_);
lean_ctor_set(v___x_1586_, 1, v___x_1585_);
lean_inc_ref(v_majorType_1489_);
v___x_1587_ = l_Lean_indentExpr(v_majorType_1489_);
v___x_1588_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1588_, 0, v___x_1586_);
lean_ctor_set(v___x_1588_, 1, v___x_1587_);
v___x_1589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1589_, 0, v___x_1588_);
lean_inc(v_mvarId_1488_);
lean_inc(v_tacticName_1487_);
v___x_1590_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1487_, v_mvarId_1488_, v___x_1589_, v___y_1492_, v___y_1493_, v___y_1494_, v___y_1495_);
if (lean_obj_tag(v___x_1590_) == 0)
{
lean_dec_ref_known(v___x_1590_, 1);
v___y_1556_ = v___y_1492_;
v___y_1557_ = v___y_1493_;
v___y_1558_ = v___y_1494_;
v___y_1559_ = v___y_1495_;
goto v___jp_1555_;
}
else
{
lean_dec(v___x_1507_);
v___y_1504_ = v___x_1590_;
goto v___jp_1503_;
}
}
}
else
{
v___y_1556_ = v___y_1492_;
v___y_1557_ = v___y_1493_;
v___y_1558_ = v___y_1494_;
v___y_1559_ = v___y_1495_;
goto v___jp_1555_;
}
v___jp_1503_:
{
if (lean_obj_tag(v___y_1504_) == 0)
{
lean_dec_ref_known(v___y_1504_, 1);
v_i_1491_ = v_n_1502_;
goto _start;
}
else
{
lean_dec(v_n_1502_);
lean_dec_ref(v_majorType_1489_);
lean_dec(v_mvarId_1488_);
lean_dec(v_tacticName_1487_);
lean_dec_ref(v_idx_1486_);
return v___y_1504_;
}
}
v___jp_1509_:
{
uint8_t v___x_1514_; 
v___x_1514_ = lean_nat_dec_lt(v_idxPos_1484_, v___x_1507_);
if (v___x_1514_ == 0)
{
lean_dec(v___x_1507_);
v_i_1491_ = v_n_1502_;
goto _start;
}
else
{
lean_object* v_indicesPos_1516_; uint8_t v___x_1517_; 
v_indicesPos_1516_ = lean_ctor_get(v_recursorInfo_1485_, 6);
v___x_1517_ = l_List_elem___at___00Lean_Meta_getMajorTypeIndices_spec__0(v___x_1507_, v_indicesPos_1516_);
if (v___x_1517_ == 0)
{
lean_dec(v___x_1507_);
v_i_1491_ = v_n_1502_;
goto _start;
}
else
{
uint8_t v___x_1519_; 
v___x_1519_ = l_Lean_Expr_isFVar(v_arg_1508_);
if (v___x_1519_ == 0)
{
lean_dec(v___x_1507_);
v_i_1491_ = v_n_1502_;
goto _start;
}
else
{
lean_object* v___x_1521_; lean_object* v___x_1522_; 
v___x_1521_ = l_Lean_Expr_fvarId_x21(v_idx_1486_);
v___x_1522_ = l_Lean_FVarId_getDecl___redArg(v___x_1521_, v___y_1510_, v___y_1512_, v___y_1513_);
if (lean_obj_tag(v___x_1522_) == 0)
{
lean_object* v_a_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v_a_1526_; lean_object* v___x_1528_; uint8_t v_isShared_1529_; uint8_t v_isSharedCheck_1546_; 
v_a_1523_ = lean_ctor_get(v___x_1522_, 0);
lean_inc(v_a_1523_);
lean_dec_ref_known(v___x_1522_, 1);
v___x_1524_ = l_Lean_Expr_fvarId_x21(v_arg_1508_);
v___x_1525_ = l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg(v_a_1523_, v___x_1524_, v___x_1517_, v___y_1511_);
v_a_1526_ = lean_ctor_get(v___x_1525_, 0);
v_isSharedCheck_1546_ = !lean_is_exclusive(v___x_1525_);
if (v_isSharedCheck_1546_ == 0)
{
v___x_1528_ = v___x_1525_;
v_isShared_1529_ = v_isSharedCheck_1546_;
goto v_resetjp_1527_;
}
else
{
lean_inc(v_a_1526_);
lean_dec(v___x_1525_);
v___x_1528_ = lean_box(0);
v_isShared_1529_ = v_isSharedCheck_1546_;
goto v_resetjp_1527_;
}
v_resetjp_1527_:
{
uint8_t v___x_1530_; 
v___x_1530_ = lean_unbox(v_a_1526_);
lean_dec(v_a_1526_);
if (v___x_1530_ == 0)
{
lean_del_object(v___x_1528_);
lean_dec(v___x_1507_);
v_i_1491_ = v_n_1502_;
goto _start;
}
else
{
lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1540_; 
v___x_1532_ = lean_obj_once(&l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1, &l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1_once, _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1);
lean_inc_ref(v_idx_1486_);
v___x_1533_ = l_Lean_MessageData_ofExpr(v_idx_1486_);
v___x_1534_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1534_, 0, v___x_1532_);
lean_ctor_set(v___x_1534_, 1, v___x_1533_);
v___x_1535_ = lean_obj_once(&l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__3, &l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__3_once, _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__3);
v___x_1536_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1536_, 0, v___x_1534_);
lean_ctor_set(v___x_1536_, 1, v___x_1535_);
v___x_1537_ = lean_nat_add(v___x_1507_, v_one_1501_);
lean_dec(v___x_1507_);
v___x_1538_ = l_Nat_reprFast(v___x_1537_);
if (v_isShared_1529_ == 0)
{
lean_ctor_set_tag(v___x_1528_, 3);
lean_ctor_set(v___x_1528_, 0, v___x_1538_);
v___x_1540_ = v___x_1528_;
goto v_reusejp_1539_;
}
else
{
lean_object* v_reuseFailAlloc_1545_; 
v_reuseFailAlloc_1545_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1545_, 0, v___x_1538_);
v___x_1540_ = v_reuseFailAlloc_1545_;
goto v_reusejp_1539_;
}
v_reusejp_1539_:
{
lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; 
v___x_1541_ = l_Lean_MessageData_ofFormat(v___x_1540_);
v___x_1542_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1542_, 0, v___x_1536_);
lean_ctor_set(v___x_1542_, 1, v___x_1541_);
v___x_1543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1543_, 0, v___x_1542_);
lean_inc(v_mvarId_1488_);
lean_inc(v_tacticName_1487_);
v___x_1544_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1487_, v_mvarId_1488_, v___x_1543_, v___y_1510_, v___y_1511_, v___y_1512_, v___y_1513_);
v___y_1504_ = v___x_1544_;
goto v___jp_1503_;
}
}
}
}
else
{
lean_object* v_a_1547_; lean_object* v___x_1549_; uint8_t v_isShared_1550_; uint8_t v_isSharedCheck_1554_; 
lean_dec(v___x_1507_);
lean_dec(v_n_1502_);
lean_dec_ref(v_majorType_1489_);
lean_dec(v_mvarId_1488_);
lean_dec(v_tacticName_1487_);
lean_dec_ref(v_idx_1486_);
v_a_1547_ = lean_ctor_get(v___x_1522_, 0);
v_isSharedCheck_1554_ = !lean_is_exclusive(v___x_1522_);
if (v_isSharedCheck_1554_ == 0)
{
v___x_1549_ = v___x_1522_;
v_isShared_1550_ = v_isSharedCheck_1554_;
goto v_resetjp_1548_;
}
else
{
lean_inc(v_a_1547_);
lean_dec(v___x_1522_);
v___x_1549_ = lean_box(0);
v_isShared_1550_ = v_isSharedCheck_1554_;
goto v_resetjp_1548_;
}
v_resetjp_1548_:
{
lean_object* v___x_1552_; 
if (v_isShared_1550_ == 0)
{
v___x_1552_ = v___x_1549_;
goto v_reusejp_1551_;
}
else
{
lean_object* v_reuseFailAlloc_1553_; 
v_reuseFailAlloc_1553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1553_, 0, v_a_1547_);
v___x_1552_ = v_reuseFailAlloc_1553_;
goto v_reusejp_1551_;
}
v_reusejp_1551_:
{
return v___x_1552_;
}
}
}
}
}
}
}
v___jp_1555_:
{
uint8_t v___x_1560_; 
v___x_1560_ = lean_nat_dec_lt(v___x_1507_, v_idxPos_1484_);
if (v___x_1560_ == 0)
{
v___y_1510_ = v___y_1556_;
v___y_1511_ = v___y_1557_;
v___y_1512_ = v___y_1558_;
v___y_1513_ = v___y_1559_;
goto v___jp_1509_;
}
else
{
lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v_a_1563_; lean_object* v___x_1565_; uint8_t v_isShared_1566_; uint8_t v_isSharedCheck_1579_; 
v___x_1561_ = l_Lean_Expr_fvarId_x21(v_idx_1486_);
lean_inc(v_arg_1508_);
v___x_1562_ = l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2___redArg(v_arg_1508_, v___x_1561_, v___y_1557_);
v_a_1563_ = lean_ctor_get(v___x_1562_, 0);
v_isSharedCheck_1579_ = !lean_is_exclusive(v___x_1562_);
if (v_isSharedCheck_1579_ == 0)
{
v___x_1565_ = v___x_1562_;
v_isShared_1566_ = v_isSharedCheck_1579_;
goto v_resetjp_1564_;
}
else
{
lean_inc(v_a_1563_);
lean_dec(v___x_1562_);
v___x_1565_ = lean_box(0);
v_isShared_1566_ = v_isSharedCheck_1579_;
goto v_resetjp_1564_;
}
v_resetjp_1564_:
{
uint8_t v___x_1567_; 
v___x_1567_ = lean_unbox(v_a_1563_);
lean_dec(v_a_1563_);
if (v___x_1567_ == 0)
{
lean_del_object(v___x_1565_);
v___y_1510_ = v___y_1556_;
v___y_1511_ = v___y_1557_;
v___y_1512_ = v___y_1558_;
v___y_1513_ = v___y_1559_;
goto v___jp_1509_;
}
else
{
lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1576_; 
v___x_1568_ = lean_obj_once(&l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1, &l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1_once, _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1);
lean_inc_ref(v_idx_1486_);
v___x_1569_ = l_Lean_MessageData_ofExpr(v_idx_1486_);
v___x_1570_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1570_, 0, v___x_1568_);
lean_ctor_set(v___x_1570_, 1, v___x_1569_);
v___x_1571_ = lean_obj_once(&l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__5, &l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__5_once, _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__5);
v___x_1572_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1572_, 0, v___x_1570_);
lean_ctor_set(v___x_1572_, 1, v___x_1571_);
lean_inc_ref(v_majorType_1489_);
v___x_1573_ = l_Lean_indentExpr(v_majorType_1489_);
v___x_1574_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1574_, 0, v___x_1572_);
lean_ctor_set(v___x_1574_, 1, v___x_1573_);
if (v_isShared_1566_ == 0)
{
lean_ctor_set_tag(v___x_1565_, 1);
lean_ctor_set(v___x_1565_, 0, v___x_1574_);
v___x_1576_ = v___x_1565_;
goto v_reusejp_1575_;
}
else
{
lean_object* v_reuseFailAlloc_1578_; 
v_reuseFailAlloc_1578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1578_, 0, v___x_1574_);
v___x_1576_ = v_reuseFailAlloc_1578_;
goto v_reusejp_1575_;
}
v_reusejp_1575_:
{
lean_object* v___x_1577_; 
lean_inc(v_mvarId_1488_);
lean_inc(v_tacticName_1487_);
v___x_1577_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1487_, v_mvarId_1488_, v___x_1576_, v___y_1556_, v___y_1557_, v___y_1558_, v___y_1559_);
if (lean_obj_tag(v___x_1577_) == 0)
{
lean_dec_ref_known(v___x_1577_, 1);
v___y_1510_ = v___y_1556_;
v___y_1511_ = v___y_1557_;
v___y_1512_ = v___y_1558_;
v___y_1513_ = v___y_1559_;
goto v___jp_1509_;
}
else
{
lean_dec(v___x_1507_);
v___y_1504_ = v___x_1577_;
goto v___jp_1503_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_majorTypeArgs_1483_ = stack[0].m_obj;
lean_object* v_idxPos_1484_ = stack[1].m_obj;
lean_object* v_recursorInfo_1485_ = stack[2].m_obj;
lean_object* v_idx_1486_ = stack[3].m_obj;
lean_object* v_tacticName_1487_ = stack[4].m_obj;
lean_object* v_mvarId_1488_ = stack[5].m_obj;
lean_object* v_majorType_1489_ = stack[6].m_obj;
lean_object* v_n_1490_ = stack[7].m_obj;
lean_object* v_i_1491_ = stack[8].m_obj;
lean_object* v___y_1492_ = stack[9].m_obj;
lean_object* v___y_1493_ = stack[10].m_obj;
lean_object* v___y_1494_ = stack[11].m_obj;
lean_object* v___y_1495_ = stack[12].m_obj;
lean_object* v_res_1591_;
v_res_1591_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg(v_majorTypeArgs_1483_, v_idxPos_1484_, v_recursorInfo_1485_, v_idx_1486_, v_tacticName_1487_, v_mvarId_1488_, v_majorType_1489_, v_n_1490_, v_i_1491_, v___y_1492_, v___y_1493_, v___y_1494_, v___y_1495_);
stack->m_obj
 = v_res_1591_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___boxed(lean_object* v_majorTypeArgs_1592_, lean_object* v_idxPos_1593_, lean_object* v_recursorInfo_1594_, lean_object* v_idx_1595_, lean_object* v_tacticName_1596_, lean_object* v_mvarId_1597_, lean_object* v_majorType_1598_, lean_object* v_n_1599_, lean_object* v_i_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_){
_start:
{
lean_object* v_res_1606_; 
v_res_1606_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg(v_majorTypeArgs_1592_, v_idxPos_1593_, v_recursorInfo_1594_, v_idx_1595_, v_tacticName_1596_, v_mvarId_1597_, v_majorType_1598_, v_n_1599_, v_i_1600_, v___y_1601_, v___y_1602_, v___y_1603_, v___y_1604_);
lean_dec(v___y_1604_);
lean_dec_ref(v___y_1603_);
lean_dec(v___y_1602_);
lean_dec_ref(v___y_1601_);
lean_dec(v_n_1599_);
lean_dec_ref(v_recursorInfo_1594_);
lean_dec(v_idxPos_1593_);
lean_dec_ref(v_majorTypeArgs_1592_);
return v_res_1606_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__1(void){
_start:
{
lean_object* v___x_1608_; lean_object* v___x_1609_; 
v___x_1608_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__0));
v___x_1609_ = l_Lean_stringToMessageData(v___x_1608_);
return v___x_1609_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__3(void){
_start:
{
lean_object* v___x_1611_; lean_object* v___x_1612_; 
v___x_1611_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__2));
v___x_1612_ = l_Lean_stringToMessageData(v___x_1611_);
return v___x_1612_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__5(void){
_start:
{
lean_object* v___x_1614_; lean_object* v___x_1615_; 
v___x_1614_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__4));
v___x_1615_ = l_Lean_stringToMessageData(v___x_1614_);
return v___x_1615_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4(lean_object* v_majorTypeArgs_1616_, lean_object* v_recursorInfo_1617_, lean_object* v_tacticName_1618_, lean_object* v_mvarId_1619_, lean_object* v_majorType_1620_, size_t v_sz_1621_, size_t v_i_1622_, lean_object* v_bs_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_){
_start:
{
uint8_t v___x_1629_; 
v___x_1629_ = lean_usize_dec_lt(v_i_1622_, v_sz_1621_);
if (v___x_1629_ == 0)
{
lean_object* v___x_1630_; 
lean_dec_ref(v_majorType_1620_);
lean_dec(v_mvarId_1619_);
lean_dec(v_tacticName_1618_);
v___x_1630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1630_, 0, v_bs_1623_);
return v___x_1630_;
}
else
{
lean_object* v_v_1631_; lean_object* v___x_1632_; lean_object* v_bs_x27_1633_; lean_object* v_a_1635_; lean_object* v___x_1640_; uint8_t v___x_1641_; 
v_v_1631_ = lean_array_uget(v_bs_1623_, v_i_1622_);
v___x_1632_ = lean_unsigned_to_nat(0u);
v_bs_x27_1633_ = lean_array_uset(v_bs_1623_, v_i_1622_, v___x_1632_);
v___x_1640_ = lean_array_get_size(v_majorTypeArgs_1616_);
v___x_1641_ = lean_nat_dec_le(v___x_1640_, v_v_1631_);
if (v___x_1641_ == 0)
{
lean_object* v_idx_1642_; lean_object* v___y_1644_; lean_object* v___y_1645_; lean_object* v___y_1646_; lean_object* v___y_1647_; uint8_t v___x_1657_; 
v_idx_1642_ = lean_array_fget_borrowed(v_majorTypeArgs_1616_, v_v_1631_);
v___x_1657_ = l_Lean_Expr_isFVar(v_idx_1642_);
if (v___x_1657_ == 0)
{
lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; 
v___x_1658_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__1);
lean_inc(v_idx_1642_);
v___x_1659_ = l_Lean_MessageData_ofExpr(v_idx_1642_);
v___x_1660_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1660_, 0, v___x_1658_);
lean_ctor_set(v___x_1660_, 1, v___x_1659_);
v___x_1661_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__3);
v___x_1662_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1662_, 0, v___x_1660_);
lean_ctor_set(v___x_1662_, 1, v___x_1661_);
lean_inc_ref(v_majorType_1620_);
v___x_1663_ = l_Lean_indentExpr(v_majorType_1620_);
v___x_1664_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1664_, 0, v___x_1662_);
lean_ctor_set(v___x_1664_, 1, v___x_1663_);
v___x_1665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1665_, 0, v___x_1664_);
lean_inc(v_mvarId_1619_);
lean_inc(v_tacticName_1618_);
v___x_1666_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1618_, v_mvarId_1619_, v___x_1665_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_);
if (lean_obj_tag(v___x_1666_) == 0)
{
lean_dec_ref_known(v___x_1666_, 1);
v___y_1644_ = v___y_1624_;
v___y_1645_ = v___y_1625_;
v___y_1646_ = v___y_1626_;
v___y_1647_ = v___y_1627_;
goto v___jp_1643_;
}
else
{
lean_object* v_a_1667_; lean_object* v___x_1669_; uint8_t v_isShared_1670_; uint8_t v_isSharedCheck_1674_; 
lean_dec_ref(v_bs_x27_1633_);
lean_dec(v_v_1631_);
lean_dec_ref(v_majorType_1620_);
lean_dec(v_mvarId_1619_);
lean_dec(v_tacticName_1618_);
v_a_1667_ = lean_ctor_get(v___x_1666_, 0);
v_isSharedCheck_1674_ = !lean_is_exclusive(v___x_1666_);
if (v_isSharedCheck_1674_ == 0)
{
v___x_1669_ = v___x_1666_;
v_isShared_1670_ = v_isSharedCheck_1674_;
goto v_resetjp_1668_;
}
else
{
lean_inc(v_a_1667_);
lean_dec(v___x_1666_);
v___x_1669_ = lean_box(0);
v_isShared_1670_ = v_isSharedCheck_1674_;
goto v_resetjp_1668_;
}
v_resetjp_1668_:
{
lean_object* v___x_1672_; 
if (v_isShared_1670_ == 0)
{
v___x_1672_ = v___x_1669_;
goto v_reusejp_1671_;
}
else
{
lean_object* v_reuseFailAlloc_1673_; 
v_reuseFailAlloc_1673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1673_, 0, v_a_1667_);
v___x_1672_ = v_reuseFailAlloc_1673_;
goto v_reusejp_1671_;
}
v_reusejp_1671_:
{
return v___x_1672_;
}
}
}
}
else
{
v___y_1644_ = v___y_1624_;
v___y_1645_ = v___y_1625_;
v___y_1646_ = v___y_1626_;
v___y_1647_ = v___y_1627_;
goto v___jp_1643_;
}
v___jp_1643_:
{
lean_object* v___x_1648_; 
lean_inc_ref(v_majorType_1620_);
lean_inc(v_mvarId_1619_);
lean_inc(v_tacticName_1618_);
lean_inc(v_idx_1642_);
v___x_1648_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg(v_majorTypeArgs_1616_, v_v_1631_, v_recursorInfo_1617_, v_idx_1642_, v_tacticName_1618_, v_mvarId_1619_, v_majorType_1620_, v___x_1640_, v___x_1640_, v___y_1644_, v___y_1645_, v___y_1646_, v___y_1647_);
lean_dec(v_v_1631_);
if (lean_obj_tag(v___x_1648_) == 0)
{
lean_dec_ref_known(v___x_1648_, 1);
lean_inc(v_idx_1642_);
v_a_1635_ = v_idx_1642_;
goto v___jp_1634_;
}
else
{
lean_object* v_a_1649_; lean_object* v___x_1651_; uint8_t v_isShared_1652_; uint8_t v_isSharedCheck_1656_; 
lean_dec_ref(v_bs_x27_1633_);
lean_dec_ref(v_majorType_1620_);
lean_dec(v_mvarId_1619_);
lean_dec(v_tacticName_1618_);
v_a_1649_ = lean_ctor_get(v___x_1648_, 0);
v_isSharedCheck_1656_ = !lean_is_exclusive(v___x_1648_);
if (v_isSharedCheck_1656_ == 0)
{
v___x_1651_ = v___x_1648_;
v_isShared_1652_ = v_isSharedCheck_1656_;
goto v_resetjp_1650_;
}
else
{
lean_inc(v_a_1649_);
lean_dec(v___x_1648_);
v___x_1651_ = lean_box(0);
v_isShared_1652_ = v_isSharedCheck_1656_;
goto v_resetjp_1650_;
}
v_resetjp_1650_:
{
lean_object* v___x_1654_; 
if (v_isShared_1652_ == 0)
{
v___x_1654_ = v___x_1651_;
goto v_reusejp_1653_;
}
else
{
lean_object* v_reuseFailAlloc_1655_; 
v_reuseFailAlloc_1655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1655_, 0, v_a_1649_);
v___x_1654_ = v_reuseFailAlloc_1655_;
goto v_reusejp_1653_;
}
v_reusejp_1653_:
{
return v___x_1654_;
}
}
}
}
}
else
{
lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; 
lean_dec(v_v_1631_);
v___x_1675_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__5, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__5);
lean_inc_ref(v_majorType_1620_);
v___x_1676_ = l_Lean_indentExpr(v_majorType_1620_);
v___x_1677_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1677_, 0, v___x_1675_);
lean_ctor_set(v___x_1677_, 1, v___x_1676_);
v___x_1678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1678_, 0, v___x_1677_);
lean_inc(v_mvarId_1619_);
lean_inc(v_tacticName_1618_);
v___x_1679_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1618_, v_mvarId_1619_, v___x_1678_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_);
if (lean_obj_tag(v___x_1679_) == 0)
{
lean_object* v_a_1680_; 
v_a_1680_ = lean_ctor_get(v___x_1679_, 0);
lean_inc(v_a_1680_);
lean_dec_ref_known(v___x_1679_, 1);
v_a_1635_ = v_a_1680_;
goto v___jp_1634_;
}
else
{
lean_object* v_a_1681_; lean_object* v___x_1683_; uint8_t v_isShared_1684_; uint8_t v_isSharedCheck_1688_; 
lean_dec_ref(v_bs_x27_1633_);
lean_dec_ref(v_majorType_1620_);
lean_dec(v_mvarId_1619_);
lean_dec(v_tacticName_1618_);
v_a_1681_ = lean_ctor_get(v___x_1679_, 0);
v_isSharedCheck_1688_ = !lean_is_exclusive(v___x_1679_);
if (v_isSharedCheck_1688_ == 0)
{
v___x_1683_ = v___x_1679_;
v_isShared_1684_ = v_isSharedCheck_1688_;
goto v_resetjp_1682_;
}
else
{
lean_inc(v_a_1681_);
lean_dec(v___x_1679_);
v___x_1683_ = lean_box(0);
v_isShared_1684_ = v_isSharedCheck_1688_;
goto v_resetjp_1682_;
}
v_resetjp_1682_:
{
lean_object* v___x_1686_; 
if (v_isShared_1684_ == 0)
{
v___x_1686_ = v___x_1683_;
goto v_reusejp_1685_;
}
else
{
lean_object* v_reuseFailAlloc_1687_; 
v_reuseFailAlloc_1687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1687_, 0, v_a_1681_);
v___x_1686_ = v_reuseFailAlloc_1687_;
goto v_reusejp_1685_;
}
v_reusejp_1685_:
{
return v___x_1686_;
}
}
}
}
v___jp_1634_:
{
size_t v___x_1636_; size_t v___x_1637_; lean_object* v___x_1638_; 
v___x_1636_ = ((size_t)1ULL);
v___x_1637_ = lean_usize_add(v_i_1622_, v___x_1636_);
v___x_1638_ = lean_array_uset(v_bs_x27_1633_, v_i_1622_, v_a_1635_);
v_i_1622_ = v___x_1637_;
v_bs_1623_ = v___x_1638_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_majorTypeArgs_1616_ = stack[0].m_obj;
lean_object* v_recursorInfo_1617_ = stack[1].m_obj;
lean_object* v_tacticName_1618_ = stack[2].m_obj;
lean_object* v_mvarId_1619_ = stack[3].m_obj;
lean_object* v_majorType_1620_ = stack[4].m_obj;
size_t v_sz_1621_ = stack[5].m_num;
size_t v_i_1622_ = stack[6].m_num;
lean_object* v_bs_1623_ = stack[7].m_obj;
lean_object* v___y_1624_ = stack[8].m_obj;
lean_object* v___y_1625_ = stack[9].m_obj;
lean_object* v___y_1626_ = stack[10].m_obj;
lean_object* v___y_1627_ = stack[11].m_obj;
lean_object* v_res_1689_;
v_res_1689_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4(v_majorTypeArgs_1616_, v_recursorInfo_1617_, v_tacticName_1618_, v_mvarId_1619_, v_majorType_1620_, v_sz_1621_, v_i_1622_, v_bs_1623_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_);
stack->m_obj
 = v_res_1689_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___boxed(lean_object* v_majorTypeArgs_1690_, lean_object* v_recursorInfo_1691_, lean_object* v_tacticName_1692_, lean_object* v_mvarId_1693_, lean_object* v_majorType_1694_, lean_object* v_sz_1695_, lean_object* v_i_1696_, lean_object* v_bs_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_){
_start:
{
size_t v_sz_boxed_1703_; size_t v_i_boxed_1704_; lean_object* v_res_1705_; 
v_sz_boxed_1703_ = lean_unbox_usize(v_sz_1695_);
lean_dec(v_sz_1695_);
v_i_boxed_1704_ = lean_unbox_usize(v_i_1696_);
lean_dec(v_i_1696_);
v_res_1705_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4(v_majorTypeArgs_1690_, v_recursorInfo_1691_, v_tacticName_1692_, v_mvarId_1693_, v_majorType_1694_, v_sz_boxed_1703_, v_i_boxed_1704_, v_bs_1697_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_);
lean_dec(v___y_1701_);
lean_dec_ref(v___y_1700_);
lean_dec(v___y_1699_);
lean_dec_ref(v___y_1698_);
lean_dec_ref(v_recursorInfo_1691_);
lean_dec_ref(v_majorTypeArgs_1690_);
return v_res_1705_;
}
}
static lean_object* _init_l_Lean_Meta_getMajorTypeIndices___closed__0(void){
_start:
{
lean_object* v___x_1706_; lean_object* v_dummy_1707_; 
v___x_1706_ = lean_box(0);
v_dummy_1707_ = l_Lean_Expr_sort___override(v___x_1706_);
return v_dummy_1707_;
}
}
lean_object* l_Lean_Meta_getMajorTypeIndices(lean_object* v_mvarId_1708_, lean_object* v_tacticName_1709_, lean_object* v_recursorInfo_1710_, lean_object* v_majorType_1711_, lean_object* v_a_1712_, lean_object* v_a_1713_, lean_object* v_a_1714_, lean_object* v_a_1715_){
_start:
{
lean_object* v_indicesPos_1717_; lean_object* v_nargs_1718_; lean_object* v_dummy_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v_majorTypeArgs_1723_; lean_object* v___x_1724_; size_t v_sz_1725_; size_t v___x_1726_; lean_object* v___x_1727_; 
v_indicesPos_1717_ = lean_ctor_get(v_recursorInfo_1710_, 6);
v_nargs_1718_ = l_Lean_Expr_getAppNumArgs(v_majorType_1711_);
v_dummy_1719_ = lean_obj_once(&l_Lean_Meta_getMajorTypeIndices___closed__0, &l_Lean_Meta_getMajorTypeIndices___closed__0_once, _init_l_Lean_Meta_getMajorTypeIndices___closed__0);
lean_inc(v_nargs_1718_);
v___x_1720_ = lean_mk_array(v_nargs_1718_, v_dummy_1719_);
v___x_1721_ = lean_unsigned_to_nat(1u);
v___x_1722_ = lean_nat_sub(v_nargs_1718_, v___x_1721_);
lean_dec(v_nargs_1718_);
lean_inc_ref(v_majorType_1711_);
v_majorTypeArgs_1723_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_majorType_1711_, v___x_1720_, v___x_1722_);
lean_inc(v_indicesPos_1717_);
v___x_1724_ = lean_array_mk(v_indicesPos_1717_);
v_sz_1725_ = lean_array_size(v___x_1724_);
v___x_1726_ = ((size_t)0ULL);
v___x_1727_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4(v_majorTypeArgs_1723_, v_recursorInfo_1710_, v_tacticName_1709_, v_mvarId_1708_, v_majorType_1711_, v_sz_1725_, v___x_1726_, v___x_1724_, v_a_1712_, v_a_1713_, v_a_1714_, v_a_1715_);
lean_dec_ref(v_recursorInfo_1710_);
lean_dec_ref(v_majorTypeArgs_1723_);
return v___x_1727_;
}
}
LEAN_EXPORT void l_Lean_Meta_getMajorTypeIndices_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1708_ = stack[0].m_obj;
lean_object* v_tacticName_1709_ = stack[1].m_obj;
lean_object* v_recursorInfo_1710_ = stack[2].m_obj;
lean_object* v_majorType_1711_ = stack[3].m_obj;
lean_object* v_a_1712_ = stack[4].m_obj;
lean_object* v_a_1713_ = stack[5].m_obj;
lean_object* v_a_1714_ = stack[6].m_obj;
lean_object* v_a_1715_ = stack[7].m_obj;
lean_object* v_res_1728_;
v_res_1728_ = l_Lean_Meta_getMajorTypeIndices(v_mvarId_1708_, v_tacticName_1709_, v_recursorInfo_1710_, v_majorType_1711_, v_a_1712_, v_a_1713_, v_a_1714_, v_a_1715_);
stack->m_obj
 = v_res_1728_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMajorTypeIndices___boxed(lean_object* v_mvarId_1729_, lean_object* v_tacticName_1730_, lean_object* v_recursorInfo_1731_, lean_object* v_majorType_1732_, lean_object* v_a_1733_, lean_object* v_a_1734_, lean_object* v_a_1735_, lean_object* v_a_1736_, lean_object* v_a_1737_){
_start:
{
lean_object* v_res_1738_; 
v_res_1738_ = l_Lean_Meta_getMajorTypeIndices(v_mvarId_1729_, v_tacticName_1730_, v_recursorInfo_1731_, v_majorType_1732_, v_a_1733_, v_a_1734_, v_a_1735_, v_a_1736_);
lean_dec(v_a_1736_);
lean_dec_ref(v_a_1735_);
lean_dec(v_a_1734_);
lean_dec_ref(v_a_1733_);
return v_res_1738_;
}
}
lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3(lean_object* v_majorTypeArgs_1739_, lean_object* v_idxPos_1740_, lean_object* v_recursorInfo_1741_, lean_object* v_idx_1742_, lean_object* v_tacticName_1743_, lean_object* v_mvarId_1744_, lean_object* v_majorType_1745_, lean_object* v_n_1746_, lean_object* v_i_1747_, lean_object* v_a_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_){
_start:
{
lean_object* v___x_1754_; 
v___x_1754_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg(v_majorTypeArgs_1739_, v_idxPos_1740_, v_recursorInfo_1741_, v_idx_1742_, v_tacticName_1743_, v_mvarId_1744_, v_majorType_1745_, v_n_1746_, v_i_1747_, v___y_1749_, v___y_1750_, v___y_1751_, v___y_1752_);
return v___x_1754_;
}
}
LEAN_EXPORT void l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_majorTypeArgs_1739_ = stack[0].m_obj;
lean_object* v_idxPos_1740_ = stack[1].m_obj;
lean_object* v_recursorInfo_1741_ = stack[2].m_obj;
lean_object* v_idx_1742_ = stack[3].m_obj;
lean_object* v_tacticName_1743_ = stack[4].m_obj;
lean_object* v_mvarId_1744_ = stack[5].m_obj;
lean_object* v_majorType_1745_ = stack[6].m_obj;
lean_object* v_n_1746_ = stack[7].m_obj;
lean_object* v_i_1747_ = stack[8].m_obj;
lean_object* v___y_1749_ = stack[10].m_obj;
lean_object* v___y_1750_ = stack[11].m_obj;
lean_object* v___y_1751_ = stack[12].m_obj;
lean_object* v___y_1752_ = stack[13].m_obj;
lean_object* v_res_1755_;
v_res_1755_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3(v_majorTypeArgs_1739_, v_idxPos_1740_, v_recursorInfo_1741_, v_idx_1742_, v_tacticName_1743_, v_mvarId_1744_, v_majorType_1745_, v_n_1746_, v_i_1747_, lean_box(0), v___y_1749_, v___y_1750_, v___y_1751_, v___y_1752_);
stack->m_obj
 = v_res_1755_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___boxed(lean_object* v_majorTypeArgs_1756_, lean_object* v_idxPos_1757_, lean_object* v_recursorInfo_1758_, lean_object* v_idx_1759_, lean_object* v_tacticName_1760_, lean_object* v_mvarId_1761_, lean_object* v_majorType_1762_, lean_object* v_n_1763_, lean_object* v_i_1764_, lean_object* v_a_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_){
_start:
{
lean_object* v_res_1771_; 
v_res_1771_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3(v_majorTypeArgs_1756_, v_idxPos_1757_, v_recursorInfo_1758_, v_idx_1759_, v_tacticName_1760_, v_mvarId_1761_, v_majorType_1762_, v_n_1763_, v_i_1764_, v_a_1765_, v___y_1766_, v___y_1767_, v___y_1768_, v___y_1769_);
lean_dec(v___y_1769_);
lean_dec_ref(v___y_1768_);
lean_dec(v___y_1767_);
lean_dec_ref(v___y_1766_);
lean_dec(v_n_1763_);
lean_dec_ref(v_recursorInfo_1758_);
lean_dec(v_idxPos_1757_);
lean_dec_ref(v_majorTypeArgs_1756_);
return v_res_1771_;
}
}
lean_object* l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1___redArg(lean_object* v_name_1772_, lean_object* v_msg_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_){
_start:
{
lean_object* v_ref_1779_; lean_object* v_msg_1780_; lean_object* v___x_1781_; lean_object* v_a_1782_; lean_object* v___x_1784_; uint8_t v_isShared_1785_; uint8_t v_isSharedCheck_1790_; 
v_ref_1779_ = lean_ctor_get(v___y_1776_, 2);
v_msg_1780_ = l_Lean_MessageData_tagWithErrorName(v_msg_1773_, v_name_1772_);
v___x_1781_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1_spec__2(v_msg_1780_, v___y_1774_, v___y_1775_, v___y_1776_, v___y_1777_);
v_a_1782_ = lean_ctor_get(v___x_1781_, 0);
v_isSharedCheck_1790_ = !lean_is_exclusive(v___x_1781_);
if (v_isSharedCheck_1790_ == 0)
{
v___x_1784_ = v___x_1781_;
v_isShared_1785_ = v_isSharedCheck_1790_;
goto v_resetjp_1783_;
}
else
{
lean_inc(v_a_1782_);
lean_dec(v___x_1781_);
v___x_1784_ = lean_box(0);
v_isShared_1785_ = v_isSharedCheck_1790_;
goto v_resetjp_1783_;
}
v_resetjp_1783_:
{
lean_object* v___x_1786_; lean_object* v___x_1788_; 
lean_inc(v_ref_1779_);
v___x_1786_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1786_, 0, v_ref_1779_);
lean_ctor_set(v___x_1786_, 1, v_a_1782_);
if (v_isShared_1785_ == 0)
{
lean_ctor_set_tag(v___x_1784_, 1);
lean_ctor_set(v___x_1784_, 0, v___x_1786_);
v___x_1788_ = v___x_1784_;
goto v_reusejp_1787_;
}
else
{
lean_object* v_reuseFailAlloc_1789_; 
v_reuseFailAlloc_1789_ = lean_alloc_ctor(1, 1, 0);
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
LEAN_EXPORT void l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_1772_ = stack[0].m_obj;
lean_object* v_msg_1773_ = stack[1].m_obj;
lean_object* v___y_1774_ = stack[2].m_obj;
lean_object* v___y_1775_ = stack[3].m_obj;
lean_object* v___y_1776_ = stack[4].m_obj;
lean_object* v___y_1777_ = stack[5].m_obj;
lean_object* v_res_1791_;
v_res_1791_ = l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1___redArg(v_name_1772_, v_msg_1773_, v___y_1774_, v___y_1775_, v___y_1776_, v___y_1777_);
stack->m_obj
 = v_res_1791_;
}
LEAN_EXPORT lean_object* l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1___redArg___boxed(lean_object* v_name_1792_, lean_object* v_msg_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_){
_start:
{
lean_object* v_res_1799_; 
v_res_1799_ = l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1___redArg(v_name_1792_, v_msg_1793_, v___y_1794_, v___y_1795_, v___y_1796_, v___y_1797_);
lean_dec(v___y_1797_);
lean_dec_ref(v___y_1796_);
lean_dec(v___y_1795_);
lean_dec_ref(v___y_1794_);
return v_res_1799_;
}
}
lean_object* l_List_foldlM___at___00Lean_Meta_mkRecursorAppPrefix_spec__0(lean_object* v_a_1800_, lean_object* v___x_1801_, lean_object* v_tacticName_1802_, lean_object* v_mvarId_1803_, lean_object* v_x_1804_, lean_object* v_x_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_){
_start:
{
if (lean_obj_tag(v_x_1805_) == 0)
{
lean_object* v___x_1811_; 
lean_dec(v_mvarId_1803_);
lean_dec(v_tacticName_1802_);
lean_dec(v_a_1800_);
v___x_1811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1811_, 0, v_x_1804_);
return v___x_1811_;
}
else
{
lean_object* v_head_1812_; 
v_head_1812_ = lean_ctor_get(v_x_1805_, 0);
if (lean_obj_tag(v_head_1812_) == 0)
{
lean_object* v_tail_1813_; lean_object* v_fst_1814_; lean_object* v___x_1816_; uint8_t v_isShared_1817_; uint8_t v_isSharedCheck_1825_; 
v_tail_1813_ = lean_ctor_get(v_x_1805_, 1);
v_fst_1814_ = lean_ctor_get(v_x_1804_, 0);
v_isSharedCheck_1825_ = !lean_is_exclusive(v_x_1804_);
if (v_isSharedCheck_1825_ == 0)
{
lean_object* v_unused_1826_; 
v_unused_1826_ = lean_ctor_get(v_x_1804_, 1);
lean_dec(v_unused_1826_);
v___x_1816_ = v_x_1804_;
v_isShared_1817_ = v_isSharedCheck_1825_;
goto v_resetjp_1815_;
}
else
{
lean_inc(v_fst_1814_);
lean_dec(v_x_1804_);
v___x_1816_ = lean_box(0);
v_isShared_1817_ = v_isSharedCheck_1825_;
goto v_resetjp_1815_;
}
v_resetjp_1815_:
{
lean_object* v___x_1818_; uint8_t v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1822_; 
lean_inc(v_a_1800_);
v___x_1818_ = lean_array_push(v_fst_1814_, v_a_1800_);
v___x_1819_ = 1;
v___x_1820_ = lean_box(v___x_1819_);
if (v_isShared_1817_ == 0)
{
lean_ctor_set(v___x_1816_, 1, v___x_1820_);
lean_ctor_set(v___x_1816_, 0, v___x_1818_);
v___x_1822_ = v___x_1816_;
goto v_reusejp_1821_;
}
else
{
lean_object* v_reuseFailAlloc_1824_; 
v_reuseFailAlloc_1824_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1824_, 0, v___x_1818_);
lean_ctor_set(v_reuseFailAlloc_1824_, 1, v___x_1820_);
v___x_1822_ = v_reuseFailAlloc_1824_;
goto v_reusejp_1821_;
}
v_reusejp_1821_:
{
v_x_1804_ = v___x_1822_;
v_x_1805_ = v_tail_1813_;
goto _start;
}
}
}
else
{
lean_object* v_tail_1827_; lean_object* v_fst_1828_; lean_object* v_snd_1829_; lean_object* v___x_1831_; uint8_t v_isShared_1832_; uint8_t v_isSharedCheck_1846_; 
v_tail_1827_ = lean_ctor_get(v_x_1805_, 1);
v_fst_1828_ = lean_ctor_get(v_x_1804_, 0);
v_snd_1829_ = lean_ctor_get(v_x_1804_, 1);
v_isSharedCheck_1846_ = !lean_is_exclusive(v_x_1804_);
if (v_isSharedCheck_1846_ == 0)
{
v___x_1831_ = v_x_1804_;
v_isShared_1832_ = v_isSharedCheck_1846_;
goto v_resetjp_1830_;
}
else
{
lean_inc(v_snd_1829_);
lean_inc(v_fst_1828_);
lean_dec(v_x_1804_);
v___x_1831_ = lean_box(0);
v_isShared_1832_ = v_isSharedCheck_1846_;
goto v_resetjp_1830_;
}
v_resetjp_1830_:
{
lean_object* v_idx_1833_; lean_object* v___x_1834_; uint8_t v___x_1835_; 
v_idx_1833_ = lean_ctor_get(v_head_1812_, 0);
v___x_1834_ = lean_array_get_size(v___x_1801_);
v___x_1835_ = lean_nat_dec_le(v___x_1834_, v_idx_1833_);
if (v___x_1835_ == 0)
{
lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1839_; 
v___x_1836_ = lean_array_fget_borrowed(v___x_1801_, v_idx_1833_);
lean_inc(v___x_1836_);
v___x_1837_ = lean_array_push(v_fst_1828_, v___x_1836_);
if (v_isShared_1832_ == 0)
{
lean_ctor_set(v___x_1831_, 0, v___x_1837_);
v___x_1839_ = v___x_1831_;
goto v_reusejp_1838_;
}
else
{
lean_object* v_reuseFailAlloc_1841_; 
v_reuseFailAlloc_1841_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1841_, 0, v___x_1837_);
lean_ctor_set(v_reuseFailAlloc_1841_, 1, v_snd_1829_);
v___x_1839_ = v_reuseFailAlloc_1841_;
goto v_reusejp_1838_;
}
v_reusejp_1838_:
{
v_x_1804_ = v___x_1839_;
v_x_1805_ = v_tail_1827_;
goto _start;
}
}
else
{
lean_object* v___x_1842_; lean_object* v___x_1843_; 
lean_del_object(v___x_1831_);
lean_dec(v_snd_1829_);
lean_dec(v_fst_1828_);
v___x_1842_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9);
lean_inc(v_mvarId_1803_);
lean_inc(v_tacticName_1802_);
v___x_1843_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1802_, v_mvarId_1803_, v___x_1842_, v___y_1806_, v___y_1807_, v___y_1808_, v___y_1809_);
if (lean_obj_tag(v___x_1843_) == 0)
{
lean_object* v_a_1844_; 
v_a_1844_ = lean_ctor_get(v___x_1843_, 0);
lean_inc(v_a_1844_);
lean_dec_ref_known(v___x_1843_, 1);
v_x_1804_ = v_a_1844_;
v_x_1805_ = v_tail_1827_;
goto _start;
}
else
{
lean_dec(v_mvarId_1803_);
lean_dec(v_tacticName_1802_);
lean_dec(v_a_1800_);
return v___x_1843_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_List_foldlM___at___00Lean_Meta_mkRecursorAppPrefix_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1800_ = stack[0].m_obj;
lean_object* v___x_1801_ = stack[1].m_obj;
lean_object* v_tacticName_1802_ = stack[2].m_obj;
lean_object* v_mvarId_1803_ = stack[3].m_obj;
lean_object* v_x_1804_ = stack[4].m_obj;
lean_object* v_x_1805_ = stack[5].m_obj;
lean_object* v___y_1806_ = stack[6].m_obj;
lean_object* v___y_1807_ = stack[7].m_obj;
lean_object* v___y_1808_ = stack[8].m_obj;
lean_object* v___y_1809_ = stack[9].m_obj;
lean_object* v_res_1847_;
v_res_1847_ = l_List_foldlM___at___00Lean_Meta_mkRecursorAppPrefix_spec__0(v_a_1800_, v___x_1801_, v_tacticName_1802_, v_mvarId_1803_, v_x_1804_, v_x_1805_, v___y_1806_, v___y_1807_, v___y_1808_, v___y_1809_);
stack->m_obj
 = v_res_1847_;
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Meta_mkRecursorAppPrefix_spec__0___boxed(lean_object* v_a_1848_, lean_object* v___x_1849_, lean_object* v_tacticName_1850_, lean_object* v_mvarId_1851_, lean_object* v_x_1852_, lean_object* v_x_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_){
_start:
{
lean_object* v_res_1859_; 
v_res_1859_ = l_List_foldlM___at___00Lean_Meta_mkRecursorAppPrefix_spec__0(v_a_1848_, v___x_1849_, v_tacticName_1850_, v_mvarId_1851_, v_x_1852_, v_x_1853_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_);
lean_dec(v___y_1857_);
lean_dec_ref(v___y_1856_);
lean_dec(v___y_1855_);
lean_dec_ref(v___y_1854_);
lean_dec(v_x_1853_);
lean_dec_ref(v___x_1849_);
return v_res_1859_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__8(void){
_start:
{
lean_object* v___x_1875_; lean_object* v___x_1876_; 
v___x_1875_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__7));
v___x_1876_ = l_Lean_stringToMessageData(v___x_1875_);
return v___x_1876_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__10(void){
_start:
{
lean_object* v___x_1878_; lean_object* v___x_1879_; 
v___x_1878_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__9));
v___x_1879_ = l_Lean_stringToMessageData(v___x_1878_);
return v___x_1879_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__13(void){
_start:
{
lean_object* v___x_1883_; lean_object* v___x_1884_; 
v___x_1883_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__12));
v___x_1884_ = l_Lean_MessageData_ofFormat(v___x_1883_);
return v___x_1884_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__14(void){
_start:
{
lean_object* v___x_1885_; lean_object* v___x_1886_; 
v___x_1885_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__13, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__13_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__13);
v___x_1886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1886_, 0, v___x_1885_);
return v___x_1886_;
}
}
lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2(lean_object* v_recursorInfo_1887_, lean_object* v_a_1888_, lean_object* v_tacticName_1889_, lean_object* v_mvarId_1890_, lean_object* v_indices_1891_, lean_object* v_a_1892_, lean_object* v_major_1893_, lean_object* v_x_1894_, lean_object* v_x_1895_, lean_object* v_x_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_){
_start:
{
if (lean_obj_tag(v_x_1894_) == 5)
{
lean_object* v_fn_1902_; lean_object* v_arg_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; 
v_fn_1902_ = lean_ctor_get(v_x_1894_, 0);
lean_inc_ref(v_fn_1902_);
v_arg_1903_ = lean_ctor_get(v_x_1894_, 1);
lean_inc_ref(v_arg_1903_);
lean_dec_ref_known(v_x_1894_, 2);
v___x_1904_ = lean_array_set(v_x_1895_, v_x_1896_, v_arg_1903_);
v___x_1905_ = lean_unsigned_to_nat(1u);
v___x_1906_ = lean_nat_sub(v_x_1896_, v___x_1905_);
lean_dec(v_x_1896_);
v_x_1894_ = v_fn_1902_;
v_x_1895_ = v___x_1904_;
v_x_1896_ = v___x_1906_;
goto _start;
}
else
{
lean_dec(v_x_1896_);
if (lean_obj_tag(v_x_1894_) == 4)
{
lean_object* v_us_1908_; lean_object* v_recursorName_1909_; lean_object* v_univLevelPos_1910_; uint8_t v_depElim_1911_; lean_object* v_paramsPos_1912_; lean_object* v___x_1913_; uint8_t v___x_1914_; lean_object* v___y_1916_; lean_object* v_motive_1917_; lean_object* v___y_1918_; lean_object* v___y_1919_; lean_object* v___y_1920_; lean_object* v___y_1921_; lean_object* v___x_1934_; lean_object* v___x_1935_; 
v_us_1908_ = lean_ctor_get(v_x_1894_, 1);
lean_inc(v_us_1908_);
lean_dec_ref_known(v_x_1894_, 2);
v_recursorName_1909_ = lean_ctor_get(v_recursorInfo_1887_, 0);
lean_inc(v_recursorName_1909_);
v_univLevelPos_1910_ = lean_ctor_get(v_recursorInfo_1887_, 2);
lean_inc(v_univLevelPos_1910_);
v_depElim_1911_ = lean_ctor_get_uint8(v_recursorInfo_1887_, sizeof(void*)*8);
v_paramsPos_1912_ = lean_ctor_get(v_recursorInfo_1887_, 5);
lean_inc(v_paramsPos_1912_);
lean_dec_ref(v_recursorInfo_1887_);
v___x_1913_ = lean_array_mk(v_us_1908_);
v___x_1914_ = 0;
v___x_1934_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__1));
lean_inc(v_mvarId_1890_);
lean_inc(v_tacticName_1889_);
lean_inc(v_a_1888_);
v___x_1935_ = l_List_foldlM___at___00Lean_Meta_mkRecursorAppPrefix_spec__0(v_a_1888_, v___x_1913_, v_tacticName_1889_, v_mvarId_1890_, v___x_1934_, v_univLevelPos_1910_, v___y_1897_, v___y_1898_, v___y_1899_, v___y_1900_);
lean_dec(v_univLevelPos_1910_);
lean_dec_ref(v___x_1913_);
if (lean_obj_tag(v___x_1935_) == 0)
{
lean_object* v_a_1936_; lean_object* v_fst_1937_; lean_object* v_snd_1938_; lean_object* v___x_1940_; uint8_t v_isShared_1941_; uint8_t v_isSharedCheck_1982_; 
v_a_1936_ = lean_ctor_get(v___x_1935_, 0);
lean_inc(v_a_1936_);
lean_dec_ref_known(v___x_1935_, 1);
v_fst_1937_ = lean_ctor_get(v_a_1936_, 0);
v_snd_1938_ = lean_ctor_get(v_a_1936_, 1);
v_isSharedCheck_1982_ = !lean_is_exclusive(v_a_1936_);
if (v_isSharedCheck_1982_ == 0)
{
v___x_1940_ = v_a_1936_;
v_isShared_1941_ = v_isSharedCheck_1982_;
goto v_resetjp_1939_;
}
else
{
lean_inc(v_snd_1938_);
lean_inc(v_fst_1937_);
lean_dec(v_a_1936_);
v___x_1940_ = lean_box(0);
v_isShared_1941_ = v_isSharedCheck_1982_;
goto v_resetjp_1939_;
}
v_resetjp_1939_:
{
lean_object* v___y_1943_; lean_object* v___y_1944_; lean_object* v___y_1945_; lean_object* v___y_1946_; uint8_t v___x_1962_; 
v___x_1962_ = lean_unbox(v_snd_1938_);
lean_dec(v_snd_1938_);
if (v___x_1962_ == 0)
{
uint8_t v___x_1963_; 
v___x_1963_ = l_Lean_Level_isZero(v_a_1888_);
lean_dec(v_a_1888_);
if (v___x_1963_ == 0)
{
lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1968_; 
lean_dec(v_fst_1937_);
lean_dec(v_paramsPos_1912_);
lean_dec_ref(v_x_1895_);
lean_dec_ref(v_major_1893_);
lean_dec_ref(v_a_1892_);
v___x_1964_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__6));
v___x_1965_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__8, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__8_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__8);
v___x_1966_ = l_Lean_MessageData_ofName(v_recursorName_1909_);
if (v_isShared_1941_ == 0)
{
lean_ctor_set_tag(v___x_1940_, 7);
lean_ctor_set(v___x_1940_, 1, v___x_1966_);
lean_ctor_set(v___x_1940_, 0, v___x_1965_);
v___x_1968_ = v___x_1940_;
goto v_reusejp_1967_;
}
else
{
lean_object* v_reuseFailAlloc_1981_; 
v_reuseFailAlloc_1981_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1981_, 0, v___x_1965_);
lean_ctor_set(v_reuseFailAlloc_1981_, 1, v___x_1966_);
v___x_1968_ = v_reuseFailAlloc_1981_;
goto v_reusejp_1967_;
}
v_reusejp_1967_:
{
lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v_a_1973_; lean_object* v___x_1975_; uint8_t v_isShared_1976_; uint8_t v_isSharedCheck_1980_; 
v___x_1969_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__10, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__10_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__10);
v___x_1970_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1970_, 0, v___x_1968_);
lean_ctor_set(v___x_1970_, 1, v___x_1969_);
v___x_1971_ = l_Lean_Meta_mkTacticExMsg(v_tacticName_1889_, v_mvarId_1890_, v___x_1970_);
v___x_1972_ = l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1___redArg(v___x_1964_, v___x_1971_, v___y_1897_, v___y_1898_, v___y_1899_, v___y_1900_);
v_a_1973_ = lean_ctor_get(v___x_1972_, 0);
v_isSharedCheck_1980_ = !lean_is_exclusive(v___x_1972_);
if (v_isSharedCheck_1980_ == 0)
{
v___x_1975_ = v___x_1972_;
v_isShared_1976_ = v_isSharedCheck_1980_;
goto v_resetjp_1974_;
}
else
{
lean_inc(v_a_1973_);
lean_dec(v___x_1972_);
v___x_1975_ = lean_box(0);
v_isShared_1976_ = v_isSharedCheck_1980_;
goto v_resetjp_1974_;
}
v_resetjp_1974_:
{
lean_object* v___x_1978_; 
if (v_isShared_1976_ == 0)
{
v___x_1978_ = v___x_1975_;
goto v_reusejp_1977_;
}
else
{
lean_object* v_reuseFailAlloc_1979_; 
v_reuseFailAlloc_1979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1979_, 0, v_a_1973_);
v___x_1978_ = v_reuseFailAlloc_1979_;
goto v_reusejp_1977_;
}
v_reusejp_1977_:
{
return v___x_1978_;
}
}
}
}
else
{
lean_del_object(v___x_1940_);
lean_dec(v_tacticName_1889_);
v___y_1943_ = v___y_1897_;
v___y_1944_ = v___y_1898_;
v___y_1945_ = v___y_1899_;
v___y_1946_ = v___y_1900_;
goto v___jp_1942_;
}
}
else
{
lean_del_object(v___x_1940_);
lean_dec(v_tacticName_1889_);
lean_dec(v_a_1888_);
v___y_1943_ = v___y_1897_;
v___y_1944_ = v___y_1898_;
v___y_1945_ = v___y_1899_;
v___y_1946_ = v___y_1900_;
goto v___jp_1942_;
}
v___jp_1942_:
{
lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; 
v___x_1947_ = lean_array_to_list(v_fst_1937_);
v___x_1948_ = l_Lean_mkConst(v_recursorName_1909_, v___x_1947_);
v___x_1949_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams(v_mvarId_1890_, v_x_1895_, v_paramsPos_1912_, v___x_1948_, v___y_1943_, v___y_1944_, v___y_1945_, v___y_1946_);
lean_dec_ref(v_x_1895_);
if (lean_obj_tag(v___x_1949_) == 0)
{
if (v_depElim_1911_ == 0)
{
lean_object* v_a_1950_; 
lean_dec_ref(v_major_1893_);
v_a_1950_ = lean_ctor_get(v___x_1949_, 0);
lean_inc(v_a_1950_);
lean_dec_ref_known(v___x_1949_, 1);
v___y_1916_ = v_a_1950_;
v_motive_1917_ = v_a_1892_;
v___y_1918_ = v___y_1943_;
v___y_1919_ = v___y_1944_;
v___y_1920_ = v___y_1945_;
v___y_1921_ = v___y_1946_;
goto v___jp_1915_;
}
else
{
lean_object* v_a_1951_; lean_object* v___x_1952_; 
v_a_1951_ = lean_ctor_get(v___x_1949_, 0);
lean_inc(v_a_1951_);
lean_dec_ref_known(v___x_1949_, 1);
lean_inc(v___y_1946_);
lean_inc_ref(v___y_1945_);
lean_inc(v___y_1944_);
lean_inc_ref(v___y_1943_);
lean_inc_ref(v_major_1893_);
v___x_1952_ = lean_infer_type(v_major_1893_, v___y_1943_, v___y_1944_, v___y_1945_, v___y_1946_);
if (lean_obj_tag(v___x_1952_) == 0)
{
lean_object* v_a_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; 
v_a_1953_ = lean_ctor_get(v___x_1952_, 0);
lean_inc(v_a_1953_);
lean_dec_ref_known(v___x_1952_, 1);
v___x_1954_ = lean_unsigned_to_nat(1u);
v___x_1955_ = lean_mk_empty_array_with_capacity(v___x_1954_);
v___x_1956_ = lean_array_push(v___x_1955_, v_major_1893_);
v___x_1957_ = l_Lean_Expr_abstractM(v_a_1892_, v___x_1956_, v___y_1943_, v___y_1944_, v___y_1945_, v___y_1946_);
lean_dec_ref(v___x_1956_);
if (lean_obj_tag(v___x_1957_) == 0)
{
lean_object* v_a_1958_; lean_object* v___x_1959_; uint8_t v___x_1960_; lean_object* v___x_1961_; 
v_a_1958_ = lean_ctor_get(v___x_1957_, 0);
lean_inc(v_a_1958_);
lean_dec_ref_known(v___x_1957_, 1);
v___x_1959_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__3));
v___x_1960_ = 0;
v___x_1961_ = l_Lean_mkLambda(v___x_1959_, v___x_1960_, v_a_1953_, v_a_1958_);
v___y_1916_ = v_a_1951_;
v_motive_1917_ = v___x_1961_;
v___y_1918_ = v___y_1943_;
v___y_1919_ = v___y_1944_;
v___y_1920_ = v___y_1945_;
v___y_1921_ = v___y_1946_;
goto v___jp_1915_;
}
else
{
lean_dec(v_a_1953_);
lean_dec(v_a_1951_);
return v___x_1957_;
}
}
else
{
lean_dec(v_a_1951_);
lean_dec_ref(v_major_1893_);
lean_dec_ref(v_a_1892_);
return v___x_1952_;
}
}
}
else
{
lean_dec_ref(v_major_1893_);
lean_dec_ref(v_a_1892_);
return v___x_1949_;
}
}
}
}
else
{
lean_object* v_a_1983_; lean_object* v___x_1985_; uint8_t v_isShared_1986_; uint8_t v_isSharedCheck_1990_; 
lean_dec(v_paramsPos_1912_);
lean_dec(v_recursorName_1909_);
lean_dec_ref(v_x_1895_);
lean_dec_ref(v_major_1893_);
lean_dec_ref(v_a_1892_);
lean_dec(v_mvarId_1890_);
lean_dec(v_tacticName_1889_);
lean_dec(v_a_1888_);
v_a_1983_ = lean_ctor_get(v___x_1935_, 0);
v_isSharedCheck_1990_ = !lean_is_exclusive(v___x_1935_);
if (v_isSharedCheck_1990_ == 0)
{
v___x_1985_ = v___x_1935_;
v_isShared_1986_ = v_isSharedCheck_1990_;
goto v_resetjp_1984_;
}
else
{
lean_inc(v_a_1983_);
lean_dec(v___x_1935_);
v___x_1985_ = lean_box(0);
v_isShared_1986_ = v_isSharedCheck_1990_;
goto v_resetjp_1984_;
}
v_resetjp_1984_:
{
lean_object* v___x_1988_; 
if (v_isShared_1986_ == 0)
{
v___x_1988_ = v___x_1985_;
goto v_reusejp_1987_;
}
else
{
lean_object* v_reuseFailAlloc_1989_; 
v_reuseFailAlloc_1989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1989_, 0, v_a_1983_);
v___x_1988_ = v_reuseFailAlloc_1989_;
goto v_reusejp_1987_;
}
v_reusejp_1987_:
{
return v___x_1988_;
}
}
}
v___jp_1915_:
{
uint8_t v___x_1922_; uint8_t v___x_1923_; lean_object* v___x_1924_; 
v___x_1922_ = 1;
v___x_1923_ = 1;
v___x_1924_ = l_Lean_Meta_mkLambdaFVars(v_indices_1891_, v_motive_1917_, v___x_1914_, v___x_1922_, v___x_1914_, v___x_1922_, v___x_1923_, v___y_1918_, v___y_1919_, v___y_1920_, v___y_1921_);
if (lean_obj_tag(v___x_1924_) == 0)
{
lean_object* v_a_1925_; lean_object* v___x_1927_; uint8_t v_isShared_1928_; uint8_t v_isSharedCheck_1933_; 
v_a_1925_ = lean_ctor_get(v___x_1924_, 0);
v_isSharedCheck_1933_ = !lean_is_exclusive(v___x_1924_);
if (v_isSharedCheck_1933_ == 0)
{
v___x_1927_ = v___x_1924_;
v_isShared_1928_ = v_isSharedCheck_1933_;
goto v_resetjp_1926_;
}
else
{
lean_inc(v_a_1925_);
lean_dec(v___x_1924_);
v___x_1927_ = lean_box(0);
v_isShared_1928_ = v_isSharedCheck_1933_;
goto v_resetjp_1926_;
}
v_resetjp_1926_:
{
lean_object* v___x_1929_; lean_object* v___x_1931_; 
v___x_1929_ = l_Lean_Expr_app___override(v___y_1916_, v_a_1925_);
if (v_isShared_1928_ == 0)
{
lean_ctor_set(v___x_1927_, 0, v___x_1929_);
v___x_1931_ = v___x_1927_;
goto v_reusejp_1930_;
}
else
{
lean_object* v_reuseFailAlloc_1932_; 
v_reuseFailAlloc_1932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1932_, 0, v___x_1929_);
v___x_1931_ = v_reuseFailAlloc_1932_;
goto v_reusejp_1930_;
}
v_reusejp_1930_:
{
return v___x_1931_;
}
}
}
else
{
lean_dec_ref(v___y_1916_);
return v___x_1924_;
}
}
}
else
{
lean_object* v___x_1991_; lean_object* v___x_1992_; 
lean_dec_ref(v_x_1895_);
lean_dec_ref(v_x_1894_);
lean_dec_ref(v_major_1893_);
lean_dec_ref(v_a_1892_);
lean_dec(v_a_1888_);
lean_dec_ref(v_recursorInfo_1887_);
v___x_1991_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__14, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__14_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__14);
v___x_1992_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1889_, v_mvarId_1890_, v___x_1991_, v___y_1897_, v___y_1898_, v___y_1899_, v___y_1900_);
return v___x_1992_;
}
}
}
}
LEAN_EXPORT void l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_recursorInfo_1887_ = stack[0].m_obj;
lean_object* v_a_1888_ = stack[1].m_obj;
lean_object* v_tacticName_1889_ = stack[2].m_obj;
lean_object* v_mvarId_1890_ = stack[3].m_obj;
lean_object* v_indices_1891_ = stack[4].m_obj;
lean_object* v_a_1892_ = stack[5].m_obj;
lean_object* v_major_1893_ = stack[6].m_obj;
lean_object* v_x_1894_ = stack[7].m_obj;
lean_object* v_x_1895_ = stack[8].m_obj;
lean_object* v_x_1896_ = stack[9].m_obj;
lean_object* v___y_1897_ = stack[10].m_obj;
lean_object* v___y_1898_ = stack[11].m_obj;
lean_object* v___y_1899_ = stack[12].m_obj;
lean_object* v___y_1900_ = stack[13].m_obj;
lean_object* v_res_1993_;
v_res_1993_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2(v_recursorInfo_1887_, v_a_1888_, v_tacticName_1889_, v_mvarId_1890_, v_indices_1891_, v_a_1892_, v_major_1893_, v_x_1894_, v_x_1895_, v_x_1896_, v___y_1897_, v___y_1898_, v___y_1899_, v___y_1900_);
stack->m_obj
 = v_res_1993_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___boxed(lean_object* v_recursorInfo_1994_, lean_object* v_a_1995_, lean_object* v_tacticName_1996_, lean_object* v_mvarId_1997_, lean_object* v_indices_1998_, lean_object* v_a_1999_, lean_object* v_major_2000_, lean_object* v_x_2001_, lean_object* v_x_2002_, lean_object* v_x_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_){
_start:
{
lean_object* v_res_2009_; 
v_res_2009_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2(v_recursorInfo_1994_, v_a_1995_, v_tacticName_1996_, v_mvarId_1997_, v_indices_1998_, v_a_1999_, v_major_2000_, v_x_2001_, v_x_2002_, v_x_2003_, v___y_2004_, v___y_2005_, v___y_2006_, v___y_2007_);
lean_dec(v___y_2007_);
lean_dec_ref(v___y_2006_);
lean_dec(v___y_2005_);
lean_dec_ref(v___y_2004_);
lean_dec_ref(v_indices_1998_);
return v_res_2009_;
}
}
lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2(lean_object* v_a_2010_, lean_object* v_tacticName_2011_, lean_object* v_mvarId_2012_, lean_object* v_recursorInfo_2013_, lean_object* v_indices_2014_, lean_object* v_a_2015_, lean_object* v_major_2016_, lean_object* v_x_2017_, lean_object* v_x_2018_, lean_object* v_x_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_){
_start:
{
if (lean_obj_tag(v_x_2017_) == 5)
{
lean_object* v_fn_2025_; lean_object* v_arg_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; 
v_fn_2025_ = lean_ctor_get(v_x_2017_, 0);
lean_inc_ref(v_fn_2025_);
v_arg_2026_ = lean_ctor_get(v_x_2017_, 1);
lean_inc_ref(v_arg_2026_);
lean_dec_ref_known(v_x_2017_, 2);
v___x_2027_ = lean_array_set(v_x_2018_, v_x_2019_, v_arg_2026_);
v___x_2028_ = lean_unsigned_to_nat(1u);
v___x_2029_ = lean_nat_sub(v_x_2019_, v___x_2028_);
v___x_2030_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2(v_recursorInfo_2013_, v_a_2010_, v_tacticName_2011_, v_mvarId_2012_, v_indices_2014_, v_a_2015_, v_major_2016_, v_fn_2025_, v___x_2027_, v___x_2029_, v___y_2020_, v___y_2021_, v___y_2022_, v___y_2023_);
return v___x_2030_;
}
else
{
if (lean_obj_tag(v_x_2017_) == 4)
{
lean_object* v_us_2031_; lean_object* v_recursorName_2032_; lean_object* v_univLevelPos_2033_; uint8_t v_depElim_2034_; lean_object* v_paramsPos_2035_; lean_object* v___x_2036_; uint8_t v___x_2037_; lean_object* v___y_2039_; lean_object* v_motive_2040_; lean_object* v___y_2041_; lean_object* v___y_2042_; lean_object* v___y_2043_; lean_object* v___y_2044_; lean_object* v___x_2057_; lean_object* v___x_2058_; 
v_us_2031_ = lean_ctor_get(v_x_2017_, 1);
lean_inc(v_us_2031_);
lean_dec_ref_known(v_x_2017_, 2);
v_recursorName_2032_ = lean_ctor_get(v_recursorInfo_2013_, 0);
lean_inc(v_recursorName_2032_);
v_univLevelPos_2033_ = lean_ctor_get(v_recursorInfo_2013_, 2);
lean_inc(v_univLevelPos_2033_);
v_depElim_2034_ = lean_ctor_get_uint8(v_recursorInfo_2013_, sizeof(void*)*8);
v_paramsPos_2035_ = lean_ctor_get(v_recursorInfo_2013_, 5);
lean_inc(v_paramsPos_2035_);
lean_dec_ref(v_recursorInfo_2013_);
v___x_2036_ = lean_array_mk(v_us_2031_);
v___x_2037_ = 0;
v___x_2057_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__1));
lean_inc(v_mvarId_2012_);
lean_inc(v_tacticName_2011_);
lean_inc(v_a_2010_);
v___x_2058_ = l_List_foldlM___at___00Lean_Meta_mkRecursorAppPrefix_spec__0(v_a_2010_, v___x_2036_, v_tacticName_2011_, v_mvarId_2012_, v___x_2057_, v_univLevelPos_2033_, v___y_2020_, v___y_2021_, v___y_2022_, v___y_2023_);
lean_dec(v_univLevelPos_2033_);
lean_dec_ref(v___x_2036_);
if (lean_obj_tag(v___x_2058_) == 0)
{
lean_object* v_a_2059_; lean_object* v_fst_2060_; lean_object* v_snd_2061_; lean_object* v___x_2063_; uint8_t v_isShared_2064_; uint8_t v_isSharedCheck_2105_; 
v_a_2059_ = lean_ctor_get(v___x_2058_, 0);
lean_inc(v_a_2059_);
lean_dec_ref_known(v___x_2058_, 1);
v_fst_2060_ = lean_ctor_get(v_a_2059_, 0);
v_snd_2061_ = lean_ctor_get(v_a_2059_, 1);
v_isSharedCheck_2105_ = !lean_is_exclusive(v_a_2059_);
if (v_isSharedCheck_2105_ == 0)
{
v___x_2063_ = v_a_2059_;
v_isShared_2064_ = v_isSharedCheck_2105_;
goto v_resetjp_2062_;
}
else
{
lean_inc(v_snd_2061_);
lean_inc(v_fst_2060_);
lean_dec(v_a_2059_);
v___x_2063_ = lean_box(0);
v_isShared_2064_ = v_isSharedCheck_2105_;
goto v_resetjp_2062_;
}
v_resetjp_2062_:
{
lean_object* v___y_2066_; lean_object* v___y_2067_; lean_object* v___y_2068_; lean_object* v___y_2069_; uint8_t v___x_2085_; 
v___x_2085_ = lean_unbox(v_snd_2061_);
lean_dec(v_snd_2061_);
if (v___x_2085_ == 0)
{
uint8_t v___x_2086_; 
v___x_2086_ = l_Lean_Level_isZero(v_a_2010_);
lean_dec(v_a_2010_);
if (v___x_2086_ == 0)
{
lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2091_; 
lean_dec(v_fst_2060_);
lean_dec(v_paramsPos_2035_);
lean_dec_ref(v_x_2018_);
lean_dec_ref(v_major_2016_);
lean_dec_ref(v_a_2015_);
v___x_2087_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__6));
v___x_2088_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__8, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__8_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__8);
v___x_2089_ = l_Lean_MessageData_ofName(v_recursorName_2032_);
if (v_isShared_2064_ == 0)
{
lean_ctor_set_tag(v___x_2063_, 7);
lean_ctor_set(v___x_2063_, 1, v___x_2089_);
lean_ctor_set(v___x_2063_, 0, v___x_2088_);
v___x_2091_ = v___x_2063_;
goto v_reusejp_2090_;
}
else
{
lean_object* v_reuseFailAlloc_2104_; 
v_reuseFailAlloc_2104_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2104_, 0, v___x_2088_);
lean_ctor_set(v_reuseFailAlloc_2104_, 1, v___x_2089_);
v___x_2091_ = v_reuseFailAlloc_2104_;
goto v_reusejp_2090_;
}
v_reusejp_2090_:
{
lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v_a_2096_; lean_object* v___x_2098_; uint8_t v_isShared_2099_; uint8_t v_isSharedCheck_2103_; 
v___x_2092_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__10, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__10_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__10);
v___x_2093_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2093_, 0, v___x_2091_);
lean_ctor_set(v___x_2093_, 1, v___x_2092_);
v___x_2094_ = l_Lean_Meta_mkTacticExMsg(v_tacticName_2011_, v_mvarId_2012_, v___x_2093_);
v___x_2095_ = l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1___redArg(v___x_2087_, v___x_2094_, v___y_2020_, v___y_2021_, v___y_2022_, v___y_2023_);
v_a_2096_ = lean_ctor_get(v___x_2095_, 0);
v_isSharedCheck_2103_ = !lean_is_exclusive(v___x_2095_);
if (v_isSharedCheck_2103_ == 0)
{
v___x_2098_ = v___x_2095_;
v_isShared_2099_ = v_isSharedCheck_2103_;
goto v_resetjp_2097_;
}
else
{
lean_inc(v_a_2096_);
lean_dec(v___x_2095_);
v___x_2098_ = lean_box(0);
v_isShared_2099_ = v_isSharedCheck_2103_;
goto v_resetjp_2097_;
}
v_resetjp_2097_:
{
lean_object* v___x_2101_; 
if (v_isShared_2099_ == 0)
{
v___x_2101_ = v___x_2098_;
goto v_reusejp_2100_;
}
else
{
lean_object* v_reuseFailAlloc_2102_; 
v_reuseFailAlloc_2102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2102_, 0, v_a_2096_);
v___x_2101_ = v_reuseFailAlloc_2102_;
goto v_reusejp_2100_;
}
v_reusejp_2100_:
{
return v___x_2101_;
}
}
}
}
else
{
lean_del_object(v___x_2063_);
lean_dec(v_tacticName_2011_);
v___y_2066_ = v___y_2020_;
v___y_2067_ = v___y_2021_;
v___y_2068_ = v___y_2022_;
v___y_2069_ = v___y_2023_;
goto v___jp_2065_;
}
}
else
{
lean_del_object(v___x_2063_);
lean_dec(v_tacticName_2011_);
lean_dec(v_a_2010_);
v___y_2066_ = v___y_2020_;
v___y_2067_ = v___y_2021_;
v___y_2068_ = v___y_2022_;
v___y_2069_ = v___y_2023_;
goto v___jp_2065_;
}
v___jp_2065_:
{
lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; 
v___x_2070_ = lean_array_to_list(v_fst_2060_);
v___x_2071_ = l_Lean_mkConst(v_recursorName_2032_, v___x_2070_);
v___x_2072_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams(v_mvarId_2012_, v_x_2018_, v_paramsPos_2035_, v___x_2071_, v___y_2066_, v___y_2067_, v___y_2068_, v___y_2069_);
lean_dec_ref(v_x_2018_);
if (lean_obj_tag(v___x_2072_) == 0)
{
if (v_depElim_2034_ == 0)
{
lean_object* v_a_2073_; 
lean_dec_ref(v_major_2016_);
v_a_2073_ = lean_ctor_get(v___x_2072_, 0);
lean_inc(v_a_2073_);
lean_dec_ref_known(v___x_2072_, 1);
v___y_2039_ = v_a_2073_;
v_motive_2040_ = v_a_2015_;
v___y_2041_ = v___y_2066_;
v___y_2042_ = v___y_2067_;
v___y_2043_ = v___y_2068_;
v___y_2044_ = v___y_2069_;
goto v___jp_2038_;
}
else
{
lean_object* v_a_2074_; lean_object* v___x_2075_; 
v_a_2074_ = lean_ctor_get(v___x_2072_, 0);
lean_inc(v_a_2074_);
lean_dec_ref_known(v___x_2072_, 1);
lean_inc(v___y_2069_);
lean_inc_ref(v___y_2068_);
lean_inc(v___y_2067_);
lean_inc_ref(v___y_2066_);
lean_inc_ref(v_major_2016_);
v___x_2075_ = lean_infer_type(v_major_2016_, v___y_2066_, v___y_2067_, v___y_2068_, v___y_2069_);
if (lean_obj_tag(v___x_2075_) == 0)
{
lean_object* v_a_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; 
v_a_2076_ = lean_ctor_get(v___x_2075_, 0);
lean_inc(v_a_2076_);
lean_dec_ref_known(v___x_2075_, 1);
v___x_2077_ = lean_unsigned_to_nat(1u);
v___x_2078_ = lean_mk_empty_array_with_capacity(v___x_2077_);
v___x_2079_ = lean_array_push(v___x_2078_, v_major_2016_);
v___x_2080_ = l_Lean_Expr_abstractM(v_a_2015_, v___x_2079_, v___y_2066_, v___y_2067_, v___y_2068_, v___y_2069_);
lean_dec_ref(v___x_2079_);
if (lean_obj_tag(v___x_2080_) == 0)
{
lean_object* v_a_2081_; lean_object* v___x_2082_; uint8_t v___x_2083_; lean_object* v___x_2084_; 
v_a_2081_ = lean_ctor_get(v___x_2080_, 0);
lean_inc(v_a_2081_);
lean_dec_ref_known(v___x_2080_, 1);
v___x_2082_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__3));
v___x_2083_ = 0;
v___x_2084_ = l_Lean_mkLambda(v___x_2082_, v___x_2083_, v_a_2076_, v_a_2081_);
v___y_2039_ = v_a_2074_;
v_motive_2040_ = v___x_2084_;
v___y_2041_ = v___y_2066_;
v___y_2042_ = v___y_2067_;
v___y_2043_ = v___y_2068_;
v___y_2044_ = v___y_2069_;
goto v___jp_2038_;
}
else
{
lean_dec(v_a_2076_);
lean_dec(v_a_2074_);
return v___x_2080_;
}
}
else
{
lean_dec(v_a_2074_);
lean_dec_ref(v_major_2016_);
lean_dec_ref(v_a_2015_);
return v___x_2075_;
}
}
}
else
{
lean_dec_ref(v_major_2016_);
lean_dec_ref(v_a_2015_);
return v___x_2072_;
}
}
}
}
else
{
lean_object* v_a_2106_; lean_object* v___x_2108_; uint8_t v_isShared_2109_; uint8_t v_isSharedCheck_2113_; 
lean_dec(v_paramsPos_2035_);
lean_dec(v_recursorName_2032_);
lean_dec_ref(v_x_2018_);
lean_dec_ref(v_major_2016_);
lean_dec_ref(v_a_2015_);
lean_dec(v_mvarId_2012_);
lean_dec(v_tacticName_2011_);
lean_dec(v_a_2010_);
v_a_2106_ = lean_ctor_get(v___x_2058_, 0);
v_isSharedCheck_2113_ = !lean_is_exclusive(v___x_2058_);
if (v_isSharedCheck_2113_ == 0)
{
v___x_2108_ = v___x_2058_;
v_isShared_2109_ = v_isSharedCheck_2113_;
goto v_resetjp_2107_;
}
else
{
lean_inc(v_a_2106_);
lean_dec(v___x_2058_);
v___x_2108_ = lean_box(0);
v_isShared_2109_ = v_isSharedCheck_2113_;
goto v_resetjp_2107_;
}
v_resetjp_2107_:
{
lean_object* v___x_2111_; 
if (v_isShared_2109_ == 0)
{
v___x_2111_ = v___x_2108_;
goto v_reusejp_2110_;
}
else
{
lean_object* v_reuseFailAlloc_2112_; 
v_reuseFailAlloc_2112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2112_, 0, v_a_2106_);
v___x_2111_ = v_reuseFailAlloc_2112_;
goto v_reusejp_2110_;
}
v_reusejp_2110_:
{
return v___x_2111_;
}
}
}
v___jp_2038_:
{
uint8_t v___x_2045_; uint8_t v___x_2046_; lean_object* v___x_2047_; 
v___x_2045_ = 1;
v___x_2046_ = 1;
v___x_2047_ = l_Lean_Meta_mkLambdaFVars(v_indices_2014_, v_motive_2040_, v___x_2037_, v___x_2045_, v___x_2037_, v___x_2045_, v___x_2046_, v___y_2041_, v___y_2042_, v___y_2043_, v___y_2044_);
if (lean_obj_tag(v___x_2047_) == 0)
{
lean_object* v_a_2048_; lean_object* v___x_2050_; uint8_t v_isShared_2051_; uint8_t v_isSharedCheck_2056_; 
v_a_2048_ = lean_ctor_get(v___x_2047_, 0);
v_isSharedCheck_2056_ = !lean_is_exclusive(v___x_2047_);
if (v_isSharedCheck_2056_ == 0)
{
v___x_2050_ = v___x_2047_;
v_isShared_2051_ = v_isSharedCheck_2056_;
goto v_resetjp_2049_;
}
else
{
lean_inc(v_a_2048_);
lean_dec(v___x_2047_);
v___x_2050_ = lean_box(0);
v_isShared_2051_ = v_isSharedCheck_2056_;
goto v_resetjp_2049_;
}
v_resetjp_2049_:
{
lean_object* v___x_2052_; lean_object* v___x_2054_; 
v___x_2052_ = l_Lean_Expr_app___override(v___y_2039_, v_a_2048_);
if (v_isShared_2051_ == 0)
{
lean_ctor_set(v___x_2050_, 0, v___x_2052_);
v___x_2054_ = v___x_2050_;
goto v_reusejp_2053_;
}
else
{
lean_object* v_reuseFailAlloc_2055_; 
v_reuseFailAlloc_2055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2055_, 0, v___x_2052_);
v___x_2054_ = v_reuseFailAlloc_2055_;
goto v_reusejp_2053_;
}
v_reusejp_2053_:
{
return v___x_2054_;
}
}
}
else
{
lean_dec_ref(v___y_2039_);
return v___x_2047_;
}
}
}
else
{
lean_object* v___x_2114_; lean_object* v___x_2115_; 
lean_dec_ref(v_x_2018_);
lean_dec_ref(v_x_2017_);
lean_dec_ref(v_major_2016_);
lean_dec_ref(v_a_2015_);
lean_dec_ref(v_recursorInfo_2013_);
lean_dec(v_a_2010_);
v___x_2114_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__14, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__14_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__14);
v___x_2115_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_2011_, v_mvarId_2012_, v___x_2114_, v___y_2020_, v___y_2021_, v___y_2022_, v___y_2023_);
return v___x_2115_;
}
}
}
}
LEAN_EXPORT void l_Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2010_ = stack[0].m_obj;
lean_object* v_tacticName_2011_ = stack[1].m_obj;
lean_object* v_mvarId_2012_ = stack[2].m_obj;
lean_object* v_recursorInfo_2013_ = stack[3].m_obj;
lean_object* v_indices_2014_ = stack[4].m_obj;
lean_object* v_a_2015_ = stack[5].m_obj;
lean_object* v_major_2016_ = stack[6].m_obj;
lean_object* v_x_2017_ = stack[7].m_obj;
lean_object* v_x_2018_ = stack[8].m_obj;
lean_object* v_x_2019_ = stack[9].m_obj;
lean_object* v___y_2020_ = stack[10].m_obj;
lean_object* v___y_2021_ = stack[11].m_obj;
lean_object* v___y_2022_ = stack[12].m_obj;
lean_object* v___y_2023_ = stack[13].m_obj;
lean_object* v_res_2116_;
v_res_2116_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2(v_a_2010_, v_tacticName_2011_, v_mvarId_2012_, v_recursorInfo_2013_, v_indices_2014_, v_a_2015_, v_major_2016_, v_x_2017_, v_x_2018_, v_x_2019_, v___y_2020_, v___y_2021_, v___y_2022_, v___y_2023_);
stack->m_obj
 = v_res_2116_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2___boxed(lean_object* v_a_2117_, lean_object* v_tacticName_2118_, lean_object* v_mvarId_2119_, lean_object* v_recursorInfo_2120_, lean_object* v_indices_2121_, lean_object* v_a_2122_, lean_object* v_major_2123_, lean_object* v_x_2124_, lean_object* v_x_2125_, lean_object* v_x_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_){
_start:
{
lean_object* v_res_2132_; 
v_res_2132_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2(v_a_2117_, v_tacticName_2118_, v_mvarId_2119_, v_recursorInfo_2120_, v_indices_2121_, v_a_2122_, v_major_2123_, v_x_2124_, v_x_2125_, v_x_2126_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_);
lean_dec(v___y_2130_);
lean_dec_ref(v___y_2129_);
lean_dec(v___y_2128_);
lean_dec_ref(v___y_2127_);
lean_dec(v_x_2126_);
lean_dec_ref(v_indices_2121_);
return v_res_2132_;
}
}
lean_object* l_Lean_Meta_mkRecursorAppPrefix(lean_object* v_mvarId_2133_, lean_object* v_tacticName_2134_, lean_object* v_majorFVarId_2135_, lean_object* v_recursorInfo_2136_, lean_object* v_indices_2137_, lean_object* v_a_2138_, lean_object* v_a_2139_, lean_object* v_a_2140_, lean_object* v_a_2141_){
_start:
{
lean_object* v_major_2143_; lean_object* v___x_2144_; 
lean_inc(v_majorFVarId_2135_);
v_major_2143_ = l_Lean_mkFVar(v_majorFVarId_2135_);
lean_inc(v_mvarId_2133_);
v___x_2144_ = l_Lean_MVarId_getType(v_mvarId_2133_, v_a_2138_, v_a_2139_, v_a_2140_, v_a_2141_);
if (lean_obj_tag(v___x_2144_) == 0)
{
lean_object* v_a_2145_; lean_object* v___x_2146_; 
v_a_2145_ = lean_ctor_get(v___x_2144_, 0);
lean_inc_n(v_a_2145_, 2);
lean_dec_ref_known(v___x_2144_, 1);
v___x_2146_ = l_Lean_Meta_getLevel(v_a_2145_, v_a_2138_, v_a_2139_, v_a_2140_, v_a_2141_);
if (lean_obj_tag(v___x_2146_) == 0)
{
lean_object* v_a_2147_; lean_object* v___x_2148_; 
v_a_2147_ = lean_ctor_get(v___x_2146_, 0);
lean_inc(v_a_2147_);
lean_dec_ref_known(v___x_2146_, 1);
v___x_2148_ = l_Lean_Meta_normalizeLevel(v_a_2147_, v_a_2138_, v_a_2139_, v_a_2140_, v_a_2141_);
if (lean_obj_tag(v___x_2148_) == 0)
{
lean_object* v_a_2149_; lean_object* v___x_2150_; 
v_a_2149_ = lean_ctor_get(v___x_2148_, 0);
lean_inc(v_a_2149_);
lean_dec_ref_known(v___x_2148_, 1);
v___x_2150_ = l_Lean_FVarId_getDecl___redArg(v_majorFVarId_2135_, v_a_2138_, v_a_2140_, v_a_2141_);
if (lean_obj_tag(v___x_2150_) == 0)
{
lean_object* v_a_2151_; lean_object* v_typeName_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; 
v_a_2151_ = lean_ctor_get(v___x_2150_, 0);
lean_inc(v_a_2151_);
lean_dec_ref_known(v___x_2150_, 1);
v_typeName_2152_ = lean_ctor_get(v_recursorInfo_2136_, 1);
v___x_2153_ = l_Lean_LocalDecl_type(v_a_2151_);
lean_dec(v_a_2151_);
lean_inc_ref(v___x_2153_);
v___x_2154_ = l_Lean_Meta_whnfUntil(v___x_2153_, v_typeName_2152_, v_a_2138_, v_a_2139_, v_a_2140_, v_a_2141_);
if (lean_obj_tag(v___x_2154_) == 0)
{
lean_object* v_a_2155_; 
v_a_2155_ = lean_ctor_get(v___x_2154_, 0);
lean_inc(v_a_2155_);
lean_dec_ref_known(v___x_2154_, 1);
if (lean_obj_tag(v_a_2155_) == 1)
{
lean_object* v_val_2156_; lean_object* v_dummy_2157_; lean_object* v_nargs_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; 
lean_dec_ref(v___x_2153_);
v_val_2156_ = lean_ctor_get(v_a_2155_, 0);
lean_inc(v_val_2156_);
lean_dec_ref_known(v_a_2155_, 1);
v_dummy_2157_ = lean_obj_once(&l_Lean_Meta_getMajorTypeIndices___closed__0, &l_Lean_Meta_getMajorTypeIndices___closed__0_once, _init_l_Lean_Meta_getMajorTypeIndices___closed__0);
v_nargs_2158_ = l_Lean_Expr_getAppNumArgs(v_val_2156_);
lean_inc(v_nargs_2158_);
v___x_2159_ = lean_mk_array(v_nargs_2158_, v_dummy_2157_);
v___x_2160_ = lean_unsigned_to_nat(1u);
v___x_2161_ = lean_nat_sub(v_nargs_2158_, v___x_2160_);
lean_dec(v_nargs_2158_);
v___x_2162_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2(v_a_2149_, v_tacticName_2134_, v_mvarId_2133_, v_recursorInfo_2136_, v_indices_2137_, v_a_2145_, v_major_2143_, v_val_2156_, v___x_2159_, v___x_2161_, v_a_2138_, v_a_2139_, v_a_2140_, v_a_2141_);
lean_dec(v___x_2161_);
return v___x_2162_;
}
else
{
lean_object* v___x_2163_; 
lean_dec(v_a_2155_);
lean_dec(v_a_2149_);
lean_dec(v_a_2145_);
lean_dec_ref(v_major_2143_);
lean_dec_ref(v_recursorInfo_2136_);
v___x_2163_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg(v_tacticName_2134_, v_mvarId_2133_, v___x_2153_, v_a_2138_, v_a_2139_, v_a_2140_, v_a_2141_);
return v___x_2163_;
}
}
else
{
lean_object* v_a_2164_; lean_object* v___x_2166_; uint8_t v_isShared_2167_; uint8_t v_isSharedCheck_2171_; 
lean_dec_ref(v___x_2153_);
lean_dec(v_a_2149_);
lean_dec(v_a_2145_);
lean_dec_ref(v_major_2143_);
lean_dec_ref(v_recursorInfo_2136_);
lean_dec(v_tacticName_2134_);
lean_dec(v_mvarId_2133_);
v_a_2164_ = lean_ctor_get(v___x_2154_, 0);
v_isSharedCheck_2171_ = !lean_is_exclusive(v___x_2154_);
if (v_isSharedCheck_2171_ == 0)
{
v___x_2166_ = v___x_2154_;
v_isShared_2167_ = v_isSharedCheck_2171_;
goto v_resetjp_2165_;
}
else
{
lean_inc(v_a_2164_);
lean_dec(v___x_2154_);
v___x_2166_ = lean_box(0);
v_isShared_2167_ = v_isSharedCheck_2171_;
goto v_resetjp_2165_;
}
v_resetjp_2165_:
{
lean_object* v___x_2169_; 
if (v_isShared_2167_ == 0)
{
v___x_2169_ = v___x_2166_;
goto v_reusejp_2168_;
}
else
{
lean_object* v_reuseFailAlloc_2170_; 
v_reuseFailAlloc_2170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2170_, 0, v_a_2164_);
v___x_2169_ = v_reuseFailAlloc_2170_;
goto v_reusejp_2168_;
}
v_reusejp_2168_:
{
return v___x_2169_;
}
}
}
}
else
{
lean_object* v_a_2172_; lean_object* v___x_2174_; uint8_t v_isShared_2175_; uint8_t v_isSharedCheck_2179_; 
lean_dec(v_a_2149_);
lean_dec(v_a_2145_);
lean_dec_ref(v_major_2143_);
lean_dec_ref(v_recursorInfo_2136_);
lean_dec(v_tacticName_2134_);
lean_dec(v_mvarId_2133_);
v_a_2172_ = lean_ctor_get(v___x_2150_, 0);
v_isSharedCheck_2179_ = !lean_is_exclusive(v___x_2150_);
if (v_isSharedCheck_2179_ == 0)
{
v___x_2174_ = v___x_2150_;
v_isShared_2175_ = v_isSharedCheck_2179_;
goto v_resetjp_2173_;
}
else
{
lean_inc(v_a_2172_);
lean_dec(v___x_2150_);
v___x_2174_ = lean_box(0);
v_isShared_2175_ = v_isSharedCheck_2179_;
goto v_resetjp_2173_;
}
v_resetjp_2173_:
{
lean_object* v___x_2177_; 
if (v_isShared_2175_ == 0)
{
v___x_2177_ = v___x_2174_;
goto v_reusejp_2176_;
}
else
{
lean_object* v_reuseFailAlloc_2178_; 
v_reuseFailAlloc_2178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2178_, 0, v_a_2172_);
v___x_2177_ = v_reuseFailAlloc_2178_;
goto v_reusejp_2176_;
}
v_reusejp_2176_:
{
return v___x_2177_;
}
}
}
}
else
{
lean_object* v_a_2180_; lean_object* v___x_2182_; uint8_t v_isShared_2183_; uint8_t v_isSharedCheck_2187_; 
lean_dec(v_a_2145_);
lean_dec_ref(v_major_2143_);
lean_dec_ref(v_recursorInfo_2136_);
lean_dec(v_majorFVarId_2135_);
lean_dec(v_tacticName_2134_);
lean_dec(v_mvarId_2133_);
v_a_2180_ = lean_ctor_get(v___x_2148_, 0);
v_isSharedCheck_2187_ = !lean_is_exclusive(v___x_2148_);
if (v_isSharedCheck_2187_ == 0)
{
v___x_2182_ = v___x_2148_;
v_isShared_2183_ = v_isSharedCheck_2187_;
goto v_resetjp_2181_;
}
else
{
lean_inc(v_a_2180_);
lean_dec(v___x_2148_);
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
v_reuseFailAlloc_2186_ = lean_alloc_ctor(1, 1, 0);
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
}
else
{
lean_object* v_a_2188_; lean_object* v___x_2190_; uint8_t v_isShared_2191_; uint8_t v_isSharedCheck_2195_; 
lean_dec(v_a_2145_);
lean_dec_ref(v_major_2143_);
lean_dec_ref(v_recursorInfo_2136_);
lean_dec(v_majorFVarId_2135_);
lean_dec(v_tacticName_2134_);
lean_dec(v_mvarId_2133_);
v_a_2188_ = lean_ctor_get(v___x_2146_, 0);
v_isSharedCheck_2195_ = !lean_is_exclusive(v___x_2146_);
if (v_isSharedCheck_2195_ == 0)
{
v___x_2190_ = v___x_2146_;
v_isShared_2191_ = v_isSharedCheck_2195_;
goto v_resetjp_2189_;
}
else
{
lean_inc(v_a_2188_);
lean_dec(v___x_2146_);
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
else
{
lean_dec_ref(v_major_2143_);
lean_dec_ref(v_recursorInfo_2136_);
lean_dec(v_majorFVarId_2135_);
lean_dec(v_tacticName_2134_);
lean_dec(v_mvarId_2133_);
return v___x_2144_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_mkRecursorAppPrefix_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_2133_ = stack[0].m_obj;
lean_object* v_tacticName_2134_ = stack[1].m_obj;
lean_object* v_majorFVarId_2135_ = stack[2].m_obj;
lean_object* v_recursorInfo_2136_ = stack[3].m_obj;
lean_object* v_indices_2137_ = stack[4].m_obj;
lean_object* v_a_2138_ = stack[5].m_obj;
lean_object* v_a_2139_ = stack[6].m_obj;
lean_object* v_a_2140_ = stack[7].m_obj;
lean_object* v_a_2141_ = stack[8].m_obj;
lean_object* v_res_2196_;
v_res_2196_ = l_Lean_Meta_mkRecursorAppPrefix(v_mvarId_2133_, v_tacticName_2134_, v_majorFVarId_2135_, v_recursorInfo_2136_, v_indices_2137_, v_a_2138_, v_a_2139_, v_a_2140_, v_a_2141_);
stack->m_obj
 = v_res_2196_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkRecursorAppPrefix___boxed(lean_object* v_mvarId_2197_, lean_object* v_tacticName_2198_, lean_object* v_majorFVarId_2199_, lean_object* v_recursorInfo_2200_, lean_object* v_indices_2201_, lean_object* v_a_2202_, lean_object* v_a_2203_, lean_object* v_a_2204_, lean_object* v_a_2205_, lean_object* v_a_2206_){
_start:
{
lean_object* v_res_2207_; 
v_res_2207_ = l_Lean_Meta_mkRecursorAppPrefix(v_mvarId_2197_, v_tacticName_2198_, v_majorFVarId_2199_, v_recursorInfo_2200_, v_indices_2201_, v_a_2202_, v_a_2203_, v_a_2204_, v_a_2205_);
lean_dec(v_a_2205_);
lean_dec_ref(v_a_2204_);
lean_dec(v_a_2203_);
lean_dec_ref(v_a_2202_);
lean_dec_ref(v_indices_2201_);
return v_res_2207_;
}
}
lean_object* l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1(lean_object* v_00_u03b1_2208_, lean_object* v_name_2209_, lean_object* v_msg_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_){
_start:
{
lean_object* v___x_2216_; 
v___x_2216_ = l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1___redArg(v_name_2209_, v_msg_2210_, v___y_2211_, v___y_2212_, v___y_2213_, v___y_2214_);
return v___x_2216_;
}
}
LEAN_EXPORT void l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_2209_ = stack[1].m_obj;
lean_object* v_msg_2210_ = stack[2].m_obj;
lean_object* v___y_2211_ = stack[3].m_obj;
lean_object* v___y_2212_ = stack[4].m_obj;
lean_object* v___y_2213_ = stack[5].m_obj;
lean_object* v___y_2214_ = stack[6].m_obj;
lean_object* v_res_2217_;
v_res_2217_ = l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1(lean_box(0), v_name_2209_, v_msg_2210_, v___y_2211_, v___y_2212_, v___y_2213_, v___y_2214_);
stack->m_obj
 = v_res_2217_;
}
LEAN_EXPORT lean_object* l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1___boxed(lean_object* v_00_u03b1_2218_, lean_object* v_name_2219_, lean_object* v_msg_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_){
_start:
{
lean_object* v_res_2226_; 
v_res_2226_ = l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1(v_00_u03b1_2218_, v_name_2219_, v_msg_2220_, v___y_2221_, v___y_2222_, v___y_2223_, v___y_2224_);
lean_dec(v___y_2224_);
lean_dec_ref(v___y_2223_);
lean_dec(v___y_2222_);
lean_dec_ref(v___y_2221_);
return v_res_2226_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___redArg(lean_object* v_mvarId_2227_, lean_object* v_x_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_){
_start:
{
lean_object* v___x_2234_; 
v___x_2234_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_2227_, v_x_2228_, v___y_2229_, v___y_2230_, v___y_2231_, v___y_2232_);
if (lean_obj_tag(v___x_2234_) == 0)
{
lean_object* v_a_2235_; lean_object* v___x_2237_; uint8_t v_isShared_2238_; uint8_t v_isSharedCheck_2242_; 
v_a_2235_ = lean_ctor_get(v___x_2234_, 0);
v_isSharedCheck_2242_ = !lean_is_exclusive(v___x_2234_);
if (v_isSharedCheck_2242_ == 0)
{
v___x_2237_ = v___x_2234_;
v_isShared_2238_ = v_isSharedCheck_2242_;
goto v_resetjp_2236_;
}
else
{
lean_inc(v_a_2235_);
lean_dec(v___x_2234_);
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
v_reuseFailAlloc_2241_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_2243_; lean_object* v___x_2245_; uint8_t v_isShared_2246_; uint8_t v_isSharedCheck_2250_; 
v_a_2243_ = lean_ctor_get(v___x_2234_, 0);
v_isSharedCheck_2250_ = !lean_is_exclusive(v___x_2234_);
if (v_isSharedCheck_2250_ == 0)
{
v___x_2245_ = v___x_2234_;
v_isShared_2246_ = v_isSharedCheck_2250_;
goto v_resetjp_2244_;
}
else
{
lean_inc(v_a_2243_);
lean_dec(v___x_2234_);
v___x_2245_ = lean_box(0);
v_isShared_2246_ = v_isSharedCheck_2250_;
goto v_resetjp_2244_;
}
v_resetjp_2244_:
{
lean_object* v___x_2248_; 
if (v_isShared_2246_ == 0)
{
v___x_2248_ = v___x_2245_;
goto v_reusejp_2247_;
}
else
{
lean_object* v_reuseFailAlloc_2249_; 
v_reuseFailAlloc_2249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2249_, 0, v_a_2243_);
v___x_2248_ = v_reuseFailAlloc_2249_;
goto v_reusejp_2247_;
}
v_reusejp_2247_:
{
return v___x_2248_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_2227_ = stack[0].m_obj;
lean_object* v_x_2228_ = stack[1].m_obj;
lean_object* v___y_2229_ = stack[2].m_obj;
lean_object* v___y_2230_ = stack[3].m_obj;
lean_object* v___y_2231_ = stack[4].m_obj;
lean_object* v___y_2232_ = stack[5].m_obj;
lean_object* v_res_2251_;
v_res_2251_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___redArg(v_mvarId_2227_, v_x_2228_, v___y_2229_, v___y_2230_, v___y_2231_, v___y_2232_);
stack->m_obj
 = v_res_2251_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___redArg___boxed(lean_object* v_mvarId_2252_, lean_object* v_x_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_){
_start:
{
lean_object* v_res_2259_; 
v_res_2259_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___redArg(v_mvarId_2252_, v_x_2253_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_);
lean_dec(v___y_2257_);
lean_dec_ref(v___y_2256_);
lean_dec(v___y_2255_);
lean_dec_ref(v___y_2254_);
return v_res_2259_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3(lean_object* v_00_u03b1_2260_, lean_object* v_mvarId_2261_, lean_object* v_x_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_){
_start:
{
lean_object* v___x_2268_; 
v___x_2268_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___redArg(v_mvarId_2261_, v_x_2262_, v___y_2263_, v___y_2264_, v___y_2265_, v___y_2266_);
return v___x_2268_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_2261_ = stack[1].m_obj;
lean_object* v_x_2262_ = stack[2].m_obj;
lean_object* v___y_2263_ = stack[3].m_obj;
lean_object* v___y_2264_ = stack[4].m_obj;
lean_object* v___y_2265_ = stack[5].m_obj;
lean_object* v___y_2266_ = stack[6].m_obj;
lean_object* v_res_2269_;
v_res_2269_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3(lean_box(0), v_mvarId_2261_, v_x_2262_, v___y_2263_, v___y_2264_, v___y_2265_, v___y_2266_);
stack->m_obj
 = v_res_2269_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___boxed(lean_object* v_00_u03b1_2270_, lean_object* v_mvarId_2271_, lean_object* v_x_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_){
_start:
{
lean_object* v_res_2278_; 
v_res_2278_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3(v_00_u03b1_2270_, v_mvarId_2271_, v_x_2272_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_);
lean_dec(v___y_2276_);
lean_dec_ref(v___y_2275_);
lean_dec(v___y_2274_);
lean_dec_ref(v___y_2273_);
return v_res_2278_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_induction_spec__2(lean_object* v_fst_2279_, lean_object* v_as_2280_, size_t v_sz_2281_, size_t v_i_2282_, lean_object* v_b_2283_){
_start:
{
uint8_t v___x_2284_; 
v___x_2284_ = lean_usize_dec_lt(v_i_2282_, v_sz_2281_);
if (v___x_2284_ == 0)
{
return v_b_2283_;
}
else
{
lean_object* v_fst_2285_; lean_object* v_snd_2286_; lean_object* v___x_2288_; uint8_t v_isShared_2289_; uint8_t v_isSharedCheck_2304_; 
v_fst_2285_ = lean_ctor_get(v_b_2283_, 0);
v_snd_2286_ = lean_ctor_get(v_b_2283_, 1);
v_isSharedCheck_2304_ = !lean_is_exclusive(v_b_2283_);
if (v_isSharedCheck_2304_ == 0)
{
v___x_2288_ = v_b_2283_;
v_isShared_2289_ = v_isSharedCheck_2304_;
goto v_resetjp_2287_;
}
else
{
lean_inc(v_snd_2286_);
lean_inc(v_fst_2285_);
lean_dec(v_b_2283_);
v___x_2288_ = lean_box(0);
v_isShared_2289_ = v_isSharedCheck_2304_;
goto v_resetjp_2287_;
}
v_resetjp_2287_:
{
lean_object* v___x_2290_; lean_object* v_a_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2299_; 
v___x_2290_ = lean_box(0);
v_a_2291_ = lean_array_uget_borrowed(v_as_2280_, v_i_2282_);
v___x_2292_ = l_Lean_Expr_fvarId_x21(v_a_2291_);
v___x_2293_ = lean_array_get_borrowed(v___x_2290_, v_fst_2279_, v_snd_2286_);
lean_inc(v___x_2293_);
v___x_2294_ = l_Lean_mkFVar(v___x_2293_);
v___x_2295_ = l_Lean_Meta_FVarSubst_insert(v_fst_2285_, v___x_2292_, v___x_2294_);
v___x_2296_ = lean_unsigned_to_nat(1u);
v___x_2297_ = lean_nat_add(v_snd_2286_, v___x_2296_);
lean_dec(v_snd_2286_);
if (v_isShared_2289_ == 0)
{
lean_ctor_set(v___x_2288_, 1, v___x_2297_);
lean_ctor_set(v___x_2288_, 0, v___x_2295_);
v___x_2299_ = v___x_2288_;
goto v_reusejp_2298_;
}
else
{
lean_object* v_reuseFailAlloc_2303_; 
v_reuseFailAlloc_2303_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2303_, 0, v___x_2295_);
lean_ctor_set(v_reuseFailAlloc_2303_, 1, v___x_2297_);
v___x_2299_ = v_reuseFailAlloc_2303_;
goto v_reusejp_2298_;
}
v_reusejp_2298_:
{
size_t v___x_2300_; size_t v___x_2301_; 
v___x_2300_ = ((size_t)1ULL);
v___x_2301_ = lean_usize_add(v_i_2282_, v___x_2300_);
v_i_2282_ = v___x_2301_;
v_b_2283_ = v___x_2299_;
goto _start;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_induction_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_fst_2279_ = stack[0].m_obj;
lean_object* v_as_2280_ = stack[1].m_obj;
size_t v_sz_2281_ = stack[2].m_num;
size_t v_i_2282_ = stack[3].m_num;
lean_object* v_b_2283_ = stack[4].m_obj;
lean_object* v_res_2305_;
v_res_2305_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_induction_spec__2(v_fst_2279_, v_as_2280_, v_sz_2281_, v_i_2282_, v_b_2283_);
stack->m_obj
 = v_res_2305_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_induction_spec__2___boxed(lean_object* v_fst_2306_, lean_object* v_as_2307_, lean_object* v_sz_2308_, lean_object* v_i_2309_, lean_object* v_b_2310_){
_start:
{
size_t v_sz_boxed_2311_; size_t v_i_boxed_2312_; lean_object* v_res_2313_; 
v_sz_boxed_2311_ = lean_unbox_usize(v_sz_2308_);
lean_dec(v_sz_2308_);
v_i_boxed_2312_ = lean_unbox_usize(v_i_2309_);
lean_dec(v_i_2309_);
v_res_2313_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_induction_spec__2(v_fst_2306_, v_as_2307_, v_sz_boxed_2311_, v_i_boxed_2312_, v_b_2310_);
lean_dec_ref(v_as_2307_);
lean_dec_ref(v_fst_2306_);
return v_res_2313_;
}
}
lean_object* l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4___lam__0(lean_object* v_snd_2314_, lean_object* v___x_2315_, lean_object* v_fst_2316_, lean_object* v_a_2317_, lean_object* v___x_2318_, lean_object* v_givenNames_2319_, lean_object* v_fst_2320_, lean_object* v___x_2321_, lean_object* v_fst_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_){
_start:
{
lean_object* v___x_2328_; 
lean_inc_ref(v_a_2317_);
lean_inc(v_snd_2314_);
v___x_2328_ = l_Lean_Meta_mkRecursorAppPrefix(v_snd_2314_, v___x_2315_, v_fst_2316_, v_a_2317_, v___x_2318_, v___y_2323_, v___y_2324_, v___y_2325_, v___y_2326_);
if (lean_obj_tag(v___x_2328_) == 0)
{
lean_object* v_a_2329_; lean_object* v___x_2330_; 
v_a_2329_ = lean_ctor_get(v___x_2328_, 0);
lean_inc(v_a_2329_);
lean_dec_ref_known(v___x_2328_, 1);
v___x_2330_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize(v_snd_2314_, v_givenNames_2319_, v_a_2317_, v_fst_2320_, v___x_2321_, v___x_2318_, v_fst_2322_, v_a_2329_, v___y_2323_, v___y_2324_, v___y_2325_, v___y_2326_);
lean_dec_ref(v_a_2317_);
return v___x_2330_;
}
else
{
lean_object* v_a_2331_; lean_object* v___x_2333_; uint8_t v_isShared_2334_; uint8_t v_isSharedCheck_2338_; 
lean_dec(v_fst_2322_);
lean_dec_ref(v___x_2321_);
lean_dec_ref(v_a_2317_);
lean_dec(v_snd_2314_);
v_a_2331_ = lean_ctor_get(v___x_2328_, 0);
v_isSharedCheck_2338_ = !lean_is_exclusive(v___x_2328_);
if (v_isSharedCheck_2338_ == 0)
{
v___x_2333_ = v___x_2328_;
v_isShared_2334_ = v_isSharedCheck_2338_;
goto v_resetjp_2332_;
}
else
{
lean_inc(v_a_2331_);
lean_dec(v___x_2328_);
v___x_2333_ = lean_box(0);
v_isShared_2334_ = v_isSharedCheck_2338_;
goto v_resetjp_2332_;
}
v_resetjp_2332_:
{
lean_object* v___x_2336_; 
if (v_isShared_2334_ == 0)
{
v___x_2336_ = v___x_2333_;
goto v_reusejp_2335_;
}
else
{
lean_object* v_reuseFailAlloc_2337_; 
v_reuseFailAlloc_2337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2337_, 0, v_a_2331_);
v___x_2336_ = v_reuseFailAlloc_2337_;
goto v_reusejp_2335_;
}
v_reusejp_2335_:
{
return v___x_2336_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_snd_2314_ = stack[0].m_obj;
lean_object* v___x_2315_ = stack[1].m_obj;
lean_object* v_fst_2316_ = stack[2].m_obj;
lean_object* v_a_2317_ = stack[3].m_obj;
lean_object* v___x_2318_ = stack[4].m_obj;
lean_object* v_givenNames_2319_ = stack[5].m_obj;
lean_object* v_fst_2320_ = stack[6].m_obj;
lean_object* v___x_2321_ = stack[7].m_obj;
lean_object* v_fst_2322_ = stack[8].m_obj;
lean_object* v___y_2323_ = stack[9].m_obj;
lean_object* v___y_2324_ = stack[10].m_obj;
lean_object* v___y_2325_ = stack[11].m_obj;
lean_object* v___y_2326_ = stack[12].m_obj;
lean_object* v_res_2339_;
v_res_2339_ = l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4___lam__0(v_snd_2314_, v___x_2315_, v_fst_2316_, v_a_2317_, v___x_2318_, v_givenNames_2319_, v_fst_2320_, v___x_2321_, v_fst_2322_, v___y_2323_, v___y_2324_, v___y_2325_, v___y_2326_);
stack->m_obj
 = v_res_2339_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4___lam__0___boxed(lean_object* v_snd_2340_, lean_object* v___x_2341_, lean_object* v_fst_2342_, lean_object* v_a_2343_, lean_object* v___x_2344_, lean_object* v_givenNames_2345_, lean_object* v_fst_2346_, lean_object* v___x_2347_, lean_object* v_fst_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_){
_start:
{
lean_object* v_res_2354_; 
v_res_2354_ = l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4___lam__0(v_snd_2340_, v___x_2341_, v_fst_2342_, v_a_2343_, v___x_2344_, v_givenNames_2345_, v_fst_2346_, v___x_2347_, v_fst_2348_, v___y_2349_, v___y_2350_, v___y_2351_, v___y_2352_);
lean_dec(v___y_2352_);
lean_dec_ref(v___y_2351_);
lean_dec(v___y_2350_);
lean_dec_ref(v___y_2349_);
lean_dec_ref(v_fst_2346_);
lean_dec_ref(v_givenNames_2345_);
lean_dec_ref(v___x_2344_);
return v_res_2354_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_induction_spec__1(size_t v_sz_2355_, size_t v_i_2356_, lean_object* v_bs_2357_){
_start:
{
uint8_t v___x_2358_; 
v___x_2358_ = lean_usize_dec_lt(v_i_2356_, v_sz_2355_);
if (v___x_2358_ == 0)
{
return v_bs_2357_;
}
else
{
lean_object* v_v_2359_; lean_object* v___x_2360_; lean_object* v_bs_x27_2361_; lean_object* v___x_2362_; size_t v___x_2363_; size_t v___x_2364_; lean_object* v___x_2365_; 
v_v_2359_ = lean_array_uget(v_bs_2357_, v_i_2356_);
v___x_2360_ = lean_unsigned_to_nat(0u);
v_bs_x27_2361_ = lean_array_uset(v_bs_2357_, v_i_2356_, v___x_2360_);
v___x_2362_ = l_Lean_Expr_fvarId_x21(v_v_2359_);
lean_dec(v_v_2359_);
v___x_2363_ = ((size_t)1ULL);
v___x_2364_ = lean_usize_add(v_i_2356_, v___x_2363_);
v___x_2365_ = lean_array_uset(v_bs_x27_2361_, v_i_2356_, v___x_2362_);
v_i_2356_ = v___x_2364_;
v_bs_2357_ = v___x_2365_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_induction_spec__1_0interp(lean_interpreter_value* stack)
{
size_t v_sz_2355_ = stack[0].m_num;
size_t v_i_2356_ = stack[1].m_num;
lean_object* v_bs_2357_ = stack[2].m_obj;
lean_object* v_res_2367_;
v_res_2367_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_induction_spec__1(v_sz_2355_, v_i_2356_, v_bs_2357_);
stack->m_obj
 = v_res_2367_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_induction_spec__1___boxed(lean_object* v_sz_2368_, lean_object* v_i_2369_, lean_object* v_bs_2370_){
_start:
{
size_t v_sz_boxed_2371_; size_t v_i_boxed_2372_; lean_object* v_res_2373_; 
v_sz_boxed_2371_ = lean_unbox_usize(v_sz_2368_);
lean_dec(v_sz_2368_);
v_i_boxed_2372_ = lean_unbox_usize(v_i_2369_);
lean_dec(v_i_2369_);
v_res_2373_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_induction_spec__1(v_sz_boxed_2371_, v_i_boxed_2372_, v_bs_2370_);
return v_res_2373_;
}
}
lean_object* l_List_forM___at___00Lean_MVarId_induction_spec__0(lean_object* v_majorTypeArgs_2374_, lean_object* v_val_2375_, lean_object* v_mvarId_2376_, lean_object* v_as_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_){
_start:
{
if (lean_obj_tag(v_as_2377_) == 0)
{
lean_object* v___x_2383_; lean_object* v___x_2384_; 
lean_dec(v_mvarId_2376_);
lean_dec_ref(v_val_2375_);
v___x_2383_ = lean_box(0);
v___x_2384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2384_, 0, v___x_2383_);
return v___x_2384_;
}
else
{
lean_object* v_head_2385_; 
v_head_2385_ = lean_ctor_get(v_as_2377_, 0);
lean_inc(v_head_2385_);
if (lean_obj_tag(v_head_2385_) == 0)
{
lean_object* v_tail_2386_; 
v_tail_2386_ = lean_ctor_get(v_as_2377_, 1);
lean_inc(v_tail_2386_);
lean_dec_ref_known(v_as_2377_, 2);
v_as_2377_ = v_tail_2386_;
goto _start;
}
else
{
lean_object* v_tail_2388_; lean_object* v___x_2390_; uint8_t v_isShared_2391_; uint8_t v_isSharedCheck_2411_; 
v_tail_2388_ = lean_ctor_get(v_as_2377_, 1);
v_isSharedCheck_2411_ = !lean_is_exclusive(v_as_2377_);
if (v_isSharedCheck_2411_ == 0)
{
lean_object* v_unused_2412_; 
v_unused_2412_ = lean_ctor_get(v_as_2377_, 0);
lean_dec(v_unused_2412_);
v___x_2390_ = v_as_2377_;
v_isShared_2391_ = v_isSharedCheck_2411_;
goto v_resetjp_2389_;
}
else
{
lean_inc(v_tail_2388_);
lean_dec(v_as_2377_);
v___x_2390_ = lean_box(0);
v_isShared_2391_ = v_isSharedCheck_2411_;
goto v_resetjp_2389_;
}
v_resetjp_2389_:
{
lean_object* v_val_2392_; lean_object* v___x_2394_; uint8_t v_isShared_2395_; uint8_t v_isSharedCheck_2410_; 
v_val_2392_ = lean_ctor_get(v_head_2385_, 0);
v_isSharedCheck_2410_ = !lean_is_exclusive(v_head_2385_);
if (v_isSharedCheck_2410_ == 0)
{
v___x_2394_ = v_head_2385_;
v_isShared_2395_ = v_isSharedCheck_2410_;
goto v_resetjp_2393_;
}
else
{
lean_inc(v_val_2392_);
lean_dec(v_head_2385_);
v___x_2394_ = lean_box(0);
v_isShared_2395_ = v_isSharedCheck_2410_;
goto v_resetjp_2393_;
}
v_resetjp_2393_:
{
lean_object* v___x_2396_; uint8_t v___x_2397_; 
v___x_2396_ = lean_array_get_size(v_majorTypeArgs_2374_);
v___x_2397_ = lean_nat_dec_le(v___x_2396_, v_val_2392_);
lean_dec(v_val_2392_);
if (v___x_2397_ == 0)
{
lean_del_object(v___x_2394_);
lean_del_object(v___x_2390_);
v_as_2377_ = v_tail_2388_;
goto _start;
}
else
{
lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2403_; 
v___x_2399_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1));
v___x_2400_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__5, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__5);
lean_inc_ref(v_val_2375_);
v___x_2401_ = l_Lean_indentExpr(v_val_2375_);
if (v_isShared_2391_ == 0)
{
lean_ctor_set_tag(v___x_2390_, 7);
lean_ctor_set(v___x_2390_, 1, v___x_2401_);
lean_ctor_set(v___x_2390_, 0, v___x_2400_);
v___x_2403_ = v___x_2390_;
goto v_reusejp_2402_;
}
else
{
lean_object* v_reuseFailAlloc_2409_; 
v_reuseFailAlloc_2409_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2409_, 0, v___x_2400_);
lean_ctor_set(v_reuseFailAlloc_2409_, 1, v___x_2401_);
v___x_2403_ = v_reuseFailAlloc_2409_;
goto v_reusejp_2402_;
}
v_reusejp_2402_:
{
lean_object* v___x_2405_; 
if (v_isShared_2395_ == 0)
{
lean_ctor_set(v___x_2394_, 0, v___x_2403_);
v___x_2405_ = v___x_2394_;
goto v_reusejp_2404_;
}
else
{
lean_object* v_reuseFailAlloc_2408_; 
v_reuseFailAlloc_2408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2408_, 0, v___x_2403_);
v___x_2405_ = v_reuseFailAlloc_2408_;
goto v_reusejp_2404_;
}
v_reusejp_2404_:
{
lean_object* v___x_2406_; 
lean_inc(v_mvarId_2376_);
v___x_2406_ = l_Lean_Meta_throwTacticEx___redArg(v___x_2399_, v_mvarId_2376_, v___x_2405_, v___y_2378_, v___y_2379_, v___y_2380_, v___y_2381_);
if (lean_obj_tag(v___x_2406_) == 0)
{
lean_dec_ref_known(v___x_2406_, 1);
v_as_2377_ = v_tail_2388_;
goto _start;
}
else
{
lean_dec(v_tail_2388_);
lean_dec(v_mvarId_2376_);
lean_dec_ref(v_val_2375_);
return v___x_2406_;
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
LEAN_EXPORT void l_List_forM___at___00Lean_MVarId_induction_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_majorTypeArgs_2374_ = stack[0].m_obj;
lean_object* v_val_2375_ = stack[1].m_obj;
lean_object* v_mvarId_2376_ = stack[2].m_obj;
lean_object* v_as_2377_ = stack[3].m_obj;
lean_object* v___y_2378_ = stack[4].m_obj;
lean_object* v___y_2379_ = stack[5].m_obj;
lean_object* v___y_2380_ = stack[6].m_obj;
lean_object* v___y_2381_ = stack[7].m_obj;
lean_object* v_res_2413_;
v_res_2413_ = l_List_forM___at___00Lean_MVarId_induction_spec__0(v_majorTypeArgs_2374_, v_val_2375_, v_mvarId_2376_, v_as_2377_, v___y_2378_, v___y_2379_, v___y_2380_, v___y_2381_);
stack->m_obj
 = v_res_2413_;
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_MVarId_induction_spec__0___boxed(lean_object* v_majorTypeArgs_2414_, lean_object* v_val_2415_, lean_object* v_mvarId_2416_, lean_object* v_as_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_){
_start:
{
lean_object* v_res_2423_; 
v_res_2423_ = l_List_forM___at___00Lean_MVarId_induction_spec__0(v_majorTypeArgs_2414_, v_val_2415_, v_mvarId_2416_, v_as_2417_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_);
lean_dec(v___y_2421_);
lean_dec_ref(v___y_2420_);
lean_dec(v___y_2419_);
lean_dec_ref(v___y_2418_);
lean_dec_ref(v_majorTypeArgs_2414_);
return v_res_2423_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__1(void){
_start:
{
lean_object* v___x_2425_; lean_object* v___x_2426_; 
v___x_2425_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__0));
v___x_2426_ = l_Lean_stringToMessageData(v___x_2425_);
return v___x_2426_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__3(void){
_start:
{
lean_object* v___x_2428_; lean_object* v___x_2429_; 
v___x_2428_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__2));
v___x_2429_ = l_Lean_stringToMessageData(v___x_2428_);
return v___x_2429_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__5(void){
_start:
{
lean_object* v___x_2431_; lean_object* v___x_2432_; 
v___x_2431_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__4));
v___x_2432_ = l_Lean_stringToMessageData(v___x_2431_);
return v___x_2432_;
}
}
lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4(lean_object* v_a_2433_, lean_object* v_val_2434_, lean_object* v_mvarId_2435_, lean_object* v_majorFVarId_2436_, lean_object* v_givenNames_2437_, lean_object* v_recursorName_2438_, lean_object* v_x_2439_, lean_object* v_x_2440_, lean_object* v_x_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_){
_start:
{
if (lean_obj_tag(v_x_2439_) == 5)
{
lean_object* v_fn_2447_; lean_object* v_arg_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; 
v_fn_2447_ = lean_ctor_get(v_x_2439_, 0);
lean_inc_ref(v_fn_2447_);
v_arg_2448_ = lean_ctor_get(v_x_2439_, 1);
lean_inc_ref(v_arg_2448_);
lean_dec_ref_known(v_x_2439_, 2);
v___x_2449_ = lean_array_set(v_x_2440_, v_x_2441_, v_arg_2448_);
v___x_2450_ = lean_unsigned_to_nat(1u);
v___x_2451_ = lean_nat_sub(v_x_2441_, v___x_2450_);
lean_dec(v_x_2441_);
v_x_2439_ = v_fn_2447_;
v_x_2440_ = v___x_2449_;
v_x_2441_ = v___x_2451_;
goto _start;
}
else
{
uint8_t v_depElim_2453_; lean_object* v_paramsPos_2454_; lean_object* v___x_2455_; lean_object* v___y_2457_; lean_object* v___y_2458_; lean_object* v___y_2459_; lean_object* v___y_2460_; lean_object* v___y_2461_; lean_object* v___y_2462_; size_t v___y_2463_; lean_object* v___y_2464_; lean_object* v___y_2465_; lean_object* v___y_2466_; lean_object* v___y_2467_; lean_object* v___y_2468_; lean_object* v_cls_2473_; lean_object* v___x_2474_; 
lean_dec(v_x_2441_);
lean_dec_ref(v_x_2439_);
v_depElim_2453_ = lean_ctor_get_uint8(v_a_2433_, sizeof(void*)*8);
v_paramsPos_2454_ = lean_ctor_get(v_a_2433_, 5);
v___x_2455_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1));
v_cls_2473_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__2));
lean_inc(v_paramsPos_2454_);
lean_inc(v_mvarId_2435_);
lean_inc_ref(v_val_2434_);
v___x_2474_ = l_List_forM___at___00Lean_MVarId_induction_spec__0(v_x_2440_, v_val_2434_, v_mvarId_2435_, v_paramsPos_2454_, v___y_2442_, v___y_2443_, v___y_2444_, v___y_2445_);
lean_dec_ref(v_x_2440_);
if (lean_obj_tag(v___x_2474_) == 0)
{
lean_object* v___x_2475_; 
lean_dec_ref_known(v___x_2474_, 1);
lean_inc_ref(v_a_2433_);
lean_inc(v_mvarId_2435_);
v___x_2475_ = l_Lean_Meta_getMajorTypeIndices(v_mvarId_2435_, v___x_2455_, v_a_2433_, v_val_2434_, v___y_2442_, v___y_2443_, v___y_2444_, v___y_2445_);
if (lean_obj_tag(v___x_2475_) == 0)
{
lean_object* v_a_2476_; lean_object* v___y_2478_; lean_object* v___y_2479_; lean_object* v___y_2480_; lean_object* v___y_2481_; lean_object* v___x_2565_; 
v_a_2476_ = lean_ctor_get(v___x_2475_, 0);
lean_inc(v_a_2476_);
lean_dec_ref_known(v___x_2475_, 1);
lean_inc(v_mvarId_2435_);
v___x_2565_ = l_Lean_MVarId_getType(v_mvarId_2435_, v___y_2442_, v___y_2443_, v___y_2444_, v___y_2445_);
if (lean_obj_tag(v___x_2565_) == 0)
{
if (v_depElim_2453_ == 0)
{
lean_object* v_a_2566_; lean_object* v___x_2567_; lean_object* v_a_2568_; lean_object* v___x_2570_; uint8_t v_isShared_2571_; uint8_t v_isSharedCheck_2590_; 
v_a_2566_ = lean_ctor_get(v___x_2565_, 0);
lean_inc(v_a_2566_);
lean_dec_ref_known(v___x_2565_, 1);
lean_inc(v_majorFVarId_2436_);
v___x_2567_ = l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2___redArg(v_a_2566_, v_majorFVarId_2436_, v___y_2443_);
v_a_2568_ = lean_ctor_get(v___x_2567_, 0);
v_isSharedCheck_2590_ = !lean_is_exclusive(v___x_2567_);
if (v_isSharedCheck_2590_ == 0)
{
v___x_2570_ = v___x_2567_;
v_isShared_2571_ = v_isSharedCheck_2590_;
goto v_resetjp_2569_;
}
else
{
lean_inc(v_a_2568_);
lean_dec(v___x_2567_);
v___x_2570_ = lean_box(0);
v_isShared_2571_ = v_isSharedCheck_2590_;
goto v_resetjp_2569_;
}
v_resetjp_2569_:
{
uint8_t v___x_2572_; 
v___x_2572_ = lean_unbox(v_a_2568_);
lean_dec(v_a_2568_);
if (v___x_2572_ == 0)
{
lean_del_object(v___x_2570_);
lean_dec(v_recursorName_2438_);
v___y_2478_ = v___y_2442_;
v___y_2479_ = v___y_2443_;
v___y_2480_ = v___y_2444_;
v___y_2481_ = v___y_2445_;
goto v___jp_2477_;
}
else
{
lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2579_; 
v___x_2573_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__3, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__3);
v___x_2574_ = l_Lean_MessageData_ofName(v_recursorName_2438_);
v___x_2575_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2575_, 0, v___x_2573_);
lean_ctor_set(v___x_2575_, 1, v___x_2574_);
v___x_2576_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__5, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__5_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__5);
v___x_2577_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2577_, 0, v___x_2575_);
lean_ctor_set(v___x_2577_, 1, v___x_2576_);
if (v_isShared_2571_ == 0)
{
lean_ctor_set_tag(v___x_2570_, 1);
lean_ctor_set(v___x_2570_, 0, v___x_2577_);
v___x_2579_ = v___x_2570_;
goto v_reusejp_2578_;
}
else
{
lean_object* v_reuseFailAlloc_2589_; 
v_reuseFailAlloc_2589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2589_, 0, v___x_2577_);
v___x_2579_ = v_reuseFailAlloc_2589_;
goto v_reusejp_2578_;
}
v_reusejp_2578_:
{
lean_object* v___x_2580_; 
lean_inc(v_mvarId_2435_);
v___x_2580_ = l_Lean_Meta_throwTacticEx___redArg(v___x_2455_, v_mvarId_2435_, v___x_2579_, v___y_2442_, v___y_2443_, v___y_2444_, v___y_2445_);
if (lean_obj_tag(v___x_2580_) == 0)
{
lean_dec_ref_known(v___x_2580_, 1);
v___y_2478_ = v___y_2442_;
v___y_2479_ = v___y_2443_;
v___y_2480_ = v___y_2444_;
v___y_2481_ = v___y_2445_;
goto v___jp_2477_;
}
else
{
lean_object* v_a_2581_; lean_object* v___x_2583_; uint8_t v_isShared_2584_; uint8_t v_isSharedCheck_2588_; 
lean_dec(v_a_2476_);
lean_dec_ref(v_givenNames_2437_);
lean_dec(v_majorFVarId_2436_);
lean_dec(v_mvarId_2435_);
lean_dec_ref(v_a_2433_);
v_a_2581_ = lean_ctor_get(v___x_2580_, 0);
v_isSharedCheck_2588_ = !lean_is_exclusive(v___x_2580_);
if (v_isSharedCheck_2588_ == 0)
{
v___x_2583_ = v___x_2580_;
v_isShared_2584_ = v_isSharedCheck_2588_;
goto v_resetjp_2582_;
}
else
{
lean_inc(v_a_2581_);
lean_dec(v___x_2580_);
v___x_2583_ = lean_box(0);
v_isShared_2584_ = v_isSharedCheck_2588_;
goto v_resetjp_2582_;
}
v_resetjp_2582_:
{
lean_object* v___x_2586_; 
if (v_isShared_2584_ == 0)
{
v___x_2586_ = v___x_2583_;
goto v_reusejp_2585_;
}
else
{
lean_object* v_reuseFailAlloc_2587_; 
v_reuseFailAlloc_2587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2587_, 0, v_a_2581_);
v___x_2586_ = v_reuseFailAlloc_2587_;
goto v_reusejp_2585_;
}
v_reusejp_2585_:
{
return v___x_2586_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v___x_2565_, 1);
lean_dec(v_recursorName_2438_);
v___y_2478_ = v___y_2442_;
v___y_2479_ = v___y_2443_;
v___y_2480_ = v___y_2444_;
v___y_2481_ = v___y_2445_;
goto v___jp_2477_;
}
}
else
{
lean_object* v_a_2591_; lean_object* v___x_2593_; uint8_t v_isShared_2594_; uint8_t v_isSharedCheck_2598_; 
lean_dec(v_a_2476_);
lean_dec(v_recursorName_2438_);
lean_dec_ref(v_givenNames_2437_);
lean_dec(v_majorFVarId_2436_);
lean_dec(v_mvarId_2435_);
lean_dec_ref(v_a_2433_);
v_a_2591_ = lean_ctor_get(v___x_2565_, 0);
v_isSharedCheck_2598_ = !lean_is_exclusive(v___x_2565_);
if (v_isSharedCheck_2598_ == 0)
{
v___x_2593_ = v___x_2565_;
v_isShared_2594_ = v_isSharedCheck_2598_;
goto v_resetjp_2592_;
}
else
{
lean_inc(v_a_2591_);
lean_dec(v___x_2565_);
v___x_2593_ = lean_box(0);
v_isShared_2594_ = v_isSharedCheck_2598_;
goto v_resetjp_2592_;
}
v_resetjp_2592_:
{
lean_object* v___x_2596_; 
if (v_isShared_2594_ == 0)
{
v___x_2596_ = v___x_2593_;
goto v_reusejp_2595_;
}
else
{
lean_object* v_reuseFailAlloc_2597_; 
v_reuseFailAlloc_2597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2597_, 0, v_a_2591_);
v___x_2596_ = v_reuseFailAlloc_2597_;
goto v_reusejp_2595_;
}
v_reusejp_2595_:
{
return v___x_2596_;
}
}
}
v___jp_2477_:
{
size_t v_sz_2482_; size_t v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; uint8_t v___x_2486_; uint8_t v___x_2487_; lean_object* v___x_2488_; 
v_sz_2482_ = lean_array_size(v_a_2476_);
v___x_2483_ = ((size_t)0ULL);
lean_inc(v_a_2476_);
v___x_2484_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_induction_spec__1(v_sz_2482_, v___x_2483_, v_a_2476_);
lean_inc(v_majorFVarId_2436_);
v___x_2485_ = lean_array_push(v___x_2484_, v_majorFVarId_2436_);
v___x_2486_ = 1;
v___x_2487_ = 0;
v___x_2488_ = l_Lean_MVarId_revert(v_mvarId_2435_, v___x_2485_, v___x_2486_, v___x_2487_, v___y_2478_, v___y_2479_, v___y_2480_, v___y_2481_);
if (lean_obj_tag(v___x_2488_) == 0)
{
lean_object* v_a_2489_; lean_object* v_fst_2490_; lean_object* v_snd_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; 
v_a_2489_ = lean_ctor_get(v___x_2488_, 0);
lean_inc(v_a_2489_);
lean_dec_ref_known(v___x_2488_, 1);
v_fst_2490_ = lean_ctor_get(v_a_2489_, 0);
lean_inc(v_fst_2490_);
v_snd_2491_ = lean_ctor_get(v_a_2489_, 1);
lean_inc(v_snd_2491_);
lean_dec(v_a_2489_);
v___x_2492_ = lean_array_get_size(v_a_2476_);
v___x_2493_ = lean_box(0);
v___x_2494_ = l_Lean_Meta_introNCore(v_snd_2491_, v___x_2492_, v___x_2493_, v___x_2487_, v___x_2486_, v___y_2478_, v___y_2479_, v___y_2480_, v___y_2481_);
if (lean_obj_tag(v___x_2494_) == 0)
{
lean_object* v_a_2495_; lean_object* v_fst_2496_; lean_object* v_snd_2497_; lean_object* v___x_2498_; 
v_a_2495_ = lean_ctor_get(v___x_2494_, 0);
lean_inc(v_a_2495_);
lean_dec_ref_known(v___x_2494_, 1);
v_fst_2496_ = lean_ctor_get(v_a_2495_, 0);
lean_inc(v_fst_2496_);
v_snd_2497_ = lean_ctor_get(v_a_2495_, 1);
lean_inc(v_snd_2497_);
lean_dec(v_a_2495_);
v___x_2498_ = l_Lean_Meta_intro1Core(v_snd_2497_, v___x_2486_, v___y_2478_, v___y_2479_, v___y_2480_, v___y_2481_);
if (lean_obj_tag(v___x_2498_) == 0)
{
lean_object* v_a_2499_; lean_object* v_fst_2500_; lean_object* v_snd_2501_; lean_object* v___x_2503_; uint8_t v_isShared_2504_; uint8_t v_isSharedCheck_2540_; 
v_a_2499_ = lean_ctor_get(v___x_2498_, 0);
lean_inc(v_a_2499_);
lean_dec_ref_known(v___x_2498_, 1);
v_fst_2500_ = lean_ctor_get(v_a_2499_, 0);
v_snd_2501_ = lean_ctor_get(v_a_2499_, 1);
v_isSharedCheck_2540_ = !lean_is_exclusive(v_a_2499_);
if (v_isSharedCheck_2540_ == 0)
{
v___x_2503_ = v_a_2499_;
v_isShared_2504_ = v_isSharedCheck_2540_;
goto v_resetjp_2502_;
}
else
{
lean_inc(v_snd_2501_);
lean_inc(v_fst_2500_);
lean_dec(v_a_2499_);
v___x_2503_ = lean_box(0);
v_isShared_2504_ = v_isSharedCheck_2540_;
goto v_resetjp_2502_;
}
v_resetjp_2502_:
{
lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2510_; 
v___x_2505_ = lean_box(0);
lean_inc(v_fst_2500_);
v___x_2506_ = l_Lean_mkFVar(v_fst_2500_);
lean_inc_ref(v___x_2506_);
v___x_2507_ = l_Lean_Meta_FVarSubst_insert(v___x_2505_, v_majorFVarId_2436_, v___x_2506_);
v___x_2508_ = lean_unsigned_to_nat(0u);
if (v_isShared_2504_ == 0)
{
lean_ctor_set(v___x_2503_, 1, v___x_2508_);
lean_ctor_set(v___x_2503_, 0, v___x_2507_);
v___x_2510_ = v___x_2503_;
goto v_reusejp_2509_;
}
else
{
lean_object* v_reuseFailAlloc_2539_; 
v_reuseFailAlloc_2539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2539_, 0, v___x_2507_);
lean_ctor_set(v_reuseFailAlloc_2539_, 1, v___x_2508_);
v___x_2510_ = v_reuseFailAlloc_2539_;
goto v_reusejp_2509_;
}
v_reusejp_2509_:
{
lean_object* v___x_2511_; lean_object* v_toCold_2512_; lean_object* v_options_2513_; uint8_t v_hasTrace_2514_; 
v___x_2511_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_induction_spec__2(v_fst_2496_, v_a_2476_, v_sz_2482_, v___x_2483_, v___x_2510_);
lean_dec(v_a_2476_);
v_toCold_2512_ = lean_ctor_get(v___y_2480_, 0);
v_options_2513_ = lean_ctor_get(v_toCold_2512_, 2);
v_hasTrace_2514_ = lean_ctor_get_uint8(v_options_2513_, sizeof(void*)*1);
if (v_hasTrace_2514_ == 0)
{
lean_object* v_fst_2515_; 
v_fst_2515_ = lean_ctor_get(v___x_2511_, 0);
lean_inc(v_fst_2515_);
lean_dec_ref(v___x_2511_);
lean_inc(v_snd_2501_);
v___y_2457_ = v_fst_2500_;
v___y_2458_ = v_fst_2515_;
v___y_2459_ = v___x_2506_;
v___y_2460_ = v_fst_2490_;
v___y_2461_ = v_snd_2501_;
v___y_2462_ = v_fst_2496_;
v___y_2463_ = v___x_2483_;
v___y_2464_ = v_snd_2501_;
v___y_2465_ = v___y_2478_;
v___y_2466_ = v___y_2479_;
v___y_2467_ = v___y_2480_;
v___y_2468_ = v___y_2481_;
goto v___jp_2456_;
}
else
{
lean_object* v_fst_2516_; lean_object* v___x_2518_; uint8_t v_isShared_2519_; uint8_t v_isSharedCheck_2537_; 
v_fst_2516_ = lean_ctor_get(v___x_2511_, 0);
v_isSharedCheck_2537_ = !lean_is_exclusive(v___x_2511_);
if (v_isSharedCheck_2537_ == 0)
{
lean_object* v_unused_2538_; 
v_unused_2538_ = lean_ctor_get(v___x_2511_, 1);
lean_dec(v_unused_2538_);
v___x_2518_ = v___x_2511_;
v_isShared_2519_ = v_isSharedCheck_2537_;
goto v_resetjp_2517_;
}
else
{
lean_inc(v_fst_2516_);
lean_dec(v___x_2511_);
v___x_2518_ = lean_box(0);
v_isShared_2519_ = v_isSharedCheck_2537_;
goto v_resetjp_2517_;
}
v_resetjp_2517_:
{
lean_object* v_inheritedTraceOptions_2520_; lean_object* v___x_2521_; uint8_t v___x_2522_; 
v_inheritedTraceOptions_2520_ = lean_ctor_get(v_toCold_2512_, 11);
v___x_2521_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5);
v___x_2522_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2520_, v_options_2513_, v___x_2521_);
if (v___x_2522_ == 0)
{
lean_del_object(v___x_2518_);
lean_inc(v_snd_2501_);
v___y_2457_ = v_fst_2500_;
v___y_2458_ = v_fst_2516_;
v___y_2459_ = v___x_2506_;
v___y_2460_ = v_fst_2490_;
v___y_2461_ = v_snd_2501_;
v___y_2462_ = v_fst_2496_;
v___y_2463_ = v___x_2483_;
v___y_2464_ = v_snd_2501_;
v___y_2465_ = v___y_2478_;
v___y_2466_ = v___y_2479_;
v___y_2467_ = v___y_2480_;
v___y_2468_ = v___y_2481_;
goto v___jp_2456_;
}
else
{
lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2526_; 
v___x_2523_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__1);
lean_inc(v_snd_2501_);
v___x_2524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2524_, 0, v_snd_2501_);
if (v_isShared_2519_ == 0)
{
lean_ctor_set_tag(v___x_2518_, 7);
lean_ctor_set(v___x_2518_, 1, v___x_2524_);
lean_ctor_set(v___x_2518_, 0, v___x_2523_);
v___x_2526_ = v___x_2518_;
goto v_reusejp_2525_;
}
else
{
lean_object* v_reuseFailAlloc_2536_; 
v_reuseFailAlloc_2536_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2536_, 0, v___x_2523_);
lean_ctor_set(v_reuseFailAlloc_2536_, 1, v___x_2524_);
v___x_2526_ = v_reuseFailAlloc_2536_;
goto v_reusejp_2525_;
}
v_reusejp_2525_:
{
lean_object* v___x_2527_; 
v___x_2527_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1(v_cls_2473_, v___x_2526_, v___y_2478_, v___y_2479_, v___y_2480_, v___y_2481_);
if (lean_obj_tag(v___x_2527_) == 0)
{
lean_dec_ref_known(v___x_2527_, 1);
lean_inc(v_snd_2501_);
v___y_2457_ = v_fst_2500_;
v___y_2458_ = v_fst_2516_;
v___y_2459_ = v___x_2506_;
v___y_2460_ = v_fst_2490_;
v___y_2461_ = v_snd_2501_;
v___y_2462_ = v_fst_2496_;
v___y_2463_ = v___x_2483_;
v___y_2464_ = v_snd_2501_;
v___y_2465_ = v___y_2478_;
v___y_2466_ = v___y_2479_;
v___y_2467_ = v___y_2480_;
v___y_2468_ = v___y_2481_;
goto v___jp_2456_;
}
else
{
lean_object* v_a_2528_; lean_object* v___x_2530_; uint8_t v_isShared_2531_; uint8_t v_isSharedCheck_2535_; 
lean_dec(v_fst_2516_);
lean_dec_ref(v___x_2506_);
lean_dec(v_snd_2501_);
lean_dec(v_fst_2500_);
lean_dec(v_fst_2496_);
lean_dec(v_fst_2490_);
lean_dec_ref(v_givenNames_2437_);
lean_dec_ref(v_a_2433_);
v_a_2528_ = lean_ctor_get(v___x_2527_, 0);
v_isSharedCheck_2535_ = !lean_is_exclusive(v___x_2527_);
if (v_isSharedCheck_2535_ == 0)
{
v___x_2530_ = v___x_2527_;
v_isShared_2531_ = v_isSharedCheck_2535_;
goto v_resetjp_2529_;
}
else
{
lean_inc(v_a_2528_);
lean_dec(v___x_2527_);
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
}
}
}
}
else
{
lean_object* v_a_2541_; lean_object* v___x_2543_; uint8_t v_isShared_2544_; uint8_t v_isSharedCheck_2548_; 
lean_dec(v_fst_2496_);
lean_dec(v_fst_2490_);
lean_dec(v_a_2476_);
lean_dec_ref(v_givenNames_2437_);
lean_dec(v_majorFVarId_2436_);
lean_dec_ref(v_a_2433_);
v_a_2541_ = lean_ctor_get(v___x_2498_, 0);
v_isSharedCheck_2548_ = !lean_is_exclusive(v___x_2498_);
if (v_isSharedCheck_2548_ == 0)
{
v___x_2543_ = v___x_2498_;
v_isShared_2544_ = v_isSharedCheck_2548_;
goto v_resetjp_2542_;
}
else
{
lean_inc(v_a_2541_);
lean_dec(v___x_2498_);
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
else
{
lean_object* v_a_2549_; lean_object* v___x_2551_; uint8_t v_isShared_2552_; uint8_t v_isSharedCheck_2556_; 
lean_dec(v_fst_2490_);
lean_dec(v_a_2476_);
lean_dec_ref(v_givenNames_2437_);
lean_dec(v_majorFVarId_2436_);
lean_dec_ref(v_a_2433_);
v_a_2549_ = lean_ctor_get(v___x_2494_, 0);
v_isSharedCheck_2556_ = !lean_is_exclusive(v___x_2494_);
if (v_isSharedCheck_2556_ == 0)
{
v___x_2551_ = v___x_2494_;
v_isShared_2552_ = v_isSharedCheck_2556_;
goto v_resetjp_2550_;
}
else
{
lean_inc(v_a_2549_);
lean_dec(v___x_2494_);
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
else
{
lean_object* v_a_2557_; lean_object* v___x_2559_; uint8_t v_isShared_2560_; uint8_t v_isSharedCheck_2564_; 
lean_dec(v_a_2476_);
lean_dec_ref(v_givenNames_2437_);
lean_dec(v_majorFVarId_2436_);
lean_dec_ref(v_a_2433_);
v_a_2557_ = lean_ctor_get(v___x_2488_, 0);
v_isSharedCheck_2564_ = !lean_is_exclusive(v___x_2488_);
if (v_isSharedCheck_2564_ == 0)
{
v___x_2559_ = v___x_2488_;
v_isShared_2560_ = v_isSharedCheck_2564_;
goto v_resetjp_2558_;
}
else
{
lean_inc(v_a_2557_);
lean_dec(v___x_2488_);
v___x_2559_ = lean_box(0);
v_isShared_2560_ = v_isSharedCheck_2564_;
goto v_resetjp_2558_;
}
v_resetjp_2558_:
{
lean_object* v___x_2562_; 
if (v_isShared_2560_ == 0)
{
v___x_2562_ = v___x_2559_;
goto v_reusejp_2561_;
}
else
{
lean_object* v_reuseFailAlloc_2563_; 
v_reuseFailAlloc_2563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2563_, 0, v_a_2557_);
v___x_2562_ = v_reuseFailAlloc_2563_;
goto v_reusejp_2561_;
}
v_reusejp_2561_:
{
return v___x_2562_;
}
}
}
}
}
else
{
lean_object* v_a_2599_; lean_object* v___x_2601_; uint8_t v_isShared_2602_; uint8_t v_isSharedCheck_2606_; 
lean_dec(v_recursorName_2438_);
lean_dec_ref(v_givenNames_2437_);
lean_dec(v_majorFVarId_2436_);
lean_dec(v_mvarId_2435_);
lean_dec_ref(v_a_2433_);
v_a_2599_ = lean_ctor_get(v___x_2475_, 0);
v_isSharedCheck_2606_ = !lean_is_exclusive(v___x_2475_);
if (v_isSharedCheck_2606_ == 0)
{
v___x_2601_ = v___x_2475_;
v_isShared_2602_ = v_isSharedCheck_2606_;
goto v_resetjp_2600_;
}
else
{
lean_inc(v_a_2599_);
lean_dec(v___x_2475_);
v___x_2601_ = lean_box(0);
v_isShared_2602_ = v_isSharedCheck_2606_;
goto v_resetjp_2600_;
}
v_resetjp_2600_:
{
lean_object* v___x_2604_; 
if (v_isShared_2602_ == 0)
{
v___x_2604_ = v___x_2601_;
goto v_reusejp_2603_;
}
else
{
lean_object* v_reuseFailAlloc_2605_; 
v_reuseFailAlloc_2605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2605_, 0, v_a_2599_);
v___x_2604_ = v_reuseFailAlloc_2605_;
goto v_reusejp_2603_;
}
v_reusejp_2603_:
{
return v___x_2604_;
}
}
}
}
else
{
lean_object* v_a_2607_; lean_object* v___x_2609_; uint8_t v_isShared_2610_; uint8_t v_isSharedCheck_2614_; 
lean_dec(v_recursorName_2438_);
lean_dec_ref(v_givenNames_2437_);
lean_dec(v_majorFVarId_2436_);
lean_dec(v_mvarId_2435_);
lean_dec_ref(v_val_2434_);
lean_dec_ref(v_a_2433_);
v_a_2607_ = lean_ctor_get(v___x_2474_, 0);
v_isSharedCheck_2614_ = !lean_is_exclusive(v___x_2474_);
if (v_isSharedCheck_2614_ == 0)
{
v___x_2609_ = v___x_2474_;
v_isShared_2610_ = v_isSharedCheck_2614_;
goto v_resetjp_2608_;
}
else
{
lean_inc(v_a_2607_);
lean_dec(v___x_2474_);
v___x_2609_ = lean_box(0);
v_isShared_2610_ = v_isSharedCheck_2614_;
goto v_resetjp_2608_;
}
v_resetjp_2608_:
{
lean_object* v___x_2612_; 
if (v_isShared_2610_ == 0)
{
v___x_2612_ = v___x_2609_;
goto v_reusejp_2611_;
}
else
{
lean_object* v_reuseFailAlloc_2613_; 
v_reuseFailAlloc_2613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2613_, 0, v_a_2607_);
v___x_2612_ = v_reuseFailAlloc_2613_;
goto v_reusejp_2611_;
}
v_reusejp_2611_:
{
return v___x_2612_;
}
}
}
v___jp_2456_:
{
size_t v_sz_2469_; lean_object* v___x_2470_; lean_object* v___f_2471_; lean_object* v___x_2472_; 
v_sz_2469_ = lean_array_size(v___y_2462_);
v___x_2470_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__3(v_sz_2469_, v___y_2463_, v___y_2462_);
v___f_2471_ = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4___lam__0___boxed), 14, 9);
lean_closure_set(v___f_2471_, 0, v___y_2461_);
lean_closure_set(v___f_2471_, 1, v___x_2455_);
lean_closure_set(v___f_2471_, 2, v___y_2457_);
lean_closure_set(v___f_2471_, 3, v_a_2433_);
lean_closure_set(v___f_2471_, 4, v___x_2470_);
lean_closure_set(v___f_2471_, 5, v_givenNames_2437_);
lean_closure_set(v___f_2471_, 6, v___y_2460_);
lean_closure_set(v___f_2471_, 7, v___y_2459_);
lean_closure_set(v___f_2471_, 8, v___y_2458_);
v___x_2472_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___redArg(v___y_2464_, v___f_2471_, v___y_2465_, v___y_2466_, v___y_2467_, v___y_2468_);
return v___x_2472_;
}
}
}
}
LEAN_EXPORT void l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2433_ = stack[0].m_obj;
lean_object* v_val_2434_ = stack[1].m_obj;
lean_object* v_mvarId_2435_ = stack[2].m_obj;
lean_object* v_majorFVarId_2436_ = stack[3].m_obj;
lean_object* v_givenNames_2437_ = stack[4].m_obj;
lean_object* v_recursorName_2438_ = stack[5].m_obj;
lean_object* v_x_2439_ = stack[6].m_obj;
lean_object* v_x_2440_ = stack[7].m_obj;
lean_object* v_x_2441_ = stack[8].m_obj;
lean_object* v___y_2442_ = stack[9].m_obj;
lean_object* v___y_2443_ = stack[10].m_obj;
lean_object* v___y_2444_ = stack[11].m_obj;
lean_object* v___y_2445_ = stack[12].m_obj;
lean_object* v_res_2615_;
v_res_2615_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4(v_a_2433_, v_val_2434_, v_mvarId_2435_, v_majorFVarId_2436_, v_givenNames_2437_, v_recursorName_2438_, v_x_2439_, v_x_2440_, v_x_2441_, v___y_2442_, v___y_2443_, v___y_2444_, v___y_2445_);
stack->m_obj
 = v_res_2615_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___boxed(lean_object* v_a_2616_, lean_object* v_val_2617_, lean_object* v_mvarId_2618_, lean_object* v_majorFVarId_2619_, lean_object* v_givenNames_2620_, lean_object* v_recursorName_2621_, lean_object* v_x_2622_, lean_object* v_x_2623_, lean_object* v_x_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_){
_start:
{
lean_object* v_res_2630_; 
v_res_2630_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4(v_a_2616_, v_val_2617_, v_mvarId_2618_, v_majorFVarId_2619_, v_givenNames_2620_, v_recursorName_2621_, v_x_2622_, v_x_2623_, v_x_2624_, v___y_2625_, v___y_2626_, v___y_2627_, v___y_2628_);
lean_dec(v___y_2628_);
lean_dec_ref(v___y_2627_);
lean_dec(v___y_2626_);
lean_dec_ref(v___y_2625_);
return v_res_2630_;
}
}
lean_object* l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4(lean_object* v_val_2631_, lean_object* v_mvarId_2632_, lean_object* v_a_2633_, lean_object* v_majorFVarId_2634_, lean_object* v_givenNames_2635_, lean_object* v_recursorName_2636_, lean_object* v_x_2637_, lean_object* v_x_2638_, lean_object* v_x_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_){
_start:
{
if (lean_obj_tag(v_x_2637_) == 5)
{
lean_object* v_fn_2645_; lean_object* v_arg_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; 
v_fn_2645_ = lean_ctor_get(v_x_2637_, 0);
lean_inc_ref(v_fn_2645_);
v_arg_2646_ = lean_ctor_get(v_x_2637_, 1);
lean_inc_ref(v_arg_2646_);
lean_dec_ref_known(v_x_2637_, 2);
v___x_2647_ = lean_array_set(v_x_2638_, v_x_2639_, v_arg_2646_);
v___x_2648_ = lean_unsigned_to_nat(1u);
v___x_2649_ = lean_nat_sub(v_x_2639_, v___x_2648_);
v___x_2650_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4(v_a_2633_, v_val_2631_, v_mvarId_2632_, v_majorFVarId_2634_, v_givenNames_2635_, v_recursorName_2636_, v_fn_2645_, v___x_2647_, v___x_2649_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_);
return v___x_2650_;
}
else
{
uint8_t v_depElim_2651_; lean_object* v_paramsPos_2652_; lean_object* v___x_2653_; lean_object* v___y_2655_; lean_object* v___y_2656_; lean_object* v___y_2657_; lean_object* v___y_2658_; lean_object* v___y_2659_; lean_object* v___y_2660_; lean_object* v___y_2661_; size_t v___y_2662_; lean_object* v___y_2663_; lean_object* v___y_2664_; lean_object* v___y_2665_; lean_object* v___y_2666_; lean_object* v_cls_2671_; lean_object* v___x_2672_; 
lean_dec_ref(v_x_2637_);
v_depElim_2651_ = lean_ctor_get_uint8(v_a_2633_, sizeof(void*)*8);
v_paramsPos_2652_ = lean_ctor_get(v_a_2633_, 5);
v___x_2653_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1));
v_cls_2671_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__2));
lean_inc(v_paramsPos_2652_);
lean_inc(v_mvarId_2632_);
lean_inc_ref(v_val_2631_);
v___x_2672_ = l_List_forM___at___00Lean_MVarId_induction_spec__0(v_x_2638_, v_val_2631_, v_mvarId_2632_, v_paramsPos_2652_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_);
lean_dec_ref(v_x_2638_);
if (lean_obj_tag(v___x_2672_) == 0)
{
lean_object* v___x_2673_; 
lean_dec_ref_known(v___x_2672_, 1);
lean_inc_ref(v_a_2633_);
lean_inc(v_mvarId_2632_);
v___x_2673_ = l_Lean_Meta_getMajorTypeIndices(v_mvarId_2632_, v___x_2653_, v_a_2633_, v_val_2631_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_);
if (lean_obj_tag(v___x_2673_) == 0)
{
lean_object* v_a_2674_; lean_object* v___y_2676_; lean_object* v___y_2677_; lean_object* v___y_2678_; lean_object* v___y_2679_; lean_object* v___x_2763_; 
v_a_2674_ = lean_ctor_get(v___x_2673_, 0);
lean_inc(v_a_2674_);
lean_dec_ref_known(v___x_2673_, 1);
lean_inc(v_mvarId_2632_);
v___x_2763_ = l_Lean_MVarId_getType(v_mvarId_2632_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_);
if (lean_obj_tag(v___x_2763_) == 0)
{
if (v_depElim_2651_ == 0)
{
lean_object* v_a_2764_; lean_object* v___x_2765_; lean_object* v_a_2766_; lean_object* v___x_2768_; uint8_t v_isShared_2769_; uint8_t v_isSharedCheck_2788_; 
v_a_2764_ = lean_ctor_get(v___x_2763_, 0);
lean_inc(v_a_2764_);
lean_dec_ref_known(v___x_2763_, 1);
lean_inc(v_majorFVarId_2634_);
v___x_2765_ = l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2___redArg(v_a_2764_, v_majorFVarId_2634_, v___y_2641_);
v_a_2766_ = lean_ctor_get(v___x_2765_, 0);
v_isSharedCheck_2788_ = !lean_is_exclusive(v___x_2765_);
if (v_isSharedCheck_2788_ == 0)
{
v___x_2768_ = v___x_2765_;
v_isShared_2769_ = v_isSharedCheck_2788_;
goto v_resetjp_2767_;
}
else
{
lean_inc(v_a_2766_);
lean_dec(v___x_2765_);
v___x_2768_ = lean_box(0);
v_isShared_2769_ = v_isSharedCheck_2788_;
goto v_resetjp_2767_;
}
v_resetjp_2767_:
{
uint8_t v___x_2770_; 
v___x_2770_ = lean_unbox(v_a_2766_);
lean_dec(v_a_2766_);
if (v___x_2770_ == 0)
{
lean_del_object(v___x_2768_);
lean_dec(v_recursorName_2636_);
v___y_2676_ = v___y_2640_;
v___y_2677_ = v___y_2641_;
v___y_2678_ = v___y_2642_;
v___y_2679_ = v___y_2643_;
goto v___jp_2675_;
}
else
{
lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; lean_object* v___x_2777_; 
v___x_2771_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__3, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__3);
v___x_2772_ = l_Lean_MessageData_ofName(v_recursorName_2636_);
v___x_2773_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2773_, 0, v___x_2771_);
lean_ctor_set(v___x_2773_, 1, v___x_2772_);
v___x_2774_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__5, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__5_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__5);
v___x_2775_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2775_, 0, v___x_2773_);
lean_ctor_set(v___x_2775_, 1, v___x_2774_);
if (v_isShared_2769_ == 0)
{
lean_ctor_set_tag(v___x_2768_, 1);
lean_ctor_set(v___x_2768_, 0, v___x_2775_);
v___x_2777_ = v___x_2768_;
goto v_reusejp_2776_;
}
else
{
lean_object* v_reuseFailAlloc_2787_; 
v_reuseFailAlloc_2787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2787_, 0, v___x_2775_);
v___x_2777_ = v_reuseFailAlloc_2787_;
goto v_reusejp_2776_;
}
v_reusejp_2776_:
{
lean_object* v___x_2778_; 
lean_inc(v_mvarId_2632_);
v___x_2778_ = l_Lean_Meta_throwTacticEx___redArg(v___x_2653_, v_mvarId_2632_, v___x_2777_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_);
if (lean_obj_tag(v___x_2778_) == 0)
{
lean_dec_ref_known(v___x_2778_, 1);
v___y_2676_ = v___y_2640_;
v___y_2677_ = v___y_2641_;
v___y_2678_ = v___y_2642_;
v___y_2679_ = v___y_2643_;
goto v___jp_2675_;
}
else
{
lean_object* v_a_2779_; lean_object* v___x_2781_; uint8_t v_isShared_2782_; uint8_t v_isSharedCheck_2786_; 
lean_dec(v_a_2674_);
lean_dec_ref(v_givenNames_2635_);
lean_dec(v_majorFVarId_2634_);
lean_dec_ref(v_a_2633_);
lean_dec(v_mvarId_2632_);
v_a_2779_ = lean_ctor_get(v___x_2778_, 0);
v_isSharedCheck_2786_ = !lean_is_exclusive(v___x_2778_);
if (v_isSharedCheck_2786_ == 0)
{
v___x_2781_ = v___x_2778_;
v_isShared_2782_ = v_isSharedCheck_2786_;
goto v_resetjp_2780_;
}
else
{
lean_inc(v_a_2779_);
lean_dec(v___x_2778_);
v___x_2781_ = lean_box(0);
v_isShared_2782_ = v_isSharedCheck_2786_;
goto v_resetjp_2780_;
}
v_resetjp_2780_:
{
lean_object* v___x_2784_; 
if (v_isShared_2782_ == 0)
{
v___x_2784_ = v___x_2781_;
goto v_reusejp_2783_;
}
else
{
lean_object* v_reuseFailAlloc_2785_; 
v_reuseFailAlloc_2785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2785_, 0, v_a_2779_);
v___x_2784_ = v_reuseFailAlloc_2785_;
goto v_reusejp_2783_;
}
v_reusejp_2783_:
{
return v___x_2784_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v___x_2763_, 1);
lean_dec(v_recursorName_2636_);
v___y_2676_ = v___y_2640_;
v___y_2677_ = v___y_2641_;
v___y_2678_ = v___y_2642_;
v___y_2679_ = v___y_2643_;
goto v___jp_2675_;
}
}
else
{
lean_object* v_a_2789_; lean_object* v___x_2791_; uint8_t v_isShared_2792_; uint8_t v_isSharedCheck_2796_; 
lean_dec(v_a_2674_);
lean_dec(v_recursorName_2636_);
lean_dec_ref(v_givenNames_2635_);
lean_dec(v_majorFVarId_2634_);
lean_dec_ref(v_a_2633_);
lean_dec(v_mvarId_2632_);
v_a_2789_ = lean_ctor_get(v___x_2763_, 0);
v_isSharedCheck_2796_ = !lean_is_exclusive(v___x_2763_);
if (v_isSharedCheck_2796_ == 0)
{
v___x_2791_ = v___x_2763_;
v_isShared_2792_ = v_isSharedCheck_2796_;
goto v_resetjp_2790_;
}
else
{
lean_inc(v_a_2789_);
lean_dec(v___x_2763_);
v___x_2791_ = lean_box(0);
v_isShared_2792_ = v_isSharedCheck_2796_;
goto v_resetjp_2790_;
}
v_resetjp_2790_:
{
lean_object* v___x_2794_; 
if (v_isShared_2792_ == 0)
{
v___x_2794_ = v___x_2791_;
goto v_reusejp_2793_;
}
else
{
lean_object* v_reuseFailAlloc_2795_; 
v_reuseFailAlloc_2795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2795_, 0, v_a_2789_);
v___x_2794_ = v_reuseFailAlloc_2795_;
goto v_reusejp_2793_;
}
v_reusejp_2793_:
{
return v___x_2794_;
}
}
}
v___jp_2675_:
{
size_t v_sz_2680_; size_t v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; uint8_t v___x_2684_; uint8_t v___x_2685_; lean_object* v___x_2686_; 
v_sz_2680_ = lean_array_size(v_a_2674_);
v___x_2681_ = ((size_t)0ULL);
lean_inc(v_a_2674_);
v___x_2682_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_induction_spec__1(v_sz_2680_, v___x_2681_, v_a_2674_);
lean_inc(v_majorFVarId_2634_);
v___x_2683_ = lean_array_push(v___x_2682_, v_majorFVarId_2634_);
v___x_2684_ = 1;
v___x_2685_ = 0;
v___x_2686_ = l_Lean_MVarId_revert(v_mvarId_2632_, v___x_2683_, v___x_2684_, v___x_2685_, v___y_2676_, v___y_2677_, v___y_2678_, v___y_2679_);
if (lean_obj_tag(v___x_2686_) == 0)
{
lean_object* v_a_2687_; lean_object* v_fst_2688_; lean_object* v_snd_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; 
v_a_2687_ = lean_ctor_get(v___x_2686_, 0);
lean_inc(v_a_2687_);
lean_dec_ref_known(v___x_2686_, 1);
v_fst_2688_ = lean_ctor_get(v_a_2687_, 0);
lean_inc(v_fst_2688_);
v_snd_2689_ = lean_ctor_get(v_a_2687_, 1);
lean_inc(v_snd_2689_);
lean_dec(v_a_2687_);
v___x_2690_ = lean_array_get_size(v_a_2674_);
v___x_2691_ = lean_box(0);
v___x_2692_ = l_Lean_Meta_introNCore(v_snd_2689_, v___x_2690_, v___x_2691_, v___x_2685_, v___x_2684_, v___y_2676_, v___y_2677_, v___y_2678_, v___y_2679_);
if (lean_obj_tag(v___x_2692_) == 0)
{
lean_object* v_a_2693_; lean_object* v_fst_2694_; lean_object* v_snd_2695_; lean_object* v___x_2696_; 
v_a_2693_ = lean_ctor_get(v___x_2692_, 0);
lean_inc(v_a_2693_);
lean_dec_ref_known(v___x_2692_, 1);
v_fst_2694_ = lean_ctor_get(v_a_2693_, 0);
lean_inc(v_fst_2694_);
v_snd_2695_ = lean_ctor_get(v_a_2693_, 1);
lean_inc(v_snd_2695_);
lean_dec(v_a_2693_);
v___x_2696_ = l_Lean_Meta_intro1Core(v_snd_2695_, v___x_2684_, v___y_2676_, v___y_2677_, v___y_2678_, v___y_2679_);
if (lean_obj_tag(v___x_2696_) == 0)
{
lean_object* v_a_2697_; lean_object* v_fst_2698_; lean_object* v_snd_2699_; lean_object* v___x_2701_; uint8_t v_isShared_2702_; uint8_t v_isSharedCheck_2738_; 
v_a_2697_ = lean_ctor_get(v___x_2696_, 0);
lean_inc(v_a_2697_);
lean_dec_ref_known(v___x_2696_, 1);
v_fst_2698_ = lean_ctor_get(v_a_2697_, 0);
v_snd_2699_ = lean_ctor_get(v_a_2697_, 1);
v_isSharedCheck_2738_ = !lean_is_exclusive(v_a_2697_);
if (v_isSharedCheck_2738_ == 0)
{
v___x_2701_ = v_a_2697_;
v_isShared_2702_ = v_isSharedCheck_2738_;
goto v_resetjp_2700_;
}
else
{
lean_inc(v_snd_2699_);
lean_inc(v_fst_2698_);
lean_dec(v_a_2697_);
v___x_2701_ = lean_box(0);
v_isShared_2702_ = v_isSharedCheck_2738_;
goto v_resetjp_2700_;
}
v_resetjp_2700_:
{
lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2708_; 
v___x_2703_ = lean_box(0);
lean_inc(v_fst_2698_);
v___x_2704_ = l_Lean_mkFVar(v_fst_2698_);
lean_inc_ref(v___x_2704_);
v___x_2705_ = l_Lean_Meta_FVarSubst_insert(v___x_2703_, v_majorFVarId_2634_, v___x_2704_);
v___x_2706_ = lean_unsigned_to_nat(0u);
if (v_isShared_2702_ == 0)
{
lean_ctor_set(v___x_2701_, 1, v___x_2706_);
lean_ctor_set(v___x_2701_, 0, v___x_2705_);
v___x_2708_ = v___x_2701_;
goto v_reusejp_2707_;
}
else
{
lean_object* v_reuseFailAlloc_2737_; 
v_reuseFailAlloc_2737_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2737_, 0, v___x_2705_);
lean_ctor_set(v_reuseFailAlloc_2737_, 1, v___x_2706_);
v___x_2708_ = v_reuseFailAlloc_2737_;
goto v_reusejp_2707_;
}
v_reusejp_2707_:
{
lean_object* v___x_2709_; lean_object* v_toCold_2710_; lean_object* v_options_2711_; uint8_t v_hasTrace_2712_; 
v___x_2709_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_induction_spec__2(v_fst_2694_, v_a_2674_, v_sz_2680_, v___x_2681_, v___x_2708_);
lean_dec(v_a_2674_);
v_toCold_2710_ = lean_ctor_get(v___y_2678_, 0);
v_options_2711_ = lean_ctor_get(v_toCold_2710_, 2);
v_hasTrace_2712_ = lean_ctor_get_uint8(v_options_2711_, sizeof(void*)*1);
if (v_hasTrace_2712_ == 0)
{
lean_object* v_fst_2713_; 
v_fst_2713_ = lean_ctor_get(v___x_2709_, 0);
lean_inc(v_fst_2713_);
lean_dec_ref(v___x_2709_);
lean_inc(v_snd_2699_);
v___y_2655_ = v_fst_2713_;
v___y_2656_ = v___x_2704_;
v___y_2657_ = v_fst_2688_;
v___y_2658_ = v_fst_2698_;
v___y_2659_ = v_snd_2699_;
v___y_2660_ = v_fst_2694_;
v___y_2661_ = v_snd_2699_;
v___y_2662_ = v___x_2681_;
v___y_2663_ = v___y_2676_;
v___y_2664_ = v___y_2677_;
v___y_2665_ = v___y_2678_;
v___y_2666_ = v___y_2679_;
goto v___jp_2654_;
}
else
{
lean_object* v_fst_2714_; lean_object* v___x_2716_; uint8_t v_isShared_2717_; uint8_t v_isSharedCheck_2735_; 
v_fst_2714_ = lean_ctor_get(v___x_2709_, 0);
v_isSharedCheck_2735_ = !lean_is_exclusive(v___x_2709_);
if (v_isSharedCheck_2735_ == 0)
{
lean_object* v_unused_2736_; 
v_unused_2736_ = lean_ctor_get(v___x_2709_, 1);
lean_dec(v_unused_2736_);
v___x_2716_ = v___x_2709_;
v_isShared_2717_ = v_isSharedCheck_2735_;
goto v_resetjp_2715_;
}
else
{
lean_inc(v_fst_2714_);
lean_dec(v___x_2709_);
v___x_2716_ = lean_box(0);
v_isShared_2717_ = v_isSharedCheck_2735_;
goto v_resetjp_2715_;
}
v_resetjp_2715_:
{
lean_object* v_inheritedTraceOptions_2718_; lean_object* v___x_2719_; uint8_t v___x_2720_; 
v_inheritedTraceOptions_2718_ = lean_ctor_get(v_toCold_2710_, 11);
v___x_2719_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5);
v___x_2720_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2718_, v_options_2711_, v___x_2719_);
if (v___x_2720_ == 0)
{
lean_del_object(v___x_2716_);
lean_inc(v_snd_2699_);
v___y_2655_ = v_fst_2714_;
v___y_2656_ = v___x_2704_;
v___y_2657_ = v_fst_2688_;
v___y_2658_ = v_fst_2698_;
v___y_2659_ = v_snd_2699_;
v___y_2660_ = v_fst_2694_;
v___y_2661_ = v_snd_2699_;
v___y_2662_ = v___x_2681_;
v___y_2663_ = v___y_2676_;
v___y_2664_ = v___y_2677_;
v___y_2665_ = v___y_2678_;
v___y_2666_ = v___y_2679_;
goto v___jp_2654_;
}
else
{
lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2724_; 
v___x_2721_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__1);
lean_inc(v_snd_2699_);
v___x_2722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2722_, 0, v_snd_2699_);
if (v_isShared_2717_ == 0)
{
lean_ctor_set_tag(v___x_2716_, 7);
lean_ctor_set(v___x_2716_, 1, v___x_2722_);
lean_ctor_set(v___x_2716_, 0, v___x_2721_);
v___x_2724_ = v___x_2716_;
goto v_reusejp_2723_;
}
else
{
lean_object* v_reuseFailAlloc_2734_; 
v_reuseFailAlloc_2734_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2734_, 0, v___x_2721_);
lean_ctor_set(v_reuseFailAlloc_2734_, 1, v___x_2722_);
v___x_2724_ = v_reuseFailAlloc_2734_;
goto v_reusejp_2723_;
}
v_reusejp_2723_:
{
lean_object* v___x_2725_; 
v___x_2725_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1(v_cls_2671_, v___x_2724_, v___y_2676_, v___y_2677_, v___y_2678_, v___y_2679_);
if (lean_obj_tag(v___x_2725_) == 0)
{
lean_dec_ref_known(v___x_2725_, 1);
lean_inc(v_snd_2699_);
v___y_2655_ = v_fst_2714_;
v___y_2656_ = v___x_2704_;
v___y_2657_ = v_fst_2688_;
v___y_2658_ = v_fst_2698_;
v___y_2659_ = v_snd_2699_;
v___y_2660_ = v_fst_2694_;
v___y_2661_ = v_snd_2699_;
v___y_2662_ = v___x_2681_;
v___y_2663_ = v___y_2676_;
v___y_2664_ = v___y_2677_;
v___y_2665_ = v___y_2678_;
v___y_2666_ = v___y_2679_;
goto v___jp_2654_;
}
else
{
lean_object* v_a_2726_; lean_object* v___x_2728_; uint8_t v_isShared_2729_; uint8_t v_isSharedCheck_2733_; 
lean_dec(v_fst_2714_);
lean_dec_ref(v___x_2704_);
lean_dec(v_snd_2699_);
lean_dec(v_fst_2698_);
lean_dec(v_fst_2694_);
lean_dec(v_fst_2688_);
lean_dec_ref(v_givenNames_2635_);
lean_dec_ref(v_a_2633_);
v_a_2726_ = lean_ctor_get(v___x_2725_, 0);
v_isSharedCheck_2733_ = !lean_is_exclusive(v___x_2725_);
if (v_isSharedCheck_2733_ == 0)
{
v___x_2728_ = v___x_2725_;
v_isShared_2729_ = v_isSharedCheck_2733_;
goto v_resetjp_2727_;
}
else
{
lean_inc(v_a_2726_);
lean_dec(v___x_2725_);
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
}
}
}
}
}
}
}
else
{
lean_object* v_a_2739_; lean_object* v___x_2741_; uint8_t v_isShared_2742_; uint8_t v_isSharedCheck_2746_; 
lean_dec(v_fst_2694_);
lean_dec(v_fst_2688_);
lean_dec(v_a_2674_);
lean_dec_ref(v_givenNames_2635_);
lean_dec(v_majorFVarId_2634_);
lean_dec_ref(v_a_2633_);
v_a_2739_ = lean_ctor_get(v___x_2696_, 0);
v_isSharedCheck_2746_ = !lean_is_exclusive(v___x_2696_);
if (v_isSharedCheck_2746_ == 0)
{
v___x_2741_ = v___x_2696_;
v_isShared_2742_ = v_isSharedCheck_2746_;
goto v_resetjp_2740_;
}
else
{
lean_inc(v_a_2739_);
lean_dec(v___x_2696_);
v___x_2741_ = lean_box(0);
v_isShared_2742_ = v_isSharedCheck_2746_;
goto v_resetjp_2740_;
}
v_resetjp_2740_:
{
lean_object* v___x_2744_; 
if (v_isShared_2742_ == 0)
{
v___x_2744_ = v___x_2741_;
goto v_reusejp_2743_;
}
else
{
lean_object* v_reuseFailAlloc_2745_; 
v_reuseFailAlloc_2745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2745_, 0, v_a_2739_);
v___x_2744_ = v_reuseFailAlloc_2745_;
goto v_reusejp_2743_;
}
v_reusejp_2743_:
{
return v___x_2744_;
}
}
}
}
else
{
lean_object* v_a_2747_; lean_object* v___x_2749_; uint8_t v_isShared_2750_; uint8_t v_isSharedCheck_2754_; 
lean_dec(v_fst_2688_);
lean_dec(v_a_2674_);
lean_dec_ref(v_givenNames_2635_);
lean_dec(v_majorFVarId_2634_);
lean_dec_ref(v_a_2633_);
v_a_2747_ = lean_ctor_get(v___x_2692_, 0);
v_isSharedCheck_2754_ = !lean_is_exclusive(v___x_2692_);
if (v_isSharedCheck_2754_ == 0)
{
v___x_2749_ = v___x_2692_;
v_isShared_2750_ = v_isSharedCheck_2754_;
goto v_resetjp_2748_;
}
else
{
lean_inc(v_a_2747_);
lean_dec(v___x_2692_);
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
lean_dec(v_a_2674_);
lean_dec_ref(v_givenNames_2635_);
lean_dec(v_majorFVarId_2634_);
lean_dec_ref(v_a_2633_);
v_a_2755_ = lean_ctor_get(v___x_2686_, 0);
v_isSharedCheck_2762_ = !lean_is_exclusive(v___x_2686_);
if (v_isSharedCheck_2762_ == 0)
{
v___x_2757_ = v___x_2686_;
v_isShared_2758_ = v_isSharedCheck_2762_;
goto v_resetjp_2756_;
}
else
{
lean_inc(v_a_2755_);
lean_dec(v___x_2686_);
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
}
}
else
{
lean_object* v_a_2797_; lean_object* v___x_2799_; uint8_t v_isShared_2800_; uint8_t v_isSharedCheck_2804_; 
lean_dec(v_recursorName_2636_);
lean_dec_ref(v_givenNames_2635_);
lean_dec(v_majorFVarId_2634_);
lean_dec_ref(v_a_2633_);
lean_dec(v_mvarId_2632_);
v_a_2797_ = lean_ctor_get(v___x_2673_, 0);
v_isSharedCheck_2804_ = !lean_is_exclusive(v___x_2673_);
if (v_isSharedCheck_2804_ == 0)
{
v___x_2799_ = v___x_2673_;
v_isShared_2800_ = v_isSharedCheck_2804_;
goto v_resetjp_2798_;
}
else
{
lean_inc(v_a_2797_);
lean_dec(v___x_2673_);
v___x_2799_ = lean_box(0);
v_isShared_2800_ = v_isSharedCheck_2804_;
goto v_resetjp_2798_;
}
v_resetjp_2798_:
{
lean_object* v___x_2802_; 
if (v_isShared_2800_ == 0)
{
v___x_2802_ = v___x_2799_;
goto v_reusejp_2801_;
}
else
{
lean_object* v_reuseFailAlloc_2803_; 
v_reuseFailAlloc_2803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2803_, 0, v_a_2797_);
v___x_2802_ = v_reuseFailAlloc_2803_;
goto v_reusejp_2801_;
}
v_reusejp_2801_:
{
return v___x_2802_;
}
}
}
}
else
{
lean_object* v_a_2805_; lean_object* v___x_2807_; uint8_t v_isShared_2808_; uint8_t v_isSharedCheck_2812_; 
lean_dec(v_recursorName_2636_);
lean_dec_ref(v_givenNames_2635_);
lean_dec(v_majorFVarId_2634_);
lean_dec_ref(v_a_2633_);
lean_dec(v_mvarId_2632_);
lean_dec_ref(v_val_2631_);
v_a_2805_ = lean_ctor_get(v___x_2672_, 0);
v_isSharedCheck_2812_ = !lean_is_exclusive(v___x_2672_);
if (v_isSharedCheck_2812_ == 0)
{
v___x_2807_ = v___x_2672_;
v_isShared_2808_ = v_isSharedCheck_2812_;
goto v_resetjp_2806_;
}
else
{
lean_inc(v_a_2805_);
lean_dec(v___x_2672_);
v___x_2807_ = lean_box(0);
v_isShared_2808_ = v_isSharedCheck_2812_;
goto v_resetjp_2806_;
}
v_resetjp_2806_:
{
lean_object* v___x_2810_; 
if (v_isShared_2808_ == 0)
{
v___x_2810_ = v___x_2807_;
goto v_reusejp_2809_;
}
else
{
lean_object* v_reuseFailAlloc_2811_; 
v_reuseFailAlloc_2811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2811_, 0, v_a_2805_);
v___x_2810_ = v_reuseFailAlloc_2811_;
goto v_reusejp_2809_;
}
v_reusejp_2809_:
{
return v___x_2810_;
}
}
}
v___jp_2654_:
{
size_t v_sz_2667_; lean_object* v___x_2668_; lean_object* v___f_2669_; lean_object* v___x_2670_; 
v_sz_2667_ = lean_array_size(v___y_2660_);
v___x_2668_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__3(v_sz_2667_, v___y_2662_, v___y_2660_);
v___f_2669_ = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4___lam__0___boxed), 14, 9);
lean_closure_set(v___f_2669_, 0, v___y_2659_);
lean_closure_set(v___f_2669_, 1, v___x_2653_);
lean_closure_set(v___f_2669_, 2, v___y_2658_);
lean_closure_set(v___f_2669_, 3, v_a_2633_);
lean_closure_set(v___f_2669_, 4, v___x_2668_);
lean_closure_set(v___f_2669_, 5, v_givenNames_2635_);
lean_closure_set(v___f_2669_, 6, v___y_2657_);
lean_closure_set(v___f_2669_, 7, v___y_2656_);
lean_closure_set(v___f_2669_, 8, v___y_2655_);
v___x_2670_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___redArg(v___y_2661_, v___f_2669_, v___y_2663_, v___y_2664_, v___y_2665_, v___y_2666_);
return v___x_2670_;
}
}
}
}
LEAN_EXPORT void l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_2631_ = stack[0].m_obj;
lean_object* v_mvarId_2632_ = stack[1].m_obj;
lean_object* v_a_2633_ = stack[2].m_obj;
lean_object* v_majorFVarId_2634_ = stack[3].m_obj;
lean_object* v_givenNames_2635_ = stack[4].m_obj;
lean_object* v_recursorName_2636_ = stack[5].m_obj;
lean_object* v_x_2637_ = stack[6].m_obj;
lean_object* v_x_2638_ = stack[7].m_obj;
lean_object* v_x_2639_ = stack[8].m_obj;
lean_object* v___y_2640_ = stack[9].m_obj;
lean_object* v___y_2641_ = stack[10].m_obj;
lean_object* v___y_2642_ = stack[11].m_obj;
lean_object* v___y_2643_ = stack[12].m_obj;
lean_object* v_res_2813_;
v_res_2813_ = l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4(v_val_2631_, v_mvarId_2632_, v_a_2633_, v_majorFVarId_2634_, v_givenNames_2635_, v_recursorName_2636_, v_x_2637_, v_x_2638_, v_x_2639_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_);
stack->m_obj
 = v_res_2813_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4___boxed(lean_object* v_val_2814_, lean_object* v_mvarId_2815_, lean_object* v_a_2816_, lean_object* v_majorFVarId_2817_, lean_object* v_givenNames_2818_, lean_object* v_recursorName_2819_, lean_object* v_x_2820_, lean_object* v_x_2821_, lean_object* v_x_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_){
_start:
{
lean_object* v_res_2828_; 
v_res_2828_ = l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4(v_val_2814_, v_mvarId_2815_, v_a_2816_, v_majorFVarId_2817_, v_givenNames_2818_, v_recursorName_2819_, v_x_2820_, v_x_2821_, v_x_2822_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_);
lean_dec(v___y_2826_);
lean_dec_ref(v___y_2825_);
lean_dec(v___y_2824_);
lean_dec_ref(v___y_2823_);
lean_dec(v_x_2822_);
return v_res_2828_;
}
}
static lean_object* _init_l_Lean_MVarId_induction___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2830_; lean_object* v___x_2831_; 
v___x_2830_ = ((lean_object*)(l_Lean_MVarId_induction___lam__0___closed__0));
v___x_2831_ = l_Lean_stringToMessageData(v___x_2830_);
return v___x_2831_;
}
}
lean_object* l_Lean_MVarId_induction___lam__0(lean_object* v___x_2832_, lean_object* v_mvarId_2833_, lean_object* v_majorFVarId_2834_, lean_object* v_recursorName_2835_, lean_object* v_givenNames_2836_, lean_object* v_cls_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_){
_start:
{
lean_object* v___y_2844_; lean_object* v___y_2845_; lean_object* v___y_2846_; lean_object* v___y_2847_; lean_object* v_toCold_2899_; lean_object* v_options_2900_; uint8_t v_hasTrace_2901_; 
v_toCold_2899_ = lean_ctor_get(v___y_2840_, 0);
v_options_2900_ = lean_ctor_get(v_toCold_2899_, 2);
v_hasTrace_2901_ = lean_ctor_get_uint8(v_options_2900_, sizeof(void*)*1);
if (v_hasTrace_2901_ == 0)
{
lean_dec(v_cls_2837_);
v___y_2844_ = v___y_2838_;
v___y_2845_ = v___y_2839_;
v___y_2846_ = v___y_2840_;
v___y_2847_ = v___y_2841_;
goto v___jp_2843_;
}
else
{
lean_object* v_inheritedTraceOptions_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; uint8_t v___x_2905_; 
v_inheritedTraceOptions_2902_ = lean_ctor_get(v_toCold_2899_, 11);
v___x_2903_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__4));
lean_inc(v_cls_2837_);
v___x_2904_ = l_Lean_Name_append(v___x_2903_, v_cls_2837_);
v___x_2905_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2902_, v_options_2900_, v___x_2904_);
lean_dec(v___x_2904_);
if (v___x_2905_ == 0)
{
lean_dec(v_cls_2837_);
v___y_2844_ = v___y_2838_;
v___y_2845_ = v___y_2839_;
v___y_2846_ = v___y_2840_;
v___y_2847_ = v___y_2841_;
goto v___jp_2843_;
}
else
{
lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; 
v___x_2906_ = lean_obj_once(&l_Lean_MVarId_induction___lam__0___closed__1, &l_Lean_MVarId_induction___lam__0___closed__1_once, _init_l_Lean_MVarId_induction___lam__0___closed__1);
lean_inc(v_mvarId_2833_);
v___x_2907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2907_, 0, v_mvarId_2833_);
v___x_2908_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2908_, 0, v___x_2906_);
lean_ctor_set(v___x_2908_, 1, v___x_2907_);
v___x_2909_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1(v_cls_2837_, v___x_2908_, v___y_2838_, v___y_2839_, v___y_2840_, v___y_2841_);
if (lean_obj_tag(v___x_2909_) == 0)
{
lean_dec_ref_known(v___x_2909_, 1);
v___y_2844_ = v___y_2838_;
v___y_2845_ = v___y_2839_;
v___y_2846_ = v___y_2840_;
v___y_2847_ = v___y_2841_;
goto v___jp_2843_;
}
else
{
lean_object* v_a_2910_; lean_object* v___x_2912_; uint8_t v_isShared_2913_; uint8_t v_isSharedCheck_2917_; 
lean_dec_ref(v_givenNames_2836_);
lean_dec(v_recursorName_2835_);
lean_dec(v_majorFVarId_2834_);
lean_dec(v_mvarId_2833_);
lean_dec_ref(v___x_2832_);
v_a_2910_ = lean_ctor_get(v___x_2909_, 0);
v_isSharedCheck_2917_ = !lean_is_exclusive(v___x_2909_);
if (v_isSharedCheck_2917_ == 0)
{
v___x_2912_ = v___x_2909_;
v_isShared_2913_ = v_isSharedCheck_2917_;
goto v_resetjp_2911_;
}
else
{
lean_inc(v_a_2910_);
lean_dec(v___x_2909_);
v___x_2912_ = lean_box(0);
v_isShared_2913_ = v_isSharedCheck_2917_;
goto v_resetjp_2911_;
}
v_resetjp_2911_:
{
lean_object* v___x_2915_; 
if (v_isShared_2913_ == 0)
{
v___x_2915_ = v___x_2912_;
goto v_reusejp_2914_;
}
else
{
lean_object* v_reuseFailAlloc_2916_; 
v_reuseFailAlloc_2916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2916_, 0, v_a_2910_);
v___x_2915_ = v_reuseFailAlloc_2916_;
goto v_reusejp_2914_;
}
v_reusejp_2914_:
{
return v___x_2915_;
}
}
}
}
}
v___jp_2843_:
{
lean_object* v___x_2848_; lean_object* v___x_2849_; 
v___x_2848_ = l_Lean_Name_mkStr1(v___x_2832_);
lean_inc(v___x_2848_);
lean_inc(v_mvarId_2833_);
v___x_2849_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_2833_, v___x_2848_, v___y_2844_, v___y_2845_, v___y_2846_, v___y_2847_);
if (lean_obj_tag(v___x_2849_) == 0)
{
lean_object* v___x_2850_; 
lean_dec_ref_known(v___x_2849_, 1);
lean_inc(v_majorFVarId_2834_);
v___x_2850_ = l_Lean_FVarId_getDecl___redArg(v_majorFVarId_2834_, v___y_2844_, v___y_2846_, v___y_2847_);
if (lean_obj_tag(v___x_2850_) == 0)
{
lean_object* v_a_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; 
v_a_2851_ = lean_ctor_get(v___x_2850_, 0);
lean_inc(v_a_2851_);
lean_dec_ref_known(v___x_2850_, 1);
v___x_2852_ = lean_box(0);
lean_inc(v_recursorName_2835_);
v___x_2853_ = l_Lean_Meta_mkRecursorInfo(v_recursorName_2835_, v___x_2852_, v___y_2844_, v___y_2845_, v___y_2846_, v___y_2847_);
if (lean_obj_tag(v___x_2853_) == 0)
{
lean_object* v_a_2854_; lean_object* v_typeName_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; 
v_a_2854_ = lean_ctor_get(v___x_2853_, 0);
lean_inc(v_a_2854_);
lean_dec_ref_known(v___x_2853_, 1);
v_typeName_2855_ = lean_ctor_get(v_a_2854_, 1);
v___x_2856_ = l_Lean_LocalDecl_type(v_a_2851_);
lean_dec(v_a_2851_);
lean_inc_ref(v___x_2856_);
v___x_2857_ = l_Lean_Meta_whnfUntil(v___x_2856_, v_typeName_2855_, v___y_2844_, v___y_2845_, v___y_2846_, v___y_2847_);
if (lean_obj_tag(v___x_2857_) == 0)
{
lean_object* v_a_2858_; 
v_a_2858_ = lean_ctor_get(v___x_2857_, 0);
lean_inc(v_a_2858_);
lean_dec_ref_known(v___x_2857_, 1);
if (lean_obj_tag(v_a_2858_) == 1)
{
lean_object* v_val_2859_; lean_object* v_dummy_2860_; lean_object* v_nargs_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; 
lean_dec_ref(v___x_2856_);
lean_dec(v___x_2848_);
v_val_2859_ = lean_ctor_get(v_a_2858_, 0);
lean_inc_n(v_val_2859_, 2);
lean_dec_ref_known(v_a_2858_, 1);
v_dummy_2860_ = lean_obj_once(&l_Lean_Meta_getMajorTypeIndices___closed__0, &l_Lean_Meta_getMajorTypeIndices___closed__0_once, _init_l_Lean_Meta_getMajorTypeIndices___closed__0);
v_nargs_2861_ = l_Lean_Expr_getAppNumArgs(v_val_2859_);
lean_inc(v_nargs_2861_);
v___x_2862_ = lean_mk_array(v_nargs_2861_, v_dummy_2860_);
v___x_2863_ = lean_unsigned_to_nat(1u);
v___x_2864_ = lean_nat_sub(v_nargs_2861_, v___x_2863_);
lean_dec(v_nargs_2861_);
v___x_2865_ = l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4(v_val_2859_, v_mvarId_2833_, v_a_2854_, v_majorFVarId_2834_, v_givenNames_2836_, v_recursorName_2835_, v_val_2859_, v___x_2862_, v___x_2864_, v___y_2844_, v___y_2845_, v___y_2846_, v___y_2847_);
lean_dec(v___x_2864_);
return v___x_2865_;
}
else
{
lean_object* v___x_2866_; 
lean_dec(v_a_2858_);
lean_dec(v_a_2854_);
lean_dec_ref(v_givenNames_2836_);
lean_dec(v_recursorName_2835_);
lean_dec(v_majorFVarId_2834_);
v___x_2866_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg(v___x_2848_, v_mvarId_2833_, v___x_2856_, v___y_2844_, v___y_2845_, v___y_2846_, v___y_2847_);
return v___x_2866_;
}
}
else
{
lean_object* v_a_2867_; lean_object* v___x_2869_; uint8_t v_isShared_2870_; uint8_t v_isSharedCheck_2874_; 
lean_dec_ref(v___x_2856_);
lean_dec(v_a_2854_);
lean_dec(v___x_2848_);
lean_dec_ref(v_givenNames_2836_);
lean_dec(v_recursorName_2835_);
lean_dec(v_majorFVarId_2834_);
lean_dec(v_mvarId_2833_);
v_a_2867_ = lean_ctor_get(v___x_2857_, 0);
v_isSharedCheck_2874_ = !lean_is_exclusive(v___x_2857_);
if (v_isSharedCheck_2874_ == 0)
{
v___x_2869_ = v___x_2857_;
v_isShared_2870_ = v_isSharedCheck_2874_;
goto v_resetjp_2868_;
}
else
{
lean_inc(v_a_2867_);
lean_dec(v___x_2857_);
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
else
{
lean_object* v_a_2875_; lean_object* v___x_2877_; uint8_t v_isShared_2878_; uint8_t v_isSharedCheck_2882_; 
lean_dec(v_a_2851_);
lean_dec(v___x_2848_);
lean_dec_ref(v_givenNames_2836_);
lean_dec(v_recursorName_2835_);
lean_dec(v_majorFVarId_2834_);
lean_dec(v_mvarId_2833_);
v_a_2875_ = lean_ctor_get(v___x_2853_, 0);
v_isSharedCheck_2882_ = !lean_is_exclusive(v___x_2853_);
if (v_isSharedCheck_2882_ == 0)
{
v___x_2877_ = v___x_2853_;
v_isShared_2878_ = v_isSharedCheck_2882_;
goto v_resetjp_2876_;
}
else
{
lean_inc(v_a_2875_);
lean_dec(v___x_2853_);
v___x_2877_ = lean_box(0);
v_isShared_2878_ = v_isSharedCheck_2882_;
goto v_resetjp_2876_;
}
v_resetjp_2876_:
{
lean_object* v___x_2880_; 
if (v_isShared_2878_ == 0)
{
v___x_2880_ = v___x_2877_;
goto v_reusejp_2879_;
}
else
{
lean_object* v_reuseFailAlloc_2881_; 
v_reuseFailAlloc_2881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2881_, 0, v_a_2875_);
v___x_2880_ = v_reuseFailAlloc_2881_;
goto v_reusejp_2879_;
}
v_reusejp_2879_:
{
return v___x_2880_;
}
}
}
}
else
{
lean_object* v_a_2883_; lean_object* v___x_2885_; uint8_t v_isShared_2886_; uint8_t v_isSharedCheck_2890_; 
lean_dec(v___x_2848_);
lean_dec_ref(v_givenNames_2836_);
lean_dec(v_recursorName_2835_);
lean_dec(v_majorFVarId_2834_);
lean_dec(v_mvarId_2833_);
v_a_2883_ = lean_ctor_get(v___x_2850_, 0);
v_isSharedCheck_2890_ = !lean_is_exclusive(v___x_2850_);
if (v_isSharedCheck_2890_ == 0)
{
v___x_2885_ = v___x_2850_;
v_isShared_2886_ = v_isSharedCheck_2890_;
goto v_resetjp_2884_;
}
else
{
lean_inc(v_a_2883_);
lean_dec(v___x_2850_);
v___x_2885_ = lean_box(0);
v_isShared_2886_ = v_isSharedCheck_2890_;
goto v_resetjp_2884_;
}
v_resetjp_2884_:
{
lean_object* v___x_2888_; 
if (v_isShared_2886_ == 0)
{
v___x_2888_ = v___x_2885_;
goto v_reusejp_2887_;
}
else
{
lean_object* v_reuseFailAlloc_2889_; 
v_reuseFailAlloc_2889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2889_, 0, v_a_2883_);
v___x_2888_ = v_reuseFailAlloc_2889_;
goto v_reusejp_2887_;
}
v_reusejp_2887_:
{
return v___x_2888_;
}
}
}
}
else
{
lean_object* v_a_2891_; lean_object* v___x_2893_; uint8_t v_isShared_2894_; uint8_t v_isSharedCheck_2898_; 
lean_dec(v___x_2848_);
lean_dec_ref(v_givenNames_2836_);
lean_dec(v_recursorName_2835_);
lean_dec(v_majorFVarId_2834_);
lean_dec(v_mvarId_2833_);
v_a_2891_ = lean_ctor_get(v___x_2849_, 0);
v_isSharedCheck_2898_ = !lean_is_exclusive(v___x_2849_);
if (v_isSharedCheck_2898_ == 0)
{
v___x_2893_ = v___x_2849_;
v_isShared_2894_ = v_isSharedCheck_2898_;
goto v_resetjp_2892_;
}
else
{
lean_inc(v_a_2891_);
lean_dec(v___x_2849_);
v___x_2893_ = lean_box(0);
v_isShared_2894_ = v_isSharedCheck_2898_;
goto v_resetjp_2892_;
}
v_resetjp_2892_:
{
lean_object* v___x_2896_; 
if (v_isShared_2894_ == 0)
{
v___x_2896_ = v___x_2893_;
goto v_reusejp_2895_;
}
else
{
lean_object* v_reuseFailAlloc_2897_; 
v_reuseFailAlloc_2897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2897_, 0, v_a_2891_);
v___x_2896_ = v_reuseFailAlloc_2897_;
goto v_reusejp_2895_;
}
v_reusejp_2895_:
{
return v___x_2896_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_induction___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2832_ = stack[0].m_obj;
lean_object* v_mvarId_2833_ = stack[1].m_obj;
lean_object* v_majorFVarId_2834_ = stack[2].m_obj;
lean_object* v_recursorName_2835_ = stack[3].m_obj;
lean_object* v_givenNames_2836_ = stack[4].m_obj;
lean_object* v_cls_2837_ = stack[5].m_obj;
lean_object* v___y_2838_ = stack[6].m_obj;
lean_object* v___y_2839_ = stack[7].m_obj;
lean_object* v___y_2840_ = stack[8].m_obj;
lean_object* v___y_2841_ = stack[9].m_obj;
lean_object* v_res_2918_;
v_res_2918_ = l_Lean_MVarId_induction___lam__0(v___x_2832_, v_mvarId_2833_, v_majorFVarId_2834_, v_recursorName_2835_, v_givenNames_2836_, v_cls_2837_, v___y_2838_, v___y_2839_, v___y_2840_, v___y_2841_);
stack->m_obj
 = v_res_2918_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_induction___lam__0___boxed(lean_object* v___x_2919_, lean_object* v_mvarId_2920_, lean_object* v_majorFVarId_2921_, lean_object* v_recursorName_2922_, lean_object* v_givenNames_2923_, lean_object* v_cls_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_){
_start:
{
lean_object* v_res_2930_; 
v_res_2930_ = l_Lean_MVarId_induction___lam__0(v___x_2919_, v_mvarId_2920_, v_majorFVarId_2921_, v_recursorName_2922_, v_givenNames_2923_, v_cls_2924_, v___y_2925_, v___y_2926_, v___y_2927_, v___y_2928_);
lean_dec(v___y_2928_);
lean_dec_ref(v___y_2927_);
lean_dec(v___y_2926_);
lean_dec_ref(v___y_2925_);
return v_res_2930_;
}
}
lean_object* l_Lean_MVarId_induction(lean_object* v_mvarId_2931_, lean_object* v_majorFVarId_2932_, lean_object* v_recursorName_2933_, lean_object* v_givenNames_2934_, lean_object* v_a_2935_, lean_object* v_a_2936_, lean_object* v_a_2937_, lean_object* v_a_2938_){
_start:
{
lean_object* v___x_2940_; lean_object* v_cls_2941_; lean_object* v___f_2942_; lean_object* v___x_2943_; 
v___x_2940_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__0));
v_cls_2941_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__2));
lean_inc(v_mvarId_2931_);
v___f_2942_ = lean_alloc_closure((void*)(l_Lean_MVarId_induction___lam__0___boxed), 11, 6);
lean_closure_set(v___f_2942_, 0, v___x_2940_);
lean_closure_set(v___f_2942_, 1, v_mvarId_2931_);
lean_closure_set(v___f_2942_, 2, v_majorFVarId_2932_);
lean_closure_set(v___f_2942_, 3, v_recursorName_2933_);
lean_closure_set(v___f_2942_, 4, v_givenNames_2934_);
lean_closure_set(v___f_2942_, 5, v_cls_2941_);
v___x_2943_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___redArg(v_mvarId_2931_, v___f_2942_, v_a_2935_, v_a_2936_, v_a_2937_, v_a_2938_);
return v___x_2943_;
}
}
LEAN_EXPORT void l_Lean_MVarId_induction_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_2931_ = stack[0].m_obj;
lean_object* v_majorFVarId_2932_ = stack[1].m_obj;
lean_object* v_recursorName_2933_ = stack[2].m_obj;
lean_object* v_givenNames_2934_ = stack[3].m_obj;
lean_object* v_a_2935_ = stack[4].m_obj;
lean_object* v_a_2936_ = stack[5].m_obj;
lean_object* v_a_2937_ = stack[6].m_obj;
lean_object* v_a_2938_ = stack[7].m_obj;
lean_object* v_res_2944_;
v_res_2944_ = l_Lean_MVarId_induction(v_mvarId_2931_, v_majorFVarId_2932_, v_recursorName_2933_, v_givenNames_2934_, v_a_2935_, v_a_2936_, v_a_2937_, v_a_2938_);
stack->m_obj
 = v_res_2944_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_induction___boxed(lean_object* v_mvarId_2945_, lean_object* v_majorFVarId_2946_, lean_object* v_recursorName_2947_, lean_object* v_givenNames_2948_, lean_object* v_a_2949_, lean_object* v_a_2950_, lean_object* v_a_2951_, lean_object* v_a_2952_, lean_object* v_a_2953_){
_start:
{
lean_object* v_res_2954_; 
v_res_2954_ = l_Lean_MVarId_induction(v_mvarId_2945_, v_majorFVarId_2946_, v_recursorName_2947_, v_givenNames_2948_, v_a_2949_, v_a_2950_, v_a_2951_, v_a_2952_);
lean_dec(v_a_2952_);
lean_dec_ref(v_a_2951_);
lean_dec(v_a_2950_);
lean_dec_ref(v_a_2949_);
return v_res_2954_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; 
v___x_3002_ = lean_unsigned_to_nat(2221195325u);
v___x_3003_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_));
v___x_3004_ = l_Lean_Name_num___override(v___x_3003_, v___x_3002_);
return v___x_3004_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; 
v___x_3006_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_));
v___x_3007_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_);
v___x_3008_ = l_Lean_Name_str___override(v___x_3007_, v___x_3006_);
return v___x_3008_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; 
v___x_3010_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_));
v___x_3011_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_);
v___x_3012_ = l_Lean_Name_str___override(v___x_3011_, v___x_3010_);
return v___x_3012_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; 
v___x_3013_ = lean_unsigned_to_nat(2u);
v___x_3014_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_);
v___x_3015_ = l_Lean_Name_num___override(v___x_3014_, v___x_3013_);
return v___x_3015_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3017_; uint8_t v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; 
v___x_3017_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__2));
v___x_3018_ = 0;
v___x_3019_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_);
v___x_3020_ = l_Lean_registerTraceClass(v___x_3017_, v___x_3018_, v___x_3019_);
return v___x_3020_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3021_;
v_res_3021_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_();
stack->m_obj
 = v_res_3021_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2____boxed(lean_object* v_a_3022_){
_start:
{
lean_object* v_res_3023_; 
v_res_3023_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_();
return v_res_3023_;
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
