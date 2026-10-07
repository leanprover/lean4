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
lean_object* v___f_134_; lean_object* v___x_6375__overap_135_; lean_object* v___x_136_; 
v___f_134_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__4___closed__0));
v___x_6375__overap_135_ = lean_panic_fn_borrowed(v___f_134_, v_msg_128_);
lean_inc(v___y_132_);
lean_inc_ref(v___y_131_);
lean_inc(v___y_130_);
lean_inc_ref(v___y_129_);
v___x_136_ = lean_apply_5(v___x_6375__overap_135_, v___y_129_, v___y_130_, v___y_131_, v___y_132_, lean_box(0));
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
v___x_157_ = lean_box(0);
v___x_158_ = lean_array_fget_borrowed(v_reverted_145_, v___x_154_);
v___x_159_ = lean_nat_sub(v___x_154_, v___x_144_);
lean_dec(v___x_154_);
v___x_160_ = lean_nat_sub(v___x_159_, v___x_152_);
lean_dec(v___x_159_);
v___x_161_ = lean_array_get_borrowed(v___x_157_, v_fst_146_, v___x_160_);
lean_dec(v___x_160_);
lean_inc(v___x_161_);
v___x_162_ = l_Lean_mkFVar(v___x_161_);
lean_inc(v___x_158_);
v___x_163_ = l_Lean_Meta_FVarSubst_insert(v_a_149_, v___x_158_, v___x_162_);
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
lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; 
v___x_189_ = lean_array_uget_borrowed(v_as_174_, v_i_175_);
lean_inc(v___x_189_);
v___x_190_ = l_Lean_Expr_app___override(v_fst_184_, v___x_189_);
lean_inc(v_mvarId_173_);
v___x_191_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTypeBody(v_mvarId_173_, v_snd_185_, v___x_189_, v___y_178_, v___y_179_, v___y_180_, v___y_181_);
if (lean_obj_tag(v___x_191_) == 0)
{
lean_object* v_a_192_; lean_object* v___x_194_; 
v_a_192_ = lean_ctor_get(v___x_191_, 0);
lean_inc(v_a_192_);
lean_dec_ref_known(v___x_191_, 1);
if (v_isShared_188_ == 0)
{
lean_ctor_set(v___x_187_, 1, v_a_192_);
lean_ctor_set(v___x_187_, 0, v___x_190_);
v___x_194_ = v___x_187_;
goto v_reusejp_193_;
}
else
{
lean_object* v_reuseFailAlloc_198_; 
v_reuseFailAlloc_198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_198_, 0, v___x_190_);
lean_ctor_set(v_reuseFailAlloc_198_, 1, v_a_192_);
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
lean_dec_ref(v___x_190_);
lean_del_object(v___x_187_);
lean_dec(v_mvarId_173_);
v_a_199_ = lean_ctor_get(v___x_191_, 0);
v_isSharedCheck_206_ = !lean_is_exclusive(v___x_191_);
if (v_isSharedCheck_206_ == 0)
{
v___x_201_ = v___x_191_;
v_isShared_202_ = v_isSharedCheck_206_;
goto v_resetjp_200_;
}
else
{
lean_inc(v_a_199_);
lean_dec(v___x_191_);
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
v___x_257_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
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
lean_object* v_ks_309_; lean_object* v_vs_310_; lean_object* v___x_312_; uint8_t v_isShared_313_; uint8_t v_isSharedCheck_328_; 
v_ks_309_ = lean_ctor_get(v_x_258_, 0);
v_vs_310_ = lean_ctor_get(v_x_258_, 1);
v_isSharedCheck_328_ = !lean_is_exclusive(v_x_258_);
if (v_isSharedCheck_328_ == 0)
{
v___x_312_ = v_x_258_;
v_isShared_313_ = v_isSharedCheck_328_;
goto v_resetjp_311_;
}
else
{
lean_inc(v_vs_310_);
lean_inc(v_ks_309_);
lean_dec(v_x_258_);
v___x_312_ = lean_box(0);
v_isShared_313_ = v_isSharedCheck_328_;
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
lean_object* v_reuseFailAlloc_327_; 
v_reuseFailAlloc_327_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_327_, 0, v_ks_309_);
lean_ctor_set(v_reuseFailAlloc_327_, 1, v_vs_310_);
v___x_315_ = v_reuseFailAlloc_327_;
goto v_reusejp_314_;
}
v_reusejp_314_:
{
lean_object* v_newNode_316_; size_t v___x_317_; uint8_t v___x_318_; 
v_newNode_316_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__8___redArg(v___x_315_, v_x_261_, v_x_262_);
v___x_317_ = ((size_t)7ULL);
v___x_318_ = lean_usize_dec_le(v___x_317_, v_x_260_);
if (v___x_318_ == 0)
{
lean_object* v___x_319_; lean_object* v___x_320_; uint8_t v___x_321_; 
v___x_319_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_316_);
v___x_320_ = lean_unsigned_to_nat(4u);
v___x_321_ = lean_nat_dec_lt(v___x_319_, v___x_320_);
lean_dec(v___x_319_);
if (v___x_321_ == 0)
{
lean_object* v_ks_322_; lean_object* v_vs_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; 
v_ks_322_ = lean_ctor_get(v_newNode_316_, 0);
lean_inc_ref(v_ks_322_);
v_vs_323_ = lean_ctor_get(v_newNode_316_, 1);
lean_inc_ref(v_vs_323_);
lean_dec_ref(v_newNode_316_);
v___x_324_ = lean_unsigned_to_nat(0u);
v___x_325_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2___redArg___closed__0);
v___x_326_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__9___redArg(v_x_260_, v_ks_322_, v_vs_323_, v___x_324_, v___x_325_);
lean_dec_ref(v_vs_323_);
lean_dec_ref(v_ks_322_);
return v___x_326_;
}
else
{
return v_newNode_316_;
}
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
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__9___redArg(size_t v_depth_329_, lean_object* v_keys_330_, lean_object* v_vals_331_, lean_object* v_i_332_, lean_object* v_entries_333_){
_start:
{
lean_object* v___x_334_; uint8_t v___x_335_; 
v___x_334_ = lean_array_get_size(v_keys_330_);
v___x_335_ = lean_nat_dec_lt(v_i_332_, v___x_334_);
if (v___x_335_ == 0)
{
lean_dec(v_i_332_);
return v_entries_333_;
}
else
{
lean_object* v_k_336_; lean_object* v_v_337_; uint64_t v___x_338_; size_t v_h_339_; size_t v___x_340_; lean_object* v___x_341_; size_t v___x_342_; size_t v___x_343_; size_t v___x_344_; size_t v_h_345_; lean_object* v___x_346_; lean_object* v___x_347_; 
v_k_336_ = lean_array_fget_borrowed(v_keys_330_, v_i_332_);
v_v_337_ = lean_array_fget_borrowed(v_vals_331_, v_i_332_);
v___x_338_ = l_Lean_instHashableMVarId_hash(v_k_336_);
v_h_339_ = lean_uint64_to_usize(v___x_338_);
v___x_340_ = ((size_t)5ULL);
v___x_341_ = lean_unsigned_to_nat(1u);
v___x_342_ = ((size_t)1ULL);
v___x_343_ = lean_usize_sub(v_depth_329_, v___x_342_);
v___x_344_ = lean_usize_mul(v___x_340_, v___x_343_);
v_h_345_ = lean_usize_shift_right(v_h_339_, v___x_344_);
v___x_346_ = lean_nat_add(v_i_332_, v___x_341_);
lean_dec(v_i_332_);
lean_inc(v_v_337_);
lean_inc(v_k_336_);
v___x_347_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2___redArg(v_entries_333_, v_h_345_, v_depth_329_, v_k_336_, v_v_337_);
v_i_332_ = v___x_346_;
v_entries_333_ = v___x_347_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__9___redArg___boxed(lean_object* v_depth_349_, lean_object* v_keys_350_, lean_object* v_vals_351_, lean_object* v_i_352_, lean_object* v_entries_353_){
_start:
{
size_t v_depth_boxed_354_; lean_object* v_res_355_; 
v_depth_boxed_354_ = lean_unbox_usize(v_depth_349_);
lean_dec(v_depth_349_);
v_res_355_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__9___redArg(v_depth_boxed_354_, v_keys_350_, v_vals_351_, v_i_352_, v_entries_353_);
lean_dec_ref(v_vals_351_);
lean_dec_ref(v_keys_350_);
return v_res_355_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_x_356_, lean_object* v_x_357_, lean_object* v_x_358_, lean_object* v_x_359_, lean_object* v_x_360_){
_start:
{
size_t v_x_7686__boxed_361_; size_t v_x_7687__boxed_362_; lean_object* v_res_363_; 
v_x_7686__boxed_361_ = lean_unbox_usize(v_x_357_);
lean_dec(v_x_357_);
v_x_7687__boxed_362_ = lean_unbox_usize(v_x_358_);
lean_dec(v_x_358_);
v_res_363_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2___redArg(v_x_356_, v_x_7686__boxed_361_, v_x_7687__boxed_362_, v_x_359_, v_x_360_);
return v_res_363_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0___redArg(lean_object* v_x_364_, lean_object* v_x_365_, lean_object* v_x_366_){
_start:
{
uint64_t v___x_367_; size_t v___x_368_; size_t v___x_369_; lean_object* v___x_370_; 
v___x_367_ = l_Lean_instHashableMVarId_hash(v_x_365_);
v___x_368_ = lean_uint64_to_usize(v___x_367_);
v___x_369_ = ((size_t)1ULL);
v___x_370_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2___redArg(v_x_364_, v___x_368_, v___x_369_, v_x_365_, v_x_366_);
return v___x_370_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0___redArg(lean_object* v_mvarId_371_, lean_object* v_val_372_, lean_object* v___y_373_){
_start:
{
lean_object* v___x_375_; lean_object* v_mctx_376_; lean_object* v_cache_377_; lean_object* v_zetaDeltaFVarIds_378_; lean_object* v_postponed_379_; lean_object* v_diag_380_; lean_object* v___x_382_; uint8_t v_isShared_383_; uint8_t v_isSharedCheck_410_; 
v___x_375_ = lean_st_ref_take(v___y_373_);
v_mctx_376_ = lean_ctor_get(v___x_375_, 0);
v_cache_377_ = lean_ctor_get(v___x_375_, 1);
v_zetaDeltaFVarIds_378_ = lean_ctor_get(v___x_375_, 2);
v_postponed_379_ = lean_ctor_get(v___x_375_, 3);
v_diag_380_ = lean_ctor_get(v___x_375_, 4);
v_isSharedCheck_410_ = !lean_is_exclusive(v___x_375_);
if (v_isSharedCheck_410_ == 0)
{
v___x_382_ = v___x_375_;
v_isShared_383_ = v_isSharedCheck_410_;
goto v_resetjp_381_;
}
else
{
lean_inc(v_diag_380_);
lean_inc(v_postponed_379_);
lean_inc(v_zetaDeltaFVarIds_378_);
lean_inc(v_cache_377_);
lean_inc(v_mctx_376_);
lean_dec(v___x_375_);
v___x_382_ = lean_box(0);
v_isShared_383_ = v_isSharedCheck_410_;
goto v_resetjp_381_;
}
v_resetjp_381_:
{
lean_object* v_depth_384_; lean_object* v_levelAssignDepth_385_; lean_object* v_lmvarCounter_386_; lean_object* v_mvarCounter_387_; lean_object* v_lDecls_388_; lean_object* v_decls_389_; lean_object* v_userNames_390_; lean_object* v_lAssignment_391_; lean_object* v_eAssignment_392_; lean_object* v_dAssignment_393_; lean_object* v_instanceTypedMVars_394_; lean_object* v_synthNormMemo_395_; lean_object* v___x_397_; uint8_t v_isShared_398_; uint8_t v_isSharedCheck_409_; 
v_depth_384_ = lean_ctor_get(v_mctx_376_, 0);
v_levelAssignDepth_385_ = lean_ctor_get(v_mctx_376_, 1);
v_lmvarCounter_386_ = lean_ctor_get(v_mctx_376_, 2);
v_mvarCounter_387_ = lean_ctor_get(v_mctx_376_, 3);
v_lDecls_388_ = lean_ctor_get(v_mctx_376_, 4);
v_decls_389_ = lean_ctor_get(v_mctx_376_, 5);
v_userNames_390_ = lean_ctor_get(v_mctx_376_, 6);
v_lAssignment_391_ = lean_ctor_get(v_mctx_376_, 7);
v_eAssignment_392_ = lean_ctor_get(v_mctx_376_, 8);
v_dAssignment_393_ = lean_ctor_get(v_mctx_376_, 9);
v_instanceTypedMVars_394_ = lean_ctor_get(v_mctx_376_, 10);
v_synthNormMemo_395_ = lean_ctor_get(v_mctx_376_, 11);
v_isSharedCheck_409_ = !lean_is_exclusive(v_mctx_376_);
if (v_isSharedCheck_409_ == 0)
{
v___x_397_ = v_mctx_376_;
v_isShared_398_ = v_isSharedCheck_409_;
goto v_resetjp_396_;
}
else
{
lean_inc(v_synthNormMemo_395_);
lean_inc(v_instanceTypedMVars_394_);
lean_inc(v_dAssignment_393_);
lean_inc(v_eAssignment_392_);
lean_inc(v_lAssignment_391_);
lean_inc(v_userNames_390_);
lean_inc(v_decls_389_);
lean_inc(v_lDecls_388_);
lean_inc(v_mvarCounter_387_);
lean_inc(v_lmvarCounter_386_);
lean_inc(v_levelAssignDepth_385_);
lean_inc(v_depth_384_);
lean_dec(v_mctx_376_);
v___x_397_ = lean_box(0);
v_isShared_398_ = v_isSharedCheck_409_;
goto v_resetjp_396_;
}
v_resetjp_396_:
{
lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_402_; 
v___x_399_ = lean_box(0);
v___x_400_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0___redArg(v_eAssignment_392_, v_mvarId_371_, v_val_372_);
if (v_isShared_398_ == 0)
{
lean_ctor_set(v___x_397_, 8, v___x_400_);
v___x_402_ = v___x_397_;
goto v_reusejp_401_;
}
else
{
lean_object* v_reuseFailAlloc_408_; 
v_reuseFailAlloc_408_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_408_, 0, v_depth_384_);
lean_ctor_set(v_reuseFailAlloc_408_, 1, v_levelAssignDepth_385_);
lean_ctor_set(v_reuseFailAlloc_408_, 2, v_lmvarCounter_386_);
lean_ctor_set(v_reuseFailAlloc_408_, 3, v_mvarCounter_387_);
lean_ctor_set(v_reuseFailAlloc_408_, 4, v_lDecls_388_);
lean_ctor_set(v_reuseFailAlloc_408_, 5, v_decls_389_);
lean_ctor_set(v_reuseFailAlloc_408_, 6, v_userNames_390_);
lean_ctor_set(v_reuseFailAlloc_408_, 7, v_lAssignment_391_);
lean_ctor_set(v_reuseFailAlloc_408_, 8, v___x_400_);
lean_ctor_set(v_reuseFailAlloc_408_, 9, v_dAssignment_393_);
lean_ctor_set(v_reuseFailAlloc_408_, 10, v_instanceTypedMVars_394_);
lean_ctor_set(v_reuseFailAlloc_408_, 11, v_synthNormMemo_395_);
v___x_402_ = v_reuseFailAlloc_408_;
goto v_reusejp_401_;
}
v_reusejp_401_:
{
lean_object* v___x_404_; 
if (v_isShared_383_ == 0)
{
lean_ctor_set(v___x_382_, 0, v___x_402_);
v___x_404_ = v___x_382_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_407_, 0, v___x_402_);
lean_ctor_set(v_reuseFailAlloc_407_, 1, v_cache_377_);
lean_ctor_set(v_reuseFailAlloc_407_, 2, v_zetaDeltaFVarIds_378_);
lean_ctor_set(v_reuseFailAlloc_407_, 3, v_postponed_379_);
lean_ctor_set(v_reuseFailAlloc_407_, 4, v_diag_380_);
v___x_404_ = v_reuseFailAlloc_407_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
lean_object* v___x_405_; lean_object* v___x_406_; 
v___x_405_ = lean_st_ref_put(v___y_373_, v___x_404_);
v___x_406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_406_, 0, v___x_399_);
return v___x_406_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0___redArg___boxed(lean_object* v_mvarId_411_, lean_object* v_val_412_, lean_object* v___y_413_, lean_object* v___y_414_){
_start:
{
lean_object* v_res_415_; 
v_res_415_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0___redArg(v_mvarId_411_, v_val_412_, v___y_413_);
lean_dec(v___y_413_);
return v_res_415_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1_spec__2(lean_object* v_msgData_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_){
_start:
{
lean_object* v___x_422_; lean_object* v_env_423_; uint8_t v___x_424_; lean_object* v_env_425_; lean_object* v___x_426_; lean_object* v_toCold_427_; lean_object* v_mctx_428_; lean_object* v_lctx_429_; lean_object* v_options_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; 
v___x_422_ = lean_st_ref_get(v___y_420_);
v_env_423_ = lean_ctor_get(v___x_422_, 0);
lean_inc_ref(v_env_423_);
lean_dec(v___x_422_);
v___x_424_ = 0;
v_env_425_ = l_Lean_Environment_setRecordingDeps(v_env_423_, v___x_424_);
v___x_426_ = lean_st_ref_get(v___y_418_);
v_toCold_427_ = lean_ctor_get(v___y_419_, 0);
v_mctx_428_ = lean_ctor_get(v___x_426_, 0);
lean_inc_ref(v_mctx_428_);
lean_dec(v___x_426_);
v_lctx_429_ = lean_ctor_get(v___y_417_, 2);
v_options_430_ = lean_ctor_get(v_toCold_427_, 2);
lean_inc_ref(v_options_430_);
lean_inc_ref(v_lctx_429_);
v___x_431_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_431_, 0, v_env_425_);
lean_ctor_set(v___x_431_, 1, v_mctx_428_);
lean_ctor_set(v___x_431_, 2, v_lctx_429_);
lean_ctor_set(v___x_431_, 3, v_options_430_);
v___x_432_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_432_, 0, v___x_431_);
lean_ctor_set(v___x_432_, 1, v_msgData_416_);
v___x_433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_433_, 0, v___x_432_);
return v___x_433_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1_spec__2___boxed(lean_object* v_msgData_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_){
_start:
{
lean_object* v_res_440_; 
v_res_440_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1_spec__2(v_msgData_434_, v___y_435_, v___y_436_, v___y_437_, v___y_438_);
lean_dec(v___y_438_);
lean_dec_ref(v___y_437_);
lean_dec(v___y_436_);
lean_dec_ref(v___y_435_);
return v_res_440_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1___closed__0(void){
_start:
{
lean_object* v___x_441_; double v___x_442_; 
v___x_441_ = lean_unsigned_to_nat(0u);
v___x_442_ = lean_float_of_nat(v___x_441_);
return v___x_442_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1(lean_object* v_cls_446_, lean_object* v_msg_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_){
_start:
{
lean_object* v_ref_453_; lean_object* v___x_454_; lean_object* v_a_455_; lean_object* v___x_457_; uint8_t v_isShared_458_; uint8_t v_isSharedCheck_500_; 
v_ref_453_ = lean_ctor_get(v___y_450_, 2);
v___x_454_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1_spec__2(v_msg_447_, v___y_448_, v___y_449_, v___y_450_, v___y_451_);
v_a_455_ = lean_ctor_get(v___x_454_, 0);
v_isSharedCheck_500_ = !lean_is_exclusive(v___x_454_);
if (v_isSharedCheck_500_ == 0)
{
v___x_457_ = v___x_454_;
v_isShared_458_ = v_isSharedCheck_500_;
goto v_resetjp_456_;
}
else
{
lean_inc(v_a_455_);
lean_dec(v___x_454_);
v___x_457_ = lean_box(0);
v_isShared_458_ = v_isSharedCheck_500_;
goto v_resetjp_456_;
}
v_resetjp_456_:
{
lean_object* v___x_459_; lean_object* v_traceState_460_; lean_object* v_env_461_; lean_object* v_nextMacroScope_462_; lean_object* v_ngen_463_; lean_object* v_auxDeclNGen_464_; lean_object* v_cache_465_; lean_object* v_recordedDeps_466_; lean_object* v_messages_467_; lean_object* v_infoState_468_; lean_object* v_snapshotTasks_469_; lean_object* v___x_471_; uint8_t v_isShared_472_; uint8_t v_isSharedCheck_499_; 
v___x_459_ = lean_st_ref_take(v___y_451_);
v_traceState_460_ = lean_ctor_get(v___x_459_, 4);
v_env_461_ = lean_ctor_get(v___x_459_, 0);
v_nextMacroScope_462_ = lean_ctor_get(v___x_459_, 1);
v_ngen_463_ = lean_ctor_get(v___x_459_, 2);
v_auxDeclNGen_464_ = lean_ctor_get(v___x_459_, 3);
v_cache_465_ = lean_ctor_get(v___x_459_, 5);
v_recordedDeps_466_ = lean_ctor_get(v___x_459_, 6);
v_messages_467_ = lean_ctor_get(v___x_459_, 7);
v_infoState_468_ = lean_ctor_get(v___x_459_, 8);
v_snapshotTasks_469_ = lean_ctor_get(v___x_459_, 9);
v_isSharedCheck_499_ = !lean_is_exclusive(v___x_459_);
if (v_isSharedCheck_499_ == 0)
{
v___x_471_ = v___x_459_;
v_isShared_472_ = v_isSharedCheck_499_;
goto v_resetjp_470_;
}
else
{
lean_inc(v_snapshotTasks_469_);
lean_inc(v_infoState_468_);
lean_inc(v_messages_467_);
lean_inc(v_recordedDeps_466_);
lean_inc(v_cache_465_);
lean_inc(v_traceState_460_);
lean_inc(v_auxDeclNGen_464_);
lean_inc(v_ngen_463_);
lean_inc(v_nextMacroScope_462_);
lean_inc(v_env_461_);
lean_dec(v___x_459_);
v___x_471_ = lean_box(0);
v_isShared_472_ = v_isSharedCheck_499_;
goto v_resetjp_470_;
}
v_resetjp_470_:
{
uint64_t v_tid_473_; lean_object* v_traces_474_; lean_object* v___x_476_; uint8_t v_isShared_477_; uint8_t v_isSharedCheck_498_; 
v_tid_473_ = lean_ctor_get_uint64(v_traceState_460_, sizeof(void*)*1);
v_traces_474_ = lean_ctor_get(v_traceState_460_, 0);
v_isSharedCheck_498_ = !lean_is_exclusive(v_traceState_460_);
if (v_isSharedCheck_498_ == 0)
{
v___x_476_ = v_traceState_460_;
v_isShared_477_ = v_isSharedCheck_498_;
goto v_resetjp_475_;
}
else
{
lean_inc(v_traces_474_);
lean_dec(v_traceState_460_);
v___x_476_ = lean_box(0);
v_isShared_477_ = v_isSharedCheck_498_;
goto v_resetjp_475_;
}
v_resetjp_475_:
{
lean_object* v___x_478_; lean_object* v___x_479_; double v___x_480_; uint8_t v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_489_; 
v___x_478_ = lean_box(0);
v___x_479_ = lean_box(0);
v___x_480_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1___closed__0);
v___x_481_ = 0;
v___x_482_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1___closed__1));
v___x_483_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_483_, 0, v_cls_446_);
lean_ctor_set(v___x_483_, 1, v___x_479_);
lean_ctor_set(v___x_483_, 2, v___x_482_);
lean_ctor_set_float(v___x_483_, sizeof(void*)*3, v___x_480_);
lean_ctor_set_float(v___x_483_, sizeof(void*)*3 + 8, v___x_480_);
lean_ctor_set_uint8(v___x_483_, sizeof(void*)*3 + 16, v___x_481_);
v___x_484_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1___closed__2));
v___x_485_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_485_, 0, v___x_483_);
lean_ctor_set(v___x_485_, 1, v_a_455_);
lean_ctor_set(v___x_485_, 2, v___x_484_);
lean_inc(v_ref_453_);
v___x_486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_486_, 0, v_ref_453_);
lean_ctor_set(v___x_486_, 1, v___x_485_);
v___x_487_ = l_Lean_PersistentArray_push___redArg(v_traces_474_, v___x_486_);
if (v_isShared_477_ == 0)
{
lean_ctor_set(v___x_476_, 0, v___x_487_);
v___x_489_ = v___x_476_;
goto v_reusejp_488_;
}
else
{
lean_object* v_reuseFailAlloc_497_; 
v_reuseFailAlloc_497_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_497_, 0, v___x_487_);
lean_ctor_set_uint64(v_reuseFailAlloc_497_, sizeof(void*)*1, v_tid_473_);
v___x_489_ = v_reuseFailAlloc_497_;
goto v_reusejp_488_;
}
v_reusejp_488_:
{
lean_object* v___x_491_; 
if (v_isShared_472_ == 0)
{
lean_ctor_set(v___x_471_, 4, v___x_489_);
v___x_491_ = v___x_471_;
goto v_reusejp_490_;
}
else
{
lean_object* v_reuseFailAlloc_496_; 
v_reuseFailAlloc_496_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_496_, 0, v_env_461_);
lean_ctor_set(v_reuseFailAlloc_496_, 1, v_nextMacroScope_462_);
lean_ctor_set(v_reuseFailAlloc_496_, 2, v_ngen_463_);
lean_ctor_set(v_reuseFailAlloc_496_, 3, v_auxDeclNGen_464_);
lean_ctor_set(v_reuseFailAlloc_496_, 4, v___x_489_);
lean_ctor_set(v_reuseFailAlloc_496_, 5, v_cache_465_);
lean_ctor_set(v_reuseFailAlloc_496_, 6, v_recordedDeps_466_);
lean_ctor_set(v_reuseFailAlloc_496_, 7, v_messages_467_);
lean_ctor_set(v_reuseFailAlloc_496_, 8, v_infoState_468_);
lean_ctor_set(v_reuseFailAlloc_496_, 9, v_snapshotTasks_469_);
v___x_491_ = v_reuseFailAlloc_496_;
goto v_reusejp_490_;
}
v_reusejp_490_:
{
lean_object* v___x_492_; lean_object* v___x_494_; 
v___x_492_ = lean_st_ref_put(v___y_451_, v___x_491_);
if (v_isShared_458_ == 0)
{
lean_ctor_set(v___x_457_, 0, v___x_478_);
v___x_494_ = v___x_457_;
goto v_reusejp_493_;
}
else
{
lean_object* v_reuseFailAlloc_495_; 
v_reuseFailAlloc_495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_495_, 0, v___x_478_);
v___x_494_ = v_reuseFailAlloc_495_;
goto v_reusejp_493_;
}
v_reusejp_493_:
{
return v___x_494_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1___boxed(lean_object* v_cls_501_, lean_object* v_msg_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_){
_start:
{
lean_object* v_res_508_; 
v_res_508_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1(v_cls_501_, v_msg_502_, v___y_503_, v___y_504_, v___y_505_, v___y_506_);
lean_dec(v___y_506_);
lean_dec_ref(v___y_505_);
lean_dec(v___y_504_);
lean_dec_ref(v___y_503_);
return v_res_508_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__3(size_t v_sz_509_, size_t v_i_510_, lean_object* v_bs_511_){
_start:
{
uint8_t v___x_512_; 
v___x_512_ = lean_usize_dec_lt(v_i_510_, v_sz_509_);
if (v___x_512_ == 0)
{
return v_bs_511_;
}
else
{
lean_object* v_v_513_; lean_object* v___x_514_; lean_object* v_bs_x27_515_; lean_object* v___x_516_; size_t v___x_517_; size_t v___x_518_; lean_object* v___x_519_; 
v_v_513_ = lean_array_uget(v_bs_511_, v_i_510_);
v___x_514_ = lean_unsigned_to_nat(0u);
v_bs_x27_515_ = lean_array_uset(v_bs_511_, v_i_510_, v___x_514_);
v___x_516_ = l_Lean_mkFVar(v_v_513_);
v___x_517_ = ((size_t)1ULL);
v___x_518_ = lean_usize_add(v_i_510_, v___x_517_);
v___x_519_ = lean_array_uset(v_bs_x27_515_, v_i_510_, v___x_516_);
v_i_510_ = v___x_518_;
v_bs_511_ = v___x_519_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__3___boxed(lean_object* v_sz_521_, lean_object* v_i_522_, lean_object* v_bs_523_){
_start:
{
size_t v_sz_boxed_524_; size_t v_i_boxed_525_; lean_object* v_res_526_; 
v_sz_boxed_524_ = lean_unbox_usize(v_sz_521_);
lean_dec(v_sz_521_);
v_i_boxed_525_ = lean_unbox_usize(v_i_522_);
lean_dec(v_i_522_);
v_res_526_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__3(v_sz_boxed_524_, v_i_boxed_525_, v_bs_523_);
return v_res_526_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5(void){
_start:
{
lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; 
v___x_536_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__2));
v___x_537_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__4));
v___x_538_ = l_Lean_Name_append(v___x_537_, v___x_536_);
return v___x_538_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__7(void){
_start:
{
lean_object* v___x_540_; lean_object* v___x_541_; 
v___x_540_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__6));
v___x_541_ = l_Lean_stringToMessageData(v___x_540_);
return v___x_541_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__9(void){
_start:
{
lean_object* v___x_543_; lean_object* v___x_544_; 
v___x_543_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__8));
v___x_544_ = l_Lean_stringToMessageData(v___x_543_);
return v___x_544_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__11(void){
_start:
{
lean_object* v___x_546_; lean_object* v___x_547_; 
v___x_546_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__10));
v___x_547_ = l_Lean_stringToMessageData(v___x_546_);
return v___x_547_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__15(void){
_start:
{
lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; 
v___x_551_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__14));
v___x_552_ = lean_unsigned_to_nat(15u);
v___x_553_ = lean_unsigned_to_nat(120u);
v___x_554_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__13));
v___x_555_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__12));
v___x_556_ = l_mkPanicMessageWithDecl(v___x_555_, v___x_554_, v___x_553_, v___x_552_, v___x_551_);
return v___x_556_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop(lean_object* v_mvarId_557_, lean_object* v_givenNames_558_, lean_object* v_recursorInfo_559_, lean_object* v_reverted_560_, lean_object* v_major_561_, lean_object* v_indices_562_, lean_object* v_baseSubst_563_, lean_object* v_initialArity_564_, lean_object* v_numMinors_565_, lean_object* v_pos_566_, lean_object* v_minorIdx_567_, lean_object* v_recursor_568_, lean_object* v_recursorType_569_, uint8_t v_consumedMajor_570_, lean_object* v_subgoals_571_, lean_object* v_a_572_, lean_object* v_a_573_, lean_object* v_a_574_, lean_object* v_a_575_){
_start:
{
lean_object* v___y_578_; lean_object* v___y_579_; lean_object* v___y_580_; lean_object* v___y_581_; lean_object* v___y_635_; lean_object* v___y_636_; uint8_t v___y_637_; lean_object* v___y_638_; lean_object* v___y_639_; uint8_t v___y_640_; lean_object* v___y_641_; lean_object* v___y_642_; lean_object* v___y_643_; lean_object* v___y_644_; lean_object* v___y_645_; lean_object* v___y_646_; lean_object* v___y_647_; lean_object* v___y_648_; lean_object* v___y_649_; uint8_t v___y_650_; lean_object* v___y_686_; lean_object* v___y_687_; lean_object* v___y_688_; lean_object* v___y_689_; lean_object* v___y_690_; uint8_t v___y_691_; lean_object* v___y_692_; lean_object* v___y_693_; lean_object* v___y_694_; uint8_t v___y_695_; lean_object* v___y_696_; lean_object* v___y_697_; lean_object* v___y_698_; lean_object* v___y_699_; lean_object* v___y_700_; uint8_t v___y_718_; lean_object* v___y_719_; lean_object* v_fst_720_; lean_object* v_snd_721_; uint8_t v___y_738_; lean_object* v___y_739_; lean_object* v___y_740_; lean_object* v___x_752_; 
v___x_752_ = l_Lean_Meta_whnfForall(v_recursorType_569_, v_a_572_, v_a_573_, v_a_574_, v_a_575_);
if (lean_obj_tag(v___x_752_) == 0)
{
lean_object* v_a_753_; lean_object* v___y_755_; lean_object* v___y_756_; uint8_t v___y_757_; lean_object* v___y_758_; lean_object* v___y_759_; uint8_t v___y_760_; lean_object* v___y_761_; lean_object* v___y_762_; lean_object* v___y_763_; lean_object* v___y_764_; lean_object* v___y_765_; lean_object* v___y_766_; lean_object* v___y_767_; lean_object* v___y_768_; lean_object* v___y_812_; uint8_t v___y_813_; lean_object* v___y_814_; uint8_t v___y_815_; lean_object* v___y_816_; lean_object* v___y_817_; lean_object* v___y_818_; lean_object* v___y_819_; lean_object* v___y_820_; lean_object* v___y_821_; lean_object* v___y_833_; lean_object* v___y_834_; lean_object* v___y_835_; lean_object* v___y_836_; uint8_t v___y_837_; lean_object* v___y_838_; lean_object* v___y_839_; lean_object* v___y_840_; uint8_t v___y_841_; lean_object* v___y_911_; lean_object* v___y_912_; lean_object* v___y_913_; lean_object* v___y_914_; uint8_t v___y_915_; lean_object* v___y_916_; lean_object* v___y_917_; uint8_t v___y_918_; lean_object* v___y_919_; uint8_t v___y_925_; lean_object* v___y_926_; lean_object* v___y_927_; lean_object* v___y_928_; lean_object* v___y_929_; lean_object* v___y_930_; uint8_t v___y_942_; uint8_t v___x_989_; 
v_a_753_ = lean_ctor_get(v___x_752_, 0);
lean_inc(v_a_753_);
lean_dec_ref_known(v___x_752_, 1);
v___x_989_ = l_Lean_Expr_isForall(v_a_753_);
if (v___x_989_ == 0)
{
v___y_942_ = v___x_989_;
goto v___jp_941_;
}
else
{
lean_object* v_numArgs_990_; uint8_t v___x_991_; 
v_numArgs_990_ = lean_ctor_get(v_recursorInfo_559_, 3);
v___x_991_ = lean_nat_dec_lt(v_pos_566_, v_numArgs_990_);
v___y_942_ = v___x_991_;
goto v___jp_941_;
}
v___jp_754_:
{
lean_object* v___x_769_; 
v___x_769_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___y_766_, v___y_767_, v___y_764_, v___y_756_, v___y_765_, v___y_761_);
if (lean_obj_tag(v___x_769_) == 0)
{
lean_object* v_a_770_; lean_object* v___x_771_; lean_object* v___x_772_; 
v_a_770_ = lean_ctor_get(v___x_769_, 0);
lean_inc_n(v_a_770_, 2);
lean_dec_ref_known(v___x_769_, 1);
v___x_771_ = l_Lean_Expr_app___override(v_recursor_568_, v_a_770_);
lean_inc(v_mvarId_557_);
v___x_772_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTypeBody(v_mvarId_557_, v_a_753_, v_a_770_, v___y_764_, v___y_756_, v___y_765_, v___y_761_);
if (lean_obj_tag(v___x_772_) == 0)
{
lean_object* v_toCold_773_; lean_object* v_options_774_; uint8_t v_hasTrace_775_; 
v_toCold_773_ = lean_ctor_get(v___y_765_, 0);
v_options_774_ = lean_ctor_get(v_toCold_773_, 2);
v_hasTrace_775_ = lean_ctor_get_uint8(v_options_774_, sizeof(void*)*1);
if (v_hasTrace_775_ == 0)
{
lean_object* v_a_776_; 
v_a_776_ = lean_ctor_get(v___x_772_, 0);
lean_inc(v_a_776_);
lean_dec_ref_known(v___x_772_, 1);
v___y_686_ = v___y_762_;
v___y_687_ = v___y_755_;
v___y_688_ = v_a_770_;
v___y_689_ = v___y_763_;
v___y_690_ = v___y_768_;
v___y_691_ = v___y_757_;
v___y_692_ = v___y_758_;
v___y_693_ = v___y_759_;
v___y_694_ = v___x_771_;
v___y_695_ = v___y_760_;
v___y_696_ = v_a_776_;
v___y_697_ = v___y_764_;
v___y_698_ = v___y_756_;
v___y_699_ = v___y_765_;
v___y_700_ = v___y_761_;
goto v___jp_685_;
}
else
{
lean_object* v_a_777_; lean_object* v_inheritedTraceOptions_778_; lean_object* v___x_779_; lean_object* v___x_780_; uint8_t v___x_781_; 
v_a_777_ = lean_ctor_get(v___x_772_, 0);
lean_inc(v_a_777_);
lean_dec_ref_known(v___x_772_, 1);
v_inheritedTraceOptions_778_ = lean_ctor_get(v_toCold_773_, 11);
v___x_779_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__2));
v___x_780_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5);
v___x_781_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_778_, v_options_774_, v___x_780_);
if (v___x_781_ == 0)
{
v___y_686_ = v___y_762_;
v___y_687_ = v___y_755_;
v___y_688_ = v_a_770_;
v___y_689_ = v___y_763_;
v___y_690_ = v___y_768_;
v___y_691_ = v___y_757_;
v___y_692_ = v___y_758_;
v___y_693_ = v___y_759_;
v___y_694_ = v___x_771_;
v___y_695_ = v___y_760_;
v___y_696_ = v_a_777_;
v___y_697_ = v___y_764_;
v___y_698_ = v___y_756_;
v___y_699_ = v___y_765_;
v___y_700_ = v___y_761_;
goto v___jp_685_;
}
else
{
lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; 
v___x_782_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__11, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__11_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__11);
v___x_783_ = l_Lean_Expr_fvarId_x21(v_major_561_);
v___x_784_ = l_Lean_MessageData_ofName(v___x_783_);
v___x_785_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_785_, 0, v___x_782_);
lean_ctor_set(v___x_785_, 1, v___x_784_);
v___x_786_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1(v___x_779_, v___x_785_, v___y_764_, v___y_756_, v___y_765_, v___y_761_);
if (lean_obj_tag(v___x_786_) == 0)
{
lean_dec_ref_known(v___x_786_, 1);
v___y_686_ = v___y_762_;
v___y_687_ = v___y_755_;
v___y_688_ = v_a_770_;
v___y_689_ = v___y_763_;
v___y_690_ = v___y_768_;
v___y_691_ = v___y_757_;
v___y_692_ = v___y_758_;
v___y_693_ = v___y_759_;
v___y_694_ = v___x_771_;
v___y_695_ = v___y_760_;
v___y_696_ = v_a_777_;
v___y_697_ = v___y_764_;
v___y_698_ = v___y_756_;
v___y_699_ = v___y_765_;
v___y_700_ = v___y_761_;
goto v___jp_685_;
}
else
{
lean_object* v_a_787_; lean_object* v___x_789_; uint8_t v_isShared_790_; uint8_t v_isSharedCheck_794_; 
lean_dec(v_a_777_);
lean_dec_ref(v___x_771_);
lean_dec(v_a_770_);
lean_dec_ref(v___y_768_);
lean_dec(v___y_763_);
lean_dec(v___y_762_);
lean_dec(v___y_759_);
lean_dec(v___y_758_);
lean_dec_ref(v_subgoals_571_);
lean_dec(v_minorIdx_567_);
lean_dec(v_pos_566_);
lean_dec(v_baseSubst_563_);
lean_dec_ref(v_major_561_);
lean_dec(v_mvarId_557_);
v_a_787_ = lean_ctor_get(v___x_786_, 0);
v_isSharedCheck_794_ = !lean_is_exclusive(v___x_786_);
if (v_isSharedCheck_794_ == 0)
{
v___x_789_ = v___x_786_;
v_isShared_790_ = v_isSharedCheck_794_;
goto v_resetjp_788_;
}
else
{
lean_inc(v_a_787_);
lean_dec(v___x_786_);
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
else
{
lean_object* v_a_795_; lean_object* v___x_797_; uint8_t v_isShared_798_; uint8_t v_isSharedCheck_802_; 
lean_dec_ref(v___x_771_);
lean_dec(v_a_770_);
lean_dec_ref(v___y_768_);
lean_dec(v___y_763_);
lean_dec(v___y_762_);
lean_dec(v___y_759_);
lean_dec(v___y_758_);
lean_dec_ref(v_subgoals_571_);
lean_dec(v_minorIdx_567_);
lean_dec(v_pos_566_);
lean_dec(v_baseSubst_563_);
lean_dec_ref(v_major_561_);
lean_dec(v_mvarId_557_);
v_a_795_ = lean_ctor_get(v___x_772_, 0);
v_isSharedCheck_802_ = !lean_is_exclusive(v___x_772_);
if (v_isSharedCheck_802_ == 0)
{
v___x_797_ = v___x_772_;
v_isShared_798_ = v_isSharedCheck_802_;
goto v_resetjp_796_;
}
else
{
lean_inc(v_a_795_);
lean_dec(v___x_772_);
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
lean_object* v_a_803_; lean_object* v___x_805_; uint8_t v_isShared_806_; uint8_t v_isSharedCheck_810_; 
lean_dec_ref(v___y_768_);
lean_dec(v___y_763_);
lean_dec(v___y_762_);
lean_dec(v___y_759_);
lean_dec(v___y_758_);
lean_dec(v_a_753_);
lean_dec_ref(v_subgoals_571_);
lean_dec_ref(v_recursor_568_);
lean_dec(v_minorIdx_567_);
lean_dec(v_pos_566_);
lean_dec(v_baseSubst_563_);
lean_dec_ref(v_major_561_);
lean_dec(v_mvarId_557_);
v_a_803_ = lean_ctor_get(v___x_769_, 0);
v_isSharedCheck_810_ = !lean_is_exclusive(v___x_769_);
if (v_isSharedCheck_810_ == 0)
{
v___x_805_ = v___x_769_;
v_isShared_806_ = v_isSharedCheck_810_;
goto v_resetjp_804_;
}
else
{
lean_inc(v_a_803_);
lean_dec(v___x_769_);
v___x_805_ = lean_box(0);
v_isShared_806_ = v_isSharedCheck_810_;
goto v_resetjp_804_;
}
v_resetjp_804_:
{
lean_object* v___x_808_; 
if (v_isShared_806_ == 0)
{
v___x_808_ = v___x_805_;
goto v_reusejp_807_;
}
else
{
lean_object* v_reuseFailAlloc_809_; 
v_reuseFailAlloc_809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_809_, 0, v_a_803_);
v___x_808_ = v_reuseFailAlloc_809_;
goto v_reusejp_807_;
}
v_reusejp_807_:
{
return v___x_808_;
}
}
}
}
v___jp_811_:
{
lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; uint8_t v___x_828_; 
v___x_822_ = lean_nat_sub(v___y_817_, v_initialArity_564_);
lean_dec(v___y_817_);
v___x_823_ = lean_array_get_size(v_reverted_560_);
v___x_824_ = lean_array_get_size(v_indices_562_);
v___x_825_ = lean_nat_sub(v___x_823_, v___x_824_);
v___x_826_ = lean_nat_sub(v___x_825_, v___y_812_);
lean_dec(v___x_825_);
v___x_827_ = lean_array_get_size(v_givenNames_558_);
v___x_828_ = lean_nat_dec_lt(v_minorIdx_567_, v___x_827_);
if (v___x_828_ == 0)
{
lean_object* v___x_829_; lean_object* v___x_830_; 
v___x_829_ = lean_box(0);
v___x_830_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_830_, 0, v___x_829_);
lean_ctor_set_uint8(v___x_830_, sizeof(void*)*1, v___x_828_);
v___y_755_ = v___y_812_;
v___y_756_ = v___y_819_;
v___y_757_ = v___y_813_;
v___y_758_ = v___x_826_;
v___y_759_ = v___x_822_;
v___y_760_ = v___y_815_;
v___y_761_ = v___y_821_;
v___y_762_ = v___x_823_;
v___y_763_ = v___x_824_;
v___y_764_ = v___y_818_;
v___y_765_ = v___y_820_;
v___y_766_ = v___y_814_;
v___y_767_ = v___y_816_;
v___y_768_ = v___x_830_;
goto v___jp_754_;
}
else
{
lean_object* v___x_831_; 
v___x_831_ = lean_array_fget_borrowed(v_givenNames_558_, v_minorIdx_567_);
lean_inc(v___x_831_);
v___y_755_ = v___y_812_;
v___y_756_ = v___y_819_;
v___y_757_ = v___y_813_;
v___y_758_ = v___x_826_;
v___y_759_ = v___x_822_;
v___y_760_ = v___y_815_;
v___y_761_ = v___y_821_;
v___y_762_ = v___x_823_;
v___y_763_ = v___x_824_;
v___y_764_ = v___y_818_;
v___y_765_ = v___y_820_;
v___y_766_ = v___y_814_;
v___y_767_ = v___y_816_;
v___y_768_ = v___x_831_;
goto v___jp_754_;
}
}
v___jp_832_:
{
if (v___y_841_ == 0)
{
lean_object* v___x_842_; uint8_t v___x_843_; 
lean_inc_ref(v___y_835_);
v___x_842_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTargetArity(v___y_835_);
v___x_843_ = lean_nat_dec_lt(v___x_842_, v_initialArity_564_);
if (v___x_843_ == 0)
{
v___y_812_ = v___y_833_;
v___y_813_ = v___y_841_;
v___y_814_ = v___y_835_;
v___y_815_ = v___y_837_;
v___y_816_ = v___y_840_;
v___y_817_ = v___x_842_;
v___y_818_ = v___y_834_;
v___y_819_ = v___y_836_;
v___y_820_ = v___y_839_;
v___y_821_ = v___y_838_;
goto v___jp_811_;
}
else
{
lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; 
v___x_844_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1));
v___x_845_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9);
lean_inc(v_mvarId_557_);
v___x_846_ = l_Lean_Meta_throwTacticEx___redArg(v___x_844_, v_mvarId_557_, v___x_845_, v___y_834_, v___y_836_, v___y_839_, v___y_838_);
if (lean_obj_tag(v___x_846_) == 0)
{
lean_dec_ref_known(v___x_846_, 1);
v___y_812_ = v___y_833_;
v___y_813_ = v___y_841_;
v___y_814_ = v___y_835_;
v___y_815_ = v___y_837_;
v___y_816_ = v___y_840_;
v___y_817_ = v___x_842_;
v___y_818_ = v___y_834_;
v___y_819_ = v___y_836_;
v___y_820_ = v___y_839_;
v___y_821_ = v___y_838_;
goto v___jp_811_;
}
else
{
lean_object* v_a_847_; lean_object* v___x_849_; uint8_t v_isShared_850_; uint8_t v_isSharedCheck_854_; 
lean_dec(v___x_842_);
lean_dec(v___y_840_);
lean_dec_ref(v___y_835_);
lean_dec(v_a_753_);
lean_dec_ref(v_subgoals_571_);
lean_dec_ref(v_recursor_568_);
lean_dec(v_minorIdx_567_);
lean_dec(v_pos_566_);
lean_dec(v_baseSubst_563_);
lean_dec_ref(v_major_561_);
lean_dec(v_mvarId_557_);
v_a_847_ = lean_ctor_get(v___x_846_, 0);
v_isSharedCheck_854_ = !lean_is_exclusive(v___x_846_);
if (v_isSharedCheck_854_ == 0)
{
v___x_849_ = v___x_846_;
v_isShared_850_ = v_isSharedCheck_854_;
goto v_resetjp_848_;
}
else
{
lean_inc(v_a_847_);
lean_dec(v___x_846_);
v___x_849_ = lean_box(0);
v_isShared_850_ = v_isSharedCheck_854_;
goto v_resetjp_848_;
}
v_resetjp_848_:
{
lean_object* v___x_852_; 
if (v_isShared_850_ == 0)
{
v___x_852_ = v___x_849_;
goto v_reusejp_851_;
}
else
{
lean_object* v_reuseFailAlloc_853_; 
v_reuseFailAlloc_853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_853_, 0, v_a_847_);
v___x_852_ = v_reuseFailAlloc_853_;
goto v_reusejp_851_;
}
v_reusejp_851_:
{
return v___x_852_;
}
}
}
}
}
else
{
lean_object* v___x_855_; lean_object* v___x_856_; 
v___x_855_ = lean_box(0);
lean_inc_ref(v___y_835_);
v___x_856_ = l_Lean_Meta_synthInstance_x3f(v___y_835_, v___x_855_, v___y_834_, v___y_836_, v___y_839_, v___y_838_);
if (lean_obj_tag(v___x_856_) == 0)
{
lean_object* v_a_857_; 
v_a_857_ = lean_ctor_get(v___x_856_, 0);
lean_inc(v_a_857_);
lean_dec_ref_known(v___x_856_, 1);
if (lean_obj_tag(v_a_857_) == 0)
{
lean_object* v___x_858_; 
v___x_858_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___y_835_, v___y_840_, v___y_834_, v___y_836_, v___y_839_, v___y_838_);
if (lean_obj_tag(v___x_858_) == 0)
{
lean_object* v_a_859_; lean_object* v___x_860_; lean_object* v___x_861_; 
v_a_859_ = lean_ctor_get(v___x_858_, 0);
lean_inc_n(v_a_859_, 2);
lean_dec_ref_known(v___x_858_, 1);
v___x_860_ = l_Lean_Expr_app___override(v_recursor_568_, v_a_859_);
lean_inc(v_mvarId_557_);
v___x_861_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTypeBody(v_mvarId_557_, v_a_753_, v_a_859_, v___y_834_, v___y_836_, v___y_839_, v___y_838_);
if (lean_obj_tag(v___x_861_) == 0)
{
lean_object* v_a_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; 
v_a_862_ = lean_ctor_get(v___x_861_, 0);
lean_inc(v_a_862_);
lean_dec_ref_known(v___x_861_, 1);
v___x_863_ = lean_nat_add(v_pos_566_, v___y_833_);
lean_dec(v_pos_566_);
v___x_864_ = lean_nat_add(v_minorIdx_567_, v___y_833_);
lean_dec(v_minorIdx_567_);
v___x_865_ = l_Lean_Expr_mvarId_x21(v_a_859_);
lean_dec(v_a_859_);
v___x_866_ = ((lean_object*)(l_Lean_Meta_instInhabitedInductionSubgoal_default___closed__0));
v___x_867_ = lean_box(0);
v___x_868_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_868_, 0, v___x_865_);
lean_ctor_set(v___x_868_, 1, v___x_866_);
lean_ctor_set(v___x_868_, 2, v___x_867_);
v___x_869_ = lean_array_push(v_subgoals_571_, v___x_868_);
v_pos_566_ = v___x_863_;
v_minorIdx_567_ = v___x_864_;
v_recursor_568_ = v___x_860_;
v_recursorType_569_ = v_a_862_;
v_subgoals_571_ = v___x_869_;
v_a_572_ = v___y_834_;
v_a_573_ = v___y_836_;
v_a_574_ = v___y_839_;
v_a_575_ = v___y_838_;
goto _start;
}
else
{
lean_object* v_a_871_; lean_object* v___x_873_; uint8_t v_isShared_874_; uint8_t v_isSharedCheck_878_; 
lean_dec_ref(v___x_860_);
lean_dec(v_a_859_);
lean_dec_ref(v_subgoals_571_);
lean_dec(v_minorIdx_567_);
lean_dec(v_pos_566_);
lean_dec(v_baseSubst_563_);
lean_dec_ref(v_major_561_);
lean_dec(v_mvarId_557_);
v_a_871_ = lean_ctor_get(v___x_861_, 0);
v_isSharedCheck_878_ = !lean_is_exclusive(v___x_861_);
if (v_isSharedCheck_878_ == 0)
{
v___x_873_ = v___x_861_;
v_isShared_874_ = v_isSharedCheck_878_;
goto v_resetjp_872_;
}
else
{
lean_inc(v_a_871_);
lean_dec(v___x_861_);
v___x_873_ = lean_box(0);
v_isShared_874_ = v_isSharedCheck_878_;
goto v_resetjp_872_;
}
v_resetjp_872_:
{
lean_object* v___x_876_; 
if (v_isShared_874_ == 0)
{
v___x_876_ = v___x_873_;
goto v_reusejp_875_;
}
else
{
lean_object* v_reuseFailAlloc_877_; 
v_reuseFailAlloc_877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_877_, 0, v_a_871_);
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
lean_dec(v_a_753_);
lean_dec_ref(v_subgoals_571_);
lean_dec_ref(v_recursor_568_);
lean_dec(v_minorIdx_567_);
lean_dec(v_pos_566_);
lean_dec(v_baseSubst_563_);
lean_dec_ref(v_major_561_);
lean_dec(v_mvarId_557_);
v_a_879_ = lean_ctor_get(v___x_858_, 0);
v_isSharedCheck_886_ = !lean_is_exclusive(v___x_858_);
if (v_isSharedCheck_886_ == 0)
{
v___x_881_ = v___x_858_;
v_isShared_882_ = v_isSharedCheck_886_;
goto v_resetjp_880_;
}
else
{
lean_inc(v_a_879_);
lean_dec(v___x_858_);
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
else
{
lean_object* v_val_887_; lean_object* v___x_888_; lean_object* v___x_889_; 
lean_dec(v___y_840_);
lean_dec_ref(v___y_835_);
v_val_887_ = lean_ctor_get(v_a_857_, 0);
lean_inc_n(v_val_887_, 2);
lean_dec_ref_known(v_a_857_, 1);
v___x_888_ = l_Lean_Expr_app___override(v_recursor_568_, v_val_887_);
lean_inc(v_mvarId_557_);
v___x_889_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTypeBody(v_mvarId_557_, v_a_753_, v_val_887_, v___y_834_, v___y_836_, v___y_839_, v___y_838_);
lean_dec(v_val_887_);
if (lean_obj_tag(v___x_889_) == 0)
{
lean_object* v_a_890_; lean_object* v___x_891_; lean_object* v___x_892_; 
v_a_890_ = lean_ctor_get(v___x_889_, 0);
lean_inc(v_a_890_);
lean_dec_ref_known(v___x_889_, 1);
v___x_891_ = lean_nat_add(v_pos_566_, v___y_833_);
lean_dec(v_pos_566_);
v___x_892_ = lean_nat_add(v_minorIdx_567_, v___y_833_);
lean_dec(v_minorIdx_567_);
v_pos_566_ = v___x_891_;
v_minorIdx_567_ = v___x_892_;
v_recursor_568_ = v___x_888_;
v_recursorType_569_ = v_a_890_;
v_a_572_ = v___y_834_;
v_a_573_ = v___y_836_;
v_a_574_ = v___y_839_;
v_a_575_ = v___y_838_;
goto _start;
}
else
{
lean_object* v_a_894_; lean_object* v___x_896_; uint8_t v_isShared_897_; uint8_t v_isSharedCheck_901_; 
lean_dec_ref(v___x_888_);
lean_dec_ref(v_subgoals_571_);
lean_dec(v_minorIdx_567_);
lean_dec(v_pos_566_);
lean_dec(v_baseSubst_563_);
lean_dec_ref(v_major_561_);
lean_dec(v_mvarId_557_);
v_a_894_ = lean_ctor_get(v___x_889_, 0);
v_isSharedCheck_901_ = !lean_is_exclusive(v___x_889_);
if (v_isSharedCheck_901_ == 0)
{
v___x_896_ = v___x_889_;
v_isShared_897_ = v_isSharedCheck_901_;
goto v_resetjp_895_;
}
else
{
lean_inc(v_a_894_);
lean_dec(v___x_889_);
v___x_896_ = lean_box(0);
v_isShared_897_ = v_isSharedCheck_901_;
goto v_resetjp_895_;
}
v_resetjp_895_:
{
lean_object* v___x_899_; 
if (v_isShared_897_ == 0)
{
v___x_899_ = v___x_896_;
goto v_reusejp_898_;
}
else
{
lean_object* v_reuseFailAlloc_900_; 
v_reuseFailAlloc_900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_900_, 0, v_a_894_);
v___x_899_ = v_reuseFailAlloc_900_;
goto v_reusejp_898_;
}
v_reusejp_898_:
{
return v___x_899_;
}
}
}
}
}
else
{
lean_object* v_a_902_; lean_object* v___x_904_; uint8_t v_isShared_905_; uint8_t v_isSharedCheck_909_; 
lean_dec(v___y_840_);
lean_dec_ref(v___y_835_);
lean_dec(v_a_753_);
lean_dec_ref(v_subgoals_571_);
lean_dec_ref(v_recursor_568_);
lean_dec(v_minorIdx_567_);
lean_dec(v_pos_566_);
lean_dec(v_baseSubst_563_);
lean_dec_ref(v_major_561_);
lean_dec(v_mvarId_557_);
v_a_902_ = lean_ctor_get(v___x_856_, 0);
v_isSharedCheck_909_ = !lean_is_exclusive(v___x_856_);
if (v_isSharedCheck_909_ == 0)
{
v___x_904_ = v___x_856_;
v_isShared_905_ = v_isSharedCheck_909_;
goto v_resetjp_903_;
}
else
{
lean_inc(v_a_902_);
lean_dec(v___x_856_);
v___x_904_ = lean_box(0);
v_isShared_905_ = v_isSharedCheck_909_;
goto v_resetjp_903_;
}
v_resetjp_903_:
{
lean_object* v___x_907_; 
if (v_isShared_905_ == 0)
{
v___x_907_ = v___x_904_;
goto v_reusejp_906_;
}
else
{
lean_object* v_reuseFailAlloc_908_; 
v_reuseFailAlloc_908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_908_, 0, v_a_902_);
v___x_907_ = v_reuseFailAlloc_908_;
goto v_reusejp_906_;
}
v_reusejp_906_:
{
return v___x_907_;
}
}
}
}
}
v___jp_910_:
{
uint8_t v___x_920_; 
v___x_920_ = l_Lean_BinderInfo_isInstImplicit(v___y_918_);
if (v___x_920_ == 0)
{
v___y_833_ = v___y_911_;
v___y_834_ = v___y_912_;
v___y_835_ = v___y_913_;
v___y_836_ = v___y_914_;
v___y_837_ = v___y_915_;
v___y_838_ = v___y_917_;
v___y_839_ = v___y_916_;
v___y_840_ = v___y_919_;
v___y_841_ = v___x_920_;
goto v___jp_832_;
}
else
{
lean_object* v___x_921_; lean_object* v___x_922_; uint8_t v___x_923_; 
v___x_921_ = lean_array_get_size(v_givenNames_558_);
v___x_922_ = lean_unsigned_to_nat(0u);
v___x_923_ = lean_nat_dec_eq(v___x_921_, v___x_922_);
v___y_833_ = v___y_911_;
v___y_834_ = v___y_912_;
v___y_835_ = v___y_913_;
v___y_836_ = v___y_914_;
v___y_837_ = v___y_915_;
v___y_838_ = v___y_917_;
v___y_839_ = v___y_916_;
v___y_840_ = v___y_919_;
v___y_841_ = v___x_923_;
goto v___jp_832_;
}
}
v___jp_924_:
{
if (lean_obj_tag(v_a_753_) == 7)
{
lean_object* v_binderName_931_; lean_object* v_binderType_932_; uint8_t v_binderInfo_933_; lean_object* v___x_934_; lean_object* v___x_935_; uint8_t v___x_936_; 
v_binderName_931_ = lean_ctor_get(v_a_753_, 0);
v_binderType_932_ = lean_ctor_get(v_a_753_, 1);
v_binderInfo_933_ = lean_ctor_get_uint8(v_a_753_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_932_);
v___x_934_ = l_Lean_Expr_headBeta(v_binderType_932_);
v___x_935_ = lean_unsigned_to_nat(1u);
v___x_936_ = lean_nat_dec_eq(v_numMinors_565_, v___x_935_);
if (v___x_936_ == 0)
{
lean_object* v___x_937_; lean_object* v___x_938_; 
v___x_937_ = l_Lean_Name_eraseMacroScopes(v_binderName_931_);
v___x_938_ = l_Lean_Name_append(v___y_926_, v___x_937_);
v___y_911_ = v___x_935_;
v___y_912_ = v___y_927_;
v___y_913_ = v___x_934_;
v___y_914_ = v___y_928_;
v___y_915_ = v___y_925_;
v___y_916_ = v___y_929_;
v___y_917_ = v___y_930_;
v___y_918_ = v_binderInfo_933_;
v___y_919_ = v___x_938_;
goto v___jp_910_;
}
else
{
v___y_911_ = v___x_935_;
v___y_912_ = v___y_927_;
v___y_913_ = v___x_934_;
v___y_914_ = v___y_928_;
v___y_915_ = v___y_925_;
v___y_916_ = v___y_929_;
v___y_917_ = v___y_930_;
v___y_918_ = v_binderInfo_933_;
v___y_919_ = v___y_926_;
goto v___jp_910_;
}
}
else
{
lean_object* v___x_939_; lean_object* v___x_940_; 
lean_dec(v___y_926_);
lean_dec(v_a_753_);
lean_dec_ref(v_subgoals_571_);
lean_dec_ref(v_recursor_568_);
lean_dec(v_minorIdx_567_);
lean_dec(v_pos_566_);
lean_dec(v_baseSubst_563_);
lean_dec_ref(v_major_561_);
lean_dec(v_mvarId_557_);
v___x_939_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__15, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__15_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__15);
v___x_940_ = l_panic___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__4(v___x_939_, v___y_927_, v___y_928_, v___y_929_, v___y_930_);
return v___x_940_;
}
}
v___jp_941_:
{
if (v___y_942_ == 0)
{
lean_dec(v_a_753_);
lean_dec(v_minorIdx_567_);
lean_dec(v_pos_566_);
lean_dec(v_baseSubst_563_);
lean_dec_ref(v_major_561_);
if (v_consumedMajor_570_ == 0)
{
lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; 
v___x_943_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1));
v___x_944_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9);
lean_inc(v_mvarId_557_);
v___x_945_ = l_Lean_Meta_throwTacticEx___redArg(v___x_943_, v_mvarId_557_, v___x_944_, v_a_572_, v_a_573_, v_a_574_, v_a_575_);
if (lean_obj_tag(v___x_945_) == 0)
{
lean_dec_ref_known(v___x_945_, 1);
v___y_578_ = v_a_572_;
v___y_579_ = v_a_573_;
v___y_580_ = v_a_574_;
v___y_581_ = v_a_575_;
goto v___jp_577_;
}
else
{
lean_object* v_a_946_; lean_object* v___x_948_; uint8_t v_isShared_949_; uint8_t v_isSharedCheck_953_; 
lean_dec_ref(v_subgoals_571_);
lean_dec_ref(v_recursor_568_);
lean_dec(v_mvarId_557_);
v_a_946_ = lean_ctor_get(v___x_945_, 0);
v_isSharedCheck_953_ = !lean_is_exclusive(v___x_945_);
if (v_isSharedCheck_953_ == 0)
{
v___x_948_ = v___x_945_;
v_isShared_949_ = v_isSharedCheck_953_;
goto v_resetjp_947_;
}
else
{
lean_inc(v_a_946_);
lean_dec(v___x_945_);
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
else
{
v___y_578_ = v_a_572_;
v___y_579_ = v_a_573_;
v___y_580_ = v_a_574_;
v___y_581_ = v_a_575_;
goto v___jp_577_;
}
}
else
{
lean_object* v___x_954_; uint8_t v___x_955_; 
v___x_954_ = l_Lean_Meta_RecursorInfo_firstIndexPos(v_recursorInfo_559_);
v___x_955_ = lean_nat_dec_eq(v_pos_566_, v___x_954_);
lean_dec(v___x_954_);
if (v___x_955_ == 0)
{
lean_object* v___x_956_; 
lean_inc(v_mvarId_557_);
v___x_956_ = l_Lean_MVarId_getTag(v_mvarId_557_, v_a_572_, v_a_573_, v_a_574_, v_a_575_);
if (lean_obj_tag(v___x_956_) == 0)
{
lean_object* v_a_957_; uint8_t v___x_958_; 
v_a_957_ = lean_ctor_get(v___x_956_, 0);
lean_inc(v_a_957_);
lean_dec_ref_known(v___x_956_, 1);
v___x_958_ = lean_nat_dec_le(v_numMinors_565_, v_minorIdx_567_);
if (v___x_958_ == 0)
{
v___y_925_ = v___y_942_;
v___y_926_ = v_a_957_;
v___y_927_ = v_a_572_;
v___y_928_ = v_a_573_;
v___y_929_ = v_a_574_;
v___y_930_ = v_a_575_;
goto v___jp_924_;
}
else
{
lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; 
v___x_959_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1));
v___x_960_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9);
lean_inc(v_mvarId_557_);
v___x_961_ = l_Lean_Meta_throwTacticEx___redArg(v___x_959_, v_mvarId_557_, v___x_960_, v_a_572_, v_a_573_, v_a_574_, v_a_575_);
if (lean_obj_tag(v___x_961_) == 0)
{
lean_dec_ref_known(v___x_961_, 1);
v___y_925_ = v___y_942_;
v___y_926_ = v_a_957_;
v___y_927_ = v_a_572_;
v___y_928_ = v_a_573_;
v___y_929_ = v_a_574_;
v___y_930_ = v_a_575_;
goto v___jp_924_;
}
else
{
lean_object* v_a_962_; lean_object* v___x_964_; uint8_t v_isShared_965_; uint8_t v_isSharedCheck_969_; 
lean_dec(v_a_957_);
lean_dec(v_a_753_);
lean_dec_ref(v_subgoals_571_);
lean_dec_ref(v_recursor_568_);
lean_dec(v_minorIdx_567_);
lean_dec(v_pos_566_);
lean_dec(v_baseSubst_563_);
lean_dec_ref(v_major_561_);
lean_dec(v_mvarId_557_);
v_a_962_ = lean_ctor_get(v___x_961_, 0);
v_isSharedCheck_969_ = !lean_is_exclusive(v___x_961_);
if (v_isSharedCheck_969_ == 0)
{
v___x_964_ = v___x_961_;
v_isShared_965_ = v_isSharedCheck_969_;
goto v_resetjp_963_;
}
else
{
lean_inc(v_a_962_);
lean_dec(v___x_961_);
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
}
else
{
lean_object* v_a_970_; lean_object* v___x_972_; uint8_t v_isShared_973_; uint8_t v_isSharedCheck_977_; 
lean_dec(v_a_753_);
lean_dec_ref(v_subgoals_571_);
lean_dec_ref(v_recursor_568_);
lean_dec(v_minorIdx_567_);
lean_dec(v_pos_566_);
lean_dec(v_baseSubst_563_);
lean_dec_ref(v_major_561_);
lean_dec(v_mvarId_557_);
v_a_970_ = lean_ctor_get(v___x_956_, 0);
v_isSharedCheck_977_ = !lean_is_exclusive(v___x_956_);
if (v_isSharedCheck_977_ == 0)
{
v___x_972_ = v___x_956_;
v_isShared_973_ = v_isSharedCheck_977_;
goto v_resetjp_971_;
}
else
{
lean_inc(v_a_970_);
lean_dec(v___x_956_);
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
}
else
{
lean_object* v___x_978_; lean_object* v___x_979_; uint8_t v___x_980_; 
v___x_978_ = lean_unsigned_to_nat(0u);
v___x_979_ = lean_array_get_size(v_indices_562_);
v___x_980_ = lean_nat_dec_lt(v___x_978_, v___x_979_);
if (v___x_980_ == 0)
{
v___y_718_ = v___x_955_;
v___y_719_ = v___x_979_;
v_fst_720_ = v_recursor_568_;
v_snd_721_ = v_a_753_;
goto v___jp_717_;
}
else
{
lean_object* v___x_981_; uint8_t v___x_982_; 
lean_inc(v_a_753_);
lean_inc_ref(v_recursor_568_);
v___x_981_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_981_, 0, v_recursor_568_);
lean_ctor_set(v___x_981_, 1, v_a_753_);
v___x_982_ = lean_nat_dec_le(v___x_979_, v___x_979_);
if (v___x_982_ == 0)
{
if (v___x_980_ == 0)
{
lean_dec_ref_known(v___x_981_, 2);
v___y_718_ = v___x_955_;
v___y_719_ = v___x_979_;
v_fst_720_ = v_recursor_568_;
v_snd_721_ = v_a_753_;
goto v___jp_717_;
}
else
{
size_t v___x_983_; size_t v___x_984_; lean_object* v___x_985_; 
lean_dec(v_a_753_);
lean_dec_ref(v_recursor_568_);
v___x_983_ = ((size_t)0ULL);
v___x_984_ = lean_usize_of_nat(v___x_979_);
lean_inc(v_mvarId_557_);
v___x_985_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__5(v_mvarId_557_, v_indices_562_, v___x_983_, v___x_984_, v___x_981_, v_a_572_, v_a_573_, v_a_574_, v_a_575_);
v___y_738_ = v___x_955_;
v___y_739_ = v___x_979_;
v___y_740_ = v___x_985_;
goto v___jp_737_;
}
}
else
{
size_t v___x_986_; size_t v___x_987_; lean_object* v___x_988_; 
lean_dec(v_a_753_);
lean_dec_ref(v_recursor_568_);
v___x_986_ = ((size_t)0ULL);
v___x_987_ = lean_usize_of_nat(v___x_979_);
lean_inc(v_mvarId_557_);
v___x_988_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__5(v_mvarId_557_, v_indices_562_, v___x_986_, v___x_987_, v___x_981_, v_a_572_, v_a_573_, v_a_574_, v_a_575_);
v___y_738_ = v___x_955_;
v___y_739_ = v___x_979_;
v___y_740_ = v___x_988_;
goto v___jp_737_;
}
}
}
}
}
}
else
{
lean_object* v_a_992_; lean_object* v___x_994_; uint8_t v_isShared_995_; uint8_t v_isSharedCheck_999_; 
lean_dec_ref(v_subgoals_571_);
lean_dec_ref(v_recursor_568_);
lean_dec(v_minorIdx_567_);
lean_dec(v_pos_566_);
lean_dec(v_baseSubst_563_);
lean_dec_ref(v_major_561_);
lean_dec(v_mvarId_557_);
v_a_992_ = lean_ctor_get(v___x_752_, 0);
v_isSharedCheck_999_ = !lean_is_exclusive(v___x_752_);
if (v_isSharedCheck_999_ == 0)
{
v___x_994_ = v___x_752_;
v_isShared_995_ = v_isSharedCheck_999_;
goto v_resetjp_993_;
}
else
{
lean_inc(v_a_992_);
lean_dec(v___x_752_);
v___x_994_ = lean_box(0);
v_isShared_995_ = v_isSharedCheck_999_;
goto v_resetjp_993_;
}
v_resetjp_993_:
{
lean_object* v___x_997_; 
if (v_isShared_995_ == 0)
{
v___x_997_ = v___x_994_;
goto v_reusejp_996_;
}
else
{
lean_object* v_reuseFailAlloc_998_; 
v_reuseFailAlloc_998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_998_, 0, v_a_992_);
v___x_997_ = v_reuseFailAlloc_998_;
goto v_reusejp_996_;
}
v_reusejp_996_:
{
return v___x_997_;
}
}
}
v___jp_577_:
{
lean_object* v___x_582_; 
v___x_582_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0___redArg(v_mvarId_557_, v_recursor_568_, v___y_579_);
if (lean_obj_tag(v___x_582_) == 0)
{
lean_object* v___x_584_; uint8_t v_isShared_585_; uint8_t v_isSharedCheck_624_; 
v_isSharedCheck_624_ = !lean_is_exclusive(v___x_582_);
if (v_isSharedCheck_624_ == 0)
{
lean_object* v_unused_625_; 
v_unused_625_ = lean_ctor_get(v___x_582_, 0);
lean_dec(v_unused_625_);
v___x_584_ = v___x_582_;
v_isShared_585_ = v_isSharedCheck_624_;
goto v_resetjp_583_;
}
else
{
lean_dec(v___x_582_);
v___x_584_ = lean_box(0);
v_isShared_585_ = v_isSharedCheck_624_;
goto v_resetjp_583_;
}
v_resetjp_583_:
{
lean_object* v_toCold_586_; lean_object* v_options_587_; uint8_t v_hasTrace_588_; 
v_toCold_586_ = lean_ctor_get(v___y_580_, 0);
v_options_587_ = lean_ctor_get(v_toCold_586_, 2);
v_hasTrace_588_ = lean_ctor_get_uint8(v_options_587_, sizeof(void*)*1);
if (v_hasTrace_588_ == 0)
{
lean_object* v___x_590_; 
if (v_isShared_585_ == 0)
{
lean_ctor_set(v___x_584_, 0, v_subgoals_571_);
v___x_590_ = v___x_584_;
goto v_reusejp_589_;
}
else
{
lean_object* v_reuseFailAlloc_591_; 
v_reuseFailAlloc_591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_591_, 0, v_subgoals_571_);
v___x_590_ = v_reuseFailAlloc_591_;
goto v_reusejp_589_;
}
v_reusejp_589_:
{
return v___x_590_;
}
}
else
{
lean_object* v_inheritedTraceOptions_592_; lean_object* v___x_593_; lean_object* v___x_594_; uint8_t v___x_595_; 
v_inheritedTraceOptions_592_ = lean_ctor_get(v_toCold_586_, 11);
v___x_593_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__2));
v___x_594_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5);
v___x_595_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_592_, v_options_587_, v___x_594_);
if (v___x_595_ == 0)
{
lean_object* v___x_597_; 
if (v_isShared_585_ == 0)
{
lean_ctor_set(v___x_584_, 0, v_subgoals_571_);
v___x_597_ = v___x_584_;
goto v_reusejp_596_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v_subgoals_571_);
v___x_597_ = v_reuseFailAlloc_598_;
goto v_reusejp_596_;
}
v_reusejp_596_:
{
return v___x_597_;
}
}
else
{
lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; 
lean_del_object(v___x_584_);
v___x_599_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__7, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__7_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__7);
v___x_600_ = lean_array_get_size(v_subgoals_571_);
v___x_601_ = l_Nat_reprFast(v___x_600_);
v___x_602_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_602_, 0, v___x_601_);
v___x_603_ = l_Lean_MessageData_ofFormat(v___x_602_);
v___x_604_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_604_, 0, v___x_599_);
lean_ctor_set(v___x_604_, 1, v___x_603_);
v___x_605_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__9, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__9_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__9);
v___x_606_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_606_, 0, v___x_604_);
lean_ctor_set(v___x_606_, 1, v___x_605_);
v___x_607_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1(v___x_593_, v___x_606_, v___y_578_, v___y_579_, v___y_580_, v___y_581_);
if (lean_obj_tag(v___x_607_) == 0)
{
lean_object* v___x_609_; uint8_t v_isShared_610_; uint8_t v_isSharedCheck_614_; 
v_isSharedCheck_614_ = !lean_is_exclusive(v___x_607_);
if (v_isSharedCheck_614_ == 0)
{
lean_object* v_unused_615_; 
v_unused_615_ = lean_ctor_get(v___x_607_, 0);
lean_dec(v_unused_615_);
v___x_609_ = v___x_607_;
v_isShared_610_ = v_isSharedCheck_614_;
goto v_resetjp_608_;
}
else
{
lean_dec(v___x_607_);
v___x_609_ = lean_box(0);
v_isShared_610_ = v_isSharedCheck_614_;
goto v_resetjp_608_;
}
v_resetjp_608_:
{
lean_object* v___x_612_; 
if (v_isShared_610_ == 0)
{
lean_ctor_set(v___x_609_, 0, v_subgoals_571_);
v___x_612_ = v___x_609_;
goto v_reusejp_611_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v_subgoals_571_);
v___x_612_ = v_reuseFailAlloc_613_;
goto v_reusejp_611_;
}
v_reusejp_611_:
{
return v___x_612_;
}
}
}
else
{
lean_object* v_a_616_; lean_object* v___x_618_; uint8_t v_isShared_619_; uint8_t v_isSharedCheck_623_; 
lean_dec_ref(v_subgoals_571_);
v_a_616_ = lean_ctor_get(v___x_607_, 0);
v_isSharedCheck_623_ = !lean_is_exclusive(v___x_607_);
if (v_isSharedCheck_623_ == 0)
{
v___x_618_ = v___x_607_;
v_isShared_619_ = v_isSharedCheck_623_;
goto v_resetjp_617_;
}
else
{
lean_inc(v_a_616_);
lean_dec(v___x_607_);
v___x_618_ = lean_box(0);
v_isShared_619_ = v_isSharedCheck_623_;
goto v_resetjp_617_;
}
v_resetjp_617_:
{
lean_object* v___x_621_; 
if (v_isShared_619_ == 0)
{
v___x_621_ = v___x_618_;
goto v_reusejp_620_;
}
else
{
lean_object* v_reuseFailAlloc_622_; 
v_reuseFailAlloc_622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_622_, 0, v_a_616_);
v___x_621_ = v_reuseFailAlloc_622_;
goto v_reusejp_620_;
}
v_reusejp_620_:
{
return v___x_621_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_626_; lean_object* v___x_628_; uint8_t v_isShared_629_; uint8_t v_isSharedCheck_633_; 
lean_dec_ref(v_subgoals_571_);
v_a_626_ = lean_ctor_get(v___x_582_, 0);
v_isSharedCheck_633_ = !lean_is_exclusive(v___x_582_);
if (v_isSharedCheck_633_ == 0)
{
v___x_628_ = v___x_582_;
v_isShared_629_ = v_isSharedCheck_633_;
goto v_resetjp_627_;
}
else
{
lean_inc(v_a_626_);
lean_dec(v___x_582_);
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
v___jp_634_:
{
lean_object* v___x_651_; 
v___x_651_ = l_Lean_Meta_introNCore(v___y_647_, v___y_638_, v___y_649_, v___y_650_, v___y_637_, v___y_641_, v___y_636_, v___y_642_, v___y_645_);
if (lean_obj_tag(v___x_651_) == 0)
{
lean_object* v_a_652_; lean_object* v_fst_653_; lean_object* v_snd_654_; lean_object* v___x_655_; lean_object* v___x_656_; 
v_a_652_ = lean_ctor_get(v___x_651_, 0);
lean_inc(v_a_652_);
lean_dec_ref_known(v___x_651_, 1);
v_fst_653_ = lean_ctor_get(v_a_652_, 0);
lean_inc(v_fst_653_);
v_snd_654_ = lean_ctor_get(v_a_652_, 1);
lean_inc(v_snd_654_);
lean_dec(v_a_652_);
v___x_655_ = lean_box(0);
v___x_656_ = l_Lean_Meta_introNCore(v_snd_654_, v___y_639_, v___x_655_, v___y_637_, v___y_640_, v___y_641_, v___y_636_, v___y_642_, v___y_645_);
if (lean_obj_tag(v___x_656_) == 0)
{
lean_object* v_a_657_; lean_object* v_fst_658_; lean_object* v_snd_659_; lean_object* v___x_660_; size_t v_sz_661_; size_t v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; 
v_a_657_ = lean_ctor_get(v___x_656_, 0);
lean_inc(v_a_657_);
lean_dec_ref_known(v___x_656_, 1);
v_fst_658_ = lean_ctor_get(v_a_657_, 0);
lean_inc(v_fst_658_);
v_snd_659_ = lean_ctor_get(v_a_657_, 1);
lean_inc(v_snd_659_);
lean_dec(v_a_657_);
lean_inc(v_baseSubst_563_);
lean_inc(v___y_644_);
v___x_660_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__2___redArg(v___y_646_, v_reverted_560_, v_fst_658_, v___y_644_, v___y_644_, v_baseSubst_563_);
lean_dec(v___y_644_);
lean_dec(v_fst_658_);
lean_dec(v___y_646_);
v_sz_661_ = lean_array_size(v_fst_653_);
v___x_662_ = ((size_t)0ULL);
v___x_663_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__3(v_sz_661_, v___x_662_, v_fst_653_);
v___x_664_ = lean_nat_add(v_pos_566_, v___y_635_);
lean_dec(v_pos_566_);
v___x_665_ = lean_nat_add(v_minorIdx_567_, v___y_635_);
lean_dec(v_minorIdx_567_);
v___x_666_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_666_, 0, v_snd_659_);
lean_ctor_set(v___x_666_, 1, v___x_663_);
lean_ctor_set(v___x_666_, 2, v___x_660_);
v___x_667_ = lean_array_push(v_subgoals_571_, v___x_666_);
v_pos_566_ = v___x_664_;
v_minorIdx_567_ = v___x_665_;
v_recursor_568_ = v___y_648_;
v_recursorType_569_ = v___y_643_;
v_subgoals_571_ = v___x_667_;
v_a_572_ = v___y_641_;
v_a_573_ = v___y_636_;
v_a_574_ = v___y_642_;
v_a_575_ = v___y_645_;
goto _start;
}
else
{
lean_object* v_a_669_; lean_object* v___x_671_; uint8_t v_isShared_672_; uint8_t v_isSharedCheck_676_; 
lean_dec(v_fst_653_);
lean_dec_ref(v___y_648_);
lean_dec(v___y_646_);
lean_dec(v___y_644_);
lean_dec_ref(v___y_643_);
lean_dec_ref(v_subgoals_571_);
lean_dec(v_minorIdx_567_);
lean_dec(v_pos_566_);
lean_dec(v_baseSubst_563_);
lean_dec_ref(v_major_561_);
lean_dec(v_mvarId_557_);
v_a_669_ = lean_ctor_get(v___x_656_, 0);
v_isSharedCheck_676_ = !lean_is_exclusive(v___x_656_);
if (v_isSharedCheck_676_ == 0)
{
v___x_671_ = v___x_656_;
v_isShared_672_ = v_isSharedCheck_676_;
goto v_resetjp_670_;
}
else
{
lean_inc(v_a_669_);
lean_dec(v___x_656_);
v___x_671_ = lean_box(0);
v_isShared_672_ = v_isSharedCheck_676_;
goto v_resetjp_670_;
}
v_resetjp_670_:
{
lean_object* v___x_674_; 
if (v_isShared_672_ == 0)
{
v___x_674_ = v___x_671_;
goto v_reusejp_673_;
}
else
{
lean_object* v_reuseFailAlloc_675_; 
v_reuseFailAlloc_675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_675_, 0, v_a_669_);
v___x_674_ = v_reuseFailAlloc_675_;
goto v_reusejp_673_;
}
v_reusejp_673_:
{
return v___x_674_;
}
}
}
}
else
{
lean_object* v_a_677_; lean_object* v___x_679_; uint8_t v_isShared_680_; uint8_t v_isSharedCheck_684_; 
lean_dec_ref(v___y_648_);
lean_dec(v___y_646_);
lean_dec(v___y_644_);
lean_dec_ref(v___y_643_);
lean_dec(v___y_639_);
lean_dec_ref(v_subgoals_571_);
lean_dec(v_minorIdx_567_);
lean_dec(v_pos_566_);
lean_dec(v_baseSubst_563_);
lean_dec_ref(v_major_561_);
lean_dec(v_mvarId_557_);
v_a_677_ = lean_ctor_get(v___x_651_, 0);
v_isSharedCheck_684_ = !lean_is_exclusive(v___x_651_);
if (v_isSharedCheck_684_ == 0)
{
v___x_679_ = v___x_651_;
v_isShared_680_ = v_isSharedCheck_684_;
goto v_resetjp_678_;
}
else
{
lean_inc(v_a_677_);
lean_dec(v___x_651_);
v___x_679_ = lean_box(0);
v_isShared_680_ = v_isSharedCheck_684_;
goto v_resetjp_678_;
}
v_resetjp_678_:
{
lean_object* v___x_682_; 
if (v_isShared_680_ == 0)
{
v___x_682_ = v___x_679_;
goto v_reusejp_681_;
}
else
{
lean_object* v_reuseFailAlloc_683_; 
v_reuseFailAlloc_683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_683_, 0, v_a_677_);
v___x_682_ = v_reuseFailAlloc_683_;
goto v_reusejp_681_;
}
v_reusejp_681_:
{
return v___x_682_;
}
}
}
}
v___jp_685_:
{
lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; 
v___x_701_ = l_Lean_Expr_mvarId_x21(v___y_688_);
lean_dec_ref(v___y_688_);
v___x_702_ = l_Lean_Expr_fvarId_x21(v_major_561_);
v___x_703_ = l_Lean_MVarId_tryClear(v___x_701_, v___x_702_, v___y_697_, v___y_698_, v___y_699_, v___y_700_);
if (lean_obj_tag(v___x_703_) == 0)
{
uint8_t v_explicit_704_; 
v_explicit_704_ = lean_ctor_get_uint8(v___y_690_, sizeof(void*)*1);
if (v_explicit_704_ == 0)
{
lean_object* v_a_705_; lean_object* v_varNames_706_; 
v_a_705_ = lean_ctor_get(v___x_703_, 0);
lean_inc(v_a_705_);
lean_dec_ref_known(v___x_703_, 1);
v_varNames_706_ = lean_ctor_get(v___y_690_, 0);
lean_inc(v_varNames_706_);
lean_dec_ref(v___y_690_);
v___y_635_ = v___y_687_;
v___y_636_ = v___y_698_;
v___y_637_ = v___y_691_;
v___y_638_ = v___y_693_;
v___y_639_ = v___y_692_;
v___y_640_ = v___y_695_;
v___y_641_ = v___y_697_;
v___y_642_ = v___y_699_;
v___y_643_ = v___y_696_;
v___y_644_ = v___y_686_;
v___y_645_ = v___y_700_;
v___y_646_ = v___y_689_;
v___y_647_ = v_a_705_;
v___y_648_ = v___y_694_;
v___y_649_ = v_varNames_706_;
v___y_650_ = v___y_695_;
goto v___jp_634_;
}
else
{
lean_object* v_a_707_; lean_object* v_varNames_708_; 
v_a_707_ = lean_ctor_get(v___x_703_, 0);
lean_inc(v_a_707_);
lean_dec_ref_known(v___x_703_, 1);
v_varNames_708_ = lean_ctor_get(v___y_690_, 0);
lean_inc(v_varNames_708_);
lean_dec_ref(v___y_690_);
v___y_635_ = v___y_687_;
v___y_636_ = v___y_698_;
v___y_637_ = v___y_691_;
v___y_638_ = v___y_693_;
v___y_639_ = v___y_692_;
v___y_640_ = v___y_695_;
v___y_641_ = v___y_697_;
v___y_642_ = v___y_699_;
v___y_643_ = v___y_696_;
v___y_644_ = v___y_686_;
v___y_645_ = v___y_700_;
v___y_646_ = v___y_689_;
v___y_647_ = v_a_707_;
v___y_648_ = v___y_694_;
v___y_649_ = v_varNames_708_;
v___y_650_ = v___y_691_;
goto v___jp_634_;
}
}
else
{
lean_object* v_a_709_; lean_object* v___x_711_; uint8_t v_isShared_712_; uint8_t v_isSharedCheck_716_; 
lean_dec_ref(v___y_696_);
lean_dec_ref(v___y_694_);
lean_dec(v___y_693_);
lean_dec(v___y_692_);
lean_dec_ref(v___y_690_);
lean_dec(v___y_689_);
lean_dec(v___y_686_);
lean_dec_ref(v_subgoals_571_);
lean_dec(v_minorIdx_567_);
lean_dec(v_pos_566_);
lean_dec(v_baseSubst_563_);
lean_dec_ref(v_major_561_);
lean_dec(v_mvarId_557_);
v_a_709_ = lean_ctor_get(v___x_703_, 0);
v_isSharedCheck_716_ = !lean_is_exclusive(v___x_703_);
if (v_isSharedCheck_716_ == 0)
{
v___x_711_ = v___x_703_;
v_isShared_712_ = v_isSharedCheck_716_;
goto v_resetjp_710_;
}
else
{
lean_inc(v_a_709_);
lean_dec(v___x_703_);
v___x_711_ = lean_box(0);
v_isShared_712_ = v_isSharedCheck_716_;
goto v_resetjp_710_;
}
v_resetjp_710_:
{
lean_object* v___x_714_; 
if (v_isShared_712_ == 0)
{
v___x_714_ = v___x_711_;
goto v_reusejp_713_;
}
else
{
lean_object* v_reuseFailAlloc_715_; 
v_reuseFailAlloc_715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_715_, 0, v_a_709_);
v___x_714_ = v_reuseFailAlloc_715_;
goto v_reusejp_713_;
}
v_reusejp_713_:
{
return v___x_714_;
}
}
}
}
v___jp_717_:
{
lean_object* v___x_722_; lean_object* v___x_723_; 
lean_inc_ref(v_major_561_);
v___x_722_ = l_Lean_Expr_app___override(v_fst_720_, v_major_561_);
lean_inc(v_mvarId_557_);
v___x_723_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTypeBody(v_mvarId_557_, v_snd_721_, v_major_561_, v_a_572_, v_a_573_, v_a_574_, v_a_575_);
if (lean_obj_tag(v___x_723_) == 0)
{
lean_object* v_a_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; 
v_a_724_ = lean_ctor_get(v___x_723_, 0);
lean_inc(v_a_724_);
lean_dec_ref_known(v___x_723_, 1);
v___x_725_ = lean_unsigned_to_nat(1u);
v___x_726_ = lean_nat_add(v_pos_566_, v___x_725_);
lean_dec(v_pos_566_);
v___x_727_ = lean_nat_add(v___x_726_, v___y_719_);
lean_dec(v___y_719_);
lean_dec(v___x_726_);
v_pos_566_ = v___x_727_;
v_recursor_568_ = v___x_722_;
v_recursorType_569_ = v_a_724_;
v_consumedMajor_570_ = v___y_718_;
goto _start;
}
else
{
lean_object* v_a_729_; lean_object* v___x_731_; uint8_t v_isShared_732_; uint8_t v_isSharedCheck_736_; 
lean_dec_ref(v___x_722_);
lean_dec(v___y_719_);
lean_dec_ref(v_subgoals_571_);
lean_dec(v_minorIdx_567_);
lean_dec(v_pos_566_);
lean_dec(v_baseSubst_563_);
lean_dec_ref(v_major_561_);
lean_dec(v_mvarId_557_);
v_a_729_ = lean_ctor_get(v___x_723_, 0);
v_isSharedCheck_736_ = !lean_is_exclusive(v___x_723_);
if (v_isSharedCheck_736_ == 0)
{
v___x_731_ = v___x_723_;
v_isShared_732_ = v_isSharedCheck_736_;
goto v_resetjp_730_;
}
else
{
lean_inc(v_a_729_);
lean_dec(v___x_723_);
v___x_731_ = lean_box(0);
v_isShared_732_ = v_isSharedCheck_736_;
goto v_resetjp_730_;
}
v_resetjp_730_:
{
lean_object* v___x_734_; 
if (v_isShared_732_ == 0)
{
v___x_734_ = v___x_731_;
goto v_reusejp_733_;
}
else
{
lean_object* v_reuseFailAlloc_735_; 
v_reuseFailAlloc_735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_735_, 0, v_a_729_);
v___x_734_ = v_reuseFailAlloc_735_;
goto v_reusejp_733_;
}
v_reusejp_733_:
{
return v___x_734_;
}
}
}
}
v___jp_737_:
{
if (lean_obj_tag(v___y_740_) == 0)
{
lean_object* v_a_741_; lean_object* v_fst_742_; lean_object* v_snd_743_; 
v_a_741_ = lean_ctor_get(v___y_740_, 0);
lean_inc(v_a_741_);
lean_dec_ref_known(v___y_740_, 1);
v_fst_742_ = lean_ctor_get(v_a_741_, 0);
lean_inc(v_fst_742_);
v_snd_743_ = lean_ctor_get(v_a_741_, 1);
lean_inc(v_snd_743_);
lean_dec(v_a_741_);
v___y_718_ = v___y_738_;
v___y_719_ = v___y_739_;
v_fst_720_ = v_fst_742_;
v_snd_721_ = v_snd_743_;
goto v___jp_717_;
}
else
{
lean_object* v_a_744_; lean_object* v___x_746_; uint8_t v_isShared_747_; uint8_t v_isSharedCheck_751_; 
lean_dec(v___y_739_);
lean_dec_ref(v_subgoals_571_);
lean_dec(v_minorIdx_567_);
lean_dec(v_pos_566_);
lean_dec(v_baseSubst_563_);
lean_dec_ref(v_major_561_);
lean_dec(v_mvarId_557_);
v_a_744_ = lean_ctor_get(v___y_740_, 0);
v_isSharedCheck_751_ = !lean_is_exclusive(v___y_740_);
if (v_isSharedCheck_751_ == 0)
{
v___x_746_ = v___y_740_;
v_isShared_747_ = v_isSharedCheck_751_;
goto v_resetjp_745_;
}
else
{
lean_inc(v_a_744_);
lean_dec(v___y_740_);
v___x_746_ = lean_box(0);
v_isShared_747_ = v_isSharedCheck_751_;
goto v_resetjp_745_;
}
v_resetjp_745_:
{
lean_object* v___x_749_; 
if (v_isShared_747_ == 0)
{
v___x_749_ = v___x_746_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_750_; 
v_reuseFailAlloc_750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_750_, 0, v_a_744_);
v___x_749_ = v_reuseFailAlloc_750_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
return v___x_749_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___boxed(lean_object** _args){
lean_object* v_mvarId_1000_ = _args[0];
lean_object* v_givenNames_1001_ = _args[1];
lean_object* v_recursorInfo_1002_ = _args[2];
lean_object* v_reverted_1003_ = _args[3];
lean_object* v_major_1004_ = _args[4];
lean_object* v_indices_1005_ = _args[5];
lean_object* v_baseSubst_1006_ = _args[6];
lean_object* v_initialArity_1007_ = _args[7];
lean_object* v_numMinors_1008_ = _args[8];
lean_object* v_pos_1009_ = _args[9];
lean_object* v_minorIdx_1010_ = _args[10];
lean_object* v_recursor_1011_ = _args[11];
lean_object* v_recursorType_1012_ = _args[12];
lean_object* v_consumedMajor_1013_ = _args[13];
lean_object* v_subgoals_1014_ = _args[14];
lean_object* v_a_1015_ = _args[15];
lean_object* v_a_1016_ = _args[16];
lean_object* v_a_1017_ = _args[17];
lean_object* v_a_1018_ = _args[18];
lean_object* v_a_1019_ = _args[19];
_start:
{
uint8_t v_consumedMajor_boxed_1020_; lean_object* v_res_1021_; 
v_consumedMajor_boxed_1020_ = lean_unbox(v_consumedMajor_1013_);
v_res_1021_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop(v_mvarId_1000_, v_givenNames_1001_, v_recursorInfo_1002_, v_reverted_1003_, v_major_1004_, v_indices_1005_, v_baseSubst_1006_, v_initialArity_1007_, v_numMinors_1008_, v_pos_1009_, v_minorIdx_1010_, v_recursor_1011_, v_recursorType_1012_, v_consumedMajor_boxed_1020_, v_subgoals_1014_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_);
lean_dec(v_a_1018_);
lean_dec_ref(v_a_1017_);
lean_dec(v_a_1016_);
lean_dec_ref(v_a_1015_);
lean_dec(v_numMinors_1008_);
lean_dec(v_initialArity_1007_);
lean_dec_ref(v_indices_1005_);
lean_dec_ref(v_reverted_1003_);
lean_dec_ref(v_recursorInfo_1002_);
lean_dec_ref(v_givenNames_1001_);
return v_res_1021_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0(lean_object* v_mvarId_1022_, lean_object* v_val_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_){
_start:
{
lean_object* v___x_1029_; 
v___x_1029_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0___redArg(v_mvarId_1022_, v_val_1023_, v___y_1025_);
return v___x_1029_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0___boxed(lean_object* v_mvarId_1030_, lean_object* v_val_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_){
_start:
{
lean_object* v_res_1037_; 
v_res_1037_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0(v_mvarId_1030_, v_val_1031_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_);
lean_dec(v___y_1035_);
lean_dec_ref(v___y_1034_);
lean_dec(v___y_1033_);
lean_dec_ref(v___y_1032_);
return v_res_1037_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__2(lean_object* v___x_1038_, lean_object* v_reverted_1039_, lean_object* v_fst_1040_, lean_object* v_n_1041_, lean_object* v_j_1042_, lean_object* v_a_1043_, lean_object* v_a_1044_){
_start:
{
lean_object* v___x_1045_; 
v___x_1045_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__2___redArg(v___x_1038_, v_reverted_1039_, v_fst_1040_, v_n_1041_, v_j_1042_, v_a_1044_);
return v___x_1045_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__2___boxed(lean_object* v___x_1046_, lean_object* v_reverted_1047_, lean_object* v_fst_1048_, lean_object* v_n_1049_, lean_object* v_j_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_){
_start:
{
lean_object* v_res_1053_; 
v_res_1053_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__2(v___x_1046_, v_reverted_1047_, v_fst_1048_, v_n_1049_, v_j_1050_, v_a_1051_, v_a_1052_);
lean_dec(v_n_1049_);
lean_dec_ref(v_fst_1048_);
lean_dec_ref(v_reverted_1047_);
lean_dec(v___x_1046_);
return v_res_1053_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0(lean_object* v_00_u03b2_1054_, lean_object* v_x_1055_, lean_object* v_x_1056_, lean_object* v_x_1057_){
_start:
{
lean_object* v___x_1058_; 
v___x_1058_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0___redArg(v_x_1055_, v_x_1056_, v_x_1057_);
return v___x_1058_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1059_, lean_object* v_x_1060_, size_t v_x_1061_, size_t v_x_1062_, lean_object* v_x_1063_, lean_object* v_x_1064_){
_start:
{
lean_object* v___x_1065_; 
v___x_1065_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2___redArg(v_x_1060_, v_x_1061_, v_x_1062_, v_x_1063_, v_x_1064_);
return v___x_1065_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1066_, lean_object* v_x_1067_, lean_object* v_x_1068_, lean_object* v_x_1069_, lean_object* v_x_1070_, lean_object* v_x_1071_){
_start:
{
size_t v_x_9042__boxed_1072_; size_t v_x_9043__boxed_1073_; lean_object* v_res_1074_; 
v_x_9042__boxed_1072_ = lean_unbox_usize(v_x_1068_);
lean_dec(v_x_1068_);
v_x_9043__boxed_1073_ = lean_unbox_usize(v_x_1069_);
lean_dec(v_x_1069_);
v_res_1074_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2(v_00_u03b2_1066_, v_x_1067_, v_x_9042__boxed_1072_, v_x_9043__boxed_1073_, v_x_1070_, v_x_1071_);
return v_res_1074_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__8(lean_object* v_00_u03b2_1075_, lean_object* v_n_1076_, lean_object* v_k_1077_, lean_object* v_v_1078_){
_start:
{
lean_object* v___x_1079_; 
v___x_1079_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__8___redArg(v_n_1076_, v_k_1077_, v_v_1078_);
return v___x_1079_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__9(lean_object* v_00_u03b2_1080_, size_t v_depth_1081_, lean_object* v_keys_1082_, lean_object* v_vals_1083_, lean_object* v_heq_1084_, lean_object* v_i_1085_, lean_object* v_entries_1086_){
_start:
{
lean_object* v___x_1087_; 
v___x_1087_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__9___redArg(v_depth_1081_, v_keys_1082_, v_vals_1083_, v_i_1085_, v_entries_1086_);
return v___x_1087_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__9___boxed(lean_object* v_00_u03b2_1088_, lean_object* v_depth_1089_, lean_object* v_keys_1090_, lean_object* v_vals_1091_, lean_object* v_heq_1092_, lean_object* v_i_1093_, lean_object* v_entries_1094_){
_start:
{
size_t v_depth_boxed_1095_; lean_object* v_res_1096_; 
v_depth_boxed_1095_ = lean_unbox_usize(v_depth_1089_);
lean_dec(v_depth_1089_);
v_res_1096_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__9(v_00_u03b2_1088_, v_depth_boxed_1095_, v_keys_1090_, v_vals_1091_, v_heq_1092_, v_i_1093_, v_entries_1094_);
lean_dec_ref(v_vals_1091_);
lean_dec_ref(v_keys_1090_);
return v_res_1096_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__8_spec__9(lean_object* v_00_u03b2_1097_, lean_object* v_x_1098_, lean_object* v_x_1099_, lean_object* v_x_1100_, lean_object* v_x_1101_){
_start:
{
lean_object* v___x_1102_; 
v___x_1102_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__8_spec__9___redArg(v_x_1098_, v_x_1099_, v_x_1100_, v_x_1101_);
return v___x_1102_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize(lean_object* v_mvarId_1105_, lean_object* v_givenNames_1106_, lean_object* v_recursorInfo_1107_, lean_object* v_reverted_1108_, lean_object* v_major_1109_, lean_object* v_indices_1110_, lean_object* v_baseSubst_1111_, lean_object* v_recursor_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_){
_start:
{
lean_object* v___x_1118_; 
lean_inc(v_mvarId_1105_);
v___x_1118_ = l_Lean_MVarId_getType(v_mvarId_1105_, v_a_1113_, v_a_1114_, v_a_1115_, v_a_1116_);
if (lean_obj_tag(v___x_1118_) == 0)
{
lean_object* v_a_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; 
v_a_1119_ = lean_ctor_get(v___x_1118_, 0);
lean_inc(v_a_1119_);
lean_dec_ref_known(v___x_1118_, 1);
v___x_1120_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTargetArity(v_a_1119_);
lean_inc(v_a_1116_);
lean_inc_ref(v_a_1115_);
lean_inc(v_a_1114_);
lean_inc_ref(v_a_1113_);
lean_inc_ref(v_recursor_1112_);
v___x_1121_ = lean_infer_type(v_recursor_1112_, v_a_1113_, v_a_1114_, v_a_1115_, v_a_1116_);
if (lean_obj_tag(v___x_1121_) == 0)
{
lean_object* v_a_1122_; lean_object* v_paramsPos_1123_; lean_object* v_produceMotive_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; uint8_t v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; 
v_a_1122_ = lean_ctor_get(v___x_1121_, 0);
lean_inc(v_a_1122_);
lean_dec_ref_known(v___x_1121_, 1);
v_paramsPos_1123_ = lean_ctor_get(v_recursorInfo_1107_, 5);
v_produceMotive_1124_ = lean_ctor_get(v_recursorInfo_1107_, 7);
v___x_1125_ = l_List_lengthTR___redArg(v_produceMotive_1124_);
v___x_1126_ = l_List_lengthTR___redArg(v_paramsPos_1123_);
v___x_1127_ = lean_unsigned_to_nat(1u);
v___x_1128_ = lean_nat_add(v___x_1126_, v___x_1127_);
lean_dec(v___x_1126_);
v___x_1129_ = lean_unsigned_to_nat(0u);
v___x_1130_ = 0;
v___x_1131_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize___closed__0));
v___x_1132_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop(v_mvarId_1105_, v_givenNames_1106_, v_recursorInfo_1107_, v_reverted_1108_, v_major_1109_, v_indices_1110_, v_baseSubst_1111_, v___x_1120_, v___x_1125_, v___x_1128_, v___x_1129_, v_recursor_1112_, v_a_1122_, v___x_1130_, v___x_1131_, v_a_1113_, v_a_1114_, v_a_1115_, v_a_1116_);
lean_dec(v___x_1125_);
lean_dec(v___x_1120_);
return v___x_1132_;
}
else
{
lean_object* v_a_1133_; lean_object* v___x_1135_; uint8_t v_isShared_1136_; uint8_t v_isSharedCheck_1140_; 
lean_dec(v___x_1120_);
lean_dec_ref(v_recursor_1112_);
lean_dec(v_baseSubst_1111_);
lean_dec_ref(v_major_1109_);
lean_dec(v_mvarId_1105_);
v_a_1133_ = lean_ctor_get(v___x_1121_, 0);
v_isSharedCheck_1140_ = !lean_is_exclusive(v___x_1121_);
if (v_isSharedCheck_1140_ == 0)
{
v___x_1135_ = v___x_1121_;
v_isShared_1136_ = v_isSharedCheck_1140_;
goto v_resetjp_1134_;
}
else
{
lean_inc(v_a_1133_);
lean_dec(v___x_1121_);
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
else
{
lean_object* v_a_1141_; lean_object* v___x_1143_; uint8_t v_isShared_1144_; uint8_t v_isSharedCheck_1148_; 
lean_dec_ref(v_recursor_1112_);
lean_dec(v_baseSubst_1111_);
lean_dec_ref(v_major_1109_);
lean_dec(v_mvarId_1105_);
v_a_1141_ = lean_ctor_get(v___x_1118_, 0);
v_isSharedCheck_1148_ = !lean_is_exclusive(v___x_1118_);
if (v_isSharedCheck_1148_ == 0)
{
v___x_1143_ = v___x_1118_;
v_isShared_1144_ = v_isSharedCheck_1148_;
goto v_resetjp_1142_;
}
else
{
lean_inc(v_a_1141_);
lean_dec(v___x_1118_);
v___x_1143_ = lean_box(0);
v_isShared_1144_ = v_isSharedCheck_1148_;
goto v_resetjp_1142_;
}
v_resetjp_1142_:
{
lean_object* v___x_1146_; 
if (v_isShared_1144_ == 0)
{
v___x_1146_ = v___x_1143_;
goto v_reusejp_1145_;
}
else
{
lean_object* v_reuseFailAlloc_1147_; 
v_reuseFailAlloc_1147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1147_, 0, v_a_1141_);
v___x_1146_ = v_reuseFailAlloc_1147_;
goto v_reusejp_1145_;
}
v_reusejp_1145_:
{
return v___x_1146_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize___boxed(lean_object* v_mvarId_1149_, lean_object* v_givenNames_1150_, lean_object* v_recursorInfo_1151_, lean_object* v_reverted_1152_, lean_object* v_major_1153_, lean_object* v_indices_1154_, lean_object* v_baseSubst_1155_, lean_object* v_recursor_1156_, lean_object* v_a_1157_, lean_object* v_a_1158_, lean_object* v_a_1159_, lean_object* v_a_1160_, lean_object* v_a_1161_){
_start:
{
lean_object* v_res_1162_; 
v_res_1162_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize(v_mvarId_1149_, v_givenNames_1150_, v_recursorInfo_1151_, v_reverted_1152_, v_major_1153_, v_indices_1154_, v_baseSubst_1155_, v_recursor_1156_, v_a_1157_, v_a_1158_, v_a_1159_, v_a_1160_);
lean_dec(v_a_1160_);
lean_dec_ref(v_a_1159_);
lean_dec(v_a_1158_);
lean_dec_ref(v_a_1157_);
lean_dec_ref(v_indices_1154_);
lean_dec_ref(v_reverted_1152_);
lean_dec_ref(v_recursorInfo_1151_);
lean_dec_ref(v_givenNames_1150_);
return v_res_1162_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg___closed__1(void){
_start:
{
lean_object* v___x_1164_; lean_object* v___x_1165_; 
v___x_1164_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg___closed__0));
v___x_1165_ = l_Lean_stringToMessageData(v___x_1164_);
return v___x_1165_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg(lean_object* v_tacticName_1166_, lean_object* v_mvarId_1167_, lean_object* v_majorType_1168_, lean_object* v_a_1169_, lean_object* v_a_1170_, lean_object* v_a_1171_, lean_object* v_a_1172_){
_start:
{
lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; 
v___x_1174_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg___closed__1, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg___closed__1);
v___x_1175_ = l_Lean_indentExpr(v_majorType_1168_);
v___x_1176_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1176_, 0, v___x_1174_);
lean_ctor_set(v___x_1176_, 1, v___x_1175_);
v___x_1177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1177_, 0, v___x_1176_);
v___x_1178_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1166_, v_mvarId_1167_, v___x_1177_, v_a_1169_, v_a_1170_, v_a_1171_, v_a_1172_);
return v___x_1178_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg___boxed(lean_object* v_tacticName_1179_, lean_object* v_mvarId_1180_, lean_object* v_majorType_1181_, lean_object* v_a_1182_, lean_object* v_a_1183_, lean_object* v_a_1184_, lean_object* v_a_1185_, lean_object* v_a_1186_){
_start:
{
lean_object* v_res_1187_; 
v_res_1187_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg(v_tacticName_1179_, v_mvarId_1180_, v_majorType_1181_, v_a_1182_, v_a_1183_, v_a_1184_, v_a_1185_);
lean_dec(v_a_1185_);
lean_dec_ref(v_a_1184_);
lean_dec(v_a_1183_);
lean_dec_ref(v_a_1182_);
return v_res_1187_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType(lean_object* v_00_u03b1_1188_, lean_object* v_tacticName_1189_, lean_object* v_mvarId_1190_, lean_object* v_majorType_1191_, lean_object* v_a_1192_, lean_object* v_a_1193_, lean_object* v_a_1194_, lean_object* v_a_1195_){
_start:
{
lean_object* v___x_1197_; 
v___x_1197_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg(v_tacticName_1189_, v_mvarId_1190_, v_majorType_1191_, v_a_1192_, v_a_1193_, v_a_1194_, v_a_1195_);
return v___x_1197_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___boxed(lean_object* v_00_u03b1_1198_, lean_object* v_tacticName_1199_, lean_object* v_mvarId_1200_, lean_object* v_majorType_1201_, lean_object* v_a_1202_, lean_object* v_a_1203_, lean_object* v_a_1204_, lean_object* v_a_1205_, lean_object* v_a_1206_){
_start:
{
lean_object* v_res_1207_; 
v_res_1207_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType(v_00_u03b1_1198_, v_tacticName_1199_, v_mvarId_1200_, v_majorType_1201_, v_a_1202_, v_a_1203_, v_a_1204_, v_a_1205_);
lean_dec(v_a_1205_);
lean_dec_ref(v_a_1204_);
lean_dec(v_a_1203_);
lean_dec_ref(v_a_1202_);
return v_res_1207_;
}
}
LEAN_EXPORT uint8_t l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___lam__0(lean_object* v_fvarId_1208_, lean_object* v_x_1209_){
_start:
{
uint8_t v___x_1210_; 
v___x_1210_ = l_Lean_instBEqFVarId_beq(v_fvarId_1208_, v_x_1209_);
return v___x_1210_;
}
}
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___lam__0___boxed(lean_object* v_fvarId_1211_, lean_object* v_x_1212_){
_start:
{
uint8_t v_res_1213_; lean_object* v_r_1214_; 
v_res_1213_ = l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___lam__0(v_fvarId_1211_, v_x_1212_);
lean_dec(v_x_1212_);
lean_dec(v_fvarId_1211_);
v_r_1214_ = lean_box(v_res_1213_);
return v_r_1214_;
}
}
LEAN_EXPORT uint8_t l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___lam__1(lean_object* v_x_1215_){
_start:
{
uint8_t v___x_1216_; 
v___x_1216_ = 0;
return v___x_1216_;
}
}
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___lam__1___boxed(lean_object* v_x_1217_){
_start:
{
uint8_t v_res_1218_; lean_object* v_r_1219_; 
v_res_1218_ = l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___lam__1(v_x_1217_);
lean_dec(v_x_1217_);
v_r_1219_ = lean_box(v_res_1218_);
return v_r_1219_;
}
}
static lean_object* _init_l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; 
v___x_1221_ = lean_box(0);
v___x_1222_ = lean_unsigned_to_nat(16u);
v___x_1223_ = lean_mk_array(v___x_1222_, v___x_1221_);
return v___x_1223_;
}
}
static lean_object* _init_l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; 
v___x_1224_ = lean_obj_once(&l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__1, &l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__1_once, _init_l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__1);
v___x_1225_ = lean_unsigned_to_nat(0u);
v___x_1226_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1226_, 0, v___x_1225_);
lean_ctor_set(v___x_1226_, 1, v___x_1224_);
return v___x_1226_;
}
}
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg(lean_object* v_localDecl_1227_, lean_object* v_fvarId_1228_, uint8_t v_generalizeNondepLet_1229_, lean_object* v___y_1230_){
_start:
{
uint8_t v_fst_1233_; lean_object* v_snd_1234_; lean_object* v___y_1253_; lean_object* v___f_1257_; lean_object* v___f_1258_; 
v___f_1257_ = lean_alloc_closure((void*)(l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1257_, 0, v_fvarId_1228_);
v___f_1258_ = ((lean_object*)(l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__0));
if (lean_obj_tag(v_localDecl_1227_) == 0)
{
lean_object* v_type_1259_; lean_object* v___x_1260_; uint8_t v_fst_1262_; lean_object* v_mctx_1263_; lean_object* v___y_1281_; lean_object* v_mctx_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; uint8_t v___x_1289_; 
v_type_1259_ = lean_ctor_get(v_localDecl_1227_, 3);
lean_inc_ref(v_type_1259_);
lean_dec_ref_known(v_localDecl_1227_, 4);
v___x_1260_ = lean_st_ref_get(v___y_1230_);
v_mctx_1286_ = lean_ctor_get(v___x_1260_, 0);
lean_inc_ref_n(v_mctx_1286_, 2);
lean_dec(v___x_1260_);
v___x_1287_ = lean_obj_once(&l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__2, &l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__2_once, _init_l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__2);
v___x_1288_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1288_, 0, v___x_1287_);
lean_ctor_set(v___x_1288_, 1, v_mctx_1286_);
v___x_1289_ = l_Lean_Expr_hasFVar(v_type_1259_);
if (v___x_1289_ == 0)
{
uint8_t v___x_1290_; 
v___x_1290_ = l_Lean_Expr_hasMVar(v_type_1259_);
if (v___x_1290_ == 0)
{
lean_dec_ref_known(v___x_1288_, 2);
lean_dec_ref(v_type_1259_);
lean_dec_ref(v___f_1257_);
v_fst_1262_ = v___x_1290_;
v_mctx_1263_ = v_mctx_1286_;
goto v___jp_1261_;
}
else
{
lean_object* v___x_1291_; 
lean_dec_ref(v_mctx_1286_);
v___x_1291_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1257_, v___f_1258_, v_type_1259_, v___x_1288_);
v___y_1281_ = v___x_1291_;
goto v___jp_1280_;
}
}
else
{
lean_object* v___x_1292_; 
lean_dec_ref(v_mctx_1286_);
v___x_1292_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1257_, v___f_1258_, v_type_1259_, v___x_1288_);
v___y_1281_ = v___x_1292_;
goto v___jp_1280_;
}
v___jp_1261_:
{
lean_object* v___x_1264_; lean_object* v_cache_1265_; lean_object* v_zetaDeltaFVarIds_1266_; lean_object* v_postponed_1267_; lean_object* v_diag_1268_; lean_object* v___x_1270_; uint8_t v_isShared_1271_; uint8_t v_isSharedCheck_1278_; 
v___x_1264_ = lean_st_ref_take(v___y_1230_);
v_cache_1265_ = lean_ctor_get(v___x_1264_, 1);
v_zetaDeltaFVarIds_1266_ = lean_ctor_get(v___x_1264_, 2);
v_postponed_1267_ = lean_ctor_get(v___x_1264_, 3);
v_diag_1268_ = lean_ctor_get(v___x_1264_, 4);
v_isSharedCheck_1278_ = !lean_is_exclusive(v___x_1264_);
if (v_isSharedCheck_1278_ == 0)
{
lean_object* v_unused_1279_; 
v_unused_1279_ = lean_ctor_get(v___x_1264_, 0);
lean_dec(v_unused_1279_);
v___x_1270_ = v___x_1264_;
v_isShared_1271_ = v_isSharedCheck_1278_;
goto v_resetjp_1269_;
}
else
{
lean_inc(v_diag_1268_);
lean_inc(v_postponed_1267_);
lean_inc(v_zetaDeltaFVarIds_1266_);
lean_inc(v_cache_1265_);
lean_dec(v___x_1264_);
v___x_1270_ = lean_box(0);
v_isShared_1271_ = v_isSharedCheck_1278_;
goto v_resetjp_1269_;
}
v_resetjp_1269_:
{
lean_object* v___x_1273_; 
if (v_isShared_1271_ == 0)
{
lean_ctor_set(v___x_1270_, 0, v_mctx_1263_);
v___x_1273_ = v___x_1270_;
goto v_reusejp_1272_;
}
else
{
lean_object* v_reuseFailAlloc_1277_; 
v_reuseFailAlloc_1277_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1277_, 0, v_mctx_1263_);
lean_ctor_set(v_reuseFailAlloc_1277_, 1, v_cache_1265_);
lean_ctor_set(v_reuseFailAlloc_1277_, 2, v_zetaDeltaFVarIds_1266_);
lean_ctor_set(v_reuseFailAlloc_1277_, 3, v_postponed_1267_);
lean_ctor_set(v_reuseFailAlloc_1277_, 4, v_diag_1268_);
v___x_1273_ = v_reuseFailAlloc_1277_;
goto v_reusejp_1272_;
}
v_reusejp_1272_:
{
lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; 
v___x_1274_ = lean_st_ref_put(v___y_1230_, v___x_1273_);
v___x_1275_ = lean_box(v_fst_1262_);
v___x_1276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1276_, 0, v___x_1275_);
return v___x_1276_;
}
}
}
v___jp_1280_:
{
lean_object* v_snd_1282_; lean_object* v_fst_1283_; lean_object* v_mctx_1284_; uint8_t v___x_1285_; 
v_snd_1282_ = lean_ctor_get(v___y_1281_, 1);
lean_inc(v_snd_1282_);
v_fst_1283_ = lean_ctor_get(v___y_1281_, 0);
lean_inc(v_fst_1283_);
lean_dec_ref(v___y_1281_);
v_mctx_1284_ = lean_ctor_get(v_snd_1282_, 1);
lean_inc_ref(v_mctx_1284_);
lean_dec(v_snd_1282_);
v___x_1285_ = lean_unbox(v_fst_1283_);
lean_dec(v_fst_1283_);
v_fst_1262_ = v___x_1285_;
v_mctx_1263_ = v_mctx_1284_;
goto v___jp_1261_;
}
}
else
{
lean_object* v_type_1293_; lean_object* v_value_1294_; uint8_t v_nondep_1295_; uint8_t v_fst_1297_; lean_object* v_snd_1298_; lean_object* v___y_1304_; 
v_type_1293_ = lean_ctor_get(v_localDecl_1227_, 3);
lean_inc_ref(v_type_1293_);
v_value_1294_ = lean_ctor_get(v_localDecl_1227_, 4);
lean_inc_ref(v_value_1294_);
v_nondep_1295_ = lean_ctor_get_uint8(v_localDecl_1227_, sizeof(void*)*5);
lean_dec_ref_known(v_localDecl_1227_, 5);
if (v_generalizeNondepLet_1229_ == 0)
{
goto v___jp_1308_;
}
else
{
if (v_nondep_1295_ == 0)
{
goto v___jp_1308_;
}
else
{
lean_object* v___x_1317_; uint8_t v_fst_1319_; lean_object* v_mctx_1320_; lean_object* v___y_1338_; lean_object* v_mctx_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; uint8_t v___x_1346_; 
lean_dec_ref(v_value_1294_);
v___x_1317_ = lean_st_ref_get(v___y_1230_);
v_mctx_1343_ = lean_ctor_get(v___x_1317_, 0);
lean_inc_ref_n(v_mctx_1343_, 2);
lean_dec(v___x_1317_);
v___x_1344_ = lean_obj_once(&l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__2, &l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__2_once, _init_l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__2);
v___x_1345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1345_, 0, v___x_1344_);
lean_ctor_set(v___x_1345_, 1, v_mctx_1343_);
v___x_1346_ = l_Lean_Expr_hasFVar(v_type_1293_);
if (v___x_1346_ == 0)
{
uint8_t v___x_1347_; 
v___x_1347_ = l_Lean_Expr_hasMVar(v_type_1293_);
if (v___x_1347_ == 0)
{
lean_dec_ref_known(v___x_1345_, 2);
lean_dec_ref(v_type_1293_);
lean_dec_ref(v___f_1257_);
v_fst_1319_ = v___x_1347_;
v_mctx_1320_ = v_mctx_1343_;
goto v___jp_1318_;
}
else
{
lean_object* v___x_1348_; 
lean_dec_ref(v_mctx_1343_);
v___x_1348_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1257_, v___f_1258_, v_type_1293_, v___x_1345_);
v___y_1338_ = v___x_1348_;
goto v___jp_1337_;
}
}
else
{
lean_object* v___x_1349_; 
lean_dec_ref(v_mctx_1343_);
v___x_1349_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1257_, v___f_1258_, v_type_1293_, v___x_1345_);
v___y_1338_ = v___x_1349_;
goto v___jp_1337_;
}
v___jp_1318_:
{
lean_object* v___x_1321_; lean_object* v_cache_1322_; lean_object* v_zetaDeltaFVarIds_1323_; lean_object* v_postponed_1324_; lean_object* v_diag_1325_; lean_object* v___x_1327_; uint8_t v_isShared_1328_; uint8_t v_isSharedCheck_1335_; 
v___x_1321_ = lean_st_ref_take(v___y_1230_);
v_cache_1322_ = lean_ctor_get(v___x_1321_, 1);
v_zetaDeltaFVarIds_1323_ = lean_ctor_get(v___x_1321_, 2);
v_postponed_1324_ = lean_ctor_get(v___x_1321_, 3);
v_diag_1325_ = lean_ctor_get(v___x_1321_, 4);
v_isSharedCheck_1335_ = !lean_is_exclusive(v___x_1321_);
if (v_isSharedCheck_1335_ == 0)
{
lean_object* v_unused_1336_; 
v_unused_1336_ = lean_ctor_get(v___x_1321_, 0);
lean_dec(v_unused_1336_);
v___x_1327_ = v___x_1321_;
v_isShared_1328_ = v_isSharedCheck_1335_;
goto v_resetjp_1326_;
}
else
{
lean_inc(v_diag_1325_);
lean_inc(v_postponed_1324_);
lean_inc(v_zetaDeltaFVarIds_1323_);
lean_inc(v_cache_1322_);
lean_dec(v___x_1321_);
v___x_1327_ = lean_box(0);
v_isShared_1328_ = v_isSharedCheck_1335_;
goto v_resetjp_1326_;
}
v_resetjp_1326_:
{
lean_object* v___x_1330_; 
if (v_isShared_1328_ == 0)
{
lean_ctor_set(v___x_1327_, 0, v_mctx_1320_);
v___x_1330_ = v___x_1327_;
goto v_reusejp_1329_;
}
else
{
lean_object* v_reuseFailAlloc_1334_; 
v_reuseFailAlloc_1334_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1334_, 0, v_mctx_1320_);
lean_ctor_set(v_reuseFailAlloc_1334_, 1, v_cache_1322_);
lean_ctor_set(v_reuseFailAlloc_1334_, 2, v_zetaDeltaFVarIds_1323_);
lean_ctor_set(v_reuseFailAlloc_1334_, 3, v_postponed_1324_);
lean_ctor_set(v_reuseFailAlloc_1334_, 4, v_diag_1325_);
v___x_1330_ = v_reuseFailAlloc_1334_;
goto v_reusejp_1329_;
}
v_reusejp_1329_:
{
lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; 
v___x_1331_ = lean_st_ref_put(v___y_1230_, v___x_1330_);
v___x_1332_ = lean_box(v_fst_1319_);
v___x_1333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1333_, 0, v___x_1332_);
return v___x_1333_;
}
}
}
v___jp_1337_:
{
lean_object* v_snd_1339_; lean_object* v_fst_1340_; lean_object* v_mctx_1341_; uint8_t v___x_1342_; 
v_snd_1339_ = lean_ctor_get(v___y_1338_, 1);
lean_inc(v_snd_1339_);
v_fst_1340_ = lean_ctor_get(v___y_1338_, 0);
lean_inc(v_fst_1340_);
lean_dec_ref(v___y_1338_);
v_mctx_1341_ = lean_ctor_get(v_snd_1339_, 1);
lean_inc_ref(v_mctx_1341_);
lean_dec(v_snd_1339_);
v___x_1342_ = lean_unbox(v_fst_1340_);
lean_dec(v_fst_1340_);
v_fst_1319_ = v___x_1342_;
v_mctx_1320_ = v_mctx_1341_;
goto v___jp_1318_;
}
}
}
v___jp_1296_:
{
if (v_fst_1297_ == 0)
{
uint8_t v___x_1299_; 
v___x_1299_ = l_Lean_Expr_hasFVar(v_value_1294_);
if (v___x_1299_ == 0)
{
uint8_t v___x_1300_; 
v___x_1300_ = l_Lean_Expr_hasMVar(v_value_1294_);
if (v___x_1300_ == 0)
{
lean_dec_ref(v_value_1294_);
lean_dec_ref(v___f_1257_);
v_fst_1233_ = v___x_1300_;
v_snd_1234_ = v_snd_1298_;
goto v___jp_1232_;
}
else
{
lean_object* v___x_1301_; 
v___x_1301_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1257_, v___f_1258_, v_value_1294_, v_snd_1298_);
v___y_1253_ = v___x_1301_;
goto v___jp_1252_;
}
}
else
{
lean_object* v___x_1302_; 
v___x_1302_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1257_, v___f_1258_, v_value_1294_, v_snd_1298_);
v___y_1253_ = v___x_1302_;
goto v___jp_1252_;
}
}
else
{
lean_dec_ref(v_value_1294_);
lean_dec_ref(v___f_1257_);
v_fst_1233_ = v_fst_1297_;
v_snd_1234_ = v_snd_1298_;
goto v___jp_1232_;
}
}
v___jp_1303_:
{
lean_object* v_fst_1305_; lean_object* v_snd_1306_; uint8_t v___x_1307_; 
v_fst_1305_ = lean_ctor_get(v___y_1304_, 0);
lean_inc(v_fst_1305_);
v_snd_1306_ = lean_ctor_get(v___y_1304_, 1);
lean_inc(v_snd_1306_);
lean_dec_ref(v___y_1304_);
v___x_1307_ = lean_unbox(v_fst_1305_);
lean_dec(v_fst_1305_);
v_fst_1297_ = v___x_1307_;
v_snd_1298_ = v_snd_1306_;
goto v___jp_1296_;
}
v___jp_1308_:
{
lean_object* v___x_1309_; lean_object* v_mctx_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; uint8_t v___x_1313_; 
v___x_1309_ = lean_st_ref_get(v___y_1230_);
v_mctx_1310_ = lean_ctor_get(v___x_1309_, 0);
lean_inc_ref(v_mctx_1310_);
lean_dec(v___x_1309_);
v___x_1311_ = lean_obj_once(&l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__2, &l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__2_once, _init_l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__2);
v___x_1312_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1312_, 0, v___x_1311_);
lean_ctor_set(v___x_1312_, 1, v_mctx_1310_);
v___x_1313_ = l_Lean_Expr_hasFVar(v_type_1293_);
if (v___x_1313_ == 0)
{
uint8_t v___x_1314_; 
v___x_1314_ = l_Lean_Expr_hasMVar(v_type_1293_);
if (v___x_1314_ == 0)
{
lean_dec_ref(v_type_1293_);
v_fst_1297_ = v___x_1314_;
v_snd_1298_ = v___x_1312_;
goto v___jp_1296_;
}
else
{
lean_object* v___x_1315_; 
lean_inc_ref(v___f_1257_);
v___x_1315_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1257_, v___f_1258_, v_type_1293_, v___x_1312_);
v___y_1304_ = v___x_1315_;
goto v___jp_1303_;
}
}
else
{
lean_object* v___x_1316_; 
lean_inc_ref(v___f_1257_);
v___x_1316_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1257_, v___f_1258_, v_type_1293_, v___x_1312_);
v___y_1304_ = v___x_1316_;
goto v___jp_1303_;
}
}
}
v___jp_1232_:
{
lean_object* v_mctx_1235_; lean_object* v___x_1236_; lean_object* v_cache_1237_; lean_object* v_zetaDeltaFVarIds_1238_; lean_object* v_postponed_1239_; lean_object* v_diag_1240_; lean_object* v___x_1242_; uint8_t v_isShared_1243_; uint8_t v_isSharedCheck_1250_; 
v_mctx_1235_ = lean_ctor_get(v_snd_1234_, 1);
lean_inc_ref(v_mctx_1235_);
lean_dec_ref(v_snd_1234_);
v___x_1236_ = lean_st_ref_take(v___y_1230_);
v_cache_1237_ = lean_ctor_get(v___x_1236_, 1);
v_zetaDeltaFVarIds_1238_ = lean_ctor_get(v___x_1236_, 2);
v_postponed_1239_ = lean_ctor_get(v___x_1236_, 3);
v_diag_1240_ = lean_ctor_get(v___x_1236_, 4);
v_isSharedCheck_1250_ = !lean_is_exclusive(v___x_1236_);
if (v_isSharedCheck_1250_ == 0)
{
lean_object* v_unused_1251_; 
v_unused_1251_ = lean_ctor_get(v___x_1236_, 0);
lean_dec(v_unused_1251_);
v___x_1242_ = v___x_1236_;
v_isShared_1243_ = v_isSharedCheck_1250_;
goto v_resetjp_1241_;
}
else
{
lean_inc(v_diag_1240_);
lean_inc(v_postponed_1239_);
lean_inc(v_zetaDeltaFVarIds_1238_);
lean_inc(v_cache_1237_);
lean_dec(v___x_1236_);
v___x_1242_ = lean_box(0);
v_isShared_1243_ = v_isSharedCheck_1250_;
goto v_resetjp_1241_;
}
v_resetjp_1241_:
{
lean_object* v___x_1245_; 
if (v_isShared_1243_ == 0)
{
lean_ctor_set(v___x_1242_, 0, v_mctx_1235_);
v___x_1245_ = v___x_1242_;
goto v_reusejp_1244_;
}
else
{
lean_object* v_reuseFailAlloc_1249_; 
v_reuseFailAlloc_1249_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1249_, 0, v_mctx_1235_);
lean_ctor_set(v_reuseFailAlloc_1249_, 1, v_cache_1237_);
lean_ctor_set(v_reuseFailAlloc_1249_, 2, v_zetaDeltaFVarIds_1238_);
lean_ctor_set(v_reuseFailAlloc_1249_, 3, v_postponed_1239_);
lean_ctor_set(v_reuseFailAlloc_1249_, 4, v_diag_1240_);
v___x_1245_ = v_reuseFailAlloc_1249_;
goto v_reusejp_1244_;
}
v_reusejp_1244_:
{
lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; 
v___x_1246_ = lean_st_ref_put(v___y_1230_, v___x_1245_);
v___x_1247_ = lean_box(v_fst_1233_);
v___x_1248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1248_, 0, v___x_1247_);
return v___x_1248_;
}
}
}
v___jp_1252_:
{
lean_object* v_fst_1254_; lean_object* v_snd_1255_; uint8_t v___x_1256_; 
v_fst_1254_ = lean_ctor_get(v___y_1253_, 0);
lean_inc(v_fst_1254_);
v_snd_1255_ = lean_ctor_get(v___y_1253_, 1);
lean_inc(v_snd_1255_);
lean_dec_ref(v___y_1253_);
v___x_1256_ = lean_unbox(v_fst_1254_);
lean_dec(v_fst_1254_);
v_fst_1233_ = v___x_1256_;
v_snd_1234_ = v_snd_1255_;
goto v___jp_1232_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___boxed(lean_object* v_localDecl_1350_, lean_object* v_fvarId_1351_, lean_object* v_generalizeNondepLet_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_){
_start:
{
uint8_t v_generalizeNondepLet_boxed_1355_; lean_object* v_res_1356_; 
v_generalizeNondepLet_boxed_1355_ = lean_unbox(v_generalizeNondepLet_1352_);
v_res_1356_ = l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg(v_localDecl_1350_, v_fvarId_1351_, v_generalizeNondepLet_boxed_1355_, v___y_1353_);
lean_dec(v___y_1353_);
return v_res_1356_;
}
}
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1(lean_object* v_localDecl_1357_, lean_object* v_fvarId_1358_, uint8_t v_generalizeNondepLet_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_){
_start:
{
lean_object* v___x_1365_; 
v___x_1365_ = l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg(v_localDecl_1357_, v_fvarId_1358_, v_generalizeNondepLet_1359_, v___y_1361_);
return v___x_1365_;
}
}
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___boxed(lean_object* v_localDecl_1366_, lean_object* v_fvarId_1367_, lean_object* v_generalizeNondepLet_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_){
_start:
{
uint8_t v_generalizeNondepLet_boxed_1374_; lean_object* v_res_1375_; 
v_generalizeNondepLet_boxed_1374_ = lean_unbox(v_generalizeNondepLet_1368_);
v_res_1375_ = l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1(v_localDecl_1366_, v_fvarId_1367_, v_generalizeNondepLet_boxed_1374_, v___y_1369_, v___y_1370_, v___y_1371_, v___y_1372_);
lean_dec(v___y_1372_);
lean_dec_ref(v___y_1371_);
lean_dec(v___y_1370_);
lean_dec_ref(v___y_1369_);
return v_res_1375_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2___redArg(lean_object* v_e_1376_, lean_object* v_fvarId_1377_, lean_object* v___y_1378_){
_start:
{
lean_object* v___f_1380_; lean_object* v___f_1381_; lean_object* v___x_1382_; uint8_t v_fst_1384_; lean_object* v_mctx_1385_; lean_object* v___y_1403_; lean_object* v_mctx_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; uint8_t v___x_1411_; 
v___f_1380_ = ((lean_object*)(l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__0));
v___f_1381_ = lean_alloc_closure((void*)(l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1381_, 0, v_fvarId_1377_);
v___x_1382_ = lean_st_ref_get(v___y_1378_);
v_mctx_1408_ = lean_ctor_get(v___x_1382_, 0);
lean_inc_ref_n(v_mctx_1408_, 2);
lean_dec(v___x_1382_);
v___x_1409_ = lean_obj_once(&l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__2, &l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__2_once, _init_l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__2);
v___x_1410_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1410_, 0, v___x_1409_);
lean_ctor_set(v___x_1410_, 1, v_mctx_1408_);
v___x_1411_ = l_Lean_Expr_hasFVar(v_e_1376_);
if (v___x_1411_ == 0)
{
uint8_t v___x_1412_; 
v___x_1412_ = l_Lean_Expr_hasMVar(v_e_1376_);
if (v___x_1412_ == 0)
{
lean_dec_ref_known(v___x_1410_, 2);
lean_dec_ref(v___f_1381_);
lean_dec_ref(v_e_1376_);
v_fst_1384_ = v___x_1412_;
v_mctx_1385_ = v_mctx_1408_;
goto v___jp_1383_;
}
else
{
lean_object* v___x_1413_; 
lean_dec_ref(v_mctx_1408_);
v___x_1413_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1381_, v___f_1380_, v_e_1376_, v___x_1410_);
v___y_1403_ = v___x_1413_;
goto v___jp_1402_;
}
}
else
{
lean_object* v___x_1414_; 
lean_dec_ref(v_mctx_1408_);
v___x_1414_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1381_, v___f_1380_, v_e_1376_, v___x_1410_);
v___y_1403_ = v___x_1414_;
goto v___jp_1402_;
}
v___jp_1383_:
{
lean_object* v___x_1386_; lean_object* v_cache_1387_; lean_object* v_zetaDeltaFVarIds_1388_; lean_object* v_postponed_1389_; lean_object* v_diag_1390_; lean_object* v___x_1392_; uint8_t v_isShared_1393_; uint8_t v_isSharedCheck_1400_; 
v___x_1386_ = lean_st_ref_take(v___y_1378_);
v_cache_1387_ = lean_ctor_get(v___x_1386_, 1);
v_zetaDeltaFVarIds_1388_ = lean_ctor_get(v___x_1386_, 2);
v_postponed_1389_ = lean_ctor_get(v___x_1386_, 3);
v_diag_1390_ = lean_ctor_get(v___x_1386_, 4);
v_isSharedCheck_1400_ = !lean_is_exclusive(v___x_1386_);
if (v_isSharedCheck_1400_ == 0)
{
lean_object* v_unused_1401_; 
v_unused_1401_ = lean_ctor_get(v___x_1386_, 0);
lean_dec(v_unused_1401_);
v___x_1392_ = v___x_1386_;
v_isShared_1393_ = v_isSharedCheck_1400_;
goto v_resetjp_1391_;
}
else
{
lean_inc(v_diag_1390_);
lean_inc(v_postponed_1389_);
lean_inc(v_zetaDeltaFVarIds_1388_);
lean_inc(v_cache_1387_);
lean_dec(v___x_1386_);
v___x_1392_ = lean_box(0);
v_isShared_1393_ = v_isSharedCheck_1400_;
goto v_resetjp_1391_;
}
v_resetjp_1391_:
{
lean_object* v___x_1395_; 
if (v_isShared_1393_ == 0)
{
lean_ctor_set(v___x_1392_, 0, v_mctx_1385_);
v___x_1395_ = v___x_1392_;
goto v_reusejp_1394_;
}
else
{
lean_object* v_reuseFailAlloc_1399_; 
v_reuseFailAlloc_1399_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1399_, 0, v_mctx_1385_);
lean_ctor_set(v_reuseFailAlloc_1399_, 1, v_cache_1387_);
lean_ctor_set(v_reuseFailAlloc_1399_, 2, v_zetaDeltaFVarIds_1388_);
lean_ctor_set(v_reuseFailAlloc_1399_, 3, v_postponed_1389_);
lean_ctor_set(v_reuseFailAlloc_1399_, 4, v_diag_1390_);
v___x_1395_ = v_reuseFailAlloc_1399_;
goto v_reusejp_1394_;
}
v_reusejp_1394_:
{
lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; 
v___x_1396_ = lean_st_ref_put(v___y_1378_, v___x_1395_);
v___x_1397_ = lean_box(v_fst_1384_);
v___x_1398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1398_, 0, v___x_1397_);
return v___x_1398_;
}
}
}
v___jp_1402_:
{
lean_object* v_snd_1404_; lean_object* v_fst_1405_; lean_object* v_mctx_1406_; uint8_t v___x_1407_; 
v_snd_1404_ = lean_ctor_get(v___y_1403_, 1);
lean_inc(v_snd_1404_);
v_fst_1405_ = lean_ctor_get(v___y_1403_, 0);
lean_inc(v_fst_1405_);
lean_dec_ref(v___y_1403_);
v_mctx_1406_ = lean_ctor_get(v_snd_1404_, 1);
lean_inc_ref(v_mctx_1406_);
lean_dec(v_snd_1404_);
v___x_1407_ = lean_unbox(v_fst_1405_);
lean_dec(v_fst_1405_);
v_fst_1384_ = v___x_1407_;
v_mctx_1385_ = v_mctx_1406_;
goto v___jp_1383_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2___redArg___boxed(lean_object* v_e_1415_, lean_object* v_fvarId_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_){
_start:
{
lean_object* v_res_1419_; 
v_res_1419_ = l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2___redArg(v_e_1415_, v_fvarId_1416_, v___y_1417_);
lean_dec(v___y_1417_);
return v_res_1419_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2(lean_object* v_e_1420_, lean_object* v_fvarId_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_){
_start:
{
lean_object* v___x_1427_; 
v___x_1427_ = l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2___redArg(v_e_1420_, v_fvarId_1421_, v___y_1423_);
return v___x_1427_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2___boxed(lean_object* v_e_1428_, lean_object* v_fvarId_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_){
_start:
{
lean_object* v_res_1435_; 
v_res_1435_ = l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2(v_e_1428_, v_fvarId_1429_, v___y_1430_, v___y_1431_, v___y_1432_, v___y_1433_);
lean_dec(v___y_1433_);
lean_dec_ref(v___y_1432_);
lean_dec(v___y_1431_);
lean_dec_ref(v___y_1430_);
return v_res_1435_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_Meta_getMajorTypeIndices_spec__0(lean_object* v_a_1436_, lean_object* v_x_1437_){
_start:
{
if (lean_obj_tag(v_x_1437_) == 0)
{
uint8_t v___x_1438_; 
v___x_1438_ = 0;
return v___x_1438_;
}
else
{
lean_object* v_head_1439_; lean_object* v_tail_1440_; uint8_t v___x_1441_; 
v_head_1439_ = lean_ctor_get(v_x_1437_, 0);
v_tail_1440_ = lean_ctor_get(v_x_1437_, 1);
v___x_1441_ = lean_nat_dec_eq(v_a_1436_, v_head_1439_);
if (v___x_1441_ == 0)
{
v_x_1437_ = v_tail_1440_;
goto _start;
}
else
{
return v___x_1441_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_Meta_getMajorTypeIndices_spec__0___boxed(lean_object* v_a_1443_, lean_object* v_x_1444_){
_start:
{
uint8_t v_res_1445_; lean_object* v_r_1446_; 
v_res_1445_ = l_List_elem___at___00Lean_Meta_getMajorTypeIndices_spec__0(v_a_1443_, v_x_1444_);
lean_dec(v_x_1444_);
lean_dec(v_a_1443_);
v_r_1446_ = lean_box(v_res_1445_);
return v_r_1446_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_1448_; lean_object* v___x_1449_; 
v___x_1448_ = ((lean_object*)(l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__0));
v___x_1449_ = l_Lean_stringToMessageData(v___x_1448_);
return v___x_1449_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_1451_; lean_object* v___x_1452_; 
v___x_1451_ = ((lean_object*)(l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__2));
v___x_1452_ = l_Lean_stringToMessageData(v___x_1451_);
return v___x_1452_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__5(void){
_start:
{
lean_object* v___x_1454_; lean_object* v___x_1455_; 
v___x_1454_ = ((lean_object*)(l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__4));
v___x_1455_ = l_Lean_stringToMessageData(v___x_1454_);
return v___x_1455_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__7(void){
_start:
{
lean_object* v___x_1457_; lean_object* v___x_1458_; 
v___x_1457_ = ((lean_object*)(l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__6));
v___x_1458_ = l_Lean_stringToMessageData(v___x_1457_);
return v___x_1458_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg(lean_object* v_majorTypeArgs_1459_, lean_object* v_idxPos_1460_, lean_object* v_recursorInfo_1461_, lean_object* v_idx_1462_, lean_object* v_tacticName_1463_, lean_object* v_mvarId_1464_, lean_object* v_majorType_1465_, lean_object* v_n_1466_, lean_object* v_i_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_){
_start:
{
lean_object* v_zero_1473_; uint8_t v_isZero_1474_; 
v_zero_1473_ = lean_unsigned_to_nat(0u);
v_isZero_1474_ = lean_nat_dec_eq(v_i_1467_, v_zero_1473_);
if (v_isZero_1474_ == 1)
{
lean_object* v___x_1475_; lean_object* v___x_1476_; 
lean_dec(v_i_1467_);
lean_dec_ref(v_majorType_1465_);
lean_dec(v_mvarId_1464_);
lean_dec(v_tacticName_1463_);
lean_dec_ref(v_idx_1462_);
v___x_1475_ = lean_box(0);
v___x_1476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1476_, 0, v___x_1475_);
return v___x_1476_;
}
else
{
lean_object* v_one_1477_; lean_object* v_n_1478_; lean_object* v___y_1480_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v_arg_1484_; lean_object* v___y_1486_; lean_object* v___y_1487_; lean_object* v___y_1488_; lean_object* v___y_1489_; lean_object* v___y_1532_; lean_object* v___y_1533_; lean_object* v___y_1534_; lean_object* v___y_1535_; uint8_t v___x_1556_; 
v_one_1477_ = lean_unsigned_to_nat(1u);
v_n_1478_ = lean_nat_sub(v_i_1467_, v_one_1477_);
lean_dec(v_i_1467_);
v___x_1482_ = lean_nat_sub(v_n_1466_, v_n_1478_);
v___x_1483_ = lean_nat_sub(v___x_1482_, v_one_1477_);
lean_dec(v___x_1482_);
v_arg_1484_ = lean_array_fget_borrowed(v_majorTypeArgs_1459_, v___x_1483_);
v___x_1556_ = lean_nat_dec_eq(v___x_1483_, v_idxPos_1460_);
if (v___x_1556_ == 0)
{
uint8_t v___x_1557_; 
v___x_1557_ = lean_expr_eqv(v_arg_1484_, v_idx_1462_);
if (v___x_1557_ == 0)
{
v___y_1532_ = v___y_1468_;
v___y_1533_ = v___y_1469_;
v___y_1534_ = v___y_1470_;
v___y_1535_ = v___y_1471_;
goto v___jp_1531_;
}
else
{
lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; 
v___x_1558_ = lean_obj_once(&l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1, &l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1_once, _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1);
lean_inc_ref(v_idx_1462_);
v___x_1559_ = l_Lean_MessageData_ofExpr(v_idx_1462_);
v___x_1560_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1560_, 0, v___x_1558_);
lean_ctor_set(v___x_1560_, 1, v___x_1559_);
v___x_1561_ = lean_obj_once(&l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__7, &l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__7_once, _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__7);
v___x_1562_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1562_, 0, v___x_1560_);
lean_ctor_set(v___x_1562_, 1, v___x_1561_);
lean_inc_ref(v_majorType_1465_);
v___x_1563_ = l_Lean_indentExpr(v_majorType_1465_);
v___x_1564_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1564_, 0, v___x_1562_);
lean_ctor_set(v___x_1564_, 1, v___x_1563_);
v___x_1565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1565_, 0, v___x_1564_);
lean_inc(v_mvarId_1464_);
lean_inc(v_tacticName_1463_);
v___x_1566_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1463_, v_mvarId_1464_, v___x_1565_, v___y_1468_, v___y_1469_, v___y_1470_, v___y_1471_);
if (lean_obj_tag(v___x_1566_) == 0)
{
lean_dec_ref_known(v___x_1566_, 1);
v___y_1532_ = v___y_1468_;
v___y_1533_ = v___y_1469_;
v___y_1534_ = v___y_1470_;
v___y_1535_ = v___y_1471_;
goto v___jp_1531_;
}
else
{
lean_dec(v___x_1483_);
v___y_1480_ = v___x_1566_;
goto v___jp_1479_;
}
}
}
else
{
v___y_1532_ = v___y_1468_;
v___y_1533_ = v___y_1469_;
v___y_1534_ = v___y_1470_;
v___y_1535_ = v___y_1471_;
goto v___jp_1531_;
}
v___jp_1479_:
{
if (lean_obj_tag(v___y_1480_) == 0)
{
lean_dec_ref_known(v___y_1480_, 1);
v_i_1467_ = v_n_1478_;
goto _start;
}
else
{
lean_dec(v_n_1478_);
lean_dec_ref(v_majorType_1465_);
lean_dec(v_mvarId_1464_);
lean_dec(v_tacticName_1463_);
lean_dec_ref(v_idx_1462_);
return v___y_1480_;
}
}
v___jp_1485_:
{
uint8_t v___x_1490_; 
v___x_1490_ = lean_nat_dec_lt(v_idxPos_1460_, v___x_1483_);
if (v___x_1490_ == 0)
{
lean_dec(v___x_1483_);
v_i_1467_ = v_n_1478_;
goto _start;
}
else
{
lean_object* v_indicesPos_1492_; uint8_t v___x_1493_; 
v_indicesPos_1492_ = lean_ctor_get(v_recursorInfo_1461_, 6);
v___x_1493_ = l_List_elem___at___00Lean_Meta_getMajorTypeIndices_spec__0(v___x_1483_, v_indicesPos_1492_);
if (v___x_1493_ == 0)
{
lean_dec(v___x_1483_);
v_i_1467_ = v_n_1478_;
goto _start;
}
else
{
uint8_t v___x_1495_; 
v___x_1495_ = l_Lean_Expr_isFVar(v_arg_1484_);
if (v___x_1495_ == 0)
{
lean_dec(v___x_1483_);
v_i_1467_ = v_n_1478_;
goto _start;
}
else
{
lean_object* v___x_1497_; lean_object* v___x_1498_; 
v___x_1497_ = l_Lean_Expr_fvarId_x21(v_idx_1462_);
v___x_1498_ = l_Lean_FVarId_getDecl___redArg(v___x_1497_, v___y_1486_, v___y_1488_, v___y_1489_);
if (lean_obj_tag(v___x_1498_) == 0)
{
lean_object* v_a_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v_a_1502_; lean_object* v___x_1504_; uint8_t v_isShared_1505_; uint8_t v_isSharedCheck_1522_; 
v_a_1499_ = lean_ctor_get(v___x_1498_, 0);
lean_inc(v_a_1499_);
lean_dec_ref_known(v___x_1498_, 1);
v___x_1500_ = l_Lean_Expr_fvarId_x21(v_arg_1484_);
v___x_1501_ = l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg(v_a_1499_, v___x_1500_, v___x_1493_, v___y_1487_);
v_a_1502_ = lean_ctor_get(v___x_1501_, 0);
v_isSharedCheck_1522_ = !lean_is_exclusive(v___x_1501_);
if (v_isSharedCheck_1522_ == 0)
{
v___x_1504_ = v___x_1501_;
v_isShared_1505_ = v_isSharedCheck_1522_;
goto v_resetjp_1503_;
}
else
{
lean_inc(v_a_1502_);
lean_dec(v___x_1501_);
v___x_1504_ = lean_box(0);
v_isShared_1505_ = v_isSharedCheck_1522_;
goto v_resetjp_1503_;
}
v_resetjp_1503_:
{
uint8_t v___x_1506_; 
v___x_1506_ = lean_unbox(v_a_1502_);
lean_dec(v_a_1502_);
if (v___x_1506_ == 0)
{
lean_del_object(v___x_1504_);
lean_dec(v___x_1483_);
v_i_1467_ = v_n_1478_;
goto _start;
}
else
{
lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1516_; 
v___x_1508_ = lean_obj_once(&l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1, &l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1_once, _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1);
lean_inc_ref(v_idx_1462_);
v___x_1509_ = l_Lean_MessageData_ofExpr(v_idx_1462_);
v___x_1510_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1510_, 0, v___x_1508_);
lean_ctor_set(v___x_1510_, 1, v___x_1509_);
v___x_1511_ = lean_obj_once(&l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__3, &l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__3_once, _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__3);
v___x_1512_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1512_, 0, v___x_1510_);
lean_ctor_set(v___x_1512_, 1, v___x_1511_);
v___x_1513_ = lean_nat_add(v___x_1483_, v_one_1477_);
lean_dec(v___x_1483_);
v___x_1514_ = l_Nat_reprFast(v___x_1513_);
if (v_isShared_1505_ == 0)
{
lean_ctor_set_tag(v___x_1504_, 3);
lean_ctor_set(v___x_1504_, 0, v___x_1514_);
v___x_1516_ = v___x_1504_;
goto v_reusejp_1515_;
}
else
{
lean_object* v_reuseFailAlloc_1521_; 
v_reuseFailAlloc_1521_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1521_, 0, v___x_1514_);
v___x_1516_ = v_reuseFailAlloc_1521_;
goto v_reusejp_1515_;
}
v_reusejp_1515_:
{
lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; 
v___x_1517_ = l_Lean_MessageData_ofFormat(v___x_1516_);
v___x_1518_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1518_, 0, v___x_1512_);
lean_ctor_set(v___x_1518_, 1, v___x_1517_);
v___x_1519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1519_, 0, v___x_1518_);
lean_inc(v_mvarId_1464_);
lean_inc(v_tacticName_1463_);
v___x_1520_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1463_, v_mvarId_1464_, v___x_1519_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_);
v___y_1480_ = v___x_1520_;
goto v___jp_1479_;
}
}
}
}
else
{
lean_object* v_a_1523_; lean_object* v___x_1525_; uint8_t v_isShared_1526_; uint8_t v_isSharedCheck_1530_; 
lean_dec(v___x_1483_);
lean_dec(v_n_1478_);
lean_dec_ref(v_majorType_1465_);
lean_dec(v_mvarId_1464_);
lean_dec(v_tacticName_1463_);
lean_dec_ref(v_idx_1462_);
v_a_1523_ = lean_ctor_get(v___x_1498_, 0);
v_isSharedCheck_1530_ = !lean_is_exclusive(v___x_1498_);
if (v_isSharedCheck_1530_ == 0)
{
v___x_1525_ = v___x_1498_;
v_isShared_1526_ = v_isSharedCheck_1530_;
goto v_resetjp_1524_;
}
else
{
lean_inc(v_a_1523_);
lean_dec(v___x_1498_);
v___x_1525_ = lean_box(0);
v_isShared_1526_ = v_isSharedCheck_1530_;
goto v_resetjp_1524_;
}
v_resetjp_1524_:
{
lean_object* v___x_1528_; 
if (v_isShared_1526_ == 0)
{
v___x_1528_ = v___x_1525_;
goto v_reusejp_1527_;
}
else
{
lean_object* v_reuseFailAlloc_1529_; 
v_reuseFailAlloc_1529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1529_, 0, v_a_1523_);
v___x_1528_ = v_reuseFailAlloc_1529_;
goto v_reusejp_1527_;
}
v_reusejp_1527_:
{
return v___x_1528_;
}
}
}
}
}
}
}
v___jp_1531_:
{
uint8_t v___x_1536_; 
v___x_1536_ = lean_nat_dec_lt(v___x_1483_, v_idxPos_1460_);
if (v___x_1536_ == 0)
{
v___y_1486_ = v___y_1532_;
v___y_1487_ = v___y_1533_;
v___y_1488_ = v___y_1534_;
v___y_1489_ = v___y_1535_;
goto v___jp_1485_;
}
else
{
lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v_a_1539_; lean_object* v___x_1541_; uint8_t v_isShared_1542_; uint8_t v_isSharedCheck_1555_; 
v___x_1537_ = l_Lean_Expr_fvarId_x21(v_idx_1462_);
lean_inc(v_arg_1484_);
v___x_1538_ = l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2___redArg(v_arg_1484_, v___x_1537_, v___y_1533_);
v_a_1539_ = lean_ctor_get(v___x_1538_, 0);
v_isSharedCheck_1555_ = !lean_is_exclusive(v___x_1538_);
if (v_isSharedCheck_1555_ == 0)
{
v___x_1541_ = v___x_1538_;
v_isShared_1542_ = v_isSharedCheck_1555_;
goto v_resetjp_1540_;
}
else
{
lean_inc(v_a_1539_);
lean_dec(v___x_1538_);
v___x_1541_ = lean_box(0);
v_isShared_1542_ = v_isSharedCheck_1555_;
goto v_resetjp_1540_;
}
v_resetjp_1540_:
{
uint8_t v___x_1543_; 
v___x_1543_ = lean_unbox(v_a_1539_);
lean_dec(v_a_1539_);
if (v___x_1543_ == 0)
{
lean_del_object(v___x_1541_);
v___y_1486_ = v___y_1532_;
v___y_1487_ = v___y_1533_;
v___y_1488_ = v___y_1534_;
v___y_1489_ = v___y_1535_;
goto v___jp_1485_;
}
else
{
lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1552_; 
v___x_1544_ = lean_obj_once(&l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1, &l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1_once, _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1);
lean_inc_ref(v_idx_1462_);
v___x_1545_ = l_Lean_MessageData_ofExpr(v_idx_1462_);
v___x_1546_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1546_, 0, v___x_1544_);
lean_ctor_set(v___x_1546_, 1, v___x_1545_);
v___x_1547_ = lean_obj_once(&l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__5, &l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__5_once, _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__5);
v___x_1548_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1548_, 0, v___x_1546_);
lean_ctor_set(v___x_1548_, 1, v___x_1547_);
lean_inc_ref(v_majorType_1465_);
v___x_1549_ = l_Lean_indentExpr(v_majorType_1465_);
v___x_1550_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1550_, 0, v___x_1548_);
lean_ctor_set(v___x_1550_, 1, v___x_1549_);
if (v_isShared_1542_ == 0)
{
lean_ctor_set_tag(v___x_1541_, 1);
lean_ctor_set(v___x_1541_, 0, v___x_1550_);
v___x_1552_ = v___x_1541_;
goto v_reusejp_1551_;
}
else
{
lean_object* v_reuseFailAlloc_1554_; 
v_reuseFailAlloc_1554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1554_, 0, v___x_1550_);
v___x_1552_ = v_reuseFailAlloc_1554_;
goto v_reusejp_1551_;
}
v_reusejp_1551_:
{
lean_object* v___x_1553_; 
lean_inc(v_mvarId_1464_);
lean_inc(v_tacticName_1463_);
v___x_1553_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1463_, v_mvarId_1464_, v___x_1552_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_);
if (lean_obj_tag(v___x_1553_) == 0)
{
lean_dec_ref_known(v___x_1553_, 1);
v___y_1486_ = v___y_1532_;
v___y_1487_ = v___y_1533_;
v___y_1488_ = v___y_1534_;
v___y_1489_ = v___y_1535_;
goto v___jp_1485_;
}
else
{
lean_dec(v___x_1483_);
v___y_1480_ = v___x_1553_;
goto v___jp_1479_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___boxed(lean_object* v_majorTypeArgs_1567_, lean_object* v_idxPos_1568_, lean_object* v_recursorInfo_1569_, lean_object* v_idx_1570_, lean_object* v_tacticName_1571_, lean_object* v_mvarId_1572_, lean_object* v_majorType_1573_, lean_object* v_n_1574_, lean_object* v_i_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_){
_start:
{
lean_object* v_res_1581_; 
v_res_1581_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg(v_majorTypeArgs_1567_, v_idxPos_1568_, v_recursorInfo_1569_, v_idx_1570_, v_tacticName_1571_, v_mvarId_1572_, v_majorType_1573_, v_n_1574_, v_i_1575_, v___y_1576_, v___y_1577_, v___y_1578_, v___y_1579_);
lean_dec(v___y_1579_);
lean_dec_ref(v___y_1578_);
lean_dec(v___y_1577_);
lean_dec_ref(v___y_1576_);
lean_dec(v_n_1574_);
lean_dec_ref(v_recursorInfo_1569_);
lean_dec(v_idxPos_1568_);
lean_dec_ref(v_majorTypeArgs_1567_);
return v_res_1581_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__1(void){
_start:
{
lean_object* v___x_1583_; lean_object* v___x_1584_; 
v___x_1583_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__0));
v___x_1584_ = l_Lean_stringToMessageData(v___x_1583_);
return v___x_1584_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__3(void){
_start:
{
lean_object* v___x_1586_; lean_object* v___x_1587_; 
v___x_1586_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__2));
v___x_1587_ = l_Lean_stringToMessageData(v___x_1586_);
return v___x_1587_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__5(void){
_start:
{
lean_object* v___x_1589_; lean_object* v___x_1590_; 
v___x_1589_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__4));
v___x_1590_ = l_Lean_stringToMessageData(v___x_1589_);
return v___x_1590_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4(lean_object* v_majorTypeArgs_1591_, lean_object* v_recursorInfo_1592_, lean_object* v_tacticName_1593_, lean_object* v_mvarId_1594_, lean_object* v_majorType_1595_, size_t v_sz_1596_, size_t v_i_1597_, lean_object* v_bs_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_){
_start:
{
uint8_t v___x_1604_; 
v___x_1604_ = lean_usize_dec_lt(v_i_1597_, v_sz_1596_);
if (v___x_1604_ == 0)
{
lean_object* v___x_1605_; 
lean_dec_ref(v_majorType_1595_);
lean_dec(v_mvarId_1594_);
lean_dec(v_tacticName_1593_);
v___x_1605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1605_, 0, v_bs_1598_);
return v___x_1605_;
}
else
{
lean_object* v_v_1606_; lean_object* v___x_1607_; lean_object* v_bs_x27_1608_; lean_object* v_a_1610_; lean_object* v___x_1615_; uint8_t v___x_1616_; 
v_v_1606_ = lean_array_uget(v_bs_1598_, v_i_1597_);
v___x_1607_ = lean_unsigned_to_nat(0u);
v_bs_x27_1608_ = lean_array_uset(v_bs_1598_, v_i_1597_, v___x_1607_);
v___x_1615_ = lean_array_get_size(v_majorTypeArgs_1591_);
v___x_1616_ = lean_nat_dec_le(v___x_1615_, v_v_1606_);
if (v___x_1616_ == 0)
{
lean_object* v_idx_1617_; lean_object* v___y_1619_; lean_object* v___y_1620_; lean_object* v___y_1621_; lean_object* v___y_1622_; uint8_t v___x_1632_; 
v_idx_1617_ = lean_array_fget_borrowed(v_majorTypeArgs_1591_, v_v_1606_);
v___x_1632_ = l_Lean_Expr_isFVar(v_idx_1617_);
if (v___x_1632_ == 0)
{
lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; 
v___x_1633_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__1);
lean_inc(v_idx_1617_);
v___x_1634_ = l_Lean_MessageData_ofExpr(v_idx_1617_);
v___x_1635_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1635_, 0, v___x_1633_);
lean_ctor_set(v___x_1635_, 1, v___x_1634_);
v___x_1636_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__3);
v___x_1637_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1637_, 0, v___x_1635_);
lean_ctor_set(v___x_1637_, 1, v___x_1636_);
lean_inc_ref(v_majorType_1595_);
v___x_1638_ = l_Lean_indentExpr(v_majorType_1595_);
v___x_1639_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1639_, 0, v___x_1637_);
lean_ctor_set(v___x_1639_, 1, v___x_1638_);
v___x_1640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1640_, 0, v___x_1639_);
lean_inc(v_mvarId_1594_);
lean_inc(v_tacticName_1593_);
v___x_1641_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1593_, v_mvarId_1594_, v___x_1640_, v___y_1599_, v___y_1600_, v___y_1601_, v___y_1602_);
if (lean_obj_tag(v___x_1641_) == 0)
{
lean_dec_ref_known(v___x_1641_, 1);
v___y_1619_ = v___y_1599_;
v___y_1620_ = v___y_1600_;
v___y_1621_ = v___y_1601_;
v___y_1622_ = v___y_1602_;
goto v___jp_1618_;
}
else
{
lean_object* v_a_1642_; lean_object* v___x_1644_; uint8_t v_isShared_1645_; uint8_t v_isSharedCheck_1649_; 
lean_dec_ref(v_bs_x27_1608_);
lean_dec(v_v_1606_);
lean_dec_ref(v_majorType_1595_);
lean_dec(v_mvarId_1594_);
lean_dec(v_tacticName_1593_);
v_a_1642_ = lean_ctor_get(v___x_1641_, 0);
v_isSharedCheck_1649_ = !lean_is_exclusive(v___x_1641_);
if (v_isSharedCheck_1649_ == 0)
{
v___x_1644_ = v___x_1641_;
v_isShared_1645_ = v_isSharedCheck_1649_;
goto v_resetjp_1643_;
}
else
{
lean_inc(v_a_1642_);
lean_dec(v___x_1641_);
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
else
{
v___y_1619_ = v___y_1599_;
v___y_1620_ = v___y_1600_;
v___y_1621_ = v___y_1601_;
v___y_1622_ = v___y_1602_;
goto v___jp_1618_;
}
v___jp_1618_:
{
lean_object* v___x_1623_; 
lean_inc_ref(v_majorType_1595_);
lean_inc(v_mvarId_1594_);
lean_inc(v_tacticName_1593_);
lean_inc(v_idx_1617_);
v___x_1623_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg(v_majorTypeArgs_1591_, v_v_1606_, v_recursorInfo_1592_, v_idx_1617_, v_tacticName_1593_, v_mvarId_1594_, v_majorType_1595_, v___x_1615_, v___x_1615_, v___y_1619_, v___y_1620_, v___y_1621_, v___y_1622_);
lean_dec(v_v_1606_);
if (lean_obj_tag(v___x_1623_) == 0)
{
lean_dec_ref_known(v___x_1623_, 1);
lean_inc(v_idx_1617_);
v_a_1610_ = v_idx_1617_;
goto v___jp_1609_;
}
else
{
lean_object* v_a_1624_; lean_object* v___x_1626_; uint8_t v_isShared_1627_; uint8_t v_isSharedCheck_1631_; 
lean_dec_ref(v_bs_x27_1608_);
lean_dec_ref(v_majorType_1595_);
lean_dec(v_mvarId_1594_);
lean_dec(v_tacticName_1593_);
v_a_1624_ = lean_ctor_get(v___x_1623_, 0);
v_isSharedCheck_1631_ = !lean_is_exclusive(v___x_1623_);
if (v_isSharedCheck_1631_ == 0)
{
v___x_1626_ = v___x_1623_;
v_isShared_1627_ = v_isSharedCheck_1631_;
goto v_resetjp_1625_;
}
else
{
lean_inc(v_a_1624_);
lean_dec(v___x_1623_);
v___x_1626_ = lean_box(0);
v_isShared_1627_ = v_isSharedCheck_1631_;
goto v_resetjp_1625_;
}
v_resetjp_1625_:
{
lean_object* v___x_1629_; 
if (v_isShared_1627_ == 0)
{
v___x_1629_ = v___x_1626_;
goto v_reusejp_1628_;
}
else
{
lean_object* v_reuseFailAlloc_1630_; 
v_reuseFailAlloc_1630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1630_, 0, v_a_1624_);
v___x_1629_ = v_reuseFailAlloc_1630_;
goto v_reusejp_1628_;
}
v_reusejp_1628_:
{
return v___x_1629_;
}
}
}
}
}
else
{
lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; 
lean_dec(v_v_1606_);
v___x_1650_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__5, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__5);
lean_inc_ref(v_majorType_1595_);
v___x_1651_ = l_Lean_indentExpr(v_majorType_1595_);
v___x_1652_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1652_, 0, v___x_1650_);
lean_ctor_set(v___x_1652_, 1, v___x_1651_);
v___x_1653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1653_, 0, v___x_1652_);
lean_inc(v_mvarId_1594_);
lean_inc(v_tacticName_1593_);
v___x_1654_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1593_, v_mvarId_1594_, v___x_1653_, v___y_1599_, v___y_1600_, v___y_1601_, v___y_1602_);
if (lean_obj_tag(v___x_1654_) == 0)
{
lean_object* v_a_1655_; 
v_a_1655_ = lean_ctor_get(v___x_1654_, 0);
lean_inc(v_a_1655_);
lean_dec_ref_known(v___x_1654_, 1);
v_a_1610_ = v_a_1655_;
goto v___jp_1609_;
}
else
{
lean_object* v_a_1656_; lean_object* v___x_1658_; uint8_t v_isShared_1659_; uint8_t v_isSharedCheck_1663_; 
lean_dec_ref(v_bs_x27_1608_);
lean_dec_ref(v_majorType_1595_);
lean_dec(v_mvarId_1594_);
lean_dec(v_tacticName_1593_);
v_a_1656_ = lean_ctor_get(v___x_1654_, 0);
v_isSharedCheck_1663_ = !lean_is_exclusive(v___x_1654_);
if (v_isSharedCheck_1663_ == 0)
{
v___x_1658_ = v___x_1654_;
v_isShared_1659_ = v_isSharedCheck_1663_;
goto v_resetjp_1657_;
}
else
{
lean_inc(v_a_1656_);
lean_dec(v___x_1654_);
v___x_1658_ = lean_box(0);
v_isShared_1659_ = v_isSharedCheck_1663_;
goto v_resetjp_1657_;
}
v_resetjp_1657_:
{
lean_object* v___x_1661_; 
if (v_isShared_1659_ == 0)
{
v___x_1661_ = v___x_1658_;
goto v_reusejp_1660_;
}
else
{
lean_object* v_reuseFailAlloc_1662_; 
v_reuseFailAlloc_1662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1662_, 0, v_a_1656_);
v___x_1661_ = v_reuseFailAlloc_1662_;
goto v_reusejp_1660_;
}
v_reusejp_1660_:
{
return v___x_1661_;
}
}
}
}
v___jp_1609_:
{
size_t v___x_1611_; size_t v___x_1612_; lean_object* v___x_1613_; 
v___x_1611_ = ((size_t)1ULL);
v___x_1612_ = lean_usize_add(v_i_1597_, v___x_1611_);
v___x_1613_ = lean_array_uset(v_bs_x27_1608_, v_i_1597_, v_a_1610_);
v_i_1597_ = v___x_1612_;
v_bs_1598_ = v___x_1613_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___boxed(lean_object* v_majorTypeArgs_1664_, lean_object* v_recursorInfo_1665_, lean_object* v_tacticName_1666_, lean_object* v_mvarId_1667_, lean_object* v_majorType_1668_, lean_object* v_sz_1669_, lean_object* v_i_1670_, lean_object* v_bs_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_){
_start:
{
size_t v_sz_boxed_1677_; size_t v_i_boxed_1678_; lean_object* v_res_1679_; 
v_sz_boxed_1677_ = lean_unbox_usize(v_sz_1669_);
lean_dec(v_sz_1669_);
v_i_boxed_1678_ = lean_unbox_usize(v_i_1670_);
lean_dec(v_i_1670_);
v_res_1679_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4(v_majorTypeArgs_1664_, v_recursorInfo_1665_, v_tacticName_1666_, v_mvarId_1667_, v_majorType_1668_, v_sz_boxed_1677_, v_i_boxed_1678_, v_bs_1671_, v___y_1672_, v___y_1673_, v___y_1674_, v___y_1675_);
lean_dec(v___y_1675_);
lean_dec_ref(v___y_1674_);
lean_dec(v___y_1673_);
lean_dec_ref(v___y_1672_);
lean_dec_ref(v_recursorInfo_1665_);
lean_dec_ref(v_majorTypeArgs_1664_);
return v_res_1679_;
}
}
static lean_object* _init_l_Lean_Meta_getMajorTypeIndices___closed__0(void){
_start:
{
lean_object* v___x_1680_; lean_object* v_dummy_1681_; 
v___x_1680_ = lean_box(0);
v_dummy_1681_ = l_Lean_Expr_sort___override(v___x_1680_);
return v_dummy_1681_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMajorTypeIndices(lean_object* v_mvarId_1682_, lean_object* v_tacticName_1683_, lean_object* v_recursorInfo_1684_, lean_object* v_majorType_1685_, lean_object* v_a_1686_, lean_object* v_a_1687_, lean_object* v_a_1688_, lean_object* v_a_1689_){
_start:
{
lean_object* v_indicesPos_1691_; lean_object* v_nargs_1692_; lean_object* v_dummy_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v_majorTypeArgs_1697_; lean_object* v___x_1698_; size_t v_sz_1699_; size_t v___x_1700_; lean_object* v___x_1701_; 
v_indicesPos_1691_ = lean_ctor_get(v_recursorInfo_1684_, 6);
v_nargs_1692_ = l_Lean_Expr_getAppNumArgs(v_majorType_1685_);
v_dummy_1693_ = lean_obj_once(&l_Lean_Meta_getMajorTypeIndices___closed__0, &l_Lean_Meta_getMajorTypeIndices___closed__0_once, _init_l_Lean_Meta_getMajorTypeIndices___closed__0);
lean_inc(v_nargs_1692_);
v___x_1694_ = lean_mk_array(v_nargs_1692_, v_dummy_1693_);
v___x_1695_ = lean_unsigned_to_nat(1u);
v___x_1696_ = lean_nat_sub(v_nargs_1692_, v___x_1695_);
lean_dec(v_nargs_1692_);
lean_inc_ref(v_majorType_1685_);
v_majorTypeArgs_1697_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_majorType_1685_, v___x_1694_, v___x_1696_);
lean_inc(v_indicesPos_1691_);
v___x_1698_ = lean_array_mk(v_indicesPos_1691_);
v_sz_1699_ = lean_array_size(v___x_1698_);
v___x_1700_ = ((size_t)0ULL);
v___x_1701_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4(v_majorTypeArgs_1697_, v_recursorInfo_1684_, v_tacticName_1683_, v_mvarId_1682_, v_majorType_1685_, v_sz_1699_, v___x_1700_, v___x_1698_, v_a_1686_, v_a_1687_, v_a_1688_, v_a_1689_);
lean_dec_ref(v_recursorInfo_1684_);
lean_dec_ref(v_majorTypeArgs_1697_);
return v___x_1701_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMajorTypeIndices___boxed(lean_object* v_mvarId_1702_, lean_object* v_tacticName_1703_, lean_object* v_recursorInfo_1704_, lean_object* v_majorType_1705_, lean_object* v_a_1706_, lean_object* v_a_1707_, lean_object* v_a_1708_, lean_object* v_a_1709_, lean_object* v_a_1710_){
_start:
{
lean_object* v_res_1711_; 
v_res_1711_ = l_Lean_Meta_getMajorTypeIndices(v_mvarId_1702_, v_tacticName_1703_, v_recursorInfo_1704_, v_majorType_1705_, v_a_1706_, v_a_1707_, v_a_1708_, v_a_1709_);
lean_dec(v_a_1709_);
lean_dec_ref(v_a_1708_);
lean_dec(v_a_1707_);
lean_dec_ref(v_a_1706_);
return v_res_1711_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3(lean_object* v_majorTypeArgs_1712_, lean_object* v_idxPos_1713_, lean_object* v_recursorInfo_1714_, lean_object* v_idx_1715_, lean_object* v_tacticName_1716_, lean_object* v_mvarId_1717_, lean_object* v_majorType_1718_, lean_object* v_n_1719_, lean_object* v_i_1720_, lean_object* v_a_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_){
_start:
{
lean_object* v___x_1727_; 
v___x_1727_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg(v_majorTypeArgs_1712_, v_idxPos_1713_, v_recursorInfo_1714_, v_idx_1715_, v_tacticName_1716_, v_mvarId_1717_, v_majorType_1718_, v_n_1719_, v_i_1720_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_);
return v___x_1727_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___boxed(lean_object* v_majorTypeArgs_1728_, lean_object* v_idxPos_1729_, lean_object* v_recursorInfo_1730_, lean_object* v_idx_1731_, lean_object* v_tacticName_1732_, lean_object* v_mvarId_1733_, lean_object* v_majorType_1734_, lean_object* v_n_1735_, lean_object* v_i_1736_, lean_object* v_a_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_){
_start:
{
lean_object* v_res_1743_; 
v_res_1743_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3(v_majorTypeArgs_1728_, v_idxPos_1729_, v_recursorInfo_1730_, v_idx_1731_, v_tacticName_1732_, v_mvarId_1733_, v_majorType_1734_, v_n_1735_, v_i_1736_, v_a_1737_, v___y_1738_, v___y_1739_, v___y_1740_, v___y_1741_);
lean_dec(v___y_1741_);
lean_dec_ref(v___y_1740_);
lean_dec(v___y_1739_);
lean_dec_ref(v___y_1738_);
lean_dec(v_n_1735_);
lean_dec_ref(v_recursorInfo_1730_);
lean_dec(v_idxPos_1729_);
lean_dec_ref(v_majorTypeArgs_1728_);
return v_res_1743_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1___redArg(lean_object* v_name_1744_, lean_object* v_msg_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_){
_start:
{
lean_object* v_ref_1751_; lean_object* v_msg_1752_; lean_object* v___x_1753_; lean_object* v_a_1754_; lean_object* v___x_1756_; uint8_t v_isShared_1757_; uint8_t v_isSharedCheck_1762_; 
v_ref_1751_ = lean_ctor_get(v___y_1748_, 2);
v_msg_1752_ = l_Lean_MessageData_tagWithErrorName(v_msg_1745_, v_name_1744_);
v___x_1753_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1_spec__2(v_msg_1752_, v___y_1746_, v___y_1747_, v___y_1748_, v___y_1749_);
v_a_1754_ = lean_ctor_get(v___x_1753_, 0);
v_isSharedCheck_1762_ = !lean_is_exclusive(v___x_1753_);
if (v_isSharedCheck_1762_ == 0)
{
v___x_1756_ = v___x_1753_;
v_isShared_1757_ = v_isSharedCheck_1762_;
goto v_resetjp_1755_;
}
else
{
lean_inc(v_a_1754_);
lean_dec(v___x_1753_);
v___x_1756_ = lean_box(0);
v_isShared_1757_ = v_isSharedCheck_1762_;
goto v_resetjp_1755_;
}
v_resetjp_1755_:
{
lean_object* v___x_1758_; lean_object* v___x_1760_; 
lean_inc(v_ref_1751_);
v___x_1758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1758_, 0, v_ref_1751_);
lean_ctor_set(v___x_1758_, 1, v_a_1754_);
if (v_isShared_1757_ == 0)
{
lean_ctor_set_tag(v___x_1756_, 1);
lean_ctor_set(v___x_1756_, 0, v___x_1758_);
v___x_1760_ = v___x_1756_;
goto v_reusejp_1759_;
}
else
{
lean_object* v_reuseFailAlloc_1761_; 
v_reuseFailAlloc_1761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1761_, 0, v___x_1758_);
v___x_1760_ = v_reuseFailAlloc_1761_;
goto v_reusejp_1759_;
}
v_reusejp_1759_:
{
return v___x_1760_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1___redArg___boxed(lean_object* v_name_1763_, lean_object* v_msg_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_){
_start:
{
lean_object* v_res_1770_; 
v_res_1770_ = l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1___redArg(v_name_1763_, v_msg_1764_, v___y_1765_, v___y_1766_, v___y_1767_, v___y_1768_);
lean_dec(v___y_1768_);
lean_dec_ref(v___y_1767_);
lean_dec(v___y_1766_);
lean_dec_ref(v___y_1765_);
return v_res_1770_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Meta_mkRecursorAppPrefix_spec__0(lean_object* v_a_1771_, lean_object* v___x_1772_, lean_object* v_tacticName_1773_, lean_object* v_mvarId_1774_, lean_object* v_x_1775_, lean_object* v_x_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_){
_start:
{
if (lean_obj_tag(v_x_1776_) == 0)
{
lean_object* v___x_1782_; 
lean_dec(v_mvarId_1774_);
lean_dec(v_tacticName_1773_);
lean_dec(v_a_1771_);
v___x_1782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1782_, 0, v_x_1775_);
return v___x_1782_;
}
else
{
lean_object* v_head_1783_; 
v_head_1783_ = lean_ctor_get(v_x_1776_, 0);
if (lean_obj_tag(v_head_1783_) == 0)
{
lean_object* v_tail_1784_; lean_object* v_fst_1785_; lean_object* v___x_1787_; uint8_t v_isShared_1788_; uint8_t v_isSharedCheck_1796_; 
v_tail_1784_ = lean_ctor_get(v_x_1776_, 1);
v_fst_1785_ = lean_ctor_get(v_x_1775_, 0);
v_isSharedCheck_1796_ = !lean_is_exclusive(v_x_1775_);
if (v_isSharedCheck_1796_ == 0)
{
lean_object* v_unused_1797_; 
v_unused_1797_ = lean_ctor_get(v_x_1775_, 1);
lean_dec(v_unused_1797_);
v___x_1787_ = v_x_1775_;
v_isShared_1788_ = v_isSharedCheck_1796_;
goto v_resetjp_1786_;
}
else
{
lean_inc(v_fst_1785_);
lean_dec(v_x_1775_);
v___x_1787_ = lean_box(0);
v_isShared_1788_ = v_isSharedCheck_1796_;
goto v_resetjp_1786_;
}
v_resetjp_1786_:
{
lean_object* v___x_1789_; uint8_t v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1793_; 
lean_inc(v_a_1771_);
v___x_1789_ = lean_array_push(v_fst_1785_, v_a_1771_);
v___x_1790_ = 1;
v___x_1791_ = lean_box(v___x_1790_);
if (v_isShared_1788_ == 0)
{
lean_ctor_set(v___x_1787_, 1, v___x_1791_);
lean_ctor_set(v___x_1787_, 0, v___x_1789_);
v___x_1793_ = v___x_1787_;
goto v_reusejp_1792_;
}
else
{
lean_object* v_reuseFailAlloc_1795_; 
v_reuseFailAlloc_1795_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1795_, 0, v___x_1789_);
lean_ctor_set(v_reuseFailAlloc_1795_, 1, v___x_1791_);
v___x_1793_ = v_reuseFailAlloc_1795_;
goto v_reusejp_1792_;
}
v_reusejp_1792_:
{
v_x_1775_ = v___x_1793_;
v_x_1776_ = v_tail_1784_;
goto _start;
}
}
}
else
{
lean_object* v_tail_1798_; lean_object* v_fst_1799_; lean_object* v_snd_1800_; lean_object* v___x_1802_; uint8_t v_isShared_1803_; uint8_t v_isSharedCheck_1817_; 
v_tail_1798_ = lean_ctor_get(v_x_1776_, 1);
v_fst_1799_ = lean_ctor_get(v_x_1775_, 0);
v_snd_1800_ = lean_ctor_get(v_x_1775_, 1);
v_isSharedCheck_1817_ = !lean_is_exclusive(v_x_1775_);
if (v_isSharedCheck_1817_ == 0)
{
v___x_1802_ = v_x_1775_;
v_isShared_1803_ = v_isSharedCheck_1817_;
goto v_resetjp_1801_;
}
else
{
lean_inc(v_snd_1800_);
lean_inc(v_fst_1799_);
lean_dec(v_x_1775_);
v___x_1802_ = lean_box(0);
v_isShared_1803_ = v_isSharedCheck_1817_;
goto v_resetjp_1801_;
}
v_resetjp_1801_:
{
lean_object* v_idx_1804_; lean_object* v___x_1805_; uint8_t v___x_1806_; 
v_idx_1804_ = lean_ctor_get(v_head_1783_, 0);
v___x_1805_ = lean_array_get_size(v___x_1772_);
v___x_1806_ = lean_nat_dec_le(v___x_1805_, v_idx_1804_);
if (v___x_1806_ == 0)
{
lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1810_; 
v___x_1807_ = lean_array_fget_borrowed(v___x_1772_, v_idx_1804_);
lean_inc(v___x_1807_);
v___x_1808_ = lean_array_push(v_fst_1799_, v___x_1807_);
if (v_isShared_1803_ == 0)
{
lean_ctor_set(v___x_1802_, 0, v___x_1808_);
v___x_1810_ = v___x_1802_;
goto v_reusejp_1809_;
}
else
{
lean_object* v_reuseFailAlloc_1812_; 
v_reuseFailAlloc_1812_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1812_, 0, v___x_1808_);
lean_ctor_set(v_reuseFailAlloc_1812_, 1, v_snd_1800_);
v___x_1810_ = v_reuseFailAlloc_1812_;
goto v_reusejp_1809_;
}
v_reusejp_1809_:
{
v_x_1775_ = v___x_1810_;
v_x_1776_ = v_tail_1798_;
goto _start;
}
}
else
{
lean_object* v___x_1813_; lean_object* v___x_1814_; 
lean_del_object(v___x_1802_);
lean_dec(v_snd_1800_);
lean_dec(v_fst_1799_);
v___x_1813_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9);
lean_inc(v_mvarId_1774_);
lean_inc(v_tacticName_1773_);
v___x_1814_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1773_, v_mvarId_1774_, v___x_1813_, v___y_1777_, v___y_1778_, v___y_1779_, v___y_1780_);
if (lean_obj_tag(v___x_1814_) == 0)
{
lean_object* v_a_1815_; 
v_a_1815_ = lean_ctor_get(v___x_1814_, 0);
lean_inc(v_a_1815_);
lean_dec_ref_known(v___x_1814_, 1);
v_x_1775_ = v_a_1815_;
v_x_1776_ = v_tail_1798_;
goto _start;
}
else
{
lean_dec(v_mvarId_1774_);
lean_dec(v_tacticName_1773_);
lean_dec(v_a_1771_);
return v___x_1814_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Meta_mkRecursorAppPrefix_spec__0___boxed(lean_object* v_a_1818_, lean_object* v___x_1819_, lean_object* v_tacticName_1820_, lean_object* v_mvarId_1821_, lean_object* v_x_1822_, lean_object* v_x_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_){
_start:
{
lean_object* v_res_1829_; 
v_res_1829_ = l_List_foldlM___at___00Lean_Meta_mkRecursorAppPrefix_spec__0(v_a_1818_, v___x_1819_, v_tacticName_1820_, v_mvarId_1821_, v_x_1822_, v_x_1823_, v___y_1824_, v___y_1825_, v___y_1826_, v___y_1827_);
lean_dec(v___y_1827_);
lean_dec_ref(v___y_1826_);
lean_dec(v___y_1825_);
lean_dec_ref(v___y_1824_);
lean_dec(v_x_1823_);
lean_dec_ref(v___x_1819_);
return v_res_1829_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__8(void){
_start:
{
lean_object* v___x_1845_; lean_object* v___x_1846_; 
v___x_1845_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__7));
v___x_1846_ = l_Lean_stringToMessageData(v___x_1845_);
return v___x_1846_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__10(void){
_start:
{
lean_object* v___x_1848_; lean_object* v___x_1849_; 
v___x_1848_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__9));
v___x_1849_ = l_Lean_stringToMessageData(v___x_1848_);
return v___x_1849_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__13(void){
_start:
{
lean_object* v___x_1853_; lean_object* v___x_1854_; 
v___x_1853_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__12));
v___x_1854_ = l_Lean_MessageData_ofFormat(v___x_1853_);
return v___x_1854_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__14(void){
_start:
{
lean_object* v___x_1855_; lean_object* v___x_1856_; 
v___x_1855_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__13, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__13_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__13);
v___x_1856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1856_, 0, v___x_1855_);
return v___x_1856_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2(lean_object* v_recursorInfo_1857_, lean_object* v_a_1858_, lean_object* v_tacticName_1859_, lean_object* v_mvarId_1860_, lean_object* v_indices_1861_, lean_object* v_a_1862_, lean_object* v_major_1863_, lean_object* v_x_1864_, lean_object* v_x_1865_, lean_object* v_x_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_){
_start:
{
if (lean_obj_tag(v_x_1864_) == 5)
{
lean_object* v_fn_1872_; lean_object* v_arg_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; 
v_fn_1872_ = lean_ctor_get(v_x_1864_, 0);
lean_inc_ref(v_fn_1872_);
v_arg_1873_ = lean_ctor_get(v_x_1864_, 1);
lean_inc_ref(v_arg_1873_);
lean_dec_ref_known(v_x_1864_, 2);
v___x_1874_ = lean_array_set(v_x_1865_, v_x_1866_, v_arg_1873_);
v___x_1875_ = lean_unsigned_to_nat(1u);
v___x_1876_ = lean_nat_sub(v_x_1866_, v___x_1875_);
lean_dec(v_x_1866_);
v_x_1864_ = v_fn_1872_;
v_x_1865_ = v___x_1874_;
v_x_1866_ = v___x_1876_;
goto _start;
}
else
{
lean_dec(v_x_1866_);
if (lean_obj_tag(v_x_1864_) == 4)
{
lean_object* v_us_1878_; lean_object* v_recursorName_1879_; lean_object* v_univLevelPos_1880_; uint8_t v_depElim_1881_; lean_object* v_paramsPos_1882_; lean_object* v___x_1883_; uint8_t v___x_1884_; lean_object* v___y_1886_; lean_object* v_motive_1887_; lean_object* v___y_1888_; lean_object* v___y_1889_; lean_object* v___y_1890_; lean_object* v___y_1891_; lean_object* v___x_1904_; lean_object* v___x_1905_; 
v_us_1878_ = lean_ctor_get(v_x_1864_, 1);
lean_inc(v_us_1878_);
lean_dec_ref_known(v_x_1864_, 2);
v_recursorName_1879_ = lean_ctor_get(v_recursorInfo_1857_, 0);
lean_inc(v_recursorName_1879_);
v_univLevelPos_1880_ = lean_ctor_get(v_recursorInfo_1857_, 2);
lean_inc(v_univLevelPos_1880_);
v_depElim_1881_ = lean_ctor_get_uint8(v_recursorInfo_1857_, sizeof(void*)*8);
v_paramsPos_1882_ = lean_ctor_get(v_recursorInfo_1857_, 5);
lean_inc(v_paramsPos_1882_);
lean_dec_ref(v_recursorInfo_1857_);
v___x_1883_ = lean_array_mk(v_us_1878_);
v___x_1884_ = 0;
v___x_1904_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__1));
lean_inc(v_mvarId_1860_);
lean_inc(v_tacticName_1859_);
lean_inc(v_a_1858_);
v___x_1905_ = l_List_foldlM___at___00Lean_Meta_mkRecursorAppPrefix_spec__0(v_a_1858_, v___x_1883_, v_tacticName_1859_, v_mvarId_1860_, v___x_1904_, v_univLevelPos_1880_, v___y_1867_, v___y_1868_, v___y_1869_, v___y_1870_);
lean_dec(v_univLevelPos_1880_);
lean_dec_ref(v___x_1883_);
if (lean_obj_tag(v___x_1905_) == 0)
{
lean_object* v_a_1906_; lean_object* v_fst_1907_; lean_object* v_snd_1908_; lean_object* v___x_1910_; uint8_t v_isShared_1911_; uint8_t v_isSharedCheck_1952_; 
v_a_1906_ = lean_ctor_get(v___x_1905_, 0);
lean_inc(v_a_1906_);
lean_dec_ref_known(v___x_1905_, 1);
v_fst_1907_ = lean_ctor_get(v_a_1906_, 0);
v_snd_1908_ = lean_ctor_get(v_a_1906_, 1);
v_isSharedCheck_1952_ = !lean_is_exclusive(v_a_1906_);
if (v_isSharedCheck_1952_ == 0)
{
v___x_1910_ = v_a_1906_;
v_isShared_1911_ = v_isSharedCheck_1952_;
goto v_resetjp_1909_;
}
else
{
lean_inc(v_snd_1908_);
lean_inc(v_fst_1907_);
lean_dec(v_a_1906_);
v___x_1910_ = lean_box(0);
v_isShared_1911_ = v_isSharedCheck_1952_;
goto v_resetjp_1909_;
}
v_resetjp_1909_:
{
lean_object* v___y_1913_; lean_object* v___y_1914_; lean_object* v___y_1915_; lean_object* v___y_1916_; uint8_t v___x_1932_; 
v___x_1932_ = lean_unbox(v_snd_1908_);
lean_dec(v_snd_1908_);
if (v___x_1932_ == 0)
{
uint8_t v___x_1933_; 
v___x_1933_ = l_Lean_Level_isZero(v_a_1858_);
lean_dec(v_a_1858_);
if (v___x_1933_ == 0)
{
lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1938_; 
lean_dec(v_fst_1907_);
lean_dec(v_paramsPos_1882_);
lean_dec_ref(v_x_1865_);
lean_dec_ref(v_major_1863_);
lean_dec_ref(v_a_1862_);
v___x_1934_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__6));
v___x_1935_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__8, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__8_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__8);
v___x_1936_ = l_Lean_MessageData_ofName(v_recursorName_1879_);
if (v_isShared_1911_ == 0)
{
lean_ctor_set_tag(v___x_1910_, 7);
lean_ctor_set(v___x_1910_, 1, v___x_1936_);
lean_ctor_set(v___x_1910_, 0, v___x_1935_);
v___x_1938_ = v___x_1910_;
goto v_reusejp_1937_;
}
else
{
lean_object* v_reuseFailAlloc_1951_; 
v_reuseFailAlloc_1951_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1951_, 0, v___x_1935_);
lean_ctor_set(v_reuseFailAlloc_1951_, 1, v___x_1936_);
v___x_1938_ = v_reuseFailAlloc_1951_;
goto v_reusejp_1937_;
}
v_reusejp_1937_:
{
lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v_a_1943_; lean_object* v___x_1945_; uint8_t v_isShared_1946_; uint8_t v_isSharedCheck_1950_; 
v___x_1939_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__10, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__10_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__10);
v___x_1940_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1940_, 0, v___x_1938_);
lean_ctor_set(v___x_1940_, 1, v___x_1939_);
v___x_1941_ = l_Lean_Meta_mkTacticExMsg(v_tacticName_1859_, v_mvarId_1860_, v___x_1940_);
v___x_1942_ = l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1___redArg(v___x_1934_, v___x_1941_, v___y_1867_, v___y_1868_, v___y_1869_, v___y_1870_);
v_a_1943_ = lean_ctor_get(v___x_1942_, 0);
v_isSharedCheck_1950_ = !lean_is_exclusive(v___x_1942_);
if (v_isSharedCheck_1950_ == 0)
{
v___x_1945_ = v___x_1942_;
v_isShared_1946_ = v_isSharedCheck_1950_;
goto v_resetjp_1944_;
}
else
{
lean_inc(v_a_1943_);
lean_dec(v___x_1942_);
v___x_1945_ = lean_box(0);
v_isShared_1946_ = v_isSharedCheck_1950_;
goto v_resetjp_1944_;
}
v_resetjp_1944_:
{
lean_object* v___x_1948_; 
if (v_isShared_1946_ == 0)
{
v___x_1948_ = v___x_1945_;
goto v_reusejp_1947_;
}
else
{
lean_object* v_reuseFailAlloc_1949_; 
v_reuseFailAlloc_1949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1949_, 0, v_a_1943_);
v___x_1948_ = v_reuseFailAlloc_1949_;
goto v_reusejp_1947_;
}
v_reusejp_1947_:
{
return v___x_1948_;
}
}
}
}
else
{
lean_del_object(v___x_1910_);
lean_dec(v_tacticName_1859_);
v___y_1913_ = v___y_1867_;
v___y_1914_ = v___y_1868_;
v___y_1915_ = v___y_1869_;
v___y_1916_ = v___y_1870_;
goto v___jp_1912_;
}
}
else
{
lean_del_object(v___x_1910_);
lean_dec(v_tacticName_1859_);
lean_dec(v_a_1858_);
v___y_1913_ = v___y_1867_;
v___y_1914_ = v___y_1868_;
v___y_1915_ = v___y_1869_;
v___y_1916_ = v___y_1870_;
goto v___jp_1912_;
}
v___jp_1912_:
{
lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; 
v___x_1917_ = lean_array_to_list(v_fst_1907_);
v___x_1918_ = l_Lean_mkConst(v_recursorName_1879_, v___x_1917_);
v___x_1919_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams(v_mvarId_1860_, v_x_1865_, v_paramsPos_1882_, v___x_1918_, v___y_1913_, v___y_1914_, v___y_1915_, v___y_1916_);
lean_dec_ref(v_x_1865_);
if (lean_obj_tag(v___x_1919_) == 0)
{
if (v_depElim_1881_ == 0)
{
lean_object* v_a_1920_; 
lean_dec_ref(v_major_1863_);
v_a_1920_ = lean_ctor_get(v___x_1919_, 0);
lean_inc(v_a_1920_);
lean_dec_ref_known(v___x_1919_, 1);
v___y_1886_ = v_a_1920_;
v_motive_1887_ = v_a_1862_;
v___y_1888_ = v___y_1913_;
v___y_1889_ = v___y_1914_;
v___y_1890_ = v___y_1915_;
v___y_1891_ = v___y_1916_;
goto v___jp_1885_;
}
else
{
lean_object* v_a_1921_; lean_object* v___x_1922_; 
v_a_1921_ = lean_ctor_get(v___x_1919_, 0);
lean_inc(v_a_1921_);
lean_dec_ref_known(v___x_1919_, 1);
lean_inc(v___y_1916_);
lean_inc_ref(v___y_1915_);
lean_inc(v___y_1914_);
lean_inc_ref(v___y_1913_);
lean_inc_ref(v_major_1863_);
v___x_1922_ = lean_infer_type(v_major_1863_, v___y_1913_, v___y_1914_, v___y_1915_, v___y_1916_);
if (lean_obj_tag(v___x_1922_) == 0)
{
lean_object* v_a_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; 
v_a_1923_ = lean_ctor_get(v___x_1922_, 0);
lean_inc(v_a_1923_);
lean_dec_ref_known(v___x_1922_, 1);
v___x_1924_ = lean_unsigned_to_nat(1u);
v___x_1925_ = lean_mk_empty_array_with_capacity(v___x_1924_);
v___x_1926_ = lean_array_push(v___x_1925_, v_major_1863_);
v___x_1927_ = l_Lean_Expr_abstractM(v_a_1862_, v___x_1926_, v___y_1913_, v___y_1914_, v___y_1915_, v___y_1916_);
lean_dec_ref(v___x_1926_);
if (lean_obj_tag(v___x_1927_) == 0)
{
lean_object* v_a_1928_; lean_object* v___x_1929_; uint8_t v___x_1930_; lean_object* v___x_1931_; 
v_a_1928_ = lean_ctor_get(v___x_1927_, 0);
lean_inc(v_a_1928_);
lean_dec_ref_known(v___x_1927_, 1);
v___x_1929_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__3));
v___x_1930_ = 0;
v___x_1931_ = l_Lean_mkLambda(v___x_1929_, v___x_1930_, v_a_1923_, v_a_1928_);
v___y_1886_ = v_a_1921_;
v_motive_1887_ = v___x_1931_;
v___y_1888_ = v___y_1913_;
v___y_1889_ = v___y_1914_;
v___y_1890_ = v___y_1915_;
v___y_1891_ = v___y_1916_;
goto v___jp_1885_;
}
else
{
lean_dec(v_a_1923_);
lean_dec(v_a_1921_);
return v___x_1927_;
}
}
else
{
lean_dec(v_a_1921_);
lean_dec_ref(v_major_1863_);
lean_dec_ref(v_a_1862_);
return v___x_1922_;
}
}
}
else
{
lean_dec_ref(v_major_1863_);
lean_dec_ref(v_a_1862_);
return v___x_1919_;
}
}
}
}
else
{
lean_object* v_a_1953_; lean_object* v___x_1955_; uint8_t v_isShared_1956_; uint8_t v_isSharedCheck_1960_; 
lean_dec(v_paramsPos_1882_);
lean_dec(v_recursorName_1879_);
lean_dec_ref(v_x_1865_);
lean_dec_ref(v_major_1863_);
lean_dec_ref(v_a_1862_);
lean_dec(v_mvarId_1860_);
lean_dec(v_tacticName_1859_);
lean_dec(v_a_1858_);
v_a_1953_ = lean_ctor_get(v___x_1905_, 0);
v_isSharedCheck_1960_ = !lean_is_exclusive(v___x_1905_);
if (v_isSharedCheck_1960_ == 0)
{
v___x_1955_ = v___x_1905_;
v_isShared_1956_ = v_isSharedCheck_1960_;
goto v_resetjp_1954_;
}
else
{
lean_inc(v_a_1953_);
lean_dec(v___x_1905_);
v___x_1955_ = lean_box(0);
v_isShared_1956_ = v_isSharedCheck_1960_;
goto v_resetjp_1954_;
}
v_resetjp_1954_:
{
lean_object* v___x_1958_; 
if (v_isShared_1956_ == 0)
{
v___x_1958_ = v___x_1955_;
goto v_reusejp_1957_;
}
else
{
lean_object* v_reuseFailAlloc_1959_; 
v_reuseFailAlloc_1959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1959_, 0, v_a_1953_);
v___x_1958_ = v_reuseFailAlloc_1959_;
goto v_reusejp_1957_;
}
v_reusejp_1957_:
{
return v___x_1958_;
}
}
}
v___jp_1885_:
{
uint8_t v___x_1892_; uint8_t v___x_1893_; lean_object* v___x_1894_; 
v___x_1892_ = 1;
v___x_1893_ = 1;
v___x_1894_ = l_Lean_Meta_mkLambdaFVars(v_indices_1861_, v_motive_1887_, v___x_1884_, v___x_1892_, v___x_1884_, v___x_1892_, v___x_1893_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_);
if (lean_obj_tag(v___x_1894_) == 0)
{
lean_object* v_a_1895_; lean_object* v___x_1897_; uint8_t v_isShared_1898_; uint8_t v_isSharedCheck_1903_; 
v_a_1895_ = lean_ctor_get(v___x_1894_, 0);
v_isSharedCheck_1903_ = !lean_is_exclusive(v___x_1894_);
if (v_isSharedCheck_1903_ == 0)
{
v___x_1897_ = v___x_1894_;
v_isShared_1898_ = v_isSharedCheck_1903_;
goto v_resetjp_1896_;
}
else
{
lean_inc(v_a_1895_);
lean_dec(v___x_1894_);
v___x_1897_ = lean_box(0);
v_isShared_1898_ = v_isSharedCheck_1903_;
goto v_resetjp_1896_;
}
v_resetjp_1896_:
{
lean_object* v___x_1899_; lean_object* v___x_1901_; 
v___x_1899_ = l_Lean_Expr_app___override(v___y_1886_, v_a_1895_);
if (v_isShared_1898_ == 0)
{
lean_ctor_set(v___x_1897_, 0, v___x_1899_);
v___x_1901_ = v___x_1897_;
goto v_reusejp_1900_;
}
else
{
lean_object* v_reuseFailAlloc_1902_; 
v_reuseFailAlloc_1902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1902_, 0, v___x_1899_);
v___x_1901_ = v_reuseFailAlloc_1902_;
goto v_reusejp_1900_;
}
v_reusejp_1900_:
{
return v___x_1901_;
}
}
}
else
{
lean_dec_ref(v___y_1886_);
return v___x_1894_;
}
}
}
else
{
lean_object* v___x_1961_; lean_object* v___x_1962_; 
lean_dec_ref(v_x_1865_);
lean_dec_ref(v_x_1864_);
lean_dec_ref(v_major_1863_);
lean_dec_ref(v_a_1862_);
lean_dec(v_a_1858_);
lean_dec_ref(v_recursorInfo_1857_);
v___x_1961_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__14, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__14_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__14);
v___x_1962_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1859_, v_mvarId_1860_, v___x_1961_, v___y_1867_, v___y_1868_, v___y_1869_, v___y_1870_);
return v___x_1962_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___boxed(lean_object* v_recursorInfo_1963_, lean_object* v_a_1964_, lean_object* v_tacticName_1965_, lean_object* v_mvarId_1966_, lean_object* v_indices_1967_, lean_object* v_a_1968_, lean_object* v_major_1969_, lean_object* v_x_1970_, lean_object* v_x_1971_, lean_object* v_x_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_){
_start:
{
lean_object* v_res_1978_; 
v_res_1978_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2(v_recursorInfo_1963_, v_a_1964_, v_tacticName_1965_, v_mvarId_1966_, v_indices_1967_, v_a_1968_, v_major_1969_, v_x_1970_, v_x_1971_, v_x_1972_, v___y_1973_, v___y_1974_, v___y_1975_, v___y_1976_);
lean_dec(v___y_1976_);
lean_dec_ref(v___y_1975_);
lean_dec(v___y_1974_);
lean_dec_ref(v___y_1973_);
lean_dec_ref(v_indices_1967_);
return v_res_1978_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2(lean_object* v_a_1979_, lean_object* v_tacticName_1980_, lean_object* v_mvarId_1981_, lean_object* v_recursorInfo_1982_, lean_object* v_indices_1983_, lean_object* v_a_1984_, lean_object* v_major_1985_, lean_object* v_x_1986_, lean_object* v_x_1987_, lean_object* v_x_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_){
_start:
{
if (lean_obj_tag(v_x_1986_) == 5)
{
lean_object* v_fn_1994_; lean_object* v_arg_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; 
v_fn_1994_ = lean_ctor_get(v_x_1986_, 0);
lean_inc_ref(v_fn_1994_);
v_arg_1995_ = lean_ctor_get(v_x_1986_, 1);
lean_inc_ref(v_arg_1995_);
lean_dec_ref_known(v_x_1986_, 2);
v___x_1996_ = lean_array_set(v_x_1987_, v_x_1988_, v_arg_1995_);
v___x_1997_ = lean_unsigned_to_nat(1u);
v___x_1998_ = lean_nat_sub(v_x_1988_, v___x_1997_);
v___x_1999_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2(v_recursorInfo_1982_, v_a_1979_, v_tacticName_1980_, v_mvarId_1981_, v_indices_1983_, v_a_1984_, v_major_1985_, v_fn_1994_, v___x_1996_, v___x_1998_, v___y_1989_, v___y_1990_, v___y_1991_, v___y_1992_);
return v___x_1999_;
}
else
{
if (lean_obj_tag(v_x_1986_) == 4)
{
lean_object* v_us_2000_; lean_object* v_recursorName_2001_; lean_object* v_univLevelPos_2002_; uint8_t v_depElim_2003_; lean_object* v_paramsPos_2004_; lean_object* v___x_2005_; uint8_t v___x_2006_; lean_object* v___y_2008_; lean_object* v_motive_2009_; lean_object* v___y_2010_; lean_object* v___y_2011_; lean_object* v___y_2012_; lean_object* v___y_2013_; lean_object* v___x_2026_; lean_object* v___x_2027_; 
v_us_2000_ = lean_ctor_get(v_x_1986_, 1);
lean_inc(v_us_2000_);
lean_dec_ref_known(v_x_1986_, 2);
v_recursorName_2001_ = lean_ctor_get(v_recursorInfo_1982_, 0);
lean_inc(v_recursorName_2001_);
v_univLevelPos_2002_ = lean_ctor_get(v_recursorInfo_1982_, 2);
lean_inc(v_univLevelPos_2002_);
v_depElim_2003_ = lean_ctor_get_uint8(v_recursorInfo_1982_, sizeof(void*)*8);
v_paramsPos_2004_ = lean_ctor_get(v_recursorInfo_1982_, 5);
lean_inc(v_paramsPos_2004_);
lean_dec_ref(v_recursorInfo_1982_);
v___x_2005_ = lean_array_mk(v_us_2000_);
v___x_2006_ = 0;
v___x_2026_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__1));
lean_inc(v_mvarId_1981_);
lean_inc(v_tacticName_1980_);
lean_inc(v_a_1979_);
v___x_2027_ = l_List_foldlM___at___00Lean_Meta_mkRecursorAppPrefix_spec__0(v_a_1979_, v___x_2005_, v_tacticName_1980_, v_mvarId_1981_, v___x_2026_, v_univLevelPos_2002_, v___y_1989_, v___y_1990_, v___y_1991_, v___y_1992_);
lean_dec(v_univLevelPos_2002_);
lean_dec_ref(v___x_2005_);
if (lean_obj_tag(v___x_2027_) == 0)
{
lean_object* v_a_2028_; lean_object* v_fst_2029_; lean_object* v_snd_2030_; lean_object* v___x_2032_; uint8_t v_isShared_2033_; uint8_t v_isSharedCheck_2074_; 
v_a_2028_ = lean_ctor_get(v___x_2027_, 0);
lean_inc(v_a_2028_);
lean_dec_ref_known(v___x_2027_, 1);
v_fst_2029_ = lean_ctor_get(v_a_2028_, 0);
v_snd_2030_ = lean_ctor_get(v_a_2028_, 1);
v_isSharedCheck_2074_ = !lean_is_exclusive(v_a_2028_);
if (v_isSharedCheck_2074_ == 0)
{
v___x_2032_ = v_a_2028_;
v_isShared_2033_ = v_isSharedCheck_2074_;
goto v_resetjp_2031_;
}
else
{
lean_inc(v_snd_2030_);
lean_inc(v_fst_2029_);
lean_dec(v_a_2028_);
v___x_2032_ = lean_box(0);
v_isShared_2033_ = v_isSharedCheck_2074_;
goto v_resetjp_2031_;
}
v_resetjp_2031_:
{
lean_object* v___y_2035_; lean_object* v___y_2036_; lean_object* v___y_2037_; lean_object* v___y_2038_; uint8_t v___x_2054_; 
v___x_2054_ = lean_unbox(v_snd_2030_);
lean_dec(v_snd_2030_);
if (v___x_2054_ == 0)
{
uint8_t v___x_2055_; 
v___x_2055_ = l_Lean_Level_isZero(v_a_1979_);
lean_dec(v_a_1979_);
if (v___x_2055_ == 0)
{
lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2060_; 
lean_dec(v_fst_2029_);
lean_dec(v_paramsPos_2004_);
lean_dec_ref(v_x_1987_);
lean_dec_ref(v_major_1985_);
lean_dec_ref(v_a_1984_);
v___x_2056_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__6));
v___x_2057_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__8, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__8_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__8);
v___x_2058_ = l_Lean_MessageData_ofName(v_recursorName_2001_);
if (v_isShared_2033_ == 0)
{
lean_ctor_set_tag(v___x_2032_, 7);
lean_ctor_set(v___x_2032_, 1, v___x_2058_);
lean_ctor_set(v___x_2032_, 0, v___x_2057_);
v___x_2060_ = v___x_2032_;
goto v_reusejp_2059_;
}
else
{
lean_object* v_reuseFailAlloc_2073_; 
v_reuseFailAlloc_2073_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2073_, 0, v___x_2057_);
lean_ctor_set(v_reuseFailAlloc_2073_, 1, v___x_2058_);
v___x_2060_ = v_reuseFailAlloc_2073_;
goto v_reusejp_2059_;
}
v_reusejp_2059_:
{
lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v_a_2065_; lean_object* v___x_2067_; uint8_t v_isShared_2068_; uint8_t v_isSharedCheck_2072_; 
v___x_2061_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__10, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__10_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__10);
v___x_2062_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2062_, 0, v___x_2060_);
lean_ctor_set(v___x_2062_, 1, v___x_2061_);
v___x_2063_ = l_Lean_Meta_mkTacticExMsg(v_tacticName_1980_, v_mvarId_1981_, v___x_2062_);
v___x_2064_ = l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1___redArg(v___x_2056_, v___x_2063_, v___y_1989_, v___y_1990_, v___y_1991_, v___y_1992_);
v_a_2065_ = lean_ctor_get(v___x_2064_, 0);
v_isSharedCheck_2072_ = !lean_is_exclusive(v___x_2064_);
if (v_isSharedCheck_2072_ == 0)
{
v___x_2067_ = v___x_2064_;
v_isShared_2068_ = v_isSharedCheck_2072_;
goto v_resetjp_2066_;
}
else
{
lean_inc(v_a_2065_);
lean_dec(v___x_2064_);
v___x_2067_ = lean_box(0);
v_isShared_2068_ = v_isSharedCheck_2072_;
goto v_resetjp_2066_;
}
v_resetjp_2066_:
{
lean_object* v___x_2070_; 
if (v_isShared_2068_ == 0)
{
v___x_2070_ = v___x_2067_;
goto v_reusejp_2069_;
}
else
{
lean_object* v_reuseFailAlloc_2071_; 
v_reuseFailAlloc_2071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2071_, 0, v_a_2065_);
v___x_2070_ = v_reuseFailAlloc_2071_;
goto v_reusejp_2069_;
}
v_reusejp_2069_:
{
return v___x_2070_;
}
}
}
}
else
{
lean_del_object(v___x_2032_);
lean_dec(v_tacticName_1980_);
v___y_2035_ = v___y_1989_;
v___y_2036_ = v___y_1990_;
v___y_2037_ = v___y_1991_;
v___y_2038_ = v___y_1992_;
goto v___jp_2034_;
}
}
else
{
lean_del_object(v___x_2032_);
lean_dec(v_tacticName_1980_);
lean_dec(v_a_1979_);
v___y_2035_ = v___y_1989_;
v___y_2036_ = v___y_1990_;
v___y_2037_ = v___y_1991_;
v___y_2038_ = v___y_1992_;
goto v___jp_2034_;
}
v___jp_2034_:
{
lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; 
v___x_2039_ = lean_array_to_list(v_fst_2029_);
v___x_2040_ = l_Lean_mkConst(v_recursorName_2001_, v___x_2039_);
v___x_2041_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams(v_mvarId_1981_, v_x_1987_, v_paramsPos_2004_, v___x_2040_, v___y_2035_, v___y_2036_, v___y_2037_, v___y_2038_);
lean_dec_ref(v_x_1987_);
if (lean_obj_tag(v___x_2041_) == 0)
{
if (v_depElim_2003_ == 0)
{
lean_object* v_a_2042_; 
lean_dec_ref(v_major_1985_);
v_a_2042_ = lean_ctor_get(v___x_2041_, 0);
lean_inc(v_a_2042_);
lean_dec_ref_known(v___x_2041_, 1);
v___y_2008_ = v_a_2042_;
v_motive_2009_ = v_a_1984_;
v___y_2010_ = v___y_2035_;
v___y_2011_ = v___y_2036_;
v___y_2012_ = v___y_2037_;
v___y_2013_ = v___y_2038_;
goto v___jp_2007_;
}
else
{
lean_object* v_a_2043_; lean_object* v___x_2044_; 
v_a_2043_ = lean_ctor_get(v___x_2041_, 0);
lean_inc(v_a_2043_);
lean_dec_ref_known(v___x_2041_, 1);
lean_inc(v___y_2038_);
lean_inc_ref(v___y_2037_);
lean_inc(v___y_2036_);
lean_inc_ref(v___y_2035_);
lean_inc_ref(v_major_1985_);
v___x_2044_ = lean_infer_type(v_major_1985_, v___y_2035_, v___y_2036_, v___y_2037_, v___y_2038_);
if (lean_obj_tag(v___x_2044_) == 0)
{
lean_object* v_a_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; 
v_a_2045_ = lean_ctor_get(v___x_2044_, 0);
lean_inc(v_a_2045_);
lean_dec_ref_known(v___x_2044_, 1);
v___x_2046_ = lean_unsigned_to_nat(1u);
v___x_2047_ = lean_mk_empty_array_with_capacity(v___x_2046_);
v___x_2048_ = lean_array_push(v___x_2047_, v_major_1985_);
v___x_2049_ = l_Lean_Expr_abstractM(v_a_1984_, v___x_2048_, v___y_2035_, v___y_2036_, v___y_2037_, v___y_2038_);
lean_dec_ref(v___x_2048_);
if (lean_obj_tag(v___x_2049_) == 0)
{
lean_object* v_a_2050_; lean_object* v___x_2051_; uint8_t v___x_2052_; lean_object* v___x_2053_; 
v_a_2050_ = lean_ctor_get(v___x_2049_, 0);
lean_inc(v_a_2050_);
lean_dec_ref_known(v___x_2049_, 1);
v___x_2051_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__3));
v___x_2052_ = 0;
v___x_2053_ = l_Lean_mkLambda(v___x_2051_, v___x_2052_, v_a_2045_, v_a_2050_);
v___y_2008_ = v_a_2043_;
v_motive_2009_ = v___x_2053_;
v___y_2010_ = v___y_2035_;
v___y_2011_ = v___y_2036_;
v___y_2012_ = v___y_2037_;
v___y_2013_ = v___y_2038_;
goto v___jp_2007_;
}
else
{
lean_dec(v_a_2045_);
lean_dec(v_a_2043_);
return v___x_2049_;
}
}
else
{
lean_dec(v_a_2043_);
lean_dec_ref(v_major_1985_);
lean_dec_ref(v_a_1984_);
return v___x_2044_;
}
}
}
else
{
lean_dec_ref(v_major_1985_);
lean_dec_ref(v_a_1984_);
return v___x_2041_;
}
}
}
}
else
{
lean_object* v_a_2075_; lean_object* v___x_2077_; uint8_t v_isShared_2078_; uint8_t v_isSharedCheck_2082_; 
lean_dec(v_paramsPos_2004_);
lean_dec(v_recursorName_2001_);
lean_dec_ref(v_x_1987_);
lean_dec_ref(v_major_1985_);
lean_dec_ref(v_a_1984_);
lean_dec(v_mvarId_1981_);
lean_dec(v_tacticName_1980_);
lean_dec(v_a_1979_);
v_a_2075_ = lean_ctor_get(v___x_2027_, 0);
v_isSharedCheck_2082_ = !lean_is_exclusive(v___x_2027_);
if (v_isSharedCheck_2082_ == 0)
{
v___x_2077_ = v___x_2027_;
v_isShared_2078_ = v_isSharedCheck_2082_;
goto v_resetjp_2076_;
}
else
{
lean_inc(v_a_2075_);
lean_dec(v___x_2027_);
v___x_2077_ = lean_box(0);
v_isShared_2078_ = v_isSharedCheck_2082_;
goto v_resetjp_2076_;
}
v_resetjp_2076_:
{
lean_object* v___x_2080_; 
if (v_isShared_2078_ == 0)
{
v___x_2080_ = v___x_2077_;
goto v_reusejp_2079_;
}
else
{
lean_object* v_reuseFailAlloc_2081_; 
v_reuseFailAlloc_2081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2081_, 0, v_a_2075_);
v___x_2080_ = v_reuseFailAlloc_2081_;
goto v_reusejp_2079_;
}
v_reusejp_2079_:
{
return v___x_2080_;
}
}
}
v___jp_2007_:
{
uint8_t v___x_2014_; uint8_t v___x_2015_; lean_object* v___x_2016_; 
v___x_2014_ = 1;
v___x_2015_ = 1;
v___x_2016_ = l_Lean_Meta_mkLambdaFVars(v_indices_1983_, v_motive_2009_, v___x_2006_, v___x_2014_, v___x_2006_, v___x_2014_, v___x_2015_, v___y_2010_, v___y_2011_, v___y_2012_, v___y_2013_);
if (lean_obj_tag(v___x_2016_) == 0)
{
lean_object* v_a_2017_; lean_object* v___x_2019_; uint8_t v_isShared_2020_; uint8_t v_isSharedCheck_2025_; 
v_a_2017_ = lean_ctor_get(v___x_2016_, 0);
v_isSharedCheck_2025_ = !lean_is_exclusive(v___x_2016_);
if (v_isSharedCheck_2025_ == 0)
{
v___x_2019_ = v___x_2016_;
v_isShared_2020_ = v_isSharedCheck_2025_;
goto v_resetjp_2018_;
}
else
{
lean_inc(v_a_2017_);
lean_dec(v___x_2016_);
v___x_2019_ = lean_box(0);
v_isShared_2020_ = v_isSharedCheck_2025_;
goto v_resetjp_2018_;
}
v_resetjp_2018_:
{
lean_object* v___x_2021_; lean_object* v___x_2023_; 
v___x_2021_ = l_Lean_Expr_app___override(v___y_2008_, v_a_2017_);
if (v_isShared_2020_ == 0)
{
lean_ctor_set(v___x_2019_, 0, v___x_2021_);
v___x_2023_ = v___x_2019_;
goto v_reusejp_2022_;
}
else
{
lean_object* v_reuseFailAlloc_2024_; 
v_reuseFailAlloc_2024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2024_, 0, v___x_2021_);
v___x_2023_ = v_reuseFailAlloc_2024_;
goto v_reusejp_2022_;
}
v_reusejp_2022_:
{
return v___x_2023_;
}
}
}
else
{
lean_dec_ref(v___y_2008_);
return v___x_2016_;
}
}
}
else
{
lean_object* v___x_2083_; lean_object* v___x_2084_; 
lean_dec_ref(v_x_1987_);
lean_dec_ref(v_x_1986_);
lean_dec_ref(v_major_1985_);
lean_dec_ref(v_a_1984_);
lean_dec_ref(v_recursorInfo_1982_);
lean_dec(v_a_1979_);
v___x_2083_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__14, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__14_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__14);
v___x_2084_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1980_, v_mvarId_1981_, v___x_2083_, v___y_1989_, v___y_1990_, v___y_1991_, v___y_1992_);
return v___x_2084_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2___boxed(lean_object* v_a_2085_, lean_object* v_tacticName_2086_, lean_object* v_mvarId_2087_, lean_object* v_recursorInfo_2088_, lean_object* v_indices_2089_, lean_object* v_a_2090_, lean_object* v_major_2091_, lean_object* v_x_2092_, lean_object* v_x_2093_, lean_object* v_x_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_){
_start:
{
lean_object* v_res_2100_; 
v_res_2100_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2(v_a_2085_, v_tacticName_2086_, v_mvarId_2087_, v_recursorInfo_2088_, v_indices_2089_, v_a_2090_, v_major_2091_, v_x_2092_, v_x_2093_, v_x_2094_, v___y_2095_, v___y_2096_, v___y_2097_, v___y_2098_);
lean_dec(v___y_2098_);
lean_dec_ref(v___y_2097_);
lean_dec(v___y_2096_);
lean_dec_ref(v___y_2095_);
lean_dec(v_x_2094_);
lean_dec_ref(v_indices_2089_);
return v_res_2100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkRecursorAppPrefix(lean_object* v_mvarId_2101_, lean_object* v_tacticName_2102_, lean_object* v_majorFVarId_2103_, lean_object* v_recursorInfo_2104_, lean_object* v_indices_2105_, lean_object* v_a_2106_, lean_object* v_a_2107_, lean_object* v_a_2108_, lean_object* v_a_2109_){
_start:
{
lean_object* v_major_2111_; lean_object* v___x_2112_; 
lean_inc(v_majorFVarId_2103_);
v_major_2111_ = l_Lean_mkFVar(v_majorFVarId_2103_);
lean_inc(v_mvarId_2101_);
v___x_2112_ = l_Lean_MVarId_getType(v_mvarId_2101_, v_a_2106_, v_a_2107_, v_a_2108_, v_a_2109_);
if (lean_obj_tag(v___x_2112_) == 0)
{
lean_object* v_a_2113_; lean_object* v___x_2114_; 
v_a_2113_ = lean_ctor_get(v___x_2112_, 0);
lean_inc_n(v_a_2113_, 2);
lean_dec_ref_known(v___x_2112_, 1);
v___x_2114_ = l_Lean_Meta_getLevel(v_a_2113_, v_a_2106_, v_a_2107_, v_a_2108_, v_a_2109_);
if (lean_obj_tag(v___x_2114_) == 0)
{
lean_object* v_a_2115_; lean_object* v___x_2116_; 
v_a_2115_ = lean_ctor_get(v___x_2114_, 0);
lean_inc(v_a_2115_);
lean_dec_ref_known(v___x_2114_, 1);
v___x_2116_ = l_Lean_Meta_normalizeLevel(v_a_2115_, v_a_2106_, v_a_2107_, v_a_2108_, v_a_2109_);
if (lean_obj_tag(v___x_2116_) == 0)
{
lean_object* v_a_2117_; lean_object* v___x_2118_; 
v_a_2117_ = lean_ctor_get(v___x_2116_, 0);
lean_inc(v_a_2117_);
lean_dec_ref_known(v___x_2116_, 1);
v___x_2118_ = l_Lean_FVarId_getDecl___redArg(v_majorFVarId_2103_, v_a_2106_, v_a_2108_, v_a_2109_);
if (lean_obj_tag(v___x_2118_) == 0)
{
lean_object* v_a_2119_; lean_object* v_typeName_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; 
v_a_2119_ = lean_ctor_get(v___x_2118_, 0);
lean_inc(v_a_2119_);
lean_dec_ref_known(v___x_2118_, 1);
v_typeName_2120_ = lean_ctor_get(v_recursorInfo_2104_, 1);
v___x_2121_ = l_Lean_LocalDecl_type(v_a_2119_);
lean_dec(v_a_2119_);
lean_inc_ref(v___x_2121_);
v___x_2122_ = l_Lean_Meta_whnfUntil(v___x_2121_, v_typeName_2120_, v_a_2106_, v_a_2107_, v_a_2108_, v_a_2109_);
if (lean_obj_tag(v___x_2122_) == 0)
{
lean_object* v_a_2123_; 
v_a_2123_ = lean_ctor_get(v___x_2122_, 0);
lean_inc(v_a_2123_);
lean_dec_ref_known(v___x_2122_, 1);
if (lean_obj_tag(v_a_2123_) == 1)
{
lean_object* v_val_2124_; lean_object* v_dummy_2125_; lean_object* v_nargs_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; 
lean_dec_ref(v___x_2121_);
v_val_2124_ = lean_ctor_get(v_a_2123_, 0);
lean_inc(v_val_2124_);
lean_dec_ref_known(v_a_2123_, 1);
v_dummy_2125_ = lean_obj_once(&l_Lean_Meta_getMajorTypeIndices___closed__0, &l_Lean_Meta_getMajorTypeIndices___closed__0_once, _init_l_Lean_Meta_getMajorTypeIndices___closed__0);
v_nargs_2126_ = l_Lean_Expr_getAppNumArgs(v_val_2124_);
lean_inc(v_nargs_2126_);
v___x_2127_ = lean_mk_array(v_nargs_2126_, v_dummy_2125_);
v___x_2128_ = lean_unsigned_to_nat(1u);
v___x_2129_ = lean_nat_sub(v_nargs_2126_, v___x_2128_);
lean_dec(v_nargs_2126_);
v___x_2130_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2(v_a_2117_, v_tacticName_2102_, v_mvarId_2101_, v_recursorInfo_2104_, v_indices_2105_, v_a_2113_, v_major_2111_, v_val_2124_, v___x_2127_, v___x_2129_, v_a_2106_, v_a_2107_, v_a_2108_, v_a_2109_);
lean_dec(v___x_2129_);
return v___x_2130_;
}
else
{
lean_object* v___x_2131_; 
lean_dec(v_a_2123_);
lean_dec(v_a_2117_);
lean_dec(v_a_2113_);
lean_dec_ref(v_major_2111_);
lean_dec_ref(v_recursorInfo_2104_);
v___x_2131_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg(v_tacticName_2102_, v_mvarId_2101_, v___x_2121_, v_a_2106_, v_a_2107_, v_a_2108_, v_a_2109_);
return v___x_2131_;
}
}
else
{
lean_object* v_a_2132_; lean_object* v___x_2134_; uint8_t v_isShared_2135_; uint8_t v_isSharedCheck_2139_; 
lean_dec_ref(v___x_2121_);
lean_dec(v_a_2117_);
lean_dec(v_a_2113_);
lean_dec_ref(v_major_2111_);
lean_dec_ref(v_recursorInfo_2104_);
lean_dec(v_tacticName_2102_);
lean_dec(v_mvarId_2101_);
v_a_2132_ = lean_ctor_get(v___x_2122_, 0);
v_isSharedCheck_2139_ = !lean_is_exclusive(v___x_2122_);
if (v_isSharedCheck_2139_ == 0)
{
v___x_2134_ = v___x_2122_;
v_isShared_2135_ = v_isSharedCheck_2139_;
goto v_resetjp_2133_;
}
else
{
lean_inc(v_a_2132_);
lean_dec(v___x_2122_);
v___x_2134_ = lean_box(0);
v_isShared_2135_ = v_isSharedCheck_2139_;
goto v_resetjp_2133_;
}
v_resetjp_2133_:
{
lean_object* v___x_2137_; 
if (v_isShared_2135_ == 0)
{
v___x_2137_ = v___x_2134_;
goto v_reusejp_2136_;
}
else
{
lean_object* v_reuseFailAlloc_2138_; 
v_reuseFailAlloc_2138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2138_, 0, v_a_2132_);
v___x_2137_ = v_reuseFailAlloc_2138_;
goto v_reusejp_2136_;
}
v_reusejp_2136_:
{
return v___x_2137_;
}
}
}
}
else
{
lean_object* v_a_2140_; lean_object* v___x_2142_; uint8_t v_isShared_2143_; uint8_t v_isSharedCheck_2147_; 
lean_dec(v_a_2117_);
lean_dec(v_a_2113_);
lean_dec_ref(v_major_2111_);
lean_dec_ref(v_recursorInfo_2104_);
lean_dec(v_tacticName_2102_);
lean_dec(v_mvarId_2101_);
v_a_2140_ = lean_ctor_get(v___x_2118_, 0);
v_isSharedCheck_2147_ = !lean_is_exclusive(v___x_2118_);
if (v_isSharedCheck_2147_ == 0)
{
v___x_2142_ = v___x_2118_;
v_isShared_2143_ = v_isSharedCheck_2147_;
goto v_resetjp_2141_;
}
else
{
lean_inc(v_a_2140_);
lean_dec(v___x_2118_);
v___x_2142_ = lean_box(0);
v_isShared_2143_ = v_isSharedCheck_2147_;
goto v_resetjp_2141_;
}
v_resetjp_2141_:
{
lean_object* v___x_2145_; 
if (v_isShared_2143_ == 0)
{
v___x_2145_ = v___x_2142_;
goto v_reusejp_2144_;
}
else
{
lean_object* v_reuseFailAlloc_2146_; 
v_reuseFailAlloc_2146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2146_, 0, v_a_2140_);
v___x_2145_ = v_reuseFailAlloc_2146_;
goto v_reusejp_2144_;
}
v_reusejp_2144_:
{
return v___x_2145_;
}
}
}
}
else
{
lean_object* v_a_2148_; lean_object* v___x_2150_; uint8_t v_isShared_2151_; uint8_t v_isSharedCheck_2155_; 
lean_dec(v_a_2113_);
lean_dec_ref(v_major_2111_);
lean_dec_ref(v_recursorInfo_2104_);
lean_dec(v_majorFVarId_2103_);
lean_dec(v_tacticName_2102_);
lean_dec(v_mvarId_2101_);
v_a_2148_ = lean_ctor_get(v___x_2116_, 0);
v_isSharedCheck_2155_ = !lean_is_exclusive(v___x_2116_);
if (v_isSharedCheck_2155_ == 0)
{
v___x_2150_ = v___x_2116_;
v_isShared_2151_ = v_isSharedCheck_2155_;
goto v_resetjp_2149_;
}
else
{
lean_inc(v_a_2148_);
lean_dec(v___x_2116_);
v___x_2150_ = lean_box(0);
v_isShared_2151_ = v_isSharedCheck_2155_;
goto v_resetjp_2149_;
}
v_resetjp_2149_:
{
lean_object* v___x_2153_; 
if (v_isShared_2151_ == 0)
{
v___x_2153_ = v___x_2150_;
goto v_reusejp_2152_;
}
else
{
lean_object* v_reuseFailAlloc_2154_; 
v_reuseFailAlloc_2154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2154_, 0, v_a_2148_);
v___x_2153_ = v_reuseFailAlloc_2154_;
goto v_reusejp_2152_;
}
v_reusejp_2152_:
{
return v___x_2153_;
}
}
}
}
else
{
lean_object* v_a_2156_; lean_object* v___x_2158_; uint8_t v_isShared_2159_; uint8_t v_isSharedCheck_2163_; 
lean_dec(v_a_2113_);
lean_dec_ref(v_major_2111_);
lean_dec_ref(v_recursorInfo_2104_);
lean_dec(v_majorFVarId_2103_);
lean_dec(v_tacticName_2102_);
lean_dec(v_mvarId_2101_);
v_a_2156_ = lean_ctor_get(v___x_2114_, 0);
v_isSharedCheck_2163_ = !lean_is_exclusive(v___x_2114_);
if (v_isSharedCheck_2163_ == 0)
{
v___x_2158_ = v___x_2114_;
v_isShared_2159_ = v_isSharedCheck_2163_;
goto v_resetjp_2157_;
}
else
{
lean_inc(v_a_2156_);
lean_dec(v___x_2114_);
v___x_2158_ = lean_box(0);
v_isShared_2159_ = v_isSharedCheck_2163_;
goto v_resetjp_2157_;
}
v_resetjp_2157_:
{
lean_object* v___x_2161_; 
if (v_isShared_2159_ == 0)
{
v___x_2161_ = v___x_2158_;
goto v_reusejp_2160_;
}
else
{
lean_object* v_reuseFailAlloc_2162_; 
v_reuseFailAlloc_2162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2162_, 0, v_a_2156_);
v___x_2161_ = v_reuseFailAlloc_2162_;
goto v_reusejp_2160_;
}
v_reusejp_2160_:
{
return v___x_2161_;
}
}
}
}
else
{
lean_dec_ref(v_major_2111_);
lean_dec_ref(v_recursorInfo_2104_);
lean_dec(v_majorFVarId_2103_);
lean_dec(v_tacticName_2102_);
lean_dec(v_mvarId_2101_);
return v___x_2112_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkRecursorAppPrefix___boxed(lean_object* v_mvarId_2164_, lean_object* v_tacticName_2165_, lean_object* v_majorFVarId_2166_, lean_object* v_recursorInfo_2167_, lean_object* v_indices_2168_, lean_object* v_a_2169_, lean_object* v_a_2170_, lean_object* v_a_2171_, lean_object* v_a_2172_, lean_object* v_a_2173_){
_start:
{
lean_object* v_res_2174_; 
v_res_2174_ = l_Lean_Meta_mkRecursorAppPrefix(v_mvarId_2164_, v_tacticName_2165_, v_majorFVarId_2166_, v_recursorInfo_2167_, v_indices_2168_, v_a_2169_, v_a_2170_, v_a_2171_, v_a_2172_);
lean_dec(v_a_2172_);
lean_dec_ref(v_a_2171_);
lean_dec(v_a_2170_);
lean_dec_ref(v_a_2169_);
lean_dec_ref(v_indices_2168_);
return v_res_2174_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1(lean_object* v_00_u03b1_2175_, lean_object* v_name_2176_, lean_object* v_msg_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_){
_start:
{
lean_object* v___x_2183_; 
v___x_2183_ = l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1___redArg(v_name_2176_, v_msg_2177_, v___y_2178_, v___y_2179_, v___y_2180_, v___y_2181_);
return v___x_2183_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1___boxed(lean_object* v_00_u03b1_2184_, lean_object* v_name_2185_, lean_object* v_msg_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_){
_start:
{
lean_object* v_res_2192_; 
v_res_2192_ = l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1(v_00_u03b1_2184_, v_name_2185_, v_msg_2186_, v___y_2187_, v___y_2188_, v___y_2189_, v___y_2190_);
lean_dec(v___y_2190_);
lean_dec_ref(v___y_2189_);
lean_dec(v___y_2188_);
lean_dec_ref(v___y_2187_);
return v_res_2192_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___redArg(lean_object* v_mvarId_2193_, lean_object* v_x_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_){
_start:
{
lean_object* v___x_2200_; 
v___x_2200_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_2193_, v_x_2194_, v___y_2195_, v___y_2196_, v___y_2197_, v___y_2198_);
if (lean_obj_tag(v___x_2200_) == 0)
{
lean_object* v_a_2201_; lean_object* v___x_2203_; uint8_t v_isShared_2204_; uint8_t v_isSharedCheck_2208_; 
v_a_2201_ = lean_ctor_get(v___x_2200_, 0);
v_isSharedCheck_2208_ = !lean_is_exclusive(v___x_2200_);
if (v_isSharedCheck_2208_ == 0)
{
v___x_2203_ = v___x_2200_;
v_isShared_2204_ = v_isSharedCheck_2208_;
goto v_resetjp_2202_;
}
else
{
lean_inc(v_a_2201_);
lean_dec(v___x_2200_);
v___x_2203_ = lean_box(0);
v_isShared_2204_ = v_isSharedCheck_2208_;
goto v_resetjp_2202_;
}
v_resetjp_2202_:
{
lean_object* v___x_2206_; 
if (v_isShared_2204_ == 0)
{
v___x_2206_ = v___x_2203_;
goto v_reusejp_2205_;
}
else
{
lean_object* v_reuseFailAlloc_2207_; 
v_reuseFailAlloc_2207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2207_, 0, v_a_2201_);
v___x_2206_ = v_reuseFailAlloc_2207_;
goto v_reusejp_2205_;
}
v_reusejp_2205_:
{
return v___x_2206_;
}
}
}
else
{
lean_object* v_a_2209_; lean_object* v___x_2211_; uint8_t v_isShared_2212_; uint8_t v_isSharedCheck_2216_; 
v_a_2209_ = lean_ctor_get(v___x_2200_, 0);
v_isSharedCheck_2216_ = !lean_is_exclusive(v___x_2200_);
if (v_isSharedCheck_2216_ == 0)
{
v___x_2211_ = v___x_2200_;
v_isShared_2212_ = v_isSharedCheck_2216_;
goto v_resetjp_2210_;
}
else
{
lean_inc(v_a_2209_);
lean_dec(v___x_2200_);
v___x_2211_ = lean_box(0);
v_isShared_2212_ = v_isSharedCheck_2216_;
goto v_resetjp_2210_;
}
v_resetjp_2210_:
{
lean_object* v___x_2214_; 
if (v_isShared_2212_ == 0)
{
v___x_2214_ = v___x_2211_;
goto v_reusejp_2213_;
}
else
{
lean_object* v_reuseFailAlloc_2215_; 
v_reuseFailAlloc_2215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2215_, 0, v_a_2209_);
v___x_2214_ = v_reuseFailAlloc_2215_;
goto v_reusejp_2213_;
}
v_reusejp_2213_:
{
return v___x_2214_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___redArg___boxed(lean_object* v_mvarId_2217_, lean_object* v_x_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_){
_start:
{
lean_object* v_res_2224_; 
v_res_2224_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___redArg(v_mvarId_2217_, v_x_2218_, v___y_2219_, v___y_2220_, v___y_2221_, v___y_2222_);
lean_dec(v___y_2222_);
lean_dec_ref(v___y_2221_);
lean_dec(v___y_2220_);
lean_dec_ref(v___y_2219_);
return v_res_2224_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3(lean_object* v_00_u03b1_2225_, lean_object* v_mvarId_2226_, lean_object* v_x_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_){
_start:
{
lean_object* v___x_2233_; 
v___x_2233_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___redArg(v_mvarId_2226_, v_x_2227_, v___y_2228_, v___y_2229_, v___y_2230_, v___y_2231_);
return v___x_2233_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___boxed(lean_object* v_00_u03b1_2234_, lean_object* v_mvarId_2235_, lean_object* v_x_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_){
_start:
{
lean_object* v_res_2242_; 
v_res_2242_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3(v_00_u03b1_2234_, v_mvarId_2235_, v_x_2236_, v___y_2237_, v___y_2238_, v___y_2239_, v___y_2240_);
lean_dec(v___y_2240_);
lean_dec_ref(v___y_2239_);
lean_dec(v___y_2238_);
lean_dec_ref(v___y_2237_);
return v_res_2242_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_induction_spec__2(lean_object* v_fst_2243_, lean_object* v_as_2244_, size_t v_sz_2245_, size_t v_i_2246_, lean_object* v_b_2247_){
_start:
{
uint8_t v___x_2248_; 
v___x_2248_ = lean_usize_dec_lt(v_i_2246_, v_sz_2245_);
if (v___x_2248_ == 0)
{
return v_b_2247_;
}
else
{
lean_object* v_fst_2249_; lean_object* v_snd_2250_; lean_object* v___x_2252_; uint8_t v_isShared_2253_; uint8_t v_isSharedCheck_2268_; 
v_fst_2249_ = lean_ctor_get(v_b_2247_, 0);
v_snd_2250_ = lean_ctor_get(v_b_2247_, 1);
v_isSharedCheck_2268_ = !lean_is_exclusive(v_b_2247_);
if (v_isSharedCheck_2268_ == 0)
{
v___x_2252_ = v_b_2247_;
v_isShared_2253_ = v_isSharedCheck_2268_;
goto v_resetjp_2251_;
}
else
{
lean_inc(v_snd_2250_);
lean_inc(v_fst_2249_);
lean_dec(v_b_2247_);
v___x_2252_ = lean_box(0);
v_isShared_2253_ = v_isSharedCheck_2268_;
goto v_resetjp_2251_;
}
v_resetjp_2251_:
{
lean_object* v___x_2254_; lean_object* v_a_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2263_; 
v___x_2254_ = lean_box(0);
v_a_2255_ = lean_array_uget_borrowed(v_as_2244_, v_i_2246_);
v___x_2256_ = l_Lean_Expr_fvarId_x21(v_a_2255_);
v___x_2257_ = lean_array_get_borrowed(v___x_2254_, v_fst_2243_, v_snd_2250_);
lean_inc(v___x_2257_);
v___x_2258_ = l_Lean_mkFVar(v___x_2257_);
v___x_2259_ = l_Lean_Meta_FVarSubst_insert(v_fst_2249_, v___x_2256_, v___x_2258_);
v___x_2260_ = lean_unsigned_to_nat(1u);
v___x_2261_ = lean_nat_add(v_snd_2250_, v___x_2260_);
lean_dec(v_snd_2250_);
if (v_isShared_2253_ == 0)
{
lean_ctor_set(v___x_2252_, 1, v___x_2261_);
lean_ctor_set(v___x_2252_, 0, v___x_2259_);
v___x_2263_ = v___x_2252_;
goto v_reusejp_2262_;
}
else
{
lean_object* v_reuseFailAlloc_2267_; 
v_reuseFailAlloc_2267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2267_, 0, v___x_2259_);
lean_ctor_set(v_reuseFailAlloc_2267_, 1, v___x_2261_);
v___x_2263_ = v_reuseFailAlloc_2267_;
goto v_reusejp_2262_;
}
v_reusejp_2262_:
{
size_t v___x_2264_; size_t v___x_2265_; 
v___x_2264_ = ((size_t)1ULL);
v___x_2265_ = lean_usize_add(v_i_2246_, v___x_2264_);
v_i_2246_ = v___x_2265_;
v_b_2247_ = v___x_2263_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_induction_spec__2___boxed(lean_object* v_fst_2269_, lean_object* v_as_2270_, lean_object* v_sz_2271_, lean_object* v_i_2272_, lean_object* v_b_2273_){
_start:
{
size_t v_sz_boxed_2274_; size_t v_i_boxed_2275_; lean_object* v_res_2276_; 
v_sz_boxed_2274_ = lean_unbox_usize(v_sz_2271_);
lean_dec(v_sz_2271_);
v_i_boxed_2275_ = lean_unbox_usize(v_i_2272_);
lean_dec(v_i_2272_);
v_res_2276_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_induction_spec__2(v_fst_2269_, v_as_2270_, v_sz_boxed_2274_, v_i_boxed_2275_, v_b_2273_);
lean_dec_ref(v_as_2270_);
lean_dec_ref(v_fst_2269_);
return v_res_2276_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4___lam__0(lean_object* v_snd_2277_, lean_object* v___x_2278_, lean_object* v_fst_2279_, lean_object* v_a_2280_, lean_object* v___x_2281_, lean_object* v_givenNames_2282_, lean_object* v_fst_2283_, lean_object* v___x_2284_, lean_object* v_fst_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_){
_start:
{
lean_object* v___x_2291_; 
lean_inc_ref(v_a_2280_);
lean_inc(v_snd_2277_);
v___x_2291_ = l_Lean_Meta_mkRecursorAppPrefix(v_snd_2277_, v___x_2278_, v_fst_2279_, v_a_2280_, v___x_2281_, v___y_2286_, v___y_2287_, v___y_2288_, v___y_2289_);
if (lean_obj_tag(v___x_2291_) == 0)
{
lean_object* v_a_2292_; lean_object* v___x_2293_; 
v_a_2292_ = lean_ctor_get(v___x_2291_, 0);
lean_inc(v_a_2292_);
lean_dec_ref_known(v___x_2291_, 1);
v___x_2293_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize(v_snd_2277_, v_givenNames_2282_, v_a_2280_, v_fst_2283_, v___x_2284_, v___x_2281_, v_fst_2285_, v_a_2292_, v___y_2286_, v___y_2287_, v___y_2288_, v___y_2289_);
lean_dec_ref(v_a_2280_);
return v___x_2293_;
}
else
{
lean_object* v_a_2294_; lean_object* v___x_2296_; uint8_t v_isShared_2297_; uint8_t v_isSharedCheck_2301_; 
lean_dec(v_fst_2285_);
lean_dec_ref(v___x_2284_);
lean_dec_ref(v_a_2280_);
lean_dec(v_snd_2277_);
v_a_2294_ = lean_ctor_get(v___x_2291_, 0);
v_isSharedCheck_2301_ = !lean_is_exclusive(v___x_2291_);
if (v_isSharedCheck_2301_ == 0)
{
v___x_2296_ = v___x_2291_;
v_isShared_2297_ = v_isSharedCheck_2301_;
goto v_resetjp_2295_;
}
else
{
lean_inc(v_a_2294_);
lean_dec(v___x_2291_);
v___x_2296_ = lean_box(0);
v_isShared_2297_ = v_isSharedCheck_2301_;
goto v_resetjp_2295_;
}
v_resetjp_2295_:
{
lean_object* v___x_2299_; 
if (v_isShared_2297_ == 0)
{
v___x_2299_ = v___x_2296_;
goto v_reusejp_2298_;
}
else
{
lean_object* v_reuseFailAlloc_2300_; 
v_reuseFailAlloc_2300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2300_, 0, v_a_2294_);
v___x_2299_ = v_reuseFailAlloc_2300_;
goto v_reusejp_2298_;
}
v_reusejp_2298_:
{
return v___x_2299_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4___lam__0___boxed(lean_object* v_snd_2302_, lean_object* v___x_2303_, lean_object* v_fst_2304_, lean_object* v_a_2305_, lean_object* v___x_2306_, lean_object* v_givenNames_2307_, lean_object* v_fst_2308_, lean_object* v___x_2309_, lean_object* v_fst_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_){
_start:
{
lean_object* v_res_2316_; 
v_res_2316_ = l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4___lam__0(v_snd_2302_, v___x_2303_, v_fst_2304_, v_a_2305_, v___x_2306_, v_givenNames_2307_, v_fst_2308_, v___x_2309_, v_fst_2310_, v___y_2311_, v___y_2312_, v___y_2313_, v___y_2314_);
lean_dec(v___y_2314_);
lean_dec_ref(v___y_2313_);
lean_dec(v___y_2312_);
lean_dec_ref(v___y_2311_);
lean_dec_ref(v_fst_2308_);
lean_dec_ref(v_givenNames_2307_);
lean_dec_ref(v___x_2306_);
return v_res_2316_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_induction_spec__1(size_t v_sz_2317_, size_t v_i_2318_, lean_object* v_bs_2319_){
_start:
{
uint8_t v___x_2320_; 
v___x_2320_ = lean_usize_dec_lt(v_i_2318_, v_sz_2317_);
if (v___x_2320_ == 0)
{
return v_bs_2319_;
}
else
{
lean_object* v_v_2321_; lean_object* v___x_2322_; lean_object* v_bs_x27_2323_; lean_object* v___x_2324_; size_t v___x_2325_; size_t v___x_2326_; lean_object* v___x_2327_; 
v_v_2321_ = lean_array_uget(v_bs_2319_, v_i_2318_);
v___x_2322_ = lean_unsigned_to_nat(0u);
v_bs_x27_2323_ = lean_array_uset(v_bs_2319_, v_i_2318_, v___x_2322_);
v___x_2324_ = l_Lean_Expr_fvarId_x21(v_v_2321_);
lean_dec(v_v_2321_);
v___x_2325_ = ((size_t)1ULL);
v___x_2326_ = lean_usize_add(v_i_2318_, v___x_2325_);
v___x_2327_ = lean_array_uset(v_bs_x27_2323_, v_i_2318_, v___x_2324_);
v_i_2318_ = v___x_2326_;
v_bs_2319_ = v___x_2327_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_induction_spec__1___boxed(lean_object* v_sz_2329_, lean_object* v_i_2330_, lean_object* v_bs_2331_){
_start:
{
size_t v_sz_boxed_2332_; size_t v_i_boxed_2333_; lean_object* v_res_2334_; 
v_sz_boxed_2332_ = lean_unbox_usize(v_sz_2329_);
lean_dec(v_sz_2329_);
v_i_boxed_2333_ = lean_unbox_usize(v_i_2330_);
lean_dec(v_i_2330_);
v_res_2334_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_induction_spec__1(v_sz_boxed_2332_, v_i_boxed_2333_, v_bs_2331_);
return v_res_2334_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_MVarId_induction_spec__0(lean_object* v_majorTypeArgs_2335_, lean_object* v_val_2336_, lean_object* v_mvarId_2337_, lean_object* v_as_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_){
_start:
{
if (lean_obj_tag(v_as_2338_) == 0)
{
lean_object* v___x_2344_; lean_object* v___x_2345_; 
lean_dec(v_mvarId_2337_);
lean_dec_ref(v_val_2336_);
v___x_2344_ = lean_box(0);
v___x_2345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2345_, 0, v___x_2344_);
return v___x_2345_;
}
else
{
lean_object* v_head_2346_; 
v_head_2346_ = lean_ctor_get(v_as_2338_, 0);
lean_inc(v_head_2346_);
if (lean_obj_tag(v_head_2346_) == 0)
{
lean_object* v_tail_2347_; 
v_tail_2347_ = lean_ctor_get(v_as_2338_, 1);
lean_inc(v_tail_2347_);
lean_dec_ref_known(v_as_2338_, 2);
v_as_2338_ = v_tail_2347_;
goto _start;
}
else
{
lean_object* v_tail_2349_; lean_object* v___x_2351_; uint8_t v_isShared_2352_; uint8_t v_isSharedCheck_2372_; 
v_tail_2349_ = lean_ctor_get(v_as_2338_, 1);
v_isSharedCheck_2372_ = !lean_is_exclusive(v_as_2338_);
if (v_isSharedCheck_2372_ == 0)
{
lean_object* v_unused_2373_; 
v_unused_2373_ = lean_ctor_get(v_as_2338_, 0);
lean_dec(v_unused_2373_);
v___x_2351_ = v_as_2338_;
v_isShared_2352_ = v_isSharedCheck_2372_;
goto v_resetjp_2350_;
}
else
{
lean_inc(v_tail_2349_);
lean_dec(v_as_2338_);
v___x_2351_ = lean_box(0);
v_isShared_2352_ = v_isSharedCheck_2372_;
goto v_resetjp_2350_;
}
v_resetjp_2350_:
{
lean_object* v_val_2353_; lean_object* v___x_2355_; uint8_t v_isShared_2356_; uint8_t v_isSharedCheck_2371_; 
v_val_2353_ = lean_ctor_get(v_head_2346_, 0);
v_isSharedCheck_2371_ = !lean_is_exclusive(v_head_2346_);
if (v_isSharedCheck_2371_ == 0)
{
v___x_2355_ = v_head_2346_;
v_isShared_2356_ = v_isSharedCheck_2371_;
goto v_resetjp_2354_;
}
else
{
lean_inc(v_val_2353_);
lean_dec(v_head_2346_);
v___x_2355_ = lean_box(0);
v_isShared_2356_ = v_isSharedCheck_2371_;
goto v_resetjp_2354_;
}
v_resetjp_2354_:
{
lean_object* v___x_2357_; uint8_t v___x_2358_; 
v___x_2357_ = lean_array_get_size(v_majorTypeArgs_2335_);
v___x_2358_ = lean_nat_dec_le(v___x_2357_, v_val_2353_);
lean_dec(v_val_2353_);
if (v___x_2358_ == 0)
{
lean_del_object(v___x_2355_);
lean_del_object(v___x_2351_);
v_as_2338_ = v_tail_2349_;
goto _start;
}
else
{
lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2364_; 
v___x_2360_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1));
v___x_2361_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__5, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__5);
lean_inc_ref(v_val_2336_);
v___x_2362_ = l_Lean_indentExpr(v_val_2336_);
if (v_isShared_2352_ == 0)
{
lean_ctor_set_tag(v___x_2351_, 7);
lean_ctor_set(v___x_2351_, 1, v___x_2362_);
lean_ctor_set(v___x_2351_, 0, v___x_2361_);
v___x_2364_ = v___x_2351_;
goto v_reusejp_2363_;
}
else
{
lean_object* v_reuseFailAlloc_2370_; 
v_reuseFailAlloc_2370_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2370_, 0, v___x_2361_);
lean_ctor_set(v_reuseFailAlloc_2370_, 1, v___x_2362_);
v___x_2364_ = v_reuseFailAlloc_2370_;
goto v_reusejp_2363_;
}
v_reusejp_2363_:
{
lean_object* v___x_2366_; 
if (v_isShared_2356_ == 0)
{
lean_ctor_set(v___x_2355_, 0, v___x_2364_);
v___x_2366_ = v___x_2355_;
goto v_reusejp_2365_;
}
else
{
lean_object* v_reuseFailAlloc_2369_; 
v_reuseFailAlloc_2369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2369_, 0, v___x_2364_);
v___x_2366_ = v_reuseFailAlloc_2369_;
goto v_reusejp_2365_;
}
v_reusejp_2365_:
{
lean_object* v___x_2367_; 
lean_inc(v_mvarId_2337_);
v___x_2367_ = l_Lean_Meta_throwTacticEx___redArg(v___x_2360_, v_mvarId_2337_, v___x_2366_, v___y_2339_, v___y_2340_, v___y_2341_, v___y_2342_);
if (lean_obj_tag(v___x_2367_) == 0)
{
lean_dec_ref_known(v___x_2367_, 1);
v_as_2338_ = v_tail_2349_;
goto _start;
}
else
{
lean_dec(v_tail_2349_);
lean_dec(v_mvarId_2337_);
lean_dec_ref(v_val_2336_);
return v___x_2367_;
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
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_MVarId_induction_spec__0___boxed(lean_object* v_majorTypeArgs_2374_, lean_object* v_val_2375_, lean_object* v_mvarId_2376_, lean_object* v_as_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_){
_start:
{
lean_object* v_res_2383_; 
v_res_2383_ = l_List_forM___at___00Lean_MVarId_induction_spec__0(v_majorTypeArgs_2374_, v_val_2375_, v_mvarId_2376_, v_as_2377_, v___y_2378_, v___y_2379_, v___y_2380_, v___y_2381_);
lean_dec(v___y_2381_);
lean_dec_ref(v___y_2380_);
lean_dec(v___y_2379_);
lean_dec_ref(v___y_2378_);
lean_dec_ref(v_majorTypeArgs_2374_);
return v_res_2383_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__1(void){
_start:
{
lean_object* v___x_2385_; lean_object* v___x_2386_; 
v___x_2385_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__0));
v___x_2386_ = l_Lean_stringToMessageData(v___x_2385_);
return v___x_2386_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__3(void){
_start:
{
lean_object* v___x_2388_; lean_object* v___x_2389_; 
v___x_2388_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__2));
v___x_2389_ = l_Lean_stringToMessageData(v___x_2388_);
return v___x_2389_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__5(void){
_start:
{
lean_object* v___x_2391_; lean_object* v___x_2392_; 
v___x_2391_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__4));
v___x_2392_ = l_Lean_stringToMessageData(v___x_2391_);
return v___x_2392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4(lean_object* v_a_2393_, lean_object* v_val_2394_, lean_object* v_mvarId_2395_, lean_object* v_majorFVarId_2396_, lean_object* v_givenNames_2397_, lean_object* v_recursorName_2398_, lean_object* v_x_2399_, lean_object* v_x_2400_, lean_object* v_x_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_){
_start:
{
if (lean_obj_tag(v_x_2399_) == 5)
{
lean_object* v_fn_2407_; lean_object* v_arg_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; 
v_fn_2407_ = lean_ctor_get(v_x_2399_, 0);
lean_inc_ref(v_fn_2407_);
v_arg_2408_ = lean_ctor_get(v_x_2399_, 1);
lean_inc_ref(v_arg_2408_);
lean_dec_ref_known(v_x_2399_, 2);
v___x_2409_ = lean_array_set(v_x_2400_, v_x_2401_, v_arg_2408_);
v___x_2410_ = lean_unsigned_to_nat(1u);
v___x_2411_ = lean_nat_sub(v_x_2401_, v___x_2410_);
lean_dec(v_x_2401_);
v_x_2399_ = v_fn_2407_;
v_x_2400_ = v___x_2409_;
v_x_2401_ = v___x_2411_;
goto _start;
}
else
{
uint8_t v_depElim_2413_; lean_object* v_paramsPos_2414_; lean_object* v___x_2415_; lean_object* v___y_2417_; lean_object* v___y_2418_; lean_object* v___y_2419_; lean_object* v___y_2420_; lean_object* v___y_2421_; lean_object* v___y_2422_; lean_object* v___y_2423_; size_t v___y_2424_; lean_object* v___y_2425_; lean_object* v___y_2426_; lean_object* v___y_2427_; lean_object* v___y_2428_; lean_object* v_cls_2433_; lean_object* v___x_2434_; 
lean_dec(v_x_2401_);
lean_dec_ref(v_x_2399_);
v_depElim_2413_ = lean_ctor_get_uint8(v_a_2393_, sizeof(void*)*8);
v_paramsPos_2414_ = lean_ctor_get(v_a_2393_, 5);
v___x_2415_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1));
v_cls_2433_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__2));
lean_inc(v_paramsPos_2414_);
lean_inc(v_mvarId_2395_);
lean_inc_ref(v_val_2394_);
v___x_2434_ = l_List_forM___at___00Lean_MVarId_induction_spec__0(v_x_2400_, v_val_2394_, v_mvarId_2395_, v_paramsPos_2414_, v___y_2402_, v___y_2403_, v___y_2404_, v___y_2405_);
lean_dec_ref(v_x_2400_);
if (lean_obj_tag(v___x_2434_) == 0)
{
lean_object* v___x_2435_; 
lean_dec_ref_known(v___x_2434_, 1);
lean_inc_ref(v_a_2393_);
lean_inc(v_mvarId_2395_);
v___x_2435_ = l_Lean_Meta_getMajorTypeIndices(v_mvarId_2395_, v___x_2415_, v_a_2393_, v_val_2394_, v___y_2402_, v___y_2403_, v___y_2404_, v___y_2405_);
if (lean_obj_tag(v___x_2435_) == 0)
{
lean_object* v_a_2436_; lean_object* v___y_2438_; lean_object* v___y_2439_; lean_object* v___y_2440_; lean_object* v___y_2441_; lean_object* v___x_2525_; 
v_a_2436_ = lean_ctor_get(v___x_2435_, 0);
lean_inc(v_a_2436_);
lean_dec_ref_known(v___x_2435_, 1);
lean_inc(v_mvarId_2395_);
v___x_2525_ = l_Lean_MVarId_getType(v_mvarId_2395_, v___y_2402_, v___y_2403_, v___y_2404_, v___y_2405_);
if (lean_obj_tag(v___x_2525_) == 0)
{
if (v_depElim_2413_ == 0)
{
lean_object* v_a_2526_; lean_object* v___x_2527_; lean_object* v_a_2528_; lean_object* v___x_2530_; uint8_t v_isShared_2531_; uint8_t v_isSharedCheck_2550_; 
v_a_2526_ = lean_ctor_get(v___x_2525_, 0);
lean_inc(v_a_2526_);
lean_dec_ref_known(v___x_2525_, 1);
lean_inc(v_majorFVarId_2396_);
v___x_2527_ = l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2___redArg(v_a_2526_, v_majorFVarId_2396_, v___y_2403_);
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
lean_dec(v_recursorName_2398_);
v___y_2438_ = v___y_2402_;
v___y_2439_ = v___y_2403_;
v___y_2440_ = v___y_2404_;
v___y_2441_ = v___y_2405_;
goto v___jp_2437_;
}
else
{
lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2539_; 
v___x_2533_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__3, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__3);
v___x_2534_ = l_Lean_MessageData_ofName(v_recursorName_2398_);
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
lean_inc(v_mvarId_2395_);
v___x_2540_ = l_Lean_Meta_throwTacticEx___redArg(v___x_2415_, v_mvarId_2395_, v___x_2539_, v___y_2402_, v___y_2403_, v___y_2404_, v___y_2405_);
if (lean_obj_tag(v___x_2540_) == 0)
{
lean_dec_ref_known(v___x_2540_, 1);
v___y_2438_ = v___y_2402_;
v___y_2439_ = v___y_2403_;
v___y_2440_ = v___y_2404_;
v___y_2441_ = v___y_2405_;
goto v___jp_2437_;
}
else
{
lean_object* v_a_2541_; lean_object* v___x_2543_; uint8_t v_isShared_2544_; uint8_t v_isSharedCheck_2548_; 
lean_dec(v_a_2436_);
lean_dec_ref(v_givenNames_2397_);
lean_dec(v_majorFVarId_2396_);
lean_dec(v_mvarId_2395_);
lean_dec_ref(v_a_2393_);
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
lean_dec_ref_known(v___x_2525_, 1);
lean_dec(v_recursorName_2398_);
v___y_2438_ = v___y_2402_;
v___y_2439_ = v___y_2403_;
v___y_2440_ = v___y_2404_;
v___y_2441_ = v___y_2405_;
goto v___jp_2437_;
}
}
else
{
lean_object* v_a_2551_; lean_object* v___x_2553_; uint8_t v_isShared_2554_; uint8_t v_isSharedCheck_2558_; 
lean_dec(v_a_2436_);
lean_dec(v_recursorName_2398_);
lean_dec_ref(v_givenNames_2397_);
lean_dec(v_majorFVarId_2396_);
lean_dec(v_mvarId_2395_);
lean_dec_ref(v_a_2393_);
v_a_2551_ = lean_ctor_get(v___x_2525_, 0);
v_isSharedCheck_2558_ = !lean_is_exclusive(v___x_2525_);
if (v_isSharedCheck_2558_ == 0)
{
v___x_2553_ = v___x_2525_;
v_isShared_2554_ = v_isSharedCheck_2558_;
goto v_resetjp_2552_;
}
else
{
lean_inc(v_a_2551_);
lean_dec(v___x_2525_);
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
v___jp_2437_:
{
size_t v_sz_2442_; size_t v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; uint8_t v___x_2446_; uint8_t v___x_2447_; lean_object* v___x_2448_; 
v_sz_2442_ = lean_array_size(v_a_2436_);
v___x_2443_ = ((size_t)0ULL);
lean_inc(v_a_2436_);
v___x_2444_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_induction_spec__1(v_sz_2442_, v___x_2443_, v_a_2436_);
lean_inc(v_majorFVarId_2396_);
v___x_2445_ = lean_array_push(v___x_2444_, v_majorFVarId_2396_);
v___x_2446_ = 1;
v___x_2447_ = 0;
v___x_2448_ = l_Lean_MVarId_revert(v_mvarId_2395_, v___x_2445_, v___x_2446_, v___x_2447_, v___y_2438_, v___y_2439_, v___y_2440_, v___y_2441_);
if (lean_obj_tag(v___x_2448_) == 0)
{
lean_object* v_a_2449_; lean_object* v_fst_2450_; lean_object* v_snd_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; 
v_a_2449_ = lean_ctor_get(v___x_2448_, 0);
lean_inc(v_a_2449_);
lean_dec_ref_known(v___x_2448_, 1);
v_fst_2450_ = lean_ctor_get(v_a_2449_, 0);
lean_inc(v_fst_2450_);
v_snd_2451_ = lean_ctor_get(v_a_2449_, 1);
lean_inc(v_snd_2451_);
lean_dec(v_a_2449_);
v___x_2452_ = lean_array_get_size(v_a_2436_);
v___x_2453_ = lean_box(0);
v___x_2454_ = l_Lean_Meta_introNCore(v_snd_2451_, v___x_2452_, v___x_2453_, v___x_2447_, v___x_2446_, v___y_2438_, v___y_2439_, v___y_2440_, v___y_2441_);
if (lean_obj_tag(v___x_2454_) == 0)
{
lean_object* v_a_2455_; lean_object* v_fst_2456_; lean_object* v_snd_2457_; lean_object* v___x_2458_; 
v_a_2455_ = lean_ctor_get(v___x_2454_, 0);
lean_inc(v_a_2455_);
lean_dec_ref_known(v___x_2454_, 1);
v_fst_2456_ = lean_ctor_get(v_a_2455_, 0);
lean_inc(v_fst_2456_);
v_snd_2457_ = lean_ctor_get(v_a_2455_, 1);
lean_inc(v_snd_2457_);
lean_dec(v_a_2455_);
v___x_2458_ = l_Lean_Meta_intro1Core(v_snd_2457_, v___x_2446_, v___y_2438_, v___y_2439_, v___y_2440_, v___y_2441_);
if (lean_obj_tag(v___x_2458_) == 0)
{
lean_object* v_a_2459_; lean_object* v_fst_2460_; lean_object* v_snd_2461_; lean_object* v___x_2463_; uint8_t v_isShared_2464_; uint8_t v_isSharedCheck_2500_; 
v_a_2459_ = lean_ctor_get(v___x_2458_, 0);
lean_inc(v_a_2459_);
lean_dec_ref_known(v___x_2458_, 1);
v_fst_2460_ = lean_ctor_get(v_a_2459_, 0);
v_snd_2461_ = lean_ctor_get(v_a_2459_, 1);
v_isSharedCheck_2500_ = !lean_is_exclusive(v_a_2459_);
if (v_isSharedCheck_2500_ == 0)
{
v___x_2463_ = v_a_2459_;
v_isShared_2464_ = v_isSharedCheck_2500_;
goto v_resetjp_2462_;
}
else
{
lean_inc(v_snd_2461_);
lean_inc(v_fst_2460_);
lean_dec(v_a_2459_);
v___x_2463_ = lean_box(0);
v_isShared_2464_ = v_isSharedCheck_2500_;
goto v_resetjp_2462_;
}
v_resetjp_2462_:
{
lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2470_; 
v___x_2465_ = lean_box(0);
lean_inc(v_fst_2460_);
v___x_2466_ = l_Lean_mkFVar(v_fst_2460_);
lean_inc_ref(v___x_2466_);
v___x_2467_ = l_Lean_Meta_FVarSubst_insert(v___x_2465_, v_majorFVarId_2396_, v___x_2466_);
v___x_2468_ = lean_unsigned_to_nat(0u);
if (v_isShared_2464_ == 0)
{
lean_ctor_set(v___x_2463_, 1, v___x_2468_);
lean_ctor_set(v___x_2463_, 0, v___x_2467_);
v___x_2470_ = v___x_2463_;
goto v_reusejp_2469_;
}
else
{
lean_object* v_reuseFailAlloc_2499_; 
v_reuseFailAlloc_2499_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2499_, 0, v___x_2467_);
lean_ctor_set(v_reuseFailAlloc_2499_, 1, v___x_2468_);
v___x_2470_ = v_reuseFailAlloc_2499_;
goto v_reusejp_2469_;
}
v_reusejp_2469_:
{
lean_object* v___x_2471_; lean_object* v_toCold_2472_; lean_object* v_options_2473_; uint8_t v_hasTrace_2474_; 
v___x_2471_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_induction_spec__2(v_fst_2456_, v_a_2436_, v_sz_2442_, v___x_2443_, v___x_2470_);
lean_dec(v_a_2436_);
v_toCold_2472_ = lean_ctor_get(v___y_2440_, 0);
v_options_2473_ = lean_ctor_get(v_toCold_2472_, 2);
v_hasTrace_2474_ = lean_ctor_get_uint8(v_options_2473_, sizeof(void*)*1);
if (v_hasTrace_2474_ == 0)
{
lean_object* v_fst_2475_; 
v_fst_2475_ = lean_ctor_get(v___x_2471_, 0);
lean_inc(v_fst_2475_);
lean_dec_ref(v___x_2471_);
lean_inc(v_snd_2461_);
v___y_2417_ = v_fst_2450_;
v___y_2418_ = v_fst_2475_;
v___y_2419_ = v_snd_2461_;
v___y_2420_ = v_fst_2460_;
v___y_2421_ = v___x_2466_;
v___y_2422_ = v_fst_2456_;
v___y_2423_ = v_snd_2461_;
v___y_2424_ = v___x_2443_;
v___y_2425_ = v___y_2438_;
v___y_2426_ = v___y_2439_;
v___y_2427_ = v___y_2440_;
v___y_2428_ = v___y_2441_;
goto v___jp_2416_;
}
else
{
lean_object* v_fst_2476_; lean_object* v___x_2478_; uint8_t v_isShared_2479_; uint8_t v_isSharedCheck_2497_; 
v_fst_2476_ = lean_ctor_get(v___x_2471_, 0);
v_isSharedCheck_2497_ = !lean_is_exclusive(v___x_2471_);
if (v_isSharedCheck_2497_ == 0)
{
lean_object* v_unused_2498_; 
v_unused_2498_ = lean_ctor_get(v___x_2471_, 1);
lean_dec(v_unused_2498_);
v___x_2478_ = v___x_2471_;
v_isShared_2479_ = v_isSharedCheck_2497_;
goto v_resetjp_2477_;
}
else
{
lean_inc(v_fst_2476_);
lean_dec(v___x_2471_);
v___x_2478_ = lean_box(0);
v_isShared_2479_ = v_isSharedCheck_2497_;
goto v_resetjp_2477_;
}
v_resetjp_2477_:
{
lean_object* v_inheritedTraceOptions_2480_; lean_object* v___x_2481_; uint8_t v___x_2482_; 
v_inheritedTraceOptions_2480_ = lean_ctor_get(v_toCold_2472_, 11);
v___x_2481_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5);
v___x_2482_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2480_, v_options_2473_, v___x_2481_);
if (v___x_2482_ == 0)
{
lean_del_object(v___x_2478_);
lean_inc(v_snd_2461_);
v___y_2417_ = v_fst_2450_;
v___y_2418_ = v_fst_2476_;
v___y_2419_ = v_snd_2461_;
v___y_2420_ = v_fst_2460_;
v___y_2421_ = v___x_2466_;
v___y_2422_ = v_fst_2456_;
v___y_2423_ = v_snd_2461_;
v___y_2424_ = v___x_2443_;
v___y_2425_ = v___y_2438_;
v___y_2426_ = v___y_2439_;
v___y_2427_ = v___y_2440_;
v___y_2428_ = v___y_2441_;
goto v___jp_2416_;
}
else
{
lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2486_; 
v___x_2483_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__1);
lean_inc(v_snd_2461_);
v___x_2484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2484_, 0, v_snd_2461_);
if (v_isShared_2479_ == 0)
{
lean_ctor_set_tag(v___x_2478_, 7);
lean_ctor_set(v___x_2478_, 1, v___x_2484_);
lean_ctor_set(v___x_2478_, 0, v___x_2483_);
v___x_2486_ = v___x_2478_;
goto v_reusejp_2485_;
}
else
{
lean_object* v_reuseFailAlloc_2496_; 
v_reuseFailAlloc_2496_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2496_, 0, v___x_2483_);
lean_ctor_set(v_reuseFailAlloc_2496_, 1, v___x_2484_);
v___x_2486_ = v_reuseFailAlloc_2496_;
goto v_reusejp_2485_;
}
v_reusejp_2485_:
{
lean_object* v___x_2487_; 
v___x_2487_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1(v_cls_2433_, v___x_2486_, v___y_2438_, v___y_2439_, v___y_2440_, v___y_2441_);
if (lean_obj_tag(v___x_2487_) == 0)
{
lean_dec_ref_known(v___x_2487_, 1);
lean_inc(v_snd_2461_);
v___y_2417_ = v_fst_2450_;
v___y_2418_ = v_fst_2476_;
v___y_2419_ = v_snd_2461_;
v___y_2420_ = v_fst_2460_;
v___y_2421_ = v___x_2466_;
v___y_2422_ = v_fst_2456_;
v___y_2423_ = v_snd_2461_;
v___y_2424_ = v___x_2443_;
v___y_2425_ = v___y_2438_;
v___y_2426_ = v___y_2439_;
v___y_2427_ = v___y_2440_;
v___y_2428_ = v___y_2441_;
goto v___jp_2416_;
}
else
{
lean_object* v_a_2488_; lean_object* v___x_2490_; uint8_t v_isShared_2491_; uint8_t v_isSharedCheck_2495_; 
lean_dec(v_fst_2476_);
lean_dec_ref(v___x_2466_);
lean_dec(v_snd_2461_);
lean_dec(v_fst_2460_);
lean_dec(v_fst_2456_);
lean_dec(v_fst_2450_);
lean_dec_ref(v_givenNames_2397_);
lean_dec_ref(v_a_2393_);
v_a_2488_ = lean_ctor_get(v___x_2487_, 0);
v_isSharedCheck_2495_ = !lean_is_exclusive(v___x_2487_);
if (v_isSharedCheck_2495_ == 0)
{
v___x_2490_ = v___x_2487_;
v_isShared_2491_ = v_isSharedCheck_2495_;
goto v_resetjp_2489_;
}
else
{
lean_inc(v_a_2488_);
lean_dec(v___x_2487_);
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
}
}
}
}
}
}
else
{
lean_object* v_a_2501_; lean_object* v___x_2503_; uint8_t v_isShared_2504_; uint8_t v_isSharedCheck_2508_; 
lean_dec(v_fst_2456_);
lean_dec(v_fst_2450_);
lean_dec(v_a_2436_);
lean_dec_ref(v_givenNames_2397_);
lean_dec(v_majorFVarId_2396_);
lean_dec_ref(v_a_2393_);
v_a_2501_ = lean_ctor_get(v___x_2458_, 0);
v_isSharedCheck_2508_ = !lean_is_exclusive(v___x_2458_);
if (v_isSharedCheck_2508_ == 0)
{
v___x_2503_ = v___x_2458_;
v_isShared_2504_ = v_isSharedCheck_2508_;
goto v_resetjp_2502_;
}
else
{
lean_inc(v_a_2501_);
lean_dec(v___x_2458_);
v___x_2503_ = lean_box(0);
v_isShared_2504_ = v_isSharedCheck_2508_;
goto v_resetjp_2502_;
}
v_resetjp_2502_:
{
lean_object* v___x_2506_; 
if (v_isShared_2504_ == 0)
{
v___x_2506_ = v___x_2503_;
goto v_reusejp_2505_;
}
else
{
lean_object* v_reuseFailAlloc_2507_; 
v_reuseFailAlloc_2507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2507_, 0, v_a_2501_);
v___x_2506_ = v_reuseFailAlloc_2507_;
goto v_reusejp_2505_;
}
v_reusejp_2505_:
{
return v___x_2506_;
}
}
}
}
else
{
lean_object* v_a_2509_; lean_object* v___x_2511_; uint8_t v_isShared_2512_; uint8_t v_isSharedCheck_2516_; 
lean_dec(v_fst_2450_);
lean_dec(v_a_2436_);
lean_dec_ref(v_givenNames_2397_);
lean_dec(v_majorFVarId_2396_);
lean_dec_ref(v_a_2393_);
v_a_2509_ = lean_ctor_get(v___x_2454_, 0);
v_isSharedCheck_2516_ = !lean_is_exclusive(v___x_2454_);
if (v_isSharedCheck_2516_ == 0)
{
v___x_2511_ = v___x_2454_;
v_isShared_2512_ = v_isSharedCheck_2516_;
goto v_resetjp_2510_;
}
else
{
lean_inc(v_a_2509_);
lean_dec(v___x_2454_);
v___x_2511_ = lean_box(0);
v_isShared_2512_ = v_isSharedCheck_2516_;
goto v_resetjp_2510_;
}
v_resetjp_2510_:
{
lean_object* v___x_2514_; 
if (v_isShared_2512_ == 0)
{
v___x_2514_ = v___x_2511_;
goto v_reusejp_2513_;
}
else
{
lean_object* v_reuseFailAlloc_2515_; 
v_reuseFailAlloc_2515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2515_, 0, v_a_2509_);
v___x_2514_ = v_reuseFailAlloc_2515_;
goto v_reusejp_2513_;
}
v_reusejp_2513_:
{
return v___x_2514_;
}
}
}
}
else
{
lean_object* v_a_2517_; lean_object* v___x_2519_; uint8_t v_isShared_2520_; uint8_t v_isSharedCheck_2524_; 
lean_dec(v_a_2436_);
lean_dec_ref(v_givenNames_2397_);
lean_dec(v_majorFVarId_2396_);
lean_dec_ref(v_a_2393_);
v_a_2517_ = lean_ctor_get(v___x_2448_, 0);
v_isSharedCheck_2524_ = !lean_is_exclusive(v___x_2448_);
if (v_isSharedCheck_2524_ == 0)
{
v___x_2519_ = v___x_2448_;
v_isShared_2520_ = v_isSharedCheck_2524_;
goto v_resetjp_2518_;
}
else
{
lean_inc(v_a_2517_);
lean_dec(v___x_2448_);
v___x_2519_ = lean_box(0);
v_isShared_2520_ = v_isSharedCheck_2524_;
goto v_resetjp_2518_;
}
v_resetjp_2518_:
{
lean_object* v___x_2522_; 
if (v_isShared_2520_ == 0)
{
v___x_2522_ = v___x_2519_;
goto v_reusejp_2521_;
}
else
{
lean_object* v_reuseFailAlloc_2523_; 
v_reuseFailAlloc_2523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2523_, 0, v_a_2517_);
v___x_2522_ = v_reuseFailAlloc_2523_;
goto v_reusejp_2521_;
}
v_reusejp_2521_:
{
return v___x_2522_;
}
}
}
}
}
else
{
lean_object* v_a_2559_; lean_object* v___x_2561_; uint8_t v_isShared_2562_; uint8_t v_isSharedCheck_2566_; 
lean_dec(v_recursorName_2398_);
lean_dec_ref(v_givenNames_2397_);
lean_dec(v_majorFVarId_2396_);
lean_dec(v_mvarId_2395_);
lean_dec_ref(v_a_2393_);
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
}
else
{
lean_object* v_a_2567_; lean_object* v___x_2569_; uint8_t v_isShared_2570_; uint8_t v_isSharedCheck_2574_; 
lean_dec(v_recursorName_2398_);
lean_dec_ref(v_givenNames_2397_);
lean_dec(v_majorFVarId_2396_);
lean_dec(v_mvarId_2395_);
lean_dec_ref(v_val_2394_);
lean_dec_ref(v_a_2393_);
v_a_2567_ = lean_ctor_get(v___x_2434_, 0);
v_isSharedCheck_2574_ = !lean_is_exclusive(v___x_2434_);
if (v_isSharedCheck_2574_ == 0)
{
v___x_2569_ = v___x_2434_;
v_isShared_2570_ = v_isSharedCheck_2574_;
goto v_resetjp_2568_;
}
else
{
lean_inc(v_a_2567_);
lean_dec(v___x_2434_);
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
v___jp_2416_:
{
size_t v_sz_2429_; lean_object* v___x_2430_; lean_object* v___f_2431_; lean_object* v___x_2432_; 
v_sz_2429_ = lean_array_size(v___y_2422_);
v___x_2430_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__3(v_sz_2429_, v___y_2424_, v___y_2422_);
v___f_2431_ = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4___lam__0___boxed), 14, 9);
lean_closure_set(v___f_2431_, 0, v___y_2419_);
lean_closure_set(v___f_2431_, 1, v___x_2415_);
lean_closure_set(v___f_2431_, 2, v___y_2420_);
lean_closure_set(v___f_2431_, 3, v_a_2393_);
lean_closure_set(v___f_2431_, 4, v___x_2430_);
lean_closure_set(v___f_2431_, 5, v_givenNames_2397_);
lean_closure_set(v___f_2431_, 6, v___y_2417_);
lean_closure_set(v___f_2431_, 7, v___y_2421_);
lean_closure_set(v___f_2431_, 8, v___y_2418_);
v___x_2432_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___redArg(v___y_2423_, v___f_2431_, v___y_2425_, v___y_2426_, v___y_2427_, v___y_2428_);
return v___x_2432_;
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
uint8_t v_depElim_2610_; lean_object* v_paramsPos_2611_; lean_object* v___x_2612_; lean_object* v___y_2614_; lean_object* v___y_2615_; lean_object* v___y_2616_; lean_object* v___y_2617_; lean_object* v___y_2618_; lean_object* v___y_2619_; lean_object* v___y_2620_; size_t v___y_2621_; lean_object* v___y_2622_; lean_object* v___y_2623_; lean_object* v___y_2624_; lean_object* v___y_2625_; lean_object* v_cls_2630_; lean_object* v___x_2631_; 
lean_dec_ref(v_x_2596_);
v_depElim_2610_ = lean_ctor_get_uint8(v_a_2592_, sizeof(void*)*8);
v_paramsPos_2611_ = lean_ctor_get(v_a_2592_, 5);
v___x_2612_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1));
v_cls_2630_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__2));
lean_inc(v_paramsPos_2611_);
lean_inc(v_mvarId_2591_);
lean_inc_ref(v_val_2590_);
v___x_2631_ = l_List_forM___at___00Lean_MVarId_induction_spec__0(v_x_2597_, v_val_2590_, v_mvarId_2591_, v_paramsPos_2611_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_);
lean_dec_ref(v_x_2597_);
if (lean_obj_tag(v___x_2631_) == 0)
{
lean_object* v___x_2632_; 
lean_dec_ref_known(v___x_2631_, 1);
lean_inc_ref(v_a_2592_);
lean_inc(v_mvarId_2591_);
v___x_2632_ = l_Lean_Meta_getMajorTypeIndices(v_mvarId_2591_, v___x_2612_, v_a_2592_, v_val_2590_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_);
if (lean_obj_tag(v___x_2632_) == 0)
{
lean_object* v_a_2633_; lean_object* v___y_2635_; lean_object* v___y_2636_; lean_object* v___y_2637_; lean_object* v___y_2638_; lean_object* v___x_2722_; 
v_a_2633_ = lean_ctor_get(v___x_2632_, 0);
lean_inc(v_a_2633_);
lean_dec_ref_known(v___x_2632_, 1);
lean_inc(v_mvarId_2591_);
v___x_2722_ = l_Lean_MVarId_getType(v_mvarId_2591_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_);
if (lean_obj_tag(v___x_2722_) == 0)
{
if (v_depElim_2610_ == 0)
{
lean_object* v_a_2723_; lean_object* v___x_2724_; lean_object* v_a_2725_; lean_object* v___x_2727_; uint8_t v_isShared_2728_; uint8_t v_isSharedCheck_2747_; 
v_a_2723_ = lean_ctor_get(v___x_2722_, 0);
lean_inc(v_a_2723_);
lean_dec_ref_known(v___x_2722_, 1);
lean_inc(v_majorFVarId_2593_);
v___x_2724_ = l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2___redArg(v_a_2723_, v_majorFVarId_2593_, v___y_2600_);
v_a_2725_ = lean_ctor_get(v___x_2724_, 0);
v_isSharedCheck_2747_ = !lean_is_exclusive(v___x_2724_);
if (v_isSharedCheck_2747_ == 0)
{
v___x_2727_ = v___x_2724_;
v_isShared_2728_ = v_isSharedCheck_2747_;
goto v_resetjp_2726_;
}
else
{
lean_inc(v_a_2725_);
lean_dec(v___x_2724_);
v___x_2727_ = lean_box(0);
v_isShared_2728_ = v_isSharedCheck_2747_;
goto v_resetjp_2726_;
}
v_resetjp_2726_:
{
uint8_t v___x_2729_; 
v___x_2729_ = lean_unbox(v_a_2725_);
lean_dec(v_a_2725_);
if (v___x_2729_ == 0)
{
lean_del_object(v___x_2727_);
lean_dec(v_recursorName_2595_);
v___y_2635_ = v___y_2599_;
v___y_2636_ = v___y_2600_;
v___y_2637_ = v___y_2601_;
v___y_2638_ = v___y_2602_;
goto v___jp_2634_;
}
else
{
lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; lean_object* v___x_2736_; 
v___x_2730_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__3, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__3);
v___x_2731_ = l_Lean_MessageData_ofName(v_recursorName_2595_);
v___x_2732_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2732_, 0, v___x_2730_);
lean_ctor_set(v___x_2732_, 1, v___x_2731_);
v___x_2733_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__5, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__5_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__5);
v___x_2734_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2734_, 0, v___x_2732_);
lean_ctor_set(v___x_2734_, 1, v___x_2733_);
if (v_isShared_2728_ == 0)
{
lean_ctor_set_tag(v___x_2727_, 1);
lean_ctor_set(v___x_2727_, 0, v___x_2734_);
v___x_2736_ = v___x_2727_;
goto v_reusejp_2735_;
}
else
{
lean_object* v_reuseFailAlloc_2746_; 
v_reuseFailAlloc_2746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2746_, 0, v___x_2734_);
v___x_2736_ = v_reuseFailAlloc_2746_;
goto v_reusejp_2735_;
}
v_reusejp_2735_:
{
lean_object* v___x_2737_; 
lean_inc(v_mvarId_2591_);
v___x_2737_ = l_Lean_Meta_throwTacticEx___redArg(v___x_2612_, v_mvarId_2591_, v___x_2736_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_);
if (lean_obj_tag(v___x_2737_) == 0)
{
lean_dec_ref_known(v___x_2737_, 1);
v___y_2635_ = v___y_2599_;
v___y_2636_ = v___y_2600_;
v___y_2637_ = v___y_2601_;
v___y_2638_ = v___y_2602_;
goto v___jp_2634_;
}
else
{
lean_object* v_a_2738_; lean_object* v___x_2740_; uint8_t v_isShared_2741_; uint8_t v_isSharedCheck_2745_; 
lean_dec(v_a_2633_);
lean_dec_ref(v_givenNames_2594_);
lean_dec(v_majorFVarId_2593_);
lean_dec_ref(v_a_2592_);
lean_dec(v_mvarId_2591_);
v_a_2738_ = lean_ctor_get(v___x_2737_, 0);
v_isSharedCheck_2745_ = !lean_is_exclusive(v___x_2737_);
if (v_isSharedCheck_2745_ == 0)
{
v___x_2740_ = v___x_2737_;
v_isShared_2741_ = v_isSharedCheck_2745_;
goto v_resetjp_2739_;
}
else
{
lean_inc(v_a_2738_);
lean_dec(v___x_2737_);
v___x_2740_ = lean_box(0);
v_isShared_2741_ = v_isSharedCheck_2745_;
goto v_resetjp_2739_;
}
v_resetjp_2739_:
{
lean_object* v___x_2743_; 
if (v_isShared_2741_ == 0)
{
v___x_2743_ = v___x_2740_;
goto v_reusejp_2742_;
}
else
{
lean_object* v_reuseFailAlloc_2744_; 
v_reuseFailAlloc_2744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2744_, 0, v_a_2738_);
v___x_2743_ = v_reuseFailAlloc_2744_;
goto v_reusejp_2742_;
}
v_reusejp_2742_:
{
return v___x_2743_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v___x_2722_, 1);
lean_dec(v_recursorName_2595_);
v___y_2635_ = v___y_2599_;
v___y_2636_ = v___y_2600_;
v___y_2637_ = v___y_2601_;
v___y_2638_ = v___y_2602_;
goto v___jp_2634_;
}
}
else
{
lean_object* v_a_2748_; lean_object* v___x_2750_; uint8_t v_isShared_2751_; uint8_t v_isSharedCheck_2755_; 
lean_dec(v_a_2633_);
lean_dec(v_recursorName_2595_);
lean_dec_ref(v_givenNames_2594_);
lean_dec(v_majorFVarId_2593_);
lean_dec_ref(v_a_2592_);
lean_dec(v_mvarId_2591_);
v_a_2748_ = lean_ctor_get(v___x_2722_, 0);
v_isSharedCheck_2755_ = !lean_is_exclusive(v___x_2722_);
if (v_isSharedCheck_2755_ == 0)
{
v___x_2750_ = v___x_2722_;
v_isShared_2751_ = v_isSharedCheck_2755_;
goto v_resetjp_2749_;
}
else
{
lean_inc(v_a_2748_);
lean_dec(v___x_2722_);
v___x_2750_ = lean_box(0);
v_isShared_2751_ = v_isSharedCheck_2755_;
goto v_resetjp_2749_;
}
v_resetjp_2749_:
{
lean_object* v___x_2753_; 
if (v_isShared_2751_ == 0)
{
v___x_2753_ = v___x_2750_;
goto v_reusejp_2752_;
}
else
{
lean_object* v_reuseFailAlloc_2754_; 
v_reuseFailAlloc_2754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2754_, 0, v_a_2748_);
v___x_2753_ = v_reuseFailAlloc_2754_;
goto v_reusejp_2752_;
}
v_reusejp_2752_:
{
return v___x_2753_;
}
}
}
v___jp_2634_:
{
size_t v_sz_2639_; size_t v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; uint8_t v___x_2643_; uint8_t v___x_2644_; lean_object* v___x_2645_; 
v_sz_2639_ = lean_array_size(v_a_2633_);
v___x_2640_ = ((size_t)0ULL);
lean_inc(v_a_2633_);
v___x_2641_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_induction_spec__1(v_sz_2639_, v___x_2640_, v_a_2633_);
lean_inc(v_majorFVarId_2593_);
v___x_2642_ = lean_array_push(v___x_2641_, v_majorFVarId_2593_);
v___x_2643_ = 1;
v___x_2644_ = 0;
v___x_2645_ = l_Lean_MVarId_revert(v_mvarId_2591_, v___x_2642_, v___x_2643_, v___x_2644_, v___y_2635_, v___y_2636_, v___y_2637_, v___y_2638_);
if (lean_obj_tag(v___x_2645_) == 0)
{
lean_object* v_a_2646_; lean_object* v_fst_2647_; lean_object* v_snd_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; 
v_a_2646_ = lean_ctor_get(v___x_2645_, 0);
lean_inc(v_a_2646_);
lean_dec_ref_known(v___x_2645_, 1);
v_fst_2647_ = lean_ctor_get(v_a_2646_, 0);
lean_inc(v_fst_2647_);
v_snd_2648_ = lean_ctor_get(v_a_2646_, 1);
lean_inc(v_snd_2648_);
lean_dec(v_a_2646_);
v___x_2649_ = lean_array_get_size(v_a_2633_);
v___x_2650_ = lean_box(0);
v___x_2651_ = l_Lean_Meta_introNCore(v_snd_2648_, v___x_2649_, v___x_2650_, v___x_2644_, v___x_2643_, v___y_2635_, v___y_2636_, v___y_2637_, v___y_2638_);
if (lean_obj_tag(v___x_2651_) == 0)
{
lean_object* v_a_2652_; lean_object* v_fst_2653_; lean_object* v_snd_2654_; lean_object* v___x_2655_; 
v_a_2652_ = lean_ctor_get(v___x_2651_, 0);
lean_inc(v_a_2652_);
lean_dec_ref_known(v___x_2651_, 1);
v_fst_2653_ = lean_ctor_get(v_a_2652_, 0);
lean_inc(v_fst_2653_);
v_snd_2654_ = lean_ctor_get(v_a_2652_, 1);
lean_inc(v_snd_2654_);
lean_dec(v_a_2652_);
v___x_2655_ = l_Lean_Meta_intro1Core(v_snd_2654_, v___x_2643_, v___y_2635_, v___y_2636_, v___y_2637_, v___y_2638_);
if (lean_obj_tag(v___x_2655_) == 0)
{
lean_object* v_a_2656_; lean_object* v_fst_2657_; lean_object* v_snd_2658_; lean_object* v___x_2660_; uint8_t v_isShared_2661_; uint8_t v_isSharedCheck_2697_; 
v_a_2656_ = lean_ctor_get(v___x_2655_, 0);
lean_inc(v_a_2656_);
lean_dec_ref_known(v___x_2655_, 1);
v_fst_2657_ = lean_ctor_get(v_a_2656_, 0);
v_snd_2658_ = lean_ctor_get(v_a_2656_, 1);
v_isSharedCheck_2697_ = !lean_is_exclusive(v_a_2656_);
if (v_isSharedCheck_2697_ == 0)
{
v___x_2660_ = v_a_2656_;
v_isShared_2661_ = v_isSharedCheck_2697_;
goto v_resetjp_2659_;
}
else
{
lean_inc(v_snd_2658_);
lean_inc(v_fst_2657_);
lean_dec(v_a_2656_);
v___x_2660_ = lean_box(0);
v_isShared_2661_ = v_isSharedCheck_2697_;
goto v_resetjp_2659_;
}
v_resetjp_2659_:
{
lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2667_; 
v___x_2662_ = lean_box(0);
lean_inc(v_fst_2657_);
v___x_2663_ = l_Lean_mkFVar(v_fst_2657_);
lean_inc_ref(v___x_2663_);
v___x_2664_ = l_Lean_Meta_FVarSubst_insert(v___x_2662_, v_majorFVarId_2593_, v___x_2663_);
v___x_2665_ = lean_unsigned_to_nat(0u);
if (v_isShared_2661_ == 0)
{
lean_ctor_set(v___x_2660_, 1, v___x_2665_);
lean_ctor_set(v___x_2660_, 0, v___x_2664_);
v___x_2667_ = v___x_2660_;
goto v_reusejp_2666_;
}
else
{
lean_object* v_reuseFailAlloc_2696_; 
v_reuseFailAlloc_2696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2696_, 0, v___x_2664_);
lean_ctor_set(v_reuseFailAlloc_2696_, 1, v___x_2665_);
v___x_2667_ = v_reuseFailAlloc_2696_;
goto v_reusejp_2666_;
}
v_reusejp_2666_:
{
lean_object* v___x_2668_; lean_object* v_toCold_2669_; lean_object* v_options_2670_; uint8_t v_hasTrace_2671_; 
v___x_2668_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_induction_spec__2(v_fst_2653_, v_a_2633_, v_sz_2639_, v___x_2640_, v___x_2667_);
lean_dec(v_a_2633_);
v_toCold_2669_ = lean_ctor_get(v___y_2637_, 0);
v_options_2670_ = lean_ctor_get(v_toCold_2669_, 2);
v_hasTrace_2671_ = lean_ctor_get_uint8(v_options_2670_, sizeof(void*)*1);
if (v_hasTrace_2671_ == 0)
{
lean_object* v_fst_2672_; 
v_fst_2672_ = lean_ctor_get(v___x_2668_, 0);
lean_inc(v_fst_2672_);
lean_dec_ref(v___x_2668_);
lean_inc(v_snd_2658_);
v___y_2614_ = v_fst_2657_;
v___y_2615_ = v_snd_2658_;
v___y_2616_ = v___x_2663_;
v___y_2617_ = v_fst_2647_;
v___y_2618_ = v_fst_2672_;
v___y_2619_ = v_snd_2658_;
v___y_2620_ = v_fst_2653_;
v___y_2621_ = v___x_2640_;
v___y_2622_ = v___y_2635_;
v___y_2623_ = v___y_2636_;
v___y_2624_ = v___y_2637_;
v___y_2625_ = v___y_2638_;
goto v___jp_2613_;
}
else
{
lean_object* v_fst_2673_; lean_object* v___x_2675_; uint8_t v_isShared_2676_; uint8_t v_isSharedCheck_2694_; 
v_fst_2673_ = lean_ctor_get(v___x_2668_, 0);
v_isSharedCheck_2694_ = !lean_is_exclusive(v___x_2668_);
if (v_isSharedCheck_2694_ == 0)
{
lean_object* v_unused_2695_; 
v_unused_2695_ = lean_ctor_get(v___x_2668_, 1);
lean_dec(v_unused_2695_);
v___x_2675_ = v___x_2668_;
v_isShared_2676_ = v_isSharedCheck_2694_;
goto v_resetjp_2674_;
}
else
{
lean_inc(v_fst_2673_);
lean_dec(v___x_2668_);
v___x_2675_ = lean_box(0);
v_isShared_2676_ = v_isSharedCheck_2694_;
goto v_resetjp_2674_;
}
v_resetjp_2674_:
{
lean_object* v_inheritedTraceOptions_2677_; lean_object* v___x_2678_; uint8_t v___x_2679_; 
v_inheritedTraceOptions_2677_ = lean_ctor_get(v_toCold_2669_, 11);
v___x_2678_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5);
v___x_2679_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2677_, v_options_2670_, v___x_2678_);
if (v___x_2679_ == 0)
{
lean_del_object(v___x_2675_);
lean_inc(v_snd_2658_);
v___y_2614_ = v_fst_2657_;
v___y_2615_ = v_snd_2658_;
v___y_2616_ = v___x_2663_;
v___y_2617_ = v_fst_2647_;
v___y_2618_ = v_fst_2673_;
v___y_2619_ = v_snd_2658_;
v___y_2620_ = v_fst_2653_;
v___y_2621_ = v___x_2640_;
v___y_2622_ = v___y_2635_;
v___y_2623_ = v___y_2636_;
v___y_2624_ = v___y_2637_;
v___y_2625_ = v___y_2638_;
goto v___jp_2613_;
}
else
{
lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2683_; 
v___x_2680_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__1);
lean_inc(v_snd_2658_);
v___x_2681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2681_, 0, v_snd_2658_);
if (v_isShared_2676_ == 0)
{
lean_ctor_set_tag(v___x_2675_, 7);
lean_ctor_set(v___x_2675_, 1, v___x_2681_);
lean_ctor_set(v___x_2675_, 0, v___x_2680_);
v___x_2683_ = v___x_2675_;
goto v_reusejp_2682_;
}
else
{
lean_object* v_reuseFailAlloc_2693_; 
v_reuseFailAlloc_2693_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2693_, 0, v___x_2680_);
lean_ctor_set(v_reuseFailAlloc_2693_, 1, v___x_2681_);
v___x_2683_ = v_reuseFailAlloc_2693_;
goto v_reusejp_2682_;
}
v_reusejp_2682_:
{
lean_object* v___x_2684_; 
v___x_2684_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1(v_cls_2630_, v___x_2683_, v___y_2635_, v___y_2636_, v___y_2637_, v___y_2638_);
if (lean_obj_tag(v___x_2684_) == 0)
{
lean_dec_ref_known(v___x_2684_, 1);
lean_inc(v_snd_2658_);
v___y_2614_ = v_fst_2657_;
v___y_2615_ = v_snd_2658_;
v___y_2616_ = v___x_2663_;
v___y_2617_ = v_fst_2647_;
v___y_2618_ = v_fst_2673_;
v___y_2619_ = v_snd_2658_;
v___y_2620_ = v_fst_2653_;
v___y_2621_ = v___x_2640_;
v___y_2622_ = v___y_2635_;
v___y_2623_ = v___y_2636_;
v___y_2624_ = v___y_2637_;
v___y_2625_ = v___y_2638_;
goto v___jp_2613_;
}
else
{
lean_object* v_a_2685_; lean_object* v___x_2687_; uint8_t v_isShared_2688_; uint8_t v_isSharedCheck_2692_; 
lean_dec(v_fst_2673_);
lean_dec_ref(v___x_2663_);
lean_dec(v_snd_2658_);
lean_dec(v_fst_2657_);
lean_dec(v_fst_2653_);
lean_dec(v_fst_2647_);
lean_dec_ref(v_givenNames_2594_);
lean_dec_ref(v_a_2592_);
v_a_2685_ = lean_ctor_get(v___x_2684_, 0);
v_isSharedCheck_2692_ = !lean_is_exclusive(v___x_2684_);
if (v_isSharedCheck_2692_ == 0)
{
v___x_2687_ = v___x_2684_;
v_isShared_2688_ = v_isSharedCheck_2692_;
goto v_resetjp_2686_;
}
else
{
lean_inc(v_a_2685_);
lean_dec(v___x_2684_);
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
}
}
}
}
}
}
else
{
lean_object* v_a_2698_; lean_object* v___x_2700_; uint8_t v_isShared_2701_; uint8_t v_isSharedCheck_2705_; 
lean_dec(v_fst_2653_);
lean_dec(v_fst_2647_);
lean_dec(v_a_2633_);
lean_dec_ref(v_givenNames_2594_);
lean_dec(v_majorFVarId_2593_);
lean_dec_ref(v_a_2592_);
v_a_2698_ = lean_ctor_get(v___x_2655_, 0);
v_isSharedCheck_2705_ = !lean_is_exclusive(v___x_2655_);
if (v_isSharedCheck_2705_ == 0)
{
v___x_2700_ = v___x_2655_;
v_isShared_2701_ = v_isSharedCheck_2705_;
goto v_resetjp_2699_;
}
else
{
lean_inc(v_a_2698_);
lean_dec(v___x_2655_);
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
}
else
{
lean_object* v_a_2706_; lean_object* v___x_2708_; uint8_t v_isShared_2709_; uint8_t v_isSharedCheck_2713_; 
lean_dec(v_fst_2647_);
lean_dec(v_a_2633_);
lean_dec_ref(v_givenNames_2594_);
lean_dec(v_majorFVarId_2593_);
lean_dec_ref(v_a_2592_);
v_a_2706_ = lean_ctor_get(v___x_2651_, 0);
v_isSharedCheck_2713_ = !lean_is_exclusive(v___x_2651_);
if (v_isSharedCheck_2713_ == 0)
{
v___x_2708_ = v___x_2651_;
v_isShared_2709_ = v_isSharedCheck_2713_;
goto v_resetjp_2707_;
}
else
{
lean_inc(v_a_2706_);
lean_dec(v___x_2651_);
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
}
else
{
lean_object* v_a_2714_; lean_object* v___x_2716_; uint8_t v_isShared_2717_; uint8_t v_isSharedCheck_2721_; 
lean_dec(v_a_2633_);
lean_dec_ref(v_givenNames_2594_);
lean_dec(v_majorFVarId_2593_);
lean_dec_ref(v_a_2592_);
v_a_2714_ = lean_ctor_get(v___x_2645_, 0);
v_isSharedCheck_2721_ = !lean_is_exclusive(v___x_2645_);
if (v_isSharedCheck_2721_ == 0)
{
v___x_2716_ = v___x_2645_;
v_isShared_2717_ = v_isSharedCheck_2721_;
goto v_resetjp_2715_;
}
else
{
lean_inc(v_a_2714_);
lean_dec(v___x_2645_);
v___x_2716_ = lean_box(0);
v_isShared_2717_ = v_isSharedCheck_2721_;
goto v_resetjp_2715_;
}
v_resetjp_2715_:
{
lean_object* v___x_2719_; 
if (v_isShared_2717_ == 0)
{
v___x_2719_ = v___x_2716_;
goto v_reusejp_2718_;
}
else
{
lean_object* v_reuseFailAlloc_2720_; 
v_reuseFailAlloc_2720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2720_, 0, v_a_2714_);
v___x_2719_ = v_reuseFailAlloc_2720_;
goto v_reusejp_2718_;
}
v_reusejp_2718_:
{
return v___x_2719_;
}
}
}
}
}
else
{
lean_object* v_a_2756_; lean_object* v___x_2758_; uint8_t v_isShared_2759_; uint8_t v_isSharedCheck_2763_; 
lean_dec(v_recursorName_2595_);
lean_dec_ref(v_givenNames_2594_);
lean_dec(v_majorFVarId_2593_);
lean_dec_ref(v_a_2592_);
lean_dec(v_mvarId_2591_);
v_a_2756_ = lean_ctor_get(v___x_2632_, 0);
v_isSharedCheck_2763_ = !lean_is_exclusive(v___x_2632_);
if (v_isSharedCheck_2763_ == 0)
{
v___x_2758_ = v___x_2632_;
v_isShared_2759_ = v_isSharedCheck_2763_;
goto v_resetjp_2757_;
}
else
{
lean_inc(v_a_2756_);
lean_dec(v___x_2632_);
v___x_2758_ = lean_box(0);
v_isShared_2759_ = v_isSharedCheck_2763_;
goto v_resetjp_2757_;
}
v_resetjp_2757_:
{
lean_object* v___x_2761_; 
if (v_isShared_2759_ == 0)
{
v___x_2761_ = v___x_2758_;
goto v_reusejp_2760_;
}
else
{
lean_object* v_reuseFailAlloc_2762_; 
v_reuseFailAlloc_2762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2762_, 0, v_a_2756_);
v___x_2761_ = v_reuseFailAlloc_2762_;
goto v_reusejp_2760_;
}
v_reusejp_2760_:
{
return v___x_2761_;
}
}
}
}
else
{
lean_object* v_a_2764_; lean_object* v___x_2766_; uint8_t v_isShared_2767_; uint8_t v_isSharedCheck_2771_; 
lean_dec(v_recursorName_2595_);
lean_dec_ref(v_givenNames_2594_);
lean_dec(v_majorFVarId_2593_);
lean_dec_ref(v_a_2592_);
lean_dec(v_mvarId_2591_);
lean_dec_ref(v_val_2590_);
v_a_2764_ = lean_ctor_get(v___x_2631_, 0);
v_isSharedCheck_2771_ = !lean_is_exclusive(v___x_2631_);
if (v_isSharedCheck_2771_ == 0)
{
v___x_2766_ = v___x_2631_;
v_isShared_2767_ = v_isSharedCheck_2771_;
goto v_resetjp_2765_;
}
else
{
lean_inc(v_a_2764_);
lean_dec(v___x_2631_);
v___x_2766_ = lean_box(0);
v_isShared_2767_ = v_isSharedCheck_2771_;
goto v_resetjp_2765_;
}
v_resetjp_2765_:
{
lean_object* v___x_2769_; 
if (v_isShared_2767_ == 0)
{
v___x_2769_ = v___x_2766_;
goto v_reusejp_2768_;
}
else
{
lean_object* v_reuseFailAlloc_2770_; 
v_reuseFailAlloc_2770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2770_, 0, v_a_2764_);
v___x_2769_ = v_reuseFailAlloc_2770_;
goto v_reusejp_2768_;
}
v_reusejp_2768_:
{
return v___x_2769_;
}
}
}
v___jp_2613_:
{
size_t v_sz_2626_; lean_object* v___x_2627_; lean_object* v___f_2628_; lean_object* v___x_2629_; 
v_sz_2626_ = lean_array_size(v___y_2620_);
v___x_2627_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__3(v_sz_2626_, v___y_2621_, v___y_2620_);
v___f_2628_ = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4___lam__0___boxed), 14, 9);
lean_closure_set(v___f_2628_, 0, v___y_2615_);
lean_closure_set(v___f_2628_, 1, v___x_2612_);
lean_closure_set(v___f_2628_, 2, v___y_2614_);
lean_closure_set(v___f_2628_, 3, v_a_2592_);
lean_closure_set(v___f_2628_, 4, v___x_2627_);
lean_closure_set(v___f_2628_, 5, v_givenNames_2594_);
lean_closure_set(v___f_2628_, 6, v___y_2617_);
lean_closure_set(v___f_2628_, 7, v___y_2616_);
lean_closure_set(v___f_2628_, 8, v___y_2618_);
v___x_2629_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___redArg(v___y_2619_, v___f_2628_, v___y_2622_, v___y_2623_, v___y_2624_, v___y_2625_);
return v___x_2629_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4___boxed(lean_object* v_val_2772_, lean_object* v_mvarId_2773_, lean_object* v_a_2774_, lean_object* v_majorFVarId_2775_, lean_object* v_givenNames_2776_, lean_object* v_recursorName_2777_, lean_object* v_x_2778_, lean_object* v_x_2779_, lean_object* v_x_2780_, lean_object* v___y_2781_, lean_object* v___y_2782_, lean_object* v___y_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_){
_start:
{
lean_object* v_res_2786_; 
v_res_2786_ = l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4(v_val_2772_, v_mvarId_2773_, v_a_2774_, v_majorFVarId_2775_, v_givenNames_2776_, v_recursorName_2777_, v_x_2778_, v_x_2779_, v_x_2780_, v___y_2781_, v___y_2782_, v___y_2783_, v___y_2784_);
lean_dec(v___y_2784_);
lean_dec_ref(v___y_2783_);
lean_dec(v___y_2782_);
lean_dec_ref(v___y_2781_);
lean_dec(v_x_2780_);
return v_res_2786_;
}
}
static lean_object* _init_l_Lean_MVarId_induction___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2788_; lean_object* v___x_2789_; 
v___x_2788_ = ((lean_object*)(l_Lean_MVarId_induction___lam__0___closed__0));
v___x_2789_ = l_Lean_stringToMessageData(v___x_2788_);
return v___x_2789_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_induction___lam__0(lean_object* v___x_2790_, lean_object* v_mvarId_2791_, lean_object* v_majorFVarId_2792_, lean_object* v_recursorName_2793_, lean_object* v_givenNames_2794_, lean_object* v_cls_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_){
_start:
{
lean_object* v___y_2802_; lean_object* v___y_2803_; lean_object* v___y_2804_; lean_object* v___y_2805_; lean_object* v_toCold_2857_; lean_object* v_options_2858_; uint8_t v_hasTrace_2859_; 
v_toCold_2857_ = lean_ctor_get(v___y_2798_, 0);
v_options_2858_ = lean_ctor_get(v_toCold_2857_, 2);
v_hasTrace_2859_ = lean_ctor_get_uint8(v_options_2858_, sizeof(void*)*1);
if (v_hasTrace_2859_ == 0)
{
lean_dec(v_cls_2795_);
v___y_2802_ = v___y_2796_;
v___y_2803_ = v___y_2797_;
v___y_2804_ = v___y_2798_;
v___y_2805_ = v___y_2799_;
goto v___jp_2801_;
}
else
{
lean_object* v_inheritedTraceOptions_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; uint8_t v___x_2863_; 
v_inheritedTraceOptions_2860_ = lean_ctor_get(v_toCold_2857_, 11);
v___x_2861_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__4));
lean_inc(v_cls_2795_);
v___x_2862_ = l_Lean_Name_append(v___x_2861_, v_cls_2795_);
v___x_2863_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2860_, v_options_2858_, v___x_2862_);
lean_dec(v___x_2862_);
if (v___x_2863_ == 0)
{
lean_dec(v_cls_2795_);
v___y_2802_ = v___y_2796_;
v___y_2803_ = v___y_2797_;
v___y_2804_ = v___y_2798_;
v___y_2805_ = v___y_2799_;
goto v___jp_2801_;
}
else
{
lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; 
v___x_2864_ = lean_obj_once(&l_Lean_MVarId_induction___lam__0___closed__1, &l_Lean_MVarId_induction___lam__0___closed__1_once, _init_l_Lean_MVarId_induction___lam__0___closed__1);
lean_inc(v_mvarId_2791_);
v___x_2865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2865_, 0, v_mvarId_2791_);
v___x_2866_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2866_, 0, v___x_2864_);
lean_ctor_set(v___x_2866_, 1, v___x_2865_);
v___x_2867_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1(v_cls_2795_, v___x_2866_, v___y_2796_, v___y_2797_, v___y_2798_, v___y_2799_);
if (lean_obj_tag(v___x_2867_) == 0)
{
lean_dec_ref_known(v___x_2867_, 1);
v___y_2802_ = v___y_2796_;
v___y_2803_ = v___y_2797_;
v___y_2804_ = v___y_2798_;
v___y_2805_ = v___y_2799_;
goto v___jp_2801_;
}
else
{
lean_object* v_a_2868_; lean_object* v___x_2870_; uint8_t v_isShared_2871_; uint8_t v_isSharedCheck_2875_; 
lean_dec_ref(v_givenNames_2794_);
lean_dec(v_recursorName_2793_);
lean_dec(v_majorFVarId_2792_);
lean_dec(v_mvarId_2791_);
lean_dec_ref(v___x_2790_);
v_a_2868_ = lean_ctor_get(v___x_2867_, 0);
v_isSharedCheck_2875_ = !lean_is_exclusive(v___x_2867_);
if (v_isSharedCheck_2875_ == 0)
{
v___x_2870_ = v___x_2867_;
v_isShared_2871_ = v_isSharedCheck_2875_;
goto v_resetjp_2869_;
}
else
{
lean_inc(v_a_2868_);
lean_dec(v___x_2867_);
v___x_2870_ = lean_box(0);
v_isShared_2871_ = v_isSharedCheck_2875_;
goto v_resetjp_2869_;
}
v_resetjp_2869_:
{
lean_object* v___x_2873_; 
if (v_isShared_2871_ == 0)
{
v___x_2873_ = v___x_2870_;
goto v_reusejp_2872_;
}
else
{
lean_object* v_reuseFailAlloc_2874_; 
v_reuseFailAlloc_2874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2874_, 0, v_a_2868_);
v___x_2873_ = v_reuseFailAlloc_2874_;
goto v_reusejp_2872_;
}
v_reusejp_2872_:
{
return v___x_2873_;
}
}
}
}
}
v___jp_2801_:
{
lean_object* v___x_2806_; lean_object* v___x_2807_; 
v___x_2806_ = l_Lean_Name_mkStr1(v___x_2790_);
lean_inc(v___x_2806_);
lean_inc(v_mvarId_2791_);
v___x_2807_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_2791_, v___x_2806_, v___y_2802_, v___y_2803_, v___y_2804_, v___y_2805_);
if (lean_obj_tag(v___x_2807_) == 0)
{
lean_object* v___x_2808_; 
lean_dec_ref_known(v___x_2807_, 1);
lean_inc(v_majorFVarId_2792_);
v___x_2808_ = l_Lean_FVarId_getDecl___redArg(v_majorFVarId_2792_, v___y_2802_, v___y_2804_, v___y_2805_);
if (lean_obj_tag(v___x_2808_) == 0)
{
lean_object* v_a_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; 
v_a_2809_ = lean_ctor_get(v___x_2808_, 0);
lean_inc(v_a_2809_);
lean_dec_ref_known(v___x_2808_, 1);
v___x_2810_ = lean_box(0);
lean_inc(v_recursorName_2793_);
v___x_2811_ = l_Lean_Meta_mkRecursorInfo(v_recursorName_2793_, v___x_2810_, v___y_2802_, v___y_2803_, v___y_2804_, v___y_2805_);
if (lean_obj_tag(v___x_2811_) == 0)
{
lean_object* v_a_2812_; lean_object* v_typeName_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; 
v_a_2812_ = lean_ctor_get(v___x_2811_, 0);
lean_inc(v_a_2812_);
lean_dec_ref_known(v___x_2811_, 1);
v_typeName_2813_ = lean_ctor_get(v_a_2812_, 1);
v___x_2814_ = l_Lean_LocalDecl_type(v_a_2809_);
lean_dec(v_a_2809_);
lean_inc_ref(v___x_2814_);
v___x_2815_ = l_Lean_Meta_whnfUntil(v___x_2814_, v_typeName_2813_, v___y_2802_, v___y_2803_, v___y_2804_, v___y_2805_);
if (lean_obj_tag(v___x_2815_) == 0)
{
lean_object* v_a_2816_; 
v_a_2816_ = lean_ctor_get(v___x_2815_, 0);
lean_inc(v_a_2816_);
lean_dec_ref_known(v___x_2815_, 1);
if (lean_obj_tag(v_a_2816_) == 1)
{
lean_object* v_val_2817_; lean_object* v_dummy_2818_; lean_object* v_nargs_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; 
lean_dec_ref(v___x_2814_);
lean_dec(v___x_2806_);
v_val_2817_ = lean_ctor_get(v_a_2816_, 0);
lean_inc_n(v_val_2817_, 2);
lean_dec_ref_known(v_a_2816_, 1);
v_dummy_2818_ = lean_obj_once(&l_Lean_Meta_getMajorTypeIndices___closed__0, &l_Lean_Meta_getMajorTypeIndices___closed__0_once, _init_l_Lean_Meta_getMajorTypeIndices___closed__0);
v_nargs_2819_ = l_Lean_Expr_getAppNumArgs(v_val_2817_);
lean_inc(v_nargs_2819_);
v___x_2820_ = lean_mk_array(v_nargs_2819_, v_dummy_2818_);
v___x_2821_ = lean_unsigned_to_nat(1u);
v___x_2822_ = lean_nat_sub(v_nargs_2819_, v___x_2821_);
lean_dec(v_nargs_2819_);
v___x_2823_ = l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4(v_val_2817_, v_mvarId_2791_, v_a_2812_, v_majorFVarId_2792_, v_givenNames_2794_, v_recursorName_2793_, v_val_2817_, v___x_2820_, v___x_2822_, v___y_2802_, v___y_2803_, v___y_2804_, v___y_2805_);
lean_dec(v___x_2822_);
return v___x_2823_;
}
else
{
lean_object* v___x_2824_; 
lean_dec(v_a_2816_);
lean_dec(v_a_2812_);
lean_dec_ref(v_givenNames_2794_);
lean_dec(v_recursorName_2793_);
lean_dec(v_majorFVarId_2792_);
v___x_2824_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg(v___x_2806_, v_mvarId_2791_, v___x_2814_, v___y_2802_, v___y_2803_, v___y_2804_, v___y_2805_);
return v___x_2824_;
}
}
else
{
lean_object* v_a_2825_; lean_object* v___x_2827_; uint8_t v_isShared_2828_; uint8_t v_isSharedCheck_2832_; 
lean_dec_ref(v___x_2814_);
lean_dec(v_a_2812_);
lean_dec(v___x_2806_);
lean_dec_ref(v_givenNames_2794_);
lean_dec(v_recursorName_2793_);
lean_dec(v_majorFVarId_2792_);
lean_dec(v_mvarId_2791_);
v_a_2825_ = lean_ctor_get(v___x_2815_, 0);
v_isSharedCheck_2832_ = !lean_is_exclusive(v___x_2815_);
if (v_isSharedCheck_2832_ == 0)
{
v___x_2827_ = v___x_2815_;
v_isShared_2828_ = v_isSharedCheck_2832_;
goto v_resetjp_2826_;
}
else
{
lean_inc(v_a_2825_);
lean_dec(v___x_2815_);
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
else
{
lean_object* v_a_2833_; lean_object* v___x_2835_; uint8_t v_isShared_2836_; uint8_t v_isSharedCheck_2840_; 
lean_dec(v_a_2809_);
lean_dec(v___x_2806_);
lean_dec_ref(v_givenNames_2794_);
lean_dec(v_recursorName_2793_);
lean_dec(v_majorFVarId_2792_);
lean_dec(v_mvarId_2791_);
v_a_2833_ = lean_ctor_get(v___x_2811_, 0);
v_isSharedCheck_2840_ = !lean_is_exclusive(v___x_2811_);
if (v_isSharedCheck_2840_ == 0)
{
v___x_2835_ = v___x_2811_;
v_isShared_2836_ = v_isSharedCheck_2840_;
goto v_resetjp_2834_;
}
else
{
lean_inc(v_a_2833_);
lean_dec(v___x_2811_);
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
}
else
{
lean_object* v_a_2841_; lean_object* v___x_2843_; uint8_t v_isShared_2844_; uint8_t v_isSharedCheck_2848_; 
lean_dec(v___x_2806_);
lean_dec_ref(v_givenNames_2794_);
lean_dec(v_recursorName_2793_);
lean_dec(v_majorFVarId_2792_);
lean_dec(v_mvarId_2791_);
v_a_2841_ = lean_ctor_get(v___x_2808_, 0);
v_isSharedCheck_2848_ = !lean_is_exclusive(v___x_2808_);
if (v_isSharedCheck_2848_ == 0)
{
v___x_2843_ = v___x_2808_;
v_isShared_2844_ = v_isSharedCheck_2848_;
goto v_resetjp_2842_;
}
else
{
lean_inc(v_a_2841_);
lean_dec(v___x_2808_);
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
}
else
{
lean_object* v_a_2849_; lean_object* v___x_2851_; uint8_t v_isShared_2852_; uint8_t v_isSharedCheck_2856_; 
lean_dec(v___x_2806_);
lean_dec_ref(v_givenNames_2794_);
lean_dec(v_recursorName_2793_);
lean_dec(v_majorFVarId_2792_);
lean_dec(v_mvarId_2791_);
v_a_2849_ = lean_ctor_get(v___x_2807_, 0);
v_isSharedCheck_2856_ = !lean_is_exclusive(v___x_2807_);
if (v_isSharedCheck_2856_ == 0)
{
v___x_2851_ = v___x_2807_;
v_isShared_2852_ = v_isSharedCheck_2856_;
goto v_resetjp_2850_;
}
else
{
lean_inc(v_a_2849_);
lean_dec(v___x_2807_);
v___x_2851_ = lean_box(0);
v_isShared_2852_ = v_isSharedCheck_2856_;
goto v_resetjp_2850_;
}
v_resetjp_2850_:
{
lean_object* v___x_2854_; 
if (v_isShared_2852_ == 0)
{
v___x_2854_ = v___x_2851_;
goto v_reusejp_2853_;
}
else
{
lean_object* v_reuseFailAlloc_2855_; 
v_reuseFailAlloc_2855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2855_, 0, v_a_2849_);
v___x_2854_ = v_reuseFailAlloc_2855_;
goto v_reusejp_2853_;
}
v_reusejp_2853_:
{
return v___x_2854_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_induction___lam__0___boxed(lean_object* v___x_2876_, lean_object* v_mvarId_2877_, lean_object* v_majorFVarId_2878_, lean_object* v_recursorName_2879_, lean_object* v_givenNames_2880_, lean_object* v_cls_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_, lean_object* v___y_2884_, lean_object* v___y_2885_, lean_object* v___y_2886_){
_start:
{
lean_object* v_res_2887_; 
v_res_2887_ = l_Lean_MVarId_induction___lam__0(v___x_2876_, v_mvarId_2877_, v_majorFVarId_2878_, v_recursorName_2879_, v_givenNames_2880_, v_cls_2881_, v___y_2882_, v___y_2883_, v___y_2884_, v___y_2885_);
lean_dec(v___y_2885_);
lean_dec_ref(v___y_2884_);
lean_dec(v___y_2883_);
lean_dec_ref(v___y_2882_);
return v_res_2887_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_induction(lean_object* v_mvarId_2888_, lean_object* v_majorFVarId_2889_, lean_object* v_recursorName_2890_, lean_object* v_givenNames_2891_, lean_object* v_a_2892_, lean_object* v_a_2893_, lean_object* v_a_2894_, lean_object* v_a_2895_){
_start:
{
lean_object* v___x_2897_; lean_object* v_cls_2898_; lean_object* v___f_2899_; lean_object* v___x_2900_; 
v___x_2897_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__0));
v_cls_2898_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__2));
lean_inc(v_mvarId_2888_);
v___f_2899_ = lean_alloc_closure((void*)(l_Lean_MVarId_induction___lam__0___boxed), 11, 6);
lean_closure_set(v___f_2899_, 0, v___x_2897_);
lean_closure_set(v___f_2899_, 1, v_mvarId_2888_);
lean_closure_set(v___f_2899_, 2, v_majorFVarId_2889_);
lean_closure_set(v___f_2899_, 3, v_recursorName_2890_);
lean_closure_set(v___f_2899_, 4, v_givenNames_2891_);
lean_closure_set(v___f_2899_, 5, v_cls_2898_);
v___x_2900_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___redArg(v_mvarId_2888_, v___f_2899_, v_a_2892_, v_a_2893_, v_a_2894_, v_a_2895_);
return v___x_2900_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_induction___boxed(lean_object* v_mvarId_2901_, lean_object* v_majorFVarId_2902_, lean_object* v_recursorName_2903_, lean_object* v_givenNames_2904_, lean_object* v_a_2905_, lean_object* v_a_2906_, lean_object* v_a_2907_, lean_object* v_a_2908_, lean_object* v_a_2909_){
_start:
{
lean_object* v_res_2910_; 
v_res_2910_ = l_Lean_MVarId_induction(v_mvarId_2901_, v_majorFVarId_2902_, v_recursorName_2903_, v_givenNames_2904_, v_a_2905_, v_a_2906_, v_a_2907_, v_a_2908_);
lean_dec(v_a_2908_);
lean_dec_ref(v_a_2907_);
lean_dec(v_a_2906_);
lean_dec_ref(v_a_2905_);
return v_res_2910_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; 
v___x_2958_ = lean_unsigned_to_nat(2221195325u);
v___x_2959_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_));
v___x_2960_ = l_Lean_Name_num___override(v___x_2959_, v___x_2958_);
return v___x_2960_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; 
v___x_2962_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_));
v___x_2963_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_);
v___x_2964_ = l_Lean_Name_str___override(v___x_2963_, v___x_2962_);
return v___x_2964_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; 
v___x_2966_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_));
v___x_2967_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_);
v___x_2968_ = l_Lean_Name_str___override(v___x_2967_, v___x_2966_);
return v___x_2968_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; 
v___x_2969_ = lean_unsigned_to_nat(2u);
v___x_2970_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_);
v___x_2971_ = l_Lean_Name_num___override(v___x_2970_, v___x_2969_);
return v___x_2971_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2973_; uint8_t v___x_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; 
v___x_2973_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__2));
v___x_2974_ = 0;
v___x_2975_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_);
v___x_2976_ = l_Lean_registerTraceClass(v___x_2973_, v___x_2974_, v___x_2975_);
return v___x_2976_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2____boxed(lean_object* v_a_2977_){
_start:
{
lean_object* v_res_2978_; 
v_res_2978_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_();
return v_res_2978_;
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
