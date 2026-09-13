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
lean_object* v___f_134_; lean_object* v___x_6323__overap_135_; lean_object* v___x_136_; 
v___f_134_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__4___closed__0));
v___x_6323__overap_135_ = lean_panic_fn_borrowed(v___f_134_, v_msg_128_);
lean_inc(v___y_132_);
lean_inc_ref(v___y_131_);
lean_inc(v___y_130_);
lean_inc_ref(v___y_129_);
v___x_136_ = lean_apply_5(v___x_6323__overap_135_, v___y_129_, v___y_130_, v___y_131_, v___y_132_, lean_box(0));
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
size_t v_x_7617__boxed_361_; size_t v_x_7618__boxed_362_; lean_object* v_res_363_; 
v_x_7617__boxed_361_ = lean_unbox_usize(v_x_357_);
lean_dec(v_x_357_);
v_x_7618__boxed_362_ = lean_unbox_usize(v_x_358_);
lean_dec(v_x_358_);
v_res_363_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2___redArg(v_x_356_, v_x_7617__boxed_361_, v_x_7618__boxed_362_, v_x_359_, v_x_360_);
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
lean_object* v___x_375_; lean_object* v_mctx_376_; lean_object* v_cache_377_; lean_object* v_zetaDeltaFVarIds_378_; lean_object* v_postponed_379_; lean_object* v_diag_380_; lean_object* v___x_382_; uint8_t v_isShared_383_; uint8_t v_isSharedCheck_409_; 
v___x_375_ = lean_st_ref_take(v___y_373_);
v_mctx_376_ = lean_ctor_get(v___x_375_, 0);
v_cache_377_ = lean_ctor_get(v___x_375_, 1);
v_zetaDeltaFVarIds_378_ = lean_ctor_get(v___x_375_, 2);
v_postponed_379_ = lean_ctor_get(v___x_375_, 3);
v_diag_380_ = lean_ctor_get(v___x_375_, 4);
v_isSharedCheck_409_ = !lean_is_exclusive(v___x_375_);
if (v_isSharedCheck_409_ == 0)
{
v___x_382_ = v___x_375_;
v_isShared_383_ = v_isSharedCheck_409_;
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
v_isShared_383_ = v_isSharedCheck_409_;
goto v_resetjp_381_;
}
v_resetjp_381_:
{
lean_object* v_depth_384_; lean_object* v_levelAssignDepth_385_; lean_object* v_lmvarCounter_386_; lean_object* v_mvarCounter_387_; lean_object* v_lDecls_388_; lean_object* v_decls_389_; lean_object* v_userNames_390_; lean_object* v_lAssignment_391_; lean_object* v_eAssignment_392_; lean_object* v_dAssignment_393_; lean_object* v_instanceTypedMVars_394_; lean_object* v___x_396_; uint8_t v_isShared_397_; uint8_t v_isSharedCheck_408_; 
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
v_isSharedCheck_408_ = !lean_is_exclusive(v_mctx_376_);
if (v_isSharedCheck_408_ == 0)
{
v___x_396_ = v_mctx_376_;
v_isShared_397_ = v_isSharedCheck_408_;
goto v_resetjp_395_;
}
else
{
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
v___x_396_ = lean_box(0);
v_isShared_397_ = v_isSharedCheck_408_;
goto v_resetjp_395_;
}
v_resetjp_395_:
{
lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_401_; 
v___x_398_ = lean_box(0);
v___x_399_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0___redArg(v_eAssignment_392_, v_mvarId_371_, v_val_372_);
if (v_isShared_397_ == 0)
{
lean_ctor_set(v___x_396_, 8, v___x_399_);
v___x_401_ = v___x_396_;
goto v_reusejp_400_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_407_, 0, v_depth_384_);
lean_ctor_set(v_reuseFailAlloc_407_, 1, v_levelAssignDepth_385_);
lean_ctor_set(v_reuseFailAlloc_407_, 2, v_lmvarCounter_386_);
lean_ctor_set(v_reuseFailAlloc_407_, 3, v_mvarCounter_387_);
lean_ctor_set(v_reuseFailAlloc_407_, 4, v_lDecls_388_);
lean_ctor_set(v_reuseFailAlloc_407_, 5, v_decls_389_);
lean_ctor_set(v_reuseFailAlloc_407_, 6, v_userNames_390_);
lean_ctor_set(v_reuseFailAlloc_407_, 7, v_lAssignment_391_);
lean_ctor_set(v_reuseFailAlloc_407_, 8, v___x_399_);
lean_ctor_set(v_reuseFailAlloc_407_, 9, v_dAssignment_393_);
lean_ctor_set(v_reuseFailAlloc_407_, 10, v_instanceTypedMVars_394_);
v___x_401_ = v_reuseFailAlloc_407_;
goto v_reusejp_400_;
}
v_reusejp_400_:
{
lean_object* v___x_403_; 
if (v_isShared_383_ == 0)
{
lean_ctor_set(v___x_382_, 0, v___x_401_);
v___x_403_ = v___x_382_;
goto v_reusejp_402_;
}
else
{
lean_object* v_reuseFailAlloc_406_; 
v_reuseFailAlloc_406_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_406_, 0, v___x_401_);
lean_ctor_set(v_reuseFailAlloc_406_, 1, v_cache_377_);
lean_ctor_set(v_reuseFailAlloc_406_, 2, v_zetaDeltaFVarIds_378_);
lean_ctor_set(v_reuseFailAlloc_406_, 3, v_postponed_379_);
lean_ctor_set(v_reuseFailAlloc_406_, 4, v_diag_380_);
v___x_403_ = v_reuseFailAlloc_406_;
goto v_reusejp_402_;
}
v_reusejp_402_:
{
lean_object* v___x_404_; lean_object* v___x_405_; 
v___x_404_ = lean_st_ref_put(v___y_373_, v___x_403_);
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
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1_spec__2(lean_object* v_msgData_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_){
_start:
{
lean_object* v___x_421_; lean_object* v_env_422_; lean_object* v___x_423_; lean_object* v_toCold_424_; lean_object* v_mctx_425_; lean_object* v_lctx_426_; lean_object* v_options_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; 
v___x_421_ = lean_st_ref_get(v___y_419_);
v_env_422_ = lean_ctor_get(v___x_421_, 0);
lean_inc_ref(v_env_422_);
lean_dec(v___x_421_);
v___x_423_ = lean_st_ref_get(v___y_417_);
v_toCold_424_ = lean_ctor_get(v___y_418_, 0);
v_mctx_425_ = lean_ctor_get(v___x_423_, 0);
lean_inc_ref(v_mctx_425_);
lean_dec(v___x_423_);
v_lctx_426_ = lean_ctor_get(v___y_416_, 2);
v_options_427_ = lean_ctor_get(v_toCold_424_, 2);
lean_inc_ref(v_options_427_);
lean_inc_ref(v_lctx_426_);
v___x_428_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_428_, 0, v_env_422_);
lean_ctor_set(v___x_428_, 1, v_mctx_425_);
lean_ctor_set(v___x_428_, 2, v_lctx_426_);
lean_ctor_set(v___x_428_, 3, v_options_427_);
v___x_429_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_429_, 0, v___x_428_);
lean_ctor_set(v___x_429_, 1, v_msgData_415_);
v___x_430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_430_, 0, v___x_429_);
return v___x_430_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1_spec__2___boxed(lean_object* v_msgData_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_){
_start:
{
lean_object* v_res_437_; 
v_res_437_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1_spec__2(v_msgData_431_, v___y_432_, v___y_433_, v___y_434_, v___y_435_);
lean_dec(v___y_435_);
lean_dec_ref(v___y_434_);
lean_dec(v___y_433_);
lean_dec_ref(v___y_432_);
return v_res_437_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1___closed__0(void){
_start:
{
lean_object* v___x_438_; double v___x_439_; 
v___x_438_ = lean_unsigned_to_nat(0u);
v___x_439_ = lean_float_of_nat(v___x_438_);
return v___x_439_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1(lean_object* v_cls_443_, lean_object* v_msg_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_){
_start:
{
lean_object* v_ref_450_; lean_object* v___x_451_; lean_object* v_a_452_; lean_object* v___x_454_; uint8_t v_isShared_455_; uint8_t v_isSharedCheck_496_; 
v_ref_450_ = lean_ctor_get(v___y_447_, 2);
v___x_451_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1_spec__2(v_msg_444_, v___y_445_, v___y_446_, v___y_447_, v___y_448_);
v_a_452_ = lean_ctor_get(v___x_451_, 0);
v_isSharedCheck_496_ = !lean_is_exclusive(v___x_451_);
if (v_isSharedCheck_496_ == 0)
{
v___x_454_ = v___x_451_;
v_isShared_455_ = v_isSharedCheck_496_;
goto v_resetjp_453_;
}
else
{
lean_inc(v_a_452_);
lean_dec(v___x_451_);
v___x_454_ = lean_box(0);
v_isShared_455_ = v_isSharedCheck_496_;
goto v_resetjp_453_;
}
v_resetjp_453_:
{
lean_object* v___x_456_; lean_object* v_traceState_457_; lean_object* v_env_458_; lean_object* v_nextMacroScope_459_; lean_object* v_ngen_460_; lean_object* v_auxDeclNGen_461_; lean_object* v_cache_462_; lean_object* v_messages_463_; lean_object* v_infoState_464_; lean_object* v_snapshotTasks_465_; lean_object* v___x_467_; uint8_t v_isShared_468_; uint8_t v_isSharedCheck_495_; 
v___x_456_ = lean_st_ref_take(v___y_448_);
v_traceState_457_ = lean_ctor_get(v___x_456_, 4);
v_env_458_ = lean_ctor_get(v___x_456_, 0);
v_nextMacroScope_459_ = lean_ctor_get(v___x_456_, 1);
v_ngen_460_ = lean_ctor_get(v___x_456_, 2);
v_auxDeclNGen_461_ = lean_ctor_get(v___x_456_, 3);
v_cache_462_ = lean_ctor_get(v___x_456_, 5);
v_messages_463_ = lean_ctor_get(v___x_456_, 6);
v_infoState_464_ = lean_ctor_get(v___x_456_, 7);
v_snapshotTasks_465_ = lean_ctor_get(v___x_456_, 8);
v_isSharedCheck_495_ = !lean_is_exclusive(v___x_456_);
if (v_isSharedCheck_495_ == 0)
{
v___x_467_ = v___x_456_;
v_isShared_468_ = v_isSharedCheck_495_;
goto v_resetjp_466_;
}
else
{
lean_inc(v_snapshotTasks_465_);
lean_inc(v_infoState_464_);
lean_inc(v_messages_463_);
lean_inc(v_cache_462_);
lean_inc(v_traceState_457_);
lean_inc(v_auxDeclNGen_461_);
lean_inc(v_ngen_460_);
lean_inc(v_nextMacroScope_459_);
lean_inc(v_env_458_);
lean_dec(v___x_456_);
v___x_467_ = lean_box(0);
v_isShared_468_ = v_isSharedCheck_495_;
goto v_resetjp_466_;
}
v_resetjp_466_:
{
uint64_t v_tid_469_; lean_object* v_traces_470_; lean_object* v___x_472_; uint8_t v_isShared_473_; uint8_t v_isSharedCheck_494_; 
v_tid_469_ = lean_ctor_get_uint64(v_traceState_457_, sizeof(void*)*1);
v_traces_470_ = lean_ctor_get(v_traceState_457_, 0);
v_isSharedCheck_494_ = !lean_is_exclusive(v_traceState_457_);
if (v_isSharedCheck_494_ == 0)
{
v___x_472_ = v_traceState_457_;
v_isShared_473_ = v_isSharedCheck_494_;
goto v_resetjp_471_;
}
else
{
lean_inc(v_traces_470_);
lean_dec(v_traceState_457_);
v___x_472_ = lean_box(0);
v_isShared_473_ = v_isSharedCheck_494_;
goto v_resetjp_471_;
}
v_resetjp_471_:
{
lean_object* v___x_474_; lean_object* v___x_475_; double v___x_476_; uint8_t v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_485_; 
v___x_474_ = lean_box(0);
v___x_475_ = lean_box(0);
v___x_476_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1___closed__0);
v___x_477_ = 0;
v___x_478_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1___closed__1));
v___x_479_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_479_, 0, v_cls_443_);
lean_ctor_set(v___x_479_, 1, v___x_475_);
lean_ctor_set(v___x_479_, 2, v___x_478_);
lean_ctor_set_float(v___x_479_, sizeof(void*)*3, v___x_476_);
lean_ctor_set_float(v___x_479_, sizeof(void*)*3 + 8, v___x_476_);
lean_ctor_set_uint8(v___x_479_, sizeof(void*)*3 + 16, v___x_477_);
v___x_480_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1___closed__2));
v___x_481_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_481_, 0, v___x_479_);
lean_ctor_set(v___x_481_, 1, v_a_452_);
lean_ctor_set(v___x_481_, 2, v___x_480_);
lean_inc(v_ref_450_);
v___x_482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_482_, 0, v_ref_450_);
lean_ctor_set(v___x_482_, 1, v___x_481_);
v___x_483_ = l_Lean_PersistentArray_push___redArg(v_traces_470_, v___x_482_);
if (v_isShared_473_ == 0)
{
lean_ctor_set(v___x_472_, 0, v___x_483_);
v___x_485_ = v___x_472_;
goto v_reusejp_484_;
}
else
{
lean_object* v_reuseFailAlloc_493_; 
v_reuseFailAlloc_493_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_493_, 0, v___x_483_);
lean_ctor_set_uint64(v_reuseFailAlloc_493_, sizeof(void*)*1, v_tid_469_);
v___x_485_ = v_reuseFailAlloc_493_;
goto v_reusejp_484_;
}
v_reusejp_484_:
{
lean_object* v___x_487_; 
if (v_isShared_468_ == 0)
{
lean_ctor_set(v___x_467_, 4, v___x_485_);
v___x_487_ = v___x_467_;
goto v_reusejp_486_;
}
else
{
lean_object* v_reuseFailAlloc_492_; 
v_reuseFailAlloc_492_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_492_, 0, v_env_458_);
lean_ctor_set(v_reuseFailAlloc_492_, 1, v_nextMacroScope_459_);
lean_ctor_set(v_reuseFailAlloc_492_, 2, v_ngen_460_);
lean_ctor_set(v_reuseFailAlloc_492_, 3, v_auxDeclNGen_461_);
lean_ctor_set(v_reuseFailAlloc_492_, 4, v___x_485_);
lean_ctor_set(v_reuseFailAlloc_492_, 5, v_cache_462_);
lean_ctor_set(v_reuseFailAlloc_492_, 6, v_messages_463_);
lean_ctor_set(v_reuseFailAlloc_492_, 7, v_infoState_464_);
lean_ctor_set(v_reuseFailAlloc_492_, 8, v_snapshotTasks_465_);
v___x_487_ = v_reuseFailAlloc_492_;
goto v_reusejp_486_;
}
v_reusejp_486_:
{
lean_object* v___x_488_; lean_object* v___x_490_; 
v___x_488_ = lean_st_ref_put(v___y_448_, v___x_487_);
if (v_isShared_455_ == 0)
{
lean_ctor_set(v___x_454_, 0, v___x_474_);
v___x_490_ = v___x_454_;
goto v_reusejp_489_;
}
else
{
lean_object* v_reuseFailAlloc_491_; 
v_reuseFailAlloc_491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_491_, 0, v___x_474_);
v___x_490_ = v_reuseFailAlloc_491_;
goto v_reusejp_489_;
}
v_reusejp_489_:
{
return v___x_490_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1___boxed(lean_object* v_cls_497_, lean_object* v_msg_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_){
_start:
{
lean_object* v_res_504_; 
v_res_504_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1(v_cls_497_, v_msg_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_);
lean_dec(v___y_502_);
lean_dec_ref(v___y_501_);
lean_dec(v___y_500_);
lean_dec_ref(v___y_499_);
return v_res_504_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__3(size_t v_sz_505_, size_t v_i_506_, lean_object* v_bs_507_){
_start:
{
uint8_t v___x_508_; 
v___x_508_ = lean_usize_dec_lt(v_i_506_, v_sz_505_);
if (v___x_508_ == 0)
{
return v_bs_507_;
}
else
{
lean_object* v_v_509_; lean_object* v___x_510_; lean_object* v_bs_x27_511_; lean_object* v___x_512_; size_t v___x_513_; size_t v___x_514_; lean_object* v___x_515_; 
v_v_509_ = lean_array_uget(v_bs_507_, v_i_506_);
v___x_510_ = lean_unsigned_to_nat(0u);
v_bs_x27_511_ = lean_array_uset(v_bs_507_, v_i_506_, v___x_510_);
v___x_512_ = l_Lean_mkFVar(v_v_509_);
v___x_513_ = ((size_t)1ULL);
v___x_514_ = lean_usize_add(v_i_506_, v___x_513_);
v___x_515_ = lean_array_uset(v_bs_x27_511_, v_i_506_, v___x_512_);
v_i_506_ = v___x_514_;
v_bs_507_ = v___x_515_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__3___boxed(lean_object* v_sz_517_, lean_object* v_i_518_, lean_object* v_bs_519_){
_start:
{
size_t v_sz_boxed_520_; size_t v_i_boxed_521_; lean_object* v_res_522_; 
v_sz_boxed_520_ = lean_unbox_usize(v_sz_517_);
lean_dec(v_sz_517_);
v_i_boxed_521_ = lean_unbox_usize(v_i_518_);
lean_dec(v_i_518_);
v_res_522_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__3(v_sz_boxed_520_, v_i_boxed_521_, v_bs_519_);
return v_res_522_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5(void){
_start:
{
lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; 
v___x_532_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__2));
v___x_533_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__4));
v___x_534_ = l_Lean_Name_append(v___x_533_, v___x_532_);
return v___x_534_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__7(void){
_start:
{
lean_object* v___x_536_; lean_object* v___x_537_; 
v___x_536_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__6));
v___x_537_ = l_Lean_stringToMessageData(v___x_536_);
return v___x_537_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__9(void){
_start:
{
lean_object* v___x_539_; lean_object* v___x_540_; 
v___x_539_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__8));
v___x_540_ = l_Lean_stringToMessageData(v___x_539_);
return v___x_540_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__11(void){
_start:
{
lean_object* v___x_542_; lean_object* v___x_543_; 
v___x_542_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__10));
v___x_543_ = l_Lean_stringToMessageData(v___x_542_);
return v___x_543_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__15(void){
_start:
{
lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; 
v___x_547_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__14));
v___x_548_ = lean_unsigned_to_nat(15u);
v___x_549_ = lean_unsigned_to_nat(120u);
v___x_550_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__13));
v___x_551_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__12));
v___x_552_ = l_mkPanicMessageWithDecl(v___x_551_, v___x_550_, v___x_549_, v___x_548_, v___x_547_);
return v___x_552_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop(lean_object* v_mvarId_553_, lean_object* v_givenNames_554_, lean_object* v_recursorInfo_555_, lean_object* v_reverted_556_, lean_object* v_major_557_, lean_object* v_indices_558_, lean_object* v_baseSubst_559_, lean_object* v_initialArity_560_, lean_object* v_numMinors_561_, lean_object* v_pos_562_, lean_object* v_minorIdx_563_, lean_object* v_recursor_564_, lean_object* v_recursorType_565_, uint8_t v_consumedMajor_566_, lean_object* v_subgoals_567_, lean_object* v_a_568_, lean_object* v_a_569_, lean_object* v_a_570_, lean_object* v_a_571_){
_start:
{
lean_object* v___y_574_; lean_object* v___y_575_; lean_object* v___y_576_; lean_object* v___y_577_; lean_object* v___y_631_; lean_object* v___y_632_; lean_object* v___y_633_; lean_object* v___y_634_; lean_object* v___y_635_; lean_object* v___y_636_; lean_object* v___y_637_; lean_object* v___y_638_; lean_object* v___y_639_; uint8_t v___y_640_; lean_object* v___y_641_; uint8_t v___y_642_; lean_object* v___y_643_; lean_object* v___y_644_; lean_object* v___y_645_; uint8_t v___y_646_; lean_object* v___y_682_; uint8_t v___y_683_; uint8_t v___y_684_; lean_object* v___y_685_; lean_object* v___y_686_; lean_object* v___y_687_; lean_object* v___y_688_; lean_object* v___y_689_; lean_object* v___y_690_; lean_object* v___y_691_; lean_object* v___y_692_; lean_object* v___y_693_; lean_object* v___y_694_; lean_object* v___y_695_; lean_object* v___y_696_; uint8_t v___y_714_; lean_object* v___y_715_; lean_object* v_fst_716_; lean_object* v_snd_717_; lean_object* v___y_734_; uint8_t v___y_735_; lean_object* v___y_736_; uint8_t v___x_748_; lean_object* v___x_749_; 
v___x_748_ = lean_nat_dec_le(v_numMinors_561_, v_minorIdx_563_);
v___x_749_ = l_Lean_Meta_whnfForall(v_recursorType_565_, v_a_568_, v_a_569_, v_a_570_, v_a_571_);
if (lean_obj_tag(v___x_749_) == 0)
{
lean_object* v_a_750_; lean_object* v___y_752_; lean_object* v___y_753_; lean_object* v___y_754_; lean_object* v___y_755_; lean_object* v___y_756_; lean_object* v___y_757_; uint8_t v___y_758_; lean_object* v___y_759_; lean_object* v___y_760_; uint8_t v___y_761_; lean_object* v___y_762_; lean_object* v___y_763_; lean_object* v___y_764_; lean_object* v___y_765_; uint8_t v___y_809_; lean_object* v___y_810_; uint8_t v___y_811_; lean_object* v___y_812_; lean_object* v___y_813_; lean_object* v___y_814_; lean_object* v___y_815_; lean_object* v___y_816_; lean_object* v___y_817_; lean_object* v___y_818_; uint8_t v___y_830_; lean_object* v___y_831_; lean_object* v___y_832_; lean_object* v___y_833_; lean_object* v___y_834_; lean_object* v___y_835_; lean_object* v___y_836_; lean_object* v___y_837_; uint8_t v___y_838_; uint8_t v___y_908_; lean_object* v___y_909_; lean_object* v___y_910_; uint8_t v___y_911_; lean_object* v___y_912_; lean_object* v___y_913_; lean_object* v___y_914_; lean_object* v___y_915_; lean_object* v___y_916_; uint8_t v___y_922_; lean_object* v___y_923_; lean_object* v___y_924_; lean_object* v___y_925_; lean_object* v___y_926_; lean_object* v___y_927_; uint8_t v___y_939_; uint8_t v___x_986_; 
v_a_750_ = lean_ctor_get(v___x_749_, 0);
lean_inc(v_a_750_);
lean_dec_ref_known(v___x_749_, 1);
v___x_986_ = l_Lean_Expr_isForall(v_a_750_);
if (v___x_986_ == 0)
{
v___y_939_ = v___x_986_;
goto v___jp_938_;
}
else
{
lean_object* v_numArgs_987_; uint8_t v___x_988_; 
v_numArgs_987_ = lean_ctor_get(v_recursorInfo_555_, 3);
v___x_988_ = lean_nat_dec_lt(v_pos_562_, v_numArgs_987_);
v___y_939_ = v___x_988_;
goto v___jp_938_;
}
v___jp_751_:
{
lean_object* v___x_766_; 
v___x_766_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___y_755_, v___y_759_, v___y_760_, v___y_753_, v___y_764_, v___y_763_);
if (lean_obj_tag(v___x_766_) == 0)
{
lean_object* v_a_767_; lean_object* v___x_768_; lean_object* v___x_769_; 
v_a_767_ = lean_ctor_get(v___x_766_, 0);
lean_inc_n(v_a_767_, 2);
lean_dec_ref_known(v___x_766_, 1);
v___x_768_ = l_Lean_Expr_app___override(v_recursor_564_, v_a_767_);
lean_inc(v_mvarId_553_);
v___x_769_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTypeBody(v_mvarId_553_, v_a_750_, v_a_767_, v___y_760_, v___y_753_, v___y_764_, v___y_763_);
if (lean_obj_tag(v___x_769_) == 0)
{
lean_object* v_toCold_770_; lean_object* v_options_771_; uint8_t v_hasTrace_772_; 
v_toCold_770_ = lean_ctor_get(v___y_764_, 0);
v_options_771_ = lean_ctor_get(v_toCold_770_, 2);
v_hasTrace_772_ = lean_ctor_get_uint8(v_options_771_, sizeof(void*)*1);
if (v_hasTrace_772_ == 0)
{
lean_object* v_a_773_; 
v_a_773_ = lean_ctor_get(v___x_769_, 0);
lean_inc(v_a_773_);
lean_dec_ref_known(v___x_769_, 1);
v___y_682_ = v___y_757_;
v___y_683_ = v___y_758_;
v___y_684_ = v___y_761_;
v___y_685_ = v___y_762_;
v___y_686_ = v___y_752_;
v___y_687_ = v_a_767_;
v___y_688_ = v_a_773_;
v___y_689_ = v___y_765_;
v___y_690_ = v___y_756_;
v___y_691_ = v___y_754_;
v___y_692_ = v___x_768_;
v___y_693_ = v___y_760_;
v___y_694_ = v___y_753_;
v___y_695_ = v___y_764_;
v___y_696_ = v___y_763_;
goto v___jp_681_;
}
else
{
lean_object* v_a_774_; lean_object* v_inheritedTraceOptions_775_; lean_object* v___x_776_; lean_object* v___x_777_; uint8_t v___x_778_; 
v_a_774_ = lean_ctor_get(v___x_769_, 0);
lean_inc(v_a_774_);
lean_dec_ref_known(v___x_769_, 1);
v_inheritedTraceOptions_775_ = lean_ctor_get(v_toCold_770_, 11);
v___x_776_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__2));
v___x_777_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5);
v___x_778_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_775_, v_options_771_, v___x_777_);
if (v___x_778_ == 0)
{
v___y_682_ = v___y_757_;
v___y_683_ = v___y_758_;
v___y_684_ = v___y_761_;
v___y_685_ = v___y_762_;
v___y_686_ = v___y_752_;
v___y_687_ = v_a_767_;
v___y_688_ = v_a_774_;
v___y_689_ = v___y_765_;
v___y_690_ = v___y_756_;
v___y_691_ = v___y_754_;
v___y_692_ = v___x_768_;
v___y_693_ = v___y_760_;
v___y_694_ = v___y_753_;
v___y_695_ = v___y_764_;
v___y_696_ = v___y_763_;
goto v___jp_681_;
}
else
{
lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; 
v___x_779_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__11, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__11_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__11);
v___x_780_ = l_Lean_Expr_fvarId_x21(v_major_557_);
v___x_781_ = l_Lean_MessageData_ofName(v___x_780_);
v___x_782_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_782_, 0, v___x_779_);
lean_ctor_set(v___x_782_, 1, v___x_781_);
v___x_783_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1(v___x_776_, v___x_782_, v___y_760_, v___y_753_, v___y_764_, v___y_763_);
if (lean_obj_tag(v___x_783_) == 0)
{
lean_dec_ref_known(v___x_783_, 1);
v___y_682_ = v___y_757_;
v___y_683_ = v___y_758_;
v___y_684_ = v___y_761_;
v___y_685_ = v___y_762_;
v___y_686_ = v___y_752_;
v___y_687_ = v_a_767_;
v___y_688_ = v_a_774_;
v___y_689_ = v___y_765_;
v___y_690_ = v___y_756_;
v___y_691_ = v___y_754_;
v___y_692_ = v___x_768_;
v___y_693_ = v___y_760_;
v___y_694_ = v___y_753_;
v___y_695_ = v___y_764_;
v___y_696_ = v___y_763_;
goto v___jp_681_;
}
else
{
lean_object* v_a_784_; lean_object* v___x_786_; uint8_t v_isShared_787_; uint8_t v_isSharedCheck_791_; 
lean_dec(v_a_774_);
lean_dec_ref(v___x_768_);
lean_dec(v_a_767_);
lean_dec_ref(v___y_765_);
lean_dec(v___y_762_);
lean_dec(v___y_757_);
lean_dec(v___y_756_);
lean_dec(v___y_752_);
lean_dec_ref(v_subgoals_567_);
lean_dec(v_minorIdx_563_);
lean_dec(v_pos_562_);
lean_dec(v_baseSubst_559_);
lean_dec_ref(v_major_557_);
lean_dec(v_mvarId_553_);
v_a_784_ = lean_ctor_get(v___x_783_, 0);
v_isSharedCheck_791_ = !lean_is_exclusive(v___x_783_);
if (v_isSharedCheck_791_ == 0)
{
v___x_786_ = v___x_783_;
v_isShared_787_ = v_isSharedCheck_791_;
goto v_resetjp_785_;
}
else
{
lean_inc(v_a_784_);
lean_dec(v___x_783_);
v___x_786_ = lean_box(0);
v_isShared_787_ = v_isSharedCheck_791_;
goto v_resetjp_785_;
}
v_resetjp_785_:
{
lean_object* v___x_789_; 
if (v_isShared_787_ == 0)
{
v___x_789_ = v___x_786_;
goto v_reusejp_788_;
}
else
{
lean_object* v_reuseFailAlloc_790_; 
v_reuseFailAlloc_790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_790_, 0, v_a_784_);
v___x_789_ = v_reuseFailAlloc_790_;
goto v_reusejp_788_;
}
v_reusejp_788_:
{
return v___x_789_;
}
}
}
}
}
}
else
{
lean_object* v_a_792_; lean_object* v___x_794_; uint8_t v_isShared_795_; uint8_t v_isSharedCheck_799_; 
lean_dec_ref(v___x_768_);
lean_dec(v_a_767_);
lean_dec_ref(v___y_765_);
lean_dec(v___y_762_);
lean_dec(v___y_757_);
lean_dec(v___y_756_);
lean_dec(v___y_752_);
lean_dec_ref(v_subgoals_567_);
lean_dec(v_minorIdx_563_);
lean_dec(v_pos_562_);
lean_dec(v_baseSubst_559_);
lean_dec_ref(v_major_557_);
lean_dec(v_mvarId_553_);
v_a_792_ = lean_ctor_get(v___x_769_, 0);
v_isSharedCheck_799_ = !lean_is_exclusive(v___x_769_);
if (v_isSharedCheck_799_ == 0)
{
v___x_794_ = v___x_769_;
v_isShared_795_ = v_isSharedCheck_799_;
goto v_resetjp_793_;
}
else
{
lean_inc(v_a_792_);
lean_dec(v___x_769_);
v___x_794_ = lean_box(0);
v_isShared_795_ = v_isSharedCheck_799_;
goto v_resetjp_793_;
}
v_resetjp_793_:
{
lean_object* v___x_797_; 
if (v_isShared_795_ == 0)
{
v___x_797_ = v___x_794_;
goto v_reusejp_796_;
}
else
{
lean_object* v_reuseFailAlloc_798_; 
v_reuseFailAlloc_798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_798_, 0, v_a_792_);
v___x_797_ = v_reuseFailAlloc_798_;
goto v_reusejp_796_;
}
v_reusejp_796_:
{
return v___x_797_;
}
}
}
}
else
{
lean_object* v_a_800_; lean_object* v___x_802_; uint8_t v_isShared_803_; uint8_t v_isSharedCheck_807_; 
lean_dec_ref(v___y_765_);
lean_dec(v___y_762_);
lean_dec(v___y_757_);
lean_dec(v___y_756_);
lean_dec(v___y_752_);
lean_dec(v_a_750_);
lean_dec_ref(v_subgoals_567_);
lean_dec_ref(v_recursor_564_);
lean_dec(v_minorIdx_563_);
lean_dec(v_pos_562_);
lean_dec(v_baseSubst_559_);
lean_dec_ref(v_major_557_);
lean_dec(v_mvarId_553_);
v_a_800_ = lean_ctor_get(v___x_766_, 0);
v_isSharedCheck_807_ = !lean_is_exclusive(v___x_766_);
if (v_isSharedCheck_807_ == 0)
{
v___x_802_ = v___x_766_;
v_isShared_803_ = v_isSharedCheck_807_;
goto v_resetjp_801_;
}
else
{
lean_inc(v_a_800_);
lean_dec(v___x_766_);
v___x_802_ = lean_box(0);
v_isShared_803_ = v_isSharedCheck_807_;
goto v_resetjp_801_;
}
v_resetjp_801_:
{
lean_object* v___x_805_; 
if (v_isShared_803_ == 0)
{
v___x_805_ = v___x_802_;
goto v_reusejp_804_;
}
else
{
lean_object* v_reuseFailAlloc_806_; 
v_reuseFailAlloc_806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_806_, 0, v_a_800_);
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
v___jp_808_:
{
lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; uint8_t v___x_825_; 
v___x_819_ = lean_nat_sub(v___y_810_, v_initialArity_560_);
lean_dec(v___y_810_);
v___x_820_ = lean_array_get_size(v_reverted_556_);
v___x_821_ = lean_array_get_size(v_indices_558_);
v___x_822_ = lean_nat_sub(v___x_820_, v___x_821_);
v___x_823_ = lean_nat_sub(v___x_822_, v___y_814_);
lean_dec(v___x_822_);
v___x_824_ = lean_array_get_size(v_givenNames_554_);
v___x_825_ = lean_nat_dec_lt(v_minorIdx_563_, v___x_824_);
if (v___x_825_ == 0)
{
lean_object* v___x_826_; lean_object* v___x_827_; 
v___x_826_ = lean_box(0);
v___x_827_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_827_, 0, v___x_826_);
lean_ctor_set_uint8(v___x_827_, sizeof(void*)*1, v___x_825_);
v___y_752_ = v___x_823_;
v___y_753_ = v___y_816_;
v___y_754_ = v___y_814_;
v___y_755_ = v___y_813_;
v___y_756_ = v___x_819_;
v___y_757_ = v___x_820_;
v___y_758_ = v___y_809_;
v___y_759_ = v___y_812_;
v___y_760_ = v___y_815_;
v___y_761_ = v___y_811_;
v___y_762_ = v___x_821_;
v___y_763_ = v___y_818_;
v___y_764_ = v___y_817_;
v___y_765_ = v___x_827_;
goto v___jp_751_;
}
else
{
lean_object* v___x_828_; 
v___x_828_ = lean_array_fget_borrowed(v_givenNames_554_, v_minorIdx_563_);
lean_inc(v___x_828_);
v___y_752_ = v___x_823_;
v___y_753_ = v___y_816_;
v___y_754_ = v___y_814_;
v___y_755_ = v___y_813_;
v___y_756_ = v___x_819_;
v___y_757_ = v___x_820_;
v___y_758_ = v___y_809_;
v___y_759_ = v___y_812_;
v___y_760_ = v___y_815_;
v___y_761_ = v___y_811_;
v___y_762_ = v___x_821_;
v___y_763_ = v___y_818_;
v___y_764_ = v___y_817_;
v___y_765_ = v___x_828_;
goto v___jp_751_;
}
}
v___jp_829_:
{
if (v___y_838_ == 0)
{
lean_object* v___x_839_; uint8_t v___x_840_; 
lean_inc_ref(v___y_837_);
v___x_839_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTargetArity(v___y_837_);
v___x_840_ = lean_nat_dec_lt(v___x_839_, v_initialArity_560_);
if (v___x_840_ == 0)
{
v___y_809_ = v___y_830_;
v___y_810_ = v___x_839_;
v___y_811_ = v___y_838_;
v___y_812_ = v___y_833_;
v___y_813_ = v___y_837_;
v___y_814_ = v___y_836_;
v___y_815_ = v___y_832_;
v___y_816_ = v___y_835_;
v___y_817_ = v___y_831_;
v___y_818_ = v___y_834_;
goto v___jp_808_;
}
else
{
lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; 
v___x_841_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1));
v___x_842_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9);
lean_inc(v_mvarId_553_);
v___x_843_ = l_Lean_Meta_throwTacticEx___redArg(v___x_841_, v_mvarId_553_, v___x_842_, v___y_832_, v___y_835_, v___y_831_, v___y_834_);
if (lean_obj_tag(v___x_843_) == 0)
{
lean_dec_ref_known(v___x_843_, 1);
v___y_809_ = v___y_830_;
v___y_810_ = v___x_839_;
v___y_811_ = v___y_838_;
v___y_812_ = v___y_833_;
v___y_813_ = v___y_837_;
v___y_814_ = v___y_836_;
v___y_815_ = v___y_832_;
v___y_816_ = v___y_835_;
v___y_817_ = v___y_831_;
v___y_818_ = v___y_834_;
goto v___jp_808_;
}
else
{
lean_object* v_a_844_; lean_object* v___x_846_; uint8_t v_isShared_847_; uint8_t v_isSharedCheck_851_; 
lean_dec(v___x_839_);
lean_dec_ref(v___y_837_);
lean_dec(v___y_833_);
lean_dec(v_a_750_);
lean_dec_ref(v_subgoals_567_);
lean_dec_ref(v_recursor_564_);
lean_dec(v_minorIdx_563_);
lean_dec(v_pos_562_);
lean_dec(v_baseSubst_559_);
lean_dec_ref(v_major_557_);
lean_dec(v_mvarId_553_);
v_a_844_ = lean_ctor_get(v___x_843_, 0);
v_isSharedCheck_851_ = !lean_is_exclusive(v___x_843_);
if (v_isSharedCheck_851_ == 0)
{
v___x_846_ = v___x_843_;
v_isShared_847_ = v_isSharedCheck_851_;
goto v_resetjp_845_;
}
else
{
lean_inc(v_a_844_);
lean_dec(v___x_843_);
v___x_846_ = lean_box(0);
v_isShared_847_ = v_isSharedCheck_851_;
goto v_resetjp_845_;
}
v_resetjp_845_:
{
lean_object* v___x_849_; 
if (v_isShared_847_ == 0)
{
v___x_849_ = v___x_846_;
goto v_reusejp_848_;
}
else
{
lean_object* v_reuseFailAlloc_850_; 
v_reuseFailAlloc_850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_850_, 0, v_a_844_);
v___x_849_ = v_reuseFailAlloc_850_;
goto v_reusejp_848_;
}
v_reusejp_848_:
{
return v___x_849_;
}
}
}
}
}
else
{
lean_object* v___x_852_; lean_object* v___x_853_; 
v___x_852_ = lean_box(0);
lean_inc_ref(v___y_837_);
v___x_853_ = l_Lean_Meta_synthInstance_x3f(v___y_837_, v___x_852_, v___y_832_, v___y_835_, v___y_831_, v___y_834_);
if (lean_obj_tag(v___x_853_) == 0)
{
lean_object* v_a_854_; 
v_a_854_ = lean_ctor_get(v___x_853_, 0);
lean_inc(v_a_854_);
lean_dec_ref_known(v___x_853_, 1);
if (lean_obj_tag(v_a_854_) == 0)
{
lean_object* v___x_855_; 
v___x_855_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___y_837_, v___y_833_, v___y_832_, v___y_835_, v___y_831_, v___y_834_);
if (lean_obj_tag(v___x_855_) == 0)
{
lean_object* v_a_856_; lean_object* v___x_857_; lean_object* v___x_858_; 
v_a_856_ = lean_ctor_get(v___x_855_, 0);
lean_inc_n(v_a_856_, 2);
lean_dec_ref_known(v___x_855_, 1);
v___x_857_ = l_Lean_Expr_app___override(v_recursor_564_, v_a_856_);
lean_inc(v_mvarId_553_);
v___x_858_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTypeBody(v_mvarId_553_, v_a_750_, v_a_856_, v___y_832_, v___y_835_, v___y_831_, v___y_834_);
if (lean_obj_tag(v___x_858_) == 0)
{
lean_object* v_a_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; 
v_a_859_ = lean_ctor_get(v___x_858_, 0);
lean_inc(v_a_859_);
lean_dec_ref_known(v___x_858_, 1);
v___x_860_ = lean_nat_add(v_pos_562_, v___y_836_);
lean_dec(v_pos_562_);
v___x_861_ = lean_nat_add(v_minorIdx_563_, v___y_836_);
lean_dec(v_minorIdx_563_);
v___x_862_ = l_Lean_Expr_mvarId_x21(v_a_856_);
lean_dec(v_a_856_);
v___x_863_ = ((lean_object*)(l_Lean_Meta_instInhabitedInductionSubgoal_default___closed__0));
v___x_864_ = lean_box(0);
v___x_865_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_865_, 0, v___x_862_);
lean_ctor_set(v___x_865_, 1, v___x_863_);
lean_ctor_set(v___x_865_, 2, v___x_864_);
v___x_866_ = lean_array_push(v_subgoals_567_, v___x_865_);
v_pos_562_ = v___x_860_;
v_minorIdx_563_ = v___x_861_;
v_recursor_564_ = v___x_857_;
v_recursorType_565_ = v_a_859_;
v_subgoals_567_ = v___x_866_;
v_a_568_ = v___y_832_;
v_a_569_ = v___y_835_;
v_a_570_ = v___y_831_;
v_a_571_ = v___y_834_;
goto _start;
}
else
{
lean_object* v_a_868_; lean_object* v___x_870_; uint8_t v_isShared_871_; uint8_t v_isSharedCheck_875_; 
lean_dec_ref(v___x_857_);
lean_dec(v_a_856_);
lean_dec_ref(v_subgoals_567_);
lean_dec(v_minorIdx_563_);
lean_dec(v_pos_562_);
lean_dec(v_baseSubst_559_);
lean_dec_ref(v_major_557_);
lean_dec(v_mvarId_553_);
v_a_868_ = lean_ctor_get(v___x_858_, 0);
v_isSharedCheck_875_ = !lean_is_exclusive(v___x_858_);
if (v_isSharedCheck_875_ == 0)
{
v___x_870_ = v___x_858_;
v_isShared_871_ = v_isSharedCheck_875_;
goto v_resetjp_869_;
}
else
{
lean_inc(v_a_868_);
lean_dec(v___x_858_);
v___x_870_ = lean_box(0);
v_isShared_871_ = v_isSharedCheck_875_;
goto v_resetjp_869_;
}
v_resetjp_869_:
{
lean_object* v___x_873_; 
if (v_isShared_871_ == 0)
{
v___x_873_ = v___x_870_;
goto v_reusejp_872_;
}
else
{
lean_object* v_reuseFailAlloc_874_; 
v_reuseFailAlloc_874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_874_, 0, v_a_868_);
v___x_873_ = v_reuseFailAlloc_874_;
goto v_reusejp_872_;
}
v_reusejp_872_:
{
return v___x_873_;
}
}
}
}
else
{
lean_object* v_a_876_; lean_object* v___x_878_; uint8_t v_isShared_879_; uint8_t v_isSharedCheck_883_; 
lean_dec(v_a_750_);
lean_dec_ref(v_subgoals_567_);
lean_dec_ref(v_recursor_564_);
lean_dec(v_minorIdx_563_);
lean_dec(v_pos_562_);
lean_dec(v_baseSubst_559_);
lean_dec_ref(v_major_557_);
lean_dec(v_mvarId_553_);
v_a_876_ = lean_ctor_get(v___x_855_, 0);
v_isSharedCheck_883_ = !lean_is_exclusive(v___x_855_);
if (v_isSharedCheck_883_ == 0)
{
v___x_878_ = v___x_855_;
v_isShared_879_ = v_isSharedCheck_883_;
goto v_resetjp_877_;
}
else
{
lean_inc(v_a_876_);
lean_dec(v___x_855_);
v___x_878_ = lean_box(0);
v_isShared_879_ = v_isSharedCheck_883_;
goto v_resetjp_877_;
}
v_resetjp_877_:
{
lean_object* v___x_881_; 
if (v_isShared_879_ == 0)
{
v___x_881_ = v___x_878_;
goto v_reusejp_880_;
}
else
{
lean_object* v_reuseFailAlloc_882_; 
v_reuseFailAlloc_882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_882_, 0, v_a_876_);
v___x_881_ = v_reuseFailAlloc_882_;
goto v_reusejp_880_;
}
v_reusejp_880_:
{
return v___x_881_;
}
}
}
}
else
{
lean_object* v_val_884_; lean_object* v___x_885_; lean_object* v___x_886_; 
lean_dec_ref(v___y_837_);
lean_dec(v___y_833_);
v_val_884_ = lean_ctor_get(v_a_854_, 0);
lean_inc_n(v_val_884_, 2);
lean_dec_ref_known(v_a_854_, 1);
v___x_885_ = l_Lean_Expr_app___override(v_recursor_564_, v_val_884_);
lean_inc(v_mvarId_553_);
v___x_886_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTypeBody(v_mvarId_553_, v_a_750_, v_val_884_, v___y_832_, v___y_835_, v___y_831_, v___y_834_);
lean_dec(v_val_884_);
if (lean_obj_tag(v___x_886_) == 0)
{
lean_object* v_a_887_; lean_object* v___x_888_; lean_object* v___x_889_; 
v_a_887_ = lean_ctor_get(v___x_886_, 0);
lean_inc(v_a_887_);
lean_dec_ref_known(v___x_886_, 1);
v___x_888_ = lean_nat_add(v_pos_562_, v___y_836_);
lean_dec(v_pos_562_);
v___x_889_ = lean_nat_add(v_minorIdx_563_, v___y_836_);
lean_dec(v_minorIdx_563_);
v_pos_562_ = v___x_888_;
v_minorIdx_563_ = v___x_889_;
v_recursor_564_ = v___x_885_;
v_recursorType_565_ = v_a_887_;
v_a_568_ = v___y_832_;
v_a_569_ = v___y_835_;
v_a_570_ = v___y_831_;
v_a_571_ = v___y_834_;
goto _start;
}
else
{
lean_object* v_a_891_; lean_object* v___x_893_; uint8_t v_isShared_894_; uint8_t v_isSharedCheck_898_; 
lean_dec_ref(v___x_885_);
lean_dec_ref(v_subgoals_567_);
lean_dec(v_minorIdx_563_);
lean_dec(v_pos_562_);
lean_dec(v_baseSubst_559_);
lean_dec_ref(v_major_557_);
lean_dec(v_mvarId_553_);
v_a_891_ = lean_ctor_get(v___x_886_, 0);
v_isSharedCheck_898_ = !lean_is_exclusive(v___x_886_);
if (v_isSharedCheck_898_ == 0)
{
v___x_893_ = v___x_886_;
v_isShared_894_ = v_isSharedCheck_898_;
goto v_resetjp_892_;
}
else
{
lean_inc(v_a_891_);
lean_dec(v___x_886_);
v___x_893_ = lean_box(0);
v_isShared_894_ = v_isSharedCheck_898_;
goto v_resetjp_892_;
}
v_resetjp_892_:
{
lean_object* v___x_896_; 
if (v_isShared_894_ == 0)
{
v___x_896_ = v___x_893_;
goto v_reusejp_895_;
}
else
{
lean_object* v_reuseFailAlloc_897_; 
v_reuseFailAlloc_897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_897_, 0, v_a_891_);
v___x_896_ = v_reuseFailAlloc_897_;
goto v_reusejp_895_;
}
v_reusejp_895_:
{
return v___x_896_;
}
}
}
}
}
else
{
lean_object* v_a_899_; lean_object* v___x_901_; uint8_t v_isShared_902_; uint8_t v_isSharedCheck_906_; 
lean_dec_ref(v___y_837_);
lean_dec(v___y_833_);
lean_dec(v_a_750_);
lean_dec_ref(v_subgoals_567_);
lean_dec_ref(v_recursor_564_);
lean_dec(v_minorIdx_563_);
lean_dec(v_pos_562_);
lean_dec(v_baseSubst_559_);
lean_dec_ref(v_major_557_);
lean_dec(v_mvarId_553_);
v_a_899_ = lean_ctor_get(v___x_853_, 0);
v_isSharedCheck_906_ = !lean_is_exclusive(v___x_853_);
if (v_isSharedCheck_906_ == 0)
{
v___x_901_ = v___x_853_;
v_isShared_902_ = v_isSharedCheck_906_;
goto v_resetjp_900_;
}
else
{
lean_inc(v_a_899_);
lean_dec(v___x_853_);
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
v___jp_907_:
{
uint8_t v___x_917_; 
v___x_917_ = l_Lean_BinderInfo_isInstImplicit(v___y_911_);
if (v___x_917_ == 0)
{
v___y_830_ = v___y_908_;
v___y_831_ = v___y_910_;
v___y_832_ = v___y_909_;
v___y_833_ = v___y_916_;
v___y_834_ = v___y_912_;
v___y_835_ = v___y_913_;
v___y_836_ = v___y_915_;
v___y_837_ = v___y_914_;
v___y_838_ = v___x_917_;
goto v___jp_829_;
}
else
{
lean_object* v___x_918_; lean_object* v___x_919_; uint8_t v___x_920_; 
v___x_918_ = lean_array_get_size(v_givenNames_554_);
v___x_919_ = lean_unsigned_to_nat(0u);
v___x_920_ = lean_nat_dec_eq(v___x_918_, v___x_919_);
v___y_830_ = v___y_908_;
v___y_831_ = v___y_910_;
v___y_832_ = v___y_909_;
v___y_833_ = v___y_916_;
v___y_834_ = v___y_912_;
v___y_835_ = v___y_913_;
v___y_836_ = v___y_915_;
v___y_837_ = v___y_914_;
v___y_838_ = v___x_920_;
goto v___jp_829_;
}
}
v___jp_921_:
{
if (lean_obj_tag(v_a_750_) == 7)
{
lean_object* v_binderName_928_; lean_object* v_binderType_929_; uint8_t v_binderInfo_930_; lean_object* v___x_931_; lean_object* v___x_932_; uint8_t v___x_933_; 
v_binderName_928_ = lean_ctor_get(v_a_750_, 0);
v_binderType_929_ = lean_ctor_get(v_a_750_, 1);
v_binderInfo_930_ = lean_ctor_get_uint8(v_a_750_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_929_);
v___x_931_ = l_Lean_Expr_headBeta(v_binderType_929_);
v___x_932_ = lean_unsigned_to_nat(1u);
v___x_933_ = lean_nat_dec_eq(v_numMinors_561_, v___x_932_);
if (v___x_933_ == 0)
{
lean_object* v___x_934_; lean_object* v___x_935_; 
v___x_934_ = l_Lean_Name_eraseMacroScopes(v_binderName_928_);
v___x_935_ = l_Lean_Name_append(v___y_923_, v___x_934_);
v___y_908_ = v___y_922_;
v___y_909_ = v___y_924_;
v___y_910_ = v___y_926_;
v___y_911_ = v_binderInfo_930_;
v___y_912_ = v___y_927_;
v___y_913_ = v___y_925_;
v___y_914_ = v___x_931_;
v___y_915_ = v___x_932_;
v___y_916_ = v___x_935_;
goto v___jp_907_;
}
else
{
v___y_908_ = v___y_922_;
v___y_909_ = v___y_924_;
v___y_910_ = v___y_926_;
v___y_911_ = v_binderInfo_930_;
v___y_912_ = v___y_927_;
v___y_913_ = v___y_925_;
v___y_914_ = v___x_931_;
v___y_915_ = v___x_932_;
v___y_916_ = v___y_923_;
goto v___jp_907_;
}
}
else
{
lean_object* v___x_936_; lean_object* v___x_937_; 
lean_dec(v___y_923_);
lean_dec(v_a_750_);
lean_dec_ref(v_subgoals_567_);
lean_dec_ref(v_recursor_564_);
lean_dec(v_minorIdx_563_);
lean_dec(v_pos_562_);
lean_dec(v_baseSubst_559_);
lean_dec_ref(v_major_557_);
lean_dec(v_mvarId_553_);
v___x_936_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__15, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__15_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__15);
v___x_937_ = l_panic___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__4(v___x_936_, v___y_924_, v___y_925_, v___y_926_, v___y_927_);
return v___x_937_;
}
}
v___jp_938_:
{
if (v___y_939_ == 0)
{
lean_dec(v_a_750_);
lean_dec(v_minorIdx_563_);
lean_dec(v_pos_562_);
lean_dec(v_baseSubst_559_);
lean_dec_ref(v_major_557_);
if (v_consumedMajor_566_ == 0)
{
lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; 
v___x_940_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1));
v___x_941_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9);
lean_inc(v_mvarId_553_);
v___x_942_ = l_Lean_Meta_throwTacticEx___redArg(v___x_940_, v_mvarId_553_, v___x_941_, v_a_568_, v_a_569_, v_a_570_, v_a_571_);
if (lean_obj_tag(v___x_942_) == 0)
{
lean_dec_ref_known(v___x_942_, 1);
v___y_574_ = v_a_568_;
v___y_575_ = v_a_569_;
v___y_576_ = v_a_570_;
v___y_577_ = v_a_571_;
goto v___jp_573_;
}
else
{
lean_object* v_a_943_; lean_object* v___x_945_; uint8_t v_isShared_946_; uint8_t v_isSharedCheck_950_; 
lean_dec_ref(v_subgoals_567_);
lean_dec_ref(v_recursor_564_);
lean_dec(v_mvarId_553_);
v_a_943_ = lean_ctor_get(v___x_942_, 0);
v_isSharedCheck_950_ = !lean_is_exclusive(v___x_942_);
if (v_isSharedCheck_950_ == 0)
{
v___x_945_ = v___x_942_;
v_isShared_946_ = v_isSharedCheck_950_;
goto v_resetjp_944_;
}
else
{
lean_inc(v_a_943_);
lean_dec(v___x_942_);
v___x_945_ = lean_box(0);
v_isShared_946_ = v_isSharedCheck_950_;
goto v_resetjp_944_;
}
v_resetjp_944_:
{
lean_object* v___x_948_; 
if (v_isShared_946_ == 0)
{
v___x_948_ = v___x_945_;
goto v_reusejp_947_;
}
else
{
lean_object* v_reuseFailAlloc_949_; 
v_reuseFailAlloc_949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_949_, 0, v_a_943_);
v___x_948_ = v_reuseFailAlloc_949_;
goto v_reusejp_947_;
}
v_reusejp_947_:
{
return v___x_948_;
}
}
}
}
else
{
v___y_574_ = v_a_568_;
v___y_575_ = v_a_569_;
v___y_576_ = v_a_570_;
v___y_577_ = v_a_571_;
goto v___jp_573_;
}
}
else
{
lean_object* v___x_951_; uint8_t v___x_952_; 
v___x_951_ = l_Lean_Meta_RecursorInfo_firstIndexPos(v_recursorInfo_555_);
v___x_952_ = lean_nat_dec_eq(v_pos_562_, v___x_951_);
lean_dec(v___x_951_);
if (v___x_952_ == 0)
{
lean_object* v___x_953_; 
lean_inc(v_mvarId_553_);
v___x_953_ = l_Lean_MVarId_getTag(v_mvarId_553_, v_a_568_, v_a_569_, v_a_570_, v_a_571_);
if (lean_obj_tag(v___x_953_) == 0)
{
if (v___x_748_ == 0)
{
lean_object* v_a_954_; 
v_a_954_ = lean_ctor_get(v___x_953_, 0);
lean_inc(v_a_954_);
lean_dec_ref_known(v___x_953_, 1);
v___y_922_ = v___y_939_;
v___y_923_ = v_a_954_;
v___y_924_ = v_a_568_;
v___y_925_ = v_a_569_;
v___y_926_ = v_a_570_;
v___y_927_ = v_a_571_;
goto v___jp_921_;
}
else
{
lean_object* v_a_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; 
v_a_955_ = lean_ctor_get(v___x_953_, 0);
lean_inc(v_a_955_);
lean_dec_ref_known(v___x_953_, 1);
v___x_956_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1));
v___x_957_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9);
lean_inc(v_mvarId_553_);
v___x_958_ = l_Lean_Meta_throwTacticEx___redArg(v___x_956_, v_mvarId_553_, v___x_957_, v_a_568_, v_a_569_, v_a_570_, v_a_571_);
if (lean_obj_tag(v___x_958_) == 0)
{
lean_dec_ref_known(v___x_958_, 1);
v___y_922_ = v___y_939_;
v___y_923_ = v_a_955_;
v___y_924_ = v_a_568_;
v___y_925_ = v_a_569_;
v___y_926_ = v_a_570_;
v___y_927_ = v_a_571_;
goto v___jp_921_;
}
else
{
lean_object* v_a_959_; lean_object* v___x_961_; uint8_t v_isShared_962_; uint8_t v_isSharedCheck_966_; 
lean_dec(v_a_955_);
lean_dec(v_a_750_);
lean_dec_ref(v_subgoals_567_);
lean_dec_ref(v_recursor_564_);
lean_dec(v_minorIdx_563_);
lean_dec(v_pos_562_);
lean_dec(v_baseSubst_559_);
lean_dec_ref(v_major_557_);
lean_dec(v_mvarId_553_);
v_a_959_ = lean_ctor_get(v___x_958_, 0);
v_isSharedCheck_966_ = !lean_is_exclusive(v___x_958_);
if (v_isSharedCheck_966_ == 0)
{
v___x_961_ = v___x_958_;
v_isShared_962_ = v_isSharedCheck_966_;
goto v_resetjp_960_;
}
else
{
lean_inc(v_a_959_);
lean_dec(v___x_958_);
v___x_961_ = lean_box(0);
v_isShared_962_ = v_isSharedCheck_966_;
goto v_resetjp_960_;
}
v_resetjp_960_:
{
lean_object* v___x_964_; 
if (v_isShared_962_ == 0)
{
v___x_964_ = v___x_961_;
goto v_reusejp_963_;
}
else
{
lean_object* v_reuseFailAlloc_965_; 
v_reuseFailAlloc_965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_965_, 0, v_a_959_);
v___x_964_ = v_reuseFailAlloc_965_;
goto v_reusejp_963_;
}
v_reusejp_963_:
{
return v___x_964_;
}
}
}
}
}
else
{
lean_object* v_a_967_; lean_object* v___x_969_; uint8_t v_isShared_970_; uint8_t v_isSharedCheck_974_; 
lean_dec(v_a_750_);
lean_dec_ref(v_subgoals_567_);
lean_dec_ref(v_recursor_564_);
lean_dec(v_minorIdx_563_);
lean_dec(v_pos_562_);
lean_dec(v_baseSubst_559_);
lean_dec_ref(v_major_557_);
lean_dec(v_mvarId_553_);
v_a_967_ = lean_ctor_get(v___x_953_, 0);
v_isSharedCheck_974_ = !lean_is_exclusive(v___x_953_);
if (v_isSharedCheck_974_ == 0)
{
v___x_969_ = v___x_953_;
v_isShared_970_ = v_isSharedCheck_974_;
goto v_resetjp_968_;
}
else
{
lean_inc(v_a_967_);
lean_dec(v___x_953_);
v___x_969_ = lean_box(0);
v_isShared_970_ = v_isSharedCheck_974_;
goto v_resetjp_968_;
}
v_resetjp_968_:
{
lean_object* v___x_972_; 
if (v_isShared_970_ == 0)
{
v___x_972_ = v___x_969_;
goto v_reusejp_971_;
}
else
{
lean_object* v_reuseFailAlloc_973_; 
v_reuseFailAlloc_973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_973_, 0, v_a_967_);
v___x_972_ = v_reuseFailAlloc_973_;
goto v_reusejp_971_;
}
v_reusejp_971_:
{
return v___x_972_;
}
}
}
}
else
{
lean_object* v___x_975_; lean_object* v___x_976_; uint8_t v___x_977_; 
v___x_975_ = lean_unsigned_to_nat(0u);
v___x_976_ = lean_array_get_size(v_indices_558_);
v___x_977_ = lean_nat_dec_lt(v___x_975_, v___x_976_);
if (v___x_977_ == 0)
{
v___y_714_ = v___x_952_;
v___y_715_ = v___x_976_;
v_fst_716_ = v_recursor_564_;
v_snd_717_ = v_a_750_;
goto v___jp_713_;
}
else
{
lean_object* v___x_978_; uint8_t v___x_979_; 
lean_inc(v_a_750_);
lean_inc_ref(v_recursor_564_);
v___x_978_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_978_, 0, v_recursor_564_);
lean_ctor_set(v___x_978_, 1, v_a_750_);
v___x_979_ = lean_nat_dec_le(v___x_976_, v___x_976_);
if (v___x_979_ == 0)
{
if (v___x_977_ == 0)
{
lean_dec_ref_known(v___x_978_, 2);
v___y_714_ = v___x_952_;
v___y_715_ = v___x_976_;
v_fst_716_ = v_recursor_564_;
v_snd_717_ = v_a_750_;
goto v___jp_713_;
}
else
{
size_t v___x_980_; size_t v___x_981_; lean_object* v___x_982_; 
lean_dec(v_a_750_);
lean_dec_ref(v_recursor_564_);
v___x_980_ = ((size_t)0ULL);
v___x_981_ = lean_usize_of_nat(v___x_976_);
lean_inc(v_mvarId_553_);
v___x_982_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__5(v_mvarId_553_, v_indices_558_, v___x_980_, v___x_981_, v___x_978_, v_a_568_, v_a_569_, v_a_570_, v_a_571_);
v___y_734_ = v___x_976_;
v___y_735_ = v___x_952_;
v___y_736_ = v___x_982_;
goto v___jp_733_;
}
}
else
{
size_t v___x_983_; size_t v___x_984_; lean_object* v___x_985_; 
lean_dec(v_a_750_);
lean_dec_ref(v_recursor_564_);
v___x_983_ = ((size_t)0ULL);
v___x_984_ = lean_usize_of_nat(v___x_976_);
lean_inc(v_mvarId_553_);
v___x_985_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__5(v_mvarId_553_, v_indices_558_, v___x_983_, v___x_984_, v___x_978_, v_a_568_, v_a_569_, v_a_570_, v_a_571_);
v___y_734_ = v___x_976_;
v___y_735_ = v___x_952_;
v___y_736_ = v___x_985_;
goto v___jp_733_;
}
}
}
}
}
}
else
{
lean_object* v_a_989_; lean_object* v___x_991_; uint8_t v_isShared_992_; uint8_t v_isSharedCheck_996_; 
lean_dec_ref(v_subgoals_567_);
lean_dec_ref(v_recursor_564_);
lean_dec(v_minorIdx_563_);
lean_dec(v_pos_562_);
lean_dec(v_baseSubst_559_);
lean_dec_ref(v_major_557_);
lean_dec(v_mvarId_553_);
v_a_989_ = lean_ctor_get(v___x_749_, 0);
v_isSharedCheck_996_ = !lean_is_exclusive(v___x_749_);
if (v_isSharedCheck_996_ == 0)
{
v___x_991_ = v___x_749_;
v_isShared_992_ = v_isSharedCheck_996_;
goto v_resetjp_990_;
}
else
{
lean_inc(v_a_989_);
lean_dec(v___x_749_);
v___x_991_ = lean_box(0);
v_isShared_992_ = v_isSharedCheck_996_;
goto v_resetjp_990_;
}
v_resetjp_990_:
{
lean_object* v___x_994_; 
if (v_isShared_992_ == 0)
{
v___x_994_ = v___x_991_;
goto v_reusejp_993_;
}
else
{
lean_object* v_reuseFailAlloc_995_; 
v_reuseFailAlloc_995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_995_, 0, v_a_989_);
v___x_994_ = v_reuseFailAlloc_995_;
goto v_reusejp_993_;
}
v_reusejp_993_:
{
return v___x_994_;
}
}
}
v___jp_573_:
{
lean_object* v___x_578_; 
v___x_578_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0___redArg(v_mvarId_553_, v_recursor_564_, v___y_575_);
if (lean_obj_tag(v___x_578_) == 0)
{
lean_object* v___x_580_; uint8_t v_isShared_581_; uint8_t v_isSharedCheck_620_; 
v_isSharedCheck_620_ = !lean_is_exclusive(v___x_578_);
if (v_isSharedCheck_620_ == 0)
{
lean_object* v_unused_621_; 
v_unused_621_ = lean_ctor_get(v___x_578_, 0);
lean_dec(v_unused_621_);
v___x_580_ = v___x_578_;
v_isShared_581_ = v_isSharedCheck_620_;
goto v_resetjp_579_;
}
else
{
lean_dec(v___x_578_);
v___x_580_ = lean_box(0);
v_isShared_581_ = v_isSharedCheck_620_;
goto v_resetjp_579_;
}
v_resetjp_579_:
{
lean_object* v_toCold_582_; lean_object* v_options_583_; uint8_t v_hasTrace_584_; 
v_toCold_582_ = lean_ctor_get(v___y_576_, 0);
v_options_583_ = lean_ctor_get(v_toCold_582_, 2);
v_hasTrace_584_ = lean_ctor_get_uint8(v_options_583_, sizeof(void*)*1);
if (v_hasTrace_584_ == 0)
{
lean_object* v___x_586_; 
if (v_isShared_581_ == 0)
{
lean_ctor_set(v___x_580_, 0, v_subgoals_567_);
v___x_586_ = v___x_580_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_587_; 
v_reuseFailAlloc_587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_587_, 0, v_subgoals_567_);
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
v_inheritedTraceOptions_588_ = lean_ctor_get(v_toCold_582_, 11);
v___x_589_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__2));
v___x_590_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5);
v___x_591_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_588_, v_options_583_, v___x_590_);
if (v___x_591_ == 0)
{
lean_object* v___x_593_; 
if (v_isShared_581_ == 0)
{
lean_ctor_set(v___x_580_, 0, v_subgoals_567_);
v___x_593_ = v___x_580_;
goto v_reusejp_592_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v_subgoals_567_);
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
lean_del_object(v___x_580_);
v___x_595_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__7, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__7_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__7);
v___x_596_ = lean_array_get_size(v_subgoals_567_);
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
v___x_603_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1(v___x_589_, v___x_602_, v___y_574_, v___y_575_, v___y_576_, v___y_577_);
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
lean_ctor_set(v___x_605_, 0, v_subgoals_567_);
v___x_608_ = v___x_605_;
goto v_reusejp_607_;
}
else
{
lean_object* v_reuseFailAlloc_609_; 
v_reuseFailAlloc_609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v_subgoals_567_);
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
lean_dec_ref(v_subgoals_567_);
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
lean_dec_ref(v_subgoals_567_);
v_a_622_ = lean_ctor_get(v___x_578_, 0);
v_isSharedCheck_629_ = !lean_is_exclusive(v___x_578_);
if (v_isSharedCheck_629_ == 0)
{
v___x_624_ = v___x_578_;
v_isShared_625_ = v_isSharedCheck_629_;
goto v_resetjp_623_;
}
else
{
lean_inc(v_a_622_);
lean_dec(v___x_578_);
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
v___x_647_ = l_Lean_Meta_introNCore(v___y_644_, v___y_639_, v___y_631_, v___y_646_, v___y_642_, v___y_636_, v___y_633_, v___y_645_, v___y_634_);
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
v___x_652_ = l_Lean_Meta_introNCore(v_snd_650_, v___y_632_, v___x_651_, v___y_642_, v___y_640_, v___y_636_, v___y_633_, v___y_645_, v___y_634_);
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
lean_inc(v_baseSubst_559_);
lean_inc(v___y_641_);
v___x_656_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__2___redArg(v___y_643_, v_reverted_556_, v_fst_654_, v___y_641_, v___y_641_, v_baseSubst_559_);
lean_dec(v___y_641_);
lean_dec(v_fst_654_);
lean_dec(v___y_643_);
v_sz_657_ = lean_array_size(v_fst_649_);
v___x_658_ = ((size_t)0ULL);
v___x_659_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__3(v_sz_657_, v___x_658_, v_fst_649_);
v___x_660_ = lean_nat_add(v_pos_562_, v___y_638_);
lean_dec(v_pos_562_);
v___x_661_ = lean_nat_add(v_minorIdx_563_, v___y_638_);
lean_dec(v_minorIdx_563_);
v___x_662_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_662_, 0, v_snd_655_);
lean_ctor_set(v___x_662_, 1, v___x_659_);
lean_ctor_set(v___x_662_, 2, v___x_656_);
v___x_663_ = lean_array_push(v_subgoals_567_, v___x_662_);
v_pos_562_ = v___x_660_;
v_minorIdx_563_ = v___x_661_;
v_recursor_564_ = v___y_637_;
v_recursorType_565_ = v___y_635_;
v_subgoals_567_ = v___x_663_;
v_a_568_ = v___y_636_;
v_a_569_ = v___y_633_;
v_a_570_ = v___y_645_;
v_a_571_ = v___y_634_;
goto _start;
}
else
{
lean_object* v_a_665_; lean_object* v___x_667_; uint8_t v_isShared_668_; uint8_t v_isSharedCheck_672_; 
lean_dec(v_fst_649_);
lean_dec(v___y_643_);
lean_dec(v___y_641_);
lean_dec_ref(v___y_637_);
lean_dec_ref(v___y_635_);
lean_dec_ref(v_subgoals_567_);
lean_dec(v_minorIdx_563_);
lean_dec(v_pos_562_);
lean_dec(v_baseSubst_559_);
lean_dec_ref(v_major_557_);
lean_dec(v_mvarId_553_);
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
lean_dec(v___y_643_);
lean_dec(v___y_641_);
lean_dec_ref(v___y_637_);
lean_dec_ref(v___y_635_);
lean_dec(v___y_632_);
lean_dec_ref(v_subgoals_567_);
lean_dec(v_minorIdx_563_);
lean_dec(v_pos_562_);
lean_dec(v_baseSubst_559_);
lean_dec_ref(v_major_557_);
lean_dec(v_mvarId_553_);
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
v___x_698_ = l_Lean_Expr_fvarId_x21(v_major_557_);
v___x_699_ = l_Lean_MVarId_tryClear(v___x_697_, v___x_698_, v___y_693_, v___y_694_, v___y_695_, v___y_696_);
if (lean_obj_tag(v___x_699_) == 0)
{
uint8_t v_explicit_700_; 
v_explicit_700_ = lean_ctor_get_uint8(v___y_689_, sizeof(void*)*1);
if (v_explicit_700_ == 0)
{
lean_object* v_a_701_; lean_object* v_varNames_702_; 
v_a_701_ = lean_ctor_get(v___x_699_, 0);
lean_inc(v_a_701_);
lean_dec_ref_known(v___x_699_, 1);
v_varNames_702_ = lean_ctor_get(v___y_689_, 0);
lean_inc(v_varNames_702_);
lean_dec_ref(v___y_689_);
v___y_631_ = v_varNames_702_;
v___y_632_ = v___y_686_;
v___y_633_ = v___y_694_;
v___y_634_ = v___y_696_;
v___y_635_ = v___y_688_;
v___y_636_ = v___y_693_;
v___y_637_ = v___y_692_;
v___y_638_ = v___y_691_;
v___y_639_ = v___y_690_;
v___y_640_ = v___y_683_;
v___y_641_ = v___y_682_;
v___y_642_ = v___y_684_;
v___y_643_ = v___y_685_;
v___y_644_ = v_a_701_;
v___y_645_ = v___y_695_;
v___y_646_ = v___y_683_;
goto v___jp_630_;
}
else
{
lean_object* v_a_703_; lean_object* v_varNames_704_; 
v_a_703_ = lean_ctor_get(v___x_699_, 0);
lean_inc(v_a_703_);
lean_dec_ref_known(v___x_699_, 1);
v_varNames_704_ = lean_ctor_get(v___y_689_, 0);
lean_inc(v_varNames_704_);
lean_dec_ref(v___y_689_);
v___y_631_ = v_varNames_704_;
v___y_632_ = v___y_686_;
v___y_633_ = v___y_694_;
v___y_634_ = v___y_696_;
v___y_635_ = v___y_688_;
v___y_636_ = v___y_693_;
v___y_637_ = v___y_692_;
v___y_638_ = v___y_691_;
v___y_639_ = v___y_690_;
v___y_640_ = v___y_683_;
v___y_641_ = v___y_682_;
v___y_642_ = v___y_684_;
v___y_643_ = v___y_685_;
v___y_644_ = v_a_703_;
v___y_645_ = v___y_695_;
v___y_646_ = v___y_684_;
goto v___jp_630_;
}
}
else
{
lean_object* v_a_705_; lean_object* v___x_707_; uint8_t v_isShared_708_; uint8_t v_isSharedCheck_712_; 
lean_dec_ref(v___y_692_);
lean_dec(v___y_690_);
lean_dec_ref(v___y_689_);
lean_dec_ref(v___y_688_);
lean_dec(v___y_686_);
lean_dec(v___y_685_);
lean_dec(v___y_682_);
lean_dec_ref(v_subgoals_567_);
lean_dec(v_minorIdx_563_);
lean_dec(v_pos_562_);
lean_dec(v_baseSubst_559_);
lean_dec_ref(v_major_557_);
lean_dec(v_mvarId_553_);
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
lean_object* v___x_718_; lean_object* v___x_719_; 
lean_inc_ref(v_major_557_);
v___x_718_ = l_Lean_Expr_app___override(v_fst_716_, v_major_557_);
lean_inc(v_mvarId_553_);
v___x_719_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTypeBody(v_mvarId_553_, v_snd_717_, v_major_557_, v_a_568_, v_a_569_, v_a_570_, v_a_571_);
if (lean_obj_tag(v___x_719_) == 0)
{
lean_object* v_a_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; 
v_a_720_ = lean_ctor_get(v___x_719_, 0);
lean_inc(v_a_720_);
lean_dec_ref_known(v___x_719_, 1);
v___x_721_ = lean_unsigned_to_nat(1u);
v___x_722_ = lean_nat_add(v_pos_562_, v___x_721_);
lean_dec(v_pos_562_);
v___x_723_ = lean_nat_add(v___x_722_, v___y_715_);
lean_dec(v___y_715_);
lean_dec(v___x_722_);
v_pos_562_ = v___x_723_;
v_recursor_564_ = v___x_718_;
v_recursorType_565_ = v_a_720_;
v_consumedMajor_566_ = v___y_714_;
goto _start;
}
else
{
lean_object* v_a_725_; lean_object* v___x_727_; uint8_t v_isShared_728_; uint8_t v_isSharedCheck_732_; 
lean_dec_ref(v___x_718_);
lean_dec(v___y_715_);
lean_dec_ref(v_subgoals_567_);
lean_dec(v_minorIdx_563_);
lean_dec(v_pos_562_);
lean_dec(v_baseSubst_559_);
lean_dec_ref(v_major_557_);
lean_dec(v_mvarId_553_);
v_a_725_ = lean_ctor_get(v___x_719_, 0);
v_isSharedCheck_732_ = !lean_is_exclusive(v___x_719_);
if (v_isSharedCheck_732_ == 0)
{
v___x_727_ = v___x_719_;
v_isShared_728_ = v_isSharedCheck_732_;
goto v_resetjp_726_;
}
else
{
lean_inc(v_a_725_);
lean_dec(v___x_719_);
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
v___y_714_ = v___y_735_;
v___y_715_ = v___y_734_;
v_fst_716_ = v_fst_738_;
v_snd_717_ = v_snd_739_;
goto v___jp_713_;
}
else
{
lean_object* v_a_740_; lean_object* v___x_742_; uint8_t v_isShared_743_; uint8_t v_isSharedCheck_747_; 
lean_dec(v___y_734_);
lean_dec_ref(v_subgoals_567_);
lean_dec(v_minorIdx_563_);
lean_dec(v_pos_562_);
lean_dec(v_baseSubst_559_);
lean_dec_ref(v_major_557_);
lean_dec(v_mvarId_553_);
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
lean_object* v_mvarId_997_ = _args[0];
lean_object* v_givenNames_998_ = _args[1];
lean_object* v_recursorInfo_999_ = _args[2];
lean_object* v_reverted_1000_ = _args[3];
lean_object* v_major_1001_ = _args[4];
lean_object* v_indices_1002_ = _args[5];
lean_object* v_baseSubst_1003_ = _args[6];
lean_object* v_initialArity_1004_ = _args[7];
lean_object* v_numMinors_1005_ = _args[8];
lean_object* v_pos_1006_ = _args[9];
lean_object* v_minorIdx_1007_ = _args[10];
lean_object* v_recursor_1008_ = _args[11];
lean_object* v_recursorType_1009_ = _args[12];
lean_object* v_consumedMajor_1010_ = _args[13];
lean_object* v_subgoals_1011_ = _args[14];
lean_object* v_a_1012_ = _args[15];
lean_object* v_a_1013_ = _args[16];
lean_object* v_a_1014_ = _args[17];
lean_object* v_a_1015_ = _args[18];
lean_object* v_a_1016_ = _args[19];
_start:
{
uint8_t v_consumedMajor_boxed_1017_; lean_object* v_res_1018_; 
v_consumedMajor_boxed_1017_ = lean_unbox(v_consumedMajor_1010_);
v_res_1018_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop(v_mvarId_997_, v_givenNames_998_, v_recursorInfo_999_, v_reverted_1000_, v_major_1001_, v_indices_1002_, v_baseSubst_1003_, v_initialArity_1004_, v_numMinors_1005_, v_pos_1006_, v_minorIdx_1007_, v_recursor_1008_, v_recursorType_1009_, v_consumedMajor_boxed_1017_, v_subgoals_1011_, v_a_1012_, v_a_1013_, v_a_1014_, v_a_1015_);
lean_dec(v_a_1015_);
lean_dec_ref(v_a_1014_);
lean_dec(v_a_1013_);
lean_dec_ref(v_a_1012_);
lean_dec(v_numMinors_1005_);
lean_dec(v_initialArity_1004_);
lean_dec_ref(v_indices_1002_);
lean_dec_ref(v_reverted_1000_);
lean_dec_ref(v_recursorInfo_999_);
lean_dec_ref(v_givenNames_998_);
return v_res_1018_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0(lean_object* v_mvarId_1019_, lean_object* v_val_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_){
_start:
{
lean_object* v___x_1026_; 
v___x_1026_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0___redArg(v_mvarId_1019_, v_val_1020_, v___y_1022_);
return v___x_1026_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0___boxed(lean_object* v_mvarId_1027_, lean_object* v_val_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_){
_start:
{
lean_object* v_res_1034_; 
v_res_1034_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0(v_mvarId_1027_, v_val_1028_, v___y_1029_, v___y_1030_, v___y_1031_, v___y_1032_);
lean_dec(v___y_1032_);
lean_dec_ref(v___y_1031_);
lean_dec(v___y_1030_);
lean_dec_ref(v___y_1029_);
return v_res_1034_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__2(lean_object* v___x_1035_, lean_object* v_reverted_1036_, lean_object* v_fst_1037_, lean_object* v_n_1038_, lean_object* v_j_1039_, lean_object* v_a_1040_, lean_object* v_a_1041_){
_start:
{
lean_object* v___x_1042_; 
v___x_1042_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__2___redArg(v___x_1035_, v_reverted_1036_, v_fst_1037_, v_n_1038_, v_j_1039_, v_a_1041_);
return v___x_1042_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__2___boxed(lean_object* v___x_1043_, lean_object* v_reverted_1044_, lean_object* v_fst_1045_, lean_object* v_n_1046_, lean_object* v_j_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_){
_start:
{
lean_object* v_res_1050_; 
v_res_1050_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__2(v___x_1043_, v_reverted_1044_, v_fst_1045_, v_n_1046_, v_j_1047_, v_a_1048_, v_a_1049_);
lean_dec(v_n_1046_);
lean_dec_ref(v_fst_1045_);
lean_dec_ref(v_reverted_1044_);
lean_dec(v___x_1043_);
return v_res_1050_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0(lean_object* v_00_u03b2_1051_, lean_object* v_x_1052_, lean_object* v_x_1053_, lean_object* v_x_1054_){
_start:
{
lean_object* v___x_1055_; 
v___x_1055_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0___redArg(v_x_1052_, v_x_1053_, v_x_1054_);
return v___x_1055_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1056_, lean_object* v_x_1057_, size_t v_x_1058_, size_t v_x_1059_, lean_object* v_x_1060_, lean_object* v_x_1061_){
_start:
{
lean_object* v___x_1062_; 
v___x_1062_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2___redArg(v_x_1057_, v_x_1058_, v_x_1059_, v_x_1060_, v_x_1061_);
return v___x_1062_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1063_, lean_object* v_x_1064_, lean_object* v_x_1065_, lean_object* v_x_1066_, lean_object* v_x_1067_, lean_object* v_x_1068_){
_start:
{
size_t v_x_8973__boxed_1069_; size_t v_x_8974__boxed_1070_; lean_object* v_res_1071_; 
v_x_8973__boxed_1069_ = lean_unbox_usize(v_x_1065_);
lean_dec(v_x_1065_);
v_x_8974__boxed_1070_ = lean_unbox_usize(v_x_1066_);
lean_dec(v_x_1066_);
v_res_1071_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2(v_00_u03b2_1063_, v_x_1064_, v_x_8973__boxed_1069_, v_x_8974__boxed_1070_, v_x_1067_, v_x_1068_);
return v_res_1071_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__8(lean_object* v_00_u03b2_1072_, lean_object* v_n_1073_, lean_object* v_k_1074_, lean_object* v_v_1075_){
_start:
{
lean_object* v___x_1076_; 
v___x_1076_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__8___redArg(v_n_1073_, v_k_1074_, v_v_1075_);
return v___x_1076_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__9(lean_object* v_00_u03b2_1077_, size_t v_depth_1078_, lean_object* v_keys_1079_, lean_object* v_vals_1080_, lean_object* v_heq_1081_, lean_object* v_i_1082_, lean_object* v_entries_1083_){
_start:
{
lean_object* v___x_1084_; 
v___x_1084_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__9___redArg(v_depth_1078_, v_keys_1079_, v_vals_1080_, v_i_1082_, v_entries_1083_);
return v___x_1084_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__9___boxed(lean_object* v_00_u03b2_1085_, lean_object* v_depth_1086_, lean_object* v_keys_1087_, lean_object* v_vals_1088_, lean_object* v_heq_1089_, lean_object* v_i_1090_, lean_object* v_entries_1091_){
_start:
{
size_t v_depth_boxed_1092_; lean_object* v_res_1093_; 
v_depth_boxed_1092_ = lean_unbox_usize(v_depth_1086_);
lean_dec(v_depth_1086_);
v_res_1093_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__9(v_00_u03b2_1085_, v_depth_boxed_1092_, v_keys_1087_, v_vals_1088_, v_heq_1089_, v_i_1090_, v_entries_1091_);
lean_dec_ref(v_vals_1088_);
lean_dec_ref(v_keys_1087_);
return v_res_1093_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__8_spec__9(lean_object* v_00_u03b2_1094_, lean_object* v_x_1095_, lean_object* v_x_1096_, lean_object* v_x_1097_, lean_object* v_x_1098_){
_start:
{
lean_object* v___x_1099_; 
v___x_1099_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__8_spec__9___redArg(v_x_1095_, v_x_1096_, v_x_1097_, v_x_1098_);
return v___x_1099_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize(lean_object* v_mvarId_1102_, lean_object* v_givenNames_1103_, lean_object* v_recursorInfo_1104_, lean_object* v_reverted_1105_, lean_object* v_major_1106_, lean_object* v_indices_1107_, lean_object* v_baseSubst_1108_, lean_object* v_recursor_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_, lean_object* v_a_1112_, lean_object* v_a_1113_){
_start:
{
lean_object* v___x_1115_; 
lean_inc(v_mvarId_1102_);
v___x_1115_ = l_Lean_MVarId_getType(v_mvarId_1102_, v_a_1110_, v_a_1111_, v_a_1112_, v_a_1113_);
if (lean_obj_tag(v___x_1115_) == 0)
{
lean_object* v_a_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; 
v_a_1116_ = lean_ctor_get(v___x_1115_, 0);
lean_inc(v_a_1116_);
lean_dec_ref_known(v___x_1115_, 1);
v___x_1117_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTargetArity(v_a_1116_);
lean_inc(v_a_1113_);
lean_inc_ref(v_a_1112_);
lean_inc(v_a_1111_);
lean_inc_ref(v_a_1110_);
lean_inc_ref(v_recursor_1109_);
v___x_1118_ = lean_infer_type(v_recursor_1109_, v_a_1110_, v_a_1111_, v_a_1112_, v_a_1113_);
if (lean_obj_tag(v___x_1118_) == 0)
{
lean_object* v_a_1119_; lean_object* v_paramsPos_1120_; lean_object* v_produceMotive_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; uint8_t v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; 
v_a_1119_ = lean_ctor_get(v___x_1118_, 0);
lean_inc(v_a_1119_);
lean_dec_ref_known(v___x_1118_, 1);
v_paramsPos_1120_ = lean_ctor_get(v_recursorInfo_1104_, 5);
v_produceMotive_1121_ = lean_ctor_get(v_recursorInfo_1104_, 7);
v___x_1122_ = l_List_lengthTR___redArg(v_produceMotive_1121_);
v___x_1123_ = l_List_lengthTR___redArg(v_paramsPos_1120_);
v___x_1124_ = lean_unsigned_to_nat(1u);
v___x_1125_ = lean_nat_add(v___x_1123_, v___x_1124_);
lean_dec(v___x_1123_);
v___x_1126_ = lean_unsigned_to_nat(0u);
v___x_1127_ = 0;
v___x_1128_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize___closed__0));
v___x_1129_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop(v_mvarId_1102_, v_givenNames_1103_, v_recursorInfo_1104_, v_reverted_1105_, v_major_1106_, v_indices_1107_, v_baseSubst_1108_, v___x_1117_, v___x_1122_, v___x_1125_, v___x_1126_, v_recursor_1109_, v_a_1119_, v___x_1127_, v___x_1128_, v_a_1110_, v_a_1111_, v_a_1112_, v_a_1113_);
lean_dec(v___x_1122_);
lean_dec(v___x_1117_);
return v___x_1129_;
}
else
{
lean_object* v_a_1130_; lean_object* v___x_1132_; uint8_t v_isShared_1133_; uint8_t v_isSharedCheck_1137_; 
lean_dec(v___x_1117_);
lean_dec_ref(v_recursor_1109_);
lean_dec(v_baseSubst_1108_);
lean_dec_ref(v_major_1106_);
lean_dec(v_mvarId_1102_);
v_a_1130_ = lean_ctor_get(v___x_1118_, 0);
v_isSharedCheck_1137_ = !lean_is_exclusive(v___x_1118_);
if (v_isSharedCheck_1137_ == 0)
{
v___x_1132_ = v___x_1118_;
v_isShared_1133_ = v_isSharedCheck_1137_;
goto v_resetjp_1131_;
}
else
{
lean_inc(v_a_1130_);
lean_dec(v___x_1118_);
v___x_1132_ = lean_box(0);
v_isShared_1133_ = v_isSharedCheck_1137_;
goto v_resetjp_1131_;
}
v_resetjp_1131_:
{
lean_object* v___x_1135_; 
if (v_isShared_1133_ == 0)
{
v___x_1135_ = v___x_1132_;
goto v_reusejp_1134_;
}
else
{
lean_object* v_reuseFailAlloc_1136_; 
v_reuseFailAlloc_1136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1136_, 0, v_a_1130_);
v___x_1135_ = v_reuseFailAlloc_1136_;
goto v_reusejp_1134_;
}
v_reusejp_1134_:
{
return v___x_1135_;
}
}
}
}
else
{
lean_object* v_a_1138_; lean_object* v___x_1140_; uint8_t v_isShared_1141_; uint8_t v_isSharedCheck_1145_; 
lean_dec_ref(v_recursor_1109_);
lean_dec(v_baseSubst_1108_);
lean_dec_ref(v_major_1106_);
lean_dec(v_mvarId_1102_);
v_a_1138_ = lean_ctor_get(v___x_1115_, 0);
v_isSharedCheck_1145_ = !lean_is_exclusive(v___x_1115_);
if (v_isSharedCheck_1145_ == 0)
{
v___x_1140_ = v___x_1115_;
v_isShared_1141_ = v_isSharedCheck_1145_;
goto v_resetjp_1139_;
}
else
{
lean_inc(v_a_1138_);
lean_dec(v___x_1115_);
v___x_1140_ = lean_box(0);
v_isShared_1141_ = v_isSharedCheck_1145_;
goto v_resetjp_1139_;
}
v_resetjp_1139_:
{
lean_object* v___x_1143_; 
if (v_isShared_1141_ == 0)
{
v___x_1143_ = v___x_1140_;
goto v_reusejp_1142_;
}
else
{
lean_object* v_reuseFailAlloc_1144_; 
v_reuseFailAlloc_1144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1144_, 0, v_a_1138_);
v___x_1143_ = v_reuseFailAlloc_1144_;
goto v_reusejp_1142_;
}
v_reusejp_1142_:
{
return v___x_1143_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize___boxed(lean_object* v_mvarId_1146_, lean_object* v_givenNames_1147_, lean_object* v_recursorInfo_1148_, lean_object* v_reverted_1149_, lean_object* v_major_1150_, lean_object* v_indices_1151_, lean_object* v_baseSubst_1152_, lean_object* v_recursor_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_, lean_object* v_a_1157_, lean_object* v_a_1158_){
_start:
{
lean_object* v_res_1159_; 
v_res_1159_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize(v_mvarId_1146_, v_givenNames_1147_, v_recursorInfo_1148_, v_reverted_1149_, v_major_1150_, v_indices_1151_, v_baseSubst_1152_, v_recursor_1153_, v_a_1154_, v_a_1155_, v_a_1156_, v_a_1157_);
lean_dec(v_a_1157_);
lean_dec_ref(v_a_1156_);
lean_dec(v_a_1155_);
lean_dec_ref(v_a_1154_);
lean_dec_ref(v_indices_1151_);
lean_dec_ref(v_reverted_1149_);
lean_dec_ref(v_recursorInfo_1148_);
lean_dec_ref(v_givenNames_1147_);
return v_res_1159_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg___closed__1(void){
_start:
{
lean_object* v___x_1161_; lean_object* v___x_1162_; 
v___x_1161_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg___closed__0));
v___x_1162_ = l_Lean_stringToMessageData(v___x_1161_);
return v___x_1162_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg(lean_object* v_tacticName_1163_, lean_object* v_mvarId_1164_, lean_object* v_majorType_1165_, lean_object* v_a_1166_, lean_object* v_a_1167_, lean_object* v_a_1168_, lean_object* v_a_1169_){
_start:
{
lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; 
v___x_1171_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg___closed__1, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg___closed__1);
v___x_1172_ = l_Lean_indentExpr(v_majorType_1165_);
v___x_1173_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1173_, 0, v___x_1171_);
lean_ctor_set(v___x_1173_, 1, v___x_1172_);
v___x_1174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1174_, 0, v___x_1173_);
v___x_1175_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1163_, v_mvarId_1164_, v___x_1174_, v_a_1166_, v_a_1167_, v_a_1168_, v_a_1169_);
return v___x_1175_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg___boxed(lean_object* v_tacticName_1176_, lean_object* v_mvarId_1177_, lean_object* v_majorType_1178_, lean_object* v_a_1179_, lean_object* v_a_1180_, lean_object* v_a_1181_, lean_object* v_a_1182_, lean_object* v_a_1183_){
_start:
{
lean_object* v_res_1184_; 
v_res_1184_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg(v_tacticName_1176_, v_mvarId_1177_, v_majorType_1178_, v_a_1179_, v_a_1180_, v_a_1181_, v_a_1182_);
lean_dec(v_a_1182_);
lean_dec_ref(v_a_1181_);
lean_dec(v_a_1180_);
lean_dec_ref(v_a_1179_);
return v_res_1184_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType(lean_object* v_00_u03b1_1185_, lean_object* v_tacticName_1186_, lean_object* v_mvarId_1187_, lean_object* v_majorType_1188_, lean_object* v_a_1189_, lean_object* v_a_1190_, lean_object* v_a_1191_, lean_object* v_a_1192_){
_start:
{
lean_object* v___x_1194_; 
v___x_1194_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg(v_tacticName_1186_, v_mvarId_1187_, v_majorType_1188_, v_a_1189_, v_a_1190_, v_a_1191_, v_a_1192_);
return v___x_1194_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___boxed(lean_object* v_00_u03b1_1195_, lean_object* v_tacticName_1196_, lean_object* v_mvarId_1197_, lean_object* v_majorType_1198_, lean_object* v_a_1199_, lean_object* v_a_1200_, lean_object* v_a_1201_, lean_object* v_a_1202_, lean_object* v_a_1203_){
_start:
{
lean_object* v_res_1204_; 
v_res_1204_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType(v_00_u03b1_1195_, v_tacticName_1196_, v_mvarId_1197_, v_majorType_1198_, v_a_1199_, v_a_1200_, v_a_1201_, v_a_1202_);
lean_dec(v_a_1202_);
lean_dec_ref(v_a_1201_);
lean_dec(v_a_1200_);
lean_dec_ref(v_a_1199_);
return v_res_1204_;
}
}
LEAN_EXPORT uint8_t l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___lam__0(lean_object* v_fvarId_1205_, lean_object* v_x_1206_){
_start:
{
uint8_t v___x_1207_; 
v___x_1207_ = l_Lean_instBEqFVarId_beq(v_fvarId_1205_, v_x_1206_);
return v___x_1207_;
}
}
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___lam__0___boxed(lean_object* v_fvarId_1208_, lean_object* v_x_1209_){
_start:
{
uint8_t v_res_1210_; lean_object* v_r_1211_; 
v_res_1210_ = l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___lam__0(v_fvarId_1208_, v_x_1209_);
lean_dec(v_x_1209_);
lean_dec(v_fvarId_1208_);
v_r_1211_ = lean_box(v_res_1210_);
return v_r_1211_;
}
}
LEAN_EXPORT uint8_t l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___lam__1(lean_object* v_x_1212_){
_start:
{
uint8_t v___x_1213_; 
v___x_1213_ = 0;
return v___x_1213_;
}
}
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___lam__1___boxed(lean_object* v_x_1214_){
_start:
{
uint8_t v_res_1215_; lean_object* v_r_1216_; 
v_res_1215_ = l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___lam__1(v_x_1214_);
lean_dec(v_x_1214_);
v_r_1216_ = lean_box(v_res_1215_);
return v_r_1216_;
}
}
static lean_object* _init_l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; 
v___x_1218_ = lean_box(0);
v___x_1219_ = lean_unsigned_to_nat(16u);
v___x_1220_ = lean_mk_array(v___x_1219_, v___x_1218_);
return v___x_1220_;
}
}
static lean_object* _init_l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; 
v___x_1221_ = lean_obj_once(&l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__1, &l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__1_once, _init_l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__1);
v___x_1222_ = lean_unsigned_to_nat(0u);
v___x_1223_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1223_, 0, v___x_1222_);
lean_ctor_set(v___x_1223_, 1, v___x_1221_);
return v___x_1223_;
}
}
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg(lean_object* v_localDecl_1224_, lean_object* v_fvarId_1225_, uint8_t v_generalizeNondepLet_1226_, lean_object* v___y_1227_){
_start:
{
uint8_t v_fst_1230_; lean_object* v_snd_1231_; lean_object* v___y_1250_; lean_object* v___f_1254_; lean_object* v___f_1255_; 
v___f_1254_ = lean_alloc_closure((void*)(l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1254_, 0, v_fvarId_1225_);
v___f_1255_ = ((lean_object*)(l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__0));
if (lean_obj_tag(v_localDecl_1224_) == 0)
{
lean_object* v_type_1256_; lean_object* v___x_1257_; uint8_t v_fst_1259_; lean_object* v_mctx_1260_; lean_object* v___y_1278_; lean_object* v_mctx_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; uint8_t v___x_1286_; 
v_type_1256_ = lean_ctor_get(v_localDecl_1224_, 3);
lean_inc_ref(v_type_1256_);
lean_dec_ref_known(v_localDecl_1224_, 4);
v___x_1257_ = lean_st_ref_get(v___y_1227_);
v_mctx_1283_ = lean_ctor_get(v___x_1257_, 0);
lean_inc_ref_n(v_mctx_1283_, 2);
lean_dec(v___x_1257_);
v___x_1284_ = lean_obj_once(&l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__2, &l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__2_once, _init_l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__2);
v___x_1285_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1285_, 0, v___x_1284_);
lean_ctor_set(v___x_1285_, 1, v_mctx_1283_);
v___x_1286_ = l_Lean_Expr_hasFVar(v_type_1256_);
if (v___x_1286_ == 0)
{
uint8_t v___x_1287_; 
v___x_1287_ = l_Lean_Expr_hasMVar(v_type_1256_);
if (v___x_1287_ == 0)
{
lean_dec_ref_known(v___x_1285_, 2);
lean_dec_ref(v_type_1256_);
lean_dec_ref(v___f_1254_);
v_fst_1259_ = v___x_1287_;
v_mctx_1260_ = v_mctx_1283_;
goto v___jp_1258_;
}
else
{
lean_object* v___x_1288_; 
lean_dec_ref(v_mctx_1283_);
v___x_1288_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1254_, v___f_1255_, v_type_1256_, v___x_1285_);
v___y_1278_ = v___x_1288_;
goto v___jp_1277_;
}
}
else
{
lean_object* v___x_1289_; 
lean_dec_ref(v_mctx_1283_);
v___x_1289_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1254_, v___f_1255_, v_type_1256_, v___x_1285_);
v___y_1278_ = v___x_1289_;
goto v___jp_1277_;
}
v___jp_1258_:
{
lean_object* v___x_1261_; lean_object* v_cache_1262_; lean_object* v_zetaDeltaFVarIds_1263_; lean_object* v_postponed_1264_; lean_object* v_diag_1265_; lean_object* v___x_1267_; uint8_t v_isShared_1268_; uint8_t v_isSharedCheck_1275_; 
v___x_1261_ = lean_st_ref_take(v___y_1227_);
v_cache_1262_ = lean_ctor_get(v___x_1261_, 1);
v_zetaDeltaFVarIds_1263_ = lean_ctor_get(v___x_1261_, 2);
v_postponed_1264_ = lean_ctor_get(v___x_1261_, 3);
v_diag_1265_ = lean_ctor_get(v___x_1261_, 4);
v_isSharedCheck_1275_ = !lean_is_exclusive(v___x_1261_);
if (v_isSharedCheck_1275_ == 0)
{
lean_object* v_unused_1276_; 
v_unused_1276_ = lean_ctor_get(v___x_1261_, 0);
lean_dec(v_unused_1276_);
v___x_1267_ = v___x_1261_;
v_isShared_1268_ = v_isSharedCheck_1275_;
goto v_resetjp_1266_;
}
else
{
lean_inc(v_diag_1265_);
lean_inc(v_postponed_1264_);
lean_inc(v_zetaDeltaFVarIds_1263_);
lean_inc(v_cache_1262_);
lean_dec(v___x_1261_);
v___x_1267_ = lean_box(0);
v_isShared_1268_ = v_isSharedCheck_1275_;
goto v_resetjp_1266_;
}
v_resetjp_1266_:
{
lean_object* v___x_1270_; 
if (v_isShared_1268_ == 0)
{
lean_ctor_set(v___x_1267_, 0, v_mctx_1260_);
v___x_1270_ = v___x_1267_;
goto v_reusejp_1269_;
}
else
{
lean_object* v_reuseFailAlloc_1274_; 
v_reuseFailAlloc_1274_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1274_, 0, v_mctx_1260_);
lean_ctor_set(v_reuseFailAlloc_1274_, 1, v_cache_1262_);
lean_ctor_set(v_reuseFailAlloc_1274_, 2, v_zetaDeltaFVarIds_1263_);
lean_ctor_set(v_reuseFailAlloc_1274_, 3, v_postponed_1264_);
lean_ctor_set(v_reuseFailAlloc_1274_, 4, v_diag_1265_);
v___x_1270_ = v_reuseFailAlloc_1274_;
goto v_reusejp_1269_;
}
v_reusejp_1269_:
{
lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; 
v___x_1271_ = lean_st_ref_put(v___y_1227_, v___x_1270_);
v___x_1272_ = lean_box(v_fst_1259_);
v___x_1273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1273_, 0, v___x_1272_);
return v___x_1273_;
}
}
}
v___jp_1277_:
{
lean_object* v_snd_1279_; lean_object* v_fst_1280_; lean_object* v_mctx_1281_; uint8_t v___x_1282_; 
v_snd_1279_ = lean_ctor_get(v___y_1278_, 1);
lean_inc(v_snd_1279_);
v_fst_1280_ = lean_ctor_get(v___y_1278_, 0);
lean_inc(v_fst_1280_);
lean_dec_ref(v___y_1278_);
v_mctx_1281_ = lean_ctor_get(v_snd_1279_, 1);
lean_inc_ref(v_mctx_1281_);
lean_dec(v_snd_1279_);
v___x_1282_ = lean_unbox(v_fst_1280_);
lean_dec(v_fst_1280_);
v_fst_1259_ = v___x_1282_;
v_mctx_1260_ = v_mctx_1281_;
goto v___jp_1258_;
}
}
else
{
lean_object* v_type_1290_; lean_object* v_value_1291_; uint8_t v_nondep_1292_; uint8_t v_fst_1294_; lean_object* v_snd_1295_; lean_object* v___y_1301_; 
v_type_1290_ = lean_ctor_get(v_localDecl_1224_, 3);
lean_inc_ref(v_type_1290_);
v_value_1291_ = lean_ctor_get(v_localDecl_1224_, 4);
lean_inc_ref(v_value_1291_);
v_nondep_1292_ = lean_ctor_get_uint8(v_localDecl_1224_, sizeof(void*)*5);
lean_dec_ref_known(v_localDecl_1224_, 5);
if (v_generalizeNondepLet_1226_ == 0)
{
goto v___jp_1305_;
}
else
{
if (v_nondep_1292_ == 0)
{
goto v___jp_1305_;
}
else
{
lean_object* v___x_1314_; uint8_t v_fst_1316_; lean_object* v_mctx_1317_; lean_object* v___y_1335_; lean_object* v_mctx_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; uint8_t v___x_1343_; 
lean_dec_ref(v_value_1291_);
v___x_1314_ = lean_st_ref_get(v___y_1227_);
v_mctx_1340_ = lean_ctor_get(v___x_1314_, 0);
lean_inc_ref_n(v_mctx_1340_, 2);
lean_dec(v___x_1314_);
v___x_1341_ = lean_obj_once(&l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__2, &l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__2_once, _init_l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__2);
v___x_1342_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1342_, 0, v___x_1341_);
lean_ctor_set(v___x_1342_, 1, v_mctx_1340_);
v___x_1343_ = l_Lean_Expr_hasFVar(v_type_1290_);
if (v___x_1343_ == 0)
{
uint8_t v___x_1344_; 
v___x_1344_ = l_Lean_Expr_hasMVar(v_type_1290_);
if (v___x_1344_ == 0)
{
lean_dec_ref_known(v___x_1342_, 2);
lean_dec_ref(v_type_1290_);
lean_dec_ref(v___f_1254_);
v_fst_1316_ = v___x_1344_;
v_mctx_1317_ = v_mctx_1340_;
goto v___jp_1315_;
}
else
{
lean_object* v___x_1345_; 
lean_dec_ref(v_mctx_1340_);
v___x_1345_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1254_, v___f_1255_, v_type_1290_, v___x_1342_);
v___y_1335_ = v___x_1345_;
goto v___jp_1334_;
}
}
else
{
lean_object* v___x_1346_; 
lean_dec_ref(v_mctx_1340_);
v___x_1346_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1254_, v___f_1255_, v_type_1290_, v___x_1342_);
v___y_1335_ = v___x_1346_;
goto v___jp_1334_;
}
v___jp_1315_:
{
lean_object* v___x_1318_; lean_object* v_cache_1319_; lean_object* v_zetaDeltaFVarIds_1320_; lean_object* v_postponed_1321_; lean_object* v_diag_1322_; lean_object* v___x_1324_; uint8_t v_isShared_1325_; uint8_t v_isSharedCheck_1332_; 
v___x_1318_ = lean_st_ref_take(v___y_1227_);
v_cache_1319_ = lean_ctor_get(v___x_1318_, 1);
v_zetaDeltaFVarIds_1320_ = lean_ctor_get(v___x_1318_, 2);
v_postponed_1321_ = lean_ctor_get(v___x_1318_, 3);
v_diag_1322_ = lean_ctor_get(v___x_1318_, 4);
v_isSharedCheck_1332_ = !lean_is_exclusive(v___x_1318_);
if (v_isSharedCheck_1332_ == 0)
{
lean_object* v_unused_1333_; 
v_unused_1333_ = lean_ctor_get(v___x_1318_, 0);
lean_dec(v_unused_1333_);
v___x_1324_ = v___x_1318_;
v_isShared_1325_ = v_isSharedCheck_1332_;
goto v_resetjp_1323_;
}
else
{
lean_inc(v_diag_1322_);
lean_inc(v_postponed_1321_);
lean_inc(v_zetaDeltaFVarIds_1320_);
lean_inc(v_cache_1319_);
lean_dec(v___x_1318_);
v___x_1324_ = lean_box(0);
v_isShared_1325_ = v_isSharedCheck_1332_;
goto v_resetjp_1323_;
}
v_resetjp_1323_:
{
lean_object* v___x_1327_; 
if (v_isShared_1325_ == 0)
{
lean_ctor_set(v___x_1324_, 0, v_mctx_1317_);
v___x_1327_ = v___x_1324_;
goto v_reusejp_1326_;
}
else
{
lean_object* v_reuseFailAlloc_1331_; 
v_reuseFailAlloc_1331_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1331_, 0, v_mctx_1317_);
lean_ctor_set(v_reuseFailAlloc_1331_, 1, v_cache_1319_);
lean_ctor_set(v_reuseFailAlloc_1331_, 2, v_zetaDeltaFVarIds_1320_);
lean_ctor_set(v_reuseFailAlloc_1331_, 3, v_postponed_1321_);
lean_ctor_set(v_reuseFailAlloc_1331_, 4, v_diag_1322_);
v___x_1327_ = v_reuseFailAlloc_1331_;
goto v_reusejp_1326_;
}
v_reusejp_1326_:
{
lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; 
v___x_1328_ = lean_st_ref_put(v___y_1227_, v___x_1327_);
v___x_1329_ = lean_box(v_fst_1316_);
v___x_1330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1330_, 0, v___x_1329_);
return v___x_1330_;
}
}
}
v___jp_1334_:
{
lean_object* v_snd_1336_; lean_object* v_fst_1337_; lean_object* v_mctx_1338_; uint8_t v___x_1339_; 
v_snd_1336_ = lean_ctor_get(v___y_1335_, 1);
lean_inc(v_snd_1336_);
v_fst_1337_ = lean_ctor_get(v___y_1335_, 0);
lean_inc(v_fst_1337_);
lean_dec_ref(v___y_1335_);
v_mctx_1338_ = lean_ctor_get(v_snd_1336_, 1);
lean_inc_ref(v_mctx_1338_);
lean_dec(v_snd_1336_);
v___x_1339_ = lean_unbox(v_fst_1337_);
lean_dec(v_fst_1337_);
v_fst_1316_ = v___x_1339_;
v_mctx_1317_ = v_mctx_1338_;
goto v___jp_1315_;
}
}
}
v___jp_1293_:
{
if (v_fst_1294_ == 0)
{
uint8_t v___x_1296_; 
v___x_1296_ = l_Lean_Expr_hasFVar(v_value_1291_);
if (v___x_1296_ == 0)
{
uint8_t v___x_1297_; 
v___x_1297_ = l_Lean_Expr_hasMVar(v_value_1291_);
if (v___x_1297_ == 0)
{
lean_dec_ref(v_value_1291_);
lean_dec_ref(v___f_1254_);
v_fst_1230_ = v___x_1297_;
v_snd_1231_ = v_snd_1295_;
goto v___jp_1229_;
}
else
{
lean_object* v___x_1298_; 
v___x_1298_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1254_, v___f_1255_, v_value_1291_, v_snd_1295_);
v___y_1250_ = v___x_1298_;
goto v___jp_1249_;
}
}
else
{
lean_object* v___x_1299_; 
v___x_1299_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1254_, v___f_1255_, v_value_1291_, v_snd_1295_);
v___y_1250_ = v___x_1299_;
goto v___jp_1249_;
}
}
else
{
lean_dec_ref(v_value_1291_);
lean_dec_ref(v___f_1254_);
v_fst_1230_ = v_fst_1294_;
v_snd_1231_ = v_snd_1295_;
goto v___jp_1229_;
}
}
v___jp_1300_:
{
lean_object* v_fst_1302_; lean_object* v_snd_1303_; uint8_t v___x_1304_; 
v_fst_1302_ = lean_ctor_get(v___y_1301_, 0);
lean_inc(v_fst_1302_);
v_snd_1303_ = lean_ctor_get(v___y_1301_, 1);
lean_inc(v_snd_1303_);
lean_dec_ref(v___y_1301_);
v___x_1304_ = lean_unbox(v_fst_1302_);
lean_dec(v_fst_1302_);
v_fst_1294_ = v___x_1304_;
v_snd_1295_ = v_snd_1303_;
goto v___jp_1293_;
}
v___jp_1305_:
{
lean_object* v___x_1306_; lean_object* v_mctx_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; uint8_t v___x_1310_; 
v___x_1306_ = lean_st_ref_get(v___y_1227_);
v_mctx_1307_ = lean_ctor_get(v___x_1306_, 0);
lean_inc_ref(v_mctx_1307_);
lean_dec(v___x_1306_);
v___x_1308_ = lean_obj_once(&l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__2, &l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__2_once, _init_l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__2);
v___x_1309_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1309_, 0, v___x_1308_);
lean_ctor_set(v___x_1309_, 1, v_mctx_1307_);
v___x_1310_ = l_Lean_Expr_hasFVar(v_type_1290_);
if (v___x_1310_ == 0)
{
uint8_t v___x_1311_; 
v___x_1311_ = l_Lean_Expr_hasMVar(v_type_1290_);
if (v___x_1311_ == 0)
{
lean_dec_ref(v_type_1290_);
v_fst_1294_ = v___x_1311_;
v_snd_1295_ = v___x_1309_;
goto v___jp_1293_;
}
else
{
lean_object* v___x_1312_; 
lean_inc_ref(v___f_1254_);
v___x_1312_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1254_, v___f_1255_, v_type_1290_, v___x_1309_);
v___y_1301_ = v___x_1312_;
goto v___jp_1300_;
}
}
else
{
lean_object* v___x_1313_; 
lean_inc_ref(v___f_1254_);
v___x_1313_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1254_, v___f_1255_, v_type_1290_, v___x_1309_);
v___y_1301_ = v___x_1313_;
goto v___jp_1300_;
}
}
}
v___jp_1229_:
{
lean_object* v_mctx_1232_; lean_object* v___x_1233_; lean_object* v_cache_1234_; lean_object* v_zetaDeltaFVarIds_1235_; lean_object* v_postponed_1236_; lean_object* v_diag_1237_; lean_object* v___x_1239_; uint8_t v_isShared_1240_; uint8_t v_isSharedCheck_1247_; 
v_mctx_1232_ = lean_ctor_get(v_snd_1231_, 1);
lean_inc_ref(v_mctx_1232_);
lean_dec_ref(v_snd_1231_);
v___x_1233_ = lean_st_ref_take(v___y_1227_);
v_cache_1234_ = lean_ctor_get(v___x_1233_, 1);
v_zetaDeltaFVarIds_1235_ = lean_ctor_get(v___x_1233_, 2);
v_postponed_1236_ = lean_ctor_get(v___x_1233_, 3);
v_diag_1237_ = lean_ctor_get(v___x_1233_, 4);
v_isSharedCheck_1247_ = !lean_is_exclusive(v___x_1233_);
if (v_isSharedCheck_1247_ == 0)
{
lean_object* v_unused_1248_; 
v_unused_1248_ = lean_ctor_get(v___x_1233_, 0);
lean_dec(v_unused_1248_);
v___x_1239_ = v___x_1233_;
v_isShared_1240_ = v_isSharedCheck_1247_;
goto v_resetjp_1238_;
}
else
{
lean_inc(v_diag_1237_);
lean_inc(v_postponed_1236_);
lean_inc(v_zetaDeltaFVarIds_1235_);
lean_inc(v_cache_1234_);
lean_dec(v___x_1233_);
v___x_1239_ = lean_box(0);
v_isShared_1240_ = v_isSharedCheck_1247_;
goto v_resetjp_1238_;
}
v_resetjp_1238_:
{
lean_object* v___x_1242_; 
if (v_isShared_1240_ == 0)
{
lean_ctor_set(v___x_1239_, 0, v_mctx_1232_);
v___x_1242_ = v___x_1239_;
goto v_reusejp_1241_;
}
else
{
lean_object* v_reuseFailAlloc_1246_; 
v_reuseFailAlloc_1246_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1246_, 0, v_mctx_1232_);
lean_ctor_set(v_reuseFailAlloc_1246_, 1, v_cache_1234_);
lean_ctor_set(v_reuseFailAlloc_1246_, 2, v_zetaDeltaFVarIds_1235_);
lean_ctor_set(v_reuseFailAlloc_1246_, 3, v_postponed_1236_);
lean_ctor_set(v_reuseFailAlloc_1246_, 4, v_diag_1237_);
v___x_1242_ = v_reuseFailAlloc_1246_;
goto v_reusejp_1241_;
}
v_reusejp_1241_:
{
lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; 
v___x_1243_ = lean_st_ref_put(v___y_1227_, v___x_1242_);
v___x_1244_ = lean_box(v_fst_1230_);
v___x_1245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1245_, 0, v___x_1244_);
return v___x_1245_;
}
}
}
v___jp_1249_:
{
lean_object* v_fst_1251_; lean_object* v_snd_1252_; uint8_t v___x_1253_; 
v_fst_1251_ = lean_ctor_get(v___y_1250_, 0);
lean_inc(v_fst_1251_);
v_snd_1252_ = lean_ctor_get(v___y_1250_, 1);
lean_inc(v_snd_1252_);
lean_dec_ref(v___y_1250_);
v___x_1253_ = lean_unbox(v_fst_1251_);
lean_dec(v_fst_1251_);
v_fst_1230_ = v___x_1253_;
v_snd_1231_ = v_snd_1252_;
goto v___jp_1229_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___boxed(lean_object* v_localDecl_1347_, lean_object* v_fvarId_1348_, lean_object* v_generalizeNondepLet_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_){
_start:
{
uint8_t v_generalizeNondepLet_boxed_1352_; lean_object* v_res_1353_; 
v_generalizeNondepLet_boxed_1352_ = lean_unbox(v_generalizeNondepLet_1349_);
v_res_1353_ = l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg(v_localDecl_1347_, v_fvarId_1348_, v_generalizeNondepLet_boxed_1352_, v___y_1350_);
lean_dec(v___y_1350_);
return v_res_1353_;
}
}
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1(lean_object* v_localDecl_1354_, lean_object* v_fvarId_1355_, uint8_t v_generalizeNondepLet_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_){
_start:
{
lean_object* v___x_1362_; 
v___x_1362_ = l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg(v_localDecl_1354_, v_fvarId_1355_, v_generalizeNondepLet_1356_, v___y_1358_);
return v___x_1362_;
}
}
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___boxed(lean_object* v_localDecl_1363_, lean_object* v_fvarId_1364_, lean_object* v_generalizeNondepLet_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_){
_start:
{
uint8_t v_generalizeNondepLet_boxed_1371_; lean_object* v_res_1372_; 
v_generalizeNondepLet_boxed_1371_ = lean_unbox(v_generalizeNondepLet_1365_);
v_res_1372_ = l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1(v_localDecl_1363_, v_fvarId_1364_, v_generalizeNondepLet_boxed_1371_, v___y_1366_, v___y_1367_, v___y_1368_, v___y_1369_);
lean_dec(v___y_1369_);
lean_dec_ref(v___y_1368_);
lean_dec(v___y_1367_);
lean_dec_ref(v___y_1366_);
return v_res_1372_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2___redArg(lean_object* v_e_1373_, lean_object* v_fvarId_1374_, lean_object* v___y_1375_){
_start:
{
lean_object* v___f_1377_; lean_object* v___f_1378_; lean_object* v___x_1379_; uint8_t v_fst_1381_; lean_object* v_mctx_1382_; lean_object* v___y_1400_; lean_object* v_mctx_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; uint8_t v___x_1408_; 
v___f_1377_ = ((lean_object*)(l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__0));
v___f_1378_ = lean_alloc_closure((void*)(l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1378_, 0, v_fvarId_1374_);
v___x_1379_ = lean_st_ref_get(v___y_1375_);
v_mctx_1405_ = lean_ctor_get(v___x_1379_, 0);
lean_inc_ref_n(v_mctx_1405_, 2);
lean_dec(v___x_1379_);
v___x_1406_ = lean_obj_once(&l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__2, &l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__2_once, _init_l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__2);
v___x_1407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1407_, 0, v___x_1406_);
lean_ctor_set(v___x_1407_, 1, v_mctx_1405_);
v___x_1408_ = l_Lean_Expr_hasFVar(v_e_1373_);
if (v___x_1408_ == 0)
{
uint8_t v___x_1409_; 
v___x_1409_ = l_Lean_Expr_hasMVar(v_e_1373_);
if (v___x_1409_ == 0)
{
lean_dec_ref_known(v___x_1407_, 2);
lean_dec_ref(v___f_1378_);
lean_dec_ref(v_e_1373_);
v_fst_1381_ = v___x_1409_;
v_mctx_1382_ = v_mctx_1405_;
goto v___jp_1380_;
}
else
{
lean_object* v___x_1410_; 
lean_dec_ref(v_mctx_1405_);
v___x_1410_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1378_, v___f_1377_, v_e_1373_, v___x_1407_);
v___y_1400_ = v___x_1410_;
goto v___jp_1399_;
}
}
else
{
lean_object* v___x_1411_; 
lean_dec_ref(v_mctx_1405_);
v___x_1411_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1378_, v___f_1377_, v_e_1373_, v___x_1407_);
v___y_1400_ = v___x_1411_;
goto v___jp_1399_;
}
v___jp_1380_:
{
lean_object* v___x_1383_; lean_object* v_cache_1384_; lean_object* v_zetaDeltaFVarIds_1385_; lean_object* v_postponed_1386_; lean_object* v_diag_1387_; lean_object* v___x_1389_; uint8_t v_isShared_1390_; uint8_t v_isSharedCheck_1397_; 
v___x_1383_ = lean_st_ref_take(v___y_1375_);
v_cache_1384_ = lean_ctor_get(v___x_1383_, 1);
v_zetaDeltaFVarIds_1385_ = lean_ctor_get(v___x_1383_, 2);
v_postponed_1386_ = lean_ctor_get(v___x_1383_, 3);
v_diag_1387_ = lean_ctor_get(v___x_1383_, 4);
v_isSharedCheck_1397_ = !lean_is_exclusive(v___x_1383_);
if (v_isSharedCheck_1397_ == 0)
{
lean_object* v_unused_1398_; 
v_unused_1398_ = lean_ctor_get(v___x_1383_, 0);
lean_dec(v_unused_1398_);
v___x_1389_ = v___x_1383_;
v_isShared_1390_ = v_isSharedCheck_1397_;
goto v_resetjp_1388_;
}
else
{
lean_inc(v_diag_1387_);
lean_inc(v_postponed_1386_);
lean_inc(v_zetaDeltaFVarIds_1385_);
lean_inc(v_cache_1384_);
lean_dec(v___x_1383_);
v___x_1389_ = lean_box(0);
v_isShared_1390_ = v_isSharedCheck_1397_;
goto v_resetjp_1388_;
}
v_resetjp_1388_:
{
lean_object* v___x_1392_; 
if (v_isShared_1390_ == 0)
{
lean_ctor_set(v___x_1389_, 0, v_mctx_1382_);
v___x_1392_ = v___x_1389_;
goto v_reusejp_1391_;
}
else
{
lean_object* v_reuseFailAlloc_1396_; 
v_reuseFailAlloc_1396_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1396_, 0, v_mctx_1382_);
lean_ctor_set(v_reuseFailAlloc_1396_, 1, v_cache_1384_);
lean_ctor_set(v_reuseFailAlloc_1396_, 2, v_zetaDeltaFVarIds_1385_);
lean_ctor_set(v_reuseFailAlloc_1396_, 3, v_postponed_1386_);
lean_ctor_set(v_reuseFailAlloc_1396_, 4, v_diag_1387_);
v___x_1392_ = v_reuseFailAlloc_1396_;
goto v_reusejp_1391_;
}
v_reusejp_1391_:
{
lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; 
v___x_1393_ = lean_st_ref_put(v___y_1375_, v___x_1392_);
v___x_1394_ = lean_box(v_fst_1381_);
v___x_1395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1395_, 0, v___x_1394_);
return v___x_1395_;
}
}
}
v___jp_1399_:
{
lean_object* v_snd_1401_; lean_object* v_fst_1402_; lean_object* v_mctx_1403_; uint8_t v___x_1404_; 
v_snd_1401_ = lean_ctor_get(v___y_1400_, 1);
lean_inc(v_snd_1401_);
v_fst_1402_ = lean_ctor_get(v___y_1400_, 0);
lean_inc(v_fst_1402_);
lean_dec_ref(v___y_1400_);
v_mctx_1403_ = lean_ctor_get(v_snd_1401_, 1);
lean_inc_ref(v_mctx_1403_);
lean_dec(v_snd_1401_);
v___x_1404_ = lean_unbox(v_fst_1402_);
lean_dec(v_fst_1402_);
v_fst_1381_ = v___x_1404_;
v_mctx_1382_ = v_mctx_1403_;
goto v___jp_1380_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2___redArg___boxed(lean_object* v_e_1412_, lean_object* v_fvarId_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_){
_start:
{
lean_object* v_res_1416_; 
v_res_1416_ = l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2___redArg(v_e_1412_, v_fvarId_1413_, v___y_1414_);
lean_dec(v___y_1414_);
return v_res_1416_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2(lean_object* v_e_1417_, lean_object* v_fvarId_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_){
_start:
{
lean_object* v___x_1424_; 
v___x_1424_ = l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2___redArg(v_e_1417_, v_fvarId_1418_, v___y_1420_);
return v___x_1424_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2___boxed(lean_object* v_e_1425_, lean_object* v_fvarId_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_){
_start:
{
lean_object* v_res_1432_; 
v_res_1432_ = l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2(v_e_1425_, v_fvarId_1426_, v___y_1427_, v___y_1428_, v___y_1429_, v___y_1430_);
lean_dec(v___y_1430_);
lean_dec_ref(v___y_1429_);
lean_dec(v___y_1428_);
lean_dec_ref(v___y_1427_);
return v_res_1432_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_Meta_getMajorTypeIndices_spec__0(lean_object* v_a_1433_, lean_object* v_x_1434_){
_start:
{
if (lean_obj_tag(v_x_1434_) == 0)
{
uint8_t v___x_1435_; 
v___x_1435_ = 0;
return v___x_1435_;
}
else
{
lean_object* v_head_1436_; lean_object* v_tail_1437_; uint8_t v___x_1438_; 
v_head_1436_ = lean_ctor_get(v_x_1434_, 0);
v_tail_1437_ = lean_ctor_get(v_x_1434_, 1);
v___x_1438_ = lean_nat_dec_eq(v_a_1433_, v_head_1436_);
if (v___x_1438_ == 0)
{
v_x_1434_ = v_tail_1437_;
goto _start;
}
else
{
return v___x_1438_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_Meta_getMajorTypeIndices_spec__0___boxed(lean_object* v_a_1440_, lean_object* v_x_1441_){
_start:
{
uint8_t v_res_1442_; lean_object* v_r_1443_; 
v_res_1442_ = l_List_elem___at___00Lean_Meta_getMajorTypeIndices_spec__0(v_a_1440_, v_x_1441_);
lean_dec(v_x_1441_);
lean_dec(v_a_1440_);
v_r_1443_ = lean_box(v_res_1442_);
return v_r_1443_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_1445_; lean_object* v___x_1446_; 
v___x_1445_ = ((lean_object*)(l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__0));
v___x_1446_ = l_Lean_stringToMessageData(v___x_1445_);
return v___x_1446_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_1448_; lean_object* v___x_1449_; 
v___x_1448_ = ((lean_object*)(l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__2));
v___x_1449_ = l_Lean_stringToMessageData(v___x_1448_);
return v___x_1449_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__5(void){
_start:
{
lean_object* v___x_1451_; lean_object* v___x_1452_; 
v___x_1451_ = ((lean_object*)(l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__4));
v___x_1452_ = l_Lean_stringToMessageData(v___x_1451_);
return v___x_1452_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__7(void){
_start:
{
lean_object* v___x_1454_; lean_object* v___x_1455_; 
v___x_1454_ = ((lean_object*)(l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__6));
v___x_1455_ = l_Lean_stringToMessageData(v___x_1454_);
return v___x_1455_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg(lean_object* v_majorTypeArgs_1456_, lean_object* v_idxPos_1457_, lean_object* v_recursorInfo_1458_, lean_object* v_idx_1459_, lean_object* v_tacticName_1460_, lean_object* v_mvarId_1461_, lean_object* v_majorType_1462_, lean_object* v_n_1463_, lean_object* v_i_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_){
_start:
{
lean_object* v_zero_1470_; uint8_t v_isZero_1471_; 
v_zero_1470_ = lean_unsigned_to_nat(0u);
v_isZero_1471_ = lean_nat_dec_eq(v_i_1464_, v_zero_1470_);
if (v_isZero_1471_ == 1)
{
lean_object* v___x_1472_; lean_object* v___x_1473_; 
lean_dec(v_i_1464_);
lean_dec_ref(v_majorType_1462_);
lean_dec(v_mvarId_1461_);
lean_dec(v_tacticName_1460_);
lean_dec_ref(v_idx_1459_);
v___x_1472_ = lean_box(0);
v___x_1473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1473_, 0, v___x_1472_);
return v___x_1473_;
}
else
{
lean_object* v_one_1474_; lean_object* v_n_1475_; lean_object* v___y_1477_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v_arg_1481_; uint8_t v___x_1482_; lean_object* v___y_1484_; lean_object* v___y_1485_; lean_object* v___y_1486_; lean_object* v___y_1487_; uint8_t v___x_1528_; lean_object* v___y_1530_; lean_object* v___y_1531_; lean_object* v___y_1532_; lean_object* v___y_1533_; uint8_t v___x_1553_; 
v_one_1474_ = lean_unsigned_to_nat(1u);
v_n_1475_ = lean_nat_sub(v_i_1464_, v_one_1474_);
lean_dec(v_i_1464_);
v___x_1479_ = lean_nat_sub(v_n_1463_, v_n_1475_);
v___x_1480_ = lean_nat_sub(v___x_1479_, v_one_1474_);
lean_dec(v___x_1479_);
v_arg_1481_ = lean_array_fget_borrowed(v_majorTypeArgs_1456_, v___x_1480_);
v___x_1482_ = lean_nat_dec_lt(v_idxPos_1457_, v___x_1480_);
v___x_1528_ = lean_nat_dec_lt(v___x_1480_, v_idxPos_1457_);
v___x_1553_ = lean_nat_dec_eq(v___x_1480_, v_idxPos_1457_);
if (v___x_1553_ == 0)
{
uint8_t v___x_1554_; 
v___x_1554_ = lean_expr_eqv(v_arg_1481_, v_idx_1459_);
if (v___x_1554_ == 0)
{
v___y_1530_ = v___y_1465_;
v___y_1531_ = v___y_1466_;
v___y_1532_ = v___y_1467_;
v___y_1533_ = v___y_1468_;
goto v___jp_1529_;
}
else
{
lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; 
v___x_1555_ = lean_obj_once(&l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1, &l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1_once, _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1);
lean_inc_ref(v_idx_1459_);
v___x_1556_ = l_Lean_MessageData_ofExpr(v_idx_1459_);
v___x_1557_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1557_, 0, v___x_1555_);
lean_ctor_set(v___x_1557_, 1, v___x_1556_);
v___x_1558_ = lean_obj_once(&l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__7, &l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__7_once, _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__7);
v___x_1559_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1559_, 0, v___x_1557_);
lean_ctor_set(v___x_1559_, 1, v___x_1558_);
lean_inc_ref(v_majorType_1462_);
v___x_1560_ = l_Lean_indentExpr(v_majorType_1462_);
v___x_1561_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1561_, 0, v___x_1559_);
lean_ctor_set(v___x_1561_, 1, v___x_1560_);
v___x_1562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1562_, 0, v___x_1561_);
lean_inc(v_mvarId_1461_);
lean_inc(v_tacticName_1460_);
v___x_1563_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1460_, v_mvarId_1461_, v___x_1562_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_);
if (lean_obj_tag(v___x_1563_) == 0)
{
lean_dec_ref_known(v___x_1563_, 1);
v___y_1530_ = v___y_1465_;
v___y_1531_ = v___y_1466_;
v___y_1532_ = v___y_1467_;
v___y_1533_ = v___y_1468_;
goto v___jp_1529_;
}
else
{
lean_dec(v___x_1480_);
v___y_1477_ = v___x_1563_;
goto v___jp_1476_;
}
}
}
else
{
v___y_1530_ = v___y_1465_;
v___y_1531_ = v___y_1466_;
v___y_1532_ = v___y_1467_;
v___y_1533_ = v___y_1468_;
goto v___jp_1529_;
}
v___jp_1476_:
{
if (lean_obj_tag(v___y_1477_) == 0)
{
lean_dec_ref_known(v___y_1477_, 1);
v_i_1464_ = v_n_1475_;
goto _start;
}
else
{
lean_dec(v_n_1475_);
lean_dec_ref(v_majorType_1462_);
lean_dec(v_mvarId_1461_);
lean_dec(v_tacticName_1460_);
lean_dec_ref(v_idx_1459_);
return v___y_1477_;
}
}
v___jp_1483_:
{
if (v___x_1482_ == 0)
{
lean_dec(v___x_1480_);
v_i_1464_ = v_n_1475_;
goto _start;
}
else
{
lean_object* v_indicesPos_1489_; uint8_t v___x_1490_; 
v_indicesPos_1489_ = lean_ctor_get(v_recursorInfo_1458_, 6);
v___x_1490_ = l_List_elem___at___00Lean_Meta_getMajorTypeIndices_spec__0(v___x_1480_, v_indicesPos_1489_);
if (v___x_1490_ == 0)
{
lean_dec(v___x_1480_);
v_i_1464_ = v_n_1475_;
goto _start;
}
else
{
uint8_t v___x_1492_; 
v___x_1492_ = l_Lean_Expr_isFVar(v_arg_1481_);
if (v___x_1492_ == 0)
{
lean_dec(v___x_1480_);
v_i_1464_ = v_n_1475_;
goto _start;
}
else
{
lean_object* v___x_1494_; lean_object* v___x_1495_; 
v___x_1494_ = l_Lean_Expr_fvarId_x21(v_idx_1459_);
v___x_1495_ = l_Lean_FVarId_getDecl___redArg(v___x_1494_, v___y_1484_, v___y_1486_, v___y_1487_);
if (lean_obj_tag(v___x_1495_) == 0)
{
lean_object* v_a_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v_a_1499_; lean_object* v___x_1501_; uint8_t v_isShared_1502_; uint8_t v_isSharedCheck_1519_; 
v_a_1496_ = lean_ctor_get(v___x_1495_, 0);
lean_inc(v_a_1496_);
lean_dec_ref_known(v___x_1495_, 1);
v___x_1497_ = l_Lean_Expr_fvarId_x21(v_arg_1481_);
v___x_1498_ = l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg(v_a_1496_, v___x_1497_, v___x_1490_, v___y_1485_);
v_a_1499_ = lean_ctor_get(v___x_1498_, 0);
v_isSharedCheck_1519_ = !lean_is_exclusive(v___x_1498_);
if (v_isSharedCheck_1519_ == 0)
{
v___x_1501_ = v___x_1498_;
v_isShared_1502_ = v_isSharedCheck_1519_;
goto v_resetjp_1500_;
}
else
{
lean_inc(v_a_1499_);
lean_dec(v___x_1498_);
v___x_1501_ = lean_box(0);
v_isShared_1502_ = v_isSharedCheck_1519_;
goto v_resetjp_1500_;
}
v_resetjp_1500_:
{
uint8_t v___x_1503_; 
v___x_1503_ = lean_unbox(v_a_1499_);
lean_dec(v_a_1499_);
if (v___x_1503_ == 0)
{
lean_del_object(v___x_1501_);
lean_dec(v___x_1480_);
v_i_1464_ = v_n_1475_;
goto _start;
}
else
{
lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1513_; 
v___x_1505_ = lean_obj_once(&l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1, &l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1_once, _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1);
lean_inc_ref(v_idx_1459_);
v___x_1506_ = l_Lean_MessageData_ofExpr(v_idx_1459_);
v___x_1507_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1507_, 0, v___x_1505_);
lean_ctor_set(v___x_1507_, 1, v___x_1506_);
v___x_1508_ = lean_obj_once(&l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__3, &l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__3_once, _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__3);
v___x_1509_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1509_, 0, v___x_1507_);
lean_ctor_set(v___x_1509_, 1, v___x_1508_);
v___x_1510_ = lean_nat_add(v___x_1480_, v_one_1474_);
lean_dec(v___x_1480_);
v___x_1511_ = l_Nat_reprFast(v___x_1510_);
if (v_isShared_1502_ == 0)
{
lean_ctor_set_tag(v___x_1501_, 3);
lean_ctor_set(v___x_1501_, 0, v___x_1511_);
v___x_1513_ = v___x_1501_;
goto v_reusejp_1512_;
}
else
{
lean_object* v_reuseFailAlloc_1518_; 
v_reuseFailAlloc_1518_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1518_, 0, v___x_1511_);
v___x_1513_ = v_reuseFailAlloc_1518_;
goto v_reusejp_1512_;
}
v_reusejp_1512_:
{
lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; 
v___x_1514_ = l_Lean_MessageData_ofFormat(v___x_1513_);
v___x_1515_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1515_, 0, v___x_1509_);
lean_ctor_set(v___x_1515_, 1, v___x_1514_);
v___x_1516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1516_, 0, v___x_1515_);
lean_inc(v_mvarId_1461_);
lean_inc(v_tacticName_1460_);
v___x_1517_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1460_, v_mvarId_1461_, v___x_1516_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_);
v___y_1477_ = v___x_1517_;
goto v___jp_1476_;
}
}
}
}
else
{
lean_object* v_a_1520_; lean_object* v___x_1522_; uint8_t v_isShared_1523_; uint8_t v_isSharedCheck_1527_; 
lean_dec(v___x_1480_);
lean_dec(v_n_1475_);
lean_dec_ref(v_majorType_1462_);
lean_dec(v_mvarId_1461_);
lean_dec(v_tacticName_1460_);
lean_dec_ref(v_idx_1459_);
v_a_1520_ = lean_ctor_get(v___x_1495_, 0);
v_isSharedCheck_1527_ = !lean_is_exclusive(v___x_1495_);
if (v_isSharedCheck_1527_ == 0)
{
v___x_1522_ = v___x_1495_;
v_isShared_1523_ = v_isSharedCheck_1527_;
goto v_resetjp_1521_;
}
else
{
lean_inc(v_a_1520_);
lean_dec(v___x_1495_);
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
}
v___jp_1529_:
{
if (v___x_1528_ == 0)
{
v___y_1484_ = v___y_1530_;
v___y_1485_ = v___y_1531_;
v___y_1486_ = v___y_1532_;
v___y_1487_ = v___y_1533_;
goto v___jp_1483_;
}
else
{
lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v_a_1536_; lean_object* v___x_1538_; uint8_t v_isShared_1539_; uint8_t v_isSharedCheck_1552_; 
v___x_1534_ = l_Lean_Expr_fvarId_x21(v_idx_1459_);
lean_inc(v_arg_1481_);
v___x_1535_ = l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2___redArg(v_arg_1481_, v___x_1534_, v___y_1531_);
v_a_1536_ = lean_ctor_get(v___x_1535_, 0);
v_isSharedCheck_1552_ = !lean_is_exclusive(v___x_1535_);
if (v_isSharedCheck_1552_ == 0)
{
v___x_1538_ = v___x_1535_;
v_isShared_1539_ = v_isSharedCheck_1552_;
goto v_resetjp_1537_;
}
else
{
lean_inc(v_a_1536_);
lean_dec(v___x_1535_);
v___x_1538_ = lean_box(0);
v_isShared_1539_ = v_isSharedCheck_1552_;
goto v_resetjp_1537_;
}
v_resetjp_1537_:
{
uint8_t v___x_1540_; 
v___x_1540_ = lean_unbox(v_a_1536_);
lean_dec(v_a_1536_);
if (v___x_1540_ == 0)
{
lean_del_object(v___x_1538_);
v___y_1484_ = v___y_1530_;
v___y_1485_ = v___y_1531_;
v___y_1486_ = v___y_1532_;
v___y_1487_ = v___y_1533_;
goto v___jp_1483_;
}
else
{
lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1549_; 
v___x_1541_ = lean_obj_once(&l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1, &l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1_once, _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1);
lean_inc_ref(v_idx_1459_);
v___x_1542_ = l_Lean_MessageData_ofExpr(v_idx_1459_);
v___x_1543_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1543_, 0, v___x_1541_);
lean_ctor_set(v___x_1543_, 1, v___x_1542_);
v___x_1544_ = lean_obj_once(&l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__5, &l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__5_once, _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__5);
v___x_1545_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1545_, 0, v___x_1543_);
lean_ctor_set(v___x_1545_, 1, v___x_1544_);
lean_inc_ref(v_majorType_1462_);
v___x_1546_ = l_Lean_indentExpr(v_majorType_1462_);
v___x_1547_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1547_, 0, v___x_1545_);
lean_ctor_set(v___x_1547_, 1, v___x_1546_);
if (v_isShared_1539_ == 0)
{
lean_ctor_set_tag(v___x_1538_, 1);
lean_ctor_set(v___x_1538_, 0, v___x_1547_);
v___x_1549_ = v___x_1538_;
goto v_reusejp_1548_;
}
else
{
lean_object* v_reuseFailAlloc_1551_; 
v_reuseFailAlloc_1551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1551_, 0, v___x_1547_);
v___x_1549_ = v_reuseFailAlloc_1551_;
goto v_reusejp_1548_;
}
v_reusejp_1548_:
{
lean_object* v___x_1550_; 
lean_inc(v_mvarId_1461_);
lean_inc(v_tacticName_1460_);
v___x_1550_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1460_, v_mvarId_1461_, v___x_1549_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_);
if (lean_obj_tag(v___x_1550_) == 0)
{
lean_dec_ref_known(v___x_1550_, 1);
v___y_1484_ = v___y_1530_;
v___y_1485_ = v___y_1531_;
v___y_1486_ = v___y_1532_;
v___y_1487_ = v___y_1533_;
goto v___jp_1483_;
}
else
{
lean_dec(v___x_1480_);
v___y_1477_ = v___x_1550_;
goto v___jp_1476_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___boxed(lean_object* v_majorTypeArgs_1564_, lean_object* v_idxPos_1565_, lean_object* v_recursorInfo_1566_, lean_object* v_idx_1567_, lean_object* v_tacticName_1568_, lean_object* v_mvarId_1569_, lean_object* v_majorType_1570_, lean_object* v_n_1571_, lean_object* v_i_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_){
_start:
{
lean_object* v_res_1578_; 
v_res_1578_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg(v_majorTypeArgs_1564_, v_idxPos_1565_, v_recursorInfo_1566_, v_idx_1567_, v_tacticName_1568_, v_mvarId_1569_, v_majorType_1570_, v_n_1571_, v_i_1572_, v___y_1573_, v___y_1574_, v___y_1575_, v___y_1576_);
lean_dec(v___y_1576_);
lean_dec_ref(v___y_1575_);
lean_dec(v___y_1574_);
lean_dec_ref(v___y_1573_);
lean_dec(v_n_1571_);
lean_dec_ref(v_recursorInfo_1566_);
lean_dec(v_idxPos_1565_);
lean_dec_ref(v_majorTypeArgs_1564_);
return v_res_1578_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__1(void){
_start:
{
lean_object* v___x_1580_; lean_object* v___x_1581_; 
v___x_1580_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__0));
v___x_1581_ = l_Lean_stringToMessageData(v___x_1580_);
return v___x_1581_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__3(void){
_start:
{
lean_object* v___x_1583_; lean_object* v___x_1584_; 
v___x_1583_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__2));
v___x_1584_ = l_Lean_stringToMessageData(v___x_1583_);
return v___x_1584_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__5(void){
_start:
{
lean_object* v___x_1586_; lean_object* v___x_1587_; 
v___x_1586_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__4));
v___x_1587_ = l_Lean_stringToMessageData(v___x_1586_);
return v___x_1587_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4(lean_object* v_majorTypeArgs_1588_, lean_object* v_recursorInfo_1589_, lean_object* v_tacticName_1590_, lean_object* v_mvarId_1591_, lean_object* v_majorType_1592_, size_t v_sz_1593_, size_t v_i_1594_, lean_object* v_bs_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_){
_start:
{
uint8_t v___x_1601_; 
v___x_1601_ = lean_usize_dec_lt(v_i_1594_, v_sz_1593_);
if (v___x_1601_ == 0)
{
lean_object* v___x_1602_; 
lean_dec_ref(v_majorType_1592_);
lean_dec(v_mvarId_1591_);
lean_dec(v_tacticName_1590_);
v___x_1602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1602_, 0, v_bs_1595_);
return v___x_1602_;
}
else
{
lean_object* v_v_1603_; lean_object* v___x_1604_; lean_object* v_bs_x27_1605_; lean_object* v_a_1607_; lean_object* v___x_1612_; uint8_t v___x_1613_; 
v_v_1603_ = lean_array_uget(v_bs_1595_, v_i_1594_);
v___x_1604_ = lean_unsigned_to_nat(0u);
v_bs_x27_1605_ = lean_array_uset(v_bs_1595_, v_i_1594_, v___x_1604_);
v___x_1612_ = lean_array_get_size(v_majorTypeArgs_1588_);
v___x_1613_ = lean_nat_dec_le(v___x_1612_, v_v_1603_);
if (v___x_1613_ == 0)
{
lean_object* v_idx_1614_; lean_object* v___y_1616_; lean_object* v___y_1617_; lean_object* v___y_1618_; lean_object* v___y_1619_; uint8_t v___x_1629_; 
v_idx_1614_ = lean_array_fget_borrowed(v_majorTypeArgs_1588_, v_v_1603_);
v___x_1629_ = l_Lean_Expr_isFVar(v_idx_1614_);
if (v___x_1629_ == 0)
{
lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; 
v___x_1630_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__1);
lean_inc(v_idx_1614_);
v___x_1631_ = l_Lean_MessageData_ofExpr(v_idx_1614_);
v___x_1632_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1632_, 0, v___x_1630_);
lean_ctor_set(v___x_1632_, 1, v___x_1631_);
v___x_1633_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__3);
v___x_1634_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1634_, 0, v___x_1632_);
lean_ctor_set(v___x_1634_, 1, v___x_1633_);
lean_inc_ref(v_majorType_1592_);
v___x_1635_ = l_Lean_indentExpr(v_majorType_1592_);
v___x_1636_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1636_, 0, v___x_1634_);
lean_ctor_set(v___x_1636_, 1, v___x_1635_);
v___x_1637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1637_, 0, v___x_1636_);
lean_inc(v_mvarId_1591_);
lean_inc(v_tacticName_1590_);
v___x_1638_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1590_, v_mvarId_1591_, v___x_1637_, v___y_1596_, v___y_1597_, v___y_1598_, v___y_1599_);
if (lean_obj_tag(v___x_1638_) == 0)
{
lean_dec_ref_known(v___x_1638_, 1);
v___y_1616_ = v___y_1596_;
v___y_1617_ = v___y_1597_;
v___y_1618_ = v___y_1598_;
v___y_1619_ = v___y_1599_;
goto v___jp_1615_;
}
else
{
lean_object* v_a_1639_; lean_object* v___x_1641_; uint8_t v_isShared_1642_; uint8_t v_isSharedCheck_1646_; 
lean_dec_ref(v_bs_x27_1605_);
lean_dec(v_v_1603_);
lean_dec_ref(v_majorType_1592_);
lean_dec(v_mvarId_1591_);
lean_dec(v_tacticName_1590_);
v_a_1639_ = lean_ctor_get(v___x_1638_, 0);
v_isSharedCheck_1646_ = !lean_is_exclusive(v___x_1638_);
if (v_isSharedCheck_1646_ == 0)
{
v___x_1641_ = v___x_1638_;
v_isShared_1642_ = v_isSharedCheck_1646_;
goto v_resetjp_1640_;
}
else
{
lean_inc(v_a_1639_);
lean_dec(v___x_1638_);
v___x_1641_ = lean_box(0);
v_isShared_1642_ = v_isSharedCheck_1646_;
goto v_resetjp_1640_;
}
v_resetjp_1640_:
{
lean_object* v___x_1644_; 
if (v_isShared_1642_ == 0)
{
v___x_1644_ = v___x_1641_;
goto v_reusejp_1643_;
}
else
{
lean_object* v_reuseFailAlloc_1645_; 
v_reuseFailAlloc_1645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1645_, 0, v_a_1639_);
v___x_1644_ = v_reuseFailAlloc_1645_;
goto v_reusejp_1643_;
}
v_reusejp_1643_:
{
return v___x_1644_;
}
}
}
}
else
{
v___y_1616_ = v___y_1596_;
v___y_1617_ = v___y_1597_;
v___y_1618_ = v___y_1598_;
v___y_1619_ = v___y_1599_;
goto v___jp_1615_;
}
v___jp_1615_:
{
lean_object* v___x_1620_; 
lean_inc_ref(v_majorType_1592_);
lean_inc(v_mvarId_1591_);
lean_inc(v_tacticName_1590_);
lean_inc(v_idx_1614_);
v___x_1620_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg(v_majorTypeArgs_1588_, v_v_1603_, v_recursorInfo_1589_, v_idx_1614_, v_tacticName_1590_, v_mvarId_1591_, v_majorType_1592_, v___x_1612_, v___x_1612_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_);
lean_dec(v_v_1603_);
if (lean_obj_tag(v___x_1620_) == 0)
{
lean_dec_ref_known(v___x_1620_, 1);
lean_inc(v_idx_1614_);
v_a_1607_ = v_idx_1614_;
goto v___jp_1606_;
}
else
{
lean_object* v_a_1621_; lean_object* v___x_1623_; uint8_t v_isShared_1624_; uint8_t v_isSharedCheck_1628_; 
lean_dec_ref(v_bs_x27_1605_);
lean_dec_ref(v_majorType_1592_);
lean_dec(v_mvarId_1591_);
lean_dec(v_tacticName_1590_);
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
}
else
{
lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; 
lean_dec(v_v_1603_);
v___x_1647_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__5, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__5);
lean_inc_ref(v_majorType_1592_);
v___x_1648_ = l_Lean_indentExpr(v_majorType_1592_);
v___x_1649_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1649_, 0, v___x_1647_);
lean_ctor_set(v___x_1649_, 1, v___x_1648_);
v___x_1650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1650_, 0, v___x_1649_);
lean_inc(v_mvarId_1591_);
lean_inc(v_tacticName_1590_);
v___x_1651_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1590_, v_mvarId_1591_, v___x_1650_, v___y_1596_, v___y_1597_, v___y_1598_, v___y_1599_);
if (lean_obj_tag(v___x_1651_) == 0)
{
lean_object* v_a_1652_; 
v_a_1652_ = lean_ctor_get(v___x_1651_, 0);
lean_inc(v_a_1652_);
lean_dec_ref_known(v___x_1651_, 1);
v_a_1607_ = v_a_1652_;
goto v___jp_1606_;
}
else
{
lean_object* v_a_1653_; lean_object* v___x_1655_; uint8_t v_isShared_1656_; uint8_t v_isSharedCheck_1660_; 
lean_dec_ref(v_bs_x27_1605_);
lean_dec_ref(v_majorType_1592_);
lean_dec(v_mvarId_1591_);
lean_dec(v_tacticName_1590_);
v_a_1653_ = lean_ctor_get(v___x_1651_, 0);
v_isSharedCheck_1660_ = !lean_is_exclusive(v___x_1651_);
if (v_isSharedCheck_1660_ == 0)
{
v___x_1655_ = v___x_1651_;
v_isShared_1656_ = v_isSharedCheck_1660_;
goto v_resetjp_1654_;
}
else
{
lean_inc(v_a_1653_);
lean_dec(v___x_1651_);
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
}
v___jp_1606_:
{
size_t v___x_1608_; size_t v___x_1609_; lean_object* v___x_1610_; 
v___x_1608_ = ((size_t)1ULL);
v___x_1609_ = lean_usize_add(v_i_1594_, v___x_1608_);
v___x_1610_ = lean_array_uset(v_bs_x27_1605_, v_i_1594_, v_a_1607_);
v_i_1594_ = v___x_1609_;
v_bs_1595_ = v___x_1610_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___boxed(lean_object* v_majorTypeArgs_1661_, lean_object* v_recursorInfo_1662_, lean_object* v_tacticName_1663_, lean_object* v_mvarId_1664_, lean_object* v_majorType_1665_, lean_object* v_sz_1666_, lean_object* v_i_1667_, lean_object* v_bs_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_){
_start:
{
size_t v_sz_boxed_1674_; size_t v_i_boxed_1675_; lean_object* v_res_1676_; 
v_sz_boxed_1674_ = lean_unbox_usize(v_sz_1666_);
lean_dec(v_sz_1666_);
v_i_boxed_1675_ = lean_unbox_usize(v_i_1667_);
lean_dec(v_i_1667_);
v_res_1676_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4(v_majorTypeArgs_1661_, v_recursorInfo_1662_, v_tacticName_1663_, v_mvarId_1664_, v_majorType_1665_, v_sz_boxed_1674_, v_i_boxed_1675_, v_bs_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_);
lean_dec(v___y_1672_);
lean_dec_ref(v___y_1671_);
lean_dec(v___y_1670_);
lean_dec_ref(v___y_1669_);
lean_dec_ref(v_recursorInfo_1662_);
lean_dec_ref(v_majorTypeArgs_1661_);
return v_res_1676_;
}
}
static lean_object* _init_l_Lean_Meta_getMajorTypeIndices___closed__0(void){
_start:
{
lean_object* v___x_1677_; lean_object* v_dummy_1678_; 
v___x_1677_ = lean_box(0);
v_dummy_1678_ = l_Lean_Expr_sort___override(v___x_1677_);
return v_dummy_1678_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMajorTypeIndices(lean_object* v_mvarId_1679_, lean_object* v_tacticName_1680_, lean_object* v_recursorInfo_1681_, lean_object* v_majorType_1682_, lean_object* v_a_1683_, lean_object* v_a_1684_, lean_object* v_a_1685_, lean_object* v_a_1686_){
_start:
{
lean_object* v_indicesPos_1688_; lean_object* v_nargs_1689_; lean_object* v_dummy_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v_majorTypeArgs_1694_; lean_object* v___x_1695_; size_t v_sz_1696_; size_t v___x_1697_; lean_object* v___x_1698_; 
v_indicesPos_1688_ = lean_ctor_get(v_recursorInfo_1681_, 6);
v_nargs_1689_ = l_Lean_Expr_getAppNumArgs(v_majorType_1682_);
v_dummy_1690_ = lean_obj_once(&l_Lean_Meta_getMajorTypeIndices___closed__0, &l_Lean_Meta_getMajorTypeIndices___closed__0_once, _init_l_Lean_Meta_getMajorTypeIndices___closed__0);
lean_inc(v_nargs_1689_);
v___x_1691_ = lean_mk_array(v_nargs_1689_, v_dummy_1690_);
v___x_1692_ = lean_unsigned_to_nat(1u);
v___x_1693_ = lean_nat_sub(v_nargs_1689_, v___x_1692_);
lean_dec(v_nargs_1689_);
lean_inc_ref(v_majorType_1682_);
v_majorTypeArgs_1694_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_majorType_1682_, v___x_1691_, v___x_1693_);
lean_inc(v_indicesPos_1688_);
v___x_1695_ = lean_array_mk(v_indicesPos_1688_);
v_sz_1696_ = lean_array_size(v___x_1695_);
v___x_1697_ = ((size_t)0ULL);
v___x_1698_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4(v_majorTypeArgs_1694_, v_recursorInfo_1681_, v_tacticName_1680_, v_mvarId_1679_, v_majorType_1682_, v_sz_1696_, v___x_1697_, v___x_1695_, v_a_1683_, v_a_1684_, v_a_1685_, v_a_1686_);
lean_dec_ref(v_recursorInfo_1681_);
lean_dec_ref(v_majorTypeArgs_1694_);
return v___x_1698_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMajorTypeIndices___boxed(lean_object* v_mvarId_1699_, lean_object* v_tacticName_1700_, lean_object* v_recursorInfo_1701_, lean_object* v_majorType_1702_, lean_object* v_a_1703_, lean_object* v_a_1704_, lean_object* v_a_1705_, lean_object* v_a_1706_, lean_object* v_a_1707_){
_start:
{
lean_object* v_res_1708_; 
v_res_1708_ = l_Lean_Meta_getMajorTypeIndices(v_mvarId_1699_, v_tacticName_1700_, v_recursorInfo_1701_, v_majorType_1702_, v_a_1703_, v_a_1704_, v_a_1705_, v_a_1706_);
lean_dec(v_a_1706_);
lean_dec_ref(v_a_1705_);
lean_dec(v_a_1704_);
lean_dec_ref(v_a_1703_);
return v_res_1708_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3(lean_object* v_majorTypeArgs_1709_, lean_object* v_idxPos_1710_, lean_object* v_recursorInfo_1711_, lean_object* v_idx_1712_, lean_object* v_tacticName_1713_, lean_object* v_mvarId_1714_, lean_object* v_majorType_1715_, lean_object* v_n_1716_, lean_object* v_i_1717_, lean_object* v_a_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_){
_start:
{
lean_object* v___x_1724_; 
v___x_1724_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg(v_majorTypeArgs_1709_, v_idxPos_1710_, v_recursorInfo_1711_, v_idx_1712_, v_tacticName_1713_, v_mvarId_1714_, v_majorType_1715_, v_n_1716_, v_i_1717_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_);
return v___x_1724_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___boxed(lean_object* v_majorTypeArgs_1725_, lean_object* v_idxPos_1726_, lean_object* v_recursorInfo_1727_, lean_object* v_idx_1728_, lean_object* v_tacticName_1729_, lean_object* v_mvarId_1730_, lean_object* v_majorType_1731_, lean_object* v_n_1732_, lean_object* v_i_1733_, lean_object* v_a_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_){
_start:
{
lean_object* v_res_1740_; 
v_res_1740_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3(v_majorTypeArgs_1725_, v_idxPos_1726_, v_recursorInfo_1727_, v_idx_1728_, v_tacticName_1729_, v_mvarId_1730_, v_majorType_1731_, v_n_1732_, v_i_1733_, v_a_1734_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_);
lean_dec(v___y_1738_);
lean_dec_ref(v___y_1737_);
lean_dec(v___y_1736_);
lean_dec_ref(v___y_1735_);
lean_dec(v_n_1732_);
lean_dec_ref(v_recursorInfo_1727_);
lean_dec(v_idxPos_1726_);
lean_dec_ref(v_majorTypeArgs_1725_);
return v_res_1740_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1___redArg(lean_object* v_name_1741_, lean_object* v_msg_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_){
_start:
{
lean_object* v_ref_1748_; lean_object* v_msg_1749_; lean_object* v___x_1750_; lean_object* v_a_1751_; lean_object* v___x_1753_; uint8_t v_isShared_1754_; uint8_t v_isSharedCheck_1759_; 
v_ref_1748_ = lean_ctor_get(v___y_1745_, 2);
v_msg_1749_ = l_Lean_MessageData_tagWithErrorName(v_msg_1742_, v_name_1741_);
v___x_1750_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1_spec__2(v_msg_1749_, v___y_1743_, v___y_1744_, v___y_1745_, v___y_1746_);
v_a_1751_ = lean_ctor_get(v___x_1750_, 0);
v_isSharedCheck_1759_ = !lean_is_exclusive(v___x_1750_);
if (v_isSharedCheck_1759_ == 0)
{
v___x_1753_ = v___x_1750_;
v_isShared_1754_ = v_isSharedCheck_1759_;
goto v_resetjp_1752_;
}
else
{
lean_inc(v_a_1751_);
lean_dec(v___x_1750_);
v___x_1753_ = lean_box(0);
v_isShared_1754_ = v_isSharedCheck_1759_;
goto v_resetjp_1752_;
}
v_resetjp_1752_:
{
lean_object* v___x_1755_; lean_object* v___x_1757_; 
lean_inc(v_ref_1748_);
v___x_1755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1755_, 0, v_ref_1748_);
lean_ctor_set(v___x_1755_, 1, v_a_1751_);
if (v_isShared_1754_ == 0)
{
lean_ctor_set_tag(v___x_1753_, 1);
lean_ctor_set(v___x_1753_, 0, v___x_1755_);
v___x_1757_ = v___x_1753_;
goto v_reusejp_1756_;
}
else
{
lean_object* v_reuseFailAlloc_1758_; 
v_reuseFailAlloc_1758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1758_, 0, v___x_1755_);
v___x_1757_ = v_reuseFailAlloc_1758_;
goto v_reusejp_1756_;
}
v_reusejp_1756_:
{
return v___x_1757_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1___redArg___boxed(lean_object* v_name_1760_, lean_object* v_msg_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_){
_start:
{
lean_object* v_res_1767_; 
v_res_1767_ = l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1___redArg(v_name_1760_, v_msg_1761_, v___y_1762_, v___y_1763_, v___y_1764_, v___y_1765_);
lean_dec(v___y_1765_);
lean_dec_ref(v___y_1764_);
lean_dec(v___y_1763_);
lean_dec_ref(v___y_1762_);
return v_res_1767_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Meta_mkRecursorAppPrefix_spec__0(lean_object* v_a_1768_, lean_object* v___x_1769_, lean_object* v_tacticName_1770_, lean_object* v_mvarId_1771_, lean_object* v_x_1772_, lean_object* v_x_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_){
_start:
{
if (lean_obj_tag(v_x_1773_) == 0)
{
lean_object* v___x_1779_; 
lean_dec(v_mvarId_1771_);
lean_dec(v_tacticName_1770_);
lean_dec(v_a_1768_);
v___x_1779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1779_, 0, v_x_1772_);
return v___x_1779_;
}
else
{
lean_object* v_head_1780_; 
v_head_1780_ = lean_ctor_get(v_x_1773_, 0);
if (lean_obj_tag(v_head_1780_) == 0)
{
lean_object* v_tail_1781_; lean_object* v_fst_1782_; lean_object* v___x_1784_; uint8_t v_isShared_1785_; uint8_t v_isSharedCheck_1793_; 
v_tail_1781_ = lean_ctor_get(v_x_1773_, 1);
v_fst_1782_ = lean_ctor_get(v_x_1772_, 0);
v_isSharedCheck_1793_ = !lean_is_exclusive(v_x_1772_);
if (v_isSharedCheck_1793_ == 0)
{
lean_object* v_unused_1794_; 
v_unused_1794_ = lean_ctor_get(v_x_1772_, 1);
lean_dec(v_unused_1794_);
v___x_1784_ = v_x_1772_;
v_isShared_1785_ = v_isSharedCheck_1793_;
goto v_resetjp_1783_;
}
else
{
lean_inc(v_fst_1782_);
lean_dec(v_x_1772_);
v___x_1784_ = lean_box(0);
v_isShared_1785_ = v_isSharedCheck_1793_;
goto v_resetjp_1783_;
}
v_resetjp_1783_:
{
lean_object* v___x_1786_; uint8_t v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1790_; 
lean_inc(v_a_1768_);
v___x_1786_ = lean_array_push(v_fst_1782_, v_a_1768_);
v___x_1787_ = 1;
v___x_1788_ = lean_box(v___x_1787_);
if (v_isShared_1785_ == 0)
{
lean_ctor_set(v___x_1784_, 1, v___x_1788_);
lean_ctor_set(v___x_1784_, 0, v___x_1786_);
v___x_1790_ = v___x_1784_;
goto v_reusejp_1789_;
}
else
{
lean_object* v_reuseFailAlloc_1792_; 
v_reuseFailAlloc_1792_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1792_, 0, v___x_1786_);
lean_ctor_set(v_reuseFailAlloc_1792_, 1, v___x_1788_);
v___x_1790_ = v_reuseFailAlloc_1792_;
goto v_reusejp_1789_;
}
v_reusejp_1789_:
{
v_x_1772_ = v___x_1790_;
v_x_1773_ = v_tail_1781_;
goto _start;
}
}
}
else
{
lean_object* v_tail_1795_; lean_object* v_fst_1796_; lean_object* v_snd_1797_; lean_object* v___x_1799_; uint8_t v_isShared_1800_; uint8_t v_isSharedCheck_1814_; 
v_tail_1795_ = lean_ctor_get(v_x_1773_, 1);
v_fst_1796_ = lean_ctor_get(v_x_1772_, 0);
v_snd_1797_ = lean_ctor_get(v_x_1772_, 1);
v_isSharedCheck_1814_ = !lean_is_exclusive(v_x_1772_);
if (v_isSharedCheck_1814_ == 0)
{
v___x_1799_ = v_x_1772_;
v_isShared_1800_ = v_isSharedCheck_1814_;
goto v_resetjp_1798_;
}
else
{
lean_inc(v_snd_1797_);
lean_inc(v_fst_1796_);
lean_dec(v_x_1772_);
v___x_1799_ = lean_box(0);
v_isShared_1800_ = v_isSharedCheck_1814_;
goto v_resetjp_1798_;
}
v_resetjp_1798_:
{
lean_object* v_idx_1801_; lean_object* v___x_1802_; uint8_t v___x_1803_; 
v_idx_1801_ = lean_ctor_get(v_head_1780_, 0);
v___x_1802_ = lean_array_get_size(v___x_1769_);
v___x_1803_ = lean_nat_dec_le(v___x_1802_, v_idx_1801_);
if (v___x_1803_ == 0)
{
lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1807_; 
v___x_1804_ = lean_array_fget_borrowed(v___x_1769_, v_idx_1801_);
lean_inc(v___x_1804_);
v___x_1805_ = lean_array_push(v_fst_1796_, v___x_1804_);
if (v_isShared_1800_ == 0)
{
lean_ctor_set(v___x_1799_, 0, v___x_1805_);
v___x_1807_ = v___x_1799_;
goto v_reusejp_1806_;
}
else
{
lean_object* v_reuseFailAlloc_1809_; 
v_reuseFailAlloc_1809_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1809_, 0, v___x_1805_);
lean_ctor_set(v_reuseFailAlloc_1809_, 1, v_snd_1797_);
v___x_1807_ = v_reuseFailAlloc_1809_;
goto v_reusejp_1806_;
}
v_reusejp_1806_:
{
v_x_1772_ = v___x_1807_;
v_x_1773_ = v_tail_1795_;
goto _start;
}
}
else
{
lean_object* v___x_1810_; lean_object* v___x_1811_; 
lean_del_object(v___x_1799_);
lean_dec(v_snd_1797_);
lean_dec(v_fst_1796_);
v___x_1810_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9);
lean_inc(v_mvarId_1771_);
lean_inc(v_tacticName_1770_);
v___x_1811_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1770_, v_mvarId_1771_, v___x_1810_, v___y_1774_, v___y_1775_, v___y_1776_, v___y_1777_);
if (lean_obj_tag(v___x_1811_) == 0)
{
lean_object* v_a_1812_; 
v_a_1812_ = lean_ctor_get(v___x_1811_, 0);
lean_inc(v_a_1812_);
lean_dec_ref_known(v___x_1811_, 1);
v_x_1772_ = v_a_1812_;
v_x_1773_ = v_tail_1795_;
goto _start;
}
else
{
lean_dec(v_mvarId_1771_);
lean_dec(v_tacticName_1770_);
lean_dec(v_a_1768_);
return v___x_1811_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Meta_mkRecursorAppPrefix_spec__0___boxed(lean_object* v_a_1815_, lean_object* v___x_1816_, lean_object* v_tacticName_1817_, lean_object* v_mvarId_1818_, lean_object* v_x_1819_, lean_object* v_x_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_){
_start:
{
lean_object* v_res_1826_; 
v_res_1826_ = l_List_foldlM___at___00Lean_Meta_mkRecursorAppPrefix_spec__0(v_a_1815_, v___x_1816_, v_tacticName_1817_, v_mvarId_1818_, v_x_1819_, v_x_1820_, v___y_1821_, v___y_1822_, v___y_1823_, v___y_1824_);
lean_dec(v___y_1824_);
lean_dec_ref(v___y_1823_);
lean_dec(v___y_1822_);
lean_dec_ref(v___y_1821_);
lean_dec(v_x_1820_);
lean_dec_ref(v___x_1816_);
return v_res_1826_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__8(void){
_start:
{
lean_object* v___x_1842_; lean_object* v___x_1843_; 
v___x_1842_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__7));
v___x_1843_ = l_Lean_stringToMessageData(v___x_1842_);
return v___x_1843_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__10(void){
_start:
{
lean_object* v___x_1845_; lean_object* v___x_1846_; 
v___x_1845_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__9));
v___x_1846_ = l_Lean_stringToMessageData(v___x_1845_);
return v___x_1846_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__13(void){
_start:
{
lean_object* v___x_1850_; lean_object* v___x_1851_; 
v___x_1850_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__12));
v___x_1851_ = l_Lean_MessageData_ofFormat(v___x_1850_);
return v___x_1851_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__14(void){
_start:
{
lean_object* v___x_1852_; lean_object* v___x_1853_; 
v___x_1852_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__13, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__13_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__13);
v___x_1853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1853_, 0, v___x_1852_);
return v___x_1853_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2(lean_object* v_recursorInfo_1854_, lean_object* v_a_1855_, lean_object* v_tacticName_1856_, lean_object* v_mvarId_1857_, lean_object* v_indices_1858_, lean_object* v_a_1859_, lean_object* v_major_1860_, lean_object* v_x_1861_, lean_object* v_x_1862_, lean_object* v_x_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_){
_start:
{
if (lean_obj_tag(v_x_1861_) == 5)
{
lean_object* v_fn_1869_; lean_object* v_arg_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; 
v_fn_1869_ = lean_ctor_get(v_x_1861_, 0);
lean_inc_ref(v_fn_1869_);
v_arg_1870_ = lean_ctor_get(v_x_1861_, 1);
lean_inc_ref(v_arg_1870_);
lean_dec_ref_known(v_x_1861_, 2);
v___x_1871_ = lean_array_set(v_x_1862_, v_x_1863_, v_arg_1870_);
v___x_1872_ = lean_unsigned_to_nat(1u);
v___x_1873_ = lean_nat_sub(v_x_1863_, v___x_1872_);
lean_dec(v_x_1863_);
v_x_1861_ = v_fn_1869_;
v_x_1862_ = v___x_1871_;
v_x_1863_ = v___x_1873_;
goto _start;
}
else
{
lean_dec(v_x_1863_);
if (lean_obj_tag(v_x_1861_) == 4)
{
lean_object* v_us_1875_; lean_object* v_recursorName_1876_; lean_object* v_univLevelPos_1877_; uint8_t v_depElim_1878_; lean_object* v_paramsPos_1879_; lean_object* v___x_1880_; uint8_t v___x_1881_; lean_object* v___y_1883_; lean_object* v_motive_1884_; lean_object* v___y_1885_; lean_object* v___y_1886_; lean_object* v___y_1887_; lean_object* v___y_1888_; lean_object* v___x_1901_; lean_object* v___x_1902_; 
v_us_1875_ = lean_ctor_get(v_x_1861_, 1);
lean_inc(v_us_1875_);
lean_dec_ref_known(v_x_1861_, 2);
v_recursorName_1876_ = lean_ctor_get(v_recursorInfo_1854_, 0);
lean_inc(v_recursorName_1876_);
v_univLevelPos_1877_ = lean_ctor_get(v_recursorInfo_1854_, 2);
lean_inc(v_univLevelPos_1877_);
v_depElim_1878_ = lean_ctor_get_uint8(v_recursorInfo_1854_, sizeof(void*)*8);
v_paramsPos_1879_ = lean_ctor_get(v_recursorInfo_1854_, 5);
lean_inc(v_paramsPos_1879_);
lean_dec_ref(v_recursorInfo_1854_);
v___x_1880_ = lean_array_mk(v_us_1875_);
v___x_1881_ = 0;
v___x_1901_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__1));
lean_inc(v_mvarId_1857_);
lean_inc(v_tacticName_1856_);
lean_inc(v_a_1855_);
v___x_1902_ = l_List_foldlM___at___00Lean_Meta_mkRecursorAppPrefix_spec__0(v_a_1855_, v___x_1880_, v_tacticName_1856_, v_mvarId_1857_, v___x_1901_, v_univLevelPos_1877_, v___y_1864_, v___y_1865_, v___y_1866_, v___y_1867_);
lean_dec(v_univLevelPos_1877_);
lean_dec_ref(v___x_1880_);
if (lean_obj_tag(v___x_1902_) == 0)
{
lean_object* v_a_1903_; lean_object* v_fst_1904_; lean_object* v_snd_1905_; lean_object* v___x_1907_; uint8_t v_isShared_1908_; uint8_t v_isSharedCheck_1949_; 
v_a_1903_ = lean_ctor_get(v___x_1902_, 0);
lean_inc(v_a_1903_);
lean_dec_ref_known(v___x_1902_, 1);
v_fst_1904_ = lean_ctor_get(v_a_1903_, 0);
v_snd_1905_ = lean_ctor_get(v_a_1903_, 1);
v_isSharedCheck_1949_ = !lean_is_exclusive(v_a_1903_);
if (v_isSharedCheck_1949_ == 0)
{
v___x_1907_ = v_a_1903_;
v_isShared_1908_ = v_isSharedCheck_1949_;
goto v_resetjp_1906_;
}
else
{
lean_inc(v_snd_1905_);
lean_inc(v_fst_1904_);
lean_dec(v_a_1903_);
v___x_1907_ = lean_box(0);
v_isShared_1908_ = v_isSharedCheck_1949_;
goto v_resetjp_1906_;
}
v_resetjp_1906_:
{
lean_object* v___y_1910_; lean_object* v___y_1911_; lean_object* v___y_1912_; lean_object* v___y_1913_; uint8_t v___x_1929_; 
v___x_1929_ = lean_unbox(v_snd_1905_);
lean_dec(v_snd_1905_);
if (v___x_1929_ == 0)
{
uint8_t v___x_1930_; 
v___x_1930_ = l_Lean_Level_isZero(v_a_1855_);
lean_dec(v_a_1855_);
if (v___x_1930_ == 0)
{
lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1935_; 
lean_dec(v_fst_1904_);
lean_dec(v_paramsPos_1879_);
lean_dec_ref(v_x_1862_);
lean_dec_ref(v_major_1860_);
lean_dec_ref(v_a_1859_);
v___x_1931_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__6));
v___x_1932_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__8, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__8_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__8);
v___x_1933_ = l_Lean_MessageData_ofName(v_recursorName_1876_);
if (v_isShared_1908_ == 0)
{
lean_ctor_set_tag(v___x_1907_, 7);
lean_ctor_set(v___x_1907_, 1, v___x_1933_);
lean_ctor_set(v___x_1907_, 0, v___x_1932_);
v___x_1935_ = v___x_1907_;
goto v_reusejp_1934_;
}
else
{
lean_object* v_reuseFailAlloc_1948_; 
v_reuseFailAlloc_1948_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1948_, 0, v___x_1932_);
lean_ctor_set(v_reuseFailAlloc_1948_, 1, v___x_1933_);
v___x_1935_ = v_reuseFailAlloc_1948_;
goto v_reusejp_1934_;
}
v_reusejp_1934_:
{
lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v_a_1940_; lean_object* v___x_1942_; uint8_t v_isShared_1943_; uint8_t v_isSharedCheck_1947_; 
v___x_1936_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__10, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__10_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__10);
v___x_1937_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1937_, 0, v___x_1935_);
lean_ctor_set(v___x_1937_, 1, v___x_1936_);
v___x_1938_ = l_Lean_Meta_mkTacticExMsg(v_tacticName_1856_, v_mvarId_1857_, v___x_1937_);
v___x_1939_ = l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1___redArg(v___x_1931_, v___x_1938_, v___y_1864_, v___y_1865_, v___y_1866_, v___y_1867_);
v_a_1940_ = lean_ctor_get(v___x_1939_, 0);
v_isSharedCheck_1947_ = !lean_is_exclusive(v___x_1939_);
if (v_isSharedCheck_1947_ == 0)
{
v___x_1942_ = v___x_1939_;
v_isShared_1943_ = v_isSharedCheck_1947_;
goto v_resetjp_1941_;
}
else
{
lean_inc(v_a_1940_);
lean_dec(v___x_1939_);
v___x_1942_ = lean_box(0);
v_isShared_1943_ = v_isSharedCheck_1947_;
goto v_resetjp_1941_;
}
v_resetjp_1941_:
{
lean_object* v___x_1945_; 
if (v_isShared_1943_ == 0)
{
v___x_1945_ = v___x_1942_;
goto v_reusejp_1944_;
}
else
{
lean_object* v_reuseFailAlloc_1946_; 
v_reuseFailAlloc_1946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1946_, 0, v_a_1940_);
v___x_1945_ = v_reuseFailAlloc_1946_;
goto v_reusejp_1944_;
}
v_reusejp_1944_:
{
return v___x_1945_;
}
}
}
}
else
{
lean_del_object(v___x_1907_);
lean_dec(v_tacticName_1856_);
v___y_1910_ = v___y_1864_;
v___y_1911_ = v___y_1865_;
v___y_1912_ = v___y_1866_;
v___y_1913_ = v___y_1867_;
goto v___jp_1909_;
}
}
else
{
lean_del_object(v___x_1907_);
lean_dec(v_tacticName_1856_);
lean_dec(v_a_1855_);
v___y_1910_ = v___y_1864_;
v___y_1911_ = v___y_1865_;
v___y_1912_ = v___y_1866_;
v___y_1913_ = v___y_1867_;
goto v___jp_1909_;
}
v___jp_1909_:
{
lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; 
v___x_1914_ = lean_array_to_list(v_fst_1904_);
v___x_1915_ = l_Lean_mkConst(v_recursorName_1876_, v___x_1914_);
v___x_1916_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams(v_mvarId_1857_, v_x_1862_, v_paramsPos_1879_, v___x_1915_, v___y_1910_, v___y_1911_, v___y_1912_, v___y_1913_);
lean_dec_ref(v_x_1862_);
if (lean_obj_tag(v___x_1916_) == 0)
{
if (v_depElim_1878_ == 0)
{
lean_object* v_a_1917_; 
lean_dec_ref(v_major_1860_);
v_a_1917_ = lean_ctor_get(v___x_1916_, 0);
lean_inc(v_a_1917_);
lean_dec_ref_known(v___x_1916_, 1);
v___y_1883_ = v_a_1917_;
v_motive_1884_ = v_a_1859_;
v___y_1885_ = v___y_1910_;
v___y_1886_ = v___y_1911_;
v___y_1887_ = v___y_1912_;
v___y_1888_ = v___y_1913_;
goto v___jp_1882_;
}
else
{
lean_object* v_a_1918_; lean_object* v___x_1919_; 
v_a_1918_ = lean_ctor_get(v___x_1916_, 0);
lean_inc(v_a_1918_);
lean_dec_ref_known(v___x_1916_, 1);
lean_inc(v___y_1913_);
lean_inc_ref(v___y_1912_);
lean_inc(v___y_1911_);
lean_inc_ref(v___y_1910_);
lean_inc_ref(v_major_1860_);
v___x_1919_ = lean_infer_type(v_major_1860_, v___y_1910_, v___y_1911_, v___y_1912_, v___y_1913_);
if (lean_obj_tag(v___x_1919_) == 0)
{
lean_object* v_a_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; 
v_a_1920_ = lean_ctor_get(v___x_1919_, 0);
lean_inc(v_a_1920_);
lean_dec_ref_known(v___x_1919_, 1);
v___x_1921_ = lean_unsigned_to_nat(1u);
v___x_1922_ = lean_mk_empty_array_with_capacity(v___x_1921_);
v___x_1923_ = lean_array_push(v___x_1922_, v_major_1860_);
v___x_1924_ = l_Lean_Expr_abstractM(v_a_1859_, v___x_1923_, v___y_1910_, v___y_1911_, v___y_1912_, v___y_1913_);
lean_dec_ref(v___x_1923_);
if (lean_obj_tag(v___x_1924_) == 0)
{
lean_object* v_a_1925_; lean_object* v___x_1926_; uint8_t v___x_1927_; lean_object* v___x_1928_; 
v_a_1925_ = lean_ctor_get(v___x_1924_, 0);
lean_inc(v_a_1925_);
lean_dec_ref_known(v___x_1924_, 1);
v___x_1926_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__3));
v___x_1927_ = 0;
v___x_1928_ = l_Lean_mkLambda(v___x_1926_, v___x_1927_, v_a_1920_, v_a_1925_);
v___y_1883_ = v_a_1918_;
v_motive_1884_ = v___x_1928_;
v___y_1885_ = v___y_1910_;
v___y_1886_ = v___y_1911_;
v___y_1887_ = v___y_1912_;
v___y_1888_ = v___y_1913_;
goto v___jp_1882_;
}
else
{
lean_dec(v_a_1920_);
lean_dec(v_a_1918_);
return v___x_1924_;
}
}
else
{
lean_dec(v_a_1918_);
lean_dec_ref(v_major_1860_);
lean_dec_ref(v_a_1859_);
return v___x_1919_;
}
}
}
else
{
lean_dec_ref(v_major_1860_);
lean_dec_ref(v_a_1859_);
return v___x_1916_;
}
}
}
}
else
{
lean_object* v_a_1950_; lean_object* v___x_1952_; uint8_t v_isShared_1953_; uint8_t v_isSharedCheck_1957_; 
lean_dec(v_paramsPos_1879_);
lean_dec(v_recursorName_1876_);
lean_dec_ref(v_x_1862_);
lean_dec_ref(v_major_1860_);
lean_dec_ref(v_a_1859_);
lean_dec(v_mvarId_1857_);
lean_dec(v_tacticName_1856_);
lean_dec(v_a_1855_);
v_a_1950_ = lean_ctor_get(v___x_1902_, 0);
v_isSharedCheck_1957_ = !lean_is_exclusive(v___x_1902_);
if (v_isSharedCheck_1957_ == 0)
{
v___x_1952_ = v___x_1902_;
v_isShared_1953_ = v_isSharedCheck_1957_;
goto v_resetjp_1951_;
}
else
{
lean_inc(v_a_1950_);
lean_dec(v___x_1902_);
v___x_1952_ = lean_box(0);
v_isShared_1953_ = v_isSharedCheck_1957_;
goto v_resetjp_1951_;
}
v_resetjp_1951_:
{
lean_object* v___x_1955_; 
if (v_isShared_1953_ == 0)
{
v___x_1955_ = v___x_1952_;
goto v_reusejp_1954_;
}
else
{
lean_object* v_reuseFailAlloc_1956_; 
v_reuseFailAlloc_1956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1956_, 0, v_a_1950_);
v___x_1955_ = v_reuseFailAlloc_1956_;
goto v_reusejp_1954_;
}
v_reusejp_1954_:
{
return v___x_1955_;
}
}
}
v___jp_1882_:
{
uint8_t v___x_1889_; uint8_t v___x_1890_; lean_object* v___x_1891_; 
v___x_1889_ = 1;
v___x_1890_ = 1;
v___x_1891_ = l_Lean_Meta_mkLambdaFVars(v_indices_1858_, v_motive_1884_, v___x_1881_, v___x_1889_, v___x_1881_, v___x_1889_, v___x_1890_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_);
if (lean_obj_tag(v___x_1891_) == 0)
{
lean_object* v_a_1892_; lean_object* v___x_1894_; uint8_t v_isShared_1895_; uint8_t v_isSharedCheck_1900_; 
v_a_1892_ = lean_ctor_get(v___x_1891_, 0);
v_isSharedCheck_1900_ = !lean_is_exclusive(v___x_1891_);
if (v_isSharedCheck_1900_ == 0)
{
v___x_1894_ = v___x_1891_;
v_isShared_1895_ = v_isSharedCheck_1900_;
goto v_resetjp_1893_;
}
else
{
lean_inc(v_a_1892_);
lean_dec(v___x_1891_);
v___x_1894_ = lean_box(0);
v_isShared_1895_ = v_isSharedCheck_1900_;
goto v_resetjp_1893_;
}
v_resetjp_1893_:
{
lean_object* v___x_1896_; lean_object* v___x_1898_; 
v___x_1896_ = l_Lean_Expr_app___override(v___y_1883_, v_a_1892_);
if (v_isShared_1895_ == 0)
{
lean_ctor_set(v___x_1894_, 0, v___x_1896_);
v___x_1898_ = v___x_1894_;
goto v_reusejp_1897_;
}
else
{
lean_object* v_reuseFailAlloc_1899_; 
v_reuseFailAlloc_1899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1899_, 0, v___x_1896_);
v___x_1898_ = v_reuseFailAlloc_1899_;
goto v_reusejp_1897_;
}
v_reusejp_1897_:
{
return v___x_1898_;
}
}
}
else
{
lean_dec_ref(v___y_1883_);
return v___x_1891_;
}
}
}
else
{
lean_object* v___x_1958_; lean_object* v___x_1959_; 
lean_dec_ref(v_x_1862_);
lean_dec_ref(v_x_1861_);
lean_dec_ref(v_major_1860_);
lean_dec_ref(v_a_1859_);
lean_dec(v_a_1855_);
lean_dec_ref(v_recursorInfo_1854_);
v___x_1958_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__14, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__14_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__14);
v___x_1959_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1856_, v_mvarId_1857_, v___x_1958_, v___y_1864_, v___y_1865_, v___y_1866_, v___y_1867_);
return v___x_1959_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___boxed(lean_object* v_recursorInfo_1960_, lean_object* v_a_1961_, lean_object* v_tacticName_1962_, lean_object* v_mvarId_1963_, lean_object* v_indices_1964_, lean_object* v_a_1965_, lean_object* v_major_1966_, lean_object* v_x_1967_, lean_object* v_x_1968_, lean_object* v_x_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_){
_start:
{
lean_object* v_res_1975_; 
v_res_1975_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2(v_recursorInfo_1960_, v_a_1961_, v_tacticName_1962_, v_mvarId_1963_, v_indices_1964_, v_a_1965_, v_major_1966_, v_x_1967_, v_x_1968_, v_x_1969_, v___y_1970_, v___y_1971_, v___y_1972_, v___y_1973_);
lean_dec(v___y_1973_);
lean_dec_ref(v___y_1972_);
lean_dec(v___y_1971_);
lean_dec_ref(v___y_1970_);
lean_dec_ref(v_indices_1964_);
return v_res_1975_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2(lean_object* v_a_1976_, lean_object* v_tacticName_1977_, lean_object* v_mvarId_1978_, lean_object* v_recursorInfo_1979_, lean_object* v_indices_1980_, lean_object* v_a_1981_, lean_object* v_major_1982_, lean_object* v_x_1983_, lean_object* v_x_1984_, lean_object* v_x_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_){
_start:
{
if (lean_obj_tag(v_x_1983_) == 5)
{
lean_object* v_fn_1991_; lean_object* v_arg_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; 
v_fn_1991_ = lean_ctor_get(v_x_1983_, 0);
lean_inc_ref(v_fn_1991_);
v_arg_1992_ = lean_ctor_get(v_x_1983_, 1);
lean_inc_ref(v_arg_1992_);
lean_dec_ref_known(v_x_1983_, 2);
v___x_1993_ = lean_array_set(v_x_1984_, v_x_1985_, v_arg_1992_);
v___x_1994_ = lean_unsigned_to_nat(1u);
v___x_1995_ = lean_nat_sub(v_x_1985_, v___x_1994_);
v___x_1996_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2(v_recursorInfo_1979_, v_a_1976_, v_tacticName_1977_, v_mvarId_1978_, v_indices_1980_, v_a_1981_, v_major_1982_, v_fn_1991_, v___x_1993_, v___x_1995_, v___y_1986_, v___y_1987_, v___y_1988_, v___y_1989_);
return v___x_1996_;
}
else
{
if (lean_obj_tag(v_x_1983_) == 4)
{
lean_object* v_us_1997_; lean_object* v_recursorName_1998_; lean_object* v_univLevelPos_1999_; uint8_t v_depElim_2000_; lean_object* v_paramsPos_2001_; lean_object* v___x_2002_; uint8_t v___x_2003_; lean_object* v___y_2005_; lean_object* v_motive_2006_; lean_object* v___y_2007_; lean_object* v___y_2008_; lean_object* v___y_2009_; lean_object* v___y_2010_; lean_object* v___x_2023_; lean_object* v___x_2024_; 
v_us_1997_ = lean_ctor_get(v_x_1983_, 1);
lean_inc(v_us_1997_);
lean_dec_ref_known(v_x_1983_, 2);
v_recursorName_1998_ = lean_ctor_get(v_recursorInfo_1979_, 0);
lean_inc(v_recursorName_1998_);
v_univLevelPos_1999_ = lean_ctor_get(v_recursorInfo_1979_, 2);
lean_inc(v_univLevelPos_1999_);
v_depElim_2000_ = lean_ctor_get_uint8(v_recursorInfo_1979_, sizeof(void*)*8);
v_paramsPos_2001_ = lean_ctor_get(v_recursorInfo_1979_, 5);
lean_inc(v_paramsPos_2001_);
lean_dec_ref(v_recursorInfo_1979_);
v___x_2002_ = lean_array_mk(v_us_1997_);
v___x_2003_ = 0;
v___x_2023_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__1));
lean_inc(v_mvarId_1978_);
lean_inc(v_tacticName_1977_);
lean_inc(v_a_1976_);
v___x_2024_ = l_List_foldlM___at___00Lean_Meta_mkRecursorAppPrefix_spec__0(v_a_1976_, v___x_2002_, v_tacticName_1977_, v_mvarId_1978_, v___x_2023_, v_univLevelPos_1999_, v___y_1986_, v___y_1987_, v___y_1988_, v___y_1989_);
lean_dec(v_univLevelPos_1999_);
lean_dec_ref(v___x_2002_);
if (lean_obj_tag(v___x_2024_) == 0)
{
lean_object* v_a_2025_; lean_object* v_fst_2026_; lean_object* v_snd_2027_; lean_object* v___x_2029_; uint8_t v_isShared_2030_; uint8_t v_isSharedCheck_2071_; 
v_a_2025_ = lean_ctor_get(v___x_2024_, 0);
lean_inc(v_a_2025_);
lean_dec_ref_known(v___x_2024_, 1);
v_fst_2026_ = lean_ctor_get(v_a_2025_, 0);
v_snd_2027_ = lean_ctor_get(v_a_2025_, 1);
v_isSharedCheck_2071_ = !lean_is_exclusive(v_a_2025_);
if (v_isSharedCheck_2071_ == 0)
{
v___x_2029_ = v_a_2025_;
v_isShared_2030_ = v_isSharedCheck_2071_;
goto v_resetjp_2028_;
}
else
{
lean_inc(v_snd_2027_);
lean_inc(v_fst_2026_);
lean_dec(v_a_2025_);
v___x_2029_ = lean_box(0);
v_isShared_2030_ = v_isSharedCheck_2071_;
goto v_resetjp_2028_;
}
v_resetjp_2028_:
{
lean_object* v___y_2032_; lean_object* v___y_2033_; lean_object* v___y_2034_; lean_object* v___y_2035_; uint8_t v___x_2051_; 
v___x_2051_ = lean_unbox(v_snd_2027_);
lean_dec(v_snd_2027_);
if (v___x_2051_ == 0)
{
uint8_t v___x_2052_; 
v___x_2052_ = l_Lean_Level_isZero(v_a_1976_);
lean_dec(v_a_1976_);
if (v___x_2052_ == 0)
{
lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2057_; 
lean_dec(v_fst_2026_);
lean_dec(v_paramsPos_2001_);
lean_dec_ref(v_x_1984_);
lean_dec_ref(v_major_1982_);
lean_dec_ref(v_a_1981_);
v___x_2053_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__6));
v___x_2054_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__8, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__8_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__8);
v___x_2055_ = l_Lean_MessageData_ofName(v_recursorName_1998_);
if (v_isShared_2030_ == 0)
{
lean_ctor_set_tag(v___x_2029_, 7);
lean_ctor_set(v___x_2029_, 1, v___x_2055_);
lean_ctor_set(v___x_2029_, 0, v___x_2054_);
v___x_2057_ = v___x_2029_;
goto v_reusejp_2056_;
}
else
{
lean_object* v_reuseFailAlloc_2070_; 
v_reuseFailAlloc_2070_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2070_, 0, v___x_2054_);
lean_ctor_set(v_reuseFailAlloc_2070_, 1, v___x_2055_);
v___x_2057_ = v_reuseFailAlloc_2070_;
goto v_reusejp_2056_;
}
v_reusejp_2056_:
{
lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v_a_2062_; lean_object* v___x_2064_; uint8_t v_isShared_2065_; uint8_t v_isSharedCheck_2069_; 
v___x_2058_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__10, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__10_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__10);
v___x_2059_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2059_, 0, v___x_2057_);
lean_ctor_set(v___x_2059_, 1, v___x_2058_);
v___x_2060_ = l_Lean_Meta_mkTacticExMsg(v_tacticName_1977_, v_mvarId_1978_, v___x_2059_);
v___x_2061_ = l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1___redArg(v___x_2053_, v___x_2060_, v___y_1986_, v___y_1987_, v___y_1988_, v___y_1989_);
v_a_2062_ = lean_ctor_get(v___x_2061_, 0);
v_isSharedCheck_2069_ = !lean_is_exclusive(v___x_2061_);
if (v_isSharedCheck_2069_ == 0)
{
v___x_2064_ = v___x_2061_;
v_isShared_2065_ = v_isSharedCheck_2069_;
goto v_resetjp_2063_;
}
else
{
lean_inc(v_a_2062_);
lean_dec(v___x_2061_);
v___x_2064_ = lean_box(0);
v_isShared_2065_ = v_isSharedCheck_2069_;
goto v_resetjp_2063_;
}
v_resetjp_2063_:
{
lean_object* v___x_2067_; 
if (v_isShared_2065_ == 0)
{
v___x_2067_ = v___x_2064_;
goto v_reusejp_2066_;
}
else
{
lean_object* v_reuseFailAlloc_2068_; 
v_reuseFailAlloc_2068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2068_, 0, v_a_2062_);
v___x_2067_ = v_reuseFailAlloc_2068_;
goto v_reusejp_2066_;
}
v_reusejp_2066_:
{
return v___x_2067_;
}
}
}
}
else
{
lean_del_object(v___x_2029_);
lean_dec(v_tacticName_1977_);
v___y_2032_ = v___y_1986_;
v___y_2033_ = v___y_1987_;
v___y_2034_ = v___y_1988_;
v___y_2035_ = v___y_1989_;
goto v___jp_2031_;
}
}
else
{
lean_del_object(v___x_2029_);
lean_dec(v_tacticName_1977_);
lean_dec(v_a_1976_);
v___y_2032_ = v___y_1986_;
v___y_2033_ = v___y_1987_;
v___y_2034_ = v___y_1988_;
v___y_2035_ = v___y_1989_;
goto v___jp_2031_;
}
v___jp_2031_:
{
lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; 
v___x_2036_ = lean_array_to_list(v_fst_2026_);
v___x_2037_ = l_Lean_mkConst(v_recursorName_1998_, v___x_2036_);
v___x_2038_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams(v_mvarId_1978_, v_x_1984_, v_paramsPos_2001_, v___x_2037_, v___y_2032_, v___y_2033_, v___y_2034_, v___y_2035_);
lean_dec_ref(v_x_1984_);
if (lean_obj_tag(v___x_2038_) == 0)
{
if (v_depElim_2000_ == 0)
{
lean_object* v_a_2039_; 
lean_dec_ref(v_major_1982_);
v_a_2039_ = lean_ctor_get(v___x_2038_, 0);
lean_inc(v_a_2039_);
lean_dec_ref_known(v___x_2038_, 1);
v___y_2005_ = v_a_2039_;
v_motive_2006_ = v_a_1981_;
v___y_2007_ = v___y_2032_;
v___y_2008_ = v___y_2033_;
v___y_2009_ = v___y_2034_;
v___y_2010_ = v___y_2035_;
goto v___jp_2004_;
}
else
{
lean_object* v_a_2040_; lean_object* v___x_2041_; 
v_a_2040_ = lean_ctor_get(v___x_2038_, 0);
lean_inc(v_a_2040_);
lean_dec_ref_known(v___x_2038_, 1);
lean_inc(v___y_2035_);
lean_inc_ref(v___y_2034_);
lean_inc(v___y_2033_);
lean_inc_ref(v___y_2032_);
lean_inc_ref(v_major_1982_);
v___x_2041_ = lean_infer_type(v_major_1982_, v___y_2032_, v___y_2033_, v___y_2034_, v___y_2035_);
if (lean_obj_tag(v___x_2041_) == 0)
{
lean_object* v_a_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; 
v_a_2042_ = lean_ctor_get(v___x_2041_, 0);
lean_inc(v_a_2042_);
lean_dec_ref_known(v___x_2041_, 1);
v___x_2043_ = lean_unsigned_to_nat(1u);
v___x_2044_ = lean_mk_empty_array_with_capacity(v___x_2043_);
v___x_2045_ = lean_array_push(v___x_2044_, v_major_1982_);
v___x_2046_ = l_Lean_Expr_abstractM(v_a_1981_, v___x_2045_, v___y_2032_, v___y_2033_, v___y_2034_, v___y_2035_);
lean_dec_ref(v___x_2045_);
if (lean_obj_tag(v___x_2046_) == 0)
{
lean_object* v_a_2047_; lean_object* v___x_2048_; uint8_t v___x_2049_; lean_object* v___x_2050_; 
v_a_2047_ = lean_ctor_get(v___x_2046_, 0);
lean_inc(v_a_2047_);
lean_dec_ref_known(v___x_2046_, 1);
v___x_2048_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__3));
v___x_2049_ = 0;
v___x_2050_ = l_Lean_mkLambda(v___x_2048_, v___x_2049_, v_a_2042_, v_a_2047_);
v___y_2005_ = v_a_2040_;
v_motive_2006_ = v___x_2050_;
v___y_2007_ = v___y_2032_;
v___y_2008_ = v___y_2033_;
v___y_2009_ = v___y_2034_;
v___y_2010_ = v___y_2035_;
goto v___jp_2004_;
}
else
{
lean_dec(v_a_2042_);
lean_dec(v_a_2040_);
return v___x_2046_;
}
}
else
{
lean_dec(v_a_2040_);
lean_dec_ref(v_major_1982_);
lean_dec_ref(v_a_1981_);
return v___x_2041_;
}
}
}
else
{
lean_dec_ref(v_major_1982_);
lean_dec_ref(v_a_1981_);
return v___x_2038_;
}
}
}
}
else
{
lean_object* v_a_2072_; lean_object* v___x_2074_; uint8_t v_isShared_2075_; uint8_t v_isSharedCheck_2079_; 
lean_dec(v_paramsPos_2001_);
lean_dec(v_recursorName_1998_);
lean_dec_ref(v_x_1984_);
lean_dec_ref(v_major_1982_);
lean_dec_ref(v_a_1981_);
lean_dec(v_mvarId_1978_);
lean_dec(v_tacticName_1977_);
lean_dec(v_a_1976_);
v_a_2072_ = lean_ctor_get(v___x_2024_, 0);
v_isSharedCheck_2079_ = !lean_is_exclusive(v___x_2024_);
if (v_isSharedCheck_2079_ == 0)
{
v___x_2074_ = v___x_2024_;
v_isShared_2075_ = v_isSharedCheck_2079_;
goto v_resetjp_2073_;
}
else
{
lean_inc(v_a_2072_);
lean_dec(v___x_2024_);
v___x_2074_ = lean_box(0);
v_isShared_2075_ = v_isSharedCheck_2079_;
goto v_resetjp_2073_;
}
v_resetjp_2073_:
{
lean_object* v___x_2077_; 
if (v_isShared_2075_ == 0)
{
v___x_2077_ = v___x_2074_;
goto v_reusejp_2076_;
}
else
{
lean_object* v_reuseFailAlloc_2078_; 
v_reuseFailAlloc_2078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2078_, 0, v_a_2072_);
v___x_2077_ = v_reuseFailAlloc_2078_;
goto v_reusejp_2076_;
}
v_reusejp_2076_:
{
return v___x_2077_;
}
}
}
v___jp_2004_:
{
uint8_t v___x_2011_; uint8_t v___x_2012_; lean_object* v___x_2013_; 
v___x_2011_ = 1;
v___x_2012_ = 1;
v___x_2013_ = l_Lean_Meta_mkLambdaFVars(v_indices_1980_, v_motive_2006_, v___x_2003_, v___x_2011_, v___x_2003_, v___x_2011_, v___x_2012_, v___y_2007_, v___y_2008_, v___y_2009_, v___y_2010_);
if (lean_obj_tag(v___x_2013_) == 0)
{
lean_object* v_a_2014_; lean_object* v___x_2016_; uint8_t v_isShared_2017_; uint8_t v_isSharedCheck_2022_; 
v_a_2014_ = lean_ctor_get(v___x_2013_, 0);
v_isSharedCheck_2022_ = !lean_is_exclusive(v___x_2013_);
if (v_isSharedCheck_2022_ == 0)
{
v___x_2016_ = v___x_2013_;
v_isShared_2017_ = v_isSharedCheck_2022_;
goto v_resetjp_2015_;
}
else
{
lean_inc(v_a_2014_);
lean_dec(v___x_2013_);
v___x_2016_ = lean_box(0);
v_isShared_2017_ = v_isSharedCheck_2022_;
goto v_resetjp_2015_;
}
v_resetjp_2015_:
{
lean_object* v___x_2018_; lean_object* v___x_2020_; 
v___x_2018_ = l_Lean_Expr_app___override(v___y_2005_, v_a_2014_);
if (v_isShared_2017_ == 0)
{
lean_ctor_set(v___x_2016_, 0, v___x_2018_);
v___x_2020_ = v___x_2016_;
goto v_reusejp_2019_;
}
else
{
lean_object* v_reuseFailAlloc_2021_; 
v_reuseFailAlloc_2021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2021_, 0, v___x_2018_);
v___x_2020_ = v_reuseFailAlloc_2021_;
goto v_reusejp_2019_;
}
v_reusejp_2019_:
{
return v___x_2020_;
}
}
}
else
{
lean_dec_ref(v___y_2005_);
return v___x_2013_;
}
}
}
else
{
lean_object* v___x_2080_; lean_object* v___x_2081_; 
lean_dec_ref(v_x_1984_);
lean_dec_ref(v_x_1983_);
lean_dec_ref(v_major_1982_);
lean_dec_ref(v_a_1981_);
lean_dec_ref(v_recursorInfo_1979_);
lean_dec(v_a_1976_);
v___x_2080_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__14, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__14_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__14);
v___x_2081_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1977_, v_mvarId_1978_, v___x_2080_, v___y_1986_, v___y_1987_, v___y_1988_, v___y_1989_);
return v___x_2081_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2___boxed(lean_object* v_a_2082_, lean_object* v_tacticName_2083_, lean_object* v_mvarId_2084_, lean_object* v_recursorInfo_2085_, lean_object* v_indices_2086_, lean_object* v_a_2087_, lean_object* v_major_2088_, lean_object* v_x_2089_, lean_object* v_x_2090_, lean_object* v_x_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_){
_start:
{
lean_object* v_res_2097_; 
v_res_2097_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2(v_a_2082_, v_tacticName_2083_, v_mvarId_2084_, v_recursorInfo_2085_, v_indices_2086_, v_a_2087_, v_major_2088_, v_x_2089_, v_x_2090_, v_x_2091_, v___y_2092_, v___y_2093_, v___y_2094_, v___y_2095_);
lean_dec(v___y_2095_);
lean_dec_ref(v___y_2094_);
lean_dec(v___y_2093_);
lean_dec_ref(v___y_2092_);
lean_dec(v_x_2091_);
lean_dec_ref(v_indices_2086_);
return v_res_2097_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkRecursorAppPrefix(lean_object* v_mvarId_2098_, lean_object* v_tacticName_2099_, lean_object* v_majorFVarId_2100_, lean_object* v_recursorInfo_2101_, lean_object* v_indices_2102_, lean_object* v_a_2103_, lean_object* v_a_2104_, lean_object* v_a_2105_, lean_object* v_a_2106_){
_start:
{
lean_object* v_major_2108_; lean_object* v___x_2109_; 
lean_inc(v_majorFVarId_2100_);
v_major_2108_ = l_Lean_mkFVar(v_majorFVarId_2100_);
lean_inc(v_mvarId_2098_);
v___x_2109_ = l_Lean_MVarId_getType(v_mvarId_2098_, v_a_2103_, v_a_2104_, v_a_2105_, v_a_2106_);
if (lean_obj_tag(v___x_2109_) == 0)
{
lean_object* v_a_2110_; lean_object* v___x_2111_; 
v_a_2110_ = lean_ctor_get(v___x_2109_, 0);
lean_inc_n(v_a_2110_, 2);
lean_dec_ref_known(v___x_2109_, 1);
v___x_2111_ = l_Lean_Meta_getLevel(v_a_2110_, v_a_2103_, v_a_2104_, v_a_2105_, v_a_2106_);
if (lean_obj_tag(v___x_2111_) == 0)
{
lean_object* v_a_2112_; lean_object* v___x_2113_; 
v_a_2112_ = lean_ctor_get(v___x_2111_, 0);
lean_inc(v_a_2112_);
lean_dec_ref_known(v___x_2111_, 1);
v___x_2113_ = l_Lean_Meta_normalizeLevel(v_a_2112_, v_a_2103_, v_a_2104_, v_a_2105_, v_a_2106_);
if (lean_obj_tag(v___x_2113_) == 0)
{
lean_object* v_a_2114_; lean_object* v___x_2115_; 
v_a_2114_ = lean_ctor_get(v___x_2113_, 0);
lean_inc(v_a_2114_);
lean_dec_ref_known(v___x_2113_, 1);
v___x_2115_ = l_Lean_FVarId_getDecl___redArg(v_majorFVarId_2100_, v_a_2103_, v_a_2105_, v_a_2106_);
if (lean_obj_tag(v___x_2115_) == 0)
{
lean_object* v_a_2116_; lean_object* v_typeName_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; 
v_a_2116_ = lean_ctor_get(v___x_2115_, 0);
lean_inc(v_a_2116_);
lean_dec_ref_known(v___x_2115_, 1);
v_typeName_2117_ = lean_ctor_get(v_recursorInfo_2101_, 1);
v___x_2118_ = l_Lean_LocalDecl_type(v_a_2116_);
lean_dec(v_a_2116_);
lean_inc_ref(v___x_2118_);
v___x_2119_ = l_Lean_Meta_whnfUntil(v___x_2118_, v_typeName_2117_, v_a_2103_, v_a_2104_, v_a_2105_, v_a_2106_);
if (lean_obj_tag(v___x_2119_) == 0)
{
lean_object* v_a_2120_; 
v_a_2120_ = lean_ctor_get(v___x_2119_, 0);
lean_inc(v_a_2120_);
lean_dec_ref_known(v___x_2119_, 1);
if (lean_obj_tag(v_a_2120_) == 1)
{
lean_object* v_val_2121_; lean_object* v_dummy_2122_; lean_object* v_nargs_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; 
lean_dec_ref(v___x_2118_);
v_val_2121_ = lean_ctor_get(v_a_2120_, 0);
lean_inc(v_val_2121_);
lean_dec_ref_known(v_a_2120_, 1);
v_dummy_2122_ = lean_obj_once(&l_Lean_Meta_getMajorTypeIndices___closed__0, &l_Lean_Meta_getMajorTypeIndices___closed__0_once, _init_l_Lean_Meta_getMajorTypeIndices___closed__0);
v_nargs_2123_ = l_Lean_Expr_getAppNumArgs(v_val_2121_);
lean_inc(v_nargs_2123_);
v___x_2124_ = lean_mk_array(v_nargs_2123_, v_dummy_2122_);
v___x_2125_ = lean_unsigned_to_nat(1u);
v___x_2126_ = lean_nat_sub(v_nargs_2123_, v___x_2125_);
lean_dec(v_nargs_2123_);
v___x_2127_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2(v_a_2114_, v_tacticName_2099_, v_mvarId_2098_, v_recursorInfo_2101_, v_indices_2102_, v_a_2110_, v_major_2108_, v_val_2121_, v___x_2124_, v___x_2126_, v_a_2103_, v_a_2104_, v_a_2105_, v_a_2106_);
lean_dec(v___x_2126_);
return v___x_2127_;
}
else
{
lean_object* v___x_2128_; 
lean_dec(v_a_2120_);
lean_dec(v_a_2114_);
lean_dec(v_a_2110_);
lean_dec_ref(v_major_2108_);
lean_dec_ref(v_recursorInfo_2101_);
v___x_2128_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg(v_tacticName_2099_, v_mvarId_2098_, v___x_2118_, v_a_2103_, v_a_2104_, v_a_2105_, v_a_2106_);
return v___x_2128_;
}
}
else
{
lean_object* v_a_2129_; lean_object* v___x_2131_; uint8_t v_isShared_2132_; uint8_t v_isSharedCheck_2136_; 
lean_dec_ref(v___x_2118_);
lean_dec(v_a_2114_);
lean_dec(v_a_2110_);
lean_dec_ref(v_major_2108_);
lean_dec_ref(v_recursorInfo_2101_);
lean_dec(v_tacticName_2099_);
lean_dec(v_mvarId_2098_);
v_a_2129_ = lean_ctor_get(v___x_2119_, 0);
v_isSharedCheck_2136_ = !lean_is_exclusive(v___x_2119_);
if (v_isSharedCheck_2136_ == 0)
{
v___x_2131_ = v___x_2119_;
v_isShared_2132_ = v_isSharedCheck_2136_;
goto v_resetjp_2130_;
}
else
{
lean_inc(v_a_2129_);
lean_dec(v___x_2119_);
v___x_2131_ = lean_box(0);
v_isShared_2132_ = v_isSharedCheck_2136_;
goto v_resetjp_2130_;
}
v_resetjp_2130_:
{
lean_object* v___x_2134_; 
if (v_isShared_2132_ == 0)
{
v___x_2134_ = v___x_2131_;
goto v_reusejp_2133_;
}
else
{
lean_object* v_reuseFailAlloc_2135_; 
v_reuseFailAlloc_2135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2135_, 0, v_a_2129_);
v___x_2134_ = v_reuseFailAlloc_2135_;
goto v_reusejp_2133_;
}
v_reusejp_2133_:
{
return v___x_2134_;
}
}
}
}
else
{
lean_object* v_a_2137_; lean_object* v___x_2139_; uint8_t v_isShared_2140_; uint8_t v_isSharedCheck_2144_; 
lean_dec(v_a_2114_);
lean_dec(v_a_2110_);
lean_dec_ref(v_major_2108_);
lean_dec_ref(v_recursorInfo_2101_);
lean_dec(v_tacticName_2099_);
lean_dec(v_mvarId_2098_);
v_a_2137_ = lean_ctor_get(v___x_2115_, 0);
v_isSharedCheck_2144_ = !lean_is_exclusive(v___x_2115_);
if (v_isSharedCheck_2144_ == 0)
{
v___x_2139_ = v___x_2115_;
v_isShared_2140_ = v_isSharedCheck_2144_;
goto v_resetjp_2138_;
}
else
{
lean_inc(v_a_2137_);
lean_dec(v___x_2115_);
v___x_2139_ = lean_box(0);
v_isShared_2140_ = v_isSharedCheck_2144_;
goto v_resetjp_2138_;
}
v_resetjp_2138_:
{
lean_object* v___x_2142_; 
if (v_isShared_2140_ == 0)
{
v___x_2142_ = v___x_2139_;
goto v_reusejp_2141_;
}
else
{
lean_object* v_reuseFailAlloc_2143_; 
v_reuseFailAlloc_2143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2143_, 0, v_a_2137_);
v___x_2142_ = v_reuseFailAlloc_2143_;
goto v_reusejp_2141_;
}
v_reusejp_2141_:
{
return v___x_2142_;
}
}
}
}
else
{
lean_object* v_a_2145_; lean_object* v___x_2147_; uint8_t v_isShared_2148_; uint8_t v_isSharedCheck_2152_; 
lean_dec(v_a_2110_);
lean_dec_ref(v_major_2108_);
lean_dec_ref(v_recursorInfo_2101_);
lean_dec(v_majorFVarId_2100_);
lean_dec(v_tacticName_2099_);
lean_dec(v_mvarId_2098_);
v_a_2145_ = lean_ctor_get(v___x_2113_, 0);
v_isSharedCheck_2152_ = !lean_is_exclusive(v___x_2113_);
if (v_isSharedCheck_2152_ == 0)
{
v___x_2147_ = v___x_2113_;
v_isShared_2148_ = v_isSharedCheck_2152_;
goto v_resetjp_2146_;
}
else
{
lean_inc(v_a_2145_);
lean_dec(v___x_2113_);
v___x_2147_ = lean_box(0);
v_isShared_2148_ = v_isSharedCheck_2152_;
goto v_resetjp_2146_;
}
v_resetjp_2146_:
{
lean_object* v___x_2150_; 
if (v_isShared_2148_ == 0)
{
v___x_2150_ = v___x_2147_;
goto v_reusejp_2149_;
}
else
{
lean_object* v_reuseFailAlloc_2151_; 
v_reuseFailAlloc_2151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2151_, 0, v_a_2145_);
v___x_2150_ = v_reuseFailAlloc_2151_;
goto v_reusejp_2149_;
}
v_reusejp_2149_:
{
return v___x_2150_;
}
}
}
}
else
{
lean_object* v_a_2153_; lean_object* v___x_2155_; uint8_t v_isShared_2156_; uint8_t v_isSharedCheck_2160_; 
lean_dec(v_a_2110_);
lean_dec_ref(v_major_2108_);
lean_dec_ref(v_recursorInfo_2101_);
lean_dec(v_majorFVarId_2100_);
lean_dec(v_tacticName_2099_);
lean_dec(v_mvarId_2098_);
v_a_2153_ = lean_ctor_get(v___x_2111_, 0);
v_isSharedCheck_2160_ = !lean_is_exclusive(v___x_2111_);
if (v_isSharedCheck_2160_ == 0)
{
v___x_2155_ = v___x_2111_;
v_isShared_2156_ = v_isSharedCheck_2160_;
goto v_resetjp_2154_;
}
else
{
lean_inc(v_a_2153_);
lean_dec(v___x_2111_);
v___x_2155_ = lean_box(0);
v_isShared_2156_ = v_isSharedCheck_2160_;
goto v_resetjp_2154_;
}
v_resetjp_2154_:
{
lean_object* v___x_2158_; 
if (v_isShared_2156_ == 0)
{
v___x_2158_ = v___x_2155_;
goto v_reusejp_2157_;
}
else
{
lean_object* v_reuseFailAlloc_2159_; 
v_reuseFailAlloc_2159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2159_, 0, v_a_2153_);
v___x_2158_ = v_reuseFailAlloc_2159_;
goto v_reusejp_2157_;
}
v_reusejp_2157_:
{
return v___x_2158_;
}
}
}
}
else
{
lean_dec_ref(v_major_2108_);
lean_dec_ref(v_recursorInfo_2101_);
lean_dec(v_majorFVarId_2100_);
lean_dec(v_tacticName_2099_);
lean_dec(v_mvarId_2098_);
return v___x_2109_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkRecursorAppPrefix___boxed(lean_object* v_mvarId_2161_, lean_object* v_tacticName_2162_, lean_object* v_majorFVarId_2163_, lean_object* v_recursorInfo_2164_, lean_object* v_indices_2165_, lean_object* v_a_2166_, lean_object* v_a_2167_, lean_object* v_a_2168_, lean_object* v_a_2169_, lean_object* v_a_2170_){
_start:
{
lean_object* v_res_2171_; 
v_res_2171_ = l_Lean_Meta_mkRecursorAppPrefix(v_mvarId_2161_, v_tacticName_2162_, v_majorFVarId_2163_, v_recursorInfo_2164_, v_indices_2165_, v_a_2166_, v_a_2167_, v_a_2168_, v_a_2169_);
lean_dec(v_a_2169_);
lean_dec_ref(v_a_2168_);
lean_dec(v_a_2167_);
lean_dec_ref(v_a_2166_);
lean_dec_ref(v_indices_2165_);
return v_res_2171_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1(lean_object* v_00_u03b1_2172_, lean_object* v_name_2173_, lean_object* v_msg_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_){
_start:
{
lean_object* v___x_2180_; 
v___x_2180_ = l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1___redArg(v_name_2173_, v_msg_2174_, v___y_2175_, v___y_2176_, v___y_2177_, v___y_2178_);
return v___x_2180_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1___boxed(lean_object* v_00_u03b1_2181_, lean_object* v_name_2182_, lean_object* v_msg_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_){
_start:
{
lean_object* v_res_2189_; 
v_res_2189_ = l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1(v_00_u03b1_2181_, v_name_2182_, v_msg_2183_, v___y_2184_, v___y_2185_, v___y_2186_, v___y_2187_);
lean_dec(v___y_2187_);
lean_dec_ref(v___y_2186_);
lean_dec(v___y_2185_);
lean_dec_ref(v___y_2184_);
return v_res_2189_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___redArg(lean_object* v_mvarId_2190_, lean_object* v_x_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_){
_start:
{
lean_object* v___x_2197_; 
v___x_2197_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_2190_, v_x_2191_, v___y_2192_, v___y_2193_, v___y_2194_, v___y_2195_);
if (lean_obj_tag(v___x_2197_) == 0)
{
lean_object* v_a_2198_; lean_object* v___x_2200_; uint8_t v_isShared_2201_; uint8_t v_isSharedCheck_2205_; 
v_a_2198_ = lean_ctor_get(v___x_2197_, 0);
v_isSharedCheck_2205_ = !lean_is_exclusive(v___x_2197_);
if (v_isSharedCheck_2205_ == 0)
{
v___x_2200_ = v___x_2197_;
v_isShared_2201_ = v_isSharedCheck_2205_;
goto v_resetjp_2199_;
}
else
{
lean_inc(v_a_2198_);
lean_dec(v___x_2197_);
v___x_2200_ = lean_box(0);
v_isShared_2201_ = v_isSharedCheck_2205_;
goto v_resetjp_2199_;
}
v_resetjp_2199_:
{
lean_object* v___x_2203_; 
if (v_isShared_2201_ == 0)
{
v___x_2203_ = v___x_2200_;
goto v_reusejp_2202_;
}
else
{
lean_object* v_reuseFailAlloc_2204_; 
v_reuseFailAlloc_2204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2204_, 0, v_a_2198_);
v___x_2203_ = v_reuseFailAlloc_2204_;
goto v_reusejp_2202_;
}
v_reusejp_2202_:
{
return v___x_2203_;
}
}
}
else
{
lean_object* v_a_2206_; lean_object* v___x_2208_; uint8_t v_isShared_2209_; uint8_t v_isSharedCheck_2213_; 
v_a_2206_ = lean_ctor_get(v___x_2197_, 0);
v_isSharedCheck_2213_ = !lean_is_exclusive(v___x_2197_);
if (v_isSharedCheck_2213_ == 0)
{
v___x_2208_ = v___x_2197_;
v_isShared_2209_ = v_isSharedCheck_2213_;
goto v_resetjp_2207_;
}
else
{
lean_inc(v_a_2206_);
lean_dec(v___x_2197_);
v___x_2208_ = lean_box(0);
v_isShared_2209_ = v_isSharedCheck_2213_;
goto v_resetjp_2207_;
}
v_resetjp_2207_:
{
lean_object* v___x_2211_; 
if (v_isShared_2209_ == 0)
{
v___x_2211_ = v___x_2208_;
goto v_reusejp_2210_;
}
else
{
lean_object* v_reuseFailAlloc_2212_; 
v_reuseFailAlloc_2212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2212_, 0, v_a_2206_);
v___x_2211_ = v_reuseFailAlloc_2212_;
goto v_reusejp_2210_;
}
v_reusejp_2210_:
{
return v___x_2211_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___redArg___boxed(lean_object* v_mvarId_2214_, lean_object* v_x_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_){
_start:
{
lean_object* v_res_2221_; 
v_res_2221_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___redArg(v_mvarId_2214_, v_x_2215_, v___y_2216_, v___y_2217_, v___y_2218_, v___y_2219_);
lean_dec(v___y_2219_);
lean_dec_ref(v___y_2218_);
lean_dec(v___y_2217_);
lean_dec_ref(v___y_2216_);
return v_res_2221_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3(lean_object* v_00_u03b1_2222_, lean_object* v_mvarId_2223_, lean_object* v_x_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_){
_start:
{
lean_object* v___x_2230_; 
v___x_2230_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___redArg(v_mvarId_2223_, v_x_2224_, v___y_2225_, v___y_2226_, v___y_2227_, v___y_2228_);
return v___x_2230_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___boxed(lean_object* v_00_u03b1_2231_, lean_object* v_mvarId_2232_, lean_object* v_x_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_){
_start:
{
lean_object* v_res_2239_; 
v_res_2239_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3(v_00_u03b1_2231_, v_mvarId_2232_, v_x_2233_, v___y_2234_, v___y_2235_, v___y_2236_, v___y_2237_);
lean_dec(v___y_2237_);
lean_dec_ref(v___y_2236_);
lean_dec(v___y_2235_);
lean_dec_ref(v___y_2234_);
return v_res_2239_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_induction_spec__2(lean_object* v_fst_2240_, lean_object* v_as_2241_, size_t v_sz_2242_, size_t v_i_2243_, lean_object* v_b_2244_){
_start:
{
uint8_t v___x_2245_; 
v___x_2245_ = lean_usize_dec_lt(v_i_2243_, v_sz_2242_);
if (v___x_2245_ == 0)
{
return v_b_2244_;
}
else
{
lean_object* v_fst_2246_; lean_object* v_snd_2247_; lean_object* v___x_2249_; uint8_t v_isShared_2250_; uint8_t v_isSharedCheck_2265_; 
v_fst_2246_ = lean_ctor_get(v_b_2244_, 0);
v_snd_2247_ = lean_ctor_get(v_b_2244_, 1);
v_isSharedCheck_2265_ = !lean_is_exclusive(v_b_2244_);
if (v_isSharedCheck_2265_ == 0)
{
v___x_2249_ = v_b_2244_;
v_isShared_2250_ = v_isSharedCheck_2265_;
goto v_resetjp_2248_;
}
else
{
lean_inc(v_snd_2247_);
lean_inc(v_fst_2246_);
lean_dec(v_b_2244_);
v___x_2249_ = lean_box(0);
v_isShared_2250_ = v_isSharedCheck_2265_;
goto v_resetjp_2248_;
}
v_resetjp_2248_:
{
lean_object* v___x_2251_; lean_object* v_a_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2260_; 
v___x_2251_ = lean_box(0);
v_a_2252_ = lean_array_uget_borrowed(v_as_2241_, v_i_2243_);
v___x_2253_ = l_Lean_Expr_fvarId_x21(v_a_2252_);
v___x_2254_ = lean_array_get_borrowed(v___x_2251_, v_fst_2240_, v_snd_2247_);
lean_inc(v___x_2254_);
v___x_2255_ = l_Lean_mkFVar(v___x_2254_);
v___x_2256_ = l_Lean_Meta_FVarSubst_insert(v_fst_2246_, v___x_2253_, v___x_2255_);
v___x_2257_ = lean_unsigned_to_nat(1u);
v___x_2258_ = lean_nat_add(v_snd_2247_, v___x_2257_);
lean_dec(v_snd_2247_);
if (v_isShared_2250_ == 0)
{
lean_ctor_set(v___x_2249_, 1, v___x_2258_);
lean_ctor_set(v___x_2249_, 0, v___x_2256_);
v___x_2260_ = v___x_2249_;
goto v_reusejp_2259_;
}
else
{
lean_object* v_reuseFailAlloc_2264_; 
v_reuseFailAlloc_2264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2264_, 0, v___x_2256_);
lean_ctor_set(v_reuseFailAlloc_2264_, 1, v___x_2258_);
v___x_2260_ = v_reuseFailAlloc_2264_;
goto v_reusejp_2259_;
}
v_reusejp_2259_:
{
size_t v___x_2261_; size_t v___x_2262_; 
v___x_2261_ = ((size_t)1ULL);
v___x_2262_ = lean_usize_add(v_i_2243_, v___x_2261_);
v_i_2243_ = v___x_2262_;
v_b_2244_ = v___x_2260_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_induction_spec__2___boxed(lean_object* v_fst_2266_, lean_object* v_as_2267_, lean_object* v_sz_2268_, lean_object* v_i_2269_, lean_object* v_b_2270_){
_start:
{
size_t v_sz_boxed_2271_; size_t v_i_boxed_2272_; lean_object* v_res_2273_; 
v_sz_boxed_2271_ = lean_unbox_usize(v_sz_2268_);
lean_dec(v_sz_2268_);
v_i_boxed_2272_ = lean_unbox_usize(v_i_2269_);
lean_dec(v_i_2269_);
v_res_2273_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_induction_spec__2(v_fst_2266_, v_as_2267_, v_sz_boxed_2271_, v_i_boxed_2272_, v_b_2270_);
lean_dec_ref(v_as_2267_);
lean_dec_ref(v_fst_2266_);
return v_res_2273_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4___lam__0(lean_object* v_snd_2274_, lean_object* v___x_2275_, lean_object* v_fst_2276_, lean_object* v_a_2277_, lean_object* v___x_2278_, lean_object* v_givenNames_2279_, lean_object* v_fst_2280_, lean_object* v___x_2281_, lean_object* v_fst_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_){
_start:
{
lean_object* v___x_2288_; 
lean_inc_ref(v_a_2277_);
lean_inc(v_snd_2274_);
v___x_2288_ = l_Lean_Meta_mkRecursorAppPrefix(v_snd_2274_, v___x_2275_, v_fst_2276_, v_a_2277_, v___x_2278_, v___y_2283_, v___y_2284_, v___y_2285_, v___y_2286_);
if (lean_obj_tag(v___x_2288_) == 0)
{
lean_object* v_a_2289_; lean_object* v___x_2290_; 
v_a_2289_ = lean_ctor_get(v___x_2288_, 0);
lean_inc(v_a_2289_);
lean_dec_ref_known(v___x_2288_, 1);
v___x_2290_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize(v_snd_2274_, v_givenNames_2279_, v_a_2277_, v_fst_2280_, v___x_2281_, v___x_2278_, v_fst_2282_, v_a_2289_, v___y_2283_, v___y_2284_, v___y_2285_, v___y_2286_);
lean_dec_ref(v_a_2277_);
return v___x_2290_;
}
else
{
lean_object* v_a_2291_; lean_object* v___x_2293_; uint8_t v_isShared_2294_; uint8_t v_isSharedCheck_2298_; 
lean_dec(v_fst_2282_);
lean_dec_ref(v___x_2281_);
lean_dec_ref(v_a_2277_);
lean_dec(v_snd_2274_);
v_a_2291_ = lean_ctor_get(v___x_2288_, 0);
v_isSharedCheck_2298_ = !lean_is_exclusive(v___x_2288_);
if (v_isSharedCheck_2298_ == 0)
{
v___x_2293_ = v___x_2288_;
v_isShared_2294_ = v_isSharedCheck_2298_;
goto v_resetjp_2292_;
}
else
{
lean_inc(v_a_2291_);
lean_dec(v___x_2288_);
v___x_2293_ = lean_box(0);
v_isShared_2294_ = v_isSharedCheck_2298_;
goto v_resetjp_2292_;
}
v_resetjp_2292_:
{
lean_object* v___x_2296_; 
if (v_isShared_2294_ == 0)
{
v___x_2296_ = v___x_2293_;
goto v_reusejp_2295_;
}
else
{
lean_object* v_reuseFailAlloc_2297_; 
v_reuseFailAlloc_2297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2297_, 0, v_a_2291_);
v___x_2296_ = v_reuseFailAlloc_2297_;
goto v_reusejp_2295_;
}
v_reusejp_2295_:
{
return v___x_2296_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4___lam__0___boxed(lean_object* v_snd_2299_, lean_object* v___x_2300_, lean_object* v_fst_2301_, lean_object* v_a_2302_, lean_object* v___x_2303_, lean_object* v_givenNames_2304_, lean_object* v_fst_2305_, lean_object* v___x_2306_, lean_object* v_fst_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_){
_start:
{
lean_object* v_res_2313_; 
v_res_2313_ = l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4___lam__0(v_snd_2299_, v___x_2300_, v_fst_2301_, v_a_2302_, v___x_2303_, v_givenNames_2304_, v_fst_2305_, v___x_2306_, v_fst_2307_, v___y_2308_, v___y_2309_, v___y_2310_, v___y_2311_);
lean_dec(v___y_2311_);
lean_dec_ref(v___y_2310_);
lean_dec(v___y_2309_);
lean_dec_ref(v___y_2308_);
lean_dec_ref(v_fst_2305_);
lean_dec_ref(v_givenNames_2304_);
lean_dec_ref(v___x_2303_);
return v_res_2313_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_induction_spec__1(size_t v_sz_2314_, size_t v_i_2315_, lean_object* v_bs_2316_){
_start:
{
uint8_t v___x_2317_; 
v___x_2317_ = lean_usize_dec_lt(v_i_2315_, v_sz_2314_);
if (v___x_2317_ == 0)
{
return v_bs_2316_;
}
else
{
lean_object* v_v_2318_; lean_object* v___x_2319_; lean_object* v_bs_x27_2320_; lean_object* v___x_2321_; size_t v___x_2322_; size_t v___x_2323_; lean_object* v___x_2324_; 
v_v_2318_ = lean_array_uget(v_bs_2316_, v_i_2315_);
v___x_2319_ = lean_unsigned_to_nat(0u);
v_bs_x27_2320_ = lean_array_uset(v_bs_2316_, v_i_2315_, v___x_2319_);
v___x_2321_ = l_Lean_Expr_fvarId_x21(v_v_2318_);
lean_dec(v_v_2318_);
v___x_2322_ = ((size_t)1ULL);
v___x_2323_ = lean_usize_add(v_i_2315_, v___x_2322_);
v___x_2324_ = lean_array_uset(v_bs_x27_2320_, v_i_2315_, v___x_2321_);
v_i_2315_ = v___x_2323_;
v_bs_2316_ = v___x_2324_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_induction_spec__1___boxed(lean_object* v_sz_2326_, lean_object* v_i_2327_, lean_object* v_bs_2328_){
_start:
{
size_t v_sz_boxed_2329_; size_t v_i_boxed_2330_; lean_object* v_res_2331_; 
v_sz_boxed_2329_ = lean_unbox_usize(v_sz_2326_);
lean_dec(v_sz_2326_);
v_i_boxed_2330_ = lean_unbox_usize(v_i_2327_);
lean_dec(v_i_2327_);
v_res_2331_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_induction_spec__1(v_sz_boxed_2329_, v_i_boxed_2330_, v_bs_2328_);
return v_res_2331_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_MVarId_induction_spec__0(lean_object* v_majorTypeArgs_2332_, lean_object* v_val_2333_, lean_object* v_mvarId_2334_, lean_object* v_as_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_){
_start:
{
if (lean_obj_tag(v_as_2335_) == 0)
{
lean_object* v___x_2341_; lean_object* v___x_2342_; 
lean_dec(v_mvarId_2334_);
lean_dec_ref(v_val_2333_);
v___x_2341_ = lean_box(0);
v___x_2342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2342_, 0, v___x_2341_);
return v___x_2342_;
}
else
{
lean_object* v_head_2343_; 
v_head_2343_ = lean_ctor_get(v_as_2335_, 0);
lean_inc(v_head_2343_);
if (lean_obj_tag(v_head_2343_) == 0)
{
lean_object* v_tail_2344_; 
v_tail_2344_ = lean_ctor_get(v_as_2335_, 1);
lean_inc(v_tail_2344_);
lean_dec_ref_known(v_as_2335_, 2);
v_as_2335_ = v_tail_2344_;
goto _start;
}
else
{
lean_object* v_tail_2346_; lean_object* v___x_2348_; uint8_t v_isShared_2349_; uint8_t v_isSharedCheck_2369_; 
v_tail_2346_ = lean_ctor_get(v_as_2335_, 1);
v_isSharedCheck_2369_ = !lean_is_exclusive(v_as_2335_);
if (v_isSharedCheck_2369_ == 0)
{
lean_object* v_unused_2370_; 
v_unused_2370_ = lean_ctor_get(v_as_2335_, 0);
lean_dec(v_unused_2370_);
v___x_2348_ = v_as_2335_;
v_isShared_2349_ = v_isSharedCheck_2369_;
goto v_resetjp_2347_;
}
else
{
lean_inc(v_tail_2346_);
lean_dec(v_as_2335_);
v___x_2348_ = lean_box(0);
v_isShared_2349_ = v_isSharedCheck_2369_;
goto v_resetjp_2347_;
}
v_resetjp_2347_:
{
lean_object* v_val_2350_; lean_object* v___x_2352_; uint8_t v_isShared_2353_; uint8_t v_isSharedCheck_2368_; 
v_val_2350_ = lean_ctor_get(v_head_2343_, 0);
v_isSharedCheck_2368_ = !lean_is_exclusive(v_head_2343_);
if (v_isSharedCheck_2368_ == 0)
{
v___x_2352_ = v_head_2343_;
v_isShared_2353_ = v_isSharedCheck_2368_;
goto v_resetjp_2351_;
}
else
{
lean_inc(v_val_2350_);
lean_dec(v_head_2343_);
v___x_2352_ = lean_box(0);
v_isShared_2353_ = v_isSharedCheck_2368_;
goto v_resetjp_2351_;
}
v_resetjp_2351_:
{
lean_object* v___x_2354_; uint8_t v___x_2355_; 
v___x_2354_ = lean_array_get_size(v_majorTypeArgs_2332_);
v___x_2355_ = lean_nat_dec_le(v___x_2354_, v_val_2350_);
lean_dec(v_val_2350_);
if (v___x_2355_ == 0)
{
lean_del_object(v___x_2352_);
lean_del_object(v___x_2348_);
v_as_2335_ = v_tail_2346_;
goto _start;
}
else
{
lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2361_; 
v___x_2357_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1));
v___x_2358_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__5, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__5);
lean_inc_ref(v_val_2333_);
v___x_2359_ = l_Lean_indentExpr(v_val_2333_);
if (v_isShared_2349_ == 0)
{
lean_ctor_set_tag(v___x_2348_, 7);
lean_ctor_set(v___x_2348_, 1, v___x_2359_);
lean_ctor_set(v___x_2348_, 0, v___x_2358_);
v___x_2361_ = v___x_2348_;
goto v_reusejp_2360_;
}
else
{
lean_object* v_reuseFailAlloc_2367_; 
v_reuseFailAlloc_2367_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2367_, 0, v___x_2358_);
lean_ctor_set(v_reuseFailAlloc_2367_, 1, v___x_2359_);
v___x_2361_ = v_reuseFailAlloc_2367_;
goto v_reusejp_2360_;
}
v_reusejp_2360_:
{
lean_object* v___x_2363_; 
if (v_isShared_2353_ == 0)
{
lean_ctor_set(v___x_2352_, 0, v___x_2361_);
v___x_2363_ = v___x_2352_;
goto v_reusejp_2362_;
}
else
{
lean_object* v_reuseFailAlloc_2366_; 
v_reuseFailAlloc_2366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2366_, 0, v___x_2361_);
v___x_2363_ = v_reuseFailAlloc_2366_;
goto v_reusejp_2362_;
}
v_reusejp_2362_:
{
lean_object* v___x_2364_; 
lean_inc(v_mvarId_2334_);
v___x_2364_ = l_Lean_Meta_throwTacticEx___redArg(v___x_2357_, v_mvarId_2334_, v___x_2363_, v___y_2336_, v___y_2337_, v___y_2338_, v___y_2339_);
if (lean_obj_tag(v___x_2364_) == 0)
{
lean_dec_ref_known(v___x_2364_, 1);
v_as_2335_ = v_tail_2346_;
goto _start;
}
else
{
lean_dec(v_tail_2346_);
lean_dec(v_mvarId_2334_);
lean_dec_ref(v_val_2333_);
return v___x_2364_;
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
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_MVarId_induction_spec__0___boxed(lean_object* v_majorTypeArgs_2371_, lean_object* v_val_2372_, lean_object* v_mvarId_2373_, lean_object* v_as_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_){
_start:
{
lean_object* v_res_2380_; 
v_res_2380_ = l_List_forM___at___00Lean_MVarId_induction_spec__0(v_majorTypeArgs_2371_, v_val_2372_, v_mvarId_2373_, v_as_2374_, v___y_2375_, v___y_2376_, v___y_2377_, v___y_2378_);
lean_dec(v___y_2378_);
lean_dec_ref(v___y_2377_);
lean_dec(v___y_2376_);
lean_dec_ref(v___y_2375_);
lean_dec_ref(v_majorTypeArgs_2371_);
return v_res_2380_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__1(void){
_start:
{
lean_object* v___x_2382_; lean_object* v___x_2383_; 
v___x_2382_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__0));
v___x_2383_ = l_Lean_stringToMessageData(v___x_2382_);
return v___x_2383_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__3(void){
_start:
{
lean_object* v___x_2385_; lean_object* v___x_2386_; 
v___x_2385_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__2));
v___x_2386_ = l_Lean_stringToMessageData(v___x_2385_);
return v___x_2386_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__5(void){
_start:
{
lean_object* v___x_2388_; lean_object* v___x_2389_; 
v___x_2388_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__4));
v___x_2389_ = l_Lean_stringToMessageData(v___x_2388_);
return v___x_2389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4(lean_object* v_a_2390_, lean_object* v_val_2391_, lean_object* v_mvarId_2392_, lean_object* v_majorFVarId_2393_, lean_object* v_givenNames_2394_, lean_object* v_recursorName_2395_, lean_object* v_x_2396_, lean_object* v_x_2397_, lean_object* v_x_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_){
_start:
{
if (lean_obj_tag(v_x_2396_) == 5)
{
lean_object* v_fn_2404_; lean_object* v_arg_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; 
v_fn_2404_ = lean_ctor_get(v_x_2396_, 0);
lean_inc_ref(v_fn_2404_);
v_arg_2405_ = lean_ctor_get(v_x_2396_, 1);
lean_inc_ref(v_arg_2405_);
lean_dec_ref_known(v_x_2396_, 2);
v___x_2406_ = lean_array_set(v_x_2397_, v_x_2398_, v_arg_2405_);
v___x_2407_ = lean_unsigned_to_nat(1u);
v___x_2408_ = lean_nat_sub(v_x_2398_, v___x_2407_);
lean_dec(v_x_2398_);
v_x_2396_ = v_fn_2404_;
v_x_2397_ = v___x_2406_;
v_x_2398_ = v___x_2408_;
goto _start;
}
else
{
uint8_t v_depElim_2410_; lean_object* v_paramsPos_2411_; lean_object* v___x_2412_; lean_object* v___y_2414_; lean_object* v___y_2415_; lean_object* v___y_2416_; lean_object* v___y_2417_; lean_object* v___y_2418_; size_t v___y_2419_; lean_object* v___y_2420_; lean_object* v___y_2421_; lean_object* v___y_2422_; lean_object* v___y_2423_; lean_object* v___y_2424_; lean_object* v___y_2425_; lean_object* v_cls_2430_; lean_object* v___x_2431_; 
lean_dec(v_x_2398_);
lean_dec_ref(v_x_2396_);
v_depElim_2410_ = lean_ctor_get_uint8(v_a_2390_, sizeof(void*)*8);
v_paramsPos_2411_ = lean_ctor_get(v_a_2390_, 5);
v___x_2412_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1));
v_cls_2430_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__2));
lean_inc(v_paramsPos_2411_);
lean_inc(v_mvarId_2392_);
lean_inc_ref(v_val_2391_);
v___x_2431_ = l_List_forM___at___00Lean_MVarId_induction_spec__0(v_x_2397_, v_val_2391_, v_mvarId_2392_, v_paramsPos_2411_, v___y_2399_, v___y_2400_, v___y_2401_, v___y_2402_);
lean_dec_ref(v_x_2397_);
if (lean_obj_tag(v___x_2431_) == 0)
{
lean_object* v___x_2432_; 
lean_dec_ref_known(v___x_2431_, 1);
lean_inc_ref(v_a_2390_);
lean_inc(v_mvarId_2392_);
v___x_2432_ = l_Lean_Meta_getMajorTypeIndices(v_mvarId_2392_, v___x_2412_, v_a_2390_, v_val_2391_, v___y_2399_, v___y_2400_, v___y_2401_, v___y_2402_);
if (lean_obj_tag(v___x_2432_) == 0)
{
lean_object* v_a_2433_; lean_object* v___y_2435_; lean_object* v___y_2436_; lean_object* v___y_2437_; lean_object* v___y_2438_; lean_object* v___x_2522_; 
v_a_2433_ = lean_ctor_get(v___x_2432_, 0);
lean_inc(v_a_2433_);
lean_dec_ref_known(v___x_2432_, 1);
lean_inc(v_mvarId_2392_);
v___x_2522_ = l_Lean_MVarId_getType(v_mvarId_2392_, v___y_2399_, v___y_2400_, v___y_2401_, v___y_2402_);
if (lean_obj_tag(v___x_2522_) == 0)
{
if (v_depElim_2410_ == 0)
{
lean_object* v_a_2523_; lean_object* v___x_2524_; lean_object* v_a_2525_; lean_object* v___x_2527_; uint8_t v_isShared_2528_; uint8_t v_isSharedCheck_2547_; 
v_a_2523_ = lean_ctor_get(v___x_2522_, 0);
lean_inc(v_a_2523_);
lean_dec_ref_known(v___x_2522_, 1);
lean_inc(v_majorFVarId_2393_);
v___x_2524_ = l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2___redArg(v_a_2523_, v_majorFVarId_2393_, v___y_2400_);
v_a_2525_ = lean_ctor_get(v___x_2524_, 0);
v_isSharedCheck_2547_ = !lean_is_exclusive(v___x_2524_);
if (v_isSharedCheck_2547_ == 0)
{
v___x_2527_ = v___x_2524_;
v_isShared_2528_ = v_isSharedCheck_2547_;
goto v_resetjp_2526_;
}
else
{
lean_inc(v_a_2525_);
lean_dec(v___x_2524_);
v___x_2527_ = lean_box(0);
v_isShared_2528_ = v_isSharedCheck_2547_;
goto v_resetjp_2526_;
}
v_resetjp_2526_:
{
uint8_t v___x_2529_; 
v___x_2529_ = lean_unbox(v_a_2525_);
lean_dec(v_a_2525_);
if (v___x_2529_ == 0)
{
lean_del_object(v___x_2527_);
lean_dec(v_recursorName_2395_);
v___y_2435_ = v___y_2399_;
v___y_2436_ = v___y_2400_;
v___y_2437_ = v___y_2401_;
v___y_2438_ = v___y_2402_;
goto v___jp_2434_;
}
else
{
lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2536_; 
v___x_2530_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__3, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__3);
v___x_2531_ = l_Lean_MessageData_ofName(v_recursorName_2395_);
v___x_2532_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2532_, 0, v___x_2530_);
lean_ctor_set(v___x_2532_, 1, v___x_2531_);
v___x_2533_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__5, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__5_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__5);
v___x_2534_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2534_, 0, v___x_2532_);
lean_ctor_set(v___x_2534_, 1, v___x_2533_);
if (v_isShared_2528_ == 0)
{
lean_ctor_set_tag(v___x_2527_, 1);
lean_ctor_set(v___x_2527_, 0, v___x_2534_);
v___x_2536_ = v___x_2527_;
goto v_reusejp_2535_;
}
else
{
lean_object* v_reuseFailAlloc_2546_; 
v_reuseFailAlloc_2546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2546_, 0, v___x_2534_);
v___x_2536_ = v_reuseFailAlloc_2546_;
goto v_reusejp_2535_;
}
v_reusejp_2535_:
{
lean_object* v___x_2537_; 
lean_inc(v_mvarId_2392_);
v___x_2537_ = l_Lean_Meta_throwTacticEx___redArg(v___x_2412_, v_mvarId_2392_, v___x_2536_, v___y_2399_, v___y_2400_, v___y_2401_, v___y_2402_);
if (lean_obj_tag(v___x_2537_) == 0)
{
lean_dec_ref_known(v___x_2537_, 1);
v___y_2435_ = v___y_2399_;
v___y_2436_ = v___y_2400_;
v___y_2437_ = v___y_2401_;
v___y_2438_ = v___y_2402_;
goto v___jp_2434_;
}
else
{
lean_object* v_a_2538_; lean_object* v___x_2540_; uint8_t v_isShared_2541_; uint8_t v_isSharedCheck_2545_; 
lean_dec(v_a_2433_);
lean_dec_ref(v_givenNames_2394_);
lean_dec(v_majorFVarId_2393_);
lean_dec(v_mvarId_2392_);
lean_dec_ref(v_a_2390_);
v_a_2538_ = lean_ctor_get(v___x_2537_, 0);
v_isSharedCheck_2545_ = !lean_is_exclusive(v___x_2537_);
if (v_isSharedCheck_2545_ == 0)
{
v___x_2540_ = v___x_2537_;
v_isShared_2541_ = v_isSharedCheck_2545_;
goto v_resetjp_2539_;
}
else
{
lean_inc(v_a_2538_);
lean_dec(v___x_2537_);
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
}
}
}
else
{
lean_dec_ref_known(v___x_2522_, 1);
lean_dec(v_recursorName_2395_);
v___y_2435_ = v___y_2399_;
v___y_2436_ = v___y_2400_;
v___y_2437_ = v___y_2401_;
v___y_2438_ = v___y_2402_;
goto v___jp_2434_;
}
}
else
{
lean_object* v_a_2548_; lean_object* v___x_2550_; uint8_t v_isShared_2551_; uint8_t v_isSharedCheck_2555_; 
lean_dec(v_a_2433_);
lean_dec(v_recursorName_2395_);
lean_dec_ref(v_givenNames_2394_);
lean_dec(v_majorFVarId_2393_);
lean_dec(v_mvarId_2392_);
lean_dec_ref(v_a_2390_);
v_a_2548_ = lean_ctor_get(v___x_2522_, 0);
v_isSharedCheck_2555_ = !lean_is_exclusive(v___x_2522_);
if (v_isSharedCheck_2555_ == 0)
{
v___x_2550_ = v___x_2522_;
v_isShared_2551_ = v_isSharedCheck_2555_;
goto v_resetjp_2549_;
}
else
{
lean_inc(v_a_2548_);
lean_dec(v___x_2522_);
v___x_2550_ = lean_box(0);
v_isShared_2551_ = v_isSharedCheck_2555_;
goto v_resetjp_2549_;
}
v_resetjp_2549_:
{
lean_object* v___x_2553_; 
if (v_isShared_2551_ == 0)
{
v___x_2553_ = v___x_2550_;
goto v_reusejp_2552_;
}
else
{
lean_object* v_reuseFailAlloc_2554_; 
v_reuseFailAlloc_2554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2554_, 0, v_a_2548_);
v___x_2553_ = v_reuseFailAlloc_2554_;
goto v_reusejp_2552_;
}
v_reusejp_2552_:
{
return v___x_2553_;
}
}
}
v___jp_2434_:
{
size_t v_sz_2439_; size_t v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; uint8_t v___x_2443_; uint8_t v___x_2444_; lean_object* v___x_2445_; 
v_sz_2439_ = lean_array_size(v_a_2433_);
v___x_2440_ = ((size_t)0ULL);
lean_inc(v_a_2433_);
v___x_2441_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_induction_spec__1(v_sz_2439_, v___x_2440_, v_a_2433_);
lean_inc(v_majorFVarId_2393_);
v___x_2442_ = lean_array_push(v___x_2441_, v_majorFVarId_2393_);
v___x_2443_ = 1;
v___x_2444_ = 0;
v___x_2445_ = l_Lean_MVarId_revert(v_mvarId_2392_, v___x_2442_, v___x_2443_, v___x_2444_, v___y_2435_, v___y_2436_, v___y_2437_, v___y_2438_);
if (lean_obj_tag(v___x_2445_) == 0)
{
lean_object* v_a_2446_; lean_object* v_fst_2447_; lean_object* v_snd_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; 
v_a_2446_ = lean_ctor_get(v___x_2445_, 0);
lean_inc(v_a_2446_);
lean_dec_ref_known(v___x_2445_, 1);
v_fst_2447_ = lean_ctor_get(v_a_2446_, 0);
lean_inc(v_fst_2447_);
v_snd_2448_ = lean_ctor_get(v_a_2446_, 1);
lean_inc(v_snd_2448_);
lean_dec(v_a_2446_);
v___x_2449_ = lean_array_get_size(v_a_2433_);
v___x_2450_ = lean_box(0);
v___x_2451_ = l_Lean_Meta_introNCore(v_snd_2448_, v___x_2449_, v___x_2450_, v___x_2444_, v___x_2443_, v___y_2435_, v___y_2436_, v___y_2437_, v___y_2438_);
if (lean_obj_tag(v___x_2451_) == 0)
{
lean_object* v_a_2452_; lean_object* v_fst_2453_; lean_object* v_snd_2454_; lean_object* v___x_2455_; 
v_a_2452_ = lean_ctor_get(v___x_2451_, 0);
lean_inc(v_a_2452_);
lean_dec_ref_known(v___x_2451_, 1);
v_fst_2453_ = lean_ctor_get(v_a_2452_, 0);
lean_inc(v_fst_2453_);
v_snd_2454_ = lean_ctor_get(v_a_2452_, 1);
lean_inc(v_snd_2454_);
lean_dec(v_a_2452_);
v___x_2455_ = l_Lean_Meta_intro1Core(v_snd_2454_, v___x_2443_, v___y_2435_, v___y_2436_, v___y_2437_, v___y_2438_);
if (lean_obj_tag(v___x_2455_) == 0)
{
lean_object* v_a_2456_; lean_object* v_fst_2457_; lean_object* v_snd_2458_; lean_object* v___x_2460_; uint8_t v_isShared_2461_; uint8_t v_isSharedCheck_2497_; 
v_a_2456_ = lean_ctor_get(v___x_2455_, 0);
lean_inc(v_a_2456_);
lean_dec_ref_known(v___x_2455_, 1);
v_fst_2457_ = lean_ctor_get(v_a_2456_, 0);
v_snd_2458_ = lean_ctor_get(v_a_2456_, 1);
v_isSharedCheck_2497_ = !lean_is_exclusive(v_a_2456_);
if (v_isSharedCheck_2497_ == 0)
{
v___x_2460_ = v_a_2456_;
v_isShared_2461_ = v_isSharedCheck_2497_;
goto v_resetjp_2459_;
}
else
{
lean_inc(v_snd_2458_);
lean_inc(v_fst_2457_);
lean_dec(v_a_2456_);
v___x_2460_ = lean_box(0);
v_isShared_2461_ = v_isSharedCheck_2497_;
goto v_resetjp_2459_;
}
v_resetjp_2459_:
{
lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2467_; 
v___x_2462_ = lean_box(0);
lean_inc(v_fst_2457_);
v___x_2463_ = l_Lean_mkFVar(v_fst_2457_);
lean_inc_ref(v___x_2463_);
v___x_2464_ = l_Lean_Meta_FVarSubst_insert(v___x_2462_, v_majorFVarId_2393_, v___x_2463_);
v___x_2465_ = lean_unsigned_to_nat(0u);
if (v_isShared_2461_ == 0)
{
lean_ctor_set(v___x_2460_, 1, v___x_2465_);
lean_ctor_set(v___x_2460_, 0, v___x_2464_);
v___x_2467_ = v___x_2460_;
goto v_reusejp_2466_;
}
else
{
lean_object* v_reuseFailAlloc_2496_; 
v_reuseFailAlloc_2496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2496_, 0, v___x_2464_);
lean_ctor_set(v_reuseFailAlloc_2496_, 1, v___x_2465_);
v___x_2467_ = v_reuseFailAlloc_2496_;
goto v_reusejp_2466_;
}
v_reusejp_2466_:
{
lean_object* v___x_2468_; lean_object* v_toCold_2469_; lean_object* v_options_2470_; uint8_t v_hasTrace_2471_; 
v___x_2468_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_induction_spec__2(v_fst_2453_, v_a_2433_, v_sz_2439_, v___x_2440_, v___x_2467_);
lean_dec(v_a_2433_);
v_toCold_2469_ = lean_ctor_get(v___y_2437_, 0);
v_options_2470_ = lean_ctor_get(v_toCold_2469_, 2);
v_hasTrace_2471_ = lean_ctor_get_uint8(v_options_2470_, sizeof(void*)*1);
if (v_hasTrace_2471_ == 0)
{
lean_object* v_fst_2472_; 
v_fst_2472_ = lean_ctor_get(v___x_2468_, 0);
lean_inc(v_fst_2472_);
lean_dec_ref(v___x_2468_);
lean_inc(v_snd_2458_);
v___y_2414_ = v___x_2463_;
v___y_2415_ = v_fst_2457_;
v___y_2416_ = v_fst_2472_;
v___y_2417_ = v_fst_2447_;
v___y_2418_ = v_snd_2458_;
v___y_2419_ = v___x_2440_;
v___y_2420_ = v_fst_2453_;
v___y_2421_ = v_snd_2458_;
v___y_2422_ = v___y_2435_;
v___y_2423_ = v___y_2436_;
v___y_2424_ = v___y_2437_;
v___y_2425_ = v___y_2438_;
goto v___jp_2413_;
}
else
{
lean_object* v_fst_2473_; lean_object* v___x_2475_; uint8_t v_isShared_2476_; uint8_t v_isSharedCheck_2494_; 
v_fst_2473_ = lean_ctor_get(v___x_2468_, 0);
v_isSharedCheck_2494_ = !lean_is_exclusive(v___x_2468_);
if (v_isSharedCheck_2494_ == 0)
{
lean_object* v_unused_2495_; 
v_unused_2495_ = lean_ctor_get(v___x_2468_, 1);
lean_dec(v_unused_2495_);
v___x_2475_ = v___x_2468_;
v_isShared_2476_ = v_isSharedCheck_2494_;
goto v_resetjp_2474_;
}
else
{
lean_inc(v_fst_2473_);
lean_dec(v___x_2468_);
v___x_2475_ = lean_box(0);
v_isShared_2476_ = v_isSharedCheck_2494_;
goto v_resetjp_2474_;
}
v_resetjp_2474_:
{
lean_object* v_inheritedTraceOptions_2477_; lean_object* v___x_2478_; uint8_t v___x_2479_; 
v_inheritedTraceOptions_2477_ = lean_ctor_get(v_toCold_2469_, 11);
v___x_2478_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5);
v___x_2479_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2477_, v_options_2470_, v___x_2478_);
if (v___x_2479_ == 0)
{
lean_del_object(v___x_2475_);
lean_inc(v_snd_2458_);
v___y_2414_ = v___x_2463_;
v___y_2415_ = v_fst_2457_;
v___y_2416_ = v_fst_2473_;
v___y_2417_ = v_fst_2447_;
v___y_2418_ = v_snd_2458_;
v___y_2419_ = v___x_2440_;
v___y_2420_ = v_fst_2453_;
v___y_2421_ = v_snd_2458_;
v___y_2422_ = v___y_2435_;
v___y_2423_ = v___y_2436_;
v___y_2424_ = v___y_2437_;
v___y_2425_ = v___y_2438_;
goto v___jp_2413_;
}
else
{
lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2483_; 
v___x_2480_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__1);
lean_inc(v_snd_2458_);
v___x_2481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2481_, 0, v_snd_2458_);
if (v_isShared_2476_ == 0)
{
lean_ctor_set_tag(v___x_2475_, 7);
lean_ctor_set(v___x_2475_, 1, v___x_2481_);
lean_ctor_set(v___x_2475_, 0, v___x_2480_);
v___x_2483_ = v___x_2475_;
goto v_reusejp_2482_;
}
else
{
lean_object* v_reuseFailAlloc_2493_; 
v_reuseFailAlloc_2493_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2493_, 0, v___x_2480_);
lean_ctor_set(v_reuseFailAlloc_2493_, 1, v___x_2481_);
v___x_2483_ = v_reuseFailAlloc_2493_;
goto v_reusejp_2482_;
}
v_reusejp_2482_:
{
lean_object* v___x_2484_; 
v___x_2484_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1(v_cls_2430_, v___x_2483_, v___y_2435_, v___y_2436_, v___y_2437_, v___y_2438_);
if (lean_obj_tag(v___x_2484_) == 0)
{
lean_dec_ref_known(v___x_2484_, 1);
lean_inc(v_snd_2458_);
v___y_2414_ = v___x_2463_;
v___y_2415_ = v_fst_2457_;
v___y_2416_ = v_fst_2473_;
v___y_2417_ = v_fst_2447_;
v___y_2418_ = v_snd_2458_;
v___y_2419_ = v___x_2440_;
v___y_2420_ = v_fst_2453_;
v___y_2421_ = v_snd_2458_;
v___y_2422_ = v___y_2435_;
v___y_2423_ = v___y_2436_;
v___y_2424_ = v___y_2437_;
v___y_2425_ = v___y_2438_;
goto v___jp_2413_;
}
else
{
lean_object* v_a_2485_; lean_object* v___x_2487_; uint8_t v_isShared_2488_; uint8_t v_isSharedCheck_2492_; 
lean_dec(v_fst_2473_);
lean_dec_ref(v___x_2463_);
lean_dec(v_snd_2458_);
lean_dec(v_fst_2457_);
lean_dec(v_fst_2453_);
lean_dec(v_fst_2447_);
lean_dec_ref(v_givenNames_2394_);
lean_dec_ref(v_a_2390_);
v_a_2485_ = lean_ctor_get(v___x_2484_, 0);
v_isSharedCheck_2492_ = !lean_is_exclusive(v___x_2484_);
if (v_isSharedCheck_2492_ == 0)
{
v___x_2487_ = v___x_2484_;
v_isShared_2488_ = v_isSharedCheck_2492_;
goto v_resetjp_2486_;
}
else
{
lean_inc(v_a_2485_);
lean_dec(v___x_2484_);
v___x_2487_ = lean_box(0);
v_isShared_2488_ = v_isSharedCheck_2492_;
goto v_resetjp_2486_;
}
v_resetjp_2486_:
{
lean_object* v___x_2490_; 
if (v_isShared_2488_ == 0)
{
v___x_2490_ = v___x_2487_;
goto v_reusejp_2489_;
}
else
{
lean_object* v_reuseFailAlloc_2491_; 
v_reuseFailAlloc_2491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2491_, 0, v_a_2485_);
v___x_2490_ = v_reuseFailAlloc_2491_;
goto v_reusejp_2489_;
}
v_reusejp_2489_:
{
return v___x_2490_;
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
lean_object* v_a_2498_; lean_object* v___x_2500_; uint8_t v_isShared_2501_; uint8_t v_isSharedCheck_2505_; 
lean_dec(v_fst_2453_);
lean_dec(v_fst_2447_);
lean_dec(v_a_2433_);
lean_dec_ref(v_givenNames_2394_);
lean_dec(v_majorFVarId_2393_);
lean_dec_ref(v_a_2390_);
v_a_2498_ = lean_ctor_get(v___x_2455_, 0);
v_isSharedCheck_2505_ = !lean_is_exclusive(v___x_2455_);
if (v_isSharedCheck_2505_ == 0)
{
v___x_2500_ = v___x_2455_;
v_isShared_2501_ = v_isSharedCheck_2505_;
goto v_resetjp_2499_;
}
else
{
lean_inc(v_a_2498_);
lean_dec(v___x_2455_);
v___x_2500_ = lean_box(0);
v_isShared_2501_ = v_isSharedCheck_2505_;
goto v_resetjp_2499_;
}
v_resetjp_2499_:
{
lean_object* v___x_2503_; 
if (v_isShared_2501_ == 0)
{
v___x_2503_ = v___x_2500_;
goto v_reusejp_2502_;
}
else
{
lean_object* v_reuseFailAlloc_2504_; 
v_reuseFailAlloc_2504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2504_, 0, v_a_2498_);
v___x_2503_ = v_reuseFailAlloc_2504_;
goto v_reusejp_2502_;
}
v_reusejp_2502_:
{
return v___x_2503_;
}
}
}
}
else
{
lean_object* v_a_2506_; lean_object* v___x_2508_; uint8_t v_isShared_2509_; uint8_t v_isSharedCheck_2513_; 
lean_dec(v_fst_2447_);
lean_dec(v_a_2433_);
lean_dec_ref(v_givenNames_2394_);
lean_dec(v_majorFVarId_2393_);
lean_dec_ref(v_a_2390_);
v_a_2506_ = lean_ctor_get(v___x_2451_, 0);
v_isSharedCheck_2513_ = !lean_is_exclusive(v___x_2451_);
if (v_isSharedCheck_2513_ == 0)
{
v___x_2508_ = v___x_2451_;
v_isShared_2509_ = v_isSharedCheck_2513_;
goto v_resetjp_2507_;
}
else
{
lean_inc(v_a_2506_);
lean_dec(v___x_2451_);
v___x_2508_ = lean_box(0);
v_isShared_2509_ = v_isSharedCheck_2513_;
goto v_resetjp_2507_;
}
v_resetjp_2507_:
{
lean_object* v___x_2511_; 
if (v_isShared_2509_ == 0)
{
v___x_2511_ = v___x_2508_;
goto v_reusejp_2510_;
}
else
{
lean_object* v_reuseFailAlloc_2512_; 
v_reuseFailAlloc_2512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2512_, 0, v_a_2506_);
v___x_2511_ = v_reuseFailAlloc_2512_;
goto v_reusejp_2510_;
}
v_reusejp_2510_:
{
return v___x_2511_;
}
}
}
}
else
{
lean_object* v_a_2514_; lean_object* v___x_2516_; uint8_t v_isShared_2517_; uint8_t v_isSharedCheck_2521_; 
lean_dec(v_a_2433_);
lean_dec_ref(v_givenNames_2394_);
lean_dec(v_majorFVarId_2393_);
lean_dec_ref(v_a_2390_);
v_a_2514_ = lean_ctor_get(v___x_2445_, 0);
v_isSharedCheck_2521_ = !lean_is_exclusive(v___x_2445_);
if (v_isSharedCheck_2521_ == 0)
{
v___x_2516_ = v___x_2445_;
v_isShared_2517_ = v_isSharedCheck_2521_;
goto v_resetjp_2515_;
}
else
{
lean_inc(v_a_2514_);
lean_dec(v___x_2445_);
v___x_2516_ = lean_box(0);
v_isShared_2517_ = v_isSharedCheck_2521_;
goto v_resetjp_2515_;
}
v_resetjp_2515_:
{
lean_object* v___x_2519_; 
if (v_isShared_2517_ == 0)
{
v___x_2519_ = v___x_2516_;
goto v_reusejp_2518_;
}
else
{
lean_object* v_reuseFailAlloc_2520_; 
v_reuseFailAlloc_2520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2520_, 0, v_a_2514_);
v___x_2519_ = v_reuseFailAlloc_2520_;
goto v_reusejp_2518_;
}
v_reusejp_2518_:
{
return v___x_2519_;
}
}
}
}
}
else
{
lean_object* v_a_2556_; lean_object* v___x_2558_; uint8_t v_isShared_2559_; uint8_t v_isSharedCheck_2563_; 
lean_dec(v_recursorName_2395_);
lean_dec_ref(v_givenNames_2394_);
lean_dec(v_majorFVarId_2393_);
lean_dec(v_mvarId_2392_);
lean_dec_ref(v_a_2390_);
v_a_2556_ = lean_ctor_get(v___x_2432_, 0);
v_isSharedCheck_2563_ = !lean_is_exclusive(v___x_2432_);
if (v_isSharedCheck_2563_ == 0)
{
v___x_2558_ = v___x_2432_;
v_isShared_2559_ = v_isSharedCheck_2563_;
goto v_resetjp_2557_;
}
else
{
lean_inc(v_a_2556_);
lean_dec(v___x_2432_);
v___x_2558_ = lean_box(0);
v_isShared_2559_ = v_isSharedCheck_2563_;
goto v_resetjp_2557_;
}
v_resetjp_2557_:
{
lean_object* v___x_2561_; 
if (v_isShared_2559_ == 0)
{
v___x_2561_ = v___x_2558_;
goto v_reusejp_2560_;
}
else
{
lean_object* v_reuseFailAlloc_2562_; 
v_reuseFailAlloc_2562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2562_, 0, v_a_2556_);
v___x_2561_ = v_reuseFailAlloc_2562_;
goto v_reusejp_2560_;
}
v_reusejp_2560_:
{
return v___x_2561_;
}
}
}
}
else
{
lean_object* v_a_2564_; lean_object* v___x_2566_; uint8_t v_isShared_2567_; uint8_t v_isSharedCheck_2571_; 
lean_dec(v_recursorName_2395_);
lean_dec_ref(v_givenNames_2394_);
lean_dec(v_majorFVarId_2393_);
lean_dec(v_mvarId_2392_);
lean_dec_ref(v_val_2391_);
lean_dec_ref(v_a_2390_);
v_a_2564_ = lean_ctor_get(v___x_2431_, 0);
v_isSharedCheck_2571_ = !lean_is_exclusive(v___x_2431_);
if (v_isSharedCheck_2571_ == 0)
{
v___x_2566_ = v___x_2431_;
v_isShared_2567_ = v_isSharedCheck_2571_;
goto v_resetjp_2565_;
}
else
{
lean_inc(v_a_2564_);
lean_dec(v___x_2431_);
v___x_2566_ = lean_box(0);
v_isShared_2567_ = v_isSharedCheck_2571_;
goto v_resetjp_2565_;
}
v_resetjp_2565_:
{
lean_object* v___x_2569_; 
if (v_isShared_2567_ == 0)
{
v___x_2569_ = v___x_2566_;
goto v_reusejp_2568_;
}
else
{
lean_object* v_reuseFailAlloc_2570_; 
v_reuseFailAlloc_2570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2570_, 0, v_a_2564_);
v___x_2569_ = v_reuseFailAlloc_2570_;
goto v_reusejp_2568_;
}
v_reusejp_2568_:
{
return v___x_2569_;
}
}
}
v___jp_2413_:
{
size_t v_sz_2426_; lean_object* v___x_2427_; lean_object* v___f_2428_; lean_object* v___x_2429_; 
v_sz_2426_ = lean_array_size(v___y_2420_);
v___x_2427_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__3(v_sz_2426_, v___y_2419_, v___y_2420_);
v___f_2428_ = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4___lam__0___boxed), 14, 9);
lean_closure_set(v___f_2428_, 0, v___y_2418_);
lean_closure_set(v___f_2428_, 1, v___x_2412_);
lean_closure_set(v___f_2428_, 2, v___y_2415_);
lean_closure_set(v___f_2428_, 3, v_a_2390_);
lean_closure_set(v___f_2428_, 4, v___x_2427_);
lean_closure_set(v___f_2428_, 5, v_givenNames_2394_);
lean_closure_set(v___f_2428_, 6, v___y_2417_);
lean_closure_set(v___f_2428_, 7, v___y_2414_);
lean_closure_set(v___f_2428_, 8, v___y_2416_);
v___x_2429_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___redArg(v___y_2421_, v___f_2428_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_);
return v___x_2429_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___boxed(lean_object* v_a_2572_, lean_object* v_val_2573_, lean_object* v_mvarId_2574_, lean_object* v_majorFVarId_2575_, lean_object* v_givenNames_2576_, lean_object* v_recursorName_2577_, lean_object* v_x_2578_, lean_object* v_x_2579_, lean_object* v_x_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_){
_start:
{
lean_object* v_res_2586_; 
v_res_2586_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4(v_a_2572_, v_val_2573_, v_mvarId_2574_, v_majorFVarId_2575_, v_givenNames_2576_, v_recursorName_2577_, v_x_2578_, v_x_2579_, v_x_2580_, v___y_2581_, v___y_2582_, v___y_2583_, v___y_2584_);
lean_dec(v___y_2584_);
lean_dec_ref(v___y_2583_);
lean_dec(v___y_2582_);
lean_dec_ref(v___y_2581_);
return v_res_2586_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4(lean_object* v_val_2587_, lean_object* v_mvarId_2588_, lean_object* v_a_2589_, lean_object* v_majorFVarId_2590_, lean_object* v_givenNames_2591_, lean_object* v_recursorName_2592_, lean_object* v_x_2593_, lean_object* v_x_2594_, lean_object* v_x_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_){
_start:
{
if (lean_obj_tag(v_x_2593_) == 5)
{
lean_object* v_fn_2601_; lean_object* v_arg_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; 
v_fn_2601_ = lean_ctor_get(v_x_2593_, 0);
lean_inc_ref(v_fn_2601_);
v_arg_2602_ = lean_ctor_get(v_x_2593_, 1);
lean_inc_ref(v_arg_2602_);
lean_dec_ref_known(v_x_2593_, 2);
v___x_2603_ = lean_array_set(v_x_2594_, v_x_2595_, v_arg_2602_);
v___x_2604_ = lean_unsigned_to_nat(1u);
v___x_2605_ = lean_nat_sub(v_x_2595_, v___x_2604_);
v___x_2606_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4(v_a_2589_, v_val_2587_, v_mvarId_2588_, v_majorFVarId_2590_, v_givenNames_2591_, v_recursorName_2592_, v_fn_2601_, v___x_2603_, v___x_2605_, v___y_2596_, v___y_2597_, v___y_2598_, v___y_2599_);
return v___x_2606_;
}
else
{
uint8_t v_depElim_2607_; lean_object* v_paramsPos_2608_; lean_object* v___x_2609_; lean_object* v___y_2611_; lean_object* v___y_2612_; lean_object* v___y_2613_; lean_object* v___y_2614_; lean_object* v___y_2615_; lean_object* v___y_2616_; lean_object* v___y_2617_; size_t v___y_2618_; lean_object* v___y_2619_; lean_object* v___y_2620_; lean_object* v___y_2621_; lean_object* v___y_2622_; lean_object* v_cls_2627_; lean_object* v___x_2628_; 
lean_dec_ref(v_x_2593_);
v_depElim_2607_ = lean_ctor_get_uint8(v_a_2589_, sizeof(void*)*8);
v_paramsPos_2608_ = lean_ctor_get(v_a_2589_, 5);
v___x_2609_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1));
v_cls_2627_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__2));
lean_inc(v_paramsPos_2608_);
lean_inc(v_mvarId_2588_);
lean_inc_ref(v_val_2587_);
v___x_2628_ = l_List_forM___at___00Lean_MVarId_induction_spec__0(v_x_2594_, v_val_2587_, v_mvarId_2588_, v_paramsPos_2608_, v___y_2596_, v___y_2597_, v___y_2598_, v___y_2599_);
lean_dec_ref(v_x_2594_);
if (lean_obj_tag(v___x_2628_) == 0)
{
lean_object* v___x_2629_; 
lean_dec_ref_known(v___x_2628_, 1);
lean_inc_ref(v_a_2589_);
lean_inc(v_mvarId_2588_);
v___x_2629_ = l_Lean_Meta_getMajorTypeIndices(v_mvarId_2588_, v___x_2609_, v_a_2589_, v_val_2587_, v___y_2596_, v___y_2597_, v___y_2598_, v___y_2599_);
if (lean_obj_tag(v___x_2629_) == 0)
{
lean_object* v_a_2630_; lean_object* v___y_2632_; lean_object* v___y_2633_; lean_object* v___y_2634_; lean_object* v___y_2635_; lean_object* v___x_2719_; 
v_a_2630_ = lean_ctor_get(v___x_2629_, 0);
lean_inc(v_a_2630_);
lean_dec_ref_known(v___x_2629_, 1);
lean_inc(v_mvarId_2588_);
v___x_2719_ = l_Lean_MVarId_getType(v_mvarId_2588_, v___y_2596_, v___y_2597_, v___y_2598_, v___y_2599_);
if (lean_obj_tag(v___x_2719_) == 0)
{
if (v_depElim_2607_ == 0)
{
lean_object* v_a_2720_; lean_object* v___x_2721_; lean_object* v_a_2722_; lean_object* v___x_2724_; uint8_t v_isShared_2725_; uint8_t v_isSharedCheck_2744_; 
v_a_2720_ = lean_ctor_get(v___x_2719_, 0);
lean_inc(v_a_2720_);
lean_dec_ref_known(v___x_2719_, 1);
lean_inc(v_majorFVarId_2590_);
v___x_2721_ = l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2___redArg(v_a_2720_, v_majorFVarId_2590_, v___y_2597_);
v_a_2722_ = lean_ctor_get(v___x_2721_, 0);
v_isSharedCheck_2744_ = !lean_is_exclusive(v___x_2721_);
if (v_isSharedCheck_2744_ == 0)
{
v___x_2724_ = v___x_2721_;
v_isShared_2725_ = v_isSharedCheck_2744_;
goto v_resetjp_2723_;
}
else
{
lean_inc(v_a_2722_);
lean_dec(v___x_2721_);
v___x_2724_ = lean_box(0);
v_isShared_2725_ = v_isSharedCheck_2744_;
goto v_resetjp_2723_;
}
v_resetjp_2723_:
{
uint8_t v___x_2726_; 
v___x_2726_ = lean_unbox(v_a_2722_);
lean_dec(v_a_2722_);
if (v___x_2726_ == 0)
{
lean_del_object(v___x_2724_);
lean_dec(v_recursorName_2592_);
v___y_2632_ = v___y_2596_;
v___y_2633_ = v___y_2597_;
v___y_2634_ = v___y_2598_;
v___y_2635_ = v___y_2599_;
goto v___jp_2631_;
}
else
{
lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v___x_2733_; 
v___x_2727_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__3, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__3);
v___x_2728_ = l_Lean_MessageData_ofName(v_recursorName_2592_);
v___x_2729_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2729_, 0, v___x_2727_);
lean_ctor_set(v___x_2729_, 1, v___x_2728_);
v___x_2730_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__5, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__5_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__5);
v___x_2731_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2731_, 0, v___x_2729_);
lean_ctor_set(v___x_2731_, 1, v___x_2730_);
if (v_isShared_2725_ == 0)
{
lean_ctor_set_tag(v___x_2724_, 1);
lean_ctor_set(v___x_2724_, 0, v___x_2731_);
v___x_2733_ = v___x_2724_;
goto v_reusejp_2732_;
}
else
{
lean_object* v_reuseFailAlloc_2743_; 
v_reuseFailAlloc_2743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2743_, 0, v___x_2731_);
v___x_2733_ = v_reuseFailAlloc_2743_;
goto v_reusejp_2732_;
}
v_reusejp_2732_:
{
lean_object* v___x_2734_; 
lean_inc(v_mvarId_2588_);
v___x_2734_ = l_Lean_Meta_throwTacticEx___redArg(v___x_2609_, v_mvarId_2588_, v___x_2733_, v___y_2596_, v___y_2597_, v___y_2598_, v___y_2599_);
if (lean_obj_tag(v___x_2734_) == 0)
{
lean_dec_ref_known(v___x_2734_, 1);
v___y_2632_ = v___y_2596_;
v___y_2633_ = v___y_2597_;
v___y_2634_ = v___y_2598_;
v___y_2635_ = v___y_2599_;
goto v___jp_2631_;
}
else
{
lean_object* v_a_2735_; lean_object* v___x_2737_; uint8_t v_isShared_2738_; uint8_t v_isSharedCheck_2742_; 
lean_dec(v_a_2630_);
lean_dec_ref(v_givenNames_2591_);
lean_dec(v_majorFVarId_2590_);
lean_dec_ref(v_a_2589_);
lean_dec(v_mvarId_2588_);
v_a_2735_ = lean_ctor_get(v___x_2734_, 0);
v_isSharedCheck_2742_ = !lean_is_exclusive(v___x_2734_);
if (v_isSharedCheck_2742_ == 0)
{
v___x_2737_ = v___x_2734_;
v_isShared_2738_ = v_isSharedCheck_2742_;
goto v_resetjp_2736_;
}
else
{
lean_inc(v_a_2735_);
lean_dec(v___x_2734_);
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
}
}
}
else
{
lean_dec_ref_known(v___x_2719_, 1);
lean_dec(v_recursorName_2592_);
v___y_2632_ = v___y_2596_;
v___y_2633_ = v___y_2597_;
v___y_2634_ = v___y_2598_;
v___y_2635_ = v___y_2599_;
goto v___jp_2631_;
}
}
else
{
lean_object* v_a_2745_; lean_object* v___x_2747_; uint8_t v_isShared_2748_; uint8_t v_isSharedCheck_2752_; 
lean_dec(v_a_2630_);
lean_dec(v_recursorName_2592_);
lean_dec_ref(v_givenNames_2591_);
lean_dec(v_majorFVarId_2590_);
lean_dec_ref(v_a_2589_);
lean_dec(v_mvarId_2588_);
v_a_2745_ = lean_ctor_get(v___x_2719_, 0);
v_isSharedCheck_2752_ = !lean_is_exclusive(v___x_2719_);
if (v_isSharedCheck_2752_ == 0)
{
v___x_2747_ = v___x_2719_;
v_isShared_2748_ = v_isSharedCheck_2752_;
goto v_resetjp_2746_;
}
else
{
lean_inc(v_a_2745_);
lean_dec(v___x_2719_);
v___x_2747_ = lean_box(0);
v_isShared_2748_ = v_isSharedCheck_2752_;
goto v_resetjp_2746_;
}
v_resetjp_2746_:
{
lean_object* v___x_2750_; 
if (v_isShared_2748_ == 0)
{
v___x_2750_ = v___x_2747_;
goto v_reusejp_2749_;
}
else
{
lean_object* v_reuseFailAlloc_2751_; 
v_reuseFailAlloc_2751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2751_, 0, v_a_2745_);
v___x_2750_ = v_reuseFailAlloc_2751_;
goto v_reusejp_2749_;
}
v_reusejp_2749_:
{
return v___x_2750_;
}
}
}
v___jp_2631_:
{
size_t v_sz_2636_; size_t v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; uint8_t v___x_2640_; uint8_t v___x_2641_; lean_object* v___x_2642_; 
v_sz_2636_ = lean_array_size(v_a_2630_);
v___x_2637_ = ((size_t)0ULL);
lean_inc(v_a_2630_);
v___x_2638_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_induction_spec__1(v_sz_2636_, v___x_2637_, v_a_2630_);
lean_inc(v_majorFVarId_2590_);
v___x_2639_ = lean_array_push(v___x_2638_, v_majorFVarId_2590_);
v___x_2640_ = 1;
v___x_2641_ = 0;
v___x_2642_ = l_Lean_MVarId_revert(v_mvarId_2588_, v___x_2639_, v___x_2640_, v___x_2641_, v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_);
if (lean_obj_tag(v___x_2642_) == 0)
{
lean_object* v_a_2643_; lean_object* v_fst_2644_; lean_object* v_snd_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; 
v_a_2643_ = lean_ctor_get(v___x_2642_, 0);
lean_inc(v_a_2643_);
lean_dec_ref_known(v___x_2642_, 1);
v_fst_2644_ = lean_ctor_get(v_a_2643_, 0);
lean_inc(v_fst_2644_);
v_snd_2645_ = lean_ctor_get(v_a_2643_, 1);
lean_inc(v_snd_2645_);
lean_dec(v_a_2643_);
v___x_2646_ = lean_array_get_size(v_a_2630_);
v___x_2647_ = lean_box(0);
v___x_2648_ = l_Lean_Meta_introNCore(v_snd_2645_, v___x_2646_, v___x_2647_, v___x_2641_, v___x_2640_, v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_);
if (lean_obj_tag(v___x_2648_) == 0)
{
lean_object* v_a_2649_; lean_object* v_fst_2650_; lean_object* v_snd_2651_; lean_object* v___x_2652_; 
v_a_2649_ = lean_ctor_get(v___x_2648_, 0);
lean_inc(v_a_2649_);
lean_dec_ref_known(v___x_2648_, 1);
v_fst_2650_ = lean_ctor_get(v_a_2649_, 0);
lean_inc(v_fst_2650_);
v_snd_2651_ = lean_ctor_get(v_a_2649_, 1);
lean_inc(v_snd_2651_);
lean_dec(v_a_2649_);
v___x_2652_ = l_Lean_Meta_intro1Core(v_snd_2651_, v___x_2640_, v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_);
if (lean_obj_tag(v___x_2652_) == 0)
{
lean_object* v_a_2653_; lean_object* v_fst_2654_; lean_object* v_snd_2655_; lean_object* v___x_2657_; uint8_t v_isShared_2658_; uint8_t v_isSharedCheck_2694_; 
v_a_2653_ = lean_ctor_get(v___x_2652_, 0);
lean_inc(v_a_2653_);
lean_dec_ref_known(v___x_2652_, 1);
v_fst_2654_ = lean_ctor_get(v_a_2653_, 0);
v_snd_2655_ = lean_ctor_get(v_a_2653_, 1);
v_isSharedCheck_2694_ = !lean_is_exclusive(v_a_2653_);
if (v_isSharedCheck_2694_ == 0)
{
v___x_2657_ = v_a_2653_;
v_isShared_2658_ = v_isSharedCheck_2694_;
goto v_resetjp_2656_;
}
else
{
lean_inc(v_snd_2655_);
lean_inc(v_fst_2654_);
lean_dec(v_a_2653_);
v___x_2657_ = lean_box(0);
v_isShared_2658_ = v_isSharedCheck_2694_;
goto v_resetjp_2656_;
}
v_resetjp_2656_:
{
lean_object* v___x_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2664_; 
v___x_2659_ = lean_box(0);
lean_inc(v_fst_2654_);
v___x_2660_ = l_Lean_mkFVar(v_fst_2654_);
lean_inc_ref(v___x_2660_);
v___x_2661_ = l_Lean_Meta_FVarSubst_insert(v___x_2659_, v_majorFVarId_2590_, v___x_2660_);
v___x_2662_ = lean_unsigned_to_nat(0u);
if (v_isShared_2658_ == 0)
{
lean_ctor_set(v___x_2657_, 1, v___x_2662_);
lean_ctor_set(v___x_2657_, 0, v___x_2661_);
v___x_2664_ = v___x_2657_;
goto v_reusejp_2663_;
}
else
{
lean_object* v_reuseFailAlloc_2693_; 
v_reuseFailAlloc_2693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2693_, 0, v___x_2661_);
lean_ctor_set(v_reuseFailAlloc_2693_, 1, v___x_2662_);
v___x_2664_ = v_reuseFailAlloc_2693_;
goto v_reusejp_2663_;
}
v_reusejp_2663_:
{
lean_object* v___x_2665_; lean_object* v_toCold_2666_; lean_object* v_options_2667_; uint8_t v_hasTrace_2668_; 
v___x_2665_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_induction_spec__2(v_fst_2650_, v_a_2630_, v_sz_2636_, v___x_2637_, v___x_2664_);
lean_dec(v_a_2630_);
v_toCold_2666_ = lean_ctor_get(v___y_2634_, 0);
v_options_2667_ = lean_ctor_get(v_toCold_2666_, 2);
v_hasTrace_2668_ = lean_ctor_get_uint8(v_options_2667_, sizeof(void*)*1);
if (v_hasTrace_2668_ == 0)
{
lean_object* v_fst_2669_; 
v_fst_2669_ = lean_ctor_get(v___x_2665_, 0);
lean_inc(v_fst_2669_);
lean_dec_ref(v___x_2665_);
lean_inc(v_snd_2655_);
v___y_2611_ = v_snd_2655_;
v___y_2612_ = v_fst_2669_;
v___y_2613_ = v_fst_2644_;
v___y_2614_ = v_fst_2654_;
v___y_2615_ = v___x_2660_;
v___y_2616_ = v_snd_2655_;
v___y_2617_ = v_fst_2650_;
v___y_2618_ = v___x_2637_;
v___y_2619_ = v___y_2632_;
v___y_2620_ = v___y_2633_;
v___y_2621_ = v___y_2634_;
v___y_2622_ = v___y_2635_;
goto v___jp_2610_;
}
else
{
lean_object* v_fst_2670_; lean_object* v___x_2672_; uint8_t v_isShared_2673_; uint8_t v_isSharedCheck_2691_; 
v_fst_2670_ = lean_ctor_get(v___x_2665_, 0);
v_isSharedCheck_2691_ = !lean_is_exclusive(v___x_2665_);
if (v_isSharedCheck_2691_ == 0)
{
lean_object* v_unused_2692_; 
v_unused_2692_ = lean_ctor_get(v___x_2665_, 1);
lean_dec(v_unused_2692_);
v___x_2672_ = v___x_2665_;
v_isShared_2673_ = v_isSharedCheck_2691_;
goto v_resetjp_2671_;
}
else
{
lean_inc(v_fst_2670_);
lean_dec(v___x_2665_);
v___x_2672_ = lean_box(0);
v_isShared_2673_ = v_isSharedCheck_2691_;
goto v_resetjp_2671_;
}
v_resetjp_2671_:
{
lean_object* v_inheritedTraceOptions_2674_; lean_object* v___x_2675_; uint8_t v___x_2676_; 
v_inheritedTraceOptions_2674_ = lean_ctor_get(v_toCold_2666_, 11);
v___x_2675_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5);
v___x_2676_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2674_, v_options_2667_, v___x_2675_);
if (v___x_2676_ == 0)
{
lean_del_object(v___x_2672_);
lean_inc(v_snd_2655_);
v___y_2611_ = v_snd_2655_;
v___y_2612_ = v_fst_2670_;
v___y_2613_ = v_fst_2644_;
v___y_2614_ = v_fst_2654_;
v___y_2615_ = v___x_2660_;
v___y_2616_ = v_snd_2655_;
v___y_2617_ = v_fst_2650_;
v___y_2618_ = v___x_2637_;
v___y_2619_ = v___y_2632_;
v___y_2620_ = v___y_2633_;
v___y_2621_ = v___y_2634_;
v___y_2622_ = v___y_2635_;
goto v___jp_2610_;
}
else
{
lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2680_; 
v___x_2677_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__1);
lean_inc(v_snd_2655_);
v___x_2678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2678_, 0, v_snd_2655_);
if (v_isShared_2673_ == 0)
{
lean_ctor_set_tag(v___x_2672_, 7);
lean_ctor_set(v___x_2672_, 1, v___x_2678_);
lean_ctor_set(v___x_2672_, 0, v___x_2677_);
v___x_2680_ = v___x_2672_;
goto v_reusejp_2679_;
}
else
{
lean_object* v_reuseFailAlloc_2690_; 
v_reuseFailAlloc_2690_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2690_, 0, v___x_2677_);
lean_ctor_set(v_reuseFailAlloc_2690_, 1, v___x_2678_);
v___x_2680_ = v_reuseFailAlloc_2690_;
goto v_reusejp_2679_;
}
v_reusejp_2679_:
{
lean_object* v___x_2681_; 
v___x_2681_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1(v_cls_2627_, v___x_2680_, v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_);
if (lean_obj_tag(v___x_2681_) == 0)
{
lean_dec_ref_known(v___x_2681_, 1);
lean_inc(v_snd_2655_);
v___y_2611_ = v_snd_2655_;
v___y_2612_ = v_fst_2670_;
v___y_2613_ = v_fst_2644_;
v___y_2614_ = v_fst_2654_;
v___y_2615_ = v___x_2660_;
v___y_2616_ = v_snd_2655_;
v___y_2617_ = v_fst_2650_;
v___y_2618_ = v___x_2637_;
v___y_2619_ = v___y_2632_;
v___y_2620_ = v___y_2633_;
v___y_2621_ = v___y_2634_;
v___y_2622_ = v___y_2635_;
goto v___jp_2610_;
}
else
{
lean_object* v_a_2682_; lean_object* v___x_2684_; uint8_t v_isShared_2685_; uint8_t v_isSharedCheck_2689_; 
lean_dec(v_fst_2670_);
lean_dec_ref(v___x_2660_);
lean_dec(v_snd_2655_);
lean_dec(v_fst_2654_);
lean_dec(v_fst_2650_);
lean_dec(v_fst_2644_);
lean_dec_ref(v_givenNames_2591_);
lean_dec_ref(v_a_2589_);
v_a_2682_ = lean_ctor_get(v___x_2681_, 0);
v_isSharedCheck_2689_ = !lean_is_exclusive(v___x_2681_);
if (v_isSharedCheck_2689_ == 0)
{
v___x_2684_ = v___x_2681_;
v_isShared_2685_ = v_isSharedCheck_2689_;
goto v_resetjp_2683_;
}
else
{
lean_inc(v_a_2682_);
lean_dec(v___x_2681_);
v___x_2684_ = lean_box(0);
v_isShared_2685_ = v_isSharedCheck_2689_;
goto v_resetjp_2683_;
}
v_resetjp_2683_:
{
lean_object* v___x_2687_; 
if (v_isShared_2685_ == 0)
{
v___x_2687_ = v___x_2684_;
goto v_reusejp_2686_;
}
else
{
lean_object* v_reuseFailAlloc_2688_; 
v_reuseFailAlloc_2688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2688_, 0, v_a_2682_);
v___x_2687_ = v_reuseFailAlloc_2688_;
goto v_reusejp_2686_;
}
v_reusejp_2686_:
{
return v___x_2687_;
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
lean_object* v_a_2695_; lean_object* v___x_2697_; uint8_t v_isShared_2698_; uint8_t v_isSharedCheck_2702_; 
lean_dec(v_fst_2650_);
lean_dec(v_fst_2644_);
lean_dec(v_a_2630_);
lean_dec_ref(v_givenNames_2591_);
lean_dec(v_majorFVarId_2590_);
lean_dec_ref(v_a_2589_);
v_a_2695_ = lean_ctor_get(v___x_2652_, 0);
v_isSharedCheck_2702_ = !lean_is_exclusive(v___x_2652_);
if (v_isSharedCheck_2702_ == 0)
{
v___x_2697_ = v___x_2652_;
v_isShared_2698_ = v_isSharedCheck_2702_;
goto v_resetjp_2696_;
}
else
{
lean_inc(v_a_2695_);
lean_dec(v___x_2652_);
v___x_2697_ = lean_box(0);
v_isShared_2698_ = v_isSharedCheck_2702_;
goto v_resetjp_2696_;
}
v_resetjp_2696_:
{
lean_object* v___x_2700_; 
if (v_isShared_2698_ == 0)
{
v___x_2700_ = v___x_2697_;
goto v_reusejp_2699_;
}
else
{
lean_object* v_reuseFailAlloc_2701_; 
v_reuseFailAlloc_2701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2701_, 0, v_a_2695_);
v___x_2700_ = v_reuseFailAlloc_2701_;
goto v_reusejp_2699_;
}
v_reusejp_2699_:
{
return v___x_2700_;
}
}
}
}
else
{
lean_object* v_a_2703_; lean_object* v___x_2705_; uint8_t v_isShared_2706_; uint8_t v_isSharedCheck_2710_; 
lean_dec(v_fst_2644_);
lean_dec(v_a_2630_);
lean_dec_ref(v_givenNames_2591_);
lean_dec(v_majorFVarId_2590_);
lean_dec_ref(v_a_2589_);
v_a_2703_ = lean_ctor_get(v___x_2648_, 0);
v_isSharedCheck_2710_ = !lean_is_exclusive(v___x_2648_);
if (v_isSharedCheck_2710_ == 0)
{
v___x_2705_ = v___x_2648_;
v_isShared_2706_ = v_isSharedCheck_2710_;
goto v_resetjp_2704_;
}
else
{
lean_inc(v_a_2703_);
lean_dec(v___x_2648_);
v___x_2705_ = lean_box(0);
v_isShared_2706_ = v_isSharedCheck_2710_;
goto v_resetjp_2704_;
}
v_resetjp_2704_:
{
lean_object* v___x_2708_; 
if (v_isShared_2706_ == 0)
{
v___x_2708_ = v___x_2705_;
goto v_reusejp_2707_;
}
else
{
lean_object* v_reuseFailAlloc_2709_; 
v_reuseFailAlloc_2709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2709_, 0, v_a_2703_);
v___x_2708_ = v_reuseFailAlloc_2709_;
goto v_reusejp_2707_;
}
v_reusejp_2707_:
{
return v___x_2708_;
}
}
}
}
else
{
lean_object* v_a_2711_; lean_object* v___x_2713_; uint8_t v_isShared_2714_; uint8_t v_isSharedCheck_2718_; 
lean_dec(v_a_2630_);
lean_dec_ref(v_givenNames_2591_);
lean_dec(v_majorFVarId_2590_);
lean_dec_ref(v_a_2589_);
v_a_2711_ = lean_ctor_get(v___x_2642_, 0);
v_isSharedCheck_2718_ = !lean_is_exclusive(v___x_2642_);
if (v_isSharedCheck_2718_ == 0)
{
v___x_2713_ = v___x_2642_;
v_isShared_2714_ = v_isSharedCheck_2718_;
goto v_resetjp_2712_;
}
else
{
lean_inc(v_a_2711_);
lean_dec(v___x_2642_);
v___x_2713_ = lean_box(0);
v_isShared_2714_ = v_isSharedCheck_2718_;
goto v_resetjp_2712_;
}
v_resetjp_2712_:
{
lean_object* v___x_2716_; 
if (v_isShared_2714_ == 0)
{
v___x_2716_ = v___x_2713_;
goto v_reusejp_2715_;
}
else
{
lean_object* v_reuseFailAlloc_2717_; 
v_reuseFailAlloc_2717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2717_, 0, v_a_2711_);
v___x_2716_ = v_reuseFailAlloc_2717_;
goto v_reusejp_2715_;
}
v_reusejp_2715_:
{
return v___x_2716_;
}
}
}
}
}
else
{
lean_object* v_a_2753_; lean_object* v___x_2755_; uint8_t v_isShared_2756_; uint8_t v_isSharedCheck_2760_; 
lean_dec(v_recursorName_2592_);
lean_dec_ref(v_givenNames_2591_);
lean_dec(v_majorFVarId_2590_);
lean_dec_ref(v_a_2589_);
lean_dec(v_mvarId_2588_);
v_a_2753_ = lean_ctor_get(v___x_2629_, 0);
v_isSharedCheck_2760_ = !lean_is_exclusive(v___x_2629_);
if (v_isSharedCheck_2760_ == 0)
{
v___x_2755_ = v___x_2629_;
v_isShared_2756_ = v_isSharedCheck_2760_;
goto v_resetjp_2754_;
}
else
{
lean_inc(v_a_2753_);
lean_dec(v___x_2629_);
v___x_2755_ = lean_box(0);
v_isShared_2756_ = v_isSharedCheck_2760_;
goto v_resetjp_2754_;
}
v_resetjp_2754_:
{
lean_object* v___x_2758_; 
if (v_isShared_2756_ == 0)
{
v___x_2758_ = v___x_2755_;
goto v_reusejp_2757_;
}
else
{
lean_object* v_reuseFailAlloc_2759_; 
v_reuseFailAlloc_2759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2759_, 0, v_a_2753_);
v___x_2758_ = v_reuseFailAlloc_2759_;
goto v_reusejp_2757_;
}
v_reusejp_2757_:
{
return v___x_2758_;
}
}
}
}
else
{
lean_object* v_a_2761_; lean_object* v___x_2763_; uint8_t v_isShared_2764_; uint8_t v_isSharedCheck_2768_; 
lean_dec(v_recursorName_2592_);
lean_dec_ref(v_givenNames_2591_);
lean_dec(v_majorFVarId_2590_);
lean_dec_ref(v_a_2589_);
lean_dec(v_mvarId_2588_);
lean_dec_ref(v_val_2587_);
v_a_2761_ = lean_ctor_get(v___x_2628_, 0);
v_isSharedCheck_2768_ = !lean_is_exclusive(v___x_2628_);
if (v_isSharedCheck_2768_ == 0)
{
v___x_2763_ = v___x_2628_;
v_isShared_2764_ = v_isSharedCheck_2768_;
goto v_resetjp_2762_;
}
else
{
lean_inc(v_a_2761_);
lean_dec(v___x_2628_);
v___x_2763_ = lean_box(0);
v_isShared_2764_ = v_isSharedCheck_2768_;
goto v_resetjp_2762_;
}
v_resetjp_2762_:
{
lean_object* v___x_2766_; 
if (v_isShared_2764_ == 0)
{
v___x_2766_ = v___x_2763_;
goto v_reusejp_2765_;
}
else
{
lean_object* v_reuseFailAlloc_2767_; 
v_reuseFailAlloc_2767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2767_, 0, v_a_2761_);
v___x_2766_ = v_reuseFailAlloc_2767_;
goto v_reusejp_2765_;
}
v_reusejp_2765_:
{
return v___x_2766_;
}
}
}
v___jp_2610_:
{
size_t v_sz_2623_; lean_object* v___x_2624_; lean_object* v___f_2625_; lean_object* v___x_2626_; 
v_sz_2623_ = lean_array_size(v___y_2617_);
v___x_2624_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__3(v_sz_2623_, v___y_2618_, v___y_2617_);
v___f_2625_ = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4___lam__0___boxed), 14, 9);
lean_closure_set(v___f_2625_, 0, v___y_2611_);
lean_closure_set(v___f_2625_, 1, v___x_2609_);
lean_closure_set(v___f_2625_, 2, v___y_2614_);
lean_closure_set(v___f_2625_, 3, v_a_2589_);
lean_closure_set(v___f_2625_, 4, v___x_2624_);
lean_closure_set(v___f_2625_, 5, v_givenNames_2591_);
lean_closure_set(v___f_2625_, 6, v___y_2613_);
lean_closure_set(v___f_2625_, 7, v___y_2615_);
lean_closure_set(v___f_2625_, 8, v___y_2612_);
v___x_2626_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___redArg(v___y_2616_, v___f_2625_, v___y_2619_, v___y_2620_, v___y_2621_, v___y_2622_);
return v___x_2626_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4___boxed(lean_object* v_val_2769_, lean_object* v_mvarId_2770_, lean_object* v_a_2771_, lean_object* v_majorFVarId_2772_, lean_object* v_givenNames_2773_, lean_object* v_recursorName_2774_, lean_object* v_x_2775_, lean_object* v_x_2776_, lean_object* v_x_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_, lean_object* v___y_2780_, lean_object* v___y_2781_, lean_object* v___y_2782_){
_start:
{
lean_object* v_res_2783_; 
v_res_2783_ = l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4(v_val_2769_, v_mvarId_2770_, v_a_2771_, v_majorFVarId_2772_, v_givenNames_2773_, v_recursorName_2774_, v_x_2775_, v_x_2776_, v_x_2777_, v___y_2778_, v___y_2779_, v___y_2780_, v___y_2781_);
lean_dec(v___y_2781_);
lean_dec_ref(v___y_2780_);
lean_dec(v___y_2779_);
lean_dec_ref(v___y_2778_);
lean_dec(v_x_2777_);
return v_res_2783_;
}
}
static lean_object* _init_l_Lean_MVarId_induction___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2785_; lean_object* v___x_2786_; 
v___x_2785_ = ((lean_object*)(l_Lean_MVarId_induction___lam__0___closed__0));
v___x_2786_ = l_Lean_stringToMessageData(v___x_2785_);
return v___x_2786_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_induction___lam__0(lean_object* v___x_2787_, lean_object* v_mvarId_2788_, lean_object* v_majorFVarId_2789_, lean_object* v_recursorName_2790_, lean_object* v_givenNames_2791_, lean_object* v_cls_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_){
_start:
{
lean_object* v___y_2799_; lean_object* v___y_2800_; lean_object* v___y_2801_; lean_object* v___y_2802_; lean_object* v_toCold_2854_; lean_object* v_options_2855_; uint8_t v_hasTrace_2856_; 
v_toCold_2854_ = lean_ctor_get(v___y_2795_, 0);
v_options_2855_ = lean_ctor_get(v_toCold_2854_, 2);
v_hasTrace_2856_ = lean_ctor_get_uint8(v_options_2855_, sizeof(void*)*1);
if (v_hasTrace_2856_ == 0)
{
lean_dec(v_cls_2792_);
v___y_2799_ = v___y_2793_;
v___y_2800_ = v___y_2794_;
v___y_2801_ = v___y_2795_;
v___y_2802_ = v___y_2796_;
goto v___jp_2798_;
}
else
{
lean_object* v_inheritedTraceOptions_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; uint8_t v___x_2860_; 
v_inheritedTraceOptions_2857_ = lean_ctor_get(v_toCold_2854_, 11);
v___x_2858_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__4));
lean_inc(v_cls_2792_);
v___x_2859_ = l_Lean_Name_append(v___x_2858_, v_cls_2792_);
v___x_2860_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2857_, v_options_2855_, v___x_2859_);
lean_dec(v___x_2859_);
if (v___x_2860_ == 0)
{
lean_dec(v_cls_2792_);
v___y_2799_ = v___y_2793_;
v___y_2800_ = v___y_2794_;
v___y_2801_ = v___y_2795_;
v___y_2802_ = v___y_2796_;
goto v___jp_2798_;
}
else
{
lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; 
v___x_2861_ = lean_obj_once(&l_Lean_MVarId_induction___lam__0___closed__1, &l_Lean_MVarId_induction___lam__0___closed__1_once, _init_l_Lean_MVarId_induction___lam__0___closed__1);
lean_inc(v_mvarId_2788_);
v___x_2862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2862_, 0, v_mvarId_2788_);
v___x_2863_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2863_, 0, v___x_2861_);
lean_ctor_set(v___x_2863_, 1, v___x_2862_);
v___x_2864_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1(v_cls_2792_, v___x_2863_, v___y_2793_, v___y_2794_, v___y_2795_, v___y_2796_);
if (lean_obj_tag(v___x_2864_) == 0)
{
lean_dec_ref_known(v___x_2864_, 1);
v___y_2799_ = v___y_2793_;
v___y_2800_ = v___y_2794_;
v___y_2801_ = v___y_2795_;
v___y_2802_ = v___y_2796_;
goto v___jp_2798_;
}
else
{
lean_object* v_a_2865_; lean_object* v___x_2867_; uint8_t v_isShared_2868_; uint8_t v_isSharedCheck_2872_; 
lean_dec_ref(v_givenNames_2791_);
lean_dec(v_recursorName_2790_);
lean_dec(v_majorFVarId_2789_);
lean_dec(v_mvarId_2788_);
lean_dec_ref(v___x_2787_);
v_a_2865_ = lean_ctor_get(v___x_2864_, 0);
v_isSharedCheck_2872_ = !lean_is_exclusive(v___x_2864_);
if (v_isSharedCheck_2872_ == 0)
{
v___x_2867_ = v___x_2864_;
v_isShared_2868_ = v_isSharedCheck_2872_;
goto v_resetjp_2866_;
}
else
{
lean_inc(v_a_2865_);
lean_dec(v___x_2864_);
v___x_2867_ = lean_box(0);
v_isShared_2868_ = v_isSharedCheck_2872_;
goto v_resetjp_2866_;
}
v_resetjp_2866_:
{
lean_object* v___x_2870_; 
if (v_isShared_2868_ == 0)
{
v___x_2870_ = v___x_2867_;
goto v_reusejp_2869_;
}
else
{
lean_object* v_reuseFailAlloc_2871_; 
v_reuseFailAlloc_2871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2871_, 0, v_a_2865_);
v___x_2870_ = v_reuseFailAlloc_2871_;
goto v_reusejp_2869_;
}
v_reusejp_2869_:
{
return v___x_2870_;
}
}
}
}
}
v___jp_2798_:
{
lean_object* v___x_2803_; lean_object* v___x_2804_; 
v___x_2803_ = l_Lean_Name_mkStr1(v___x_2787_);
lean_inc(v___x_2803_);
lean_inc(v_mvarId_2788_);
v___x_2804_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_2788_, v___x_2803_, v___y_2799_, v___y_2800_, v___y_2801_, v___y_2802_);
if (lean_obj_tag(v___x_2804_) == 0)
{
lean_object* v___x_2805_; 
lean_dec_ref_known(v___x_2804_, 1);
lean_inc(v_majorFVarId_2789_);
v___x_2805_ = l_Lean_FVarId_getDecl___redArg(v_majorFVarId_2789_, v___y_2799_, v___y_2801_, v___y_2802_);
if (lean_obj_tag(v___x_2805_) == 0)
{
lean_object* v_a_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; 
v_a_2806_ = lean_ctor_get(v___x_2805_, 0);
lean_inc(v_a_2806_);
lean_dec_ref_known(v___x_2805_, 1);
v___x_2807_ = lean_box(0);
lean_inc(v_recursorName_2790_);
v___x_2808_ = l_Lean_Meta_mkRecursorInfo(v_recursorName_2790_, v___x_2807_, v___y_2799_, v___y_2800_, v___y_2801_, v___y_2802_);
if (lean_obj_tag(v___x_2808_) == 0)
{
lean_object* v_a_2809_; lean_object* v_typeName_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; 
v_a_2809_ = lean_ctor_get(v___x_2808_, 0);
lean_inc(v_a_2809_);
lean_dec_ref_known(v___x_2808_, 1);
v_typeName_2810_ = lean_ctor_get(v_a_2809_, 1);
v___x_2811_ = l_Lean_LocalDecl_type(v_a_2806_);
lean_dec(v_a_2806_);
lean_inc_ref(v___x_2811_);
v___x_2812_ = l_Lean_Meta_whnfUntil(v___x_2811_, v_typeName_2810_, v___y_2799_, v___y_2800_, v___y_2801_, v___y_2802_);
if (lean_obj_tag(v___x_2812_) == 0)
{
lean_object* v_a_2813_; 
v_a_2813_ = lean_ctor_get(v___x_2812_, 0);
lean_inc(v_a_2813_);
lean_dec_ref_known(v___x_2812_, 1);
if (lean_obj_tag(v_a_2813_) == 1)
{
lean_object* v_val_2814_; lean_object* v_dummy_2815_; lean_object* v_nargs_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; 
lean_dec_ref(v___x_2811_);
lean_dec(v___x_2803_);
v_val_2814_ = lean_ctor_get(v_a_2813_, 0);
lean_inc_n(v_val_2814_, 2);
lean_dec_ref_known(v_a_2813_, 1);
v_dummy_2815_ = lean_obj_once(&l_Lean_Meta_getMajorTypeIndices___closed__0, &l_Lean_Meta_getMajorTypeIndices___closed__0_once, _init_l_Lean_Meta_getMajorTypeIndices___closed__0);
v_nargs_2816_ = l_Lean_Expr_getAppNumArgs(v_val_2814_);
lean_inc(v_nargs_2816_);
v___x_2817_ = lean_mk_array(v_nargs_2816_, v_dummy_2815_);
v___x_2818_ = lean_unsigned_to_nat(1u);
v___x_2819_ = lean_nat_sub(v_nargs_2816_, v___x_2818_);
lean_dec(v_nargs_2816_);
v___x_2820_ = l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4(v_val_2814_, v_mvarId_2788_, v_a_2809_, v_majorFVarId_2789_, v_givenNames_2791_, v_recursorName_2790_, v_val_2814_, v___x_2817_, v___x_2819_, v___y_2799_, v___y_2800_, v___y_2801_, v___y_2802_);
lean_dec(v___x_2819_);
return v___x_2820_;
}
else
{
lean_object* v___x_2821_; 
lean_dec(v_a_2813_);
lean_dec(v_a_2809_);
lean_dec_ref(v_givenNames_2791_);
lean_dec(v_recursorName_2790_);
lean_dec(v_majorFVarId_2789_);
v___x_2821_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg(v___x_2803_, v_mvarId_2788_, v___x_2811_, v___y_2799_, v___y_2800_, v___y_2801_, v___y_2802_);
return v___x_2821_;
}
}
else
{
lean_object* v_a_2822_; lean_object* v___x_2824_; uint8_t v_isShared_2825_; uint8_t v_isSharedCheck_2829_; 
lean_dec_ref(v___x_2811_);
lean_dec(v_a_2809_);
lean_dec(v___x_2803_);
lean_dec_ref(v_givenNames_2791_);
lean_dec(v_recursorName_2790_);
lean_dec(v_majorFVarId_2789_);
lean_dec(v_mvarId_2788_);
v_a_2822_ = lean_ctor_get(v___x_2812_, 0);
v_isSharedCheck_2829_ = !lean_is_exclusive(v___x_2812_);
if (v_isSharedCheck_2829_ == 0)
{
v___x_2824_ = v___x_2812_;
v_isShared_2825_ = v_isSharedCheck_2829_;
goto v_resetjp_2823_;
}
else
{
lean_inc(v_a_2822_);
lean_dec(v___x_2812_);
v___x_2824_ = lean_box(0);
v_isShared_2825_ = v_isSharedCheck_2829_;
goto v_resetjp_2823_;
}
v_resetjp_2823_:
{
lean_object* v___x_2827_; 
if (v_isShared_2825_ == 0)
{
v___x_2827_ = v___x_2824_;
goto v_reusejp_2826_;
}
else
{
lean_object* v_reuseFailAlloc_2828_; 
v_reuseFailAlloc_2828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2828_, 0, v_a_2822_);
v___x_2827_ = v_reuseFailAlloc_2828_;
goto v_reusejp_2826_;
}
v_reusejp_2826_:
{
return v___x_2827_;
}
}
}
}
else
{
lean_object* v_a_2830_; lean_object* v___x_2832_; uint8_t v_isShared_2833_; uint8_t v_isSharedCheck_2837_; 
lean_dec(v_a_2806_);
lean_dec(v___x_2803_);
lean_dec_ref(v_givenNames_2791_);
lean_dec(v_recursorName_2790_);
lean_dec(v_majorFVarId_2789_);
lean_dec(v_mvarId_2788_);
v_a_2830_ = lean_ctor_get(v___x_2808_, 0);
v_isSharedCheck_2837_ = !lean_is_exclusive(v___x_2808_);
if (v_isSharedCheck_2837_ == 0)
{
v___x_2832_ = v___x_2808_;
v_isShared_2833_ = v_isSharedCheck_2837_;
goto v_resetjp_2831_;
}
else
{
lean_inc(v_a_2830_);
lean_dec(v___x_2808_);
v___x_2832_ = lean_box(0);
v_isShared_2833_ = v_isSharedCheck_2837_;
goto v_resetjp_2831_;
}
v_resetjp_2831_:
{
lean_object* v___x_2835_; 
if (v_isShared_2833_ == 0)
{
v___x_2835_ = v___x_2832_;
goto v_reusejp_2834_;
}
else
{
lean_object* v_reuseFailAlloc_2836_; 
v_reuseFailAlloc_2836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2836_, 0, v_a_2830_);
v___x_2835_ = v_reuseFailAlloc_2836_;
goto v_reusejp_2834_;
}
v_reusejp_2834_:
{
return v___x_2835_;
}
}
}
}
else
{
lean_object* v_a_2838_; lean_object* v___x_2840_; uint8_t v_isShared_2841_; uint8_t v_isSharedCheck_2845_; 
lean_dec(v___x_2803_);
lean_dec_ref(v_givenNames_2791_);
lean_dec(v_recursorName_2790_);
lean_dec(v_majorFVarId_2789_);
lean_dec(v_mvarId_2788_);
v_a_2838_ = lean_ctor_get(v___x_2805_, 0);
v_isSharedCheck_2845_ = !lean_is_exclusive(v___x_2805_);
if (v_isSharedCheck_2845_ == 0)
{
v___x_2840_ = v___x_2805_;
v_isShared_2841_ = v_isSharedCheck_2845_;
goto v_resetjp_2839_;
}
else
{
lean_inc(v_a_2838_);
lean_dec(v___x_2805_);
v___x_2840_ = lean_box(0);
v_isShared_2841_ = v_isSharedCheck_2845_;
goto v_resetjp_2839_;
}
v_resetjp_2839_:
{
lean_object* v___x_2843_; 
if (v_isShared_2841_ == 0)
{
v___x_2843_ = v___x_2840_;
goto v_reusejp_2842_;
}
else
{
lean_object* v_reuseFailAlloc_2844_; 
v_reuseFailAlloc_2844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2844_, 0, v_a_2838_);
v___x_2843_ = v_reuseFailAlloc_2844_;
goto v_reusejp_2842_;
}
v_reusejp_2842_:
{
return v___x_2843_;
}
}
}
}
else
{
lean_object* v_a_2846_; lean_object* v___x_2848_; uint8_t v_isShared_2849_; uint8_t v_isSharedCheck_2853_; 
lean_dec(v___x_2803_);
lean_dec_ref(v_givenNames_2791_);
lean_dec(v_recursorName_2790_);
lean_dec(v_majorFVarId_2789_);
lean_dec(v_mvarId_2788_);
v_a_2846_ = lean_ctor_get(v___x_2804_, 0);
v_isSharedCheck_2853_ = !lean_is_exclusive(v___x_2804_);
if (v_isSharedCheck_2853_ == 0)
{
v___x_2848_ = v___x_2804_;
v_isShared_2849_ = v_isSharedCheck_2853_;
goto v_resetjp_2847_;
}
else
{
lean_inc(v_a_2846_);
lean_dec(v___x_2804_);
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
}
LEAN_EXPORT lean_object* l_Lean_MVarId_induction___lam__0___boxed(lean_object* v___x_2873_, lean_object* v_mvarId_2874_, lean_object* v_majorFVarId_2875_, lean_object* v_recursorName_2876_, lean_object* v_givenNames_2877_, lean_object* v_cls_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_){
_start:
{
lean_object* v_res_2884_; 
v_res_2884_ = l_Lean_MVarId_induction___lam__0(v___x_2873_, v_mvarId_2874_, v_majorFVarId_2875_, v_recursorName_2876_, v_givenNames_2877_, v_cls_2878_, v___y_2879_, v___y_2880_, v___y_2881_, v___y_2882_);
lean_dec(v___y_2882_);
lean_dec_ref(v___y_2881_);
lean_dec(v___y_2880_);
lean_dec_ref(v___y_2879_);
return v_res_2884_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_induction(lean_object* v_mvarId_2885_, lean_object* v_majorFVarId_2886_, lean_object* v_recursorName_2887_, lean_object* v_givenNames_2888_, lean_object* v_a_2889_, lean_object* v_a_2890_, lean_object* v_a_2891_, lean_object* v_a_2892_){
_start:
{
lean_object* v___x_2894_; lean_object* v_cls_2895_; lean_object* v___f_2896_; lean_object* v___x_2897_; 
v___x_2894_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__0));
v_cls_2895_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__2));
lean_inc(v_mvarId_2885_);
v___f_2896_ = lean_alloc_closure((void*)(l_Lean_MVarId_induction___lam__0___boxed), 11, 6);
lean_closure_set(v___f_2896_, 0, v___x_2894_);
lean_closure_set(v___f_2896_, 1, v_mvarId_2885_);
lean_closure_set(v___f_2896_, 2, v_majorFVarId_2886_);
lean_closure_set(v___f_2896_, 3, v_recursorName_2887_);
lean_closure_set(v___f_2896_, 4, v_givenNames_2888_);
lean_closure_set(v___f_2896_, 5, v_cls_2895_);
v___x_2897_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___redArg(v_mvarId_2885_, v___f_2896_, v_a_2889_, v_a_2890_, v_a_2891_, v_a_2892_);
return v___x_2897_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_induction___boxed(lean_object* v_mvarId_2898_, lean_object* v_majorFVarId_2899_, lean_object* v_recursorName_2900_, lean_object* v_givenNames_2901_, lean_object* v_a_2902_, lean_object* v_a_2903_, lean_object* v_a_2904_, lean_object* v_a_2905_, lean_object* v_a_2906_){
_start:
{
lean_object* v_res_2907_; 
v_res_2907_ = l_Lean_MVarId_induction(v_mvarId_2898_, v_majorFVarId_2899_, v_recursorName_2900_, v_givenNames_2901_, v_a_2902_, v_a_2903_, v_a_2904_, v_a_2905_);
lean_dec(v_a_2905_);
lean_dec_ref(v_a_2904_);
lean_dec(v_a_2903_);
lean_dec_ref(v_a_2902_);
return v_res_2907_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; 
v___x_2955_ = lean_unsigned_to_nat(2221195325u);
v___x_2956_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_));
v___x_2957_ = l_Lean_Name_num___override(v___x_2956_, v___x_2955_);
return v___x_2957_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; 
v___x_2959_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_));
v___x_2960_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_);
v___x_2961_ = l_Lean_Name_str___override(v___x_2960_, v___x_2959_);
return v___x_2961_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; 
v___x_2963_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_));
v___x_2964_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_);
v___x_2965_ = l_Lean_Name_str___override(v___x_2964_, v___x_2963_);
return v___x_2965_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; 
v___x_2966_ = lean_unsigned_to_nat(2u);
v___x_2967_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_);
v___x_2968_ = l_Lean_Name_num___override(v___x_2967_, v___x_2966_);
return v___x_2968_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2970_; uint8_t v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; 
v___x_2970_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__2));
v___x_2971_ = 0;
v___x_2972_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_);
v___x_2973_ = l_Lean_registerTraceClass(v___x_2970_, v___x_2971_, v___x_2972_);
return v___x_2973_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2____boxed(lean_object* v_a_2974_){
_start:
{
lean_object* v_res_2975_; 
v_res_2975_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_();
return v_res_2975_;
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
