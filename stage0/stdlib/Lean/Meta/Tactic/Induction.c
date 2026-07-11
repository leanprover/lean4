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
uint8_t lean_bool_not(uint8_t);
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
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_MVarId_tryClear(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_introNCore(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_FVarSubst_insert(lean_object*, lean_object*, lean_object*);
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
lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
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
LEAN_EXPORT uint8_t l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___lam__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__0_value;
static lean_once_cell_t l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__1;
static lean_once_cell_t l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__2;
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
lean_object* v___f_134_; lean_object* v___x_8805__overap_135_; lean_object* v___x_136_; 
v___f_134_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__4___closed__0));
v___x_8805__overap_135_ = lean_panic_fn_borrowed(v___f_134_, v_msg_128_);
lean_inc(v___y_132_);
lean_inc_ref(v___y_131_);
lean_inc(v___y_130_);
lean_inc_ref(v___y_129_);
v___x_136_ = lean_apply_5(v___x_8805__overap_135_, v___y_129_, v___y_130_, v___y_131_, v___y_132_, lean_box(0));
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
size_t v_x_10046__boxed_363_; size_t v_x_10047__boxed_364_; lean_object* v_res_365_; 
v_x_10046__boxed_363_ = lean_unbox_usize(v_x_359_);
lean_dec(v_x_359_);
v_x_10047__boxed_364_ = lean_unbox_usize(v_x_360_);
lean_dec(v_x_360_);
v_res_365_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2___redArg(v_x_358_, v_x_10046__boxed_363_, v_x_10047__boxed_364_, v_x_361_, v_x_362_);
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
lean_object* v___x_377_; lean_object* v_mctx_378_; lean_object* v_cache_379_; lean_object* v_zetaDeltaFVarIds_380_; lean_object* v_postponed_381_; lean_object* v_diag_382_; lean_object* v___x_384_; uint8_t v_isShared_385_; uint8_t v_isSharedCheck_410_; 
v___x_377_ = lean_st_ref_take(v___y_375_);
v_mctx_378_ = lean_ctor_get(v___x_377_, 0);
v_cache_379_ = lean_ctor_get(v___x_377_, 1);
v_zetaDeltaFVarIds_380_ = lean_ctor_get(v___x_377_, 2);
v_postponed_381_ = lean_ctor_get(v___x_377_, 3);
v_diag_382_ = lean_ctor_get(v___x_377_, 4);
v_isSharedCheck_410_ = !lean_is_exclusive(v___x_377_);
if (v_isSharedCheck_410_ == 0)
{
v___x_384_ = v___x_377_;
v_isShared_385_ = v_isSharedCheck_410_;
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
v_isShared_385_ = v_isSharedCheck_410_;
goto v_resetjp_383_;
}
v_resetjp_383_:
{
lean_object* v_depth_386_; lean_object* v_levelAssignDepth_387_; lean_object* v_lmvarCounter_388_; lean_object* v_mvarCounter_389_; lean_object* v_lDecls_390_; lean_object* v_decls_391_; lean_object* v_userNames_392_; lean_object* v_lAssignment_393_; lean_object* v_eAssignment_394_; lean_object* v_dAssignment_395_; lean_object* v___x_397_; uint8_t v_isShared_398_; uint8_t v_isSharedCheck_409_; 
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
v_isSharedCheck_409_ = !lean_is_exclusive(v_mctx_378_);
if (v_isSharedCheck_409_ == 0)
{
v___x_397_ = v_mctx_378_;
v_isShared_398_ = v_isSharedCheck_409_;
goto v_resetjp_396_;
}
else
{
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
v___x_397_ = lean_box(0);
v_isShared_398_ = v_isSharedCheck_409_;
goto v_resetjp_396_;
}
v_resetjp_396_:
{
lean_object* v___x_399_; lean_object* v___x_401_; 
v___x_399_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0___redArg(v_eAssignment_394_, v_mvarId_373_, v_val_374_);
if (v_isShared_398_ == 0)
{
lean_ctor_set(v___x_397_, 8, v___x_399_);
v___x_401_ = v___x_397_;
goto v_reusejp_400_;
}
else
{
lean_object* v_reuseFailAlloc_408_; 
v_reuseFailAlloc_408_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_408_, 0, v_depth_386_);
lean_ctor_set(v_reuseFailAlloc_408_, 1, v_levelAssignDepth_387_);
lean_ctor_set(v_reuseFailAlloc_408_, 2, v_lmvarCounter_388_);
lean_ctor_set(v_reuseFailAlloc_408_, 3, v_mvarCounter_389_);
lean_ctor_set(v_reuseFailAlloc_408_, 4, v_lDecls_390_);
lean_ctor_set(v_reuseFailAlloc_408_, 5, v_decls_391_);
lean_ctor_set(v_reuseFailAlloc_408_, 6, v_userNames_392_);
lean_ctor_set(v_reuseFailAlloc_408_, 7, v_lAssignment_393_);
lean_ctor_set(v_reuseFailAlloc_408_, 8, v___x_399_);
lean_ctor_set(v_reuseFailAlloc_408_, 9, v_dAssignment_395_);
v___x_401_ = v_reuseFailAlloc_408_;
goto v_reusejp_400_;
}
v_reusejp_400_:
{
lean_object* v___x_403_; 
if (v_isShared_385_ == 0)
{
lean_ctor_set(v___x_384_, 0, v___x_401_);
v___x_403_ = v___x_384_;
goto v_reusejp_402_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_407_, 0, v___x_401_);
lean_ctor_set(v_reuseFailAlloc_407_, 1, v_cache_379_);
lean_ctor_set(v_reuseFailAlloc_407_, 2, v_zetaDeltaFVarIds_380_);
lean_ctor_set(v_reuseFailAlloc_407_, 3, v_postponed_381_);
lean_ctor_set(v_reuseFailAlloc_407_, 4, v_diag_382_);
v___x_403_ = v_reuseFailAlloc_407_;
goto v_reusejp_402_;
}
v_reusejp_402_:
{
lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; 
v___x_404_ = lean_st_ref_set(v___y_375_, v___x_403_);
v___x_405_ = lean_box(0);
v___x_406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_406_, 0, v___x_405_);
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
lean_object* v___x_422_; lean_object* v_env_423_; lean_object* v___x_424_; lean_object* v_mctx_425_; lean_object* v_lctx_426_; lean_object* v_options_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; 
v___x_422_ = lean_st_ref_get(v___y_420_);
v_env_423_ = lean_ctor_get(v___x_422_, 0);
lean_inc_ref(v_env_423_);
lean_dec(v___x_422_);
v___x_424_ = lean_st_ref_get(v___y_418_);
v_mctx_425_ = lean_ctor_get(v___x_424_, 0);
lean_inc_ref(v_mctx_425_);
lean_dec(v___x_424_);
v_lctx_426_ = lean_ctor_get(v___y_417_, 2);
v_options_427_ = lean_ctor_get(v___y_419_, 2);
lean_inc_ref(v_options_427_);
lean_inc_ref(v_lctx_426_);
v___x_428_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_428_, 0, v_env_423_);
lean_ctor_set(v___x_428_, 1, v_mctx_425_);
lean_ctor_set(v___x_428_, 2, v_lctx_426_);
lean_ctor_set(v___x_428_, 3, v_options_427_);
v___x_429_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_429_, 0, v___x_428_);
lean_ctor_set(v___x_429_, 1, v_msgData_416_);
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
v_ref_450_ = lean_ctor_get(v___y_447_, 5);
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
lean_object* v___x_474_; double v___x_475_; uint8_t v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_484_; 
v___x_474_ = lean_box(0);
v___x_475_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1___closed__0);
v___x_476_ = 0;
v___x_477_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1___closed__1));
v___x_478_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_478_, 0, v_cls_443_);
lean_ctor_set(v___x_478_, 1, v___x_474_);
lean_ctor_set(v___x_478_, 2, v___x_477_);
lean_ctor_set_float(v___x_478_, sizeof(void*)*3, v___x_475_);
lean_ctor_set_float(v___x_478_, sizeof(void*)*3 + 8, v___x_475_);
lean_ctor_set_uint8(v___x_478_, sizeof(void*)*3 + 16, v___x_476_);
v___x_479_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1___closed__2));
v___x_480_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_480_, 0, v___x_478_);
lean_ctor_set(v___x_480_, 1, v_a_452_);
lean_ctor_set(v___x_480_, 2, v___x_479_);
lean_inc(v_ref_450_);
v___x_481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_481_, 0, v_ref_450_);
lean_ctor_set(v___x_481_, 1, v___x_480_);
v___x_482_ = l_Lean_PersistentArray_push___redArg(v_traces_470_, v___x_481_);
if (v_isShared_473_ == 0)
{
lean_ctor_set(v___x_472_, 0, v___x_482_);
v___x_484_ = v___x_472_;
goto v_reusejp_483_;
}
else
{
lean_object* v_reuseFailAlloc_493_; 
v_reuseFailAlloc_493_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_493_, 0, v___x_482_);
lean_ctor_set_uint64(v_reuseFailAlloc_493_, sizeof(void*)*1, v_tid_469_);
v___x_484_ = v_reuseFailAlloc_493_;
goto v_reusejp_483_;
}
v_reusejp_483_:
{
lean_object* v___x_486_; 
if (v_isShared_468_ == 0)
{
lean_ctor_set(v___x_467_, 4, v___x_484_);
v___x_486_ = v___x_467_;
goto v_reusejp_485_;
}
else
{
lean_object* v_reuseFailAlloc_492_; 
v_reuseFailAlloc_492_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_492_, 0, v_env_458_);
lean_ctor_set(v_reuseFailAlloc_492_, 1, v_nextMacroScope_459_);
lean_ctor_set(v_reuseFailAlloc_492_, 2, v_ngen_460_);
lean_ctor_set(v_reuseFailAlloc_492_, 3, v_auxDeclNGen_461_);
lean_ctor_set(v_reuseFailAlloc_492_, 4, v___x_484_);
lean_ctor_set(v_reuseFailAlloc_492_, 5, v_cache_462_);
lean_ctor_set(v_reuseFailAlloc_492_, 6, v_messages_463_);
lean_ctor_set(v_reuseFailAlloc_492_, 7, v_infoState_464_);
lean_ctor_set(v_reuseFailAlloc_492_, 8, v_snapshotTasks_465_);
v___x_486_ = v_reuseFailAlloc_492_;
goto v_reusejp_485_;
}
v_reusejp_485_:
{
lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_490_; 
v___x_487_ = lean_st_ref_set(v___y_448_, v___x_486_);
v___x_488_ = lean_box(0);
if (v_isShared_455_ == 0)
{
lean_ctor_set(v___x_454_, 0, v___x_488_);
v___x_490_ = v___x_454_;
goto v_reusejp_489_;
}
else
{
lean_object* v_reuseFailAlloc_491_; 
v_reuseFailAlloc_491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_491_, 0, v___x_488_);
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
lean_object* v___y_574_; lean_object* v___y_575_; lean_object* v___y_576_; lean_object* v___y_577_; lean_object* v___y_630_; lean_object* v___y_631_; lean_object* v___y_632_; uint8_t v___y_633_; lean_object* v___y_634_; lean_object* v___y_635_; lean_object* v___y_636_; lean_object* v___y_637_; lean_object* v___y_638_; lean_object* v___y_639_; uint8_t v___y_640_; lean_object* v___y_641_; lean_object* v___y_642_; lean_object* v___y_643_; lean_object* v___y_644_; lean_object* v___y_695_; uint8_t v___y_696_; lean_object* v_fst_697_; lean_object* v_snd_698_; lean_object* v___y_715_; uint8_t v___y_716_; lean_object* v___y_717_; lean_object* v___x_729_; 
v___x_729_ = l_Lean_Meta_whnfForall(v_recursorType_565_, v_a_568_, v_a_569_, v_a_570_, v_a_571_);
if (lean_obj_tag(v___x_729_) == 0)
{
lean_object* v_a_730_; lean_object* v___y_732_; uint8_t v___y_733_; lean_object* v___y_734_; lean_object* v___y_735_; lean_object* v___y_736_; lean_object* v___y_737_; lean_object* v___y_738_; lean_object* v___y_739_; uint8_t v___y_740_; lean_object* v___y_741_; lean_object* v___y_742_; lean_object* v___y_743_; lean_object* v___y_744_; lean_object* v___y_745_; lean_object* v___y_787_; uint8_t v___y_788_; lean_object* v___y_789_; lean_object* v___y_790_; uint8_t v___y_791_; lean_object* v___y_792_; lean_object* v___y_793_; lean_object* v___y_794_; lean_object* v___y_795_; lean_object* v___y_796_; lean_object* v___y_808_; lean_object* v___y_809_; lean_object* v___y_810_; lean_object* v___y_811_; uint8_t v___y_812_; lean_object* v___y_813_; lean_object* v___y_814_; lean_object* v___y_815_; uint8_t v___y_816_; lean_object* v___y_886_; lean_object* v___y_887_; lean_object* v___y_888_; uint8_t v___y_889_; lean_object* v___y_890_; lean_object* v___y_891_; lean_object* v___y_892_; uint8_t v___y_893_; lean_object* v___y_894_; uint8_t v___y_900_; lean_object* v___y_901_; lean_object* v___y_902_; lean_object* v___y_903_; lean_object* v___y_904_; lean_object* v___y_905_; uint8_t v___y_917_; uint8_t v___x_964_; 
v_a_730_ = lean_ctor_get(v___x_729_, 0);
lean_inc(v_a_730_);
lean_dec_ref_known(v___x_729_, 1);
v___x_964_ = l_Lean_Expr_isForall(v_a_730_);
if (v___x_964_ == 0)
{
v___y_917_ = v___x_964_;
goto v___jp_916_;
}
else
{
lean_object* v_numArgs_965_; uint8_t v___x_966_; 
v_numArgs_965_ = lean_ctor_get(v_recursorInfo_555_, 3);
v___x_966_ = lean_nat_dec_lt(v_pos_562_, v_numArgs_965_);
v___y_917_ = v___x_966_;
goto v___jp_916_;
}
v___jp_731_:
{
lean_object* v___x_746_; 
v___x_746_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___y_735_, v___y_734_, v___y_737_, v___y_743_, v___y_732_, v___y_742_);
if (lean_obj_tag(v___x_746_) == 0)
{
lean_object* v_a_747_; lean_object* v___x_748_; 
v_a_747_ = lean_ctor_get(v___x_746_, 0);
lean_inc(v_a_747_);
lean_dec_ref_known(v___x_746_, 1);
lean_inc(v_mvarId_553_);
v___x_748_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTypeBody(v_mvarId_553_, v_a_730_, v_a_747_, v___y_737_, v___y_743_, v___y_732_, v___y_742_);
if (lean_obj_tag(v___x_748_) == 0)
{
lean_object* v_options_749_; lean_object* v_a_750_; lean_object* v_inheritedTraceOptions_751_; uint8_t v_hasTrace_752_; lean_object* v___x_753_; 
v_options_749_ = lean_ctor_get(v___y_732_, 2);
v_a_750_ = lean_ctor_get(v___x_748_, 0);
lean_inc(v_a_750_);
lean_dec_ref_known(v___x_748_, 1);
v_inheritedTraceOptions_751_ = lean_ctor_get(v___y_732_, 13);
v_hasTrace_752_ = lean_ctor_get_uint8(v_options_749_, sizeof(void*)*1);
lean_inc(v_a_747_);
v___x_753_ = l_Lean_Expr_app___override(v_recursor_564_, v_a_747_);
if (v_hasTrace_752_ == 0)
{
v___y_630_ = v___y_745_;
v___y_631_ = v_a_747_;
v___y_632_ = v___x_753_;
v___y_633_ = v___y_733_;
v___y_634_ = v___y_736_;
v___y_635_ = v_a_750_;
v___y_636_ = v___y_738_;
v___y_637_ = v___y_739_;
v___y_638_ = v___y_744_;
v___y_639_ = v___y_741_;
v___y_640_ = v___y_740_;
v___y_641_ = v___y_737_;
v___y_642_ = v___y_743_;
v___y_643_ = v___y_732_;
v___y_644_ = v___y_742_;
goto v___jp_629_;
}
else
{
lean_object* v___x_754_; lean_object* v___x_755_; uint8_t v___x_756_; 
v___x_754_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__2));
v___x_755_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5);
v___x_756_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_751_, v_options_749_, v___x_755_);
if (v___x_756_ == 0)
{
v___y_630_ = v___y_745_;
v___y_631_ = v_a_747_;
v___y_632_ = v___x_753_;
v___y_633_ = v___y_733_;
v___y_634_ = v___y_736_;
v___y_635_ = v_a_750_;
v___y_636_ = v___y_738_;
v___y_637_ = v___y_739_;
v___y_638_ = v___y_744_;
v___y_639_ = v___y_741_;
v___y_640_ = v___y_740_;
v___y_641_ = v___y_737_;
v___y_642_ = v___y_743_;
v___y_643_ = v___y_732_;
v___y_644_ = v___y_742_;
goto v___jp_629_;
}
else
{
lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; 
v___x_757_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__11, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__11_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__11);
v___x_758_ = l_Lean_Expr_fvarId_x21(v_major_557_);
v___x_759_ = l_Lean_MessageData_ofName(v___x_758_);
v___x_760_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_760_, 0, v___x_757_);
lean_ctor_set(v___x_760_, 1, v___x_759_);
v___x_761_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1(v___x_754_, v___x_760_, v___y_737_, v___y_743_, v___y_732_, v___y_742_);
if (lean_obj_tag(v___x_761_) == 0)
{
lean_dec_ref_known(v___x_761_, 1);
v___y_630_ = v___y_745_;
v___y_631_ = v_a_747_;
v___y_632_ = v___x_753_;
v___y_633_ = v___y_733_;
v___y_634_ = v___y_736_;
v___y_635_ = v_a_750_;
v___y_636_ = v___y_738_;
v___y_637_ = v___y_739_;
v___y_638_ = v___y_744_;
v___y_639_ = v___y_741_;
v___y_640_ = v___y_740_;
v___y_641_ = v___y_737_;
v___y_642_ = v___y_743_;
v___y_643_ = v___y_732_;
v___y_644_ = v___y_742_;
goto v___jp_629_;
}
else
{
lean_object* v_a_762_; lean_object* v___x_764_; uint8_t v_isShared_765_; uint8_t v_isSharedCheck_769_; 
lean_dec_ref(v___x_753_);
lean_dec(v_a_750_);
lean_dec(v_a_747_);
lean_dec_ref(v___y_745_);
lean_dec(v___y_744_);
lean_dec(v___y_739_);
lean_dec(v___y_738_);
lean_dec(v___y_736_);
lean_dec_ref(v_subgoals_567_);
lean_dec(v_minorIdx_563_);
lean_dec(v_pos_562_);
lean_dec(v_baseSubst_559_);
lean_dec_ref(v_major_557_);
lean_dec(v_mvarId_553_);
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
lean_dec(v_a_747_);
lean_dec_ref(v___y_745_);
lean_dec(v___y_744_);
lean_dec(v___y_739_);
lean_dec(v___y_738_);
lean_dec(v___y_736_);
lean_dec_ref(v_subgoals_567_);
lean_dec_ref(v_recursor_564_);
lean_dec(v_minorIdx_563_);
lean_dec(v_pos_562_);
lean_dec(v_baseSubst_559_);
lean_dec_ref(v_major_557_);
lean_dec(v_mvarId_553_);
v_a_770_ = lean_ctor_get(v___x_748_, 0);
v_isSharedCheck_777_ = !lean_is_exclusive(v___x_748_);
if (v_isSharedCheck_777_ == 0)
{
v___x_772_ = v___x_748_;
v_isShared_773_ = v_isSharedCheck_777_;
goto v_resetjp_771_;
}
else
{
lean_inc(v_a_770_);
lean_dec(v___x_748_);
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
lean_dec_ref(v___y_745_);
lean_dec(v___y_744_);
lean_dec(v___y_739_);
lean_dec(v___y_738_);
lean_dec(v___y_736_);
lean_dec(v_a_730_);
lean_dec_ref(v_subgoals_567_);
lean_dec_ref(v_recursor_564_);
lean_dec(v_minorIdx_563_);
lean_dec(v_pos_562_);
lean_dec(v_baseSubst_559_);
lean_dec_ref(v_major_557_);
lean_dec(v_mvarId_553_);
v_a_778_ = lean_ctor_get(v___x_746_, 0);
v_isSharedCheck_785_ = !lean_is_exclusive(v___x_746_);
if (v_isSharedCheck_785_ == 0)
{
v___x_780_ = v___x_746_;
v_isShared_781_ = v_isSharedCheck_785_;
goto v_resetjp_779_;
}
else
{
lean_inc(v_a_778_);
lean_dec(v___x_746_);
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
lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; uint8_t v___x_803_; 
v___x_797_ = lean_nat_sub(v___y_787_, v_initialArity_560_);
lean_dec(v___y_787_);
v___x_798_ = lean_array_get_size(v_reverted_556_);
v___x_799_ = lean_array_get_size(v_indices_558_);
v___x_800_ = lean_nat_sub(v___x_798_, v___x_799_);
v___x_801_ = lean_nat_sub(v___x_800_, v___y_792_);
lean_dec(v___x_800_);
v___x_802_ = lean_array_get_size(v_givenNames_554_);
v___x_803_ = lean_nat_dec_lt(v_minorIdx_563_, v___x_802_);
if (v___x_803_ == 0)
{
lean_object* v___x_804_; lean_object* v___x_805_; 
v___x_804_ = lean_box(0);
v___x_805_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_805_, 0, v___x_804_);
lean_ctor_set_uint8(v___x_805_, sizeof(void*)*1, v___y_791_);
v___y_732_ = v___y_795_;
v___y_733_ = v___y_788_;
v___y_734_ = v___y_789_;
v___y_735_ = v___y_790_;
v___y_736_ = v___x_797_;
v___y_737_ = v___y_793_;
v___y_738_ = v___x_798_;
v___y_739_ = v___x_799_;
v___y_740_ = v___y_791_;
v___y_741_ = v___y_792_;
v___y_742_ = v___y_796_;
v___y_743_ = v___y_794_;
v___y_744_ = v___x_801_;
v___y_745_ = v___x_805_;
goto v___jp_731_;
}
else
{
lean_object* v___x_806_; 
v___x_806_ = lean_array_fget_borrowed(v_givenNames_554_, v_minorIdx_563_);
lean_inc(v___x_806_);
v___y_732_ = v___y_795_;
v___y_733_ = v___y_788_;
v___y_734_ = v___y_789_;
v___y_735_ = v___y_790_;
v___y_736_ = v___x_797_;
v___y_737_ = v___y_793_;
v___y_738_ = v___x_798_;
v___y_739_ = v___x_799_;
v___y_740_ = v___y_791_;
v___y_741_ = v___y_792_;
v___y_742_ = v___y_796_;
v___y_743_ = v___y_794_;
v___y_744_ = v___x_801_;
v___y_745_ = v___x_806_;
goto v___jp_731_;
}
}
v___jp_807_:
{
if (v___y_816_ == 0)
{
lean_object* v___x_817_; uint8_t v___x_818_; 
lean_inc_ref(v___y_814_);
v___x_817_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTargetArity(v___y_814_);
v___x_818_ = lean_nat_dec_lt(v___x_817_, v_initialArity_560_);
if (v___x_818_ == 0)
{
v___y_787_ = v___x_817_;
v___y_788_ = v___y_812_;
v___y_789_ = v___y_813_;
v___y_790_ = v___y_814_;
v___y_791_ = v___y_816_;
v___y_792_ = v___y_815_;
v___y_793_ = v___y_808_;
v___y_794_ = v___y_811_;
v___y_795_ = v___y_810_;
v___y_796_ = v___y_809_;
goto v___jp_786_;
}
else
{
lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; 
v___x_819_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1));
v___x_820_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9);
lean_inc(v_mvarId_553_);
v___x_821_ = l_Lean_Meta_throwTacticEx___redArg(v___x_819_, v_mvarId_553_, v___x_820_, v___y_808_, v___y_811_, v___y_810_, v___y_809_);
if (lean_obj_tag(v___x_821_) == 0)
{
lean_dec_ref_known(v___x_821_, 1);
v___y_787_ = v___x_817_;
v___y_788_ = v___y_812_;
v___y_789_ = v___y_813_;
v___y_790_ = v___y_814_;
v___y_791_ = v___y_816_;
v___y_792_ = v___y_815_;
v___y_793_ = v___y_808_;
v___y_794_ = v___y_811_;
v___y_795_ = v___y_810_;
v___y_796_ = v___y_809_;
goto v___jp_786_;
}
else
{
lean_object* v_a_822_; lean_object* v___x_824_; uint8_t v_isShared_825_; uint8_t v_isSharedCheck_829_; 
lean_dec(v___x_817_);
lean_dec_ref(v___y_814_);
lean_dec(v___y_813_);
lean_dec(v_a_730_);
lean_dec_ref(v_subgoals_567_);
lean_dec_ref(v_recursor_564_);
lean_dec(v_minorIdx_563_);
lean_dec(v_pos_562_);
lean_dec(v_baseSubst_559_);
lean_dec_ref(v_major_557_);
lean_dec(v_mvarId_553_);
v_a_822_ = lean_ctor_get(v___x_821_, 0);
v_isSharedCheck_829_ = !lean_is_exclusive(v___x_821_);
if (v_isSharedCheck_829_ == 0)
{
v___x_824_ = v___x_821_;
v_isShared_825_ = v_isSharedCheck_829_;
goto v_resetjp_823_;
}
else
{
lean_inc(v_a_822_);
lean_dec(v___x_821_);
v___x_824_ = lean_box(0);
v_isShared_825_ = v_isSharedCheck_829_;
goto v_resetjp_823_;
}
v_resetjp_823_:
{
lean_object* v___x_827_; 
if (v_isShared_825_ == 0)
{
v___x_827_ = v___x_824_;
goto v_reusejp_826_;
}
else
{
lean_object* v_reuseFailAlloc_828_; 
v_reuseFailAlloc_828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_828_, 0, v_a_822_);
v___x_827_ = v_reuseFailAlloc_828_;
goto v_reusejp_826_;
}
v_reusejp_826_:
{
return v___x_827_;
}
}
}
}
}
else
{
lean_object* v___x_830_; lean_object* v___x_831_; 
v___x_830_ = lean_box(0);
lean_inc_ref(v___y_814_);
v___x_831_ = l_Lean_Meta_synthInstance_x3f(v___y_814_, v___x_830_, v___y_808_, v___y_811_, v___y_810_, v___y_809_);
if (lean_obj_tag(v___x_831_) == 0)
{
lean_object* v_a_832_; 
v_a_832_ = lean_ctor_get(v___x_831_, 0);
lean_inc(v_a_832_);
lean_dec_ref_known(v___x_831_, 1);
if (lean_obj_tag(v_a_832_) == 0)
{
lean_object* v___x_833_; 
v___x_833_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___y_814_, v___y_813_, v___y_808_, v___y_811_, v___y_810_, v___y_809_);
if (lean_obj_tag(v___x_833_) == 0)
{
lean_object* v_a_834_; lean_object* v___x_835_; 
v_a_834_ = lean_ctor_get(v___x_833_, 0);
lean_inc(v_a_834_);
lean_dec_ref_known(v___x_833_, 1);
lean_inc(v_mvarId_553_);
v___x_835_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTypeBody(v_mvarId_553_, v_a_730_, v_a_834_, v___y_808_, v___y_811_, v___y_810_, v___y_809_);
if (lean_obj_tag(v___x_835_) == 0)
{
lean_object* v_a_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; 
v_a_836_ = lean_ctor_get(v___x_835_, 0);
lean_inc(v_a_836_);
lean_dec_ref_known(v___x_835_, 1);
lean_inc(v_a_834_);
v___x_837_ = l_Lean_Expr_app___override(v_recursor_564_, v_a_834_);
v___x_838_ = lean_nat_add(v_pos_562_, v___y_815_);
lean_dec(v_pos_562_);
v___x_839_ = lean_nat_add(v_minorIdx_563_, v___y_815_);
lean_dec(v_minorIdx_563_);
v___x_840_ = l_Lean_Expr_mvarId_x21(v_a_834_);
lean_dec(v_a_834_);
v___x_841_ = ((lean_object*)(l_Lean_Meta_instInhabitedInductionSubgoal_default___closed__0));
v___x_842_ = lean_box(0);
v___x_843_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_843_, 0, v___x_840_);
lean_ctor_set(v___x_843_, 1, v___x_841_);
lean_ctor_set(v___x_843_, 2, v___x_842_);
v___x_844_ = lean_array_push(v_subgoals_567_, v___x_843_);
v_pos_562_ = v___x_838_;
v_minorIdx_563_ = v___x_839_;
v_recursor_564_ = v___x_837_;
v_recursorType_565_ = v_a_836_;
v_subgoals_567_ = v___x_844_;
v_a_568_ = v___y_808_;
v_a_569_ = v___y_811_;
v_a_570_ = v___y_810_;
v_a_571_ = v___y_809_;
goto _start;
}
else
{
lean_object* v_a_846_; lean_object* v___x_848_; uint8_t v_isShared_849_; uint8_t v_isSharedCheck_853_; 
lean_dec(v_a_834_);
lean_dec_ref(v_subgoals_567_);
lean_dec_ref(v_recursor_564_);
lean_dec(v_minorIdx_563_);
lean_dec(v_pos_562_);
lean_dec(v_baseSubst_559_);
lean_dec_ref(v_major_557_);
lean_dec(v_mvarId_553_);
v_a_846_ = lean_ctor_get(v___x_835_, 0);
v_isSharedCheck_853_ = !lean_is_exclusive(v___x_835_);
if (v_isSharedCheck_853_ == 0)
{
v___x_848_ = v___x_835_;
v_isShared_849_ = v_isSharedCheck_853_;
goto v_resetjp_847_;
}
else
{
lean_inc(v_a_846_);
lean_dec(v___x_835_);
v___x_848_ = lean_box(0);
v_isShared_849_ = v_isSharedCheck_853_;
goto v_resetjp_847_;
}
v_resetjp_847_:
{
lean_object* v___x_851_; 
if (v_isShared_849_ == 0)
{
v___x_851_ = v___x_848_;
goto v_reusejp_850_;
}
else
{
lean_object* v_reuseFailAlloc_852_; 
v_reuseFailAlloc_852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_852_, 0, v_a_846_);
v___x_851_ = v_reuseFailAlloc_852_;
goto v_reusejp_850_;
}
v_reusejp_850_:
{
return v___x_851_;
}
}
}
}
else
{
lean_object* v_a_854_; lean_object* v___x_856_; uint8_t v_isShared_857_; uint8_t v_isSharedCheck_861_; 
lean_dec(v_a_730_);
lean_dec_ref(v_subgoals_567_);
lean_dec_ref(v_recursor_564_);
lean_dec(v_minorIdx_563_);
lean_dec(v_pos_562_);
lean_dec(v_baseSubst_559_);
lean_dec_ref(v_major_557_);
lean_dec(v_mvarId_553_);
v_a_854_ = lean_ctor_get(v___x_833_, 0);
v_isSharedCheck_861_ = !lean_is_exclusive(v___x_833_);
if (v_isSharedCheck_861_ == 0)
{
v___x_856_ = v___x_833_;
v_isShared_857_ = v_isSharedCheck_861_;
goto v_resetjp_855_;
}
else
{
lean_inc(v_a_854_);
lean_dec(v___x_833_);
v___x_856_ = lean_box(0);
v_isShared_857_ = v_isSharedCheck_861_;
goto v_resetjp_855_;
}
v_resetjp_855_:
{
lean_object* v___x_859_; 
if (v_isShared_857_ == 0)
{
v___x_859_ = v___x_856_;
goto v_reusejp_858_;
}
else
{
lean_object* v_reuseFailAlloc_860_; 
v_reuseFailAlloc_860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_860_, 0, v_a_854_);
v___x_859_ = v_reuseFailAlloc_860_;
goto v_reusejp_858_;
}
v_reusejp_858_:
{
return v___x_859_;
}
}
}
}
else
{
lean_object* v_val_862_; lean_object* v___x_863_; 
lean_dec_ref(v___y_814_);
lean_dec(v___y_813_);
v_val_862_ = lean_ctor_get(v_a_832_, 0);
lean_inc(v_val_862_);
lean_dec_ref_known(v_a_832_, 1);
lean_inc(v_mvarId_553_);
v___x_863_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTypeBody(v_mvarId_553_, v_a_730_, v_val_862_, v___y_808_, v___y_811_, v___y_810_, v___y_809_);
if (lean_obj_tag(v___x_863_) == 0)
{
lean_object* v_a_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; 
v_a_864_ = lean_ctor_get(v___x_863_, 0);
lean_inc(v_a_864_);
lean_dec_ref_known(v___x_863_, 1);
v___x_865_ = l_Lean_Expr_app___override(v_recursor_564_, v_val_862_);
v___x_866_ = lean_nat_add(v_pos_562_, v___y_815_);
lean_dec(v_pos_562_);
v___x_867_ = lean_nat_add(v_minorIdx_563_, v___y_815_);
lean_dec(v_minorIdx_563_);
v_pos_562_ = v___x_866_;
v_minorIdx_563_ = v___x_867_;
v_recursor_564_ = v___x_865_;
v_recursorType_565_ = v_a_864_;
v_a_568_ = v___y_808_;
v_a_569_ = v___y_811_;
v_a_570_ = v___y_810_;
v_a_571_ = v___y_809_;
goto _start;
}
else
{
lean_object* v_a_869_; lean_object* v___x_871_; uint8_t v_isShared_872_; uint8_t v_isSharedCheck_876_; 
lean_dec(v_val_862_);
lean_dec_ref(v_subgoals_567_);
lean_dec_ref(v_recursor_564_);
lean_dec(v_minorIdx_563_);
lean_dec(v_pos_562_);
lean_dec(v_baseSubst_559_);
lean_dec_ref(v_major_557_);
lean_dec(v_mvarId_553_);
v_a_869_ = lean_ctor_get(v___x_863_, 0);
v_isSharedCheck_876_ = !lean_is_exclusive(v___x_863_);
if (v_isSharedCheck_876_ == 0)
{
v___x_871_ = v___x_863_;
v_isShared_872_ = v_isSharedCheck_876_;
goto v_resetjp_870_;
}
else
{
lean_inc(v_a_869_);
lean_dec(v___x_863_);
v___x_871_ = lean_box(0);
v_isShared_872_ = v_isSharedCheck_876_;
goto v_resetjp_870_;
}
v_resetjp_870_:
{
lean_object* v___x_874_; 
if (v_isShared_872_ == 0)
{
v___x_874_ = v___x_871_;
goto v_reusejp_873_;
}
else
{
lean_object* v_reuseFailAlloc_875_; 
v_reuseFailAlloc_875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_875_, 0, v_a_869_);
v___x_874_ = v_reuseFailAlloc_875_;
goto v_reusejp_873_;
}
v_reusejp_873_:
{
return v___x_874_;
}
}
}
}
}
else
{
lean_object* v_a_877_; lean_object* v___x_879_; uint8_t v_isShared_880_; uint8_t v_isSharedCheck_884_; 
lean_dec_ref(v___y_814_);
lean_dec(v___y_813_);
lean_dec(v_a_730_);
lean_dec_ref(v_subgoals_567_);
lean_dec_ref(v_recursor_564_);
lean_dec(v_minorIdx_563_);
lean_dec(v_pos_562_);
lean_dec(v_baseSubst_559_);
lean_dec_ref(v_major_557_);
lean_dec(v_mvarId_553_);
v_a_877_ = lean_ctor_get(v___x_831_, 0);
v_isSharedCheck_884_ = !lean_is_exclusive(v___x_831_);
if (v_isSharedCheck_884_ == 0)
{
v___x_879_ = v___x_831_;
v_isShared_880_ = v_isSharedCheck_884_;
goto v_resetjp_878_;
}
else
{
lean_inc(v_a_877_);
lean_dec(v___x_831_);
v___x_879_ = lean_box(0);
v_isShared_880_ = v_isSharedCheck_884_;
goto v_resetjp_878_;
}
v_resetjp_878_:
{
lean_object* v___x_882_; 
if (v_isShared_880_ == 0)
{
v___x_882_ = v___x_879_;
goto v_reusejp_881_;
}
else
{
lean_object* v_reuseFailAlloc_883_; 
v_reuseFailAlloc_883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_883_, 0, v_a_877_);
v___x_882_ = v_reuseFailAlloc_883_;
goto v_reusejp_881_;
}
v_reusejp_881_:
{
return v___x_882_;
}
}
}
}
}
v___jp_885_:
{
uint8_t v___x_895_; 
v___x_895_ = l_Lean_BinderInfo_isInstImplicit(v___y_893_);
if (v___x_895_ == 0)
{
v___y_808_ = v___y_886_;
v___y_809_ = v___y_888_;
v___y_810_ = v___y_887_;
v___y_811_ = v___y_890_;
v___y_812_ = v___y_889_;
v___y_813_ = v___y_894_;
v___y_814_ = v___y_891_;
v___y_815_ = v___y_892_;
v___y_816_ = v___x_895_;
goto v___jp_807_;
}
else
{
lean_object* v___x_896_; lean_object* v___x_897_; uint8_t v___x_898_; 
v___x_896_ = lean_array_get_size(v_givenNames_554_);
v___x_897_ = lean_unsigned_to_nat(0u);
v___x_898_ = lean_nat_dec_eq(v___x_896_, v___x_897_);
v___y_808_ = v___y_886_;
v___y_809_ = v___y_888_;
v___y_810_ = v___y_887_;
v___y_811_ = v___y_890_;
v___y_812_ = v___y_889_;
v___y_813_ = v___y_894_;
v___y_814_ = v___y_891_;
v___y_815_ = v___y_892_;
v___y_816_ = v___x_898_;
goto v___jp_807_;
}
}
v___jp_899_:
{
if (lean_obj_tag(v_a_730_) == 7)
{
lean_object* v_binderName_906_; lean_object* v_binderType_907_; uint8_t v_binderInfo_908_; lean_object* v___x_909_; lean_object* v___x_910_; uint8_t v___x_911_; 
v_binderName_906_ = lean_ctor_get(v_a_730_, 0);
v_binderType_907_ = lean_ctor_get(v_a_730_, 1);
v_binderInfo_908_ = lean_ctor_get_uint8(v_a_730_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_907_);
v___x_909_ = l_Lean_Expr_headBeta(v_binderType_907_);
v___x_910_ = lean_unsigned_to_nat(1u);
v___x_911_ = lean_nat_dec_eq(v_numMinors_561_, v___x_910_);
if (v___x_911_ == 0)
{
lean_object* v___x_912_; lean_object* v___x_913_; 
v___x_912_ = l_Lean_Name_eraseMacroScopes(v_binderName_906_);
v___x_913_ = l_Lean_Name_append(v___y_901_, v___x_912_);
v___y_886_ = v___y_902_;
v___y_887_ = v___y_904_;
v___y_888_ = v___y_905_;
v___y_889_ = v___y_900_;
v___y_890_ = v___y_903_;
v___y_891_ = v___x_909_;
v___y_892_ = v___x_910_;
v___y_893_ = v_binderInfo_908_;
v___y_894_ = v___x_913_;
goto v___jp_885_;
}
else
{
v___y_886_ = v___y_902_;
v___y_887_ = v___y_904_;
v___y_888_ = v___y_905_;
v___y_889_ = v___y_900_;
v___y_890_ = v___y_903_;
v___y_891_ = v___x_909_;
v___y_892_ = v___x_910_;
v___y_893_ = v_binderInfo_908_;
v___y_894_ = v___y_901_;
goto v___jp_885_;
}
}
else
{
lean_object* v___x_914_; lean_object* v___x_915_; 
lean_dec(v___y_901_);
lean_dec(v_a_730_);
lean_dec_ref(v_subgoals_567_);
lean_dec_ref(v_recursor_564_);
lean_dec(v_minorIdx_563_);
lean_dec(v_pos_562_);
lean_dec(v_baseSubst_559_);
lean_dec_ref(v_major_557_);
lean_dec(v_mvarId_553_);
v___x_914_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__15, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__15_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__15);
v___x_915_ = l_panic___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__4(v___x_914_, v___y_902_, v___y_903_, v___y_904_, v___y_905_);
return v___x_915_;
}
}
v___jp_916_:
{
if (v___y_917_ == 0)
{
lean_dec(v_a_730_);
lean_dec(v_minorIdx_563_);
lean_dec(v_pos_562_);
lean_dec(v_baseSubst_559_);
lean_dec_ref(v_major_557_);
if (v_consumedMajor_566_ == 0)
{
lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; 
v___x_918_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1));
v___x_919_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9);
lean_inc(v_mvarId_553_);
v___x_920_ = l_Lean_Meta_throwTacticEx___redArg(v___x_918_, v_mvarId_553_, v___x_919_, v_a_568_, v_a_569_, v_a_570_, v_a_571_);
if (lean_obj_tag(v___x_920_) == 0)
{
lean_dec_ref_known(v___x_920_, 1);
v___y_574_ = v_a_568_;
v___y_575_ = v_a_569_;
v___y_576_ = v_a_570_;
v___y_577_ = v_a_571_;
goto v___jp_573_;
}
else
{
lean_object* v_a_921_; lean_object* v___x_923_; uint8_t v_isShared_924_; uint8_t v_isSharedCheck_928_; 
lean_dec_ref(v_subgoals_567_);
lean_dec_ref(v_recursor_564_);
lean_dec(v_mvarId_553_);
v_a_921_ = lean_ctor_get(v___x_920_, 0);
v_isSharedCheck_928_ = !lean_is_exclusive(v___x_920_);
if (v_isSharedCheck_928_ == 0)
{
v___x_923_ = v___x_920_;
v_isShared_924_ = v_isSharedCheck_928_;
goto v_resetjp_922_;
}
else
{
lean_inc(v_a_921_);
lean_dec(v___x_920_);
v___x_923_ = lean_box(0);
v_isShared_924_ = v_isSharedCheck_928_;
goto v_resetjp_922_;
}
v_resetjp_922_:
{
lean_object* v___x_926_; 
if (v_isShared_924_ == 0)
{
v___x_926_ = v___x_923_;
goto v_reusejp_925_;
}
else
{
lean_object* v_reuseFailAlloc_927_; 
v_reuseFailAlloc_927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_927_, 0, v_a_921_);
v___x_926_ = v_reuseFailAlloc_927_;
goto v_reusejp_925_;
}
v_reusejp_925_:
{
return v___x_926_;
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
lean_object* v___x_929_; uint8_t v___x_930_; 
v___x_929_ = l_Lean_Meta_RecursorInfo_firstIndexPos(v_recursorInfo_555_);
v___x_930_ = lean_nat_dec_eq(v_pos_562_, v___x_929_);
lean_dec(v___x_929_);
if (v___x_930_ == 0)
{
lean_object* v___x_931_; 
lean_inc(v_mvarId_553_);
v___x_931_ = l_Lean_MVarId_getTag(v_mvarId_553_, v_a_568_, v_a_569_, v_a_570_, v_a_571_);
if (lean_obj_tag(v___x_931_) == 0)
{
lean_object* v_a_932_; uint8_t v___x_933_; 
v_a_932_ = lean_ctor_get(v___x_931_, 0);
lean_inc(v_a_932_);
lean_dec_ref_known(v___x_931_, 1);
v___x_933_ = lean_nat_dec_le(v_numMinors_561_, v_minorIdx_563_);
if (v___x_933_ == 0)
{
v___y_900_ = v___y_917_;
v___y_901_ = v_a_932_;
v___y_902_ = v_a_568_;
v___y_903_ = v_a_569_;
v___y_904_ = v_a_570_;
v___y_905_ = v_a_571_;
goto v___jp_899_;
}
else
{
lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; 
v___x_934_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1));
v___x_935_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9);
lean_inc(v_mvarId_553_);
v___x_936_ = l_Lean_Meta_throwTacticEx___redArg(v___x_934_, v_mvarId_553_, v___x_935_, v_a_568_, v_a_569_, v_a_570_, v_a_571_);
if (lean_obj_tag(v___x_936_) == 0)
{
lean_dec_ref_known(v___x_936_, 1);
v___y_900_ = v___y_917_;
v___y_901_ = v_a_932_;
v___y_902_ = v_a_568_;
v___y_903_ = v_a_569_;
v___y_904_ = v_a_570_;
v___y_905_ = v_a_571_;
goto v___jp_899_;
}
else
{
lean_object* v_a_937_; lean_object* v___x_939_; uint8_t v_isShared_940_; uint8_t v_isSharedCheck_944_; 
lean_dec(v_a_932_);
lean_dec(v_a_730_);
lean_dec_ref(v_subgoals_567_);
lean_dec_ref(v_recursor_564_);
lean_dec(v_minorIdx_563_);
lean_dec(v_pos_562_);
lean_dec(v_baseSubst_559_);
lean_dec_ref(v_major_557_);
lean_dec(v_mvarId_553_);
v_a_937_ = lean_ctor_get(v___x_936_, 0);
v_isSharedCheck_944_ = !lean_is_exclusive(v___x_936_);
if (v_isSharedCheck_944_ == 0)
{
v___x_939_ = v___x_936_;
v_isShared_940_ = v_isSharedCheck_944_;
goto v_resetjp_938_;
}
else
{
lean_inc(v_a_937_);
lean_dec(v___x_936_);
v___x_939_ = lean_box(0);
v_isShared_940_ = v_isSharedCheck_944_;
goto v_resetjp_938_;
}
v_resetjp_938_:
{
lean_object* v___x_942_; 
if (v_isShared_940_ == 0)
{
v___x_942_ = v___x_939_;
goto v_reusejp_941_;
}
else
{
lean_object* v_reuseFailAlloc_943_; 
v_reuseFailAlloc_943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_943_, 0, v_a_937_);
v___x_942_ = v_reuseFailAlloc_943_;
goto v_reusejp_941_;
}
v_reusejp_941_:
{
return v___x_942_;
}
}
}
}
}
else
{
lean_object* v_a_945_; lean_object* v___x_947_; uint8_t v_isShared_948_; uint8_t v_isSharedCheck_952_; 
lean_dec(v_a_730_);
lean_dec_ref(v_subgoals_567_);
lean_dec_ref(v_recursor_564_);
lean_dec(v_minorIdx_563_);
lean_dec(v_pos_562_);
lean_dec(v_baseSubst_559_);
lean_dec_ref(v_major_557_);
lean_dec(v_mvarId_553_);
v_a_945_ = lean_ctor_get(v___x_931_, 0);
v_isSharedCheck_952_ = !lean_is_exclusive(v___x_931_);
if (v_isSharedCheck_952_ == 0)
{
v___x_947_ = v___x_931_;
v_isShared_948_ = v_isSharedCheck_952_;
goto v_resetjp_946_;
}
else
{
lean_inc(v_a_945_);
lean_dec(v___x_931_);
v___x_947_ = lean_box(0);
v_isShared_948_ = v_isSharedCheck_952_;
goto v_resetjp_946_;
}
v_resetjp_946_:
{
lean_object* v___x_950_; 
if (v_isShared_948_ == 0)
{
v___x_950_ = v___x_947_;
goto v_reusejp_949_;
}
else
{
lean_object* v_reuseFailAlloc_951_; 
v_reuseFailAlloc_951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_951_, 0, v_a_945_);
v___x_950_ = v_reuseFailAlloc_951_;
goto v_reusejp_949_;
}
v_reusejp_949_:
{
return v___x_950_;
}
}
}
}
else
{
lean_object* v___x_953_; lean_object* v___x_954_; uint8_t v___x_955_; 
v___x_953_ = lean_unsigned_to_nat(0u);
v___x_954_ = lean_array_get_size(v_indices_558_);
v___x_955_ = lean_nat_dec_lt(v___x_953_, v___x_954_);
if (v___x_955_ == 0)
{
v___y_695_ = v___x_954_;
v___y_696_ = v___x_930_;
v_fst_697_ = v_recursor_564_;
v_snd_698_ = v_a_730_;
goto v___jp_694_;
}
else
{
lean_object* v___x_956_; uint8_t v___x_957_; 
lean_inc(v_a_730_);
lean_inc_ref(v_recursor_564_);
v___x_956_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_956_, 0, v_recursor_564_);
lean_ctor_set(v___x_956_, 1, v_a_730_);
v___x_957_ = lean_nat_dec_le(v___x_954_, v___x_954_);
if (v___x_957_ == 0)
{
if (v___x_955_ == 0)
{
lean_dec_ref_known(v___x_956_, 2);
v___y_695_ = v___x_954_;
v___y_696_ = v___x_930_;
v_fst_697_ = v_recursor_564_;
v_snd_698_ = v_a_730_;
goto v___jp_694_;
}
else
{
size_t v___x_958_; size_t v___x_959_; lean_object* v___x_960_; 
lean_dec(v_a_730_);
lean_dec_ref(v_recursor_564_);
v___x_958_ = ((size_t)0ULL);
v___x_959_ = lean_usize_of_nat(v___x_954_);
lean_inc(v_mvarId_553_);
v___x_960_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__5(v_mvarId_553_, v_indices_558_, v___x_958_, v___x_959_, v___x_956_, v_a_568_, v_a_569_, v_a_570_, v_a_571_);
v___y_715_ = v___x_954_;
v___y_716_ = v___x_930_;
v___y_717_ = v___x_960_;
goto v___jp_714_;
}
}
else
{
size_t v___x_961_; size_t v___x_962_; lean_object* v___x_963_; 
lean_dec(v_a_730_);
lean_dec_ref(v_recursor_564_);
v___x_961_ = ((size_t)0ULL);
v___x_962_ = lean_usize_of_nat(v___x_954_);
lean_inc(v_mvarId_553_);
v___x_963_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__5(v_mvarId_553_, v_indices_558_, v___x_961_, v___x_962_, v___x_956_, v_a_568_, v_a_569_, v_a_570_, v_a_571_);
v___y_715_ = v___x_954_;
v___y_716_ = v___x_930_;
v___y_717_ = v___x_963_;
goto v___jp_714_;
}
}
}
}
}
}
else
{
lean_object* v_a_967_; lean_object* v___x_969_; uint8_t v_isShared_970_; uint8_t v_isSharedCheck_974_; 
lean_dec_ref(v_subgoals_567_);
lean_dec_ref(v_recursor_564_);
lean_dec(v_minorIdx_563_);
lean_dec(v_pos_562_);
lean_dec(v_baseSubst_559_);
lean_dec_ref(v_major_557_);
lean_dec(v_mvarId_553_);
v_a_967_ = lean_ctor_get(v___x_729_, 0);
v_isSharedCheck_974_ = !lean_is_exclusive(v___x_729_);
if (v_isSharedCheck_974_ == 0)
{
v___x_969_ = v___x_729_;
v_isShared_970_ = v_isSharedCheck_974_;
goto v_resetjp_968_;
}
else
{
lean_inc(v_a_967_);
lean_dec(v___x_729_);
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
v___jp_573_:
{
lean_object* v___x_578_; 
v___x_578_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0___redArg(v_mvarId_553_, v_recursor_564_, v___y_575_);
if (lean_obj_tag(v___x_578_) == 0)
{
lean_object* v___x_580_; uint8_t v_isShared_581_; uint8_t v_isSharedCheck_619_; 
v_isSharedCheck_619_ = !lean_is_exclusive(v___x_578_);
if (v_isSharedCheck_619_ == 0)
{
lean_object* v_unused_620_; 
v_unused_620_ = lean_ctor_get(v___x_578_, 0);
lean_dec(v_unused_620_);
v___x_580_ = v___x_578_;
v_isShared_581_ = v_isSharedCheck_619_;
goto v_resetjp_579_;
}
else
{
lean_dec(v___x_578_);
v___x_580_ = lean_box(0);
v_isShared_581_ = v_isSharedCheck_619_;
goto v_resetjp_579_;
}
v_resetjp_579_:
{
lean_object* v_options_582_; uint8_t v_hasTrace_583_; 
v_options_582_ = lean_ctor_get(v___y_576_, 2);
v_hasTrace_583_ = lean_ctor_get_uint8(v_options_582_, sizeof(void*)*1);
if (v_hasTrace_583_ == 0)
{
lean_object* v___x_585_; 
if (v_isShared_581_ == 0)
{
lean_ctor_set(v___x_580_, 0, v_subgoals_567_);
v___x_585_ = v___x_580_;
goto v_reusejp_584_;
}
else
{
lean_object* v_reuseFailAlloc_586_; 
v_reuseFailAlloc_586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_586_, 0, v_subgoals_567_);
v___x_585_ = v_reuseFailAlloc_586_;
goto v_reusejp_584_;
}
v_reusejp_584_:
{
return v___x_585_;
}
}
else
{
lean_object* v_inheritedTraceOptions_587_; lean_object* v___x_588_; lean_object* v___x_589_; uint8_t v___x_590_; 
v_inheritedTraceOptions_587_ = lean_ctor_get(v___y_576_, 13);
v___x_588_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__2));
v___x_589_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5);
v___x_590_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_587_, v_options_582_, v___x_589_);
if (v___x_590_ == 0)
{
lean_object* v___x_592_; 
if (v_isShared_581_ == 0)
{
lean_ctor_set(v___x_580_, 0, v_subgoals_567_);
v___x_592_ = v___x_580_;
goto v_reusejp_591_;
}
else
{
lean_object* v_reuseFailAlloc_593_; 
v_reuseFailAlloc_593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_593_, 0, v_subgoals_567_);
v___x_592_ = v_reuseFailAlloc_593_;
goto v_reusejp_591_;
}
v_reusejp_591_:
{
return v___x_592_;
}
}
else
{
lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; 
lean_del_object(v___x_580_);
v___x_594_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__7, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__7_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__7);
v___x_595_ = lean_array_get_size(v_subgoals_567_);
v___x_596_ = l_Nat_reprFast(v___x_595_);
v___x_597_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_597_, 0, v___x_596_);
v___x_598_ = l_Lean_MessageData_ofFormat(v___x_597_);
v___x_599_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_599_, 0, v___x_594_);
lean_ctor_set(v___x_599_, 1, v___x_598_);
v___x_600_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__9, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__9_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__9);
v___x_601_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_601_, 0, v___x_599_);
lean_ctor_set(v___x_601_, 1, v___x_600_);
v___x_602_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1(v___x_588_, v___x_601_, v___y_574_, v___y_575_, v___y_576_, v___y_577_);
if (lean_obj_tag(v___x_602_) == 0)
{
lean_object* v___x_604_; uint8_t v_isShared_605_; uint8_t v_isSharedCheck_609_; 
v_isSharedCheck_609_ = !lean_is_exclusive(v___x_602_);
if (v_isSharedCheck_609_ == 0)
{
lean_object* v_unused_610_; 
v_unused_610_ = lean_ctor_get(v___x_602_, 0);
lean_dec(v_unused_610_);
v___x_604_ = v___x_602_;
v_isShared_605_ = v_isSharedCheck_609_;
goto v_resetjp_603_;
}
else
{
lean_dec(v___x_602_);
v___x_604_ = lean_box(0);
v_isShared_605_ = v_isSharedCheck_609_;
goto v_resetjp_603_;
}
v_resetjp_603_:
{
lean_object* v___x_607_; 
if (v_isShared_605_ == 0)
{
lean_ctor_set(v___x_604_, 0, v_subgoals_567_);
v___x_607_ = v___x_604_;
goto v_reusejp_606_;
}
else
{
lean_object* v_reuseFailAlloc_608_; 
v_reuseFailAlloc_608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_608_, 0, v_subgoals_567_);
v___x_607_ = v_reuseFailAlloc_608_;
goto v_reusejp_606_;
}
v_reusejp_606_:
{
return v___x_607_;
}
}
}
else
{
lean_object* v_a_611_; lean_object* v___x_613_; uint8_t v_isShared_614_; uint8_t v_isSharedCheck_618_; 
lean_dec_ref(v_subgoals_567_);
v_a_611_ = lean_ctor_get(v___x_602_, 0);
v_isSharedCheck_618_ = !lean_is_exclusive(v___x_602_);
if (v_isSharedCheck_618_ == 0)
{
v___x_613_ = v___x_602_;
v_isShared_614_ = v_isSharedCheck_618_;
goto v_resetjp_612_;
}
else
{
lean_inc(v_a_611_);
lean_dec(v___x_602_);
v___x_613_ = lean_box(0);
v_isShared_614_ = v_isSharedCheck_618_;
goto v_resetjp_612_;
}
v_resetjp_612_:
{
lean_object* v___x_616_; 
if (v_isShared_614_ == 0)
{
v___x_616_ = v___x_613_;
goto v_reusejp_615_;
}
else
{
lean_object* v_reuseFailAlloc_617_; 
v_reuseFailAlloc_617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_617_, 0, v_a_611_);
v___x_616_ = v_reuseFailAlloc_617_;
goto v_reusejp_615_;
}
v_reusejp_615_:
{
return v___x_616_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_621_; lean_object* v___x_623_; uint8_t v_isShared_624_; uint8_t v_isSharedCheck_628_; 
lean_dec_ref(v_subgoals_567_);
v_a_621_ = lean_ctor_get(v___x_578_, 0);
v_isSharedCheck_628_ = !lean_is_exclusive(v___x_578_);
if (v_isSharedCheck_628_ == 0)
{
v___x_623_ = v___x_578_;
v_isShared_624_ = v_isSharedCheck_628_;
goto v_resetjp_622_;
}
else
{
lean_inc(v_a_621_);
lean_dec(v___x_578_);
v___x_623_ = lean_box(0);
v_isShared_624_ = v_isSharedCheck_628_;
goto v_resetjp_622_;
}
v_resetjp_622_:
{
lean_object* v___x_626_; 
if (v_isShared_624_ == 0)
{
v___x_626_ = v___x_623_;
goto v_reusejp_625_;
}
else
{
lean_object* v_reuseFailAlloc_627_; 
v_reuseFailAlloc_627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_627_, 0, v_a_621_);
v___x_626_ = v_reuseFailAlloc_627_;
goto v_reusejp_625_;
}
v_reusejp_625_:
{
return v___x_626_;
}
}
}
}
v___jp_629_:
{
lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; 
v___x_645_ = l_Lean_Expr_mvarId_x21(v___y_631_);
lean_dec_ref(v___y_631_);
v___x_646_ = l_Lean_Expr_fvarId_x21(v_major_557_);
v___x_647_ = l_Lean_MVarId_tryClear(v___x_645_, v___x_646_, v___y_641_, v___y_642_, v___y_643_, v___y_644_);
if (lean_obj_tag(v___x_647_) == 0)
{
lean_object* v_a_648_; uint8_t v_explicit_649_; lean_object* v_varNames_650_; uint8_t v___x_651_; lean_object* v___x_652_; 
v_a_648_ = lean_ctor_get(v___x_647_, 0);
lean_inc(v_a_648_);
lean_dec_ref_known(v___x_647_, 1);
v_explicit_649_ = lean_ctor_get_uint8(v___y_630_, sizeof(void*)*1);
v_varNames_650_ = lean_ctor_get(v___y_630_, 0);
lean_inc(v_varNames_650_);
lean_dec_ref(v___y_630_);
v___x_651_ = lean_bool_not(v_explicit_649_);
v___x_652_ = l_Lean_Meta_introNCore(v_a_648_, v___y_634_, v_varNames_650_, v___x_651_, v___y_640_, v___y_641_, v___y_642_, v___y_643_, v___y_644_);
if (lean_obj_tag(v___x_652_) == 0)
{
lean_object* v_a_653_; lean_object* v_fst_654_; lean_object* v_snd_655_; lean_object* v___x_656_; lean_object* v___x_657_; 
v_a_653_ = lean_ctor_get(v___x_652_, 0);
lean_inc(v_a_653_);
lean_dec_ref_known(v___x_652_, 1);
v_fst_654_ = lean_ctor_get(v_a_653_, 0);
lean_inc(v_fst_654_);
v_snd_655_ = lean_ctor_get(v_a_653_, 1);
lean_inc(v_snd_655_);
lean_dec(v_a_653_);
v___x_656_ = lean_box(0);
v___x_657_ = l_Lean_Meta_introNCore(v_snd_655_, v___y_638_, v___x_656_, v___y_640_, v___y_633_, v___y_641_, v___y_642_, v___y_643_, v___y_644_);
if (lean_obj_tag(v___x_657_) == 0)
{
lean_object* v_a_658_; lean_object* v_fst_659_; lean_object* v_snd_660_; lean_object* v___x_661_; size_t v_sz_662_; size_t v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; 
v_a_658_ = lean_ctor_get(v___x_657_, 0);
lean_inc(v_a_658_);
lean_dec_ref_known(v___x_657_, 1);
v_fst_659_ = lean_ctor_get(v_a_658_, 0);
lean_inc(v_fst_659_);
v_snd_660_ = lean_ctor_get(v_a_658_, 1);
lean_inc(v_snd_660_);
lean_dec(v_a_658_);
lean_inc(v_baseSubst_559_);
lean_inc(v___y_636_);
v___x_661_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__2___redArg(v___y_637_, v_reverted_556_, v_fst_659_, v___y_636_, v___y_636_, v_baseSubst_559_);
lean_dec(v___y_636_);
lean_dec(v_fst_659_);
lean_dec(v___y_637_);
v_sz_662_ = lean_array_size(v_fst_654_);
v___x_663_ = ((size_t)0ULL);
v___x_664_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__3(v_sz_662_, v___x_663_, v_fst_654_);
v___x_665_ = lean_nat_add(v_pos_562_, v___y_639_);
lean_dec(v_pos_562_);
v___x_666_ = lean_nat_add(v_minorIdx_563_, v___y_639_);
lean_dec(v_minorIdx_563_);
v___x_667_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_667_, 0, v_snd_660_);
lean_ctor_set(v___x_667_, 1, v___x_664_);
lean_ctor_set(v___x_667_, 2, v___x_661_);
v___x_668_ = lean_array_push(v_subgoals_567_, v___x_667_);
v_pos_562_ = v___x_665_;
v_minorIdx_563_ = v___x_666_;
v_recursor_564_ = v___y_632_;
v_recursorType_565_ = v___y_635_;
v_subgoals_567_ = v___x_668_;
v_a_568_ = v___y_641_;
v_a_569_ = v___y_642_;
v_a_570_ = v___y_643_;
v_a_571_ = v___y_644_;
goto _start;
}
else
{
lean_object* v_a_670_; lean_object* v___x_672_; uint8_t v_isShared_673_; uint8_t v_isSharedCheck_677_; 
lean_dec(v_fst_654_);
lean_dec(v___y_637_);
lean_dec(v___y_636_);
lean_dec_ref(v___y_635_);
lean_dec_ref(v___y_632_);
lean_dec_ref(v_subgoals_567_);
lean_dec(v_minorIdx_563_);
lean_dec(v_pos_562_);
lean_dec(v_baseSubst_559_);
lean_dec_ref(v_major_557_);
lean_dec(v_mvarId_553_);
v_a_670_ = lean_ctor_get(v___x_657_, 0);
v_isSharedCheck_677_ = !lean_is_exclusive(v___x_657_);
if (v_isSharedCheck_677_ == 0)
{
v___x_672_ = v___x_657_;
v_isShared_673_ = v_isSharedCheck_677_;
goto v_resetjp_671_;
}
else
{
lean_inc(v_a_670_);
lean_dec(v___x_657_);
v___x_672_ = lean_box(0);
v_isShared_673_ = v_isSharedCheck_677_;
goto v_resetjp_671_;
}
v_resetjp_671_:
{
lean_object* v___x_675_; 
if (v_isShared_673_ == 0)
{
v___x_675_ = v___x_672_;
goto v_reusejp_674_;
}
else
{
lean_object* v_reuseFailAlloc_676_; 
v_reuseFailAlloc_676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_676_, 0, v_a_670_);
v___x_675_ = v_reuseFailAlloc_676_;
goto v_reusejp_674_;
}
v_reusejp_674_:
{
return v___x_675_;
}
}
}
}
else
{
lean_object* v_a_678_; lean_object* v___x_680_; uint8_t v_isShared_681_; uint8_t v_isSharedCheck_685_; 
lean_dec(v___y_638_);
lean_dec(v___y_637_);
lean_dec(v___y_636_);
lean_dec_ref(v___y_635_);
lean_dec_ref(v___y_632_);
lean_dec_ref(v_subgoals_567_);
lean_dec(v_minorIdx_563_);
lean_dec(v_pos_562_);
lean_dec(v_baseSubst_559_);
lean_dec_ref(v_major_557_);
lean_dec(v_mvarId_553_);
v_a_678_ = lean_ctor_get(v___x_652_, 0);
v_isSharedCheck_685_ = !lean_is_exclusive(v___x_652_);
if (v_isSharedCheck_685_ == 0)
{
v___x_680_ = v___x_652_;
v_isShared_681_ = v_isSharedCheck_685_;
goto v_resetjp_679_;
}
else
{
lean_inc(v_a_678_);
lean_dec(v___x_652_);
v___x_680_ = lean_box(0);
v_isShared_681_ = v_isSharedCheck_685_;
goto v_resetjp_679_;
}
v_resetjp_679_:
{
lean_object* v___x_683_; 
if (v_isShared_681_ == 0)
{
v___x_683_ = v___x_680_;
goto v_reusejp_682_;
}
else
{
lean_object* v_reuseFailAlloc_684_; 
v_reuseFailAlloc_684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_684_, 0, v_a_678_);
v___x_683_ = v_reuseFailAlloc_684_;
goto v_reusejp_682_;
}
v_reusejp_682_:
{
return v___x_683_;
}
}
}
}
else
{
lean_object* v_a_686_; lean_object* v___x_688_; uint8_t v_isShared_689_; uint8_t v_isSharedCheck_693_; 
lean_dec(v___y_638_);
lean_dec(v___y_637_);
lean_dec(v___y_636_);
lean_dec_ref(v___y_635_);
lean_dec(v___y_634_);
lean_dec_ref(v___y_632_);
lean_dec_ref(v___y_630_);
lean_dec_ref(v_subgoals_567_);
lean_dec(v_minorIdx_563_);
lean_dec(v_pos_562_);
lean_dec(v_baseSubst_559_);
lean_dec_ref(v_major_557_);
lean_dec(v_mvarId_553_);
v_a_686_ = lean_ctor_get(v___x_647_, 0);
v_isSharedCheck_693_ = !lean_is_exclusive(v___x_647_);
if (v_isSharedCheck_693_ == 0)
{
v___x_688_ = v___x_647_;
v_isShared_689_ = v_isSharedCheck_693_;
goto v_resetjp_687_;
}
else
{
lean_inc(v_a_686_);
lean_dec(v___x_647_);
v___x_688_ = lean_box(0);
v_isShared_689_ = v_isSharedCheck_693_;
goto v_resetjp_687_;
}
v_resetjp_687_:
{
lean_object* v___x_691_; 
if (v_isShared_689_ == 0)
{
v___x_691_ = v___x_688_;
goto v_reusejp_690_;
}
else
{
lean_object* v_reuseFailAlloc_692_; 
v_reuseFailAlloc_692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_692_, 0, v_a_686_);
v___x_691_ = v_reuseFailAlloc_692_;
goto v_reusejp_690_;
}
v_reusejp_690_:
{
return v___x_691_;
}
}
}
}
v___jp_694_:
{
lean_object* v___x_699_; 
lean_inc(v_mvarId_553_);
v___x_699_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTypeBody(v_mvarId_553_, v_snd_698_, v_major_557_, v_a_568_, v_a_569_, v_a_570_, v_a_571_);
if (lean_obj_tag(v___x_699_) == 0)
{
lean_object* v_a_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; 
v_a_700_ = lean_ctor_get(v___x_699_, 0);
lean_inc(v_a_700_);
lean_dec_ref_known(v___x_699_, 1);
lean_inc_ref(v_major_557_);
v___x_701_ = l_Lean_Expr_app___override(v_fst_697_, v_major_557_);
v___x_702_ = lean_unsigned_to_nat(1u);
v___x_703_ = lean_nat_add(v_pos_562_, v___x_702_);
lean_dec(v_pos_562_);
v___x_704_ = lean_nat_add(v___x_703_, v___y_695_);
lean_dec(v___y_695_);
lean_dec(v___x_703_);
v_pos_562_ = v___x_704_;
v_recursor_564_ = v___x_701_;
v_recursorType_565_ = v_a_700_;
v_consumedMajor_566_ = v___y_696_;
goto _start;
}
else
{
lean_object* v_a_706_; lean_object* v___x_708_; uint8_t v_isShared_709_; uint8_t v_isSharedCheck_713_; 
lean_dec_ref(v_fst_697_);
lean_dec(v___y_695_);
lean_dec_ref(v_subgoals_567_);
lean_dec(v_minorIdx_563_);
lean_dec(v_pos_562_);
lean_dec(v_baseSubst_559_);
lean_dec_ref(v_major_557_);
lean_dec(v_mvarId_553_);
v_a_706_ = lean_ctor_get(v___x_699_, 0);
v_isSharedCheck_713_ = !lean_is_exclusive(v___x_699_);
if (v_isSharedCheck_713_ == 0)
{
v___x_708_ = v___x_699_;
v_isShared_709_ = v_isSharedCheck_713_;
goto v_resetjp_707_;
}
else
{
lean_inc(v_a_706_);
lean_dec(v___x_699_);
v___x_708_ = lean_box(0);
v_isShared_709_ = v_isSharedCheck_713_;
goto v_resetjp_707_;
}
v_resetjp_707_:
{
lean_object* v___x_711_; 
if (v_isShared_709_ == 0)
{
v___x_711_ = v___x_708_;
goto v_reusejp_710_;
}
else
{
lean_object* v_reuseFailAlloc_712_; 
v_reuseFailAlloc_712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_712_, 0, v_a_706_);
v___x_711_ = v_reuseFailAlloc_712_;
goto v_reusejp_710_;
}
v_reusejp_710_:
{
return v___x_711_;
}
}
}
}
v___jp_714_:
{
if (lean_obj_tag(v___y_717_) == 0)
{
lean_object* v_a_718_; lean_object* v_fst_719_; lean_object* v_snd_720_; 
v_a_718_ = lean_ctor_get(v___y_717_, 0);
lean_inc(v_a_718_);
lean_dec_ref_known(v___y_717_, 1);
v_fst_719_ = lean_ctor_get(v_a_718_, 0);
lean_inc(v_fst_719_);
v_snd_720_ = lean_ctor_get(v_a_718_, 1);
lean_inc(v_snd_720_);
lean_dec(v_a_718_);
v___y_695_ = v___y_715_;
v___y_696_ = v___y_716_;
v_fst_697_ = v_fst_719_;
v_snd_698_ = v_snd_720_;
goto v___jp_694_;
}
else
{
lean_object* v_a_721_; lean_object* v___x_723_; uint8_t v_isShared_724_; uint8_t v_isSharedCheck_728_; 
lean_dec(v___y_715_);
lean_dec_ref(v_subgoals_567_);
lean_dec(v_minorIdx_563_);
lean_dec(v_pos_562_);
lean_dec(v_baseSubst_559_);
lean_dec_ref(v_major_557_);
lean_dec(v_mvarId_553_);
v_a_721_ = lean_ctor_get(v___y_717_, 0);
v_isSharedCheck_728_ = !lean_is_exclusive(v___y_717_);
if (v_isSharedCheck_728_ == 0)
{
v___x_723_ = v___y_717_;
v_isShared_724_ = v_isSharedCheck_728_;
goto v_resetjp_722_;
}
else
{
lean_inc(v_a_721_);
lean_dec(v___y_717_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___boxed(lean_object** _args){
lean_object* v_mvarId_975_ = _args[0];
lean_object* v_givenNames_976_ = _args[1];
lean_object* v_recursorInfo_977_ = _args[2];
lean_object* v_reverted_978_ = _args[3];
lean_object* v_major_979_ = _args[4];
lean_object* v_indices_980_ = _args[5];
lean_object* v_baseSubst_981_ = _args[6];
lean_object* v_initialArity_982_ = _args[7];
lean_object* v_numMinors_983_ = _args[8];
lean_object* v_pos_984_ = _args[9];
lean_object* v_minorIdx_985_ = _args[10];
lean_object* v_recursor_986_ = _args[11];
lean_object* v_recursorType_987_ = _args[12];
lean_object* v_consumedMajor_988_ = _args[13];
lean_object* v_subgoals_989_ = _args[14];
lean_object* v_a_990_ = _args[15];
lean_object* v_a_991_ = _args[16];
lean_object* v_a_992_ = _args[17];
lean_object* v_a_993_ = _args[18];
lean_object* v_a_994_ = _args[19];
_start:
{
uint8_t v_consumedMajor_boxed_995_; lean_object* v_res_996_; 
v_consumedMajor_boxed_995_ = lean_unbox(v_consumedMajor_988_);
v_res_996_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop(v_mvarId_975_, v_givenNames_976_, v_recursorInfo_977_, v_reverted_978_, v_major_979_, v_indices_980_, v_baseSubst_981_, v_initialArity_982_, v_numMinors_983_, v_pos_984_, v_minorIdx_985_, v_recursor_986_, v_recursorType_987_, v_consumedMajor_boxed_995_, v_subgoals_989_, v_a_990_, v_a_991_, v_a_992_, v_a_993_);
lean_dec(v_a_993_);
lean_dec_ref(v_a_992_);
lean_dec(v_a_991_);
lean_dec_ref(v_a_990_);
lean_dec(v_numMinors_983_);
lean_dec(v_initialArity_982_);
lean_dec_ref(v_indices_980_);
lean_dec_ref(v_reverted_978_);
lean_dec_ref(v_recursorInfo_977_);
lean_dec_ref(v_givenNames_976_);
return v_res_996_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0(lean_object* v_mvarId_997_, lean_object* v_val_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_){
_start:
{
lean_object* v___x_1004_; 
v___x_1004_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0___redArg(v_mvarId_997_, v_val_998_, v___y_1000_);
return v___x_1004_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0___boxed(lean_object* v_mvarId_1005_, lean_object* v_val_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_){
_start:
{
lean_object* v_res_1012_; 
v_res_1012_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0(v_mvarId_1005_, v_val_1006_, v___y_1007_, v___y_1008_, v___y_1009_, v___y_1010_);
lean_dec(v___y_1010_);
lean_dec_ref(v___y_1009_);
lean_dec(v___y_1008_);
lean_dec_ref(v___y_1007_);
return v_res_1012_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__2(lean_object* v___x_1013_, lean_object* v_reverted_1014_, lean_object* v_fst_1015_, lean_object* v_n_1016_, lean_object* v_j_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_){
_start:
{
lean_object* v___x_1020_; 
v___x_1020_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__2___redArg(v___x_1013_, v_reverted_1014_, v_fst_1015_, v_n_1016_, v_j_1017_, v_a_1019_);
return v___x_1020_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__2___boxed(lean_object* v___x_1021_, lean_object* v_reverted_1022_, lean_object* v_fst_1023_, lean_object* v_n_1024_, lean_object* v_j_1025_, lean_object* v_a_1026_, lean_object* v_a_1027_){
_start:
{
lean_object* v_res_1028_; 
v_res_1028_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__2(v___x_1021_, v_reverted_1022_, v_fst_1023_, v_n_1024_, v_j_1025_, v_a_1026_, v_a_1027_);
lean_dec(v_n_1024_);
lean_dec_ref(v_fst_1023_);
lean_dec_ref(v_reverted_1022_);
lean_dec(v___x_1021_);
return v_res_1028_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0(lean_object* v_00_u03b2_1029_, lean_object* v_x_1030_, lean_object* v_x_1031_, lean_object* v_x_1032_){
_start:
{
lean_object* v___x_1033_; 
v___x_1033_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0___redArg(v_x_1030_, v_x_1031_, v_x_1032_);
return v___x_1033_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1034_, lean_object* v_x_1035_, size_t v_x_1036_, size_t v_x_1037_, lean_object* v_x_1038_, lean_object* v_x_1039_){
_start:
{
lean_object* v___x_1040_; 
v___x_1040_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2___redArg(v_x_1035_, v_x_1036_, v_x_1037_, v_x_1038_, v_x_1039_);
return v___x_1040_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1041_, lean_object* v_x_1042_, lean_object* v_x_1043_, lean_object* v_x_1044_, lean_object* v_x_1045_, lean_object* v_x_1046_){
_start:
{
size_t v_x_11368__boxed_1047_; size_t v_x_11369__boxed_1048_; lean_object* v_res_1049_; 
v_x_11368__boxed_1047_ = lean_unbox_usize(v_x_1043_);
lean_dec(v_x_1043_);
v_x_11369__boxed_1048_ = lean_unbox_usize(v_x_1044_);
lean_dec(v_x_1044_);
v_res_1049_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2(v_00_u03b2_1041_, v_x_1042_, v_x_11368__boxed_1047_, v_x_11369__boxed_1048_, v_x_1045_, v_x_1046_);
return v_res_1049_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__8(lean_object* v_00_u03b2_1050_, lean_object* v_n_1051_, lean_object* v_k_1052_, lean_object* v_v_1053_){
_start:
{
lean_object* v___x_1054_; 
v___x_1054_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__8___redArg(v_n_1051_, v_k_1052_, v_v_1053_);
return v___x_1054_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__9(lean_object* v_00_u03b2_1055_, size_t v_depth_1056_, lean_object* v_keys_1057_, lean_object* v_vals_1058_, lean_object* v_heq_1059_, lean_object* v_i_1060_, lean_object* v_entries_1061_){
_start:
{
lean_object* v___x_1062_; 
v___x_1062_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__9___redArg(v_depth_1056_, v_keys_1057_, v_vals_1058_, v_i_1060_, v_entries_1061_);
return v___x_1062_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__9___boxed(lean_object* v_00_u03b2_1063_, lean_object* v_depth_1064_, lean_object* v_keys_1065_, lean_object* v_vals_1066_, lean_object* v_heq_1067_, lean_object* v_i_1068_, lean_object* v_entries_1069_){
_start:
{
size_t v_depth_boxed_1070_; lean_object* v_res_1071_; 
v_depth_boxed_1070_ = lean_unbox_usize(v_depth_1064_);
lean_dec(v_depth_1064_);
v_res_1071_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__9(v_00_u03b2_1063_, v_depth_boxed_1070_, v_keys_1065_, v_vals_1066_, v_heq_1067_, v_i_1068_, v_entries_1069_);
lean_dec_ref(v_vals_1066_);
lean_dec_ref(v_keys_1065_);
return v_res_1071_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__8_spec__9(lean_object* v_00_u03b2_1072_, lean_object* v_x_1073_, lean_object* v_x_1074_, lean_object* v_x_1075_, lean_object* v_x_1076_){
_start:
{
lean_object* v___x_1077_; 
v___x_1077_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__8_spec__9___redArg(v_x_1073_, v_x_1074_, v_x_1075_, v_x_1076_);
return v___x_1077_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize(lean_object* v_mvarId_1080_, lean_object* v_givenNames_1081_, lean_object* v_recursorInfo_1082_, lean_object* v_reverted_1083_, lean_object* v_major_1084_, lean_object* v_indices_1085_, lean_object* v_baseSubst_1086_, lean_object* v_recursor_1087_, lean_object* v_a_1088_, lean_object* v_a_1089_, lean_object* v_a_1090_, lean_object* v_a_1091_){
_start:
{
lean_object* v___x_1093_; 
lean_inc(v_mvarId_1080_);
v___x_1093_ = l_Lean_MVarId_getType(v_mvarId_1080_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_);
if (lean_obj_tag(v___x_1093_) == 0)
{
lean_object* v_a_1094_; lean_object* v___x_1095_; 
v_a_1094_ = lean_ctor_get(v___x_1093_, 0);
lean_inc(v_a_1094_);
lean_dec_ref_known(v___x_1093_, 1);
lean_inc(v_a_1091_);
lean_inc_ref(v_a_1090_);
lean_inc(v_a_1089_);
lean_inc_ref(v_a_1088_);
lean_inc_ref(v_recursor_1087_);
v___x_1095_ = lean_infer_type(v_recursor_1087_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_);
if (lean_obj_tag(v___x_1095_) == 0)
{
lean_object* v_a_1096_; lean_object* v_paramsPos_1097_; lean_object* v_produceMotive_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; uint8_t v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; 
v_a_1096_ = lean_ctor_get(v___x_1095_, 0);
lean_inc(v_a_1096_);
lean_dec_ref_known(v___x_1095_, 1);
v_paramsPos_1097_ = lean_ctor_get(v_recursorInfo_1082_, 5);
v_produceMotive_1098_ = lean_ctor_get(v_recursorInfo_1082_, 7);
v___x_1099_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTargetArity(v_a_1094_);
v___x_1100_ = l_List_lengthTR___redArg(v_produceMotive_1098_);
v___x_1101_ = l_List_lengthTR___redArg(v_paramsPos_1097_);
v___x_1102_ = lean_unsigned_to_nat(1u);
v___x_1103_ = lean_nat_add(v___x_1101_, v___x_1102_);
lean_dec(v___x_1101_);
v___x_1104_ = lean_unsigned_to_nat(0u);
v___x_1105_ = 0;
v___x_1106_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize___closed__0));
v___x_1107_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop(v_mvarId_1080_, v_givenNames_1081_, v_recursorInfo_1082_, v_reverted_1083_, v_major_1084_, v_indices_1085_, v_baseSubst_1086_, v___x_1099_, v___x_1100_, v___x_1103_, v___x_1104_, v_recursor_1087_, v_a_1096_, v___x_1105_, v___x_1106_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_);
lean_dec(v___x_1100_);
lean_dec(v___x_1099_);
return v___x_1107_;
}
else
{
lean_object* v_a_1108_; lean_object* v___x_1110_; uint8_t v_isShared_1111_; uint8_t v_isSharedCheck_1115_; 
lean_dec(v_a_1094_);
lean_dec_ref(v_recursor_1087_);
lean_dec(v_baseSubst_1086_);
lean_dec_ref(v_major_1084_);
lean_dec(v_mvarId_1080_);
v_a_1108_ = lean_ctor_get(v___x_1095_, 0);
v_isSharedCheck_1115_ = !lean_is_exclusive(v___x_1095_);
if (v_isSharedCheck_1115_ == 0)
{
v___x_1110_ = v___x_1095_;
v_isShared_1111_ = v_isSharedCheck_1115_;
goto v_resetjp_1109_;
}
else
{
lean_inc(v_a_1108_);
lean_dec(v___x_1095_);
v___x_1110_ = lean_box(0);
v_isShared_1111_ = v_isSharedCheck_1115_;
goto v_resetjp_1109_;
}
v_resetjp_1109_:
{
lean_object* v___x_1113_; 
if (v_isShared_1111_ == 0)
{
v___x_1113_ = v___x_1110_;
goto v_reusejp_1112_;
}
else
{
lean_object* v_reuseFailAlloc_1114_; 
v_reuseFailAlloc_1114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1114_, 0, v_a_1108_);
v___x_1113_ = v_reuseFailAlloc_1114_;
goto v_reusejp_1112_;
}
v_reusejp_1112_:
{
return v___x_1113_;
}
}
}
}
else
{
lean_object* v_a_1116_; lean_object* v___x_1118_; uint8_t v_isShared_1119_; uint8_t v_isSharedCheck_1123_; 
lean_dec_ref(v_recursor_1087_);
lean_dec(v_baseSubst_1086_);
lean_dec_ref(v_major_1084_);
lean_dec(v_mvarId_1080_);
v_a_1116_ = lean_ctor_get(v___x_1093_, 0);
v_isSharedCheck_1123_ = !lean_is_exclusive(v___x_1093_);
if (v_isSharedCheck_1123_ == 0)
{
v___x_1118_ = v___x_1093_;
v_isShared_1119_ = v_isSharedCheck_1123_;
goto v_resetjp_1117_;
}
else
{
lean_inc(v_a_1116_);
lean_dec(v___x_1093_);
v___x_1118_ = lean_box(0);
v_isShared_1119_ = v_isSharedCheck_1123_;
goto v_resetjp_1117_;
}
v_resetjp_1117_:
{
lean_object* v___x_1121_; 
if (v_isShared_1119_ == 0)
{
v___x_1121_ = v___x_1118_;
goto v_reusejp_1120_;
}
else
{
lean_object* v_reuseFailAlloc_1122_; 
v_reuseFailAlloc_1122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1122_, 0, v_a_1116_);
v___x_1121_ = v_reuseFailAlloc_1122_;
goto v_reusejp_1120_;
}
v_reusejp_1120_:
{
return v___x_1121_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize___boxed(lean_object* v_mvarId_1124_, lean_object* v_givenNames_1125_, lean_object* v_recursorInfo_1126_, lean_object* v_reverted_1127_, lean_object* v_major_1128_, lean_object* v_indices_1129_, lean_object* v_baseSubst_1130_, lean_object* v_recursor_1131_, lean_object* v_a_1132_, lean_object* v_a_1133_, lean_object* v_a_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_){
_start:
{
lean_object* v_res_1137_; 
v_res_1137_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize(v_mvarId_1124_, v_givenNames_1125_, v_recursorInfo_1126_, v_reverted_1127_, v_major_1128_, v_indices_1129_, v_baseSubst_1130_, v_recursor_1131_, v_a_1132_, v_a_1133_, v_a_1134_, v_a_1135_);
lean_dec(v_a_1135_);
lean_dec_ref(v_a_1134_);
lean_dec(v_a_1133_);
lean_dec_ref(v_a_1132_);
lean_dec_ref(v_indices_1129_);
lean_dec_ref(v_reverted_1127_);
lean_dec_ref(v_recursorInfo_1126_);
lean_dec_ref(v_givenNames_1125_);
return v_res_1137_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg___closed__1(void){
_start:
{
lean_object* v___x_1139_; lean_object* v___x_1140_; 
v___x_1139_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg___closed__0));
v___x_1140_ = l_Lean_stringToMessageData(v___x_1139_);
return v___x_1140_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg(lean_object* v_tacticName_1141_, lean_object* v_mvarId_1142_, lean_object* v_majorType_1143_, lean_object* v_a_1144_, lean_object* v_a_1145_, lean_object* v_a_1146_, lean_object* v_a_1147_){
_start:
{
lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; 
v___x_1149_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg___closed__1, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg___closed__1);
v___x_1150_ = l_Lean_indentExpr(v_majorType_1143_);
v___x_1151_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1151_, 0, v___x_1149_);
lean_ctor_set(v___x_1151_, 1, v___x_1150_);
v___x_1152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1152_, 0, v___x_1151_);
v___x_1153_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1141_, v_mvarId_1142_, v___x_1152_, v_a_1144_, v_a_1145_, v_a_1146_, v_a_1147_);
return v___x_1153_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg___boxed(lean_object* v_tacticName_1154_, lean_object* v_mvarId_1155_, lean_object* v_majorType_1156_, lean_object* v_a_1157_, lean_object* v_a_1158_, lean_object* v_a_1159_, lean_object* v_a_1160_, lean_object* v_a_1161_){
_start:
{
lean_object* v_res_1162_; 
v_res_1162_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg(v_tacticName_1154_, v_mvarId_1155_, v_majorType_1156_, v_a_1157_, v_a_1158_, v_a_1159_, v_a_1160_);
lean_dec(v_a_1160_);
lean_dec_ref(v_a_1159_);
lean_dec(v_a_1158_);
lean_dec_ref(v_a_1157_);
return v_res_1162_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType(lean_object* v_00_u03b1_1163_, lean_object* v_tacticName_1164_, lean_object* v_mvarId_1165_, lean_object* v_majorType_1166_, lean_object* v_a_1167_, lean_object* v_a_1168_, lean_object* v_a_1169_, lean_object* v_a_1170_){
_start:
{
lean_object* v___x_1172_; 
v___x_1172_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg(v_tacticName_1164_, v_mvarId_1165_, v_majorType_1166_, v_a_1167_, v_a_1168_, v_a_1169_, v_a_1170_);
return v___x_1172_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___boxed(lean_object* v_00_u03b1_1173_, lean_object* v_tacticName_1174_, lean_object* v_mvarId_1175_, lean_object* v_majorType_1176_, lean_object* v_a_1177_, lean_object* v_a_1178_, lean_object* v_a_1179_, lean_object* v_a_1180_, lean_object* v_a_1181_){
_start:
{
lean_object* v_res_1182_; 
v_res_1182_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType(v_00_u03b1_1173_, v_tacticName_1174_, v_mvarId_1175_, v_majorType_1176_, v_a_1177_, v_a_1178_, v_a_1179_, v_a_1180_);
lean_dec(v_a_1180_);
lean_dec_ref(v_a_1179_);
lean_dec(v_a_1178_);
lean_dec_ref(v_a_1177_);
return v_res_1182_;
}
}
LEAN_EXPORT uint8_t l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___lam__0(lean_object* v_x_1183_){
_start:
{
uint8_t v___x_1184_; 
v___x_1184_ = 0;
return v___x_1184_;
}
}
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___lam__0___boxed(lean_object* v_x_1185_){
_start:
{
uint8_t v_res_1186_; lean_object* v_r_1187_; 
v_res_1186_ = l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___lam__0(v_x_1185_);
lean_dec(v_x_1185_);
v_r_1187_ = lean_box(v_res_1186_);
return v_r_1187_;
}
}
LEAN_EXPORT uint8_t l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___lam__1(lean_object* v_fvarId_1188_, lean_object* v_x_1189_){
_start:
{
uint8_t v___x_1190_; 
v___x_1190_ = l_Lean_instBEqFVarId_beq(v_fvarId_1188_, v_x_1189_);
return v___x_1190_;
}
}
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___lam__1___boxed(lean_object* v_fvarId_1191_, lean_object* v_x_1192_){
_start:
{
uint8_t v_res_1193_; lean_object* v_r_1194_; 
v_res_1193_ = l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___lam__1(v_fvarId_1191_, v_x_1192_);
lean_dec(v_x_1192_);
lean_dec(v_fvarId_1191_);
v_r_1194_ = lean_box(v_res_1193_);
return v_r_1194_;
}
}
static lean_object* _init_l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; 
v___x_1196_ = lean_box(0);
v___x_1197_ = lean_unsigned_to_nat(16u);
v___x_1198_ = lean_mk_array(v___x_1197_, v___x_1196_);
return v___x_1198_;
}
}
static lean_object* _init_l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; 
v___x_1199_ = lean_obj_once(&l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__1, &l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__1_once, _init_l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__1);
v___x_1200_ = lean_unsigned_to_nat(0u);
v___x_1201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1201_, 0, v___x_1200_);
lean_ctor_set(v___x_1201_, 1, v___x_1199_);
return v___x_1201_;
}
}
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg(lean_object* v_localDecl_1202_, lean_object* v_fvarId_1203_, uint8_t v_generalizeNondepLet_1204_, lean_object* v___y_1205_){
_start:
{
uint8_t v_fst_1208_; lean_object* v_snd_1209_; lean_object* v___f_1227_; lean_object* v___f_1228_; 
v___f_1227_ = ((lean_object*)(l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__0));
v___f_1228_ = lean_alloc_closure((void*)(l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_1228_, 0, v_fvarId_1203_);
if (lean_obj_tag(v_localDecl_1202_) == 0)
{
lean_object* v_type_1229_; lean_object* v___x_1230_; uint8_t v_fst_1232_; lean_object* v_mctx_1233_; lean_object* v_mctx_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; uint8_t v___y_1254_; uint8_t v___x_1261_; uint8_t v___x_1262_; 
v_type_1229_ = lean_ctor_get(v_localDecl_1202_, 3);
lean_inc_ref(v_type_1229_);
lean_dec_ref_known(v_localDecl_1202_, 4);
v___x_1230_ = lean_st_ref_get(v___y_1205_);
v_mctx_1250_ = lean_ctor_get(v___x_1230_, 0);
lean_inc_ref_n(v_mctx_1250_, 2);
lean_dec(v___x_1230_);
v___x_1251_ = lean_obj_once(&l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__2, &l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__2_once, _init_l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__2);
v___x_1252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1252_, 0, v___x_1251_);
lean_ctor_set(v___x_1252_, 1, v_mctx_1250_);
v___x_1261_ = l_Lean_Expr_hasFVar(v_type_1229_);
v___x_1262_ = lean_bool_not(v___x_1261_);
if (v___x_1262_ == 0)
{
v___y_1254_ = v___x_1262_;
goto v___jp_1253_;
}
else
{
uint8_t v___x_1263_; uint8_t v___x_1264_; 
v___x_1263_ = l_Lean_Expr_hasMVar(v_type_1229_);
v___x_1264_ = lean_bool_not(v___x_1263_);
v___y_1254_ = v___x_1264_;
goto v___jp_1253_;
}
v___jp_1231_:
{
lean_object* v___x_1234_; lean_object* v_cache_1235_; lean_object* v_zetaDeltaFVarIds_1236_; lean_object* v_postponed_1237_; lean_object* v_diag_1238_; lean_object* v___x_1240_; uint8_t v_isShared_1241_; uint8_t v_isSharedCheck_1248_; 
v___x_1234_ = lean_st_ref_take(v___y_1205_);
v_cache_1235_ = lean_ctor_get(v___x_1234_, 1);
v_zetaDeltaFVarIds_1236_ = lean_ctor_get(v___x_1234_, 2);
v_postponed_1237_ = lean_ctor_get(v___x_1234_, 3);
v_diag_1238_ = lean_ctor_get(v___x_1234_, 4);
v_isSharedCheck_1248_ = !lean_is_exclusive(v___x_1234_);
if (v_isSharedCheck_1248_ == 0)
{
lean_object* v_unused_1249_; 
v_unused_1249_ = lean_ctor_get(v___x_1234_, 0);
lean_dec(v_unused_1249_);
v___x_1240_ = v___x_1234_;
v_isShared_1241_ = v_isSharedCheck_1248_;
goto v_resetjp_1239_;
}
else
{
lean_inc(v_diag_1238_);
lean_inc(v_postponed_1237_);
lean_inc(v_zetaDeltaFVarIds_1236_);
lean_inc(v_cache_1235_);
lean_dec(v___x_1234_);
v___x_1240_ = lean_box(0);
v_isShared_1241_ = v_isSharedCheck_1248_;
goto v_resetjp_1239_;
}
v_resetjp_1239_:
{
lean_object* v___x_1243_; 
if (v_isShared_1241_ == 0)
{
lean_ctor_set(v___x_1240_, 0, v_mctx_1233_);
v___x_1243_ = v___x_1240_;
goto v_reusejp_1242_;
}
else
{
lean_object* v_reuseFailAlloc_1247_; 
v_reuseFailAlloc_1247_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1247_, 0, v_mctx_1233_);
lean_ctor_set(v_reuseFailAlloc_1247_, 1, v_cache_1235_);
lean_ctor_set(v_reuseFailAlloc_1247_, 2, v_zetaDeltaFVarIds_1236_);
lean_ctor_set(v_reuseFailAlloc_1247_, 3, v_postponed_1237_);
lean_ctor_set(v_reuseFailAlloc_1247_, 4, v_diag_1238_);
v___x_1243_ = v_reuseFailAlloc_1247_;
goto v_reusejp_1242_;
}
v_reusejp_1242_:
{
lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; 
v___x_1244_ = lean_st_ref_set(v___y_1205_, v___x_1243_);
v___x_1245_ = lean_box(v_fst_1232_);
v___x_1246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1246_, 0, v___x_1245_);
return v___x_1246_;
}
}
}
v___jp_1253_:
{
if (v___y_1254_ == 0)
{
lean_object* v___x_1255_; lean_object* v_snd_1256_; lean_object* v_fst_1257_; lean_object* v_mctx_1258_; uint8_t v___x_1259_; 
lean_dec_ref(v_mctx_1250_);
v___x_1255_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1228_, v___f_1227_, v_type_1229_, v___x_1252_);
v_snd_1256_ = lean_ctor_get(v___x_1255_, 1);
lean_inc(v_snd_1256_);
v_fst_1257_ = lean_ctor_get(v___x_1255_, 0);
lean_inc(v_fst_1257_);
lean_dec_ref(v___x_1255_);
v_mctx_1258_ = lean_ctor_get(v_snd_1256_, 1);
lean_inc_ref(v_mctx_1258_);
lean_dec(v_snd_1256_);
v___x_1259_ = lean_unbox(v_fst_1257_);
lean_dec(v_fst_1257_);
v_fst_1232_ = v___x_1259_;
v_mctx_1233_ = v_mctx_1258_;
goto v___jp_1231_;
}
else
{
uint8_t v___x_1260_; 
lean_dec_ref_known(v___x_1252_, 2);
lean_dec_ref(v_type_1229_);
lean_dec_ref(v___f_1228_);
v___x_1260_ = 0;
v_fst_1232_ = v___x_1260_;
v_mctx_1233_ = v_mctx_1250_;
goto v___jp_1231_;
}
}
}
else
{
lean_object* v_type_1265_; lean_object* v_value_1266_; uint8_t v_nondep_1267_; lean_object* v___y_1269_; uint8_t v___y_1270_; uint8_t v___y_1271_; uint8_t v_fst_1277_; lean_object* v_snd_1278_; lean_object* v___y_1284_; uint8_t v___y_1285_; uint8_t v___y_1286_; uint8_t v___y_1295_; 
v_type_1265_ = lean_ctor_get(v_localDecl_1202_, 3);
lean_inc_ref(v_type_1265_);
v_value_1266_ = lean_ctor_get(v_localDecl_1202_, 4);
lean_inc_ref(v_value_1266_);
v_nondep_1267_ = lean_ctor_get_uint8(v_localDecl_1202_, sizeof(void*)*5);
lean_dec_ref_known(v_localDecl_1202_, 5);
if (v_generalizeNondepLet_1204_ == 0)
{
v___y_1295_ = v_generalizeNondepLet_1204_;
goto v___jp_1294_;
}
else
{
if (v_nondep_1267_ == 0)
{
v___y_1295_ = v_nondep_1267_;
goto v___jp_1294_;
}
else
{
lean_object* v___x_1304_; uint8_t v_fst_1306_; lean_object* v_mctx_1307_; lean_object* v_mctx_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; uint8_t v___y_1328_; uint8_t v___x_1335_; uint8_t v___x_1336_; 
lean_dec_ref(v_value_1266_);
v___x_1304_ = lean_st_ref_get(v___y_1205_);
v_mctx_1324_ = lean_ctor_get(v___x_1304_, 0);
lean_inc_ref_n(v_mctx_1324_, 2);
lean_dec(v___x_1304_);
v___x_1325_ = lean_obj_once(&l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__2, &l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__2_once, _init_l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__2);
v___x_1326_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1326_, 0, v___x_1325_);
lean_ctor_set(v___x_1326_, 1, v_mctx_1324_);
v___x_1335_ = l_Lean_Expr_hasFVar(v_type_1265_);
v___x_1336_ = lean_bool_not(v___x_1335_);
if (v___x_1336_ == 0)
{
v___y_1328_ = v___x_1336_;
goto v___jp_1327_;
}
else
{
uint8_t v___x_1337_; uint8_t v___x_1338_; 
v___x_1337_ = l_Lean_Expr_hasMVar(v_type_1265_);
v___x_1338_ = lean_bool_not(v___x_1337_);
v___y_1328_ = v___x_1338_;
goto v___jp_1327_;
}
v___jp_1305_:
{
lean_object* v___x_1308_; lean_object* v_cache_1309_; lean_object* v_zetaDeltaFVarIds_1310_; lean_object* v_postponed_1311_; lean_object* v_diag_1312_; lean_object* v___x_1314_; uint8_t v_isShared_1315_; uint8_t v_isSharedCheck_1322_; 
v___x_1308_ = lean_st_ref_take(v___y_1205_);
v_cache_1309_ = lean_ctor_get(v___x_1308_, 1);
v_zetaDeltaFVarIds_1310_ = lean_ctor_get(v___x_1308_, 2);
v_postponed_1311_ = lean_ctor_get(v___x_1308_, 3);
v_diag_1312_ = lean_ctor_get(v___x_1308_, 4);
v_isSharedCheck_1322_ = !lean_is_exclusive(v___x_1308_);
if (v_isSharedCheck_1322_ == 0)
{
lean_object* v_unused_1323_; 
v_unused_1323_ = lean_ctor_get(v___x_1308_, 0);
lean_dec(v_unused_1323_);
v___x_1314_ = v___x_1308_;
v_isShared_1315_ = v_isSharedCheck_1322_;
goto v_resetjp_1313_;
}
else
{
lean_inc(v_diag_1312_);
lean_inc(v_postponed_1311_);
lean_inc(v_zetaDeltaFVarIds_1310_);
lean_inc(v_cache_1309_);
lean_dec(v___x_1308_);
v___x_1314_ = lean_box(0);
v_isShared_1315_ = v_isSharedCheck_1322_;
goto v_resetjp_1313_;
}
v_resetjp_1313_:
{
lean_object* v___x_1317_; 
if (v_isShared_1315_ == 0)
{
lean_ctor_set(v___x_1314_, 0, v_mctx_1307_);
v___x_1317_ = v___x_1314_;
goto v_reusejp_1316_;
}
else
{
lean_object* v_reuseFailAlloc_1321_; 
v_reuseFailAlloc_1321_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1321_, 0, v_mctx_1307_);
lean_ctor_set(v_reuseFailAlloc_1321_, 1, v_cache_1309_);
lean_ctor_set(v_reuseFailAlloc_1321_, 2, v_zetaDeltaFVarIds_1310_);
lean_ctor_set(v_reuseFailAlloc_1321_, 3, v_postponed_1311_);
lean_ctor_set(v_reuseFailAlloc_1321_, 4, v_diag_1312_);
v___x_1317_ = v_reuseFailAlloc_1321_;
goto v_reusejp_1316_;
}
v_reusejp_1316_:
{
lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; 
v___x_1318_ = lean_st_ref_set(v___y_1205_, v___x_1317_);
v___x_1319_ = lean_box(v_fst_1306_);
v___x_1320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1320_, 0, v___x_1319_);
return v___x_1320_;
}
}
}
v___jp_1327_:
{
if (v___y_1328_ == 0)
{
lean_object* v___x_1329_; lean_object* v_snd_1330_; lean_object* v_fst_1331_; lean_object* v_mctx_1332_; uint8_t v___x_1333_; 
lean_dec_ref(v_mctx_1324_);
v___x_1329_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1228_, v___f_1227_, v_type_1265_, v___x_1326_);
v_snd_1330_ = lean_ctor_get(v___x_1329_, 1);
lean_inc(v_snd_1330_);
v_fst_1331_ = lean_ctor_get(v___x_1329_, 0);
lean_inc(v_fst_1331_);
lean_dec_ref(v___x_1329_);
v_mctx_1332_ = lean_ctor_get(v_snd_1330_, 1);
lean_inc_ref(v_mctx_1332_);
lean_dec(v_snd_1330_);
v___x_1333_ = lean_unbox(v_fst_1331_);
lean_dec(v_fst_1331_);
v_fst_1306_ = v___x_1333_;
v_mctx_1307_ = v_mctx_1332_;
goto v___jp_1305_;
}
else
{
uint8_t v___x_1334_; 
lean_dec_ref_known(v___x_1326_, 2);
lean_dec_ref(v_type_1265_);
lean_dec_ref(v___f_1228_);
v___x_1334_ = 0;
v_fst_1306_ = v___x_1334_;
v_mctx_1307_ = v_mctx_1324_;
goto v___jp_1305_;
}
}
}
}
v___jp_1268_:
{
if (v___y_1271_ == 0)
{
lean_object* v___x_1272_; lean_object* v_fst_1273_; lean_object* v_snd_1274_; uint8_t v___x_1275_; 
v___x_1272_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1228_, v___f_1227_, v_value_1266_, v___y_1269_);
v_fst_1273_ = lean_ctor_get(v___x_1272_, 0);
lean_inc(v_fst_1273_);
v_snd_1274_ = lean_ctor_get(v___x_1272_, 1);
lean_inc(v_snd_1274_);
lean_dec_ref(v___x_1272_);
v___x_1275_ = lean_unbox(v_fst_1273_);
lean_dec(v_fst_1273_);
v_fst_1208_ = v___x_1275_;
v_snd_1209_ = v_snd_1274_;
goto v___jp_1207_;
}
else
{
lean_dec_ref(v_value_1266_);
lean_dec_ref(v___f_1228_);
v_fst_1208_ = v___y_1270_;
v_snd_1209_ = v___y_1269_;
goto v___jp_1207_;
}
}
v___jp_1276_:
{
uint8_t v___x_1279_; uint8_t v___x_1280_; 
v___x_1279_ = l_Lean_Expr_hasFVar(v_value_1266_);
v___x_1280_ = lean_bool_not(v___x_1279_);
if (v___x_1280_ == 0)
{
v___y_1269_ = v_snd_1278_;
v___y_1270_ = v_fst_1277_;
v___y_1271_ = v___x_1280_;
goto v___jp_1268_;
}
else
{
uint8_t v___x_1281_; uint8_t v___x_1282_; 
v___x_1281_ = l_Lean_Expr_hasMVar(v_value_1266_);
v___x_1282_ = lean_bool_not(v___x_1281_);
v___y_1269_ = v_snd_1278_;
v___y_1270_ = v_fst_1277_;
v___y_1271_ = v___x_1282_;
goto v___jp_1268_;
}
}
v___jp_1283_:
{
if (v___y_1286_ == 0)
{
lean_object* v___x_1287_; lean_object* v_fst_1288_; uint8_t v___x_1289_; 
lean_inc_ref(v___f_1228_);
v___x_1287_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1228_, v___f_1227_, v_type_1265_, v___y_1284_);
v_fst_1288_ = lean_ctor_get(v___x_1287_, 0);
lean_inc(v_fst_1288_);
v___x_1289_ = lean_unbox(v_fst_1288_);
if (v___x_1289_ == 0)
{
lean_object* v_snd_1290_; uint8_t v___x_1291_; 
v_snd_1290_ = lean_ctor_get(v___x_1287_, 1);
lean_inc(v_snd_1290_);
lean_dec_ref(v___x_1287_);
v___x_1291_ = lean_unbox(v_fst_1288_);
lean_dec(v_fst_1288_);
v_fst_1277_ = v___x_1291_;
v_snd_1278_ = v_snd_1290_;
goto v___jp_1276_;
}
else
{
lean_object* v_snd_1292_; uint8_t v___x_1293_; 
lean_dec_ref(v_value_1266_);
lean_dec_ref(v___f_1228_);
v_snd_1292_ = lean_ctor_get(v___x_1287_, 1);
lean_inc(v_snd_1292_);
lean_dec_ref(v___x_1287_);
v___x_1293_ = lean_unbox(v_fst_1288_);
lean_dec(v_fst_1288_);
v_fst_1208_ = v___x_1293_;
v_snd_1209_ = v_snd_1292_;
goto v___jp_1207_;
}
}
else
{
lean_dec_ref(v_type_1265_);
v_fst_1277_ = v___y_1285_;
v_snd_1278_ = v___y_1284_;
goto v___jp_1276_;
}
}
v___jp_1294_:
{
lean_object* v___x_1296_; lean_object* v_mctx_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; uint8_t v___x_1300_; uint8_t v___x_1301_; 
v___x_1296_ = lean_st_ref_get(v___y_1205_);
v_mctx_1297_ = lean_ctor_get(v___x_1296_, 0);
lean_inc_ref(v_mctx_1297_);
lean_dec(v___x_1296_);
v___x_1298_ = lean_obj_once(&l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__2, &l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__2_once, _init_l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__2);
v___x_1299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1299_, 0, v___x_1298_);
lean_ctor_set(v___x_1299_, 1, v_mctx_1297_);
v___x_1300_ = l_Lean_Expr_hasFVar(v_type_1265_);
v___x_1301_ = lean_bool_not(v___x_1300_);
if (v___x_1301_ == 0)
{
v___y_1284_ = v___x_1299_;
v___y_1285_ = v___y_1295_;
v___y_1286_ = v___x_1301_;
goto v___jp_1283_;
}
else
{
uint8_t v___x_1302_; uint8_t v___x_1303_; 
v___x_1302_ = l_Lean_Expr_hasMVar(v_type_1265_);
v___x_1303_ = lean_bool_not(v___x_1302_);
v___y_1284_ = v___x_1299_;
v___y_1285_ = v___y_1295_;
v___y_1286_ = v___x_1303_;
goto v___jp_1283_;
}
}
}
v___jp_1207_:
{
lean_object* v_mctx_1210_; lean_object* v___x_1211_; lean_object* v_cache_1212_; lean_object* v_zetaDeltaFVarIds_1213_; lean_object* v_postponed_1214_; lean_object* v_diag_1215_; lean_object* v___x_1217_; uint8_t v_isShared_1218_; uint8_t v_isSharedCheck_1225_; 
v_mctx_1210_ = lean_ctor_get(v_snd_1209_, 1);
lean_inc_ref(v_mctx_1210_);
lean_dec_ref(v_snd_1209_);
v___x_1211_ = lean_st_ref_take(v___y_1205_);
v_cache_1212_ = lean_ctor_get(v___x_1211_, 1);
v_zetaDeltaFVarIds_1213_ = lean_ctor_get(v___x_1211_, 2);
v_postponed_1214_ = lean_ctor_get(v___x_1211_, 3);
v_diag_1215_ = lean_ctor_get(v___x_1211_, 4);
v_isSharedCheck_1225_ = !lean_is_exclusive(v___x_1211_);
if (v_isSharedCheck_1225_ == 0)
{
lean_object* v_unused_1226_; 
v_unused_1226_ = lean_ctor_get(v___x_1211_, 0);
lean_dec(v_unused_1226_);
v___x_1217_ = v___x_1211_;
v_isShared_1218_ = v_isSharedCheck_1225_;
goto v_resetjp_1216_;
}
else
{
lean_inc(v_diag_1215_);
lean_inc(v_postponed_1214_);
lean_inc(v_zetaDeltaFVarIds_1213_);
lean_inc(v_cache_1212_);
lean_dec(v___x_1211_);
v___x_1217_ = lean_box(0);
v_isShared_1218_ = v_isSharedCheck_1225_;
goto v_resetjp_1216_;
}
v_resetjp_1216_:
{
lean_object* v___x_1220_; 
if (v_isShared_1218_ == 0)
{
lean_ctor_set(v___x_1217_, 0, v_mctx_1210_);
v___x_1220_ = v___x_1217_;
goto v_reusejp_1219_;
}
else
{
lean_object* v_reuseFailAlloc_1224_; 
v_reuseFailAlloc_1224_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1224_, 0, v_mctx_1210_);
lean_ctor_set(v_reuseFailAlloc_1224_, 1, v_cache_1212_);
lean_ctor_set(v_reuseFailAlloc_1224_, 2, v_zetaDeltaFVarIds_1213_);
lean_ctor_set(v_reuseFailAlloc_1224_, 3, v_postponed_1214_);
lean_ctor_set(v_reuseFailAlloc_1224_, 4, v_diag_1215_);
v___x_1220_ = v_reuseFailAlloc_1224_;
goto v_reusejp_1219_;
}
v_reusejp_1219_:
{
lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; 
v___x_1221_ = lean_st_ref_set(v___y_1205_, v___x_1220_);
v___x_1222_ = lean_box(v_fst_1208_);
v___x_1223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1223_, 0, v___x_1222_);
return v___x_1223_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___boxed(lean_object* v_localDecl_1339_, lean_object* v_fvarId_1340_, lean_object* v_generalizeNondepLet_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_){
_start:
{
uint8_t v_generalizeNondepLet_boxed_1344_; lean_object* v_res_1345_; 
v_generalizeNondepLet_boxed_1344_ = lean_unbox(v_generalizeNondepLet_1341_);
v_res_1345_ = l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg(v_localDecl_1339_, v_fvarId_1340_, v_generalizeNondepLet_boxed_1344_, v___y_1342_);
lean_dec(v___y_1342_);
return v_res_1345_;
}
}
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0(lean_object* v_localDecl_1346_, lean_object* v_fvarId_1347_, uint8_t v_generalizeNondepLet_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_){
_start:
{
lean_object* v___x_1354_; 
v___x_1354_ = l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg(v_localDecl_1346_, v_fvarId_1347_, v_generalizeNondepLet_1348_, v___y_1350_);
return v___x_1354_;
}
}
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___boxed(lean_object* v_localDecl_1355_, lean_object* v_fvarId_1356_, lean_object* v_generalizeNondepLet_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_){
_start:
{
uint8_t v_generalizeNondepLet_boxed_1363_; lean_object* v_res_1364_; 
v_generalizeNondepLet_boxed_1363_ = lean_unbox(v_generalizeNondepLet_1357_);
v_res_1364_ = l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0(v_localDecl_1355_, v_fvarId_1356_, v_generalizeNondepLet_boxed_1363_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_);
lean_dec(v___y_1361_);
lean_dec_ref(v___y_1360_);
lean_dec(v___y_1359_);
lean_dec_ref(v___y_1358_);
return v_res_1364_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2___redArg(lean_object* v_e_1365_, lean_object* v_fvarId_1366_, lean_object* v___y_1367_){
_start:
{
lean_object* v___x_1369_; uint8_t v_fst_1371_; lean_object* v_mctx_1372_; lean_object* v_mctx_1389_; lean_object* v___f_1390_; lean_object* v___f_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; uint8_t v___y_1395_; uint8_t v___x_1402_; uint8_t v___x_1403_; 
v___x_1369_ = lean_st_ref_get(v___y_1367_);
v_mctx_1389_ = lean_ctor_get(v___x_1369_, 0);
lean_inc_ref_n(v_mctx_1389_, 2);
lean_dec(v___x_1369_);
v___f_1390_ = ((lean_object*)(l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__0));
v___f_1391_ = lean_alloc_closure((void*)(l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_1391_, 0, v_fvarId_1366_);
v___x_1392_ = lean_obj_once(&l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__2, &l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__2_once, _init_l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__2);
v___x_1393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1393_, 0, v___x_1392_);
lean_ctor_set(v___x_1393_, 1, v_mctx_1389_);
v___x_1402_ = l_Lean_Expr_hasFVar(v_e_1365_);
v___x_1403_ = lean_bool_not(v___x_1402_);
if (v___x_1403_ == 0)
{
v___y_1395_ = v___x_1403_;
goto v___jp_1394_;
}
else
{
uint8_t v___x_1404_; uint8_t v___x_1405_; 
v___x_1404_ = l_Lean_Expr_hasMVar(v_e_1365_);
v___x_1405_ = lean_bool_not(v___x_1404_);
v___y_1395_ = v___x_1405_;
goto v___jp_1394_;
}
v___jp_1370_:
{
lean_object* v___x_1373_; lean_object* v_cache_1374_; lean_object* v_zetaDeltaFVarIds_1375_; lean_object* v_postponed_1376_; lean_object* v_diag_1377_; lean_object* v___x_1379_; uint8_t v_isShared_1380_; uint8_t v_isSharedCheck_1387_; 
v___x_1373_ = lean_st_ref_take(v___y_1367_);
v_cache_1374_ = lean_ctor_get(v___x_1373_, 1);
v_zetaDeltaFVarIds_1375_ = lean_ctor_get(v___x_1373_, 2);
v_postponed_1376_ = lean_ctor_get(v___x_1373_, 3);
v_diag_1377_ = lean_ctor_get(v___x_1373_, 4);
v_isSharedCheck_1387_ = !lean_is_exclusive(v___x_1373_);
if (v_isSharedCheck_1387_ == 0)
{
lean_object* v_unused_1388_; 
v_unused_1388_ = lean_ctor_get(v___x_1373_, 0);
lean_dec(v_unused_1388_);
v___x_1379_ = v___x_1373_;
v_isShared_1380_ = v_isSharedCheck_1387_;
goto v_resetjp_1378_;
}
else
{
lean_inc(v_diag_1377_);
lean_inc(v_postponed_1376_);
lean_inc(v_zetaDeltaFVarIds_1375_);
lean_inc(v_cache_1374_);
lean_dec(v___x_1373_);
v___x_1379_ = lean_box(0);
v_isShared_1380_ = v_isSharedCheck_1387_;
goto v_resetjp_1378_;
}
v_resetjp_1378_:
{
lean_object* v___x_1382_; 
if (v_isShared_1380_ == 0)
{
lean_ctor_set(v___x_1379_, 0, v_mctx_1372_);
v___x_1382_ = v___x_1379_;
goto v_reusejp_1381_;
}
else
{
lean_object* v_reuseFailAlloc_1386_; 
v_reuseFailAlloc_1386_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1386_, 0, v_mctx_1372_);
lean_ctor_set(v_reuseFailAlloc_1386_, 1, v_cache_1374_);
lean_ctor_set(v_reuseFailAlloc_1386_, 2, v_zetaDeltaFVarIds_1375_);
lean_ctor_set(v_reuseFailAlloc_1386_, 3, v_postponed_1376_);
lean_ctor_set(v_reuseFailAlloc_1386_, 4, v_diag_1377_);
v___x_1382_ = v_reuseFailAlloc_1386_;
goto v_reusejp_1381_;
}
v_reusejp_1381_:
{
lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; 
v___x_1383_ = lean_st_ref_set(v___y_1367_, v___x_1382_);
v___x_1384_ = lean_box(v_fst_1371_);
v___x_1385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1385_, 0, v___x_1384_);
return v___x_1385_;
}
}
}
v___jp_1394_:
{
if (v___y_1395_ == 0)
{
lean_object* v___x_1396_; lean_object* v_snd_1397_; lean_object* v_fst_1398_; lean_object* v_mctx_1399_; uint8_t v___x_1400_; 
lean_dec_ref(v_mctx_1389_);
v___x_1396_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1391_, v___f_1390_, v_e_1365_, v___x_1393_);
v_snd_1397_ = lean_ctor_get(v___x_1396_, 1);
lean_inc(v_snd_1397_);
v_fst_1398_ = lean_ctor_get(v___x_1396_, 0);
lean_inc(v_fst_1398_);
lean_dec_ref(v___x_1396_);
v_mctx_1399_ = lean_ctor_get(v_snd_1397_, 1);
lean_inc_ref(v_mctx_1399_);
lean_dec(v_snd_1397_);
v___x_1400_ = lean_unbox(v_fst_1398_);
lean_dec(v_fst_1398_);
v_fst_1371_ = v___x_1400_;
v_mctx_1372_ = v_mctx_1399_;
goto v___jp_1370_;
}
else
{
uint8_t v___x_1401_; 
lean_dec_ref_known(v___x_1393_, 2);
lean_dec_ref(v___f_1391_);
lean_dec_ref(v_e_1365_);
v___x_1401_ = 0;
v_fst_1371_ = v___x_1401_;
v_mctx_1372_ = v_mctx_1389_;
goto v___jp_1370_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2___redArg___boxed(lean_object* v_e_1406_, lean_object* v_fvarId_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_){
_start:
{
lean_object* v_res_1410_; 
v_res_1410_ = l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2___redArg(v_e_1406_, v_fvarId_1407_, v___y_1408_);
lean_dec(v___y_1408_);
return v_res_1410_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2(lean_object* v_e_1411_, lean_object* v_fvarId_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_){
_start:
{
lean_object* v___x_1418_; 
v___x_1418_ = l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2___redArg(v_e_1411_, v_fvarId_1412_, v___y_1414_);
return v___x_1418_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2___boxed(lean_object* v_e_1419_, lean_object* v_fvarId_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_){
_start:
{
lean_object* v_res_1426_; 
v_res_1426_ = l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2(v_e_1419_, v_fvarId_1420_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_);
lean_dec(v___y_1424_);
lean_dec_ref(v___y_1423_);
lean_dec(v___y_1422_);
lean_dec_ref(v___y_1421_);
return v_res_1426_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_Meta_getMajorTypeIndices_spec__1(lean_object* v_a_1427_, lean_object* v_x_1428_){
_start:
{
if (lean_obj_tag(v_x_1428_) == 0)
{
uint8_t v___x_1429_; 
v___x_1429_ = 0;
return v___x_1429_;
}
else
{
lean_object* v_head_1430_; lean_object* v_tail_1431_; uint8_t v___x_1432_; 
v_head_1430_ = lean_ctor_get(v_x_1428_, 0);
v_tail_1431_ = lean_ctor_get(v_x_1428_, 1);
v___x_1432_ = lean_nat_dec_eq(v_a_1427_, v_head_1430_);
if (v___x_1432_ == 0)
{
v_x_1428_ = v_tail_1431_;
goto _start;
}
else
{
return v___x_1432_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_Meta_getMajorTypeIndices_spec__1___boxed(lean_object* v_a_1434_, lean_object* v_x_1435_){
_start:
{
uint8_t v_res_1436_; lean_object* v_r_1437_; 
v_res_1436_ = l_List_elem___at___00Lean_Meta_getMajorTypeIndices_spec__1(v_a_1434_, v_x_1435_);
lean_dec(v_x_1435_);
lean_dec(v_a_1434_);
v_r_1437_ = lean_box(v_res_1436_);
return v_r_1437_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_1439_; lean_object* v___x_1440_; 
v___x_1439_ = ((lean_object*)(l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__0));
v___x_1440_ = l_Lean_stringToMessageData(v___x_1439_);
return v___x_1440_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_1442_; lean_object* v___x_1443_; 
v___x_1442_ = ((lean_object*)(l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__2));
v___x_1443_ = l_Lean_stringToMessageData(v___x_1442_);
return v___x_1443_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__5(void){
_start:
{
lean_object* v___x_1445_; lean_object* v___x_1446_; 
v___x_1445_ = ((lean_object*)(l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__4));
v___x_1446_ = l_Lean_stringToMessageData(v___x_1445_);
return v___x_1446_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__7(void){
_start:
{
lean_object* v___x_1448_; lean_object* v___x_1449_; 
v___x_1448_ = ((lean_object*)(l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__6));
v___x_1449_ = l_Lean_stringToMessageData(v___x_1448_);
return v___x_1449_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg(lean_object* v_majorTypeArgs_1450_, lean_object* v_idx_1451_, lean_object* v_tacticName_1452_, lean_object* v_mvarId_1453_, lean_object* v_idxPos_1454_, lean_object* v_recursorInfo_1455_, lean_object* v_majorType_1456_, lean_object* v_n_1457_, lean_object* v_i_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_){
_start:
{
lean_object* v_zero_1464_; uint8_t v_isZero_1465_; 
v_zero_1464_ = lean_unsigned_to_nat(0u);
v_isZero_1465_ = lean_nat_dec_eq(v_i_1458_, v_zero_1464_);
if (v_isZero_1465_ == 1)
{
lean_object* v___x_1466_; lean_object* v___x_1467_; 
lean_dec(v_i_1458_);
lean_dec_ref(v_majorType_1456_);
lean_dec(v_mvarId_1453_);
lean_dec(v_tacticName_1452_);
lean_dec_ref(v_idx_1451_);
v___x_1466_ = lean_box(0);
v___x_1467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1467_, 0, v___x_1466_);
return v___x_1467_;
}
else
{
lean_object* v_one_1468_; lean_object* v_n_1469_; lean_object* v___y_1471_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v_arg_1475_; lean_object* v___y_1477_; lean_object* v___y_1478_; lean_object* v___y_1479_; lean_object* v___y_1480_; uint8_t v___y_1481_; lean_object* v___y_1520_; lean_object* v___y_1521_; lean_object* v___y_1522_; lean_object* v___y_1523_; lean_object* v___y_1528_; lean_object* v___y_1529_; lean_object* v___y_1530_; lean_object* v___y_1531_; uint8_t v___y_1553_; uint8_t v___x_1563_; uint8_t v___x_1564_; 
v_one_1468_ = lean_unsigned_to_nat(1u);
v_n_1469_ = lean_nat_sub(v_i_1458_, v_one_1468_);
lean_dec(v_i_1458_);
v___x_1473_ = lean_nat_sub(v_n_1457_, v_n_1469_);
v___x_1474_ = lean_nat_sub(v___x_1473_, v_one_1468_);
lean_dec(v___x_1473_);
v_arg_1475_ = lean_array_fget_borrowed(v_majorTypeArgs_1450_, v___x_1474_);
v___x_1563_ = lean_nat_dec_eq(v___x_1474_, v_idxPos_1454_);
v___x_1564_ = lean_bool_not(v___x_1563_);
if (v___x_1564_ == 0)
{
v___y_1553_ = v___x_1564_;
goto v___jp_1552_;
}
else
{
uint8_t v___x_1565_; 
v___x_1565_ = lean_expr_eqv(v_arg_1475_, v_idx_1451_);
v___y_1553_ = v___x_1565_;
goto v___jp_1552_;
}
v___jp_1470_:
{
if (lean_obj_tag(v___y_1471_) == 0)
{
lean_dec_ref_known(v___y_1471_, 1);
v_i_1458_ = v_n_1469_;
goto _start;
}
else
{
lean_dec(v_n_1469_);
lean_dec_ref(v_majorType_1456_);
lean_dec(v_mvarId_1453_);
lean_dec(v_tacticName_1452_);
lean_dec_ref(v_idx_1451_);
return v___y_1471_;
}
}
v___jp_1476_:
{
if (v___y_1481_ == 0)
{
lean_dec(v___x_1474_);
v_i_1458_ = v_n_1469_;
goto _start;
}
else
{
uint8_t v___x_1483_; 
v___x_1483_ = l_Lean_Expr_isFVar(v_arg_1475_);
if (v___x_1483_ == 0)
{
lean_dec(v___x_1474_);
v_i_1458_ = v_n_1469_;
goto _start;
}
else
{
lean_object* v___x_1485_; lean_object* v___x_1486_; 
v___x_1485_ = l_Lean_Expr_fvarId_x21(v_idx_1451_);
v___x_1486_ = l_Lean_FVarId_getDecl___redArg(v___x_1485_, v___y_1478_, v___y_1480_, v___y_1479_);
if (lean_obj_tag(v___x_1486_) == 0)
{
lean_object* v_a_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v_a_1490_; lean_object* v___x_1492_; uint8_t v_isShared_1493_; uint8_t v_isSharedCheck_1510_; 
v_a_1487_ = lean_ctor_get(v___x_1486_, 0);
lean_inc(v_a_1487_);
lean_dec_ref_known(v___x_1486_, 1);
v___x_1488_ = l_Lean_Expr_fvarId_x21(v_arg_1475_);
v___x_1489_ = l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg(v_a_1487_, v___x_1488_, v___y_1481_, v___y_1477_);
v_a_1490_ = lean_ctor_get(v___x_1489_, 0);
v_isSharedCheck_1510_ = !lean_is_exclusive(v___x_1489_);
if (v_isSharedCheck_1510_ == 0)
{
v___x_1492_ = v___x_1489_;
v_isShared_1493_ = v_isSharedCheck_1510_;
goto v_resetjp_1491_;
}
else
{
lean_inc(v_a_1490_);
lean_dec(v___x_1489_);
v___x_1492_ = lean_box(0);
v_isShared_1493_ = v_isSharedCheck_1510_;
goto v_resetjp_1491_;
}
v_resetjp_1491_:
{
uint8_t v___x_1494_; 
v___x_1494_ = lean_unbox(v_a_1490_);
lean_dec(v_a_1490_);
if (v___x_1494_ == 0)
{
lean_del_object(v___x_1492_);
lean_dec(v___x_1474_);
v_i_1458_ = v_n_1469_;
goto _start;
}
else
{
lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1504_; 
v___x_1496_ = lean_obj_once(&l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1, &l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1_once, _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1);
lean_inc_ref(v_idx_1451_);
v___x_1497_ = l_Lean_MessageData_ofExpr(v_idx_1451_);
v___x_1498_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1498_, 0, v___x_1496_);
lean_ctor_set(v___x_1498_, 1, v___x_1497_);
v___x_1499_ = lean_obj_once(&l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__3, &l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__3_once, _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__3);
v___x_1500_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1500_, 0, v___x_1498_);
lean_ctor_set(v___x_1500_, 1, v___x_1499_);
v___x_1501_ = lean_nat_add(v___x_1474_, v_one_1468_);
lean_dec(v___x_1474_);
v___x_1502_ = l_Nat_reprFast(v___x_1501_);
if (v_isShared_1493_ == 0)
{
lean_ctor_set_tag(v___x_1492_, 3);
lean_ctor_set(v___x_1492_, 0, v___x_1502_);
v___x_1504_ = v___x_1492_;
goto v_reusejp_1503_;
}
else
{
lean_object* v_reuseFailAlloc_1509_; 
v_reuseFailAlloc_1509_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1509_, 0, v___x_1502_);
v___x_1504_ = v_reuseFailAlloc_1509_;
goto v_reusejp_1503_;
}
v_reusejp_1503_:
{
lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; 
v___x_1505_ = l_Lean_MessageData_ofFormat(v___x_1504_);
v___x_1506_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1506_, 0, v___x_1500_);
lean_ctor_set(v___x_1506_, 1, v___x_1505_);
v___x_1507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1507_, 0, v___x_1506_);
lean_inc(v_mvarId_1453_);
lean_inc(v_tacticName_1452_);
v___x_1508_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1452_, v_mvarId_1453_, v___x_1507_, v___y_1478_, v___y_1477_, v___y_1480_, v___y_1479_);
v___y_1471_ = v___x_1508_;
goto v___jp_1470_;
}
}
}
}
else
{
lean_object* v_a_1511_; lean_object* v___x_1513_; uint8_t v_isShared_1514_; uint8_t v_isSharedCheck_1518_; 
lean_dec(v___x_1474_);
lean_dec(v_n_1469_);
lean_dec_ref(v_majorType_1456_);
lean_dec(v_mvarId_1453_);
lean_dec(v_tacticName_1452_);
lean_dec_ref(v_idx_1451_);
v_a_1511_ = lean_ctor_get(v___x_1486_, 0);
v_isSharedCheck_1518_ = !lean_is_exclusive(v___x_1486_);
if (v_isSharedCheck_1518_ == 0)
{
v___x_1513_ = v___x_1486_;
v_isShared_1514_ = v_isSharedCheck_1518_;
goto v_resetjp_1512_;
}
else
{
lean_inc(v_a_1511_);
lean_dec(v___x_1486_);
v___x_1513_ = lean_box(0);
v_isShared_1514_ = v_isSharedCheck_1518_;
goto v_resetjp_1512_;
}
v_resetjp_1512_:
{
lean_object* v___x_1516_; 
if (v_isShared_1514_ == 0)
{
v___x_1516_ = v___x_1513_;
goto v_reusejp_1515_;
}
else
{
lean_object* v_reuseFailAlloc_1517_; 
v_reuseFailAlloc_1517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1517_, 0, v_a_1511_);
v___x_1516_ = v_reuseFailAlloc_1517_;
goto v_reusejp_1515_;
}
v_reusejp_1515_:
{
return v___x_1516_;
}
}
}
}
}
}
v___jp_1519_:
{
uint8_t v___x_1524_; 
v___x_1524_ = lean_nat_dec_lt(v_idxPos_1454_, v___x_1474_);
if (v___x_1524_ == 0)
{
v___y_1477_ = v___y_1521_;
v___y_1478_ = v___y_1520_;
v___y_1479_ = v___y_1523_;
v___y_1480_ = v___y_1522_;
v___y_1481_ = v___x_1524_;
goto v___jp_1476_;
}
else
{
lean_object* v_indicesPos_1525_; uint8_t v___x_1526_; 
v_indicesPos_1525_ = lean_ctor_get(v_recursorInfo_1455_, 6);
v___x_1526_ = l_List_elem___at___00Lean_Meta_getMajorTypeIndices_spec__1(v___x_1474_, v_indicesPos_1525_);
v___y_1477_ = v___y_1521_;
v___y_1478_ = v___y_1520_;
v___y_1479_ = v___y_1523_;
v___y_1480_ = v___y_1522_;
v___y_1481_ = v___x_1526_;
goto v___jp_1476_;
}
}
v___jp_1527_:
{
uint8_t v___x_1532_; 
v___x_1532_ = lean_nat_dec_lt(v___x_1474_, v_idxPos_1454_);
if (v___x_1532_ == 0)
{
v___y_1520_ = v___y_1528_;
v___y_1521_ = v___y_1529_;
v___y_1522_ = v___y_1530_;
v___y_1523_ = v___y_1531_;
goto v___jp_1519_;
}
else
{
lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v_a_1535_; lean_object* v___x_1537_; uint8_t v_isShared_1538_; uint8_t v_isSharedCheck_1551_; 
v___x_1533_ = l_Lean_Expr_fvarId_x21(v_idx_1451_);
lean_inc(v_arg_1475_);
v___x_1534_ = l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2___redArg(v_arg_1475_, v___x_1533_, v___y_1529_);
v_a_1535_ = lean_ctor_get(v___x_1534_, 0);
v_isSharedCheck_1551_ = !lean_is_exclusive(v___x_1534_);
if (v_isSharedCheck_1551_ == 0)
{
v___x_1537_ = v___x_1534_;
v_isShared_1538_ = v_isSharedCheck_1551_;
goto v_resetjp_1536_;
}
else
{
lean_inc(v_a_1535_);
lean_dec(v___x_1534_);
v___x_1537_ = lean_box(0);
v_isShared_1538_ = v_isSharedCheck_1551_;
goto v_resetjp_1536_;
}
v_resetjp_1536_:
{
uint8_t v___x_1539_; 
v___x_1539_ = lean_unbox(v_a_1535_);
lean_dec(v_a_1535_);
if (v___x_1539_ == 0)
{
lean_del_object(v___x_1537_);
v___y_1520_ = v___y_1528_;
v___y_1521_ = v___y_1529_;
v___y_1522_ = v___y_1530_;
v___y_1523_ = v___y_1531_;
goto v___jp_1519_;
}
else
{
lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1548_; 
v___x_1540_ = lean_obj_once(&l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1, &l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1_once, _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1);
lean_inc_ref(v_idx_1451_);
v___x_1541_ = l_Lean_MessageData_ofExpr(v_idx_1451_);
v___x_1542_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1542_, 0, v___x_1540_);
lean_ctor_set(v___x_1542_, 1, v___x_1541_);
v___x_1543_ = lean_obj_once(&l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__5, &l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__5_once, _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__5);
v___x_1544_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1544_, 0, v___x_1542_);
lean_ctor_set(v___x_1544_, 1, v___x_1543_);
lean_inc_ref(v_majorType_1456_);
v___x_1545_ = l_Lean_indentExpr(v_majorType_1456_);
v___x_1546_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1546_, 0, v___x_1544_);
lean_ctor_set(v___x_1546_, 1, v___x_1545_);
if (v_isShared_1538_ == 0)
{
lean_ctor_set_tag(v___x_1537_, 1);
lean_ctor_set(v___x_1537_, 0, v___x_1546_);
v___x_1548_ = v___x_1537_;
goto v_reusejp_1547_;
}
else
{
lean_object* v_reuseFailAlloc_1550_; 
v_reuseFailAlloc_1550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1550_, 0, v___x_1546_);
v___x_1548_ = v_reuseFailAlloc_1550_;
goto v_reusejp_1547_;
}
v_reusejp_1547_:
{
lean_object* v___x_1549_; 
lean_inc(v_mvarId_1453_);
lean_inc(v_tacticName_1452_);
v___x_1549_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1452_, v_mvarId_1453_, v___x_1548_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_);
if (lean_obj_tag(v___x_1549_) == 0)
{
lean_dec_ref_known(v___x_1549_, 1);
v___y_1520_ = v___y_1528_;
v___y_1521_ = v___y_1529_;
v___y_1522_ = v___y_1530_;
v___y_1523_ = v___y_1531_;
goto v___jp_1519_;
}
else
{
lean_dec(v___x_1474_);
v___y_1471_ = v___x_1549_;
goto v___jp_1470_;
}
}
}
}
}
}
v___jp_1552_:
{
if (v___y_1553_ == 0)
{
v___y_1528_ = v___y_1459_;
v___y_1529_ = v___y_1460_;
v___y_1530_ = v___y_1461_;
v___y_1531_ = v___y_1462_;
goto v___jp_1527_;
}
else
{
lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; 
v___x_1554_ = lean_obj_once(&l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1, &l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1_once, _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1);
lean_inc_ref(v_idx_1451_);
v___x_1555_ = l_Lean_MessageData_ofExpr(v_idx_1451_);
v___x_1556_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1556_, 0, v___x_1554_);
lean_ctor_set(v___x_1556_, 1, v___x_1555_);
v___x_1557_ = lean_obj_once(&l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__7, &l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__7_once, _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__7);
v___x_1558_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1558_, 0, v___x_1556_);
lean_ctor_set(v___x_1558_, 1, v___x_1557_);
lean_inc_ref(v_majorType_1456_);
v___x_1559_ = l_Lean_indentExpr(v_majorType_1456_);
v___x_1560_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1560_, 0, v___x_1558_);
lean_ctor_set(v___x_1560_, 1, v___x_1559_);
v___x_1561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1561_, 0, v___x_1560_);
lean_inc(v_mvarId_1453_);
lean_inc(v_tacticName_1452_);
v___x_1562_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1452_, v_mvarId_1453_, v___x_1561_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_);
if (lean_obj_tag(v___x_1562_) == 0)
{
lean_dec_ref_known(v___x_1562_, 1);
v___y_1528_ = v___y_1459_;
v___y_1529_ = v___y_1460_;
v___y_1530_ = v___y_1461_;
v___y_1531_ = v___y_1462_;
goto v___jp_1527_;
}
else
{
lean_dec(v___x_1474_);
v___y_1471_ = v___x_1562_;
goto v___jp_1470_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___boxed(lean_object* v_majorTypeArgs_1566_, lean_object* v_idx_1567_, lean_object* v_tacticName_1568_, lean_object* v_mvarId_1569_, lean_object* v_idxPos_1570_, lean_object* v_recursorInfo_1571_, lean_object* v_majorType_1572_, lean_object* v_n_1573_, lean_object* v_i_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_){
_start:
{
lean_object* v_res_1580_; 
v_res_1580_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg(v_majorTypeArgs_1566_, v_idx_1567_, v_tacticName_1568_, v_mvarId_1569_, v_idxPos_1570_, v_recursorInfo_1571_, v_majorType_1572_, v_n_1573_, v_i_1574_, v___y_1575_, v___y_1576_, v___y_1577_, v___y_1578_);
lean_dec(v___y_1578_);
lean_dec_ref(v___y_1577_);
lean_dec(v___y_1576_);
lean_dec_ref(v___y_1575_);
lean_dec(v_n_1573_);
lean_dec_ref(v_recursorInfo_1571_);
lean_dec(v_idxPos_1570_);
lean_dec_ref(v_majorTypeArgs_1566_);
return v_res_1580_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__1(void){
_start:
{
lean_object* v___x_1582_; lean_object* v___x_1583_; 
v___x_1582_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__0));
v___x_1583_ = l_Lean_stringToMessageData(v___x_1582_);
return v___x_1583_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__3(void){
_start:
{
lean_object* v___x_1585_; lean_object* v___x_1586_; 
v___x_1585_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__2));
v___x_1586_ = l_Lean_stringToMessageData(v___x_1585_);
return v___x_1586_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__5(void){
_start:
{
lean_object* v___x_1588_; lean_object* v___x_1589_; 
v___x_1588_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__4));
v___x_1589_ = l_Lean_stringToMessageData(v___x_1588_);
return v___x_1589_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4(lean_object* v_majorTypeArgs_1590_, lean_object* v_tacticName_1591_, lean_object* v_mvarId_1592_, lean_object* v_recursorInfo_1593_, lean_object* v_majorType_1594_, size_t v_sz_1595_, size_t v_i_1596_, lean_object* v_bs_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_){
_start:
{
uint8_t v___x_1603_; 
v___x_1603_ = lean_usize_dec_lt(v_i_1596_, v_sz_1595_);
if (v___x_1603_ == 0)
{
lean_object* v___x_1604_; 
lean_dec_ref(v_majorType_1594_);
lean_dec(v_mvarId_1592_);
lean_dec(v_tacticName_1591_);
v___x_1604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1604_, 0, v_bs_1597_);
return v___x_1604_;
}
else
{
lean_object* v_v_1605_; lean_object* v___x_1606_; lean_object* v_bs_x27_1607_; lean_object* v_a_1609_; lean_object* v___x_1614_; uint8_t v___x_1615_; 
v_v_1605_ = lean_array_uget(v_bs_1597_, v_i_1596_);
v___x_1606_ = lean_unsigned_to_nat(0u);
v_bs_x27_1607_ = lean_array_uset(v_bs_1597_, v_i_1596_, v___x_1606_);
v___x_1614_ = lean_array_get_size(v_majorTypeArgs_1590_);
v___x_1615_ = lean_nat_dec_le(v___x_1614_, v_v_1605_);
if (v___x_1615_ == 0)
{
lean_object* v_idx_1616_; lean_object* v___y_1618_; lean_object* v___y_1619_; lean_object* v___y_1620_; lean_object* v___y_1621_; uint8_t v___x_1631_; 
v_idx_1616_ = lean_array_fget_borrowed(v_majorTypeArgs_1590_, v_v_1605_);
v___x_1631_ = l_Lean_Expr_isFVar(v_idx_1616_);
if (v___x_1631_ == 0)
{
lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; 
v___x_1632_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__1);
lean_inc(v_idx_1616_);
v___x_1633_ = l_Lean_MessageData_ofExpr(v_idx_1616_);
v___x_1634_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1634_, 0, v___x_1632_);
lean_ctor_set(v___x_1634_, 1, v___x_1633_);
v___x_1635_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__3);
v___x_1636_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1636_, 0, v___x_1634_);
lean_ctor_set(v___x_1636_, 1, v___x_1635_);
lean_inc_ref(v_majorType_1594_);
v___x_1637_ = l_Lean_indentExpr(v_majorType_1594_);
v___x_1638_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1638_, 0, v___x_1636_);
lean_ctor_set(v___x_1638_, 1, v___x_1637_);
v___x_1639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1639_, 0, v___x_1638_);
lean_inc(v_mvarId_1592_);
lean_inc(v_tacticName_1591_);
v___x_1640_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1591_, v_mvarId_1592_, v___x_1639_, v___y_1598_, v___y_1599_, v___y_1600_, v___y_1601_);
if (lean_obj_tag(v___x_1640_) == 0)
{
lean_dec_ref_known(v___x_1640_, 1);
v___y_1618_ = v___y_1598_;
v___y_1619_ = v___y_1599_;
v___y_1620_ = v___y_1600_;
v___y_1621_ = v___y_1601_;
goto v___jp_1617_;
}
else
{
lean_object* v_a_1641_; lean_object* v___x_1643_; uint8_t v_isShared_1644_; uint8_t v_isSharedCheck_1648_; 
lean_dec_ref(v_bs_x27_1607_);
lean_dec(v_v_1605_);
lean_dec_ref(v_majorType_1594_);
lean_dec(v_mvarId_1592_);
lean_dec(v_tacticName_1591_);
v_a_1641_ = lean_ctor_get(v___x_1640_, 0);
v_isSharedCheck_1648_ = !lean_is_exclusive(v___x_1640_);
if (v_isSharedCheck_1648_ == 0)
{
v___x_1643_ = v___x_1640_;
v_isShared_1644_ = v_isSharedCheck_1648_;
goto v_resetjp_1642_;
}
else
{
lean_inc(v_a_1641_);
lean_dec(v___x_1640_);
v___x_1643_ = lean_box(0);
v_isShared_1644_ = v_isSharedCheck_1648_;
goto v_resetjp_1642_;
}
v_resetjp_1642_:
{
lean_object* v___x_1646_; 
if (v_isShared_1644_ == 0)
{
v___x_1646_ = v___x_1643_;
goto v_reusejp_1645_;
}
else
{
lean_object* v_reuseFailAlloc_1647_; 
v_reuseFailAlloc_1647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1647_, 0, v_a_1641_);
v___x_1646_ = v_reuseFailAlloc_1647_;
goto v_reusejp_1645_;
}
v_reusejp_1645_:
{
return v___x_1646_;
}
}
}
}
else
{
v___y_1618_ = v___y_1598_;
v___y_1619_ = v___y_1599_;
v___y_1620_ = v___y_1600_;
v___y_1621_ = v___y_1601_;
goto v___jp_1617_;
}
v___jp_1617_:
{
lean_object* v___x_1622_; 
lean_inc_ref(v_majorType_1594_);
lean_inc(v_mvarId_1592_);
lean_inc(v_tacticName_1591_);
lean_inc(v_idx_1616_);
v___x_1622_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg(v_majorTypeArgs_1590_, v_idx_1616_, v_tacticName_1591_, v_mvarId_1592_, v_v_1605_, v_recursorInfo_1593_, v_majorType_1594_, v___x_1614_, v___x_1614_, v___y_1618_, v___y_1619_, v___y_1620_, v___y_1621_);
lean_dec(v_v_1605_);
if (lean_obj_tag(v___x_1622_) == 0)
{
lean_dec_ref_known(v___x_1622_, 1);
lean_inc(v_idx_1616_);
v_a_1609_ = v_idx_1616_;
goto v___jp_1608_;
}
else
{
lean_object* v_a_1623_; lean_object* v___x_1625_; uint8_t v_isShared_1626_; uint8_t v_isSharedCheck_1630_; 
lean_dec_ref(v_bs_x27_1607_);
lean_dec_ref(v_majorType_1594_);
lean_dec(v_mvarId_1592_);
lean_dec(v_tacticName_1591_);
v_a_1623_ = lean_ctor_get(v___x_1622_, 0);
v_isSharedCheck_1630_ = !lean_is_exclusive(v___x_1622_);
if (v_isSharedCheck_1630_ == 0)
{
v___x_1625_ = v___x_1622_;
v_isShared_1626_ = v_isSharedCheck_1630_;
goto v_resetjp_1624_;
}
else
{
lean_inc(v_a_1623_);
lean_dec(v___x_1622_);
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
}
else
{
lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; 
lean_dec(v_v_1605_);
v___x_1649_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__5, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__5);
lean_inc_ref(v_majorType_1594_);
v___x_1650_ = l_Lean_indentExpr(v_majorType_1594_);
v___x_1651_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1651_, 0, v___x_1649_);
lean_ctor_set(v___x_1651_, 1, v___x_1650_);
v___x_1652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1652_, 0, v___x_1651_);
lean_inc(v_mvarId_1592_);
lean_inc(v_tacticName_1591_);
v___x_1653_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1591_, v_mvarId_1592_, v___x_1652_, v___y_1598_, v___y_1599_, v___y_1600_, v___y_1601_);
if (lean_obj_tag(v___x_1653_) == 0)
{
lean_object* v_a_1654_; 
v_a_1654_ = lean_ctor_get(v___x_1653_, 0);
lean_inc(v_a_1654_);
lean_dec_ref_known(v___x_1653_, 1);
v_a_1609_ = v_a_1654_;
goto v___jp_1608_;
}
else
{
lean_object* v_a_1655_; lean_object* v___x_1657_; uint8_t v_isShared_1658_; uint8_t v_isSharedCheck_1662_; 
lean_dec_ref(v_bs_x27_1607_);
lean_dec_ref(v_majorType_1594_);
lean_dec(v_mvarId_1592_);
lean_dec(v_tacticName_1591_);
v_a_1655_ = lean_ctor_get(v___x_1653_, 0);
v_isSharedCheck_1662_ = !lean_is_exclusive(v___x_1653_);
if (v_isSharedCheck_1662_ == 0)
{
v___x_1657_ = v___x_1653_;
v_isShared_1658_ = v_isSharedCheck_1662_;
goto v_resetjp_1656_;
}
else
{
lean_inc(v_a_1655_);
lean_dec(v___x_1653_);
v___x_1657_ = lean_box(0);
v_isShared_1658_ = v_isSharedCheck_1662_;
goto v_resetjp_1656_;
}
v_resetjp_1656_:
{
lean_object* v___x_1660_; 
if (v_isShared_1658_ == 0)
{
v___x_1660_ = v___x_1657_;
goto v_reusejp_1659_;
}
else
{
lean_object* v_reuseFailAlloc_1661_; 
v_reuseFailAlloc_1661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1661_, 0, v_a_1655_);
v___x_1660_ = v_reuseFailAlloc_1661_;
goto v_reusejp_1659_;
}
v_reusejp_1659_:
{
return v___x_1660_;
}
}
}
}
v___jp_1608_:
{
size_t v___x_1610_; size_t v___x_1611_; lean_object* v___x_1612_; 
v___x_1610_ = ((size_t)1ULL);
v___x_1611_ = lean_usize_add(v_i_1596_, v___x_1610_);
v___x_1612_ = lean_array_uset(v_bs_x27_1607_, v_i_1596_, v_a_1609_);
v_i_1596_ = v___x_1611_;
v_bs_1597_ = v___x_1612_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___boxed(lean_object* v_majorTypeArgs_1663_, lean_object* v_tacticName_1664_, lean_object* v_mvarId_1665_, lean_object* v_recursorInfo_1666_, lean_object* v_majorType_1667_, lean_object* v_sz_1668_, lean_object* v_i_1669_, lean_object* v_bs_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_){
_start:
{
size_t v_sz_boxed_1676_; size_t v_i_boxed_1677_; lean_object* v_res_1678_; 
v_sz_boxed_1676_ = lean_unbox_usize(v_sz_1668_);
lean_dec(v_sz_1668_);
v_i_boxed_1677_ = lean_unbox_usize(v_i_1669_);
lean_dec(v_i_1669_);
v_res_1678_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4(v_majorTypeArgs_1663_, v_tacticName_1664_, v_mvarId_1665_, v_recursorInfo_1666_, v_majorType_1667_, v_sz_boxed_1676_, v_i_boxed_1677_, v_bs_1670_, v___y_1671_, v___y_1672_, v___y_1673_, v___y_1674_);
lean_dec(v___y_1674_);
lean_dec_ref(v___y_1673_);
lean_dec(v___y_1672_);
lean_dec_ref(v___y_1671_);
lean_dec_ref(v_recursorInfo_1666_);
lean_dec_ref(v_majorTypeArgs_1663_);
return v_res_1678_;
}
}
static lean_object* _init_l_Lean_Meta_getMajorTypeIndices___closed__0(void){
_start:
{
lean_object* v___x_1679_; lean_object* v_dummy_1680_; 
v___x_1679_ = lean_box(0);
v_dummy_1680_ = l_Lean_Expr_sort___override(v___x_1679_);
return v_dummy_1680_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMajorTypeIndices(lean_object* v_mvarId_1681_, lean_object* v_tacticName_1682_, lean_object* v_recursorInfo_1683_, lean_object* v_majorType_1684_, lean_object* v_a_1685_, lean_object* v_a_1686_, lean_object* v_a_1687_, lean_object* v_a_1688_){
_start:
{
lean_object* v_indicesPos_1690_; lean_object* v_nargs_1691_; lean_object* v_dummy_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v_majorTypeArgs_1696_; lean_object* v___x_1697_; size_t v_sz_1698_; size_t v___x_1699_; lean_object* v___x_1700_; 
v_indicesPos_1690_ = lean_ctor_get(v_recursorInfo_1683_, 6);
v_nargs_1691_ = l_Lean_Expr_getAppNumArgs(v_majorType_1684_);
v_dummy_1692_ = lean_obj_once(&l_Lean_Meta_getMajorTypeIndices___closed__0, &l_Lean_Meta_getMajorTypeIndices___closed__0_once, _init_l_Lean_Meta_getMajorTypeIndices___closed__0);
lean_inc(v_nargs_1691_);
v___x_1693_ = lean_mk_array(v_nargs_1691_, v_dummy_1692_);
v___x_1694_ = lean_unsigned_to_nat(1u);
v___x_1695_ = lean_nat_sub(v_nargs_1691_, v___x_1694_);
lean_dec(v_nargs_1691_);
lean_inc_ref(v_majorType_1684_);
v_majorTypeArgs_1696_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_majorType_1684_, v___x_1693_, v___x_1695_);
lean_inc(v_indicesPos_1690_);
v___x_1697_ = lean_array_mk(v_indicesPos_1690_);
v_sz_1698_ = lean_array_size(v___x_1697_);
v___x_1699_ = ((size_t)0ULL);
v___x_1700_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4(v_majorTypeArgs_1696_, v_tacticName_1682_, v_mvarId_1681_, v_recursorInfo_1683_, v_majorType_1684_, v_sz_1698_, v___x_1699_, v___x_1697_, v_a_1685_, v_a_1686_, v_a_1687_, v_a_1688_);
lean_dec_ref(v_recursorInfo_1683_);
lean_dec_ref(v_majorTypeArgs_1696_);
return v___x_1700_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMajorTypeIndices___boxed(lean_object* v_mvarId_1701_, lean_object* v_tacticName_1702_, lean_object* v_recursorInfo_1703_, lean_object* v_majorType_1704_, lean_object* v_a_1705_, lean_object* v_a_1706_, lean_object* v_a_1707_, lean_object* v_a_1708_, lean_object* v_a_1709_){
_start:
{
lean_object* v_res_1710_; 
v_res_1710_ = l_Lean_Meta_getMajorTypeIndices(v_mvarId_1701_, v_tacticName_1702_, v_recursorInfo_1703_, v_majorType_1704_, v_a_1705_, v_a_1706_, v_a_1707_, v_a_1708_);
lean_dec(v_a_1708_);
lean_dec_ref(v_a_1707_);
lean_dec(v_a_1706_);
lean_dec_ref(v_a_1705_);
return v_res_1710_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3(lean_object* v_majorTypeArgs_1711_, lean_object* v_idx_1712_, lean_object* v_tacticName_1713_, lean_object* v_mvarId_1714_, lean_object* v_idxPos_1715_, lean_object* v_recursorInfo_1716_, lean_object* v_majorType_1717_, lean_object* v_n_1718_, lean_object* v_i_1719_, lean_object* v_a_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_){
_start:
{
lean_object* v___x_1726_; 
v___x_1726_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg(v_majorTypeArgs_1711_, v_idx_1712_, v_tacticName_1713_, v_mvarId_1714_, v_idxPos_1715_, v_recursorInfo_1716_, v_majorType_1717_, v_n_1718_, v_i_1719_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_);
return v___x_1726_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___boxed(lean_object* v_majorTypeArgs_1727_, lean_object* v_idx_1728_, lean_object* v_tacticName_1729_, lean_object* v_mvarId_1730_, lean_object* v_idxPos_1731_, lean_object* v_recursorInfo_1732_, lean_object* v_majorType_1733_, lean_object* v_n_1734_, lean_object* v_i_1735_, lean_object* v_a_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_){
_start:
{
lean_object* v_res_1742_; 
v_res_1742_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3(v_majorTypeArgs_1727_, v_idx_1728_, v_tacticName_1729_, v_mvarId_1730_, v_idxPos_1731_, v_recursorInfo_1732_, v_majorType_1733_, v_n_1734_, v_i_1735_, v_a_1736_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_);
lean_dec(v___y_1740_);
lean_dec_ref(v___y_1739_);
lean_dec(v___y_1738_);
lean_dec_ref(v___y_1737_);
lean_dec(v_n_1734_);
lean_dec_ref(v_recursorInfo_1732_);
lean_dec(v_idxPos_1731_);
lean_dec_ref(v_majorTypeArgs_1727_);
return v_res_1742_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1___redArg(lean_object* v_name_1743_, lean_object* v_msg_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_){
_start:
{
lean_object* v_ref_1750_; lean_object* v_msg_1751_; lean_object* v___x_1752_; lean_object* v_a_1753_; lean_object* v___x_1755_; uint8_t v_isShared_1756_; uint8_t v_isSharedCheck_1761_; 
v_ref_1750_ = lean_ctor_get(v___y_1747_, 5);
v_msg_1751_ = l_Lean_MessageData_tagWithErrorName(v_msg_1744_, v_name_1743_);
v___x_1752_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1_spec__2(v_msg_1751_, v___y_1745_, v___y_1746_, v___y_1747_, v___y_1748_);
v_a_1753_ = lean_ctor_get(v___x_1752_, 0);
v_isSharedCheck_1761_ = !lean_is_exclusive(v___x_1752_);
if (v_isSharedCheck_1761_ == 0)
{
v___x_1755_ = v___x_1752_;
v_isShared_1756_ = v_isSharedCheck_1761_;
goto v_resetjp_1754_;
}
else
{
lean_inc(v_a_1753_);
lean_dec(v___x_1752_);
v___x_1755_ = lean_box(0);
v_isShared_1756_ = v_isSharedCheck_1761_;
goto v_resetjp_1754_;
}
v_resetjp_1754_:
{
lean_object* v___x_1757_; lean_object* v___x_1759_; 
lean_inc(v_ref_1750_);
v___x_1757_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1757_, 0, v_ref_1750_);
lean_ctor_set(v___x_1757_, 1, v_a_1753_);
if (v_isShared_1756_ == 0)
{
lean_ctor_set_tag(v___x_1755_, 1);
lean_ctor_set(v___x_1755_, 0, v___x_1757_);
v___x_1759_ = v___x_1755_;
goto v_reusejp_1758_;
}
else
{
lean_object* v_reuseFailAlloc_1760_; 
v_reuseFailAlloc_1760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1760_, 0, v___x_1757_);
v___x_1759_ = v_reuseFailAlloc_1760_;
goto v_reusejp_1758_;
}
v_reusejp_1758_:
{
return v___x_1759_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1___redArg___boxed(lean_object* v_name_1762_, lean_object* v_msg_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_){
_start:
{
lean_object* v_res_1769_; 
v_res_1769_ = l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1___redArg(v_name_1762_, v_msg_1763_, v___y_1764_, v___y_1765_, v___y_1766_, v___y_1767_);
lean_dec(v___y_1767_);
lean_dec_ref(v___y_1766_);
lean_dec(v___y_1765_);
lean_dec_ref(v___y_1764_);
return v_res_1769_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Meta_mkRecursorAppPrefix_spec__0(lean_object* v_a_1770_, lean_object* v___x_1771_, lean_object* v_tacticName_1772_, lean_object* v_mvarId_1773_, lean_object* v_x_1774_, lean_object* v_x_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_){
_start:
{
if (lean_obj_tag(v_x_1775_) == 0)
{
lean_object* v___x_1781_; 
lean_dec(v_mvarId_1773_);
lean_dec(v_tacticName_1772_);
lean_dec(v_a_1770_);
v___x_1781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1781_, 0, v_x_1774_);
return v___x_1781_;
}
else
{
lean_object* v_head_1782_; 
v_head_1782_ = lean_ctor_get(v_x_1775_, 0);
if (lean_obj_tag(v_head_1782_) == 0)
{
lean_object* v_tail_1783_; lean_object* v_fst_1784_; lean_object* v___x_1786_; uint8_t v_isShared_1787_; uint8_t v_isSharedCheck_1795_; 
v_tail_1783_ = lean_ctor_get(v_x_1775_, 1);
v_fst_1784_ = lean_ctor_get(v_x_1774_, 0);
v_isSharedCheck_1795_ = !lean_is_exclusive(v_x_1774_);
if (v_isSharedCheck_1795_ == 0)
{
lean_object* v_unused_1796_; 
v_unused_1796_ = lean_ctor_get(v_x_1774_, 1);
lean_dec(v_unused_1796_);
v___x_1786_ = v_x_1774_;
v_isShared_1787_ = v_isSharedCheck_1795_;
goto v_resetjp_1785_;
}
else
{
lean_inc(v_fst_1784_);
lean_dec(v_x_1774_);
v___x_1786_ = lean_box(0);
v_isShared_1787_ = v_isSharedCheck_1795_;
goto v_resetjp_1785_;
}
v_resetjp_1785_:
{
lean_object* v___x_1788_; uint8_t v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1792_; 
lean_inc(v_a_1770_);
v___x_1788_ = lean_array_push(v_fst_1784_, v_a_1770_);
v___x_1789_ = 1;
v___x_1790_ = lean_box(v___x_1789_);
if (v_isShared_1787_ == 0)
{
lean_ctor_set(v___x_1786_, 1, v___x_1790_);
lean_ctor_set(v___x_1786_, 0, v___x_1788_);
v___x_1792_ = v___x_1786_;
goto v_reusejp_1791_;
}
else
{
lean_object* v_reuseFailAlloc_1794_; 
v_reuseFailAlloc_1794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1794_, 0, v___x_1788_);
lean_ctor_set(v_reuseFailAlloc_1794_, 1, v___x_1790_);
v___x_1792_ = v_reuseFailAlloc_1794_;
goto v_reusejp_1791_;
}
v_reusejp_1791_:
{
v_x_1774_ = v___x_1792_;
v_x_1775_ = v_tail_1783_;
goto _start;
}
}
}
else
{
lean_object* v_tail_1797_; lean_object* v_fst_1798_; lean_object* v_snd_1799_; lean_object* v___x_1801_; uint8_t v_isShared_1802_; uint8_t v_isSharedCheck_1816_; 
v_tail_1797_ = lean_ctor_get(v_x_1775_, 1);
v_fst_1798_ = lean_ctor_get(v_x_1774_, 0);
v_snd_1799_ = lean_ctor_get(v_x_1774_, 1);
v_isSharedCheck_1816_ = !lean_is_exclusive(v_x_1774_);
if (v_isSharedCheck_1816_ == 0)
{
v___x_1801_ = v_x_1774_;
v_isShared_1802_ = v_isSharedCheck_1816_;
goto v_resetjp_1800_;
}
else
{
lean_inc(v_snd_1799_);
lean_inc(v_fst_1798_);
lean_dec(v_x_1774_);
v___x_1801_ = lean_box(0);
v_isShared_1802_ = v_isSharedCheck_1816_;
goto v_resetjp_1800_;
}
v_resetjp_1800_:
{
lean_object* v_idx_1803_; lean_object* v___x_1804_; uint8_t v___x_1805_; 
v_idx_1803_ = lean_ctor_get(v_head_1782_, 0);
v___x_1804_ = lean_array_get_size(v___x_1771_);
v___x_1805_ = lean_nat_dec_le(v___x_1804_, v_idx_1803_);
if (v___x_1805_ == 0)
{
lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1809_; 
v___x_1806_ = lean_array_fget_borrowed(v___x_1771_, v_idx_1803_);
lean_inc(v___x_1806_);
v___x_1807_ = lean_array_push(v_fst_1798_, v___x_1806_);
if (v_isShared_1802_ == 0)
{
lean_ctor_set(v___x_1801_, 0, v___x_1807_);
v___x_1809_ = v___x_1801_;
goto v_reusejp_1808_;
}
else
{
lean_object* v_reuseFailAlloc_1811_; 
v_reuseFailAlloc_1811_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1811_, 0, v___x_1807_);
lean_ctor_set(v_reuseFailAlloc_1811_, 1, v_snd_1799_);
v___x_1809_ = v_reuseFailAlloc_1811_;
goto v_reusejp_1808_;
}
v_reusejp_1808_:
{
v_x_1774_ = v___x_1809_;
v_x_1775_ = v_tail_1797_;
goto _start;
}
}
else
{
lean_object* v___x_1812_; lean_object* v___x_1813_; 
lean_del_object(v___x_1801_);
lean_dec(v_snd_1799_);
lean_dec(v_fst_1798_);
v___x_1812_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9);
lean_inc(v_mvarId_1773_);
lean_inc(v_tacticName_1772_);
v___x_1813_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1772_, v_mvarId_1773_, v___x_1812_, v___y_1776_, v___y_1777_, v___y_1778_, v___y_1779_);
if (lean_obj_tag(v___x_1813_) == 0)
{
lean_object* v_a_1814_; 
v_a_1814_ = lean_ctor_get(v___x_1813_, 0);
lean_inc(v_a_1814_);
lean_dec_ref_known(v___x_1813_, 1);
v_x_1774_ = v_a_1814_;
v_x_1775_ = v_tail_1797_;
goto _start;
}
else
{
lean_dec(v_mvarId_1773_);
lean_dec(v_tacticName_1772_);
lean_dec(v_a_1770_);
return v___x_1813_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Meta_mkRecursorAppPrefix_spec__0___boxed(lean_object* v_a_1817_, lean_object* v___x_1818_, lean_object* v_tacticName_1819_, lean_object* v_mvarId_1820_, lean_object* v_x_1821_, lean_object* v_x_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_){
_start:
{
lean_object* v_res_1828_; 
v_res_1828_ = l_List_foldlM___at___00Lean_Meta_mkRecursorAppPrefix_spec__0(v_a_1817_, v___x_1818_, v_tacticName_1819_, v_mvarId_1820_, v_x_1821_, v_x_1822_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_);
lean_dec(v___y_1826_);
lean_dec_ref(v___y_1825_);
lean_dec(v___y_1824_);
lean_dec_ref(v___y_1823_);
lean_dec(v_x_1822_);
lean_dec_ref(v___x_1818_);
return v_res_1828_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__8(void){
_start:
{
lean_object* v___x_1844_; lean_object* v___x_1845_; 
v___x_1844_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__7));
v___x_1845_ = l_Lean_stringToMessageData(v___x_1844_);
return v___x_1845_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__10(void){
_start:
{
lean_object* v___x_1847_; lean_object* v___x_1848_; 
v___x_1847_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__9));
v___x_1848_ = l_Lean_stringToMessageData(v___x_1847_);
return v___x_1848_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__13(void){
_start:
{
lean_object* v___x_1852_; lean_object* v___x_1853_; 
v___x_1852_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__12));
v___x_1853_ = l_Lean_MessageData_ofFormat(v___x_1852_);
return v___x_1853_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__14(void){
_start:
{
lean_object* v___x_1854_; lean_object* v___x_1855_; 
v___x_1854_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__13, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__13_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__13);
v___x_1855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1855_, 0, v___x_1854_);
return v___x_1855_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2(lean_object* v_recursorInfo_1856_, lean_object* v_a_1857_, lean_object* v_tacticName_1858_, lean_object* v_mvarId_1859_, lean_object* v_indices_1860_, lean_object* v_a_1861_, lean_object* v_major_1862_, lean_object* v_x_1863_, lean_object* v_x_1864_, lean_object* v_x_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_){
_start:
{
if (lean_obj_tag(v_x_1863_) == 5)
{
lean_object* v_fn_1871_; lean_object* v_arg_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; 
v_fn_1871_ = lean_ctor_get(v_x_1863_, 0);
lean_inc_ref(v_fn_1871_);
v_arg_1872_ = lean_ctor_get(v_x_1863_, 1);
lean_inc_ref(v_arg_1872_);
lean_dec_ref_known(v_x_1863_, 2);
v___x_1873_ = lean_array_set(v_x_1864_, v_x_1865_, v_arg_1872_);
v___x_1874_ = lean_unsigned_to_nat(1u);
v___x_1875_ = lean_nat_sub(v_x_1865_, v___x_1874_);
lean_dec(v_x_1865_);
v_x_1863_ = v_fn_1871_;
v_x_1864_ = v___x_1873_;
v_x_1865_ = v___x_1875_;
goto _start;
}
else
{
lean_dec(v_x_1865_);
if (lean_obj_tag(v_x_1863_) == 4)
{
lean_object* v_us_1877_; lean_object* v_recursorName_1878_; lean_object* v_univLevelPos_1879_; uint8_t v_depElim_1880_; lean_object* v_paramsPos_1881_; lean_object* v___x_1882_; uint8_t v___x_1883_; lean_object* v___y_1885_; lean_object* v_motive_1886_; lean_object* v___y_1887_; lean_object* v___y_1888_; lean_object* v___y_1889_; lean_object* v___y_1890_; lean_object* v___x_1903_; lean_object* v___x_1904_; 
v_us_1877_ = lean_ctor_get(v_x_1863_, 1);
lean_inc(v_us_1877_);
lean_dec_ref_known(v_x_1863_, 2);
v_recursorName_1878_ = lean_ctor_get(v_recursorInfo_1856_, 0);
lean_inc(v_recursorName_1878_);
v_univLevelPos_1879_ = lean_ctor_get(v_recursorInfo_1856_, 2);
lean_inc(v_univLevelPos_1879_);
v_depElim_1880_ = lean_ctor_get_uint8(v_recursorInfo_1856_, sizeof(void*)*8);
v_paramsPos_1881_ = lean_ctor_get(v_recursorInfo_1856_, 5);
lean_inc(v_paramsPos_1881_);
lean_dec_ref(v_recursorInfo_1856_);
v___x_1882_ = lean_array_mk(v_us_1877_);
v___x_1883_ = 0;
v___x_1903_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__1));
lean_inc(v_mvarId_1859_);
lean_inc(v_tacticName_1858_);
lean_inc(v_a_1857_);
v___x_1904_ = l_List_foldlM___at___00Lean_Meta_mkRecursorAppPrefix_spec__0(v_a_1857_, v___x_1882_, v_tacticName_1858_, v_mvarId_1859_, v___x_1903_, v_univLevelPos_1879_, v___y_1866_, v___y_1867_, v___y_1868_, v___y_1869_);
lean_dec(v_univLevelPos_1879_);
lean_dec_ref(v___x_1882_);
if (lean_obj_tag(v___x_1904_) == 0)
{
lean_object* v_a_1905_; lean_object* v_fst_1906_; lean_object* v_snd_1907_; lean_object* v___x_1909_; uint8_t v_isShared_1910_; uint8_t v_isSharedCheck_1953_; 
v_a_1905_ = lean_ctor_get(v___x_1904_, 0);
lean_inc(v_a_1905_);
lean_dec_ref_known(v___x_1904_, 1);
v_fst_1906_ = lean_ctor_get(v_a_1905_, 0);
v_snd_1907_ = lean_ctor_get(v_a_1905_, 1);
v_isSharedCheck_1953_ = !lean_is_exclusive(v_a_1905_);
if (v_isSharedCheck_1953_ == 0)
{
v___x_1909_ = v_a_1905_;
v_isShared_1910_ = v_isSharedCheck_1953_;
goto v_resetjp_1908_;
}
else
{
lean_inc(v_snd_1907_);
lean_inc(v_fst_1906_);
lean_dec(v_a_1905_);
v___x_1909_ = lean_box(0);
v_isShared_1910_ = v_isSharedCheck_1953_;
goto v_resetjp_1908_;
}
v_resetjp_1908_:
{
lean_object* v___y_1912_; lean_object* v___y_1913_; lean_object* v___y_1914_; lean_object* v___y_1915_; uint8_t v___x_1931_; uint8_t v___x_1932_; 
v___x_1931_ = lean_unbox(v_snd_1907_);
lean_dec(v_snd_1907_);
v___x_1932_ = lean_bool_not(v___x_1931_);
if (v___x_1932_ == 0)
{
lean_del_object(v___x_1909_);
lean_dec(v_tacticName_1858_);
lean_dec(v_a_1857_);
v___y_1912_ = v___y_1866_;
v___y_1913_ = v___y_1867_;
v___y_1914_ = v___y_1868_;
v___y_1915_ = v___y_1869_;
goto v___jp_1911_;
}
else
{
uint8_t v___x_1933_; uint8_t v___x_1934_; 
v___x_1933_ = l_Lean_Level_isZero(v_a_1857_);
lean_dec(v_a_1857_);
v___x_1934_ = lean_bool_not(v___x_1933_);
if (v___x_1934_ == 0)
{
lean_del_object(v___x_1909_);
lean_dec(v_tacticName_1858_);
v___y_1912_ = v___y_1866_;
v___y_1913_ = v___y_1867_;
v___y_1914_ = v___y_1868_;
v___y_1915_ = v___y_1869_;
goto v___jp_1911_;
}
else
{
lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1939_; 
lean_dec(v_fst_1906_);
lean_dec(v_paramsPos_1881_);
lean_dec_ref(v_x_1864_);
lean_dec_ref(v_major_1862_);
lean_dec_ref(v_a_1861_);
v___x_1935_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__6));
v___x_1936_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__8, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__8_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__8);
v___x_1937_ = l_Lean_MessageData_ofName(v_recursorName_1878_);
if (v_isShared_1910_ == 0)
{
lean_ctor_set_tag(v___x_1909_, 7);
lean_ctor_set(v___x_1909_, 1, v___x_1937_);
lean_ctor_set(v___x_1909_, 0, v___x_1936_);
v___x_1939_ = v___x_1909_;
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
v___x_1942_ = l_Lean_Meta_mkTacticExMsg(v_tacticName_1858_, v_mvarId_1859_, v___x_1941_);
v___x_1943_ = l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1___redArg(v___x_1935_, v___x_1942_, v___y_1866_, v___y_1867_, v___y_1868_, v___y_1869_);
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
}
v___jp_1911_:
{
lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; 
v___x_1916_ = lean_array_to_list(v_fst_1906_);
v___x_1917_ = l_Lean_mkConst(v_recursorName_1878_, v___x_1916_);
v___x_1918_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams(v_mvarId_1859_, v_x_1864_, v_paramsPos_1881_, v___x_1917_, v___y_1912_, v___y_1913_, v___y_1914_, v___y_1915_);
lean_dec_ref(v_x_1864_);
if (lean_obj_tag(v___x_1918_) == 0)
{
if (v_depElim_1880_ == 0)
{
lean_object* v_a_1919_; 
lean_dec_ref(v_major_1862_);
v_a_1919_ = lean_ctor_get(v___x_1918_, 0);
lean_inc(v_a_1919_);
lean_dec_ref_known(v___x_1918_, 1);
v___y_1885_ = v_a_1919_;
v_motive_1886_ = v_a_1861_;
v___y_1887_ = v___y_1912_;
v___y_1888_ = v___y_1913_;
v___y_1889_ = v___y_1914_;
v___y_1890_ = v___y_1915_;
goto v___jp_1884_;
}
else
{
lean_object* v_a_1920_; lean_object* v___x_1921_; 
v_a_1920_ = lean_ctor_get(v___x_1918_, 0);
lean_inc(v_a_1920_);
lean_dec_ref_known(v___x_1918_, 1);
lean_inc(v___y_1915_);
lean_inc_ref(v___y_1914_);
lean_inc(v___y_1913_);
lean_inc_ref(v___y_1912_);
lean_inc_ref(v_major_1862_);
v___x_1921_ = lean_infer_type(v_major_1862_, v___y_1912_, v___y_1913_, v___y_1914_, v___y_1915_);
if (lean_obj_tag(v___x_1921_) == 0)
{
lean_object* v_a_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; 
v_a_1922_ = lean_ctor_get(v___x_1921_, 0);
lean_inc(v_a_1922_);
lean_dec_ref_known(v___x_1921_, 1);
v___x_1923_ = lean_unsigned_to_nat(1u);
v___x_1924_ = lean_mk_empty_array_with_capacity(v___x_1923_);
v___x_1925_ = lean_array_push(v___x_1924_, v_major_1862_);
v___x_1926_ = l_Lean_Expr_abstractM(v_a_1861_, v___x_1925_, v___y_1912_, v___y_1913_, v___y_1914_, v___y_1915_);
lean_dec_ref(v___x_1925_);
if (lean_obj_tag(v___x_1926_) == 0)
{
lean_object* v_a_1927_; lean_object* v___x_1928_; uint8_t v___x_1929_; lean_object* v___x_1930_; 
v_a_1927_ = lean_ctor_get(v___x_1926_, 0);
lean_inc(v_a_1927_);
lean_dec_ref_known(v___x_1926_, 1);
v___x_1928_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__3));
v___x_1929_ = 0;
v___x_1930_ = l_Lean_mkLambda(v___x_1928_, v___x_1929_, v_a_1922_, v_a_1927_);
v___y_1885_ = v_a_1920_;
v_motive_1886_ = v___x_1930_;
v___y_1887_ = v___y_1912_;
v___y_1888_ = v___y_1913_;
v___y_1889_ = v___y_1914_;
v___y_1890_ = v___y_1915_;
goto v___jp_1884_;
}
else
{
lean_dec(v_a_1922_);
lean_dec(v_a_1920_);
return v___x_1926_;
}
}
else
{
lean_dec(v_a_1920_);
lean_dec_ref(v_major_1862_);
lean_dec_ref(v_a_1861_);
return v___x_1921_;
}
}
}
else
{
lean_dec_ref(v_major_1862_);
lean_dec_ref(v_a_1861_);
return v___x_1918_;
}
}
}
}
else
{
lean_object* v_a_1954_; lean_object* v___x_1956_; uint8_t v_isShared_1957_; uint8_t v_isSharedCheck_1961_; 
lean_dec(v_paramsPos_1881_);
lean_dec(v_recursorName_1878_);
lean_dec_ref(v_x_1864_);
lean_dec_ref(v_major_1862_);
lean_dec_ref(v_a_1861_);
lean_dec(v_mvarId_1859_);
lean_dec(v_tacticName_1858_);
lean_dec(v_a_1857_);
v_a_1954_ = lean_ctor_get(v___x_1904_, 0);
v_isSharedCheck_1961_ = !lean_is_exclusive(v___x_1904_);
if (v_isSharedCheck_1961_ == 0)
{
v___x_1956_ = v___x_1904_;
v_isShared_1957_ = v_isSharedCheck_1961_;
goto v_resetjp_1955_;
}
else
{
lean_inc(v_a_1954_);
lean_dec(v___x_1904_);
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
v___jp_1884_:
{
uint8_t v___x_1891_; uint8_t v___x_1892_; lean_object* v___x_1893_; 
v___x_1891_ = 1;
v___x_1892_ = 1;
v___x_1893_ = l_Lean_Meta_mkLambdaFVars(v_indices_1860_, v_motive_1886_, v___x_1883_, v___x_1891_, v___x_1883_, v___x_1891_, v___x_1892_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_);
if (lean_obj_tag(v___x_1893_) == 0)
{
lean_object* v_a_1894_; lean_object* v___x_1896_; uint8_t v_isShared_1897_; uint8_t v_isSharedCheck_1902_; 
v_a_1894_ = lean_ctor_get(v___x_1893_, 0);
v_isSharedCheck_1902_ = !lean_is_exclusive(v___x_1893_);
if (v_isSharedCheck_1902_ == 0)
{
v___x_1896_ = v___x_1893_;
v_isShared_1897_ = v_isSharedCheck_1902_;
goto v_resetjp_1895_;
}
else
{
lean_inc(v_a_1894_);
lean_dec(v___x_1893_);
v___x_1896_ = lean_box(0);
v_isShared_1897_ = v_isSharedCheck_1902_;
goto v_resetjp_1895_;
}
v_resetjp_1895_:
{
lean_object* v___x_1898_; lean_object* v___x_1900_; 
v___x_1898_ = l_Lean_Expr_app___override(v___y_1885_, v_a_1894_);
if (v_isShared_1897_ == 0)
{
lean_ctor_set(v___x_1896_, 0, v___x_1898_);
v___x_1900_ = v___x_1896_;
goto v_reusejp_1899_;
}
else
{
lean_object* v_reuseFailAlloc_1901_; 
v_reuseFailAlloc_1901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1901_, 0, v___x_1898_);
v___x_1900_ = v_reuseFailAlloc_1901_;
goto v_reusejp_1899_;
}
v_reusejp_1899_:
{
return v___x_1900_;
}
}
}
else
{
lean_dec_ref(v___y_1885_);
return v___x_1893_;
}
}
}
else
{
lean_object* v___x_1962_; lean_object* v___x_1963_; 
lean_dec_ref(v_x_1864_);
lean_dec_ref(v_x_1863_);
lean_dec_ref(v_major_1862_);
lean_dec_ref(v_a_1861_);
lean_dec(v_a_1857_);
lean_dec_ref(v_recursorInfo_1856_);
v___x_1962_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__14, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__14_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__14);
v___x_1963_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1858_, v_mvarId_1859_, v___x_1962_, v___y_1866_, v___y_1867_, v___y_1868_, v___y_1869_);
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
lean_object* v_a_2029_; lean_object* v_fst_2030_; lean_object* v_snd_2031_; lean_object* v___x_2033_; uint8_t v_isShared_2034_; uint8_t v_isSharedCheck_2077_; 
v_a_2029_ = lean_ctor_get(v___x_2028_, 0);
lean_inc(v_a_2029_);
lean_dec_ref_known(v___x_2028_, 1);
v_fst_2030_ = lean_ctor_get(v_a_2029_, 0);
v_snd_2031_ = lean_ctor_get(v_a_2029_, 1);
v_isSharedCheck_2077_ = !lean_is_exclusive(v_a_2029_);
if (v_isSharedCheck_2077_ == 0)
{
v___x_2033_ = v_a_2029_;
v_isShared_2034_ = v_isSharedCheck_2077_;
goto v_resetjp_2032_;
}
else
{
lean_inc(v_snd_2031_);
lean_inc(v_fst_2030_);
lean_dec(v_a_2029_);
v___x_2033_ = lean_box(0);
v_isShared_2034_ = v_isSharedCheck_2077_;
goto v_resetjp_2032_;
}
v_resetjp_2032_:
{
lean_object* v___y_2036_; lean_object* v___y_2037_; lean_object* v___y_2038_; lean_object* v___y_2039_; uint8_t v___x_2055_; uint8_t v___x_2056_; 
v___x_2055_ = lean_unbox(v_snd_2031_);
lean_dec(v_snd_2031_);
v___x_2056_ = lean_bool_not(v___x_2055_);
if (v___x_2056_ == 0)
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
else
{
uint8_t v___x_2057_; uint8_t v___x_2058_; 
v___x_2057_ = l_Lean_Level_isZero(v_a_1980_);
lean_dec(v_a_1980_);
v___x_2058_ = lean_bool_not(v___x_2057_);
if (v___x_2058_ == 0)
{
lean_del_object(v___x_2033_);
lean_dec(v_tacticName_1981_);
v___y_2036_ = v___y_1990_;
v___y_2037_ = v___y_1991_;
v___y_2038_ = v___y_1992_;
v___y_2039_ = v___y_1993_;
goto v___jp_2035_;
}
else
{
lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2063_; 
lean_dec(v_fst_2030_);
lean_dec(v_paramsPos_2005_);
lean_dec_ref(v_x_1988_);
lean_dec_ref(v_major_1986_);
lean_dec_ref(v_a_1985_);
v___x_2059_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__6));
v___x_2060_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__8, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__8_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__8);
v___x_2061_ = l_Lean_MessageData_ofName(v_recursorName_2002_);
if (v_isShared_2034_ == 0)
{
lean_ctor_set_tag(v___x_2033_, 7);
lean_ctor_set(v___x_2033_, 1, v___x_2061_);
lean_ctor_set(v___x_2033_, 0, v___x_2060_);
v___x_2063_ = v___x_2033_;
goto v_reusejp_2062_;
}
else
{
lean_object* v_reuseFailAlloc_2076_; 
v_reuseFailAlloc_2076_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2076_, 0, v___x_2060_);
lean_ctor_set(v_reuseFailAlloc_2076_, 1, v___x_2061_);
v___x_2063_ = v_reuseFailAlloc_2076_;
goto v_reusejp_2062_;
}
v_reusejp_2062_:
{
lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v_a_2068_; lean_object* v___x_2070_; uint8_t v_isShared_2071_; uint8_t v_isSharedCheck_2075_; 
v___x_2064_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__10, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__10_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__10);
v___x_2065_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2065_, 0, v___x_2063_);
lean_ctor_set(v___x_2065_, 1, v___x_2064_);
v___x_2066_ = l_Lean_Meta_mkTacticExMsg(v_tacticName_1981_, v_mvarId_1982_, v___x_2065_);
v___x_2067_ = l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1___redArg(v___x_2059_, v___x_2066_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_);
v_a_2068_ = lean_ctor_get(v___x_2067_, 0);
v_isSharedCheck_2075_ = !lean_is_exclusive(v___x_2067_);
if (v_isSharedCheck_2075_ == 0)
{
v___x_2070_ = v___x_2067_;
v_isShared_2071_ = v_isSharedCheck_2075_;
goto v_resetjp_2069_;
}
else
{
lean_inc(v_a_2068_);
lean_dec(v___x_2067_);
v___x_2070_ = lean_box(0);
v_isShared_2071_ = v_isSharedCheck_2075_;
goto v_resetjp_2069_;
}
v_resetjp_2069_:
{
lean_object* v___x_2073_; 
if (v_isShared_2071_ == 0)
{
v___x_2073_ = v___x_2070_;
goto v_reusejp_2072_;
}
else
{
lean_object* v_reuseFailAlloc_2074_; 
v_reuseFailAlloc_2074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2074_, 0, v_a_2068_);
v___x_2073_ = v_reuseFailAlloc_2074_;
goto v_reusejp_2072_;
}
v_reusejp_2072_:
{
return v___x_2073_;
}
}
}
}
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
lean_object* v_a_2078_; lean_object* v___x_2080_; uint8_t v_isShared_2081_; uint8_t v_isSharedCheck_2085_; 
lean_dec(v_paramsPos_2005_);
lean_dec(v_recursorName_2002_);
lean_dec_ref(v_x_1988_);
lean_dec_ref(v_major_1986_);
lean_dec_ref(v_a_1985_);
lean_dec(v_mvarId_1982_);
lean_dec(v_tacticName_1981_);
lean_dec(v_a_1980_);
v_a_2078_ = lean_ctor_get(v___x_2028_, 0);
v_isSharedCheck_2085_ = !lean_is_exclusive(v___x_2028_);
if (v_isSharedCheck_2085_ == 0)
{
v___x_2080_ = v___x_2028_;
v_isShared_2081_ = v_isSharedCheck_2085_;
goto v_resetjp_2079_;
}
else
{
lean_inc(v_a_2078_);
lean_dec(v___x_2028_);
v___x_2080_ = lean_box(0);
v_isShared_2081_ = v_isSharedCheck_2085_;
goto v_resetjp_2079_;
}
v_resetjp_2079_:
{
lean_object* v___x_2083_; 
if (v_isShared_2081_ == 0)
{
v___x_2083_ = v___x_2080_;
goto v_reusejp_2082_;
}
else
{
lean_object* v_reuseFailAlloc_2084_; 
v_reuseFailAlloc_2084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2084_, 0, v_a_2078_);
v___x_2083_ = v_reuseFailAlloc_2084_;
goto v_reusejp_2082_;
}
v_reusejp_2082_:
{
return v___x_2083_;
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
lean_object* v___x_2086_; lean_object* v___x_2087_; 
lean_dec_ref(v_x_1988_);
lean_dec_ref(v_x_1987_);
lean_dec_ref(v_major_1986_);
lean_dec_ref(v_a_1985_);
lean_dec_ref(v_recursorInfo_1983_);
lean_dec(v_a_1980_);
v___x_2086_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__14, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__14_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__14);
v___x_2087_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1981_, v_mvarId_1982_, v___x_2086_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_);
return v___x_2087_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2___boxed(lean_object* v_a_2088_, lean_object* v_tacticName_2089_, lean_object* v_mvarId_2090_, lean_object* v_recursorInfo_2091_, lean_object* v_indices_2092_, lean_object* v_a_2093_, lean_object* v_major_2094_, lean_object* v_x_2095_, lean_object* v_x_2096_, lean_object* v_x_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_){
_start:
{
lean_object* v_res_2103_; 
v_res_2103_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2(v_a_2088_, v_tacticName_2089_, v_mvarId_2090_, v_recursorInfo_2091_, v_indices_2092_, v_a_2093_, v_major_2094_, v_x_2095_, v_x_2096_, v_x_2097_, v___y_2098_, v___y_2099_, v___y_2100_, v___y_2101_);
lean_dec(v___y_2101_);
lean_dec_ref(v___y_2100_);
lean_dec(v___y_2099_);
lean_dec_ref(v___y_2098_);
lean_dec(v_x_2097_);
lean_dec_ref(v_indices_2092_);
return v_res_2103_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkRecursorAppPrefix(lean_object* v_mvarId_2104_, lean_object* v_tacticName_2105_, lean_object* v_majorFVarId_2106_, lean_object* v_recursorInfo_2107_, lean_object* v_indices_2108_, lean_object* v_a_2109_, lean_object* v_a_2110_, lean_object* v_a_2111_, lean_object* v_a_2112_){
_start:
{
lean_object* v___x_2114_; 
lean_inc(v_mvarId_2104_);
v___x_2114_ = l_Lean_MVarId_getType(v_mvarId_2104_, v_a_2109_, v_a_2110_, v_a_2111_, v_a_2112_);
if (lean_obj_tag(v___x_2114_) == 0)
{
lean_object* v_a_2115_; lean_object* v___x_2116_; 
v_a_2115_ = lean_ctor_get(v___x_2114_, 0);
lean_inc_n(v_a_2115_, 2);
lean_dec_ref_known(v___x_2114_, 1);
v___x_2116_ = l_Lean_Meta_getLevel(v_a_2115_, v_a_2109_, v_a_2110_, v_a_2111_, v_a_2112_);
if (lean_obj_tag(v___x_2116_) == 0)
{
lean_object* v_a_2117_; lean_object* v___x_2118_; 
v_a_2117_ = lean_ctor_get(v___x_2116_, 0);
lean_inc(v_a_2117_);
lean_dec_ref_known(v___x_2116_, 1);
v___x_2118_ = l_Lean_Meta_normalizeLevel(v_a_2117_, v_a_2109_, v_a_2110_, v_a_2111_, v_a_2112_);
if (lean_obj_tag(v___x_2118_) == 0)
{
lean_object* v_a_2119_; lean_object* v_major_2120_; lean_object* v___x_2121_; 
v_a_2119_ = lean_ctor_get(v___x_2118_, 0);
lean_inc(v_a_2119_);
lean_dec_ref_known(v___x_2118_, 1);
lean_inc(v_majorFVarId_2106_);
v_major_2120_ = l_Lean_mkFVar(v_majorFVarId_2106_);
v___x_2121_ = l_Lean_FVarId_getDecl___redArg(v_majorFVarId_2106_, v_a_2109_, v_a_2111_, v_a_2112_);
if (lean_obj_tag(v___x_2121_) == 0)
{
lean_object* v_a_2122_; lean_object* v_typeName_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; 
v_a_2122_ = lean_ctor_get(v___x_2121_, 0);
lean_inc(v_a_2122_);
lean_dec_ref_known(v___x_2121_, 1);
v_typeName_2123_ = lean_ctor_get(v_recursorInfo_2107_, 1);
v___x_2124_ = l_Lean_LocalDecl_type(v_a_2122_);
lean_dec(v_a_2122_);
lean_inc_ref(v___x_2124_);
v___x_2125_ = l_Lean_Meta_whnfUntil(v___x_2124_, v_typeName_2123_, v_a_2109_, v_a_2110_, v_a_2111_, v_a_2112_);
if (lean_obj_tag(v___x_2125_) == 0)
{
lean_object* v_a_2126_; 
v_a_2126_ = lean_ctor_get(v___x_2125_, 0);
lean_inc(v_a_2126_);
lean_dec_ref_known(v___x_2125_, 1);
if (lean_obj_tag(v_a_2126_) == 1)
{
lean_object* v_val_2127_; lean_object* v_dummy_2128_; lean_object* v_nargs_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; 
lean_dec_ref(v___x_2124_);
v_val_2127_ = lean_ctor_get(v_a_2126_, 0);
lean_inc(v_val_2127_);
lean_dec_ref_known(v_a_2126_, 1);
v_dummy_2128_ = lean_obj_once(&l_Lean_Meta_getMajorTypeIndices___closed__0, &l_Lean_Meta_getMajorTypeIndices___closed__0_once, _init_l_Lean_Meta_getMajorTypeIndices___closed__0);
v_nargs_2129_ = l_Lean_Expr_getAppNumArgs(v_val_2127_);
lean_inc(v_nargs_2129_);
v___x_2130_ = lean_mk_array(v_nargs_2129_, v_dummy_2128_);
v___x_2131_ = lean_unsigned_to_nat(1u);
v___x_2132_ = lean_nat_sub(v_nargs_2129_, v___x_2131_);
lean_dec(v_nargs_2129_);
v___x_2133_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2(v_a_2119_, v_tacticName_2105_, v_mvarId_2104_, v_recursorInfo_2107_, v_indices_2108_, v_a_2115_, v_major_2120_, v_val_2127_, v___x_2130_, v___x_2132_, v_a_2109_, v_a_2110_, v_a_2111_, v_a_2112_);
lean_dec(v___x_2132_);
return v___x_2133_;
}
else
{
lean_object* v___x_2134_; 
lean_dec(v_a_2126_);
lean_dec_ref(v_major_2120_);
lean_dec(v_a_2119_);
lean_dec(v_a_2115_);
lean_dec_ref(v_recursorInfo_2107_);
v___x_2134_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg(v_tacticName_2105_, v_mvarId_2104_, v___x_2124_, v_a_2109_, v_a_2110_, v_a_2111_, v_a_2112_);
return v___x_2134_;
}
}
else
{
lean_object* v_a_2135_; lean_object* v___x_2137_; uint8_t v_isShared_2138_; uint8_t v_isSharedCheck_2142_; 
lean_dec_ref(v___x_2124_);
lean_dec_ref(v_major_2120_);
lean_dec(v_a_2119_);
lean_dec(v_a_2115_);
lean_dec_ref(v_recursorInfo_2107_);
lean_dec(v_tacticName_2105_);
lean_dec(v_mvarId_2104_);
v_a_2135_ = lean_ctor_get(v___x_2125_, 0);
v_isSharedCheck_2142_ = !lean_is_exclusive(v___x_2125_);
if (v_isSharedCheck_2142_ == 0)
{
v___x_2137_ = v___x_2125_;
v_isShared_2138_ = v_isSharedCheck_2142_;
goto v_resetjp_2136_;
}
else
{
lean_inc(v_a_2135_);
lean_dec(v___x_2125_);
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
lean_object* v_a_2143_; lean_object* v___x_2145_; uint8_t v_isShared_2146_; uint8_t v_isSharedCheck_2150_; 
lean_dec_ref(v_major_2120_);
lean_dec(v_a_2119_);
lean_dec(v_a_2115_);
lean_dec_ref(v_recursorInfo_2107_);
lean_dec(v_tacticName_2105_);
lean_dec(v_mvarId_2104_);
v_a_2143_ = lean_ctor_get(v___x_2121_, 0);
v_isSharedCheck_2150_ = !lean_is_exclusive(v___x_2121_);
if (v_isSharedCheck_2150_ == 0)
{
v___x_2145_ = v___x_2121_;
v_isShared_2146_ = v_isSharedCheck_2150_;
goto v_resetjp_2144_;
}
else
{
lean_inc(v_a_2143_);
lean_dec(v___x_2121_);
v___x_2145_ = lean_box(0);
v_isShared_2146_ = v_isSharedCheck_2150_;
goto v_resetjp_2144_;
}
v_resetjp_2144_:
{
lean_object* v___x_2148_; 
if (v_isShared_2146_ == 0)
{
v___x_2148_ = v___x_2145_;
goto v_reusejp_2147_;
}
else
{
lean_object* v_reuseFailAlloc_2149_; 
v_reuseFailAlloc_2149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2149_, 0, v_a_2143_);
v___x_2148_ = v_reuseFailAlloc_2149_;
goto v_reusejp_2147_;
}
v_reusejp_2147_:
{
return v___x_2148_;
}
}
}
}
else
{
lean_object* v_a_2151_; lean_object* v___x_2153_; uint8_t v_isShared_2154_; uint8_t v_isSharedCheck_2158_; 
lean_dec(v_a_2115_);
lean_dec_ref(v_recursorInfo_2107_);
lean_dec(v_majorFVarId_2106_);
lean_dec(v_tacticName_2105_);
lean_dec(v_mvarId_2104_);
v_a_2151_ = lean_ctor_get(v___x_2118_, 0);
v_isSharedCheck_2158_ = !lean_is_exclusive(v___x_2118_);
if (v_isSharedCheck_2158_ == 0)
{
v___x_2153_ = v___x_2118_;
v_isShared_2154_ = v_isSharedCheck_2158_;
goto v_resetjp_2152_;
}
else
{
lean_inc(v_a_2151_);
lean_dec(v___x_2118_);
v___x_2153_ = lean_box(0);
v_isShared_2154_ = v_isSharedCheck_2158_;
goto v_resetjp_2152_;
}
v_resetjp_2152_:
{
lean_object* v___x_2156_; 
if (v_isShared_2154_ == 0)
{
v___x_2156_ = v___x_2153_;
goto v_reusejp_2155_;
}
else
{
lean_object* v_reuseFailAlloc_2157_; 
v_reuseFailAlloc_2157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2157_, 0, v_a_2151_);
v___x_2156_ = v_reuseFailAlloc_2157_;
goto v_reusejp_2155_;
}
v_reusejp_2155_:
{
return v___x_2156_;
}
}
}
}
else
{
lean_object* v_a_2159_; lean_object* v___x_2161_; uint8_t v_isShared_2162_; uint8_t v_isSharedCheck_2166_; 
lean_dec(v_a_2115_);
lean_dec_ref(v_recursorInfo_2107_);
lean_dec(v_majorFVarId_2106_);
lean_dec(v_tacticName_2105_);
lean_dec(v_mvarId_2104_);
v_a_2159_ = lean_ctor_get(v___x_2116_, 0);
v_isSharedCheck_2166_ = !lean_is_exclusive(v___x_2116_);
if (v_isSharedCheck_2166_ == 0)
{
v___x_2161_ = v___x_2116_;
v_isShared_2162_ = v_isSharedCheck_2166_;
goto v_resetjp_2160_;
}
else
{
lean_inc(v_a_2159_);
lean_dec(v___x_2116_);
v___x_2161_ = lean_box(0);
v_isShared_2162_ = v_isSharedCheck_2166_;
goto v_resetjp_2160_;
}
v_resetjp_2160_:
{
lean_object* v___x_2164_; 
if (v_isShared_2162_ == 0)
{
v___x_2164_ = v___x_2161_;
goto v_reusejp_2163_;
}
else
{
lean_object* v_reuseFailAlloc_2165_; 
v_reuseFailAlloc_2165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2165_, 0, v_a_2159_);
v___x_2164_ = v_reuseFailAlloc_2165_;
goto v_reusejp_2163_;
}
v_reusejp_2163_:
{
return v___x_2164_;
}
}
}
}
else
{
lean_dec_ref(v_recursorInfo_2107_);
lean_dec(v_majorFVarId_2106_);
lean_dec(v_tacticName_2105_);
lean_dec(v_mvarId_2104_);
return v___x_2114_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkRecursorAppPrefix___boxed(lean_object* v_mvarId_2167_, lean_object* v_tacticName_2168_, lean_object* v_majorFVarId_2169_, lean_object* v_recursorInfo_2170_, lean_object* v_indices_2171_, lean_object* v_a_2172_, lean_object* v_a_2173_, lean_object* v_a_2174_, lean_object* v_a_2175_, lean_object* v_a_2176_){
_start:
{
lean_object* v_res_2177_; 
v_res_2177_ = l_Lean_Meta_mkRecursorAppPrefix(v_mvarId_2167_, v_tacticName_2168_, v_majorFVarId_2169_, v_recursorInfo_2170_, v_indices_2171_, v_a_2172_, v_a_2173_, v_a_2174_, v_a_2175_);
lean_dec(v_a_2175_);
lean_dec_ref(v_a_2174_);
lean_dec(v_a_2173_);
lean_dec_ref(v_a_2172_);
lean_dec_ref(v_indices_2171_);
return v_res_2177_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1(lean_object* v_00_u03b1_2178_, lean_object* v_name_2179_, lean_object* v_msg_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_){
_start:
{
lean_object* v___x_2186_; 
v___x_2186_ = l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1___redArg(v_name_2179_, v_msg_2180_, v___y_2181_, v___y_2182_, v___y_2183_, v___y_2184_);
return v___x_2186_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1___boxed(lean_object* v_00_u03b1_2187_, lean_object* v_name_2188_, lean_object* v_msg_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_){
_start:
{
lean_object* v_res_2195_; 
v_res_2195_ = l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1(v_00_u03b1_2187_, v_name_2188_, v_msg_2189_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_);
lean_dec(v___y_2193_);
lean_dec_ref(v___y_2192_);
lean_dec(v___y_2191_);
lean_dec_ref(v___y_2190_);
return v_res_2195_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___redArg(lean_object* v_mvarId_2196_, lean_object* v_x_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_){
_start:
{
lean_object* v___x_2203_; 
v___x_2203_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_2196_, v_x_2197_, v___y_2198_, v___y_2199_, v___y_2200_, v___y_2201_);
if (lean_obj_tag(v___x_2203_) == 0)
{
lean_object* v_a_2204_; lean_object* v___x_2206_; uint8_t v_isShared_2207_; uint8_t v_isSharedCheck_2211_; 
v_a_2204_ = lean_ctor_get(v___x_2203_, 0);
v_isSharedCheck_2211_ = !lean_is_exclusive(v___x_2203_);
if (v_isSharedCheck_2211_ == 0)
{
v___x_2206_ = v___x_2203_;
v_isShared_2207_ = v_isSharedCheck_2211_;
goto v_resetjp_2205_;
}
else
{
lean_inc(v_a_2204_);
lean_dec(v___x_2203_);
v___x_2206_ = lean_box(0);
v_isShared_2207_ = v_isSharedCheck_2211_;
goto v_resetjp_2205_;
}
v_resetjp_2205_:
{
lean_object* v___x_2209_; 
if (v_isShared_2207_ == 0)
{
v___x_2209_ = v___x_2206_;
goto v_reusejp_2208_;
}
else
{
lean_object* v_reuseFailAlloc_2210_; 
v_reuseFailAlloc_2210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2210_, 0, v_a_2204_);
v___x_2209_ = v_reuseFailAlloc_2210_;
goto v_reusejp_2208_;
}
v_reusejp_2208_:
{
return v___x_2209_;
}
}
}
else
{
lean_object* v_a_2212_; lean_object* v___x_2214_; uint8_t v_isShared_2215_; uint8_t v_isSharedCheck_2219_; 
v_a_2212_ = lean_ctor_get(v___x_2203_, 0);
v_isSharedCheck_2219_ = !lean_is_exclusive(v___x_2203_);
if (v_isSharedCheck_2219_ == 0)
{
v___x_2214_ = v___x_2203_;
v_isShared_2215_ = v_isSharedCheck_2219_;
goto v_resetjp_2213_;
}
else
{
lean_inc(v_a_2212_);
lean_dec(v___x_2203_);
v___x_2214_ = lean_box(0);
v_isShared_2215_ = v_isSharedCheck_2219_;
goto v_resetjp_2213_;
}
v_resetjp_2213_:
{
lean_object* v___x_2217_; 
if (v_isShared_2215_ == 0)
{
v___x_2217_ = v___x_2214_;
goto v_reusejp_2216_;
}
else
{
lean_object* v_reuseFailAlloc_2218_; 
v_reuseFailAlloc_2218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2218_, 0, v_a_2212_);
v___x_2217_ = v_reuseFailAlloc_2218_;
goto v_reusejp_2216_;
}
v_reusejp_2216_:
{
return v___x_2217_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___redArg___boxed(lean_object* v_mvarId_2220_, lean_object* v_x_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_){
_start:
{
lean_object* v_res_2227_; 
v_res_2227_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___redArg(v_mvarId_2220_, v_x_2221_, v___y_2222_, v___y_2223_, v___y_2224_, v___y_2225_);
lean_dec(v___y_2225_);
lean_dec_ref(v___y_2224_);
lean_dec(v___y_2223_);
lean_dec_ref(v___y_2222_);
return v_res_2227_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3(lean_object* v_00_u03b1_2228_, lean_object* v_mvarId_2229_, lean_object* v_x_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_){
_start:
{
lean_object* v___x_2236_; 
v___x_2236_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___redArg(v_mvarId_2229_, v_x_2230_, v___y_2231_, v___y_2232_, v___y_2233_, v___y_2234_);
return v___x_2236_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___boxed(lean_object* v_00_u03b1_2237_, lean_object* v_mvarId_2238_, lean_object* v_x_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_){
_start:
{
lean_object* v_res_2245_; 
v_res_2245_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3(v_00_u03b1_2237_, v_mvarId_2238_, v_x_2239_, v___y_2240_, v___y_2241_, v___y_2242_, v___y_2243_);
lean_dec(v___y_2243_);
lean_dec_ref(v___y_2242_);
lean_dec(v___y_2241_);
lean_dec_ref(v___y_2240_);
return v_res_2245_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_induction_spec__2(lean_object* v_fst_2246_, lean_object* v_as_2247_, size_t v_sz_2248_, size_t v_i_2249_, lean_object* v_b_2250_){
_start:
{
uint8_t v___x_2251_; 
v___x_2251_ = lean_usize_dec_lt(v_i_2249_, v_sz_2248_);
if (v___x_2251_ == 0)
{
return v_b_2250_;
}
else
{
lean_object* v_fst_2252_; lean_object* v_snd_2253_; lean_object* v___x_2255_; uint8_t v_isShared_2256_; uint8_t v_isSharedCheck_2271_; 
v_fst_2252_ = lean_ctor_get(v_b_2250_, 0);
v_snd_2253_ = lean_ctor_get(v_b_2250_, 1);
v_isSharedCheck_2271_ = !lean_is_exclusive(v_b_2250_);
if (v_isSharedCheck_2271_ == 0)
{
v___x_2255_ = v_b_2250_;
v_isShared_2256_ = v_isSharedCheck_2271_;
goto v_resetjp_2254_;
}
else
{
lean_inc(v_snd_2253_);
lean_inc(v_fst_2252_);
lean_dec(v_b_2250_);
v___x_2255_ = lean_box(0);
v_isShared_2256_ = v_isSharedCheck_2271_;
goto v_resetjp_2254_;
}
v_resetjp_2254_:
{
lean_object* v___x_2257_; lean_object* v_a_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2266_; 
v___x_2257_ = lean_box(0);
v_a_2258_ = lean_array_uget_borrowed(v_as_2247_, v_i_2249_);
v___x_2259_ = l_Lean_Expr_fvarId_x21(v_a_2258_);
v___x_2260_ = lean_array_get_borrowed(v___x_2257_, v_fst_2246_, v_snd_2253_);
lean_inc(v___x_2260_);
v___x_2261_ = l_Lean_mkFVar(v___x_2260_);
v___x_2262_ = l_Lean_Meta_FVarSubst_insert(v_fst_2252_, v___x_2259_, v___x_2261_);
v___x_2263_ = lean_unsigned_to_nat(1u);
v___x_2264_ = lean_nat_add(v_snd_2253_, v___x_2263_);
lean_dec(v_snd_2253_);
if (v_isShared_2256_ == 0)
{
lean_ctor_set(v___x_2255_, 1, v___x_2264_);
lean_ctor_set(v___x_2255_, 0, v___x_2262_);
v___x_2266_ = v___x_2255_;
goto v_reusejp_2265_;
}
else
{
lean_object* v_reuseFailAlloc_2270_; 
v_reuseFailAlloc_2270_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2270_, 0, v___x_2262_);
lean_ctor_set(v_reuseFailAlloc_2270_, 1, v___x_2264_);
v___x_2266_ = v_reuseFailAlloc_2270_;
goto v_reusejp_2265_;
}
v_reusejp_2265_:
{
size_t v___x_2267_; size_t v___x_2268_; 
v___x_2267_ = ((size_t)1ULL);
v___x_2268_ = lean_usize_add(v_i_2249_, v___x_2267_);
v_i_2249_ = v___x_2268_;
v_b_2250_ = v___x_2266_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_induction_spec__2___boxed(lean_object* v_fst_2272_, lean_object* v_as_2273_, lean_object* v_sz_2274_, lean_object* v_i_2275_, lean_object* v_b_2276_){
_start:
{
size_t v_sz_boxed_2277_; size_t v_i_boxed_2278_; lean_object* v_res_2279_; 
v_sz_boxed_2277_ = lean_unbox_usize(v_sz_2274_);
lean_dec(v_sz_2274_);
v_i_boxed_2278_ = lean_unbox_usize(v_i_2275_);
lean_dec(v_i_2275_);
v_res_2279_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_induction_spec__2(v_fst_2272_, v_as_2273_, v_sz_boxed_2277_, v_i_boxed_2278_, v_b_2276_);
lean_dec_ref(v_as_2273_);
lean_dec_ref(v_fst_2272_);
return v_res_2279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4___lam__0(lean_object* v_snd_2280_, lean_object* v___x_2281_, lean_object* v_fst_2282_, lean_object* v_a_2283_, lean_object* v___x_2284_, lean_object* v_givenNames_2285_, lean_object* v_fst_2286_, lean_object* v___x_2287_, lean_object* v_fst_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_){
_start:
{
lean_object* v___x_2294_; 
lean_inc_ref(v_a_2283_);
lean_inc(v_snd_2280_);
v___x_2294_ = l_Lean_Meta_mkRecursorAppPrefix(v_snd_2280_, v___x_2281_, v_fst_2282_, v_a_2283_, v___x_2284_, v___y_2289_, v___y_2290_, v___y_2291_, v___y_2292_);
if (lean_obj_tag(v___x_2294_) == 0)
{
lean_object* v_a_2295_; lean_object* v___x_2296_; 
v_a_2295_ = lean_ctor_get(v___x_2294_, 0);
lean_inc(v_a_2295_);
lean_dec_ref_known(v___x_2294_, 1);
v___x_2296_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize(v_snd_2280_, v_givenNames_2285_, v_a_2283_, v_fst_2286_, v___x_2287_, v___x_2284_, v_fst_2288_, v_a_2295_, v___y_2289_, v___y_2290_, v___y_2291_, v___y_2292_);
lean_dec_ref(v_a_2283_);
return v___x_2296_;
}
else
{
lean_object* v_a_2297_; lean_object* v___x_2299_; uint8_t v_isShared_2300_; uint8_t v_isSharedCheck_2304_; 
lean_dec(v_fst_2288_);
lean_dec_ref(v___x_2287_);
lean_dec_ref(v_a_2283_);
lean_dec(v_snd_2280_);
v_a_2297_ = lean_ctor_get(v___x_2294_, 0);
v_isSharedCheck_2304_ = !lean_is_exclusive(v___x_2294_);
if (v_isSharedCheck_2304_ == 0)
{
v___x_2299_ = v___x_2294_;
v_isShared_2300_ = v_isSharedCheck_2304_;
goto v_resetjp_2298_;
}
else
{
lean_inc(v_a_2297_);
lean_dec(v___x_2294_);
v___x_2299_ = lean_box(0);
v_isShared_2300_ = v_isSharedCheck_2304_;
goto v_resetjp_2298_;
}
v_resetjp_2298_:
{
lean_object* v___x_2302_; 
if (v_isShared_2300_ == 0)
{
v___x_2302_ = v___x_2299_;
goto v_reusejp_2301_;
}
else
{
lean_object* v_reuseFailAlloc_2303_; 
v_reuseFailAlloc_2303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2303_, 0, v_a_2297_);
v___x_2302_ = v_reuseFailAlloc_2303_;
goto v_reusejp_2301_;
}
v_reusejp_2301_:
{
return v___x_2302_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4___lam__0___boxed(lean_object* v_snd_2305_, lean_object* v___x_2306_, lean_object* v_fst_2307_, lean_object* v_a_2308_, lean_object* v___x_2309_, lean_object* v_givenNames_2310_, lean_object* v_fst_2311_, lean_object* v___x_2312_, lean_object* v_fst_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_){
_start:
{
lean_object* v_res_2319_; 
v_res_2319_ = l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4___lam__0(v_snd_2305_, v___x_2306_, v_fst_2307_, v_a_2308_, v___x_2309_, v_givenNames_2310_, v_fst_2311_, v___x_2312_, v_fst_2313_, v___y_2314_, v___y_2315_, v___y_2316_, v___y_2317_);
lean_dec(v___y_2317_);
lean_dec_ref(v___y_2316_);
lean_dec(v___y_2315_);
lean_dec_ref(v___y_2314_);
lean_dec_ref(v_fst_2311_);
lean_dec_ref(v_givenNames_2310_);
lean_dec_ref(v___x_2309_);
return v_res_2319_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_induction_spec__1(size_t v_sz_2320_, size_t v_i_2321_, lean_object* v_bs_2322_){
_start:
{
uint8_t v___x_2323_; 
v___x_2323_ = lean_usize_dec_lt(v_i_2321_, v_sz_2320_);
if (v___x_2323_ == 0)
{
return v_bs_2322_;
}
else
{
lean_object* v_v_2324_; lean_object* v___x_2325_; lean_object* v_bs_x27_2326_; lean_object* v___x_2327_; size_t v___x_2328_; size_t v___x_2329_; lean_object* v___x_2330_; 
v_v_2324_ = lean_array_uget(v_bs_2322_, v_i_2321_);
v___x_2325_ = lean_unsigned_to_nat(0u);
v_bs_x27_2326_ = lean_array_uset(v_bs_2322_, v_i_2321_, v___x_2325_);
v___x_2327_ = l_Lean_Expr_fvarId_x21(v_v_2324_);
lean_dec(v_v_2324_);
v___x_2328_ = ((size_t)1ULL);
v___x_2329_ = lean_usize_add(v_i_2321_, v___x_2328_);
v___x_2330_ = lean_array_uset(v_bs_x27_2326_, v_i_2321_, v___x_2327_);
v_i_2321_ = v___x_2329_;
v_bs_2322_ = v___x_2330_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_induction_spec__1___boxed(lean_object* v_sz_2332_, lean_object* v_i_2333_, lean_object* v_bs_2334_){
_start:
{
size_t v_sz_boxed_2335_; size_t v_i_boxed_2336_; lean_object* v_res_2337_; 
v_sz_boxed_2335_ = lean_unbox_usize(v_sz_2332_);
lean_dec(v_sz_2332_);
v_i_boxed_2336_ = lean_unbox_usize(v_i_2333_);
lean_dec(v_i_2333_);
v_res_2337_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_induction_spec__1(v_sz_boxed_2335_, v_i_boxed_2336_, v_bs_2334_);
return v_res_2337_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_MVarId_induction_spec__0(lean_object* v_majorTypeArgs_2338_, lean_object* v_val_2339_, lean_object* v_mvarId_2340_, lean_object* v_as_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_){
_start:
{
if (lean_obj_tag(v_as_2341_) == 0)
{
lean_object* v___x_2347_; lean_object* v___x_2348_; 
lean_dec(v_mvarId_2340_);
lean_dec_ref(v_val_2339_);
v___x_2347_ = lean_box(0);
v___x_2348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2348_, 0, v___x_2347_);
return v___x_2348_;
}
else
{
lean_object* v_head_2349_; 
v_head_2349_ = lean_ctor_get(v_as_2341_, 0);
lean_inc(v_head_2349_);
if (lean_obj_tag(v_head_2349_) == 0)
{
lean_object* v_tail_2350_; 
v_tail_2350_ = lean_ctor_get(v_as_2341_, 1);
lean_inc(v_tail_2350_);
lean_dec_ref_known(v_as_2341_, 2);
v_as_2341_ = v_tail_2350_;
goto _start;
}
else
{
lean_object* v_tail_2352_; lean_object* v___x_2354_; uint8_t v_isShared_2355_; uint8_t v_isSharedCheck_2375_; 
v_tail_2352_ = lean_ctor_get(v_as_2341_, 1);
v_isSharedCheck_2375_ = !lean_is_exclusive(v_as_2341_);
if (v_isSharedCheck_2375_ == 0)
{
lean_object* v_unused_2376_; 
v_unused_2376_ = lean_ctor_get(v_as_2341_, 0);
lean_dec(v_unused_2376_);
v___x_2354_ = v_as_2341_;
v_isShared_2355_ = v_isSharedCheck_2375_;
goto v_resetjp_2353_;
}
else
{
lean_inc(v_tail_2352_);
lean_dec(v_as_2341_);
v___x_2354_ = lean_box(0);
v_isShared_2355_ = v_isSharedCheck_2375_;
goto v_resetjp_2353_;
}
v_resetjp_2353_:
{
lean_object* v_val_2356_; lean_object* v___x_2358_; uint8_t v_isShared_2359_; uint8_t v_isSharedCheck_2374_; 
v_val_2356_ = lean_ctor_get(v_head_2349_, 0);
v_isSharedCheck_2374_ = !lean_is_exclusive(v_head_2349_);
if (v_isSharedCheck_2374_ == 0)
{
v___x_2358_ = v_head_2349_;
v_isShared_2359_ = v_isSharedCheck_2374_;
goto v_resetjp_2357_;
}
else
{
lean_inc(v_val_2356_);
lean_dec(v_head_2349_);
v___x_2358_ = lean_box(0);
v_isShared_2359_ = v_isSharedCheck_2374_;
goto v_resetjp_2357_;
}
v_resetjp_2357_:
{
lean_object* v___x_2360_; uint8_t v___x_2361_; 
v___x_2360_ = lean_array_get_size(v_majorTypeArgs_2338_);
v___x_2361_ = lean_nat_dec_le(v___x_2360_, v_val_2356_);
lean_dec(v_val_2356_);
if (v___x_2361_ == 0)
{
lean_del_object(v___x_2358_);
lean_del_object(v___x_2354_);
v_as_2341_ = v_tail_2352_;
goto _start;
}
else
{
lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2367_; 
v___x_2363_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1));
v___x_2364_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__5, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__5);
lean_inc_ref(v_val_2339_);
v___x_2365_ = l_Lean_indentExpr(v_val_2339_);
if (v_isShared_2355_ == 0)
{
lean_ctor_set_tag(v___x_2354_, 7);
lean_ctor_set(v___x_2354_, 1, v___x_2365_);
lean_ctor_set(v___x_2354_, 0, v___x_2364_);
v___x_2367_ = v___x_2354_;
goto v_reusejp_2366_;
}
else
{
lean_object* v_reuseFailAlloc_2373_; 
v_reuseFailAlloc_2373_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2373_, 0, v___x_2364_);
lean_ctor_set(v_reuseFailAlloc_2373_, 1, v___x_2365_);
v___x_2367_ = v_reuseFailAlloc_2373_;
goto v_reusejp_2366_;
}
v_reusejp_2366_:
{
lean_object* v___x_2369_; 
if (v_isShared_2359_ == 0)
{
lean_ctor_set(v___x_2358_, 0, v___x_2367_);
v___x_2369_ = v___x_2358_;
goto v_reusejp_2368_;
}
else
{
lean_object* v_reuseFailAlloc_2372_; 
v_reuseFailAlloc_2372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2372_, 0, v___x_2367_);
v___x_2369_ = v_reuseFailAlloc_2372_;
goto v_reusejp_2368_;
}
v_reusejp_2368_:
{
lean_object* v___x_2370_; 
lean_inc(v_mvarId_2340_);
v___x_2370_ = l_Lean_Meta_throwTacticEx___redArg(v___x_2363_, v_mvarId_2340_, v___x_2369_, v___y_2342_, v___y_2343_, v___y_2344_, v___y_2345_);
if (lean_obj_tag(v___x_2370_) == 0)
{
lean_dec_ref_known(v___x_2370_, 1);
v_as_2341_ = v_tail_2352_;
goto _start;
}
else
{
lean_dec(v_tail_2352_);
lean_dec(v_mvarId_2340_);
lean_dec_ref(v_val_2339_);
return v___x_2370_;
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
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_MVarId_induction_spec__0___boxed(lean_object* v_majorTypeArgs_2377_, lean_object* v_val_2378_, lean_object* v_mvarId_2379_, lean_object* v_as_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_){
_start:
{
lean_object* v_res_2386_; 
v_res_2386_ = l_List_forM___at___00Lean_MVarId_induction_spec__0(v_majorTypeArgs_2377_, v_val_2378_, v_mvarId_2379_, v_as_2380_, v___y_2381_, v___y_2382_, v___y_2383_, v___y_2384_);
lean_dec(v___y_2384_);
lean_dec_ref(v___y_2383_);
lean_dec(v___y_2382_);
lean_dec_ref(v___y_2381_);
lean_dec_ref(v_majorTypeArgs_2377_);
return v_res_2386_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__1(void){
_start:
{
lean_object* v___x_2388_; lean_object* v___x_2389_; 
v___x_2388_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__0));
v___x_2389_ = l_Lean_stringToMessageData(v___x_2388_);
return v___x_2389_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__3(void){
_start:
{
lean_object* v___x_2391_; lean_object* v___x_2392_; 
v___x_2391_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__2));
v___x_2392_ = l_Lean_stringToMessageData(v___x_2391_);
return v___x_2392_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__5(void){
_start:
{
lean_object* v___x_2394_; lean_object* v___x_2395_; 
v___x_2394_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__4));
v___x_2395_ = l_Lean_stringToMessageData(v___x_2394_);
return v___x_2395_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4(lean_object* v_a_2396_, lean_object* v_val_2397_, lean_object* v_mvarId_2398_, lean_object* v_majorFVarId_2399_, lean_object* v_givenNames_2400_, lean_object* v_recursorName_2401_, lean_object* v_x_2402_, lean_object* v_x_2403_, lean_object* v_x_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_){
_start:
{
if (lean_obj_tag(v_x_2402_) == 5)
{
lean_object* v_fn_2410_; lean_object* v_arg_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; 
v_fn_2410_ = lean_ctor_get(v_x_2402_, 0);
lean_inc_ref(v_fn_2410_);
v_arg_2411_ = lean_ctor_get(v_x_2402_, 1);
lean_inc_ref(v_arg_2411_);
lean_dec_ref_known(v_x_2402_, 2);
v___x_2412_ = lean_array_set(v_x_2403_, v_x_2404_, v_arg_2411_);
v___x_2413_ = lean_unsigned_to_nat(1u);
v___x_2414_ = lean_nat_sub(v_x_2404_, v___x_2413_);
lean_dec(v_x_2404_);
v_x_2402_ = v_fn_2410_;
v_x_2403_ = v___x_2412_;
v_x_2404_ = v___x_2414_;
goto _start;
}
else
{
uint8_t v_depElim_2416_; lean_object* v_paramsPos_2417_; lean_object* v___x_2418_; 
lean_dec(v_x_2404_);
lean_dec_ref(v_x_2402_);
v_depElim_2416_ = lean_ctor_get_uint8(v_a_2396_, sizeof(void*)*8);
v_paramsPos_2417_ = lean_ctor_get(v_a_2396_, 5);
lean_inc(v_paramsPos_2417_);
lean_inc(v_mvarId_2398_);
lean_inc_ref(v_val_2397_);
v___x_2418_ = l_List_forM___at___00Lean_MVarId_induction_spec__0(v_x_2403_, v_val_2397_, v_mvarId_2398_, v_paramsPos_2417_, v___y_2405_, v___y_2406_, v___y_2407_, v___y_2408_);
lean_dec_ref(v_x_2403_);
if (lean_obj_tag(v___x_2418_) == 0)
{
lean_object* v___x_2419_; lean_object* v___y_2421_; lean_object* v___y_2422_; lean_object* v___y_2423_; lean_object* v___y_2424_; lean_object* v___y_2425_; lean_object* v___y_2426_; lean_object* v___y_2427_; size_t v___y_2428_; lean_object* v___y_2429_; lean_object* v___y_2430_; lean_object* v___y_2431_; lean_object* v___y_2432_; lean_object* v___x_2437_; 
lean_dec_ref_known(v___x_2418_, 1);
v___x_2419_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1));
lean_inc_ref(v_a_2396_);
lean_inc(v_mvarId_2398_);
v___x_2437_ = l_Lean_Meta_getMajorTypeIndices(v_mvarId_2398_, v___x_2419_, v_a_2396_, v_val_2397_, v___y_2405_, v___y_2406_, v___y_2407_, v___y_2408_);
if (lean_obj_tag(v___x_2437_) == 0)
{
lean_object* v_a_2438_; lean_object* v___x_2439_; 
v_a_2438_ = lean_ctor_get(v___x_2437_, 0);
lean_inc(v_a_2438_);
lean_dec_ref_known(v___x_2437_, 1);
lean_inc(v_mvarId_2398_);
v___x_2439_ = l_Lean_MVarId_getType(v_mvarId_2398_, v___y_2405_, v___y_2406_, v___y_2407_, v___y_2408_);
if (lean_obj_tag(v___x_2439_) == 0)
{
lean_object* v_a_2440_; lean_object* v_cls_2441_; lean_object* v___y_2443_; lean_object* v___y_2444_; lean_object* v___y_2445_; lean_object* v___y_2446_; uint8_t v_a_2530_; uint8_t v___x_2546_; 
v_a_2440_ = lean_ctor_get(v___x_2439_, 0);
lean_inc(v_a_2440_);
lean_dec_ref_known(v___x_2439_, 1);
v_cls_2441_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__2));
v___x_2546_ = lean_bool_not(v_depElim_2416_);
if (v___x_2546_ == 0)
{
lean_dec(v_a_2440_);
v_a_2530_ = v___x_2546_;
goto v___jp_2529_;
}
else
{
lean_object* v___x_2547_; lean_object* v_a_2548_; uint8_t v___x_2549_; 
lean_inc(v_majorFVarId_2399_);
v___x_2547_ = l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2___redArg(v_a_2440_, v_majorFVarId_2399_, v___y_2406_);
v_a_2548_ = lean_ctor_get(v___x_2547_, 0);
lean_inc(v_a_2548_);
lean_dec_ref(v___x_2547_);
v___x_2549_ = lean_unbox(v_a_2548_);
lean_dec(v_a_2548_);
v_a_2530_ = v___x_2549_;
goto v___jp_2529_;
}
v___jp_2442_:
{
size_t v_sz_2447_; size_t v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; uint8_t v___x_2451_; uint8_t v___x_2452_; lean_object* v___x_2453_; 
v_sz_2447_ = lean_array_size(v_a_2438_);
v___x_2448_ = ((size_t)0ULL);
lean_inc(v_a_2438_);
v___x_2449_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_induction_spec__1(v_sz_2447_, v___x_2448_, v_a_2438_);
lean_inc(v_majorFVarId_2399_);
v___x_2450_ = lean_array_push(v___x_2449_, v_majorFVarId_2399_);
v___x_2451_ = 1;
v___x_2452_ = 0;
v___x_2453_ = l_Lean_MVarId_revert(v_mvarId_2398_, v___x_2450_, v___x_2451_, v___x_2452_, v___y_2443_, v___y_2444_, v___y_2445_, v___y_2446_);
if (lean_obj_tag(v___x_2453_) == 0)
{
lean_object* v_a_2454_; lean_object* v_fst_2455_; lean_object* v_snd_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; 
v_a_2454_ = lean_ctor_get(v___x_2453_, 0);
lean_inc(v_a_2454_);
lean_dec_ref_known(v___x_2453_, 1);
v_fst_2455_ = lean_ctor_get(v_a_2454_, 0);
lean_inc(v_fst_2455_);
v_snd_2456_ = lean_ctor_get(v_a_2454_, 1);
lean_inc(v_snd_2456_);
lean_dec(v_a_2454_);
v___x_2457_ = lean_array_get_size(v_a_2438_);
v___x_2458_ = lean_box(0);
v___x_2459_ = l_Lean_Meta_introNCore(v_snd_2456_, v___x_2457_, v___x_2458_, v___x_2452_, v___x_2451_, v___y_2443_, v___y_2444_, v___y_2445_, v___y_2446_);
if (lean_obj_tag(v___x_2459_) == 0)
{
lean_object* v_a_2460_; lean_object* v_fst_2461_; lean_object* v_snd_2462_; lean_object* v___x_2463_; 
v_a_2460_ = lean_ctor_get(v___x_2459_, 0);
lean_inc(v_a_2460_);
lean_dec_ref_known(v___x_2459_, 1);
v_fst_2461_ = lean_ctor_get(v_a_2460_, 0);
lean_inc(v_fst_2461_);
v_snd_2462_ = lean_ctor_get(v_a_2460_, 1);
lean_inc(v_snd_2462_);
lean_dec(v_a_2460_);
v___x_2463_ = l_Lean_Meta_intro1Core(v_snd_2462_, v___x_2451_, v___y_2443_, v___y_2444_, v___y_2445_, v___y_2446_);
if (lean_obj_tag(v___x_2463_) == 0)
{
lean_object* v_a_2464_; lean_object* v_fst_2465_; lean_object* v_snd_2466_; lean_object* v___x_2468_; uint8_t v_isShared_2469_; uint8_t v_isSharedCheck_2504_; 
v_a_2464_ = lean_ctor_get(v___x_2463_, 0);
lean_inc(v_a_2464_);
lean_dec_ref_known(v___x_2463_, 1);
v_fst_2465_ = lean_ctor_get(v_a_2464_, 0);
v_snd_2466_ = lean_ctor_get(v_a_2464_, 1);
v_isSharedCheck_2504_ = !lean_is_exclusive(v_a_2464_);
if (v_isSharedCheck_2504_ == 0)
{
v___x_2468_ = v_a_2464_;
v_isShared_2469_ = v_isSharedCheck_2504_;
goto v_resetjp_2467_;
}
else
{
lean_inc(v_snd_2466_);
lean_inc(v_fst_2465_);
lean_dec(v_a_2464_);
v___x_2468_ = lean_box(0);
v_isShared_2469_ = v_isSharedCheck_2504_;
goto v_resetjp_2467_;
}
v_resetjp_2467_:
{
lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2475_; 
v___x_2470_ = lean_box(0);
lean_inc(v_fst_2465_);
v___x_2471_ = l_Lean_mkFVar(v_fst_2465_);
lean_inc_ref(v___x_2471_);
v___x_2472_ = l_Lean_Meta_FVarSubst_insert(v___x_2470_, v_majorFVarId_2399_, v___x_2471_);
v___x_2473_ = lean_unsigned_to_nat(0u);
if (v_isShared_2469_ == 0)
{
lean_ctor_set(v___x_2468_, 1, v___x_2473_);
lean_ctor_set(v___x_2468_, 0, v___x_2472_);
v___x_2475_ = v___x_2468_;
goto v_reusejp_2474_;
}
else
{
lean_object* v_reuseFailAlloc_2503_; 
v_reuseFailAlloc_2503_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2503_, 0, v___x_2472_);
lean_ctor_set(v_reuseFailAlloc_2503_, 1, v___x_2473_);
v___x_2475_ = v_reuseFailAlloc_2503_;
goto v_reusejp_2474_;
}
v_reusejp_2474_:
{
lean_object* v___x_2476_; lean_object* v_options_2477_; uint8_t v_hasTrace_2478_; 
v___x_2476_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_induction_spec__2(v_fst_2461_, v_a_2438_, v_sz_2447_, v___x_2448_, v___x_2475_);
lean_dec(v_a_2438_);
v_options_2477_ = lean_ctor_get(v___y_2445_, 2);
v_hasTrace_2478_ = lean_ctor_get_uint8(v_options_2477_, sizeof(void*)*1);
if (v_hasTrace_2478_ == 0)
{
lean_object* v_fst_2479_; 
v_fst_2479_ = lean_ctor_get(v___x_2476_, 0);
lean_inc(v_fst_2479_);
lean_dec_ref(v___x_2476_);
lean_inc(v_snd_2466_);
v___y_2421_ = v_fst_2465_;
v___y_2422_ = v_fst_2455_;
v___y_2423_ = v_snd_2466_;
v___y_2424_ = v_fst_2479_;
v___y_2425_ = v___x_2471_;
v___y_2426_ = v_snd_2466_;
v___y_2427_ = v_fst_2461_;
v___y_2428_ = v___x_2448_;
v___y_2429_ = v___y_2443_;
v___y_2430_ = v___y_2444_;
v___y_2431_ = v___y_2445_;
v___y_2432_ = v___y_2446_;
goto v___jp_2420_;
}
else
{
lean_object* v_fst_2480_; lean_object* v___x_2482_; uint8_t v_isShared_2483_; uint8_t v_isSharedCheck_2501_; 
v_fst_2480_ = lean_ctor_get(v___x_2476_, 0);
v_isSharedCheck_2501_ = !lean_is_exclusive(v___x_2476_);
if (v_isSharedCheck_2501_ == 0)
{
lean_object* v_unused_2502_; 
v_unused_2502_ = lean_ctor_get(v___x_2476_, 1);
lean_dec(v_unused_2502_);
v___x_2482_ = v___x_2476_;
v_isShared_2483_ = v_isSharedCheck_2501_;
goto v_resetjp_2481_;
}
else
{
lean_inc(v_fst_2480_);
lean_dec(v___x_2476_);
v___x_2482_ = lean_box(0);
v_isShared_2483_ = v_isSharedCheck_2501_;
goto v_resetjp_2481_;
}
v_resetjp_2481_:
{
lean_object* v_inheritedTraceOptions_2484_; lean_object* v___x_2485_; uint8_t v___x_2486_; 
v_inheritedTraceOptions_2484_ = lean_ctor_get(v___y_2445_, 13);
v___x_2485_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5);
v___x_2486_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2484_, v_options_2477_, v___x_2485_);
if (v___x_2486_ == 0)
{
lean_del_object(v___x_2482_);
lean_inc(v_snd_2466_);
v___y_2421_ = v_fst_2465_;
v___y_2422_ = v_fst_2455_;
v___y_2423_ = v_snd_2466_;
v___y_2424_ = v_fst_2480_;
v___y_2425_ = v___x_2471_;
v___y_2426_ = v_snd_2466_;
v___y_2427_ = v_fst_2461_;
v___y_2428_ = v___x_2448_;
v___y_2429_ = v___y_2443_;
v___y_2430_ = v___y_2444_;
v___y_2431_ = v___y_2445_;
v___y_2432_ = v___y_2446_;
goto v___jp_2420_;
}
else
{
lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2490_; 
v___x_2487_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__1);
lean_inc(v_snd_2466_);
v___x_2488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2488_, 0, v_snd_2466_);
if (v_isShared_2483_ == 0)
{
lean_ctor_set_tag(v___x_2482_, 7);
lean_ctor_set(v___x_2482_, 1, v___x_2488_);
lean_ctor_set(v___x_2482_, 0, v___x_2487_);
v___x_2490_ = v___x_2482_;
goto v_reusejp_2489_;
}
else
{
lean_object* v_reuseFailAlloc_2500_; 
v_reuseFailAlloc_2500_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2500_, 0, v___x_2487_);
lean_ctor_set(v_reuseFailAlloc_2500_, 1, v___x_2488_);
v___x_2490_ = v_reuseFailAlloc_2500_;
goto v_reusejp_2489_;
}
v_reusejp_2489_:
{
lean_object* v___x_2491_; 
v___x_2491_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1(v_cls_2441_, v___x_2490_, v___y_2443_, v___y_2444_, v___y_2445_, v___y_2446_);
if (lean_obj_tag(v___x_2491_) == 0)
{
lean_dec_ref_known(v___x_2491_, 1);
lean_inc(v_snd_2466_);
v___y_2421_ = v_fst_2465_;
v___y_2422_ = v_fst_2455_;
v___y_2423_ = v_snd_2466_;
v___y_2424_ = v_fst_2480_;
v___y_2425_ = v___x_2471_;
v___y_2426_ = v_snd_2466_;
v___y_2427_ = v_fst_2461_;
v___y_2428_ = v___x_2448_;
v___y_2429_ = v___y_2443_;
v___y_2430_ = v___y_2444_;
v___y_2431_ = v___y_2445_;
v___y_2432_ = v___y_2446_;
goto v___jp_2420_;
}
else
{
lean_object* v_a_2492_; lean_object* v___x_2494_; uint8_t v_isShared_2495_; uint8_t v_isSharedCheck_2499_; 
lean_dec(v_fst_2480_);
lean_dec_ref(v___x_2471_);
lean_dec(v_snd_2466_);
lean_dec(v_fst_2465_);
lean_dec(v_fst_2461_);
lean_dec(v_fst_2455_);
lean_dec_ref(v_givenNames_2400_);
lean_dec_ref(v_a_2396_);
v_a_2492_ = lean_ctor_get(v___x_2491_, 0);
v_isSharedCheck_2499_ = !lean_is_exclusive(v___x_2491_);
if (v_isSharedCheck_2499_ == 0)
{
v___x_2494_ = v___x_2491_;
v_isShared_2495_ = v_isSharedCheck_2499_;
goto v_resetjp_2493_;
}
else
{
lean_inc(v_a_2492_);
lean_dec(v___x_2491_);
v___x_2494_ = lean_box(0);
v_isShared_2495_ = v_isSharedCheck_2499_;
goto v_resetjp_2493_;
}
v_resetjp_2493_:
{
lean_object* v___x_2497_; 
if (v_isShared_2495_ == 0)
{
v___x_2497_ = v___x_2494_;
goto v_reusejp_2496_;
}
else
{
lean_object* v_reuseFailAlloc_2498_; 
v_reuseFailAlloc_2498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2498_, 0, v_a_2492_);
v___x_2497_ = v_reuseFailAlloc_2498_;
goto v_reusejp_2496_;
}
v_reusejp_2496_:
{
return v___x_2497_;
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
lean_object* v_a_2505_; lean_object* v___x_2507_; uint8_t v_isShared_2508_; uint8_t v_isSharedCheck_2512_; 
lean_dec(v_fst_2461_);
lean_dec(v_fst_2455_);
lean_dec(v_a_2438_);
lean_dec_ref(v_givenNames_2400_);
lean_dec(v_majorFVarId_2399_);
lean_dec_ref(v_a_2396_);
v_a_2505_ = lean_ctor_get(v___x_2463_, 0);
v_isSharedCheck_2512_ = !lean_is_exclusive(v___x_2463_);
if (v_isSharedCheck_2512_ == 0)
{
v___x_2507_ = v___x_2463_;
v_isShared_2508_ = v_isSharedCheck_2512_;
goto v_resetjp_2506_;
}
else
{
lean_inc(v_a_2505_);
lean_dec(v___x_2463_);
v___x_2507_ = lean_box(0);
v_isShared_2508_ = v_isSharedCheck_2512_;
goto v_resetjp_2506_;
}
v_resetjp_2506_:
{
lean_object* v___x_2510_; 
if (v_isShared_2508_ == 0)
{
v___x_2510_ = v___x_2507_;
goto v_reusejp_2509_;
}
else
{
lean_object* v_reuseFailAlloc_2511_; 
v_reuseFailAlloc_2511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2511_, 0, v_a_2505_);
v___x_2510_ = v_reuseFailAlloc_2511_;
goto v_reusejp_2509_;
}
v_reusejp_2509_:
{
return v___x_2510_;
}
}
}
}
else
{
lean_object* v_a_2513_; lean_object* v___x_2515_; uint8_t v_isShared_2516_; uint8_t v_isSharedCheck_2520_; 
lean_dec(v_fst_2455_);
lean_dec(v_a_2438_);
lean_dec_ref(v_givenNames_2400_);
lean_dec(v_majorFVarId_2399_);
lean_dec_ref(v_a_2396_);
v_a_2513_ = lean_ctor_get(v___x_2459_, 0);
v_isSharedCheck_2520_ = !lean_is_exclusive(v___x_2459_);
if (v_isSharedCheck_2520_ == 0)
{
v___x_2515_ = v___x_2459_;
v_isShared_2516_ = v_isSharedCheck_2520_;
goto v_resetjp_2514_;
}
else
{
lean_inc(v_a_2513_);
lean_dec(v___x_2459_);
v___x_2515_ = lean_box(0);
v_isShared_2516_ = v_isSharedCheck_2520_;
goto v_resetjp_2514_;
}
v_resetjp_2514_:
{
lean_object* v___x_2518_; 
if (v_isShared_2516_ == 0)
{
v___x_2518_ = v___x_2515_;
goto v_reusejp_2517_;
}
else
{
lean_object* v_reuseFailAlloc_2519_; 
v_reuseFailAlloc_2519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2519_, 0, v_a_2513_);
v___x_2518_ = v_reuseFailAlloc_2519_;
goto v_reusejp_2517_;
}
v_reusejp_2517_:
{
return v___x_2518_;
}
}
}
}
else
{
lean_object* v_a_2521_; lean_object* v___x_2523_; uint8_t v_isShared_2524_; uint8_t v_isSharedCheck_2528_; 
lean_dec(v_a_2438_);
lean_dec_ref(v_givenNames_2400_);
lean_dec(v_majorFVarId_2399_);
lean_dec_ref(v_a_2396_);
v_a_2521_ = lean_ctor_get(v___x_2453_, 0);
v_isSharedCheck_2528_ = !lean_is_exclusive(v___x_2453_);
if (v_isSharedCheck_2528_ == 0)
{
v___x_2523_ = v___x_2453_;
v_isShared_2524_ = v_isSharedCheck_2528_;
goto v_resetjp_2522_;
}
else
{
lean_inc(v_a_2521_);
lean_dec(v___x_2453_);
v___x_2523_ = lean_box(0);
v_isShared_2524_ = v_isSharedCheck_2528_;
goto v_resetjp_2522_;
}
v_resetjp_2522_:
{
lean_object* v___x_2526_; 
if (v_isShared_2524_ == 0)
{
v___x_2526_ = v___x_2523_;
goto v_reusejp_2525_;
}
else
{
lean_object* v_reuseFailAlloc_2527_; 
v_reuseFailAlloc_2527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2527_, 0, v_a_2521_);
v___x_2526_ = v_reuseFailAlloc_2527_;
goto v_reusejp_2525_;
}
v_reusejp_2525_:
{
return v___x_2526_;
}
}
}
}
v___jp_2529_:
{
if (v_a_2530_ == 0)
{
lean_dec(v_recursorName_2401_);
v___y_2443_ = v___y_2405_;
v___y_2444_ = v___y_2406_;
v___y_2445_ = v___y_2407_;
v___y_2446_ = v___y_2408_;
goto v___jp_2442_;
}
else
{
lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; 
v___x_2531_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__3, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__3);
v___x_2532_ = l_Lean_MessageData_ofName(v_recursorName_2401_);
v___x_2533_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2533_, 0, v___x_2531_);
lean_ctor_set(v___x_2533_, 1, v___x_2532_);
v___x_2534_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__5, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__5_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__5);
v___x_2535_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2535_, 0, v___x_2533_);
lean_ctor_set(v___x_2535_, 1, v___x_2534_);
v___x_2536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2536_, 0, v___x_2535_);
lean_inc(v_mvarId_2398_);
v___x_2537_ = l_Lean_Meta_throwTacticEx___redArg(v___x_2419_, v_mvarId_2398_, v___x_2536_, v___y_2405_, v___y_2406_, v___y_2407_, v___y_2408_);
if (lean_obj_tag(v___x_2537_) == 0)
{
lean_dec_ref_known(v___x_2537_, 1);
v___y_2443_ = v___y_2405_;
v___y_2444_ = v___y_2406_;
v___y_2445_ = v___y_2407_;
v___y_2446_ = v___y_2408_;
goto v___jp_2442_;
}
else
{
lean_object* v_a_2538_; lean_object* v___x_2540_; uint8_t v_isShared_2541_; uint8_t v_isSharedCheck_2545_; 
lean_dec(v_a_2438_);
lean_dec_ref(v_givenNames_2400_);
lean_dec(v_majorFVarId_2399_);
lean_dec(v_mvarId_2398_);
lean_dec_ref(v_a_2396_);
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
else
{
lean_object* v_a_2550_; lean_object* v___x_2552_; uint8_t v_isShared_2553_; uint8_t v_isSharedCheck_2557_; 
lean_dec(v_a_2438_);
lean_dec(v_recursorName_2401_);
lean_dec_ref(v_givenNames_2400_);
lean_dec(v_majorFVarId_2399_);
lean_dec(v_mvarId_2398_);
lean_dec_ref(v_a_2396_);
v_a_2550_ = lean_ctor_get(v___x_2439_, 0);
v_isSharedCheck_2557_ = !lean_is_exclusive(v___x_2439_);
if (v_isSharedCheck_2557_ == 0)
{
v___x_2552_ = v___x_2439_;
v_isShared_2553_ = v_isSharedCheck_2557_;
goto v_resetjp_2551_;
}
else
{
lean_inc(v_a_2550_);
lean_dec(v___x_2439_);
v___x_2552_ = lean_box(0);
v_isShared_2553_ = v_isSharedCheck_2557_;
goto v_resetjp_2551_;
}
v_resetjp_2551_:
{
lean_object* v___x_2555_; 
if (v_isShared_2553_ == 0)
{
v___x_2555_ = v___x_2552_;
goto v_reusejp_2554_;
}
else
{
lean_object* v_reuseFailAlloc_2556_; 
v_reuseFailAlloc_2556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2556_, 0, v_a_2550_);
v___x_2555_ = v_reuseFailAlloc_2556_;
goto v_reusejp_2554_;
}
v_reusejp_2554_:
{
return v___x_2555_;
}
}
}
}
else
{
lean_object* v_a_2558_; lean_object* v___x_2560_; uint8_t v_isShared_2561_; uint8_t v_isSharedCheck_2565_; 
lean_dec(v_recursorName_2401_);
lean_dec_ref(v_givenNames_2400_);
lean_dec(v_majorFVarId_2399_);
lean_dec(v_mvarId_2398_);
lean_dec_ref(v_a_2396_);
v_a_2558_ = lean_ctor_get(v___x_2437_, 0);
v_isSharedCheck_2565_ = !lean_is_exclusive(v___x_2437_);
if (v_isSharedCheck_2565_ == 0)
{
v___x_2560_ = v___x_2437_;
v_isShared_2561_ = v_isSharedCheck_2565_;
goto v_resetjp_2559_;
}
else
{
lean_inc(v_a_2558_);
lean_dec(v___x_2437_);
v___x_2560_ = lean_box(0);
v_isShared_2561_ = v_isSharedCheck_2565_;
goto v_resetjp_2559_;
}
v_resetjp_2559_:
{
lean_object* v___x_2563_; 
if (v_isShared_2561_ == 0)
{
v___x_2563_ = v___x_2560_;
goto v_reusejp_2562_;
}
else
{
lean_object* v_reuseFailAlloc_2564_; 
v_reuseFailAlloc_2564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2564_, 0, v_a_2558_);
v___x_2563_ = v_reuseFailAlloc_2564_;
goto v_reusejp_2562_;
}
v_reusejp_2562_:
{
return v___x_2563_;
}
}
}
v___jp_2420_:
{
size_t v_sz_2433_; lean_object* v___x_2434_; lean_object* v___f_2435_; lean_object* v___x_2436_; 
v_sz_2433_ = lean_array_size(v___y_2427_);
v___x_2434_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__3(v_sz_2433_, v___y_2428_, v___y_2427_);
v___f_2435_ = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4___lam__0___boxed), 14, 9);
lean_closure_set(v___f_2435_, 0, v___y_2423_);
lean_closure_set(v___f_2435_, 1, v___x_2419_);
lean_closure_set(v___f_2435_, 2, v___y_2421_);
lean_closure_set(v___f_2435_, 3, v_a_2396_);
lean_closure_set(v___f_2435_, 4, v___x_2434_);
lean_closure_set(v___f_2435_, 5, v_givenNames_2400_);
lean_closure_set(v___f_2435_, 6, v___y_2422_);
lean_closure_set(v___f_2435_, 7, v___y_2425_);
lean_closure_set(v___f_2435_, 8, v___y_2424_);
v___x_2436_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___redArg(v___y_2426_, v___f_2435_, v___y_2429_, v___y_2430_, v___y_2431_, v___y_2432_);
return v___x_2436_;
}
}
else
{
lean_object* v_a_2566_; lean_object* v___x_2568_; uint8_t v_isShared_2569_; uint8_t v_isSharedCheck_2573_; 
lean_dec(v_recursorName_2401_);
lean_dec_ref(v_givenNames_2400_);
lean_dec(v_majorFVarId_2399_);
lean_dec(v_mvarId_2398_);
lean_dec_ref(v_val_2397_);
lean_dec_ref(v_a_2396_);
v_a_2566_ = lean_ctor_get(v___x_2418_, 0);
v_isSharedCheck_2573_ = !lean_is_exclusive(v___x_2418_);
if (v_isSharedCheck_2573_ == 0)
{
v___x_2568_ = v___x_2418_;
v_isShared_2569_ = v_isSharedCheck_2573_;
goto v_resetjp_2567_;
}
else
{
lean_inc(v_a_2566_);
lean_dec(v___x_2418_);
v___x_2568_ = lean_box(0);
v_isShared_2569_ = v_isSharedCheck_2573_;
goto v_resetjp_2567_;
}
v_resetjp_2567_:
{
lean_object* v___x_2571_; 
if (v_isShared_2569_ == 0)
{
v___x_2571_ = v___x_2568_;
goto v_reusejp_2570_;
}
else
{
lean_object* v_reuseFailAlloc_2572_; 
v_reuseFailAlloc_2572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2572_, 0, v_a_2566_);
v___x_2571_ = v_reuseFailAlloc_2572_;
goto v_reusejp_2570_;
}
v_reusejp_2570_:
{
return v___x_2571_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___boxed(lean_object* v_a_2574_, lean_object* v_val_2575_, lean_object* v_mvarId_2576_, lean_object* v_majorFVarId_2577_, lean_object* v_givenNames_2578_, lean_object* v_recursorName_2579_, lean_object* v_x_2580_, lean_object* v_x_2581_, lean_object* v_x_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_, lean_object* v___y_2587_){
_start:
{
lean_object* v_res_2588_; 
v_res_2588_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4(v_a_2574_, v_val_2575_, v_mvarId_2576_, v_majorFVarId_2577_, v_givenNames_2578_, v_recursorName_2579_, v_x_2580_, v_x_2581_, v_x_2582_, v___y_2583_, v___y_2584_, v___y_2585_, v___y_2586_);
lean_dec(v___y_2586_);
lean_dec_ref(v___y_2585_);
lean_dec(v___y_2584_);
lean_dec_ref(v___y_2583_);
return v_res_2588_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4(lean_object* v_val_2589_, lean_object* v_mvarId_2590_, lean_object* v_a_2591_, lean_object* v_majorFVarId_2592_, lean_object* v_givenNames_2593_, lean_object* v_recursorName_2594_, lean_object* v_x_2595_, lean_object* v_x_2596_, lean_object* v_x_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_){
_start:
{
if (lean_obj_tag(v_x_2595_) == 5)
{
lean_object* v_fn_2603_; lean_object* v_arg_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; 
v_fn_2603_ = lean_ctor_get(v_x_2595_, 0);
lean_inc_ref(v_fn_2603_);
v_arg_2604_ = lean_ctor_get(v_x_2595_, 1);
lean_inc_ref(v_arg_2604_);
lean_dec_ref_known(v_x_2595_, 2);
v___x_2605_ = lean_array_set(v_x_2596_, v_x_2597_, v_arg_2604_);
v___x_2606_ = lean_unsigned_to_nat(1u);
v___x_2607_ = lean_nat_sub(v_x_2597_, v___x_2606_);
v___x_2608_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4(v_a_2591_, v_val_2589_, v_mvarId_2590_, v_majorFVarId_2592_, v_givenNames_2593_, v_recursorName_2594_, v_fn_2603_, v___x_2605_, v___x_2607_, v___y_2598_, v___y_2599_, v___y_2600_, v___y_2601_);
return v___x_2608_;
}
else
{
uint8_t v_depElim_2609_; lean_object* v_paramsPos_2610_; lean_object* v___x_2611_; 
lean_dec_ref(v_x_2595_);
v_depElim_2609_ = lean_ctor_get_uint8(v_a_2591_, sizeof(void*)*8);
v_paramsPos_2610_ = lean_ctor_get(v_a_2591_, 5);
lean_inc(v_paramsPos_2610_);
lean_inc(v_mvarId_2590_);
lean_inc_ref(v_val_2589_);
v___x_2611_ = l_List_forM___at___00Lean_MVarId_induction_spec__0(v_x_2596_, v_val_2589_, v_mvarId_2590_, v_paramsPos_2610_, v___y_2598_, v___y_2599_, v___y_2600_, v___y_2601_);
lean_dec_ref(v_x_2596_);
if (lean_obj_tag(v___x_2611_) == 0)
{
lean_object* v___x_2612_; lean_object* v___y_2614_; lean_object* v___y_2615_; lean_object* v___y_2616_; lean_object* v___y_2617_; lean_object* v___y_2618_; size_t v___y_2619_; lean_object* v___y_2620_; lean_object* v___y_2621_; lean_object* v___y_2622_; lean_object* v___y_2623_; lean_object* v___y_2624_; lean_object* v___y_2625_; lean_object* v___x_2630_; 
lean_dec_ref_known(v___x_2611_, 1);
v___x_2612_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1));
lean_inc_ref(v_a_2591_);
lean_inc(v_mvarId_2590_);
v___x_2630_ = l_Lean_Meta_getMajorTypeIndices(v_mvarId_2590_, v___x_2612_, v_a_2591_, v_val_2589_, v___y_2598_, v___y_2599_, v___y_2600_, v___y_2601_);
if (lean_obj_tag(v___x_2630_) == 0)
{
lean_object* v_a_2631_; lean_object* v___x_2632_; 
v_a_2631_ = lean_ctor_get(v___x_2630_, 0);
lean_inc(v_a_2631_);
lean_dec_ref_known(v___x_2630_, 1);
lean_inc(v_mvarId_2590_);
v___x_2632_ = l_Lean_MVarId_getType(v_mvarId_2590_, v___y_2598_, v___y_2599_, v___y_2600_, v___y_2601_);
if (lean_obj_tag(v___x_2632_) == 0)
{
lean_object* v_a_2633_; lean_object* v_cls_2634_; lean_object* v___y_2636_; lean_object* v___y_2637_; lean_object* v___y_2638_; lean_object* v___y_2639_; uint8_t v_a_2723_; uint8_t v___x_2739_; 
v_a_2633_ = lean_ctor_get(v___x_2632_, 0);
lean_inc(v_a_2633_);
lean_dec_ref_known(v___x_2632_, 1);
v_cls_2634_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__2));
v___x_2739_ = lean_bool_not(v_depElim_2609_);
if (v___x_2739_ == 0)
{
lean_dec(v_a_2633_);
v_a_2723_ = v___x_2739_;
goto v___jp_2722_;
}
else
{
lean_object* v___x_2740_; lean_object* v_a_2741_; uint8_t v___x_2742_; 
lean_inc(v_majorFVarId_2592_);
v___x_2740_ = l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2___redArg(v_a_2633_, v_majorFVarId_2592_, v___y_2599_);
v_a_2741_ = lean_ctor_get(v___x_2740_, 0);
lean_inc(v_a_2741_);
lean_dec_ref(v___x_2740_);
v___x_2742_ = lean_unbox(v_a_2741_);
lean_dec(v_a_2741_);
v_a_2723_ = v___x_2742_;
goto v___jp_2722_;
}
v___jp_2635_:
{
size_t v_sz_2640_; size_t v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; uint8_t v___x_2644_; uint8_t v___x_2645_; lean_object* v___x_2646_; 
v_sz_2640_ = lean_array_size(v_a_2631_);
v___x_2641_ = ((size_t)0ULL);
lean_inc(v_a_2631_);
v___x_2642_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_induction_spec__1(v_sz_2640_, v___x_2641_, v_a_2631_);
lean_inc(v_majorFVarId_2592_);
v___x_2643_ = lean_array_push(v___x_2642_, v_majorFVarId_2592_);
v___x_2644_ = 1;
v___x_2645_ = 0;
v___x_2646_ = l_Lean_MVarId_revert(v_mvarId_2590_, v___x_2643_, v___x_2644_, v___x_2645_, v___y_2636_, v___y_2637_, v___y_2638_, v___y_2639_);
if (lean_obj_tag(v___x_2646_) == 0)
{
lean_object* v_a_2647_; lean_object* v_fst_2648_; lean_object* v_snd_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; 
v_a_2647_ = lean_ctor_get(v___x_2646_, 0);
lean_inc(v_a_2647_);
lean_dec_ref_known(v___x_2646_, 1);
v_fst_2648_ = lean_ctor_get(v_a_2647_, 0);
lean_inc(v_fst_2648_);
v_snd_2649_ = lean_ctor_get(v_a_2647_, 1);
lean_inc(v_snd_2649_);
lean_dec(v_a_2647_);
v___x_2650_ = lean_array_get_size(v_a_2631_);
v___x_2651_ = lean_box(0);
v___x_2652_ = l_Lean_Meta_introNCore(v_snd_2649_, v___x_2650_, v___x_2651_, v___x_2645_, v___x_2644_, v___y_2636_, v___y_2637_, v___y_2638_, v___y_2639_);
if (lean_obj_tag(v___x_2652_) == 0)
{
lean_object* v_a_2653_; lean_object* v_fst_2654_; lean_object* v_snd_2655_; lean_object* v___x_2656_; 
v_a_2653_ = lean_ctor_get(v___x_2652_, 0);
lean_inc(v_a_2653_);
lean_dec_ref_known(v___x_2652_, 1);
v_fst_2654_ = lean_ctor_get(v_a_2653_, 0);
lean_inc(v_fst_2654_);
v_snd_2655_ = lean_ctor_get(v_a_2653_, 1);
lean_inc(v_snd_2655_);
lean_dec(v_a_2653_);
v___x_2656_ = l_Lean_Meta_intro1Core(v_snd_2655_, v___x_2644_, v___y_2636_, v___y_2637_, v___y_2638_, v___y_2639_);
if (lean_obj_tag(v___x_2656_) == 0)
{
lean_object* v_a_2657_; lean_object* v_fst_2658_; lean_object* v_snd_2659_; lean_object* v___x_2661_; uint8_t v_isShared_2662_; uint8_t v_isSharedCheck_2697_; 
v_a_2657_ = lean_ctor_get(v___x_2656_, 0);
lean_inc(v_a_2657_);
lean_dec_ref_known(v___x_2656_, 1);
v_fst_2658_ = lean_ctor_get(v_a_2657_, 0);
v_snd_2659_ = lean_ctor_get(v_a_2657_, 1);
v_isSharedCheck_2697_ = !lean_is_exclusive(v_a_2657_);
if (v_isSharedCheck_2697_ == 0)
{
v___x_2661_ = v_a_2657_;
v_isShared_2662_ = v_isSharedCheck_2697_;
goto v_resetjp_2660_;
}
else
{
lean_inc(v_snd_2659_);
lean_inc(v_fst_2658_);
lean_dec(v_a_2657_);
v___x_2661_ = lean_box(0);
v_isShared_2662_ = v_isSharedCheck_2697_;
goto v_resetjp_2660_;
}
v_resetjp_2660_:
{
lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2668_; 
v___x_2663_ = lean_box(0);
lean_inc(v_fst_2658_);
v___x_2664_ = l_Lean_mkFVar(v_fst_2658_);
lean_inc_ref(v___x_2664_);
v___x_2665_ = l_Lean_Meta_FVarSubst_insert(v___x_2663_, v_majorFVarId_2592_, v___x_2664_);
v___x_2666_ = lean_unsigned_to_nat(0u);
if (v_isShared_2662_ == 0)
{
lean_ctor_set(v___x_2661_, 1, v___x_2666_);
lean_ctor_set(v___x_2661_, 0, v___x_2665_);
v___x_2668_ = v___x_2661_;
goto v_reusejp_2667_;
}
else
{
lean_object* v_reuseFailAlloc_2696_; 
v_reuseFailAlloc_2696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2696_, 0, v___x_2665_);
lean_ctor_set(v_reuseFailAlloc_2696_, 1, v___x_2666_);
v___x_2668_ = v_reuseFailAlloc_2696_;
goto v_reusejp_2667_;
}
v_reusejp_2667_:
{
lean_object* v___x_2669_; lean_object* v_options_2670_; uint8_t v_hasTrace_2671_; 
v___x_2669_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_induction_spec__2(v_fst_2654_, v_a_2631_, v_sz_2640_, v___x_2641_, v___x_2668_);
lean_dec(v_a_2631_);
v_options_2670_ = lean_ctor_get(v___y_2638_, 2);
v_hasTrace_2671_ = lean_ctor_get_uint8(v_options_2670_, sizeof(void*)*1);
if (v_hasTrace_2671_ == 0)
{
lean_object* v_fst_2672_; 
v_fst_2672_ = lean_ctor_get(v___x_2669_, 0);
lean_inc(v_fst_2672_);
lean_dec_ref(v___x_2669_);
lean_inc(v_snd_2659_);
v___y_2614_ = v_fst_2648_;
v___y_2615_ = v_fst_2672_;
v___y_2616_ = v_snd_2659_;
v___y_2617_ = v___x_2664_;
v___y_2618_ = v_fst_2658_;
v___y_2619_ = v___x_2641_;
v___y_2620_ = v_snd_2659_;
v___y_2621_ = v_fst_2654_;
v___y_2622_ = v___y_2636_;
v___y_2623_ = v___y_2637_;
v___y_2624_ = v___y_2638_;
v___y_2625_ = v___y_2639_;
goto v___jp_2613_;
}
else
{
lean_object* v_fst_2673_; lean_object* v___x_2675_; uint8_t v_isShared_2676_; uint8_t v_isSharedCheck_2694_; 
v_fst_2673_ = lean_ctor_get(v___x_2669_, 0);
v_isSharedCheck_2694_ = !lean_is_exclusive(v___x_2669_);
if (v_isSharedCheck_2694_ == 0)
{
lean_object* v_unused_2695_; 
v_unused_2695_ = lean_ctor_get(v___x_2669_, 1);
lean_dec(v_unused_2695_);
v___x_2675_ = v___x_2669_;
v_isShared_2676_ = v_isSharedCheck_2694_;
goto v_resetjp_2674_;
}
else
{
lean_inc(v_fst_2673_);
lean_dec(v___x_2669_);
v___x_2675_ = lean_box(0);
v_isShared_2676_ = v_isSharedCheck_2694_;
goto v_resetjp_2674_;
}
v_resetjp_2674_:
{
lean_object* v_inheritedTraceOptions_2677_; lean_object* v___x_2678_; uint8_t v___x_2679_; 
v_inheritedTraceOptions_2677_ = lean_ctor_get(v___y_2638_, 13);
v___x_2678_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5);
v___x_2679_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2677_, v_options_2670_, v___x_2678_);
if (v___x_2679_ == 0)
{
lean_del_object(v___x_2675_);
lean_inc(v_snd_2659_);
v___y_2614_ = v_fst_2648_;
v___y_2615_ = v_fst_2673_;
v___y_2616_ = v_snd_2659_;
v___y_2617_ = v___x_2664_;
v___y_2618_ = v_fst_2658_;
v___y_2619_ = v___x_2641_;
v___y_2620_ = v_snd_2659_;
v___y_2621_ = v_fst_2654_;
v___y_2622_ = v___y_2636_;
v___y_2623_ = v___y_2637_;
v___y_2624_ = v___y_2638_;
v___y_2625_ = v___y_2639_;
goto v___jp_2613_;
}
else
{
lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2683_; 
v___x_2680_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__1);
lean_inc(v_snd_2659_);
v___x_2681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2681_, 0, v_snd_2659_);
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
v___x_2684_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1(v_cls_2634_, v___x_2683_, v___y_2636_, v___y_2637_, v___y_2638_, v___y_2639_);
if (lean_obj_tag(v___x_2684_) == 0)
{
lean_dec_ref_known(v___x_2684_, 1);
lean_inc(v_snd_2659_);
v___y_2614_ = v_fst_2648_;
v___y_2615_ = v_fst_2673_;
v___y_2616_ = v_snd_2659_;
v___y_2617_ = v___x_2664_;
v___y_2618_ = v_fst_2658_;
v___y_2619_ = v___x_2641_;
v___y_2620_ = v_snd_2659_;
v___y_2621_ = v_fst_2654_;
v___y_2622_ = v___y_2636_;
v___y_2623_ = v___y_2637_;
v___y_2624_ = v___y_2638_;
v___y_2625_ = v___y_2639_;
goto v___jp_2613_;
}
else
{
lean_object* v_a_2685_; lean_object* v___x_2687_; uint8_t v_isShared_2688_; uint8_t v_isSharedCheck_2692_; 
lean_dec(v_fst_2673_);
lean_dec_ref(v___x_2664_);
lean_dec(v_snd_2659_);
lean_dec(v_fst_2658_);
lean_dec(v_fst_2654_);
lean_dec(v_fst_2648_);
lean_dec_ref(v_givenNames_2593_);
lean_dec_ref(v_a_2591_);
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
lean_dec(v_fst_2654_);
lean_dec(v_fst_2648_);
lean_dec(v_a_2631_);
lean_dec_ref(v_givenNames_2593_);
lean_dec(v_majorFVarId_2592_);
lean_dec_ref(v_a_2591_);
v_a_2698_ = lean_ctor_get(v___x_2656_, 0);
v_isSharedCheck_2705_ = !lean_is_exclusive(v___x_2656_);
if (v_isSharedCheck_2705_ == 0)
{
v___x_2700_ = v___x_2656_;
v_isShared_2701_ = v_isSharedCheck_2705_;
goto v_resetjp_2699_;
}
else
{
lean_inc(v_a_2698_);
lean_dec(v___x_2656_);
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
lean_dec(v_fst_2648_);
lean_dec(v_a_2631_);
lean_dec_ref(v_givenNames_2593_);
lean_dec(v_majorFVarId_2592_);
lean_dec_ref(v_a_2591_);
v_a_2706_ = lean_ctor_get(v___x_2652_, 0);
v_isSharedCheck_2713_ = !lean_is_exclusive(v___x_2652_);
if (v_isSharedCheck_2713_ == 0)
{
v___x_2708_ = v___x_2652_;
v_isShared_2709_ = v_isSharedCheck_2713_;
goto v_resetjp_2707_;
}
else
{
lean_inc(v_a_2706_);
lean_dec(v___x_2652_);
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
lean_dec(v_a_2631_);
lean_dec_ref(v_givenNames_2593_);
lean_dec(v_majorFVarId_2592_);
lean_dec_ref(v_a_2591_);
v_a_2714_ = lean_ctor_get(v___x_2646_, 0);
v_isSharedCheck_2721_ = !lean_is_exclusive(v___x_2646_);
if (v_isSharedCheck_2721_ == 0)
{
v___x_2716_ = v___x_2646_;
v_isShared_2717_ = v_isSharedCheck_2721_;
goto v_resetjp_2715_;
}
else
{
lean_inc(v_a_2714_);
lean_dec(v___x_2646_);
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
v___jp_2722_:
{
if (v_a_2723_ == 0)
{
lean_dec(v_recursorName_2594_);
v___y_2636_ = v___y_2598_;
v___y_2637_ = v___y_2599_;
v___y_2638_ = v___y_2600_;
v___y_2639_ = v___y_2601_;
goto v___jp_2635_;
}
else
{
lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; 
v___x_2724_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__3, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__3);
v___x_2725_ = l_Lean_MessageData_ofName(v_recursorName_2594_);
v___x_2726_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2726_, 0, v___x_2724_);
lean_ctor_set(v___x_2726_, 1, v___x_2725_);
v___x_2727_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__5, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__5_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__5);
v___x_2728_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2728_, 0, v___x_2726_);
lean_ctor_set(v___x_2728_, 1, v___x_2727_);
v___x_2729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2729_, 0, v___x_2728_);
lean_inc(v_mvarId_2590_);
v___x_2730_ = l_Lean_Meta_throwTacticEx___redArg(v___x_2612_, v_mvarId_2590_, v___x_2729_, v___y_2598_, v___y_2599_, v___y_2600_, v___y_2601_);
if (lean_obj_tag(v___x_2730_) == 0)
{
lean_dec_ref_known(v___x_2730_, 1);
v___y_2636_ = v___y_2598_;
v___y_2637_ = v___y_2599_;
v___y_2638_ = v___y_2600_;
v___y_2639_ = v___y_2601_;
goto v___jp_2635_;
}
else
{
lean_object* v_a_2731_; lean_object* v___x_2733_; uint8_t v_isShared_2734_; uint8_t v_isSharedCheck_2738_; 
lean_dec(v_a_2631_);
lean_dec_ref(v_givenNames_2593_);
lean_dec(v_majorFVarId_2592_);
lean_dec_ref(v_a_2591_);
lean_dec(v_mvarId_2590_);
v_a_2731_ = lean_ctor_get(v___x_2730_, 0);
v_isSharedCheck_2738_ = !lean_is_exclusive(v___x_2730_);
if (v_isSharedCheck_2738_ == 0)
{
v___x_2733_ = v___x_2730_;
v_isShared_2734_ = v_isSharedCheck_2738_;
goto v_resetjp_2732_;
}
else
{
lean_inc(v_a_2731_);
lean_dec(v___x_2730_);
v___x_2733_ = lean_box(0);
v_isShared_2734_ = v_isSharedCheck_2738_;
goto v_resetjp_2732_;
}
v_resetjp_2732_:
{
lean_object* v___x_2736_; 
if (v_isShared_2734_ == 0)
{
v___x_2736_ = v___x_2733_;
goto v_reusejp_2735_;
}
else
{
lean_object* v_reuseFailAlloc_2737_; 
v_reuseFailAlloc_2737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2737_, 0, v_a_2731_);
v___x_2736_ = v_reuseFailAlloc_2737_;
goto v_reusejp_2735_;
}
v_reusejp_2735_:
{
return v___x_2736_;
}
}
}
}
}
}
else
{
lean_object* v_a_2743_; lean_object* v___x_2745_; uint8_t v_isShared_2746_; uint8_t v_isSharedCheck_2750_; 
lean_dec(v_a_2631_);
lean_dec(v_recursorName_2594_);
lean_dec_ref(v_givenNames_2593_);
lean_dec(v_majorFVarId_2592_);
lean_dec_ref(v_a_2591_);
lean_dec(v_mvarId_2590_);
v_a_2743_ = lean_ctor_get(v___x_2632_, 0);
v_isSharedCheck_2750_ = !lean_is_exclusive(v___x_2632_);
if (v_isSharedCheck_2750_ == 0)
{
v___x_2745_ = v___x_2632_;
v_isShared_2746_ = v_isSharedCheck_2750_;
goto v_resetjp_2744_;
}
else
{
lean_inc(v_a_2743_);
lean_dec(v___x_2632_);
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
}
else
{
lean_object* v_a_2751_; lean_object* v___x_2753_; uint8_t v_isShared_2754_; uint8_t v_isSharedCheck_2758_; 
lean_dec(v_recursorName_2594_);
lean_dec_ref(v_givenNames_2593_);
lean_dec(v_majorFVarId_2592_);
lean_dec_ref(v_a_2591_);
lean_dec(v_mvarId_2590_);
v_a_2751_ = lean_ctor_get(v___x_2630_, 0);
v_isSharedCheck_2758_ = !lean_is_exclusive(v___x_2630_);
if (v_isSharedCheck_2758_ == 0)
{
v___x_2753_ = v___x_2630_;
v_isShared_2754_ = v_isSharedCheck_2758_;
goto v_resetjp_2752_;
}
else
{
lean_inc(v_a_2751_);
lean_dec(v___x_2630_);
v___x_2753_ = lean_box(0);
v_isShared_2754_ = v_isSharedCheck_2758_;
goto v_resetjp_2752_;
}
v_resetjp_2752_:
{
lean_object* v___x_2756_; 
if (v_isShared_2754_ == 0)
{
v___x_2756_ = v___x_2753_;
goto v_reusejp_2755_;
}
else
{
lean_object* v_reuseFailAlloc_2757_; 
v_reuseFailAlloc_2757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2757_, 0, v_a_2751_);
v___x_2756_ = v_reuseFailAlloc_2757_;
goto v_reusejp_2755_;
}
v_reusejp_2755_:
{
return v___x_2756_;
}
}
}
v___jp_2613_:
{
size_t v_sz_2626_; lean_object* v___x_2627_; lean_object* v___f_2628_; lean_object* v___x_2629_; 
v_sz_2626_ = lean_array_size(v___y_2621_);
v___x_2627_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__3(v_sz_2626_, v___y_2619_, v___y_2621_);
v___f_2628_ = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4___lam__0___boxed), 14, 9);
lean_closure_set(v___f_2628_, 0, v___y_2616_);
lean_closure_set(v___f_2628_, 1, v___x_2612_);
lean_closure_set(v___f_2628_, 2, v___y_2618_);
lean_closure_set(v___f_2628_, 3, v_a_2591_);
lean_closure_set(v___f_2628_, 4, v___x_2627_);
lean_closure_set(v___f_2628_, 5, v_givenNames_2593_);
lean_closure_set(v___f_2628_, 6, v___y_2614_);
lean_closure_set(v___f_2628_, 7, v___y_2617_);
lean_closure_set(v___f_2628_, 8, v___y_2615_);
v___x_2629_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___redArg(v___y_2620_, v___f_2628_, v___y_2622_, v___y_2623_, v___y_2624_, v___y_2625_);
return v___x_2629_;
}
}
else
{
lean_object* v_a_2759_; lean_object* v___x_2761_; uint8_t v_isShared_2762_; uint8_t v_isSharedCheck_2766_; 
lean_dec(v_recursorName_2594_);
lean_dec_ref(v_givenNames_2593_);
lean_dec(v_majorFVarId_2592_);
lean_dec_ref(v_a_2591_);
lean_dec(v_mvarId_2590_);
lean_dec_ref(v_val_2589_);
v_a_2759_ = lean_ctor_get(v___x_2611_, 0);
v_isSharedCheck_2766_ = !lean_is_exclusive(v___x_2611_);
if (v_isSharedCheck_2766_ == 0)
{
v___x_2761_ = v___x_2611_;
v_isShared_2762_ = v_isSharedCheck_2766_;
goto v_resetjp_2760_;
}
else
{
lean_inc(v_a_2759_);
lean_dec(v___x_2611_);
v___x_2761_ = lean_box(0);
v_isShared_2762_ = v_isSharedCheck_2766_;
goto v_resetjp_2760_;
}
v_resetjp_2760_:
{
lean_object* v___x_2764_; 
if (v_isShared_2762_ == 0)
{
v___x_2764_ = v___x_2761_;
goto v_reusejp_2763_;
}
else
{
lean_object* v_reuseFailAlloc_2765_; 
v_reuseFailAlloc_2765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2765_, 0, v_a_2759_);
v___x_2764_ = v_reuseFailAlloc_2765_;
goto v_reusejp_2763_;
}
v_reusejp_2763_:
{
return v___x_2764_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4___boxed(lean_object* v_val_2767_, lean_object* v_mvarId_2768_, lean_object* v_a_2769_, lean_object* v_majorFVarId_2770_, lean_object* v_givenNames_2771_, lean_object* v_recursorName_2772_, lean_object* v_x_2773_, lean_object* v_x_2774_, lean_object* v_x_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_, lean_object* v___y_2780_){
_start:
{
lean_object* v_res_2781_; 
v_res_2781_ = l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4(v_val_2767_, v_mvarId_2768_, v_a_2769_, v_majorFVarId_2770_, v_givenNames_2771_, v_recursorName_2772_, v_x_2773_, v_x_2774_, v_x_2775_, v___y_2776_, v___y_2777_, v___y_2778_, v___y_2779_);
lean_dec(v___y_2779_);
lean_dec_ref(v___y_2778_);
lean_dec(v___y_2777_);
lean_dec_ref(v___y_2776_);
lean_dec(v_x_2775_);
return v_res_2781_;
}
}
static lean_object* _init_l_Lean_MVarId_induction___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2783_; lean_object* v___x_2784_; 
v___x_2783_ = ((lean_object*)(l_Lean_MVarId_induction___lam__0___closed__0));
v___x_2784_ = l_Lean_stringToMessageData(v___x_2783_);
return v___x_2784_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_induction___lam__0(lean_object* v___x_2785_, lean_object* v_mvarId_2786_, lean_object* v_majorFVarId_2787_, lean_object* v_recursorName_2788_, lean_object* v_givenNames_2789_, lean_object* v_cls_2790_, lean_object* v___y_2791_, lean_object* v___y_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_){
_start:
{
lean_object* v___y_2797_; lean_object* v___y_2798_; lean_object* v___y_2799_; lean_object* v___y_2800_; lean_object* v_options_2852_; uint8_t v_hasTrace_2853_; 
v_options_2852_ = lean_ctor_get(v___y_2793_, 2);
v_hasTrace_2853_ = lean_ctor_get_uint8(v_options_2852_, sizeof(void*)*1);
if (v_hasTrace_2853_ == 0)
{
lean_dec(v_cls_2790_);
v___y_2797_ = v___y_2791_;
v___y_2798_ = v___y_2792_;
v___y_2799_ = v___y_2793_;
v___y_2800_ = v___y_2794_;
goto v___jp_2796_;
}
else
{
lean_object* v_inheritedTraceOptions_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; uint8_t v___x_2857_; 
v_inheritedTraceOptions_2854_ = lean_ctor_get(v___y_2793_, 13);
v___x_2855_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__4));
lean_inc(v_cls_2790_);
v___x_2856_ = l_Lean_Name_append(v___x_2855_, v_cls_2790_);
v___x_2857_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2854_, v_options_2852_, v___x_2856_);
lean_dec(v___x_2856_);
if (v___x_2857_ == 0)
{
lean_dec(v_cls_2790_);
v___y_2797_ = v___y_2791_;
v___y_2798_ = v___y_2792_;
v___y_2799_ = v___y_2793_;
v___y_2800_ = v___y_2794_;
goto v___jp_2796_;
}
else
{
lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; 
v___x_2858_ = lean_obj_once(&l_Lean_MVarId_induction___lam__0___closed__1, &l_Lean_MVarId_induction___lam__0___closed__1_once, _init_l_Lean_MVarId_induction___lam__0___closed__1);
lean_inc(v_mvarId_2786_);
v___x_2859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2859_, 0, v_mvarId_2786_);
v___x_2860_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2860_, 0, v___x_2858_);
lean_ctor_set(v___x_2860_, 1, v___x_2859_);
v___x_2861_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1(v_cls_2790_, v___x_2860_, v___y_2791_, v___y_2792_, v___y_2793_, v___y_2794_);
if (lean_obj_tag(v___x_2861_) == 0)
{
lean_dec_ref_known(v___x_2861_, 1);
v___y_2797_ = v___y_2791_;
v___y_2798_ = v___y_2792_;
v___y_2799_ = v___y_2793_;
v___y_2800_ = v___y_2794_;
goto v___jp_2796_;
}
else
{
lean_object* v_a_2862_; lean_object* v___x_2864_; uint8_t v_isShared_2865_; uint8_t v_isSharedCheck_2869_; 
lean_dec_ref(v_givenNames_2789_);
lean_dec(v_recursorName_2788_);
lean_dec(v_majorFVarId_2787_);
lean_dec(v_mvarId_2786_);
lean_dec_ref(v___x_2785_);
v_a_2862_ = lean_ctor_get(v___x_2861_, 0);
v_isSharedCheck_2869_ = !lean_is_exclusive(v___x_2861_);
if (v_isSharedCheck_2869_ == 0)
{
v___x_2864_ = v___x_2861_;
v_isShared_2865_ = v_isSharedCheck_2869_;
goto v_resetjp_2863_;
}
else
{
lean_inc(v_a_2862_);
lean_dec(v___x_2861_);
v___x_2864_ = lean_box(0);
v_isShared_2865_ = v_isSharedCheck_2869_;
goto v_resetjp_2863_;
}
v_resetjp_2863_:
{
lean_object* v___x_2867_; 
if (v_isShared_2865_ == 0)
{
v___x_2867_ = v___x_2864_;
goto v_reusejp_2866_;
}
else
{
lean_object* v_reuseFailAlloc_2868_; 
v_reuseFailAlloc_2868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2868_, 0, v_a_2862_);
v___x_2867_ = v_reuseFailAlloc_2868_;
goto v_reusejp_2866_;
}
v_reusejp_2866_:
{
return v___x_2867_;
}
}
}
}
}
v___jp_2796_:
{
lean_object* v___x_2801_; lean_object* v___x_2802_; 
v___x_2801_ = l_Lean_Name_mkStr1(v___x_2785_);
lean_inc(v___x_2801_);
lean_inc(v_mvarId_2786_);
v___x_2802_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_2786_, v___x_2801_, v___y_2797_, v___y_2798_, v___y_2799_, v___y_2800_);
if (lean_obj_tag(v___x_2802_) == 0)
{
lean_object* v___x_2803_; 
lean_dec_ref_known(v___x_2802_, 1);
lean_inc(v_majorFVarId_2787_);
v___x_2803_ = l_Lean_FVarId_getDecl___redArg(v_majorFVarId_2787_, v___y_2797_, v___y_2799_, v___y_2800_);
if (lean_obj_tag(v___x_2803_) == 0)
{
lean_object* v_a_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; 
v_a_2804_ = lean_ctor_get(v___x_2803_, 0);
lean_inc(v_a_2804_);
lean_dec_ref_known(v___x_2803_, 1);
v___x_2805_ = lean_box(0);
lean_inc(v_recursorName_2788_);
v___x_2806_ = l_Lean_Meta_mkRecursorInfo(v_recursorName_2788_, v___x_2805_, v___y_2797_, v___y_2798_, v___y_2799_, v___y_2800_);
if (lean_obj_tag(v___x_2806_) == 0)
{
lean_object* v_a_2807_; lean_object* v_typeName_2808_; lean_object* v___x_2809_; lean_object* v___x_2810_; 
v_a_2807_ = lean_ctor_get(v___x_2806_, 0);
lean_inc(v_a_2807_);
lean_dec_ref_known(v___x_2806_, 1);
v_typeName_2808_ = lean_ctor_get(v_a_2807_, 1);
v___x_2809_ = l_Lean_LocalDecl_type(v_a_2804_);
lean_dec(v_a_2804_);
lean_inc_ref(v___x_2809_);
v___x_2810_ = l_Lean_Meta_whnfUntil(v___x_2809_, v_typeName_2808_, v___y_2797_, v___y_2798_, v___y_2799_, v___y_2800_);
if (lean_obj_tag(v___x_2810_) == 0)
{
lean_object* v_a_2811_; 
v_a_2811_ = lean_ctor_get(v___x_2810_, 0);
lean_inc(v_a_2811_);
lean_dec_ref_known(v___x_2810_, 1);
if (lean_obj_tag(v_a_2811_) == 1)
{
lean_object* v_val_2812_; lean_object* v_dummy_2813_; lean_object* v_nargs_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; 
lean_dec_ref(v___x_2809_);
lean_dec(v___x_2801_);
v_val_2812_ = lean_ctor_get(v_a_2811_, 0);
lean_inc_n(v_val_2812_, 2);
lean_dec_ref_known(v_a_2811_, 1);
v_dummy_2813_ = lean_obj_once(&l_Lean_Meta_getMajorTypeIndices___closed__0, &l_Lean_Meta_getMajorTypeIndices___closed__0_once, _init_l_Lean_Meta_getMajorTypeIndices___closed__0);
v_nargs_2814_ = l_Lean_Expr_getAppNumArgs(v_val_2812_);
lean_inc(v_nargs_2814_);
v___x_2815_ = lean_mk_array(v_nargs_2814_, v_dummy_2813_);
v___x_2816_ = lean_unsigned_to_nat(1u);
v___x_2817_ = lean_nat_sub(v_nargs_2814_, v___x_2816_);
lean_dec(v_nargs_2814_);
v___x_2818_ = l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4(v_val_2812_, v_mvarId_2786_, v_a_2807_, v_majorFVarId_2787_, v_givenNames_2789_, v_recursorName_2788_, v_val_2812_, v___x_2815_, v___x_2817_, v___y_2797_, v___y_2798_, v___y_2799_, v___y_2800_);
lean_dec(v___x_2817_);
return v___x_2818_;
}
else
{
lean_object* v___x_2819_; 
lean_dec(v_a_2811_);
lean_dec(v_a_2807_);
lean_dec_ref(v_givenNames_2789_);
lean_dec(v_recursorName_2788_);
lean_dec(v_majorFVarId_2787_);
v___x_2819_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg(v___x_2801_, v_mvarId_2786_, v___x_2809_, v___y_2797_, v___y_2798_, v___y_2799_, v___y_2800_);
return v___x_2819_;
}
}
else
{
lean_object* v_a_2820_; lean_object* v___x_2822_; uint8_t v_isShared_2823_; uint8_t v_isSharedCheck_2827_; 
lean_dec_ref(v___x_2809_);
lean_dec(v_a_2807_);
lean_dec(v___x_2801_);
lean_dec_ref(v_givenNames_2789_);
lean_dec(v_recursorName_2788_);
lean_dec(v_majorFVarId_2787_);
lean_dec(v_mvarId_2786_);
v_a_2820_ = lean_ctor_get(v___x_2810_, 0);
v_isSharedCheck_2827_ = !lean_is_exclusive(v___x_2810_);
if (v_isSharedCheck_2827_ == 0)
{
v___x_2822_ = v___x_2810_;
v_isShared_2823_ = v_isSharedCheck_2827_;
goto v_resetjp_2821_;
}
else
{
lean_inc(v_a_2820_);
lean_dec(v___x_2810_);
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
lean_dec(v_a_2804_);
lean_dec(v___x_2801_);
lean_dec_ref(v_givenNames_2789_);
lean_dec(v_recursorName_2788_);
lean_dec(v_majorFVarId_2787_);
lean_dec(v_mvarId_2786_);
v_a_2828_ = lean_ctor_get(v___x_2806_, 0);
v_isSharedCheck_2835_ = !lean_is_exclusive(v___x_2806_);
if (v_isSharedCheck_2835_ == 0)
{
v___x_2830_ = v___x_2806_;
v_isShared_2831_ = v_isSharedCheck_2835_;
goto v_resetjp_2829_;
}
else
{
lean_inc(v_a_2828_);
lean_dec(v___x_2806_);
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
else
{
lean_object* v_a_2836_; lean_object* v___x_2838_; uint8_t v_isShared_2839_; uint8_t v_isSharedCheck_2843_; 
lean_dec(v___x_2801_);
lean_dec_ref(v_givenNames_2789_);
lean_dec(v_recursorName_2788_);
lean_dec(v_majorFVarId_2787_);
lean_dec(v_mvarId_2786_);
v_a_2836_ = lean_ctor_get(v___x_2803_, 0);
v_isSharedCheck_2843_ = !lean_is_exclusive(v___x_2803_);
if (v_isSharedCheck_2843_ == 0)
{
v___x_2838_ = v___x_2803_;
v_isShared_2839_ = v_isSharedCheck_2843_;
goto v_resetjp_2837_;
}
else
{
lean_inc(v_a_2836_);
lean_dec(v___x_2803_);
v___x_2838_ = lean_box(0);
v_isShared_2839_ = v_isSharedCheck_2843_;
goto v_resetjp_2837_;
}
v_resetjp_2837_:
{
lean_object* v___x_2841_; 
if (v_isShared_2839_ == 0)
{
v___x_2841_ = v___x_2838_;
goto v_reusejp_2840_;
}
else
{
lean_object* v_reuseFailAlloc_2842_; 
v_reuseFailAlloc_2842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2842_, 0, v_a_2836_);
v___x_2841_ = v_reuseFailAlloc_2842_;
goto v_reusejp_2840_;
}
v_reusejp_2840_:
{
return v___x_2841_;
}
}
}
}
else
{
lean_object* v_a_2844_; lean_object* v___x_2846_; uint8_t v_isShared_2847_; uint8_t v_isSharedCheck_2851_; 
lean_dec(v___x_2801_);
lean_dec_ref(v_givenNames_2789_);
lean_dec(v_recursorName_2788_);
lean_dec(v_majorFVarId_2787_);
lean_dec(v_mvarId_2786_);
v_a_2844_ = lean_ctor_get(v___x_2802_, 0);
v_isSharedCheck_2851_ = !lean_is_exclusive(v___x_2802_);
if (v_isSharedCheck_2851_ == 0)
{
v___x_2846_ = v___x_2802_;
v_isShared_2847_ = v_isSharedCheck_2851_;
goto v_resetjp_2845_;
}
else
{
lean_inc(v_a_2844_);
lean_dec(v___x_2802_);
v___x_2846_ = lean_box(0);
v_isShared_2847_ = v_isSharedCheck_2851_;
goto v_resetjp_2845_;
}
v_resetjp_2845_:
{
lean_object* v___x_2849_; 
if (v_isShared_2847_ == 0)
{
v___x_2849_ = v___x_2846_;
goto v_reusejp_2848_;
}
else
{
lean_object* v_reuseFailAlloc_2850_; 
v_reuseFailAlloc_2850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2850_, 0, v_a_2844_);
v___x_2849_ = v_reuseFailAlloc_2850_;
goto v_reusejp_2848_;
}
v_reusejp_2848_:
{
return v___x_2849_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_induction___lam__0___boxed(lean_object* v___x_2870_, lean_object* v_mvarId_2871_, lean_object* v_majorFVarId_2872_, lean_object* v_recursorName_2873_, lean_object* v_givenNames_2874_, lean_object* v_cls_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_){
_start:
{
lean_object* v_res_2881_; 
v_res_2881_ = l_Lean_MVarId_induction___lam__0(v___x_2870_, v_mvarId_2871_, v_majorFVarId_2872_, v_recursorName_2873_, v_givenNames_2874_, v_cls_2875_, v___y_2876_, v___y_2877_, v___y_2878_, v___y_2879_);
lean_dec(v___y_2879_);
lean_dec_ref(v___y_2878_);
lean_dec(v___y_2877_);
lean_dec_ref(v___y_2876_);
return v_res_2881_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_induction(lean_object* v_mvarId_2882_, lean_object* v_majorFVarId_2883_, lean_object* v_recursorName_2884_, lean_object* v_givenNames_2885_, lean_object* v_a_2886_, lean_object* v_a_2887_, lean_object* v_a_2888_, lean_object* v_a_2889_){
_start:
{
lean_object* v___x_2891_; lean_object* v_cls_2892_; lean_object* v___f_2893_; lean_object* v___x_2894_; 
v___x_2891_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__0));
v_cls_2892_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__2));
lean_inc(v_mvarId_2882_);
v___f_2893_ = lean_alloc_closure((void*)(l_Lean_MVarId_induction___lam__0___boxed), 11, 6);
lean_closure_set(v___f_2893_, 0, v___x_2891_);
lean_closure_set(v___f_2893_, 1, v_mvarId_2882_);
lean_closure_set(v___f_2893_, 2, v_majorFVarId_2883_);
lean_closure_set(v___f_2893_, 3, v_recursorName_2884_);
lean_closure_set(v___f_2893_, 4, v_givenNames_2885_);
lean_closure_set(v___f_2893_, 5, v_cls_2892_);
v___x_2894_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___redArg(v_mvarId_2882_, v___f_2893_, v_a_2886_, v_a_2887_, v_a_2888_, v_a_2889_);
return v___x_2894_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_induction___boxed(lean_object* v_mvarId_2895_, lean_object* v_majorFVarId_2896_, lean_object* v_recursorName_2897_, lean_object* v_givenNames_2898_, lean_object* v_a_2899_, lean_object* v_a_2900_, lean_object* v_a_2901_, lean_object* v_a_2902_, lean_object* v_a_2903_){
_start:
{
lean_object* v_res_2904_; 
v_res_2904_ = l_Lean_MVarId_induction(v_mvarId_2895_, v_majorFVarId_2896_, v_recursorName_2897_, v_givenNames_2898_, v_a_2899_, v_a_2900_, v_a_2901_, v_a_2902_);
lean_dec(v_a_2902_);
lean_dec_ref(v_a_2901_);
lean_dec(v_a_2900_);
lean_dec_ref(v_a_2899_);
return v_res_2904_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; 
v___x_2952_ = lean_unsigned_to_nat(2221195325u);
v___x_2953_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_));
v___x_2954_ = l_Lean_Name_num___override(v___x_2953_, v___x_2952_);
return v___x_2954_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; 
v___x_2956_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_));
v___x_2957_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_);
v___x_2958_ = l_Lean_Name_str___override(v___x_2957_, v___x_2956_);
return v___x_2958_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; 
v___x_2960_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_));
v___x_2961_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_);
v___x_2962_ = l_Lean_Name_str___override(v___x_2961_, v___x_2960_);
return v___x_2962_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; 
v___x_2963_ = lean_unsigned_to_nat(2u);
v___x_2964_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_);
v___x_2965_ = l_Lean_Name_num___override(v___x_2964_, v___x_2963_);
return v___x_2965_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2967_; uint8_t v___x_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; 
v___x_2967_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__2));
v___x_2968_ = 0;
v___x_2969_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_);
v___x_2970_ = l_Lean_registerTraceClass(v___x_2967_, v___x_2968_, v___x_2969_);
return v___x_2970_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2____boxed(lean_object* v_a_2971_){
_start:
{
lean_object* v_res_2972_; 
v_res_2972_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_();
return v_res_2972_;
}
}
lean_object* runtime_initialize_Lean_Meta_RecursorInfo(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_SynthInstance(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Revert(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Intro(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_FVarSubst(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_WHNF(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Induction(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
