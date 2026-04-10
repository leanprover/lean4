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
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
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
lean_object* lean_st_ref_set(lean_object*, lean_object*);
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
lean_object* lean_erase_macro_scopes(lean_object*);
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
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2___redArg___closed__2;
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
lean_dec_ref(v_x_1_);
v_x_1_ = v_expr_2_;
goto _start;
}
case 7:
{
lean_object* v_body_4_; lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; 
v_body_4_ = lean_ctor_get(v_x_1_, 2);
lean_inc_ref(v_body_4_);
lean_dec_ref(v_x_1_);
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
lean_dec_ref(v_x_32_);
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
lean_dec_ref(v___x_47_);
v___x_49_ = l_Lean_Meta_whnfForall(v_a_48_, v_a_34_, v_a_35_, v_a_36_, v_a_37_);
if (lean_obj_tag(v___x_49_) == 0)
{
lean_object* v_a_50_; 
v_a_50_ = lean_ctor_get(v___x_49_, 0);
lean_inc(v_a_50_);
lean_dec_ref(v___x_49_);
if (lean_obj_tag(v_a_50_) == 7)
{
lean_object* v_binderType_51_; lean_object* v___x_52_; 
v_binderType_51_ = lean_ctor_get(v_a_50_, 1);
lean_inc_ref(v_binderType_51_);
lean_dec_ref(v_a_50_);
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
lean_dec_ref(v___x_52_);
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
lean_dec_ref(v_head_40_);
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
lean_dec_ref(v___y_43_);
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
lean_dec_ref(v_a_100_);
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
lean_object* v___f_134_; lean_object* v___x_8861__overap_135_; lean_object* v___x_136_; 
v___f_134_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__4___closed__0));
v___x_8861__overap_135_ = lean_panic_fn_borrowed(v___f_134_, v_msg_128_);
lean_inc(v___y_132_);
lean_inc_ref(v___y_131_);
lean_inc(v___y_130_);
lean_inc_ref(v___y_129_);
v___x_136_ = lean_apply_5(v___x_8861__overap_135_, v___y_129_, v___y_130_, v___y_131_, v___y_132_, lean_box(0));
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
lean_dec_ref(v___x_190_);
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
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2___redArg___closed__0(void){
_start:
{
size_t v___x_257_; size_t v___x_258_; size_t v___x_259_; 
v___x_257_ = ((size_t)5ULL);
v___x_258_ = ((size_t)1ULL);
v___x_259_ = lean_usize_shift_left(v___x_258_, v___x_257_);
return v___x_259_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2___redArg___closed__1(void){
_start:
{
size_t v___x_260_; size_t v___x_261_; size_t v___x_262_; 
v___x_260_ = ((size_t)1ULL);
v___x_261_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2___redArg___closed__0);
v___x_262_ = lean_usize_sub(v___x_261_, v___x_260_);
return v___x_262_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_263_; 
v___x_263_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_263_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2___redArg(lean_object* v_x_264_, size_t v_x_265_, size_t v_x_266_, lean_object* v_x_267_, lean_object* v_x_268_){
_start:
{
if (lean_obj_tag(v_x_264_) == 0)
{
lean_object* v_es_269_; size_t v___x_270_; size_t v___x_271_; size_t v___x_272_; size_t v___x_273_; lean_object* v_j_274_; lean_object* v___x_275_; uint8_t v___x_276_; 
v_es_269_ = lean_ctor_get(v_x_264_, 0);
v___x_270_ = ((size_t)5ULL);
v___x_271_ = ((size_t)1ULL);
v___x_272_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2___redArg___closed__1);
v___x_273_ = lean_usize_land(v_x_265_, v___x_272_);
v_j_274_ = lean_usize_to_nat(v___x_273_);
v___x_275_ = lean_array_get_size(v_es_269_);
v___x_276_ = lean_nat_dec_lt(v_j_274_, v___x_275_);
if (v___x_276_ == 0)
{
lean_dec(v_j_274_);
lean_dec(v_x_268_);
lean_dec(v_x_267_);
return v_x_264_;
}
else
{
lean_object* v___x_278_; uint8_t v_isShared_279_; uint8_t v_isSharedCheck_313_; 
lean_inc_ref(v_es_269_);
v_isSharedCheck_313_ = !lean_is_exclusive(v_x_264_);
if (v_isSharedCheck_313_ == 0)
{
lean_object* v_unused_314_; 
v_unused_314_ = lean_ctor_get(v_x_264_, 0);
lean_dec(v_unused_314_);
v___x_278_ = v_x_264_;
v_isShared_279_ = v_isSharedCheck_313_;
goto v_resetjp_277_;
}
else
{
lean_dec(v_x_264_);
v___x_278_ = lean_box(0);
v_isShared_279_ = v_isSharedCheck_313_;
goto v_resetjp_277_;
}
v_resetjp_277_:
{
lean_object* v_v_280_; lean_object* v___x_281_; lean_object* v_xs_x27_282_; lean_object* v___y_284_; 
v_v_280_ = lean_array_fget(v_es_269_, v_j_274_);
v___x_281_ = lean_box(0);
v_xs_x27_282_ = lean_array_fset(v_es_269_, v_j_274_, v___x_281_);
switch(lean_obj_tag(v_v_280_))
{
case 0:
{
lean_object* v_key_289_; lean_object* v_val_290_; lean_object* v___x_292_; uint8_t v_isShared_293_; uint8_t v_isSharedCheck_300_; 
v_key_289_ = lean_ctor_get(v_v_280_, 0);
v_val_290_ = lean_ctor_get(v_v_280_, 1);
v_isSharedCheck_300_ = !lean_is_exclusive(v_v_280_);
if (v_isSharedCheck_300_ == 0)
{
v___x_292_ = v_v_280_;
v_isShared_293_ = v_isSharedCheck_300_;
goto v_resetjp_291_;
}
else
{
lean_inc(v_val_290_);
lean_inc(v_key_289_);
lean_dec(v_v_280_);
v___x_292_ = lean_box(0);
v_isShared_293_ = v_isSharedCheck_300_;
goto v_resetjp_291_;
}
v_resetjp_291_:
{
uint8_t v___x_294_; 
v___x_294_ = l_Lean_instBEqMVarId_beq(v_x_267_, v_key_289_);
if (v___x_294_ == 0)
{
lean_object* v___x_295_; lean_object* v___x_296_; 
lean_del_object(v___x_292_);
v___x_295_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_289_, v_val_290_, v_x_267_, v_x_268_);
v___x_296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_296_, 0, v___x_295_);
v___y_284_ = v___x_296_;
goto v___jp_283_;
}
else
{
lean_object* v___x_298_; 
lean_dec(v_val_290_);
lean_dec(v_key_289_);
if (v_isShared_293_ == 0)
{
lean_ctor_set(v___x_292_, 1, v_x_268_);
lean_ctor_set(v___x_292_, 0, v_x_267_);
v___x_298_ = v___x_292_;
goto v_reusejp_297_;
}
else
{
lean_object* v_reuseFailAlloc_299_; 
v_reuseFailAlloc_299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_299_, 0, v_x_267_);
lean_ctor_set(v_reuseFailAlloc_299_, 1, v_x_268_);
v___x_298_ = v_reuseFailAlloc_299_;
goto v_reusejp_297_;
}
v_reusejp_297_:
{
v___y_284_ = v___x_298_;
goto v___jp_283_;
}
}
}
}
case 1:
{
lean_object* v_node_301_; lean_object* v___x_303_; uint8_t v_isShared_304_; uint8_t v_isSharedCheck_311_; 
v_node_301_ = lean_ctor_get(v_v_280_, 0);
v_isSharedCheck_311_ = !lean_is_exclusive(v_v_280_);
if (v_isSharedCheck_311_ == 0)
{
v___x_303_ = v_v_280_;
v_isShared_304_ = v_isSharedCheck_311_;
goto v_resetjp_302_;
}
else
{
lean_inc(v_node_301_);
lean_dec(v_v_280_);
v___x_303_ = lean_box(0);
v_isShared_304_ = v_isSharedCheck_311_;
goto v_resetjp_302_;
}
v_resetjp_302_:
{
size_t v___x_305_; size_t v___x_306_; lean_object* v___x_307_; lean_object* v___x_309_; 
v___x_305_ = lean_usize_shift_right(v_x_265_, v___x_270_);
v___x_306_ = lean_usize_add(v_x_266_, v___x_271_);
v___x_307_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2___redArg(v_node_301_, v___x_305_, v___x_306_, v_x_267_, v_x_268_);
if (v_isShared_304_ == 0)
{
lean_ctor_set(v___x_303_, 0, v___x_307_);
v___x_309_ = v___x_303_;
goto v_reusejp_308_;
}
else
{
lean_object* v_reuseFailAlloc_310_; 
v_reuseFailAlloc_310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_310_, 0, v___x_307_);
v___x_309_ = v_reuseFailAlloc_310_;
goto v_reusejp_308_;
}
v_reusejp_308_:
{
v___y_284_ = v___x_309_;
goto v___jp_283_;
}
}
}
default: 
{
lean_object* v___x_312_; 
v___x_312_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_312_, 0, v_x_267_);
lean_ctor_set(v___x_312_, 1, v_x_268_);
v___y_284_ = v___x_312_;
goto v___jp_283_;
}
}
v___jp_283_:
{
lean_object* v___x_285_; lean_object* v___x_287_; 
v___x_285_ = lean_array_fset(v_xs_x27_282_, v_j_274_, v___y_284_);
lean_dec(v_j_274_);
if (v_isShared_279_ == 0)
{
lean_ctor_set(v___x_278_, 0, v___x_285_);
v___x_287_ = v___x_278_;
goto v_reusejp_286_;
}
else
{
lean_object* v_reuseFailAlloc_288_; 
v_reuseFailAlloc_288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_288_, 0, v___x_285_);
v___x_287_ = v_reuseFailAlloc_288_;
goto v_reusejp_286_;
}
v_reusejp_286_:
{
return v___x_287_;
}
}
}
}
}
else
{
lean_object* v_ks_315_; lean_object* v_vs_316_; lean_object* v___x_318_; uint8_t v_isShared_319_; uint8_t v_isSharedCheck_336_; 
v_ks_315_ = lean_ctor_get(v_x_264_, 0);
v_vs_316_ = lean_ctor_get(v_x_264_, 1);
v_isSharedCheck_336_ = !lean_is_exclusive(v_x_264_);
if (v_isSharedCheck_336_ == 0)
{
v___x_318_ = v_x_264_;
v_isShared_319_ = v_isSharedCheck_336_;
goto v_resetjp_317_;
}
else
{
lean_inc(v_vs_316_);
lean_inc(v_ks_315_);
lean_dec(v_x_264_);
v___x_318_ = lean_box(0);
v_isShared_319_ = v_isSharedCheck_336_;
goto v_resetjp_317_;
}
v_resetjp_317_:
{
lean_object* v___x_321_; 
if (v_isShared_319_ == 0)
{
v___x_321_ = v___x_318_;
goto v_reusejp_320_;
}
else
{
lean_object* v_reuseFailAlloc_335_; 
v_reuseFailAlloc_335_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_335_, 0, v_ks_315_);
lean_ctor_set(v_reuseFailAlloc_335_, 1, v_vs_316_);
v___x_321_ = v_reuseFailAlloc_335_;
goto v_reusejp_320_;
}
v_reusejp_320_:
{
lean_object* v_newNode_322_; uint8_t v___y_324_; size_t v___x_330_; uint8_t v___x_331_; 
v_newNode_322_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__8___redArg(v___x_321_, v_x_267_, v_x_268_);
v___x_330_ = ((size_t)7ULL);
v___x_331_ = lean_usize_dec_le(v___x_330_, v_x_266_);
if (v___x_331_ == 0)
{
lean_object* v___x_332_; lean_object* v___x_333_; uint8_t v___x_334_; 
v___x_332_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_322_);
v___x_333_ = lean_unsigned_to_nat(4u);
v___x_334_ = lean_nat_dec_lt(v___x_332_, v___x_333_);
lean_dec(v___x_332_);
v___y_324_ = v___x_334_;
goto v___jp_323_;
}
else
{
v___y_324_ = v___x_331_;
goto v___jp_323_;
}
v___jp_323_:
{
if (v___y_324_ == 0)
{
lean_object* v_ks_325_; lean_object* v_vs_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; 
v_ks_325_ = lean_ctor_get(v_newNode_322_, 0);
lean_inc_ref(v_ks_325_);
v_vs_326_ = lean_ctor_get(v_newNode_322_, 1);
lean_inc_ref(v_vs_326_);
lean_dec_ref(v_newNode_322_);
v___x_327_ = lean_unsigned_to_nat(0u);
v___x_328_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2___redArg___closed__2);
v___x_329_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__9___redArg(v_x_266_, v_ks_325_, v_vs_326_, v___x_327_, v___x_328_);
lean_dec_ref(v_vs_326_);
lean_dec_ref(v_ks_325_);
return v___x_329_;
}
else
{
return v_newNode_322_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__9___redArg(size_t v_depth_337_, lean_object* v_keys_338_, lean_object* v_vals_339_, lean_object* v_i_340_, lean_object* v_entries_341_){
_start:
{
lean_object* v___x_342_; uint8_t v___x_343_; 
v___x_342_ = lean_array_get_size(v_keys_338_);
v___x_343_ = lean_nat_dec_lt(v_i_340_, v___x_342_);
if (v___x_343_ == 0)
{
lean_dec(v_i_340_);
return v_entries_341_;
}
else
{
lean_object* v_k_344_; lean_object* v_v_345_; uint64_t v___x_346_; size_t v_h_347_; size_t v___x_348_; lean_object* v___x_349_; size_t v___x_350_; size_t v___x_351_; size_t v___x_352_; size_t v_h_353_; lean_object* v___x_354_; lean_object* v___x_355_; 
v_k_344_ = lean_array_fget_borrowed(v_keys_338_, v_i_340_);
v_v_345_ = lean_array_fget_borrowed(v_vals_339_, v_i_340_);
v___x_346_ = l_Lean_instHashableMVarId_hash(v_k_344_);
v_h_347_ = lean_uint64_to_usize(v___x_346_);
v___x_348_ = ((size_t)5ULL);
v___x_349_ = lean_unsigned_to_nat(1u);
v___x_350_ = ((size_t)1ULL);
v___x_351_ = lean_usize_sub(v_depth_337_, v___x_350_);
v___x_352_ = lean_usize_mul(v___x_348_, v___x_351_);
v_h_353_ = lean_usize_shift_right(v_h_347_, v___x_352_);
v___x_354_ = lean_nat_add(v_i_340_, v___x_349_);
lean_dec(v_i_340_);
lean_inc(v_v_345_);
lean_inc(v_k_344_);
v___x_355_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2___redArg(v_entries_341_, v_h_353_, v_depth_337_, v_k_344_, v_v_345_);
v_i_340_ = v___x_354_;
v_entries_341_ = v___x_355_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__9___redArg___boxed(lean_object* v_depth_357_, lean_object* v_keys_358_, lean_object* v_vals_359_, lean_object* v_i_360_, lean_object* v_entries_361_){
_start:
{
size_t v_depth_boxed_362_; lean_object* v_res_363_; 
v_depth_boxed_362_ = lean_unbox_usize(v_depth_357_);
lean_dec(v_depth_357_);
v_res_363_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__9___redArg(v_depth_boxed_362_, v_keys_358_, v_vals_359_, v_i_360_, v_entries_361_);
lean_dec_ref(v_vals_359_);
lean_dec_ref(v_keys_358_);
return v_res_363_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_x_364_, lean_object* v_x_365_, lean_object* v_x_366_, lean_object* v_x_367_, lean_object* v_x_368_){
_start:
{
size_t v_x_10132__boxed_369_; size_t v_x_10133__boxed_370_; lean_object* v_res_371_; 
v_x_10132__boxed_369_ = lean_unbox_usize(v_x_365_);
lean_dec(v_x_365_);
v_x_10133__boxed_370_ = lean_unbox_usize(v_x_366_);
lean_dec(v_x_366_);
v_res_371_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2___redArg(v_x_364_, v_x_10132__boxed_369_, v_x_10133__boxed_370_, v_x_367_, v_x_368_);
return v_res_371_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0___redArg(lean_object* v_x_372_, lean_object* v_x_373_, lean_object* v_x_374_){
_start:
{
uint64_t v___x_375_; size_t v___x_376_; size_t v___x_377_; lean_object* v___x_378_; 
v___x_375_ = l_Lean_instHashableMVarId_hash(v_x_373_);
v___x_376_ = lean_uint64_to_usize(v___x_375_);
v___x_377_ = ((size_t)1ULL);
v___x_378_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2___redArg(v_x_372_, v___x_376_, v___x_377_, v_x_373_, v_x_374_);
return v___x_378_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0___redArg(lean_object* v_mvarId_379_, lean_object* v_val_380_, lean_object* v___y_381_){
_start:
{
lean_object* v___x_383_; lean_object* v_mctx_384_; lean_object* v_cache_385_; lean_object* v_zetaDeltaFVarIds_386_; lean_object* v_postponed_387_; lean_object* v_diag_388_; lean_object* v___x_390_; uint8_t v_isShared_391_; uint8_t v_isSharedCheck_416_; 
v___x_383_ = lean_st_ref_take(v___y_381_);
v_mctx_384_ = lean_ctor_get(v___x_383_, 0);
v_cache_385_ = lean_ctor_get(v___x_383_, 1);
v_zetaDeltaFVarIds_386_ = lean_ctor_get(v___x_383_, 2);
v_postponed_387_ = lean_ctor_get(v___x_383_, 3);
v_diag_388_ = lean_ctor_get(v___x_383_, 4);
v_isSharedCheck_416_ = !lean_is_exclusive(v___x_383_);
if (v_isSharedCheck_416_ == 0)
{
v___x_390_ = v___x_383_;
v_isShared_391_ = v_isSharedCheck_416_;
goto v_resetjp_389_;
}
else
{
lean_inc(v_diag_388_);
lean_inc(v_postponed_387_);
lean_inc(v_zetaDeltaFVarIds_386_);
lean_inc(v_cache_385_);
lean_inc(v_mctx_384_);
lean_dec(v___x_383_);
v___x_390_ = lean_box(0);
v_isShared_391_ = v_isSharedCheck_416_;
goto v_resetjp_389_;
}
v_resetjp_389_:
{
lean_object* v_depth_392_; lean_object* v_levelAssignDepth_393_; lean_object* v_lmvarCounter_394_; lean_object* v_mvarCounter_395_; lean_object* v_lDecls_396_; lean_object* v_decls_397_; lean_object* v_userNames_398_; lean_object* v_lAssignment_399_; lean_object* v_eAssignment_400_; lean_object* v_dAssignment_401_; lean_object* v___x_403_; uint8_t v_isShared_404_; uint8_t v_isSharedCheck_415_; 
v_depth_392_ = lean_ctor_get(v_mctx_384_, 0);
v_levelAssignDepth_393_ = lean_ctor_get(v_mctx_384_, 1);
v_lmvarCounter_394_ = lean_ctor_get(v_mctx_384_, 2);
v_mvarCounter_395_ = lean_ctor_get(v_mctx_384_, 3);
v_lDecls_396_ = lean_ctor_get(v_mctx_384_, 4);
v_decls_397_ = lean_ctor_get(v_mctx_384_, 5);
v_userNames_398_ = lean_ctor_get(v_mctx_384_, 6);
v_lAssignment_399_ = lean_ctor_get(v_mctx_384_, 7);
v_eAssignment_400_ = lean_ctor_get(v_mctx_384_, 8);
v_dAssignment_401_ = lean_ctor_get(v_mctx_384_, 9);
v_isSharedCheck_415_ = !lean_is_exclusive(v_mctx_384_);
if (v_isSharedCheck_415_ == 0)
{
v___x_403_ = v_mctx_384_;
v_isShared_404_ = v_isSharedCheck_415_;
goto v_resetjp_402_;
}
else
{
lean_inc(v_dAssignment_401_);
lean_inc(v_eAssignment_400_);
lean_inc(v_lAssignment_399_);
lean_inc(v_userNames_398_);
lean_inc(v_decls_397_);
lean_inc(v_lDecls_396_);
lean_inc(v_mvarCounter_395_);
lean_inc(v_lmvarCounter_394_);
lean_inc(v_levelAssignDepth_393_);
lean_inc(v_depth_392_);
lean_dec(v_mctx_384_);
v___x_403_ = lean_box(0);
v_isShared_404_ = v_isSharedCheck_415_;
goto v_resetjp_402_;
}
v_resetjp_402_:
{
lean_object* v___x_405_; lean_object* v___x_407_; 
v___x_405_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0___redArg(v_eAssignment_400_, v_mvarId_379_, v_val_380_);
if (v_isShared_404_ == 0)
{
lean_ctor_set(v___x_403_, 8, v___x_405_);
v___x_407_ = v___x_403_;
goto v_reusejp_406_;
}
else
{
lean_object* v_reuseFailAlloc_414_; 
v_reuseFailAlloc_414_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_414_, 0, v_depth_392_);
lean_ctor_set(v_reuseFailAlloc_414_, 1, v_levelAssignDepth_393_);
lean_ctor_set(v_reuseFailAlloc_414_, 2, v_lmvarCounter_394_);
lean_ctor_set(v_reuseFailAlloc_414_, 3, v_mvarCounter_395_);
lean_ctor_set(v_reuseFailAlloc_414_, 4, v_lDecls_396_);
lean_ctor_set(v_reuseFailAlloc_414_, 5, v_decls_397_);
lean_ctor_set(v_reuseFailAlloc_414_, 6, v_userNames_398_);
lean_ctor_set(v_reuseFailAlloc_414_, 7, v_lAssignment_399_);
lean_ctor_set(v_reuseFailAlloc_414_, 8, v___x_405_);
lean_ctor_set(v_reuseFailAlloc_414_, 9, v_dAssignment_401_);
v___x_407_ = v_reuseFailAlloc_414_;
goto v_reusejp_406_;
}
v_reusejp_406_:
{
lean_object* v___x_409_; 
if (v_isShared_391_ == 0)
{
lean_ctor_set(v___x_390_, 0, v___x_407_);
v___x_409_ = v___x_390_;
goto v_reusejp_408_;
}
else
{
lean_object* v_reuseFailAlloc_413_; 
v_reuseFailAlloc_413_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_413_, 0, v___x_407_);
lean_ctor_set(v_reuseFailAlloc_413_, 1, v_cache_385_);
lean_ctor_set(v_reuseFailAlloc_413_, 2, v_zetaDeltaFVarIds_386_);
lean_ctor_set(v_reuseFailAlloc_413_, 3, v_postponed_387_);
lean_ctor_set(v_reuseFailAlloc_413_, 4, v_diag_388_);
v___x_409_ = v_reuseFailAlloc_413_;
goto v_reusejp_408_;
}
v_reusejp_408_:
{
lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; 
v___x_410_ = lean_st_ref_set(v___y_381_, v___x_409_);
v___x_411_ = lean_box(0);
v___x_412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_412_, 0, v___x_411_);
return v___x_412_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0___redArg___boxed(lean_object* v_mvarId_417_, lean_object* v_val_418_, lean_object* v___y_419_, lean_object* v___y_420_){
_start:
{
lean_object* v_res_421_; 
v_res_421_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0___redArg(v_mvarId_417_, v_val_418_, v___y_419_);
lean_dec(v___y_419_);
return v_res_421_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1_spec__2(lean_object* v_msgData_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_){
_start:
{
lean_object* v___x_428_; lean_object* v_env_429_; lean_object* v___x_430_; lean_object* v_mctx_431_; lean_object* v_lctx_432_; lean_object* v_options_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; 
v___x_428_ = lean_st_ref_get(v___y_426_);
v_env_429_ = lean_ctor_get(v___x_428_, 0);
lean_inc_ref(v_env_429_);
lean_dec(v___x_428_);
v___x_430_ = lean_st_ref_get(v___y_424_);
v_mctx_431_ = lean_ctor_get(v___x_430_, 0);
lean_inc_ref(v_mctx_431_);
lean_dec(v___x_430_);
v_lctx_432_ = lean_ctor_get(v___y_423_, 2);
v_options_433_ = lean_ctor_get(v___y_425_, 2);
lean_inc_ref(v_options_433_);
lean_inc_ref(v_lctx_432_);
v___x_434_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_434_, 0, v_env_429_);
lean_ctor_set(v___x_434_, 1, v_mctx_431_);
lean_ctor_set(v___x_434_, 2, v_lctx_432_);
lean_ctor_set(v___x_434_, 3, v_options_433_);
v___x_435_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_435_, 0, v___x_434_);
lean_ctor_set(v___x_435_, 1, v_msgData_422_);
v___x_436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_436_, 0, v___x_435_);
return v___x_436_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1_spec__2___boxed(lean_object* v_msgData_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_){
_start:
{
lean_object* v_res_443_; 
v_res_443_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1_spec__2(v_msgData_437_, v___y_438_, v___y_439_, v___y_440_, v___y_441_);
lean_dec(v___y_441_);
lean_dec_ref(v___y_440_);
lean_dec(v___y_439_);
lean_dec_ref(v___y_438_);
return v_res_443_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1___closed__0(void){
_start:
{
lean_object* v___x_444_; double v___x_445_; 
v___x_444_ = lean_unsigned_to_nat(0u);
v___x_445_ = lean_float_of_nat(v___x_444_);
return v___x_445_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1(lean_object* v_cls_449_, lean_object* v_msg_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_){
_start:
{
lean_object* v_ref_456_; lean_object* v___x_457_; lean_object* v_a_458_; lean_object* v___x_460_; uint8_t v_isShared_461_; uint8_t v_isSharedCheck_502_; 
v_ref_456_ = lean_ctor_get(v___y_453_, 5);
v___x_457_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1_spec__2(v_msg_450_, v___y_451_, v___y_452_, v___y_453_, v___y_454_);
v_a_458_ = lean_ctor_get(v___x_457_, 0);
v_isSharedCheck_502_ = !lean_is_exclusive(v___x_457_);
if (v_isSharedCheck_502_ == 0)
{
v___x_460_ = v___x_457_;
v_isShared_461_ = v_isSharedCheck_502_;
goto v_resetjp_459_;
}
else
{
lean_inc(v_a_458_);
lean_dec(v___x_457_);
v___x_460_ = lean_box(0);
v_isShared_461_ = v_isSharedCheck_502_;
goto v_resetjp_459_;
}
v_resetjp_459_:
{
lean_object* v___x_462_; lean_object* v_traceState_463_; lean_object* v_env_464_; lean_object* v_nextMacroScope_465_; lean_object* v_ngen_466_; lean_object* v_auxDeclNGen_467_; lean_object* v_cache_468_; lean_object* v_messages_469_; lean_object* v_infoState_470_; lean_object* v_snapshotTasks_471_; lean_object* v___x_473_; uint8_t v_isShared_474_; uint8_t v_isSharedCheck_501_; 
v___x_462_ = lean_st_ref_take(v___y_454_);
v_traceState_463_ = lean_ctor_get(v___x_462_, 4);
v_env_464_ = lean_ctor_get(v___x_462_, 0);
v_nextMacroScope_465_ = lean_ctor_get(v___x_462_, 1);
v_ngen_466_ = lean_ctor_get(v___x_462_, 2);
v_auxDeclNGen_467_ = lean_ctor_get(v___x_462_, 3);
v_cache_468_ = lean_ctor_get(v___x_462_, 5);
v_messages_469_ = lean_ctor_get(v___x_462_, 6);
v_infoState_470_ = lean_ctor_get(v___x_462_, 7);
v_snapshotTasks_471_ = lean_ctor_get(v___x_462_, 8);
v_isSharedCheck_501_ = !lean_is_exclusive(v___x_462_);
if (v_isSharedCheck_501_ == 0)
{
v___x_473_ = v___x_462_;
v_isShared_474_ = v_isSharedCheck_501_;
goto v_resetjp_472_;
}
else
{
lean_inc(v_snapshotTasks_471_);
lean_inc(v_infoState_470_);
lean_inc(v_messages_469_);
lean_inc(v_cache_468_);
lean_inc(v_traceState_463_);
lean_inc(v_auxDeclNGen_467_);
lean_inc(v_ngen_466_);
lean_inc(v_nextMacroScope_465_);
lean_inc(v_env_464_);
lean_dec(v___x_462_);
v___x_473_ = lean_box(0);
v_isShared_474_ = v_isSharedCheck_501_;
goto v_resetjp_472_;
}
v_resetjp_472_:
{
uint64_t v_tid_475_; lean_object* v_traces_476_; lean_object* v___x_478_; uint8_t v_isShared_479_; uint8_t v_isSharedCheck_500_; 
v_tid_475_ = lean_ctor_get_uint64(v_traceState_463_, sizeof(void*)*1);
v_traces_476_ = lean_ctor_get(v_traceState_463_, 0);
v_isSharedCheck_500_ = !lean_is_exclusive(v_traceState_463_);
if (v_isSharedCheck_500_ == 0)
{
v___x_478_ = v_traceState_463_;
v_isShared_479_ = v_isSharedCheck_500_;
goto v_resetjp_477_;
}
else
{
lean_inc(v_traces_476_);
lean_dec(v_traceState_463_);
v___x_478_ = lean_box(0);
v_isShared_479_ = v_isSharedCheck_500_;
goto v_resetjp_477_;
}
v_resetjp_477_:
{
lean_object* v___x_480_; double v___x_481_; uint8_t v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_490_; 
v___x_480_ = lean_box(0);
v___x_481_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1___closed__0);
v___x_482_ = 0;
v___x_483_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1___closed__1));
v___x_484_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_484_, 0, v_cls_449_);
lean_ctor_set(v___x_484_, 1, v___x_480_);
lean_ctor_set(v___x_484_, 2, v___x_483_);
lean_ctor_set_float(v___x_484_, sizeof(void*)*3, v___x_481_);
lean_ctor_set_float(v___x_484_, sizeof(void*)*3 + 8, v___x_481_);
lean_ctor_set_uint8(v___x_484_, sizeof(void*)*3 + 16, v___x_482_);
v___x_485_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1___closed__2));
v___x_486_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_486_, 0, v___x_484_);
lean_ctor_set(v___x_486_, 1, v_a_458_);
lean_ctor_set(v___x_486_, 2, v___x_485_);
lean_inc(v_ref_456_);
v___x_487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_487_, 0, v_ref_456_);
lean_ctor_set(v___x_487_, 1, v___x_486_);
v___x_488_ = l_Lean_PersistentArray_push___redArg(v_traces_476_, v___x_487_);
if (v_isShared_479_ == 0)
{
lean_ctor_set(v___x_478_, 0, v___x_488_);
v___x_490_ = v___x_478_;
goto v_reusejp_489_;
}
else
{
lean_object* v_reuseFailAlloc_499_; 
v_reuseFailAlloc_499_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_499_, 0, v___x_488_);
lean_ctor_set_uint64(v_reuseFailAlloc_499_, sizeof(void*)*1, v_tid_475_);
v___x_490_ = v_reuseFailAlloc_499_;
goto v_reusejp_489_;
}
v_reusejp_489_:
{
lean_object* v___x_492_; 
if (v_isShared_474_ == 0)
{
lean_ctor_set(v___x_473_, 4, v___x_490_);
v___x_492_ = v___x_473_;
goto v_reusejp_491_;
}
else
{
lean_object* v_reuseFailAlloc_498_; 
v_reuseFailAlloc_498_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_498_, 0, v_env_464_);
lean_ctor_set(v_reuseFailAlloc_498_, 1, v_nextMacroScope_465_);
lean_ctor_set(v_reuseFailAlloc_498_, 2, v_ngen_466_);
lean_ctor_set(v_reuseFailAlloc_498_, 3, v_auxDeclNGen_467_);
lean_ctor_set(v_reuseFailAlloc_498_, 4, v___x_490_);
lean_ctor_set(v_reuseFailAlloc_498_, 5, v_cache_468_);
lean_ctor_set(v_reuseFailAlloc_498_, 6, v_messages_469_);
lean_ctor_set(v_reuseFailAlloc_498_, 7, v_infoState_470_);
lean_ctor_set(v_reuseFailAlloc_498_, 8, v_snapshotTasks_471_);
v___x_492_ = v_reuseFailAlloc_498_;
goto v_reusejp_491_;
}
v_reusejp_491_:
{
lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_496_; 
v___x_493_ = lean_st_ref_set(v___y_454_, v___x_492_);
v___x_494_ = lean_box(0);
if (v_isShared_461_ == 0)
{
lean_ctor_set(v___x_460_, 0, v___x_494_);
v___x_496_ = v___x_460_;
goto v_reusejp_495_;
}
else
{
lean_object* v_reuseFailAlloc_497_; 
v_reuseFailAlloc_497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_497_, 0, v___x_494_);
v___x_496_ = v_reuseFailAlloc_497_;
goto v_reusejp_495_;
}
v_reusejp_495_:
{
return v___x_496_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1___boxed(lean_object* v_cls_503_, lean_object* v_msg_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_){
_start:
{
lean_object* v_res_510_; 
v_res_510_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1(v_cls_503_, v_msg_504_, v___y_505_, v___y_506_, v___y_507_, v___y_508_);
lean_dec(v___y_508_);
lean_dec_ref(v___y_507_);
lean_dec(v___y_506_);
lean_dec_ref(v___y_505_);
return v_res_510_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__3(size_t v_sz_511_, size_t v_i_512_, lean_object* v_bs_513_){
_start:
{
uint8_t v___x_514_; 
v___x_514_ = lean_usize_dec_lt(v_i_512_, v_sz_511_);
if (v___x_514_ == 0)
{
return v_bs_513_;
}
else
{
lean_object* v_v_515_; lean_object* v___x_516_; lean_object* v_bs_x27_517_; lean_object* v___x_518_; size_t v___x_519_; size_t v___x_520_; lean_object* v___x_521_; 
v_v_515_ = lean_array_uget(v_bs_513_, v_i_512_);
v___x_516_ = lean_unsigned_to_nat(0u);
v_bs_x27_517_ = lean_array_uset(v_bs_513_, v_i_512_, v___x_516_);
v___x_518_ = l_Lean_mkFVar(v_v_515_);
v___x_519_ = ((size_t)1ULL);
v___x_520_ = lean_usize_add(v_i_512_, v___x_519_);
v___x_521_ = lean_array_uset(v_bs_x27_517_, v_i_512_, v___x_518_);
v_i_512_ = v___x_520_;
v_bs_513_ = v___x_521_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__3___boxed(lean_object* v_sz_523_, lean_object* v_i_524_, lean_object* v_bs_525_){
_start:
{
size_t v_sz_boxed_526_; size_t v_i_boxed_527_; lean_object* v_res_528_; 
v_sz_boxed_526_ = lean_unbox_usize(v_sz_523_);
lean_dec(v_sz_523_);
v_i_boxed_527_ = lean_unbox_usize(v_i_524_);
lean_dec(v_i_524_);
v_res_528_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__3(v_sz_boxed_526_, v_i_boxed_527_, v_bs_525_);
return v_res_528_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5(void){
_start:
{
lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; 
v___x_538_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__2));
v___x_539_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__4));
v___x_540_ = l_Lean_Name_append(v___x_539_, v___x_538_);
return v___x_540_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__7(void){
_start:
{
lean_object* v___x_542_; lean_object* v___x_543_; 
v___x_542_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__6));
v___x_543_ = l_Lean_stringToMessageData(v___x_542_);
return v___x_543_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__9(void){
_start:
{
lean_object* v___x_545_; lean_object* v___x_546_; 
v___x_545_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__8));
v___x_546_ = l_Lean_stringToMessageData(v___x_545_);
return v___x_546_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__11(void){
_start:
{
lean_object* v___x_548_; lean_object* v___x_549_; 
v___x_548_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__10));
v___x_549_ = l_Lean_stringToMessageData(v___x_548_);
return v___x_549_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__15(void){
_start:
{
lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; 
v___x_553_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__14));
v___x_554_ = lean_unsigned_to_nat(15u);
v___x_555_ = lean_unsigned_to_nat(120u);
v___x_556_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__13));
v___x_557_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__12));
v___x_558_ = l_mkPanicMessageWithDecl(v___x_557_, v___x_556_, v___x_555_, v___x_554_, v___x_553_);
return v___x_558_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop(lean_object* v_mvarId_559_, lean_object* v_givenNames_560_, lean_object* v_recursorInfo_561_, lean_object* v_reverted_562_, lean_object* v_major_563_, lean_object* v_indices_564_, lean_object* v_baseSubst_565_, lean_object* v_initialArity_566_, lean_object* v_numMinors_567_, lean_object* v_pos_568_, lean_object* v_minorIdx_569_, lean_object* v_recursor_570_, lean_object* v_recursorType_571_, uint8_t v_consumedMajor_572_, lean_object* v_subgoals_573_, lean_object* v_a_574_, lean_object* v_a_575_, lean_object* v_a_576_, lean_object* v_a_577_){
_start:
{
lean_object* v___y_580_; lean_object* v___y_581_; lean_object* v___y_582_; lean_object* v___y_583_; lean_object* v___y_636_; uint8_t v___y_637_; lean_object* v___y_638_; lean_object* v___y_639_; uint8_t v___y_640_; lean_object* v___y_641_; lean_object* v___y_642_; lean_object* v___y_643_; lean_object* v___y_644_; lean_object* v___y_645_; lean_object* v___y_646_; lean_object* v___y_647_; lean_object* v___y_648_; lean_object* v___y_649_; lean_object* v___y_650_; uint8_t v___y_651_; lean_object* v___y_687_; uint8_t v___y_688_; lean_object* v___y_689_; lean_object* v___y_690_; uint8_t v___y_691_; lean_object* v___y_692_; lean_object* v___y_693_; lean_object* v___y_694_; lean_object* v___y_695_; lean_object* v___y_696_; lean_object* v___y_697_; lean_object* v___y_698_; lean_object* v___y_699_; lean_object* v___y_700_; lean_object* v___y_701_; lean_object* v___y_719_; uint8_t v___y_720_; lean_object* v_fst_721_; lean_object* v_snd_722_; lean_object* v___y_739_; uint8_t v___y_740_; lean_object* v___y_741_; lean_object* v___x_753_; 
v___x_753_ = l_Lean_Meta_whnfForall(v_recursorType_571_, v_a_574_, v_a_575_, v_a_576_, v_a_577_);
if (lean_obj_tag(v___x_753_) == 0)
{
lean_object* v_a_754_; uint8_t v___y_756_; lean_object* v___y_757_; uint8_t v___y_758_; lean_object* v___y_759_; lean_object* v___y_760_; lean_object* v___y_761_; lean_object* v___y_762_; lean_object* v___y_763_; lean_object* v___y_764_; lean_object* v___y_765_; lean_object* v___y_766_; lean_object* v___y_767_; lean_object* v___y_768_; lean_object* v___y_769_; uint8_t v___y_811_; lean_object* v___y_812_; uint8_t v___y_813_; lean_object* v___y_814_; lean_object* v___y_815_; lean_object* v___y_816_; lean_object* v___y_817_; lean_object* v___y_818_; lean_object* v___y_819_; lean_object* v___y_820_; lean_object* v___y_832_; lean_object* v___y_833_; uint8_t v___y_834_; lean_object* v___y_835_; lean_object* v___y_836_; lean_object* v___y_837_; lean_object* v___y_838_; lean_object* v___y_839_; uint8_t v___y_840_; lean_object* v___y_910_; uint8_t v___y_911_; lean_object* v___y_912_; lean_object* v___y_913_; lean_object* v___y_914_; lean_object* v___y_915_; uint8_t v___y_916_; lean_object* v___y_917_; lean_object* v___y_918_; uint8_t v___y_924_; lean_object* v___y_925_; lean_object* v___y_926_; lean_object* v___y_927_; lean_object* v___y_928_; lean_object* v___y_929_; uint8_t v___y_941_; uint8_t v___x_988_; 
v_a_754_ = lean_ctor_get(v___x_753_, 0);
lean_inc(v_a_754_);
lean_dec_ref(v___x_753_);
v___x_988_ = l_Lean_Expr_isForall(v_a_754_);
if (v___x_988_ == 0)
{
v___y_941_ = v___x_988_;
goto v___jp_940_;
}
else
{
lean_object* v_numArgs_989_; uint8_t v___x_990_; 
v_numArgs_989_ = lean_ctor_get(v_recursorInfo_561_, 3);
v___x_990_ = lean_nat_dec_lt(v_pos_568_, v_numArgs_989_);
v___y_941_ = v___x_990_;
goto v___jp_940_;
}
v___jp_755_:
{
lean_object* v___x_770_; 
v___x_770_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___y_757_, v___y_763_, v___y_760_, v___y_765_, v___y_762_, v___y_761_);
if (lean_obj_tag(v___x_770_) == 0)
{
lean_object* v_a_771_; lean_object* v___x_772_; 
v_a_771_ = lean_ctor_get(v___x_770_, 0);
lean_inc(v_a_771_);
lean_dec_ref(v___x_770_);
lean_inc(v_mvarId_559_);
v___x_772_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTypeBody(v_mvarId_559_, v_a_754_, v_a_771_, v___y_760_, v___y_765_, v___y_762_, v___y_761_);
if (lean_obj_tag(v___x_772_) == 0)
{
lean_object* v_options_773_; lean_object* v_a_774_; lean_object* v_inheritedTraceOptions_775_; uint8_t v_hasTrace_776_; lean_object* v___x_777_; 
v_options_773_ = lean_ctor_get(v___y_762_, 2);
v_a_774_ = lean_ctor_get(v___x_772_, 0);
lean_inc(v_a_774_);
lean_dec_ref(v___x_772_);
v_inheritedTraceOptions_775_ = lean_ctor_get(v___y_762_, 13);
v_hasTrace_776_ = lean_ctor_get_uint8(v_options_773_, sizeof(void*)*1);
lean_inc(v_a_771_);
v___x_777_ = l_Lean_Expr_app___override(v_recursor_570_, v_a_771_);
if (v_hasTrace_776_ == 0)
{
v___y_687_ = v___y_764_;
v___y_688_ = v___y_756_;
v___y_689_ = v___y_766_;
v___y_690_ = v___y_767_;
v___y_691_ = v___y_758_;
v___y_692_ = v___y_759_;
v___y_693_ = v_a_771_;
v___y_694_ = v_a_774_;
v___y_695_ = v___x_777_;
v___y_696_ = v___y_768_;
v___y_697_ = v___y_769_;
v___y_698_ = v___y_760_;
v___y_699_ = v___y_765_;
v___y_700_ = v___y_762_;
v___y_701_ = v___y_761_;
goto v___jp_686_;
}
else
{
lean_object* v___x_778_; lean_object* v___x_779_; uint8_t v___x_780_; 
v___x_778_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__2));
v___x_779_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5);
v___x_780_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_775_, v_options_773_, v___x_779_);
if (v___x_780_ == 0)
{
v___y_687_ = v___y_764_;
v___y_688_ = v___y_756_;
v___y_689_ = v___y_766_;
v___y_690_ = v___y_767_;
v___y_691_ = v___y_758_;
v___y_692_ = v___y_759_;
v___y_693_ = v_a_771_;
v___y_694_ = v_a_774_;
v___y_695_ = v___x_777_;
v___y_696_ = v___y_768_;
v___y_697_ = v___y_769_;
v___y_698_ = v___y_760_;
v___y_699_ = v___y_765_;
v___y_700_ = v___y_762_;
v___y_701_ = v___y_761_;
goto v___jp_686_;
}
else
{
lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; 
v___x_781_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__11, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__11_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__11);
v___x_782_ = l_Lean_Expr_fvarId_x21(v_major_563_);
v___x_783_ = l_Lean_MessageData_ofName(v___x_782_);
v___x_784_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_784_, 0, v___x_781_);
lean_ctor_set(v___x_784_, 1, v___x_783_);
v___x_785_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1(v___x_778_, v___x_784_, v___y_760_, v___y_765_, v___y_762_, v___y_761_);
if (lean_obj_tag(v___x_785_) == 0)
{
lean_dec_ref(v___x_785_);
v___y_687_ = v___y_764_;
v___y_688_ = v___y_756_;
v___y_689_ = v___y_766_;
v___y_690_ = v___y_767_;
v___y_691_ = v___y_758_;
v___y_692_ = v___y_759_;
v___y_693_ = v_a_771_;
v___y_694_ = v_a_774_;
v___y_695_ = v___x_777_;
v___y_696_ = v___y_768_;
v___y_697_ = v___y_769_;
v___y_698_ = v___y_760_;
v___y_699_ = v___y_765_;
v___y_700_ = v___y_762_;
v___y_701_ = v___y_761_;
goto v___jp_686_;
}
else
{
lean_object* v_a_786_; lean_object* v___x_788_; uint8_t v_isShared_789_; uint8_t v_isSharedCheck_793_; 
lean_dec_ref(v___x_777_);
lean_dec(v_a_774_);
lean_dec(v_a_771_);
lean_dec_ref(v___y_769_);
lean_dec(v___y_768_);
lean_dec(v___y_767_);
lean_dec(v___y_766_);
lean_dec(v___y_764_);
lean_dec_ref(v_subgoals_573_);
lean_dec(v_minorIdx_569_);
lean_dec(v_pos_568_);
lean_dec(v_baseSubst_565_);
lean_dec_ref(v_major_563_);
lean_dec(v_mvarId_559_);
v_a_786_ = lean_ctor_get(v___x_785_, 0);
v_isSharedCheck_793_ = !lean_is_exclusive(v___x_785_);
if (v_isSharedCheck_793_ == 0)
{
v___x_788_ = v___x_785_;
v_isShared_789_ = v_isSharedCheck_793_;
goto v_resetjp_787_;
}
else
{
lean_inc(v_a_786_);
lean_dec(v___x_785_);
v___x_788_ = lean_box(0);
v_isShared_789_ = v_isSharedCheck_793_;
goto v_resetjp_787_;
}
v_resetjp_787_:
{
lean_object* v___x_791_; 
if (v_isShared_789_ == 0)
{
v___x_791_ = v___x_788_;
goto v_reusejp_790_;
}
else
{
lean_object* v_reuseFailAlloc_792_; 
v_reuseFailAlloc_792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_792_, 0, v_a_786_);
v___x_791_ = v_reuseFailAlloc_792_;
goto v_reusejp_790_;
}
v_reusejp_790_:
{
return v___x_791_;
}
}
}
}
}
}
else
{
lean_object* v_a_794_; lean_object* v___x_796_; uint8_t v_isShared_797_; uint8_t v_isSharedCheck_801_; 
lean_dec(v_a_771_);
lean_dec_ref(v___y_769_);
lean_dec(v___y_768_);
lean_dec(v___y_767_);
lean_dec(v___y_766_);
lean_dec(v___y_764_);
lean_dec_ref(v_subgoals_573_);
lean_dec_ref(v_recursor_570_);
lean_dec(v_minorIdx_569_);
lean_dec(v_pos_568_);
lean_dec(v_baseSubst_565_);
lean_dec_ref(v_major_563_);
lean_dec(v_mvarId_559_);
v_a_794_ = lean_ctor_get(v___x_772_, 0);
v_isSharedCheck_801_ = !lean_is_exclusive(v___x_772_);
if (v_isSharedCheck_801_ == 0)
{
v___x_796_ = v___x_772_;
v_isShared_797_ = v_isSharedCheck_801_;
goto v_resetjp_795_;
}
else
{
lean_inc(v_a_794_);
lean_dec(v___x_772_);
v___x_796_ = lean_box(0);
v_isShared_797_ = v_isSharedCheck_801_;
goto v_resetjp_795_;
}
v_resetjp_795_:
{
lean_object* v___x_799_; 
if (v_isShared_797_ == 0)
{
v___x_799_ = v___x_796_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v_a_794_);
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
lean_dec_ref(v___y_769_);
lean_dec(v___y_768_);
lean_dec(v___y_767_);
lean_dec(v___y_766_);
lean_dec(v___y_764_);
lean_dec(v_a_754_);
lean_dec_ref(v_subgoals_573_);
lean_dec_ref(v_recursor_570_);
lean_dec(v_minorIdx_569_);
lean_dec(v_pos_568_);
lean_dec(v_baseSubst_565_);
lean_dec_ref(v_major_563_);
lean_dec(v_mvarId_559_);
v_a_802_ = lean_ctor_get(v___x_770_, 0);
v_isSharedCheck_809_ = !lean_is_exclusive(v___x_770_);
if (v_isSharedCheck_809_ == 0)
{
v___x_804_ = v___x_770_;
v_isShared_805_ = v_isSharedCheck_809_;
goto v_resetjp_803_;
}
else
{
lean_inc(v_a_802_);
lean_dec(v___x_770_);
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
v___jp_810_:
{
lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; uint8_t v___x_827_; 
v___x_821_ = lean_nat_sub(v___y_815_, v_initialArity_566_);
lean_dec(v___y_815_);
v___x_822_ = lean_array_get_size(v_reverted_562_);
v___x_823_ = lean_array_get_size(v_indices_564_);
v___x_824_ = lean_nat_sub(v___x_822_, v___x_823_);
v___x_825_ = lean_nat_sub(v___x_824_, v___y_814_);
lean_dec(v___x_824_);
v___x_826_ = lean_array_get_size(v_givenNames_560_);
v___x_827_ = lean_nat_dec_lt(v_minorIdx_569_, v___x_826_);
if (v___x_827_ == 0)
{
lean_object* v___x_828_; lean_object* v___x_829_; 
v___x_828_ = lean_box(0);
v___x_829_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_829_, 0, v___x_828_);
lean_ctor_set_uint8(v___x_829_, sizeof(void*)*1, v___y_811_);
v___y_756_ = v___y_811_;
v___y_757_ = v___y_812_;
v___y_758_ = v___y_813_;
v___y_759_ = v___y_814_;
v___y_760_ = v___y_817_;
v___y_761_ = v___y_820_;
v___y_762_ = v___y_819_;
v___y_763_ = v___y_816_;
v___y_764_ = v___x_825_;
v___y_765_ = v___y_818_;
v___y_766_ = v___x_822_;
v___y_767_ = v___x_821_;
v___y_768_ = v___x_823_;
v___y_769_ = v___x_829_;
goto v___jp_755_;
}
else
{
lean_object* v___x_830_; 
v___x_830_ = lean_array_fget_borrowed(v_givenNames_560_, v_minorIdx_569_);
lean_inc(v___x_830_);
v___y_756_ = v___y_811_;
v___y_757_ = v___y_812_;
v___y_758_ = v___y_813_;
v___y_759_ = v___y_814_;
v___y_760_ = v___y_817_;
v___y_761_ = v___y_820_;
v___y_762_ = v___y_819_;
v___y_763_ = v___y_816_;
v___y_764_ = v___x_825_;
v___y_765_ = v___y_818_;
v___y_766_ = v___x_822_;
v___y_767_ = v___x_821_;
v___y_768_ = v___x_823_;
v___y_769_ = v___x_830_;
goto v___jp_755_;
}
}
v___jp_831_:
{
if (v___y_840_ == 0)
{
lean_object* v___x_841_; uint8_t v___x_842_; 
lean_inc_ref(v___y_832_);
v___x_841_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTargetArity(v___y_832_);
v___x_842_ = lean_nat_dec_lt(v___x_841_, v_initialArity_566_);
if (v___x_842_ == 0)
{
v___y_811_ = v___y_840_;
v___y_812_ = v___y_832_;
v___y_813_ = v___y_834_;
v___y_814_ = v___y_836_;
v___y_815_ = v___x_841_;
v___y_816_ = v___y_839_;
v___y_817_ = v___y_835_;
v___y_818_ = v___y_837_;
v___y_819_ = v___y_833_;
v___y_820_ = v___y_838_;
goto v___jp_810_;
}
else
{
lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; 
v___x_843_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1));
v___x_844_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9);
lean_inc(v_mvarId_559_);
v___x_845_ = l_Lean_Meta_throwTacticEx___redArg(v___x_843_, v_mvarId_559_, v___x_844_, v___y_835_, v___y_837_, v___y_833_, v___y_838_);
if (lean_obj_tag(v___x_845_) == 0)
{
lean_dec_ref(v___x_845_);
v___y_811_ = v___y_840_;
v___y_812_ = v___y_832_;
v___y_813_ = v___y_834_;
v___y_814_ = v___y_836_;
v___y_815_ = v___x_841_;
v___y_816_ = v___y_839_;
v___y_817_ = v___y_835_;
v___y_818_ = v___y_837_;
v___y_819_ = v___y_833_;
v___y_820_ = v___y_838_;
goto v___jp_810_;
}
else
{
lean_object* v_a_846_; lean_object* v___x_848_; uint8_t v_isShared_849_; uint8_t v_isSharedCheck_853_; 
lean_dec(v___x_841_);
lean_dec(v___y_839_);
lean_dec_ref(v___y_832_);
lean_dec(v_a_754_);
lean_dec_ref(v_subgoals_573_);
lean_dec_ref(v_recursor_570_);
lean_dec(v_minorIdx_569_);
lean_dec(v_pos_568_);
lean_dec(v_baseSubst_565_);
lean_dec_ref(v_major_563_);
lean_dec(v_mvarId_559_);
v_a_846_ = lean_ctor_get(v___x_845_, 0);
v_isSharedCheck_853_ = !lean_is_exclusive(v___x_845_);
if (v_isSharedCheck_853_ == 0)
{
v___x_848_ = v___x_845_;
v_isShared_849_ = v_isSharedCheck_853_;
goto v_resetjp_847_;
}
else
{
lean_inc(v_a_846_);
lean_dec(v___x_845_);
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
}
else
{
lean_object* v___x_854_; lean_object* v___x_855_; 
v___x_854_ = lean_box(0);
lean_inc_ref(v___y_832_);
v___x_855_ = l_Lean_Meta_synthInstance_x3f(v___y_832_, v___x_854_, v___y_835_, v___y_837_, v___y_833_, v___y_838_);
if (lean_obj_tag(v___x_855_) == 0)
{
lean_object* v_a_856_; 
v_a_856_ = lean_ctor_get(v___x_855_, 0);
lean_inc(v_a_856_);
lean_dec_ref(v___x_855_);
if (lean_obj_tag(v_a_856_) == 0)
{
lean_object* v___x_857_; 
v___x_857_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___y_832_, v___y_839_, v___y_835_, v___y_837_, v___y_833_, v___y_838_);
if (lean_obj_tag(v___x_857_) == 0)
{
lean_object* v_a_858_; lean_object* v___x_859_; 
v_a_858_ = lean_ctor_get(v___x_857_, 0);
lean_inc(v_a_858_);
lean_dec_ref(v___x_857_);
lean_inc(v_mvarId_559_);
v___x_859_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTypeBody(v_mvarId_559_, v_a_754_, v_a_858_, v___y_835_, v___y_837_, v___y_833_, v___y_838_);
if (lean_obj_tag(v___x_859_) == 0)
{
lean_object* v_a_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; 
v_a_860_ = lean_ctor_get(v___x_859_, 0);
lean_inc(v_a_860_);
lean_dec_ref(v___x_859_);
lean_inc(v_a_858_);
v___x_861_ = l_Lean_Expr_app___override(v_recursor_570_, v_a_858_);
v___x_862_ = lean_nat_add(v_pos_568_, v___y_836_);
lean_dec(v_pos_568_);
v___x_863_ = lean_nat_add(v_minorIdx_569_, v___y_836_);
lean_dec(v_minorIdx_569_);
v___x_864_ = l_Lean_Expr_mvarId_x21(v_a_858_);
lean_dec(v_a_858_);
v___x_865_ = ((lean_object*)(l_Lean_Meta_instInhabitedInductionSubgoal_default___closed__0));
v___x_866_ = lean_box(0);
v___x_867_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_867_, 0, v___x_864_);
lean_ctor_set(v___x_867_, 1, v___x_865_);
lean_ctor_set(v___x_867_, 2, v___x_866_);
v___x_868_ = lean_array_push(v_subgoals_573_, v___x_867_);
v_pos_568_ = v___x_862_;
v_minorIdx_569_ = v___x_863_;
v_recursor_570_ = v___x_861_;
v_recursorType_571_ = v_a_860_;
v_subgoals_573_ = v___x_868_;
v_a_574_ = v___y_835_;
v_a_575_ = v___y_837_;
v_a_576_ = v___y_833_;
v_a_577_ = v___y_838_;
goto _start;
}
else
{
lean_object* v_a_870_; lean_object* v___x_872_; uint8_t v_isShared_873_; uint8_t v_isSharedCheck_877_; 
lean_dec(v_a_858_);
lean_dec_ref(v_subgoals_573_);
lean_dec_ref(v_recursor_570_);
lean_dec(v_minorIdx_569_);
lean_dec(v_pos_568_);
lean_dec(v_baseSubst_565_);
lean_dec_ref(v_major_563_);
lean_dec(v_mvarId_559_);
v_a_870_ = lean_ctor_get(v___x_859_, 0);
v_isSharedCheck_877_ = !lean_is_exclusive(v___x_859_);
if (v_isSharedCheck_877_ == 0)
{
v___x_872_ = v___x_859_;
v_isShared_873_ = v_isSharedCheck_877_;
goto v_resetjp_871_;
}
else
{
lean_inc(v_a_870_);
lean_dec(v___x_859_);
v___x_872_ = lean_box(0);
v_isShared_873_ = v_isSharedCheck_877_;
goto v_resetjp_871_;
}
v_resetjp_871_:
{
lean_object* v___x_875_; 
if (v_isShared_873_ == 0)
{
v___x_875_ = v___x_872_;
goto v_reusejp_874_;
}
else
{
lean_object* v_reuseFailAlloc_876_; 
v_reuseFailAlloc_876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_876_, 0, v_a_870_);
v___x_875_ = v_reuseFailAlloc_876_;
goto v_reusejp_874_;
}
v_reusejp_874_:
{
return v___x_875_;
}
}
}
}
else
{
lean_object* v_a_878_; lean_object* v___x_880_; uint8_t v_isShared_881_; uint8_t v_isSharedCheck_885_; 
lean_dec(v_a_754_);
lean_dec_ref(v_subgoals_573_);
lean_dec_ref(v_recursor_570_);
lean_dec(v_minorIdx_569_);
lean_dec(v_pos_568_);
lean_dec(v_baseSubst_565_);
lean_dec_ref(v_major_563_);
lean_dec(v_mvarId_559_);
v_a_878_ = lean_ctor_get(v___x_857_, 0);
v_isSharedCheck_885_ = !lean_is_exclusive(v___x_857_);
if (v_isSharedCheck_885_ == 0)
{
v___x_880_ = v___x_857_;
v_isShared_881_ = v_isSharedCheck_885_;
goto v_resetjp_879_;
}
else
{
lean_inc(v_a_878_);
lean_dec(v___x_857_);
v___x_880_ = lean_box(0);
v_isShared_881_ = v_isSharedCheck_885_;
goto v_resetjp_879_;
}
v_resetjp_879_:
{
lean_object* v___x_883_; 
if (v_isShared_881_ == 0)
{
v___x_883_ = v___x_880_;
goto v_reusejp_882_;
}
else
{
lean_object* v_reuseFailAlloc_884_; 
v_reuseFailAlloc_884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_884_, 0, v_a_878_);
v___x_883_ = v_reuseFailAlloc_884_;
goto v_reusejp_882_;
}
v_reusejp_882_:
{
return v___x_883_;
}
}
}
}
else
{
lean_object* v_val_886_; lean_object* v___x_887_; 
lean_dec(v___y_839_);
lean_dec_ref(v___y_832_);
v_val_886_ = lean_ctor_get(v_a_856_, 0);
lean_inc(v_val_886_);
lean_dec_ref(v_a_856_);
lean_inc(v_mvarId_559_);
v___x_887_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTypeBody(v_mvarId_559_, v_a_754_, v_val_886_, v___y_835_, v___y_837_, v___y_833_, v___y_838_);
if (lean_obj_tag(v___x_887_) == 0)
{
lean_object* v_a_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; 
v_a_888_ = lean_ctor_get(v___x_887_, 0);
lean_inc(v_a_888_);
lean_dec_ref(v___x_887_);
v___x_889_ = l_Lean_Expr_app___override(v_recursor_570_, v_val_886_);
v___x_890_ = lean_nat_add(v_pos_568_, v___y_836_);
lean_dec(v_pos_568_);
v___x_891_ = lean_nat_add(v_minorIdx_569_, v___y_836_);
lean_dec(v_minorIdx_569_);
v_pos_568_ = v___x_890_;
v_minorIdx_569_ = v___x_891_;
v_recursor_570_ = v___x_889_;
v_recursorType_571_ = v_a_888_;
v_a_574_ = v___y_835_;
v_a_575_ = v___y_837_;
v_a_576_ = v___y_833_;
v_a_577_ = v___y_838_;
goto _start;
}
else
{
lean_object* v_a_893_; lean_object* v___x_895_; uint8_t v_isShared_896_; uint8_t v_isSharedCheck_900_; 
lean_dec(v_val_886_);
lean_dec_ref(v_subgoals_573_);
lean_dec_ref(v_recursor_570_);
lean_dec(v_minorIdx_569_);
lean_dec(v_pos_568_);
lean_dec(v_baseSubst_565_);
lean_dec_ref(v_major_563_);
lean_dec(v_mvarId_559_);
v_a_893_ = lean_ctor_get(v___x_887_, 0);
v_isSharedCheck_900_ = !lean_is_exclusive(v___x_887_);
if (v_isSharedCheck_900_ == 0)
{
v___x_895_ = v___x_887_;
v_isShared_896_ = v_isSharedCheck_900_;
goto v_resetjp_894_;
}
else
{
lean_inc(v_a_893_);
lean_dec(v___x_887_);
v___x_895_ = lean_box(0);
v_isShared_896_ = v_isSharedCheck_900_;
goto v_resetjp_894_;
}
v_resetjp_894_:
{
lean_object* v___x_898_; 
if (v_isShared_896_ == 0)
{
v___x_898_ = v___x_895_;
goto v_reusejp_897_;
}
else
{
lean_object* v_reuseFailAlloc_899_; 
v_reuseFailAlloc_899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_899_, 0, v_a_893_);
v___x_898_ = v_reuseFailAlloc_899_;
goto v_reusejp_897_;
}
v_reusejp_897_:
{
return v___x_898_;
}
}
}
}
}
else
{
lean_object* v_a_901_; lean_object* v___x_903_; uint8_t v_isShared_904_; uint8_t v_isSharedCheck_908_; 
lean_dec(v___y_839_);
lean_dec_ref(v___y_832_);
lean_dec(v_a_754_);
lean_dec_ref(v_subgoals_573_);
lean_dec_ref(v_recursor_570_);
lean_dec(v_minorIdx_569_);
lean_dec(v_pos_568_);
lean_dec(v_baseSubst_565_);
lean_dec_ref(v_major_563_);
lean_dec(v_mvarId_559_);
v_a_901_ = lean_ctor_get(v___x_855_, 0);
v_isSharedCheck_908_ = !lean_is_exclusive(v___x_855_);
if (v_isSharedCheck_908_ == 0)
{
v___x_903_ = v___x_855_;
v_isShared_904_ = v_isSharedCheck_908_;
goto v_resetjp_902_;
}
else
{
lean_inc(v_a_901_);
lean_dec(v___x_855_);
v___x_903_ = lean_box(0);
v_isShared_904_ = v_isSharedCheck_908_;
goto v_resetjp_902_;
}
v_resetjp_902_:
{
lean_object* v___x_906_; 
if (v_isShared_904_ == 0)
{
v___x_906_ = v___x_903_;
goto v_reusejp_905_;
}
else
{
lean_object* v_reuseFailAlloc_907_; 
v_reuseFailAlloc_907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_907_, 0, v_a_901_);
v___x_906_ = v_reuseFailAlloc_907_;
goto v_reusejp_905_;
}
v_reusejp_905_:
{
return v___x_906_;
}
}
}
}
}
v___jp_909_:
{
uint8_t v___x_919_; 
v___x_919_ = l_Lean_BinderInfo_isInstImplicit(v___y_916_);
if (v___x_919_ == 0)
{
v___y_832_ = v___y_910_;
v___y_833_ = v___y_912_;
v___y_834_ = v___y_911_;
v___y_835_ = v___y_914_;
v___y_836_ = v___y_913_;
v___y_837_ = v___y_915_;
v___y_838_ = v___y_917_;
v___y_839_ = v___y_918_;
v___y_840_ = v___x_919_;
goto v___jp_831_;
}
else
{
lean_object* v___x_920_; lean_object* v___x_921_; uint8_t v___x_922_; 
v___x_920_ = lean_array_get_size(v_givenNames_560_);
v___x_921_ = lean_unsigned_to_nat(0u);
v___x_922_ = lean_nat_dec_eq(v___x_920_, v___x_921_);
v___y_832_ = v___y_910_;
v___y_833_ = v___y_912_;
v___y_834_ = v___y_911_;
v___y_835_ = v___y_914_;
v___y_836_ = v___y_913_;
v___y_837_ = v___y_915_;
v___y_838_ = v___y_917_;
v___y_839_ = v___y_918_;
v___y_840_ = v___x_922_;
goto v___jp_831_;
}
}
v___jp_923_:
{
if (lean_obj_tag(v_a_754_) == 7)
{
lean_object* v_binderName_930_; lean_object* v_binderType_931_; uint8_t v_binderInfo_932_; lean_object* v___x_933_; lean_object* v___x_934_; uint8_t v___x_935_; 
v_binderName_930_ = lean_ctor_get(v_a_754_, 0);
v_binderType_931_ = lean_ctor_get(v_a_754_, 1);
v_binderInfo_932_ = lean_ctor_get_uint8(v_a_754_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_931_);
v___x_933_ = l_Lean_Expr_headBeta(v_binderType_931_);
v___x_934_ = lean_unsigned_to_nat(1u);
v___x_935_ = lean_nat_dec_eq(v_numMinors_567_, v___x_934_);
if (v___x_935_ == 0)
{
lean_object* v___x_936_; lean_object* v___x_937_; 
lean_inc(v_binderName_930_);
v___x_936_ = lean_erase_macro_scopes(v_binderName_930_);
v___x_937_ = l_Lean_Name_append(v___y_925_, v___x_936_);
v___y_910_ = v___x_933_;
v___y_911_ = v___y_924_;
v___y_912_ = v___y_928_;
v___y_913_ = v___x_934_;
v___y_914_ = v___y_926_;
v___y_915_ = v___y_927_;
v___y_916_ = v_binderInfo_932_;
v___y_917_ = v___y_929_;
v___y_918_ = v___x_937_;
goto v___jp_909_;
}
else
{
v___y_910_ = v___x_933_;
v___y_911_ = v___y_924_;
v___y_912_ = v___y_928_;
v___y_913_ = v___x_934_;
v___y_914_ = v___y_926_;
v___y_915_ = v___y_927_;
v___y_916_ = v_binderInfo_932_;
v___y_917_ = v___y_929_;
v___y_918_ = v___y_925_;
goto v___jp_909_;
}
}
else
{
lean_object* v___x_938_; lean_object* v___x_939_; 
lean_dec(v___y_925_);
lean_dec(v_a_754_);
lean_dec_ref(v_subgoals_573_);
lean_dec_ref(v_recursor_570_);
lean_dec(v_minorIdx_569_);
lean_dec(v_pos_568_);
lean_dec(v_baseSubst_565_);
lean_dec_ref(v_major_563_);
lean_dec(v_mvarId_559_);
v___x_938_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__15, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__15_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__15);
v___x_939_ = l_panic___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__4(v___x_938_, v___y_926_, v___y_927_, v___y_928_, v___y_929_);
return v___x_939_;
}
}
v___jp_940_:
{
if (v___y_941_ == 0)
{
lean_dec(v_a_754_);
lean_dec(v_minorIdx_569_);
lean_dec(v_pos_568_);
lean_dec(v_baseSubst_565_);
lean_dec_ref(v_major_563_);
if (v_consumedMajor_572_ == 0)
{
lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; 
v___x_942_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1));
v___x_943_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9);
lean_inc(v_mvarId_559_);
v___x_944_ = l_Lean_Meta_throwTacticEx___redArg(v___x_942_, v_mvarId_559_, v___x_943_, v_a_574_, v_a_575_, v_a_576_, v_a_577_);
if (lean_obj_tag(v___x_944_) == 0)
{
lean_dec_ref(v___x_944_);
v___y_580_ = v_a_574_;
v___y_581_ = v_a_575_;
v___y_582_ = v_a_576_;
v___y_583_ = v_a_577_;
goto v___jp_579_;
}
else
{
lean_object* v_a_945_; lean_object* v___x_947_; uint8_t v_isShared_948_; uint8_t v_isSharedCheck_952_; 
lean_dec_ref(v_subgoals_573_);
lean_dec_ref(v_recursor_570_);
lean_dec(v_mvarId_559_);
v_a_945_ = lean_ctor_get(v___x_944_, 0);
v_isSharedCheck_952_ = !lean_is_exclusive(v___x_944_);
if (v_isSharedCheck_952_ == 0)
{
v___x_947_ = v___x_944_;
v_isShared_948_ = v_isSharedCheck_952_;
goto v_resetjp_946_;
}
else
{
lean_inc(v_a_945_);
lean_dec(v___x_944_);
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
v___y_580_ = v_a_574_;
v___y_581_ = v_a_575_;
v___y_582_ = v_a_576_;
v___y_583_ = v_a_577_;
goto v___jp_579_;
}
}
else
{
lean_object* v___x_953_; uint8_t v___x_954_; 
v___x_953_ = l_Lean_Meta_RecursorInfo_firstIndexPos(v_recursorInfo_561_);
v___x_954_ = lean_nat_dec_eq(v_pos_568_, v___x_953_);
lean_dec(v___x_953_);
if (v___x_954_ == 0)
{
lean_object* v___x_955_; 
lean_inc(v_mvarId_559_);
v___x_955_ = l_Lean_MVarId_getTag(v_mvarId_559_, v_a_574_, v_a_575_, v_a_576_, v_a_577_);
if (lean_obj_tag(v___x_955_) == 0)
{
lean_object* v_a_956_; uint8_t v___x_957_; 
v_a_956_ = lean_ctor_get(v___x_955_, 0);
lean_inc(v_a_956_);
lean_dec_ref(v___x_955_);
v___x_957_ = lean_nat_dec_le(v_numMinors_567_, v_minorIdx_569_);
if (v___x_957_ == 0)
{
v___y_924_ = v___y_941_;
v___y_925_ = v_a_956_;
v___y_926_ = v_a_574_;
v___y_927_ = v_a_575_;
v___y_928_ = v_a_576_;
v___y_929_ = v_a_577_;
goto v___jp_923_;
}
else
{
lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; 
v___x_958_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1));
v___x_959_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9);
lean_inc(v_mvarId_559_);
v___x_960_ = l_Lean_Meta_throwTacticEx___redArg(v___x_958_, v_mvarId_559_, v___x_959_, v_a_574_, v_a_575_, v_a_576_, v_a_577_);
if (lean_obj_tag(v___x_960_) == 0)
{
lean_dec_ref(v___x_960_);
v___y_924_ = v___y_941_;
v___y_925_ = v_a_956_;
v___y_926_ = v_a_574_;
v___y_927_ = v_a_575_;
v___y_928_ = v_a_576_;
v___y_929_ = v_a_577_;
goto v___jp_923_;
}
else
{
lean_object* v_a_961_; lean_object* v___x_963_; uint8_t v_isShared_964_; uint8_t v_isSharedCheck_968_; 
lean_dec(v_a_956_);
lean_dec(v_a_754_);
lean_dec_ref(v_subgoals_573_);
lean_dec_ref(v_recursor_570_);
lean_dec(v_minorIdx_569_);
lean_dec(v_pos_568_);
lean_dec(v_baseSubst_565_);
lean_dec_ref(v_major_563_);
lean_dec(v_mvarId_559_);
v_a_961_ = lean_ctor_get(v___x_960_, 0);
v_isSharedCheck_968_ = !lean_is_exclusive(v___x_960_);
if (v_isSharedCheck_968_ == 0)
{
v___x_963_ = v___x_960_;
v_isShared_964_ = v_isSharedCheck_968_;
goto v_resetjp_962_;
}
else
{
lean_inc(v_a_961_);
lean_dec(v___x_960_);
v___x_963_ = lean_box(0);
v_isShared_964_ = v_isSharedCheck_968_;
goto v_resetjp_962_;
}
v_resetjp_962_:
{
lean_object* v___x_966_; 
if (v_isShared_964_ == 0)
{
v___x_966_ = v___x_963_;
goto v_reusejp_965_;
}
else
{
lean_object* v_reuseFailAlloc_967_; 
v_reuseFailAlloc_967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_967_, 0, v_a_961_);
v___x_966_ = v_reuseFailAlloc_967_;
goto v_reusejp_965_;
}
v_reusejp_965_:
{
return v___x_966_;
}
}
}
}
}
else
{
lean_object* v_a_969_; lean_object* v___x_971_; uint8_t v_isShared_972_; uint8_t v_isSharedCheck_976_; 
lean_dec(v_a_754_);
lean_dec_ref(v_subgoals_573_);
lean_dec_ref(v_recursor_570_);
lean_dec(v_minorIdx_569_);
lean_dec(v_pos_568_);
lean_dec(v_baseSubst_565_);
lean_dec_ref(v_major_563_);
lean_dec(v_mvarId_559_);
v_a_969_ = lean_ctor_get(v___x_955_, 0);
v_isSharedCheck_976_ = !lean_is_exclusive(v___x_955_);
if (v_isSharedCheck_976_ == 0)
{
v___x_971_ = v___x_955_;
v_isShared_972_ = v_isSharedCheck_976_;
goto v_resetjp_970_;
}
else
{
lean_inc(v_a_969_);
lean_dec(v___x_955_);
v___x_971_ = lean_box(0);
v_isShared_972_ = v_isSharedCheck_976_;
goto v_resetjp_970_;
}
v_resetjp_970_:
{
lean_object* v___x_974_; 
if (v_isShared_972_ == 0)
{
v___x_974_ = v___x_971_;
goto v_reusejp_973_;
}
else
{
lean_object* v_reuseFailAlloc_975_; 
v_reuseFailAlloc_975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_975_, 0, v_a_969_);
v___x_974_ = v_reuseFailAlloc_975_;
goto v_reusejp_973_;
}
v_reusejp_973_:
{
return v___x_974_;
}
}
}
}
else
{
lean_object* v___x_977_; lean_object* v___x_978_; uint8_t v___x_979_; 
v___x_977_ = lean_unsigned_to_nat(0u);
v___x_978_ = lean_array_get_size(v_indices_564_);
v___x_979_ = lean_nat_dec_lt(v___x_977_, v___x_978_);
if (v___x_979_ == 0)
{
v___y_719_ = v___x_978_;
v___y_720_ = v___x_954_;
v_fst_721_ = v_recursor_570_;
v_snd_722_ = v_a_754_;
goto v___jp_718_;
}
else
{
lean_object* v___x_980_; uint8_t v___x_981_; 
lean_inc(v_a_754_);
lean_inc_ref(v_recursor_570_);
v___x_980_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_980_, 0, v_recursor_570_);
lean_ctor_set(v___x_980_, 1, v_a_754_);
v___x_981_ = lean_nat_dec_le(v___x_978_, v___x_978_);
if (v___x_981_ == 0)
{
if (v___x_979_ == 0)
{
lean_dec_ref(v___x_980_);
v___y_719_ = v___x_978_;
v___y_720_ = v___x_954_;
v_fst_721_ = v_recursor_570_;
v_snd_722_ = v_a_754_;
goto v___jp_718_;
}
else
{
size_t v___x_982_; size_t v___x_983_; lean_object* v___x_984_; 
lean_dec(v_a_754_);
lean_dec_ref(v_recursor_570_);
v___x_982_ = ((size_t)0ULL);
v___x_983_ = lean_usize_of_nat(v___x_978_);
lean_inc(v_mvarId_559_);
v___x_984_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__5(v_mvarId_559_, v_indices_564_, v___x_982_, v___x_983_, v___x_980_, v_a_574_, v_a_575_, v_a_576_, v_a_577_);
v___y_739_ = v___x_978_;
v___y_740_ = v___x_954_;
v___y_741_ = v___x_984_;
goto v___jp_738_;
}
}
else
{
size_t v___x_985_; size_t v___x_986_; lean_object* v___x_987_; 
lean_dec(v_a_754_);
lean_dec_ref(v_recursor_570_);
v___x_985_ = ((size_t)0ULL);
v___x_986_ = lean_usize_of_nat(v___x_978_);
lean_inc(v_mvarId_559_);
v___x_987_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__5(v_mvarId_559_, v_indices_564_, v___x_985_, v___x_986_, v___x_980_, v_a_574_, v_a_575_, v_a_576_, v_a_577_);
v___y_739_ = v___x_978_;
v___y_740_ = v___x_954_;
v___y_741_ = v___x_987_;
goto v___jp_738_;
}
}
}
}
}
}
else
{
lean_object* v_a_991_; lean_object* v___x_993_; uint8_t v_isShared_994_; uint8_t v_isSharedCheck_998_; 
lean_dec_ref(v_subgoals_573_);
lean_dec_ref(v_recursor_570_);
lean_dec(v_minorIdx_569_);
lean_dec(v_pos_568_);
lean_dec(v_baseSubst_565_);
lean_dec_ref(v_major_563_);
lean_dec(v_mvarId_559_);
v_a_991_ = lean_ctor_get(v___x_753_, 0);
v_isSharedCheck_998_ = !lean_is_exclusive(v___x_753_);
if (v_isSharedCheck_998_ == 0)
{
v___x_993_ = v___x_753_;
v_isShared_994_ = v_isSharedCheck_998_;
goto v_resetjp_992_;
}
else
{
lean_inc(v_a_991_);
lean_dec(v___x_753_);
v___x_993_ = lean_box(0);
v_isShared_994_ = v_isSharedCheck_998_;
goto v_resetjp_992_;
}
v_resetjp_992_:
{
lean_object* v___x_996_; 
if (v_isShared_994_ == 0)
{
v___x_996_ = v___x_993_;
goto v_reusejp_995_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v_a_991_);
v___x_996_ = v_reuseFailAlloc_997_;
goto v_reusejp_995_;
}
v_reusejp_995_:
{
return v___x_996_;
}
}
}
v___jp_579_:
{
lean_object* v___x_584_; 
v___x_584_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0___redArg(v_mvarId_559_, v_recursor_570_, v___y_581_);
if (lean_obj_tag(v___x_584_) == 0)
{
lean_object* v___x_586_; uint8_t v_isShared_587_; uint8_t v_isSharedCheck_625_; 
v_isSharedCheck_625_ = !lean_is_exclusive(v___x_584_);
if (v_isSharedCheck_625_ == 0)
{
lean_object* v_unused_626_; 
v_unused_626_ = lean_ctor_get(v___x_584_, 0);
lean_dec(v_unused_626_);
v___x_586_ = v___x_584_;
v_isShared_587_ = v_isSharedCheck_625_;
goto v_resetjp_585_;
}
else
{
lean_dec(v___x_584_);
v___x_586_ = lean_box(0);
v_isShared_587_ = v_isSharedCheck_625_;
goto v_resetjp_585_;
}
v_resetjp_585_:
{
lean_object* v_options_588_; uint8_t v_hasTrace_589_; 
v_options_588_ = lean_ctor_get(v___y_582_, 2);
v_hasTrace_589_ = lean_ctor_get_uint8(v_options_588_, sizeof(void*)*1);
if (v_hasTrace_589_ == 0)
{
lean_object* v___x_591_; 
if (v_isShared_587_ == 0)
{
lean_ctor_set(v___x_586_, 0, v_subgoals_573_);
v___x_591_ = v___x_586_;
goto v_reusejp_590_;
}
else
{
lean_object* v_reuseFailAlloc_592_; 
v_reuseFailAlloc_592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_592_, 0, v_subgoals_573_);
v___x_591_ = v_reuseFailAlloc_592_;
goto v_reusejp_590_;
}
v_reusejp_590_:
{
return v___x_591_;
}
}
else
{
lean_object* v_inheritedTraceOptions_593_; lean_object* v___x_594_; lean_object* v___x_595_; uint8_t v___x_596_; 
v_inheritedTraceOptions_593_ = lean_ctor_get(v___y_582_, 13);
v___x_594_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__2));
v___x_595_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5);
v___x_596_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_593_, v_options_588_, v___x_595_);
if (v___x_596_ == 0)
{
lean_object* v___x_598_; 
if (v_isShared_587_ == 0)
{
lean_ctor_set(v___x_586_, 0, v_subgoals_573_);
v___x_598_ = v___x_586_;
goto v_reusejp_597_;
}
else
{
lean_object* v_reuseFailAlloc_599_; 
v_reuseFailAlloc_599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_599_, 0, v_subgoals_573_);
v___x_598_ = v_reuseFailAlloc_599_;
goto v_reusejp_597_;
}
v_reusejp_597_:
{
return v___x_598_;
}
}
else
{
lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; 
lean_del_object(v___x_586_);
v___x_600_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__7, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__7_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__7);
v___x_601_ = lean_array_get_size(v_subgoals_573_);
v___x_602_ = l_Nat_reprFast(v___x_601_);
v___x_603_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_603_, 0, v___x_602_);
v___x_604_ = l_Lean_MessageData_ofFormat(v___x_603_);
v___x_605_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_605_, 0, v___x_600_);
lean_ctor_set(v___x_605_, 1, v___x_604_);
v___x_606_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__9, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__9_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__9);
v___x_607_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_607_, 0, v___x_605_);
lean_ctor_set(v___x_607_, 1, v___x_606_);
v___x_608_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1(v___x_594_, v___x_607_, v___y_580_, v___y_581_, v___y_582_, v___y_583_);
if (lean_obj_tag(v___x_608_) == 0)
{
lean_object* v___x_610_; uint8_t v_isShared_611_; uint8_t v_isSharedCheck_615_; 
v_isSharedCheck_615_ = !lean_is_exclusive(v___x_608_);
if (v_isSharedCheck_615_ == 0)
{
lean_object* v_unused_616_; 
v_unused_616_ = lean_ctor_get(v___x_608_, 0);
lean_dec(v_unused_616_);
v___x_610_ = v___x_608_;
v_isShared_611_ = v_isSharedCheck_615_;
goto v_resetjp_609_;
}
else
{
lean_dec(v___x_608_);
v___x_610_ = lean_box(0);
v_isShared_611_ = v_isSharedCheck_615_;
goto v_resetjp_609_;
}
v_resetjp_609_:
{
lean_object* v___x_613_; 
if (v_isShared_611_ == 0)
{
lean_ctor_set(v___x_610_, 0, v_subgoals_573_);
v___x_613_ = v___x_610_;
goto v_reusejp_612_;
}
else
{
lean_object* v_reuseFailAlloc_614_; 
v_reuseFailAlloc_614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_614_, 0, v_subgoals_573_);
v___x_613_ = v_reuseFailAlloc_614_;
goto v_reusejp_612_;
}
v_reusejp_612_:
{
return v___x_613_;
}
}
}
else
{
lean_object* v_a_617_; lean_object* v___x_619_; uint8_t v_isShared_620_; uint8_t v_isSharedCheck_624_; 
lean_dec_ref(v_subgoals_573_);
v_a_617_ = lean_ctor_get(v___x_608_, 0);
v_isSharedCheck_624_ = !lean_is_exclusive(v___x_608_);
if (v_isSharedCheck_624_ == 0)
{
v___x_619_ = v___x_608_;
v_isShared_620_ = v_isSharedCheck_624_;
goto v_resetjp_618_;
}
else
{
lean_inc(v_a_617_);
lean_dec(v___x_608_);
v___x_619_ = lean_box(0);
v_isShared_620_ = v_isSharedCheck_624_;
goto v_resetjp_618_;
}
v_resetjp_618_:
{
lean_object* v___x_622_; 
if (v_isShared_620_ == 0)
{
v___x_622_ = v___x_619_;
goto v_reusejp_621_;
}
else
{
lean_object* v_reuseFailAlloc_623_; 
v_reuseFailAlloc_623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_623_, 0, v_a_617_);
v___x_622_ = v_reuseFailAlloc_623_;
goto v_reusejp_621_;
}
v_reusejp_621_:
{
return v___x_622_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_627_; lean_object* v___x_629_; uint8_t v_isShared_630_; uint8_t v_isSharedCheck_634_; 
lean_dec_ref(v_subgoals_573_);
v_a_627_ = lean_ctor_get(v___x_584_, 0);
v_isSharedCheck_634_ = !lean_is_exclusive(v___x_584_);
if (v_isSharedCheck_634_ == 0)
{
v___x_629_ = v___x_584_;
v_isShared_630_ = v_isSharedCheck_634_;
goto v_resetjp_628_;
}
else
{
lean_inc(v_a_627_);
lean_dec(v___x_584_);
v___x_629_ = lean_box(0);
v_isShared_630_ = v_isSharedCheck_634_;
goto v_resetjp_628_;
}
v_resetjp_628_:
{
lean_object* v___x_632_; 
if (v_isShared_630_ == 0)
{
v___x_632_ = v___x_629_;
goto v_reusejp_631_;
}
else
{
lean_object* v_reuseFailAlloc_633_; 
v_reuseFailAlloc_633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_633_, 0, v_a_627_);
v___x_632_ = v_reuseFailAlloc_633_;
goto v_reusejp_631_;
}
v_reusejp_631_:
{
return v___x_632_;
}
}
}
}
v___jp_635_:
{
lean_object* v___x_652_; 
v___x_652_ = l_Lean_Meta_introNCore(v___y_636_, v___y_646_, v___y_650_, v___y_651_, v___y_637_, v___y_639_, v___y_643_, v___y_638_, v___y_645_);
if (lean_obj_tag(v___x_652_) == 0)
{
lean_object* v_a_653_; lean_object* v_fst_654_; lean_object* v_snd_655_; lean_object* v___x_656_; lean_object* v___x_657_; 
v_a_653_ = lean_ctor_get(v___x_652_, 0);
lean_inc(v_a_653_);
lean_dec_ref(v___x_652_);
v_fst_654_ = lean_ctor_get(v_a_653_, 0);
lean_inc(v_fst_654_);
v_snd_655_ = lean_ctor_get(v_a_653_, 1);
lean_inc(v_snd_655_);
lean_dec(v_a_653_);
v___x_656_ = lean_box(0);
v___x_657_ = l_Lean_Meta_introNCore(v_snd_655_, v___y_644_, v___x_656_, v___y_637_, v___y_640_, v___y_639_, v___y_643_, v___y_638_, v___y_645_);
if (lean_obj_tag(v___x_657_) == 0)
{
lean_object* v_a_658_; lean_object* v_fst_659_; lean_object* v_snd_660_; lean_object* v___x_661_; size_t v_sz_662_; size_t v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; 
v_a_658_ = lean_ctor_get(v___x_657_, 0);
lean_inc(v_a_658_);
lean_dec_ref(v___x_657_);
v_fst_659_ = lean_ctor_get(v_a_658_, 0);
lean_inc(v_fst_659_);
v_snd_660_ = lean_ctor_get(v_a_658_, 1);
lean_inc(v_snd_660_);
lean_dec(v_a_658_);
lean_inc(v_baseSubst_565_);
lean_inc(v___y_647_);
v___x_661_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__2___redArg(v___y_649_, v_reverted_562_, v_fst_659_, v___y_647_, v___y_647_, v_baseSubst_565_);
lean_dec(v___y_647_);
lean_dec(v_fst_659_);
lean_dec(v___y_649_);
v_sz_662_ = lean_array_size(v_fst_654_);
v___x_663_ = ((size_t)0ULL);
v___x_664_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__3(v_sz_662_, v___x_663_, v_fst_654_);
v___x_665_ = lean_nat_add(v_pos_568_, v___y_641_);
lean_dec(v_pos_568_);
v___x_666_ = lean_nat_add(v_minorIdx_569_, v___y_641_);
lean_dec(v_minorIdx_569_);
v___x_667_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_667_, 0, v_snd_660_);
lean_ctor_set(v___x_667_, 1, v___x_664_);
lean_ctor_set(v___x_667_, 2, v___x_661_);
v___x_668_ = lean_array_push(v_subgoals_573_, v___x_667_);
v_pos_568_ = v___x_665_;
v_minorIdx_569_ = v___x_666_;
v_recursor_570_ = v___y_642_;
v_recursorType_571_ = v___y_648_;
v_subgoals_573_ = v___x_668_;
v_a_574_ = v___y_639_;
v_a_575_ = v___y_643_;
v_a_576_ = v___y_638_;
v_a_577_ = v___y_645_;
goto _start;
}
else
{
lean_object* v_a_670_; lean_object* v___x_672_; uint8_t v_isShared_673_; uint8_t v_isSharedCheck_677_; 
lean_dec(v_fst_654_);
lean_dec(v___y_649_);
lean_dec_ref(v___y_648_);
lean_dec(v___y_647_);
lean_dec_ref(v___y_642_);
lean_dec_ref(v_subgoals_573_);
lean_dec(v_minorIdx_569_);
lean_dec(v_pos_568_);
lean_dec(v_baseSubst_565_);
lean_dec_ref(v_major_563_);
lean_dec(v_mvarId_559_);
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
lean_dec(v___y_649_);
lean_dec_ref(v___y_648_);
lean_dec(v___y_647_);
lean_dec(v___y_644_);
lean_dec_ref(v___y_642_);
lean_dec_ref(v_subgoals_573_);
lean_dec(v_minorIdx_569_);
lean_dec(v_pos_568_);
lean_dec(v_baseSubst_565_);
lean_dec_ref(v_major_563_);
lean_dec(v_mvarId_559_);
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
v___jp_686_:
{
lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; 
v___x_702_ = l_Lean_Expr_mvarId_x21(v___y_693_);
lean_dec_ref(v___y_693_);
v___x_703_ = l_Lean_Expr_fvarId_x21(v_major_563_);
v___x_704_ = l_Lean_MVarId_tryClear(v___x_702_, v___x_703_, v___y_698_, v___y_699_, v___y_700_, v___y_701_);
if (lean_obj_tag(v___x_704_) == 0)
{
uint8_t v_explicit_705_; 
v_explicit_705_ = lean_ctor_get_uint8(v___y_697_, sizeof(void*)*1);
if (v_explicit_705_ == 0)
{
lean_object* v_a_706_; lean_object* v_varNames_707_; 
v_a_706_ = lean_ctor_get(v___x_704_, 0);
lean_inc(v_a_706_);
lean_dec_ref(v___x_704_);
v_varNames_707_ = lean_ctor_get(v___y_697_, 0);
lean_inc(v_varNames_707_);
lean_dec_ref(v___y_697_);
v___y_636_ = v_a_706_;
v___y_637_ = v___y_688_;
v___y_638_ = v___y_700_;
v___y_639_ = v___y_698_;
v___y_640_ = v___y_691_;
v___y_641_ = v___y_692_;
v___y_642_ = v___y_695_;
v___y_643_ = v___y_699_;
v___y_644_ = v___y_687_;
v___y_645_ = v___y_701_;
v___y_646_ = v___y_690_;
v___y_647_ = v___y_689_;
v___y_648_ = v___y_694_;
v___y_649_ = v___y_696_;
v___y_650_ = v_varNames_707_;
v___y_651_ = v___y_691_;
goto v___jp_635_;
}
else
{
lean_object* v_a_708_; lean_object* v_varNames_709_; 
v_a_708_ = lean_ctor_get(v___x_704_, 0);
lean_inc(v_a_708_);
lean_dec_ref(v___x_704_);
v_varNames_709_ = lean_ctor_get(v___y_697_, 0);
lean_inc(v_varNames_709_);
lean_dec_ref(v___y_697_);
v___y_636_ = v_a_708_;
v___y_637_ = v___y_688_;
v___y_638_ = v___y_700_;
v___y_639_ = v___y_698_;
v___y_640_ = v___y_691_;
v___y_641_ = v___y_692_;
v___y_642_ = v___y_695_;
v___y_643_ = v___y_699_;
v___y_644_ = v___y_687_;
v___y_645_ = v___y_701_;
v___y_646_ = v___y_690_;
v___y_647_ = v___y_689_;
v___y_648_ = v___y_694_;
v___y_649_ = v___y_696_;
v___y_650_ = v_varNames_709_;
v___y_651_ = v___y_688_;
goto v___jp_635_;
}
}
else
{
lean_object* v_a_710_; lean_object* v___x_712_; uint8_t v_isShared_713_; uint8_t v_isSharedCheck_717_; 
lean_dec_ref(v___y_697_);
lean_dec(v___y_696_);
lean_dec_ref(v___y_695_);
lean_dec_ref(v___y_694_);
lean_dec(v___y_690_);
lean_dec(v___y_689_);
lean_dec(v___y_687_);
lean_dec_ref(v_subgoals_573_);
lean_dec(v_minorIdx_569_);
lean_dec(v_pos_568_);
lean_dec(v_baseSubst_565_);
lean_dec_ref(v_major_563_);
lean_dec(v_mvarId_559_);
v_a_710_ = lean_ctor_get(v___x_704_, 0);
v_isSharedCheck_717_ = !lean_is_exclusive(v___x_704_);
if (v_isSharedCheck_717_ == 0)
{
v___x_712_ = v___x_704_;
v_isShared_713_ = v_isSharedCheck_717_;
goto v_resetjp_711_;
}
else
{
lean_inc(v_a_710_);
lean_dec(v___x_704_);
v___x_712_ = lean_box(0);
v_isShared_713_ = v_isSharedCheck_717_;
goto v_resetjp_711_;
}
v_resetjp_711_:
{
lean_object* v___x_715_; 
if (v_isShared_713_ == 0)
{
v___x_715_ = v___x_712_;
goto v_reusejp_714_;
}
else
{
lean_object* v_reuseFailAlloc_716_; 
v_reuseFailAlloc_716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_716_, 0, v_a_710_);
v___x_715_ = v_reuseFailAlloc_716_;
goto v_reusejp_714_;
}
v_reusejp_714_:
{
return v___x_715_;
}
}
}
}
v___jp_718_:
{
lean_object* v___x_723_; 
lean_inc(v_mvarId_559_);
v___x_723_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTypeBody(v_mvarId_559_, v_snd_722_, v_major_563_, v_a_574_, v_a_575_, v_a_576_, v_a_577_);
if (lean_obj_tag(v___x_723_) == 0)
{
lean_object* v_a_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; 
v_a_724_ = lean_ctor_get(v___x_723_, 0);
lean_inc(v_a_724_);
lean_dec_ref(v___x_723_);
lean_inc_ref(v_major_563_);
v___x_725_ = l_Lean_Expr_app___override(v_fst_721_, v_major_563_);
v___x_726_ = lean_unsigned_to_nat(1u);
v___x_727_ = lean_nat_add(v_pos_568_, v___x_726_);
lean_dec(v_pos_568_);
v___x_728_ = lean_nat_add(v___x_727_, v___y_719_);
lean_dec(v___y_719_);
lean_dec(v___x_727_);
v_pos_568_ = v___x_728_;
v_recursor_570_ = v___x_725_;
v_recursorType_571_ = v_a_724_;
v_consumedMajor_572_ = v___y_720_;
goto _start;
}
else
{
lean_object* v_a_730_; lean_object* v___x_732_; uint8_t v_isShared_733_; uint8_t v_isSharedCheck_737_; 
lean_dec_ref(v_fst_721_);
lean_dec(v___y_719_);
lean_dec_ref(v_subgoals_573_);
lean_dec(v_minorIdx_569_);
lean_dec(v_pos_568_);
lean_dec(v_baseSubst_565_);
lean_dec_ref(v_major_563_);
lean_dec(v_mvarId_559_);
v_a_730_ = lean_ctor_get(v___x_723_, 0);
v_isSharedCheck_737_ = !lean_is_exclusive(v___x_723_);
if (v_isSharedCheck_737_ == 0)
{
v___x_732_ = v___x_723_;
v_isShared_733_ = v_isSharedCheck_737_;
goto v_resetjp_731_;
}
else
{
lean_inc(v_a_730_);
lean_dec(v___x_723_);
v___x_732_ = lean_box(0);
v_isShared_733_ = v_isSharedCheck_737_;
goto v_resetjp_731_;
}
v_resetjp_731_:
{
lean_object* v___x_735_; 
if (v_isShared_733_ == 0)
{
v___x_735_ = v___x_732_;
goto v_reusejp_734_;
}
else
{
lean_object* v_reuseFailAlloc_736_; 
v_reuseFailAlloc_736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_736_, 0, v_a_730_);
v___x_735_ = v_reuseFailAlloc_736_;
goto v_reusejp_734_;
}
v_reusejp_734_:
{
return v___x_735_;
}
}
}
}
v___jp_738_:
{
if (lean_obj_tag(v___y_741_) == 0)
{
lean_object* v_a_742_; lean_object* v_fst_743_; lean_object* v_snd_744_; 
v_a_742_ = lean_ctor_get(v___y_741_, 0);
lean_inc(v_a_742_);
lean_dec_ref(v___y_741_);
v_fst_743_ = lean_ctor_get(v_a_742_, 0);
lean_inc(v_fst_743_);
v_snd_744_ = lean_ctor_get(v_a_742_, 1);
lean_inc(v_snd_744_);
lean_dec(v_a_742_);
v___y_719_ = v___y_739_;
v___y_720_ = v___y_740_;
v_fst_721_ = v_fst_743_;
v_snd_722_ = v_snd_744_;
goto v___jp_718_;
}
else
{
lean_object* v_a_745_; lean_object* v___x_747_; uint8_t v_isShared_748_; uint8_t v_isSharedCheck_752_; 
lean_dec(v___y_739_);
lean_dec_ref(v_subgoals_573_);
lean_dec(v_minorIdx_569_);
lean_dec(v_pos_568_);
lean_dec(v_baseSubst_565_);
lean_dec_ref(v_major_563_);
lean_dec(v_mvarId_559_);
v_a_745_ = lean_ctor_get(v___y_741_, 0);
v_isSharedCheck_752_ = !lean_is_exclusive(v___y_741_);
if (v_isSharedCheck_752_ == 0)
{
v___x_747_ = v___y_741_;
v_isShared_748_ = v_isSharedCheck_752_;
goto v_resetjp_746_;
}
else
{
lean_inc(v_a_745_);
lean_dec(v___y_741_);
v___x_747_ = lean_box(0);
v_isShared_748_ = v_isSharedCheck_752_;
goto v_resetjp_746_;
}
v_resetjp_746_:
{
lean_object* v___x_750_; 
if (v_isShared_748_ == 0)
{
v___x_750_ = v___x_747_;
goto v_reusejp_749_;
}
else
{
lean_object* v_reuseFailAlloc_751_; 
v_reuseFailAlloc_751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_751_, 0, v_a_745_);
v___x_750_ = v_reuseFailAlloc_751_;
goto v_reusejp_749_;
}
v_reusejp_749_:
{
return v___x_750_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___boxed(lean_object** _args){
lean_object* v_mvarId_999_ = _args[0];
lean_object* v_givenNames_1000_ = _args[1];
lean_object* v_recursorInfo_1001_ = _args[2];
lean_object* v_reverted_1002_ = _args[3];
lean_object* v_major_1003_ = _args[4];
lean_object* v_indices_1004_ = _args[5];
lean_object* v_baseSubst_1005_ = _args[6];
lean_object* v_initialArity_1006_ = _args[7];
lean_object* v_numMinors_1007_ = _args[8];
lean_object* v_pos_1008_ = _args[9];
lean_object* v_minorIdx_1009_ = _args[10];
lean_object* v_recursor_1010_ = _args[11];
lean_object* v_recursorType_1011_ = _args[12];
lean_object* v_consumedMajor_1012_ = _args[13];
lean_object* v_subgoals_1013_ = _args[14];
lean_object* v_a_1014_ = _args[15];
lean_object* v_a_1015_ = _args[16];
lean_object* v_a_1016_ = _args[17];
lean_object* v_a_1017_ = _args[18];
lean_object* v_a_1018_ = _args[19];
_start:
{
uint8_t v_consumedMajor_boxed_1019_; lean_object* v_res_1020_; 
v_consumedMajor_boxed_1019_ = lean_unbox(v_consumedMajor_1012_);
v_res_1020_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop(v_mvarId_999_, v_givenNames_1000_, v_recursorInfo_1001_, v_reverted_1002_, v_major_1003_, v_indices_1004_, v_baseSubst_1005_, v_initialArity_1006_, v_numMinors_1007_, v_pos_1008_, v_minorIdx_1009_, v_recursor_1010_, v_recursorType_1011_, v_consumedMajor_boxed_1019_, v_subgoals_1013_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_);
lean_dec(v_a_1017_);
lean_dec_ref(v_a_1016_);
lean_dec(v_a_1015_);
lean_dec_ref(v_a_1014_);
lean_dec(v_numMinors_1007_);
lean_dec(v_initialArity_1006_);
lean_dec_ref(v_indices_1004_);
lean_dec_ref(v_reverted_1002_);
lean_dec_ref(v_recursorInfo_1001_);
lean_dec_ref(v_givenNames_1000_);
return v_res_1020_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0(lean_object* v_mvarId_1021_, lean_object* v_val_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_){
_start:
{
lean_object* v___x_1028_; 
v___x_1028_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0___redArg(v_mvarId_1021_, v_val_1022_, v___y_1024_);
return v___x_1028_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0___boxed(lean_object* v_mvarId_1029_, lean_object* v_val_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_){
_start:
{
lean_object* v_res_1036_; 
v_res_1036_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0(v_mvarId_1029_, v_val_1030_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_);
lean_dec(v___y_1034_);
lean_dec_ref(v___y_1033_);
lean_dec(v___y_1032_);
lean_dec_ref(v___y_1031_);
return v_res_1036_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__2(lean_object* v___x_1037_, lean_object* v_reverted_1038_, lean_object* v_fst_1039_, lean_object* v_n_1040_, lean_object* v_j_1041_, lean_object* v_a_1042_, lean_object* v_a_1043_){
_start:
{
lean_object* v___x_1044_; 
v___x_1044_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__2___redArg(v___x_1037_, v_reverted_1038_, v_fst_1039_, v_n_1040_, v_j_1041_, v_a_1043_);
return v___x_1044_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__2___boxed(lean_object* v___x_1045_, lean_object* v_reverted_1046_, lean_object* v_fst_1047_, lean_object* v_n_1048_, lean_object* v_j_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_){
_start:
{
lean_object* v_res_1052_; 
v_res_1052_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__2(v___x_1045_, v_reverted_1046_, v_fst_1047_, v_n_1048_, v_j_1049_, v_a_1050_, v_a_1051_);
lean_dec(v_n_1048_);
lean_dec_ref(v_fst_1047_);
lean_dec_ref(v_reverted_1046_);
lean_dec(v___x_1045_);
return v_res_1052_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0(lean_object* v_00_u03b2_1053_, lean_object* v_x_1054_, lean_object* v_x_1055_, lean_object* v_x_1056_){
_start:
{
lean_object* v___x_1057_; 
v___x_1057_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0___redArg(v_x_1054_, v_x_1055_, v_x_1056_);
return v___x_1057_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1058_, lean_object* v_x_1059_, size_t v_x_1060_, size_t v_x_1061_, lean_object* v_x_1062_, lean_object* v_x_1063_){
_start:
{
lean_object* v___x_1064_; 
v___x_1064_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2___redArg(v_x_1059_, v_x_1060_, v_x_1061_, v_x_1062_, v_x_1063_);
return v___x_1064_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1065_, lean_object* v_x_1066_, lean_object* v_x_1067_, lean_object* v_x_1068_, lean_object* v_x_1069_, lean_object* v_x_1070_){
_start:
{
size_t v_x_11494__boxed_1071_; size_t v_x_11495__boxed_1072_; lean_object* v_res_1073_; 
v_x_11494__boxed_1071_ = lean_unbox_usize(v_x_1067_);
lean_dec(v_x_1067_);
v_x_11495__boxed_1072_ = lean_unbox_usize(v_x_1068_);
lean_dec(v_x_1068_);
v_res_1073_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2(v_00_u03b2_1065_, v_x_1066_, v_x_11494__boxed_1071_, v_x_11495__boxed_1072_, v_x_1069_, v_x_1070_);
return v_res_1073_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__8(lean_object* v_00_u03b2_1074_, lean_object* v_n_1075_, lean_object* v_k_1076_, lean_object* v_v_1077_){
_start:
{
lean_object* v___x_1078_; 
v___x_1078_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__8___redArg(v_n_1075_, v_k_1076_, v_v_1077_);
return v___x_1078_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__9(lean_object* v_00_u03b2_1079_, size_t v_depth_1080_, lean_object* v_keys_1081_, lean_object* v_vals_1082_, lean_object* v_heq_1083_, lean_object* v_i_1084_, lean_object* v_entries_1085_){
_start:
{
lean_object* v___x_1086_; 
v___x_1086_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__9___redArg(v_depth_1080_, v_keys_1081_, v_vals_1082_, v_i_1084_, v_entries_1085_);
return v___x_1086_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__9___boxed(lean_object* v_00_u03b2_1087_, lean_object* v_depth_1088_, lean_object* v_keys_1089_, lean_object* v_vals_1090_, lean_object* v_heq_1091_, lean_object* v_i_1092_, lean_object* v_entries_1093_){
_start:
{
size_t v_depth_boxed_1094_; lean_object* v_res_1095_; 
v_depth_boxed_1094_ = lean_unbox_usize(v_depth_1088_);
lean_dec(v_depth_1088_);
v_res_1095_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__9(v_00_u03b2_1087_, v_depth_boxed_1094_, v_keys_1089_, v_vals_1090_, v_heq_1091_, v_i_1092_, v_entries_1093_);
lean_dec_ref(v_vals_1090_);
lean_dec_ref(v_keys_1089_);
return v_res_1095_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__8_spec__9(lean_object* v_00_u03b2_1096_, lean_object* v_x_1097_, lean_object* v_x_1098_, lean_object* v_x_1099_, lean_object* v_x_1100_){
_start:
{
lean_object* v___x_1101_; 
v___x_1101_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__8_spec__9___redArg(v_x_1097_, v_x_1098_, v_x_1099_, v_x_1100_);
return v___x_1101_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize(lean_object* v_mvarId_1104_, lean_object* v_givenNames_1105_, lean_object* v_recursorInfo_1106_, lean_object* v_reverted_1107_, lean_object* v_major_1108_, lean_object* v_indices_1109_, lean_object* v_baseSubst_1110_, lean_object* v_recursor_1111_, lean_object* v_a_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_){
_start:
{
lean_object* v___x_1117_; 
lean_inc(v_mvarId_1104_);
v___x_1117_ = l_Lean_MVarId_getType(v_mvarId_1104_, v_a_1112_, v_a_1113_, v_a_1114_, v_a_1115_);
if (lean_obj_tag(v___x_1117_) == 0)
{
lean_object* v_a_1118_; lean_object* v___x_1119_; 
v_a_1118_ = lean_ctor_get(v___x_1117_, 0);
lean_inc(v_a_1118_);
lean_dec_ref(v___x_1117_);
lean_inc(v_a_1115_);
lean_inc_ref(v_a_1114_);
lean_inc(v_a_1113_);
lean_inc_ref(v_a_1112_);
lean_inc_ref(v_recursor_1111_);
v___x_1119_ = lean_infer_type(v_recursor_1111_, v_a_1112_, v_a_1113_, v_a_1114_, v_a_1115_);
if (lean_obj_tag(v___x_1119_) == 0)
{
lean_object* v_a_1120_; lean_object* v_paramsPos_1121_; lean_object* v_produceMotive_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; uint8_t v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; 
v_a_1120_ = lean_ctor_get(v___x_1119_, 0);
lean_inc(v_a_1120_);
lean_dec_ref(v___x_1119_);
v_paramsPos_1121_ = lean_ctor_get(v_recursorInfo_1106_, 5);
v_produceMotive_1122_ = lean_ctor_get(v_recursorInfo_1106_, 7);
v___x_1123_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTargetArity(v_a_1118_);
v___x_1124_ = l_List_lengthTR___redArg(v_produceMotive_1122_);
v___x_1125_ = l_List_lengthTR___redArg(v_paramsPos_1121_);
v___x_1126_ = lean_unsigned_to_nat(1u);
v___x_1127_ = lean_nat_add(v___x_1125_, v___x_1126_);
lean_dec(v___x_1125_);
v___x_1128_ = lean_unsigned_to_nat(0u);
v___x_1129_ = 0;
v___x_1130_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize___closed__0));
v___x_1131_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop(v_mvarId_1104_, v_givenNames_1105_, v_recursorInfo_1106_, v_reverted_1107_, v_major_1108_, v_indices_1109_, v_baseSubst_1110_, v___x_1123_, v___x_1124_, v___x_1127_, v___x_1128_, v_recursor_1111_, v_a_1120_, v___x_1129_, v___x_1130_, v_a_1112_, v_a_1113_, v_a_1114_, v_a_1115_);
lean_dec(v___x_1124_);
lean_dec(v___x_1123_);
return v___x_1131_;
}
else
{
lean_object* v_a_1132_; lean_object* v___x_1134_; uint8_t v_isShared_1135_; uint8_t v_isSharedCheck_1139_; 
lean_dec(v_a_1118_);
lean_dec_ref(v_recursor_1111_);
lean_dec(v_baseSubst_1110_);
lean_dec_ref(v_major_1108_);
lean_dec(v_mvarId_1104_);
v_a_1132_ = lean_ctor_get(v___x_1119_, 0);
v_isSharedCheck_1139_ = !lean_is_exclusive(v___x_1119_);
if (v_isSharedCheck_1139_ == 0)
{
v___x_1134_ = v___x_1119_;
v_isShared_1135_ = v_isSharedCheck_1139_;
goto v_resetjp_1133_;
}
else
{
lean_inc(v_a_1132_);
lean_dec(v___x_1119_);
v___x_1134_ = lean_box(0);
v_isShared_1135_ = v_isSharedCheck_1139_;
goto v_resetjp_1133_;
}
v_resetjp_1133_:
{
lean_object* v___x_1137_; 
if (v_isShared_1135_ == 0)
{
v___x_1137_ = v___x_1134_;
goto v_reusejp_1136_;
}
else
{
lean_object* v_reuseFailAlloc_1138_; 
v_reuseFailAlloc_1138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1138_, 0, v_a_1132_);
v___x_1137_ = v_reuseFailAlloc_1138_;
goto v_reusejp_1136_;
}
v_reusejp_1136_:
{
return v___x_1137_;
}
}
}
}
else
{
lean_object* v_a_1140_; lean_object* v___x_1142_; uint8_t v_isShared_1143_; uint8_t v_isSharedCheck_1147_; 
lean_dec_ref(v_recursor_1111_);
lean_dec(v_baseSubst_1110_);
lean_dec_ref(v_major_1108_);
lean_dec(v_mvarId_1104_);
v_a_1140_ = lean_ctor_get(v___x_1117_, 0);
v_isSharedCheck_1147_ = !lean_is_exclusive(v___x_1117_);
if (v_isSharedCheck_1147_ == 0)
{
v___x_1142_ = v___x_1117_;
v_isShared_1143_ = v_isSharedCheck_1147_;
goto v_resetjp_1141_;
}
else
{
lean_inc(v_a_1140_);
lean_dec(v___x_1117_);
v___x_1142_ = lean_box(0);
v_isShared_1143_ = v_isSharedCheck_1147_;
goto v_resetjp_1141_;
}
v_resetjp_1141_:
{
lean_object* v___x_1145_; 
if (v_isShared_1143_ == 0)
{
v___x_1145_ = v___x_1142_;
goto v_reusejp_1144_;
}
else
{
lean_object* v_reuseFailAlloc_1146_; 
v_reuseFailAlloc_1146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1146_, 0, v_a_1140_);
v___x_1145_ = v_reuseFailAlloc_1146_;
goto v_reusejp_1144_;
}
v_reusejp_1144_:
{
return v___x_1145_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize___boxed(lean_object* v_mvarId_1148_, lean_object* v_givenNames_1149_, lean_object* v_recursorInfo_1150_, lean_object* v_reverted_1151_, lean_object* v_major_1152_, lean_object* v_indices_1153_, lean_object* v_baseSubst_1154_, lean_object* v_recursor_1155_, lean_object* v_a_1156_, lean_object* v_a_1157_, lean_object* v_a_1158_, lean_object* v_a_1159_, lean_object* v_a_1160_){
_start:
{
lean_object* v_res_1161_; 
v_res_1161_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize(v_mvarId_1148_, v_givenNames_1149_, v_recursorInfo_1150_, v_reverted_1151_, v_major_1152_, v_indices_1153_, v_baseSubst_1154_, v_recursor_1155_, v_a_1156_, v_a_1157_, v_a_1158_, v_a_1159_);
lean_dec(v_a_1159_);
lean_dec_ref(v_a_1158_);
lean_dec(v_a_1157_);
lean_dec_ref(v_a_1156_);
lean_dec_ref(v_indices_1153_);
lean_dec_ref(v_reverted_1151_);
lean_dec_ref(v_recursorInfo_1150_);
lean_dec_ref(v_givenNames_1149_);
return v_res_1161_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg___closed__1(void){
_start:
{
lean_object* v___x_1163_; lean_object* v___x_1164_; 
v___x_1163_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg___closed__0));
v___x_1164_ = l_Lean_stringToMessageData(v___x_1163_);
return v___x_1164_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg(lean_object* v_tacticName_1165_, lean_object* v_mvarId_1166_, lean_object* v_majorType_1167_, lean_object* v_a_1168_, lean_object* v_a_1169_, lean_object* v_a_1170_, lean_object* v_a_1171_){
_start:
{
lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; 
v___x_1173_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg___closed__1, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg___closed__1);
v___x_1174_ = l_Lean_indentExpr(v_majorType_1167_);
v___x_1175_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1175_, 0, v___x_1173_);
lean_ctor_set(v___x_1175_, 1, v___x_1174_);
v___x_1176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1176_, 0, v___x_1175_);
v___x_1177_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1165_, v_mvarId_1166_, v___x_1176_, v_a_1168_, v_a_1169_, v_a_1170_, v_a_1171_);
return v___x_1177_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg___boxed(lean_object* v_tacticName_1178_, lean_object* v_mvarId_1179_, lean_object* v_majorType_1180_, lean_object* v_a_1181_, lean_object* v_a_1182_, lean_object* v_a_1183_, lean_object* v_a_1184_, lean_object* v_a_1185_){
_start:
{
lean_object* v_res_1186_; 
v_res_1186_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg(v_tacticName_1178_, v_mvarId_1179_, v_majorType_1180_, v_a_1181_, v_a_1182_, v_a_1183_, v_a_1184_);
lean_dec(v_a_1184_);
lean_dec_ref(v_a_1183_);
lean_dec(v_a_1182_);
lean_dec_ref(v_a_1181_);
return v_res_1186_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType(lean_object* v_00_u03b1_1187_, lean_object* v_tacticName_1188_, lean_object* v_mvarId_1189_, lean_object* v_majorType_1190_, lean_object* v_a_1191_, lean_object* v_a_1192_, lean_object* v_a_1193_, lean_object* v_a_1194_){
_start:
{
lean_object* v___x_1196_; 
v___x_1196_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg(v_tacticName_1188_, v_mvarId_1189_, v_majorType_1190_, v_a_1191_, v_a_1192_, v_a_1193_, v_a_1194_);
return v___x_1196_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___boxed(lean_object* v_00_u03b1_1197_, lean_object* v_tacticName_1198_, lean_object* v_mvarId_1199_, lean_object* v_majorType_1200_, lean_object* v_a_1201_, lean_object* v_a_1202_, lean_object* v_a_1203_, lean_object* v_a_1204_, lean_object* v_a_1205_){
_start:
{
lean_object* v_res_1206_; 
v_res_1206_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType(v_00_u03b1_1197_, v_tacticName_1198_, v_mvarId_1199_, v_majorType_1200_, v_a_1201_, v_a_1202_, v_a_1203_, v_a_1204_);
lean_dec(v_a_1204_);
lean_dec_ref(v_a_1203_);
lean_dec(v_a_1202_);
lean_dec_ref(v_a_1201_);
return v_res_1206_;
}
}
LEAN_EXPORT uint8_t l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___lam__0(lean_object* v_fvarId_1207_, lean_object* v_x_1208_){
_start:
{
uint8_t v___x_1209_; 
v___x_1209_ = l_Lean_instBEqFVarId_beq(v_fvarId_1207_, v_x_1208_);
return v___x_1209_;
}
}
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___lam__0___boxed(lean_object* v_fvarId_1210_, lean_object* v_x_1211_){
_start:
{
uint8_t v_res_1212_; lean_object* v_r_1213_; 
v_res_1212_ = l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___lam__0(v_fvarId_1210_, v_x_1211_);
lean_dec(v_x_1211_);
lean_dec(v_fvarId_1210_);
v_r_1213_ = lean_box(v_res_1212_);
return v_r_1213_;
}
}
LEAN_EXPORT uint8_t l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___lam__1(lean_object* v_x_1214_){
_start:
{
uint8_t v___x_1215_; 
v___x_1215_ = 0;
return v___x_1215_;
}
}
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___lam__1___boxed(lean_object* v_x_1216_){
_start:
{
uint8_t v_res_1217_; lean_object* v_r_1218_; 
v_res_1217_ = l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___lam__1(v_x_1216_);
lean_dec(v_x_1216_);
v_r_1218_ = lean_box(v_res_1217_);
return v_r_1218_;
}
}
static lean_object* _init_l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; 
v___x_1220_ = lean_box(0);
v___x_1221_ = lean_unsigned_to_nat(16u);
v___x_1222_ = lean_mk_array(v___x_1221_, v___x_1220_);
return v___x_1222_;
}
}
static lean_object* _init_l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; 
v___x_1223_ = lean_obj_once(&l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__1, &l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__1_once, _init_l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__1);
v___x_1224_ = lean_unsigned_to_nat(0u);
v___x_1225_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1225_, 0, v___x_1224_);
lean_ctor_set(v___x_1225_, 1, v___x_1223_);
return v___x_1225_;
}
}
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg(lean_object* v_localDecl_1226_, lean_object* v_fvarId_1227_, uint8_t v_generalizeNondepLet_1228_, lean_object* v___y_1229_){
_start:
{
uint8_t v_fst_1232_; lean_object* v_snd_1233_; lean_object* v___y_1252_; lean_object* v___f_1256_; lean_object* v___f_1257_; 
v___f_1256_ = lean_alloc_closure((void*)(l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1256_, 0, v_fvarId_1227_);
v___f_1257_ = ((lean_object*)(l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__0));
if (lean_obj_tag(v_localDecl_1226_) == 0)
{
lean_object* v_type_1258_; lean_object* v___x_1259_; uint8_t v_fst_1261_; lean_object* v_mctx_1262_; lean_object* v___y_1280_; lean_object* v_mctx_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; uint8_t v___x_1288_; 
v_type_1258_ = lean_ctor_get(v_localDecl_1226_, 3);
lean_inc_ref(v_type_1258_);
lean_dec_ref(v_localDecl_1226_);
v___x_1259_ = lean_st_ref_get(v___y_1229_);
v_mctx_1285_ = lean_ctor_get(v___x_1259_, 0);
lean_inc_ref_n(v_mctx_1285_, 2);
lean_dec(v___x_1259_);
v___x_1286_ = lean_obj_once(&l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__2, &l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__2_once, _init_l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__2);
v___x_1287_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1287_, 0, v___x_1286_);
lean_ctor_set(v___x_1287_, 1, v_mctx_1285_);
v___x_1288_ = l_Lean_Expr_hasFVar(v_type_1258_);
if (v___x_1288_ == 0)
{
uint8_t v___x_1289_; 
v___x_1289_ = l_Lean_Expr_hasMVar(v_type_1258_);
if (v___x_1289_ == 0)
{
lean_dec_ref(v___x_1287_);
lean_dec_ref(v_type_1258_);
lean_dec_ref(v___f_1256_);
v_fst_1261_ = v___x_1289_;
v_mctx_1262_ = v_mctx_1285_;
goto v___jp_1260_;
}
else
{
lean_object* v___x_1290_; 
lean_dec_ref(v_mctx_1285_);
v___x_1290_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1256_, v___f_1257_, v_type_1258_, v___x_1287_);
v___y_1280_ = v___x_1290_;
goto v___jp_1279_;
}
}
else
{
lean_object* v___x_1291_; 
lean_dec_ref(v_mctx_1285_);
v___x_1291_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1256_, v___f_1257_, v_type_1258_, v___x_1287_);
v___y_1280_ = v___x_1291_;
goto v___jp_1279_;
}
v___jp_1260_:
{
lean_object* v___x_1263_; lean_object* v_cache_1264_; lean_object* v_zetaDeltaFVarIds_1265_; lean_object* v_postponed_1266_; lean_object* v_diag_1267_; lean_object* v___x_1269_; uint8_t v_isShared_1270_; uint8_t v_isSharedCheck_1277_; 
v___x_1263_ = lean_st_ref_take(v___y_1229_);
v_cache_1264_ = lean_ctor_get(v___x_1263_, 1);
v_zetaDeltaFVarIds_1265_ = lean_ctor_get(v___x_1263_, 2);
v_postponed_1266_ = lean_ctor_get(v___x_1263_, 3);
v_diag_1267_ = lean_ctor_get(v___x_1263_, 4);
v_isSharedCheck_1277_ = !lean_is_exclusive(v___x_1263_);
if (v_isSharedCheck_1277_ == 0)
{
lean_object* v_unused_1278_; 
v_unused_1278_ = lean_ctor_get(v___x_1263_, 0);
lean_dec(v_unused_1278_);
v___x_1269_ = v___x_1263_;
v_isShared_1270_ = v_isSharedCheck_1277_;
goto v_resetjp_1268_;
}
else
{
lean_inc(v_diag_1267_);
lean_inc(v_postponed_1266_);
lean_inc(v_zetaDeltaFVarIds_1265_);
lean_inc(v_cache_1264_);
lean_dec(v___x_1263_);
v___x_1269_ = lean_box(0);
v_isShared_1270_ = v_isSharedCheck_1277_;
goto v_resetjp_1268_;
}
v_resetjp_1268_:
{
lean_object* v___x_1272_; 
if (v_isShared_1270_ == 0)
{
lean_ctor_set(v___x_1269_, 0, v_mctx_1262_);
v___x_1272_ = v___x_1269_;
goto v_reusejp_1271_;
}
else
{
lean_object* v_reuseFailAlloc_1276_; 
v_reuseFailAlloc_1276_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1276_, 0, v_mctx_1262_);
lean_ctor_set(v_reuseFailAlloc_1276_, 1, v_cache_1264_);
lean_ctor_set(v_reuseFailAlloc_1276_, 2, v_zetaDeltaFVarIds_1265_);
lean_ctor_set(v_reuseFailAlloc_1276_, 3, v_postponed_1266_);
lean_ctor_set(v_reuseFailAlloc_1276_, 4, v_diag_1267_);
v___x_1272_ = v_reuseFailAlloc_1276_;
goto v_reusejp_1271_;
}
v_reusejp_1271_:
{
lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; 
v___x_1273_ = lean_st_ref_set(v___y_1229_, v___x_1272_);
v___x_1274_ = lean_box(v_fst_1261_);
v___x_1275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1275_, 0, v___x_1274_);
return v___x_1275_;
}
}
}
v___jp_1279_:
{
lean_object* v_snd_1281_; lean_object* v_fst_1282_; lean_object* v_mctx_1283_; uint8_t v___x_1284_; 
v_snd_1281_ = lean_ctor_get(v___y_1280_, 1);
lean_inc(v_snd_1281_);
v_fst_1282_ = lean_ctor_get(v___y_1280_, 0);
lean_inc(v_fst_1282_);
lean_dec_ref(v___y_1280_);
v_mctx_1283_ = lean_ctor_get(v_snd_1281_, 1);
lean_inc_ref(v_mctx_1283_);
lean_dec(v_snd_1281_);
v___x_1284_ = lean_unbox(v_fst_1282_);
lean_dec(v_fst_1282_);
v_fst_1261_ = v___x_1284_;
v_mctx_1262_ = v_mctx_1283_;
goto v___jp_1260_;
}
}
else
{
lean_object* v_type_1292_; lean_object* v_value_1293_; uint8_t v_nondep_1294_; uint8_t v_fst_1296_; lean_object* v_snd_1297_; lean_object* v___y_1303_; 
v_type_1292_ = lean_ctor_get(v_localDecl_1226_, 3);
lean_inc_ref(v_type_1292_);
v_value_1293_ = lean_ctor_get(v_localDecl_1226_, 4);
lean_inc_ref(v_value_1293_);
v_nondep_1294_ = lean_ctor_get_uint8(v_localDecl_1226_, sizeof(void*)*5);
lean_dec_ref(v_localDecl_1226_);
if (v_generalizeNondepLet_1228_ == 0)
{
goto v___jp_1307_;
}
else
{
if (v_nondep_1294_ == 0)
{
goto v___jp_1307_;
}
else
{
lean_object* v___x_1316_; uint8_t v_fst_1318_; lean_object* v_mctx_1319_; lean_object* v___y_1337_; lean_object* v_mctx_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; uint8_t v___x_1345_; 
lean_dec_ref(v_value_1293_);
v___x_1316_ = lean_st_ref_get(v___y_1229_);
v_mctx_1342_ = lean_ctor_get(v___x_1316_, 0);
lean_inc_ref_n(v_mctx_1342_, 2);
lean_dec(v___x_1316_);
v___x_1343_ = lean_obj_once(&l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__2, &l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__2_once, _init_l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__2);
v___x_1344_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1344_, 0, v___x_1343_);
lean_ctor_set(v___x_1344_, 1, v_mctx_1342_);
v___x_1345_ = l_Lean_Expr_hasFVar(v_type_1292_);
if (v___x_1345_ == 0)
{
uint8_t v___x_1346_; 
v___x_1346_ = l_Lean_Expr_hasMVar(v_type_1292_);
if (v___x_1346_ == 0)
{
lean_dec_ref(v___x_1344_);
lean_dec_ref(v_type_1292_);
lean_dec_ref(v___f_1256_);
v_fst_1318_ = v___x_1346_;
v_mctx_1319_ = v_mctx_1342_;
goto v___jp_1317_;
}
else
{
lean_object* v___x_1347_; 
lean_dec_ref(v_mctx_1342_);
v___x_1347_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1256_, v___f_1257_, v_type_1292_, v___x_1344_);
v___y_1337_ = v___x_1347_;
goto v___jp_1336_;
}
}
else
{
lean_object* v___x_1348_; 
lean_dec_ref(v_mctx_1342_);
v___x_1348_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1256_, v___f_1257_, v_type_1292_, v___x_1344_);
v___y_1337_ = v___x_1348_;
goto v___jp_1336_;
}
v___jp_1317_:
{
lean_object* v___x_1320_; lean_object* v_cache_1321_; lean_object* v_zetaDeltaFVarIds_1322_; lean_object* v_postponed_1323_; lean_object* v_diag_1324_; lean_object* v___x_1326_; uint8_t v_isShared_1327_; uint8_t v_isSharedCheck_1334_; 
v___x_1320_ = lean_st_ref_take(v___y_1229_);
v_cache_1321_ = lean_ctor_get(v___x_1320_, 1);
v_zetaDeltaFVarIds_1322_ = lean_ctor_get(v___x_1320_, 2);
v_postponed_1323_ = lean_ctor_get(v___x_1320_, 3);
v_diag_1324_ = lean_ctor_get(v___x_1320_, 4);
v_isSharedCheck_1334_ = !lean_is_exclusive(v___x_1320_);
if (v_isSharedCheck_1334_ == 0)
{
lean_object* v_unused_1335_; 
v_unused_1335_ = lean_ctor_get(v___x_1320_, 0);
lean_dec(v_unused_1335_);
v___x_1326_ = v___x_1320_;
v_isShared_1327_ = v_isSharedCheck_1334_;
goto v_resetjp_1325_;
}
else
{
lean_inc(v_diag_1324_);
lean_inc(v_postponed_1323_);
lean_inc(v_zetaDeltaFVarIds_1322_);
lean_inc(v_cache_1321_);
lean_dec(v___x_1320_);
v___x_1326_ = lean_box(0);
v_isShared_1327_ = v_isSharedCheck_1334_;
goto v_resetjp_1325_;
}
v_resetjp_1325_:
{
lean_object* v___x_1329_; 
if (v_isShared_1327_ == 0)
{
lean_ctor_set(v___x_1326_, 0, v_mctx_1319_);
v___x_1329_ = v___x_1326_;
goto v_reusejp_1328_;
}
else
{
lean_object* v_reuseFailAlloc_1333_; 
v_reuseFailAlloc_1333_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1333_, 0, v_mctx_1319_);
lean_ctor_set(v_reuseFailAlloc_1333_, 1, v_cache_1321_);
lean_ctor_set(v_reuseFailAlloc_1333_, 2, v_zetaDeltaFVarIds_1322_);
lean_ctor_set(v_reuseFailAlloc_1333_, 3, v_postponed_1323_);
lean_ctor_set(v_reuseFailAlloc_1333_, 4, v_diag_1324_);
v___x_1329_ = v_reuseFailAlloc_1333_;
goto v_reusejp_1328_;
}
v_reusejp_1328_:
{
lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; 
v___x_1330_ = lean_st_ref_set(v___y_1229_, v___x_1329_);
v___x_1331_ = lean_box(v_fst_1318_);
v___x_1332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1332_, 0, v___x_1331_);
return v___x_1332_;
}
}
}
v___jp_1336_:
{
lean_object* v_snd_1338_; lean_object* v_fst_1339_; lean_object* v_mctx_1340_; uint8_t v___x_1341_; 
v_snd_1338_ = lean_ctor_get(v___y_1337_, 1);
lean_inc(v_snd_1338_);
v_fst_1339_ = lean_ctor_get(v___y_1337_, 0);
lean_inc(v_fst_1339_);
lean_dec_ref(v___y_1337_);
v_mctx_1340_ = lean_ctor_get(v_snd_1338_, 1);
lean_inc_ref(v_mctx_1340_);
lean_dec(v_snd_1338_);
v___x_1341_ = lean_unbox(v_fst_1339_);
lean_dec(v_fst_1339_);
v_fst_1318_ = v___x_1341_;
v_mctx_1319_ = v_mctx_1340_;
goto v___jp_1317_;
}
}
}
v___jp_1295_:
{
if (v_fst_1296_ == 0)
{
uint8_t v___x_1298_; 
v___x_1298_ = l_Lean_Expr_hasFVar(v_value_1293_);
if (v___x_1298_ == 0)
{
uint8_t v___x_1299_; 
v___x_1299_ = l_Lean_Expr_hasMVar(v_value_1293_);
if (v___x_1299_ == 0)
{
lean_dec_ref(v_value_1293_);
lean_dec_ref(v___f_1256_);
v_fst_1232_ = v___x_1299_;
v_snd_1233_ = v_snd_1297_;
goto v___jp_1231_;
}
else
{
lean_object* v___x_1300_; 
v___x_1300_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1256_, v___f_1257_, v_value_1293_, v_snd_1297_);
v___y_1252_ = v___x_1300_;
goto v___jp_1251_;
}
}
else
{
lean_object* v___x_1301_; 
v___x_1301_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1256_, v___f_1257_, v_value_1293_, v_snd_1297_);
v___y_1252_ = v___x_1301_;
goto v___jp_1251_;
}
}
else
{
lean_dec_ref(v_value_1293_);
lean_dec_ref(v___f_1256_);
v_fst_1232_ = v_fst_1296_;
v_snd_1233_ = v_snd_1297_;
goto v___jp_1231_;
}
}
v___jp_1302_:
{
lean_object* v_fst_1304_; lean_object* v_snd_1305_; uint8_t v___x_1306_; 
v_fst_1304_ = lean_ctor_get(v___y_1303_, 0);
lean_inc(v_fst_1304_);
v_snd_1305_ = lean_ctor_get(v___y_1303_, 1);
lean_inc(v_snd_1305_);
lean_dec_ref(v___y_1303_);
v___x_1306_ = lean_unbox(v_fst_1304_);
lean_dec(v_fst_1304_);
v_fst_1296_ = v___x_1306_;
v_snd_1297_ = v_snd_1305_;
goto v___jp_1295_;
}
v___jp_1307_:
{
lean_object* v___x_1308_; lean_object* v_mctx_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; uint8_t v___x_1312_; 
v___x_1308_ = lean_st_ref_get(v___y_1229_);
v_mctx_1309_ = lean_ctor_get(v___x_1308_, 0);
lean_inc_ref(v_mctx_1309_);
lean_dec(v___x_1308_);
v___x_1310_ = lean_obj_once(&l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__2, &l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__2_once, _init_l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__2);
v___x_1311_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1311_, 0, v___x_1310_);
lean_ctor_set(v___x_1311_, 1, v_mctx_1309_);
v___x_1312_ = l_Lean_Expr_hasFVar(v_type_1292_);
if (v___x_1312_ == 0)
{
uint8_t v___x_1313_; 
v___x_1313_ = l_Lean_Expr_hasMVar(v_type_1292_);
if (v___x_1313_ == 0)
{
lean_dec_ref(v_type_1292_);
v_fst_1296_ = v___x_1313_;
v_snd_1297_ = v___x_1311_;
goto v___jp_1295_;
}
else
{
lean_object* v___x_1314_; 
lean_inc_ref(v___f_1256_);
v___x_1314_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1256_, v___f_1257_, v_type_1292_, v___x_1311_);
v___y_1303_ = v___x_1314_;
goto v___jp_1302_;
}
}
else
{
lean_object* v___x_1315_; 
lean_inc_ref(v___f_1256_);
v___x_1315_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1256_, v___f_1257_, v_type_1292_, v___x_1311_);
v___y_1303_ = v___x_1315_;
goto v___jp_1302_;
}
}
}
v___jp_1231_:
{
lean_object* v_mctx_1234_; lean_object* v___x_1235_; lean_object* v_cache_1236_; lean_object* v_zetaDeltaFVarIds_1237_; lean_object* v_postponed_1238_; lean_object* v_diag_1239_; lean_object* v___x_1241_; uint8_t v_isShared_1242_; uint8_t v_isSharedCheck_1249_; 
v_mctx_1234_ = lean_ctor_get(v_snd_1233_, 1);
lean_inc_ref(v_mctx_1234_);
lean_dec_ref(v_snd_1233_);
v___x_1235_ = lean_st_ref_take(v___y_1229_);
v_cache_1236_ = lean_ctor_get(v___x_1235_, 1);
v_zetaDeltaFVarIds_1237_ = lean_ctor_get(v___x_1235_, 2);
v_postponed_1238_ = lean_ctor_get(v___x_1235_, 3);
v_diag_1239_ = lean_ctor_get(v___x_1235_, 4);
v_isSharedCheck_1249_ = !lean_is_exclusive(v___x_1235_);
if (v_isSharedCheck_1249_ == 0)
{
lean_object* v_unused_1250_; 
v_unused_1250_ = lean_ctor_get(v___x_1235_, 0);
lean_dec(v_unused_1250_);
v___x_1241_ = v___x_1235_;
v_isShared_1242_ = v_isSharedCheck_1249_;
goto v_resetjp_1240_;
}
else
{
lean_inc(v_diag_1239_);
lean_inc(v_postponed_1238_);
lean_inc(v_zetaDeltaFVarIds_1237_);
lean_inc(v_cache_1236_);
lean_dec(v___x_1235_);
v___x_1241_ = lean_box(0);
v_isShared_1242_ = v_isSharedCheck_1249_;
goto v_resetjp_1240_;
}
v_resetjp_1240_:
{
lean_object* v___x_1244_; 
if (v_isShared_1242_ == 0)
{
lean_ctor_set(v___x_1241_, 0, v_mctx_1234_);
v___x_1244_ = v___x_1241_;
goto v_reusejp_1243_;
}
else
{
lean_object* v_reuseFailAlloc_1248_; 
v_reuseFailAlloc_1248_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1248_, 0, v_mctx_1234_);
lean_ctor_set(v_reuseFailAlloc_1248_, 1, v_cache_1236_);
lean_ctor_set(v_reuseFailAlloc_1248_, 2, v_zetaDeltaFVarIds_1237_);
lean_ctor_set(v_reuseFailAlloc_1248_, 3, v_postponed_1238_);
lean_ctor_set(v_reuseFailAlloc_1248_, 4, v_diag_1239_);
v___x_1244_ = v_reuseFailAlloc_1248_;
goto v_reusejp_1243_;
}
v_reusejp_1243_:
{
lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; 
v___x_1245_ = lean_st_ref_set(v___y_1229_, v___x_1244_);
v___x_1246_ = lean_box(v_fst_1232_);
v___x_1247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1247_, 0, v___x_1246_);
return v___x_1247_;
}
}
}
v___jp_1251_:
{
lean_object* v_fst_1253_; lean_object* v_snd_1254_; uint8_t v___x_1255_; 
v_fst_1253_ = lean_ctor_get(v___y_1252_, 0);
lean_inc(v_fst_1253_);
v_snd_1254_ = lean_ctor_get(v___y_1252_, 1);
lean_inc(v_snd_1254_);
lean_dec_ref(v___y_1252_);
v___x_1255_ = lean_unbox(v_fst_1253_);
lean_dec(v_fst_1253_);
v_fst_1232_ = v___x_1255_;
v_snd_1233_ = v_snd_1254_;
goto v___jp_1231_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___boxed(lean_object* v_localDecl_1349_, lean_object* v_fvarId_1350_, lean_object* v_generalizeNondepLet_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_){
_start:
{
uint8_t v_generalizeNondepLet_boxed_1354_; lean_object* v_res_1355_; 
v_generalizeNondepLet_boxed_1354_ = lean_unbox(v_generalizeNondepLet_1351_);
v_res_1355_ = l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg(v_localDecl_1349_, v_fvarId_1350_, v_generalizeNondepLet_boxed_1354_, v___y_1352_);
lean_dec(v___y_1352_);
return v_res_1355_;
}
}
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0(lean_object* v_localDecl_1356_, lean_object* v_fvarId_1357_, uint8_t v_generalizeNondepLet_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_){
_start:
{
lean_object* v___x_1364_; 
v___x_1364_ = l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg(v_localDecl_1356_, v_fvarId_1357_, v_generalizeNondepLet_1358_, v___y_1360_);
return v___x_1364_;
}
}
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___boxed(lean_object* v_localDecl_1365_, lean_object* v_fvarId_1366_, lean_object* v_generalizeNondepLet_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_){
_start:
{
uint8_t v_generalizeNondepLet_boxed_1373_; lean_object* v_res_1374_; 
v_generalizeNondepLet_boxed_1373_ = lean_unbox(v_generalizeNondepLet_1367_);
v_res_1374_ = l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0(v_localDecl_1365_, v_fvarId_1366_, v_generalizeNondepLet_boxed_1373_, v___y_1368_, v___y_1369_, v___y_1370_, v___y_1371_);
lean_dec(v___y_1371_);
lean_dec_ref(v___y_1370_);
lean_dec(v___y_1369_);
lean_dec_ref(v___y_1368_);
return v_res_1374_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2___redArg(lean_object* v_e_1375_, lean_object* v_fvarId_1376_, lean_object* v___y_1377_){
_start:
{
lean_object* v___x_1379_; uint8_t v_fst_1381_; lean_object* v_mctx_1382_; lean_object* v___y_1400_; lean_object* v_mctx_1405_; lean_object* v___f_1406_; lean_object* v___f_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; uint8_t v___x_1410_; 
v___x_1379_ = lean_st_ref_get(v___y_1377_);
v_mctx_1405_ = lean_ctor_get(v___x_1379_, 0);
lean_inc_ref_n(v_mctx_1405_, 2);
lean_dec(v___x_1379_);
v___f_1406_ = ((lean_object*)(l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__0));
v___f_1407_ = lean_alloc_closure((void*)(l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1407_, 0, v_fvarId_1376_);
v___x_1408_ = lean_obj_once(&l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__2, &l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__2_once, _init_l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__2);
v___x_1409_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1409_, 0, v___x_1408_);
lean_ctor_set(v___x_1409_, 1, v_mctx_1405_);
v___x_1410_ = l_Lean_Expr_hasFVar(v_e_1375_);
if (v___x_1410_ == 0)
{
uint8_t v___x_1411_; 
v___x_1411_ = l_Lean_Expr_hasMVar(v_e_1375_);
if (v___x_1411_ == 0)
{
lean_dec_ref(v___x_1409_);
lean_dec_ref(v___f_1407_);
lean_dec_ref(v_e_1375_);
v_fst_1381_ = v___x_1411_;
v_mctx_1382_ = v_mctx_1405_;
goto v___jp_1380_;
}
else
{
lean_object* v___x_1412_; 
lean_dec_ref(v_mctx_1405_);
v___x_1412_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1407_, v___f_1406_, v_e_1375_, v___x_1409_);
v___y_1400_ = v___x_1412_;
goto v___jp_1399_;
}
}
else
{
lean_object* v___x_1413_; 
lean_dec_ref(v_mctx_1405_);
v___x_1413_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1407_, v___f_1406_, v_e_1375_, v___x_1409_);
v___y_1400_ = v___x_1413_;
goto v___jp_1399_;
}
v___jp_1380_:
{
lean_object* v___x_1383_; lean_object* v_cache_1384_; lean_object* v_zetaDeltaFVarIds_1385_; lean_object* v_postponed_1386_; lean_object* v_diag_1387_; lean_object* v___x_1389_; uint8_t v_isShared_1390_; uint8_t v_isSharedCheck_1397_; 
v___x_1383_ = lean_st_ref_take(v___y_1377_);
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
v___x_1393_ = lean_st_ref_set(v___y_1377_, v___x_1392_);
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
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2___redArg___boxed(lean_object* v_e_1414_, lean_object* v_fvarId_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_){
_start:
{
lean_object* v_res_1418_; 
v_res_1418_ = l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2___redArg(v_e_1414_, v_fvarId_1415_, v___y_1416_);
lean_dec(v___y_1416_);
return v_res_1418_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2(lean_object* v_e_1419_, lean_object* v_fvarId_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_){
_start:
{
lean_object* v___x_1426_; 
v___x_1426_ = l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2___redArg(v_e_1419_, v_fvarId_1420_, v___y_1422_);
return v___x_1426_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2___boxed(lean_object* v_e_1427_, lean_object* v_fvarId_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_){
_start:
{
lean_object* v_res_1434_; 
v_res_1434_ = l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2(v_e_1427_, v_fvarId_1428_, v___y_1429_, v___y_1430_, v___y_1431_, v___y_1432_);
lean_dec(v___y_1432_);
lean_dec_ref(v___y_1431_);
lean_dec(v___y_1430_);
lean_dec_ref(v___y_1429_);
return v_res_1434_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_Meta_getMajorTypeIndices_spec__1(lean_object* v_a_1435_, lean_object* v_x_1436_){
_start:
{
if (lean_obj_tag(v_x_1436_) == 0)
{
uint8_t v___x_1437_; 
v___x_1437_ = 0;
return v___x_1437_;
}
else
{
lean_object* v_head_1438_; lean_object* v_tail_1439_; uint8_t v___x_1440_; 
v_head_1438_ = lean_ctor_get(v_x_1436_, 0);
v_tail_1439_ = lean_ctor_get(v_x_1436_, 1);
v___x_1440_ = lean_nat_dec_eq(v_a_1435_, v_head_1438_);
if (v___x_1440_ == 0)
{
v_x_1436_ = v_tail_1439_;
goto _start;
}
else
{
return v___x_1440_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_Meta_getMajorTypeIndices_spec__1___boxed(lean_object* v_a_1442_, lean_object* v_x_1443_){
_start:
{
uint8_t v_res_1444_; lean_object* v_r_1445_; 
v_res_1444_ = l_List_elem___at___00Lean_Meta_getMajorTypeIndices_spec__1(v_a_1442_, v_x_1443_);
lean_dec(v_x_1443_);
lean_dec(v_a_1442_);
v_r_1445_ = lean_box(v_res_1444_);
return v_r_1445_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_1447_; lean_object* v___x_1448_; 
v___x_1447_ = ((lean_object*)(l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__0));
v___x_1448_ = l_Lean_stringToMessageData(v___x_1447_);
return v___x_1448_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_1450_; lean_object* v___x_1451_; 
v___x_1450_ = ((lean_object*)(l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__2));
v___x_1451_ = l_Lean_stringToMessageData(v___x_1450_);
return v___x_1451_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__5(void){
_start:
{
lean_object* v___x_1453_; lean_object* v___x_1454_; 
v___x_1453_ = ((lean_object*)(l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__4));
v___x_1454_ = l_Lean_stringToMessageData(v___x_1453_);
return v___x_1454_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__7(void){
_start:
{
lean_object* v___x_1456_; lean_object* v___x_1457_; 
v___x_1456_ = ((lean_object*)(l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__6));
v___x_1457_ = l_Lean_stringToMessageData(v___x_1456_);
return v___x_1457_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg(lean_object* v_majorTypeArgs_1458_, lean_object* v_idx_1459_, lean_object* v_tacticName_1460_, lean_object* v_mvarId_1461_, lean_object* v_idxPos_1462_, lean_object* v_recursorInfo_1463_, lean_object* v_majorType_1464_, lean_object* v_n_1465_, lean_object* v_i_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_){
_start:
{
lean_object* v_zero_1472_; uint8_t v_isZero_1473_; 
v_zero_1472_ = lean_unsigned_to_nat(0u);
v_isZero_1473_ = lean_nat_dec_eq(v_i_1466_, v_zero_1472_);
if (v_isZero_1473_ == 1)
{
lean_object* v___x_1474_; lean_object* v___x_1475_; 
lean_dec(v_i_1466_);
lean_dec_ref(v_majorType_1464_);
lean_dec(v_mvarId_1461_);
lean_dec(v_tacticName_1460_);
lean_dec_ref(v_idx_1459_);
v___x_1474_ = lean_box(0);
v___x_1475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1475_, 0, v___x_1474_);
return v___x_1475_;
}
else
{
lean_object* v_one_1476_; lean_object* v_n_1477_; lean_object* v___y_1479_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v_arg_1483_; lean_object* v___y_1485_; lean_object* v___y_1486_; lean_object* v___y_1487_; lean_object* v___y_1488_; uint8_t v___y_1489_; lean_object* v___y_1528_; lean_object* v___y_1529_; lean_object* v___y_1530_; lean_object* v___y_1531_; lean_object* v___y_1536_; lean_object* v___y_1537_; lean_object* v___y_1538_; lean_object* v___y_1539_; uint8_t v___x_1560_; 
v_one_1476_ = lean_unsigned_to_nat(1u);
v_n_1477_ = lean_nat_sub(v_i_1466_, v_one_1476_);
lean_dec(v_i_1466_);
v___x_1481_ = lean_nat_sub(v_n_1465_, v_n_1477_);
v___x_1482_ = lean_nat_sub(v___x_1481_, v_one_1476_);
lean_dec(v___x_1481_);
v_arg_1483_ = lean_array_fget_borrowed(v_majorTypeArgs_1458_, v___x_1482_);
v___x_1560_ = lean_nat_dec_eq(v___x_1482_, v_idxPos_1462_);
if (v___x_1560_ == 0)
{
uint8_t v___x_1561_; 
v___x_1561_ = lean_expr_eqv(v_arg_1483_, v_idx_1459_);
if (v___x_1561_ == 0)
{
v___y_1536_ = v___y_1467_;
v___y_1537_ = v___y_1468_;
v___y_1538_ = v___y_1469_;
v___y_1539_ = v___y_1470_;
goto v___jp_1535_;
}
else
{
lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; 
v___x_1562_ = lean_obj_once(&l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1, &l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1_once, _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1);
lean_inc_ref(v_idx_1459_);
v___x_1563_ = l_Lean_MessageData_ofExpr(v_idx_1459_);
v___x_1564_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1564_, 0, v___x_1562_);
lean_ctor_set(v___x_1564_, 1, v___x_1563_);
v___x_1565_ = lean_obj_once(&l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__7, &l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__7_once, _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__7);
v___x_1566_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1566_, 0, v___x_1564_);
lean_ctor_set(v___x_1566_, 1, v___x_1565_);
lean_inc_ref(v_majorType_1464_);
v___x_1567_ = l_Lean_indentExpr(v_majorType_1464_);
v___x_1568_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1568_, 0, v___x_1566_);
lean_ctor_set(v___x_1568_, 1, v___x_1567_);
v___x_1569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1569_, 0, v___x_1568_);
lean_inc(v_mvarId_1461_);
lean_inc(v_tacticName_1460_);
v___x_1570_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1460_, v_mvarId_1461_, v___x_1569_, v___y_1467_, v___y_1468_, v___y_1469_, v___y_1470_);
if (lean_obj_tag(v___x_1570_) == 0)
{
lean_dec_ref(v___x_1570_);
v___y_1536_ = v___y_1467_;
v___y_1537_ = v___y_1468_;
v___y_1538_ = v___y_1469_;
v___y_1539_ = v___y_1470_;
goto v___jp_1535_;
}
else
{
lean_dec(v___x_1482_);
v___y_1479_ = v___x_1570_;
goto v___jp_1478_;
}
}
}
else
{
v___y_1536_ = v___y_1467_;
v___y_1537_ = v___y_1468_;
v___y_1538_ = v___y_1469_;
v___y_1539_ = v___y_1470_;
goto v___jp_1535_;
}
v___jp_1478_:
{
if (lean_obj_tag(v___y_1479_) == 0)
{
lean_dec_ref(v___y_1479_);
v_i_1466_ = v_n_1477_;
goto _start;
}
else
{
lean_dec(v_n_1477_);
lean_dec_ref(v_majorType_1464_);
lean_dec(v_mvarId_1461_);
lean_dec(v_tacticName_1460_);
lean_dec_ref(v_idx_1459_);
return v___y_1479_;
}
}
v___jp_1484_:
{
if (v___y_1489_ == 0)
{
lean_dec(v___x_1482_);
v_i_1466_ = v_n_1477_;
goto _start;
}
else
{
uint8_t v___x_1491_; 
v___x_1491_ = l_Lean_Expr_isFVar(v_arg_1483_);
if (v___x_1491_ == 0)
{
lean_dec(v___x_1482_);
v_i_1466_ = v_n_1477_;
goto _start;
}
else
{
lean_object* v___x_1493_; lean_object* v___x_1494_; 
v___x_1493_ = l_Lean_Expr_fvarId_x21(v_idx_1459_);
v___x_1494_ = l_Lean_FVarId_getDecl___redArg(v___x_1493_, v___y_1486_, v___y_1485_, v___y_1487_);
if (lean_obj_tag(v___x_1494_) == 0)
{
lean_object* v_a_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v_a_1498_; lean_object* v___x_1500_; uint8_t v_isShared_1501_; uint8_t v_isSharedCheck_1518_; 
v_a_1495_ = lean_ctor_get(v___x_1494_, 0);
lean_inc(v_a_1495_);
lean_dec_ref(v___x_1494_);
v___x_1496_ = l_Lean_Expr_fvarId_x21(v_arg_1483_);
v___x_1497_ = l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg(v_a_1495_, v___x_1496_, v___y_1489_, v___y_1488_);
v_a_1498_ = lean_ctor_get(v___x_1497_, 0);
v_isSharedCheck_1518_ = !lean_is_exclusive(v___x_1497_);
if (v_isSharedCheck_1518_ == 0)
{
v___x_1500_ = v___x_1497_;
v_isShared_1501_ = v_isSharedCheck_1518_;
goto v_resetjp_1499_;
}
else
{
lean_inc(v_a_1498_);
lean_dec(v___x_1497_);
v___x_1500_ = lean_box(0);
v_isShared_1501_ = v_isSharedCheck_1518_;
goto v_resetjp_1499_;
}
v_resetjp_1499_:
{
uint8_t v___x_1502_; 
v___x_1502_ = lean_unbox(v_a_1498_);
lean_dec(v_a_1498_);
if (v___x_1502_ == 0)
{
lean_del_object(v___x_1500_);
lean_dec(v___x_1482_);
v_i_1466_ = v_n_1477_;
goto _start;
}
else
{
lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1512_; 
v___x_1504_ = lean_obj_once(&l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1, &l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1_once, _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1);
lean_inc_ref(v_idx_1459_);
v___x_1505_ = l_Lean_MessageData_ofExpr(v_idx_1459_);
v___x_1506_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1506_, 0, v___x_1504_);
lean_ctor_set(v___x_1506_, 1, v___x_1505_);
v___x_1507_ = lean_obj_once(&l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__3, &l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__3_once, _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__3);
v___x_1508_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1508_, 0, v___x_1506_);
lean_ctor_set(v___x_1508_, 1, v___x_1507_);
v___x_1509_ = lean_nat_add(v___x_1482_, v_one_1476_);
lean_dec(v___x_1482_);
v___x_1510_ = l_Nat_reprFast(v___x_1509_);
if (v_isShared_1501_ == 0)
{
lean_ctor_set_tag(v___x_1500_, 3);
lean_ctor_set(v___x_1500_, 0, v___x_1510_);
v___x_1512_ = v___x_1500_;
goto v_reusejp_1511_;
}
else
{
lean_object* v_reuseFailAlloc_1517_; 
v_reuseFailAlloc_1517_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1517_, 0, v___x_1510_);
v___x_1512_ = v_reuseFailAlloc_1517_;
goto v_reusejp_1511_;
}
v_reusejp_1511_:
{
lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; 
v___x_1513_ = l_Lean_MessageData_ofFormat(v___x_1512_);
v___x_1514_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1514_, 0, v___x_1508_);
lean_ctor_set(v___x_1514_, 1, v___x_1513_);
v___x_1515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1515_, 0, v___x_1514_);
lean_inc(v_mvarId_1461_);
lean_inc(v_tacticName_1460_);
v___x_1516_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1460_, v_mvarId_1461_, v___x_1515_, v___y_1486_, v___y_1488_, v___y_1485_, v___y_1487_);
v___y_1479_ = v___x_1516_;
goto v___jp_1478_;
}
}
}
}
else
{
lean_object* v_a_1519_; lean_object* v___x_1521_; uint8_t v_isShared_1522_; uint8_t v_isSharedCheck_1526_; 
lean_dec(v___x_1482_);
lean_dec(v_n_1477_);
lean_dec_ref(v_majorType_1464_);
lean_dec(v_mvarId_1461_);
lean_dec(v_tacticName_1460_);
lean_dec_ref(v_idx_1459_);
v_a_1519_ = lean_ctor_get(v___x_1494_, 0);
v_isSharedCheck_1526_ = !lean_is_exclusive(v___x_1494_);
if (v_isSharedCheck_1526_ == 0)
{
v___x_1521_ = v___x_1494_;
v_isShared_1522_ = v_isSharedCheck_1526_;
goto v_resetjp_1520_;
}
else
{
lean_inc(v_a_1519_);
lean_dec(v___x_1494_);
v___x_1521_ = lean_box(0);
v_isShared_1522_ = v_isSharedCheck_1526_;
goto v_resetjp_1520_;
}
v_resetjp_1520_:
{
lean_object* v___x_1524_; 
if (v_isShared_1522_ == 0)
{
v___x_1524_ = v___x_1521_;
goto v_reusejp_1523_;
}
else
{
lean_object* v_reuseFailAlloc_1525_; 
v_reuseFailAlloc_1525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1525_, 0, v_a_1519_);
v___x_1524_ = v_reuseFailAlloc_1525_;
goto v_reusejp_1523_;
}
v_reusejp_1523_:
{
return v___x_1524_;
}
}
}
}
}
}
v___jp_1527_:
{
uint8_t v___x_1532_; 
v___x_1532_ = lean_nat_dec_lt(v_idxPos_1462_, v___x_1482_);
if (v___x_1532_ == 0)
{
v___y_1485_ = v___y_1530_;
v___y_1486_ = v___y_1528_;
v___y_1487_ = v___y_1531_;
v___y_1488_ = v___y_1529_;
v___y_1489_ = v___x_1532_;
goto v___jp_1484_;
}
else
{
lean_object* v_indicesPos_1533_; uint8_t v___x_1534_; 
v_indicesPos_1533_ = lean_ctor_get(v_recursorInfo_1463_, 6);
v___x_1534_ = l_List_elem___at___00Lean_Meta_getMajorTypeIndices_spec__1(v___x_1482_, v_indicesPos_1533_);
v___y_1485_ = v___y_1530_;
v___y_1486_ = v___y_1528_;
v___y_1487_ = v___y_1531_;
v___y_1488_ = v___y_1529_;
v___y_1489_ = v___x_1534_;
goto v___jp_1484_;
}
}
v___jp_1535_:
{
uint8_t v___x_1540_; 
v___x_1540_ = lean_nat_dec_lt(v___x_1482_, v_idxPos_1462_);
if (v___x_1540_ == 0)
{
v___y_1528_ = v___y_1536_;
v___y_1529_ = v___y_1537_;
v___y_1530_ = v___y_1538_;
v___y_1531_ = v___y_1539_;
goto v___jp_1527_;
}
else
{
lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v_a_1543_; lean_object* v___x_1545_; uint8_t v_isShared_1546_; uint8_t v_isSharedCheck_1559_; 
v___x_1541_ = l_Lean_Expr_fvarId_x21(v_idx_1459_);
lean_inc(v_arg_1483_);
v___x_1542_ = l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2___redArg(v_arg_1483_, v___x_1541_, v___y_1537_);
v_a_1543_ = lean_ctor_get(v___x_1542_, 0);
v_isSharedCheck_1559_ = !lean_is_exclusive(v___x_1542_);
if (v_isSharedCheck_1559_ == 0)
{
v___x_1545_ = v___x_1542_;
v_isShared_1546_ = v_isSharedCheck_1559_;
goto v_resetjp_1544_;
}
else
{
lean_inc(v_a_1543_);
lean_dec(v___x_1542_);
v___x_1545_ = lean_box(0);
v_isShared_1546_ = v_isSharedCheck_1559_;
goto v_resetjp_1544_;
}
v_resetjp_1544_:
{
uint8_t v___x_1547_; 
v___x_1547_ = lean_unbox(v_a_1543_);
lean_dec(v_a_1543_);
if (v___x_1547_ == 0)
{
lean_del_object(v___x_1545_);
v___y_1528_ = v___y_1536_;
v___y_1529_ = v___y_1537_;
v___y_1530_ = v___y_1538_;
v___y_1531_ = v___y_1539_;
goto v___jp_1527_;
}
else
{
lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1556_; 
v___x_1548_ = lean_obj_once(&l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1, &l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1_once, _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1);
lean_inc_ref(v_idx_1459_);
v___x_1549_ = l_Lean_MessageData_ofExpr(v_idx_1459_);
v___x_1550_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1550_, 0, v___x_1548_);
lean_ctor_set(v___x_1550_, 1, v___x_1549_);
v___x_1551_ = lean_obj_once(&l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__5, &l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__5_once, _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__5);
v___x_1552_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1552_, 0, v___x_1550_);
lean_ctor_set(v___x_1552_, 1, v___x_1551_);
lean_inc_ref(v_majorType_1464_);
v___x_1553_ = l_Lean_indentExpr(v_majorType_1464_);
v___x_1554_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1554_, 0, v___x_1552_);
lean_ctor_set(v___x_1554_, 1, v___x_1553_);
if (v_isShared_1546_ == 0)
{
lean_ctor_set_tag(v___x_1545_, 1);
lean_ctor_set(v___x_1545_, 0, v___x_1554_);
v___x_1556_ = v___x_1545_;
goto v_reusejp_1555_;
}
else
{
lean_object* v_reuseFailAlloc_1558_; 
v_reuseFailAlloc_1558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1558_, 0, v___x_1554_);
v___x_1556_ = v_reuseFailAlloc_1558_;
goto v_reusejp_1555_;
}
v_reusejp_1555_:
{
lean_object* v___x_1557_; 
lean_inc(v_mvarId_1461_);
lean_inc(v_tacticName_1460_);
v___x_1557_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1460_, v_mvarId_1461_, v___x_1556_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_);
if (lean_obj_tag(v___x_1557_) == 0)
{
lean_dec_ref(v___x_1557_);
v___y_1528_ = v___y_1536_;
v___y_1529_ = v___y_1537_;
v___y_1530_ = v___y_1538_;
v___y_1531_ = v___y_1539_;
goto v___jp_1527_;
}
else
{
lean_dec(v___x_1482_);
v___y_1479_ = v___x_1557_;
goto v___jp_1478_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___boxed(lean_object* v_majorTypeArgs_1571_, lean_object* v_idx_1572_, lean_object* v_tacticName_1573_, lean_object* v_mvarId_1574_, lean_object* v_idxPos_1575_, lean_object* v_recursorInfo_1576_, lean_object* v_majorType_1577_, lean_object* v_n_1578_, lean_object* v_i_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_){
_start:
{
lean_object* v_res_1585_; 
v_res_1585_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg(v_majorTypeArgs_1571_, v_idx_1572_, v_tacticName_1573_, v_mvarId_1574_, v_idxPos_1575_, v_recursorInfo_1576_, v_majorType_1577_, v_n_1578_, v_i_1579_, v___y_1580_, v___y_1581_, v___y_1582_, v___y_1583_);
lean_dec(v___y_1583_);
lean_dec_ref(v___y_1582_);
lean_dec(v___y_1581_);
lean_dec_ref(v___y_1580_);
lean_dec(v_n_1578_);
lean_dec_ref(v_recursorInfo_1576_);
lean_dec(v_idxPos_1575_);
lean_dec_ref(v_majorTypeArgs_1571_);
return v_res_1585_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__1(void){
_start:
{
lean_object* v___x_1587_; lean_object* v___x_1588_; 
v___x_1587_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__0));
v___x_1588_ = l_Lean_stringToMessageData(v___x_1587_);
return v___x_1588_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__3(void){
_start:
{
lean_object* v___x_1590_; lean_object* v___x_1591_; 
v___x_1590_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__2));
v___x_1591_ = l_Lean_stringToMessageData(v___x_1590_);
return v___x_1591_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__5(void){
_start:
{
lean_object* v___x_1593_; lean_object* v___x_1594_; 
v___x_1593_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__4));
v___x_1594_ = l_Lean_stringToMessageData(v___x_1593_);
return v___x_1594_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4(lean_object* v_majorTypeArgs_1595_, lean_object* v_tacticName_1596_, lean_object* v_mvarId_1597_, lean_object* v_recursorInfo_1598_, lean_object* v_majorType_1599_, size_t v_sz_1600_, size_t v_i_1601_, lean_object* v_bs_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_){
_start:
{
uint8_t v___x_1608_; 
v___x_1608_ = lean_usize_dec_lt(v_i_1601_, v_sz_1600_);
if (v___x_1608_ == 0)
{
lean_object* v___x_1609_; 
lean_dec_ref(v_majorType_1599_);
lean_dec(v_mvarId_1597_);
lean_dec(v_tacticName_1596_);
v___x_1609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1609_, 0, v_bs_1602_);
return v___x_1609_;
}
else
{
lean_object* v_v_1610_; lean_object* v___x_1611_; lean_object* v_bs_x27_1612_; lean_object* v_a_1614_; lean_object* v___x_1619_; uint8_t v___x_1620_; 
v_v_1610_ = lean_array_uget(v_bs_1602_, v_i_1601_);
v___x_1611_ = lean_unsigned_to_nat(0u);
v_bs_x27_1612_ = lean_array_uset(v_bs_1602_, v_i_1601_, v___x_1611_);
v___x_1619_ = lean_array_get_size(v_majorTypeArgs_1595_);
v___x_1620_ = lean_nat_dec_le(v___x_1619_, v_v_1610_);
if (v___x_1620_ == 0)
{
lean_object* v_idx_1621_; lean_object* v___y_1623_; lean_object* v___y_1624_; lean_object* v___y_1625_; lean_object* v___y_1626_; uint8_t v___x_1636_; 
v_idx_1621_ = lean_array_fget_borrowed(v_majorTypeArgs_1595_, v_v_1610_);
v___x_1636_ = l_Lean_Expr_isFVar(v_idx_1621_);
if (v___x_1636_ == 0)
{
lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; 
v___x_1637_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__1);
lean_inc(v_idx_1621_);
v___x_1638_ = l_Lean_MessageData_ofExpr(v_idx_1621_);
v___x_1639_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1639_, 0, v___x_1637_);
lean_ctor_set(v___x_1639_, 1, v___x_1638_);
v___x_1640_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__3);
v___x_1641_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1641_, 0, v___x_1639_);
lean_ctor_set(v___x_1641_, 1, v___x_1640_);
lean_inc_ref(v_majorType_1599_);
v___x_1642_ = l_Lean_indentExpr(v_majorType_1599_);
v___x_1643_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1643_, 0, v___x_1641_);
lean_ctor_set(v___x_1643_, 1, v___x_1642_);
v___x_1644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1644_, 0, v___x_1643_);
lean_inc(v_mvarId_1597_);
lean_inc(v_tacticName_1596_);
v___x_1645_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1596_, v_mvarId_1597_, v___x_1644_, v___y_1603_, v___y_1604_, v___y_1605_, v___y_1606_);
if (lean_obj_tag(v___x_1645_) == 0)
{
lean_dec_ref(v___x_1645_);
v___y_1623_ = v___y_1603_;
v___y_1624_ = v___y_1604_;
v___y_1625_ = v___y_1605_;
v___y_1626_ = v___y_1606_;
goto v___jp_1622_;
}
else
{
lean_object* v_a_1646_; lean_object* v___x_1648_; uint8_t v_isShared_1649_; uint8_t v_isSharedCheck_1653_; 
lean_dec_ref(v_bs_x27_1612_);
lean_dec(v_v_1610_);
lean_dec_ref(v_majorType_1599_);
lean_dec(v_mvarId_1597_);
lean_dec(v_tacticName_1596_);
v_a_1646_ = lean_ctor_get(v___x_1645_, 0);
v_isSharedCheck_1653_ = !lean_is_exclusive(v___x_1645_);
if (v_isSharedCheck_1653_ == 0)
{
v___x_1648_ = v___x_1645_;
v_isShared_1649_ = v_isSharedCheck_1653_;
goto v_resetjp_1647_;
}
else
{
lean_inc(v_a_1646_);
lean_dec(v___x_1645_);
v___x_1648_ = lean_box(0);
v_isShared_1649_ = v_isSharedCheck_1653_;
goto v_resetjp_1647_;
}
v_resetjp_1647_:
{
lean_object* v___x_1651_; 
if (v_isShared_1649_ == 0)
{
v___x_1651_ = v___x_1648_;
goto v_reusejp_1650_;
}
else
{
lean_object* v_reuseFailAlloc_1652_; 
v_reuseFailAlloc_1652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1652_, 0, v_a_1646_);
v___x_1651_ = v_reuseFailAlloc_1652_;
goto v_reusejp_1650_;
}
v_reusejp_1650_:
{
return v___x_1651_;
}
}
}
}
else
{
v___y_1623_ = v___y_1603_;
v___y_1624_ = v___y_1604_;
v___y_1625_ = v___y_1605_;
v___y_1626_ = v___y_1606_;
goto v___jp_1622_;
}
v___jp_1622_:
{
lean_object* v___x_1627_; 
lean_inc_ref(v_majorType_1599_);
lean_inc(v_mvarId_1597_);
lean_inc(v_tacticName_1596_);
lean_inc(v_idx_1621_);
v___x_1627_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg(v_majorTypeArgs_1595_, v_idx_1621_, v_tacticName_1596_, v_mvarId_1597_, v_v_1610_, v_recursorInfo_1598_, v_majorType_1599_, v___x_1619_, v___x_1619_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_);
lean_dec(v_v_1610_);
if (lean_obj_tag(v___x_1627_) == 0)
{
lean_dec_ref(v___x_1627_);
lean_inc(v_idx_1621_);
v_a_1614_ = v_idx_1621_;
goto v___jp_1613_;
}
else
{
lean_object* v_a_1628_; lean_object* v___x_1630_; uint8_t v_isShared_1631_; uint8_t v_isSharedCheck_1635_; 
lean_dec_ref(v_bs_x27_1612_);
lean_dec_ref(v_majorType_1599_);
lean_dec(v_mvarId_1597_);
lean_dec(v_tacticName_1596_);
v_a_1628_ = lean_ctor_get(v___x_1627_, 0);
v_isSharedCheck_1635_ = !lean_is_exclusive(v___x_1627_);
if (v_isSharedCheck_1635_ == 0)
{
v___x_1630_ = v___x_1627_;
v_isShared_1631_ = v_isSharedCheck_1635_;
goto v_resetjp_1629_;
}
else
{
lean_inc(v_a_1628_);
lean_dec(v___x_1627_);
v___x_1630_ = lean_box(0);
v_isShared_1631_ = v_isSharedCheck_1635_;
goto v_resetjp_1629_;
}
v_resetjp_1629_:
{
lean_object* v___x_1633_; 
if (v_isShared_1631_ == 0)
{
v___x_1633_ = v___x_1630_;
goto v_reusejp_1632_;
}
else
{
lean_object* v_reuseFailAlloc_1634_; 
v_reuseFailAlloc_1634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1634_, 0, v_a_1628_);
v___x_1633_ = v_reuseFailAlloc_1634_;
goto v_reusejp_1632_;
}
v_reusejp_1632_:
{
return v___x_1633_;
}
}
}
}
}
else
{
lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; 
lean_dec(v_v_1610_);
v___x_1654_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__5, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__5);
lean_inc_ref(v_majorType_1599_);
v___x_1655_ = l_Lean_indentExpr(v_majorType_1599_);
v___x_1656_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1656_, 0, v___x_1654_);
lean_ctor_set(v___x_1656_, 1, v___x_1655_);
v___x_1657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1657_, 0, v___x_1656_);
lean_inc(v_mvarId_1597_);
lean_inc(v_tacticName_1596_);
v___x_1658_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1596_, v_mvarId_1597_, v___x_1657_, v___y_1603_, v___y_1604_, v___y_1605_, v___y_1606_);
if (lean_obj_tag(v___x_1658_) == 0)
{
lean_object* v_a_1659_; 
v_a_1659_ = lean_ctor_get(v___x_1658_, 0);
lean_inc(v_a_1659_);
lean_dec_ref(v___x_1658_);
v_a_1614_ = v_a_1659_;
goto v___jp_1613_;
}
else
{
lean_object* v_a_1660_; lean_object* v___x_1662_; uint8_t v_isShared_1663_; uint8_t v_isSharedCheck_1667_; 
lean_dec_ref(v_bs_x27_1612_);
lean_dec_ref(v_majorType_1599_);
lean_dec(v_mvarId_1597_);
lean_dec(v_tacticName_1596_);
v_a_1660_ = lean_ctor_get(v___x_1658_, 0);
v_isSharedCheck_1667_ = !lean_is_exclusive(v___x_1658_);
if (v_isSharedCheck_1667_ == 0)
{
v___x_1662_ = v___x_1658_;
v_isShared_1663_ = v_isSharedCheck_1667_;
goto v_resetjp_1661_;
}
else
{
lean_inc(v_a_1660_);
lean_dec(v___x_1658_);
v___x_1662_ = lean_box(0);
v_isShared_1663_ = v_isSharedCheck_1667_;
goto v_resetjp_1661_;
}
v_resetjp_1661_:
{
lean_object* v___x_1665_; 
if (v_isShared_1663_ == 0)
{
v___x_1665_ = v___x_1662_;
goto v_reusejp_1664_;
}
else
{
lean_object* v_reuseFailAlloc_1666_; 
v_reuseFailAlloc_1666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1666_, 0, v_a_1660_);
v___x_1665_ = v_reuseFailAlloc_1666_;
goto v_reusejp_1664_;
}
v_reusejp_1664_:
{
return v___x_1665_;
}
}
}
}
v___jp_1613_:
{
size_t v___x_1615_; size_t v___x_1616_; lean_object* v___x_1617_; 
v___x_1615_ = ((size_t)1ULL);
v___x_1616_ = lean_usize_add(v_i_1601_, v___x_1615_);
v___x_1617_ = lean_array_uset(v_bs_x27_1612_, v_i_1601_, v_a_1614_);
v_i_1601_ = v___x_1616_;
v_bs_1602_ = v___x_1617_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___boxed(lean_object* v_majorTypeArgs_1668_, lean_object* v_tacticName_1669_, lean_object* v_mvarId_1670_, lean_object* v_recursorInfo_1671_, lean_object* v_majorType_1672_, lean_object* v_sz_1673_, lean_object* v_i_1674_, lean_object* v_bs_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_){
_start:
{
size_t v_sz_boxed_1681_; size_t v_i_boxed_1682_; lean_object* v_res_1683_; 
v_sz_boxed_1681_ = lean_unbox_usize(v_sz_1673_);
lean_dec(v_sz_1673_);
v_i_boxed_1682_ = lean_unbox_usize(v_i_1674_);
lean_dec(v_i_1674_);
v_res_1683_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4(v_majorTypeArgs_1668_, v_tacticName_1669_, v_mvarId_1670_, v_recursorInfo_1671_, v_majorType_1672_, v_sz_boxed_1681_, v_i_boxed_1682_, v_bs_1675_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_);
lean_dec(v___y_1679_);
lean_dec_ref(v___y_1678_);
lean_dec(v___y_1677_);
lean_dec_ref(v___y_1676_);
lean_dec_ref(v_recursorInfo_1671_);
lean_dec_ref(v_majorTypeArgs_1668_);
return v_res_1683_;
}
}
static lean_object* _init_l_Lean_Meta_getMajorTypeIndices___closed__0(void){
_start:
{
lean_object* v___x_1684_; lean_object* v_dummy_1685_; 
v___x_1684_ = lean_box(0);
v_dummy_1685_ = l_Lean_Expr_sort___override(v___x_1684_);
return v_dummy_1685_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMajorTypeIndices(lean_object* v_mvarId_1686_, lean_object* v_tacticName_1687_, lean_object* v_recursorInfo_1688_, lean_object* v_majorType_1689_, lean_object* v_a_1690_, lean_object* v_a_1691_, lean_object* v_a_1692_, lean_object* v_a_1693_){
_start:
{
lean_object* v_indicesPos_1695_; lean_object* v_nargs_1696_; lean_object* v_dummy_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v_majorTypeArgs_1701_; lean_object* v___x_1702_; size_t v_sz_1703_; size_t v___x_1704_; lean_object* v___x_1705_; 
v_indicesPos_1695_ = lean_ctor_get(v_recursorInfo_1688_, 6);
v_nargs_1696_ = l_Lean_Expr_getAppNumArgs(v_majorType_1689_);
v_dummy_1697_ = lean_obj_once(&l_Lean_Meta_getMajorTypeIndices___closed__0, &l_Lean_Meta_getMajorTypeIndices___closed__0_once, _init_l_Lean_Meta_getMajorTypeIndices___closed__0);
lean_inc(v_nargs_1696_);
v___x_1698_ = lean_mk_array(v_nargs_1696_, v_dummy_1697_);
v___x_1699_ = lean_unsigned_to_nat(1u);
v___x_1700_ = lean_nat_sub(v_nargs_1696_, v___x_1699_);
lean_dec(v_nargs_1696_);
lean_inc_ref(v_majorType_1689_);
v_majorTypeArgs_1701_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_majorType_1689_, v___x_1698_, v___x_1700_);
lean_inc(v_indicesPos_1695_);
v___x_1702_ = lean_array_mk(v_indicesPos_1695_);
v_sz_1703_ = lean_array_size(v___x_1702_);
v___x_1704_ = ((size_t)0ULL);
v___x_1705_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4(v_majorTypeArgs_1701_, v_tacticName_1687_, v_mvarId_1686_, v_recursorInfo_1688_, v_majorType_1689_, v_sz_1703_, v___x_1704_, v___x_1702_, v_a_1690_, v_a_1691_, v_a_1692_, v_a_1693_);
lean_dec_ref(v_recursorInfo_1688_);
lean_dec_ref(v_majorTypeArgs_1701_);
return v___x_1705_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMajorTypeIndices___boxed(lean_object* v_mvarId_1706_, lean_object* v_tacticName_1707_, lean_object* v_recursorInfo_1708_, lean_object* v_majorType_1709_, lean_object* v_a_1710_, lean_object* v_a_1711_, lean_object* v_a_1712_, lean_object* v_a_1713_, lean_object* v_a_1714_){
_start:
{
lean_object* v_res_1715_; 
v_res_1715_ = l_Lean_Meta_getMajorTypeIndices(v_mvarId_1706_, v_tacticName_1707_, v_recursorInfo_1708_, v_majorType_1709_, v_a_1710_, v_a_1711_, v_a_1712_, v_a_1713_);
lean_dec(v_a_1713_);
lean_dec_ref(v_a_1712_);
lean_dec(v_a_1711_);
lean_dec_ref(v_a_1710_);
return v_res_1715_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3(lean_object* v_majorTypeArgs_1716_, lean_object* v_idx_1717_, lean_object* v_tacticName_1718_, lean_object* v_mvarId_1719_, lean_object* v_idxPos_1720_, lean_object* v_recursorInfo_1721_, lean_object* v_majorType_1722_, lean_object* v_n_1723_, lean_object* v_i_1724_, lean_object* v_a_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_){
_start:
{
lean_object* v___x_1731_; 
v___x_1731_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg(v_majorTypeArgs_1716_, v_idx_1717_, v_tacticName_1718_, v_mvarId_1719_, v_idxPos_1720_, v_recursorInfo_1721_, v_majorType_1722_, v_n_1723_, v_i_1724_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_);
return v___x_1731_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___boxed(lean_object* v_majorTypeArgs_1732_, lean_object* v_idx_1733_, lean_object* v_tacticName_1734_, lean_object* v_mvarId_1735_, lean_object* v_idxPos_1736_, lean_object* v_recursorInfo_1737_, lean_object* v_majorType_1738_, lean_object* v_n_1739_, lean_object* v_i_1740_, lean_object* v_a_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_){
_start:
{
lean_object* v_res_1747_; 
v_res_1747_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3(v_majorTypeArgs_1732_, v_idx_1733_, v_tacticName_1734_, v_mvarId_1735_, v_idxPos_1736_, v_recursorInfo_1737_, v_majorType_1738_, v_n_1739_, v_i_1740_, v_a_1741_, v___y_1742_, v___y_1743_, v___y_1744_, v___y_1745_);
lean_dec(v___y_1745_);
lean_dec_ref(v___y_1744_);
lean_dec(v___y_1743_);
lean_dec_ref(v___y_1742_);
lean_dec(v_n_1739_);
lean_dec_ref(v_recursorInfo_1737_);
lean_dec(v_idxPos_1736_);
lean_dec_ref(v_majorTypeArgs_1732_);
return v_res_1747_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1___redArg(lean_object* v_name_1748_, lean_object* v_msg_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_){
_start:
{
lean_object* v_ref_1755_; lean_object* v_msg_1756_; lean_object* v___x_1757_; lean_object* v_a_1758_; lean_object* v___x_1760_; uint8_t v_isShared_1761_; uint8_t v_isSharedCheck_1766_; 
v_ref_1755_ = lean_ctor_get(v___y_1752_, 5);
v_msg_1756_ = l_Lean_MessageData_tagWithErrorName(v_msg_1749_, v_name_1748_);
v___x_1757_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1_spec__2(v_msg_1756_, v___y_1750_, v___y_1751_, v___y_1752_, v___y_1753_);
v_a_1758_ = lean_ctor_get(v___x_1757_, 0);
v_isSharedCheck_1766_ = !lean_is_exclusive(v___x_1757_);
if (v_isSharedCheck_1766_ == 0)
{
v___x_1760_ = v___x_1757_;
v_isShared_1761_ = v_isSharedCheck_1766_;
goto v_resetjp_1759_;
}
else
{
lean_inc(v_a_1758_);
lean_dec(v___x_1757_);
v___x_1760_ = lean_box(0);
v_isShared_1761_ = v_isSharedCheck_1766_;
goto v_resetjp_1759_;
}
v_resetjp_1759_:
{
lean_object* v___x_1762_; lean_object* v___x_1764_; 
lean_inc(v_ref_1755_);
v___x_1762_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1762_, 0, v_ref_1755_);
lean_ctor_set(v___x_1762_, 1, v_a_1758_);
if (v_isShared_1761_ == 0)
{
lean_ctor_set_tag(v___x_1760_, 1);
lean_ctor_set(v___x_1760_, 0, v___x_1762_);
v___x_1764_ = v___x_1760_;
goto v_reusejp_1763_;
}
else
{
lean_object* v_reuseFailAlloc_1765_; 
v_reuseFailAlloc_1765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1765_, 0, v___x_1762_);
v___x_1764_ = v_reuseFailAlloc_1765_;
goto v_reusejp_1763_;
}
v_reusejp_1763_:
{
return v___x_1764_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1___redArg___boxed(lean_object* v_name_1767_, lean_object* v_msg_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_){
_start:
{
lean_object* v_res_1774_; 
v_res_1774_ = l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1___redArg(v_name_1767_, v_msg_1768_, v___y_1769_, v___y_1770_, v___y_1771_, v___y_1772_);
lean_dec(v___y_1772_);
lean_dec_ref(v___y_1771_);
lean_dec(v___y_1770_);
lean_dec_ref(v___y_1769_);
return v_res_1774_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Meta_mkRecursorAppPrefix_spec__0(lean_object* v_a_1775_, lean_object* v___x_1776_, lean_object* v_tacticName_1777_, lean_object* v_mvarId_1778_, lean_object* v_x_1779_, lean_object* v_x_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_){
_start:
{
if (lean_obj_tag(v_x_1780_) == 0)
{
lean_object* v___x_1786_; 
lean_dec(v_mvarId_1778_);
lean_dec(v_tacticName_1777_);
lean_dec(v_a_1775_);
v___x_1786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1786_, 0, v_x_1779_);
return v___x_1786_;
}
else
{
lean_object* v_head_1787_; 
v_head_1787_ = lean_ctor_get(v_x_1780_, 0);
if (lean_obj_tag(v_head_1787_) == 0)
{
lean_object* v_tail_1788_; lean_object* v_fst_1789_; lean_object* v___x_1791_; uint8_t v_isShared_1792_; uint8_t v_isSharedCheck_1800_; 
v_tail_1788_ = lean_ctor_get(v_x_1780_, 1);
v_fst_1789_ = lean_ctor_get(v_x_1779_, 0);
v_isSharedCheck_1800_ = !lean_is_exclusive(v_x_1779_);
if (v_isSharedCheck_1800_ == 0)
{
lean_object* v_unused_1801_; 
v_unused_1801_ = lean_ctor_get(v_x_1779_, 1);
lean_dec(v_unused_1801_);
v___x_1791_ = v_x_1779_;
v_isShared_1792_ = v_isSharedCheck_1800_;
goto v_resetjp_1790_;
}
else
{
lean_inc(v_fst_1789_);
lean_dec(v_x_1779_);
v___x_1791_ = lean_box(0);
v_isShared_1792_ = v_isSharedCheck_1800_;
goto v_resetjp_1790_;
}
v_resetjp_1790_:
{
lean_object* v___x_1793_; uint8_t v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1797_; 
lean_inc(v_a_1775_);
v___x_1793_ = lean_array_push(v_fst_1789_, v_a_1775_);
v___x_1794_ = 1;
v___x_1795_ = lean_box(v___x_1794_);
if (v_isShared_1792_ == 0)
{
lean_ctor_set(v___x_1791_, 1, v___x_1795_);
lean_ctor_set(v___x_1791_, 0, v___x_1793_);
v___x_1797_ = v___x_1791_;
goto v_reusejp_1796_;
}
else
{
lean_object* v_reuseFailAlloc_1799_; 
v_reuseFailAlloc_1799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1799_, 0, v___x_1793_);
lean_ctor_set(v_reuseFailAlloc_1799_, 1, v___x_1795_);
v___x_1797_ = v_reuseFailAlloc_1799_;
goto v_reusejp_1796_;
}
v_reusejp_1796_:
{
v_x_1779_ = v___x_1797_;
v_x_1780_ = v_tail_1788_;
goto _start;
}
}
}
else
{
lean_object* v_tail_1802_; lean_object* v_fst_1803_; lean_object* v_snd_1804_; lean_object* v___x_1806_; uint8_t v_isShared_1807_; uint8_t v_isSharedCheck_1821_; 
v_tail_1802_ = lean_ctor_get(v_x_1780_, 1);
v_fst_1803_ = lean_ctor_get(v_x_1779_, 0);
v_snd_1804_ = lean_ctor_get(v_x_1779_, 1);
v_isSharedCheck_1821_ = !lean_is_exclusive(v_x_1779_);
if (v_isSharedCheck_1821_ == 0)
{
v___x_1806_ = v_x_1779_;
v_isShared_1807_ = v_isSharedCheck_1821_;
goto v_resetjp_1805_;
}
else
{
lean_inc(v_snd_1804_);
lean_inc(v_fst_1803_);
lean_dec(v_x_1779_);
v___x_1806_ = lean_box(0);
v_isShared_1807_ = v_isSharedCheck_1821_;
goto v_resetjp_1805_;
}
v_resetjp_1805_:
{
lean_object* v_idx_1808_; lean_object* v___x_1809_; uint8_t v___x_1810_; 
v_idx_1808_ = lean_ctor_get(v_head_1787_, 0);
v___x_1809_ = lean_array_get_size(v___x_1776_);
v___x_1810_ = lean_nat_dec_le(v___x_1809_, v_idx_1808_);
if (v___x_1810_ == 0)
{
lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1814_; 
v___x_1811_ = lean_array_fget_borrowed(v___x_1776_, v_idx_1808_);
lean_inc(v___x_1811_);
v___x_1812_ = lean_array_push(v_fst_1803_, v___x_1811_);
if (v_isShared_1807_ == 0)
{
lean_ctor_set(v___x_1806_, 0, v___x_1812_);
v___x_1814_ = v___x_1806_;
goto v_reusejp_1813_;
}
else
{
lean_object* v_reuseFailAlloc_1816_; 
v_reuseFailAlloc_1816_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1816_, 0, v___x_1812_);
lean_ctor_set(v_reuseFailAlloc_1816_, 1, v_snd_1804_);
v___x_1814_ = v_reuseFailAlloc_1816_;
goto v_reusejp_1813_;
}
v_reusejp_1813_:
{
v_x_1779_ = v___x_1814_;
v_x_1780_ = v_tail_1802_;
goto _start;
}
}
else
{
lean_object* v___x_1817_; lean_object* v___x_1818_; 
lean_del_object(v___x_1806_);
lean_dec(v_snd_1804_);
lean_dec(v_fst_1803_);
v___x_1817_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9);
lean_inc(v_mvarId_1778_);
lean_inc(v_tacticName_1777_);
v___x_1818_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1777_, v_mvarId_1778_, v___x_1817_, v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_);
if (lean_obj_tag(v___x_1818_) == 0)
{
lean_object* v_a_1819_; 
v_a_1819_ = lean_ctor_get(v___x_1818_, 0);
lean_inc(v_a_1819_);
lean_dec_ref(v___x_1818_);
v_x_1779_ = v_a_1819_;
v_x_1780_ = v_tail_1802_;
goto _start;
}
else
{
lean_dec(v_mvarId_1778_);
lean_dec(v_tacticName_1777_);
lean_dec(v_a_1775_);
return v___x_1818_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Meta_mkRecursorAppPrefix_spec__0___boxed(lean_object* v_a_1822_, lean_object* v___x_1823_, lean_object* v_tacticName_1824_, lean_object* v_mvarId_1825_, lean_object* v_x_1826_, lean_object* v_x_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_){
_start:
{
lean_object* v_res_1833_; 
v_res_1833_ = l_List_foldlM___at___00Lean_Meta_mkRecursorAppPrefix_spec__0(v_a_1822_, v___x_1823_, v_tacticName_1824_, v_mvarId_1825_, v_x_1826_, v_x_1827_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_);
lean_dec(v___y_1831_);
lean_dec_ref(v___y_1830_);
lean_dec(v___y_1829_);
lean_dec_ref(v___y_1828_);
lean_dec(v_x_1827_);
lean_dec_ref(v___x_1823_);
return v_res_1833_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__8(void){
_start:
{
lean_object* v___x_1849_; lean_object* v___x_1850_; 
v___x_1849_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__7));
v___x_1850_ = l_Lean_stringToMessageData(v___x_1849_);
return v___x_1850_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__10(void){
_start:
{
lean_object* v___x_1852_; lean_object* v___x_1853_; 
v___x_1852_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__9));
v___x_1853_ = l_Lean_stringToMessageData(v___x_1852_);
return v___x_1853_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__13(void){
_start:
{
lean_object* v___x_1857_; lean_object* v___x_1858_; 
v___x_1857_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__12));
v___x_1858_ = l_Lean_MessageData_ofFormat(v___x_1857_);
return v___x_1858_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__14(void){
_start:
{
lean_object* v___x_1859_; lean_object* v___x_1860_; 
v___x_1859_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__13, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__13_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__13);
v___x_1860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1860_, 0, v___x_1859_);
return v___x_1860_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2(lean_object* v_recursorInfo_1861_, lean_object* v_a_1862_, lean_object* v_tacticName_1863_, lean_object* v_mvarId_1864_, lean_object* v_indices_1865_, lean_object* v_a_1866_, lean_object* v_major_1867_, lean_object* v_x_1868_, lean_object* v_x_1869_, lean_object* v_x_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_){
_start:
{
if (lean_obj_tag(v_x_1868_) == 5)
{
lean_object* v_fn_1876_; lean_object* v_arg_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; 
v_fn_1876_ = lean_ctor_get(v_x_1868_, 0);
lean_inc_ref(v_fn_1876_);
v_arg_1877_ = lean_ctor_get(v_x_1868_, 1);
lean_inc_ref(v_arg_1877_);
lean_dec_ref(v_x_1868_);
v___x_1878_ = lean_array_set(v_x_1869_, v_x_1870_, v_arg_1877_);
v___x_1879_ = lean_unsigned_to_nat(1u);
v___x_1880_ = lean_nat_sub(v_x_1870_, v___x_1879_);
lean_dec(v_x_1870_);
v_x_1868_ = v_fn_1876_;
v_x_1869_ = v___x_1878_;
v_x_1870_ = v___x_1880_;
goto _start;
}
else
{
lean_dec(v_x_1870_);
if (lean_obj_tag(v_x_1868_) == 4)
{
lean_object* v_us_1882_; lean_object* v_recursorName_1883_; lean_object* v_univLevelPos_1884_; uint8_t v_depElim_1885_; lean_object* v_paramsPos_1886_; lean_object* v___x_1887_; uint8_t v___x_1888_; lean_object* v___y_1890_; lean_object* v_motive_1891_; lean_object* v___y_1892_; lean_object* v___y_1893_; lean_object* v___y_1894_; lean_object* v___y_1895_; lean_object* v___x_1908_; lean_object* v___x_1909_; 
v_us_1882_ = lean_ctor_get(v_x_1868_, 1);
lean_inc(v_us_1882_);
lean_dec_ref(v_x_1868_);
v_recursorName_1883_ = lean_ctor_get(v_recursorInfo_1861_, 0);
lean_inc(v_recursorName_1883_);
v_univLevelPos_1884_ = lean_ctor_get(v_recursorInfo_1861_, 2);
lean_inc(v_univLevelPos_1884_);
v_depElim_1885_ = lean_ctor_get_uint8(v_recursorInfo_1861_, sizeof(void*)*8);
v_paramsPos_1886_ = lean_ctor_get(v_recursorInfo_1861_, 5);
lean_inc(v_paramsPos_1886_);
lean_dec_ref(v_recursorInfo_1861_);
v___x_1887_ = lean_array_mk(v_us_1882_);
v___x_1888_ = 0;
v___x_1908_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__1));
lean_inc(v_mvarId_1864_);
lean_inc(v_tacticName_1863_);
lean_inc(v_a_1862_);
v___x_1909_ = l_List_foldlM___at___00Lean_Meta_mkRecursorAppPrefix_spec__0(v_a_1862_, v___x_1887_, v_tacticName_1863_, v_mvarId_1864_, v___x_1908_, v_univLevelPos_1884_, v___y_1871_, v___y_1872_, v___y_1873_, v___y_1874_);
lean_dec(v_univLevelPos_1884_);
lean_dec_ref(v___x_1887_);
if (lean_obj_tag(v___x_1909_) == 0)
{
lean_object* v_a_1910_; lean_object* v_fst_1911_; lean_object* v_snd_1912_; lean_object* v___x_1914_; uint8_t v_isShared_1915_; uint8_t v_isSharedCheck_1956_; 
v_a_1910_ = lean_ctor_get(v___x_1909_, 0);
lean_inc(v_a_1910_);
lean_dec_ref(v___x_1909_);
v_fst_1911_ = lean_ctor_get(v_a_1910_, 0);
v_snd_1912_ = lean_ctor_get(v_a_1910_, 1);
v_isSharedCheck_1956_ = !lean_is_exclusive(v_a_1910_);
if (v_isSharedCheck_1956_ == 0)
{
v___x_1914_ = v_a_1910_;
v_isShared_1915_ = v_isSharedCheck_1956_;
goto v_resetjp_1913_;
}
else
{
lean_inc(v_snd_1912_);
lean_inc(v_fst_1911_);
lean_dec(v_a_1910_);
v___x_1914_ = lean_box(0);
v_isShared_1915_ = v_isSharedCheck_1956_;
goto v_resetjp_1913_;
}
v_resetjp_1913_:
{
lean_object* v___y_1917_; lean_object* v___y_1918_; lean_object* v___y_1919_; lean_object* v___y_1920_; uint8_t v___x_1936_; 
v___x_1936_ = lean_unbox(v_snd_1912_);
lean_dec(v_snd_1912_);
if (v___x_1936_ == 0)
{
uint8_t v___x_1937_; 
v___x_1937_ = l_Lean_Level_isZero(v_a_1862_);
lean_dec(v_a_1862_);
if (v___x_1937_ == 0)
{
lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1942_; 
lean_dec(v_fst_1911_);
lean_dec(v_paramsPos_1886_);
lean_dec_ref(v_x_1869_);
lean_dec_ref(v_major_1867_);
lean_dec_ref(v_a_1866_);
v___x_1938_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__6));
v___x_1939_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__8, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__8_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__8);
v___x_1940_ = l_Lean_MessageData_ofName(v_recursorName_1883_);
if (v_isShared_1915_ == 0)
{
lean_ctor_set_tag(v___x_1914_, 7);
lean_ctor_set(v___x_1914_, 1, v___x_1940_);
lean_ctor_set(v___x_1914_, 0, v___x_1939_);
v___x_1942_ = v___x_1914_;
goto v_reusejp_1941_;
}
else
{
lean_object* v_reuseFailAlloc_1955_; 
v_reuseFailAlloc_1955_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1955_, 0, v___x_1939_);
lean_ctor_set(v_reuseFailAlloc_1955_, 1, v___x_1940_);
v___x_1942_ = v_reuseFailAlloc_1955_;
goto v_reusejp_1941_;
}
v_reusejp_1941_:
{
lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v_a_1947_; lean_object* v___x_1949_; uint8_t v_isShared_1950_; uint8_t v_isSharedCheck_1954_; 
v___x_1943_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__10, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__10_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__10);
v___x_1944_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1944_, 0, v___x_1942_);
lean_ctor_set(v___x_1944_, 1, v___x_1943_);
v___x_1945_ = l_Lean_Meta_mkTacticExMsg(v_tacticName_1863_, v_mvarId_1864_, v___x_1944_);
v___x_1946_ = l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1___redArg(v___x_1938_, v___x_1945_, v___y_1871_, v___y_1872_, v___y_1873_, v___y_1874_);
v_a_1947_ = lean_ctor_get(v___x_1946_, 0);
v_isSharedCheck_1954_ = !lean_is_exclusive(v___x_1946_);
if (v_isSharedCheck_1954_ == 0)
{
v___x_1949_ = v___x_1946_;
v_isShared_1950_ = v_isSharedCheck_1954_;
goto v_resetjp_1948_;
}
else
{
lean_inc(v_a_1947_);
lean_dec(v___x_1946_);
v___x_1949_ = lean_box(0);
v_isShared_1950_ = v_isSharedCheck_1954_;
goto v_resetjp_1948_;
}
v_resetjp_1948_:
{
lean_object* v___x_1952_; 
if (v_isShared_1950_ == 0)
{
v___x_1952_ = v___x_1949_;
goto v_reusejp_1951_;
}
else
{
lean_object* v_reuseFailAlloc_1953_; 
v_reuseFailAlloc_1953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1953_, 0, v_a_1947_);
v___x_1952_ = v_reuseFailAlloc_1953_;
goto v_reusejp_1951_;
}
v_reusejp_1951_:
{
return v___x_1952_;
}
}
}
}
else
{
lean_del_object(v___x_1914_);
lean_dec(v_tacticName_1863_);
v___y_1917_ = v___y_1871_;
v___y_1918_ = v___y_1872_;
v___y_1919_ = v___y_1873_;
v___y_1920_ = v___y_1874_;
goto v___jp_1916_;
}
}
else
{
lean_del_object(v___x_1914_);
lean_dec(v_tacticName_1863_);
lean_dec(v_a_1862_);
v___y_1917_ = v___y_1871_;
v___y_1918_ = v___y_1872_;
v___y_1919_ = v___y_1873_;
v___y_1920_ = v___y_1874_;
goto v___jp_1916_;
}
v___jp_1916_:
{
lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; 
v___x_1921_ = lean_array_to_list(v_fst_1911_);
v___x_1922_ = l_Lean_mkConst(v_recursorName_1883_, v___x_1921_);
v___x_1923_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams(v_mvarId_1864_, v_x_1869_, v_paramsPos_1886_, v___x_1922_, v___y_1917_, v___y_1918_, v___y_1919_, v___y_1920_);
lean_dec_ref(v_x_1869_);
if (lean_obj_tag(v___x_1923_) == 0)
{
if (v_depElim_1885_ == 0)
{
lean_object* v_a_1924_; 
lean_dec_ref(v_major_1867_);
v_a_1924_ = lean_ctor_get(v___x_1923_, 0);
lean_inc(v_a_1924_);
lean_dec_ref(v___x_1923_);
v___y_1890_ = v_a_1924_;
v_motive_1891_ = v_a_1866_;
v___y_1892_ = v___y_1917_;
v___y_1893_ = v___y_1918_;
v___y_1894_ = v___y_1919_;
v___y_1895_ = v___y_1920_;
goto v___jp_1889_;
}
else
{
lean_object* v_a_1925_; lean_object* v___x_1926_; 
v_a_1925_ = lean_ctor_get(v___x_1923_, 0);
lean_inc(v_a_1925_);
lean_dec_ref(v___x_1923_);
lean_inc(v___y_1920_);
lean_inc_ref(v___y_1919_);
lean_inc(v___y_1918_);
lean_inc_ref(v___y_1917_);
lean_inc_ref(v_major_1867_);
v___x_1926_ = lean_infer_type(v_major_1867_, v___y_1917_, v___y_1918_, v___y_1919_, v___y_1920_);
if (lean_obj_tag(v___x_1926_) == 0)
{
lean_object* v_a_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; 
v_a_1927_ = lean_ctor_get(v___x_1926_, 0);
lean_inc(v_a_1927_);
lean_dec_ref(v___x_1926_);
v___x_1928_ = lean_unsigned_to_nat(1u);
v___x_1929_ = lean_mk_empty_array_with_capacity(v___x_1928_);
v___x_1930_ = lean_array_push(v___x_1929_, v_major_1867_);
v___x_1931_ = l_Lean_Expr_abstractM(v_a_1866_, v___x_1930_, v___y_1917_, v___y_1918_, v___y_1919_, v___y_1920_);
lean_dec_ref(v___x_1930_);
if (lean_obj_tag(v___x_1931_) == 0)
{
lean_object* v_a_1932_; lean_object* v___x_1933_; uint8_t v___x_1934_; lean_object* v___x_1935_; 
v_a_1932_ = lean_ctor_get(v___x_1931_, 0);
lean_inc(v_a_1932_);
lean_dec_ref(v___x_1931_);
v___x_1933_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__3));
v___x_1934_ = 0;
v___x_1935_ = l_Lean_mkLambda(v___x_1933_, v___x_1934_, v_a_1927_, v_a_1932_);
v___y_1890_ = v_a_1925_;
v_motive_1891_ = v___x_1935_;
v___y_1892_ = v___y_1917_;
v___y_1893_ = v___y_1918_;
v___y_1894_ = v___y_1919_;
v___y_1895_ = v___y_1920_;
goto v___jp_1889_;
}
else
{
lean_dec(v_a_1927_);
lean_dec(v_a_1925_);
return v___x_1931_;
}
}
else
{
lean_dec(v_a_1925_);
lean_dec_ref(v_major_1867_);
lean_dec_ref(v_a_1866_);
return v___x_1926_;
}
}
}
else
{
lean_dec_ref(v_major_1867_);
lean_dec_ref(v_a_1866_);
return v___x_1923_;
}
}
}
}
else
{
lean_object* v_a_1957_; lean_object* v___x_1959_; uint8_t v_isShared_1960_; uint8_t v_isSharedCheck_1964_; 
lean_dec(v_paramsPos_1886_);
lean_dec(v_recursorName_1883_);
lean_dec_ref(v_x_1869_);
lean_dec_ref(v_major_1867_);
lean_dec_ref(v_a_1866_);
lean_dec(v_mvarId_1864_);
lean_dec(v_tacticName_1863_);
lean_dec(v_a_1862_);
v_a_1957_ = lean_ctor_get(v___x_1909_, 0);
v_isSharedCheck_1964_ = !lean_is_exclusive(v___x_1909_);
if (v_isSharedCheck_1964_ == 0)
{
v___x_1959_ = v___x_1909_;
v_isShared_1960_ = v_isSharedCheck_1964_;
goto v_resetjp_1958_;
}
else
{
lean_inc(v_a_1957_);
lean_dec(v___x_1909_);
v___x_1959_ = lean_box(0);
v_isShared_1960_ = v_isSharedCheck_1964_;
goto v_resetjp_1958_;
}
v_resetjp_1958_:
{
lean_object* v___x_1962_; 
if (v_isShared_1960_ == 0)
{
v___x_1962_ = v___x_1959_;
goto v_reusejp_1961_;
}
else
{
lean_object* v_reuseFailAlloc_1963_; 
v_reuseFailAlloc_1963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1963_, 0, v_a_1957_);
v___x_1962_ = v_reuseFailAlloc_1963_;
goto v_reusejp_1961_;
}
v_reusejp_1961_:
{
return v___x_1962_;
}
}
}
v___jp_1889_:
{
uint8_t v___x_1896_; uint8_t v___x_1897_; lean_object* v___x_1898_; 
v___x_1896_ = 1;
v___x_1897_ = 1;
v___x_1898_ = l_Lean_Meta_mkLambdaFVars(v_indices_1865_, v_motive_1891_, v___x_1888_, v___x_1896_, v___x_1888_, v___x_1896_, v___x_1897_, v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_);
if (lean_obj_tag(v___x_1898_) == 0)
{
lean_object* v_a_1899_; lean_object* v___x_1901_; uint8_t v_isShared_1902_; uint8_t v_isSharedCheck_1907_; 
v_a_1899_ = lean_ctor_get(v___x_1898_, 0);
v_isSharedCheck_1907_ = !lean_is_exclusive(v___x_1898_);
if (v_isSharedCheck_1907_ == 0)
{
v___x_1901_ = v___x_1898_;
v_isShared_1902_ = v_isSharedCheck_1907_;
goto v_resetjp_1900_;
}
else
{
lean_inc(v_a_1899_);
lean_dec(v___x_1898_);
v___x_1901_ = lean_box(0);
v_isShared_1902_ = v_isSharedCheck_1907_;
goto v_resetjp_1900_;
}
v_resetjp_1900_:
{
lean_object* v___x_1903_; lean_object* v___x_1905_; 
v___x_1903_ = l_Lean_Expr_app___override(v___y_1890_, v_a_1899_);
if (v_isShared_1902_ == 0)
{
lean_ctor_set(v___x_1901_, 0, v___x_1903_);
v___x_1905_ = v___x_1901_;
goto v_reusejp_1904_;
}
else
{
lean_object* v_reuseFailAlloc_1906_; 
v_reuseFailAlloc_1906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1906_, 0, v___x_1903_);
v___x_1905_ = v_reuseFailAlloc_1906_;
goto v_reusejp_1904_;
}
v_reusejp_1904_:
{
return v___x_1905_;
}
}
}
else
{
lean_dec_ref(v___y_1890_);
return v___x_1898_;
}
}
}
else
{
lean_object* v___x_1965_; lean_object* v___x_1966_; 
lean_dec_ref(v_x_1869_);
lean_dec_ref(v_x_1868_);
lean_dec_ref(v_major_1867_);
lean_dec_ref(v_a_1866_);
lean_dec(v_a_1862_);
lean_dec_ref(v_recursorInfo_1861_);
v___x_1965_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__14, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__14_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__14);
v___x_1966_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1863_, v_mvarId_1864_, v___x_1965_, v___y_1871_, v___y_1872_, v___y_1873_, v___y_1874_);
return v___x_1966_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___boxed(lean_object* v_recursorInfo_1967_, lean_object* v_a_1968_, lean_object* v_tacticName_1969_, lean_object* v_mvarId_1970_, lean_object* v_indices_1971_, lean_object* v_a_1972_, lean_object* v_major_1973_, lean_object* v_x_1974_, lean_object* v_x_1975_, lean_object* v_x_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_){
_start:
{
lean_object* v_res_1982_; 
v_res_1982_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2(v_recursorInfo_1967_, v_a_1968_, v_tacticName_1969_, v_mvarId_1970_, v_indices_1971_, v_a_1972_, v_major_1973_, v_x_1974_, v_x_1975_, v_x_1976_, v___y_1977_, v___y_1978_, v___y_1979_, v___y_1980_);
lean_dec(v___y_1980_);
lean_dec_ref(v___y_1979_);
lean_dec(v___y_1978_);
lean_dec_ref(v___y_1977_);
lean_dec_ref(v_indices_1971_);
return v_res_1982_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2(lean_object* v_a_1983_, lean_object* v_tacticName_1984_, lean_object* v_mvarId_1985_, lean_object* v_recursorInfo_1986_, lean_object* v_indices_1987_, lean_object* v_a_1988_, lean_object* v_major_1989_, lean_object* v_x_1990_, lean_object* v_x_1991_, lean_object* v_x_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_){
_start:
{
if (lean_obj_tag(v_x_1990_) == 5)
{
lean_object* v_fn_1998_; lean_object* v_arg_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; 
v_fn_1998_ = lean_ctor_get(v_x_1990_, 0);
lean_inc_ref(v_fn_1998_);
v_arg_1999_ = lean_ctor_get(v_x_1990_, 1);
lean_inc_ref(v_arg_1999_);
lean_dec_ref(v_x_1990_);
v___x_2000_ = lean_array_set(v_x_1991_, v_x_1992_, v_arg_1999_);
v___x_2001_ = lean_unsigned_to_nat(1u);
v___x_2002_ = lean_nat_sub(v_x_1992_, v___x_2001_);
v___x_2003_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2(v_recursorInfo_1986_, v_a_1983_, v_tacticName_1984_, v_mvarId_1985_, v_indices_1987_, v_a_1988_, v_major_1989_, v_fn_1998_, v___x_2000_, v___x_2002_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_);
return v___x_2003_;
}
else
{
if (lean_obj_tag(v_x_1990_) == 4)
{
lean_object* v_us_2004_; lean_object* v_recursorName_2005_; lean_object* v_univLevelPos_2006_; uint8_t v_depElim_2007_; lean_object* v_paramsPos_2008_; lean_object* v___x_2009_; uint8_t v___x_2010_; lean_object* v___y_2012_; lean_object* v_motive_2013_; lean_object* v___y_2014_; lean_object* v___y_2015_; lean_object* v___y_2016_; lean_object* v___y_2017_; lean_object* v___x_2030_; lean_object* v___x_2031_; 
v_us_2004_ = lean_ctor_get(v_x_1990_, 1);
lean_inc(v_us_2004_);
lean_dec_ref(v_x_1990_);
v_recursorName_2005_ = lean_ctor_get(v_recursorInfo_1986_, 0);
lean_inc(v_recursorName_2005_);
v_univLevelPos_2006_ = lean_ctor_get(v_recursorInfo_1986_, 2);
lean_inc(v_univLevelPos_2006_);
v_depElim_2007_ = lean_ctor_get_uint8(v_recursorInfo_1986_, sizeof(void*)*8);
v_paramsPos_2008_ = lean_ctor_get(v_recursorInfo_1986_, 5);
lean_inc(v_paramsPos_2008_);
lean_dec_ref(v_recursorInfo_1986_);
v___x_2009_ = lean_array_mk(v_us_2004_);
v___x_2010_ = 0;
v___x_2030_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__1));
lean_inc(v_mvarId_1985_);
lean_inc(v_tacticName_1984_);
lean_inc(v_a_1983_);
v___x_2031_ = l_List_foldlM___at___00Lean_Meta_mkRecursorAppPrefix_spec__0(v_a_1983_, v___x_2009_, v_tacticName_1984_, v_mvarId_1985_, v___x_2030_, v_univLevelPos_2006_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_);
lean_dec(v_univLevelPos_2006_);
lean_dec_ref(v___x_2009_);
if (lean_obj_tag(v___x_2031_) == 0)
{
lean_object* v_a_2032_; lean_object* v_fst_2033_; lean_object* v_snd_2034_; lean_object* v___x_2036_; uint8_t v_isShared_2037_; uint8_t v_isSharedCheck_2078_; 
v_a_2032_ = lean_ctor_get(v___x_2031_, 0);
lean_inc(v_a_2032_);
lean_dec_ref(v___x_2031_);
v_fst_2033_ = lean_ctor_get(v_a_2032_, 0);
v_snd_2034_ = lean_ctor_get(v_a_2032_, 1);
v_isSharedCheck_2078_ = !lean_is_exclusive(v_a_2032_);
if (v_isSharedCheck_2078_ == 0)
{
v___x_2036_ = v_a_2032_;
v_isShared_2037_ = v_isSharedCheck_2078_;
goto v_resetjp_2035_;
}
else
{
lean_inc(v_snd_2034_);
lean_inc(v_fst_2033_);
lean_dec(v_a_2032_);
v___x_2036_ = lean_box(0);
v_isShared_2037_ = v_isSharedCheck_2078_;
goto v_resetjp_2035_;
}
v_resetjp_2035_:
{
lean_object* v___y_2039_; lean_object* v___y_2040_; lean_object* v___y_2041_; lean_object* v___y_2042_; uint8_t v___x_2058_; 
v___x_2058_ = lean_unbox(v_snd_2034_);
lean_dec(v_snd_2034_);
if (v___x_2058_ == 0)
{
uint8_t v___x_2059_; 
v___x_2059_ = l_Lean_Level_isZero(v_a_1983_);
lean_dec(v_a_1983_);
if (v___x_2059_ == 0)
{
lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2064_; 
lean_dec(v_fst_2033_);
lean_dec(v_paramsPos_2008_);
lean_dec_ref(v_x_1991_);
lean_dec_ref(v_major_1989_);
lean_dec_ref(v_a_1988_);
v___x_2060_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__6));
v___x_2061_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__8, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__8_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__8);
v___x_2062_ = l_Lean_MessageData_ofName(v_recursorName_2005_);
if (v_isShared_2037_ == 0)
{
lean_ctor_set_tag(v___x_2036_, 7);
lean_ctor_set(v___x_2036_, 1, v___x_2062_);
lean_ctor_set(v___x_2036_, 0, v___x_2061_);
v___x_2064_ = v___x_2036_;
goto v_reusejp_2063_;
}
else
{
lean_object* v_reuseFailAlloc_2077_; 
v_reuseFailAlloc_2077_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2077_, 0, v___x_2061_);
lean_ctor_set(v_reuseFailAlloc_2077_, 1, v___x_2062_);
v___x_2064_ = v_reuseFailAlloc_2077_;
goto v_reusejp_2063_;
}
v_reusejp_2063_:
{
lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v_a_2069_; lean_object* v___x_2071_; uint8_t v_isShared_2072_; uint8_t v_isSharedCheck_2076_; 
v___x_2065_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__10, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__10_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__10);
v___x_2066_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2066_, 0, v___x_2064_);
lean_ctor_set(v___x_2066_, 1, v___x_2065_);
v___x_2067_ = l_Lean_Meta_mkTacticExMsg(v_tacticName_1984_, v_mvarId_1985_, v___x_2066_);
v___x_2068_ = l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1___redArg(v___x_2060_, v___x_2067_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_);
v_a_2069_ = lean_ctor_get(v___x_2068_, 0);
v_isSharedCheck_2076_ = !lean_is_exclusive(v___x_2068_);
if (v_isSharedCheck_2076_ == 0)
{
v___x_2071_ = v___x_2068_;
v_isShared_2072_ = v_isSharedCheck_2076_;
goto v_resetjp_2070_;
}
else
{
lean_inc(v_a_2069_);
lean_dec(v___x_2068_);
v___x_2071_ = lean_box(0);
v_isShared_2072_ = v_isSharedCheck_2076_;
goto v_resetjp_2070_;
}
v_resetjp_2070_:
{
lean_object* v___x_2074_; 
if (v_isShared_2072_ == 0)
{
v___x_2074_ = v___x_2071_;
goto v_reusejp_2073_;
}
else
{
lean_object* v_reuseFailAlloc_2075_; 
v_reuseFailAlloc_2075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2075_, 0, v_a_2069_);
v___x_2074_ = v_reuseFailAlloc_2075_;
goto v_reusejp_2073_;
}
v_reusejp_2073_:
{
return v___x_2074_;
}
}
}
}
else
{
lean_del_object(v___x_2036_);
lean_dec(v_tacticName_1984_);
v___y_2039_ = v___y_1993_;
v___y_2040_ = v___y_1994_;
v___y_2041_ = v___y_1995_;
v___y_2042_ = v___y_1996_;
goto v___jp_2038_;
}
}
else
{
lean_del_object(v___x_2036_);
lean_dec(v_tacticName_1984_);
lean_dec(v_a_1983_);
v___y_2039_ = v___y_1993_;
v___y_2040_ = v___y_1994_;
v___y_2041_ = v___y_1995_;
v___y_2042_ = v___y_1996_;
goto v___jp_2038_;
}
v___jp_2038_:
{
lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; 
v___x_2043_ = lean_array_to_list(v_fst_2033_);
v___x_2044_ = l_Lean_mkConst(v_recursorName_2005_, v___x_2043_);
v___x_2045_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams(v_mvarId_1985_, v_x_1991_, v_paramsPos_2008_, v___x_2044_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_);
lean_dec_ref(v_x_1991_);
if (lean_obj_tag(v___x_2045_) == 0)
{
if (v_depElim_2007_ == 0)
{
lean_object* v_a_2046_; 
lean_dec_ref(v_major_1989_);
v_a_2046_ = lean_ctor_get(v___x_2045_, 0);
lean_inc(v_a_2046_);
lean_dec_ref(v___x_2045_);
v___y_2012_ = v_a_2046_;
v_motive_2013_ = v_a_1988_;
v___y_2014_ = v___y_2039_;
v___y_2015_ = v___y_2040_;
v___y_2016_ = v___y_2041_;
v___y_2017_ = v___y_2042_;
goto v___jp_2011_;
}
else
{
lean_object* v_a_2047_; lean_object* v___x_2048_; 
v_a_2047_ = lean_ctor_get(v___x_2045_, 0);
lean_inc(v_a_2047_);
lean_dec_ref(v___x_2045_);
lean_inc(v___y_2042_);
lean_inc_ref(v___y_2041_);
lean_inc(v___y_2040_);
lean_inc_ref(v___y_2039_);
lean_inc_ref(v_major_1989_);
v___x_2048_ = lean_infer_type(v_major_1989_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_);
if (lean_obj_tag(v___x_2048_) == 0)
{
lean_object* v_a_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; 
v_a_2049_ = lean_ctor_get(v___x_2048_, 0);
lean_inc(v_a_2049_);
lean_dec_ref(v___x_2048_);
v___x_2050_ = lean_unsigned_to_nat(1u);
v___x_2051_ = lean_mk_empty_array_with_capacity(v___x_2050_);
v___x_2052_ = lean_array_push(v___x_2051_, v_major_1989_);
v___x_2053_ = l_Lean_Expr_abstractM(v_a_1988_, v___x_2052_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_);
lean_dec_ref(v___x_2052_);
if (lean_obj_tag(v___x_2053_) == 0)
{
lean_object* v_a_2054_; lean_object* v___x_2055_; uint8_t v___x_2056_; lean_object* v___x_2057_; 
v_a_2054_ = lean_ctor_get(v___x_2053_, 0);
lean_inc(v_a_2054_);
lean_dec_ref(v___x_2053_);
v___x_2055_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__3));
v___x_2056_ = 0;
v___x_2057_ = l_Lean_mkLambda(v___x_2055_, v___x_2056_, v_a_2049_, v_a_2054_);
v___y_2012_ = v_a_2047_;
v_motive_2013_ = v___x_2057_;
v___y_2014_ = v___y_2039_;
v___y_2015_ = v___y_2040_;
v___y_2016_ = v___y_2041_;
v___y_2017_ = v___y_2042_;
goto v___jp_2011_;
}
else
{
lean_dec(v_a_2049_);
lean_dec(v_a_2047_);
return v___x_2053_;
}
}
else
{
lean_dec(v_a_2047_);
lean_dec_ref(v_major_1989_);
lean_dec_ref(v_a_1988_);
return v___x_2048_;
}
}
}
else
{
lean_dec_ref(v_major_1989_);
lean_dec_ref(v_a_1988_);
return v___x_2045_;
}
}
}
}
else
{
lean_object* v_a_2079_; lean_object* v___x_2081_; uint8_t v_isShared_2082_; uint8_t v_isSharedCheck_2086_; 
lean_dec(v_paramsPos_2008_);
lean_dec(v_recursorName_2005_);
lean_dec_ref(v_x_1991_);
lean_dec_ref(v_major_1989_);
lean_dec_ref(v_a_1988_);
lean_dec(v_mvarId_1985_);
lean_dec(v_tacticName_1984_);
lean_dec(v_a_1983_);
v_a_2079_ = lean_ctor_get(v___x_2031_, 0);
v_isSharedCheck_2086_ = !lean_is_exclusive(v___x_2031_);
if (v_isSharedCheck_2086_ == 0)
{
v___x_2081_ = v___x_2031_;
v_isShared_2082_ = v_isSharedCheck_2086_;
goto v_resetjp_2080_;
}
else
{
lean_inc(v_a_2079_);
lean_dec(v___x_2031_);
v___x_2081_ = lean_box(0);
v_isShared_2082_ = v_isSharedCheck_2086_;
goto v_resetjp_2080_;
}
v_resetjp_2080_:
{
lean_object* v___x_2084_; 
if (v_isShared_2082_ == 0)
{
v___x_2084_ = v___x_2081_;
goto v_reusejp_2083_;
}
else
{
lean_object* v_reuseFailAlloc_2085_; 
v_reuseFailAlloc_2085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2085_, 0, v_a_2079_);
v___x_2084_ = v_reuseFailAlloc_2085_;
goto v_reusejp_2083_;
}
v_reusejp_2083_:
{
return v___x_2084_;
}
}
}
v___jp_2011_:
{
uint8_t v___x_2018_; uint8_t v___x_2019_; lean_object* v___x_2020_; 
v___x_2018_ = 1;
v___x_2019_ = 1;
v___x_2020_ = l_Lean_Meta_mkLambdaFVars(v_indices_1987_, v_motive_2013_, v___x_2010_, v___x_2018_, v___x_2010_, v___x_2018_, v___x_2019_, v___y_2014_, v___y_2015_, v___y_2016_, v___y_2017_);
if (lean_obj_tag(v___x_2020_) == 0)
{
lean_object* v_a_2021_; lean_object* v___x_2023_; uint8_t v_isShared_2024_; uint8_t v_isSharedCheck_2029_; 
v_a_2021_ = lean_ctor_get(v___x_2020_, 0);
v_isSharedCheck_2029_ = !lean_is_exclusive(v___x_2020_);
if (v_isSharedCheck_2029_ == 0)
{
v___x_2023_ = v___x_2020_;
v_isShared_2024_ = v_isSharedCheck_2029_;
goto v_resetjp_2022_;
}
else
{
lean_inc(v_a_2021_);
lean_dec(v___x_2020_);
v___x_2023_ = lean_box(0);
v_isShared_2024_ = v_isSharedCheck_2029_;
goto v_resetjp_2022_;
}
v_resetjp_2022_:
{
lean_object* v___x_2025_; lean_object* v___x_2027_; 
v___x_2025_ = l_Lean_Expr_app___override(v___y_2012_, v_a_2021_);
if (v_isShared_2024_ == 0)
{
lean_ctor_set(v___x_2023_, 0, v___x_2025_);
v___x_2027_ = v___x_2023_;
goto v_reusejp_2026_;
}
else
{
lean_object* v_reuseFailAlloc_2028_; 
v_reuseFailAlloc_2028_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2028_, 0, v___x_2025_);
v___x_2027_ = v_reuseFailAlloc_2028_;
goto v_reusejp_2026_;
}
v_reusejp_2026_:
{
return v___x_2027_;
}
}
}
else
{
lean_dec_ref(v___y_2012_);
return v___x_2020_;
}
}
}
else
{
lean_object* v___x_2087_; lean_object* v___x_2088_; 
lean_dec_ref(v_x_1991_);
lean_dec_ref(v_x_1990_);
lean_dec_ref(v_major_1989_);
lean_dec_ref(v_a_1988_);
lean_dec_ref(v_recursorInfo_1986_);
lean_dec(v_a_1983_);
v___x_2087_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__14, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__14_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__14);
v___x_2088_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1984_, v_mvarId_1985_, v___x_2087_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_);
return v___x_2088_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2___boxed(lean_object* v_a_2089_, lean_object* v_tacticName_2090_, lean_object* v_mvarId_2091_, lean_object* v_recursorInfo_2092_, lean_object* v_indices_2093_, lean_object* v_a_2094_, lean_object* v_major_2095_, lean_object* v_x_2096_, lean_object* v_x_2097_, lean_object* v_x_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_){
_start:
{
lean_object* v_res_2104_; 
v_res_2104_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2(v_a_2089_, v_tacticName_2090_, v_mvarId_2091_, v_recursorInfo_2092_, v_indices_2093_, v_a_2094_, v_major_2095_, v_x_2096_, v_x_2097_, v_x_2098_, v___y_2099_, v___y_2100_, v___y_2101_, v___y_2102_);
lean_dec(v___y_2102_);
lean_dec_ref(v___y_2101_);
lean_dec(v___y_2100_);
lean_dec_ref(v___y_2099_);
lean_dec(v_x_2098_);
lean_dec_ref(v_indices_2093_);
return v_res_2104_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkRecursorAppPrefix(lean_object* v_mvarId_2105_, lean_object* v_tacticName_2106_, lean_object* v_majorFVarId_2107_, lean_object* v_recursorInfo_2108_, lean_object* v_indices_2109_, lean_object* v_a_2110_, lean_object* v_a_2111_, lean_object* v_a_2112_, lean_object* v_a_2113_){
_start:
{
lean_object* v___x_2115_; 
lean_inc(v_mvarId_2105_);
v___x_2115_ = l_Lean_MVarId_getType(v_mvarId_2105_, v_a_2110_, v_a_2111_, v_a_2112_, v_a_2113_);
if (lean_obj_tag(v___x_2115_) == 0)
{
lean_object* v_a_2116_; lean_object* v___x_2117_; 
v_a_2116_ = lean_ctor_get(v___x_2115_, 0);
lean_inc_n(v_a_2116_, 2);
lean_dec_ref(v___x_2115_);
v___x_2117_ = l_Lean_Meta_getLevel(v_a_2116_, v_a_2110_, v_a_2111_, v_a_2112_, v_a_2113_);
if (lean_obj_tag(v___x_2117_) == 0)
{
lean_object* v_a_2118_; lean_object* v___x_2119_; 
v_a_2118_ = lean_ctor_get(v___x_2117_, 0);
lean_inc(v_a_2118_);
lean_dec_ref(v___x_2117_);
v___x_2119_ = l_Lean_Meta_normalizeLevel(v_a_2118_, v_a_2110_, v_a_2111_, v_a_2112_, v_a_2113_);
if (lean_obj_tag(v___x_2119_) == 0)
{
lean_object* v_a_2120_; lean_object* v_major_2121_; lean_object* v___x_2122_; 
v_a_2120_ = lean_ctor_get(v___x_2119_, 0);
lean_inc(v_a_2120_);
lean_dec_ref(v___x_2119_);
lean_inc(v_majorFVarId_2107_);
v_major_2121_ = l_Lean_mkFVar(v_majorFVarId_2107_);
v___x_2122_ = l_Lean_FVarId_getDecl___redArg(v_majorFVarId_2107_, v_a_2110_, v_a_2112_, v_a_2113_);
if (lean_obj_tag(v___x_2122_) == 0)
{
lean_object* v_a_2123_; lean_object* v_typeName_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; 
v_a_2123_ = lean_ctor_get(v___x_2122_, 0);
lean_inc(v_a_2123_);
lean_dec_ref(v___x_2122_);
v_typeName_2124_ = lean_ctor_get(v_recursorInfo_2108_, 1);
v___x_2125_ = l_Lean_LocalDecl_type(v_a_2123_);
lean_dec(v_a_2123_);
lean_inc_ref(v___x_2125_);
v___x_2126_ = l_Lean_Meta_whnfUntil(v___x_2125_, v_typeName_2124_, v_a_2110_, v_a_2111_, v_a_2112_, v_a_2113_);
if (lean_obj_tag(v___x_2126_) == 0)
{
lean_object* v_a_2127_; 
v_a_2127_ = lean_ctor_get(v___x_2126_, 0);
lean_inc(v_a_2127_);
lean_dec_ref(v___x_2126_);
if (lean_obj_tag(v_a_2127_) == 1)
{
lean_object* v_val_2128_; lean_object* v_dummy_2129_; lean_object* v_nargs_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; 
lean_dec_ref(v___x_2125_);
v_val_2128_ = lean_ctor_get(v_a_2127_, 0);
lean_inc(v_val_2128_);
lean_dec_ref(v_a_2127_);
v_dummy_2129_ = lean_obj_once(&l_Lean_Meta_getMajorTypeIndices___closed__0, &l_Lean_Meta_getMajorTypeIndices___closed__0_once, _init_l_Lean_Meta_getMajorTypeIndices___closed__0);
v_nargs_2130_ = l_Lean_Expr_getAppNumArgs(v_val_2128_);
lean_inc(v_nargs_2130_);
v___x_2131_ = lean_mk_array(v_nargs_2130_, v_dummy_2129_);
v___x_2132_ = lean_unsigned_to_nat(1u);
v___x_2133_ = lean_nat_sub(v_nargs_2130_, v___x_2132_);
lean_dec(v_nargs_2130_);
v___x_2134_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2(v_a_2120_, v_tacticName_2106_, v_mvarId_2105_, v_recursorInfo_2108_, v_indices_2109_, v_a_2116_, v_major_2121_, v_val_2128_, v___x_2131_, v___x_2133_, v_a_2110_, v_a_2111_, v_a_2112_, v_a_2113_);
lean_dec(v___x_2133_);
return v___x_2134_;
}
else
{
lean_object* v___x_2135_; 
lean_dec(v_a_2127_);
lean_dec_ref(v_major_2121_);
lean_dec(v_a_2120_);
lean_dec(v_a_2116_);
lean_dec_ref(v_recursorInfo_2108_);
v___x_2135_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg(v_tacticName_2106_, v_mvarId_2105_, v___x_2125_, v_a_2110_, v_a_2111_, v_a_2112_, v_a_2113_);
return v___x_2135_;
}
}
else
{
lean_object* v_a_2136_; lean_object* v___x_2138_; uint8_t v_isShared_2139_; uint8_t v_isSharedCheck_2143_; 
lean_dec_ref(v___x_2125_);
lean_dec_ref(v_major_2121_);
lean_dec(v_a_2120_);
lean_dec(v_a_2116_);
lean_dec_ref(v_recursorInfo_2108_);
lean_dec(v_tacticName_2106_);
lean_dec(v_mvarId_2105_);
v_a_2136_ = lean_ctor_get(v___x_2126_, 0);
v_isSharedCheck_2143_ = !lean_is_exclusive(v___x_2126_);
if (v_isSharedCheck_2143_ == 0)
{
v___x_2138_ = v___x_2126_;
v_isShared_2139_ = v_isSharedCheck_2143_;
goto v_resetjp_2137_;
}
else
{
lean_inc(v_a_2136_);
lean_dec(v___x_2126_);
v___x_2138_ = lean_box(0);
v_isShared_2139_ = v_isSharedCheck_2143_;
goto v_resetjp_2137_;
}
v_resetjp_2137_:
{
lean_object* v___x_2141_; 
if (v_isShared_2139_ == 0)
{
v___x_2141_ = v___x_2138_;
goto v_reusejp_2140_;
}
else
{
lean_object* v_reuseFailAlloc_2142_; 
v_reuseFailAlloc_2142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2142_, 0, v_a_2136_);
v___x_2141_ = v_reuseFailAlloc_2142_;
goto v_reusejp_2140_;
}
v_reusejp_2140_:
{
return v___x_2141_;
}
}
}
}
else
{
lean_object* v_a_2144_; lean_object* v___x_2146_; uint8_t v_isShared_2147_; uint8_t v_isSharedCheck_2151_; 
lean_dec_ref(v_major_2121_);
lean_dec(v_a_2120_);
lean_dec(v_a_2116_);
lean_dec_ref(v_recursorInfo_2108_);
lean_dec(v_tacticName_2106_);
lean_dec(v_mvarId_2105_);
v_a_2144_ = lean_ctor_get(v___x_2122_, 0);
v_isSharedCheck_2151_ = !lean_is_exclusive(v___x_2122_);
if (v_isSharedCheck_2151_ == 0)
{
v___x_2146_ = v___x_2122_;
v_isShared_2147_ = v_isSharedCheck_2151_;
goto v_resetjp_2145_;
}
else
{
lean_inc(v_a_2144_);
lean_dec(v___x_2122_);
v___x_2146_ = lean_box(0);
v_isShared_2147_ = v_isSharedCheck_2151_;
goto v_resetjp_2145_;
}
v_resetjp_2145_:
{
lean_object* v___x_2149_; 
if (v_isShared_2147_ == 0)
{
v___x_2149_ = v___x_2146_;
goto v_reusejp_2148_;
}
else
{
lean_object* v_reuseFailAlloc_2150_; 
v_reuseFailAlloc_2150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2150_, 0, v_a_2144_);
v___x_2149_ = v_reuseFailAlloc_2150_;
goto v_reusejp_2148_;
}
v_reusejp_2148_:
{
return v___x_2149_;
}
}
}
}
else
{
lean_object* v_a_2152_; lean_object* v___x_2154_; uint8_t v_isShared_2155_; uint8_t v_isSharedCheck_2159_; 
lean_dec(v_a_2116_);
lean_dec_ref(v_recursorInfo_2108_);
lean_dec(v_majorFVarId_2107_);
lean_dec(v_tacticName_2106_);
lean_dec(v_mvarId_2105_);
v_a_2152_ = lean_ctor_get(v___x_2119_, 0);
v_isSharedCheck_2159_ = !lean_is_exclusive(v___x_2119_);
if (v_isSharedCheck_2159_ == 0)
{
v___x_2154_ = v___x_2119_;
v_isShared_2155_ = v_isSharedCheck_2159_;
goto v_resetjp_2153_;
}
else
{
lean_inc(v_a_2152_);
lean_dec(v___x_2119_);
v___x_2154_ = lean_box(0);
v_isShared_2155_ = v_isSharedCheck_2159_;
goto v_resetjp_2153_;
}
v_resetjp_2153_:
{
lean_object* v___x_2157_; 
if (v_isShared_2155_ == 0)
{
v___x_2157_ = v___x_2154_;
goto v_reusejp_2156_;
}
else
{
lean_object* v_reuseFailAlloc_2158_; 
v_reuseFailAlloc_2158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2158_, 0, v_a_2152_);
v___x_2157_ = v_reuseFailAlloc_2158_;
goto v_reusejp_2156_;
}
v_reusejp_2156_:
{
return v___x_2157_;
}
}
}
}
else
{
lean_object* v_a_2160_; lean_object* v___x_2162_; uint8_t v_isShared_2163_; uint8_t v_isSharedCheck_2167_; 
lean_dec(v_a_2116_);
lean_dec_ref(v_recursorInfo_2108_);
lean_dec(v_majorFVarId_2107_);
lean_dec(v_tacticName_2106_);
lean_dec(v_mvarId_2105_);
v_a_2160_ = lean_ctor_get(v___x_2117_, 0);
v_isSharedCheck_2167_ = !lean_is_exclusive(v___x_2117_);
if (v_isSharedCheck_2167_ == 0)
{
v___x_2162_ = v___x_2117_;
v_isShared_2163_ = v_isSharedCheck_2167_;
goto v_resetjp_2161_;
}
else
{
lean_inc(v_a_2160_);
lean_dec(v___x_2117_);
v___x_2162_ = lean_box(0);
v_isShared_2163_ = v_isSharedCheck_2167_;
goto v_resetjp_2161_;
}
v_resetjp_2161_:
{
lean_object* v___x_2165_; 
if (v_isShared_2163_ == 0)
{
v___x_2165_ = v___x_2162_;
goto v_reusejp_2164_;
}
else
{
lean_object* v_reuseFailAlloc_2166_; 
v_reuseFailAlloc_2166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2166_, 0, v_a_2160_);
v___x_2165_ = v_reuseFailAlloc_2166_;
goto v_reusejp_2164_;
}
v_reusejp_2164_:
{
return v___x_2165_;
}
}
}
}
else
{
lean_dec_ref(v_recursorInfo_2108_);
lean_dec(v_majorFVarId_2107_);
lean_dec(v_tacticName_2106_);
lean_dec(v_mvarId_2105_);
return v___x_2115_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkRecursorAppPrefix___boxed(lean_object* v_mvarId_2168_, lean_object* v_tacticName_2169_, lean_object* v_majorFVarId_2170_, lean_object* v_recursorInfo_2171_, lean_object* v_indices_2172_, lean_object* v_a_2173_, lean_object* v_a_2174_, lean_object* v_a_2175_, lean_object* v_a_2176_, lean_object* v_a_2177_){
_start:
{
lean_object* v_res_2178_; 
v_res_2178_ = l_Lean_Meta_mkRecursorAppPrefix(v_mvarId_2168_, v_tacticName_2169_, v_majorFVarId_2170_, v_recursorInfo_2171_, v_indices_2172_, v_a_2173_, v_a_2174_, v_a_2175_, v_a_2176_);
lean_dec(v_a_2176_);
lean_dec_ref(v_a_2175_);
lean_dec(v_a_2174_);
lean_dec_ref(v_a_2173_);
lean_dec_ref(v_indices_2172_);
return v_res_2178_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1(lean_object* v_00_u03b1_2179_, lean_object* v_name_2180_, lean_object* v_msg_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_){
_start:
{
lean_object* v___x_2187_; 
v___x_2187_ = l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1___redArg(v_name_2180_, v_msg_2181_, v___y_2182_, v___y_2183_, v___y_2184_, v___y_2185_);
return v___x_2187_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1___boxed(lean_object* v_00_u03b1_2188_, lean_object* v_name_2189_, lean_object* v_msg_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_){
_start:
{
lean_object* v_res_2196_; 
v_res_2196_ = l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1(v_00_u03b1_2188_, v_name_2189_, v_msg_2190_, v___y_2191_, v___y_2192_, v___y_2193_, v___y_2194_);
lean_dec(v___y_2194_);
lean_dec_ref(v___y_2193_);
lean_dec(v___y_2192_);
lean_dec_ref(v___y_2191_);
return v_res_2196_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___redArg(lean_object* v_mvarId_2197_, lean_object* v_x_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_){
_start:
{
lean_object* v___x_2204_; 
v___x_2204_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_2197_, v_x_2198_, v___y_2199_, v___y_2200_, v___y_2201_, v___y_2202_);
if (lean_obj_tag(v___x_2204_) == 0)
{
lean_object* v_a_2205_; lean_object* v___x_2207_; uint8_t v_isShared_2208_; uint8_t v_isSharedCheck_2212_; 
v_a_2205_ = lean_ctor_get(v___x_2204_, 0);
v_isSharedCheck_2212_ = !lean_is_exclusive(v___x_2204_);
if (v_isSharedCheck_2212_ == 0)
{
v___x_2207_ = v___x_2204_;
v_isShared_2208_ = v_isSharedCheck_2212_;
goto v_resetjp_2206_;
}
else
{
lean_inc(v_a_2205_);
lean_dec(v___x_2204_);
v___x_2207_ = lean_box(0);
v_isShared_2208_ = v_isSharedCheck_2212_;
goto v_resetjp_2206_;
}
v_resetjp_2206_:
{
lean_object* v___x_2210_; 
if (v_isShared_2208_ == 0)
{
v___x_2210_ = v___x_2207_;
goto v_reusejp_2209_;
}
else
{
lean_object* v_reuseFailAlloc_2211_; 
v_reuseFailAlloc_2211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2211_, 0, v_a_2205_);
v___x_2210_ = v_reuseFailAlloc_2211_;
goto v_reusejp_2209_;
}
v_reusejp_2209_:
{
return v___x_2210_;
}
}
}
else
{
lean_object* v_a_2213_; lean_object* v___x_2215_; uint8_t v_isShared_2216_; uint8_t v_isSharedCheck_2220_; 
v_a_2213_ = lean_ctor_get(v___x_2204_, 0);
v_isSharedCheck_2220_ = !lean_is_exclusive(v___x_2204_);
if (v_isSharedCheck_2220_ == 0)
{
v___x_2215_ = v___x_2204_;
v_isShared_2216_ = v_isSharedCheck_2220_;
goto v_resetjp_2214_;
}
else
{
lean_inc(v_a_2213_);
lean_dec(v___x_2204_);
v___x_2215_ = lean_box(0);
v_isShared_2216_ = v_isSharedCheck_2220_;
goto v_resetjp_2214_;
}
v_resetjp_2214_:
{
lean_object* v___x_2218_; 
if (v_isShared_2216_ == 0)
{
v___x_2218_ = v___x_2215_;
goto v_reusejp_2217_;
}
else
{
lean_object* v_reuseFailAlloc_2219_; 
v_reuseFailAlloc_2219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2219_, 0, v_a_2213_);
v___x_2218_ = v_reuseFailAlloc_2219_;
goto v_reusejp_2217_;
}
v_reusejp_2217_:
{
return v___x_2218_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___redArg___boxed(lean_object* v_mvarId_2221_, lean_object* v_x_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_){
_start:
{
lean_object* v_res_2228_; 
v_res_2228_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___redArg(v_mvarId_2221_, v_x_2222_, v___y_2223_, v___y_2224_, v___y_2225_, v___y_2226_);
lean_dec(v___y_2226_);
lean_dec_ref(v___y_2225_);
lean_dec(v___y_2224_);
lean_dec_ref(v___y_2223_);
return v_res_2228_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3(lean_object* v_00_u03b1_2229_, lean_object* v_mvarId_2230_, lean_object* v_x_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_){
_start:
{
lean_object* v___x_2237_; 
v___x_2237_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___redArg(v_mvarId_2230_, v_x_2231_, v___y_2232_, v___y_2233_, v___y_2234_, v___y_2235_);
return v___x_2237_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___boxed(lean_object* v_00_u03b1_2238_, lean_object* v_mvarId_2239_, lean_object* v_x_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_){
_start:
{
lean_object* v_res_2246_; 
v_res_2246_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3(v_00_u03b1_2238_, v_mvarId_2239_, v_x_2240_, v___y_2241_, v___y_2242_, v___y_2243_, v___y_2244_);
lean_dec(v___y_2244_);
lean_dec_ref(v___y_2243_);
lean_dec(v___y_2242_);
lean_dec_ref(v___y_2241_);
return v_res_2246_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_induction_spec__2(lean_object* v_fst_2247_, lean_object* v_as_2248_, size_t v_sz_2249_, size_t v_i_2250_, lean_object* v_b_2251_){
_start:
{
uint8_t v___x_2252_; 
v___x_2252_ = lean_usize_dec_lt(v_i_2250_, v_sz_2249_);
if (v___x_2252_ == 0)
{
return v_b_2251_;
}
else
{
lean_object* v_fst_2253_; lean_object* v_snd_2254_; lean_object* v___x_2256_; uint8_t v_isShared_2257_; uint8_t v_isSharedCheck_2272_; 
v_fst_2253_ = lean_ctor_get(v_b_2251_, 0);
v_snd_2254_ = lean_ctor_get(v_b_2251_, 1);
v_isSharedCheck_2272_ = !lean_is_exclusive(v_b_2251_);
if (v_isSharedCheck_2272_ == 0)
{
v___x_2256_ = v_b_2251_;
v_isShared_2257_ = v_isSharedCheck_2272_;
goto v_resetjp_2255_;
}
else
{
lean_inc(v_snd_2254_);
lean_inc(v_fst_2253_);
lean_dec(v_b_2251_);
v___x_2256_ = lean_box(0);
v_isShared_2257_ = v_isSharedCheck_2272_;
goto v_resetjp_2255_;
}
v_resetjp_2255_:
{
lean_object* v___x_2258_; lean_object* v_a_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2267_; 
v___x_2258_ = lean_box(0);
v_a_2259_ = lean_array_uget_borrowed(v_as_2248_, v_i_2250_);
v___x_2260_ = l_Lean_Expr_fvarId_x21(v_a_2259_);
v___x_2261_ = lean_array_get_borrowed(v___x_2258_, v_fst_2247_, v_snd_2254_);
lean_inc(v___x_2261_);
v___x_2262_ = l_Lean_mkFVar(v___x_2261_);
v___x_2263_ = l_Lean_Meta_FVarSubst_insert(v_fst_2253_, v___x_2260_, v___x_2262_);
v___x_2264_ = lean_unsigned_to_nat(1u);
v___x_2265_ = lean_nat_add(v_snd_2254_, v___x_2264_);
lean_dec(v_snd_2254_);
if (v_isShared_2257_ == 0)
{
lean_ctor_set(v___x_2256_, 1, v___x_2265_);
lean_ctor_set(v___x_2256_, 0, v___x_2263_);
v___x_2267_ = v___x_2256_;
goto v_reusejp_2266_;
}
else
{
lean_object* v_reuseFailAlloc_2271_; 
v_reuseFailAlloc_2271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2271_, 0, v___x_2263_);
lean_ctor_set(v_reuseFailAlloc_2271_, 1, v___x_2265_);
v___x_2267_ = v_reuseFailAlloc_2271_;
goto v_reusejp_2266_;
}
v_reusejp_2266_:
{
size_t v___x_2268_; size_t v___x_2269_; 
v___x_2268_ = ((size_t)1ULL);
v___x_2269_ = lean_usize_add(v_i_2250_, v___x_2268_);
v_i_2250_ = v___x_2269_;
v_b_2251_ = v___x_2267_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_induction_spec__2___boxed(lean_object* v_fst_2273_, lean_object* v_as_2274_, lean_object* v_sz_2275_, lean_object* v_i_2276_, lean_object* v_b_2277_){
_start:
{
size_t v_sz_boxed_2278_; size_t v_i_boxed_2279_; lean_object* v_res_2280_; 
v_sz_boxed_2278_ = lean_unbox_usize(v_sz_2275_);
lean_dec(v_sz_2275_);
v_i_boxed_2279_ = lean_unbox_usize(v_i_2276_);
lean_dec(v_i_2276_);
v_res_2280_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_induction_spec__2(v_fst_2273_, v_as_2274_, v_sz_boxed_2278_, v_i_boxed_2279_, v_b_2277_);
lean_dec_ref(v_as_2274_);
lean_dec_ref(v_fst_2273_);
return v_res_2280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4___lam__0(lean_object* v_snd_2281_, lean_object* v___x_2282_, lean_object* v_fst_2283_, lean_object* v_a_2284_, lean_object* v___x_2285_, lean_object* v_givenNames_2286_, lean_object* v_fst_2287_, lean_object* v___x_2288_, lean_object* v_fst_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_){
_start:
{
lean_object* v___x_2295_; 
lean_inc_ref(v_a_2284_);
lean_inc(v_snd_2281_);
v___x_2295_ = l_Lean_Meta_mkRecursorAppPrefix(v_snd_2281_, v___x_2282_, v_fst_2283_, v_a_2284_, v___x_2285_, v___y_2290_, v___y_2291_, v___y_2292_, v___y_2293_);
if (lean_obj_tag(v___x_2295_) == 0)
{
lean_object* v_a_2296_; lean_object* v___x_2297_; 
v_a_2296_ = lean_ctor_get(v___x_2295_, 0);
lean_inc(v_a_2296_);
lean_dec_ref(v___x_2295_);
v___x_2297_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize(v_snd_2281_, v_givenNames_2286_, v_a_2284_, v_fst_2287_, v___x_2288_, v___x_2285_, v_fst_2289_, v_a_2296_, v___y_2290_, v___y_2291_, v___y_2292_, v___y_2293_);
lean_dec_ref(v_a_2284_);
return v___x_2297_;
}
else
{
lean_object* v_a_2298_; lean_object* v___x_2300_; uint8_t v_isShared_2301_; uint8_t v_isSharedCheck_2305_; 
lean_dec(v_fst_2289_);
lean_dec_ref(v___x_2288_);
lean_dec_ref(v_a_2284_);
lean_dec(v_snd_2281_);
v_a_2298_ = lean_ctor_get(v___x_2295_, 0);
v_isSharedCheck_2305_ = !lean_is_exclusive(v___x_2295_);
if (v_isSharedCheck_2305_ == 0)
{
v___x_2300_ = v___x_2295_;
v_isShared_2301_ = v_isSharedCheck_2305_;
goto v_resetjp_2299_;
}
else
{
lean_inc(v_a_2298_);
lean_dec(v___x_2295_);
v___x_2300_ = lean_box(0);
v_isShared_2301_ = v_isSharedCheck_2305_;
goto v_resetjp_2299_;
}
v_resetjp_2299_:
{
lean_object* v___x_2303_; 
if (v_isShared_2301_ == 0)
{
v___x_2303_ = v___x_2300_;
goto v_reusejp_2302_;
}
else
{
lean_object* v_reuseFailAlloc_2304_; 
v_reuseFailAlloc_2304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2304_, 0, v_a_2298_);
v___x_2303_ = v_reuseFailAlloc_2304_;
goto v_reusejp_2302_;
}
v_reusejp_2302_:
{
return v___x_2303_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4___lam__0___boxed(lean_object* v_snd_2306_, lean_object* v___x_2307_, lean_object* v_fst_2308_, lean_object* v_a_2309_, lean_object* v___x_2310_, lean_object* v_givenNames_2311_, lean_object* v_fst_2312_, lean_object* v___x_2313_, lean_object* v_fst_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_){
_start:
{
lean_object* v_res_2320_; 
v_res_2320_ = l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4___lam__0(v_snd_2306_, v___x_2307_, v_fst_2308_, v_a_2309_, v___x_2310_, v_givenNames_2311_, v_fst_2312_, v___x_2313_, v_fst_2314_, v___y_2315_, v___y_2316_, v___y_2317_, v___y_2318_);
lean_dec(v___y_2318_);
lean_dec_ref(v___y_2317_);
lean_dec(v___y_2316_);
lean_dec_ref(v___y_2315_);
lean_dec_ref(v_fst_2312_);
lean_dec_ref(v_givenNames_2311_);
lean_dec_ref(v___x_2310_);
return v_res_2320_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_induction_spec__1(size_t v_sz_2321_, size_t v_i_2322_, lean_object* v_bs_2323_){
_start:
{
uint8_t v___x_2324_; 
v___x_2324_ = lean_usize_dec_lt(v_i_2322_, v_sz_2321_);
if (v___x_2324_ == 0)
{
return v_bs_2323_;
}
else
{
lean_object* v_v_2325_; lean_object* v___x_2326_; lean_object* v_bs_x27_2327_; lean_object* v___x_2328_; size_t v___x_2329_; size_t v___x_2330_; lean_object* v___x_2331_; 
v_v_2325_ = lean_array_uget(v_bs_2323_, v_i_2322_);
v___x_2326_ = lean_unsigned_to_nat(0u);
v_bs_x27_2327_ = lean_array_uset(v_bs_2323_, v_i_2322_, v___x_2326_);
v___x_2328_ = l_Lean_Expr_fvarId_x21(v_v_2325_);
lean_dec(v_v_2325_);
v___x_2329_ = ((size_t)1ULL);
v___x_2330_ = lean_usize_add(v_i_2322_, v___x_2329_);
v___x_2331_ = lean_array_uset(v_bs_x27_2327_, v_i_2322_, v___x_2328_);
v_i_2322_ = v___x_2330_;
v_bs_2323_ = v___x_2331_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_induction_spec__1___boxed(lean_object* v_sz_2333_, lean_object* v_i_2334_, lean_object* v_bs_2335_){
_start:
{
size_t v_sz_boxed_2336_; size_t v_i_boxed_2337_; lean_object* v_res_2338_; 
v_sz_boxed_2336_ = lean_unbox_usize(v_sz_2333_);
lean_dec(v_sz_2333_);
v_i_boxed_2337_ = lean_unbox_usize(v_i_2334_);
lean_dec(v_i_2334_);
v_res_2338_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_induction_spec__1(v_sz_boxed_2336_, v_i_boxed_2337_, v_bs_2335_);
return v_res_2338_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_MVarId_induction_spec__0(lean_object* v_majorTypeArgs_2339_, lean_object* v_val_2340_, lean_object* v_mvarId_2341_, lean_object* v_as_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_){
_start:
{
if (lean_obj_tag(v_as_2342_) == 0)
{
lean_object* v___x_2348_; lean_object* v___x_2349_; 
lean_dec(v_mvarId_2341_);
lean_dec_ref(v_val_2340_);
v___x_2348_ = lean_box(0);
v___x_2349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2349_, 0, v___x_2348_);
return v___x_2349_;
}
else
{
lean_object* v_head_2350_; 
v_head_2350_ = lean_ctor_get(v_as_2342_, 0);
lean_inc(v_head_2350_);
if (lean_obj_tag(v_head_2350_) == 0)
{
lean_object* v_tail_2351_; 
v_tail_2351_ = lean_ctor_get(v_as_2342_, 1);
lean_inc(v_tail_2351_);
lean_dec_ref(v_as_2342_);
v_as_2342_ = v_tail_2351_;
goto _start;
}
else
{
lean_object* v_tail_2353_; lean_object* v___x_2355_; uint8_t v_isShared_2356_; uint8_t v_isSharedCheck_2376_; 
v_tail_2353_ = lean_ctor_get(v_as_2342_, 1);
v_isSharedCheck_2376_ = !lean_is_exclusive(v_as_2342_);
if (v_isSharedCheck_2376_ == 0)
{
lean_object* v_unused_2377_; 
v_unused_2377_ = lean_ctor_get(v_as_2342_, 0);
lean_dec(v_unused_2377_);
v___x_2355_ = v_as_2342_;
v_isShared_2356_ = v_isSharedCheck_2376_;
goto v_resetjp_2354_;
}
else
{
lean_inc(v_tail_2353_);
lean_dec(v_as_2342_);
v___x_2355_ = lean_box(0);
v_isShared_2356_ = v_isSharedCheck_2376_;
goto v_resetjp_2354_;
}
v_resetjp_2354_:
{
lean_object* v_val_2357_; lean_object* v___x_2359_; uint8_t v_isShared_2360_; uint8_t v_isSharedCheck_2375_; 
v_val_2357_ = lean_ctor_get(v_head_2350_, 0);
v_isSharedCheck_2375_ = !lean_is_exclusive(v_head_2350_);
if (v_isSharedCheck_2375_ == 0)
{
v___x_2359_ = v_head_2350_;
v_isShared_2360_ = v_isSharedCheck_2375_;
goto v_resetjp_2358_;
}
else
{
lean_inc(v_val_2357_);
lean_dec(v_head_2350_);
v___x_2359_ = lean_box(0);
v_isShared_2360_ = v_isSharedCheck_2375_;
goto v_resetjp_2358_;
}
v_resetjp_2358_:
{
lean_object* v___x_2361_; uint8_t v___x_2362_; 
v___x_2361_ = lean_array_get_size(v_majorTypeArgs_2339_);
v___x_2362_ = lean_nat_dec_le(v___x_2361_, v_val_2357_);
lean_dec(v_val_2357_);
if (v___x_2362_ == 0)
{
lean_del_object(v___x_2359_);
lean_del_object(v___x_2355_);
v_as_2342_ = v_tail_2353_;
goto _start;
}
else
{
lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2368_; 
v___x_2364_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1));
v___x_2365_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__5, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__5);
lean_inc_ref(v_val_2340_);
v___x_2366_ = l_Lean_indentExpr(v_val_2340_);
if (v_isShared_2356_ == 0)
{
lean_ctor_set_tag(v___x_2355_, 7);
lean_ctor_set(v___x_2355_, 1, v___x_2366_);
lean_ctor_set(v___x_2355_, 0, v___x_2365_);
v___x_2368_ = v___x_2355_;
goto v_reusejp_2367_;
}
else
{
lean_object* v_reuseFailAlloc_2374_; 
v_reuseFailAlloc_2374_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2374_, 0, v___x_2365_);
lean_ctor_set(v_reuseFailAlloc_2374_, 1, v___x_2366_);
v___x_2368_ = v_reuseFailAlloc_2374_;
goto v_reusejp_2367_;
}
v_reusejp_2367_:
{
lean_object* v___x_2370_; 
if (v_isShared_2360_ == 0)
{
lean_ctor_set(v___x_2359_, 0, v___x_2368_);
v___x_2370_ = v___x_2359_;
goto v_reusejp_2369_;
}
else
{
lean_object* v_reuseFailAlloc_2373_; 
v_reuseFailAlloc_2373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2373_, 0, v___x_2368_);
v___x_2370_ = v_reuseFailAlloc_2373_;
goto v_reusejp_2369_;
}
v_reusejp_2369_:
{
lean_object* v___x_2371_; 
lean_inc(v_mvarId_2341_);
v___x_2371_ = l_Lean_Meta_throwTacticEx___redArg(v___x_2364_, v_mvarId_2341_, v___x_2370_, v___y_2343_, v___y_2344_, v___y_2345_, v___y_2346_);
if (lean_obj_tag(v___x_2371_) == 0)
{
lean_dec_ref(v___x_2371_);
v_as_2342_ = v_tail_2353_;
goto _start;
}
else
{
lean_dec(v_tail_2353_);
lean_dec(v_mvarId_2341_);
lean_dec_ref(v_val_2340_);
return v___x_2371_;
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
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_MVarId_induction_spec__0___boxed(lean_object* v_majorTypeArgs_2378_, lean_object* v_val_2379_, lean_object* v_mvarId_2380_, lean_object* v_as_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_){
_start:
{
lean_object* v_res_2387_; 
v_res_2387_ = l_List_forM___at___00Lean_MVarId_induction_spec__0(v_majorTypeArgs_2378_, v_val_2379_, v_mvarId_2380_, v_as_2381_, v___y_2382_, v___y_2383_, v___y_2384_, v___y_2385_);
lean_dec(v___y_2385_);
lean_dec_ref(v___y_2384_);
lean_dec(v___y_2383_);
lean_dec_ref(v___y_2382_);
lean_dec_ref(v_majorTypeArgs_2378_);
return v_res_2387_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__1(void){
_start:
{
lean_object* v___x_2389_; lean_object* v___x_2390_; 
v___x_2389_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__0));
v___x_2390_ = l_Lean_stringToMessageData(v___x_2389_);
return v___x_2390_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__3(void){
_start:
{
lean_object* v___x_2392_; lean_object* v___x_2393_; 
v___x_2392_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__2));
v___x_2393_ = l_Lean_stringToMessageData(v___x_2392_);
return v___x_2393_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__5(void){
_start:
{
lean_object* v___x_2395_; lean_object* v___x_2396_; 
v___x_2395_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__4));
v___x_2396_ = l_Lean_stringToMessageData(v___x_2395_);
return v___x_2396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4(lean_object* v_a_2397_, lean_object* v_val_2398_, lean_object* v_mvarId_2399_, lean_object* v_majorFVarId_2400_, lean_object* v_givenNames_2401_, lean_object* v_recursorName_2402_, lean_object* v_x_2403_, lean_object* v_x_2404_, lean_object* v_x_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_){
_start:
{
if (lean_obj_tag(v_x_2403_) == 5)
{
lean_object* v_fn_2411_; lean_object* v_arg_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; 
v_fn_2411_ = lean_ctor_get(v_x_2403_, 0);
lean_inc_ref(v_fn_2411_);
v_arg_2412_ = lean_ctor_get(v_x_2403_, 1);
lean_inc_ref(v_arg_2412_);
lean_dec_ref(v_x_2403_);
v___x_2413_ = lean_array_set(v_x_2404_, v_x_2405_, v_arg_2412_);
v___x_2414_ = lean_unsigned_to_nat(1u);
v___x_2415_ = lean_nat_sub(v_x_2405_, v___x_2414_);
lean_dec(v_x_2405_);
v_x_2403_ = v_fn_2411_;
v_x_2404_ = v___x_2413_;
v_x_2405_ = v___x_2415_;
goto _start;
}
else
{
uint8_t v_depElim_2417_; lean_object* v_paramsPos_2418_; lean_object* v___x_2419_; 
lean_dec(v_x_2405_);
lean_dec_ref(v_x_2403_);
v_depElim_2417_ = lean_ctor_get_uint8(v_a_2397_, sizeof(void*)*8);
v_paramsPos_2418_ = lean_ctor_get(v_a_2397_, 5);
lean_inc(v_paramsPos_2418_);
lean_inc(v_mvarId_2399_);
lean_inc_ref(v_val_2398_);
v___x_2419_ = l_List_forM___at___00Lean_MVarId_induction_spec__0(v_x_2404_, v_val_2398_, v_mvarId_2399_, v_paramsPos_2418_, v___y_2406_, v___y_2407_, v___y_2408_, v___y_2409_);
lean_dec_ref(v_x_2404_);
if (lean_obj_tag(v___x_2419_) == 0)
{
lean_object* v___x_2420_; lean_object* v___y_2422_; lean_object* v___y_2423_; lean_object* v___y_2424_; lean_object* v___y_2425_; lean_object* v___y_2426_; size_t v___y_2427_; lean_object* v___y_2428_; lean_object* v___y_2429_; lean_object* v___y_2430_; lean_object* v___y_2431_; lean_object* v___y_2432_; lean_object* v___y_2433_; lean_object* v___x_2438_; 
lean_dec_ref(v___x_2419_);
v___x_2420_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1));
lean_inc_ref(v_a_2397_);
lean_inc(v_mvarId_2399_);
v___x_2438_ = l_Lean_Meta_getMajorTypeIndices(v_mvarId_2399_, v___x_2420_, v_a_2397_, v_val_2398_, v___y_2406_, v___y_2407_, v___y_2408_, v___y_2409_);
if (lean_obj_tag(v___x_2438_) == 0)
{
lean_object* v_a_2439_; lean_object* v___x_2440_; 
v_a_2439_ = lean_ctor_get(v___x_2438_, 0);
lean_inc(v_a_2439_);
lean_dec_ref(v___x_2438_);
lean_inc(v_mvarId_2399_);
v___x_2440_ = l_Lean_MVarId_getType(v_mvarId_2399_, v___y_2406_, v___y_2407_, v___y_2408_, v___y_2409_);
if (lean_obj_tag(v___x_2440_) == 0)
{
lean_object* v_a_2441_; lean_object* v_cls_2442_; lean_object* v___y_2444_; lean_object* v___y_2445_; lean_object* v___y_2446_; lean_object* v___y_2447_; 
v_a_2441_ = lean_ctor_get(v___x_2440_, 0);
lean_inc(v_a_2441_);
lean_dec_ref(v___x_2440_);
v_cls_2442_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__2));
if (v_depElim_2417_ == 0)
{
lean_object* v___x_2530_; lean_object* v_a_2531_; lean_object* v___x_2533_; uint8_t v_isShared_2534_; uint8_t v_isSharedCheck_2553_; 
lean_inc(v_majorFVarId_2400_);
v___x_2530_ = l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2___redArg(v_a_2441_, v_majorFVarId_2400_, v___y_2407_);
v_a_2531_ = lean_ctor_get(v___x_2530_, 0);
v_isSharedCheck_2553_ = !lean_is_exclusive(v___x_2530_);
if (v_isSharedCheck_2553_ == 0)
{
v___x_2533_ = v___x_2530_;
v_isShared_2534_ = v_isSharedCheck_2553_;
goto v_resetjp_2532_;
}
else
{
lean_inc(v_a_2531_);
lean_dec(v___x_2530_);
v___x_2533_ = lean_box(0);
v_isShared_2534_ = v_isSharedCheck_2553_;
goto v_resetjp_2532_;
}
v_resetjp_2532_:
{
uint8_t v___x_2535_; 
v___x_2535_ = lean_unbox(v_a_2531_);
lean_dec(v_a_2531_);
if (v___x_2535_ == 0)
{
lean_del_object(v___x_2533_);
lean_dec(v_recursorName_2402_);
v___y_2444_ = v___y_2406_;
v___y_2445_ = v___y_2407_;
v___y_2446_ = v___y_2408_;
v___y_2447_ = v___y_2409_;
goto v___jp_2443_;
}
else
{
lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2542_; 
v___x_2536_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__3, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__3);
v___x_2537_ = l_Lean_MessageData_ofName(v_recursorName_2402_);
v___x_2538_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2538_, 0, v___x_2536_);
lean_ctor_set(v___x_2538_, 1, v___x_2537_);
v___x_2539_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__5, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__5_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__5);
v___x_2540_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2540_, 0, v___x_2538_);
lean_ctor_set(v___x_2540_, 1, v___x_2539_);
if (v_isShared_2534_ == 0)
{
lean_ctor_set_tag(v___x_2533_, 1);
lean_ctor_set(v___x_2533_, 0, v___x_2540_);
v___x_2542_ = v___x_2533_;
goto v_reusejp_2541_;
}
else
{
lean_object* v_reuseFailAlloc_2552_; 
v_reuseFailAlloc_2552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2552_, 0, v___x_2540_);
v___x_2542_ = v_reuseFailAlloc_2552_;
goto v_reusejp_2541_;
}
v_reusejp_2541_:
{
lean_object* v___x_2543_; 
lean_inc(v_mvarId_2399_);
v___x_2543_ = l_Lean_Meta_throwTacticEx___redArg(v___x_2420_, v_mvarId_2399_, v___x_2542_, v___y_2406_, v___y_2407_, v___y_2408_, v___y_2409_);
if (lean_obj_tag(v___x_2543_) == 0)
{
lean_dec_ref(v___x_2543_);
v___y_2444_ = v___y_2406_;
v___y_2445_ = v___y_2407_;
v___y_2446_ = v___y_2408_;
v___y_2447_ = v___y_2409_;
goto v___jp_2443_;
}
else
{
lean_object* v_a_2544_; lean_object* v___x_2546_; uint8_t v_isShared_2547_; uint8_t v_isSharedCheck_2551_; 
lean_dec(v_a_2439_);
lean_dec_ref(v_givenNames_2401_);
lean_dec(v_majorFVarId_2400_);
lean_dec(v_mvarId_2399_);
lean_dec_ref(v_a_2397_);
v_a_2544_ = lean_ctor_get(v___x_2543_, 0);
v_isSharedCheck_2551_ = !lean_is_exclusive(v___x_2543_);
if (v_isSharedCheck_2551_ == 0)
{
v___x_2546_ = v___x_2543_;
v_isShared_2547_ = v_isSharedCheck_2551_;
goto v_resetjp_2545_;
}
else
{
lean_inc(v_a_2544_);
lean_dec(v___x_2543_);
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
}
}
}
}
else
{
lean_dec(v_a_2441_);
lean_dec(v_recursorName_2402_);
v___y_2444_ = v___y_2406_;
v___y_2445_ = v___y_2407_;
v___y_2446_ = v___y_2408_;
v___y_2447_ = v___y_2409_;
goto v___jp_2443_;
}
v___jp_2443_:
{
size_t v_sz_2448_; size_t v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; uint8_t v___x_2452_; uint8_t v___x_2453_; lean_object* v___x_2454_; 
v_sz_2448_ = lean_array_size(v_a_2439_);
v___x_2449_ = ((size_t)0ULL);
lean_inc(v_a_2439_);
v___x_2450_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_induction_spec__1(v_sz_2448_, v___x_2449_, v_a_2439_);
lean_inc(v_majorFVarId_2400_);
v___x_2451_ = lean_array_push(v___x_2450_, v_majorFVarId_2400_);
v___x_2452_ = 1;
v___x_2453_ = 0;
v___x_2454_ = l_Lean_MVarId_revert(v_mvarId_2399_, v___x_2451_, v___x_2452_, v___x_2453_, v___y_2444_, v___y_2445_, v___y_2446_, v___y_2447_);
if (lean_obj_tag(v___x_2454_) == 0)
{
lean_object* v_a_2455_; lean_object* v_fst_2456_; lean_object* v_snd_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; 
v_a_2455_ = lean_ctor_get(v___x_2454_, 0);
lean_inc(v_a_2455_);
lean_dec_ref(v___x_2454_);
v_fst_2456_ = lean_ctor_get(v_a_2455_, 0);
lean_inc(v_fst_2456_);
v_snd_2457_ = lean_ctor_get(v_a_2455_, 1);
lean_inc(v_snd_2457_);
lean_dec(v_a_2455_);
v___x_2458_ = lean_array_get_size(v_a_2439_);
v___x_2459_ = lean_box(0);
v___x_2460_ = l_Lean_Meta_introNCore(v_snd_2457_, v___x_2458_, v___x_2459_, v___x_2453_, v___x_2452_, v___y_2444_, v___y_2445_, v___y_2446_, v___y_2447_);
if (lean_obj_tag(v___x_2460_) == 0)
{
lean_object* v_a_2461_; lean_object* v_fst_2462_; lean_object* v_snd_2463_; lean_object* v___x_2464_; 
v_a_2461_ = lean_ctor_get(v___x_2460_, 0);
lean_inc(v_a_2461_);
lean_dec_ref(v___x_2460_);
v_fst_2462_ = lean_ctor_get(v_a_2461_, 0);
lean_inc(v_fst_2462_);
v_snd_2463_ = lean_ctor_get(v_a_2461_, 1);
lean_inc(v_snd_2463_);
lean_dec(v_a_2461_);
v___x_2464_ = l_Lean_Meta_intro1Core(v_snd_2463_, v___x_2452_, v___y_2444_, v___y_2445_, v___y_2446_, v___y_2447_);
if (lean_obj_tag(v___x_2464_) == 0)
{
lean_object* v_a_2465_; lean_object* v_fst_2466_; lean_object* v_snd_2467_; lean_object* v___x_2469_; uint8_t v_isShared_2470_; uint8_t v_isSharedCheck_2505_; 
v_a_2465_ = lean_ctor_get(v___x_2464_, 0);
lean_inc(v_a_2465_);
lean_dec_ref(v___x_2464_);
v_fst_2466_ = lean_ctor_get(v_a_2465_, 0);
v_snd_2467_ = lean_ctor_get(v_a_2465_, 1);
v_isSharedCheck_2505_ = !lean_is_exclusive(v_a_2465_);
if (v_isSharedCheck_2505_ == 0)
{
v___x_2469_ = v_a_2465_;
v_isShared_2470_ = v_isSharedCheck_2505_;
goto v_resetjp_2468_;
}
else
{
lean_inc(v_snd_2467_);
lean_inc(v_fst_2466_);
lean_dec(v_a_2465_);
v___x_2469_ = lean_box(0);
v_isShared_2470_ = v_isSharedCheck_2505_;
goto v_resetjp_2468_;
}
v_resetjp_2468_:
{
lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2476_; 
v___x_2471_ = lean_box(0);
lean_inc(v_fst_2466_);
v___x_2472_ = l_Lean_mkFVar(v_fst_2466_);
lean_inc_ref(v___x_2472_);
v___x_2473_ = l_Lean_Meta_FVarSubst_insert(v___x_2471_, v_majorFVarId_2400_, v___x_2472_);
v___x_2474_ = lean_unsigned_to_nat(0u);
if (v_isShared_2470_ == 0)
{
lean_ctor_set(v___x_2469_, 1, v___x_2474_);
lean_ctor_set(v___x_2469_, 0, v___x_2473_);
v___x_2476_ = v___x_2469_;
goto v_reusejp_2475_;
}
else
{
lean_object* v_reuseFailAlloc_2504_; 
v_reuseFailAlloc_2504_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2504_, 0, v___x_2473_);
lean_ctor_set(v_reuseFailAlloc_2504_, 1, v___x_2474_);
v___x_2476_ = v_reuseFailAlloc_2504_;
goto v_reusejp_2475_;
}
v_reusejp_2475_:
{
lean_object* v___x_2477_; lean_object* v_options_2478_; uint8_t v_hasTrace_2479_; 
v___x_2477_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_induction_spec__2(v_fst_2462_, v_a_2439_, v_sz_2448_, v___x_2449_, v___x_2476_);
lean_dec(v_a_2439_);
v_options_2478_ = lean_ctor_get(v___y_2446_, 2);
v_hasTrace_2479_ = lean_ctor_get_uint8(v_options_2478_, sizeof(void*)*1);
if (v_hasTrace_2479_ == 0)
{
lean_object* v_fst_2480_; 
v_fst_2480_ = lean_ctor_get(v___x_2477_, 0);
lean_inc(v_fst_2480_);
lean_dec_ref(v___x_2477_);
lean_inc(v_snd_2467_);
v___y_2422_ = v_fst_2480_;
v___y_2423_ = v_fst_2466_;
v___y_2424_ = v_snd_2467_;
v___y_2425_ = v_fst_2456_;
v___y_2426_ = v___x_2472_;
v___y_2427_ = v___x_2449_;
v___y_2428_ = v_fst_2462_;
v___y_2429_ = v_snd_2467_;
v___y_2430_ = v___y_2444_;
v___y_2431_ = v___y_2445_;
v___y_2432_ = v___y_2446_;
v___y_2433_ = v___y_2447_;
goto v___jp_2421_;
}
else
{
lean_object* v_fst_2481_; lean_object* v___x_2483_; uint8_t v_isShared_2484_; uint8_t v_isSharedCheck_2502_; 
v_fst_2481_ = lean_ctor_get(v___x_2477_, 0);
v_isSharedCheck_2502_ = !lean_is_exclusive(v___x_2477_);
if (v_isSharedCheck_2502_ == 0)
{
lean_object* v_unused_2503_; 
v_unused_2503_ = lean_ctor_get(v___x_2477_, 1);
lean_dec(v_unused_2503_);
v___x_2483_ = v___x_2477_;
v_isShared_2484_ = v_isSharedCheck_2502_;
goto v_resetjp_2482_;
}
else
{
lean_inc(v_fst_2481_);
lean_dec(v___x_2477_);
v___x_2483_ = lean_box(0);
v_isShared_2484_ = v_isSharedCheck_2502_;
goto v_resetjp_2482_;
}
v_resetjp_2482_:
{
lean_object* v_inheritedTraceOptions_2485_; lean_object* v___x_2486_; uint8_t v___x_2487_; 
v_inheritedTraceOptions_2485_ = lean_ctor_get(v___y_2446_, 13);
v___x_2486_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5);
v___x_2487_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2485_, v_options_2478_, v___x_2486_);
if (v___x_2487_ == 0)
{
lean_del_object(v___x_2483_);
lean_inc(v_snd_2467_);
v___y_2422_ = v_fst_2481_;
v___y_2423_ = v_fst_2466_;
v___y_2424_ = v_snd_2467_;
v___y_2425_ = v_fst_2456_;
v___y_2426_ = v___x_2472_;
v___y_2427_ = v___x_2449_;
v___y_2428_ = v_fst_2462_;
v___y_2429_ = v_snd_2467_;
v___y_2430_ = v___y_2444_;
v___y_2431_ = v___y_2445_;
v___y_2432_ = v___y_2446_;
v___y_2433_ = v___y_2447_;
goto v___jp_2421_;
}
else
{
lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2491_; 
v___x_2488_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__1);
lean_inc(v_snd_2467_);
v___x_2489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2489_, 0, v_snd_2467_);
if (v_isShared_2484_ == 0)
{
lean_ctor_set_tag(v___x_2483_, 7);
lean_ctor_set(v___x_2483_, 1, v___x_2489_);
lean_ctor_set(v___x_2483_, 0, v___x_2488_);
v___x_2491_ = v___x_2483_;
goto v_reusejp_2490_;
}
else
{
lean_object* v_reuseFailAlloc_2501_; 
v_reuseFailAlloc_2501_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2501_, 0, v___x_2488_);
lean_ctor_set(v_reuseFailAlloc_2501_, 1, v___x_2489_);
v___x_2491_ = v_reuseFailAlloc_2501_;
goto v_reusejp_2490_;
}
v_reusejp_2490_:
{
lean_object* v___x_2492_; 
v___x_2492_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1(v_cls_2442_, v___x_2491_, v___y_2444_, v___y_2445_, v___y_2446_, v___y_2447_);
if (lean_obj_tag(v___x_2492_) == 0)
{
lean_dec_ref(v___x_2492_);
lean_inc(v_snd_2467_);
v___y_2422_ = v_fst_2481_;
v___y_2423_ = v_fst_2466_;
v___y_2424_ = v_snd_2467_;
v___y_2425_ = v_fst_2456_;
v___y_2426_ = v___x_2472_;
v___y_2427_ = v___x_2449_;
v___y_2428_ = v_fst_2462_;
v___y_2429_ = v_snd_2467_;
v___y_2430_ = v___y_2444_;
v___y_2431_ = v___y_2445_;
v___y_2432_ = v___y_2446_;
v___y_2433_ = v___y_2447_;
goto v___jp_2421_;
}
else
{
lean_object* v_a_2493_; lean_object* v___x_2495_; uint8_t v_isShared_2496_; uint8_t v_isSharedCheck_2500_; 
lean_dec(v_fst_2481_);
lean_dec_ref(v___x_2472_);
lean_dec(v_snd_2467_);
lean_dec(v_fst_2466_);
lean_dec(v_fst_2462_);
lean_dec(v_fst_2456_);
lean_dec_ref(v_givenNames_2401_);
lean_dec_ref(v_a_2397_);
v_a_2493_ = lean_ctor_get(v___x_2492_, 0);
v_isSharedCheck_2500_ = !lean_is_exclusive(v___x_2492_);
if (v_isSharedCheck_2500_ == 0)
{
v___x_2495_ = v___x_2492_;
v_isShared_2496_ = v_isSharedCheck_2500_;
goto v_resetjp_2494_;
}
else
{
lean_inc(v_a_2493_);
lean_dec(v___x_2492_);
v___x_2495_ = lean_box(0);
v_isShared_2496_ = v_isSharedCheck_2500_;
goto v_resetjp_2494_;
}
v_resetjp_2494_:
{
lean_object* v___x_2498_; 
if (v_isShared_2496_ == 0)
{
v___x_2498_ = v___x_2495_;
goto v_reusejp_2497_;
}
else
{
lean_object* v_reuseFailAlloc_2499_; 
v_reuseFailAlloc_2499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2499_, 0, v_a_2493_);
v___x_2498_ = v_reuseFailAlloc_2499_;
goto v_reusejp_2497_;
}
v_reusejp_2497_:
{
return v___x_2498_;
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
lean_object* v_a_2506_; lean_object* v___x_2508_; uint8_t v_isShared_2509_; uint8_t v_isSharedCheck_2513_; 
lean_dec(v_fst_2462_);
lean_dec(v_fst_2456_);
lean_dec(v_a_2439_);
lean_dec_ref(v_givenNames_2401_);
lean_dec(v_majorFVarId_2400_);
lean_dec_ref(v_a_2397_);
v_a_2506_ = lean_ctor_get(v___x_2464_, 0);
v_isSharedCheck_2513_ = !lean_is_exclusive(v___x_2464_);
if (v_isSharedCheck_2513_ == 0)
{
v___x_2508_ = v___x_2464_;
v_isShared_2509_ = v_isSharedCheck_2513_;
goto v_resetjp_2507_;
}
else
{
lean_inc(v_a_2506_);
lean_dec(v___x_2464_);
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
lean_dec(v_fst_2456_);
lean_dec(v_a_2439_);
lean_dec_ref(v_givenNames_2401_);
lean_dec(v_majorFVarId_2400_);
lean_dec_ref(v_a_2397_);
v_a_2514_ = lean_ctor_get(v___x_2460_, 0);
v_isSharedCheck_2521_ = !lean_is_exclusive(v___x_2460_);
if (v_isSharedCheck_2521_ == 0)
{
v___x_2516_ = v___x_2460_;
v_isShared_2517_ = v_isSharedCheck_2521_;
goto v_resetjp_2515_;
}
else
{
lean_inc(v_a_2514_);
lean_dec(v___x_2460_);
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
else
{
lean_object* v_a_2522_; lean_object* v___x_2524_; uint8_t v_isShared_2525_; uint8_t v_isSharedCheck_2529_; 
lean_dec(v_a_2439_);
lean_dec_ref(v_givenNames_2401_);
lean_dec(v_majorFVarId_2400_);
lean_dec_ref(v_a_2397_);
v_a_2522_ = lean_ctor_get(v___x_2454_, 0);
v_isSharedCheck_2529_ = !lean_is_exclusive(v___x_2454_);
if (v_isSharedCheck_2529_ == 0)
{
v___x_2524_ = v___x_2454_;
v_isShared_2525_ = v_isSharedCheck_2529_;
goto v_resetjp_2523_;
}
else
{
lean_inc(v_a_2522_);
lean_dec(v___x_2454_);
v___x_2524_ = lean_box(0);
v_isShared_2525_ = v_isSharedCheck_2529_;
goto v_resetjp_2523_;
}
v_resetjp_2523_:
{
lean_object* v___x_2527_; 
if (v_isShared_2525_ == 0)
{
v___x_2527_ = v___x_2524_;
goto v_reusejp_2526_;
}
else
{
lean_object* v_reuseFailAlloc_2528_; 
v_reuseFailAlloc_2528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2528_, 0, v_a_2522_);
v___x_2527_ = v_reuseFailAlloc_2528_;
goto v_reusejp_2526_;
}
v_reusejp_2526_:
{
return v___x_2527_;
}
}
}
}
}
else
{
lean_object* v_a_2554_; lean_object* v___x_2556_; uint8_t v_isShared_2557_; uint8_t v_isSharedCheck_2561_; 
lean_dec(v_a_2439_);
lean_dec(v_recursorName_2402_);
lean_dec_ref(v_givenNames_2401_);
lean_dec(v_majorFVarId_2400_);
lean_dec(v_mvarId_2399_);
lean_dec_ref(v_a_2397_);
v_a_2554_ = lean_ctor_get(v___x_2440_, 0);
v_isSharedCheck_2561_ = !lean_is_exclusive(v___x_2440_);
if (v_isSharedCheck_2561_ == 0)
{
v___x_2556_ = v___x_2440_;
v_isShared_2557_ = v_isSharedCheck_2561_;
goto v_resetjp_2555_;
}
else
{
lean_inc(v_a_2554_);
lean_dec(v___x_2440_);
v___x_2556_ = lean_box(0);
v_isShared_2557_ = v_isSharedCheck_2561_;
goto v_resetjp_2555_;
}
v_resetjp_2555_:
{
lean_object* v___x_2559_; 
if (v_isShared_2557_ == 0)
{
v___x_2559_ = v___x_2556_;
goto v_reusejp_2558_;
}
else
{
lean_object* v_reuseFailAlloc_2560_; 
v_reuseFailAlloc_2560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2560_, 0, v_a_2554_);
v___x_2559_ = v_reuseFailAlloc_2560_;
goto v_reusejp_2558_;
}
v_reusejp_2558_:
{
return v___x_2559_;
}
}
}
}
else
{
lean_object* v_a_2562_; lean_object* v___x_2564_; uint8_t v_isShared_2565_; uint8_t v_isSharedCheck_2569_; 
lean_dec(v_recursorName_2402_);
lean_dec_ref(v_givenNames_2401_);
lean_dec(v_majorFVarId_2400_);
lean_dec(v_mvarId_2399_);
lean_dec_ref(v_a_2397_);
v_a_2562_ = lean_ctor_get(v___x_2438_, 0);
v_isSharedCheck_2569_ = !lean_is_exclusive(v___x_2438_);
if (v_isSharedCheck_2569_ == 0)
{
v___x_2564_ = v___x_2438_;
v_isShared_2565_ = v_isSharedCheck_2569_;
goto v_resetjp_2563_;
}
else
{
lean_inc(v_a_2562_);
lean_dec(v___x_2438_);
v___x_2564_ = lean_box(0);
v_isShared_2565_ = v_isSharedCheck_2569_;
goto v_resetjp_2563_;
}
v_resetjp_2563_:
{
lean_object* v___x_2567_; 
if (v_isShared_2565_ == 0)
{
v___x_2567_ = v___x_2564_;
goto v_reusejp_2566_;
}
else
{
lean_object* v_reuseFailAlloc_2568_; 
v_reuseFailAlloc_2568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2568_, 0, v_a_2562_);
v___x_2567_ = v_reuseFailAlloc_2568_;
goto v_reusejp_2566_;
}
v_reusejp_2566_:
{
return v___x_2567_;
}
}
}
v___jp_2421_:
{
size_t v_sz_2434_; lean_object* v___x_2435_; lean_object* v___f_2436_; lean_object* v___x_2437_; 
v_sz_2434_ = lean_array_size(v___y_2428_);
v___x_2435_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__3(v_sz_2434_, v___y_2427_, v___y_2428_);
v___f_2436_ = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4___lam__0___boxed), 14, 9);
lean_closure_set(v___f_2436_, 0, v___y_2424_);
lean_closure_set(v___f_2436_, 1, v___x_2420_);
lean_closure_set(v___f_2436_, 2, v___y_2423_);
lean_closure_set(v___f_2436_, 3, v_a_2397_);
lean_closure_set(v___f_2436_, 4, v___x_2435_);
lean_closure_set(v___f_2436_, 5, v_givenNames_2401_);
lean_closure_set(v___f_2436_, 6, v___y_2425_);
lean_closure_set(v___f_2436_, 7, v___y_2426_);
lean_closure_set(v___f_2436_, 8, v___y_2422_);
v___x_2437_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___redArg(v___y_2429_, v___f_2436_, v___y_2430_, v___y_2431_, v___y_2432_, v___y_2433_);
return v___x_2437_;
}
}
else
{
lean_object* v_a_2570_; lean_object* v___x_2572_; uint8_t v_isShared_2573_; uint8_t v_isSharedCheck_2577_; 
lean_dec(v_recursorName_2402_);
lean_dec_ref(v_givenNames_2401_);
lean_dec(v_majorFVarId_2400_);
lean_dec(v_mvarId_2399_);
lean_dec_ref(v_val_2398_);
lean_dec_ref(v_a_2397_);
v_a_2570_ = lean_ctor_get(v___x_2419_, 0);
v_isSharedCheck_2577_ = !lean_is_exclusive(v___x_2419_);
if (v_isSharedCheck_2577_ == 0)
{
v___x_2572_ = v___x_2419_;
v_isShared_2573_ = v_isSharedCheck_2577_;
goto v_resetjp_2571_;
}
else
{
lean_inc(v_a_2570_);
lean_dec(v___x_2419_);
v___x_2572_ = lean_box(0);
v_isShared_2573_ = v_isSharedCheck_2577_;
goto v_resetjp_2571_;
}
v_resetjp_2571_:
{
lean_object* v___x_2575_; 
if (v_isShared_2573_ == 0)
{
v___x_2575_ = v___x_2572_;
goto v_reusejp_2574_;
}
else
{
lean_object* v_reuseFailAlloc_2576_; 
v_reuseFailAlloc_2576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2576_, 0, v_a_2570_);
v___x_2575_ = v_reuseFailAlloc_2576_;
goto v_reusejp_2574_;
}
v_reusejp_2574_:
{
return v___x_2575_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___boxed(lean_object* v_a_2578_, lean_object* v_val_2579_, lean_object* v_mvarId_2580_, lean_object* v_majorFVarId_2581_, lean_object* v_givenNames_2582_, lean_object* v_recursorName_2583_, lean_object* v_x_2584_, lean_object* v_x_2585_, lean_object* v_x_2586_, lean_object* v___y_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_){
_start:
{
lean_object* v_res_2592_; 
v_res_2592_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4(v_a_2578_, v_val_2579_, v_mvarId_2580_, v_majorFVarId_2581_, v_givenNames_2582_, v_recursorName_2583_, v_x_2584_, v_x_2585_, v_x_2586_, v___y_2587_, v___y_2588_, v___y_2589_, v___y_2590_);
lean_dec(v___y_2590_);
lean_dec_ref(v___y_2589_);
lean_dec(v___y_2588_);
lean_dec_ref(v___y_2587_);
return v_res_2592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4(lean_object* v_val_2593_, lean_object* v_mvarId_2594_, lean_object* v_a_2595_, lean_object* v_majorFVarId_2596_, lean_object* v_givenNames_2597_, lean_object* v_recursorName_2598_, lean_object* v_x_2599_, lean_object* v_x_2600_, lean_object* v_x_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_){
_start:
{
if (lean_obj_tag(v_x_2599_) == 5)
{
lean_object* v_fn_2607_; lean_object* v_arg_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; 
v_fn_2607_ = lean_ctor_get(v_x_2599_, 0);
lean_inc_ref(v_fn_2607_);
v_arg_2608_ = lean_ctor_get(v_x_2599_, 1);
lean_inc_ref(v_arg_2608_);
lean_dec_ref(v_x_2599_);
v___x_2609_ = lean_array_set(v_x_2600_, v_x_2601_, v_arg_2608_);
v___x_2610_ = lean_unsigned_to_nat(1u);
v___x_2611_ = lean_nat_sub(v_x_2601_, v___x_2610_);
v___x_2612_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4(v_a_2595_, v_val_2593_, v_mvarId_2594_, v_majorFVarId_2596_, v_givenNames_2597_, v_recursorName_2598_, v_fn_2607_, v___x_2609_, v___x_2611_, v___y_2602_, v___y_2603_, v___y_2604_, v___y_2605_);
return v___x_2612_;
}
else
{
uint8_t v_depElim_2613_; lean_object* v_paramsPos_2614_; lean_object* v___x_2615_; 
lean_dec_ref(v_x_2599_);
v_depElim_2613_ = lean_ctor_get_uint8(v_a_2595_, sizeof(void*)*8);
v_paramsPos_2614_ = lean_ctor_get(v_a_2595_, 5);
lean_inc(v_paramsPos_2614_);
lean_inc(v_mvarId_2594_);
lean_inc_ref(v_val_2593_);
v___x_2615_ = l_List_forM___at___00Lean_MVarId_induction_spec__0(v_x_2600_, v_val_2593_, v_mvarId_2594_, v_paramsPos_2614_, v___y_2602_, v___y_2603_, v___y_2604_, v___y_2605_);
lean_dec_ref(v_x_2600_);
if (lean_obj_tag(v___x_2615_) == 0)
{
lean_object* v___x_2616_; lean_object* v___y_2618_; lean_object* v___y_2619_; lean_object* v___y_2620_; lean_object* v___y_2621_; lean_object* v___y_2622_; lean_object* v___y_2623_; size_t v___y_2624_; lean_object* v___y_2625_; lean_object* v___y_2626_; lean_object* v___y_2627_; lean_object* v___y_2628_; lean_object* v___y_2629_; lean_object* v___x_2634_; 
lean_dec_ref(v___x_2615_);
v___x_2616_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1));
lean_inc_ref(v_a_2595_);
lean_inc(v_mvarId_2594_);
v___x_2634_ = l_Lean_Meta_getMajorTypeIndices(v_mvarId_2594_, v___x_2616_, v_a_2595_, v_val_2593_, v___y_2602_, v___y_2603_, v___y_2604_, v___y_2605_);
if (lean_obj_tag(v___x_2634_) == 0)
{
lean_object* v_a_2635_; lean_object* v___x_2636_; 
v_a_2635_ = lean_ctor_get(v___x_2634_, 0);
lean_inc(v_a_2635_);
lean_dec_ref(v___x_2634_);
lean_inc(v_mvarId_2594_);
v___x_2636_ = l_Lean_MVarId_getType(v_mvarId_2594_, v___y_2602_, v___y_2603_, v___y_2604_, v___y_2605_);
if (lean_obj_tag(v___x_2636_) == 0)
{
lean_object* v_a_2637_; lean_object* v_cls_2638_; lean_object* v___y_2640_; lean_object* v___y_2641_; lean_object* v___y_2642_; lean_object* v___y_2643_; 
v_a_2637_ = lean_ctor_get(v___x_2636_, 0);
lean_inc(v_a_2637_);
lean_dec_ref(v___x_2636_);
v_cls_2638_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__2));
if (v_depElim_2613_ == 0)
{
lean_object* v___x_2726_; lean_object* v_a_2727_; lean_object* v___x_2729_; uint8_t v_isShared_2730_; uint8_t v_isSharedCheck_2749_; 
lean_inc(v_majorFVarId_2596_);
v___x_2726_ = l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2___redArg(v_a_2637_, v_majorFVarId_2596_, v___y_2603_);
v_a_2727_ = lean_ctor_get(v___x_2726_, 0);
v_isSharedCheck_2749_ = !lean_is_exclusive(v___x_2726_);
if (v_isSharedCheck_2749_ == 0)
{
v___x_2729_ = v___x_2726_;
v_isShared_2730_ = v_isSharedCheck_2749_;
goto v_resetjp_2728_;
}
else
{
lean_inc(v_a_2727_);
lean_dec(v___x_2726_);
v___x_2729_ = lean_box(0);
v_isShared_2730_ = v_isSharedCheck_2749_;
goto v_resetjp_2728_;
}
v_resetjp_2728_:
{
uint8_t v___x_2731_; 
v___x_2731_ = lean_unbox(v_a_2727_);
lean_dec(v_a_2727_);
if (v___x_2731_ == 0)
{
lean_del_object(v___x_2729_);
lean_dec(v_recursorName_2598_);
v___y_2640_ = v___y_2602_;
v___y_2641_ = v___y_2603_;
v___y_2642_ = v___y_2604_;
v___y_2643_ = v___y_2605_;
goto v___jp_2639_;
}
else
{
lean_object* v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; lean_object* v___x_2738_; 
v___x_2732_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__3, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__3);
v___x_2733_ = l_Lean_MessageData_ofName(v_recursorName_2598_);
v___x_2734_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2734_, 0, v___x_2732_);
lean_ctor_set(v___x_2734_, 1, v___x_2733_);
v___x_2735_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__5, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__5_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__5);
v___x_2736_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2736_, 0, v___x_2734_);
lean_ctor_set(v___x_2736_, 1, v___x_2735_);
if (v_isShared_2730_ == 0)
{
lean_ctor_set_tag(v___x_2729_, 1);
lean_ctor_set(v___x_2729_, 0, v___x_2736_);
v___x_2738_ = v___x_2729_;
goto v_reusejp_2737_;
}
else
{
lean_object* v_reuseFailAlloc_2748_; 
v_reuseFailAlloc_2748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2748_, 0, v___x_2736_);
v___x_2738_ = v_reuseFailAlloc_2748_;
goto v_reusejp_2737_;
}
v_reusejp_2737_:
{
lean_object* v___x_2739_; 
lean_inc(v_mvarId_2594_);
v___x_2739_ = l_Lean_Meta_throwTacticEx___redArg(v___x_2616_, v_mvarId_2594_, v___x_2738_, v___y_2602_, v___y_2603_, v___y_2604_, v___y_2605_);
if (lean_obj_tag(v___x_2739_) == 0)
{
lean_dec_ref(v___x_2739_);
v___y_2640_ = v___y_2602_;
v___y_2641_ = v___y_2603_;
v___y_2642_ = v___y_2604_;
v___y_2643_ = v___y_2605_;
goto v___jp_2639_;
}
else
{
lean_object* v_a_2740_; lean_object* v___x_2742_; uint8_t v_isShared_2743_; uint8_t v_isSharedCheck_2747_; 
lean_dec(v_a_2635_);
lean_dec_ref(v_givenNames_2597_);
lean_dec(v_majorFVarId_2596_);
lean_dec_ref(v_a_2595_);
lean_dec(v_mvarId_2594_);
v_a_2740_ = lean_ctor_get(v___x_2739_, 0);
v_isSharedCheck_2747_ = !lean_is_exclusive(v___x_2739_);
if (v_isSharedCheck_2747_ == 0)
{
v___x_2742_ = v___x_2739_;
v_isShared_2743_ = v_isSharedCheck_2747_;
goto v_resetjp_2741_;
}
else
{
lean_inc(v_a_2740_);
lean_dec(v___x_2739_);
v___x_2742_ = lean_box(0);
v_isShared_2743_ = v_isSharedCheck_2747_;
goto v_resetjp_2741_;
}
v_resetjp_2741_:
{
lean_object* v___x_2745_; 
if (v_isShared_2743_ == 0)
{
v___x_2745_ = v___x_2742_;
goto v_reusejp_2744_;
}
else
{
lean_object* v_reuseFailAlloc_2746_; 
v_reuseFailAlloc_2746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2746_, 0, v_a_2740_);
v___x_2745_ = v_reuseFailAlloc_2746_;
goto v_reusejp_2744_;
}
v_reusejp_2744_:
{
return v___x_2745_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_2637_);
lean_dec(v_recursorName_2598_);
v___y_2640_ = v___y_2602_;
v___y_2641_ = v___y_2603_;
v___y_2642_ = v___y_2604_;
v___y_2643_ = v___y_2605_;
goto v___jp_2639_;
}
v___jp_2639_:
{
size_t v_sz_2644_; size_t v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; uint8_t v___x_2648_; uint8_t v___x_2649_; lean_object* v___x_2650_; 
v_sz_2644_ = lean_array_size(v_a_2635_);
v___x_2645_ = ((size_t)0ULL);
lean_inc(v_a_2635_);
v___x_2646_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_induction_spec__1(v_sz_2644_, v___x_2645_, v_a_2635_);
lean_inc(v_majorFVarId_2596_);
v___x_2647_ = lean_array_push(v___x_2646_, v_majorFVarId_2596_);
v___x_2648_ = 1;
v___x_2649_ = 0;
v___x_2650_ = l_Lean_MVarId_revert(v_mvarId_2594_, v___x_2647_, v___x_2648_, v___x_2649_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_);
if (lean_obj_tag(v___x_2650_) == 0)
{
lean_object* v_a_2651_; lean_object* v_fst_2652_; lean_object* v_snd_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; 
v_a_2651_ = lean_ctor_get(v___x_2650_, 0);
lean_inc(v_a_2651_);
lean_dec_ref(v___x_2650_);
v_fst_2652_ = lean_ctor_get(v_a_2651_, 0);
lean_inc(v_fst_2652_);
v_snd_2653_ = lean_ctor_get(v_a_2651_, 1);
lean_inc(v_snd_2653_);
lean_dec(v_a_2651_);
v___x_2654_ = lean_array_get_size(v_a_2635_);
v___x_2655_ = lean_box(0);
v___x_2656_ = l_Lean_Meta_introNCore(v_snd_2653_, v___x_2654_, v___x_2655_, v___x_2649_, v___x_2648_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_);
if (lean_obj_tag(v___x_2656_) == 0)
{
lean_object* v_a_2657_; lean_object* v_fst_2658_; lean_object* v_snd_2659_; lean_object* v___x_2660_; 
v_a_2657_ = lean_ctor_get(v___x_2656_, 0);
lean_inc(v_a_2657_);
lean_dec_ref(v___x_2656_);
v_fst_2658_ = lean_ctor_get(v_a_2657_, 0);
lean_inc(v_fst_2658_);
v_snd_2659_ = lean_ctor_get(v_a_2657_, 1);
lean_inc(v_snd_2659_);
lean_dec(v_a_2657_);
v___x_2660_ = l_Lean_Meta_intro1Core(v_snd_2659_, v___x_2648_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_);
if (lean_obj_tag(v___x_2660_) == 0)
{
lean_object* v_a_2661_; lean_object* v_fst_2662_; lean_object* v_snd_2663_; lean_object* v___x_2665_; uint8_t v_isShared_2666_; uint8_t v_isSharedCheck_2701_; 
v_a_2661_ = lean_ctor_get(v___x_2660_, 0);
lean_inc(v_a_2661_);
lean_dec_ref(v___x_2660_);
v_fst_2662_ = lean_ctor_get(v_a_2661_, 0);
v_snd_2663_ = lean_ctor_get(v_a_2661_, 1);
v_isSharedCheck_2701_ = !lean_is_exclusive(v_a_2661_);
if (v_isSharedCheck_2701_ == 0)
{
v___x_2665_ = v_a_2661_;
v_isShared_2666_ = v_isSharedCheck_2701_;
goto v_resetjp_2664_;
}
else
{
lean_inc(v_snd_2663_);
lean_inc(v_fst_2662_);
lean_dec(v_a_2661_);
v___x_2665_ = lean_box(0);
v_isShared_2666_ = v_isSharedCheck_2701_;
goto v_resetjp_2664_;
}
v_resetjp_2664_:
{
lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2672_; 
v___x_2667_ = lean_box(0);
lean_inc(v_fst_2662_);
v___x_2668_ = l_Lean_mkFVar(v_fst_2662_);
lean_inc_ref(v___x_2668_);
v___x_2669_ = l_Lean_Meta_FVarSubst_insert(v___x_2667_, v_majorFVarId_2596_, v___x_2668_);
v___x_2670_ = lean_unsigned_to_nat(0u);
if (v_isShared_2666_ == 0)
{
lean_ctor_set(v___x_2665_, 1, v___x_2670_);
lean_ctor_set(v___x_2665_, 0, v___x_2669_);
v___x_2672_ = v___x_2665_;
goto v_reusejp_2671_;
}
else
{
lean_object* v_reuseFailAlloc_2700_; 
v_reuseFailAlloc_2700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2700_, 0, v___x_2669_);
lean_ctor_set(v_reuseFailAlloc_2700_, 1, v___x_2670_);
v___x_2672_ = v_reuseFailAlloc_2700_;
goto v_reusejp_2671_;
}
v_reusejp_2671_:
{
lean_object* v___x_2673_; lean_object* v_options_2674_; uint8_t v_hasTrace_2675_; 
v___x_2673_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_induction_spec__2(v_fst_2658_, v_a_2635_, v_sz_2644_, v___x_2645_, v___x_2672_);
lean_dec(v_a_2635_);
v_options_2674_ = lean_ctor_get(v___y_2642_, 2);
v_hasTrace_2675_ = lean_ctor_get_uint8(v_options_2674_, sizeof(void*)*1);
if (v_hasTrace_2675_ == 0)
{
lean_object* v_fst_2676_; 
v_fst_2676_ = lean_ctor_get(v___x_2673_, 0);
lean_inc(v_fst_2676_);
lean_dec_ref(v___x_2673_);
lean_inc(v_snd_2663_);
v___y_2618_ = v___x_2668_;
v___y_2619_ = v_fst_2676_;
v___y_2620_ = v_fst_2652_;
v___y_2621_ = v_snd_2663_;
v___y_2622_ = v_fst_2662_;
v___y_2623_ = v_fst_2658_;
v___y_2624_ = v___x_2645_;
v___y_2625_ = v_snd_2663_;
v___y_2626_ = v___y_2640_;
v___y_2627_ = v___y_2641_;
v___y_2628_ = v___y_2642_;
v___y_2629_ = v___y_2643_;
goto v___jp_2617_;
}
else
{
lean_object* v_fst_2677_; lean_object* v___x_2679_; uint8_t v_isShared_2680_; uint8_t v_isSharedCheck_2698_; 
v_fst_2677_ = lean_ctor_get(v___x_2673_, 0);
v_isSharedCheck_2698_ = !lean_is_exclusive(v___x_2673_);
if (v_isSharedCheck_2698_ == 0)
{
lean_object* v_unused_2699_; 
v_unused_2699_ = lean_ctor_get(v___x_2673_, 1);
lean_dec(v_unused_2699_);
v___x_2679_ = v___x_2673_;
v_isShared_2680_ = v_isSharedCheck_2698_;
goto v_resetjp_2678_;
}
else
{
lean_inc(v_fst_2677_);
lean_dec(v___x_2673_);
v___x_2679_ = lean_box(0);
v_isShared_2680_ = v_isSharedCheck_2698_;
goto v_resetjp_2678_;
}
v_resetjp_2678_:
{
lean_object* v_inheritedTraceOptions_2681_; lean_object* v___x_2682_; uint8_t v___x_2683_; 
v_inheritedTraceOptions_2681_ = lean_ctor_get(v___y_2642_, 13);
v___x_2682_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5);
v___x_2683_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2681_, v_options_2674_, v___x_2682_);
if (v___x_2683_ == 0)
{
lean_del_object(v___x_2679_);
lean_inc(v_snd_2663_);
v___y_2618_ = v___x_2668_;
v___y_2619_ = v_fst_2677_;
v___y_2620_ = v_fst_2652_;
v___y_2621_ = v_snd_2663_;
v___y_2622_ = v_fst_2662_;
v___y_2623_ = v_fst_2658_;
v___y_2624_ = v___x_2645_;
v___y_2625_ = v_snd_2663_;
v___y_2626_ = v___y_2640_;
v___y_2627_ = v___y_2641_;
v___y_2628_ = v___y_2642_;
v___y_2629_ = v___y_2643_;
goto v___jp_2617_;
}
else
{
lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2687_; 
v___x_2684_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__1);
lean_inc(v_snd_2663_);
v___x_2685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2685_, 0, v_snd_2663_);
if (v_isShared_2680_ == 0)
{
lean_ctor_set_tag(v___x_2679_, 7);
lean_ctor_set(v___x_2679_, 1, v___x_2685_);
lean_ctor_set(v___x_2679_, 0, v___x_2684_);
v___x_2687_ = v___x_2679_;
goto v_reusejp_2686_;
}
else
{
lean_object* v_reuseFailAlloc_2697_; 
v_reuseFailAlloc_2697_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2697_, 0, v___x_2684_);
lean_ctor_set(v_reuseFailAlloc_2697_, 1, v___x_2685_);
v___x_2687_ = v_reuseFailAlloc_2697_;
goto v_reusejp_2686_;
}
v_reusejp_2686_:
{
lean_object* v___x_2688_; 
v___x_2688_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1(v_cls_2638_, v___x_2687_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_);
if (lean_obj_tag(v___x_2688_) == 0)
{
lean_dec_ref(v___x_2688_);
lean_inc(v_snd_2663_);
v___y_2618_ = v___x_2668_;
v___y_2619_ = v_fst_2677_;
v___y_2620_ = v_fst_2652_;
v___y_2621_ = v_snd_2663_;
v___y_2622_ = v_fst_2662_;
v___y_2623_ = v_fst_2658_;
v___y_2624_ = v___x_2645_;
v___y_2625_ = v_snd_2663_;
v___y_2626_ = v___y_2640_;
v___y_2627_ = v___y_2641_;
v___y_2628_ = v___y_2642_;
v___y_2629_ = v___y_2643_;
goto v___jp_2617_;
}
else
{
lean_object* v_a_2689_; lean_object* v___x_2691_; uint8_t v_isShared_2692_; uint8_t v_isSharedCheck_2696_; 
lean_dec(v_fst_2677_);
lean_dec_ref(v___x_2668_);
lean_dec(v_snd_2663_);
lean_dec(v_fst_2662_);
lean_dec(v_fst_2658_);
lean_dec(v_fst_2652_);
lean_dec_ref(v_givenNames_2597_);
lean_dec_ref(v_a_2595_);
v_a_2689_ = lean_ctor_get(v___x_2688_, 0);
v_isSharedCheck_2696_ = !lean_is_exclusive(v___x_2688_);
if (v_isSharedCheck_2696_ == 0)
{
v___x_2691_ = v___x_2688_;
v_isShared_2692_ = v_isSharedCheck_2696_;
goto v_resetjp_2690_;
}
else
{
lean_inc(v_a_2689_);
lean_dec(v___x_2688_);
v___x_2691_ = lean_box(0);
v_isShared_2692_ = v_isSharedCheck_2696_;
goto v_resetjp_2690_;
}
v_resetjp_2690_:
{
lean_object* v___x_2694_; 
if (v_isShared_2692_ == 0)
{
v___x_2694_ = v___x_2691_;
goto v_reusejp_2693_;
}
else
{
lean_object* v_reuseFailAlloc_2695_; 
v_reuseFailAlloc_2695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2695_, 0, v_a_2689_);
v___x_2694_ = v_reuseFailAlloc_2695_;
goto v_reusejp_2693_;
}
v_reusejp_2693_:
{
return v___x_2694_;
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
lean_object* v_a_2702_; lean_object* v___x_2704_; uint8_t v_isShared_2705_; uint8_t v_isSharedCheck_2709_; 
lean_dec(v_fst_2658_);
lean_dec(v_fst_2652_);
lean_dec(v_a_2635_);
lean_dec_ref(v_givenNames_2597_);
lean_dec(v_majorFVarId_2596_);
lean_dec_ref(v_a_2595_);
v_a_2702_ = lean_ctor_get(v___x_2660_, 0);
v_isSharedCheck_2709_ = !lean_is_exclusive(v___x_2660_);
if (v_isSharedCheck_2709_ == 0)
{
v___x_2704_ = v___x_2660_;
v_isShared_2705_ = v_isSharedCheck_2709_;
goto v_resetjp_2703_;
}
else
{
lean_inc(v_a_2702_);
lean_dec(v___x_2660_);
v___x_2704_ = lean_box(0);
v_isShared_2705_ = v_isSharedCheck_2709_;
goto v_resetjp_2703_;
}
v_resetjp_2703_:
{
lean_object* v___x_2707_; 
if (v_isShared_2705_ == 0)
{
v___x_2707_ = v___x_2704_;
goto v_reusejp_2706_;
}
else
{
lean_object* v_reuseFailAlloc_2708_; 
v_reuseFailAlloc_2708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2708_, 0, v_a_2702_);
v___x_2707_ = v_reuseFailAlloc_2708_;
goto v_reusejp_2706_;
}
v_reusejp_2706_:
{
return v___x_2707_;
}
}
}
}
else
{
lean_object* v_a_2710_; lean_object* v___x_2712_; uint8_t v_isShared_2713_; uint8_t v_isSharedCheck_2717_; 
lean_dec(v_fst_2652_);
lean_dec(v_a_2635_);
lean_dec_ref(v_givenNames_2597_);
lean_dec(v_majorFVarId_2596_);
lean_dec_ref(v_a_2595_);
v_a_2710_ = lean_ctor_get(v___x_2656_, 0);
v_isSharedCheck_2717_ = !lean_is_exclusive(v___x_2656_);
if (v_isSharedCheck_2717_ == 0)
{
v___x_2712_ = v___x_2656_;
v_isShared_2713_ = v_isSharedCheck_2717_;
goto v_resetjp_2711_;
}
else
{
lean_inc(v_a_2710_);
lean_dec(v___x_2656_);
v___x_2712_ = lean_box(0);
v_isShared_2713_ = v_isSharedCheck_2717_;
goto v_resetjp_2711_;
}
v_resetjp_2711_:
{
lean_object* v___x_2715_; 
if (v_isShared_2713_ == 0)
{
v___x_2715_ = v___x_2712_;
goto v_reusejp_2714_;
}
else
{
lean_object* v_reuseFailAlloc_2716_; 
v_reuseFailAlloc_2716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2716_, 0, v_a_2710_);
v___x_2715_ = v_reuseFailAlloc_2716_;
goto v_reusejp_2714_;
}
v_reusejp_2714_:
{
return v___x_2715_;
}
}
}
}
else
{
lean_object* v_a_2718_; lean_object* v___x_2720_; uint8_t v_isShared_2721_; uint8_t v_isSharedCheck_2725_; 
lean_dec(v_a_2635_);
lean_dec_ref(v_givenNames_2597_);
lean_dec(v_majorFVarId_2596_);
lean_dec_ref(v_a_2595_);
v_a_2718_ = lean_ctor_get(v___x_2650_, 0);
v_isSharedCheck_2725_ = !lean_is_exclusive(v___x_2650_);
if (v_isSharedCheck_2725_ == 0)
{
v___x_2720_ = v___x_2650_;
v_isShared_2721_ = v_isSharedCheck_2725_;
goto v_resetjp_2719_;
}
else
{
lean_inc(v_a_2718_);
lean_dec(v___x_2650_);
v___x_2720_ = lean_box(0);
v_isShared_2721_ = v_isSharedCheck_2725_;
goto v_resetjp_2719_;
}
v_resetjp_2719_:
{
lean_object* v___x_2723_; 
if (v_isShared_2721_ == 0)
{
v___x_2723_ = v___x_2720_;
goto v_reusejp_2722_;
}
else
{
lean_object* v_reuseFailAlloc_2724_; 
v_reuseFailAlloc_2724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2724_, 0, v_a_2718_);
v___x_2723_ = v_reuseFailAlloc_2724_;
goto v_reusejp_2722_;
}
v_reusejp_2722_:
{
return v___x_2723_;
}
}
}
}
}
else
{
lean_object* v_a_2750_; lean_object* v___x_2752_; uint8_t v_isShared_2753_; uint8_t v_isSharedCheck_2757_; 
lean_dec(v_a_2635_);
lean_dec(v_recursorName_2598_);
lean_dec_ref(v_givenNames_2597_);
lean_dec(v_majorFVarId_2596_);
lean_dec_ref(v_a_2595_);
lean_dec(v_mvarId_2594_);
v_a_2750_ = lean_ctor_get(v___x_2636_, 0);
v_isSharedCheck_2757_ = !lean_is_exclusive(v___x_2636_);
if (v_isSharedCheck_2757_ == 0)
{
v___x_2752_ = v___x_2636_;
v_isShared_2753_ = v_isSharedCheck_2757_;
goto v_resetjp_2751_;
}
else
{
lean_inc(v_a_2750_);
lean_dec(v___x_2636_);
v___x_2752_ = lean_box(0);
v_isShared_2753_ = v_isSharedCheck_2757_;
goto v_resetjp_2751_;
}
v_resetjp_2751_:
{
lean_object* v___x_2755_; 
if (v_isShared_2753_ == 0)
{
v___x_2755_ = v___x_2752_;
goto v_reusejp_2754_;
}
else
{
lean_object* v_reuseFailAlloc_2756_; 
v_reuseFailAlloc_2756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2756_, 0, v_a_2750_);
v___x_2755_ = v_reuseFailAlloc_2756_;
goto v_reusejp_2754_;
}
v_reusejp_2754_:
{
return v___x_2755_;
}
}
}
}
else
{
lean_object* v_a_2758_; lean_object* v___x_2760_; uint8_t v_isShared_2761_; uint8_t v_isSharedCheck_2765_; 
lean_dec(v_recursorName_2598_);
lean_dec_ref(v_givenNames_2597_);
lean_dec(v_majorFVarId_2596_);
lean_dec_ref(v_a_2595_);
lean_dec(v_mvarId_2594_);
v_a_2758_ = lean_ctor_get(v___x_2634_, 0);
v_isSharedCheck_2765_ = !lean_is_exclusive(v___x_2634_);
if (v_isSharedCheck_2765_ == 0)
{
v___x_2760_ = v___x_2634_;
v_isShared_2761_ = v_isSharedCheck_2765_;
goto v_resetjp_2759_;
}
else
{
lean_inc(v_a_2758_);
lean_dec(v___x_2634_);
v___x_2760_ = lean_box(0);
v_isShared_2761_ = v_isSharedCheck_2765_;
goto v_resetjp_2759_;
}
v_resetjp_2759_:
{
lean_object* v___x_2763_; 
if (v_isShared_2761_ == 0)
{
v___x_2763_ = v___x_2760_;
goto v_reusejp_2762_;
}
else
{
lean_object* v_reuseFailAlloc_2764_; 
v_reuseFailAlloc_2764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2764_, 0, v_a_2758_);
v___x_2763_ = v_reuseFailAlloc_2764_;
goto v_reusejp_2762_;
}
v_reusejp_2762_:
{
return v___x_2763_;
}
}
}
v___jp_2617_:
{
size_t v_sz_2630_; lean_object* v___x_2631_; lean_object* v___f_2632_; lean_object* v___x_2633_; 
v_sz_2630_ = lean_array_size(v___y_2623_);
v___x_2631_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__3(v_sz_2630_, v___y_2624_, v___y_2623_);
v___f_2632_ = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4___lam__0___boxed), 14, 9);
lean_closure_set(v___f_2632_, 0, v___y_2621_);
lean_closure_set(v___f_2632_, 1, v___x_2616_);
lean_closure_set(v___f_2632_, 2, v___y_2622_);
lean_closure_set(v___f_2632_, 3, v_a_2595_);
lean_closure_set(v___f_2632_, 4, v___x_2631_);
lean_closure_set(v___f_2632_, 5, v_givenNames_2597_);
lean_closure_set(v___f_2632_, 6, v___y_2620_);
lean_closure_set(v___f_2632_, 7, v___y_2618_);
lean_closure_set(v___f_2632_, 8, v___y_2619_);
v___x_2633_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___redArg(v___y_2625_, v___f_2632_, v___y_2626_, v___y_2627_, v___y_2628_, v___y_2629_);
return v___x_2633_;
}
}
else
{
lean_object* v_a_2766_; lean_object* v___x_2768_; uint8_t v_isShared_2769_; uint8_t v_isSharedCheck_2773_; 
lean_dec(v_recursorName_2598_);
lean_dec_ref(v_givenNames_2597_);
lean_dec(v_majorFVarId_2596_);
lean_dec_ref(v_a_2595_);
lean_dec(v_mvarId_2594_);
lean_dec_ref(v_val_2593_);
v_a_2766_ = lean_ctor_get(v___x_2615_, 0);
v_isSharedCheck_2773_ = !lean_is_exclusive(v___x_2615_);
if (v_isSharedCheck_2773_ == 0)
{
v___x_2768_ = v___x_2615_;
v_isShared_2769_ = v_isSharedCheck_2773_;
goto v_resetjp_2767_;
}
else
{
lean_inc(v_a_2766_);
lean_dec(v___x_2615_);
v___x_2768_ = lean_box(0);
v_isShared_2769_ = v_isSharedCheck_2773_;
goto v_resetjp_2767_;
}
v_resetjp_2767_:
{
lean_object* v___x_2771_; 
if (v_isShared_2769_ == 0)
{
v___x_2771_ = v___x_2768_;
goto v_reusejp_2770_;
}
else
{
lean_object* v_reuseFailAlloc_2772_; 
v_reuseFailAlloc_2772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2772_, 0, v_a_2766_);
v___x_2771_ = v_reuseFailAlloc_2772_;
goto v_reusejp_2770_;
}
v_reusejp_2770_:
{
return v___x_2771_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4___boxed(lean_object* v_val_2774_, lean_object* v_mvarId_2775_, lean_object* v_a_2776_, lean_object* v_majorFVarId_2777_, lean_object* v_givenNames_2778_, lean_object* v_recursorName_2779_, lean_object* v_x_2780_, lean_object* v_x_2781_, lean_object* v_x_2782_, lean_object* v___y_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_, lean_object* v___y_2787_){
_start:
{
lean_object* v_res_2788_; 
v_res_2788_ = l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4(v_val_2774_, v_mvarId_2775_, v_a_2776_, v_majorFVarId_2777_, v_givenNames_2778_, v_recursorName_2779_, v_x_2780_, v_x_2781_, v_x_2782_, v___y_2783_, v___y_2784_, v___y_2785_, v___y_2786_);
lean_dec(v___y_2786_);
lean_dec_ref(v___y_2785_);
lean_dec(v___y_2784_);
lean_dec_ref(v___y_2783_);
lean_dec(v_x_2782_);
return v_res_2788_;
}
}
static lean_object* _init_l_Lean_MVarId_induction___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2790_; lean_object* v___x_2791_; 
v___x_2790_ = ((lean_object*)(l_Lean_MVarId_induction___lam__0___closed__0));
v___x_2791_ = l_Lean_stringToMessageData(v___x_2790_);
return v___x_2791_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_induction___lam__0(lean_object* v___x_2792_, lean_object* v_mvarId_2793_, lean_object* v_majorFVarId_2794_, lean_object* v_recursorName_2795_, lean_object* v_givenNames_2796_, lean_object* v_cls_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_){
_start:
{
lean_object* v___y_2804_; lean_object* v___y_2805_; lean_object* v___y_2806_; lean_object* v___y_2807_; lean_object* v_options_2859_; uint8_t v_hasTrace_2860_; 
v_options_2859_ = lean_ctor_get(v___y_2800_, 2);
v_hasTrace_2860_ = lean_ctor_get_uint8(v_options_2859_, sizeof(void*)*1);
if (v_hasTrace_2860_ == 0)
{
lean_dec(v_cls_2797_);
v___y_2804_ = v___y_2798_;
v___y_2805_ = v___y_2799_;
v___y_2806_ = v___y_2800_;
v___y_2807_ = v___y_2801_;
goto v___jp_2803_;
}
else
{
lean_object* v_inheritedTraceOptions_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; uint8_t v___x_2864_; 
v_inheritedTraceOptions_2861_ = lean_ctor_get(v___y_2800_, 13);
v___x_2862_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__4));
lean_inc(v_cls_2797_);
v___x_2863_ = l_Lean_Name_append(v___x_2862_, v_cls_2797_);
v___x_2864_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2861_, v_options_2859_, v___x_2863_);
lean_dec(v___x_2863_);
if (v___x_2864_ == 0)
{
lean_dec(v_cls_2797_);
v___y_2804_ = v___y_2798_;
v___y_2805_ = v___y_2799_;
v___y_2806_ = v___y_2800_;
v___y_2807_ = v___y_2801_;
goto v___jp_2803_;
}
else
{
lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; 
v___x_2865_ = lean_obj_once(&l_Lean_MVarId_induction___lam__0___closed__1, &l_Lean_MVarId_induction___lam__0___closed__1_once, _init_l_Lean_MVarId_induction___lam__0___closed__1);
lean_inc(v_mvarId_2793_);
v___x_2866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2866_, 0, v_mvarId_2793_);
v___x_2867_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2867_, 0, v___x_2865_);
lean_ctor_set(v___x_2867_, 1, v___x_2866_);
v___x_2868_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1(v_cls_2797_, v___x_2867_, v___y_2798_, v___y_2799_, v___y_2800_, v___y_2801_);
if (lean_obj_tag(v___x_2868_) == 0)
{
lean_dec_ref(v___x_2868_);
v___y_2804_ = v___y_2798_;
v___y_2805_ = v___y_2799_;
v___y_2806_ = v___y_2800_;
v___y_2807_ = v___y_2801_;
goto v___jp_2803_;
}
else
{
lean_object* v_a_2869_; lean_object* v___x_2871_; uint8_t v_isShared_2872_; uint8_t v_isSharedCheck_2876_; 
lean_dec_ref(v_givenNames_2796_);
lean_dec(v_recursorName_2795_);
lean_dec(v_majorFVarId_2794_);
lean_dec(v_mvarId_2793_);
lean_dec_ref(v___x_2792_);
v_a_2869_ = lean_ctor_get(v___x_2868_, 0);
v_isSharedCheck_2876_ = !lean_is_exclusive(v___x_2868_);
if (v_isSharedCheck_2876_ == 0)
{
v___x_2871_ = v___x_2868_;
v_isShared_2872_ = v_isSharedCheck_2876_;
goto v_resetjp_2870_;
}
else
{
lean_inc(v_a_2869_);
lean_dec(v___x_2868_);
v___x_2871_ = lean_box(0);
v_isShared_2872_ = v_isSharedCheck_2876_;
goto v_resetjp_2870_;
}
v_resetjp_2870_:
{
lean_object* v___x_2874_; 
if (v_isShared_2872_ == 0)
{
v___x_2874_ = v___x_2871_;
goto v_reusejp_2873_;
}
else
{
lean_object* v_reuseFailAlloc_2875_; 
v_reuseFailAlloc_2875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2875_, 0, v_a_2869_);
v___x_2874_ = v_reuseFailAlloc_2875_;
goto v_reusejp_2873_;
}
v_reusejp_2873_:
{
return v___x_2874_;
}
}
}
}
}
v___jp_2803_:
{
lean_object* v___x_2808_; lean_object* v___x_2809_; 
v___x_2808_ = l_Lean_Name_mkStr1(v___x_2792_);
lean_inc(v___x_2808_);
lean_inc(v_mvarId_2793_);
v___x_2809_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_2793_, v___x_2808_, v___y_2804_, v___y_2805_, v___y_2806_, v___y_2807_);
if (lean_obj_tag(v___x_2809_) == 0)
{
lean_object* v___x_2810_; 
lean_dec_ref(v___x_2809_);
lean_inc(v_majorFVarId_2794_);
v___x_2810_ = l_Lean_FVarId_getDecl___redArg(v_majorFVarId_2794_, v___y_2804_, v___y_2806_, v___y_2807_);
if (lean_obj_tag(v___x_2810_) == 0)
{
lean_object* v_a_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; 
v_a_2811_ = lean_ctor_get(v___x_2810_, 0);
lean_inc(v_a_2811_);
lean_dec_ref(v___x_2810_);
v___x_2812_ = lean_box(0);
lean_inc(v_recursorName_2795_);
v___x_2813_ = l_Lean_Meta_mkRecursorInfo(v_recursorName_2795_, v___x_2812_, v___y_2804_, v___y_2805_, v___y_2806_, v___y_2807_);
if (lean_obj_tag(v___x_2813_) == 0)
{
lean_object* v_a_2814_; lean_object* v_typeName_2815_; lean_object* v___x_2816_; lean_object* v___x_2817_; 
v_a_2814_ = lean_ctor_get(v___x_2813_, 0);
lean_inc(v_a_2814_);
lean_dec_ref(v___x_2813_);
v_typeName_2815_ = lean_ctor_get(v_a_2814_, 1);
v___x_2816_ = l_Lean_LocalDecl_type(v_a_2811_);
lean_dec(v_a_2811_);
lean_inc_ref(v___x_2816_);
v___x_2817_ = l_Lean_Meta_whnfUntil(v___x_2816_, v_typeName_2815_, v___y_2804_, v___y_2805_, v___y_2806_, v___y_2807_);
if (lean_obj_tag(v___x_2817_) == 0)
{
lean_object* v_a_2818_; 
v_a_2818_ = lean_ctor_get(v___x_2817_, 0);
lean_inc(v_a_2818_);
lean_dec_ref(v___x_2817_);
if (lean_obj_tag(v_a_2818_) == 1)
{
lean_object* v_val_2819_; lean_object* v_dummy_2820_; lean_object* v_nargs_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; 
lean_dec_ref(v___x_2816_);
lean_dec(v___x_2808_);
v_val_2819_ = lean_ctor_get(v_a_2818_, 0);
lean_inc_n(v_val_2819_, 2);
lean_dec_ref(v_a_2818_);
v_dummy_2820_ = lean_obj_once(&l_Lean_Meta_getMajorTypeIndices___closed__0, &l_Lean_Meta_getMajorTypeIndices___closed__0_once, _init_l_Lean_Meta_getMajorTypeIndices___closed__0);
v_nargs_2821_ = l_Lean_Expr_getAppNumArgs(v_val_2819_);
lean_inc(v_nargs_2821_);
v___x_2822_ = lean_mk_array(v_nargs_2821_, v_dummy_2820_);
v___x_2823_ = lean_unsigned_to_nat(1u);
v___x_2824_ = lean_nat_sub(v_nargs_2821_, v___x_2823_);
lean_dec(v_nargs_2821_);
v___x_2825_ = l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4(v_val_2819_, v_mvarId_2793_, v_a_2814_, v_majorFVarId_2794_, v_givenNames_2796_, v_recursorName_2795_, v_val_2819_, v___x_2822_, v___x_2824_, v___y_2804_, v___y_2805_, v___y_2806_, v___y_2807_);
lean_dec(v___x_2824_);
return v___x_2825_;
}
else
{
lean_object* v___x_2826_; 
lean_dec(v_a_2818_);
lean_dec(v_a_2814_);
lean_dec_ref(v_givenNames_2796_);
lean_dec(v_recursorName_2795_);
lean_dec(v_majorFVarId_2794_);
v___x_2826_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg(v___x_2808_, v_mvarId_2793_, v___x_2816_, v___y_2804_, v___y_2805_, v___y_2806_, v___y_2807_);
return v___x_2826_;
}
}
else
{
lean_object* v_a_2827_; lean_object* v___x_2829_; uint8_t v_isShared_2830_; uint8_t v_isSharedCheck_2834_; 
lean_dec_ref(v___x_2816_);
lean_dec(v_a_2814_);
lean_dec(v___x_2808_);
lean_dec_ref(v_givenNames_2796_);
lean_dec(v_recursorName_2795_);
lean_dec(v_majorFVarId_2794_);
lean_dec(v_mvarId_2793_);
v_a_2827_ = lean_ctor_get(v___x_2817_, 0);
v_isSharedCheck_2834_ = !lean_is_exclusive(v___x_2817_);
if (v_isSharedCheck_2834_ == 0)
{
v___x_2829_ = v___x_2817_;
v_isShared_2830_ = v_isSharedCheck_2834_;
goto v_resetjp_2828_;
}
else
{
lean_inc(v_a_2827_);
lean_dec(v___x_2817_);
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
else
{
lean_object* v_a_2835_; lean_object* v___x_2837_; uint8_t v_isShared_2838_; uint8_t v_isSharedCheck_2842_; 
lean_dec(v_a_2811_);
lean_dec(v___x_2808_);
lean_dec_ref(v_givenNames_2796_);
lean_dec(v_recursorName_2795_);
lean_dec(v_majorFVarId_2794_);
lean_dec(v_mvarId_2793_);
v_a_2835_ = lean_ctor_get(v___x_2813_, 0);
v_isSharedCheck_2842_ = !lean_is_exclusive(v___x_2813_);
if (v_isSharedCheck_2842_ == 0)
{
v___x_2837_ = v___x_2813_;
v_isShared_2838_ = v_isSharedCheck_2842_;
goto v_resetjp_2836_;
}
else
{
lean_inc(v_a_2835_);
lean_dec(v___x_2813_);
v___x_2837_ = lean_box(0);
v_isShared_2838_ = v_isSharedCheck_2842_;
goto v_resetjp_2836_;
}
v_resetjp_2836_:
{
lean_object* v___x_2840_; 
if (v_isShared_2838_ == 0)
{
v___x_2840_ = v___x_2837_;
goto v_reusejp_2839_;
}
else
{
lean_object* v_reuseFailAlloc_2841_; 
v_reuseFailAlloc_2841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2841_, 0, v_a_2835_);
v___x_2840_ = v_reuseFailAlloc_2841_;
goto v_reusejp_2839_;
}
v_reusejp_2839_:
{
return v___x_2840_;
}
}
}
}
else
{
lean_object* v_a_2843_; lean_object* v___x_2845_; uint8_t v_isShared_2846_; uint8_t v_isSharedCheck_2850_; 
lean_dec(v___x_2808_);
lean_dec_ref(v_givenNames_2796_);
lean_dec(v_recursorName_2795_);
lean_dec(v_majorFVarId_2794_);
lean_dec(v_mvarId_2793_);
v_a_2843_ = lean_ctor_get(v___x_2810_, 0);
v_isSharedCheck_2850_ = !lean_is_exclusive(v___x_2810_);
if (v_isSharedCheck_2850_ == 0)
{
v___x_2845_ = v___x_2810_;
v_isShared_2846_ = v_isSharedCheck_2850_;
goto v_resetjp_2844_;
}
else
{
lean_inc(v_a_2843_);
lean_dec(v___x_2810_);
v___x_2845_ = lean_box(0);
v_isShared_2846_ = v_isSharedCheck_2850_;
goto v_resetjp_2844_;
}
v_resetjp_2844_:
{
lean_object* v___x_2848_; 
if (v_isShared_2846_ == 0)
{
v___x_2848_ = v___x_2845_;
goto v_reusejp_2847_;
}
else
{
lean_object* v_reuseFailAlloc_2849_; 
v_reuseFailAlloc_2849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2849_, 0, v_a_2843_);
v___x_2848_ = v_reuseFailAlloc_2849_;
goto v_reusejp_2847_;
}
v_reusejp_2847_:
{
return v___x_2848_;
}
}
}
}
else
{
lean_object* v_a_2851_; lean_object* v___x_2853_; uint8_t v_isShared_2854_; uint8_t v_isSharedCheck_2858_; 
lean_dec(v___x_2808_);
lean_dec_ref(v_givenNames_2796_);
lean_dec(v_recursorName_2795_);
lean_dec(v_majorFVarId_2794_);
lean_dec(v_mvarId_2793_);
v_a_2851_ = lean_ctor_get(v___x_2809_, 0);
v_isSharedCheck_2858_ = !lean_is_exclusive(v___x_2809_);
if (v_isSharedCheck_2858_ == 0)
{
v___x_2853_ = v___x_2809_;
v_isShared_2854_ = v_isSharedCheck_2858_;
goto v_resetjp_2852_;
}
else
{
lean_inc(v_a_2851_);
lean_dec(v___x_2809_);
v___x_2853_ = lean_box(0);
v_isShared_2854_ = v_isSharedCheck_2858_;
goto v_resetjp_2852_;
}
v_resetjp_2852_:
{
lean_object* v___x_2856_; 
if (v_isShared_2854_ == 0)
{
v___x_2856_ = v___x_2853_;
goto v_reusejp_2855_;
}
else
{
lean_object* v_reuseFailAlloc_2857_; 
v_reuseFailAlloc_2857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2857_, 0, v_a_2851_);
v___x_2856_ = v_reuseFailAlloc_2857_;
goto v_reusejp_2855_;
}
v_reusejp_2855_:
{
return v___x_2856_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_induction___lam__0___boxed(lean_object* v___x_2877_, lean_object* v_mvarId_2878_, lean_object* v_majorFVarId_2879_, lean_object* v_recursorName_2880_, lean_object* v_givenNames_2881_, lean_object* v_cls_2882_, lean_object* v___y_2883_, lean_object* v___y_2884_, lean_object* v___y_2885_, lean_object* v___y_2886_, lean_object* v___y_2887_){
_start:
{
lean_object* v_res_2888_; 
v_res_2888_ = l_Lean_MVarId_induction___lam__0(v___x_2877_, v_mvarId_2878_, v_majorFVarId_2879_, v_recursorName_2880_, v_givenNames_2881_, v_cls_2882_, v___y_2883_, v___y_2884_, v___y_2885_, v___y_2886_);
lean_dec(v___y_2886_);
lean_dec_ref(v___y_2885_);
lean_dec(v___y_2884_);
lean_dec_ref(v___y_2883_);
return v_res_2888_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_induction(lean_object* v_mvarId_2889_, lean_object* v_majorFVarId_2890_, lean_object* v_recursorName_2891_, lean_object* v_givenNames_2892_, lean_object* v_a_2893_, lean_object* v_a_2894_, lean_object* v_a_2895_, lean_object* v_a_2896_){
_start:
{
lean_object* v___x_2898_; lean_object* v_cls_2899_; lean_object* v___f_2900_; lean_object* v___x_2901_; 
v___x_2898_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__0));
v_cls_2899_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__2));
lean_inc(v_mvarId_2889_);
v___f_2900_ = lean_alloc_closure((void*)(l_Lean_MVarId_induction___lam__0___boxed), 11, 6);
lean_closure_set(v___f_2900_, 0, v___x_2898_);
lean_closure_set(v___f_2900_, 1, v_mvarId_2889_);
lean_closure_set(v___f_2900_, 2, v_majorFVarId_2890_);
lean_closure_set(v___f_2900_, 3, v_recursorName_2891_);
lean_closure_set(v___f_2900_, 4, v_givenNames_2892_);
lean_closure_set(v___f_2900_, 5, v_cls_2899_);
v___x_2901_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___redArg(v_mvarId_2889_, v___f_2900_, v_a_2893_, v_a_2894_, v_a_2895_, v_a_2896_);
return v___x_2901_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_induction___boxed(lean_object* v_mvarId_2902_, lean_object* v_majorFVarId_2903_, lean_object* v_recursorName_2904_, lean_object* v_givenNames_2905_, lean_object* v_a_2906_, lean_object* v_a_2907_, lean_object* v_a_2908_, lean_object* v_a_2909_, lean_object* v_a_2910_){
_start:
{
lean_object* v_res_2911_; 
v_res_2911_ = l_Lean_MVarId_induction(v_mvarId_2902_, v_majorFVarId_2903_, v_recursorName_2904_, v_givenNames_2905_, v_a_2906_, v_a_2907_, v_a_2908_, v_a_2909_);
lean_dec(v_a_2909_);
lean_dec_ref(v_a_2908_);
lean_dec(v_a_2907_);
lean_dec_ref(v_a_2906_);
return v_res_2911_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; 
v___x_2959_ = lean_unsigned_to_nat(2221195325u);
v___x_2960_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_));
v___x_2961_ = l_Lean_Name_num___override(v___x_2960_, v___x_2959_);
return v___x_2961_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; 
v___x_2963_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_));
v___x_2964_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_);
v___x_2965_ = l_Lean_Name_str___override(v___x_2964_, v___x_2963_);
return v___x_2965_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; 
v___x_2967_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_));
v___x_2968_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_);
v___x_2969_ = l_Lean_Name_str___override(v___x_2968_, v___x_2967_);
return v___x_2969_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; 
v___x_2970_ = lean_unsigned_to_nat(2u);
v___x_2971_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_);
v___x_2972_ = l_Lean_Name_num___override(v___x_2971_, v___x_2970_);
return v___x_2972_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2974_; uint8_t v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; 
v___x_2974_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__2));
v___x_2975_ = 0;
v___x_2976_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_);
v___x_2977_ = l_Lean_registerTraceClass(v___x_2974_, v___x_2975_, v___x_2976_);
return v___x_2977_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2____boxed(lean_object* v_a_2978_){
_start:
{
lean_object* v_res_2979_; 
v_res_2979_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_();
return v_res_2979_;
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
