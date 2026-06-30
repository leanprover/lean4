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
lean_object* v___f_134_; lean_object* v___x_8866__overap_135_; lean_object* v___x_136_; 
v___f_134_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__4___closed__0));
v___x_8866__overap_135_ = lean_panic_fn_borrowed(v___f_134_, v_msg_128_);
lean_inc(v___y_132_);
lean_inc_ref(v___y_131_);
lean_inc(v___y_130_);
lean_inc_ref(v___y_129_);
v___x_136_ = lean_apply_5(v___x_8866__overap_135_, v___y_129_, v___y_130_, v___y_131_, v___y_132_, lean_box(0));
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
size_t v_x_10123__boxed_363_; size_t v_x_10124__boxed_364_; lean_object* v_res_365_; 
v_x_10123__boxed_363_ = lean_unbox_usize(v_x_359_);
lean_dec(v_x_359_);
v_x_10124__boxed_364_ = lean_unbox_usize(v_x_360_);
lean_dec(v_x_360_);
v_res_365_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2___redArg(v_x_358_, v_x_10123__boxed_363_, v_x_10124__boxed_364_, v_x_361_, v_x_362_);
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
lean_object* v___y_574_; lean_object* v___y_575_; lean_object* v___y_576_; lean_object* v___y_577_; lean_object* v___y_630_; lean_object* v___y_631_; uint8_t v___y_632_; lean_object* v___y_633_; lean_object* v___y_634_; lean_object* v___y_635_; lean_object* v___y_636_; lean_object* v___y_637_; lean_object* v___y_638_; lean_object* v___y_639_; lean_object* v___y_640_; lean_object* v___y_641_; uint8_t v___y_642_; lean_object* v___y_643_; lean_object* v___y_644_; uint8_t v___y_645_; lean_object* v___y_681_; lean_object* v___y_682_; lean_object* v___y_683_; lean_object* v___y_684_; uint8_t v___y_685_; lean_object* v___y_686_; uint8_t v___y_687_; lean_object* v___y_688_; lean_object* v___y_689_; lean_object* v___y_690_; lean_object* v___y_691_; lean_object* v___y_692_; lean_object* v___y_693_; lean_object* v___y_694_; lean_object* v___y_695_; uint8_t v___y_713_; lean_object* v___y_714_; lean_object* v_fst_715_; lean_object* v_snd_716_; uint8_t v___y_733_; lean_object* v___y_734_; lean_object* v___y_735_; lean_object* v___x_747_; 
v___x_747_ = l_Lean_Meta_whnfForall(v_recursorType_565_, v_a_568_, v_a_569_, v_a_570_, v_a_571_);
if (lean_obj_tag(v___x_747_) == 0)
{
lean_object* v_a_748_; lean_object* v___y_750_; lean_object* v___y_751_; lean_object* v___y_752_; lean_object* v___y_753_; uint8_t v___y_754_; lean_object* v___y_755_; lean_object* v___y_756_; lean_object* v___y_757_; lean_object* v___y_758_; lean_object* v___y_759_; lean_object* v___y_760_; lean_object* v___y_761_; uint8_t v___y_762_; lean_object* v___y_763_; lean_object* v___y_805_; uint8_t v___y_806_; uint8_t v___y_807_; lean_object* v___y_808_; lean_object* v___y_809_; lean_object* v___y_810_; lean_object* v___y_811_; lean_object* v___y_812_; lean_object* v___y_813_; lean_object* v___y_814_; lean_object* v___y_826_; uint8_t v___y_827_; lean_object* v___y_828_; lean_object* v___y_829_; lean_object* v___y_830_; lean_object* v___y_831_; lean_object* v___y_832_; lean_object* v___y_833_; uint8_t v___y_834_; lean_object* v___y_904_; uint8_t v___y_905_; lean_object* v___y_906_; lean_object* v___y_907_; uint8_t v___y_908_; lean_object* v___y_909_; lean_object* v___y_910_; lean_object* v___y_911_; lean_object* v___y_912_; uint8_t v___y_918_; lean_object* v___y_919_; lean_object* v___y_920_; lean_object* v___y_921_; lean_object* v___y_922_; lean_object* v___y_923_; uint8_t v___y_935_; uint8_t v___x_982_; 
v_a_748_ = lean_ctor_get(v___x_747_, 0);
lean_inc(v_a_748_);
lean_dec_ref_known(v___x_747_, 1);
v___x_982_ = l_Lean_Expr_isForall(v_a_748_);
if (v___x_982_ == 0)
{
v___y_935_ = v___x_982_;
goto v___jp_934_;
}
else
{
lean_object* v_numArgs_983_; uint8_t v___x_984_; 
v_numArgs_983_ = lean_ctor_get(v_recursorInfo_555_, 3);
v___x_984_ = lean_nat_dec_lt(v_pos_562_, v_numArgs_983_);
v___y_935_ = v___x_984_;
goto v___jp_934_;
}
v___jp_749_:
{
lean_object* v___x_764_; 
v___x_764_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___y_756_, v___y_758_, v___y_752_, v___y_750_, v___y_755_, v___y_757_);
if (lean_obj_tag(v___x_764_) == 0)
{
lean_object* v_a_765_; lean_object* v___x_766_; 
v_a_765_ = lean_ctor_get(v___x_764_, 0);
lean_inc(v_a_765_);
lean_dec_ref_known(v___x_764_, 1);
lean_inc(v_mvarId_553_);
v___x_766_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTypeBody(v_mvarId_553_, v_a_748_, v_a_765_, v___y_752_, v___y_750_, v___y_755_, v___y_757_);
if (lean_obj_tag(v___x_766_) == 0)
{
lean_object* v_options_767_; lean_object* v_a_768_; lean_object* v_inheritedTraceOptions_769_; uint8_t v_hasTrace_770_; lean_object* v___x_771_; 
v_options_767_ = lean_ctor_get(v___y_755_, 2);
v_a_768_ = lean_ctor_get(v___x_766_, 0);
lean_inc(v_a_768_);
lean_dec_ref_known(v___x_766_, 1);
v_inheritedTraceOptions_769_ = lean_ctor_get(v___y_755_, 13);
v_hasTrace_770_ = lean_ctor_get_uint8(v_options_767_, sizeof(void*)*1);
lean_inc(v_a_765_);
v___x_771_ = l_Lean_Expr_app___override(v_recursor_564_, v_a_765_);
if (v_hasTrace_770_ == 0)
{
v___y_681_ = v___y_751_;
v___y_682_ = v___x_771_;
v___y_683_ = v___y_753_;
v___y_684_ = v___y_760_;
v___y_685_ = v___y_754_;
v___y_686_ = v___y_761_;
v___y_687_ = v___y_762_;
v___y_688_ = v_a_768_;
v___y_689_ = v___y_763_;
v___y_690_ = v___y_759_;
v___y_691_ = v_a_765_;
v___y_692_ = v___y_752_;
v___y_693_ = v___y_750_;
v___y_694_ = v___y_755_;
v___y_695_ = v___y_757_;
goto v___jp_680_;
}
else
{
lean_object* v___x_772_; lean_object* v___x_773_; uint8_t v___x_774_; 
v___x_772_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__2));
v___x_773_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5);
v___x_774_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_769_, v_options_767_, v___x_773_);
if (v___x_774_ == 0)
{
v___y_681_ = v___y_751_;
v___y_682_ = v___x_771_;
v___y_683_ = v___y_753_;
v___y_684_ = v___y_760_;
v___y_685_ = v___y_754_;
v___y_686_ = v___y_761_;
v___y_687_ = v___y_762_;
v___y_688_ = v_a_768_;
v___y_689_ = v___y_763_;
v___y_690_ = v___y_759_;
v___y_691_ = v_a_765_;
v___y_692_ = v___y_752_;
v___y_693_ = v___y_750_;
v___y_694_ = v___y_755_;
v___y_695_ = v___y_757_;
goto v___jp_680_;
}
else
{
lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; 
v___x_775_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__11, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__11_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__11);
v___x_776_ = l_Lean_Expr_fvarId_x21(v_major_557_);
v___x_777_ = l_Lean_MessageData_ofName(v___x_776_);
v___x_778_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_778_, 0, v___x_775_);
lean_ctor_set(v___x_778_, 1, v___x_777_);
v___x_779_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1(v___x_772_, v___x_778_, v___y_752_, v___y_750_, v___y_755_, v___y_757_);
if (lean_obj_tag(v___x_779_) == 0)
{
lean_dec_ref_known(v___x_779_, 1);
v___y_681_ = v___y_751_;
v___y_682_ = v___x_771_;
v___y_683_ = v___y_753_;
v___y_684_ = v___y_760_;
v___y_685_ = v___y_754_;
v___y_686_ = v___y_761_;
v___y_687_ = v___y_762_;
v___y_688_ = v_a_768_;
v___y_689_ = v___y_763_;
v___y_690_ = v___y_759_;
v___y_691_ = v_a_765_;
v___y_692_ = v___y_752_;
v___y_693_ = v___y_750_;
v___y_694_ = v___y_755_;
v___y_695_ = v___y_757_;
goto v___jp_680_;
}
else
{
lean_object* v_a_780_; lean_object* v___x_782_; uint8_t v_isShared_783_; uint8_t v_isSharedCheck_787_; 
lean_dec_ref(v___x_771_);
lean_dec(v_a_768_);
lean_dec(v_a_765_);
lean_dec_ref(v___y_763_);
lean_dec(v___y_761_);
lean_dec(v___y_760_);
lean_dec(v___y_753_);
lean_dec(v___y_751_);
lean_dec_ref(v_subgoals_567_);
lean_dec(v_minorIdx_563_);
lean_dec(v_pos_562_);
lean_dec(v_baseSubst_559_);
lean_dec_ref(v_major_557_);
lean_dec(v_mvarId_553_);
v_a_780_ = lean_ctor_get(v___x_779_, 0);
v_isSharedCheck_787_ = !lean_is_exclusive(v___x_779_);
if (v_isSharedCheck_787_ == 0)
{
v___x_782_ = v___x_779_;
v_isShared_783_ = v_isSharedCheck_787_;
goto v_resetjp_781_;
}
else
{
lean_inc(v_a_780_);
lean_dec(v___x_779_);
v___x_782_ = lean_box(0);
v_isShared_783_ = v_isSharedCheck_787_;
goto v_resetjp_781_;
}
v_resetjp_781_:
{
lean_object* v___x_785_; 
if (v_isShared_783_ == 0)
{
v___x_785_ = v___x_782_;
goto v_reusejp_784_;
}
else
{
lean_object* v_reuseFailAlloc_786_; 
v_reuseFailAlloc_786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_786_, 0, v_a_780_);
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
}
}
else
{
lean_object* v_a_788_; lean_object* v___x_790_; uint8_t v_isShared_791_; uint8_t v_isSharedCheck_795_; 
lean_dec(v_a_765_);
lean_dec_ref(v___y_763_);
lean_dec(v___y_761_);
lean_dec(v___y_760_);
lean_dec(v___y_753_);
lean_dec(v___y_751_);
lean_dec_ref(v_subgoals_567_);
lean_dec_ref(v_recursor_564_);
lean_dec(v_minorIdx_563_);
lean_dec(v_pos_562_);
lean_dec(v_baseSubst_559_);
lean_dec_ref(v_major_557_);
lean_dec(v_mvarId_553_);
v_a_788_ = lean_ctor_get(v___x_766_, 0);
v_isSharedCheck_795_ = !lean_is_exclusive(v___x_766_);
if (v_isSharedCheck_795_ == 0)
{
v___x_790_ = v___x_766_;
v_isShared_791_ = v_isSharedCheck_795_;
goto v_resetjp_789_;
}
else
{
lean_inc(v_a_788_);
lean_dec(v___x_766_);
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
lean_object* v_a_796_; lean_object* v___x_798_; uint8_t v_isShared_799_; uint8_t v_isSharedCheck_803_; 
lean_dec_ref(v___y_763_);
lean_dec(v___y_761_);
lean_dec(v___y_760_);
lean_dec(v___y_753_);
lean_dec(v___y_751_);
lean_dec(v_a_748_);
lean_dec_ref(v_subgoals_567_);
lean_dec_ref(v_recursor_564_);
lean_dec(v_minorIdx_563_);
lean_dec(v_pos_562_);
lean_dec(v_baseSubst_559_);
lean_dec_ref(v_major_557_);
lean_dec(v_mvarId_553_);
v_a_796_ = lean_ctor_get(v___x_764_, 0);
v_isSharedCheck_803_ = !lean_is_exclusive(v___x_764_);
if (v_isSharedCheck_803_ == 0)
{
v___x_798_ = v___x_764_;
v_isShared_799_ = v_isSharedCheck_803_;
goto v_resetjp_797_;
}
else
{
lean_inc(v_a_796_);
lean_dec(v___x_764_);
v___x_798_ = lean_box(0);
v_isShared_799_ = v_isSharedCheck_803_;
goto v_resetjp_797_;
}
v_resetjp_797_:
{
lean_object* v___x_801_; 
if (v_isShared_799_ == 0)
{
v___x_801_ = v___x_798_;
goto v_reusejp_800_;
}
else
{
lean_object* v_reuseFailAlloc_802_; 
v_reuseFailAlloc_802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_802_, 0, v_a_796_);
v___x_801_ = v_reuseFailAlloc_802_;
goto v_reusejp_800_;
}
v_reusejp_800_:
{
return v___x_801_;
}
}
}
}
v___jp_804_:
{
lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; uint8_t v___x_821_; 
v___x_815_ = lean_nat_sub(v___y_805_, v_initialArity_560_);
lean_dec(v___y_805_);
v___x_816_ = lean_array_get_size(v_reverted_556_);
v___x_817_ = lean_array_get_size(v_indices_558_);
v___x_818_ = lean_nat_sub(v___x_816_, v___x_817_);
v___x_819_ = lean_nat_sub(v___x_818_, v___y_810_);
lean_dec(v___x_818_);
v___x_820_ = lean_array_get_size(v_givenNames_554_);
v___x_821_ = lean_nat_dec_lt(v_minorIdx_563_, v___x_820_);
if (v___x_821_ == 0)
{
lean_object* v___x_822_; lean_object* v___x_823_; 
v___x_822_ = lean_box(0);
v___x_823_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_823_, 0, v___x_822_);
lean_ctor_set_uint8(v___x_823_, sizeof(void*)*1, v___y_807_);
v___y_750_ = v___y_812_;
v___y_751_ = v___x_816_;
v___y_752_ = v___y_811_;
v___y_753_ = v___x_817_;
v___y_754_ = v___y_806_;
v___y_755_ = v___y_813_;
v___y_756_ = v___y_808_;
v___y_757_ = v___y_814_;
v___y_758_ = v___y_809_;
v___y_759_ = v___y_810_;
v___y_760_ = v___x_819_;
v___y_761_ = v___x_815_;
v___y_762_ = v___y_807_;
v___y_763_ = v___x_823_;
goto v___jp_749_;
}
else
{
lean_object* v___x_824_; 
v___x_824_ = lean_array_fget_borrowed(v_givenNames_554_, v_minorIdx_563_);
lean_inc(v___x_824_);
v___y_750_ = v___y_812_;
v___y_751_ = v___x_816_;
v___y_752_ = v___y_811_;
v___y_753_ = v___x_817_;
v___y_754_ = v___y_806_;
v___y_755_ = v___y_813_;
v___y_756_ = v___y_808_;
v___y_757_ = v___y_814_;
v___y_758_ = v___y_809_;
v___y_759_ = v___y_810_;
v___y_760_ = v___x_819_;
v___y_761_ = v___x_815_;
v___y_762_ = v___y_807_;
v___y_763_ = v___x_824_;
goto v___jp_749_;
}
}
v___jp_825_:
{
if (v___y_834_ == 0)
{
lean_object* v___x_835_; uint8_t v___x_836_; 
lean_inc_ref(v___y_829_);
v___x_835_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTargetArity(v___y_829_);
v___x_836_ = lean_nat_dec_lt(v___x_835_, v_initialArity_560_);
if (v___x_836_ == 0)
{
v___y_805_ = v___x_835_;
v___y_806_ = v___y_827_;
v___y_807_ = v___y_834_;
v___y_808_ = v___y_829_;
v___y_809_ = v___y_831_;
v___y_810_ = v___y_832_;
v___y_811_ = v___y_830_;
v___y_812_ = v___y_833_;
v___y_813_ = v___y_826_;
v___y_814_ = v___y_828_;
goto v___jp_804_;
}
else
{
lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; 
v___x_837_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1));
v___x_838_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9);
lean_inc(v_mvarId_553_);
v___x_839_ = l_Lean_Meta_throwTacticEx___redArg(v___x_837_, v_mvarId_553_, v___x_838_, v___y_830_, v___y_833_, v___y_826_, v___y_828_);
if (lean_obj_tag(v___x_839_) == 0)
{
lean_dec_ref_known(v___x_839_, 1);
v___y_805_ = v___x_835_;
v___y_806_ = v___y_827_;
v___y_807_ = v___y_834_;
v___y_808_ = v___y_829_;
v___y_809_ = v___y_831_;
v___y_810_ = v___y_832_;
v___y_811_ = v___y_830_;
v___y_812_ = v___y_833_;
v___y_813_ = v___y_826_;
v___y_814_ = v___y_828_;
goto v___jp_804_;
}
else
{
lean_object* v_a_840_; lean_object* v___x_842_; uint8_t v_isShared_843_; uint8_t v_isSharedCheck_847_; 
lean_dec(v___x_835_);
lean_dec(v___y_831_);
lean_dec_ref(v___y_829_);
lean_dec(v_a_748_);
lean_dec_ref(v_subgoals_567_);
lean_dec_ref(v_recursor_564_);
lean_dec(v_minorIdx_563_);
lean_dec(v_pos_562_);
lean_dec(v_baseSubst_559_);
lean_dec_ref(v_major_557_);
lean_dec(v_mvarId_553_);
v_a_840_ = lean_ctor_get(v___x_839_, 0);
v_isSharedCheck_847_ = !lean_is_exclusive(v___x_839_);
if (v_isSharedCheck_847_ == 0)
{
v___x_842_ = v___x_839_;
v_isShared_843_ = v_isSharedCheck_847_;
goto v_resetjp_841_;
}
else
{
lean_inc(v_a_840_);
lean_dec(v___x_839_);
v___x_842_ = lean_box(0);
v_isShared_843_ = v_isSharedCheck_847_;
goto v_resetjp_841_;
}
v_resetjp_841_:
{
lean_object* v___x_845_; 
if (v_isShared_843_ == 0)
{
v___x_845_ = v___x_842_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v_a_840_);
v___x_845_ = v_reuseFailAlloc_846_;
goto v_reusejp_844_;
}
v_reusejp_844_:
{
return v___x_845_;
}
}
}
}
}
else
{
lean_object* v___x_848_; lean_object* v___x_849_; 
v___x_848_ = lean_box(0);
lean_inc_ref(v___y_829_);
v___x_849_ = l_Lean_Meta_synthInstance_x3f(v___y_829_, v___x_848_, v___y_830_, v___y_833_, v___y_826_, v___y_828_);
if (lean_obj_tag(v___x_849_) == 0)
{
lean_object* v_a_850_; 
v_a_850_ = lean_ctor_get(v___x_849_, 0);
lean_inc(v_a_850_);
lean_dec_ref_known(v___x_849_, 1);
if (lean_obj_tag(v_a_850_) == 0)
{
lean_object* v___x_851_; 
v___x_851_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___y_829_, v___y_831_, v___y_830_, v___y_833_, v___y_826_, v___y_828_);
if (lean_obj_tag(v___x_851_) == 0)
{
lean_object* v_a_852_; lean_object* v___x_853_; 
v_a_852_ = lean_ctor_get(v___x_851_, 0);
lean_inc(v_a_852_);
lean_dec_ref_known(v___x_851_, 1);
lean_inc(v_mvarId_553_);
v___x_853_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTypeBody(v_mvarId_553_, v_a_748_, v_a_852_, v___y_830_, v___y_833_, v___y_826_, v___y_828_);
if (lean_obj_tag(v___x_853_) == 0)
{
lean_object* v_a_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; 
v_a_854_ = lean_ctor_get(v___x_853_, 0);
lean_inc(v_a_854_);
lean_dec_ref_known(v___x_853_, 1);
lean_inc(v_a_852_);
v___x_855_ = l_Lean_Expr_app___override(v_recursor_564_, v_a_852_);
v___x_856_ = lean_nat_add(v_pos_562_, v___y_832_);
lean_dec(v_pos_562_);
v___x_857_ = lean_nat_add(v_minorIdx_563_, v___y_832_);
lean_dec(v_minorIdx_563_);
v___x_858_ = l_Lean_Expr_mvarId_x21(v_a_852_);
lean_dec(v_a_852_);
v___x_859_ = ((lean_object*)(l_Lean_Meta_instInhabitedInductionSubgoal_default___closed__0));
v___x_860_ = lean_box(0);
v___x_861_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_861_, 0, v___x_858_);
lean_ctor_set(v___x_861_, 1, v___x_859_);
lean_ctor_set(v___x_861_, 2, v___x_860_);
v___x_862_ = lean_array_push(v_subgoals_567_, v___x_861_);
v_pos_562_ = v___x_856_;
v_minorIdx_563_ = v___x_857_;
v_recursor_564_ = v___x_855_;
v_recursorType_565_ = v_a_854_;
v_subgoals_567_ = v___x_862_;
v_a_568_ = v___y_830_;
v_a_569_ = v___y_833_;
v_a_570_ = v___y_826_;
v_a_571_ = v___y_828_;
goto _start;
}
else
{
lean_object* v_a_864_; lean_object* v___x_866_; uint8_t v_isShared_867_; uint8_t v_isSharedCheck_871_; 
lean_dec(v_a_852_);
lean_dec_ref(v_subgoals_567_);
lean_dec_ref(v_recursor_564_);
lean_dec(v_minorIdx_563_);
lean_dec(v_pos_562_);
lean_dec(v_baseSubst_559_);
lean_dec_ref(v_major_557_);
lean_dec(v_mvarId_553_);
v_a_864_ = lean_ctor_get(v___x_853_, 0);
v_isSharedCheck_871_ = !lean_is_exclusive(v___x_853_);
if (v_isSharedCheck_871_ == 0)
{
v___x_866_ = v___x_853_;
v_isShared_867_ = v_isSharedCheck_871_;
goto v_resetjp_865_;
}
else
{
lean_inc(v_a_864_);
lean_dec(v___x_853_);
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
lean_object* v_a_872_; lean_object* v___x_874_; uint8_t v_isShared_875_; uint8_t v_isSharedCheck_879_; 
lean_dec(v_a_748_);
lean_dec_ref(v_subgoals_567_);
lean_dec_ref(v_recursor_564_);
lean_dec(v_minorIdx_563_);
lean_dec(v_pos_562_);
lean_dec(v_baseSubst_559_);
lean_dec_ref(v_major_557_);
lean_dec(v_mvarId_553_);
v_a_872_ = lean_ctor_get(v___x_851_, 0);
v_isSharedCheck_879_ = !lean_is_exclusive(v___x_851_);
if (v_isSharedCheck_879_ == 0)
{
v___x_874_ = v___x_851_;
v_isShared_875_ = v_isSharedCheck_879_;
goto v_resetjp_873_;
}
else
{
lean_inc(v_a_872_);
lean_dec(v___x_851_);
v___x_874_ = lean_box(0);
v_isShared_875_ = v_isSharedCheck_879_;
goto v_resetjp_873_;
}
v_resetjp_873_:
{
lean_object* v___x_877_; 
if (v_isShared_875_ == 0)
{
v___x_877_ = v___x_874_;
goto v_reusejp_876_;
}
else
{
lean_object* v_reuseFailAlloc_878_; 
v_reuseFailAlloc_878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_878_, 0, v_a_872_);
v___x_877_ = v_reuseFailAlloc_878_;
goto v_reusejp_876_;
}
v_reusejp_876_:
{
return v___x_877_;
}
}
}
}
else
{
lean_object* v_val_880_; lean_object* v___x_881_; 
lean_dec(v___y_831_);
lean_dec_ref(v___y_829_);
v_val_880_ = lean_ctor_get(v_a_850_, 0);
lean_inc(v_val_880_);
lean_dec_ref_known(v_a_850_, 1);
lean_inc(v_mvarId_553_);
v___x_881_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTypeBody(v_mvarId_553_, v_a_748_, v_val_880_, v___y_830_, v___y_833_, v___y_826_, v___y_828_);
if (lean_obj_tag(v___x_881_) == 0)
{
lean_object* v_a_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; 
v_a_882_ = lean_ctor_get(v___x_881_, 0);
lean_inc(v_a_882_);
lean_dec_ref_known(v___x_881_, 1);
v___x_883_ = l_Lean_Expr_app___override(v_recursor_564_, v_val_880_);
v___x_884_ = lean_nat_add(v_pos_562_, v___y_832_);
lean_dec(v_pos_562_);
v___x_885_ = lean_nat_add(v_minorIdx_563_, v___y_832_);
lean_dec(v_minorIdx_563_);
v_pos_562_ = v___x_884_;
v_minorIdx_563_ = v___x_885_;
v_recursor_564_ = v___x_883_;
v_recursorType_565_ = v_a_882_;
v_a_568_ = v___y_830_;
v_a_569_ = v___y_833_;
v_a_570_ = v___y_826_;
v_a_571_ = v___y_828_;
goto _start;
}
else
{
lean_object* v_a_887_; lean_object* v___x_889_; uint8_t v_isShared_890_; uint8_t v_isSharedCheck_894_; 
lean_dec(v_val_880_);
lean_dec_ref(v_subgoals_567_);
lean_dec_ref(v_recursor_564_);
lean_dec(v_minorIdx_563_);
lean_dec(v_pos_562_);
lean_dec(v_baseSubst_559_);
lean_dec_ref(v_major_557_);
lean_dec(v_mvarId_553_);
v_a_887_ = lean_ctor_get(v___x_881_, 0);
v_isSharedCheck_894_ = !lean_is_exclusive(v___x_881_);
if (v_isSharedCheck_894_ == 0)
{
v___x_889_ = v___x_881_;
v_isShared_890_ = v_isSharedCheck_894_;
goto v_resetjp_888_;
}
else
{
lean_inc(v_a_887_);
lean_dec(v___x_881_);
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
else
{
lean_object* v_a_895_; lean_object* v___x_897_; uint8_t v_isShared_898_; uint8_t v_isSharedCheck_902_; 
lean_dec(v___y_831_);
lean_dec_ref(v___y_829_);
lean_dec(v_a_748_);
lean_dec_ref(v_subgoals_567_);
lean_dec_ref(v_recursor_564_);
lean_dec(v_minorIdx_563_);
lean_dec(v_pos_562_);
lean_dec(v_baseSubst_559_);
lean_dec_ref(v_major_557_);
lean_dec(v_mvarId_553_);
v_a_895_ = lean_ctor_get(v___x_849_, 0);
v_isSharedCheck_902_ = !lean_is_exclusive(v___x_849_);
if (v_isSharedCheck_902_ == 0)
{
v___x_897_ = v___x_849_;
v_isShared_898_ = v_isSharedCheck_902_;
goto v_resetjp_896_;
}
else
{
lean_inc(v_a_895_);
lean_dec(v___x_849_);
v___x_897_ = lean_box(0);
v_isShared_898_ = v_isSharedCheck_902_;
goto v_resetjp_896_;
}
v_resetjp_896_:
{
lean_object* v___x_900_; 
if (v_isShared_898_ == 0)
{
v___x_900_ = v___x_897_;
goto v_reusejp_899_;
}
else
{
lean_object* v_reuseFailAlloc_901_; 
v_reuseFailAlloc_901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_901_, 0, v_a_895_);
v___x_900_ = v_reuseFailAlloc_901_;
goto v_reusejp_899_;
}
v_reusejp_899_:
{
return v___x_900_;
}
}
}
}
}
v___jp_903_:
{
uint8_t v___x_913_; 
v___x_913_ = l_Lean_BinderInfo_isInstImplicit(v___y_908_);
if (v___x_913_ == 0)
{
v___y_826_ = v___y_904_;
v___y_827_ = v___y_905_;
v___y_828_ = v___y_907_;
v___y_829_ = v___y_906_;
v___y_830_ = v___y_909_;
v___y_831_ = v___y_912_;
v___y_832_ = v___y_910_;
v___y_833_ = v___y_911_;
v___y_834_ = v___x_913_;
goto v___jp_825_;
}
else
{
lean_object* v___x_914_; lean_object* v___x_915_; uint8_t v___x_916_; 
v___x_914_ = lean_array_get_size(v_givenNames_554_);
v___x_915_ = lean_unsigned_to_nat(0u);
v___x_916_ = lean_nat_dec_eq(v___x_914_, v___x_915_);
v___y_826_ = v___y_904_;
v___y_827_ = v___y_905_;
v___y_828_ = v___y_907_;
v___y_829_ = v___y_906_;
v___y_830_ = v___y_909_;
v___y_831_ = v___y_912_;
v___y_832_ = v___y_910_;
v___y_833_ = v___y_911_;
v___y_834_ = v___x_916_;
goto v___jp_825_;
}
}
v___jp_917_:
{
if (lean_obj_tag(v_a_748_) == 7)
{
lean_object* v_binderName_924_; lean_object* v_binderType_925_; uint8_t v_binderInfo_926_; lean_object* v___x_927_; lean_object* v___x_928_; uint8_t v___x_929_; 
v_binderName_924_ = lean_ctor_get(v_a_748_, 0);
v_binderType_925_ = lean_ctor_get(v_a_748_, 1);
v_binderInfo_926_ = lean_ctor_get_uint8(v_a_748_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_925_);
v___x_927_ = l_Lean_Expr_headBeta(v_binderType_925_);
v___x_928_ = lean_unsigned_to_nat(1u);
v___x_929_ = lean_nat_dec_eq(v_numMinors_561_, v___x_928_);
if (v___x_929_ == 0)
{
lean_object* v___x_930_; lean_object* v___x_931_; 
lean_inc(v_binderName_924_);
v___x_930_ = lean_erase_macro_scopes(v_binderName_924_);
v___x_931_ = l_Lean_Name_append(v___y_919_, v___x_930_);
v___y_904_ = v___y_922_;
v___y_905_ = v___y_918_;
v___y_906_ = v___x_927_;
v___y_907_ = v___y_923_;
v___y_908_ = v_binderInfo_926_;
v___y_909_ = v___y_920_;
v___y_910_ = v___x_928_;
v___y_911_ = v___y_921_;
v___y_912_ = v___x_931_;
goto v___jp_903_;
}
else
{
v___y_904_ = v___y_922_;
v___y_905_ = v___y_918_;
v___y_906_ = v___x_927_;
v___y_907_ = v___y_923_;
v___y_908_ = v_binderInfo_926_;
v___y_909_ = v___y_920_;
v___y_910_ = v___x_928_;
v___y_911_ = v___y_921_;
v___y_912_ = v___y_919_;
goto v___jp_903_;
}
}
else
{
lean_object* v___x_932_; lean_object* v___x_933_; 
lean_dec(v___y_919_);
lean_dec(v_a_748_);
lean_dec_ref(v_subgoals_567_);
lean_dec_ref(v_recursor_564_);
lean_dec(v_minorIdx_563_);
lean_dec(v_pos_562_);
lean_dec(v_baseSubst_559_);
lean_dec_ref(v_major_557_);
lean_dec(v_mvarId_553_);
v___x_932_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__15, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__15_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__15);
v___x_933_ = l_panic___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__4(v___x_932_, v___y_920_, v___y_921_, v___y_922_, v___y_923_);
return v___x_933_;
}
}
v___jp_934_:
{
if (v___y_935_ == 0)
{
lean_dec(v_a_748_);
lean_dec(v_minorIdx_563_);
lean_dec(v_pos_562_);
lean_dec(v_baseSubst_559_);
lean_dec_ref(v_major_557_);
if (v_consumedMajor_566_ == 0)
{
lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; 
v___x_936_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1));
v___x_937_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9);
lean_inc(v_mvarId_553_);
v___x_938_ = l_Lean_Meta_throwTacticEx___redArg(v___x_936_, v_mvarId_553_, v___x_937_, v_a_568_, v_a_569_, v_a_570_, v_a_571_);
if (lean_obj_tag(v___x_938_) == 0)
{
lean_dec_ref_known(v___x_938_, 1);
v___y_574_ = v_a_568_;
v___y_575_ = v_a_569_;
v___y_576_ = v_a_570_;
v___y_577_ = v_a_571_;
goto v___jp_573_;
}
else
{
lean_object* v_a_939_; lean_object* v___x_941_; uint8_t v_isShared_942_; uint8_t v_isSharedCheck_946_; 
lean_dec_ref(v_subgoals_567_);
lean_dec_ref(v_recursor_564_);
lean_dec(v_mvarId_553_);
v_a_939_ = lean_ctor_get(v___x_938_, 0);
v_isSharedCheck_946_ = !lean_is_exclusive(v___x_938_);
if (v_isSharedCheck_946_ == 0)
{
v___x_941_ = v___x_938_;
v_isShared_942_ = v_isSharedCheck_946_;
goto v_resetjp_940_;
}
else
{
lean_inc(v_a_939_);
lean_dec(v___x_938_);
v___x_941_ = lean_box(0);
v_isShared_942_ = v_isSharedCheck_946_;
goto v_resetjp_940_;
}
v_resetjp_940_:
{
lean_object* v___x_944_; 
if (v_isShared_942_ == 0)
{
v___x_944_ = v___x_941_;
goto v_reusejp_943_;
}
else
{
lean_object* v_reuseFailAlloc_945_; 
v_reuseFailAlloc_945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_945_, 0, v_a_939_);
v___x_944_ = v_reuseFailAlloc_945_;
goto v_reusejp_943_;
}
v_reusejp_943_:
{
return v___x_944_;
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
lean_object* v___x_947_; uint8_t v___x_948_; 
v___x_947_ = l_Lean_Meta_RecursorInfo_firstIndexPos(v_recursorInfo_555_);
v___x_948_ = lean_nat_dec_eq(v_pos_562_, v___x_947_);
lean_dec(v___x_947_);
if (v___x_948_ == 0)
{
lean_object* v___x_949_; 
lean_inc(v_mvarId_553_);
v___x_949_ = l_Lean_MVarId_getTag(v_mvarId_553_, v_a_568_, v_a_569_, v_a_570_, v_a_571_);
if (lean_obj_tag(v___x_949_) == 0)
{
lean_object* v_a_950_; uint8_t v___x_951_; 
v_a_950_ = lean_ctor_get(v___x_949_, 0);
lean_inc(v_a_950_);
lean_dec_ref_known(v___x_949_, 1);
v___x_951_ = lean_nat_dec_le(v_numMinors_561_, v_minorIdx_563_);
if (v___x_951_ == 0)
{
v___y_918_ = v___y_935_;
v___y_919_ = v_a_950_;
v___y_920_ = v_a_568_;
v___y_921_ = v_a_569_;
v___y_922_ = v_a_570_;
v___y_923_ = v_a_571_;
goto v___jp_917_;
}
else
{
lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; 
v___x_952_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1));
v___x_953_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9);
lean_inc(v_mvarId_553_);
v___x_954_ = l_Lean_Meta_throwTacticEx___redArg(v___x_952_, v_mvarId_553_, v___x_953_, v_a_568_, v_a_569_, v_a_570_, v_a_571_);
if (lean_obj_tag(v___x_954_) == 0)
{
lean_dec_ref_known(v___x_954_, 1);
v___y_918_ = v___y_935_;
v___y_919_ = v_a_950_;
v___y_920_ = v_a_568_;
v___y_921_ = v_a_569_;
v___y_922_ = v_a_570_;
v___y_923_ = v_a_571_;
goto v___jp_917_;
}
else
{
lean_object* v_a_955_; lean_object* v___x_957_; uint8_t v_isShared_958_; uint8_t v_isSharedCheck_962_; 
lean_dec(v_a_950_);
lean_dec(v_a_748_);
lean_dec_ref(v_subgoals_567_);
lean_dec_ref(v_recursor_564_);
lean_dec(v_minorIdx_563_);
lean_dec(v_pos_562_);
lean_dec(v_baseSubst_559_);
lean_dec_ref(v_major_557_);
lean_dec(v_mvarId_553_);
v_a_955_ = lean_ctor_get(v___x_954_, 0);
v_isSharedCheck_962_ = !lean_is_exclusive(v___x_954_);
if (v_isSharedCheck_962_ == 0)
{
v___x_957_ = v___x_954_;
v_isShared_958_ = v_isSharedCheck_962_;
goto v_resetjp_956_;
}
else
{
lean_inc(v_a_955_);
lean_dec(v___x_954_);
v___x_957_ = lean_box(0);
v_isShared_958_ = v_isSharedCheck_962_;
goto v_resetjp_956_;
}
v_resetjp_956_:
{
lean_object* v___x_960_; 
if (v_isShared_958_ == 0)
{
v___x_960_ = v___x_957_;
goto v_reusejp_959_;
}
else
{
lean_object* v_reuseFailAlloc_961_; 
v_reuseFailAlloc_961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_961_, 0, v_a_955_);
v___x_960_ = v_reuseFailAlloc_961_;
goto v_reusejp_959_;
}
v_reusejp_959_:
{
return v___x_960_;
}
}
}
}
}
else
{
lean_object* v_a_963_; lean_object* v___x_965_; uint8_t v_isShared_966_; uint8_t v_isSharedCheck_970_; 
lean_dec(v_a_748_);
lean_dec_ref(v_subgoals_567_);
lean_dec_ref(v_recursor_564_);
lean_dec(v_minorIdx_563_);
lean_dec(v_pos_562_);
lean_dec(v_baseSubst_559_);
lean_dec_ref(v_major_557_);
lean_dec(v_mvarId_553_);
v_a_963_ = lean_ctor_get(v___x_949_, 0);
v_isSharedCheck_970_ = !lean_is_exclusive(v___x_949_);
if (v_isSharedCheck_970_ == 0)
{
v___x_965_ = v___x_949_;
v_isShared_966_ = v_isSharedCheck_970_;
goto v_resetjp_964_;
}
else
{
lean_inc(v_a_963_);
lean_dec(v___x_949_);
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
else
{
lean_object* v___x_971_; lean_object* v___x_972_; uint8_t v___x_973_; 
v___x_971_ = lean_unsigned_to_nat(0u);
v___x_972_ = lean_array_get_size(v_indices_558_);
v___x_973_ = lean_nat_dec_lt(v___x_971_, v___x_972_);
if (v___x_973_ == 0)
{
v___y_713_ = v___x_948_;
v___y_714_ = v___x_972_;
v_fst_715_ = v_recursor_564_;
v_snd_716_ = v_a_748_;
goto v___jp_712_;
}
else
{
lean_object* v___x_974_; uint8_t v___x_975_; 
lean_inc(v_a_748_);
lean_inc_ref(v_recursor_564_);
v___x_974_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_974_, 0, v_recursor_564_);
lean_ctor_set(v___x_974_, 1, v_a_748_);
v___x_975_ = lean_nat_dec_le(v___x_972_, v___x_972_);
if (v___x_975_ == 0)
{
if (v___x_973_ == 0)
{
lean_dec_ref_known(v___x_974_, 2);
v___y_713_ = v___x_948_;
v___y_714_ = v___x_972_;
v_fst_715_ = v_recursor_564_;
v_snd_716_ = v_a_748_;
goto v___jp_712_;
}
else
{
size_t v___x_976_; size_t v___x_977_; lean_object* v___x_978_; 
lean_dec(v_a_748_);
lean_dec_ref(v_recursor_564_);
v___x_976_ = ((size_t)0ULL);
v___x_977_ = lean_usize_of_nat(v___x_972_);
lean_inc(v_mvarId_553_);
v___x_978_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__5(v_mvarId_553_, v_indices_558_, v___x_976_, v___x_977_, v___x_974_, v_a_568_, v_a_569_, v_a_570_, v_a_571_);
v___y_733_ = v___x_948_;
v___y_734_ = v___x_972_;
v___y_735_ = v___x_978_;
goto v___jp_732_;
}
}
else
{
size_t v___x_979_; size_t v___x_980_; lean_object* v___x_981_; 
lean_dec(v_a_748_);
lean_dec_ref(v_recursor_564_);
v___x_979_ = ((size_t)0ULL);
v___x_980_ = lean_usize_of_nat(v___x_972_);
lean_inc(v_mvarId_553_);
v___x_981_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__5(v_mvarId_553_, v_indices_558_, v___x_979_, v___x_980_, v___x_974_, v_a_568_, v_a_569_, v_a_570_, v_a_571_);
v___y_733_ = v___x_948_;
v___y_734_ = v___x_972_;
v___y_735_ = v___x_981_;
goto v___jp_732_;
}
}
}
}
}
}
else
{
lean_object* v_a_985_; lean_object* v___x_987_; uint8_t v_isShared_988_; uint8_t v_isSharedCheck_992_; 
lean_dec_ref(v_subgoals_567_);
lean_dec_ref(v_recursor_564_);
lean_dec(v_minorIdx_563_);
lean_dec(v_pos_562_);
lean_dec(v_baseSubst_559_);
lean_dec_ref(v_major_557_);
lean_dec(v_mvarId_553_);
v_a_985_ = lean_ctor_get(v___x_747_, 0);
v_isSharedCheck_992_ = !lean_is_exclusive(v___x_747_);
if (v_isSharedCheck_992_ == 0)
{
v___x_987_ = v___x_747_;
v_isShared_988_ = v_isSharedCheck_992_;
goto v_resetjp_986_;
}
else
{
lean_inc(v_a_985_);
lean_dec(v___x_747_);
v___x_987_ = lean_box(0);
v_isShared_988_ = v_isSharedCheck_992_;
goto v_resetjp_986_;
}
v_resetjp_986_:
{
lean_object* v___x_990_; 
if (v_isShared_988_ == 0)
{
v___x_990_ = v___x_987_;
goto v_reusejp_989_;
}
else
{
lean_object* v_reuseFailAlloc_991_; 
v_reuseFailAlloc_991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_991_, 0, v_a_985_);
v___x_990_ = v_reuseFailAlloc_991_;
goto v_reusejp_989_;
}
v_reusejp_989_:
{
return v___x_990_;
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
lean_object* v___x_646_; 
v___x_646_ = l_Lean_Meta_introNCore(v___y_644_, v___y_640_, v___y_638_, v___y_645_, v___y_642_, v___y_633_, v___y_643_, v___y_635_, v___y_641_);
if (lean_obj_tag(v___x_646_) == 0)
{
lean_object* v_a_647_; lean_object* v_fst_648_; lean_object* v_snd_649_; lean_object* v___x_650_; lean_object* v___x_651_; 
v_a_647_ = lean_ctor_get(v___x_646_, 0);
lean_inc(v_a_647_);
lean_dec_ref_known(v___x_646_, 1);
v_fst_648_ = lean_ctor_get(v_a_647_, 0);
lean_inc(v_fst_648_);
v_snd_649_ = lean_ctor_get(v_a_647_, 1);
lean_inc(v_snd_649_);
lean_dec(v_a_647_);
v___x_650_ = lean_box(0);
v___x_651_ = l_Lean_Meta_introNCore(v_snd_649_, v___y_639_, v___x_650_, v___y_642_, v___y_632_, v___y_633_, v___y_643_, v___y_635_, v___y_641_);
if (lean_obj_tag(v___x_651_) == 0)
{
lean_object* v_a_652_; lean_object* v_fst_653_; lean_object* v_snd_654_; lean_object* v___x_655_; size_t v_sz_656_; size_t v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; 
v_a_652_ = lean_ctor_get(v___x_651_, 0);
lean_inc(v_a_652_);
lean_dec_ref_known(v___x_651_, 1);
v_fst_653_ = lean_ctor_get(v_a_652_, 0);
lean_inc(v_fst_653_);
v_snd_654_ = lean_ctor_get(v_a_652_, 1);
lean_inc(v_snd_654_);
lean_dec(v_a_652_);
lean_inc(v_baseSubst_559_);
lean_inc(v___y_630_);
v___x_655_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__2___redArg(v___y_631_, v_reverted_556_, v_fst_653_, v___y_630_, v___y_630_, v_baseSubst_559_);
lean_dec(v___y_630_);
lean_dec(v_fst_653_);
lean_dec(v___y_631_);
v_sz_656_ = lean_array_size(v_fst_648_);
v___x_657_ = ((size_t)0ULL);
v___x_658_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__3(v_sz_656_, v___x_657_, v_fst_648_);
v___x_659_ = lean_nat_add(v_pos_562_, v___y_636_);
lean_dec(v_pos_562_);
v___x_660_ = lean_nat_add(v_minorIdx_563_, v___y_636_);
lean_dec(v_minorIdx_563_);
v___x_661_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_661_, 0, v_snd_654_);
lean_ctor_set(v___x_661_, 1, v___x_658_);
lean_ctor_set(v___x_661_, 2, v___x_655_);
v___x_662_ = lean_array_push(v_subgoals_567_, v___x_661_);
v_pos_562_ = v___x_659_;
v_minorIdx_563_ = v___x_660_;
v_recursor_564_ = v___y_637_;
v_recursorType_565_ = v___y_634_;
v_subgoals_567_ = v___x_662_;
v_a_568_ = v___y_633_;
v_a_569_ = v___y_643_;
v_a_570_ = v___y_635_;
v_a_571_ = v___y_641_;
goto _start;
}
else
{
lean_object* v_a_664_; lean_object* v___x_666_; uint8_t v_isShared_667_; uint8_t v_isSharedCheck_671_; 
lean_dec(v_fst_648_);
lean_dec_ref(v___y_637_);
lean_dec_ref(v___y_634_);
lean_dec(v___y_631_);
lean_dec(v___y_630_);
lean_dec_ref(v_subgoals_567_);
lean_dec(v_minorIdx_563_);
lean_dec(v_pos_562_);
lean_dec(v_baseSubst_559_);
lean_dec_ref(v_major_557_);
lean_dec(v_mvarId_553_);
v_a_664_ = lean_ctor_get(v___x_651_, 0);
v_isSharedCheck_671_ = !lean_is_exclusive(v___x_651_);
if (v_isSharedCheck_671_ == 0)
{
v___x_666_ = v___x_651_;
v_isShared_667_ = v_isSharedCheck_671_;
goto v_resetjp_665_;
}
else
{
lean_inc(v_a_664_);
lean_dec(v___x_651_);
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
lean_object* v_a_672_; lean_object* v___x_674_; uint8_t v_isShared_675_; uint8_t v_isSharedCheck_679_; 
lean_dec(v___y_639_);
lean_dec_ref(v___y_637_);
lean_dec_ref(v___y_634_);
lean_dec(v___y_631_);
lean_dec(v___y_630_);
lean_dec_ref(v_subgoals_567_);
lean_dec(v_minorIdx_563_);
lean_dec(v_pos_562_);
lean_dec(v_baseSubst_559_);
lean_dec_ref(v_major_557_);
lean_dec(v_mvarId_553_);
v_a_672_ = lean_ctor_get(v___x_646_, 0);
v_isSharedCheck_679_ = !lean_is_exclusive(v___x_646_);
if (v_isSharedCheck_679_ == 0)
{
v___x_674_ = v___x_646_;
v_isShared_675_ = v_isSharedCheck_679_;
goto v_resetjp_673_;
}
else
{
lean_inc(v_a_672_);
lean_dec(v___x_646_);
v___x_674_ = lean_box(0);
v_isShared_675_ = v_isSharedCheck_679_;
goto v_resetjp_673_;
}
v_resetjp_673_:
{
lean_object* v___x_677_; 
if (v_isShared_675_ == 0)
{
v___x_677_ = v___x_674_;
goto v_reusejp_676_;
}
else
{
lean_object* v_reuseFailAlloc_678_; 
v_reuseFailAlloc_678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_678_, 0, v_a_672_);
v___x_677_ = v_reuseFailAlloc_678_;
goto v_reusejp_676_;
}
v_reusejp_676_:
{
return v___x_677_;
}
}
}
}
v___jp_680_:
{
lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; 
v___x_696_ = l_Lean_Expr_mvarId_x21(v___y_691_);
lean_dec_ref(v___y_691_);
v___x_697_ = l_Lean_Expr_fvarId_x21(v_major_557_);
v___x_698_ = l_Lean_MVarId_tryClear(v___x_696_, v___x_697_, v___y_692_, v___y_693_, v___y_694_, v___y_695_);
if (lean_obj_tag(v___x_698_) == 0)
{
uint8_t v_explicit_699_; 
v_explicit_699_ = lean_ctor_get_uint8(v___y_689_, sizeof(void*)*1);
if (v_explicit_699_ == 0)
{
lean_object* v_a_700_; lean_object* v_varNames_701_; 
v_a_700_ = lean_ctor_get(v___x_698_, 0);
lean_inc(v_a_700_);
lean_dec_ref_known(v___x_698_, 1);
v_varNames_701_ = lean_ctor_get(v___y_689_, 0);
lean_inc(v_varNames_701_);
lean_dec_ref(v___y_689_);
v___y_630_ = v___y_681_;
v___y_631_ = v___y_683_;
v___y_632_ = v___y_685_;
v___y_633_ = v___y_692_;
v___y_634_ = v___y_688_;
v___y_635_ = v___y_694_;
v___y_636_ = v___y_690_;
v___y_637_ = v___y_682_;
v___y_638_ = v_varNames_701_;
v___y_639_ = v___y_684_;
v___y_640_ = v___y_686_;
v___y_641_ = v___y_695_;
v___y_642_ = v___y_687_;
v___y_643_ = v___y_693_;
v___y_644_ = v_a_700_;
v___y_645_ = v___y_685_;
goto v___jp_629_;
}
else
{
lean_object* v_a_702_; lean_object* v_varNames_703_; 
v_a_702_ = lean_ctor_get(v___x_698_, 0);
lean_inc(v_a_702_);
lean_dec_ref_known(v___x_698_, 1);
v_varNames_703_ = lean_ctor_get(v___y_689_, 0);
lean_inc(v_varNames_703_);
lean_dec_ref(v___y_689_);
v___y_630_ = v___y_681_;
v___y_631_ = v___y_683_;
v___y_632_ = v___y_685_;
v___y_633_ = v___y_692_;
v___y_634_ = v___y_688_;
v___y_635_ = v___y_694_;
v___y_636_ = v___y_690_;
v___y_637_ = v___y_682_;
v___y_638_ = v_varNames_703_;
v___y_639_ = v___y_684_;
v___y_640_ = v___y_686_;
v___y_641_ = v___y_695_;
v___y_642_ = v___y_687_;
v___y_643_ = v___y_693_;
v___y_644_ = v_a_702_;
v___y_645_ = v___y_687_;
goto v___jp_629_;
}
}
else
{
lean_object* v_a_704_; lean_object* v___x_706_; uint8_t v_isShared_707_; uint8_t v_isSharedCheck_711_; 
lean_dec_ref(v___y_689_);
lean_dec_ref(v___y_688_);
lean_dec(v___y_686_);
lean_dec(v___y_684_);
lean_dec(v___y_683_);
lean_dec_ref(v___y_682_);
lean_dec(v___y_681_);
lean_dec_ref(v_subgoals_567_);
lean_dec(v_minorIdx_563_);
lean_dec(v_pos_562_);
lean_dec(v_baseSubst_559_);
lean_dec_ref(v_major_557_);
lean_dec(v_mvarId_553_);
v_a_704_ = lean_ctor_get(v___x_698_, 0);
v_isSharedCheck_711_ = !lean_is_exclusive(v___x_698_);
if (v_isSharedCheck_711_ == 0)
{
v___x_706_ = v___x_698_;
v_isShared_707_ = v_isSharedCheck_711_;
goto v_resetjp_705_;
}
else
{
lean_inc(v_a_704_);
lean_dec(v___x_698_);
v___x_706_ = lean_box(0);
v_isShared_707_ = v_isSharedCheck_711_;
goto v_resetjp_705_;
}
v_resetjp_705_:
{
lean_object* v___x_709_; 
if (v_isShared_707_ == 0)
{
v___x_709_ = v___x_706_;
goto v_reusejp_708_;
}
else
{
lean_object* v_reuseFailAlloc_710_; 
v_reuseFailAlloc_710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_710_, 0, v_a_704_);
v___x_709_ = v_reuseFailAlloc_710_;
goto v_reusejp_708_;
}
v_reusejp_708_:
{
return v___x_709_;
}
}
}
}
v___jp_712_:
{
lean_object* v___x_717_; 
lean_inc(v_mvarId_553_);
v___x_717_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTypeBody(v_mvarId_553_, v_snd_716_, v_major_557_, v_a_568_, v_a_569_, v_a_570_, v_a_571_);
if (lean_obj_tag(v___x_717_) == 0)
{
lean_object* v_a_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; 
v_a_718_ = lean_ctor_get(v___x_717_, 0);
lean_inc(v_a_718_);
lean_dec_ref_known(v___x_717_, 1);
lean_inc_ref(v_major_557_);
v___x_719_ = l_Lean_Expr_app___override(v_fst_715_, v_major_557_);
v___x_720_ = lean_unsigned_to_nat(1u);
v___x_721_ = lean_nat_add(v_pos_562_, v___x_720_);
lean_dec(v_pos_562_);
v___x_722_ = lean_nat_add(v___x_721_, v___y_714_);
lean_dec(v___y_714_);
lean_dec(v___x_721_);
v_pos_562_ = v___x_722_;
v_recursor_564_ = v___x_719_;
v_recursorType_565_ = v_a_718_;
v_consumedMajor_566_ = v___y_713_;
goto _start;
}
else
{
lean_object* v_a_724_; lean_object* v___x_726_; uint8_t v_isShared_727_; uint8_t v_isSharedCheck_731_; 
lean_dec_ref(v_fst_715_);
lean_dec(v___y_714_);
lean_dec_ref(v_subgoals_567_);
lean_dec(v_minorIdx_563_);
lean_dec(v_pos_562_);
lean_dec(v_baseSubst_559_);
lean_dec_ref(v_major_557_);
lean_dec(v_mvarId_553_);
v_a_724_ = lean_ctor_get(v___x_717_, 0);
v_isSharedCheck_731_ = !lean_is_exclusive(v___x_717_);
if (v_isSharedCheck_731_ == 0)
{
v___x_726_ = v___x_717_;
v_isShared_727_ = v_isSharedCheck_731_;
goto v_resetjp_725_;
}
else
{
lean_inc(v_a_724_);
lean_dec(v___x_717_);
v___x_726_ = lean_box(0);
v_isShared_727_ = v_isSharedCheck_731_;
goto v_resetjp_725_;
}
v_resetjp_725_:
{
lean_object* v___x_729_; 
if (v_isShared_727_ == 0)
{
v___x_729_ = v___x_726_;
goto v_reusejp_728_;
}
else
{
lean_object* v_reuseFailAlloc_730_; 
v_reuseFailAlloc_730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_730_, 0, v_a_724_);
v___x_729_ = v_reuseFailAlloc_730_;
goto v_reusejp_728_;
}
v_reusejp_728_:
{
return v___x_729_;
}
}
}
}
v___jp_732_:
{
if (lean_obj_tag(v___y_735_) == 0)
{
lean_object* v_a_736_; lean_object* v_fst_737_; lean_object* v_snd_738_; 
v_a_736_ = lean_ctor_get(v___y_735_, 0);
lean_inc(v_a_736_);
lean_dec_ref_known(v___y_735_, 1);
v_fst_737_ = lean_ctor_get(v_a_736_, 0);
lean_inc(v_fst_737_);
v_snd_738_ = lean_ctor_get(v_a_736_, 1);
lean_inc(v_snd_738_);
lean_dec(v_a_736_);
v___y_713_ = v___y_733_;
v___y_714_ = v___y_734_;
v_fst_715_ = v_fst_737_;
v_snd_716_ = v_snd_738_;
goto v___jp_712_;
}
else
{
lean_object* v_a_739_; lean_object* v___x_741_; uint8_t v_isShared_742_; uint8_t v_isSharedCheck_746_; 
lean_dec(v___y_734_);
lean_dec_ref(v_subgoals_567_);
lean_dec(v_minorIdx_563_);
lean_dec(v_pos_562_);
lean_dec(v_baseSubst_559_);
lean_dec_ref(v_major_557_);
lean_dec(v_mvarId_553_);
v_a_739_ = lean_ctor_get(v___y_735_, 0);
v_isSharedCheck_746_ = !lean_is_exclusive(v___y_735_);
if (v_isSharedCheck_746_ == 0)
{
v___x_741_ = v___y_735_;
v_isShared_742_ = v_isSharedCheck_746_;
goto v_resetjp_740_;
}
else
{
lean_inc(v_a_739_);
lean_dec(v___y_735_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___boxed(lean_object** _args){
lean_object* v_mvarId_993_ = _args[0];
lean_object* v_givenNames_994_ = _args[1];
lean_object* v_recursorInfo_995_ = _args[2];
lean_object* v_reverted_996_ = _args[3];
lean_object* v_major_997_ = _args[4];
lean_object* v_indices_998_ = _args[5];
lean_object* v_baseSubst_999_ = _args[6];
lean_object* v_initialArity_1000_ = _args[7];
lean_object* v_numMinors_1001_ = _args[8];
lean_object* v_pos_1002_ = _args[9];
lean_object* v_minorIdx_1003_ = _args[10];
lean_object* v_recursor_1004_ = _args[11];
lean_object* v_recursorType_1005_ = _args[12];
lean_object* v_consumedMajor_1006_ = _args[13];
lean_object* v_subgoals_1007_ = _args[14];
lean_object* v_a_1008_ = _args[15];
lean_object* v_a_1009_ = _args[16];
lean_object* v_a_1010_ = _args[17];
lean_object* v_a_1011_ = _args[18];
lean_object* v_a_1012_ = _args[19];
_start:
{
uint8_t v_consumedMajor_boxed_1013_; lean_object* v_res_1014_; 
v_consumedMajor_boxed_1013_ = lean_unbox(v_consumedMajor_1006_);
v_res_1014_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop(v_mvarId_993_, v_givenNames_994_, v_recursorInfo_995_, v_reverted_996_, v_major_997_, v_indices_998_, v_baseSubst_999_, v_initialArity_1000_, v_numMinors_1001_, v_pos_1002_, v_minorIdx_1003_, v_recursor_1004_, v_recursorType_1005_, v_consumedMajor_boxed_1013_, v_subgoals_1007_, v_a_1008_, v_a_1009_, v_a_1010_, v_a_1011_);
lean_dec(v_a_1011_);
lean_dec_ref(v_a_1010_);
lean_dec(v_a_1009_);
lean_dec_ref(v_a_1008_);
lean_dec(v_numMinors_1001_);
lean_dec(v_initialArity_1000_);
lean_dec_ref(v_indices_998_);
lean_dec_ref(v_reverted_996_);
lean_dec_ref(v_recursorInfo_995_);
lean_dec_ref(v_givenNames_994_);
return v_res_1014_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0(lean_object* v_mvarId_1015_, lean_object* v_val_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_){
_start:
{
lean_object* v___x_1022_; 
v___x_1022_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0___redArg(v_mvarId_1015_, v_val_1016_, v___y_1018_);
return v___x_1022_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0___boxed(lean_object* v_mvarId_1023_, lean_object* v_val_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_){
_start:
{
lean_object* v_res_1030_; 
v_res_1030_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0(v_mvarId_1023_, v_val_1024_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_);
lean_dec(v___y_1028_);
lean_dec_ref(v___y_1027_);
lean_dec(v___y_1026_);
lean_dec_ref(v___y_1025_);
return v_res_1030_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__2(lean_object* v___x_1031_, lean_object* v_reverted_1032_, lean_object* v_fst_1033_, lean_object* v_n_1034_, lean_object* v_j_1035_, lean_object* v_a_1036_, lean_object* v_a_1037_){
_start:
{
lean_object* v___x_1038_; 
v___x_1038_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__2___redArg(v___x_1031_, v_reverted_1032_, v_fst_1033_, v_n_1034_, v_j_1035_, v_a_1037_);
return v___x_1038_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__2___boxed(lean_object* v___x_1039_, lean_object* v_reverted_1040_, lean_object* v_fst_1041_, lean_object* v_n_1042_, lean_object* v_j_1043_, lean_object* v_a_1044_, lean_object* v_a_1045_){
_start:
{
lean_object* v_res_1046_; 
v_res_1046_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__2(v___x_1039_, v_reverted_1040_, v_fst_1041_, v_n_1042_, v_j_1043_, v_a_1044_, v_a_1045_);
lean_dec(v_n_1042_);
lean_dec_ref(v_fst_1041_);
lean_dec_ref(v_reverted_1040_);
lean_dec(v___x_1039_);
return v_res_1046_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0(lean_object* v_00_u03b2_1047_, lean_object* v_x_1048_, lean_object* v_x_1049_, lean_object* v_x_1050_){
_start:
{
lean_object* v___x_1051_; 
v___x_1051_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0___redArg(v_x_1048_, v_x_1049_, v_x_1050_);
return v___x_1051_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1052_, lean_object* v_x_1053_, size_t v_x_1054_, size_t v_x_1055_, lean_object* v_x_1056_, lean_object* v_x_1057_){
_start:
{
lean_object* v___x_1058_; 
v___x_1058_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2___redArg(v_x_1053_, v_x_1054_, v_x_1055_, v_x_1056_, v_x_1057_);
return v___x_1058_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1059_, lean_object* v_x_1060_, lean_object* v_x_1061_, lean_object* v_x_1062_, lean_object* v_x_1063_, lean_object* v_x_1064_){
_start:
{
size_t v_x_11479__boxed_1065_; size_t v_x_11480__boxed_1066_; lean_object* v_res_1067_; 
v_x_11479__boxed_1065_ = lean_unbox_usize(v_x_1061_);
lean_dec(v_x_1061_);
v_x_11480__boxed_1066_ = lean_unbox_usize(v_x_1062_);
lean_dec(v_x_1062_);
v_res_1067_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2(v_00_u03b2_1059_, v_x_1060_, v_x_11479__boxed_1065_, v_x_11480__boxed_1066_, v_x_1063_, v_x_1064_);
return v_res_1067_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__8(lean_object* v_00_u03b2_1068_, lean_object* v_n_1069_, lean_object* v_k_1070_, lean_object* v_v_1071_){
_start:
{
lean_object* v___x_1072_; 
v___x_1072_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__8___redArg(v_n_1069_, v_k_1070_, v_v_1071_);
return v___x_1072_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__9(lean_object* v_00_u03b2_1073_, size_t v_depth_1074_, lean_object* v_keys_1075_, lean_object* v_vals_1076_, lean_object* v_heq_1077_, lean_object* v_i_1078_, lean_object* v_entries_1079_){
_start:
{
lean_object* v___x_1080_; 
v___x_1080_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__9___redArg(v_depth_1074_, v_keys_1075_, v_vals_1076_, v_i_1078_, v_entries_1079_);
return v___x_1080_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__9___boxed(lean_object* v_00_u03b2_1081_, lean_object* v_depth_1082_, lean_object* v_keys_1083_, lean_object* v_vals_1084_, lean_object* v_heq_1085_, lean_object* v_i_1086_, lean_object* v_entries_1087_){
_start:
{
size_t v_depth_boxed_1088_; lean_object* v_res_1089_; 
v_depth_boxed_1088_ = lean_unbox_usize(v_depth_1082_);
lean_dec(v_depth_1082_);
v_res_1089_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__9(v_00_u03b2_1081_, v_depth_boxed_1088_, v_keys_1083_, v_vals_1084_, v_heq_1085_, v_i_1086_, v_entries_1087_);
lean_dec_ref(v_vals_1084_);
lean_dec_ref(v_keys_1083_);
return v_res_1089_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__8_spec__9(lean_object* v_00_u03b2_1090_, lean_object* v_x_1091_, lean_object* v_x_1092_, lean_object* v_x_1093_, lean_object* v_x_1094_){
_start:
{
lean_object* v___x_1095_; 
v___x_1095_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__8_spec__9___redArg(v_x_1091_, v_x_1092_, v_x_1093_, v_x_1094_);
return v___x_1095_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize(lean_object* v_mvarId_1098_, lean_object* v_givenNames_1099_, lean_object* v_recursorInfo_1100_, lean_object* v_reverted_1101_, lean_object* v_major_1102_, lean_object* v_indices_1103_, lean_object* v_baseSubst_1104_, lean_object* v_recursor_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_, lean_object* v_a_1109_){
_start:
{
lean_object* v___x_1111_; 
lean_inc(v_mvarId_1098_);
v___x_1111_ = l_Lean_MVarId_getType(v_mvarId_1098_, v_a_1106_, v_a_1107_, v_a_1108_, v_a_1109_);
if (lean_obj_tag(v___x_1111_) == 0)
{
lean_object* v_a_1112_; lean_object* v___x_1113_; 
v_a_1112_ = lean_ctor_get(v___x_1111_, 0);
lean_inc(v_a_1112_);
lean_dec_ref_known(v___x_1111_, 1);
lean_inc(v_a_1109_);
lean_inc_ref(v_a_1108_);
lean_inc(v_a_1107_);
lean_inc_ref(v_a_1106_);
lean_inc_ref(v_recursor_1105_);
v___x_1113_ = lean_infer_type(v_recursor_1105_, v_a_1106_, v_a_1107_, v_a_1108_, v_a_1109_);
if (lean_obj_tag(v___x_1113_) == 0)
{
lean_object* v_a_1114_; lean_object* v_paramsPos_1115_; lean_object* v_produceMotive_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; uint8_t v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; 
v_a_1114_ = lean_ctor_get(v___x_1113_, 0);
lean_inc(v_a_1114_);
lean_dec_ref_known(v___x_1113_, 1);
v_paramsPos_1115_ = lean_ctor_get(v_recursorInfo_1100_, 5);
v_produceMotive_1116_ = lean_ctor_get(v_recursorInfo_1100_, 7);
v___x_1117_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTargetArity(v_a_1112_);
v___x_1118_ = l_List_lengthTR___redArg(v_produceMotive_1116_);
v___x_1119_ = l_List_lengthTR___redArg(v_paramsPos_1115_);
v___x_1120_ = lean_unsigned_to_nat(1u);
v___x_1121_ = lean_nat_add(v___x_1119_, v___x_1120_);
lean_dec(v___x_1119_);
v___x_1122_ = lean_unsigned_to_nat(0u);
v___x_1123_ = 0;
v___x_1124_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize___closed__0));
v___x_1125_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop(v_mvarId_1098_, v_givenNames_1099_, v_recursorInfo_1100_, v_reverted_1101_, v_major_1102_, v_indices_1103_, v_baseSubst_1104_, v___x_1117_, v___x_1118_, v___x_1121_, v___x_1122_, v_recursor_1105_, v_a_1114_, v___x_1123_, v___x_1124_, v_a_1106_, v_a_1107_, v_a_1108_, v_a_1109_);
lean_dec(v___x_1118_);
lean_dec(v___x_1117_);
return v___x_1125_;
}
else
{
lean_object* v_a_1126_; lean_object* v___x_1128_; uint8_t v_isShared_1129_; uint8_t v_isSharedCheck_1133_; 
lean_dec(v_a_1112_);
lean_dec_ref(v_recursor_1105_);
lean_dec(v_baseSubst_1104_);
lean_dec_ref(v_major_1102_);
lean_dec(v_mvarId_1098_);
v_a_1126_ = lean_ctor_get(v___x_1113_, 0);
v_isSharedCheck_1133_ = !lean_is_exclusive(v___x_1113_);
if (v_isSharedCheck_1133_ == 0)
{
v___x_1128_ = v___x_1113_;
v_isShared_1129_ = v_isSharedCheck_1133_;
goto v_resetjp_1127_;
}
else
{
lean_inc(v_a_1126_);
lean_dec(v___x_1113_);
v___x_1128_ = lean_box(0);
v_isShared_1129_ = v_isSharedCheck_1133_;
goto v_resetjp_1127_;
}
v_resetjp_1127_:
{
lean_object* v___x_1131_; 
if (v_isShared_1129_ == 0)
{
v___x_1131_ = v___x_1128_;
goto v_reusejp_1130_;
}
else
{
lean_object* v_reuseFailAlloc_1132_; 
v_reuseFailAlloc_1132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1132_, 0, v_a_1126_);
v___x_1131_ = v_reuseFailAlloc_1132_;
goto v_reusejp_1130_;
}
v_reusejp_1130_:
{
return v___x_1131_;
}
}
}
}
else
{
lean_object* v_a_1134_; lean_object* v___x_1136_; uint8_t v_isShared_1137_; uint8_t v_isSharedCheck_1141_; 
lean_dec_ref(v_recursor_1105_);
lean_dec(v_baseSubst_1104_);
lean_dec_ref(v_major_1102_);
lean_dec(v_mvarId_1098_);
v_a_1134_ = lean_ctor_get(v___x_1111_, 0);
v_isSharedCheck_1141_ = !lean_is_exclusive(v___x_1111_);
if (v_isSharedCheck_1141_ == 0)
{
v___x_1136_ = v___x_1111_;
v_isShared_1137_ = v_isSharedCheck_1141_;
goto v_resetjp_1135_;
}
else
{
lean_inc(v_a_1134_);
lean_dec(v___x_1111_);
v___x_1136_ = lean_box(0);
v_isShared_1137_ = v_isSharedCheck_1141_;
goto v_resetjp_1135_;
}
v_resetjp_1135_:
{
lean_object* v___x_1139_; 
if (v_isShared_1137_ == 0)
{
v___x_1139_ = v___x_1136_;
goto v_reusejp_1138_;
}
else
{
lean_object* v_reuseFailAlloc_1140_; 
v_reuseFailAlloc_1140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1140_, 0, v_a_1134_);
v___x_1139_ = v_reuseFailAlloc_1140_;
goto v_reusejp_1138_;
}
v_reusejp_1138_:
{
return v___x_1139_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize___boxed(lean_object* v_mvarId_1142_, lean_object* v_givenNames_1143_, lean_object* v_recursorInfo_1144_, lean_object* v_reverted_1145_, lean_object* v_major_1146_, lean_object* v_indices_1147_, lean_object* v_baseSubst_1148_, lean_object* v_recursor_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_){
_start:
{
lean_object* v_res_1155_; 
v_res_1155_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize(v_mvarId_1142_, v_givenNames_1143_, v_recursorInfo_1144_, v_reverted_1145_, v_major_1146_, v_indices_1147_, v_baseSubst_1148_, v_recursor_1149_, v_a_1150_, v_a_1151_, v_a_1152_, v_a_1153_);
lean_dec(v_a_1153_);
lean_dec_ref(v_a_1152_);
lean_dec(v_a_1151_);
lean_dec_ref(v_a_1150_);
lean_dec_ref(v_indices_1147_);
lean_dec_ref(v_reverted_1145_);
lean_dec_ref(v_recursorInfo_1144_);
lean_dec_ref(v_givenNames_1143_);
return v_res_1155_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg___closed__1(void){
_start:
{
lean_object* v___x_1157_; lean_object* v___x_1158_; 
v___x_1157_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg___closed__0));
v___x_1158_ = l_Lean_stringToMessageData(v___x_1157_);
return v___x_1158_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg(lean_object* v_tacticName_1159_, lean_object* v_mvarId_1160_, lean_object* v_majorType_1161_, lean_object* v_a_1162_, lean_object* v_a_1163_, lean_object* v_a_1164_, lean_object* v_a_1165_){
_start:
{
lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; 
v___x_1167_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg___closed__1, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg___closed__1);
v___x_1168_ = l_Lean_indentExpr(v_majorType_1161_);
v___x_1169_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1169_, 0, v___x_1167_);
lean_ctor_set(v___x_1169_, 1, v___x_1168_);
v___x_1170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1170_, 0, v___x_1169_);
v___x_1171_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1159_, v_mvarId_1160_, v___x_1170_, v_a_1162_, v_a_1163_, v_a_1164_, v_a_1165_);
return v___x_1171_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg___boxed(lean_object* v_tacticName_1172_, lean_object* v_mvarId_1173_, lean_object* v_majorType_1174_, lean_object* v_a_1175_, lean_object* v_a_1176_, lean_object* v_a_1177_, lean_object* v_a_1178_, lean_object* v_a_1179_){
_start:
{
lean_object* v_res_1180_; 
v_res_1180_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg(v_tacticName_1172_, v_mvarId_1173_, v_majorType_1174_, v_a_1175_, v_a_1176_, v_a_1177_, v_a_1178_);
lean_dec(v_a_1178_);
lean_dec_ref(v_a_1177_);
lean_dec(v_a_1176_);
lean_dec_ref(v_a_1175_);
return v_res_1180_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType(lean_object* v_00_u03b1_1181_, lean_object* v_tacticName_1182_, lean_object* v_mvarId_1183_, lean_object* v_majorType_1184_, lean_object* v_a_1185_, lean_object* v_a_1186_, lean_object* v_a_1187_, lean_object* v_a_1188_){
_start:
{
lean_object* v___x_1190_; 
v___x_1190_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg(v_tacticName_1182_, v_mvarId_1183_, v_majorType_1184_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_);
return v___x_1190_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___boxed(lean_object* v_00_u03b1_1191_, lean_object* v_tacticName_1192_, lean_object* v_mvarId_1193_, lean_object* v_majorType_1194_, lean_object* v_a_1195_, lean_object* v_a_1196_, lean_object* v_a_1197_, lean_object* v_a_1198_, lean_object* v_a_1199_){
_start:
{
lean_object* v_res_1200_; 
v_res_1200_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType(v_00_u03b1_1191_, v_tacticName_1192_, v_mvarId_1193_, v_majorType_1194_, v_a_1195_, v_a_1196_, v_a_1197_, v_a_1198_);
lean_dec(v_a_1198_);
lean_dec_ref(v_a_1197_);
lean_dec(v_a_1196_);
lean_dec_ref(v_a_1195_);
return v_res_1200_;
}
}
LEAN_EXPORT uint8_t l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___lam__0(lean_object* v_fvarId_1201_, lean_object* v_x_1202_){
_start:
{
uint8_t v___x_1203_; 
v___x_1203_ = l_Lean_instBEqFVarId_beq(v_fvarId_1201_, v_x_1202_);
return v___x_1203_;
}
}
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___lam__0___boxed(lean_object* v_fvarId_1204_, lean_object* v_x_1205_){
_start:
{
uint8_t v_res_1206_; lean_object* v_r_1207_; 
v_res_1206_ = l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___lam__0(v_fvarId_1204_, v_x_1205_);
lean_dec(v_x_1205_);
lean_dec(v_fvarId_1204_);
v_r_1207_ = lean_box(v_res_1206_);
return v_r_1207_;
}
}
LEAN_EXPORT uint8_t l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___lam__1(lean_object* v_x_1208_){
_start:
{
uint8_t v___x_1209_; 
v___x_1209_ = 0;
return v___x_1209_;
}
}
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___lam__1___boxed(lean_object* v_x_1210_){
_start:
{
uint8_t v_res_1211_; lean_object* v_r_1212_; 
v_res_1211_ = l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___lam__1(v_x_1210_);
lean_dec(v_x_1210_);
v_r_1212_ = lean_box(v_res_1211_);
return v_r_1212_;
}
}
static lean_object* _init_l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; 
v___x_1214_ = lean_box(0);
v___x_1215_ = lean_unsigned_to_nat(16u);
v___x_1216_ = lean_mk_array(v___x_1215_, v___x_1214_);
return v___x_1216_;
}
}
static lean_object* _init_l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; 
v___x_1217_ = lean_obj_once(&l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__1, &l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__1_once, _init_l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__1);
v___x_1218_ = lean_unsigned_to_nat(0u);
v___x_1219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1219_, 0, v___x_1218_);
lean_ctor_set(v___x_1219_, 1, v___x_1217_);
return v___x_1219_;
}
}
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg(lean_object* v_localDecl_1220_, lean_object* v_fvarId_1221_, uint8_t v_generalizeNondepLet_1222_, lean_object* v___y_1223_){
_start:
{
uint8_t v_fst_1226_; lean_object* v_snd_1227_; lean_object* v___y_1246_; lean_object* v___f_1250_; lean_object* v___f_1251_; 
v___f_1250_ = lean_alloc_closure((void*)(l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1250_, 0, v_fvarId_1221_);
v___f_1251_ = ((lean_object*)(l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__0));
if (lean_obj_tag(v_localDecl_1220_) == 0)
{
lean_object* v_type_1252_; lean_object* v___x_1253_; uint8_t v_fst_1255_; lean_object* v_mctx_1256_; lean_object* v___y_1274_; lean_object* v_mctx_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; uint8_t v___x_1282_; 
v_type_1252_ = lean_ctor_get(v_localDecl_1220_, 3);
lean_inc_ref(v_type_1252_);
lean_dec_ref_known(v_localDecl_1220_, 4);
v___x_1253_ = lean_st_ref_get(v___y_1223_);
v_mctx_1279_ = lean_ctor_get(v___x_1253_, 0);
lean_inc_ref_n(v_mctx_1279_, 2);
lean_dec(v___x_1253_);
v___x_1280_ = lean_obj_once(&l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__2, &l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__2_once, _init_l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__2);
v___x_1281_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1281_, 0, v___x_1280_);
lean_ctor_set(v___x_1281_, 1, v_mctx_1279_);
v___x_1282_ = l_Lean_Expr_hasFVar(v_type_1252_);
if (v___x_1282_ == 0)
{
uint8_t v___x_1283_; 
v___x_1283_ = l_Lean_Expr_hasMVar(v_type_1252_);
if (v___x_1283_ == 0)
{
lean_dec_ref_known(v___x_1281_, 2);
lean_dec_ref(v_type_1252_);
lean_dec_ref(v___f_1250_);
v_fst_1255_ = v___x_1283_;
v_mctx_1256_ = v_mctx_1279_;
goto v___jp_1254_;
}
else
{
lean_object* v___x_1284_; 
lean_dec_ref(v_mctx_1279_);
v___x_1284_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1250_, v___f_1251_, v_type_1252_, v___x_1281_);
v___y_1274_ = v___x_1284_;
goto v___jp_1273_;
}
}
else
{
lean_object* v___x_1285_; 
lean_dec_ref(v_mctx_1279_);
v___x_1285_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1250_, v___f_1251_, v_type_1252_, v___x_1281_);
v___y_1274_ = v___x_1285_;
goto v___jp_1273_;
}
v___jp_1254_:
{
lean_object* v___x_1257_; lean_object* v_cache_1258_; lean_object* v_zetaDeltaFVarIds_1259_; lean_object* v_postponed_1260_; lean_object* v_diag_1261_; lean_object* v___x_1263_; uint8_t v_isShared_1264_; uint8_t v_isSharedCheck_1271_; 
v___x_1257_ = lean_st_ref_take(v___y_1223_);
v_cache_1258_ = lean_ctor_get(v___x_1257_, 1);
v_zetaDeltaFVarIds_1259_ = lean_ctor_get(v___x_1257_, 2);
v_postponed_1260_ = lean_ctor_get(v___x_1257_, 3);
v_diag_1261_ = lean_ctor_get(v___x_1257_, 4);
v_isSharedCheck_1271_ = !lean_is_exclusive(v___x_1257_);
if (v_isSharedCheck_1271_ == 0)
{
lean_object* v_unused_1272_; 
v_unused_1272_ = lean_ctor_get(v___x_1257_, 0);
lean_dec(v_unused_1272_);
v___x_1263_ = v___x_1257_;
v_isShared_1264_ = v_isSharedCheck_1271_;
goto v_resetjp_1262_;
}
else
{
lean_inc(v_diag_1261_);
lean_inc(v_postponed_1260_);
lean_inc(v_zetaDeltaFVarIds_1259_);
lean_inc(v_cache_1258_);
lean_dec(v___x_1257_);
v___x_1263_ = lean_box(0);
v_isShared_1264_ = v_isSharedCheck_1271_;
goto v_resetjp_1262_;
}
v_resetjp_1262_:
{
lean_object* v___x_1266_; 
if (v_isShared_1264_ == 0)
{
lean_ctor_set(v___x_1263_, 0, v_mctx_1256_);
v___x_1266_ = v___x_1263_;
goto v_reusejp_1265_;
}
else
{
lean_object* v_reuseFailAlloc_1270_; 
v_reuseFailAlloc_1270_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1270_, 0, v_mctx_1256_);
lean_ctor_set(v_reuseFailAlloc_1270_, 1, v_cache_1258_);
lean_ctor_set(v_reuseFailAlloc_1270_, 2, v_zetaDeltaFVarIds_1259_);
lean_ctor_set(v_reuseFailAlloc_1270_, 3, v_postponed_1260_);
lean_ctor_set(v_reuseFailAlloc_1270_, 4, v_diag_1261_);
v___x_1266_ = v_reuseFailAlloc_1270_;
goto v_reusejp_1265_;
}
v_reusejp_1265_:
{
lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; 
v___x_1267_ = lean_st_ref_set(v___y_1223_, v___x_1266_);
v___x_1268_ = lean_box(v_fst_1255_);
v___x_1269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1269_, 0, v___x_1268_);
return v___x_1269_;
}
}
}
v___jp_1273_:
{
lean_object* v_snd_1275_; lean_object* v_fst_1276_; lean_object* v_mctx_1277_; uint8_t v___x_1278_; 
v_snd_1275_ = lean_ctor_get(v___y_1274_, 1);
lean_inc(v_snd_1275_);
v_fst_1276_ = lean_ctor_get(v___y_1274_, 0);
lean_inc(v_fst_1276_);
lean_dec_ref(v___y_1274_);
v_mctx_1277_ = lean_ctor_get(v_snd_1275_, 1);
lean_inc_ref(v_mctx_1277_);
lean_dec(v_snd_1275_);
v___x_1278_ = lean_unbox(v_fst_1276_);
lean_dec(v_fst_1276_);
v_fst_1255_ = v___x_1278_;
v_mctx_1256_ = v_mctx_1277_;
goto v___jp_1254_;
}
}
else
{
lean_object* v_type_1286_; lean_object* v_value_1287_; uint8_t v_nondep_1288_; uint8_t v_fst_1290_; lean_object* v_snd_1291_; lean_object* v___y_1297_; 
v_type_1286_ = lean_ctor_get(v_localDecl_1220_, 3);
lean_inc_ref(v_type_1286_);
v_value_1287_ = lean_ctor_get(v_localDecl_1220_, 4);
lean_inc_ref(v_value_1287_);
v_nondep_1288_ = lean_ctor_get_uint8(v_localDecl_1220_, sizeof(void*)*5);
lean_dec_ref_known(v_localDecl_1220_, 5);
if (v_generalizeNondepLet_1222_ == 0)
{
goto v___jp_1301_;
}
else
{
if (v_nondep_1288_ == 0)
{
goto v___jp_1301_;
}
else
{
lean_object* v___x_1310_; uint8_t v_fst_1312_; lean_object* v_mctx_1313_; lean_object* v___y_1331_; lean_object* v_mctx_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; uint8_t v___x_1339_; 
lean_dec_ref(v_value_1287_);
v___x_1310_ = lean_st_ref_get(v___y_1223_);
v_mctx_1336_ = lean_ctor_get(v___x_1310_, 0);
lean_inc_ref_n(v_mctx_1336_, 2);
lean_dec(v___x_1310_);
v___x_1337_ = lean_obj_once(&l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__2, &l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__2_once, _init_l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__2);
v___x_1338_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1338_, 0, v___x_1337_);
lean_ctor_set(v___x_1338_, 1, v_mctx_1336_);
v___x_1339_ = l_Lean_Expr_hasFVar(v_type_1286_);
if (v___x_1339_ == 0)
{
uint8_t v___x_1340_; 
v___x_1340_ = l_Lean_Expr_hasMVar(v_type_1286_);
if (v___x_1340_ == 0)
{
lean_dec_ref_known(v___x_1338_, 2);
lean_dec_ref(v_type_1286_);
lean_dec_ref(v___f_1250_);
v_fst_1312_ = v___x_1340_;
v_mctx_1313_ = v_mctx_1336_;
goto v___jp_1311_;
}
else
{
lean_object* v___x_1341_; 
lean_dec_ref(v_mctx_1336_);
v___x_1341_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1250_, v___f_1251_, v_type_1286_, v___x_1338_);
v___y_1331_ = v___x_1341_;
goto v___jp_1330_;
}
}
else
{
lean_object* v___x_1342_; 
lean_dec_ref(v_mctx_1336_);
v___x_1342_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1250_, v___f_1251_, v_type_1286_, v___x_1338_);
v___y_1331_ = v___x_1342_;
goto v___jp_1330_;
}
v___jp_1311_:
{
lean_object* v___x_1314_; lean_object* v_cache_1315_; lean_object* v_zetaDeltaFVarIds_1316_; lean_object* v_postponed_1317_; lean_object* v_diag_1318_; lean_object* v___x_1320_; uint8_t v_isShared_1321_; uint8_t v_isSharedCheck_1328_; 
v___x_1314_ = lean_st_ref_take(v___y_1223_);
v_cache_1315_ = lean_ctor_get(v___x_1314_, 1);
v_zetaDeltaFVarIds_1316_ = lean_ctor_get(v___x_1314_, 2);
v_postponed_1317_ = lean_ctor_get(v___x_1314_, 3);
v_diag_1318_ = lean_ctor_get(v___x_1314_, 4);
v_isSharedCheck_1328_ = !lean_is_exclusive(v___x_1314_);
if (v_isSharedCheck_1328_ == 0)
{
lean_object* v_unused_1329_; 
v_unused_1329_ = lean_ctor_get(v___x_1314_, 0);
lean_dec(v_unused_1329_);
v___x_1320_ = v___x_1314_;
v_isShared_1321_ = v_isSharedCheck_1328_;
goto v_resetjp_1319_;
}
else
{
lean_inc(v_diag_1318_);
lean_inc(v_postponed_1317_);
lean_inc(v_zetaDeltaFVarIds_1316_);
lean_inc(v_cache_1315_);
lean_dec(v___x_1314_);
v___x_1320_ = lean_box(0);
v_isShared_1321_ = v_isSharedCheck_1328_;
goto v_resetjp_1319_;
}
v_resetjp_1319_:
{
lean_object* v___x_1323_; 
if (v_isShared_1321_ == 0)
{
lean_ctor_set(v___x_1320_, 0, v_mctx_1313_);
v___x_1323_ = v___x_1320_;
goto v_reusejp_1322_;
}
else
{
lean_object* v_reuseFailAlloc_1327_; 
v_reuseFailAlloc_1327_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1327_, 0, v_mctx_1313_);
lean_ctor_set(v_reuseFailAlloc_1327_, 1, v_cache_1315_);
lean_ctor_set(v_reuseFailAlloc_1327_, 2, v_zetaDeltaFVarIds_1316_);
lean_ctor_set(v_reuseFailAlloc_1327_, 3, v_postponed_1317_);
lean_ctor_set(v_reuseFailAlloc_1327_, 4, v_diag_1318_);
v___x_1323_ = v_reuseFailAlloc_1327_;
goto v_reusejp_1322_;
}
v_reusejp_1322_:
{
lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; 
v___x_1324_ = lean_st_ref_set(v___y_1223_, v___x_1323_);
v___x_1325_ = lean_box(v_fst_1312_);
v___x_1326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1326_, 0, v___x_1325_);
return v___x_1326_;
}
}
}
v___jp_1330_:
{
lean_object* v_snd_1332_; lean_object* v_fst_1333_; lean_object* v_mctx_1334_; uint8_t v___x_1335_; 
v_snd_1332_ = lean_ctor_get(v___y_1331_, 1);
lean_inc(v_snd_1332_);
v_fst_1333_ = lean_ctor_get(v___y_1331_, 0);
lean_inc(v_fst_1333_);
lean_dec_ref(v___y_1331_);
v_mctx_1334_ = lean_ctor_get(v_snd_1332_, 1);
lean_inc_ref(v_mctx_1334_);
lean_dec(v_snd_1332_);
v___x_1335_ = lean_unbox(v_fst_1333_);
lean_dec(v_fst_1333_);
v_fst_1312_ = v___x_1335_;
v_mctx_1313_ = v_mctx_1334_;
goto v___jp_1311_;
}
}
}
v___jp_1289_:
{
if (v_fst_1290_ == 0)
{
uint8_t v___x_1292_; 
v___x_1292_ = l_Lean_Expr_hasFVar(v_value_1287_);
if (v___x_1292_ == 0)
{
uint8_t v___x_1293_; 
v___x_1293_ = l_Lean_Expr_hasMVar(v_value_1287_);
if (v___x_1293_ == 0)
{
lean_dec_ref(v_value_1287_);
lean_dec_ref(v___f_1250_);
v_fst_1226_ = v___x_1293_;
v_snd_1227_ = v_snd_1291_;
goto v___jp_1225_;
}
else
{
lean_object* v___x_1294_; 
v___x_1294_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1250_, v___f_1251_, v_value_1287_, v_snd_1291_);
v___y_1246_ = v___x_1294_;
goto v___jp_1245_;
}
}
else
{
lean_object* v___x_1295_; 
v___x_1295_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1250_, v___f_1251_, v_value_1287_, v_snd_1291_);
v___y_1246_ = v___x_1295_;
goto v___jp_1245_;
}
}
else
{
lean_dec_ref(v_value_1287_);
lean_dec_ref(v___f_1250_);
v_fst_1226_ = v_fst_1290_;
v_snd_1227_ = v_snd_1291_;
goto v___jp_1225_;
}
}
v___jp_1296_:
{
lean_object* v_fst_1298_; lean_object* v_snd_1299_; uint8_t v___x_1300_; 
v_fst_1298_ = lean_ctor_get(v___y_1297_, 0);
lean_inc(v_fst_1298_);
v_snd_1299_ = lean_ctor_get(v___y_1297_, 1);
lean_inc(v_snd_1299_);
lean_dec_ref(v___y_1297_);
v___x_1300_ = lean_unbox(v_fst_1298_);
lean_dec(v_fst_1298_);
v_fst_1290_ = v___x_1300_;
v_snd_1291_ = v_snd_1299_;
goto v___jp_1289_;
}
v___jp_1301_:
{
lean_object* v___x_1302_; lean_object* v_mctx_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; uint8_t v___x_1306_; 
v___x_1302_ = lean_st_ref_get(v___y_1223_);
v_mctx_1303_ = lean_ctor_get(v___x_1302_, 0);
lean_inc_ref(v_mctx_1303_);
lean_dec(v___x_1302_);
v___x_1304_ = lean_obj_once(&l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__2, &l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__2_once, _init_l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__2);
v___x_1305_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1305_, 0, v___x_1304_);
lean_ctor_set(v___x_1305_, 1, v_mctx_1303_);
v___x_1306_ = l_Lean_Expr_hasFVar(v_type_1286_);
if (v___x_1306_ == 0)
{
uint8_t v___x_1307_; 
v___x_1307_ = l_Lean_Expr_hasMVar(v_type_1286_);
if (v___x_1307_ == 0)
{
lean_dec_ref(v_type_1286_);
v_fst_1290_ = v___x_1307_;
v_snd_1291_ = v___x_1305_;
goto v___jp_1289_;
}
else
{
lean_object* v___x_1308_; 
lean_inc_ref(v___f_1250_);
v___x_1308_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1250_, v___f_1251_, v_type_1286_, v___x_1305_);
v___y_1297_ = v___x_1308_;
goto v___jp_1296_;
}
}
else
{
lean_object* v___x_1309_; 
lean_inc_ref(v___f_1250_);
v___x_1309_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1250_, v___f_1251_, v_type_1286_, v___x_1305_);
v___y_1297_ = v___x_1309_;
goto v___jp_1296_;
}
}
}
v___jp_1225_:
{
lean_object* v_mctx_1228_; lean_object* v___x_1229_; lean_object* v_cache_1230_; lean_object* v_zetaDeltaFVarIds_1231_; lean_object* v_postponed_1232_; lean_object* v_diag_1233_; lean_object* v___x_1235_; uint8_t v_isShared_1236_; uint8_t v_isSharedCheck_1243_; 
v_mctx_1228_ = lean_ctor_get(v_snd_1227_, 1);
lean_inc_ref(v_mctx_1228_);
lean_dec_ref(v_snd_1227_);
v___x_1229_ = lean_st_ref_take(v___y_1223_);
v_cache_1230_ = lean_ctor_get(v___x_1229_, 1);
v_zetaDeltaFVarIds_1231_ = lean_ctor_get(v___x_1229_, 2);
v_postponed_1232_ = lean_ctor_get(v___x_1229_, 3);
v_diag_1233_ = lean_ctor_get(v___x_1229_, 4);
v_isSharedCheck_1243_ = !lean_is_exclusive(v___x_1229_);
if (v_isSharedCheck_1243_ == 0)
{
lean_object* v_unused_1244_; 
v_unused_1244_ = lean_ctor_get(v___x_1229_, 0);
lean_dec(v_unused_1244_);
v___x_1235_ = v___x_1229_;
v_isShared_1236_ = v_isSharedCheck_1243_;
goto v_resetjp_1234_;
}
else
{
lean_inc(v_diag_1233_);
lean_inc(v_postponed_1232_);
lean_inc(v_zetaDeltaFVarIds_1231_);
lean_inc(v_cache_1230_);
lean_dec(v___x_1229_);
v___x_1235_ = lean_box(0);
v_isShared_1236_ = v_isSharedCheck_1243_;
goto v_resetjp_1234_;
}
v_resetjp_1234_:
{
lean_object* v___x_1238_; 
if (v_isShared_1236_ == 0)
{
lean_ctor_set(v___x_1235_, 0, v_mctx_1228_);
v___x_1238_ = v___x_1235_;
goto v_reusejp_1237_;
}
else
{
lean_object* v_reuseFailAlloc_1242_; 
v_reuseFailAlloc_1242_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1242_, 0, v_mctx_1228_);
lean_ctor_set(v_reuseFailAlloc_1242_, 1, v_cache_1230_);
lean_ctor_set(v_reuseFailAlloc_1242_, 2, v_zetaDeltaFVarIds_1231_);
lean_ctor_set(v_reuseFailAlloc_1242_, 3, v_postponed_1232_);
lean_ctor_set(v_reuseFailAlloc_1242_, 4, v_diag_1233_);
v___x_1238_ = v_reuseFailAlloc_1242_;
goto v_reusejp_1237_;
}
v_reusejp_1237_:
{
lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; 
v___x_1239_ = lean_st_ref_set(v___y_1223_, v___x_1238_);
v___x_1240_ = lean_box(v_fst_1226_);
v___x_1241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1241_, 0, v___x_1240_);
return v___x_1241_;
}
}
}
v___jp_1245_:
{
lean_object* v_fst_1247_; lean_object* v_snd_1248_; uint8_t v___x_1249_; 
v_fst_1247_ = lean_ctor_get(v___y_1246_, 0);
lean_inc(v_fst_1247_);
v_snd_1248_ = lean_ctor_get(v___y_1246_, 1);
lean_inc(v_snd_1248_);
lean_dec_ref(v___y_1246_);
v___x_1249_ = lean_unbox(v_fst_1247_);
lean_dec(v_fst_1247_);
v_fst_1226_ = v___x_1249_;
v_snd_1227_ = v_snd_1248_;
goto v___jp_1225_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___boxed(lean_object* v_localDecl_1343_, lean_object* v_fvarId_1344_, lean_object* v_generalizeNondepLet_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_){
_start:
{
uint8_t v_generalizeNondepLet_boxed_1348_; lean_object* v_res_1349_; 
v_generalizeNondepLet_boxed_1348_ = lean_unbox(v_generalizeNondepLet_1345_);
v_res_1349_ = l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg(v_localDecl_1343_, v_fvarId_1344_, v_generalizeNondepLet_boxed_1348_, v___y_1346_);
lean_dec(v___y_1346_);
return v_res_1349_;
}
}
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0(lean_object* v_localDecl_1350_, lean_object* v_fvarId_1351_, uint8_t v_generalizeNondepLet_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_){
_start:
{
lean_object* v___x_1358_; 
v___x_1358_ = l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg(v_localDecl_1350_, v_fvarId_1351_, v_generalizeNondepLet_1352_, v___y_1354_);
return v___x_1358_;
}
}
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___boxed(lean_object* v_localDecl_1359_, lean_object* v_fvarId_1360_, lean_object* v_generalizeNondepLet_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_){
_start:
{
uint8_t v_generalizeNondepLet_boxed_1367_; lean_object* v_res_1368_; 
v_generalizeNondepLet_boxed_1367_ = lean_unbox(v_generalizeNondepLet_1361_);
v_res_1368_ = l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0(v_localDecl_1359_, v_fvarId_1360_, v_generalizeNondepLet_boxed_1367_, v___y_1362_, v___y_1363_, v___y_1364_, v___y_1365_);
lean_dec(v___y_1365_);
lean_dec_ref(v___y_1364_);
lean_dec(v___y_1363_);
lean_dec_ref(v___y_1362_);
return v_res_1368_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2___redArg(lean_object* v_e_1369_, lean_object* v_fvarId_1370_, lean_object* v___y_1371_){
_start:
{
lean_object* v___x_1373_; uint8_t v_fst_1375_; lean_object* v_mctx_1376_; lean_object* v___y_1394_; lean_object* v_mctx_1399_; lean_object* v___f_1400_; lean_object* v___f_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; uint8_t v___x_1404_; 
v___x_1373_ = lean_st_ref_get(v___y_1371_);
v_mctx_1399_ = lean_ctor_get(v___x_1373_, 0);
lean_inc_ref_n(v_mctx_1399_, 2);
lean_dec(v___x_1373_);
v___f_1400_ = ((lean_object*)(l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__0));
v___f_1401_ = lean_alloc_closure((void*)(l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1401_, 0, v_fvarId_1370_);
v___x_1402_ = lean_obj_once(&l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__2, &l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__2_once, _init_l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__2);
v___x_1403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1403_, 0, v___x_1402_);
lean_ctor_set(v___x_1403_, 1, v_mctx_1399_);
v___x_1404_ = l_Lean_Expr_hasFVar(v_e_1369_);
if (v___x_1404_ == 0)
{
uint8_t v___x_1405_; 
v___x_1405_ = l_Lean_Expr_hasMVar(v_e_1369_);
if (v___x_1405_ == 0)
{
lean_dec_ref_known(v___x_1403_, 2);
lean_dec_ref(v___f_1401_);
lean_dec_ref(v_e_1369_);
v_fst_1375_ = v___x_1405_;
v_mctx_1376_ = v_mctx_1399_;
goto v___jp_1374_;
}
else
{
lean_object* v___x_1406_; 
lean_dec_ref(v_mctx_1399_);
v___x_1406_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1401_, v___f_1400_, v_e_1369_, v___x_1403_);
v___y_1394_ = v___x_1406_;
goto v___jp_1393_;
}
}
else
{
lean_object* v___x_1407_; 
lean_dec_ref(v_mctx_1399_);
v___x_1407_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1401_, v___f_1400_, v_e_1369_, v___x_1403_);
v___y_1394_ = v___x_1407_;
goto v___jp_1393_;
}
v___jp_1374_:
{
lean_object* v___x_1377_; lean_object* v_cache_1378_; lean_object* v_zetaDeltaFVarIds_1379_; lean_object* v_postponed_1380_; lean_object* v_diag_1381_; lean_object* v___x_1383_; uint8_t v_isShared_1384_; uint8_t v_isSharedCheck_1391_; 
v___x_1377_ = lean_st_ref_take(v___y_1371_);
v_cache_1378_ = lean_ctor_get(v___x_1377_, 1);
v_zetaDeltaFVarIds_1379_ = lean_ctor_get(v___x_1377_, 2);
v_postponed_1380_ = lean_ctor_get(v___x_1377_, 3);
v_diag_1381_ = lean_ctor_get(v___x_1377_, 4);
v_isSharedCheck_1391_ = !lean_is_exclusive(v___x_1377_);
if (v_isSharedCheck_1391_ == 0)
{
lean_object* v_unused_1392_; 
v_unused_1392_ = lean_ctor_get(v___x_1377_, 0);
lean_dec(v_unused_1392_);
v___x_1383_ = v___x_1377_;
v_isShared_1384_ = v_isSharedCheck_1391_;
goto v_resetjp_1382_;
}
else
{
lean_inc(v_diag_1381_);
lean_inc(v_postponed_1380_);
lean_inc(v_zetaDeltaFVarIds_1379_);
lean_inc(v_cache_1378_);
lean_dec(v___x_1377_);
v___x_1383_ = lean_box(0);
v_isShared_1384_ = v_isSharedCheck_1391_;
goto v_resetjp_1382_;
}
v_resetjp_1382_:
{
lean_object* v___x_1386_; 
if (v_isShared_1384_ == 0)
{
lean_ctor_set(v___x_1383_, 0, v_mctx_1376_);
v___x_1386_ = v___x_1383_;
goto v_reusejp_1385_;
}
else
{
lean_object* v_reuseFailAlloc_1390_; 
v_reuseFailAlloc_1390_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1390_, 0, v_mctx_1376_);
lean_ctor_set(v_reuseFailAlloc_1390_, 1, v_cache_1378_);
lean_ctor_set(v_reuseFailAlloc_1390_, 2, v_zetaDeltaFVarIds_1379_);
lean_ctor_set(v_reuseFailAlloc_1390_, 3, v_postponed_1380_);
lean_ctor_set(v_reuseFailAlloc_1390_, 4, v_diag_1381_);
v___x_1386_ = v_reuseFailAlloc_1390_;
goto v_reusejp_1385_;
}
v_reusejp_1385_:
{
lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; 
v___x_1387_ = lean_st_ref_set(v___y_1371_, v___x_1386_);
v___x_1388_ = lean_box(v_fst_1375_);
v___x_1389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1389_, 0, v___x_1388_);
return v___x_1389_;
}
}
}
v___jp_1393_:
{
lean_object* v_snd_1395_; lean_object* v_fst_1396_; lean_object* v_mctx_1397_; uint8_t v___x_1398_; 
v_snd_1395_ = lean_ctor_get(v___y_1394_, 1);
lean_inc(v_snd_1395_);
v_fst_1396_ = lean_ctor_get(v___y_1394_, 0);
lean_inc(v_fst_1396_);
lean_dec_ref(v___y_1394_);
v_mctx_1397_ = lean_ctor_get(v_snd_1395_, 1);
lean_inc_ref(v_mctx_1397_);
lean_dec(v_snd_1395_);
v___x_1398_ = lean_unbox(v_fst_1396_);
lean_dec(v_fst_1396_);
v_fst_1375_ = v___x_1398_;
v_mctx_1376_ = v_mctx_1397_;
goto v___jp_1374_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2___redArg___boxed(lean_object* v_e_1408_, lean_object* v_fvarId_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_){
_start:
{
lean_object* v_res_1412_; 
v_res_1412_ = l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2___redArg(v_e_1408_, v_fvarId_1409_, v___y_1410_);
lean_dec(v___y_1410_);
return v_res_1412_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2(lean_object* v_e_1413_, lean_object* v_fvarId_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_){
_start:
{
lean_object* v___x_1420_; 
v___x_1420_ = l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2___redArg(v_e_1413_, v_fvarId_1414_, v___y_1416_);
return v___x_1420_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2___boxed(lean_object* v_e_1421_, lean_object* v_fvarId_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_){
_start:
{
lean_object* v_res_1428_; 
v_res_1428_ = l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2(v_e_1421_, v_fvarId_1422_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1426_);
lean_dec(v___y_1426_);
lean_dec_ref(v___y_1425_);
lean_dec(v___y_1424_);
lean_dec_ref(v___y_1423_);
return v_res_1428_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_Meta_getMajorTypeIndices_spec__1(lean_object* v_a_1429_, lean_object* v_x_1430_){
_start:
{
if (lean_obj_tag(v_x_1430_) == 0)
{
uint8_t v___x_1431_; 
v___x_1431_ = 0;
return v___x_1431_;
}
else
{
lean_object* v_head_1432_; lean_object* v_tail_1433_; uint8_t v___x_1434_; 
v_head_1432_ = lean_ctor_get(v_x_1430_, 0);
v_tail_1433_ = lean_ctor_get(v_x_1430_, 1);
v___x_1434_ = lean_nat_dec_eq(v_a_1429_, v_head_1432_);
if (v___x_1434_ == 0)
{
v_x_1430_ = v_tail_1433_;
goto _start;
}
else
{
return v___x_1434_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_Meta_getMajorTypeIndices_spec__1___boxed(lean_object* v_a_1436_, lean_object* v_x_1437_){
_start:
{
uint8_t v_res_1438_; lean_object* v_r_1439_; 
v_res_1438_ = l_List_elem___at___00Lean_Meta_getMajorTypeIndices_spec__1(v_a_1436_, v_x_1437_);
lean_dec(v_x_1437_);
lean_dec(v_a_1436_);
v_r_1439_ = lean_box(v_res_1438_);
return v_r_1439_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_1441_; lean_object* v___x_1442_; 
v___x_1441_ = ((lean_object*)(l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__0));
v___x_1442_ = l_Lean_stringToMessageData(v___x_1441_);
return v___x_1442_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_1444_; lean_object* v___x_1445_; 
v___x_1444_ = ((lean_object*)(l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__2));
v___x_1445_ = l_Lean_stringToMessageData(v___x_1444_);
return v___x_1445_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__5(void){
_start:
{
lean_object* v___x_1447_; lean_object* v___x_1448_; 
v___x_1447_ = ((lean_object*)(l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__4));
v___x_1448_ = l_Lean_stringToMessageData(v___x_1447_);
return v___x_1448_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__7(void){
_start:
{
lean_object* v___x_1450_; lean_object* v___x_1451_; 
v___x_1450_ = ((lean_object*)(l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__6));
v___x_1451_ = l_Lean_stringToMessageData(v___x_1450_);
return v___x_1451_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg(lean_object* v_majorTypeArgs_1452_, lean_object* v_idx_1453_, lean_object* v_tacticName_1454_, lean_object* v_mvarId_1455_, lean_object* v_idxPos_1456_, lean_object* v_recursorInfo_1457_, lean_object* v_majorType_1458_, lean_object* v_n_1459_, lean_object* v_i_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_){
_start:
{
lean_object* v_zero_1466_; uint8_t v_isZero_1467_; 
v_zero_1466_ = lean_unsigned_to_nat(0u);
v_isZero_1467_ = lean_nat_dec_eq(v_i_1460_, v_zero_1466_);
if (v_isZero_1467_ == 1)
{
lean_object* v___x_1468_; lean_object* v___x_1469_; 
lean_dec(v_i_1460_);
lean_dec_ref(v_majorType_1458_);
lean_dec(v_mvarId_1455_);
lean_dec(v_tacticName_1454_);
lean_dec_ref(v_idx_1453_);
v___x_1468_ = lean_box(0);
v___x_1469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1469_, 0, v___x_1468_);
return v___x_1469_;
}
else
{
lean_object* v_one_1470_; lean_object* v_n_1471_; lean_object* v___y_1473_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v_arg_1477_; lean_object* v___y_1479_; lean_object* v___y_1480_; lean_object* v___y_1481_; lean_object* v___y_1482_; uint8_t v___y_1483_; lean_object* v___y_1522_; lean_object* v___y_1523_; lean_object* v___y_1524_; lean_object* v___y_1525_; lean_object* v___y_1530_; lean_object* v___y_1531_; lean_object* v___y_1532_; lean_object* v___y_1533_; uint8_t v___x_1554_; 
v_one_1470_ = lean_unsigned_to_nat(1u);
v_n_1471_ = lean_nat_sub(v_i_1460_, v_one_1470_);
lean_dec(v_i_1460_);
v___x_1475_ = lean_nat_sub(v_n_1459_, v_n_1471_);
v___x_1476_ = lean_nat_sub(v___x_1475_, v_one_1470_);
lean_dec(v___x_1475_);
v_arg_1477_ = lean_array_fget_borrowed(v_majorTypeArgs_1452_, v___x_1476_);
v___x_1554_ = lean_nat_dec_eq(v___x_1476_, v_idxPos_1456_);
if (v___x_1554_ == 0)
{
uint8_t v___x_1555_; 
v___x_1555_ = lean_expr_eqv(v_arg_1477_, v_idx_1453_);
if (v___x_1555_ == 0)
{
v___y_1530_ = v___y_1461_;
v___y_1531_ = v___y_1462_;
v___y_1532_ = v___y_1463_;
v___y_1533_ = v___y_1464_;
goto v___jp_1529_;
}
else
{
lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; 
v___x_1556_ = lean_obj_once(&l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1, &l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1_once, _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1);
lean_inc_ref(v_idx_1453_);
v___x_1557_ = l_Lean_MessageData_ofExpr(v_idx_1453_);
v___x_1558_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1558_, 0, v___x_1556_);
lean_ctor_set(v___x_1558_, 1, v___x_1557_);
v___x_1559_ = lean_obj_once(&l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__7, &l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__7_once, _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__7);
v___x_1560_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1560_, 0, v___x_1558_);
lean_ctor_set(v___x_1560_, 1, v___x_1559_);
lean_inc_ref(v_majorType_1458_);
v___x_1561_ = l_Lean_indentExpr(v_majorType_1458_);
v___x_1562_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1562_, 0, v___x_1560_);
lean_ctor_set(v___x_1562_, 1, v___x_1561_);
v___x_1563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1563_, 0, v___x_1562_);
lean_inc(v_mvarId_1455_);
lean_inc(v_tacticName_1454_);
v___x_1564_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1454_, v_mvarId_1455_, v___x_1563_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_);
if (lean_obj_tag(v___x_1564_) == 0)
{
lean_dec_ref_known(v___x_1564_, 1);
v___y_1530_ = v___y_1461_;
v___y_1531_ = v___y_1462_;
v___y_1532_ = v___y_1463_;
v___y_1533_ = v___y_1464_;
goto v___jp_1529_;
}
else
{
lean_dec(v___x_1476_);
v___y_1473_ = v___x_1564_;
goto v___jp_1472_;
}
}
}
else
{
v___y_1530_ = v___y_1461_;
v___y_1531_ = v___y_1462_;
v___y_1532_ = v___y_1463_;
v___y_1533_ = v___y_1464_;
goto v___jp_1529_;
}
v___jp_1472_:
{
if (lean_obj_tag(v___y_1473_) == 0)
{
lean_dec_ref_known(v___y_1473_, 1);
v_i_1460_ = v_n_1471_;
goto _start;
}
else
{
lean_dec(v_n_1471_);
lean_dec_ref(v_majorType_1458_);
lean_dec(v_mvarId_1455_);
lean_dec(v_tacticName_1454_);
lean_dec_ref(v_idx_1453_);
return v___y_1473_;
}
}
v___jp_1478_:
{
if (v___y_1483_ == 0)
{
lean_dec(v___x_1476_);
v_i_1460_ = v_n_1471_;
goto _start;
}
else
{
uint8_t v___x_1485_; 
v___x_1485_ = l_Lean_Expr_isFVar(v_arg_1477_);
if (v___x_1485_ == 0)
{
lean_dec(v___x_1476_);
v_i_1460_ = v_n_1471_;
goto _start;
}
else
{
lean_object* v___x_1487_; lean_object* v___x_1488_; 
v___x_1487_ = l_Lean_Expr_fvarId_x21(v_idx_1453_);
v___x_1488_ = l_Lean_FVarId_getDecl___redArg(v___x_1487_, v___y_1479_, v___y_1481_, v___y_1482_);
if (lean_obj_tag(v___x_1488_) == 0)
{
lean_object* v_a_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v_a_1492_; lean_object* v___x_1494_; uint8_t v_isShared_1495_; uint8_t v_isSharedCheck_1512_; 
v_a_1489_ = lean_ctor_get(v___x_1488_, 0);
lean_inc(v_a_1489_);
lean_dec_ref_known(v___x_1488_, 1);
v___x_1490_ = l_Lean_Expr_fvarId_x21(v_arg_1477_);
v___x_1491_ = l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg(v_a_1489_, v___x_1490_, v___y_1483_, v___y_1480_);
v_a_1492_ = lean_ctor_get(v___x_1491_, 0);
v_isSharedCheck_1512_ = !lean_is_exclusive(v___x_1491_);
if (v_isSharedCheck_1512_ == 0)
{
v___x_1494_ = v___x_1491_;
v_isShared_1495_ = v_isSharedCheck_1512_;
goto v_resetjp_1493_;
}
else
{
lean_inc(v_a_1492_);
lean_dec(v___x_1491_);
v___x_1494_ = lean_box(0);
v_isShared_1495_ = v_isSharedCheck_1512_;
goto v_resetjp_1493_;
}
v_resetjp_1493_:
{
uint8_t v___x_1496_; 
v___x_1496_ = lean_unbox(v_a_1492_);
lean_dec(v_a_1492_);
if (v___x_1496_ == 0)
{
lean_del_object(v___x_1494_);
lean_dec(v___x_1476_);
v_i_1460_ = v_n_1471_;
goto _start;
}
else
{
lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1506_; 
v___x_1498_ = lean_obj_once(&l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1, &l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1_once, _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1);
lean_inc_ref(v_idx_1453_);
v___x_1499_ = l_Lean_MessageData_ofExpr(v_idx_1453_);
v___x_1500_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1500_, 0, v___x_1498_);
lean_ctor_set(v___x_1500_, 1, v___x_1499_);
v___x_1501_ = lean_obj_once(&l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__3, &l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__3_once, _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__3);
v___x_1502_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1502_, 0, v___x_1500_);
lean_ctor_set(v___x_1502_, 1, v___x_1501_);
v___x_1503_ = lean_nat_add(v___x_1476_, v_one_1470_);
lean_dec(v___x_1476_);
v___x_1504_ = l_Nat_reprFast(v___x_1503_);
if (v_isShared_1495_ == 0)
{
lean_ctor_set_tag(v___x_1494_, 3);
lean_ctor_set(v___x_1494_, 0, v___x_1504_);
v___x_1506_ = v___x_1494_;
goto v_reusejp_1505_;
}
else
{
lean_object* v_reuseFailAlloc_1511_; 
v_reuseFailAlloc_1511_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1511_, 0, v___x_1504_);
v___x_1506_ = v_reuseFailAlloc_1511_;
goto v_reusejp_1505_;
}
v_reusejp_1505_:
{
lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; 
v___x_1507_ = l_Lean_MessageData_ofFormat(v___x_1506_);
v___x_1508_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1508_, 0, v___x_1502_);
lean_ctor_set(v___x_1508_, 1, v___x_1507_);
v___x_1509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1509_, 0, v___x_1508_);
lean_inc(v_mvarId_1455_);
lean_inc(v_tacticName_1454_);
v___x_1510_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1454_, v_mvarId_1455_, v___x_1509_, v___y_1479_, v___y_1480_, v___y_1481_, v___y_1482_);
v___y_1473_ = v___x_1510_;
goto v___jp_1472_;
}
}
}
}
else
{
lean_object* v_a_1513_; lean_object* v___x_1515_; uint8_t v_isShared_1516_; uint8_t v_isSharedCheck_1520_; 
lean_dec(v___x_1476_);
lean_dec(v_n_1471_);
lean_dec_ref(v_majorType_1458_);
lean_dec(v_mvarId_1455_);
lean_dec(v_tacticName_1454_);
lean_dec_ref(v_idx_1453_);
v_a_1513_ = lean_ctor_get(v___x_1488_, 0);
v_isSharedCheck_1520_ = !lean_is_exclusive(v___x_1488_);
if (v_isSharedCheck_1520_ == 0)
{
v___x_1515_ = v___x_1488_;
v_isShared_1516_ = v_isSharedCheck_1520_;
goto v_resetjp_1514_;
}
else
{
lean_inc(v_a_1513_);
lean_dec(v___x_1488_);
v___x_1515_ = lean_box(0);
v_isShared_1516_ = v_isSharedCheck_1520_;
goto v_resetjp_1514_;
}
v_resetjp_1514_:
{
lean_object* v___x_1518_; 
if (v_isShared_1516_ == 0)
{
v___x_1518_ = v___x_1515_;
goto v_reusejp_1517_;
}
else
{
lean_object* v_reuseFailAlloc_1519_; 
v_reuseFailAlloc_1519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1519_, 0, v_a_1513_);
v___x_1518_ = v_reuseFailAlloc_1519_;
goto v_reusejp_1517_;
}
v_reusejp_1517_:
{
return v___x_1518_;
}
}
}
}
}
}
v___jp_1521_:
{
uint8_t v___x_1526_; 
v___x_1526_ = lean_nat_dec_lt(v_idxPos_1456_, v___x_1476_);
if (v___x_1526_ == 0)
{
v___y_1479_ = v___y_1522_;
v___y_1480_ = v___y_1523_;
v___y_1481_ = v___y_1524_;
v___y_1482_ = v___y_1525_;
v___y_1483_ = v___x_1526_;
goto v___jp_1478_;
}
else
{
lean_object* v_indicesPos_1527_; uint8_t v___x_1528_; 
v_indicesPos_1527_ = lean_ctor_get(v_recursorInfo_1457_, 6);
v___x_1528_ = l_List_elem___at___00Lean_Meta_getMajorTypeIndices_spec__1(v___x_1476_, v_indicesPos_1527_);
v___y_1479_ = v___y_1522_;
v___y_1480_ = v___y_1523_;
v___y_1481_ = v___y_1524_;
v___y_1482_ = v___y_1525_;
v___y_1483_ = v___x_1528_;
goto v___jp_1478_;
}
}
v___jp_1529_:
{
uint8_t v___x_1534_; 
v___x_1534_ = lean_nat_dec_lt(v___x_1476_, v_idxPos_1456_);
if (v___x_1534_ == 0)
{
v___y_1522_ = v___y_1530_;
v___y_1523_ = v___y_1531_;
v___y_1524_ = v___y_1532_;
v___y_1525_ = v___y_1533_;
goto v___jp_1521_;
}
else
{
lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v_a_1537_; lean_object* v___x_1539_; uint8_t v_isShared_1540_; uint8_t v_isSharedCheck_1553_; 
v___x_1535_ = l_Lean_Expr_fvarId_x21(v_idx_1453_);
lean_inc(v_arg_1477_);
v___x_1536_ = l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2___redArg(v_arg_1477_, v___x_1535_, v___y_1531_);
v_a_1537_ = lean_ctor_get(v___x_1536_, 0);
v_isSharedCheck_1553_ = !lean_is_exclusive(v___x_1536_);
if (v_isSharedCheck_1553_ == 0)
{
v___x_1539_ = v___x_1536_;
v_isShared_1540_ = v_isSharedCheck_1553_;
goto v_resetjp_1538_;
}
else
{
lean_inc(v_a_1537_);
lean_dec(v___x_1536_);
v___x_1539_ = lean_box(0);
v_isShared_1540_ = v_isSharedCheck_1553_;
goto v_resetjp_1538_;
}
v_resetjp_1538_:
{
uint8_t v___x_1541_; 
v___x_1541_ = lean_unbox(v_a_1537_);
lean_dec(v_a_1537_);
if (v___x_1541_ == 0)
{
lean_del_object(v___x_1539_);
v___y_1522_ = v___y_1530_;
v___y_1523_ = v___y_1531_;
v___y_1524_ = v___y_1532_;
v___y_1525_ = v___y_1533_;
goto v___jp_1521_;
}
else
{
lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1550_; 
v___x_1542_ = lean_obj_once(&l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1, &l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1_once, _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1);
lean_inc_ref(v_idx_1453_);
v___x_1543_ = l_Lean_MessageData_ofExpr(v_idx_1453_);
v___x_1544_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1544_, 0, v___x_1542_);
lean_ctor_set(v___x_1544_, 1, v___x_1543_);
v___x_1545_ = lean_obj_once(&l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__5, &l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__5_once, _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__5);
v___x_1546_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1546_, 0, v___x_1544_);
lean_ctor_set(v___x_1546_, 1, v___x_1545_);
lean_inc_ref(v_majorType_1458_);
v___x_1547_ = l_Lean_indentExpr(v_majorType_1458_);
v___x_1548_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1548_, 0, v___x_1546_);
lean_ctor_set(v___x_1548_, 1, v___x_1547_);
if (v_isShared_1540_ == 0)
{
lean_ctor_set_tag(v___x_1539_, 1);
lean_ctor_set(v___x_1539_, 0, v___x_1548_);
v___x_1550_ = v___x_1539_;
goto v_reusejp_1549_;
}
else
{
lean_object* v_reuseFailAlloc_1552_; 
v_reuseFailAlloc_1552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1552_, 0, v___x_1548_);
v___x_1550_ = v_reuseFailAlloc_1552_;
goto v_reusejp_1549_;
}
v_reusejp_1549_:
{
lean_object* v___x_1551_; 
lean_inc(v_mvarId_1455_);
lean_inc(v_tacticName_1454_);
v___x_1551_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1454_, v_mvarId_1455_, v___x_1550_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_);
if (lean_obj_tag(v___x_1551_) == 0)
{
lean_dec_ref_known(v___x_1551_, 1);
v___y_1522_ = v___y_1530_;
v___y_1523_ = v___y_1531_;
v___y_1524_ = v___y_1532_;
v___y_1525_ = v___y_1533_;
goto v___jp_1521_;
}
else
{
lean_dec(v___x_1476_);
v___y_1473_ = v___x_1551_;
goto v___jp_1472_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___boxed(lean_object* v_majorTypeArgs_1565_, lean_object* v_idx_1566_, lean_object* v_tacticName_1567_, lean_object* v_mvarId_1568_, lean_object* v_idxPos_1569_, lean_object* v_recursorInfo_1570_, lean_object* v_majorType_1571_, lean_object* v_n_1572_, lean_object* v_i_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_){
_start:
{
lean_object* v_res_1579_; 
v_res_1579_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg(v_majorTypeArgs_1565_, v_idx_1566_, v_tacticName_1567_, v_mvarId_1568_, v_idxPos_1569_, v_recursorInfo_1570_, v_majorType_1571_, v_n_1572_, v_i_1573_, v___y_1574_, v___y_1575_, v___y_1576_, v___y_1577_);
lean_dec(v___y_1577_);
lean_dec_ref(v___y_1576_);
lean_dec(v___y_1575_);
lean_dec_ref(v___y_1574_);
lean_dec(v_n_1572_);
lean_dec_ref(v_recursorInfo_1570_);
lean_dec(v_idxPos_1569_);
lean_dec_ref(v_majorTypeArgs_1565_);
return v_res_1579_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__1(void){
_start:
{
lean_object* v___x_1581_; lean_object* v___x_1582_; 
v___x_1581_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__0));
v___x_1582_ = l_Lean_stringToMessageData(v___x_1581_);
return v___x_1582_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__3(void){
_start:
{
lean_object* v___x_1584_; lean_object* v___x_1585_; 
v___x_1584_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__2));
v___x_1585_ = l_Lean_stringToMessageData(v___x_1584_);
return v___x_1585_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__5(void){
_start:
{
lean_object* v___x_1587_; lean_object* v___x_1588_; 
v___x_1587_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__4));
v___x_1588_ = l_Lean_stringToMessageData(v___x_1587_);
return v___x_1588_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4(lean_object* v_majorTypeArgs_1589_, lean_object* v_tacticName_1590_, lean_object* v_mvarId_1591_, lean_object* v_recursorInfo_1592_, lean_object* v_majorType_1593_, size_t v_sz_1594_, size_t v_i_1595_, lean_object* v_bs_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_){
_start:
{
uint8_t v___x_1602_; 
v___x_1602_ = lean_usize_dec_lt(v_i_1595_, v_sz_1594_);
if (v___x_1602_ == 0)
{
lean_object* v___x_1603_; 
lean_dec_ref(v_majorType_1593_);
lean_dec(v_mvarId_1591_);
lean_dec(v_tacticName_1590_);
v___x_1603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1603_, 0, v_bs_1596_);
return v___x_1603_;
}
else
{
lean_object* v_v_1604_; lean_object* v___x_1605_; lean_object* v_bs_x27_1606_; lean_object* v_a_1608_; lean_object* v___x_1613_; uint8_t v___x_1614_; 
v_v_1604_ = lean_array_uget(v_bs_1596_, v_i_1595_);
v___x_1605_ = lean_unsigned_to_nat(0u);
v_bs_x27_1606_ = lean_array_uset(v_bs_1596_, v_i_1595_, v___x_1605_);
v___x_1613_ = lean_array_get_size(v_majorTypeArgs_1589_);
v___x_1614_ = lean_nat_dec_le(v___x_1613_, v_v_1604_);
if (v___x_1614_ == 0)
{
lean_object* v_idx_1615_; lean_object* v___y_1617_; lean_object* v___y_1618_; lean_object* v___y_1619_; lean_object* v___y_1620_; uint8_t v___x_1630_; 
v_idx_1615_ = lean_array_fget_borrowed(v_majorTypeArgs_1589_, v_v_1604_);
v___x_1630_ = l_Lean_Expr_isFVar(v_idx_1615_);
if (v___x_1630_ == 0)
{
lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; 
v___x_1631_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__1);
lean_inc(v_idx_1615_);
v___x_1632_ = l_Lean_MessageData_ofExpr(v_idx_1615_);
v___x_1633_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1633_, 0, v___x_1631_);
lean_ctor_set(v___x_1633_, 1, v___x_1632_);
v___x_1634_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__3);
v___x_1635_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1635_, 0, v___x_1633_);
lean_ctor_set(v___x_1635_, 1, v___x_1634_);
lean_inc_ref(v_majorType_1593_);
v___x_1636_ = l_Lean_indentExpr(v_majorType_1593_);
v___x_1637_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1637_, 0, v___x_1635_);
lean_ctor_set(v___x_1637_, 1, v___x_1636_);
v___x_1638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1638_, 0, v___x_1637_);
lean_inc(v_mvarId_1591_);
lean_inc(v_tacticName_1590_);
v___x_1639_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1590_, v_mvarId_1591_, v___x_1638_, v___y_1597_, v___y_1598_, v___y_1599_, v___y_1600_);
if (lean_obj_tag(v___x_1639_) == 0)
{
lean_dec_ref_known(v___x_1639_, 1);
v___y_1617_ = v___y_1597_;
v___y_1618_ = v___y_1598_;
v___y_1619_ = v___y_1599_;
v___y_1620_ = v___y_1600_;
goto v___jp_1616_;
}
else
{
lean_object* v_a_1640_; lean_object* v___x_1642_; uint8_t v_isShared_1643_; uint8_t v_isSharedCheck_1647_; 
lean_dec_ref(v_bs_x27_1606_);
lean_dec(v_v_1604_);
lean_dec_ref(v_majorType_1593_);
lean_dec(v_mvarId_1591_);
lean_dec(v_tacticName_1590_);
v_a_1640_ = lean_ctor_get(v___x_1639_, 0);
v_isSharedCheck_1647_ = !lean_is_exclusive(v___x_1639_);
if (v_isSharedCheck_1647_ == 0)
{
v___x_1642_ = v___x_1639_;
v_isShared_1643_ = v_isSharedCheck_1647_;
goto v_resetjp_1641_;
}
else
{
lean_inc(v_a_1640_);
lean_dec(v___x_1639_);
v___x_1642_ = lean_box(0);
v_isShared_1643_ = v_isSharedCheck_1647_;
goto v_resetjp_1641_;
}
v_resetjp_1641_:
{
lean_object* v___x_1645_; 
if (v_isShared_1643_ == 0)
{
v___x_1645_ = v___x_1642_;
goto v_reusejp_1644_;
}
else
{
lean_object* v_reuseFailAlloc_1646_; 
v_reuseFailAlloc_1646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1646_, 0, v_a_1640_);
v___x_1645_ = v_reuseFailAlloc_1646_;
goto v_reusejp_1644_;
}
v_reusejp_1644_:
{
return v___x_1645_;
}
}
}
}
else
{
v___y_1617_ = v___y_1597_;
v___y_1618_ = v___y_1598_;
v___y_1619_ = v___y_1599_;
v___y_1620_ = v___y_1600_;
goto v___jp_1616_;
}
v___jp_1616_:
{
lean_object* v___x_1621_; 
lean_inc_ref(v_majorType_1593_);
lean_inc(v_mvarId_1591_);
lean_inc(v_tacticName_1590_);
lean_inc(v_idx_1615_);
v___x_1621_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg(v_majorTypeArgs_1589_, v_idx_1615_, v_tacticName_1590_, v_mvarId_1591_, v_v_1604_, v_recursorInfo_1592_, v_majorType_1593_, v___x_1613_, v___x_1613_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_);
lean_dec(v_v_1604_);
if (lean_obj_tag(v___x_1621_) == 0)
{
lean_dec_ref_known(v___x_1621_, 1);
lean_inc(v_idx_1615_);
v_a_1608_ = v_idx_1615_;
goto v___jp_1607_;
}
else
{
lean_object* v_a_1622_; lean_object* v___x_1624_; uint8_t v_isShared_1625_; uint8_t v_isSharedCheck_1629_; 
lean_dec_ref(v_bs_x27_1606_);
lean_dec_ref(v_majorType_1593_);
lean_dec(v_mvarId_1591_);
lean_dec(v_tacticName_1590_);
v_a_1622_ = lean_ctor_get(v___x_1621_, 0);
v_isSharedCheck_1629_ = !lean_is_exclusive(v___x_1621_);
if (v_isSharedCheck_1629_ == 0)
{
v___x_1624_ = v___x_1621_;
v_isShared_1625_ = v_isSharedCheck_1629_;
goto v_resetjp_1623_;
}
else
{
lean_inc(v_a_1622_);
lean_dec(v___x_1621_);
v___x_1624_ = lean_box(0);
v_isShared_1625_ = v_isSharedCheck_1629_;
goto v_resetjp_1623_;
}
v_resetjp_1623_:
{
lean_object* v___x_1627_; 
if (v_isShared_1625_ == 0)
{
v___x_1627_ = v___x_1624_;
goto v_reusejp_1626_;
}
else
{
lean_object* v_reuseFailAlloc_1628_; 
v_reuseFailAlloc_1628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1628_, 0, v_a_1622_);
v___x_1627_ = v_reuseFailAlloc_1628_;
goto v_reusejp_1626_;
}
v_reusejp_1626_:
{
return v___x_1627_;
}
}
}
}
}
else
{
lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; 
lean_dec(v_v_1604_);
v___x_1648_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__5, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__5);
lean_inc_ref(v_majorType_1593_);
v___x_1649_ = l_Lean_indentExpr(v_majorType_1593_);
v___x_1650_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1650_, 0, v___x_1648_);
lean_ctor_set(v___x_1650_, 1, v___x_1649_);
v___x_1651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1651_, 0, v___x_1650_);
lean_inc(v_mvarId_1591_);
lean_inc(v_tacticName_1590_);
v___x_1652_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1590_, v_mvarId_1591_, v___x_1651_, v___y_1597_, v___y_1598_, v___y_1599_, v___y_1600_);
if (lean_obj_tag(v___x_1652_) == 0)
{
lean_object* v_a_1653_; 
v_a_1653_ = lean_ctor_get(v___x_1652_, 0);
lean_inc(v_a_1653_);
lean_dec_ref_known(v___x_1652_, 1);
v_a_1608_ = v_a_1653_;
goto v___jp_1607_;
}
else
{
lean_object* v_a_1654_; lean_object* v___x_1656_; uint8_t v_isShared_1657_; uint8_t v_isSharedCheck_1661_; 
lean_dec_ref(v_bs_x27_1606_);
lean_dec_ref(v_majorType_1593_);
lean_dec(v_mvarId_1591_);
lean_dec(v_tacticName_1590_);
v_a_1654_ = lean_ctor_get(v___x_1652_, 0);
v_isSharedCheck_1661_ = !lean_is_exclusive(v___x_1652_);
if (v_isSharedCheck_1661_ == 0)
{
v___x_1656_ = v___x_1652_;
v_isShared_1657_ = v_isSharedCheck_1661_;
goto v_resetjp_1655_;
}
else
{
lean_inc(v_a_1654_);
lean_dec(v___x_1652_);
v___x_1656_ = lean_box(0);
v_isShared_1657_ = v_isSharedCheck_1661_;
goto v_resetjp_1655_;
}
v_resetjp_1655_:
{
lean_object* v___x_1659_; 
if (v_isShared_1657_ == 0)
{
v___x_1659_ = v___x_1656_;
goto v_reusejp_1658_;
}
else
{
lean_object* v_reuseFailAlloc_1660_; 
v_reuseFailAlloc_1660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1660_, 0, v_a_1654_);
v___x_1659_ = v_reuseFailAlloc_1660_;
goto v_reusejp_1658_;
}
v_reusejp_1658_:
{
return v___x_1659_;
}
}
}
}
v___jp_1607_:
{
size_t v___x_1609_; size_t v___x_1610_; lean_object* v___x_1611_; 
v___x_1609_ = ((size_t)1ULL);
v___x_1610_ = lean_usize_add(v_i_1595_, v___x_1609_);
v___x_1611_ = lean_array_uset(v_bs_x27_1606_, v_i_1595_, v_a_1608_);
v_i_1595_ = v___x_1610_;
v_bs_1596_ = v___x_1611_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___boxed(lean_object* v_majorTypeArgs_1662_, lean_object* v_tacticName_1663_, lean_object* v_mvarId_1664_, lean_object* v_recursorInfo_1665_, lean_object* v_majorType_1666_, lean_object* v_sz_1667_, lean_object* v_i_1668_, lean_object* v_bs_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_){
_start:
{
size_t v_sz_boxed_1675_; size_t v_i_boxed_1676_; lean_object* v_res_1677_; 
v_sz_boxed_1675_ = lean_unbox_usize(v_sz_1667_);
lean_dec(v_sz_1667_);
v_i_boxed_1676_ = lean_unbox_usize(v_i_1668_);
lean_dec(v_i_1668_);
v_res_1677_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4(v_majorTypeArgs_1662_, v_tacticName_1663_, v_mvarId_1664_, v_recursorInfo_1665_, v_majorType_1666_, v_sz_boxed_1675_, v_i_boxed_1676_, v_bs_1669_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_);
lean_dec(v___y_1673_);
lean_dec_ref(v___y_1672_);
lean_dec(v___y_1671_);
lean_dec_ref(v___y_1670_);
lean_dec_ref(v_recursorInfo_1665_);
lean_dec_ref(v_majorTypeArgs_1662_);
return v_res_1677_;
}
}
static lean_object* _init_l_Lean_Meta_getMajorTypeIndices___closed__0(void){
_start:
{
lean_object* v___x_1678_; lean_object* v_dummy_1679_; 
v___x_1678_ = lean_box(0);
v_dummy_1679_ = l_Lean_Expr_sort___override(v___x_1678_);
return v_dummy_1679_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMajorTypeIndices(lean_object* v_mvarId_1680_, lean_object* v_tacticName_1681_, lean_object* v_recursorInfo_1682_, lean_object* v_majorType_1683_, lean_object* v_a_1684_, lean_object* v_a_1685_, lean_object* v_a_1686_, lean_object* v_a_1687_){
_start:
{
lean_object* v_indicesPos_1689_; lean_object* v_nargs_1690_; lean_object* v_dummy_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v_majorTypeArgs_1695_; lean_object* v___x_1696_; size_t v_sz_1697_; size_t v___x_1698_; lean_object* v___x_1699_; 
v_indicesPos_1689_ = lean_ctor_get(v_recursorInfo_1682_, 6);
v_nargs_1690_ = l_Lean_Expr_getAppNumArgs(v_majorType_1683_);
v_dummy_1691_ = lean_obj_once(&l_Lean_Meta_getMajorTypeIndices___closed__0, &l_Lean_Meta_getMajorTypeIndices___closed__0_once, _init_l_Lean_Meta_getMajorTypeIndices___closed__0);
lean_inc(v_nargs_1690_);
v___x_1692_ = lean_mk_array(v_nargs_1690_, v_dummy_1691_);
v___x_1693_ = lean_unsigned_to_nat(1u);
v___x_1694_ = lean_nat_sub(v_nargs_1690_, v___x_1693_);
lean_dec(v_nargs_1690_);
lean_inc_ref(v_majorType_1683_);
v_majorTypeArgs_1695_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_majorType_1683_, v___x_1692_, v___x_1694_);
lean_inc(v_indicesPos_1689_);
v___x_1696_ = lean_array_mk(v_indicesPos_1689_);
v_sz_1697_ = lean_array_size(v___x_1696_);
v___x_1698_ = ((size_t)0ULL);
v___x_1699_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4(v_majorTypeArgs_1695_, v_tacticName_1681_, v_mvarId_1680_, v_recursorInfo_1682_, v_majorType_1683_, v_sz_1697_, v___x_1698_, v___x_1696_, v_a_1684_, v_a_1685_, v_a_1686_, v_a_1687_);
lean_dec_ref(v_recursorInfo_1682_);
lean_dec_ref(v_majorTypeArgs_1695_);
return v___x_1699_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMajorTypeIndices___boxed(lean_object* v_mvarId_1700_, lean_object* v_tacticName_1701_, lean_object* v_recursorInfo_1702_, lean_object* v_majorType_1703_, lean_object* v_a_1704_, lean_object* v_a_1705_, lean_object* v_a_1706_, lean_object* v_a_1707_, lean_object* v_a_1708_){
_start:
{
lean_object* v_res_1709_; 
v_res_1709_ = l_Lean_Meta_getMajorTypeIndices(v_mvarId_1700_, v_tacticName_1701_, v_recursorInfo_1702_, v_majorType_1703_, v_a_1704_, v_a_1705_, v_a_1706_, v_a_1707_);
lean_dec(v_a_1707_);
lean_dec_ref(v_a_1706_);
lean_dec(v_a_1705_);
lean_dec_ref(v_a_1704_);
return v_res_1709_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3(lean_object* v_majorTypeArgs_1710_, lean_object* v_idx_1711_, lean_object* v_tacticName_1712_, lean_object* v_mvarId_1713_, lean_object* v_idxPos_1714_, lean_object* v_recursorInfo_1715_, lean_object* v_majorType_1716_, lean_object* v_n_1717_, lean_object* v_i_1718_, lean_object* v_a_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_){
_start:
{
lean_object* v___x_1725_; 
v___x_1725_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg(v_majorTypeArgs_1710_, v_idx_1711_, v_tacticName_1712_, v_mvarId_1713_, v_idxPos_1714_, v_recursorInfo_1715_, v_majorType_1716_, v_n_1717_, v_i_1718_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_);
return v___x_1725_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___boxed(lean_object* v_majorTypeArgs_1726_, lean_object* v_idx_1727_, lean_object* v_tacticName_1728_, lean_object* v_mvarId_1729_, lean_object* v_idxPos_1730_, lean_object* v_recursorInfo_1731_, lean_object* v_majorType_1732_, lean_object* v_n_1733_, lean_object* v_i_1734_, lean_object* v_a_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_){
_start:
{
lean_object* v_res_1741_; 
v_res_1741_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3(v_majorTypeArgs_1726_, v_idx_1727_, v_tacticName_1728_, v_mvarId_1729_, v_idxPos_1730_, v_recursorInfo_1731_, v_majorType_1732_, v_n_1733_, v_i_1734_, v_a_1735_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_);
lean_dec(v___y_1739_);
lean_dec_ref(v___y_1738_);
lean_dec(v___y_1737_);
lean_dec_ref(v___y_1736_);
lean_dec(v_n_1733_);
lean_dec_ref(v_recursorInfo_1731_);
lean_dec(v_idxPos_1730_);
lean_dec_ref(v_majorTypeArgs_1726_);
return v_res_1741_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1___redArg(lean_object* v_name_1742_, lean_object* v_msg_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_){
_start:
{
lean_object* v_ref_1749_; lean_object* v_msg_1750_; lean_object* v___x_1751_; lean_object* v_a_1752_; lean_object* v___x_1754_; uint8_t v_isShared_1755_; uint8_t v_isSharedCheck_1760_; 
v_ref_1749_ = lean_ctor_get(v___y_1746_, 5);
v_msg_1750_ = l_Lean_MessageData_tagWithErrorName(v_msg_1743_, v_name_1742_);
v___x_1751_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1_spec__2(v_msg_1750_, v___y_1744_, v___y_1745_, v___y_1746_, v___y_1747_);
v_a_1752_ = lean_ctor_get(v___x_1751_, 0);
v_isSharedCheck_1760_ = !lean_is_exclusive(v___x_1751_);
if (v_isSharedCheck_1760_ == 0)
{
v___x_1754_ = v___x_1751_;
v_isShared_1755_ = v_isSharedCheck_1760_;
goto v_resetjp_1753_;
}
else
{
lean_inc(v_a_1752_);
lean_dec(v___x_1751_);
v___x_1754_ = lean_box(0);
v_isShared_1755_ = v_isSharedCheck_1760_;
goto v_resetjp_1753_;
}
v_resetjp_1753_:
{
lean_object* v___x_1756_; lean_object* v___x_1758_; 
lean_inc(v_ref_1749_);
v___x_1756_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1756_, 0, v_ref_1749_);
lean_ctor_set(v___x_1756_, 1, v_a_1752_);
if (v_isShared_1755_ == 0)
{
lean_ctor_set_tag(v___x_1754_, 1);
lean_ctor_set(v___x_1754_, 0, v___x_1756_);
v___x_1758_ = v___x_1754_;
goto v_reusejp_1757_;
}
else
{
lean_object* v_reuseFailAlloc_1759_; 
v_reuseFailAlloc_1759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1759_, 0, v___x_1756_);
v___x_1758_ = v_reuseFailAlloc_1759_;
goto v_reusejp_1757_;
}
v_reusejp_1757_:
{
return v___x_1758_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1___redArg___boxed(lean_object* v_name_1761_, lean_object* v_msg_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_){
_start:
{
lean_object* v_res_1768_; 
v_res_1768_ = l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1___redArg(v_name_1761_, v_msg_1762_, v___y_1763_, v___y_1764_, v___y_1765_, v___y_1766_);
lean_dec(v___y_1766_);
lean_dec_ref(v___y_1765_);
lean_dec(v___y_1764_);
lean_dec_ref(v___y_1763_);
return v_res_1768_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Meta_mkRecursorAppPrefix_spec__0(lean_object* v_a_1769_, lean_object* v___x_1770_, lean_object* v_tacticName_1771_, lean_object* v_mvarId_1772_, lean_object* v_x_1773_, lean_object* v_x_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_){
_start:
{
if (lean_obj_tag(v_x_1774_) == 0)
{
lean_object* v___x_1780_; 
lean_dec(v_mvarId_1772_);
lean_dec(v_tacticName_1771_);
lean_dec(v_a_1769_);
v___x_1780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1780_, 0, v_x_1773_);
return v___x_1780_;
}
else
{
lean_object* v_head_1781_; 
v_head_1781_ = lean_ctor_get(v_x_1774_, 0);
if (lean_obj_tag(v_head_1781_) == 0)
{
lean_object* v_tail_1782_; lean_object* v_fst_1783_; lean_object* v___x_1785_; uint8_t v_isShared_1786_; uint8_t v_isSharedCheck_1794_; 
v_tail_1782_ = lean_ctor_get(v_x_1774_, 1);
v_fst_1783_ = lean_ctor_get(v_x_1773_, 0);
v_isSharedCheck_1794_ = !lean_is_exclusive(v_x_1773_);
if (v_isSharedCheck_1794_ == 0)
{
lean_object* v_unused_1795_; 
v_unused_1795_ = lean_ctor_get(v_x_1773_, 1);
lean_dec(v_unused_1795_);
v___x_1785_ = v_x_1773_;
v_isShared_1786_ = v_isSharedCheck_1794_;
goto v_resetjp_1784_;
}
else
{
lean_inc(v_fst_1783_);
lean_dec(v_x_1773_);
v___x_1785_ = lean_box(0);
v_isShared_1786_ = v_isSharedCheck_1794_;
goto v_resetjp_1784_;
}
v_resetjp_1784_:
{
lean_object* v___x_1787_; uint8_t v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1791_; 
lean_inc(v_a_1769_);
v___x_1787_ = lean_array_push(v_fst_1783_, v_a_1769_);
v___x_1788_ = 1;
v___x_1789_ = lean_box(v___x_1788_);
if (v_isShared_1786_ == 0)
{
lean_ctor_set(v___x_1785_, 1, v___x_1789_);
lean_ctor_set(v___x_1785_, 0, v___x_1787_);
v___x_1791_ = v___x_1785_;
goto v_reusejp_1790_;
}
else
{
lean_object* v_reuseFailAlloc_1793_; 
v_reuseFailAlloc_1793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1793_, 0, v___x_1787_);
lean_ctor_set(v_reuseFailAlloc_1793_, 1, v___x_1789_);
v___x_1791_ = v_reuseFailAlloc_1793_;
goto v_reusejp_1790_;
}
v_reusejp_1790_:
{
v_x_1773_ = v___x_1791_;
v_x_1774_ = v_tail_1782_;
goto _start;
}
}
}
else
{
lean_object* v_tail_1796_; lean_object* v_fst_1797_; lean_object* v_snd_1798_; lean_object* v___x_1800_; uint8_t v_isShared_1801_; uint8_t v_isSharedCheck_1815_; 
v_tail_1796_ = lean_ctor_get(v_x_1774_, 1);
v_fst_1797_ = lean_ctor_get(v_x_1773_, 0);
v_snd_1798_ = lean_ctor_get(v_x_1773_, 1);
v_isSharedCheck_1815_ = !lean_is_exclusive(v_x_1773_);
if (v_isSharedCheck_1815_ == 0)
{
v___x_1800_ = v_x_1773_;
v_isShared_1801_ = v_isSharedCheck_1815_;
goto v_resetjp_1799_;
}
else
{
lean_inc(v_snd_1798_);
lean_inc(v_fst_1797_);
lean_dec(v_x_1773_);
v___x_1800_ = lean_box(0);
v_isShared_1801_ = v_isSharedCheck_1815_;
goto v_resetjp_1799_;
}
v_resetjp_1799_:
{
lean_object* v_idx_1802_; lean_object* v___x_1803_; uint8_t v___x_1804_; 
v_idx_1802_ = lean_ctor_get(v_head_1781_, 0);
v___x_1803_ = lean_array_get_size(v___x_1770_);
v___x_1804_ = lean_nat_dec_le(v___x_1803_, v_idx_1802_);
if (v___x_1804_ == 0)
{
lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1808_; 
v___x_1805_ = lean_array_fget_borrowed(v___x_1770_, v_idx_1802_);
lean_inc(v___x_1805_);
v___x_1806_ = lean_array_push(v_fst_1797_, v___x_1805_);
if (v_isShared_1801_ == 0)
{
lean_ctor_set(v___x_1800_, 0, v___x_1806_);
v___x_1808_ = v___x_1800_;
goto v_reusejp_1807_;
}
else
{
lean_object* v_reuseFailAlloc_1810_; 
v_reuseFailAlloc_1810_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1810_, 0, v___x_1806_);
lean_ctor_set(v_reuseFailAlloc_1810_, 1, v_snd_1798_);
v___x_1808_ = v_reuseFailAlloc_1810_;
goto v_reusejp_1807_;
}
v_reusejp_1807_:
{
v_x_1773_ = v___x_1808_;
v_x_1774_ = v_tail_1796_;
goto _start;
}
}
else
{
lean_object* v___x_1811_; lean_object* v___x_1812_; 
lean_del_object(v___x_1800_);
lean_dec(v_snd_1798_);
lean_dec(v_fst_1797_);
v___x_1811_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9);
lean_inc(v_mvarId_1772_);
lean_inc(v_tacticName_1771_);
v___x_1812_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1771_, v_mvarId_1772_, v___x_1811_, v___y_1775_, v___y_1776_, v___y_1777_, v___y_1778_);
if (lean_obj_tag(v___x_1812_) == 0)
{
lean_object* v_a_1813_; 
v_a_1813_ = lean_ctor_get(v___x_1812_, 0);
lean_inc(v_a_1813_);
lean_dec_ref_known(v___x_1812_, 1);
v_x_1773_ = v_a_1813_;
v_x_1774_ = v_tail_1796_;
goto _start;
}
else
{
lean_dec(v_mvarId_1772_);
lean_dec(v_tacticName_1771_);
lean_dec(v_a_1769_);
return v___x_1812_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Meta_mkRecursorAppPrefix_spec__0___boxed(lean_object* v_a_1816_, lean_object* v___x_1817_, lean_object* v_tacticName_1818_, lean_object* v_mvarId_1819_, lean_object* v_x_1820_, lean_object* v_x_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_){
_start:
{
lean_object* v_res_1827_; 
v_res_1827_ = l_List_foldlM___at___00Lean_Meta_mkRecursorAppPrefix_spec__0(v_a_1816_, v___x_1817_, v_tacticName_1818_, v_mvarId_1819_, v_x_1820_, v_x_1821_, v___y_1822_, v___y_1823_, v___y_1824_, v___y_1825_);
lean_dec(v___y_1825_);
lean_dec_ref(v___y_1824_);
lean_dec(v___y_1823_);
lean_dec_ref(v___y_1822_);
lean_dec(v_x_1821_);
lean_dec_ref(v___x_1817_);
return v_res_1827_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__8(void){
_start:
{
lean_object* v___x_1843_; lean_object* v___x_1844_; 
v___x_1843_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__7));
v___x_1844_ = l_Lean_stringToMessageData(v___x_1843_);
return v___x_1844_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__10(void){
_start:
{
lean_object* v___x_1846_; lean_object* v___x_1847_; 
v___x_1846_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__9));
v___x_1847_ = l_Lean_stringToMessageData(v___x_1846_);
return v___x_1847_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__13(void){
_start:
{
lean_object* v___x_1851_; lean_object* v___x_1852_; 
v___x_1851_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__12));
v___x_1852_ = l_Lean_MessageData_ofFormat(v___x_1851_);
return v___x_1852_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__14(void){
_start:
{
lean_object* v___x_1853_; lean_object* v___x_1854_; 
v___x_1853_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__13, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__13_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__13);
v___x_1854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1854_, 0, v___x_1853_);
return v___x_1854_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2(lean_object* v_recursorInfo_1855_, lean_object* v_a_1856_, lean_object* v_tacticName_1857_, lean_object* v_mvarId_1858_, lean_object* v_indices_1859_, lean_object* v_a_1860_, lean_object* v_major_1861_, lean_object* v_x_1862_, lean_object* v_x_1863_, lean_object* v_x_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_){
_start:
{
if (lean_obj_tag(v_x_1862_) == 5)
{
lean_object* v_fn_1870_; lean_object* v_arg_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; 
v_fn_1870_ = lean_ctor_get(v_x_1862_, 0);
lean_inc_ref(v_fn_1870_);
v_arg_1871_ = lean_ctor_get(v_x_1862_, 1);
lean_inc_ref(v_arg_1871_);
lean_dec_ref_known(v_x_1862_, 2);
v___x_1872_ = lean_array_set(v_x_1863_, v_x_1864_, v_arg_1871_);
v___x_1873_ = lean_unsigned_to_nat(1u);
v___x_1874_ = lean_nat_sub(v_x_1864_, v___x_1873_);
lean_dec(v_x_1864_);
v_x_1862_ = v_fn_1870_;
v_x_1863_ = v___x_1872_;
v_x_1864_ = v___x_1874_;
goto _start;
}
else
{
lean_dec(v_x_1864_);
if (lean_obj_tag(v_x_1862_) == 4)
{
lean_object* v_us_1876_; lean_object* v_recursorName_1877_; lean_object* v_univLevelPos_1878_; uint8_t v_depElim_1879_; lean_object* v_paramsPos_1880_; lean_object* v___x_1881_; uint8_t v___x_1882_; lean_object* v___y_1884_; lean_object* v_motive_1885_; lean_object* v___y_1886_; lean_object* v___y_1887_; lean_object* v___y_1888_; lean_object* v___y_1889_; lean_object* v___x_1902_; lean_object* v___x_1903_; 
v_us_1876_ = lean_ctor_get(v_x_1862_, 1);
lean_inc(v_us_1876_);
lean_dec_ref_known(v_x_1862_, 2);
v_recursorName_1877_ = lean_ctor_get(v_recursorInfo_1855_, 0);
lean_inc(v_recursorName_1877_);
v_univLevelPos_1878_ = lean_ctor_get(v_recursorInfo_1855_, 2);
lean_inc(v_univLevelPos_1878_);
v_depElim_1879_ = lean_ctor_get_uint8(v_recursorInfo_1855_, sizeof(void*)*8);
v_paramsPos_1880_ = lean_ctor_get(v_recursorInfo_1855_, 5);
lean_inc(v_paramsPos_1880_);
lean_dec_ref(v_recursorInfo_1855_);
v___x_1881_ = lean_array_mk(v_us_1876_);
v___x_1882_ = 0;
v___x_1902_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__1));
lean_inc(v_mvarId_1858_);
lean_inc(v_tacticName_1857_);
lean_inc(v_a_1856_);
v___x_1903_ = l_List_foldlM___at___00Lean_Meta_mkRecursorAppPrefix_spec__0(v_a_1856_, v___x_1881_, v_tacticName_1857_, v_mvarId_1858_, v___x_1902_, v_univLevelPos_1878_, v___y_1865_, v___y_1866_, v___y_1867_, v___y_1868_);
lean_dec(v_univLevelPos_1878_);
lean_dec_ref(v___x_1881_);
if (lean_obj_tag(v___x_1903_) == 0)
{
lean_object* v_a_1904_; lean_object* v_fst_1905_; lean_object* v_snd_1906_; lean_object* v___x_1908_; uint8_t v_isShared_1909_; uint8_t v_isSharedCheck_1950_; 
v_a_1904_ = lean_ctor_get(v___x_1903_, 0);
lean_inc(v_a_1904_);
lean_dec_ref_known(v___x_1903_, 1);
v_fst_1905_ = lean_ctor_get(v_a_1904_, 0);
v_snd_1906_ = lean_ctor_get(v_a_1904_, 1);
v_isSharedCheck_1950_ = !lean_is_exclusive(v_a_1904_);
if (v_isSharedCheck_1950_ == 0)
{
v___x_1908_ = v_a_1904_;
v_isShared_1909_ = v_isSharedCheck_1950_;
goto v_resetjp_1907_;
}
else
{
lean_inc(v_snd_1906_);
lean_inc(v_fst_1905_);
lean_dec(v_a_1904_);
v___x_1908_ = lean_box(0);
v_isShared_1909_ = v_isSharedCheck_1950_;
goto v_resetjp_1907_;
}
v_resetjp_1907_:
{
lean_object* v___y_1911_; lean_object* v___y_1912_; lean_object* v___y_1913_; lean_object* v___y_1914_; uint8_t v___x_1930_; 
v___x_1930_ = lean_unbox(v_snd_1906_);
lean_dec(v_snd_1906_);
if (v___x_1930_ == 0)
{
uint8_t v___x_1931_; 
v___x_1931_ = l_Lean_Level_isZero(v_a_1856_);
lean_dec(v_a_1856_);
if (v___x_1931_ == 0)
{
lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1936_; 
lean_dec(v_fst_1905_);
lean_dec(v_paramsPos_1880_);
lean_dec_ref(v_x_1863_);
lean_dec_ref(v_major_1861_);
lean_dec_ref(v_a_1860_);
v___x_1932_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__6));
v___x_1933_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__8, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__8_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__8);
v___x_1934_ = l_Lean_MessageData_ofName(v_recursorName_1877_);
if (v_isShared_1909_ == 0)
{
lean_ctor_set_tag(v___x_1908_, 7);
lean_ctor_set(v___x_1908_, 1, v___x_1934_);
lean_ctor_set(v___x_1908_, 0, v___x_1933_);
v___x_1936_ = v___x_1908_;
goto v_reusejp_1935_;
}
else
{
lean_object* v_reuseFailAlloc_1949_; 
v_reuseFailAlloc_1949_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1949_, 0, v___x_1933_);
lean_ctor_set(v_reuseFailAlloc_1949_, 1, v___x_1934_);
v___x_1936_ = v_reuseFailAlloc_1949_;
goto v_reusejp_1935_;
}
v_reusejp_1935_:
{
lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v_a_1941_; lean_object* v___x_1943_; uint8_t v_isShared_1944_; uint8_t v_isSharedCheck_1948_; 
v___x_1937_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__10, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__10_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__10);
v___x_1938_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1938_, 0, v___x_1936_);
lean_ctor_set(v___x_1938_, 1, v___x_1937_);
v___x_1939_ = l_Lean_Meta_mkTacticExMsg(v_tacticName_1857_, v_mvarId_1858_, v___x_1938_);
v___x_1940_ = l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1___redArg(v___x_1932_, v___x_1939_, v___y_1865_, v___y_1866_, v___y_1867_, v___y_1868_);
v_a_1941_ = lean_ctor_get(v___x_1940_, 0);
v_isSharedCheck_1948_ = !lean_is_exclusive(v___x_1940_);
if (v_isSharedCheck_1948_ == 0)
{
v___x_1943_ = v___x_1940_;
v_isShared_1944_ = v_isSharedCheck_1948_;
goto v_resetjp_1942_;
}
else
{
lean_inc(v_a_1941_);
lean_dec(v___x_1940_);
v___x_1943_ = lean_box(0);
v_isShared_1944_ = v_isSharedCheck_1948_;
goto v_resetjp_1942_;
}
v_resetjp_1942_:
{
lean_object* v___x_1946_; 
if (v_isShared_1944_ == 0)
{
v___x_1946_ = v___x_1943_;
goto v_reusejp_1945_;
}
else
{
lean_object* v_reuseFailAlloc_1947_; 
v_reuseFailAlloc_1947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1947_, 0, v_a_1941_);
v___x_1946_ = v_reuseFailAlloc_1947_;
goto v_reusejp_1945_;
}
v_reusejp_1945_:
{
return v___x_1946_;
}
}
}
}
else
{
lean_del_object(v___x_1908_);
lean_dec(v_tacticName_1857_);
v___y_1911_ = v___y_1865_;
v___y_1912_ = v___y_1866_;
v___y_1913_ = v___y_1867_;
v___y_1914_ = v___y_1868_;
goto v___jp_1910_;
}
}
else
{
lean_del_object(v___x_1908_);
lean_dec(v_tacticName_1857_);
lean_dec(v_a_1856_);
v___y_1911_ = v___y_1865_;
v___y_1912_ = v___y_1866_;
v___y_1913_ = v___y_1867_;
v___y_1914_ = v___y_1868_;
goto v___jp_1910_;
}
v___jp_1910_:
{
lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; 
v___x_1915_ = lean_array_to_list(v_fst_1905_);
v___x_1916_ = l_Lean_mkConst(v_recursorName_1877_, v___x_1915_);
v___x_1917_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams(v_mvarId_1858_, v_x_1863_, v_paramsPos_1880_, v___x_1916_, v___y_1911_, v___y_1912_, v___y_1913_, v___y_1914_);
lean_dec_ref(v_x_1863_);
if (lean_obj_tag(v___x_1917_) == 0)
{
if (v_depElim_1879_ == 0)
{
lean_object* v_a_1918_; 
lean_dec_ref(v_major_1861_);
v_a_1918_ = lean_ctor_get(v___x_1917_, 0);
lean_inc(v_a_1918_);
lean_dec_ref_known(v___x_1917_, 1);
v___y_1884_ = v_a_1918_;
v_motive_1885_ = v_a_1860_;
v___y_1886_ = v___y_1911_;
v___y_1887_ = v___y_1912_;
v___y_1888_ = v___y_1913_;
v___y_1889_ = v___y_1914_;
goto v___jp_1883_;
}
else
{
lean_object* v_a_1919_; lean_object* v___x_1920_; 
v_a_1919_ = lean_ctor_get(v___x_1917_, 0);
lean_inc(v_a_1919_);
lean_dec_ref_known(v___x_1917_, 1);
lean_inc(v___y_1914_);
lean_inc_ref(v___y_1913_);
lean_inc(v___y_1912_);
lean_inc_ref(v___y_1911_);
lean_inc_ref(v_major_1861_);
v___x_1920_ = lean_infer_type(v_major_1861_, v___y_1911_, v___y_1912_, v___y_1913_, v___y_1914_);
if (lean_obj_tag(v___x_1920_) == 0)
{
lean_object* v_a_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; 
v_a_1921_ = lean_ctor_get(v___x_1920_, 0);
lean_inc(v_a_1921_);
lean_dec_ref_known(v___x_1920_, 1);
v___x_1922_ = lean_unsigned_to_nat(1u);
v___x_1923_ = lean_mk_empty_array_with_capacity(v___x_1922_);
v___x_1924_ = lean_array_push(v___x_1923_, v_major_1861_);
v___x_1925_ = l_Lean_Expr_abstractM(v_a_1860_, v___x_1924_, v___y_1911_, v___y_1912_, v___y_1913_, v___y_1914_);
lean_dec_ref(v___x_1924_);
if (lean_obj_tag(v___x_1925_) == 0)
{
lean_object* v_a_1926_; lean_object* v___x_1927_; uint8_t v___x_1928_; lean_object* v___x_1929_; 
v_a_1926_ = lean_ctor_get(v___x_1925_, 0);
lean_inc(v_a_1926_);
lean_dec_ref_known(v___x_1925_, 1);
v___x_1927_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__3));
v___x_1928_ = 0;
v___x_1929_ = l_Lean_mkLambda(v___x_1927_, v___x_1928_, v_a_1921_, v_a_1926_);
v___y_1884_ = v_a_1919_;
v_motive_1885_ = v___x_1929_;
v___y_1886_ = v___y_1911_;
v___y_1887_ = v___y_1912_;
v___y_1888_ = v___y_1913_;
v___y_1889_ = v___y_1914_;
goto v___jp_1883_;
}
else
{
lean_dec(v_a_1921_);
lean_dec(v_a_1919_);
return v___x_1925_;
}
}
else
{
lean_dec(v_a_1919_);
lean_dec_ref(v_major_1861_);
lean_dec_ref(v_a_1860_);
return v___x_1920_;
}
}
}
else
{
lean_dec_ref(v_major_1861_);
lean_dec_ref(v_a_1860_);
return v___x_1917_;
}
}
}
}
else
{
lean_object* v_a_1951_; lean_object* v___x_1953_; uint8_t v_isShared_1954_; uint8_t v_isSharedCheck_1958_; 
lean_dec(v_paramsPos_1880_);
lean_dec(v_recursorName_1877_);
lean_dec_ref(v_x_1863_);
lean_dec_ref(v_major_1861_);
lean_dec_ref(v_a_1860_);
lean_dec(v_mvarId_1858_);
lean_dec(v_tacticName_1857_);
lean_dec(v_a_1856_);
v_a_1951_ = lean_ctor_get(v___x_1903_, 0);
v_isSharedCheck_1958_ = !lean_is_exclusive(v___x_1903_);
if (v_isSharedCheck_1958_ == 0)
{
v___x_1953_ = v___x_1903_;
v_isShared_1954_ = v_isSharedCheck_1958_;
goto v_resetjp_1952_;
}
else
{
lean_inc(v_a_1951_);
lean_dec(v___x_1903_);
v___x_1953_ = lean_box(0);
v_isShared_1954_ = v_isSharedCheck_1958_;
goto v_resetjp_1952_;
}
v_resetjp_1952_:
{
lean_object* v___x_1956_; 
if (v_isShared_1954_ == 0)
{
v___x_1956_ = v___x_1953_;
goto v_reusejp_1955_;
}
else
{
lean_object* v_reuseFailAlloc_1957_; 
v_reuseFailAlloc_1957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1957_, 0, v_a_1951_);
v___x_1956_ = v_reuseFailAlloc_1957_;
goto v_reusejp_1955_;
}
v_reusejp_1955_:
{
return v___x_1956_;
}
}
}
v___jp_1883_:
{
uint8_t v___x_1890_; uint8_t v___x_1891_; lean_object* v___x_1892_; 
v___x_1890_ = 1;
v___x_1891_ = 1;
v___x_1892_ = l_Lean_Meta_mkLambdaFVars(v_indices_1859_, v_motive_1885_, v___x_1882_, v___x_1890_, v___x_1882_, v___x_1890_, v___x_1891_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_);
if (lean_obj_tag(v___x_1892_) == 0)
{
lean_object* v_a_1893_; lean_object* v___x_1895_; uint8_t v_isShared_1896_; uint8_t v_isSharedCheck_1901_; 
v_a_1893_ = lean_ctor_get(v___x_1892_, 0);
v_isSharedCheck_1901_ = !lean_is_exclusive(v___x_1892_);
if (v_isSharedCheck_1901_ == 0)
{
v___x_1895_ = v___x_1892_;
v_isShared_1896_ = v_isSharedCheck_1901_;
goto v_resetjp_1894_;
}
else
{
lean_inc(v_a_1893_);
lean_dec(v___x_1892_);
v___x_1895_ = lean_box(0);
v_isShared_1896_ = v_isSharedCheck_1901_;
goto v_resetjp_1894_;
}
v_resetjp_1894_:
{
lean_object* v___x_1897_; lean_object* v___x_1899_; 
v___x_1897_ = l_Lean_Expr_app___override(v___y_1884_, v_a_1893_);
if (v_isShared_1896_ == 0)
{
lean_ctor_set(v___x_1895_, 0, v___x_1897_);
v___x_1899_ = v___x_1895_;
goto v_reusejp_1898_;
}
else
{
lean_object* v_reuseFailAlloc_1900_; 
v_reuseFailAlloc_1900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1900_, 0, v___x_1897_);
v___x_1899_ = v_reuseFailAlloc_1900_;
goto v_reusejp_1898_;
}
v_reusejp_1898_:
{
return v___x_1899_;
}
}
}
else
{
lean_dec_ref(v___y_1884_);
return v___x_1892_;
}
}
}
else
{
lean_object* v___x_1959_; lean_object* v___x_1960_; 
lean_dec_ref(v_x_1863_);
lean_dec_ref(v_x_1862_);
lean_dec_ref(v_major_1861_);
lean_dec_ref(v_a_1860_);
lean_dec(v_a_1856_);
lean_dec_ref(v_recursorInfo_1855_);
v___x_1959_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__14, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__14_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__14);
v___x_1960_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1857_, v_mvarId_1858_, v___x_1959_, v___y_1865_, v___y_1866_, v___y_1867_, v___y_1868_);
return v___x_1960_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___boxed(lean_object* v_recursorInfo_1961_, lean_object* v_a_1962_, lean_object* v_tacticName_1963_, lean_object* v_mvarId_1964_, lean_object* v_indices_1965_, lean_object* v_a_1966_, lean_object* v_major_1967_, lean_object* v_x_1968_, lean_object* v_x_1969_, lean_object* v_x_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_){
_start:
{
lean_object* v_res_1976_; 
v_res_1976_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2(v_recursorInfo_1961_, v_a_1962_, v_tacticName_1963_, v_mvarId_1964_, v_indices_1965_, v_a_1966_, v_major_1967_, v_x_1968_, v_x_1969_, v_x_1970_, v___y_1971_, v___y_1972_, v___y_1973_, v___y_1974_);
lean_dec(v___y_1974_);
lean_dec_ref(v___y_1973_);
lean_dec(v___y_1972_);
lean_dec_ref(v___y_1971_);
lean_dec_ref(v_indices_1965_);
return v_res_1976_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2(lean_object* v_a_1977_, lean_object* v_tacticName_1978_, lean_object* v_mvarId_1979_, lean_object* v_recursorInfo_1980_, lean_object* v_indices_1981_, lean_object* v_a_1982_, lean_object* v_major_1983_, lean_object* v_x_1984_, lean_object* v_x_1985_, lean_object* v_x_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_){
_start:
{
if (lean_obj_tag(v_x_1984_) == 5)
{
lean_object* v_fn_1992_; lean_object* v_arg_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; 
v_fn_1992_ = lean_ctor_get(v_x_1984_, 0);
lean_inc_ref(v_fn_1992_);
v_arg_1993_ = lean_ctor_get(v_x_1984_, 1);
lean_inc_ref(v_arg_1993_);
lean_dec_ref_known(v_x_1984_, 2);
v___x_1994_ = lean_array_set(v_x_1985_, v_x_1986_, v_arg_1993_);
v___x_1995_ = lean_unsigned_to_nat(1u);
v___x_1996_ = lean_nat_sub(v_x_1986_, v___x_1995_);
v___x_1997_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2(v_recursorInfo_1980_, v_a_1977_, v_tacticName_1978_, v_mvarId_1979_, v_indices_1981_, v_a_1982_, v_major_1983_, v_fn_1992_, v___x_1994_, v___x_1996_, v___y_1987_, v___y_1988_, v___y_1989_, v___y_1990_);
return v___x_1997_;
}
else
{
if (lean_obj_tag(v_x_1984_) == 4)
{
lean_object* v_us_1998_; lean_object* v_recursorName_1999_; lean_object* v_univLevelPos_2000_; uint8_t v_depElim_2001_; lean_object* v_paramsPos_2002_; lean_object* v___x_2003_; uint8_t v___x_2004_; lean_object* v___y_2006_; lean_object* v_motive_2007_; lean_object* v___y_2008_; lean_object* v___y_2009_; lean_object* v___y_2010_; lean_object* v___y_2011_; lean_object* v___x_2024_; lean_object* v___x_2025_; 
v_us_1998_ = lean_ctor_get(v_x_1984_, 1);
lean_inc(v_us_1998_);
lean_dec_ref_known(v_x_1984_, 2);
v_recursorName_1999_ = lean_ctor_get(v_recursorInfo_1980_, 0);
lean_inc(v_recursorName_1999_);
v_univLevelPos_2000_ = lean_ctor_get(v_recursorInfo_1980_, 2);
lean_inc(v_univLevelPos_2000_);
v_depElim_2001_ = lean_ctor_get_uint8(v_recursorInfo_1980_, sizeof(void*)*8);
v_paramsPos_2002_ = lean_ctor_get(v_recursorInfo_1980_, 5);
lean_inc(v_paramsPos_2002_);
lean_dec_ref(v_recursorInfo_1980_);
v___x_2003_ = lean_array_mk(v_us_1998_);
v___x_2004_ = 0;
v___x_2024_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__1));
lean_inc(v_mvarId_1979_);
lean_inc(v_tacticName_1978_);
lean_inc(v_a_1977_);
v___x_2025_ = l_List_foldlM___at___00Lean_Meta_mkRecursorAppPrefix_spec__0(v_a_1977_, v___x_2003_, v_tacticName_1978_, v_mvarId_1979_, v___x_2024_, v_univLevelPos_2000_, v___y_1987_, v___y_1988_, v___y_1989_, v___y_1990_);
lean_dec(v_univLevelPos_2000_);
lean_dec_ref(v___x_2003_);
if (lean_obj_tag(v___x_2025_) == 0)
{
lean_object* v_a_2026_; lean_object* v_fst_2027_; lean_object* v_snd_2028_; lean_object* v___x_2030_; uint8_t v_isShared_2031_; uint8_t v_isSharedCheck_2072_; 
v_a_2026_ = lean_ctor_get(v___x_2025_, 0);
lean_inc(v_a_2026_);
lean_dec_ref_known(v___x_2025_, 1);
v_fst_2027_ = lean_ctor_get(v_a_2026_, 0);
v_snd_2028_ = lean_ctor_get(v_a_2026_, 1);
v_isSharedCheck_2072_ = !lean_is_exclusive(v_a_2026_);
if (v_isSharedCheck_2072_ == 0)
{
v___x_2030_ = v_a_2026_;
v_isShared_2031_ = v_isSharedCheck_2072_;
goto v_resetjp_2029_;
}
else
{
lean_inc(v_snd_2028_);
lean_inc(v_fst_2027_);
lean_dec(v_a_2026_);
v___x_2030_ = lean_box(0);
v_isShared_2031_ = v_isSharedCheck_2072_;
goto v_resetjp_2029_;
}
v_resetjp_2029_:
{
lean_object* v___y_2033_; lean_object* v___y_2034_; lean_object* v___y_2035_; lean_object* v___y_2036_; uint8_t v___x_2052_; 
v___x_2052_ = lean_unbox(v_snd_2028_);
lean_dec(v_snd_2028_);
if (v___x_2052_ == 0)
{
uint8_t v___x_2053_; 
v___x_2053_ = l_Lean_Level_isZero(v_a_1977_);
lean_dec(v_a_1977_);
if (v___x_2053_ == 0)
{
lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2058_; 
lean_dec(v_fst_2027_);
lean_dec(v_paramsPos_2002_);
lean_dec_ref(v_x_1985_);
lean_dec_ref(v_major_1983_);
lean_dec_ref(v_a_1982_);
v___x_2054_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__6));
v___x_2055_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__8, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__8_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__8);
v___x_2056_ = l_Lean_MessageData_ofName(v_recursorName_1999_);
if (v_isShared_2031_ == 0)
{
lean_ctor_set_tag(v___x_2030_, 7);
lean_ctor_set(v___x_2030_, 1, v___x_2056_);
lean_ctor_set(v___x_2030_, 0, v___x_2055_);
v___x_2058_ = v___x_2030_;
goto v_reusejp_2057_;
}
else
{
lean_object* v_reuseFailAlloc_2071_; 
v_reuseFailAlloc_2071_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2071_, 0, v___x_2055_);
lean_ctor_set(v_reuseFailAlloc_2071_, 1, v___x_2056_);
v___x_2058_ = v_reuseFailAlloc_2071_;
goto v_reusejp_2057_;
}
v_reusejp_2057_:
{
lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v_a_2063_; lean_object* v___x_2065_; uint8_t v_isShared_2066_; uint8_t v_isSharedCheck_2070_; 
v___x_2059_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__10, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__10_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__10);
v___x_2060_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2060_, 0, v___x_2058_);
lean_ctor_set(v___x_2060_, 1, v___x_2059_);
v___x_2061_ = l_Lean_Meta_mkTacticExMsg(v_tacticName_1978_, v_mvarId_1979_, v___x_2060_);
v___x_2062_ = l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1___redArg(v___x_2054_, v___x_2061_, v___y_1987_, v___y_1988_, v___y_1989_, v___y_1990_);
v_a_2063_ = lean_ctor_get(v___x_2062_, 0);
v_isSharedCheck_2070_ = !lean_is_exclusive(v___x_2062_);
if (v_isSharedCheck_2070_ == 0)
{
v___x_2065_ = v___x_2062_;
v_isShared_2066_ = v_isSharedCheck_2070_;
goto v_resetjp_2064_;
}
else
{
lean_inc(v_a_2063_);
lean_dec(v___x_2062_);
v___x_2065_ = lean_box(0);
v_isShared_2066_ = v_isSharedCheck_2070_;
goto v_resetjp_2064_;
}
v_resetjp_2064_:
{
lean_object* v___x_2068_; 
if (v_isShared_2066_ == 0)
{
v___x_2068_ = v___x_2065_;
goto v_reusejp_2067_;
}
else
{
lean_object* v_reuseFailAlloc_2069_; 
v_reuseFailAlloc_2069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2069_, 0, v_a_2063_);
v___x_2068_ = v_reuseFailAlloc_2069_;
goto v_reusejp_2067_;
}
v_reusejp_2067_:
{
return v___x_2068_;
}
}
}
}
else
{
lean_del_object(v___x_2030_);
lean_dec(v_tacticName_1978_);
v___y_2033_ = v___y_1987_;
v___y_2034_ = v___y_1988_;
v___y_2035_ = v___y_1989_;
v___y_2036_ = v___y_1990_;
goto v___jp_2032_;
}
}
else
{
lean_del_object(v___x_2030_);
lean_dec(v_tacticName_1978_);
lean_dec(v_a_1977_);
v___y_2033_ = v___y_1987_;
v___y_2034_ = v___y_1988_;
v___y_2035_ = v___y_1989_;
v___y_2036_ = v___y_1990_;
goto v___jp_2032_;
}
v___jp_2032_:
{
lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; 
v___x_2037_ = lean_array_to_list(v_fst_2027_);
v___x_2038_ = l_Lean_mkConst(v_recursorName_1999_, v___x_2037_);
v___x_2039_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams(v_mvarId_1979_, v_x_1985_, v_paramsPos_2002_, v___x_2038_, v___y_2033_, v___y_2034_, v___y_2035_, v___y_2036_);
lean_dec_ref(v_x_1985_);
if (lean_obj_tag(v___x_2039_) == 0)
{
if (v_depElim_2001_ == 0)
{
lean_object* v_a_2040_; 
lean_dec_ref(v_major_1983_);
v_a_2040_ = lean_ctor_get(v___x_2039_, 0);
lean_inc(v_a_2040_);
lean_dec_ref_known(v___x_2039_, 1);
v___y_2006_ = v_a_2040_;
v_motive_2007_ = v_a_1982_;
v___y_2008_ = v___y_2033_;
v___y_2009_ = v___y_2034_;
v___y_2010_ = v___y_2035_;
v___y_2011_ = v___y_2036_;
goto v___jp_2005_;
}
else
{
lean_object* v_a_2041_; lean_object* v___x_2042_; 
v_a_2041_ = lean_ctor_get(v___x_2039_, 0);
lean_inc(v_a_2041_);
lean_dec_ref_known(v___x_2039_, 1);
lean_inc(v___y_2036_);
lean_inc_ref(v___y_2035_);
lean_inc(v___y_2034_);
lean_inc_ref(v___y_2033_);
lean_inc_ref(v_major_1983_);
v___x_2042_ = lean_infer_type(v_major_1983_, v___y_2033_, v___y_2034_, v___y_2035_, v___y_2036_);
if (lean_obj_tag(v___x_2042_) == 0)
{
lean_object* v_a_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; 
v_a_2043_ = lean_ctor_get(v___x_2042_, 0);
lean_inc(v_a_2043_);
lean_dec_ref_known(v___x_2042_, 1);
v___x_2044_ = lean_unsigned_to_nat(1u);
v___x_2045_ = lean_mk_empty_array_with_capacity(v___x_2044_);
v___x_2046_ = lean_array_push(v___x_2045_, v_major_1983_);
v___x_2047_ = l_Lean_Expr_abstractM(v_a_1982_, v___x_2046_, v___y_2033_, v___y_2034_, v___y_2035_, v___y_2036_);
lean_dec_ref(v___x_2046_);
if (lean_obj_tag(v___x_2047_) == 0)
{
lean_object* v_a_2048_; lean_object* v___x_2049_; uint8_t v___x_2050_; lean_object* v___x_2051_; 
v_a_2048_ = lean_ctor_get(v___x_2047_, 0);
lean_inc(v_a_2048_);
lean_dec_ref_known(v___x_2047_, 1);
v___x_2049_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__3));
v___x_2050_ = 0;
v___x_2051_ = l_Lean_mkLambda(v___x_2049_, v___x_2050_, v_a_2043_, v_a_2048_);
v___y_2006_ = v_a_2041_;
v_motive_2007_ = v___x_2051_;
v___y_2008_ = v___y_2033_;
v___y_2009_ = v___y_2034_;
v___y_2010_ = v___y_2035_;
v___y_2011_ = v___y_2036_;
goto v___jp_2005_;
}
else
{
lean_dec(v_a_2043_);
lean_dec(v_a_2041_);
return v___x_2047_;
}
}
else
{
lean_dec(v_a_2041_);
lean_dec_ref(v_major_1983_);
lean_dec_ref(v_a_1982_);
return v___x_2042_;
}
}
}
else
{
lean_dec_ref(v_major_1983_);
lean_dec_ref(v_a_1982_);
return v___x_2039_;
}
}
}
}
else
{
lean_object* v_a_2073_; lean_object* v___x_2075_; uint8_t v_isShared_2076_; uint8_t v_isSharedCheck_2080_; 
lean_dec(v_paramsPos_2002_);
lean_dec(v_recursorName_1999_);
lean_dec_ref(v_x_1985_);
lean_dec_ref(v_major_1983_);
lean_dec_ref(v_a_1982_);
lean_dec(v_mvarId_1979_);
lean_dec(v_tacticName_1978_);
lean_dec(v_a_1977_);
v_a_2073_ = lean_ctor_get(v___x_2025_, 0);
v_isSharedCheck_2080_ = !lean_is_exclusive(v___x_2025_);
if (v_isSharedCheck_2080_ == 0)
{
v___x_2075_ = v___x_2025_;
v_isShared_2076_ = v_isSharedCheck_2080_;
goto v_resetjp_2074_;
}
else
{
lean_inc(v_a_2073_);
lean_dec(v___x_2025_);
v___x_2075_ = lean_box(0);
v_isShared_2076_ = v_isSharedCheck_2080_;
goto v_resetjp_2074_;
}
v_resetjp_2074_:
{
lean_object* v___x_2078_; 
if (v_isShared_2076_ == 0)
{
v___x_2078_ = v___x_2075_;
goto v_reusejp_2077_;
}
else
{
lean_object* v_reuseFailAlloc_2079_; 
v_reuseFailAlloc_2079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2079_, 0, v_a_2073_);
v___x_2078_ = v_reuseFailAlloc_2079_;
goto v_reusejp_2077_;
}
v_reusejp_2077_:
{
return v___x_2078_;
}
}
}
v___jp_2005_:
{
uint8_t v___x_2012_; uint8_t v___x_2013_; lean_object* v___x_2014_; 
v___x_2012_ = 1;
v___x_2013_ = 1;
v___x_2014_ = l_Lean_Meta_mkLambdaFVars(v_indices_1981_, v_motive_2007_, v___x_2004_, v___x_2012_, v___x_2004_, v___x_2012_, v___x_2013_, v___y_2008_, v___y_2009_, v___y_2010_, v___y_2011_);
if (lean_obj_tag(v___x_2014_) == 0)
{
lean_object* v_a_2015_; lean_object* v___x_2017_; uint8_t v_isShared_2018_; uint8_t v_isSharedCheck_2023_; 
v_a_2015_ = lean_ctor_get(v___x_2014_, 0);
v_isSharedCheck_2023_ = !lean_is_exclusive(v___x_2014_);
if (v_isSharedCheck_2023_ == 0)
{
v___x_2017_ = v___x_2014_;
v_isShared_2018_ = v_isSharedCheck_2023_;
goto v_resetjp_2016_;
}
else
{
lean_inc(v_a_2015_);
lean_dec(v___x_2014_);
v___x_2017_ = lean_box(0);
v_isShared_2018_ = v_isSharedCheck_2023_;
goto v_resetjp_2016_;
}
v_resetjp_2016_:
{
lean_object* v___x_2019_; lean_object* v___x_2021_; 
v___x_2019_ = l_Lean_Expr_app___override(v___y_2006_, v_a_2015_);
if (v_isShared_2018_ == 0)
{
lean_ctor_set(v___x_2017_, 0, v___x_2019_);
v___x_2021_ = v___x_2017_;
goto v_reusejp_2020_;
}
else
{
lean_object* v_reuseFailAlloc_2022_; 
v_reuseFailAlloc_2022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2022_, 0, v___x_2019_);
v___x_2021_ = v_reuseFailAlloc_2022_;
goto v_reusejp_2020_;
}
v_reusejp_2020_:
{
return v___x_2021_;
}
}
}
else
{
lean_dec_ref(v___y_2006_);
return v___x_2014_;
}
}
}
else
{
lean_object* v___x_2081_; lean_object* v___x_2082_; 
lean_dec_ref(v_x_1985_);
lean_dec_ref(v_x_1984_);
lean_dec_ref(v_major_1983_);
lean_dec_ref(v_a_1982_);
lean_dec_ref(v_recursorInfo_1980_);
lean_dec(v_a_1977_);
v___x_2081_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__14, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__14_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__14);
v___x_2082_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1978_, v_mvarId_1979_, v___x_2081_, v___y_1987_, v___y_1988_, v___y_1989_, v___y_1990_);
return v___x_2082_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2___boxed(lean_object* v_a_2083_, lean_object* v_tacticName_2084_, lean_object* v_mvarId_2085_, lean_object* v_recursorInfo_2086_, lean_object* v_indices_2087_, lean_object* v_a_2088_, lean_object* v_major_2089_, lean_object* v_x_2090_, lean_object* v_x_2091_, lean_object* v_x_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_){
_start:
{
lean_object* v_res_2098_; 
v_res_2098_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2(v_a_2083_, v_tacticName_2084_, v_mvarId_2085_, v_recursorInfo_2086_, v_indices_2087_, v_a_2088_, v_major_2089_, v_x_2090_, v_x_2091_, v_x_2092_, v___y_2093_, v___y_2094_, v___y_2095_, v___y_2096_);
lean_dec(v___y_2096_);
lean_dec_ref(v___y_2095_);
lean_dec(v___y_2094_);
lean_dec_ref(v___y_2093_);
lean_dec(v_x_2092_);
lean_dec_ref(v_indices_2087_);
return v_res_2098_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkRecursorAppPrefix(lean_object* v_mvarId_2099_, lean_object* v_tacticName_2100_, lean_object* v_majorFVarId_2101_, lean_object* v_recursorInfo_2102_, lean_object* v_indices_2103_, lean_object* v_a_2104_, lean_object* v_a_2105_, lean_object* v_a_2106_, lean_object* v_a_2107_){
_start:
{
lean_object* v___x_2109_; 
lean_inc(v_mvarId_2099_);
v___x_2109_ = l_Lean_MVarId_getType(v_mvarId_2099_, v_a_2104_, v_a_2105_, v_a_2106_, v_a_2107_);
if (lean_obj_tag(v___x_2109_) == 0)
{
lean_object* v_a_2110_; lean_object* v___x_2111_; 
v_a_2110_ = lean_ctor_get(v___x_2109_, 0);
lean_inc_n(v_a_2110_, 2);
lean_dec_ref_known(v___x_2109_, 1);
v___x_2111_ = l_Lean_Meta_getLevel(v_a_2110_, v_a_2104_, v_a_2105_, v_a_2106_, v_a_2107_);
if (lean_obj_tag(v___x_2111_) == 0)
{
lean_object* v_a_2112_; lean_object* v___x_2113_; 
v_a_2112_ = lean_ctor_get(v___x_2111_, 0);
lean_inc(v_a_2112_);
lean_dec_ref_known(v___x_2111_, 1);
v___x_2113_ = l_Lean_Meta_normalizeLevel(v_a_2112_, v_a_2104_, v_a_2105_, v_a_2106_, v_a_2107_);
if (lean_obj_tag(v___x_2113_) == 0)
{
lean_object* v_a_2114_; lean_object* v_major_2115_; lean_object* v___x_2116_; 
v_a_2114_ = lean_ctor_get(v___x_2113_, 0);
lean_inc(v_a_2114_);
lean_dec_ref_known(v___x_2113_, 1);
lean_inc(v_majorFVarId_2101_);
v_major_2115_ = l_Lean_mkFVar(v_majorFVarId_2101_);
v___x_2116_ = l_Lean_FVarId_getDecl___redArg(v_majorFVarId_2101_, v_a_2104_, v_a_2106_, v_a_2107_);
if (lean_obj_tag(v___x_2116_) == 0)
{
lean_object* v_a_2117_; lean_object* v_typeName_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; 
v_a_2117_ = lean_ctor_get(v___x_2116_, 0);
lean_inc(v_a_2117_);
lean_dec_ref_known(v___x_2116_, 1);
v_typeName_2118_ = lean_ctor_get(v_recursorInfo_2102_, 1);
v___x_2119_ = l_Lean_LocalDecl_type(v_a_2117_);
lean_dec(v_a_2117_);
lean_inc_ref(v___x_2119_);
v___x_2120_ = l_Lean_Meta_whnfUntil(v___x_2119_, v_typeName_2118_, v_a_2104_, v_a_2105_, v_a_2106_, v_a_2107_);
if (lean_obj_tag(v___x_2120_) == 0)
{
lean_object* v_a_2121_; 
v_a_2121_ = lean_ctor_get(v___x_2120_, 0);
lean_inc(v_a_2121_);
lean_dec_ref_known(v___x_2120_, 1);
if (lean_obj_tag(v_a_2121_) == 1)
{
lean_object* v_val_2122_; lean_object* v_dummy_2123_; lean_object* v_nargs_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; 
lean_dec_ref(v___x_2119_);
v_val_2122_ = lean_ctor_get(v_a_2121_, 0);
lean_inc(v_val_2122_);
lean_dec_ref_known(v_a_2121_, 1);
v_dummy_2123_ = lean_obj_once(&l_Lean_Meta_getMajorTypeIndices___closed__0, &l_Lean_Meta_getMajorTypeIndices___closed__0_once, _init_l_Lean_Meta_getMajorTypeIndices___closed__0);
v_nargs_2124_ = l_Lean_Expr_getAppNumArgs(v_val_2122_);
lean_inc(v_nargs_2124_);
v___x_2125_ = lean_mk_array(v_nargs_2124_, v_dummy_2123_);
v___x_2126_ = lean_unsigned_to_nat(1u);
v___x_2127_ = lean_nat_sub(v_nargs_2124_, v___x_2126_);
lean_dec(v_nargs_2124_);
v___x_2128_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2(v_a_2114_, v_tacticName_2100_, v_mvarId_2099_, v_recursorInfo_2102_, v_indices_2103_, v_a_2110_, v_major_2115_, v_val_2122_, v___x_2125_, v___x_2127_, v_a_2104_, v_a_2105_, v_a_2106_, v_a_2107_);
lean_dec(v___x_2127_);
return v___x_2128_;
}
else
{
lean_object* v___x_2129_; 
lean_dec(v_a_2121_);
lean_dec_ref(v_major_2115_);
lean_dec(v_a_2114_);
lean_dec(v_a_2110_);
lean_dec_ref(v_recursorInfo_2102_);
v___x_2129_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg(v_tacticName_2100_, v_mvarId_2099_, v___x_2119_, v_a_2104_, v_a_2105_, v_a_2106_, v_a_2107_);
return v___x_2129_;
}
}
else
{
lean_object* v_a_2130_; lean_object* v___x_2132_; uint8_t v_isShared_2133_; uint8_t v_isSharedCheck_2137_; 
lean_dec_ref(v___x_2119_);
lean_dec_ref(v_major_2115_);
lean_dec(v_a_2114_);
lean_dec(v_a_2110_);
lean_dec_ref(v_recursorInfo_2102_);
lean_dec(v_tacticName_2100_);
lean_dec(v_mvarId_2099_);
v_a_2130_ = lean_ctor_get(v___x_2120_, 0);
v_isSharedCheck_2137_ = !lean_is_exclusive(v___x_2120_);
if (v_isSharedCheck_2137_ == 0)
{
v___x_2132_ = v___x_2120_;
v_isShared_2133_ = v_isSharedCheck_2137_;
goto v_resetjp_2131_;
}
else
{
lean_inc(v_a_2130_);
lean_dec(v___x_2120_);
v___x_2132_ = lean_box(0);
v_isShared_2133_ = v_isSharedCheck_2137_;
goto v_resetjp_2131_;
}
v_resetjp_2131_:
{
lean_object* v___x_2135_; 
if (v_isShared_2133_ == 0)
{
v___x_2135_ = v___x_2132_;
goto v_reusejp_2134_;
}
else
{
lean_object* v_reuseFailAlloc_2136_; 
v_reuseFailAlloc_2136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2136_, 0, v_a_2130_);
v___x_2135_ = v_reuseFailAlloc_2136_;
goto v_reusejp_2134_;
}
v_reusejp_2134_:
{
return v___x_2135_;
}
}
}
}
else
{
lean_object* v_a_2138_; lean_object* v___x_2140_; uint8_t v_isShared_2141_; uint8_t v_isSharedCheck_2145_; 
lean_dec_ref(v_major_2115_);
lean_dec(v_a_2114_);
lean_dec(v_a_2110_);
lean_dec_ref(v_recursorInfo_2102_);
lean_dec(v_tacticName_2100_);
lean_dec(v_mvarId_2099_);
v_a_2138_ = lean_ctor_get(v___x_2116_, 0);
v_isSharedCheck_2145_ = !lean_is_exclusive(v___x_2116_);
if (v_isSharedCheck_2145_ == 0)
{
v___x_2140_ = v___x_2116_;
v_isShared_2141_ = v_isSharedCheck_2145_;
goto v_resetjp_2139_;
}
else
{
lean_inc(v_a_2138_);
lean_dec(v___x_2116_);
v___x_2140_ = lean_box(0);
v_isShared_2141_ = v_isSharedCheck_2145_;
goto v_resetjp_2139_;
}
v_resetjp_2139_:
{
lean_object* v___x_2143_; 
if (v_isShared_2141_ == 0)
{
v___x_2143_ = v___x_2140_;
goto v_reusejp_2142_;
}
else
{
lean_object* v_reuseFailAlloc_2144_; 
v_reuseFailAlloc_2144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2144_, 0, v_a_2138_);
v___x_2143_ = v_reuseFailAlloc_2144_;
goto v_reusejp_2142_;
}
v_reusejp_2142_:
{
return v___x_2143_;
}
}
}
}
else
{
lean_object* v_a_2146_; lean_object* v___x_2148_; uint8_t v_isShared_2149_; uint8_t v_isSharedCheck_2153_; 
lean_dec(v_a_2110_);
lean_dec_ref(v_recursorInfo_2102_);
lean_dec(v_majorFVarId_2101_);
lean_dec(v_tacticName_2100_);
lean_dec(v_mvarId_2099_);
v_a_2146_ = lean_ctor_get(v___x_2113_, 0);
v_isSharedCheck_2153_ = !lean_is_exclusive(v___x_2113_);
if (v_isSharedCheck_2153_ == 0)
{
v___x_2148_ = v___x_2113_;
v_isShared_2149_ = v_isSharedCheck_2153_;
goto v_resetjp_2147_;
}
else
{
lean_inc(v_a_2146_);
lean_dec(v___x_2113_);
v___x_2148_ = lean_box(0);
v_isShared_2149_ = v_isSharedCheck_2153_;
goto v_resetjp_2147_;
}
v_resetjp_2147_:
{
lean_object* v___x_2151_; 
if (v_isShared_2149_ == 0)
{
v___x_2151_ = v___x_2148_;
goto v_reusejp_2150_;
}
else
{
lean_object* v_reuseFailAlloc_2152_; 
v_reuseFailAlloc_2152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2152_, 0, v_a_2146_);
v___x_2151_ = v_reuseFailAlloc_2152_;
goto v_reusejp_2150_;
}
v_reusejp_2150_:
{
return v___x_2151_;
}
}
}
}
else
{
lean_object* v_a_2154_; lean_object* v___x_2156_; uint8_t v_isShared_2157_; uint8_t v_isSharedCheck_2161_; 
lean_dec(v_a_2110_);
lean_dec_ref(v_recursorInfo_2102_);
lean_dec(v_majorFVarId_2101_);
lean_dec(v_tacticName_2100_);
lean_dec(v_mvarId_2099_);
v_a_2154_ = lean_ctor_get(v___x_2111_, 0);
v_isSharedCheck_2161_ = !lean_is_exclusive(v___x_2111_);
if (v_isSharedCheck_2161_ == 0)
{
v___x_2156_ = v___x_2111_;
v_isShared_2157_ = v_isSharedCheck_2161_;
goto v_resetjp_2155_;
}
else
{
lean_inc(v_a_2154_);
lean_dec(v___x_2111_);
v___x_2156_ = lean_box(0);
v_isShared_2157_ = v_isSharedCheck_2161_;
goto v_resetjp_2155_;
}
v_resetjp_2155_:
{
lean_object* v___x_2159_; 
if (v_isShared_2157_ == 0)
{
v___x_2159_ = v___x_2156_;
goto v_reusejp_2158_;
}
else
{
lean_object* v_reuseFailAlloc_2160_; 
v_reuseFailAlloc_2160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2160_, 0, v_a_2154_);
v___x_2159_ = v_reuseFailAlloc_2160_;
goto v_reusejp_2158_;
}
v_reusejp_2158_:
{
return v___x_2159_;
}
}
}
}
else
{
lean_dec_ref(v_recursorInfo_2102_);
lean_dec(v_majorFVarId_2101_);
lean_dec(v_tacticName_2100_);
lean_dec(v_mvarId_2099_);
return v___x_2109_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkRecursorAppPrefix___boxed(lean_object* v_mvarId_2162_, lean_object* v_tacticName_2163_, lean_object* v_majorFVarId_2164_, lean_object* v_recursorInfo_2165_, lean_object* v_indices_2166_, lean_object* v_a_2167_, lean_object* v_a_2168_, lean_object* v_a_2169_, lean_object* v_a_2170_, lean_object* v_a_2171_){
_start:
{
lean_object* v_res_2172_; 
v_res_2172_ = l_Lean_Meta_mkRecursorAppPrefix(v_mvarId_2162_, v_tacticName_2163_, v_majorFVarId_2164_, v_recursorInfo_2165_, v_indices_2166_, v_a_2167_, v_a_2168_, v_a_2169_, v_a_2170_);
lean_dec(v_a_2170_);
lean_dec_ref(v_a_2169_);
lean_dec(v_a_2168_);
lean_dec_ref(v_a_2167_);
lean_dec_ref(v_indices_2166_);
return v_res_2172_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1(lean_object* v_00_u03b1_2173_, lean_object* v_name_2174_, lean_object* v_msg_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_){
_start:
{
lean_object* v___x_2181_; 
v___x_2181_ = l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1___redArg(v_name_2174_, v_msg_2175_, v___y_2176_, v___y_2177_, v___y_2178_, v___y_2179_);
return v___x_2181_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1___boxed(lean_object* v_00_u03b1_2182_, lean_object* v_name_2183_, lean_object* v_msg_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_){
_start:
{
lean_object* v_res_2190_; 
v_res_2190_ = l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1(v_00_u03b1_2182_, v_name_2183_, v_msg_2184_, v___y_2185_, v___y_2186_, v___y_2187_, v___y_2188_);
lean_dec(v___y_2188_);
lean_dec_ref(v___y_2187_);
lean_dec(v___y_2186_);
lean_dec_ref(v___y_2185_);
return v_res_2190_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___redArg(lean_object* v_mvarId_2191_, lean_object* v_x_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_){
_start:
{
lean_object* v___x_2198_; 
v___x_2198_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_2191_, v_x_2192_, v___y_2193_, v___y_2194_, v___y_2195_, v___y_2196_);
if (lean_obj_tag(v___x_2198_) == 0)
{
lean_object* v_a_2199_; lean_object* v___x_2201_; uint8_t v_isShared_2202_; uint8_t v_isSharedCheck_2206_; 
v_a_2199_ = lean_ctor_get(v___x_2198_, 0);
v_isSharedCheck_2206_ = !lean_is_exclusive(v___x_2198_);
if (v_isSharedCheck_2206_ == 0)
{
v___x_2201_ = v___x_2198_;
v_isShared_2202_ = v_isSharedCheck_2206_;
goto v_resetjp_2200_;
}
else
{
lean_inc(v_a_2199_);
lean_dec(v___x_2198_);
v___x_2201_ = lean_box(0);
v_isShared_2202_ = v_isSharedCheck_2206_;
goto v_resetjp_2200_;
}
v_resetjp_2200_:
{
lean_object* v___x_2204_; 
if (v_isShared_2202_ == 0)
{
v___x_2204_ = v___x_2201_;
goto v_reusejp_2203_;
}
else
{
lean_object* v_reuseFailAlloc_2205_; 
v_reuseFailAlloc_2205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2205_, 0, v_a_2199_);
v___x_2204_ = v_reuseFailAlloc_2205_;
goto v_reusejp_2203_;
}
v_reusejp_2203_:
{
return v___x_2204_;
}
}
}
else
{
lean_object* v_a_2207_; lean_object* v___x_2209_; uint8_t v_isShared_2210_; uint8_t v_isSharedCheck_2214_; 
v_a_2207_ = lean_ctor_get(v___x_2198_, 0);
v_isSharedCheck_2214_ = !lean_is_exclusive(v___x_2198_);
if (v_isSharedCheck_2214_ == 0)
{
v___x_2209_ = v___x_2198_;
v_isShared_2210_ = v_isSharedCheck_2214_;
goto v_resetjp_2208_;
}
else
{
lean_inc(v_a_2207_);
lean_dec(v___x_2198_);
v___x_2209_ = lean_box(0);
v_isShared_2210_ = v_isSharedCheck_2214_;
goto v_resetjp_2208_;
}
v_resetjp_2208_:
{
lean_object* v___x_2212_; 
if (v_isShared_2210_ == 0)
{
v___x_2212_ = v___x_2209_;
goto v_reusejp_2211_;
}
else
{
lean_object* v_reuseFailAlloc_2213_; 
v_reuseFailAlloc_2213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2213_, 0, v_a_2207_);
v___x_2212_ = v_reuseFailAlloc_2213_;
goto v_reusejp_2211_;
}
v_reusejp_2211_:
{
return v___x_2212_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___redArg___boxed(lean_object* v_mvarId_2215_, lean_object* v_x_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_){
_start:
{
lean_object* v_res_2222_; 
v_res_2222_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___redArg(v_mvarId_2215_, v_x_2216_, v___y_2217_, v___y_2218_, v___y_2219_, v___y_2220_);
lean_dec(v___y_2220_);
lean_dec_ref(v___y_2219_);
lean_dec(v___y_2218_);
lean_dec_ref(v___y_2217_);
return v_res_2222_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3(lean_object* v_00_u03b1_2223_, lean_object* v_mvarId_2224_, lean_object* v_x_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_){
_start:
{
lean_object* v___x_2231_; 
v___x_2231_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___redArg(v_mvarId_2224_, v_x_2225_, v___y_2226_, v___y_2227_, v___y_2228_, v___y_2229_);
return v___x_2231_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___boxed(lean_object* v_00_u03b1_2232_, lean_object* v_mvarId_2233_, lean_object* v_x_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_){
_start:
{
lean_object* v_res_2240_; 
v_res_2240_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3(v_00_u03b1_2232_, v_mvarId_2233_, v_x_2234_, v___y_2235_, v___y_2236_, v___y_2237_, v___y_2238_);
lean_dec(v___y_2238_);
lean_dec_ref(v___y_2237_);
lean_dec(v___y_2236_);
lean_dec_ref(v___y_2235_);
return v_res_2240_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_induction_spec__2(lean_object* v_fst_2241_, lean_object* v_as_2242_, size_t v_sz_2243_, size_t v_i_2244_, lean_object* v_b_2245_){
_start:
{
uint8_t v___x_2246_; 
v___x_2246_ = lean_usize_dec_lt(v_i_2244_, v_sz_2243_);
if (v___x_2246_ == 0)
{
return v_b_2245_;
}
else
{
lean_object* v_fst_2247_; lean_object* v_snd_2248_; lean_object* v___x_2250_; uint8_t v_isShared_2251_; uint8_t v_isSharedCheck_2266_; 
v_fst_2247_ = lean_ctor_get(v_b_2245_, 0);
v_snd_2248_ = lean_ctor_get(v_b_2245_, 1);
v_isSharedCheck_2266_ = !lean_is_exclusive(v_b_2245_);
if (v_isSharedCheck_2266_ == 0)
{
v___x_2250_ = v_b_2245_;
v_isShared_2251_ = v_isSharedCheck_2266_;
goto v_resetjp_2249_;
}
else
{
lean_inc(v_snd_2248_);
lean_inc(v_fst_2247_);
lean_dec(v_b_2245_);
v___x_2250_ = lean_box(0);
v_isShared_2251_ = v_isSharedCheck_2266_;
goto v_resetjp_2249_;
}
v_resetjp_2249_:
{
lean_object* v___x_2252_; lean_object* v_a_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2261_; 
v___x_2252_ = lean_box(0);
v_a_2253_ = lean_array_uget_borrowed(v_as_2242_, v_i_2244_);
v___x_2254_ = l_Lean_Expr_fvarId_x21(v_a_2253_);
v___x_2255_ = lean_array_get_borrowed(v___x_2252_, v_fst_2241_, v_snd_2248_);
lean_inc(v___x_2255_);
v___x_2256_ = l_Lean_mkFVar(v___x_2255_);
v___x_2257_ = l_Lean_Meta_FVarSubst_insert(v_fst_2247_, v___x_2254_, v___x_2256_);
v___x_2258_ = lean_unsigned_to_nat(1u);
v___x_2259_ = lean_nat_add(v_snd_2248_, v___x_2258_);
lean_dec(v_snd_2248_);
if (v_isShared_2251_ == 0)
{
lean_ctor_set(v___x_2250_, 1, v___x_2259_);
lean_ctor_set(v___x_2250_, 0, v___x_2257_);
v___x_2261_ = v___x_2250_;
goto v_reusejp_2260_;
}
else
{
lean_object* v_reuseFailAlloc_2265_; 
v_reuseFailAlloc_2265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2265_, 0, v___x_2257_);
lean_ctor_set(v_reuseFailAlloc_2265_, 1, v___x_2259_);
v___x_2261_ = v_reuseFailAlloc_2265_;
goto v_reusejp_2260_;
}
v_reusejp_2260_:
{
size_t v___x_2262_; size_t v___x_2263_; 
v___x_2262_ = ((size_t)1ULL);
v___x_2263_ = lean_usize_add(v_i_2244_, v___x_2262_);
v_i_2244_ = v___x_2263_;
v_b_2245_ = v___x_2261_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_induction_spec__2___boxed(lean_object* v_fst_2267_, lean_object* v_as_2268_, lean_object* v_sz_2269_, lean_object* v_i_2270_, lean_object* v_b_2271_){
_start:
{
size_t v_sz_boxed_2272_; size_t v_i_boxed_2273_; lean_object* v_res_2274_; 
v_sz_boxed_2272_ = lean_unbox_usize(v_sz_2269_);
lean_dec(v_sz_2269_);
v_i_boxed_2273_ = lean_unbox_usize(v_i_2270_);
lean_dec(v_i_2270_);
v_res_2274_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_induction_spec__2(v_fst_2267_, v_as_2268_, v_sz_boxed_2272_, v_i_boxed_2273_, v_b_2271_);
lean_dec_ref(v_as_2268_);
lean_dec_ref(v_fst_2267_);
return v_res_2274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4___lam__0(lean_object* v_snd_2275_, lean_object* v___x_2276_, lean_object* v_fst_2277_, lean_object* v_a_2278_, lean_object* v___x_2279_, lean_object* v_givenNames_2280_, lean_object* v_fst_2281_, lean_object* v___x_2282_, lean_object* v_fst_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_){
_start:
{
lean_object* v___x_2289_; 
lean_inc_ref(v_a_2278_);
lean_inc(v_snd_2275_);
v___x_2289_ = l_Lean_Meta_mkRecursorAppPrefix(v_snd_2275_, v___x_2276_, v_fst_2277_, v_a_2278_, v___x_2279_, v___y_2284_, v___y_2285_, v___y_2286_, v___y_2287_);
if (lean_obj_tag(v___x_2289_) == 0)
{
lean_object* v_a_2290_; lean_object* v___x_2291_; 
v_a_2290_ = lean_ctor_get(v___x_2289_, 0);
lean_inc(v_a_2290_);
lean_dec_ref_known(v___x_2289_, 1);
v___x_2291_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize(v_snd_2275_, v_givenNames_2280_, v_a_2278_, v_fst_2281_, v___x_2282_, v___x_2279_, v_fst_2283_, v_a_2290_, v___y_2284_, v___y_2285_, v___y_2286_, v___y_2287_);
lean_dec_ref(v_a_2278_);
return v___x_2291_;
}
else
{
lean_object* v_a_2292_; lean_object* v___x_2294_; uint8_t v_isShared_2295_; uint8_t v_isSharedCheck_2299_; 
lean_dec(v_fst_2283_);
lean_dec_ref(v___x_2282_);
lean_dec_ref(v_a_2278_);
lean_dec(v_snd_2275_);
v_a_2292_ = lean_ctor_get(v___x_2289_, 0);
v_isSharedCheck_2299_ = !lean_is_exclusive(v___x_2289_);
if (v_isSharedCheck_2299_ == 0)
{
v___x_2294_ = v___x_2289_;
v_isShared_2295_ = v_isSharedCheck_2299_;
goto v_resetjp_2293_;
}
else
{
lean_inc(v_a_2292_);
lean_dec(v___x_2289_);
v___x_2294_ = lean_box(0);
v_isShared_2295_ = v_isSharedCheck_2299_;
goto v_resetjp_2293_;
}
v_resetjp_2293_:
{
lean_object* v___x_2297_; 
if (v_isShared_2295_ == 0)
{
v___x_2297_ = v___x_2294_;
goto v_reusejp_2296_;
}
else
{
lean_object* v_reuseFailAlloc_2298_; 
v_reuseFailAlloc_2298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2298_, 0, v_a_2292_);
v___x_2297_ = v_reuseFailAlloc_2298_;
goto v_reusejp_2296_;
}
v_reusejp_2296_:
{
return v___x_2297_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4___lam__0___boxed(lean_object* v_snd_2300_, lean_object* v___x_2301_, lean_object* v_fst_2302_, lean_object* v_a_2303_, lean_object* v___x_2304_, lean_object* v_givenNames_2305_, lean_object* v_fst_2306_, lean_object* v___x_2307_, lean_object* v_fst_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_){
_start:
{
lean_object* v_res_2314_; 
v_res_2314_ = l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4___lam__0(v_snd_2300_, v___x_2301_, v_fst_2302_, v_a_2303_, v___x_2304_, v_givenNames_2305_, v_fst_2306_, v___x_2307_, v_fst_2308_, v___y_2309_, v___y_2310_, v___y_2311_, v___y_2312_);
lean_dec(v___y_2312_);
lean_dec_ref(v___y_2311_);
lean_dec(v___y_2310_);
lean_dec_ref(v___y_2309_);
lean_dec_ref(v_fst_2306_);
lean_dec_ref(v_givenNames_2305_);
lean_dec_ref(v___x_2304_);
return v_res_2314_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_induction_spec__1(size_t v_sz_2315_, size_t v_i_2316_, lean_object* v_bs_2317_){
_start:
{
uint8_t v___x_2318_; 
v___x_2318_ = lean_usize_dec_lt(v_i_2316_, v_sz_2315_);
if (v___x_2318_ == 0)
{
return v_bs_2317_;
}
else
{
lean_object* v_v_2319_; lean_object* v___x_2320_; lean_object* v_bs_x27_2321_; lean_object* v___x_2322_; size_t v___x_2323_; size_t v___x_2324_; lean_object* v___x_2325_; 
v_v_2319_ = lean_array_uget(v_bs_2317_, v_i_2316_);
v___x_2320_ = lean_unsigned_to_nat(0u);
v_bs_x27_2321_ = lean_array_uset(v_bs_2317_, v_i_2316_, v___x_2320_);
v___x_2322_ = l_Lean_Expr_fvarId_x21(v_v_2319_);
lean_dec(v_v_2319_);
v___x_2323_ = ((size_t)1ULL);
v___x_2324_ = lean_usize_add(v_i_2316_, v___x_2323_);
v___x_2325_ = lean_array_uset(v_bs_x27_2321_, v_i_2316_, v___x_2322_);
v_i_2316_ = v___x_2324_;
v_bs_2317_ = v___x_2325_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_induction_spec__1___boxed(lean_object* v_sz_2327_, lean_object* v_i_2328_, lean_object* v_bs_2329_){
_start:
{
size_t v_sz_boxed_2330_; size_t v_i_boxed_2331_; lean_object* v_res_2332_; 
v_sz_boxed_2330_ = lean_unbox_usize(v_sz_2327_);
lean_dec(v_sz_2327_);
v_i_boxed_2331_ = lean_unbox_usize(v_i_2328_);
lean_dec(v_i_2328_);
v_res_2332_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_induction_spec__1(v_sz_boxed_2330_, v_i_boxed_2331_, v_bs_2329_);
return v_res_2332_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_MVarId_induction_spec__0(lean_object* v_majorTypeArgs_2333_, lean_object* v_val_2334_, lean_object* v_mvarId_2335_, lean_object* v_as_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_){
_start:
{
if (lean_obj_tag(v_as_2336_) == 0)
{
lean_object* v___x_2342_; lean_object* v___x_2343_; 
lean_dec(v_mvarId_2335_);
lean_dec_ref(v_val_2334_);
v___x_2342_ = lean_box(0);
v___x_2343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2343_, 0, v___x_2342_);
return v___x_2343_;
}
else
{
lean_object* v_head_2344_; 
v_head_2344_ = lean_ctor_get(v_as_2336_, 0);
lean_inc(v_head_2344_);
if (lean_obj_tag(v_head_2344_) == 0)
{
lean_object* v_tail_2345_; 
v_tail_2345_ = lean_ctor_get(v_as_2336_, 1);
lean_inc(v_tail_2345_);
lean_dec_ref_known(v_as_2336_, 2);
v_as_2336_ = v_tail_2345_;
goto _start;
}
else
{
lean_object* v_tail_2347_; lean_object* v___x_2349_; uint8_t v_isShared_2350_; uint8_t v_isSharedCheck_2370_; 
v_tail_2347_ = lean_ctor_get(v_as_2336_, 1);
v_isSharedCheck_2370_ = !lean_is_exclusive(v_as_2336_);
if (v_isSharedCheck_2370_ == 0)
{
lean_object* v_unused_2371_; 
v_unused_2371_ = lean_ctor_get(v_as_2336_, 0);
lean_dec(v_unused_2371_);
v___x_2349_ = v_as_2336_;
v_isShared_2350_ = v_isSharedCheck_2370_;
goto v_resetjp_2348_;
}
else
{
lean_inc(v_tail_2347_);
lean_dec(v_as_2336_);
v___x_2349_ = lean_box(0);
v_isShared_2350_ = v_isSharedCheck_2370_;
goto v_resetjp_2348_;
}
v_resetjp_2348_:
{
lean_object* v_val_2351_; lean_object* v___x_2353_; uint8_t v_isShared_2354_; uint8_t v_isSharedCheck_2369_; 
v_val_2351_ = lean_ctor_get(v_head_2344_, 0);
v_isSharedCheck_2369_ = !lean_is_exclusive(v_head_2344_);
if (v_isSharedCheck_2369_ == 0)
{
v___x_2353_ = v_head_2344_;
v_isShared_2354_ = v_isSharedCheck_2369_;
goto v_resetjp_2352_;
}
else
{
lean_inc(v_val_2351_);
lean_dec(v_head_2344_);
v___x_2353_ = lean_box(0);
v_isShared_2354_ = v_isSharedCheck_2369_;
goto v_resetjp_2352_;
}
v_resetjp_2352_:
{
lean_object* v___x_2355_; uint8_t v___x_2356_; 
v___x_2355_ = lean_array_get_size(v_majorTypeArgs_2333_);
v___x_2356_ = lean_nat_dec_le(v___x_2355_, v_val_2351_);
lean_dec(v_val_2351_);
if (v___x_2356_ == 0)
{
lean_del_object(v___x_2353_);
lean_del_object(v___x_2349_);
v_as_2336_ = v_tail_2347_;
goto _start;
}
else
{
lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2362_; 
v___x_2358_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1));
v___x_2359_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__5, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__5);
lean_inc_ref(v_val_2334_);
v___x_2360_ = l_Lean_indentExpr(v_val_2334_);
if (v_isShared_2350_ == 0)
{
lean_ctor_set_tag(v___x_2349_, 7);
lean_ctor_set(v___x_2349_, 1, v___x_2360_);
lean_ctor_set(v___x_2349_, 0, v___x_2359_);
v___x_2362_ = v___x_2349_;
goto v_reusejp_2361_;
}
else
{
lean_object* v_reuseFailAlloc_2368_; 
v_reuseFailAlloc_2368_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2368_, 0, v___x_2359_);
lean_ctor_set(v_reuseFailAlloc_2368_, 1, v___x_2360_);
v___x_2362_ = v_reuseFailAlloc_2368_;
goto v_reusejp_2361_;
}
v_reusejp_2361_:
{
lean_object* v___x_2364_; 
if (v_isShared_2354_ == 0)
{
lean_ctor_set(v___x_2353_, 0, v___x_2362_);
v___x_2364_ = v___x_2353_;
goto v_reusejp_2363_;
}
else
{
lean_object* v_reuseFailAlloc_2367_; 
v_reuseFailAlloc_2367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2367_, 0, v___x_2362_);
v___x_2364_ = v_reuseFailAlloc_2367_;
goto v_reusejp_2363_;
}
v_reusejp_2363_:
{
lean_object* v___x_2365_; 
lean_inc(v_mvarId_2335_);
v___x_2365_ = l_Lean_Meta_throwTacticEx___redArg(v___x_2358_, v_mvarId_2335_, v___x_2364_, v___y_2337_, v___y_2338_, v___y_2339_, v___y_2340_);
if (lean_obj_tag(v___x_2365_) == 0)
{
lean_dec_ref_known(v___x_2365_, 1);
v_as_2336_ = v_tail_2347_;
goto _start;
}
else
{
lean_dec(v_tail_2347_);
lean_dec(v_mvarId_2335_);
lean_dec_ref(v_val_2334_);
return v___x_2365_;
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
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_MVarId_induction_spec__0___boxed(lean_object* v_majorTypeArgs_2372_, lean_object* v_val_2373_, lean_object* v_mvarId_2374_, lean_object* v_as_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_){
_start:
{
lean_object* v_res_2381_; 
v_res_2381_ = l_List_forM___at___00Lean_MVarId_induction_spec__0(v_majorTypeArgs_2372_, v_val_2373_, v_mvarId_2374_, v_as_2375_, v___y_2376_, v___y_2377_, v___y_2378_, v___y_2379_);
lean_dec(v___y_2379_);
lean_dec_ref(v___y_2378_);
lean_dec(v___y_2377_);
lean_dec_ref(v___y_2376_);
lean_dec_ref(v_majorTypeArgs_2372_);
return v_res_2381_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__1(void){
_start:
{
lean_object* v___x_2383_; lean_object* v___x_2384_; 
v___x_2383_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__0));
v___x_2384_ = l_Lean_stringToMessageData(v___x_2383_);
return v___x_2384_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__3(void){
_start:
{
lean_object* v___x_2386_; lean_object* v___x_2387_; 
v___x_2386_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__2));
v___x_2387_ = l_Lean_stringToMessageData(v___x_2386_);
return v___x_2387_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__5(void){
_start:
{
lean_object* v___x_2389_; lean_object* v___x_2390_; 
v___x_2389_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__4));
v___x_2390_ = l_Lean_stringToMessageData(v___x_2389_);
return v___x_2390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4(lean_object* v_a_2391_, lean_object* v_val_2392_, lean_object* v_mvarId_2393_, lean_object* v_majorFVarId_2394_, lean_object* v_givenNames_2395_, lean_object* v_recursorName_2396_, lean_object* v_x_2397_, lean_object* v_x_2398_, lean_object* v_x_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_){
_start:
{
if (lean_obj_tag(v_x_2397_) == 5)
{
lean_object* v_fn_2405_; lean_object* v_arg_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; 
v_fn_2405_ = lean_ctor_get(v_x_2397_, 0);
lean_inc_ref(v_fn_2405_);
v_arg_2406_ = lean_ctor_get(v_x_2397_, 1);
lean_inc_ref(v_arg_2406_);
lean_dec_ref_known(v_x_2397_, 2);
v___x_2407_ = lean_array_set(v_x_2398_, v_x_2399_, v_arg_2406_);
v___x_2408_ = lean_unsigned_to_nat(1u);
v___x_2409_ = lean_nat_sub(v_x_2399_, v___x_2408_);
lean_dec(v_x_2399_);
v_x_2397_ = v_fn_2405_;
v_x_2398_ = v___x_2407_;
v_x_2399_ = v___x_2409_;
goto _start;
}
else
{
uint8_t v_depElim_2411_; lean_object* v_paramsPos_2412_; lean_object* v___x_2413_; 
lean_dec(v_x_2399_);
lean_dec_ref(v_x_2397_);
v_depElim_2411_ = lean_ctor_get_uint8(v_a_2391_, sizeof(void*)*8);
v_paramsPos_2412_ = lean_ctor_get(v_a_2391_, 5);
lean_inc(v_paramsPos_2412_);
lean_inc(v_mvarId_2393_);
lean_inc_ref(v_val_2392_);
v___x_2413_ = l_List_forM___at___00Lean_MVarId_induction_spec__0(v_x_2398_, v_val_2392_, v_mvarId_2393_, v_paramsPos_2412_, v___y_2400_, v___y_2401_, v___y_2402_, v___y_2403_);
lean_dec_ref(v_x_2398_);
if (lean_obj_tag(v___x_2413_) == 0)
{
lean_object* v___x_2414_; lean_object* v___y_2416_; lean_object* v___y_2417_; lean_object* v___y_2418_; lean_object* v___y_2419_; lean_object* v___y_2420_; size_t v___y_2421_; lean_object* v___y_2422_; lean_object* v___y_2423_; lean_object* v___y_2424_; lean_object* v___y_2425_; lean_object* v___y_2426_; lean_object* v___y_2427_; lean_object* v___x_2432_; 
lean_dec_ref_known(v___x_2413_, 1);
v___x_2414_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1));
lean_inc_ref(v_a_2391_);
lean_inc(v_mvarId_2393_);
v___x_2432_ = l_Lean_Meta_getMajorTypeIndices(v_mvarId_2393_, v___x_2414_, v_a_2391_, v_val_2392_, v___y_2400_, v___y_2401_, v___y_2402_, v___y_2403_);
if (lean_obj_tag(v___x_2432_) == 0)
{
lean_object* v_a_2433_; lean_object* v___x_2434_; 
v_a_2433_ = lean_ctor_get(v___x_2432_, 0);
lean_inc(v_a_2433_);
lean_dec_ref_known(v___x_2432_, 1);
lean_inc(v_mvarId_2393_);
v___x_2434_ = l_Lean_MVarId_getType(v_mvarId_2393_, v___y_2400_, v___y_2401_, v___y_2402_, v___y_2403_);
if (lean_obj_tag(v___x_2434_) == 0)
{
lean_object* v_a_2435_; lean_object* v_cls_2436_; lean_object* v___y_2438_; lean_object* v___y_2439_; lean_object* v___y_2440_; lean_object* v___y_2441_; 
v_a_2435_ = lean_ctor_get(v___x_2434_, 0);
lean_inc(v_a_2435_);
lean_dec_ref_known(v___x_2434_, 1);
v_cls_2436_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__2));
if (v_depElim_2411_ == 0)
{
lean_object* v___x_2524_; lean_object* v_a_2525_; lean_object* v___x_2527_; uint8_t v_isShared_2528_; uint8_t v_isSharedCheck_2547_; 
lean_inc(v_majorFVarId_2394_);
v___x_2524_ = l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2___redArg(v_a_2435_, v_majorFVarId_2394_, v___y_2401_);
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
lean_dec(v_recursorName_2396_);
v___y_2438_ = v___y_2400_;
v___y_2439_ = v___y_2401_;
v___y_2440_ = v___y_2402_;
v___y_2441_ = v___y_2403_;
goto v___jp_2437_;
}
else
{
lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2536_; 
v___x_2530_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__3, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__3);
v___x_2531_ = l_Lean_MessageData_ofName(v_recursorName_2396_);
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
lean_inc(v_mvarId_2393_);
v___x_2537_ = l_Lean_Meta_throwTacticEx___redArg(v___x_2414_, v_mvarId_2393_, v___x_2536_, v___y_2400_, v___y_2401_, v___y_2402_, v___y_2403_);
if (lean_obj_tag(v___x_2537_) == 0)
{
lean_dec_ref_known(v___x_2537_, 1);
v___y_2438_ = v___y_2400_;
v___y_2439_ = v___y_2401_;
v___y_2440_ = v___y_2402_;
v___y_2441_ = v___y_2403_;
goto v___jp_2437_;
}
else
{
lean_object* v_a_2538_; lean_object* v___x_2540_; uint8_t v_isShared_2541_; uint8_t v_isSharedCheck_2545_; 
lean_dec(v_a_2433_);
lean_dec_ref(v_givenNames_2395_);
lean_dec(v_majorFVarId_2394_);
lean_dec(v_mvarId_2393_);
lean_dec_ref(v_a_2391_);
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
lean_dec(v_a_2435_);
lean_dec(v_recursorName_2396_);
v___y_2438_ = v___y_2400_;
v___y_2439_ = v___y_2401_;
v___y_2440_ = v___y_2402_;
v___y_2441_ = v___y_2403_;
goto v___jp_2437_;
}
v___jp_2437_:
{
size_t v_sz_2442_; size_t v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; uint8_t v___x_2446_; uint8_t v___x_2447_; lean_object* v___x_2448_; 
v_sz_2442_ = lean_array_size(v_a_2433_);
v___x_2443_ = ((size_t)0ULL);
lean_inc(v_a_2433_);
v___x_2444_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_induction_spec__1(v_sz_2442_, v___x_2443_, v_a_2433_);
lean_inc(v_majorFVarId_2394_);
v___x_2445_ = lean_array_push(v___x_2444_, v_majorFVarId_2394_);
v___x_2446_ = 1;
v___x_2447_ = 0;
v___x_2448_ = l_Lean_MVarId_revert(v_mvarId_2393_, v___x_2445_, v___x_2446_, v___x_2447_, v___y_2438_, v___y_2439_, v___y_2440_, v___y_2441_);
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
v___x_2452_ = lean_array_get_size(v_a_2433_);
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
lean_object* v_a_2459_; lean_object* v_fst_2460_; lean_object* v_snd_2461_; lean_object* v___x_2463_; uint8_t v_isShared_2464_; uint8_t v_isSharedCheck_2499_; 
v_a_2459_ = lean_ctor_get(v___x_2458_, 0);
lean_inc(v_a_2459_);
lean_dec_ref_known(v___x_2458_, 1);
v_fst_2460_ = lean_ctor_get(v_a_2459_, 0);
v_snd_2461_ = lean_ctor_get(v_a_2459_, 1);
v_isSharedCheck_2499_ = !lean_is_exclusive(v_a_2459_);
if (v_isSharedCheck_2499_ == 0)
{
v___x_2463_ = v_a_2459_;
v_isShared_2464_ = v_isSharedCheck_2499_;
goto v_resetjp_2462_;
}
else
{
lean_inc(v_snd_2461_);
lean_inc(v_fst_2460_);
lean_dec(v_a_2459_);
v___x_2463_ = lean_box(0);
v_isShared_2464_ = v_isSharedCheck_2499_;
goto v_resetjp_2462_;
}
v_resetjp_2462_:
{
lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2470_; 
v___x_2465_ = lean_box(0);
lean_inc(v_fst_2460_);
v___x_2466_ = l_Lean_mkFVar(v_fst_2460_);
lean_inc_ref(v___x_2466_);
v___x_2467_ = l_Lean_Meta_FVarSubst_insert(v___x_2465_, v_majorFVarId_2394_, v___x_2466_);
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
lean_object* v_reuseFailAlloc_2498_; 
v_reuseFailAlloc_2498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2498_, 0, v___x_2467_);
lean_ctor_set(v_reuseFailAlloc_2498_, 1, v___x_2468_);
v___x_2470_ = v_reuseFailAlloc_2498_;
goto v_reusejp_2469_;
}
v_reusejp_2469_:
{
lean_object* v___x_2471_; lean_object* v_options_2472_; uint8_t v_hasTrace_2473_; 
v___x_2471_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_induction_spec__2(v_fst_2456_, v_a_2433_, v_sz_2442_, v___x_2443_, v___x_2470_);
lean_dec(v_a_2433_);
v_options_2472_ = lean_ctor_get(v___y_2440_, 2);
v_hasTrace_2473_ = lean_ctor_get_uint8(v_options_2472_, sizeof(void*)*1);
if (v_hasTrace_2473_ == 0)
{
lean_object* v_fst_2474_; 
v_fst_2474_ = lean_ctor_get(v___x_2471_, 0);
lean_inc(v_fst_2474_);
lean_dec_ref(v___x_2471_);
lean_inc(v_snd_2461_);
v___y_2416_ = v___x_2466_;
v___y_2417_ = v_fst_2450_;
v___y_2418_ = v_fst_2460_;
v___y_2419_ = v_fst_2474_;
v___y_2420_ = v_snd_2461_;
v___y_2421_ = v___x_2443_;
v___y_2422_ = v_snd_2461_;
v___y_2423_ = v_fst_2456_;
v___y_2424_ = v___y_2438_;
v___y_2425_ = v___y_2439_;
v___y_2426_ = v___y_2440_;
v___y_2427_ = v___y_2441_;
goto v___jp_2415_;
}
else
{
lean_object* v_fst_2475_; lean_object* v___x_2477_; uint8_t v_isShared_2478_; uint8_t v_isSharedCheck_2496_; 
v_fst_2475_ = lean_ctor_get(v___x_2471_, 0);
v_isSharedCheck_2496_ = !lean_is_exclusive(v___x_2471_);
if (v_isSharedCheck_2496_ == 0)
{
lean_object* v_unused_2497_; 
v_unused_2497_ = lean_ctor_get(v___x_2471_, 1);
lean_dec(v_unused_2497_);
v___x_2477_ = v___x_2471_;
v_isShared_2478_ = v_isSharedCheck_2496_;
goto v_resetjp_2476_;
}
else
{
lean_inc(v_fst_2475_);
lean_dec(v___x_2471_);
v___x_2477_ = lean_box(0);
v_isShared_2478_ = v_isSharedCheck_2496_;
goto v_resetjp_2476_;
}
v_resetjp_2476_:
{
lean_object* v_inheritedTraceOptions_2479_; lean_object* v___x_2480_; uint8_t v___x_2481_; 
v_inheritedTraceOptions_2479_ = lean_ctor_get(v___y_2440_, 13);
v___x_2480_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5);
v___x_2481_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2479_, v_options_2472_, v___x_2480_);
if (v___x_2481_ == 0)
{
lean_del_object(v___x_2477_);
lean_inc(v_snd_2461_);
v___y_2416_ = v___x_2466_;
v___y_2417_ = v_fst_2450_;
v___y_2418_ = v_fst_2460_;
v___y_2419_ = v_fst_2475_;
v___y_2420_ = v_snd_2461_;
v___y_2421_ = v___x_2443_;
v___y_2422_ = v_snd_2461_;
v___y_2423_ = v_fst_2456_;
v___y_2424_ = v___y_2438_;
v___y_2425_ = v___y_2439_;
v___y_2426_ = v___y_2440_;
v___y_2427_ = v___y_2441_;
goto v___jp_2415_;
}
else
{
lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2485_; 
v___x_2482_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__1);
lean_inc(v_snd_2461_);
v___x_2483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2483_, 0, v_snd_2461_);
if (v_isShared_2478_ == 0)
{
lean_ctor_set_tag(v___x_2477_, 7);
lean_ctor_set(v___x_2477_, 1, v___x_2483_);
lean_ctor_set(v___x_2477_, 0, v___x_2482_);
v___x_2485_ = v___x_2477_;
goto v_reusejp_2484_;
}
else
{
lean_object* v_reuseFailAlloc_2495_; 
v_reuseFailAlloc_2495_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2495_, 0, v___x_2482_);
lean_ctor_set(v_reuseFailAlloc_2495_, 1, v___x_2483_);
v___x_2485_ = v_reuseFailAlloc_2495_;
goto v_reusejp_2484_;
}
v_reusejp_2484_:
{
lean_object* v___x_2486_; 
v___x_2486_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1(v_cls_2436_, v___x_2485_, v___y_2438_, v___y_2439_, v___y_2440_, v___y_2441_);
if (lean_obj_tag(v___x_2486_) == 0)
{
lean_dec_ref_known(v___x_2486_, 1);
lean_inc(v_snd_2461_);
v___y_2416_ = v___x_2466_;
v___y_2417_ = v_fst_2450_;
v___y_2418_ = v_fst_2460_;
v___y_2419_ = v_fst_2475_;
v___y_2420_ = v_snd_2461_;
v___y_2421_ = v___x_2443_;
v___y_2422_ = v_snd_2461_;
v___y_2423_ = v_fst_2456_;
v___y_2424_ = v___y_2438_;
v___y_2425_ = v___y_2439_;
v___y_2426_ = v___y_2440_;
v___y_2427_ = v___y_2441_;
goto v___jp_2415_;
}
else
{
lean_object* v_a_2487_; lean_object* v___x_2489_; uint8_t v_isShared_2490_; uint8_t v_isSharedCheck_2494_; 
lean_dec(v_fst_2475_);
lean_dec_ref(v___x_2466_);
lean_dec(v_snd_2461_);
lean_dec(v_fst_2460_);
lean_dec(v_fst_2456_);
lean_dec(v_fst_2450_);
lean_dec_ref(v_givenNames_2395_);
lean_dec_ref(v_a_2391_);
v_a_2487_ = lean_ctor_get(v___x_2486_, 0);
v_isSharedCheck_2494_ = !lean_is_exclusive(v___x_2486_);
if (v_isSharedCheck_2494_ == 0)
{
v___x_2489_ = v___x_2486_;
v_isShared_2490_ = v_isSharedCheck_2494_;
goto v_resetjp_2488_;
}
else
{
lean_inc(v_a_2487_);
lean_dec(v___x_2486_);
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
}
}
}
}
}
}
else
{
lean_object* v_a_2500_; lean_object* v___x_2502_; uint8_t v_isShared_2503_; uint8_t v_isSharedCheck_2507_; 
lean_dec(v_fst_2456_);
lean_dec(v_fst_2450_);
lean_dec(v_a_2433_);
lean_dec_ref(v_givenNames_2395_);
lean_dec(v_majorFVarId_2394_);
lean_dec_ref(v_a_2391_);
v_a_2500_ = lean_ctor_get(v___x_2458_, 0);
v_isSharedCheck_2507_ = !lean_is_exclusive(v___x_2458_);
if (v_isSharedCheck_2507_ == 0)
{
v___x_2502_ = v___x_2458_;
v_isShared_2503_ = v_isSharedCheck_2507_;
goto v_resetjp_2501_;
}
else
{
lean_inc(v_a_2500_);
lean_dec(v___x_2458_);
v___x_2502_ = lean_box(0);
v_isShared_2503_ = v_isSharedCheck_2507_;
goto v_resetjp_2501_;
}
v_resetjp_2501_:
{
lean_object* v___x_2505_; 
if (v_isShared_2503_ == 0)
{
v___x_2505_ = v___x_2502_;
goto v_reusejp_2504_;
}
else
{
lean_object* v_reuseFailAlloc_2506_; 
v_reuseFailAlloc_2506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2506_, 0, v_a_2500_);
v___x_2505_ = v_reuseFailAlloc_2506_;
goto v_reusejp_2504_;
}
v_reusejp_2504_:
{
return v___x_2505_;
}
}
}
}
else
{
lean_object* v_a_2508_; lean_object* v___x_2510_; uint8_t v_isShared_2511_; uint8_t v_isSharedCheck_2515_; 
lean_dec(v_fst_2450_);
lean_dec(v_a_2433_);
lean_dec_ref(v_givenNames_2395_);
lean_dec(v_majorFVarId_2394_);
lean_dec_ref(v_a_2391_);
v_a_2508_ = lean_ctor_get(v___x_2454_, 0);
v_isSharedCheck_2515_ = !lean_is_exclusive(v___x_2454_);
if (v_isSharedCheck_2515_ == 0)
{
v___x_2510_ = v___x_2454_;
v_isShared_2511_ = v_isSharedCheck_2515_;
goto v_resetjp_2509_;
}
else
{
lean_inc(v_a_2508_);
lean_dec(v___x_2454_);
v___x_2510_ = lean_box(0);
v_isShared_2511_ = v_isSharedCheck_2515_;
goto v_resetjp_2509_;
}
v_resetjp_2509_:
{
lean_object* v___x_2513_; 
if (v_isShared_2511_ == 0)
{
v___x_2513_ = v___x_2510_;
goto v_reusejp_2512_;
}
else
{
lean_object* v_reuseFailAlloc_2514_; 
v_reuseFailAlloc_2514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2514_, 0, v_a_2508_);
v___x_2513_ = v_reuseFailAlloc_2514_;
goto v_reusejp_2512_;
}
v_reusejp_2512_:
{
return v___x_2513_;
}
}
}
}
else
{
lean_object* v_a_2516_; lean_object* v___x_2518_; uint8_t v_isShared_2519_; uint8_t v_isSharedCheck_2523_; 
lean_dec(v_a_2433_);
lean_dec_ref(v_givenNames_2395_);
lean_dec(v_majorFVarId_2394_);
lean_dec_ref(v_a_2391_);
v_a_2516_ = lean_ctor_get(v___x_2448_, 0);
v_isSharedCheck_2523_ = !lean_is_exclusive(v___x_2448_);
if (v_isSharedCheck_2523_ == 0)
{
v___x_2518_ = v___x_2448_;
v_isShared_2519_ = v_isSharedCheck_2523_;
goto v_resetjp_2517_;
}
else
{
lean_inc(v_a_2516_);
lean_dec(v___x_2448_);
v___x_2518_ = lean_box(0);
v_isShared_2519_ = v_isSharedCheck_2523_;
goto v_resetjp_2517_;
}
v_resetjp_2517_:
{
lean_object* v___x_2521_; 
if (v_isShared_2519_ == 0)
{
v___x_2521_ = v___x_2518_;
goto v_reusejp_2520_;
}
else
{
lean_object* v_reuseFailAlloc_2522_; 
v_reuseFailAlloc_2522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2522_, 0, v_a_2516_);
v___x_2521_ = v_reuseFailAlloc_2522_;
goto v_reusejp_2520_;
}
v_reusejp_2520_:
{
return v___x_2521_;
}
}
}
}
}
else
{
lean_object* v_a_2548_; lean_object* v___x_2550_; uint8_t v_isShared_2551_; uint8_t v_isSharedCheck_2555_; 
lean_dec(v_a_2433_);
lean_dec(v_recursorName_2396_);
lean_dec_ref(v_givenNames_2395_);
lean_dec(v_majorFVarId_2394_);
lean_dec(v_mvarId_2393_);
lean_dec_ref(v_a_2391_);
v_a_2548_ = lean_ctor_get(v___x_2434_, 0);
v_isSharedCheck_2555_ = !lean_is_exclusive(v___x_2434_);
if (v_isSharedCheck_2555_ == 0)
{
v___x_2550_ = v___x_2434_;
v_isShared_2551_ = v_isSharedCheck_2555_;
goto v_resetjp_2549_;
}
else
{
lean_inc(v_a_2548_);
lean_dec(v___x_2434_);
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
}
else
{
lean_object* v_a_2556_; lean_object* v___x_2558_; uint8_t v_isShared_2559_; uint8_t v_isSharedCheck_2563_; 
lean_dec(v_recursorName_2396_);
lean_dec_ref(v_givenNames_2395_);
lean_dec(v_majorFVarId_2394_);
lean_dec(v_mvarId_2393_);
lean_dec_ref(v_a_2391_);
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
v___jp_2415_:
{
size_t v_sz_2428_; lean_object* v___x_2429_; lean_object* v___f_2430_; lean_object* v___x_2431_; 
v_sz_2428_ = lean_array_size(v___y_2423_);
v___x_2429_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__3(v_sz_2428_, v___y_2421_, v___y_2423_);
v___f_2430_ = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4___lam__0___boxed), 14, 9);
lean_closure_set(v___f_2430_, 0, v___y_2420_);
lean_closure_set(v___f_2430_, 1, v___x_2414_);
lean_closure_set(v___f_2430_, 2, v___y_2418_);
lean_closure_set(v___f_2430_, 3, v_a_2391_);
lean_closure_set(v___f_2430_, 4, v___x_2429_);
lean_closure_set(v___f_2430_, 5, v_givenNames_2395_);
lean_closure_set(v___f_2430_, 6, v___y_2417_);
lean_closure_set(v___f_2430_, 7, v___y_2416_);
lean_closure_set(v___f_2430_, 8, v___y_2419_);
v___x_2431_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___redArg(v___y_2422_, v___f_2430_, v___y_2424_, v___y_2425_, v___y_2426_, v___y_2427_);
return v___x_2431_;
}
}
else
{
lean_object* v_a_2564_; lean_object* v___x_2566_; uint8_t v_isShared_2567_; uint8_t v_isSharedCheck_2571_; 
lean_dec(v_recursorName_2396_);
lean_dec_ref(v_givenNames_2395_);
lean_dec(v_majorFVarId_2394_);
lean_dec(v_mvarId_2393_);
lean_dec_ref(v_val_2392_);
lean_dec_ref(v_a_2391_);
v_a_2564_ = lean_ctor_get(v___x_2413_, 0);
v_isSharedCheck_2571_ = !lean_is_exclusive(v___x_2413_);
if (v_isSharedCheck_2571_ == 0)
{
v___x_2566_ = v___x_2413_;
v_isShared_2567_ = v_isSharedCheck_2571_;
goto v_resetjp_2565_;
}
else
{
lean_inc(v_a_2564_);
lean_dec(v___x_2413_);
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
uint8_t v_depElim_2607_; lean_object* v_paramsPos_2608_; lean_object* v___x_2609_; 
lean_dec_ref(v_x_2593_);
v_depElim_2607_ = lean_ctor_get_uint8(v_a_2589_, sizeof(void*)*8);
v_paramsPos_2608_ = lean_ctor_get(v_a_2589_, 5);
lean_inc(v_paramsPos_2608_);
lean_inc(v_mvarId_2588_);
lean_inc_ref(v_val_2587_);
v___x_2609_ = l_List_forM___at___00Lean_MVarId_induction_spec__0(v_x_2594_, v_val_2587_, v_mvarId_2588_, v_paramsPos_2608_, v___y_2596_, v___y_2597_, v___y_2598_, v___y_2599_);
lean_dec_ref(v_x_2594_);
if (lean_obj_tag(v___x_2609_) == 0)
{
lean_object* v___x_2610_; lean_object* v___y_2612_; lean_object* v___y_2613_; lean_object* v___y_2614_; lean_object* v___y_2615_; lean_object* v___y_2616_; lean_object* v___y_2617_; lean_object* v___y_2618_; size_t v___y_2619_; lean_object* v___y_2620_; lean_object* v___y_2621_; lean_object* v___y_2622_; lean_object* v___y_2623_; lean_object* v___x_2628_; 
lean_dec_ref_known(v___x_2609_, 1);
v___x_2610_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1));
lean_inc_ref(v_a_2589_);
lean_inc(v_mvarId_2588_);
v___x_2628_ = l_Lean_Meta_getMajorTypeIndices(v_mvarId_2588_, v___x_2610_, v_a_2589_, v_val_2587_, v___y_2596_, v___y_2597_, v___y_2598_, v___y_2599_);
if (lean_obj_tag(v___x_2628_) == 0)
{
lean_object* v_a_2629_; lean_object* v___x_2630_; 
v_a_2629_ = lean_ctor_get(v___x_2628_, 0);
lean_inc(v_a_2629_);
lean_dec_ref_known(v___x_2628_, 1);
lean_inc(v_mvarId_2588_);
v___x_2630_ = l_Lean_MVarId_getType(v_mvarId_2588_, v___y_2596_, v___y_2597_, v___y_2598_, v___y_2599_);
if (lean_obj_tag(v___x_2630_) == 0)
{
lean_object* v_a_2631_; lean_object* v_cls_2632_; lean_object* v___y_2634_; lean_object* v___y_2635_; lean_object* v___y_2636_; lean_object* v___y_2637_; 
v_a_2631_ = lean_ctor_get(v___x_2630_, 0);
lean_inc(v_a_2631_);
lean_dec_ref_known(v___x_2630_, 1);
v_cls_2632_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__2));
if (v_depElim_2607_ == 0)
{
lean_object* v___x_2720_; lean_object* v_a_2721_; lean_object* v___x_2723_; uint8_t v_isShared_2724_; uint8_t v_isSharedCheck_2743_; 
lean_inc(v_majorFVarId_2590_);
v___x_2720_ = l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2___redArg(v_a_2631_, v_majorFVarId_2590_, v___y_2597_);
v_a_2721_ = lean_ctor_get(v___x_2720_, 0);
v_isSharedCheck_2743_ = !lean_is_exclusive(v___x_2720_);
if (v_isSharedCheck_2743_ == 0)
{
v___x_2723_ = v___x_2720_;
v_isShared_2724_ = v_isSharedCheck_2743_;
goto v_resetjp_2722_;
}
else
{
lean_inc(v_a_2721_);
lean_dec(v___x_2720_);
v___x_2723_ = lean_box(0);
v_isShared_2724_ = v_isSharedCheck_2743_;
goto v_resetjp_2722_;
}
v_resetjp_2722_:
{
uint8_t v___x_2725_; 
v___x_2725_ = lean_unbox(v_a_2721_);
lean_dec(v_a_2721_);
if (v___x_2725_ == 0)
{
lean_del_object(v___x_2723_);
lean_dec(v_recursorName_2592_);
v___y_2634_ = v___y_2596_;
v___y_2635_ = v___y_2597_;
v___y_2636_ = v___y_2598_;
v___y_2637_ = v___y_2599_;
goto v___jp_2633_;
}
else
{
lean_object* v___x_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; lean_object* v___x_2732_; 
v___x_2726_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__3, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__3);
v___x_2727_ = l_Lean_MessageData_ofName(v_recursorName_2592_);
v___x_2728_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2728_, 0, v___x_2726_);
lean_ctor_set(v___x_2728_, 1, v___x_2727_);
v___x_2729_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__5, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__5_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__5);
v___x_2730_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2730_, 0, v___x_2728_);
lean_ctor_set(v___x_2730_, 1, v___x_2729_);
if (v_isShared_2724_ == 0)
{
lean_ctor_set_tag(v___x_2723_, 1);
lean_ctor_set(v___x_2723_, 0, v___x_2730_);
v___x_2732_ = v___x_2723_;
goto v_reusejp_2731_;
}
else
{
lean_object* v_reuseFailAlloc_2742_; 
v_reuseFailAlloc_2742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2742_, 0, v___x_2730_);
v___x_2732_ = v_reuseFailAlloc_2742_;
goto v_reusejp_2731_;
}
v_reusejp_2731_:
{
lean_object* v___x_2733_; 
lean_inc(v_mvarId_2588_);
v___x_2733_ = l_Lean_Meta_throwTacticEx___redArg(v___x_2610_, v_mvarId_2588_, v___x_2732_, v___y_2596_, v___y_2597_, v___y_2598_, v___y_2599_);
if (lean_obj_tag(v___x_2733_) == 0)
{
lean_dec_ref_known(v___x_2733_, 1);
v___y_2634_ = v___y_2596_;
v___y_2635_ = v___y_2597_;
v___y_2636_ = v___y_2598_;
v___y_2637_ = v___y_2599_;
goto v___jp_2633_;
}
else
{
lean_object* v_a_2734_; lean_object* v___x_2736_; uint8_t v_isShared_2737_; uint8_t v_isSharedCheck_2741_; 
lean_dec(v_a_2629_);
lean_dec_ref(v_givenNames_2591_);
lean_dec(v_majorFVarId_2590_);
lean_dec_ref(v_a_2589_);
lean_dec(v_mvarId_2588_);
v_a_2734_ = lean_ctor_get(v___x_2733_, 0);
v_isSharedCheck_2741_ = !lean_is_exclusive(v___x_2733_);
if (v_isSharedCheck_2741_ == 0)
{
v___x_2736_ = v___x_2733_;
v_isShared_2737_ = v_isSharedCheck_2741_;
goto v_resetjp_2735_;
}
else
{
lean_inc(v_a_2734_);
lean_dec(v___x_2733_);
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
}
}
}
else
{
lean_dec(v_a_2631_);
lean_dec(v_recursorName_2592_);
v___y_2634_ = v___y_2596_;
v___y_2635_ = v___y_2597_;
v___y_2636_ = v___y_2598_;
v___y_2637_ = v___y_2599_;
goto v___jp_2633_;
}
v___jp_2633_:
{
size_t v_sz_2638_; size_t v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; uint8_t v___x_2642_; uint8_t v___x_2643_; lean_object* v___x_2644_; 
v_sz_2638_ = lean_array_size(v_a_2629_);
v___x_2639_ = ((size_t)0ULL);
lean_inc(v_a_2629_);
v___x_2640_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_induction_spec__1(v_sz_2638_, v___x_2639_, v_a_2629_);
lean_inc(v_majorFVarId_2590_);
v___x_2641_ = lean_array_push(v___x_2640_, v_majorFVarId_2590_);
v___x_2642_ = 1;
v___x_2643_ = 0;
v___x_2644_ = l_Lean_MVarId_revert(v_mvarId_2588_, v___x_2641_, v___x_2642_, v___x_2643_, v___y_2634_, v___y_2635_, v___y_2636_, v___y_2637_);
if (lean_obj_tag(v___x_2644_) == 0)
{
lean_object* v_a_2645_; lean_object* v_fst_2646_; lean_object* v_snd_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; 
v_a_2645_ = lean_ctor_get(v___x_2644_, 0);
lean_inc(v_a_2645_);
lean_dec_ref_known(v___x_2644_, 1);
v_fst_2646_ = lean_ctor_get(v_a_2645_, 0);
lean_inc(v_fst_2646_);
v_snd_2647_ = lean_ctor_get(v_a_2645_, 1);
lean_inc(v_snd_2647_);
lean_dec(v_a_2645_);
v___x_2648_ = lean_array_get_size(v_a_2629_);
v___x_2649_ = lean_box(0);
v___x_2650_ = l_Lean_Meta_introNCore(v_snd_2647_, v___x_2648_, v___x_2649_, v___x_2643_, v___x_2642_, v___y_2634_, v___y_2635_, v___y_2636_, v___y_2637_);
if (lean_obj_tag(v___x_2650_) == 0)
{
lean_object* v_a_2651_; lean_object* v_fst_2652_; lean_object* v_snd_2653_; lean_object* v___x_2654_; 
v_a_2651_ = lean_ctor_get(v___x_2650_, 0);
lean_inc(v_a_2651_);
lean_dec_ref_known(v___x_2650_, 1);
v_fst_2652_ = lean_ctor_get(v_a_2651_, 0);
lean_inc(v_fst_2652_);
v_snd_2653_ = lean_ctor_get(v_a_2651_, 1);
lean_inc(v_snd_2653_);
lean_dec(v_a_2651_);
v___x_2654_ = l_Lean_Meta_intro1Core(v_snd_2653_, v___x_2642_, v___y_2634_, v___y_2635_, v___y_2636_, v___y_2637_);
if (lean_obj_tag(v___x_2654_) == 0)
{
lean_object* v_a_2655_; lean_object* v_fst_2656_; lean_object* v_snd_2657_; lean_object* v___x_2659_; uint8_t v_isShared_2660_; uint8_t v_isSharedCheck_2695_; 
v_a_2655_ = lean_ctor_get(v___x_2654_, 0);
lean_inc(v_a_2655_);
lean_dec_ref_known(v___x_2654_, 1);
v_fst_2656_ = lean_ctor_get(v_a_2655_, 0);
v_snd_2657_ = lean_ctor_get(v_a_2655_, 1);
v_isSharedCheck_2695_ = !lean_is_exclusive(v_a_2655_);
if (v_isSharedCheck_2695_ == 0)
{
v___x_2659_ = v_a_2655_;
v_isShared_2660_ = v_isSharedCheck_2695_;
goto v_resetjp_2658_;
}
else
{
lean_inc(v_snd_2657_);
lean_inc(v_fst_2656_);
lean_dec(v_a_2655_);
v___x_2659_ = lean_box(0);
v_isShared_2660_ = v_isSharedCheck_2695_;
goto v_resetjp_2658_;
}
v_resetjp_2658_:
{
lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2666_; 
v___x_2661_ = lean_box(0);
lean_inc(v_fst_2656_);
v___x_2662_ = l_Lean_mkFVar(v_fst_2656_);
lean_inc_ref(v___x_2662_);
v___x_2663_ = l_Lean_Meta_FVarSubst_insert(v___x_2661_, v_majorFVarId_2590_, v___x_2662_);
v___x_2664_ = lean_unsigned_to_nat(0u);
if (v_isShared_2660_ == 0)
{
lean_ctor_set(v___x_2659_, 1, v___x_2664_);
lean_ctor_set(v___x_2659_, 0, v___x_2663_);
v___x_2666_ = v___x_2659_;
goto v_reusejp_2665_;
}
else
{
lean_object* v_reuseFailAlloc_2694_; 
v_reuseFailAlloc_2694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2694_, 0, v___x_2663_);
lean_ctor_set(v_reuseFailAlloc_2694_, 1, v___x_2664_);
v___x_2666_ = v_reuseFailAlloc_2694_;
goto v_reusejp_2665_;
}
v_reusejp_2665_:
{
lean_object* v___x_2667_; lean_object* v_options_2668_; uint8_t v_hasTrace_2669_; 
v___x_2667_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_induction_spec__2(v_fst_2652_, v_a_2629_, v_sz_2638_, v___x_2639_, v___x_2666_);
lean_dec(v_a_2629_);
v_options_2668_ = lean_ctor_get(v___y_2636_, 2);
v_hasTrace_2669_ = lean_ctor_get_uint8(v_options_2668_, sizeof(void*)*1);
if (v_hasTrace_2669_ == 0)
{
lean_object* v_fst_2670_; 
v_fst_2670_ = lean_ctor_get(v___x_2667_, 0);
lean_inc(v_fst_2670_);
lean_dec_ref(v___x_2667_);
lean_inc(v_snd_2657_);
v___y_2612_ = v___x_2662_;
v___y_2613_ = v_fst_2670_;
v___y_2614_ = v_snd_2657_;
v___y_2615_ = v_fst_2656_;
v___y_2616_ = v_fst_2646_;
v___y_2617_ = v_fst_2652_;
v___y_2618_ = v_snd_2657_;
v___y_2619_ = v___x_2639_;
v___y_2620_ = v___y_2634_;
v___y_2621_ = v___y_2635_;
v___y_2622_ = v___y_2636_;
v___y_2623_ = v___y_2637_;
goto v___jp_2611_;
}
else
{
lean_object* v_fst_2671_; lean_object* v___x_2673_; uint8_t v_isShared_2674_; uint8_t v_isSharedCheck_2692_; 
v_fst_2671_ = lean_ctor_get(v___x_2667_, 0);
v_isSharedCheck_2692_ = !lean_is_exclusive(v___x_2667_);
if (v_isSharedCheck_2692_ == 0)
{
lean_object* v_unused_2693_; 
v_unused_2693_ = lean_ctor_get(v___x_2667_, 1);
lean_dec(v_unused_2693_);
v___x_2673_ = v___x_2667_;
v_isShared_2674_ = v_isSharedCheck_2692_;
goto v_resetjp_2672_;
}
else
{
lean_inc(v_fst_2671_);
lean_dec(v___x_2667_);
v___x_2673_ = lean_box(0);
v_isShared_2674_ = v_isSharedCheck_2692_;
goto v_resetjp_2672_;
}
v_resetjp_2672_:
{
lean_object* v_inheritedTraceOptions_2675_; lean_object* v___x_2676_; uint8_t v___x_2677_; 
v_inheritedTraceOptions_2675_ = lean_ctor_get(v___y_2636_, 13);
v___x_2676_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5);
v___x_2677_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2675_, v_options_2668_, v___x_2676_);
if (v___x_2677_ == 0)
{
lean_del_object(v___x_2673_);
lean_inc(v_snd_2657_);
v___y_2612_ = v___x_2662_;
v___y_2613_ = v_fst_2671_;
v___y_2614_ = v_snd_2657_;
v___y_2615_ = v_fst_2656_;
v___y_2616_ = v_fst_2646_;
v___y_2617_ = v_fst_2652_;
v___y_2618_ = v_snd_2657_;
v___y_2619_ = v___x_2639_;
v___y_2620_ = v___y_2634_;
v___y_2621_ = v___y_2635_;
v___y_2622_ = v___y_2636_;
v___y_2623_ = v___y_2637_;
goto v___jp_2611_;
}
else
{
lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2681_; 
v___x_2678_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__1);
lean_inc(v_snd_2657_);
v___x_2679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2679_, 0, v_snd_2657_);
if (v_isShared_2674_ == 0)
{
lean_ctor_set_tag(v___x_2673_, 7);
lean_ctor_set(v___x_2673_, 1, v___x_2679_);
lean_ctor_set(v___x_2673_, 0, v___x_2678_);
v___x_2681_ = v___x_2673_;
goto v_reusejp_2680_;
}
else
{
lean_object* v_reuseFailAlloc_2691_; 
v_reuseFailAlloc_2691_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2691_, 0, v___x_2678_);
lean_ctor_set(v_reuseFailAlloc_2691_, 1, v___x_2679_);
v___x_2681_ = v_reuseFailAlloc_2691_;
goto v_reusejp_2680_;
}
v_reusejp_2680_:
{
lean_object* v___x_2682_; 
v___x_2682_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1(v_cls_2632_, v___x_2681_, v___y_2634_, v___y_2635_, v___y_2636_, v___y_2637_);
if (lean_obj_tag(v___x_2682_) == 0)
{
lean_dec_ref_known(v___x_2682_, 1);
lean_inc(v_snd_2657_);
v___y_2612_ = v___x_2662_;
v___y_2613_ = v_fst_2671_;
v___y_2614_ = v_snd_2657_;
v___y_2615_ = v_fst_2656_;
v___y_2616_ = v_fst_2646_;
v___y_2617_ = v_fst_2652_;
v___y_2618_ = v_snd_2657_;
v___y_2619_ = v___x_2639_;
v___y_2620_ = v___y_2634_;
v___y_2621_ = v___y_2635_;
v___y_2622_ = v___y_2636_;
v___y_2623_ = v___y_2637_;
goto v___jp_2611_;
}
else
{
lean_object* v_a_2683_; lean_object* v___x_2685_; uint8_t v_isShared_2686_; uint8_t v_isSharedCheck_2690_; 
lean_dec(v_fst_2671_);
lean_dec_ref(v___x_2662_);
lean_dec(v_snd_2657_);
lean_dec(v_fst_2656_);
lean_dec(v_fst_2652_);
lean_dec(v_fst_2646_);
lean_dec_ref(v_givenNames_2591_);
lean_dec_ref(v_a_2589_);
v_a_2683_ = lean_ctor_get(v___x_2682_, 0);
v_isSharedCheck_2690_ = !lean_is_exclusive(v___x_2682_);
if (v_isSharedCheck_2690_ == 0)
{
v___x_2685_ = v___x_2682_;
v_isShared_2686_ = v_isSharedCheck_2690_;
goto v_resetjp_2684_;
}
else
{
lean_inc(v_a_2683_);
lean_dec(v___x_2682_);
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
}
}
}
}
}
}
else
{
lean_object* v_a_2696_; lean_object* v___x_2698_; uint8_t v_isShared_2699_; uint8_t v_isSharedCheck_2703_; 
lean_dec(v_fst_2652_);
lean_dec(v_fst_2646_);
lean_dec(v_a_2629_);
lean_dec_ref(v_givenNames_2591_);
lean_dec(v_majorFVarId_2590_);
lean_dec_ref(v_a_2589_);
v_a_2696_ = lean_ctor_get(v___x_2654_, 0);
v_isSharedCheck_2703_ = !lean_is_exclusive(v___x_2654_);
if (v_isSharedCheck_2703_ == 0)
{
v___x_2698_ = v___x_2654_;
v_isShared_2699_ = v_isSharedCheck_2703_;
goto v_resetjp_2697_;
}
else
{
lean_inc(v_a_2696_);
lean_dec(v___x_2654_);
v___x_2698_ = lean_box(0);
v_isShared_2699_ = v_isSharedCheck_2703_;
goto v_resetjp_2697_;
}
v_resetjp_2697_:
{
lean_object* v___x_2701_; 
if (v_isShared_2699_ == 0)
{
v___x_2701_ = v___x_2698_;
goto v_reusejp_2700_;
}
else
{
lean_object* v_reuseFailAlloc_2702_; 
v_reuseFailAlloc_2702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2702_, 0, v_a_2696_);
v___x_2701_ = v_reuseFailAlloc_2702_;
goto v_reusejp_2700_;
}
v_reusejp_2700_:
{
return v___x_2701_;
}
}
}
}
else
{
lean_object* v_a_2704_; lean_object* v___x_2706_; uint8_t v_isShared_2707_; uint8_t v_isSharedCheck_2711_; 
lean_dec(v_fst_2646_);
lean_dec(v_a_2629_);
lean_dec_ref(v_givenNames_2591_);
lean_dec(v_majorFVarId_2590_);
lean_dec_ref(v_a_2589_);
v_a_2704_ = lean_ctor_get(v___x_2650_, 0);
v_isSharedCheck_2711_ = !lean_is_exclusive(v___x_2650_);
if (v_isSharedCheck_2711_ == 0)
{
v___x_2706_ = v___x_2650_;
v_isShared_2707_ = v_isSharedCheck_2711_;
goto v_resetjp_2705_;
}
else
{
lean_inc(v_a_2704_);
lean_dec(v___x_2650_);
v___x_2706_ = lean_box(0);
v_isShared_2707_ = v_isSharedCheck_2711_;
goto v_resetjp_2705_;
}
v_resetjp_2705_:
{
lean_object* v___x_2709_; 
if (v_isShared_2707_ == 0)
{
v___x_2709_ = v___x_2706_;
goto v_reusejp_2708_;
}
else
{
lean_object* v_reuseFailAlloc_2710_; 
v_reuseFailAlloc_2710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2710_, 0, v_a_2704_);
v___x_2709_ = v_reuseFailAlloc_2710_;
goto v_reusejp_2708_;
}
v_reusejp_2708_:
{
return v___x_2709_;
}
}
}
}
else
{
lean_object* v_a_2712_; lean_object* v___x_2714_; uint8_t v_isShared_2715_; uint8_t v_isSharedCheck_2719_; 
lean_dec(v_a_2629_);
lean_dec_ref(v_givenNames_2591_);
lean_dec(v_majorFVarId_2590_);
lean_dec_ref(v_a_2589_);
v_a_2712_ = lean_ctor_get(v___x_2644_, 0);
v_isSharedCheck_2719_ = !lean_is_exclusive(v___x_2644_);
if (v_isSharedCheck_2719_ == 0)
{
v___x_2714_ = v___x_2644_;
v_isShared_2715_ = v_isSharedCheck_2719_;
goto v_resetjp_2713_;
}
else
{
lean_inc(v_a_2712_);
lean_dec(v___x_2644_);
v___x_2714_ = lean_box(0);
v_isShared_2715_ = v_isSharedCheck_2719_;
goto v_resetjp_2713_;
}
v_resetjp_2713_:
{
lean_object* v___x_2717_; 
if (v_isShared_2715_ == 0)
{
v___x_2717_ = v___x_2714_;
goto v_reusejp_2716_;
}
else
{
lean_object* v_reuseFailAlloc_2718_; 
v_reuseFailAlloc_2718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2718_, 0, v_a_2712_);
v___x_2717_ = v_reuseFailAlloc_2718_;
goto v_reusejp_2716_;
}
v_reusejp_2716_:
{
return v___x_2717_;
}
}
}
}
}
else
{
lean_object* v_a_2744_; lean_object* v___x_2746_; uint8_t v_isShared_2747_; uint8_t v_isSharedCheck_2751_; 
lean_dec(v_a_2629_);
lean_dec(v_recursorName_2592_);
lean_dec_ref(v_givenNames_2591_);
lean_dec(v_majorFVarId_2590_);
lean_dec_ref(v_a_2589_);
lean_dec(v_mvarId_2588_);
v_a_2744_ = lean_ctor_get(v___x_2630_, 0);
v_isSharedCheck_2751_ = !lean_is_exclusive(v___x_2630_);
if (v_isSharedCheck_2751_ == 0)
{
v___x_2746_ = v___x_2630_;
v_isShared_2747_ = v_isSharedCheck_2751_;
goto v_resetjp_2745_;
}
else
{
lean_inc(v_a_2744_);
lean_dec(v___x_2630_);
v___x_2746_ = lean_box(0);
v_isShared_2747_ = v_isSharedCheck_2751_;
goto v_resetjp_2745_;
}
v_resetjp_2745_:
{
lean_object* v___x_2749_; 
if (v_isShared_2747_ == 0)
{
v___x_2749_ = v___x_2746_;
goto v_reusejp_2748_;
}
else
{
lean_object* v_reuseFailAlloc_2750_; 
v_reuseFailAlloc_2750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2750_, 0, v_a_2744_);
v___x_2749_ = v_reuseFailAlloc_2750_;
goto v_reusejp_2748_;
}
v_reusejp_2748_:
{
return v___x_2749_;
}
}
}
}
else
{
lean_object* v_a_2752_; lean_object* v___x_2754_; uint8_t v_isShared_2755_; uint8_t v_isSharedCheck_2759_; 
lean_dec(v_recursorName_2592_);
lean_dec_ref(v_givenNames_2591_);
lean_dec(v_majorFVarId_2590_);
lean_dec_ref(v_a_2589_);
lean_dec(v_mvarId_2588_);
v_a_2752_ = lean_ctor_get(v___x_2628_, 0);
v_isSharedCheck_2759_ = !lean_is_exclusive(v___x_2628_);
if (v_isSharedCheck_2759_ == 0)
{
v___x_2754_ = v___x_2628_;
v_isShared_2755_ = v_isSharedCheck_2759_;
goto v_resetjp_2753_;
}
else
{
lean_inc(v_a_2752_);
lean_dec(v___x_2628_);
v___x_2754_ = lean_box(0);
v_isShared_2755_ = v_isSharedCheck_2759_;
goto v_resetjp_2753_;
}
v_resetjp_2753_:
{
lean_object* v___x_2757_; 
if (v_isShared_2755_ == 0)
{
v___x_2757_ = v___x_2754_;
goto v_reusejp_2756_;
}
else
{
lean_object* v_reuseFailAlloc_2758_; 
v_reuseFailAlloc_2758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2758_, 0, v_a_2752_);
v___x_2757_ = v_reuseFailAlloc_2758_;
goto v_reusejp_2756_;
}
v_reusejp_2756_:
{
return v___x_2757_;
}
}
}
v___jp_2611_:
{
size_t v_sz_2624_; lean_object* v___x_2625_; lean_object* v___f_2626_; lean_object* v___x_2627_; 
v_sz_2624_ = lean_array_size(v___y_2617_);
v___x_2625_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__3(v_sz_2624_, v___y_2619_, v___y_2617_);
v___f_2626_ = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4___lam__0___boxed), 14, 9);
lean_closure_set(v___f_2626_, 0, v___y_2614_);
lean_closure_set(v___f_2626_, 1, v___x_2610_);
lean_closure_set(v___f_2626_, 2, v___y_2615_);
lean_closure_set(v___f_2626_, 3, v_a_2589_);
lean_closure_set(v___f_2626_, 4, v___x_2625_);
lean_closure_set(v___f_2626_, 5, v_givenNames_2591_);
lean_closure_set(v___f_2626_, 6, v___y_2616_);
lean_closure_set(v___f_2626_, 7, v___y_2612_);
lean_closure_set(v___f_2626_, 8, v___y_2613_);
v___x_2627_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___redArg(v___y_2618_, v___f_2626_, v___y_2620_, v___y_2621_, v___y_2622_, v___y_2623_);
return v___x_2627_;
}
}
else
{
lean_object* v_a_2760_; lean_object* v___x_2762_; uint8_t v_isShared_2763_; uint8_t v_isSharedCheck_2767_; 
lean_dec(v_recursorName_2592_);
lean_dec_ref(v_givenNames_2591_);
lean_dec(v_majorFVarId_2590_);
lean_dec_ref(v_a_2589_);
lean_dec(v_mvarId_2588_);
lean_dec_ref(v_val_2587_);
v_a_2760_ = lean_ctor_get(v___x_2609_, 0);
v_isSharedCheck_2767_ = !lean_is_exclusive(v___x_2609_);
if (v_isSharedCheck_2767_ == 0)
{
v___x_2762_ = v___x_2609_;
v_isShared_2763_ = v_isSharedCheck_2767_;
goto v_resetjp_2761_;
}
else
{
lean_inc(v_a_2760_);
lean_dec(v___x_2609_);
v___x_2762_ = lean_box(0);
v_isShared_2763_ = v_isSharedCheck_2767_;
goto v_resetjp_2761_;
}
v_resetjp_2761_:
{
lean_object* v___x_2765_; 
if (v_isShared_2763_ == 0)
{
v___x_2765_ = v___x_2762_;
goto v_reusejp_2764_;
}
else
{
lean_object* v_reuseFailAlloc_2766_; 
v_reuseFailAlloc_2766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2766_, 0, v_a_2760_);
v___x_2765_ = v_reuseFailAlloc_2766_;
goto v_reusejp_2764_;
}
v_reusejp_2764_:
{
return v___x_2765_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4___boxed(lean_object* v_val_2768_, lean_object* v_mvarId_2769_, lean_object* v_a_2770_, lean_object* v_majorFVarId_2771_, lean_object* v_givenNames_2772_, lean_object* v_recursorName_2773_, lean_object* v_x_2774_, lean_object* v_x_2775_, lean_object* v_x_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_, lean_object* v___y_2780_, lean_object* v___y_2781_){
_start:
{
lean_object* v_res_2782_; 
v_res_2782_ = l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4(v_val_2768_, v_mvarId_2769_, v_a_2770_, v_majorFVarId_2771_, v_givenNames_2772_, v_recursorName_2773_, v_x_2774_, v_x_2775_, v_x_2776_, v___y_2777_, v___y_2778_, v___y_2779_, v___y_2780_);
lean_dec(v___y_2780_);
lean_dec_ref(v___y_2779_);
lean_dec(v___y_2778_);
lean_dec_ref(v___y_2777_);
lean_dec(v_x_2776_);
return v_res_2782_;
}
}
static lean_object* _init_l_Lean_MVarId_induction___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2784_; lean_object* v___x_2785_; 
v___x_2784_ = ((lean_object*)(l_Lean_MVarId_induction___lam__0___closed__0));
v___x_2785_ = l_Lean_stringToMessageData(v___x_2784_);
return v___x_2785_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_induction___lam__0(lean_object* v___x_2786_, lean_object* v_mvarId_2787_, lean_object* v_majorFVarId_2788_, lean_object* v_recursorName_2789_, lean_object* v_givenNames_2790_, lean_object* v_cls_2791_, lean_object* v___y_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_){
_start:
{
lean_object* v___y_2798_; lean_object* v___y_2799_; lean_object* v___y_2800_; lean_object* v___y_2801_; lean_object* v_options_2853_; uint8_t v_hasTrace_2854_; 
v_options_2853_ = lean_ctor_get(v___y_2794_, 2);
v_hasTrace_2854_ = lean_ctor_get_uint8(v_options_2853_, sizeof(void*)*1);
if (v_hasTrace_2854_ == 0)
{
lean_dec(v_cls_2791_);
v___y_2798_ = v___y_2792_;
v___y_2799_ = v___y_2793_;
v___y_2800_ = v___y_2794_;
v___y_2801_ = v___y_2795_;
goto v___jp_2797_;
}
else
{
lean_object* v_inheritedTraceOptions_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; uint8_t v___x_2858_; 
v_inheritedTraceOptions_2855_ = lean_ctor_get(v___y_2794_, 13);
v___x_2856_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__4));
lean_inc(v_cls_2791_);
v___x_2857_ = l_Lean_Name_append(v___x_2856_, v_cls_2791_);
v___x_2858_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2855_, v_options_2853_, v___x_2857_);
lean_dec(v___x_2857_);
if (v___x_2858_ == 0)
{
lean_dec(v_cls_2791_);
v___y_2798_ = v___y_2792_;
v___y_2799_ = v___y_2793_;
v___y_2800_ = v___y_2794_;
v___y_2801_ = v___y_2795_;
goto v___jp_2797_;
}
else
{
lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; 
v___x_2859_ = lean_obj_once(&l_Lean_MVarId_induction___lam__0___closed__1, &l_Lean_MVarId_induction___lam__0___closed__1_once, _init_l_Lean_MVarId_induction___lam__0___closed__1);
lean_inc(v_mvarId_2787_);
v___x_2860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2860_, 0, v_mvarId_2787_);
v___x_2861_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2861_, 0, v___x_2859_);
lean_ctor_set(v___x_2861_, 1, v___x_2860_);
v___x_2862_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1(v_cls_2791_, v___x_2861_, v___y_2792_, v___y_2793_, v___y_2794_, v___y_2795_);
if (lean_obj_tag(v___x_2862_) == 0)
{
lean_dec_ref_known(v___x_2862_, 1);
v___y_2798_ = v___y_2792_;
v___y_2799_ = v___y_2793_;
v___y_2800_ = v___y_2794_;
v___y_2801_ = v___y_2795_;
goto v___jp_2797_;
}
else
{
lean_object* v_a_2863_; lean_object* v___x_2865_; uint8_t v_isShared_2866_; uint8_t v_isSharedCheck_2870_; 
lean_dec_ref(v_givenNames_2790_);
lean_dec(v_recursorName_2789_);
lean_dec(v_majorFVarId_2788_);
lean_dec(v_mvarId_2787_);
lean_dec_ref(v___x_2786_);
v_a_2863_ = lean_ctor_get(v___x_2862_, 0);
v_isSharedCheck_2870_ = !lean_is_exclusive(v___x_2862_);
if (v_isSharedCheck_2870_ == 0)
{
v___x_2865_ = v___x_2862_;
v_isShared_2866_ = v_isSharedCheck_2870_;
goto v_resetjp_2864_;
}
else
{
lean_inc(v_a_2863_);
lean_dec(v___x_2862_);
v___x_2865_ = lean_box(0);
v_isShared_2866_ = v_isSharedCheck_2870_;
goto v_resetjp_2864_;
}
v_resetjp_2864_:
{
lean_object* v___x_2868_; 
if (v_isShared_2866_ == 0)
{
v___x_2868_ = v___x_2865_;
goto v_reusejp_2867_;
}
else
{
lean_object* v_reuseFailAlloc_2869_; 
v_reuseFailAlloc_2869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2869_, 0, v_a_2863_);
v___x_2868_ = v_reuseFailAlloc_2869_;
goto v_reusejp_2867_;
}
v_reusejp_2867_:
{
return v___x_2868_;
}
}
}
}
}
v___jp_2797_:
{
lean_object* v___x_2802_; lean_object* v___x_2803_; 
v___x_2802_ = l_Lean_Name_mkStr1(v___x_2786_);
lean_inc(v___x_2802_);
lean_inc(v_mvarId_2787_);
v___x_2803_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_2787_, v___x_2802_, v___y_2798_, v___y_2799_, v___y_2800_, v___y_2801_);
if (lean_obj_tag(v___x_2803_) == 0)
{
lean_object* v___x_2804_; 
lean_dec_ref_known(v___x_2803_, 1);
lean_inc(v_majorFVarId_2788_);
v___x_2804_ = l_Lean_FVarId_getDecl___redArg(v_majorFVarId_2788_, v___y_2798_, v___y_2800_, v___y_2801_);
if (lean_obj_tag(v___x_2804_) == 0)
{
lean_object* v_a_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; 
v_a_2805_ = lean_ctor_get(v___x_2804_, 0);
lean_inc(v_a_2805_);
lean_dec_ref_known(v___x_2804_, 1);
v___x_2806_ = lean_box(0);
lean_inc(v_recursorName_2789_);
v___x_2807_ = l_Lean_Meta_mkRecursorInfo(v_recursorName_2789_, v___x_2806_, v___y_2798_, v___y_2799_, v___y_2800_, v___y_2801_);
if (lean_obj_tag(v___x_2807_) == 0)
{
lean_object* v_a_2808_; lean_object* v_typeName_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; 
v_a_2808_ = lean_ctor_get(v___x_2807_, 0);
lean_inc(v_a_2808_);
lean_dec_ref_known(v___x_2807_, 1);
v_typeName_2809_ = lean_ctor_get(v_a_2808_, 1);
v___x_2810_ = l_Lean_LocalDecl_type(v_a_2805_);
lean_dec(v_a_2805_);
lean_inc_ref(v___x_2810_);
v___x_2811_ = l_Lean_Meta_whnfUntil(v___x_2810_, v_typeName_2809_, v___y_2798_, v___y_2799_, v___y_2800_, v___y_2801_);
if (lean_obj_tag(v___x_2811_) == 0)
{
lean_object* v_a_2812_; 
v_a_2812_ = lean_ctor_get(v___x_2811_, 0);
lean_inc(v_a_2812_);
lean_dec_ref_known(v___x_2811_, 1);
if (lean_obj_tag(v_a_2812_) == 1)
{
lean_object* v_val_2813_; lean_object* v_dummy_2814_; lean_object* v_nargs_2815_; lean_object* v___x_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; 
lean_dec_ref(v___x_2810_);
lean_dec(v___x_2802_);
v_val_2813_ = lean_ctor_get(v_a_2812_, 0);
lean_inc_n(v_val_2813_, 2);
lean_dec_ref_known(v_a_2812_, 1);
v_dummy_2814_ = lean_obj_once(&l_Lean_Meta_getMajorTypeIndices___closed__0, &l_Lean_Meta_getMajorTypeIndices___closed__0_once, _init_l_Lean_Meta_getMajorTypeIndices___closed__0);
v_nargs_2815_ = l_Lean_Expr_getAppNumArgs(v_val_2813_);
lean_inc(v_nargs_2815_);
v___x_2816_ = lean_mk_array(v_nargs_2815_, v_dummy_2814_);
v___x_2817_ = lean_unsigned_to_nat(1u);
v___x_2818_ = lean_nat_sub(v_nargs_2815_, v___x_2817_);
lean_dec(v_nargs_2815_);
v___x_2819_ = l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4(v_val_2813_, v_mvarId_2787_, v_a_2808_, v_majorFVarId_2788_, v_givenNames_2790_, v_recursorName_2789_, v_val_2813_, v___x_2816_, v___x_2818_, v___y_2798_, v___y_2799_, v___y_2800_, v___y_2801_);
lean_dec(v___x_2818_);
return v___x_2819_;
}
else
{
lean_object* v___x_2820_; 
lean_dec(v_a_2812_);
lean_dec(v_a_2808_);
lean_dec_ref(v_givenNames_2790_);
lean_dec(v_recursorName_2789_);
lean_dec(v_majorFVarId_2788_);
v___x_2820_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg(v___x_2802_, v_mvarId_2787_, v___x_2810_, v___y_2798_, v___y_2799_, v___y_2800_, v___y_2801_);
return v___x_2820_;
}
}
else
{
lean_object* v_a_2821_; lean_object* v___x_2823_; uint8_t v_isShared_2824_; uint8_t v_isSharedCheck_2828_; 
lean_dec_ref(v___x_2810_);
lean_dec(v_a_2808_);
lean_dec(v___x_2802_);
lean_dec_ref(v_givenNames_2790_);
lean_dec(v_recursorName_2789_);
lean_dec(v_majorFVarId_2788_);
lean_dec(v_mvarId_2787_);
v_a_2821_ = lean_ctor_get(v___x_2811_, 0);
v_isSharedCheck_2828_ = !lean_is_exclusive(v___x_2811_);
if (v_isSharedCheck_2828_ == 0)
{
v___x_2823_ = v___x_2811_;
v_isShared_2824_ = v_isSharedCheck_2828_;
goto v_resetjp_2822_;
}
else
{
lean_inc(v_a_2821_);
lean_dec(v___x_2811_);
v___x_2823_ = lean_box(0);
v_isShared_2824_ = v_isSharedCheck_2828_;
goto v_resetjp_2822_;
}
v_resetjp_2822_:
{
lean_object* v___x_2826_; 
if (v_isShared_2824_ == 0)
{
v___x_2826_ = v___x_2823_;
goto v_reusejp_2825_;
}
else
{
lean_object* v_reuseFailAlloc_2827_; 
v_reuseFailAlloc_2827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2827_, 0, v_a_2821_);
v___x_2826_ = v_reuseFailAlloc_2827_;
goto v_reusejp_2825_;
}
v_reusejp_2825_:
{
return v___x_2826_;
}
}
}
}
else
{
lean_object* v_a_2829_; lean_object* v___x_2831_; uint8_t v_isShared_2832_; uint8_t v_isSharedCheck_2836_; 
lean_dec(v_a_2805_);
lean_dec(v___x_2802_);
lean_dec_ref(v_givenNames_2790_);
lean_dec(v_recursorName_2789_);
lean_dec(v_majorFVarId_2788_);
lean_dec(v_mvarId_2787_);
v_a_2829_ = lean_ctor_get(v___x_2807_, 0);
v_isSharedCheck_2836_ = !lean_is_exclusive(v___x_2807_);
if (v_isSharedCheck_2836_ == 0)
{
v___x_2831_ = v___x_2807_;
v_isShared_2832_ = v_isSharedCheck_2836_;
goto v_resetjp_2830_;
}
else
{
lean_inc(v_a_2829_);
lean_dec(v___x_2807_);
v___x_2831_ = lean_box(0);
v_isShared_2832_ = v_isSharedCheck_2836_;
goto v_resetjp_2830_;
}
v_resetjp_2830_:
{
lean_object* v___x_2834_; 
if (v_isShared_2832_ == 0)
{
v___x_2834_ = v___x_2831_;
goto v_reusejp_2833_;
}
else
{
lean_object* v_reuseFailAlloc_2835_; 
v_reuseFailAlloc_2835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2835_, 0, v_a_2829_);
v___x_2834_ = v_reuseFailAlloc_2835_;
goto v_reusejp_2833_;
}
v_reusejp_2833_:
{
return v___x_2834_;
}
}
}
}
else
{
lean_object* v_a_2837_; lean_object* v___x_2839_; uint8_t v_isShared_2840_; uint8_t v_isSharedCheck_2844_; 
lean_dec(v___x_2802_);
lean_dec_ref(v_givenNames_2790_);
lean_dec(v_recursorName_2789_);
lean_dec(v_majorFVarId_2788_);
lean_dec(v_mvarId_2787_);
v_a_2837_ = lean_ctor_get(v___x_2804_, 0);
v_isSharedCheck_2844_ = !lean_is_exclusive(v___x_2804_);
if (v_isSharedCheck_2844_ == 0)
{
v___x_2839_ = v___x_2804_;
v_isShared_2840_ = v_isSharedCheck_2844_;
goto v_resetjp_2838_;
}
else
{
lean_inc(v_a_2837_);
lean_dec(v___x_2804_);
v___x_2839_ = lean_box(0);
v_isShared_2840_ = v_isSharedCheck_2844_;
goto v_resetjp_2838_;
}
v_resetjp_2838_:
{
lean_object* v___x_2842_; 
if (v_isShared_2840_ == 0)
{
v___x_2842_ = v___x_2839_;
goto v_reusejp_2841_;
}
else
{
lean_object* v_reuseFailAlloc_2843_; 
v_reuseFailAlloc_2843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2843_, 0, v_a_2837_);
v___x_2842_ = v_reuseFailAlloc_2843_;
goto v_reusejp_2841_;
}
v_reusejp_2841_:
{
return v___x_2842_;
}
}
}
}
else
{
lean_object* v_a_2845_; lean_object* v___x_2847_; uint8_t v_isShared_2848_; uint8_t v_isSharedCheck_2852_; 
lean_dec(v___x_2802_);
lean_dec_ref(v_givenNames_2790_);
lean_dec(v_recursorName_2789_);
lean_dec(v_majorFVarId_2788_);
lean_dec(v_mvarId_2787_);
v_a_2845_ = lean_ctor_get(v___x_2803_, 0);
v_isSharedCheck_2852_ = !lean_is_exclusive(v___x_2803_);
if (v_isSharedCheck_2852_ == 0)
{
v___x_2847_ = v___x_2803_;
v_isShared_2848_ = v_isSharedCheck_2852_;
goto v_resetjp_2846_;
}
else
{
lean_inc(v_a_2845_);
lean_dec(v___x_2803_);
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
}
LEAN_EXPORT lean_object* l_Lean_MVarId_induction___lam__0___boxed(lean_object* v___x_2871_, lean_object* v_mvarId_2872_, lean_object* v_majorFVarId_2873_, lean_object* v_recursorName_2874_, lean_object* v_givenNames_2875_, lean_object* v_cls_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_){
_start:
{
lean_object* v_res_2882_; 
v_res_2882_ = l_Lean_MVarId_induction___lam__0(v___x_2871_, v_mvarId_2872_, v_majorFVarId_2873_, v_recursorName_2874_, v_givenNames_2875_, v_cls_2876_, v___y_2877_, v___y_2878_, v___y_2879_, v___y_2880_);
lean_dec(v___y_2880_);
lean_dec_ref(v___y_2879_);
lean_dec(v___y_2878_);
lean_dec_ref(v___y_2877_);
return v_res_2882_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_induction(lean_object* v_mvarId_2883_, lean_object* v_majorFVarId_2884_, lean_object* v_recursorName_2885_, lean_object* v_givenNames_2886_, lean_object* v_a_2887_, lean_object* v_a_2888_, lean_object* v_a_2889_, lean_object* v_a_2890_){
_start:
{
lean_object* v___x_2892_; lean_object* v_cls_2893_; lean_object* v___f_2894_; lean_object* v___x_2895_; 
v___x_2892_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__0));
v_cls_2893_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__2));
lean_inc(v_mvarId_2883_);
v___f_2894_ = lean_alloc_closure((void*)(l_Lean_MVarId_induction___lam__0___boxed), 11, 6);
lean_closure_set(v___f_2894_, 0, v___x_2892_);
lean_closure_set(v___f_2894_, 1, v_mvarId_2883_);
lean_closure_set(v___f_2894_, 2, v_majorFVarId_2884_);
lean_closure_set(v___f_2894_, 3, v_recursorName_2885_);
lean_closure_set(v___f_2894_, 4, v_givenNames_2886_);
lean_closure_set(v___f_2894_, 5, v_cls_2893_);
v___x_2895_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___redArg(v_mvarId_2883_, v___f_2894_, v_a_2887_, v_a_2888_, v_a_2889_, v_a_2890_);
return v___x_2895_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_induction___boxed(lean_object* v_mvarId_2896_, lean_object* v_majorFVarId_2897_, lean_object* v_recursorName_2898_, lean_object* v_givenNames_2899_, lean_object* v_a_2900_, lean_object* v_a_2901_, lean_object* v_a_2902_, lean_object* v_a_2903_, lean_object* v_a_2904_){
_start:
{
lean_object* v_res_2905_; 
v_res_2905_ = l_Lean_MVarId_induction(v_mvarId_2896_, v_majorFVarId_2897_, v_recursorName_2898_, v_givenNames_2899_, v_a_2900_, v_a_2901_, v_a_2902_, v_a_2903_);
lean_dec(v_a_2903_);
lean_dec_ref(v_a_2902_);
lean_dec(v_a_2901_);
lean_dec_ref(v_a_2900_);
return v_res_2905_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; 
v___x_2953_ = lean_unsigned_to_nat(2221195325u);
v___x_2954_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_));
v___x_2955_ = l_Lean_Name_num___override(v___x_2954_, v___x_2953_);
return v___x_2955_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; 
v___x_2957_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_));
v___x_2958_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_);
v___x_2959_ = l_Lean_Name_str___override(v___x_2958_, v___x_2957_);
return v___x_2959_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; 
v___x_2961_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_));
v___x_2962_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_);
v___x_2963_ = l_Lean_Name_str___override(v___x_2962_, v___x_2961_);
return v___x_2963_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; 
v___x_2964_ = lean_unsigned_to_nat(2u);
v___x_2965_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_);
v___x_2966_ = l_Lean_Name_num___override(v___x_2965_, v___x_2964_);
return v___x_2966_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2968_; uint8_t v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; 
v___x_2968_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__2));
v___x_2969_ = 0;
v___x_2970_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_);
v___x_2971_ = l_Lean_registerTraceClass(v___x_2968_, v___x_2969_, v___x_2970_);
return v___x_2971_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2____boxed(lean_object* v_a_2972_){
_start:
{
lean_object* v_res_2973_; 
v_res_2973_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_();
return v_res_2973_;
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
