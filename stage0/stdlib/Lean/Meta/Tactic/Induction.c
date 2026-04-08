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
extern lean_object* l_Lean_Meta_instInhabitedFVarSubst_default;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_instInhabitedMVarId_default;
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
static lean_once_cell_t l_Lean_Meta_instInhabitedInductionSubgoal_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instInhabitedInductionSubgoal_default___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedInductionSubgoal_default;
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedInductionSubgoal;
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
static const lean_array_object l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__12_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "Lean.Meta.Tactic.Induction"};
static const lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__13_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 62, .m_capacity = 62, .m_length = 61, .m_data = "_private.Lean.Meta.Tactic.Induction.0.Lean.Meta.finalize.loop"};
static const lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__14 = (const lean_object*)&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__14_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__15 = (const lean_object*)&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__15_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__16;
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
static lean_object* _init_l_Lean_Meta_instInhabitedInductionSubgoal_default___closed__1(void){
_start:
{
lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; 
v___x_85_ = l_Lean_Meta_instInhabitedFVarSubst_default;
v___x_86_ = ((lean_object*)(l_Lean_Meta_instInhabitedInductionSubgoal_default___closed__0));
v___x_87_ = l_Lean_instInhabitedMVarId_default;
v___x_88_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_88_, 0, v___x_87_);
lean_ctor_set(v___x_88_, 1, v___x_86_);
lean_ctor_set(v___x_88_, 2, v___x_85_);
return v___x_88_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedInductionSubgoal_default(void){
_start:
{
lean_object* v___x_89_; 
v___x_89_ = lean_obj_once(&l_Lean_Meta_instInhabitedInductionSubgoal_default___closed__1, &l_Lean_Meta_instInhabitedInductionSubgoal_default___closed__1_once, _init_l_Lean_Meta_instInhabitedInductionSubgoal_default___closed__1);
return v___x_89_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedInductionSubgoal(void){
_start:
{
lean_object* v___x_90_; 
v___x_90_ = l_Lean_Meta_instInhabitedInductionSubgoal_default;
return v___x_90_;
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
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__16(void){
_start:
{
lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; 
v___x_555_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__15));
v___x_556_ = lean_unsigned_to_nat(15u);
v___x_557_ = lean_unsigned_to_nat(120u);
v___x_558_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__14));
v___x_559_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__13));
v___x_560_ = l_mkPanicMessageWithDecl(v___x_559_, v___x_558_, v___x_557_, v___x_556_, v___x_555_);
return v___x_560_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop(lean_object* v_mvarId_561_, lean_object* v_givenNames_562_, lean_object* v_recursorInfo_563_, lean_object* v_reverted_564_, lean_object* v_major_565_, lean_object* v_indices_566_, lean_object* v_baseSubst_567_, lean_object* v_initialArity_568_, lean_object* v_numMinors_569_, lean_object* v_pos_570_, lean_object* v_minorIdx_571_, lean_object* v_recursor_572_, lean_object* v_recursorType_573_, uint8_t v_consumedMajor_574_, lean_object* v_subgoals_575_, lean_object* v_a_576_, lean_object* v_a_577_, lean_object* v_a_578_, lean_object* v_a_579_){
_start:
{
lean_object* v___y_582_; lean_object* v___y_583_; lean_object* v___y_584_; lean_object* v___y_585_; lean_object* v___y_638_; uint8_t v___y_639_; lean_object* v___y_640_; lean_object* v___y_641_; lean_object* v___y_642_; lean_object* v___y_643_; lean_object* v___y_644_; lean_object* v___y_645_; lean_object* v___y_646_; lean_object* v___y_647_; lean_object* v___y_648_; lean_object* v___y_649_; lean_object* v___y_650_; lean_object* v___y_651_; uint8_t v___y_652_; uint8_t v___y_653_; lean_object* v___y_689_; lean_object* v___y_690_; lean_object* v___y_691_; uint8_t v___y_692_; lean_object* v___y_693_; lean_object* v___y_694_; lean_object* v___y_695_; lean_object* v___y_696_; lean_object* v___y_697_; lean_object* v___y_698_; uint8_t v___y_699_; lean_object* v___y_700_; lean_object* v___y_701_; lean_object* v___y_702_; lean_object* v___y_703_; uint8_t v___y_721_; lean_object* v___y_722_; lean_object* v_fst_723_; lean_object* v_snd_724_; lean_object* v___y_741_; uint8_t v___y_742_; lean_object* v___y_743_; lean_object* v___x_755_; 
v___x_755_ = l_Lean_Meta_whnfForall(v_recursorType_573_, v_a_576_, v_a_577_, v_a_578_, v_a_579_);
if (lean_obj_tag(v___x_755_) == 0)
{
lean_object* v_a_756_; lean_object* v___y_758_; lean_object* v___y_759_; lean_object* v___y_760_; uint8_t v___y_761_; lean_object* v___y_762_; lean_object* v___y_763_; lean_object* v___y_764_; lean_object* v___y_765_; lean_object* v___y_766_; lean_object* v___y_767_; lean_object* v___y_768_; lean_object* v___y_769_; uint8_t v___y_770_; lean_object* v___y_771_; lean_object* v___y_813_; uint8_t v___y_814_; lean_object* v___y_815_; lean_object* v___y_816_; lean_object* v___y_817_; uint8_t v___y_818_; lean_object* v___y_819_; lean_object* v___y_820_; lean_object* v___y_821_; lean_object* v___y_822_; lean_object* v___y_834_; lean_object* v___y_835_; lean_object* v___y_836_; lean_object* v___y_837_; lean_object* v___y_838_; lean_object* v___y_839_; lean_object* v___y_840_; uint8_t v___y_841_; uint8_t v___y_842_; lean_object* v___y_912_; lean_object* v___y_913_; lean_object* v___y_914_; lean_object* v___y_915_; uint8_t v___y_916_; lean_object* v___y_917_; lean_object* v___y_918_; uint8_t v___y_919_; lean_object* v___y_920_; lean_object* v___y_926_; uint8_t v___y_927_; lean_object* v___y_928_; lean_object* v___y_929_; lean_object* v___y_930_; lean_object* v___y_931_; uint8_t v___y_943_; uint8_t v___x_990_; 
v_a_756_ = lean_ctor_get(v___x_755_, 0);
lean_inc(v_a_756_);
lean_dec_ref(v___x_755_);
v___x_990_ = l_Lean_Expr_isForall(v_a_756_);
if (v___x_990_ == 0)
{
v___y_943_ = v___x_990_;
goto v___jp_942_;
}
else
{
lean_object* v_numArgs_991_; uint8_t v___x_992_; 
v_numArgs_991_ = lean_ctor_get(v_recursorInfo_563_, 3);
v___x_992_ = lean_nat_dec_lt(v_pos_570_, v_numArgs_991_);
v___y_943_ = v___x_992_;
goto v___jp_942_;
}
v___jp_757_:
{
lean_object* v___x_772_; 
v___x_772_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___y_758_, v___y_760_, v___y_766_, v___y_763_, v___y_765_, v___y_767_);
if (lean_obj_tag(v___x_772_) == 0)
{
lean_object* v_a_773_; lean_object* v___x_774_; 
v_a_773_ = lean_ctor_get(v___x_772_, 0);
lean_inc(v_a_773_);
lean_dec_ref(v___x_772_);
lean_inc(v_mvarId_561_);
v___x_774_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTypeBody(v_mvarId_561_, v_a_756_, v_a_773_, v___y_766_, v___y_763_, v___y_765_, v___y_767_);
if (lean_obj_tag(v___x_774_) == 0)
{
lean_object* v_options_775_; lean_object* v_a_776_; lean_object* v_inheritedTraceOptions_777_; uint8_t v_hasTrace_778_; lean_object* v___x_779_; 
v_options_775_ = lean_ctor_get(v___y_765_, 2);
v_a_776_ = lean_ctor_get(v___x_774_, 0);
lean_inc(v_a_776_);
lean_dec_ref(v___x_774_);
v_inheritedTraceOptions_777_ = lean_ctor_get(v___y_765_, 13);
v_hasTrace_778_ = lean_ctor_get_uint8(v_options_775_, sizeof(void*)*1);
lean_inc(v_a_773_);
v___x_779_ = l_Lean_Expr_app___override(v_recursor_572_, v_a_773_);
if (v_hasTrace_778_ == 0)
{
v___y_689_ = v_a_773_;
v___y_690_ = v___x_779_;
v___y_691_ = v___y_759_;
v___y_692_ = v___y_761_;
v___y_693_ = v___y_762_;
v___y_694_ = v___y_771_;
v___y_695_ = v___y_768_;
v___y_696_ = v___y_769_;
v___y_697_ = v___y_764_;
v___y_698_ = v_a_776_;
v___y_699_ = v___y_770_;
v___y_700_ = v___y_766_;
v___y_701_ = v___y_763_;
v___y_702_ = v___y_765_;
v___y_703_ = v___y_767_;
goto v___jp_688_;
}
else
{
lean_object* v___x_780_; lean_object* v___x_781_; uint8_t v___x_782_; 
v___x_780_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__2));
v___x_781_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5);
v___x_782_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_777_, v_options_775_, v___x_781_);
if (v___x_782_ == 0)
{
v___y_689_ = v_a_773_;
v___y_690_ = v___x_779_;
v___y_691_ = v___y_759_;
v___y_692_ = v___y_761_;
v___y_693_ = v___y_762_;
v___y_694_ = v___y_771_;
v___y_695_ = v___y_768_;
v___y_696_ = v___y_769_;
v___y_697_ = v___y_764_;
v___y_698_ = v_a_776_;
v___y_699_ = v___y_770_;
v___y_700_ = v___y_766_;
v___y_701_ = v___y_763_;
v___y_702_ = v___y_765_;
v___y_703_ = v___y_767_;
goto v___jp_688_;
}
else
{
lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; 
v___x_783_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__11, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__11_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__11);
v___x_784_ = l_Lean_Expr_fvarId_x21(v_major_565_);
v___x_785_ = l_Lean_MessageData_ofName(v___x_784_);
v___x_786_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_786_, 0, v___x_783_);
lean_ctor_set(v___x_786_, 1, v___x_785_);
v___x_787_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1(v___x_780_, v___x_786_, v___y_766_, v___y_763_, v___y_765_, v___y_767_);
if (lean_obj_tag(v___x_787_) == 0)
{
lean_dec_ref(v___x_787_);
v___y_689_ = v_a_773_;
v___y_690_ = v___x_779_;
v___y_691_ = v___y_759_;
v___y_692_ = v___y_761_;
v___y_693_ = v___y_762_;
v___y_694_ = v___y_771_;
v___y_695_ = v___y_768_;
v___y_696_ = v___y_769_;
v___y_697_ = v___y_764_;
v___y_698_ = v_a_776_;
v___y_699_ = v___y_770_;
v___y_700_ = v___y_766_;
v___y_701_ = v___y_763_;
v___y_702_ = v___y_765_;
v___y_703_ = v___y_767_;
goto v___jp_688_;
}
else
{
lean_object* v_a_788_; lean_object* v___x_790_; uint8_t v_isShared_791_; uint8_t v_isSharedCheck_795_; 
lean_dec_ref(v___x_779_);
lean_dec(v_a_776_);
lean_dec(v_a_773_);
lean_dec_ref(v___y_771_);
lean_dec(v___y_769_);
lean_dec(v___y_764_);
lean_dec(v___y_762_);
lean_dec(v___y_759_);
lean_dec_ref(v_subgoals_575_);
lean_dec(v_minorIdx_571_);
lean_dec(v_pos_570_);
lean_dec(v_baseSubst_567_);
lean_dec_ref(v_major_565_);
lean_dec(v_mvarId_561_);
v_a_788_ = lean_ctor_get(v___x_787_, 0);
v_isSharedCheck_795_ = !lean_is_exclusive(v___x_787_);
if (v_isSharedCheck_795_ == 0)
{
v___x_790_ = v___x_787_;
v_isShared_791_ = v_isSharedCheck_795_;
goto v_resetjp_789_;
}
else
{
lean_inc(v_a_788_);
lean_dec(v___x_787_);
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
}
}
else
{
lean_object* v_a_796_; lean_object* v___x_798_; uint8_t v_isShared_799_; uint8_t v_isSharedCheck_803_; 
lean_dec(v_a_773_);
lean_dec_ref(v___y_771_);
lean_dec(v___y_769_);
lean_dec(v___y_764_);
lean_dec(v___y_762_);
lean_dec(v___y_759_);
lean_dec_ref(v_subgoals_575_);
lean_dec_ref(v_recursor_572_);
lean_dec(v_minorIdx_571_);
lean_dec(v_pos_570_);
lean_dec(v_baseSubst_567_);
lean_dec_ref(v_major_565_);
lean_dec(v_mvarId_561_);
v_a_796_ = lean_ctor_get(v___x_774_, 0);
v_isSharedCheck_803_ = !lean_is_exclusive(v___x_774_);
if (v_isSharedCheck_803_ == 0)
{
v___x_798_ = v___x_774_;
v_isShared_799_ = v_isSharedCheck_803_;
goto v_resetjp_797_;
}
else
{
lean_inc(v_a_796_);
lean_dec(v___x_774_);
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
else
{
lean_object* v_a_804_; lean_object* v___x_806_; uint8_t v_isShared_807_; uint8_t v_isSharedCheck_811_; 
lean_dec_ref(v___y_771_);
lean_dec(v___y_769_);
lean_dec(v___y_764_);
lean_dec(v___y_762_);
lean_dec(v___y_759_);
lean_dec(v_a_756_);
lean_dec_ref(v_subgoals_575_);
lean_dec_ref(v_recursor_572_);
lean_dec(v_minorIdx_571_);
lean_dec(v_pos_570_);
lean_dec(v_baseSubst_567_);
lean_dec_ref(v_major_565_);
lean_dec(v_mvarId_561_);
v_a_804_ = lean_ctor_get(v___x_772_, 0);
v_isSharedCheck_811_ = !lean_is_exclusive(v___x_772_);
if (v_isSharedCheck_811_ == 0)
{
v___x_806_ = v___x_772_;
v_isShared_807_ = v_isSharedCheck_811_;
goto v_resetjp_805_;
}
else
{
lean_inc(v_a_804_);
lean_dec(v___x_772_);
v___x_806_ = lean_box(0);
v_isShared_807_ = v_isSharedCheck_811_;
goto v_resetjp_805_;
}
v_resetjp_805_:
{
lean_object* v___x_809_; 
if (v_isShared_807_ == 0)
{
v___x_809_ = v___x_806_;
goto v_reusejp_808_;
}
else
{
lean_object* v_reuseFailAlloc_810_; 
v_reuseFailAlloc_810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_810_, 0, v_a_804_);
v___x_809_ = v_reuseFailAlloc_810_;
goto v_reusejp_808_;
}
v_reusejp_808_:
{
return v___x_809_;
}
}
}
}
v___jp_812_:
{
lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; uint8_t v___x_829_; 
v___x_823_ = lean_nat_sub(v___y_816_, v_initialArity_568_);
lean_dec(v___y_816_);
v___x_824_ = lean_array_get_size(v_reverted_564_);
v___x_825_ = lean_array_get_size(v_indices_566_);
v___x_826_ = lean_nat_sub(v___x_824_, v___x_825_);
v___x_827_ = lean_nat_sub(v___x_826_, v___y_817_);
lean_dec(v___x_826_);
v___x_828_ = lean_array_get_size(v_givenNames_562_);
v___x_829_ = lean_nat_dec_lt(v_minorIdx_571_, v___x_828_);
if (v___x_829_ == 0)
{
lean_object* v___x_830_; lean_object* v___x_831_; 
v___x_830_ = lean_box(0);
v___x_831_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_831_, 0, v___x_830_);
lean_ctor_set_uint8(v___x_831_, sizeof(void*)*1, v___y_814_);
v___y_758_ = v___y_813_;
v___y_759_ = v___x_827_;
v___y_760_ = v___y_815_;
v___y_761_ = v___y_814_;
v___y_762_ = v___x_825_;
v___y_763_ = v___y_820_;
v___y_764_ = v___x_824_;
v___y_765_ = v___y_821_;
v___y_766_ = v___y_819_;
v___y_767_ = v___y_822_;
v___y_768_ = v___y_817_;
v___y_769_ = v___x_823_;
v___y_770_ = v___y_818_;
v___y_771_ = v___x_831_;
goto v___jp_757_;
}
else
{
lean_object* v___x_832_; 
v___x_832_ = lean_array_fget_borrowed(v_givenNames_562_, v_minorIdx_571_);
lean_inc(v___x_832_);
v___y_758_ = v___y_813_;
v___y_759_ = v___x_827_;
v___y_760_ = v___y_815_;
v___y_761_ = v___y_814_;
v___y_762_ = v___x_825_;
v___y_763_ = v___y_820_;
v___y_764_ = v___x_824_;
v___y_765_ = v___y_821_;
v___y_766_ = v___y_819_;
v___y_767_ = v___y_822_;
v___y_768_ = v___y_817_;
v___y_769_ = v___x_823_;
v___y_770_ = v___y_818_;
v___y_771_ = v___x_832_;
goto v___jp_757_;
}
}
v___jp_833_:
{
if (v___y_842_ == 0)
{
lean_object* v___x_843_; uint8_t v___x_844_; 
lean_inc_ref(v___y_834_);
v___x_843_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTargetArity(v___y_834_);
v___x_844_ = lean_nat_dec_lt(v___x_843_, v_initialArity_568_);
if (v___x_844_ == 0)
{
v___y_813_ = v___y_834_;
v___y_814_ = v___y_842_;
v___y_815_ = v___y_836_;
v___y_816_ = v___x_843_;
v___y_817_ = v___y_839_;
v___y_818_ = v___y_841_;
v___y_819_ = v___y_838_;
v___y_820_ = v___y_840_;
v___y_821_ = v___y_837_;
v___y_822_ = v___y_835_;
goto v___jp_812_;
}
else
{
lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; 
v___x_845_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1));
v___x_846_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9);
lean_inc(v_mvarId_561_);
v___x_847_ = l_Lean_Meta_throwTacticEx___redArg(v___x_845_, v_mvarId_561_, v___x_846_, v___y_838_, v___y_840_, v___y_837_, v___y_835_);
if (lean_obj_tag(v___x_847_) == 0)
{
lean_dec_ref(v___x_847_);
v___y_813_ = v___y_834_;
v___y_814_ = v___y_842_;
v___y_815_ = v___y_836_;
v___y_816_ = v___x_843_;
v___y_817_ = v___y_839_;
v___y_818_ = v___y_841_;
v___y_819_ = v___y_838_;
v___y_820_ = v___y_840_;
v___y_821_ = v___y_837_;
v___y_822_ = v___y_835_;
goto v___jp_812_;
}
else
{
lean_object* v_a_848_; lean_object* v___x_850_; uint8_t v_isShared_851_; uint8_t v_isSharedCheck_855_; 
lean_dec(v___x_843_);
lean_dec(v___y_836_);
lean_dec_ref(v___y_834_);
lean_dec(v_a_756_);
lean_dec_ref(v_subgoals_575_);
lean_dec_ref(v_recursor_572_);
lean_dec(v_minorIdx_571_);
lean_dec(v_pos_570_);
lean_dec(v_baseSubst_567_);
lean_dec_ref(v_major_565_);
lean_dec(v_mvarId_561_);
v_a_848_ = lean_ctor_get(v___x_847_, 0);
v_isSharedCheck_855_ = !lean_is_exclusive(v___x_847_);
if (v_isSharedCheck_855_ == 0)
{
v___x_850_ = v___x_847_;
v_isShared_851_ = v_isSharedCheck_855_;
goto v_resetjp_849_;
}
else
{
lean_inc(v_a_848_);
lean_dec(v___x_847_);
v___x_850_ = lean_box(0);
v_isShared_851_ = v_isSharedCheck_855_;
goto v_resetjp_849_;
}
v_resetjp_849_:
{
lean_object* v___x_853_; 
if (v_isShared_851_ == 0)
{
v___x_853_ = v___x_850_;
goto v_reusejp_852_;
}
else
{
lean_object* v_reuseFailAlloc_854_; 
v_reuseFailAlloc_854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_854_, 0, v_a_848_);
v___x_853_ = v_reuseFailAlloc_854_;
goto v_reusejp_852_;
}
v_reusejp_852_:
{
return v___x_853_;
}
}
}
}
}
else
{
lean_object* v___x_856_; lean_object* v___x_857_; 
v___x_856_ = lean_box(0);
lean_inc_ref(v___y_834_);
v___x_857_ = l_Lean_Meta_synthInstance_x3f(v___y_834_, v___x_856_, v___y_838_, v___y_840_, v___y_837_, v___y_835_);
if (lean_obj_tag(v___x_857_) == 0)
{
lean_object* v_a_858_; 
v_a_858_ = lean_ctor_get(v___x_857_, 0);
lean_inc(v_a_858_);
lean_dec_ref(v___x_857_);
if (lean_obj_tag(v_a_858_) == 0)
{
lean_object* v___x_859_; 
v___x_859_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___y_834_, v___y_836_, v___y_838_, v___y_840_, v___y_837_, v___y_835_);
if (lean_obj_tag(v___x_859_) == 0)
{
lean_object* v_a_860_; lean_object* v___x_861_; 
v_a_860_ = lean_ctor_get(v___x_859_, 0);
lean_inc(v_a_860_);
lean_dec_ref(v___x_859_);
lean_inc(v_mvarId_561_);
v___x_861_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTypeBody(v_mvarId_561_, v_a_756_, v_a_860_, v___y_838_, v___y_840_, v___y_837_, v___y_835_);
if (lean_obj_tag(v___x_861_) == 0)
{
lean_object* v_a_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; 
v_a_862_ = lean_ctor_get(v___x_861_, 0);
lean_inc(v_a_862_);
lean_dec_ref(v___x_861_);
lean_inc(v_a_860_);
v___x_863_ = l_Lean_Expr_app___override(v_recursor_572_, v_a_860_);
v___x_864_ = lean_nat_add(v_pos_570_, v___y_839_);
lean_dec(v_pos_570_);
v___x_865_ = lean_nat_add(v_minorIdx_571_, v___y_839_);
lean_dec(v_minorIdx_571_);
v___x_866_ = l_Lean_Expr_mvarId_x21(v_a_860_);
lean_dec(v_a_860_);
v___x_867_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__12));
v___x_868_ = lean_box(0);
v___x_869_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_869_, 0, v___x_866_);
lean_ctor_set(v___x_869_, 1, v___x_867_);
lean_ctor_set(v___x_869_, 2, v___x_868_);
v___x_870_ = lean_array_push(v_subgoals_575_, v___x_869_);
v_pos_570_ = v___x_864_;
v_minorIdx_571_ = v___x_865_;
v_recursor_572_ = v___x_863_;
v_recursorType_573_ = v_a_862_;
v_subgoals_575_ = v___x_870_;
v_a_576_ = v___y_838_;
v_a_577_ = v___y_840_;
v_a_578_ = v___y_837_;
v_a_579_ = v___y_835_;
goto _start;
}
else
{
lean_object* v_a_872_; lean_object* v___x_874_; uint8_t v_isShared_875_; uint8_t v_isSharedCheck_879_; 
lean_dec(v_a_860_);
lean_dec_ref(v_subgoals_575_);
lean_dec_ref(v_recursor_572_);
lean_dec(v_minorIdx_571_);
lean_dec(v_pos_570_);
lean_dec(v_baseSubst_567_);
lean_dec_ref(v_major_565_);
lean_dec(v_mvarId_561_);
v_a_872_ = lean_ctor_get(v___x_861_, 0);
v_isSharedCheck_879_ = !lean_is_exclusive(v___x_861_);
if (v_isSharedCheck_879_ == 0)
{
v___x_874_ = v___x_861_;
v_isShared_875_ = v_isSharedCheck_879_;
goto v_resetjp_873_;
}
else
{
lean_inc(v_a_872_);
lean_dec(v___x_861_);
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
lean_object* v_a_880_; lean_object* v___x_882_; uint8_t v_isShared_883_; uint8_t v_isSharedCheck_887_; 
lean_dec(v_a_756_);
lean_dec_ref(v_subgoals_575_);
lean_dec_ref(v_recursor_572_);
lean_dec(v_minorIdx_571_);
lean_dec(v_pos_570_);
lean_dec(v_baseSubst_567_);
lean_dec_ref(v_major_565_);
lean_dec(v_mvarId_561_);
v_a_880_ = lean_ctor_get(v___x_859_, 0);
v_isSharedCheck_887_ = !lean_is_exclusive(v___x_859_);
if (v_isSharedCheck_887_ == 0)
{
v___x_882_ = v___x_859_;
v_isShared_883_ = v_isSharedCheck_887_;
goto v_resetjp_881_;
}
else
{
lean_inc(v_a_880_);
lean_dec(v___x_859_);
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
else
{
lean_object* v_val_888_; lean_object* v___x_889_; 
lean_dec(v___y_836_);
lean_dec_ref(v___y_834_);
v_val_888_ = lean_ctor_get(v_a_858_, 0);
lean_inc(v_val_888_);
lean_dec_ref(v_a_858_);
lean_inc(v_mvarId_561_);
v___x_889_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTypeBody(v_mvarId_561_, v_a_756_, v_val_888_, v___y_838_, v___y_840_, v___y_837_, v___y_835_);
if (lean_obj_tag(v___x_889_) == 0)
{
lean_object* v_a_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; 
v_a_890_ = lean_ctor_get(v___x_889_, 0);
lean_inc(v_a_890_);
lean_dec_ref(v___x_889_);
v___x_891_ = l_Lean_Expr_app___override(v_recursor_572_, v_val_888_);
v___x_892_ = lean_nat_add(v_pos_570_, v___y_839_);
lean_dec(v_pos_570_);
v___x_893_ = lean_nat_add(v_minorIdx_571_, v___y_839_);
lean_dec(v_minorIdx_571_);
v_pos_570_ = v___x_892_;
v_minorIdx_571_ = v___x_893_;
v_recursor_572_ = v___x_891_;
v_recursorType_573_ = v_a_890_;
v_a_576_ = v___y_838_;
v_a_577_ = v___y_840_;
v_a_578_ = v___y_837_;
v_a_579_ = v___y_835_;
goto _start;
}
else
{
lean_object* v_a_895_; lean_object* v___x_897_; uint8_t v_isShared_898_; uint8_t v_isSharedCheck_902_; 
lean_dec(v_val_888_);
lean_dec_ref(v_subgoals_575_);
lean_dec_ref(v_recursor_572_);
lean_dec(v_minorIdx_571_);
lean_dec(v_pos_570_);
lean_dec(v_baseSubst_567_);
lean_dec_ref(v_major_565_);
lean_dec(v_mvarId_561_);
v_a_895_ = lean_ctor_get(v___x_889_, 0);
v_isSharedCheck_902_ = !lean_is_exclusive(v___x_889_);
if (v_isSharedCheck_902_ == 0)
{
v___x_897_ = v___x_889_;
v_isShared_898_ = v_isSharedCheck_902_;
goto v_resetjp_896_;
}
else
{
lean_inc(v_a_895_);
lean_dec(v___x_889_);
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
else
{
lean_object* v_a_903_; lean_object* v___x_905_; uint8_t v_isShared_906_; uint8_t v_isSharedCheck_910_; 
lean_dec(v___y_836_);
lean_dec_ref(v___y_834_);
lean_dec(v_a_756_);
lean_dec_ref(v_subgoals_575_);
lean_dec_ref(v_recursor_572_);
lean_dec(v_minorIdx_571_);
lean_dec(v_pos_570_);
lean_dec(v_baseSubst_567_);
lean_dec_ref(v_major_565_);
lean_dec(v_mvarId_561_);
v_a_903_ = lean_ctor_get(v___x_857_, 0);
v_isSharedCheck_910_ = !lean_is_exclusive(v___x_857_);
if (v_isSharedCheck_910_ == 0)
{
v___x_905_ = v___x_857_;
v_isShared_906_ = v_isSharedCheck_910_;
goto v_resetjp_904_;
}
else
{
lean_inc(v_a_903_);
lean_dec(v___x_857_);
v___x_905_ = lean_box(0);
v_isShared_906_ = v_isSharedCheck_910_;
goto v_resetjp_904_;
}
v_resetjp_904_:
{
lean_object* v___x_908_; 
if (v_isShared_906_ == 0)
{
v___x_908_ = v___x_905_;
goto v_reusejp_907_;
}
else
{
lean_object* v_reuseFailAlloc_909_; 
v_reuseFailAlloc_909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_909_, 0, v_a_903_);
v___x_908_ = v_reuseFailAlloc_909_;
goto v_reusejp_907_;
}
v_reusejp_907_:
{
return v___x_908_;
}
}
}
}
}
v___jp_911_:
{
uint8_t v___x_921_; 
v___x_921_ = l_Lean_BinderInfo_isInstImplicit(v___y_916_);
if (v___x_921_ == 0)
{
v___y_834_ = v___y_912_;
v___y_835_ = v___y_913_;
v___y_836_ = v___y_920_;
v___y_837_ = v___y_914_;
v___y_838_ = v___y_915_;
v___y_839_ = v___y_917_;
v___y_840_ = v___y_918_;
v___y_841_ = v___y_919_;
v___y_842_ = v___x_921_;
goto v___jp_833_;
}
else
{
lean_object* v___x_922_; lean_object* v___x_923_; uint8_t v___x_924_; 
v___x_922_ = lean_array_get_size(v_givenNames_562_);
v___x_923_ = lean_unsigned_to_nat(0u);
v___x_924_ = lean_nat_dec_eq(v___x_922_, v___x_923_);
v___y_834_ = v___y_912_;
v___y_835_ = v___y_913_;
v___y_836_ = v___y_920_;
v___y_837_ = v___y_914_;
v___y_838_ = v___y_915_;
v___y_839_ = v___y_917_;
v___y_840_ = v___y_918_;
v___y_841_ = v___y_919_;
v___y_842_ = v___x_924_;
goto v___jp_833_;
}
}
v___jp_925_:
{
if (lean_obj_tag(v_a_756_) == 7)
{
lean_object* v_binderName_932_; lean_object* v_binderType_933_; uint8_t v_binderInfo_934_; lean_object* v___x_935_; lean_object* v___x_936_; uint8_t v___x_937_; 
v_binderName_932_ = lean_ctor_get(v_a_756_, 0);
v_binderType_933_ = lean_ctor_get(v_a_756_, 1);
v_binderInfo_934_ = lean_ctor_get_uint8(v_a_756_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_933_);
v___x_935_ = l_Lean_Expr_headBeta(v_binderType_933_);
v___x_936_ = lean_unsigned_to_nat(1u);
v___x_937_ = lean_nat_dec_eq(v_numMinors_569_, v___x_936_);
if (v___x_937_ == 0)
{
lean_object* v___x_938_; lean_object* v___x_939_; 
lean_inc(v_binderName_932_);
v___x_938_ = lean_erase_macro_scopes(v_binderName_932_);
v___x_939_ = l_Lean_Name_append(v___y_926_, v___x_938_);
v___y_912_ = v___x_935_;
v___y_913_ = v___y_931_;
v___y_914_ = v___y_930_;
v___y_915_ = v___y_928_;
v___y_916_ = v_binderInfo_934_;
v___y_917_ = v___x_936_;
v___y_918_ = v___y_929_;
v___y_919_ = v___y_927_;
v___y_920_ = v___x_939_;
goto v___jp_911_;
}
else
{
v___y_912_ = v___x_935_;
v___y_913_ = v___y_931_;
v___y_914_ = v___y_930_;
v___y_915_ = v___y_928_;
v___y_916_ = v_binderInfo_934_;
v___y_917_ = v___x_936_;
v___y_918_ = v___y_929_;
v___y_919_ = v___y_927_;
v___y_920_ = v___y_926_;
goto v___jp_911_;
}
}
else
{
lean_object* v___x_940_; lean_object* v___x_941_; 
lean_dec(v___y_926_);
lean_dec(v_a_756_);
lean_dec_ref(v_subgoals_575_);
lean_dec_ref(v_recursor_572_);
lean_dec(v_minorIdx_571_);
lean_dec(v_pos_570_);
lean_dec(v_baseSubst_567_);
lean_dec_ref(v_major_565_);
lean_dec(v_mvarId_561_);
v___x_940_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__16, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__16_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__16);
v___x_941_ = l_panic___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__4(v___x_940_, v___y_928_, v___y_929_, v___y_930_, v___y_931_);
return v___x_941_;
}
}
v___jp_942_:
{
if (v___y_943_ == 0)
{
lean_dec(v_a_756_);
lean_dec(v_minorIdx_571_);
lean_dec(v_pos_570_);
lean_dec(v_baseSubst_567_);
lean_dec_ref(v_major_565_);
if (v_consumedMajor_574_ == 0)
{
lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; 
v___x_944_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1));
v___x_945_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9);
lean_inc(v_mvarId_561_);
v___x_946_ = l_Lean_Meta_throwTacticEx___redArg(v___x_944_, v_mvarId_561_, v___x_945_, v_a_576_, v_a_577_, v_a_578_, v_a_579_);
if (lean_obj_tag(v___x_946_) == 0)
{
lean_dec_ref(v___x_946_);
v___y_582_ = v_a_576_;
v___y_583_ = v_a_577_;
v___y_584_ = v_a_578_;
v___y_585_ = v_a_579_;
goto v___jp_581_;
}
else
{
lean_object* v_a_947_; lean_object* v___x_949_; uint8_t v_isShared_950_; uint8_t v_isSharedCheck_954_; 
lean_dec_ref(v_subgoals_575_);
lean_dec_ref(v_recursor_572_);
lean_dec(v_mvarId_561_);
v_a_947_ = lean_ctor_get(v___x_946_, 0);
v_isSharedCheck_954_ = !lean_is_exclusive(v___x_946_);
if (v_isSharedCheck_954_ == 0)
{
v___x_949_ = v___x_946_;
v_isShared_950_ = v_isSharedCheck_954_;
goto v_resetjp_948_;
}
else
{
lean_inc(v_a_947_);
lean_dec(v___x_946_);
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
else
{
v___y_582_ = v_a_576_;
v___y_583_ = v_a_577_;
v___y_584_ = v_a_578_;
v___y_585_ = v_a_579_;
goto v___jp_581_;
}
}
else
{
lean_object* v___x_955_; uint8_t v___x_956_; 
v___x_955_ = l_Lean_Meta_RecursorInfo_firstIndexPos(v_recursorInfo_563_);
v___x_956_ = lean_nat_dec_eq(v_pos_570_, v___x_955_);
lean_dec(v___x_955_);
if (v___x_956_ == 0)
{
lean_object* v___x_957_; 
lean_inc(v_mvarId_561_);
v___x_957_ = l_Lean_MVarId_getTag(v_mvarId_561_, v_a_576_, v_a_577_, v_a_578_, v_a_579_);
if (lean_obj_tag(v___x_957_) == 0)
{
lean_object* v_a_958_; uint8_t v___x_959_; 
v_a_958_ = lean_ctor_get(v___x_957_, 0);
lean_inc(v_a_958_);
lean_dec_ref(v___x_957_);
v___x_959_ = lean_nat_dec_le(v_numMinors_569_, v_minorIdx_571_);
if (v___x_959_ == 0)
{
v___y_926_ = v_a_958_;
v___y_927_ = v___y_943_;
v___y_928_ = v_a_576_;
v___y_929_ = v_a_577_;
v___y_930_ = v_a_578_;
v___y_931_ = v_a_579_;
goto v___jp_925_;
}
else
{
lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; 
v___x_960_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1));
v___x_961_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9);
lean_inc(v_mvarId_561_);
v___x_962_ = l_Lean_Meta_throwTacticEx___redArg(v___x_960_, v_mvarId_561_, v___x_961_, v_a_576_, v_a_577_, v_a_578_, v_a_579_);
if (lean_obj_tag(v___x_962_) == 0)
{
lean_dec_ref(v___x_962_);
v___y_926_ = v_a_958_;
v___y_927_ = v___y_943_;
v___y_928_ = v_a_576_;
v___y_929_ = v_a_577_;
v___y_930_ = v_a_578_;
v___y_931_ = v_a_579_;
goto v___jp_925_;
}
else
{
lean_object* v_a_963_; lean_object* v___x_965_; uint8_t v_isShared_966_; uint8_t v_isSharedCheck_970_; 
lean_dec(v_a_958_);
lean_dec(v_a_756_);
lean_dec_ref(v_subgoals_575_);
lean_dec_ref(v_recursor_572_);
lean_dec(v_minorIdx_571_);
lean_dec(v_pos_570_);
lean_dec(v_baseSubst_567_);
lean_dec_ref(v_major_565_);
lean_dec(v_mvarId_561_);
v_a_963_ = lean_ctor_get(v___x_962_, 0);
v_isSharedCheck_970_ = !lean_is_exclusive(v___x_962_);
if (v_isSharedCheck_970_ == 0)
{
v___x_965_ = v___x_962_;
v_isShared_966_ = v_isSharedCheck_970_;
goto v_resetjp_964_;
}
else
{
lean_inc(v_a_963_);
lean_dec(v___x_962_);
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
}
else
{
lean_object* v_a_971_; lean_object* v___x_973_; uint8_t v_isShared_974_; uint8_t v_isSharedCheck_978_; 
lean_dec(v_a_756_);
lean_dec_ref(v_subgoals_575_);
lean_dec_ref(v_recursor_572_);
lean_dec(v_minorIdx_571_);
lean_dec(v_pos_570_);
lean_dec(v_baseSubst_567_);
lean_dec_ref(v_major_565_);
lean_dec(v_mvarId_561_);
v_a_971_ = lean_ctor_get(v___x_957_, 0);
v_isSharedCheck_978_ = !lean_is_exclusive(v___x_957_);
if (v_isSharedCheck_978_ == 0)
{
v___x_973_ = v___x_957_;
v_isShared_974_ = v_isSharedCheck_978_;
goto v_resetjp_972_;
}
else
{
lean_inc(v_a_971_);
lean_dec(v___x_957_);
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
}
else
{
lean_object* v___x_979_; lean_object* v___x_980_; uint8_t v___x_981_; 
v___x_979_ = lean_unsigned_to_nat(0u);
v___x_980_ = lean_array_get_size(v_indices_566_);
v___x_981_ = lean_nat_dec_lt(v___x_979_, v___x_980_);
if (v___x_981_ == 0)
{
v___y_721_ = v___x_956_;
v___y_722_ = v___x_980_;
v_fst_723_ = v_recursor_572_;
v_snd_724_ = v_a_756_;
goto v___jp_720_;
}
else
{
lean_object* v___x_982_; uint8_t v___x_983_; 
lean_inc(v_a_756_);
lean_inc_ref(v_recursor_572_);
v___x_982_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_982_, 0, v_recursor_572_);
lean_ctor_set(v___x_982_, 1, v_a_756_);
v___x_983_ = lean_nat_dec_le(v___x_980_, v___x_980_);
if (v___x_983_ == 0)
{
if (v___x_981_ == 0)
{
lean_dec_ref(v___x_982_);
v___y_721_ = v___x_956_;
v___y_722_ = v___x_980_;
v_fst_723_ = v_recursor_572_;
v_snd_724_ = v_a_756_;
goto v___jp_720_;
}
else
{
size_t v___x_984_; size_t v___x_985_; lean_object* v___x_986_; 
lean_dec(v_a_756_);
lean_dec_ref(v_recursor_572_);
v___x_984_ = ((size_t)0ULL);
v___x_985_ = lean_usize_of_nat(v___x_980_);
lean_inc(v_mvarId_561_);
v___x_986_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__5(v_mvarId_561_, v_indices_566_, v___x_984_, v___x_985_, v___x_982_, v_a_576_, v_a_577_, v_a_578_, v_a_579_);
v___y_741_ = v___x_980_;
v___y_742_ = v___x_956_;
v___y_743_ = v___x_986_;
goto v___jp_740_;
}
}
else
{
size_t v___x_987_; size_t v___x_988_; lean_object* v___x_989_; 
lean_dec(v_a_756_);
lean_dec_ref(v_recursor_572_);
v___x_987_ = ((size_t)0ULL);
v___x_988_ = lean_usize_of_nat(v___x_980_);
lean_inc(v_mvarId_561_);
v___x_989_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__5(v_mvarId_561_, v_indices_566_, v___x_987_, v___x_988_, v___x_982_, v_a_576_, v_a_577_, v_a_578_, v_a_579_);
v___y_741_ = v___x_980_;
v___y_742_ = v___x_956_;
v___y_743_ = v___x_989_;
goto v___jp_740_;
}
}
}
}
}
}
else
{
lean_object* v_a_993_; lean_object* v___x_995_; uint8_t v_isShared_996_; uint8_t v_isSharedCheck_1000_; 
lean_dec_ref(v_subgoals_575_);
lean_dec_ref(v_recursor_572_);
lean_dec(v_minorIdx_571_);
lean_dec(v_pos_570_);
lean_dec(v_baseSubst_567_);
lean_dec_ref(v_major_565_);
lean_dec(v_mvarId_561_);
v_a_993_ = lean_ctor_get(v___x_755_, 0);
v_isSharedCheck_1000_ = !lean_is_exclusive(v___x_755_);
if (v_isSharedCheck_1000_ == 0)
{
v___x_995_ = v___x_755_;
v_isShared_996_ = v_isSharedCheck_1000_;
goto v_resetjp_994_;
}
else
{
lean_inc(v_a_993_);
lean_dec(v___x_755_);
v___x_995_ = lean_box(0);
v_isShared_996_ = v_isSharedCheck_1000_;
goto v_resetjp_994_;
}
v_resetjp_994_:
{
lean_object* v___x_998_; 
if (v_isShared_996_ == 0)
{
v___x_998_ = v___x_995_;
goto v_reusejp_997_;
}
else
{
lean_object* v_reuseFailAlloc_999_; 
v_reuseFailAlloc_999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_999_, 0, v_a_993_);
v___x_998_ = v_reuseFailAlloc_999_;
goto v_reusejp_997_;
}
v_reusejp_997_:
{
return v___x_998_;
}
}
}
v___jp_581_:
{
lean_object* v___x_586_; 
v___x_586_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0___redArg(v_mvarId_561_, v_recursor_572_, v___y_583_);
if (lean_obj_tag(v___x_586_) == 0)
{
lean_object* v___x_588_; uint8_t v_isShared_589_; uint8_t v_isSharedCheck_627_; 
v_isSharedCheck_627_ = !lean_is_exclusive(v___x_586_);
if (v_isSharedCheck_627_ == 0)
{
lean_object* v_unused_628_; 
v_unused_628_ = lean_ctor_get(v___x_586_, 0);
lean_dec(v_unused_628_);
v___x_588_ = v___x_586_;
v_isShared_589_ = v_isSharedCheck_627_;
goto v_resetjp_587_;
}
else
{
lean_dec(v___x_586_);
v___x_588_ = lean_box(0);
v_isShared_589_ = v_isSharedCheck_627_;
goto v_resetjp_587_;
}
v_resetjp_587_:
{
lean_object* v_options_590_; uint8_t v_hasTrace_591_; 
v_options_590_ = lean_ctor_get(v___y_584_, 2);
v_hasTrace_591_ = lean_ctor_get_uint8(v_options_590_, sizeof(void*)*1);
if (v_hasTrace_591_ == 0)
{
lean_object* v___x_593_; 
if (v_isShared_589_ == 0)
{
lean_ctor_set(v___x_588_, 0, v_subgoals_575_);
v___x_593_ = v___x_588_;
goto v_reusejp_592_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v_subgoals_575_);
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
lean_object* v_inheritedTraceOptions_595_; lean_object* v___x_596_; lean_object* v___x_597_; uint8_t v___x_598_; 
v_inheritedTraceOptions_595_ = lean_ctor_get(v___y_584_, 13);
v___x_596_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__2));
v___x_597_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5);
v___x_598_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_595_, v_options_590_, v___x_597_);
if (v___x_598_ == 0)
{
lean_object* v___x_600_; 
if (v_isShared_589_ == 0)
{
lean_ctor_set(v___x_588_, 0, v_subgoals_575_);
v___x_600_ = v___x_588_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_601_; 
v_reuseFailAlloc_601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_601_, 0, v_subgoals_575_);
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
lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; 
lean_del_object(v___x_588_);
v___x_602_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__7, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__7_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__7);
v___x_603_ = lean_array_get_size(v_subgoals_575_);
v___x_604_ = l_Nat_reprFast(v___x_603_);
v___x_605_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_605_, 0, v___x_604_);
v___x_606_ = l_Lean_MessageData_ofFormat(v___x_605_);
v___x_607_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_607_, 0, v___x_602_);
lean_ctor_set(v___x_607_, 1, v___x_606_);
v___x_608_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__9, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__9_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__9);
v___x_609_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_609_, 0, v___x_607_);
lean_ctor_set(v___x_609_, 1, v___x_608_);
v___x_610_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1(v___x_596_, v___x_609_, v___y_582_, v___y_583_, v___y_584_, v___y_585_);
if (lean_obj_tag(v___x_610_) == 0)
{
lean_object* v___x_612_; uint8_t v_isShared_613_; uint8_t v_isSharedCheck_617_; 
v_isSharedCheck_617_ = !lean_is_exclusive(v___x_610_);
if (v_isSharedCheck_617_ == 0)
{
lean_object* v_unused_618_; 
v_unused_618_ = lean_ctor_get(v___x_610_, 0);
lean_dec(v_unused_618_);
v___x_612_ = v___x_610_;
v_isShared_613_ = v_isSharedCheck_617_;
goto v_resetjp_611_;
}
else
{
lean_dec(v___x_610_);
v___x_612_ = lean_box(0);
v_isShared_613_ = v_isSharedCheck_617_;
goto v_resetjp_611_;
}
v_resetjp_611_:
{
lean_object* v___x_615_; 
if (v_isShared_613_ == 0)
{
lean_ctor_set(v___x_612_, 0, v_subgoals_575_);
v___x_615_ = v___x_612_;
goto v_reusejp_614_;
}
else
{
lean_object* v_reuseFailAlloc_616_; 
v_reuseFailAlloc_616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_616_, 0, v_subgoals_575_);
v___x_615_ = v_reuseFailAlloc_616_;
goto v_reusejp_614_;
}
v_reusejp_614_:
{
return v___x_615_;
}
}
}
else
{
lean_object* v_a_619_; lean_object* v___x_621_; uint8_t v_isShared_622_; uint8_t v_isSharedCheck_626_; 
lean_dec_ref(v_subgoals_575_);
v_a_619_ = lean_ctor_get(v___x_610_, 0);
v_isSharedCheck_626_ = !lean_is_exclusive(v___x_610_);
if (v_isSharedCheck_626_ == 0)
{
v___x_621_ = v___x_610_;
v_isShared_622_ = v_isSharedCheck_626_;
goto v_resetjp_620_;
}
else
{
lean_inc(v_a_619_);
lean_dec(v___x_610_);
v___x_621_ = lean_box(0);
v_isShared_622_ = v_isSharedCheck_626_;
goto v_resetjp_620_;
}
v_resetjp_620_:
{
lean_object* v___x_624_; 
if (v_isShared_622_ == 0)
{
v___x_624_ = v___x_621_;
goto v_reusejp_623_;
}
else
{
lean_object* v_reuseFailAlloc_625_; 
v_reuseFailAlloc_625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_625_, 0, v_a_619_);
v___x_624_ = v_reuseFailAlloc_625_;
goto v_reusejp_623_;
}
v_reusejp_623_:
{
return v___x_624_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_629_; lean_object* v___x_631_; uint8_t v_isShared_632_; uint8_t v_isSharedCheck_636_; 
lean_dec_ref(v_subgoals_575_);
v_a_629_ = lean_ctor_get(v___x_586_, 0);
v_isSharedCheck_636_ = !lean_is_exclusive(v___x_586_);
if (v_isSharedCheck_636_ == 0)
{
v___x_631_ = v___x_586_;
v_isShared_632_ = v_isSharedCheck_636_;
goto v_resetjp_630_;
}
else
{
lean_inc(v_a_629_);
lean_dec(v___x_586_);
v___x_631_ = lean_box(0);
v_isShared_632_ = v_isSharedCheck_636_;
goto v_resetjp_630_;
}
v_resetjp_630_:
{
lean_object* v___x_634_; 
if (v_isShared_632_ == 0)
{
v___x_634_ = v___x_631_;
goto v_reusejp_633_;
}
else
{
lean_object* v_reuseFailAlloc_635_; 
v_reuseFailAlloc_635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_635_, 0, v_a_629_);
v___x_634_ = v_reuseFailAlloc_635_;
goto v_reusejp_633_;
}
v_reusejp_633_:
{
return v___x_634_;
}
}
}
}
v___jp_637_:
{
lean_object* v___x_654_; 
v___x_654_ = l_Lean_Meta_introNCore(v___y_646_, v___y_650_, v___y_645_, v___y_653_, v___y_639_, v___y_641_, v___y_647_, v___y_643_, v___y_648_);
if (lean_obj_tag(v___x_654_) == 0)
{
lean_object* v_a_655_; lean_object* v_fst_656_; lean_object* v_snd_657_; lean_object* v___x_658_; lean_object* v___x_659_; 
v_a_655_ = lean_ctor_get(v___x_654_, 0);
lean_inc(v_a_655_);
lean_dec_ref(v___x_654_);
v_fst_656_ = lean_ctor_get(v_a_655_, 0);
lean_inc(v_fst_656_);
v_snd_657_ = lean_ctor_get(v_a_655_, 1);
lean_inc(v_snd_657_);
lean_dec(v_a_655_);
v___x_658_ = lean_box(0);
v___x_659_ = l_Lean_Meta_introNCore(v_snd_657_, v___y_638_, v___x_658_, v___y_639_, v___y_652_, v___y_641_, v___y_647_, v___y_643_, v___y_648_);
if (lean_obj_tag(v___x_659_) == 0)
{
lean_object* v_a_660_; lean_object* v_fst_661_; lean_object* v_snd_662_; lean_object* v___x_663_; size_t v_sz_664_; size_t v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; 
v_a_660_ = lean_ctor_get(v___x_659_, 0);
lean_inc(v_a_660_);
lean_dec_ref(v___x_659_);
v_fst_661_ = lean_ctor_get(v_a_660_, 0);
lean_inc(v_fst_661_);
v_snd_662_ = lean_ctor_get(v_a_660_, 1);
lean_inc(v_snd_662_);
lean_dec(v_a_660_);
lean_inc(v_baseSubst_567_);
lean_inc(v___y_642_);
v___x_663_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__2___redArg(v___y_640_, v_reverted_564_, v_fst_661_, v___y_642_, v___y_642_, v_baseSubst_567_);
lean_dec(v___y_642_);
lean_dec(v_fst_661_);
lean_dec(v___y_640_);
v_sz_664_ = lean_array_size(v_fst_656_);
v___x_665_ = ((size_t)0ULL);
v___x_666_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__3(v_sz_664_, v___x_665_, v_fst_656_);
v___x_667_ = lean_nat_add(v_pos_570_, v___y_649_);
lean_dec(v_pos_570_);
v___x_668_ = lean_nat_add(v_minorIdx_571_, v___y_649_);
lean_dec(v_minorIdx_571_);
v___x_669_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_669_, 0, v_snd_662_);
lean_ctor_set(v___x_669_, 1, v___x_666_);
lean_ctor_set(v___x_669_, 2, v___x_663_);
v___x_670_ = lean_array_push(v_subgoals_575_, v___x_669_);
v_pos_570_ = v___x_667_;
v_minorIdx_571_ = v___x_668_;
v_recursor_572_ = v___y_644_;
v_recursorType_573_ = v___y_651_;
v_subgoals_575_ = v___x_670_;
v_a_576_ = v___y_641_;
v_a_577_ = v___y_647_;
v_a_578_ = v___y_643_;
v_a_579_ = v___y_648_;
goto _start;
}
else
{
lean_object* v_a_672_; lean_object* v___x_674_; uint8_t v_isShared_675_; uint8_t v_isSharedCheck_679_; 
lean_dec(v_fst_656_);
lean_dec_ref(v___y_651_);
lean_dec_ref(v___y_644_);
lean_dec(v___y_642_);
lean_dec(v___y_640_);
lean_dec_ref(v_subgoals_575_);
lean_dec(v_minorIdx_571_);
lean_dec(v_pos_570_);
lean_dec(v_baseSubst_567_);
lean_dec_ref(v_major_565_);
lean_dec(v_mvarId_561_);
v_a_672_ = lean_ctor_get(v___x_659_, 0);
v_isSharedCheck_679_ = !lean_is_exclusive(v___x_659_);
if (v_isSharedCheck_679_ == 0)
{
v___x_674_ = v___x_659_;
v_isShared_675_ = v_isSharedCheck_679_;
goto v_resetjp_673_;
}
else
{
lean_inc(v_a_672_);
lean_dec(v___x_659_);
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
else
{
lean_object* v_a_680_; lean_object* v___x_682_; uint8_t v_isShared_683_; uint8_t v_isSharedCheck_687_; 
lean_dec_ref(v___y_651_);
lean_dec_ref(v___y_644_);
lean_dec(v___y_642_);
lean_dec(v___y_640_);
lean_dec(v___y_638_);
lean_dec_ref(v_subgoals_575_);
lean_dec(v_minorIdx_571_);
lean_dec(v_pos_570_);
lean_dec(v_baseSubst_567_);
lean_dec_ref(v_major_565_);
lean_dec(v_mvarId_561_);
v_a_680_ = lean_ctor_get(v___x_654_, 0);
v_isSharedCheck_687_ = !lean_is_exclusive(v___x_654_);
if (v_isSharedCheck_687_ == 0)
{
v___x_682_ = v___x_654_;
v_isShared_683_ = v_isSharedCheck_687_;
goto v_resetjp_681_;
}
else
{
lean_inc(v_a_680_);
lean_dec(v___x_654_);
v___x_682_ = lean_box(0);
v_isShared_683_ = v_isSharedCheck_687_;
goto v_resetjp_681_;
}
v_resetjp_681_:
{
lean_object* v___x_685_; 
if (v_isShared_683_ == 0)
{
v___x_685_ = v___x_682_;
goto v_reusejp_684_;
}
else
{
lean_object* v_reuseFailAlloc_686_; 
v_reuseFailAlloc_686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_686_, 0, v_a_680_);
v___x_685_ = v_reuseFailAlloc_686_;
goto v_reusejp_684_;
}
v_reusejp_684_:
{
return v___x_685_;
}
}
}
}
v___jp_688_:
{
lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; 
v___x_704_ = l_Lean_Expr_mvarId_x21(v___y_689_);
lean_dec_ref(v___y_689_);
v___x_705_ = l_Lean_Expr_fvarId_x21(v_major_565_);
v___x_706_ = l_Lean_MVarId_tryClear(v___x_704_, v___x_705_, v___y_700_, v___y_701_, v___y_702_, v___y_703_);
if (lean_obj_tag(v___x_706_) == 0)
{
uint8_t v_explicit_707_; 
v_explicit_707_ = lean_ctor_get_uint8(v___y_694_, sizeof(void*)*1);
if (v_explicit_707_ == 0)
{
lean_object* v_a_708_; lean_object* v_varNames_709_; 
v_a_708_ = lean_ctor_get(v___x_706_, 0);
lean_inc(v_a_708_);
lean_dec_ref(v___x_706_);
v_varNames_709_ = lean_ctor_get(v___y_694_, 0);
lean_inc(v_varNames_709_);
lean_dec_ref(v___y_694_);
v___y_638_ = v___y_691_;
v___y_639_ = v___y_692_;
v___y_640_ = v___y_693_;
v___y_641_ = v___y_700_;
v___y_642_ = v___y_697_;
v___y_643_ = v___y_702_;
v___y_644_ = v___y_690_;
v___y_645_ = v_varNames_709_;
v___y_646_ = v_a_708_;
v___y_647_ = v___y_701_;
v___y_648_ = v___y_703_;
v___y_649_ = v___y_695_;
v___y_650_ = v___y_696_;
v___y_651_ = v___y_698_;
v___y_652_ = v___y_699_;
v___y_653_ = v___y_699_;
goto v___jp_637_;
}
else
{
lean_object* v_a_710_; lean_object* v_varNames_711_; 
v_a_710_ = lean_ctor_get(v___x_706_, 0);
lean_inc(v_a_710_);
lean_dec_ref(v___x_706_);
v_varNames_711_ = lean_ctor_get(v___y_694_, 0);
lean_inc(v_varNames_711_);
lean_dec_ref(v___y_694_);
v___y_638_ = v___y_691_;
v___y_639_ = v___y_692_;
v___y_640_ = v___y_693_;
v___y_641_ = v___y_700_;
v___y_642_ = v___y_697_;
v___y_643_ = v___y_702_;
v___y_644_ = v___y_690_;
v___y_645_ = v_varNames_711_;
v___y_646_ = v_a_710_;
v___y_647_ = v___y_701_;
v___y_648_ = v___y_703_;
v___y_649_ = v___y_695_;
v___y_650_ = v___y_696_;
v___y_651_ = v___y_698_;
v___y_652_ = v___y_699_;
v___y_653_ = v___y_692_;
goto v___jp_637_;
}
}
else
{
lean_object* v_a_712_; lean_object* v___x_714_; uint8_t v_isShared_715_; uint8_t v_isSharedCheck_719_; 
lean_dec_ref(v___y_698_);
lean_dec(v___y_697_);
lean_dec(v___y_696_);
lean_dec_ref(v___y_694_);
lean_dec(v___y_693_);
lean_dec(v___y_691_);
lean_dec_ref(v___y_690_);
lean_dec_ref(v_subgoals_575_);
lean_dec(v_minorIdx_571_);
lean_dec(v_pos_570_);
lean_dec(v_baseSubst_567_);
lean_dec_ref(v_major_565_);
lean_dec(v_mvarId_561_);
v_a_712_ = lean_ctor_get(v___x_706_, 0);
v_isSharedCheck_719_ = !lean_is_exclusive(v___x_706_);
if (v_isSharedCheck_719_ == 0)
{
v___x_714_ = v___x_706_;
v_isShared_715_ = v_isSharedCheck_719_;
goto v_resetjp_713_;
}
else
{
lean_inc(v_a_712_);
lean_dec(v___x_706_);
v___x_714_ = lean_box(0);
v_isShared_715_ = v_isSharedCheck_719_;
goto v_resetjp_713_;
}
v_resetjp_713_:
{
lean_object* v___x_717_; 
if (v_isShared_715_ == 0)
{
v___x_717_ = v___x_714_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_718_; 
v_reuseFailAlloc_718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_718_, 0, v_a_712_);
v___x_717_ = v_reuseFailAlloc_718_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
return v___x_717_;
}
}
}
}
v___jp_720_:
{
lean_object* v___x_725_; 
lean_inc(v_mvarId_561_);
v___x_725_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTypeBody(v_mvarId_561_, v_snd_724_, v_major_565_, v_a_576_, v_a_577_, v_a_578_, v_a_579_);
if (lean_obj_tag(v___x_725_) == 0)
{
lean_object* v_a_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; 
v_a_726_ = lean_ctor_get(v___x_725_, 0);
lean_inc(v_a_726_);
lean_dec_ref(v___x_725_);
lean_inc_ref(v_major_565_);
v___x_727_ = l_Lean_Expr_app___override(v_fst_723_, v_major_565_);
v___x_728_ = lean_unsigned_to_nat(1u);
v___x_729_ = lean_nat_add(v_pos_570_, v___x_728_);
lean_dec(v_pos_570_);
v___x_730_ = lean_nat_add(v___x_729_, v___y_722_);
lean_dec(v___y_722_);
lean_dec(v___x_729_);
v_pos_570_ = v___x_730_;
v_recursor_572_ = v___x_727_;
v_recursorType_573_ = v_a_726_;
v_consumedMajor_574_ = v___y_721_;
goto _start;
}
else
{
lean_object* v_a_732_; lean_object* v___x_734_; uint8_t v_isShared_735_; uint8_t v_isSharedCheck_739_; 
lean_dec_ref(v_fst_723_);
lean_dec(v___y_722_);
lean_dec_ref(v_subgoals_575_);
lean_dec(v_minorIdx_571_);
lean_dec(v_pos_570_);
lean_dec(v_baseSubst_567_);
lean_dec_ref(v_major_565_);
lean_dec(v_mvarId_561_);
v_a_732_ = lean_ctor_get(v___x_725_, 0);
v_isSharedCheck_739_ = !lean_is_exclusive(v___x_725_);
if (v_isSharedCheck_739_ == 0)
{
v___x_734_ = v___x_725_;
v_isShared_735_ = v_isSharedCheck_739_;
goto v_resetjp_733_;
}
else
{
lean_inc(v_a_732_);
lean_dec(v___x_725_);
v___x_734_ = lean_box(0);
v_isShared_735_ = v_isSharedCheck_739_;
goto v_resetjp_733_;
}
v_resetjp_733_:
{
lean_object* v___x_737_; 
if (v_isShared_735_ == 0)
{
v___x_737_ = v___x_734_;
goto v_reusejp_736_;
}
else
{
lean_object* v_reuseFailAlloc_738_; 
v_reuseFailAlloc_738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_738_, 0, v_a_732_);
v___x_737_ = v_reuseFailAlloc_738_;
goto v_reusejp_736_;
}
v_reusejp_736_:
{
return v___x_737_;
}
}
}
}
v___jp_740_:
{
if (lean_obj_tag(v___y_743_) == 0)
{
lean_object* v_a_744_; lean_object* v_fst_745_; lean_object* v_snd_746_; 
v_a_744_ = lean_ctor_get(v___y_743_, 0);
lean_inc(v_a_744_);
lean_dec_ref(v___y_743_);
v_fst_745_ = lean_ctor_get(v_a_744_, 0);
lean_inc(v_fst_745_);
v_snd_746_ = lean_ctor_get(v_a_744_, 1);
lean_inc(v_snd_746_);
lean_dec(v_a_744_);
v___y_721_ = v___y_742_;
v___y_722_ = v___y_741_;
v_fst_723_ = v_fst_745_;
v_snd_724_ = v_snd_746_;
goto v___jp_720_;
}
else
{
lean_object* v_a_747_; lean_object* v___x_749_; uint8_t v_isShared_750_; uint8_t v_isSharedCheck_754_; 
lean_dec(v___y_741_);
lean_dec_ref(v_subgoals_575_);
lean_dec(v_minorIdx_571_);
lean_dec(v_pos_570_);
lean_dec(v_baseSubst_567_);
lean_dec_ref(v_major_565_);
lean_dec(v_mvarId_561_);
v_a_747_ = lean_ctor_get(v___y_743_, 0);
v_isSharedCheck_754_ = !lean_is_exclusive(v___y_743_);
if (v_isSharedCheck_754_ == 0)
{
v___x_749_ = v___y_743_;
v_isShared_750_ = v_isSharedCheck_754_;
goto v_resetjp_748_;
}
else
{
lean_inc(v_a_747_);
lean_dec(v___y_743_);
v___x_749_ = lean_box(0);
v_isShared_750_ = v_isSharedCheck_754_;
goto v_resetjp_748_;
}
v_resetjp_748_:
{
lean_object* v___x_752_; 
if (v_isShared_750_ == 0)
{
v___x_752_ = v___x_749_;
goto v_reusejp_751_;
}
else
{
lean_object* v_reuseFailAlloc_753_; 
v_reuseFailAlloc_753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_753_, 0, v_a_747_);
v___x_752_ = v_reuseFailAlloc_753_;
goto v_reusejp_751_;
}
v_reusejp_751_:
{
return v___x_752_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___boxed(lean_object** _args){
lean_object* v_mvarId_1001_ = _args[0];
lean_object* v_givenNames_1002_ = _args[1];
lean_object* v_recursorInfo_1003_ = _args[2];
lean_object* v_reverted_1004_ = _args[3];
lean_object* v_major_1005_ = _args[4];
lean_object* v_indices_1006_ = _args[5];
lean_object* v_baseSubst_1007_ = _args[6];
lean_object* v_initialArity_1008_ = _args[7];
lean_object* v_numMinors_1009_ = _args[8];
lean_object* v_pos_1010_ = _args[9];
lean_object* v_minorIdx_1011_ = _args[10];
lean_object* v_recursor_1012_ = _args[11];
lean_object* v_recursorType_1013_ = _args[12];
lean_object* v_consumedMajor_1014_ = _args[13];
lean_object* v_subgoals_1015_ = _args[14];
lean_object* v_a_1016_ = _args[15];
lean_object* v_a_1017_ = _args[16];
lean_object* v_a_1018_ = _args[17];
lean_object* v_a_1019_ = _args[18];
lean_object* v_a_1020_ = _args[19];
_start:
{
uint8_t v_consumedMajor_boxed_1021_; lean_object* v_res_1022_; 
v_consumedMajor_boxed_1021_ = lean_unbox(v_consumedMajor_1014_);
v_res_1022_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop(v_mvarId_1001_, v_givenNames_1002_, v_recursorInfo_1003_, v_reverted_1004_, v_major_1005_, v_indices_1006_, v_baseSubst_1007_, v_initialArity_1008_, v_numMinors_1009_, v_pos_1010_, v_minorIdx_1011_, v_recursor_1012_, v_recursorType_1013_, v_consumedMajor_boxed_1021_, v_subgoals_1015_, v_a_1016_, v_a_1017_, v_a_1018_, v_a_1019_);
lean_dec(v_a_1019_);
lean_dec_ref(v_a_1018_);
lean_dec(v_a_1017_);
lean_dec_ref(v_a_1016_);
lean_dec(v_numMinors_1009_);
lean_dec(v_initialArity_1008_);
lean_dec_ref(v_indices_1006_);
lean_dec_ref(v_reverted_1004_);
lean_dec_ref(v_recursorInfo_1003_);
lean_dec_ref(v_givenNames_1002_);
return v_res_1022_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0(lean_object* v_mvarId_1023_, lean_object* v_val_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_){
_start:
{
lean_object* v___x_1030_; 
v___x_1030_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0___redArg(v_mvarId_1023_, v_val_1024_, v___y_1026_);
return v___x_1030_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0___boxed(lean_object* v_mvarId_1031_, lean_object* v_val_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_){
_start:
{
lean_object* v_res_1038_; 
v_res_1038_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0(v_mvarId_1031_, v_val_1032_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_);
lean_dec(v___y_1036_);
lean_dec_ref(v___y_1035_);
lean_dec(v___y_1034_);
lean_dec_ref(v___y_1033_);
return v_res_1038_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__2(lean_object* v___x_1039_, lean_object* v_reverted_1040_, lean_object* v_fst_1041_, lean_object* v_n_1042_, lean_object* v_j_1043_, lean_object* v_a_1044_, lean_object* v_a_1045_){
_start:
{
lean_object* v___x_1046_; 
v___x_1046_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__2___redArg(v___x_1039_, v_reverted_1040_, v_fst_1041_, v_n_1042_, v_j_1043_, v_a_1045_);
return v___x_1046_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__2___boxed(lean_object* v___x_1047_, lean_object* v_reverted_1048_, lean_object* v_fst_1049_, lean_object* v_n_1050_, lean_object* v_j_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_){
_start:
{
lean_object* v_res_1054_; 
v_res_1054_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__2(v___x_1047_, v_reverted_1048_, v_fst_1049_, v_n_1050_, v_j_1051_, v_a_1052_, v_a_1053_);
lean_dec(v_n_1050_);
lean_dec_ref(v_fst_1049_);
lean_dec_ref(v_reverted_1048_);
lean_dec(v___x_1047_);
return v_res_1054_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0(lean_object* v_00_u03b2_1055_, lean_object* v_x_1056_, lean_object* v_x_1057_, lean_object* v_x_1058_){
_start:
{
lean_object* v___x_1059_; 
v___x_1059_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0___redArg(v_x_1056_, v_x_1057_, v_x_1058_);
return v___x_1059_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1060_, lean_object* v_x_1061_, size_t v_x_1062_, size_t v_x_1063_, lean_object* v_x_1064_, lean_object* v_x_1065_){
_start:
{
lean_object* v___x_1066_; 
v___x_1066_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2___redArg(v_x_1061_, v_x_1062_, v_x_1063_, v_x_1064_, v_x_1065_);
return v___x_1066_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1067_, lean_object* v_x_1068_, lean_object* v_x_1069_, lean_object* v_x_1070_, lean_object* v_x_1071_, lean_object* v_x_1072_){
_start:
{
size_t v_x_11498__boxed_1073_; size_t v_x_11499__boxed_1074_; lean_object* v_res_1075_; 
v_x_11498__boxed_1073_ = lean_unbox_usize(v_x_1069_);
lean_dec(v_x_1069_);
v_x_11499__boxed_1074_ = lean_unbox_usize(v_x_1070_);
lean_dec(v_x_1070_);
v_res_1075_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2(v_00_u03b2_1067_, v_x_1068_, v_x_11498__boxed_1073_, v_x_11499__boxed_1074_, v_x_1071_, v_x_1072_);
return v_res_1075_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__8(lean_object* v_00_u03b2_1076_, lean_object* v_n_1077_, lean_object* v_k_1078_, lean_object* v_v_1079_){
_start:
{
lean_object* v___x_1080_; 
v___x_1080_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__8___redArg(v_n_1077_, v_k_1078_, v_v_1079_);
return v___x_1080_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__9(lean_object* v_00_u03b2_1081_, size_t v_depth_1082_, lean_object* v_keys_1083_, lean_object* v_vals_1084_, lean_object* v_heq_1085_, lean_object* v_i_1086_, lean_object* v_entries_1087_){
_start:
{
lean_object* v___x_1088_; 
v___x_1088_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__9___redArg(v_depth_1082_, v_keys_1083_, v_vals_1084_, v_i_1086_, v_entries_1087_);
return v___x_1088_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__9___boxed(lean_object* v_00_u03b2_1089_, lean_object* v_depth_1090_, lean_object* v_keys_1091_, lean_object* v_vals_1092_, lean_object* v_heq_1093_, lean_object* v_i_1094_, lean_object* v_entries_1095_){
_start:
{
size_t v_depth_boxed_1096_; lean_object* v_res_1097_; 
v_depth_boxed_1096_ = lean_unbox_usize(v_depth_1090_);
lean_dec(v_depth_1090_);
v_res_1097_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__9(v_00_u03b2_1089_, v_depth_boxed_1096_, v_keys_1091_, v_vals_1092_, v_heq_1093_, v_i_1094_, v_entries_1095_);
lean_dec_ref(v_vals_1092_);
lean_dec_ref(v_keys_1091_);
return v_res_1097_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__8_spec__9(lean_object* v_00_u03b2_1098_, lean_object* v_x_1099_, lean_object* v_x_1100_, lean_object* v_x_1101_, lean_object* v_x_1102_){
_start:
{
lean_object* v___x_1103_; 
v___x_1103_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__8_spec__9___redArg(v_x_1099_, v_x_1100_, v_x_1101_, v_x_1102_);
return v___x_1103_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize(lean_object* v_mvarId_1106_, lean_object* v_givenNames_1107_, lean_object* v_recursorInfo_1108_, lean_object* v_reverted_1109_, lean_object* v_major_1110_, lean_object* v_indices_1111_, lean_object* v_baseSubst_1112_, lean_object* v_recursor_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_, lean_object* v_a_1117_){
_start:
{
lean_object* v___x_1119_; 
lean_inc(v_mvarId_1106_);
v___x_1119_ = l_Lean_MVarId_getType(v_mvarId_1106_, v_a_1114_, v_a_1115_, v_a_1116_, v_a_1117_);
if (lean_obj_tag(v___x_1119_) == 0)
{
lean_object* v_a_1120_; lean_object* v___x_1121_; 
v_a_1120_ = lean_ctor_get(v___x_1119_, 0);
lean_inc(v_a_1120_);
lean_dec_ref(v___x_1119_);
lean_inc(v_a_1117_);
lean_inc_ref(v_a_1116_);
lean_inc(v_a_1115_);
lean_inc_ref(v_a_1114_);
lean_inc_ref(v_recursor_1113_);
v___x_1121_ = lean_infer_type(v_recursor_1113_, v_a_1114_, v_a_1115_, v_a_1116_, v_a_1117_);
if (lean_obj_tag(v___x_1121_) == 0)
{
lean_object* v_a_1122_; lean_object* v_paramsPos_1123_; lean_object* v_produceMotive_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; uint8_t v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; 
v_a_1122_ = lean_ctor_get(v___x_1121_, 0);
lean_inc(v_a_1122_);
lean_dec_ref(v___x_1121_);
v_paramsPos_1123_ = lean_ctor_get(v_recursorInfo_1108_, 5);
v_produceMotive_1124_ = lean_ctor_get(v_recursorInfo_1108_, 7);
v___x_1125_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTargetArity(v_a_1120_);
v___x_1126_ = l_List_lengthTR___redArg(v_produceMotive_1124_);
v___x_1127_ = l_List_lengthTR___redArg(v_paramsPos_1123_);
v___x_1128_ = lean_unsigned_to_nat(1u);
v___x_1129_ = lean_nat_add(v___x_1127_, v___x_1128_);
lean_dec(v___x_1127_);
v___x_1130_ = lean_unsigned_to_nat(0u);
v___x_1131_ = 0;
v___x_1132_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize___closed__0));
v___x_1133_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop(v_mvarId_1106_, v_givenNames_1107_, v_recursorInfo_1108_, v_reverted_1109_, v_major_1110_, v_indices_1111_, v_baseSubst_1112_, v___x_1125_, v___x_1126_, v___x_1129_, v___x_1130_, v_recursor_1113_, v_a_1122_, v___x_1131_, v___x_1132_, v_a_1114_, v_a_1115_, v_a_1116_, v_a_1117_);
lean_dec(v___x_1126_);
lean_dec(v___x_1125_);
return v___x_1133_;
}
else
{
lean_object* v_a_1134_; lean_object* v___x_1136_; uint8_t v_isShared_1137_; uint8_t v_isSharedCheck_1141_; 
lean_dec(v_a_1120_);
lean_dec_ref(v_recursor_1113_);
lean_dec(v_baseSubst_1112_);
lean_dec_ref(v_major_1110_);
lean_dec(v_mvarId_1106_);
v_a_1134_ = lean_ctor_get(v___x_1121_, 0);
v_isSharedCheck_1141_ = !lean_is_exclusive(v___x_1121_);
if (v_isSharedCheck_1141_ == 0)
{
v___x_1136_ = v___x_1121_;
v_isShared_1137_ = v_isSharedCheck_1141_;
goto v_resetjp_1135_;
}
else
{
lean_inc(v_a_1134_);
lean_dec(v___x_1121_);
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
else
{
lean_object* v_a_1142_; lean_object* v___x_1144_; uint8_t v_isShared_1145_; uint8_t v_isSharedCheck_1149_; 
lean_dec_ref(v_recursor_1113_);
lean_dec(v_baseSubst_1112_);
lean_dec_ref(v_major_1110_);
lean_dec(v_mvarId_1106_);
v_a_1142_ = lean_ctor_get(v___x_1119_, 0);
v_isSharedCheck_1149_ = !lean_is_exclusive(v___x_1119_);
if (v_isSharedCheck_1149_ == 0)
{
v___x_1144_ = v___x_1119_;
v_isShared_1145_ = v_isSharedCheck_1149_;
goto v_resetjp_1143_;
}
else
{
lean_inc(v_a_1142_);
lean_dec(v___x_1119_);
v___x_1144_ = lean_box(0);
v_isShared_1145_ = v_isSharedCheck_1149_;
goto v_resetjp_1143_;
}
v_resetjp_1143_:
{
lean_object* v___x_1147_; 
if (v_isShared_1145_ == 0)
{
v___x_1147_ = v___x_1144_;
goto v_reusejp_1146_;
}
else
{
lean_object* v_reuseFailAlloc_1148_; 
v_reuseFailAlloc_1148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1148_, 0, v_a_1142_);
v___x_1147_ = v_reuseFailAlloc_1148_;
goto v_reusejp_1146_;
}
v_reusejp_1146_:
{
return v___x_1147_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize___boxed(lean_object* v_mvarId_1150_, lean_object* v_givenNames_1151_, lean_object* v_recursorInfo_1152_, lean_object* v_reverted_1153_, lean_object* v_major_1154_, lean_object* v_indices_1155_, lean_object* v_baseSubst_1156_, lean_object* v_recursor_1157_, lean_object* v_a_1158_, lean_object* v_a_1159_, lean_object* v_a_1160_, lean_object* v_a_1161_, lean_object* v_a_1162_){
_start:
{
lean_object* v_res_1163_; 
v_res_1163_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize(v_mvarId_1150_, v_givenNames_1151_, v_recursorInfo_1152_, v_reverted_1153_, v_major_1154_, v_indices_1155_, v_baseSubst_1156_, v_recursor_1157_, v_a_1158_, v_a_1159_, v_a_1160_, v_a_1161_);
lean_dec(v_a_1161_);
lean_dec_ref(v_a_1160_);
lean_dec(v_a_1159_);
lean_dec_ref(v_a_1158_);
lean_dec_ref(v_indices_1155_);
lean_dec_ref(v_reverted_1153_);
lean_dec_ref(v_recursorInfo_1152_);
lean_dec_ref(v_givenNames_1151_);
return v_res_1163_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg___closed__1(void){
_start:
{
lean_object* v___x_1165_; lean_object* v___x_1166_; 
v___x_1165_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg___closed__0));
v___x_1166_ = l_Lean_stringToMessageData(v___x_1165_);
return v___x_1166_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg(lean_object* v_tacticName_1167_, lean_object* v_mvarId_1168_, lean_object* v_majorType_1169_, lean_object* v_a_1170_, lean_object* v_a_1171_, lean_object* v_a_1172_, lean_object* v_a_1173_){
_start:
{
lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; 
v___x_1175_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg___closed__1, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg___closed__1);
v___x_1176_ = l_Lean_indentExpr(v_majorType_1169_);
v___x_1177_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1177_, 0, v___x_1175_);
lean_ctor_set(v___x_1177_, 1, v___x_1176_);
v___x_1178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1178_, 0, v___x_1177_);
v___x_1179_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1167_, v_mvarId_1168_, v___x_1178_, v_a_1170_, v_a_1171_, v_a_1172_, v_a_1173_);
return v___x_1179_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg___boxed(lean_object* v_tacticName_1180_, lean_object* v_mvarId_1181_, lean_object* v_majorType_1182_, lean_object* v_a_1183_, lean_object* v_a_1184_, lean_object* v_a_1185_, lean_object* v_a_1186_, lean_object* v_a_1187_){
_start:
{
lean_object* v_res_1188_; 
v_res_1188_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg(v_tacticName_1180_, v_mvarId_1181_, v_majorType_1182_, v_a_1183_, v_a_1184_, v_a_1185_, v_a_1186_);
lean_dec(v_a_1186_);
lean_dec_ref(v_a_1185_);
lean_dec(v_a_1184_);
lean_dec_ref(v_a_1183_);
return v_res_1188_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType(lean_object* v_00_u03b1_1189_, lean_object* v_tacticName_1190_, lean_object* v_mvarId_1191_, lean_object* v_majorType_1192_, lean_object* v_a_1193_, lean_object* v_a_1194_, lean_object* v_a_1195_, lean_object* v_a_1196_){
_start:
{
lean_object* v___x_1198_; 
v___x_1198_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg(v_tacticName_1190_, v_mvarId_1191_, v_majorType_1192_, v_a_1193_, v_a_1194_, v_a_1195_, v_a_1196_);
return v___x_1198_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___boxed(lean_object* v_00_u03b1_1199_, lean_object* v_tacticName_1200_, lean_object* v_mvarId_1201_, lean_object* v_majorType_1202_, lean_object* v_a_1203_, lean_object* v_a_1204_, lean_object* v_a_1205_, lean_object* v_a_1206_, lean_object* v_a_1207_){
_start:
{
lean_object* v_res_1208_; 
v_res_1208_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType(v_00_u03b1_1199_, v_tacticName_1200_, v_mvarId_1201_, v_majorType_1202_, v_a_1203_, v_a_1204_, v_a_1205_, v_a_1206_);
lean_dec(v_a_1206_);
lean_dec_ref(v_a_1205_);
lean_dec(v_a_1204_);
lean_dec_ref(v_a_1203_);
return v_res_1208_;
}
}
LEAN_EXPORT uint8_t l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___lam__0(lean_object* v_fvarId_1209_, lean_object* v_x_1210_){
_start:
{
uint8_t v___x_1211_; 
v___x_1211_ = l_Lean_instBEqFVarId_beq(v_fvarId_1209_, v_x_1210_);
return v___x_1211_;
}
}
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___lam__0___boxed(lean_object* v_fvarId_1212_, lean_object* v_x_1213_){
_start:
{
uint8_t v_res_1214_; lean_object* v_r_1215_; 
v_res_1214_ = l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___lam__0(v_fvarId_1212_, v_x_1213_);
lean_dec(v_x_1213_);
lean_dec(v_fvarId_1212_);
v_r_1215_ = lean_box(v_res_1214_);
return v_r_1215_;
}
}
LEAN_EXPORT uint8_t l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___lam__1(lean_object* v_x_1216_){
_start:
{
uint8_t v___x_1217_; 
v___x_1217_ = 0;
return v___x_1217_;
}
}
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___lam__1___boxed(lean_object* v_x_1218_){
_start:
{
uint8_t v_res_1219_; lean_object* v_r_1220_; 
v_res_1219_ = l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___lam__1(v_x_1218_);
lean_dec(v_x_1218_);
v_r_1220_ = lean_box(v_res_1219_);
return v_r_1220_;
}
}
static lean_object* _init_l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; 
v___x_1222_ = lean_box(0);
v___x_1223_ = lean_unsigned_to_nat(16u);
v___x_1224_ = lean_mk_array(v___x_1223_, v___x_1222_);
return v___x_1224_;
}
}
static lean_object* _init_l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; 
v___x_1225_ = lean_obj_once(&l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__1, &l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__1_once, _init_l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__1);
v___x_1226_ = lean_unsigned_to_nat(0u);
v___x_1227_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1227_, 0, v___x_1226_);
lean_ctor_set(v___x_1227_, 1, v___x_1225_);
return v___x_1227_;
}
}
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg(lean_object* v_localDecl_1228_, lean_object* v_fvarId_1229_, uint8_t v_generalizeNondepLet_1230_, lean_object* v___y_1231_){
_start:
{
uint8_t v_fst_1234_; lean_object* v_snd_1235_; lean_object* v___y_1254_; lean_object* v___f_1258_; lean_object* v___f_1259_; 
v___f_1258_ = lean_alloc_closure((void*)(l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1258_, 0, v_fvarId_1229_);
v___f_1259_ = ((lean_object*)(l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__0));
if (lean_obj_tag(v_localDecl_1228_) == 0)
{
lean_object* v_type_1260_; lean_object* v___x_1261_; uint8_t v_fst_1263_; lean_object* v_mctx_1264_; lean_object* v___y_1282_; lean_object* v_mctx_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; uint8_t v___x_1290_; 
v_type_1260_ = lean_ctor_get(v_localDecl_1228_, 3);
lean_inc_ref(v_type_1260_);
lean_dec_ref(v_localDecl_1228_);
v___x_1261_ = lean_st_ref_get(v___y_1231_);
v_mctx_1287_ = lean_ctor_get(v___x_1261_, 0);
lean_inc_ref_n(v_mctx_1287_, 2);
lean_dec(v___x_1261_);
v___x_1288_ = lean_obj_once(&l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__2, &l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__2_once, _init_l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__2);
v___x_1289_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1289_, 0, v___x_1288_);
lean_ctor_set(v___x_1289_, 1, v_mctx_1287_);
v___x_1290_ = l_Lean_Expr_hasFVar(v_type_1260_);
if (v___x_1290_ == 0)
{
uint8_t v___x_1291_; 
v___x_1291_ = l_Lean_Expr_hasMVar(v_type_1260_);
if (v___x_1291_ == 0)
{
lean_dec_ref(v___x_1289_);
lean_dec_ref(v_type_1260_);
lean_dec_ref(v___f_1258_);
v_fst_1263_ = v___x_1291_;
v_mctx_1264_ = v_mctx_1287_;
goto v___jp_1262_;
}
else
{
lean_object* v___x_1292_; 
lean_dec_ref(v_mctx_1287_);
v___x_1292_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1258_, v___f_1259_, v_type_1260_, v___x_1289_);
v___y_1282_ = v___x_1292_;
goto v___jp_1281_;
}
}
else
{
lean_object* v___x_1293_; 
lean_dec_ref(v_mctx_1287_);
v___x_1293_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1258_, v___f_1259_, v_type_1260_, v___x_1289_);
v___y_1282_ = v___x_1293_;
goto v___jp_1281_;
}
v___jp_1262_:
{
lean_object* v___x_1265_; lean_object* v_cache_1266_; lean_object* v_zetaDeltaFVarIds_1267_; lean_object* v_postponed_1268_; lean_object* v_diag_1269_; lean_object* v___x_1271_; uint8_t v_isShared_1272_; uint8_t v_isSharedCheck_1279_; 
v___x_1265_ = lean_st_ref_take(v___y_1231_);
v_cache_1266_ = lean_ctor_get(v___x_1265_, 1);
v_zetaDeltaFVarIds_1267_ = lean_ctor_get(v___x_1265_, 2);
v_postponed_1268_ = lean_ctor_get(v___x_1265_, 3);
v_diag_1269_ = lean_ctor_get(v___x_1265_, 4);
v_isSharedCheck_1279_ = !lean_is_exclusive(v___x_1265_);
if (v_isSharedCheck_1279_ == 0)
{
lean_object* v_unused_1280_; 
v_unused_1280_ = lean_ctor_get(v___x_1265_, 0);
lean_dec(v_unused_1280_);
v___x_1271_ = v___x_1265_;
v_isShared_1272_ = v_isSharedCheck_1279_;
goto v_resetjp_1270_;
}
else
{
lean_inc(v_diag_1269_);
lean_inc(v_postponed_1268_);
lean_inc(v_zetaDeltaFVarIds_1267_);
lean_inc(v_cache_1266_);
lean_dec(v___x_1265_);
v___x_1271_ = lean_box(0);
v_isShared_1272_ = v_isSharedCheck_1279_;
goto v_resetjp_1270_;
}
v_resetjp_1270_:
{
lean_object* v___x_1274_; 
if (v_isShared_1272_ == 0)
{
lean_ctor_set(v___x_1271_, 0, v_mctx_1264_);
v___x_1274_ = v___x_1271_;
goto v_reusejp_1273_;
}
else
{
lean_object* v_reuseFailAlloc_1278_; 
v_reuseFailAlloc_1278_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1278_, 0, v_mctx_1264_);
lean_ctor_set(v_reuseFailAlloc_1278_, 1, v_cache_1266_);
lean_ctor_set(v_reuseFailAlloc_1278_, 2, v_zetaDeltaFVarIds_1267_);
lean_ctor_set(v_reuseFailAlloc_1278_, 3, v_postponed_1268_);
lean_ctor_set(v_reuseFailAlloc_1278_, 4, v_diag_1269_);
v___x_1274_ = v_reuseFailAlloc_1278_;
goto v_reusejp_1273_;
}
v_reusejp_1273_:
{
lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; 
v___x_1275_ = lean_st_ref_set(v___y_1231_, v___x_1274_);
v___x_1276_ = lean_box(v_fst_1263_);
v___x_1277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1277_, 0, v___x_1276_);
return v___x_1277_;
}
}
}
v___jp_1281_:
{
lean_object* v_snd_1283_; lean_object* v_fst_1284_; lean_object* v_mctx_1285_; uint8_t v___x_1286_; 
v_snd_1283_ = lean_ctor_get(v___y_1282_, 1);
lean_inc(v_snd_1283_);
v_fst_1284_ = lean_ctor_get(v___y_1282_, 0);
lean_inc(v_fst_1284_);
lean_dec_ref(v___y_1282_);
v_mctx_1285_ = lean_ctor_get(v_snd_1283_, 1);
lean_inc_ref(v_mctx_1285_);
lean_dec(v_snd_1283_);
v___x_1286_ = lean_unbox(v_fst_1284_);
lean_dec(v_fst_1284_);
v_fst_1263_ = v___x_1286_;
v_mctx_1264_ = v_mctx_1285_;
goto v___jp_1262_;
}
}
else
{
lean_object* v_type_1294_; lean_object* v_value_1295_; uint8_t v_nondep_1296_; uint8_t v_fst_1298_; lean_object* v_snd_1299_; lean_object* v___y_1305_; 
v_type_1294_ = lean_ctor_get(v_localDecl_1228_, 3);
lean_inc_ref(v_type_1294_);
v_value_1295_ = lean_ctor_get(v_localDecl_1228_, 4);
lean_inc_ref(v_value_1295_);
v_nondep_1296_ = lean_ctor_get_uint8(v_localDecl_1228_, sizeof(void*)*5);
lean_dec_ref(v_localDecl_1228_);
if (v_generalizeNondepLet_1230_ == 0)
{
goto v___jp_1309_;
}
else
{
if (v_nondep_1296_ == 0)
{
goto v___jp_1309_;
}
else
{
lean_object* v___x_1318_; uint8_t v_fst_1320_; lean_object* v_mctx_1321_; lean_object* v___y_1339_; lean_object* v_mctx_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; uint8_t v___x_1347_; 
lean_dec_ref(v_value_1295_);
v___x_1318_ = lean_st_ref_get(v___y_1231_);
v_mctx_1344_ = lean_ctor_get(v___x_1318_, 0);
lean_inc_ref_n(v_mctx_1344_, 2);
lean_dec(v___x_1318_);
v___x_1345_ = lean_obj_once(&l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__2, &l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__2_once, _init_l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__2);
v___x_1346_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1346_, 0, v___x_1345_);
lean_ctor_set(v___x_1346_, 1, v_mctx_1344_);
v___x_1347_ = l_Lean_Expr_hasFVar(v_type_1294_);
if (v___x_1347_ == 0)
{
uint8_t v___x_1348_; 
v___x_1348_ = l_Lean_Expr_hasMVar(v_type_1294_);
if (v___x_1348_ == 0)
{
lean_dec_ref(v___x_1346_);
lean_dec_ref(v_type_1294_);
lean_dec_ref(v___f_1258_);
v_fst_1320_ = v___x_1348_;
v_mctx_1321_ = v_mctx_1344_;
goto v___jp_1319_;
}
else
{
lean_object* v___x_1349_; 
lean_dec_ref(v_mctx_1344_);
v___x_1349_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1258_, v___f_1259_, v_type_1294_, v___x_1346_);
v___y_1339_ = v___x_1349_;
goto v___jp_1338_;
}
}
else
{
lean_object* v___x_1350_; 
lean_dec_ref(v_mctx_1344_);
v___x_1350_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1258_, v___f_1259_, v_type_1294_, v___x_1346_);
v___y_1339_ = v___x_1350_;
goto v___jp_1338_;
}
v___jp_1319_:
{
lean_object* v___x_1322_; lean_object* v_cache_1323_; lean_object* v_zetaDeltaFVarIds_1324_; lean_object* v_postponed_1325_; lean_object* v_diag_1326_; lean_object* v___x_1328_; uint8_t v_isShared_1329_; uint8_t v_isSharedCheck_1336_; 
v___x_1322_ = lean_st_ref_take(v___y_1231_);
v_cache_1323_ = lean_ctor_get(v___x_1322_, 1);
v_zetaDeltaFVarIds_1324_ = lean_ctor_get(v___x_1322_, 2);
v_postponed_1325_ = lean_ctor_get(v___x_1322_, 3);
v_diag_1326_ = lean_ctor_get(v___x_1322_, 4);
v_isSharedCheck_1336_ = !lean_is_exclusive(v___x_1322_);
if (v_isSharedCheck_1336_ == 0)
{
lean_object* v_unused_1337_; 
v_unused_1337_ = lean_ctor_get(v___x_1322_, 0);
lean_dec(v_unused_1337_);
v___x_1328_ = v___x_1322_;
v_isShared_1329_ = v_isSharedCheck_1336_;
goto v_resetjp_1327_;
}
else
{
lean_inc(v_diag_1326_);
lean_inc(v_postponed_1325_);
lean_inc(v_zetaDeltaFVarIds_1324_);
lean_inc(v_cache_1323_);
lean_dec(v___x_1322_);
v___x_1328_ = lean_box(0);
v_isShared_1329_ = v_isSharedCheck_1336_;
goto v_resetjp_1327_;
}
v_resetjp_1327_:
{
lean_object* v___x_1331_; 
if (v_isShared_1329_ == 0)
{
lean_ctor_set(v___x_1328_, 0, v_mctx_1321_);
v___x_1331_ = v___x_1328_;
goto v_reusejp_1330_;
}
else
{
lean_object* v_reuseFailAlloc_1335_; 
v_reuseFailAlloc_1335_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1335_, 0, v_mctx_1321_);
lean_ctor_set(v_reuseFailAlloc_1335_, 1, v_cache_1323_);
lean_ctor_set(v_reuseFailAlloc_1335_, 2, v_zetaDeltaFVarIds_1324_);
lean_ctor_set(v_reuseFailAlloc_1335_, 3, v_postponed_1325_);
lean_ctor_set(v_reuseFailAlloc_1335_, 4, v_diag_1326_);
v___x_1331_ = v_reuseFailAlloc_1335_;
goto v_reusejp_1330_;
}
v_reusejp_1330_:
{
lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; 
v___x_1332_ = lean_st_ref_set(v___y_1231_, v___x_1331_);
v___x_1333_ = lean_box(v_fst_1320_);
v___x_1334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1334_, 0, v___x_1333_);
return v___x_1334_;
}
}
}
v___jp_1338_:
{
lean_object* v_snd_1340_; lean_object* v_fst_1341_; lean_object* v_mctx_1342_; uint8_t v___x_1343_; 
v_snd_1340_ = lean_ctor_get(v___y_1339_, 1);
lean_inc(v_snd_1340_);
v_fst_1341_ = lean_ctor_get(v___y_1339_, 0);
lean_inc(v_fst_1341_);
lean_dec_ref(v___y_1339_);
v_mctx_1342_ = lean_ctor_get(v_snd_1340_, 1);
lean_inc_ref(v_mctx_1342_);
lean_dec(v_snd_1340_);
v___x_1343_ = lean_unbox(v_fst_1341_);
lean_dec(v_fst_1341_);
v_fst_1320_ = v___x_1343_;
v_mctx_1321_ = v_mctx_1342_;
goto v___jp_1319_;
}
}
}
v___jp_1297_:
{
if (v_fst_1298_ == 0)
{
uint8_t v___x_1300_; 
v___x_1300_ = l_Lean_Expr_hasFVar(v_value_1295_);
if (v___x_1300_ == 0)
{
uint8_t v___x_1301_; 
v___x_1301_ = l_Lean_Expr_hasMVar(v_value_1295_);
if (v___x_1301_ == 0)
{
lean_dec_ref(v_value_1295_);
lean_dec_ref(v___f_1258_);
v_fst_1234_ = v___x_1301_;
v_snd_1235_ = v_snd_1299_;
goto v___jp_1233_;
}
else
{
lean_object* v___x_1302_; 
v___x_1302_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1258_, v___f_1259_, v_value_1295_, v_snd_1299_);
v___y_1254_ = v___x_1302_;
goto v___jp_1253_;
}
}
else
{
lean_object* v___x_1303_; 
v___x_1303_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1258_, v___f_1259_, v_value_1295_, v_snd_1299_);
v___y_1254_ = v___x_1303_;
goto v___jp_1253_;
}
}
else
{
lean_dec_ref(v_value_1295_);
lean_dec_ref(v___f_1258_);
v_fst_1234_ = v_fst_1298_;
v_snd_1235_ = v_snd_1299_;
goto v___jp_1233_;
}
}
v___jp_1304_:
{
lean_object* v_fst_1306_; lean_object* v_snd_1307_; uint8_t v___x_1308_; 
v_fst_1306_ = lean_ctor_get(v___y_1305_, 0);
lean_inc(v_fst_1306_);
v_snd_1307_ = lean_ctor_get(v___y_1305_, 1);
lean_inc(v_snd_1307_);
lean_dec_ref(v___y_1305_);
v___x_1308_ = lean_unbox(v_fst_1306_);
lean_dec(v_fst_1306_);
v_fst_1298_ = v___x_1308_;
v_snd_1299_ = v_snd_1307_;
goto v___jp_1297_;
}
v___jp_1309_:
{
lean_object* v___x_1310_; lean_object* v_mctx_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; uint8_t v___x_1314_; 
v___x_1310_ = lean_st_ref_get(v___y_1231_);
v_mctx_1311_ = lean_ctor_get(v___x_1310_, 0);
lean_inc_ref(v_mctx_1311_);
lean_dec(v___x_1310_);
v___x_1312_ = lean_obj_once(&l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__2, &l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__2_once, _init_l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__2);
v___x_1313_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1313_, 0, v___x_1312_);
lean_ctor_set(v___x_1313_, 1, v_mctx_1311_);
v___x_1314_ = l_Lean_Expr_hasFVar(v_type_1294_);
if (v___x_1314_ == 0)
{
uint8_t v___x_1315_; 
v___x_1315_ = l_Lean_Expr_hasMVar(v_type_1294_);
if (v___x_1315_ == 0)
{
lean_dec_ref(v_type_1294_);
v_fst_1298_ = v___x_1315_;
v_snd_1299_ = v___x_1313_;
goto v___jp_1297_;
}
else
{
lean_object* v___x_1316_; 
lean_inc_ref(v___f_1258_);
v___x_1316_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1258_, v___f_1259_, v_type_1294_, v___x_1313_);
v___y_1305_ = v___x_1316_;
goto v___jp_1304_;
}
}
else
{
lean_object* v___x_1317_; 
lean_inc_ref(v___f_1258_);
v___x_1317_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1258_, v___f_1259_, v_type_1294_, v___x_1313_);
v___y_1305_ = v___x_1317_;
goto v___jp_1304_;
}
}
}
v___jp_1233_:
{
lean_object* v_mctx_1236_; lean_object* v___x_1237_; lean_object* v_cache_1238_; lean_object* v_zetaDeltaFVarIds_1239_; lean_object* v_postponed_1240_; lean_object* v_diag_1241_; lean_object* v___x_1243_; uint8_t v_isShared_1244_; uint8_t v_isSharedCheck_1251_; 
v_mctx_1236_ = lean_ctor_get(v_snd_1235_, 1);
lean_inc_ref(v_mctx_1236_);
lean_dec_ref(v_snd_1235_);
v___x_1237_ = lean_st_ref_take(v___y_1231_);
v_cache_1238_ = lean_ctor_get(v___x_1237_, 1);
v_zetaDeltaFVarIds_1239_ = lean_ctor_get(v___x_1237_, 2);
v_postponed_1240_ = lean_ctor_get(v___x_1237_, 3);
v_diag_1241_ = lean_ctor_get(v___x_1237_, 4);
v_isSharedCheck_1251_ = !lean_is_exclusive(v___x_1237_);
if (v_isSharedCheck_1251_ == 0)
{
lean_object* v_unused_1252_; 
v_unused_1252_ = lean_ctor_get(v___x_1237_, 0);
lean_dec(v_unused_1252_);
v___x_1243_ = v___x_1237_;
v_isShared_1244_ = v_isSharedCheck_1251_;
goto v_resetjp_1242_;
}
else
{
lean_inc(v_diag_1241_);
lean_inc(v_postponed_1240_);
lean_inc(v_zetaDeltaFVarIds_1239_);
lean_inc(v_cache_1238_);
lean_dec(v___x_1237_);
v___x_1243_ = lean_box(0);
v_isShared_1244_ = v_isSharedCheck_1251_;
goto v_resetjp_1242_;
}
v_resetjp_1242_:
{
lean_object* v___x_1246_; 
if (v_isShared_1244_ == 0)
{
lean_ctor_set(v___x_1243_, 0, v_mctx_1236_);
v___x_1246_ = v___x_1243_;
goto v_reusejp_1245_;
}
else
{
lean_object* v_reuseFailAlloc_1250_; 
v_reuseFailAlloc_1250_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1250_, 0, v_mctx_1236_);
lean_ctor_set(v_reuseFailAlloc_1250_, 1, v_cache_1238_);
lean_ctor_set(v_reuseFailAlloc_1250_, 2, v_zetaDeltaFVarIds_1239_);
lean_ctor_set(v_reuseFailAlloc_1250_, 3, v_postponed_1240_);
lean_ctor_set(v_reuseFailAlloc_1250_, 4, v_diag_1241_);
v___x_1246_ = v_reuseFailAlloc_1250_;
goto v_reusejp_1245_;
}
v_reusejp_1245_:
{
lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; 
v___x_1247_ = lean_st_ref_set(v___y_1231_, v___x_1246_);
v___x_1248_ = lean_box(v_fst_1234_);
v___x_1249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1249_, 0, v___x_1248_);
return v___x_1249_;
}
}
}
v___jp_1253_:
{
lean_object* v_fst_1255_; lean_object* v_snd_1256_; uint8_t v___x_1257_; 
v_fst_1255_ = lean_ctor_get(v___y_1254_, 0);
lean_inc(v_fst_1255_);
v_snd_1256_ = lean_ctor_get(v___y_1254_, 1);
lean_inc(v_snd_1256_);
lean_dec_ref(v___y_1254_);
v___x_1257_ = lean_unbox(v_fst_1255_);
lean_dec(v_fst_1255_);
v_fst_1234_ = v___x_1257_;
v_snd_1235_ = v_snd_1256_;
goto v___jp_1233_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___boxed(lean_object* v_localDecl_1351_, lean_object* v_fvarId_1352_, lean_object* v_generalizeNondepLet_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_){
_start:
{
uint8_t v_generalizeNondepLet_boxed_1356_; lean_object* v_res_1357_; 
v_generalizeNondepLet_boxed_1356_ = lean_unbox(v_generalizeNondepLet_1353_);
v_res_1357_ = l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg(v_localDecl_1351_, v_fvarId_1352_, v_generalizeNondepLet_boxed_1356_, v___y_1354_);
lean_dec(v___y_1354_);
return v_res_1357_;
}
}
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0(lean_object* v_localDecl_1358_, lean_object* v_fvarId_1359_, uint8_t v_generalizeNondepLet_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_){
_start:
{
lean_object* v___x_1366_; 
v___x_1366_ = l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg(v_localDecl_1358_, v_fvarId_1359_, v_generalizeNondepLet_1360_, v___y_1362_);
return v___x_1366_;
}
}
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___boxed(lean_object* v_localDecl_1367_, lean_object* v_fvarId_1368_, lean_object* v_generalizeNondepLet_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_){
_start:
{
uint8_t v_generalizeNondepLet_boxed_1375_; lean_object* v_res_1376_; 
v_generalizeNondepLet_boxed_1375_ = lean_unbox(v_generalizeNondepLet_1369_);
v_res_1376_ = l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0(v_localDecl_1367_, v_fvarId_1368_, v_generalizeNondepLet_boxed_1375_, v___y_1370_, v___y_1371_, v___y_1372_, v___y_1373_);
lean_dec(v___y_1373_);
lean_dec_ref(v___y_1372_);
lean_dec(v___y_1371_);
lean_dec_ref(v___y_1370_);
return v_res_1376_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2___redArg(lean_object* v_e_1377_, lean_object* v_fvarId_1378_, lean_object* v___y_1379_){
_start:
{
lean_object* v___x_1381_; uint8_t v_fst_1383_; lean_object* v_mctx_1384_; lean_object* v___y_1402_; lean_object* v_mctx_1407_; lean_object* v___f_1408_; lean_object* v___f_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; uint8_t v___x_1412_; 
v___x_1381_ = lean_st_ref_get(v___y_1379_);
v_mctx_1407_ = lean_ctor_get(v___x_1381_, 0);
lean_inc_ref_n(v_mctx_1407_, 2);
lean_dec(v___x_1381_);
v___f_1408_ = ((lean_object*)(l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__0));
v___f_1409_ = lean_alloc_closure((void*)(l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1409_, 0, v_fvarId_1378_);
v___x_1410_ = lean_obj_once(&l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__2, &l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__2_once, _init_l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__2);
v___x_1411_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1411_, 0, v___x_1410_);
lean_ctor_set(v___x_1411_, 1, v_mctx_1407_);
v___x_1412_ = l_Lean_Expr_hasFVar(v_e_1377_);
if (v___x_1412_ == 0)
{
uint8_t v___x_1413_; 
v___x_1413_ = l_Lean_Expr_hasMVar(v_e_1377_);
if (v___x_1413_ == 0)
{
lean_dec_ref(v___x_1411_);
lean_dec_ref(v___f_1409_);
lean_dec_ref(v_e_1377_);
v_fst_1383_ = v___x_1413_;
v_mctx_1384_ = v_mctx_1407_;
goto v___jp_1382_;
}
else
{
lean_object* v___x_1414_; 
lean_dec_ref(v_mctx_1407_);
v___x_1414_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1409_, v___f_1408_, v_e_1377_, v___x_1411_);
v___y_1402_ = v___x_1414_;
goto v___jp_1401_;
}
}
else
{
lean_object* v___x_1415_; 
lean_dec_ref(v_mctx_1407_);
v___x_1415_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1409_, v___f_1408_, v_e_1377_, v___x_1411_);
v___y_1402_ = v___x_1415_;
goto v___jp_1401_;
}
v___jp_1382_:
{
lean_object* v___x_1385_; lean_object* v_cache_1386_; lean_object* v_zetaDeltaFVarIds_1387_; lean_object* v_postponed_1388_; lean_object* v_diag_1389_; lean_object* v___x_1391_; uint8_t v_isShared_1392_; uint8_t v_isSharedCheck_1399_; 
v___x_1385_ = lean_st_ref_take(v___y_1379_);
v_cache_1386_ = lean_ctor_get(v___x_1385_, 1);
v_zetaDeltaFVarIds_1387_ = lean_ctor_get(v___x_1385_, 2);
v_postponed_1388_ = lean_ctor_get(v___x_1385_, 3);
v_diag_1389_ = lean_ctor_get(v___x_1385_, 4);
v_isSharedCheck_1399_ = !lean_is_exclusive(v___x_1385_);
if (v_isSharedCheck_1399_ == 0)
{
lean_object* v_unused_1400_; 
v_unused_1400_ = lean_ctor_get(v___x_1385_, 0);
lean_dec(v_unused_1400_);
v___x_1391_ = v___x_1385_;
v_isShared_1392_ = v_isSharedCheck_1399_;
goto v_resetjp_1390_;
}
else
{
lean_inc(v_diag_1389_);
lean_inc(v_postponed_1388_);
lean_inc(v_zetaDeltaFVarIds_1387_);
lean_inc(v_cache_1386_);
lean_dec(v___x_1385_);
v___x_1391_ = lean_box(0);
v_isShared_1392_ = v_isSharedCheck_1399_;
goto v_resetjp_1390_;
}
v_resetjp_1390_:
{
lean_object* v___x_1394_; 
if (v_isShared_1392_ == 0)
{
lean_ctor_set(v___x_1391_, 0, v_mctx_1384_);
v___x_1394_ = v___x_1391_;
goto v_reusejp_1393_;
}
else
{
lean_object* v_reuseFailAlloc_1398_; 
v_reuseFailAlloc_1398_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1398_, 0, v_mctx_1384_);
lean_ctor_set(v_reuseFailAlloc_1398_, 1, v_cache_1386_);
lean_ctor_set(v_reuseFailAlloc_1398_, 2, v_zetaDeltaFVarIds_1387_);
lean_ctor_set(v_reuseFailAlloc_1398_, 3, v_postponed_1388_);
lean_ctor_set(v_reuseFailAlloc_1398_, 4, v_diag_1389_);
v___x_1394_ = v_reuseFailAlloc_1398_;
goto v_reusejp_1393_;
}
v_reusejp_1393_:
{
lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; 
v___x_1395_ = lean_st_ref_set(v___y_1379_, v___x_1394_);
v___x_1396_ = lean_box(v_fst_1383_);
v___x_1397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1397_, 0, v___x_1396_);
return v___x_1397_;
}
}
}
v___jp_1401_:
{
lean_object* v_snd_1403_; lean_object* v_fst_1404_; lean_object* v_mctx_1405_; uint8_t v___x_1406_; 
v_snd_1403_ = lean_ctor_get(v___y_1402_, 1);
lean_inc(v_snd_1403_);
v_fst_1404_ = lean_ctor_get(v___y_1402_, 0);
lean_inc(v_fst_1404_);
lean_dec_ref(v___y_1402_);
v_mctx_1405_ = lean_ctor_get(v_snd_1403_, 1);
lean_inc_ref(v_mctx_1405_);
lean_dec(v_snd_1403_);
v___x_1406_ = lean_unbox(v_fst_1404_);
lean_dec(v_fst_1404_);
v_fst_1383_ = v___x_1406_;
v_mctx_1384_ = v_mctx_1405_;
goto v___jp_1382_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2___redArg___boxed(lean_object* v_e_1416_, lean_object* v_fvarId_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_){
_start:
{
lean_object* v_res_1420_; 
v_res_1420_ = l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2___redArg(v_e_1416_, v_fvarId_1417_, v___y_1418_);
lean_dec(v___y_1418_);
return v_res_1420_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2(lean_object* v_e_1421_, lean_object* v_fvarId_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_){
_start:
{
lean_object* v___x_1428_; 
v___x_1428_ = l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2___redArg(v_e_1421_, v_fvarId_1422_, v___y_1424_);
return v___x_1428_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2___boxed(lean_object* v_e_1429_, lean_object* v_fvarId_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_){
_start:
{
lean_object* v_res_1436_; 
v_res_1436_ = l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2(v_e_1429_, v_fvarId_1430_, v___y_1431_, v___y_1432_, v___y_1433_, v___y_1434_);
lean_dec(v___y_1434_);
lean_dec_ref(v___y_1433_);
lean_dec(v___y_1432_);
lean_dec_ref(v___y_1431_);
return v_res_1436_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_Meta_getMajorTypeIndices_spec__1(lean_object* v_a_1437_, lean_object* v_x_1438_){
_start:
{
if (lean_obj_tag(v_x_1438_) == 0)
{
uint8_t v___x_1439_; 
v___x_1439_ = 0;
return v___x_1439_;
}
else
{
lean_object* v_head_1440_; lean_object* v_tail_1441_; uint8_t v___x_1442_; 
v_head_1440_ = lean_ctor_get(v_x_1438_, 0);
v_tail_1441_ = lean_ctor_get(v_x_1438_, 1);
v___x_1442_ = lean_nat_dec_eq(v_a_1437_, v_head_1440_);
if (v___x_1442_ == 0)
{
v_x_1438_ = v_tail_1441_;
goto _start;
}
else
{
return v___x_1442_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_Meta_getMajorTypeIndices_spec__1___boxed(lean_object* v_a_1444_, lean_object* v_x_1445_){
_start:
{
uint8_t v_res_1446_; lean_object* v_r_1447_; 
v_res_1446_ = l_List_elem___at___00Lean_Meta_getMajorTypeIndices_spec__1(v_a_1444_, v_x_1445_);
lean_dec(v_x_1445_);
lean_dec(v_a_1444_);
v_r_1447_ = lean_box(v_res_1446_);
return v_r_1447_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_1449_; lean_object* v___x_1450_; 
v___x_1449_ = ((lean_object*)(l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__0));
v___x_1450_ = l_Lean_stringToMessageData(v___x_1449_);
return v___x_1450_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_1452_; lean_object* v___x_1453_; 
v___x_1452_ = ((lean_object*)(l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__2));
v___x_1453_ = l_Lean_stringToMessageData(v___x_1452_);
return v___x_1453_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__5(void){
_start:
{
lean_object* v___x_1455_; lean_object* v___x_1456_; 
v___x_1455_ = ((lean_object*)(l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__4));
v___x_1456_ = l_Lean_stringToMessageData(v___x_1455_);
return v___x_1456_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__7(void){
_start:
{
lean_object* v___x_1458_; lean_object* v___x_1459_; 
v___x_1458_ = ((lean_object*)(l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__6));
v___x_1459_ = l_Lean_stringToMessageData(v___x_1458_);
return v___x_1459_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg(lean_object* v_majorTypeArgs_1460_, lean_object* v_idx_1461_, lean_object* v_tacticName_1462_, lean_object* v_mvarId_1463_, lean_object* v_idxPos_1464_, lean_object* v_recursorInfo_1465_, lean_object* v_majorType_1466_, lean_object* v_n_1467_, lean_object* v_i_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_){
_start:
{
lean_object* v_zero_1474_; uint8_t v_isZero_1475_; 
v_zero_1474_ = lean_unsigned_to_nat(0u);
v_isZero_1475_ = lean_nat_dec_eq(v_i_1468_, v_zero_1474_);
if (v_isZero_1475_ == 1)
{
lean_object* v___x_1476_; lean_object* v___x_1477_; 
lean_dec(v_i_1468_);
lean_dec_ref(v_majorType_1466_);
lean_dec(v_mvarId_1463_);
lean_dec(v_tacticName_1462_);
lean_dec_ref(v_idx_1461_);
v___x_1476_ = lean_box(0);
v___x_1477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1477_, 0, v___x_1476_);
return v___x_1477_;
}
else
{
lean_object* v_one_1478_; lean_object* v_n_1479_; lean_object* v___y_1481_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v_arg_1485_; lean_object* v___y_1487_; lean_object* v___y_1488_; lean_object* v___y_1489_; lean_object* v___y_1490_; uint8_t v___y_1491_; lean_object* v___y_1530_; lean_object* v___y_1531_; lean_object* v___y_1532_; lean_object* v___y_1533_; lean_object* v___y_1538_; lean_object* v___y_1539_; lean_object* v___y_1540_; lean_object* v___y_1541_; uint8_t v___x_1562_; 
v_one_1478_ = lean_unsigned_to_nat(1u);
v_n_1479_ = lean_nat_sub(v_i_1468_, v_one_1478_);
lean_dec(v_i_1468_);
v___x_1483_ = lean_nat_sub(v_n_1467_, v_n_1479_);
v___x_1484_ = lean_nat_sub(v___x_1483_, v_one_1478_);
lean_dec(v___x_1483_);
v_arg_1485_ = lean_array_fget_borrowed(v_majorTypeArgs_1460_, v___x_1484_);
v___x_1562_ = lean_nat_dec_eq(v___x_1484_, v_idxPos_1464_);
if (v___x_1562_ == 0)
{
uint8_t v___x_1563_; 
v___x_1563_ = lean_expr_eqv(v_arg_1485_, v_idx_1461_);
if (v___x_1563_ == 0)
{
v___y_1538_ = v___y_1469_;
v___y_1539_ = v___y_1470_;
v___y_1540_ = v___y_1471_;
v___y_1541_ = v___y_1472_;
goto v___jp_1537_;
}
else
{
lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; 
v___x_1564_ = lean_obj_once(&l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1, &l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1_once, _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1);
lean_inc_ref(v_idx_1461_);
v___x_1565_ = l_Lean_MessageData_ofExpr(v_idx_1461_);
v___x_1566_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1566_, 0, v___x_1564_);
lean_ctor_set(v___x_1566_, 1, v___x_1565_);
v___x_1567_ = lean_obj_once(&l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__7, &l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__7_once, _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__7);
v___x_1568_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1568_, 0, v___x_1566_);
lean_ctor_set(v___x_1568_, 1, v___x_1567_);
lean_inc_ref(v_majorType_1466_);
v___x_1569_ = l_Lean_indentExpr(v_majorType_1466_);
v___x_1570_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1570_, 0, v___x_1568_);
lean_ctor_set(v___x_1570_, 1, v___x_1569_);
v___x_1571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1571_, 0, v___x_1570_);
lean_inc(v_mvarId_1463_);
lean_inc(v_tacticName_1462_);
v___x_1572_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1462_, v_mvarId_1463_, v___x_1571_, v___y_1469_, v___y_1470_, v___y_1471_, v___y_1472_);
if (lean_obj_tag(v___x_1572_) == 0)
{
lean_dec_ref(v___x_1572_);
v___y_1538_ = v___y_1469_;
v___y_1539_ = v___y_1470_;
v___y_1540_ = v___y_1471_;
v___y_1541_ = v___y_1472_;
goto v___jp_1537_;
}
else
{
lean_dec(v___x_1484_);
v___y_1481_ = v___x_1572_;
goto v___jp_1480_;
}
}
}
else
{
v___y_1538_ = v___y_1469_;
v___y_1539_ = v___y_1470_;
v___y_1540_ = v___y_1471_;
v___y_1541_ = v___y_1472_;
goto v___jp_1537_;
}
v___jp_1480_:
{
if (lean_obj_tag(v___y_1481_) == 0)
{
lean_dec_ref(v___y_1481_);
v_i_1468_ = v_n_1479_;
goto _start;
}
else
{
lean_dec(v_n_1479_);
lean_dec_ref(v_majorType_1466_);
lean_dec(v_mvarId_1463_);
lean_dec(v_tacticName_1462_);
lean_dec_ref(v_idx_1461_);
return v___y_1481_;
}
}
v___jp_1486_:
{
if (v___y_1491_ == 0)
{
lean_dec(v___x_1484_);
v_i_1468_ = v_n_1479_;
goto _start;
}
else
{
uint8_t v___x_1493_; 
v___x_1493_ = l_Lean_Expr_isFVar(v_arg_1485_);
if (v___x_1493_ == 0)
{
lean_dec(v___x_1484_);
v_i_1468_ = v_n_1479_;
goto _start;
}
else
{
lean_object* v___x_1495_; lean_object* v___x_1496_; 
v___x_1495_ = l_Lean_Expr_fvarId_x21(v_idx_1461_);
v___x_1496_ = l_Lean_FVarId_getDecl___redArg(v___x_1495_, v___y_1488_, v___y_1487_, v___y_1490_);
if (lean_obj_tag(v___x_1496_) == 0)
{
lean_object* v_a_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v_a_1500_; lean_object* v___x_1502_; uint8_t v_isShared_1503_; uint8_t v_isSharedCheck_1520_; 
v_a_1497_ = lean_ctor_get(v___x_1496_, 0);
lean_inc(v_a_1497_);
lean_dec_ref(v___x_1496_);
v___x_1498_ = l_Lean_Expr_fvarId_x21(v_arg_1485_);
v___x_1499_ = l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg(v_a_1497_, v___x_1498_, v___y_1491_, v___y_1489_);
v_a_1500_ = lean_ctor_get(v___x_1499_, 0);
v_isSharedCheck_1520_ = !lean_is_exclusive(v___x_1499_);
if (v_isSharedCheck_1520_ == 0)
{
v___x_1502_ = v___x_1499_;
v_isShared_1503_ = v_isSharedCheck_1520_;
goto v_resetjp_1501_;
}
else
{
lean_inc(v_a_1500_);
lean_dec(v___x_1499_);
v___x_1502_ = lean_box(0);
v_isShared_1503_ = v_isSharedCheck_1520_;
goto v_resetjp_1501_;
}
v_resetjp_1501_:
{
uint8_t v___x_1504_; 
v___x_1504_ = lean_unbox(v_a_1500_);
lean_dec(v_a_1500_);
if (v___x_1504_ == 0)
{
lean_del_object(v___x_1502_);
lean_dec(v___x_1484_);
v_i_1468_ = v_n_1479_;
goto _start;
}
else
{
lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1514_; 
v___x_1506_ = lean_obj_once(&l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1, &l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1_once, _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1);
lean_inc_ref(v_idx_1461_);
v___x_1507_ = l_Lean_MessageData_ofExpr(v_idx_1461_);
v___x_1508_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1508_, 0, v___x_1506_);
lean_ctor_set(v___x_1508_, 1, v___x_1507_);
v___x_1509_ = lean_obj_once(&l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__3, &l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__3_once, _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__3);
v___x_1510_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1510_, 0, v___x_1508_);
lean_ctor_set(v___x_1510_, 1, v___x_1509_);
v___x_1511_ = lean_nat_add(v___x_1484_, v_one_1478_);
lean_dec(v___x_1484_);
v___x_1512_ = l_Nat_reprFast(v___x_1511_);
if (v_isShared_1503_ == 0)
{
lean_ctor_set_tag(v___x_1502_, 3);
lean_ctor_set(v___x_1502_, 0, v___x_1512_);
v___x_1514_ = v___x_1502_;
goto v_reusejp_1513_;
}
else
{
lean_object* v_reuseFailAlloc_1519_; 
v_reuseFailAlloc_1519_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1519_, 0, v___x_1512_);
v___x_1514_ = v_reuseFailAlloc_1519_;
goto v_reusejp_1513_;
}
v_reusejp_1513_:
{
lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; 
v___x_1515_ = l_Lean_MessageData_ofFormat(v___x_1514_);
v___x_1516_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1516_, 0, v___x_1510_);
lean_ctor_set(v___x_1516_, 1, v___x_1515_);
v___x_1517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1517_, 0, v___x_1516_);
lean_inc(v_mvarId_1463_);
lean_inc(v_tacticName_1462_);
v___x_1518_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1462_, v_mvarId_1463_, v___x_1517_, v___y_1488_, v___y_1489_, v___y_1487_, v___y_1490_);
v___y_1481_ = v___x_1518_;
goto v___jp_1480_;
}
}
}
}
else
{
lean_object* v_a_1521_; lean_object* v___x_1523_; uint8_t v_isShared_1524_; uint8_t v_isSharedCheck_1528_; 
lean_dec(v___x_1484_);
lean_dec(v_n_1479_);
lean_dec_ref(v_majorType_1466_);
lean_dec(v_mvarId_1463_);
lean_dec(v_tacticName_1462_);
lean_dec_ref(v_idx_1461_);
v_a_1521_ = lean_ctor_get(v___x_1496_, 0);
v_isSharedCheck_1528_ = !lean_is_exclusive(v___x_1496_);
if (v_isSharedCheck_1528_ == 0)
{
v___x_1523_ = v___x_1496_;
v_isShared_1524_ = v_isSharedCheck_1528_;
goto v_resetjp_1522_;
}
else
{
lean_inc(v_a_1521_);
lean_dec(v___x_1496_);
v___x_1523_ = lean_box(0);
v_isShared_1524_ = v_isSharedCheck_1528_;
goto v_resetjp_1522_;
}
v_resetjp_1522_:
{
lean_object* v___x_1526_; 
if (v_isShared_1524_ == 0)
{
v___x_1526_ = v___x_1523_;
goto v_reusejp_1525_;
}
else
{
lean_object* v_reuseFailAlloc_1527_; 
v_reuseFailAlloc_1527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1527_, 0, v_a_1521_);
v___x_1526_ = v_reuseFailAlloc_1527_;
goto v_reusejp_1525_;
}
v_reusejp_1525_:
{
return v___x_1526_;
}
}
}
}
}
}
v___jp_1529_:
{
uint8_t v___x_1534_; 
v___x_1534_ = lean_nat_dec_lt(v_idxPos_1464_, v___x_1484_);
if (v___x_1534_ == 0)
{
v___y_1487_ = v___y_1532_;
v___y_1488_ = v___y_1530_;
v___y_1489_ = v___y_1531_;
v___y_1490_ = v___y_1533_;
v___y_1491_ = v___x_1534_;
goto v___jp_1486_;
}
else
{
lean_object* v_indicesPos_1535_; uint8_t v___x_1536_; 
v_indicesPos_1535_ = lean_ctor_get(v_recursorInfo_1465_, 6);
v___x_1536_ = l_List_elem___at___00Lean_Meta_getMajorTypeIndices_spec__1(v___x_1484_, v_indicesPos_1535_);
v___y_1487_ = v___y_1532_;
v___y_1488_ = v___y_1530_;
v___y_1489_ = v___y_1531_;
v___y_1490_ = v___y_1533_;
v___y_1491_ = v___x_1536_;
goto v___jp_1486_;
}
}
v___jp_1537_:
{
uint8_t v___x_1542_; 
v___x_1542_ = lean_nat_dec_lt(v___x_1484_, v_idxPos_1464_);
if (v___x_1542_ == 0)
{
v___y_1530_ = v___y_1538_;
v___y_1531_ = v___y_1539_;
v___y_1532_ = v___y_1540_;
v___y_1533_ = v___y_1541_;
goto v___jp_1529_;
}
else
{
lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v_a_1545_; lean_object* v___x_1547_; uint8_t v_isShared_1548_; uint8_t v_isSharedCheck_1561_; 
v___x_1543_ = l_Lean_Expr_fvarId_x21(v_idx_1461_);
lean_inc(v_arg_1485_);
v___x_1544_ = l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2___redArg(v_arg_1485_, v___x_1543_, v___y_1539_);
v_a_1545_ = lean_ctor_get(v___x_1544_, 0);
v_isSharedCheck_1561_ = !lean_is_exclusive(v___x_1544_);
if (v_isSharedCheck_1561_ == 0)
{
v___x_1547_ = v___x_1544_;
v_isShared_1548_ = v_isSharedCheck_1561_;
goto v_resetjp_1546_;
}
else
{
lean_inc(v_a_1545_);
lean_dec(v___x_1544_);
v___x_1547_ = lean_box(0);
v_isShared_1548_ = v_isSharedCheck_1561_;
goto v_resetjp_1546_;
}
v_resetjp_1546_:
{
uint8_t v___x_1549_; 
v___x_1549_ = lean_unbox(v_a_1545_);
lean_dec(v_a_1545_);
if (v___x_1549_ == 0)
{
lean_del_object(v___x_1547_);
v___y_1530_ = v___y_1538_;
v___y_1531_ = v___y_1539_;
v___y_1532_ = v___y_1540_;
v___y_1533_ = v___y_1541_;
goto v___jp_1529_;
}
else
{
lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1558_; 
v___x_1550_ = lean_obj_once(&l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1, &l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1_once, _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1);
lean_inc_ref(v_idx_1461_);
v___x_1551_ = l_Lean_MessageData_ofExpr(v_idx_1461_);
v___x_1552_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1552_, 0, v___x_1550_);
lean_ctor_set(v___x_1552_, 1, v___x_1551_);
v___x_1553_ = lean_obj_once(&l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__5, &l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__5_once, _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__5);
v___x_1554_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1554_, 0, v___x_1552_);
lean_ctor_set(v___x_1554_, 1, v___x_1553_);
lean_inc_ref(v_majorType_1466_);
v___x_1555_ = l_Lean_indentExpr(v_majorType_1466_);
v___x_1556_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1556_, 0, v___x_1554_);
lean_ctor_set(v___x_1556_, 1, v___x_1555_);
if (v_isShared_1548_ == 0)
{
lean_ctor_set_tag(v___x_1547_, 1);
lean_ctor_set(v___x_1547_, 0, v___x_1556_);
v___x_1558_ = v___x_1547_;
goto v_reusejp_1557_;
}
else
{
lean_object* v_reuseFailAlloc_1560_; 
v_reuseFailAlloc_1560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1560_, 0, v___x_1556_);
v___x_1558_ = v_reuseFailAlloc_1560_;
goto v_reusejp_1557_;
}
v_reusejp_1557_:
{
lean_object* v___x_1559_; 
lean_inc(v_mvarId_1463_);
lean_inc(v_tacticName_1462_);
v___x_1559_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1462_, v_mvarId_1463_, v___x_1558_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_);
if (lean_obj_tag(v___x_1559_) == 0)
{
lean_dec_ref(v___x_1559_);
v___y_1530_ = v___y_1538_;
v___y_1531_ = v___y_1539_;
v___y_1532_ = v___y_1540_;
v___y_1533_ = v___y_1541_;
goto v___jp_1529_;
}
else
{
lean_dec(v___x_1484_);
v___y_1481_ = v___x_1559_;
goto v___jp_1480_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___boxed(lean_object* v_majorTypeArgs_1573_, lean_object* v_idx_1574_, lean_object* v_tacticName_1575_, lean_object* v_mvarId_1576_, lean_object* v_idxPos_1577_, lean_object* v_recursorInfo_1578_, lean_object* v_majorType_1579_, lean_object* v_n_1580_, lean_object* v_i_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_){
_start:
{
lean_object* v_res_1587_; 
v_res_1587_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg(v_majorTypeArgs_1573_, v_idx_1574_, v_tacticName_1575_, v_mvarId_1576_, v_idxPos_1577_, v_recursorInfo_1578_, v_majorType_1579_, v_n_1580_, v_i_1581_, v___y_1582_, v___y_1583_, v___y_1584_, v___y_1585_);
lean_dec(v___y_1585_);
lean_dec_ref(v___y_1584_);
lean_dec(v___y_1583_);
lean_dec_ref(v___y_1582_);
lean_dec(v_n_1580_);
lean_dec_ref(v_recursorInfo_1578_);
lean_dec(v_idxPos_1577_);
lean_dec_ref(v_majorTypeArgs_1573_);
return v_res_1587_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__1(void){
_start:
{
lean_object* v___x_1589_; lean_object* v___x_1590_; 
v___x_1589_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__0));
v___x_1590_ = l_Lean_stringToMessageData(v___x_1589_);
return v___x_1590_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__3(void){
_start:
{
lean_object* v___x_1592_; lean_object* v___x_1593_; 
v___x_1592_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__2));
v___x_1593_ = l_Lean_stringToMessageData(v___x_1592_);
return v___x_1593_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__5(void){
_start:
{
lean_object* v___x_1595_; lean_object* v___x_1596_; 
v___x_1595_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__4));
v___x_1596_ = l_Lean_stringToMessageData(v___x_1595_);
return v___x_1596_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4(lean_object* v_majorTypeArgs_1597_, lean_object* v_tacticName_1598_, lean_object* v_mvarId_1599_, lean_object* v_recursorInfo_1600_, lean_object* v_majorType_1601_, size_t v_sz_1602_, size_t v_i_1603_, lean_object* v_bs_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_){
_start:
{
uint8_t v___x_1610_; 
v___x_1610_ = lean_usize_dec_lt(v_i_1603_, v_sz_1602_);
if (v___x_1610_ == 0)
{
lean_object* v___x_1611_; 
lean_dec_ref(v_majorType_1601_);
lean_dec(v_mvarId_1599_);
lean_dec(v_tacticName_1598_);
v___x_1611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1611_, 0, v_bs_1604_);
return v___x_1611_;
}
else
{
lean_object* v_v_1612_; lean_object* v___x_1613_; lean_object* v_bs_x27_1614_; lean_object* v_a_1616_; lean_object* v___x_1621_; uint8_t v___x_1622_; 
v_v_1612_ = lean_array_uget(v_bs_1604_, v_i_1603_);
v___x_1613_ = lean_unsigned_to_nat(0u);
v_bs_x27_1614_ = lean_array_uset(v_bs_1604_, v_i_1603_, v___x_1613_);
v___x_1621_ = lean_array_get_size(v_majorTypeArgs_1597_);
v___x_1622_ = lean_nat_dec_le(v___x_1621_, v_v_1612_);
if (v___x_1622_ == 0)
{
lean_object* v_idx_1623_; lean_object* v___y_1625_; lean_object* v___y_1626_; lean_object* v___y_1627_; lean_object* v___y_1628_; uint8_t v___x_1638_; 
v_idx_1623_ = lean_array_fget_borrowed(v_majorTypeArgs_1597_, v_v_1612_);
v___x_1638_ = l_Lean_Expr_isFVar(v_idx_1623_);
if (v___x_1638_ == 0)
{
lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; 
v___x_1639_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__1);
lean_inc(v_idx_1623_);
v___x_1640_ = l_Lean_MessageData_ofExpr(v_idx_1623_);
v___x_1641_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1641_, 0, v___x_1639_);
lean_ctor_set(v___x_1641_, 1, v___x_1640_);
v___x_1642_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__3);
v___x_1643_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1643_, 0, v___x_1641_);
lean_ctor_set(v___x_1643_, 1, v___x_1642_);
lean_inc_ref(v_majorType_1601_);
v___x_1644_ = l_Lean_indentExpr(v_majorType_1601_);
v___x_1645_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1645_, 0, v___x_1643_);
lean_ctor_set(v___x_1645_, 1, v___x_1644_);
v___x_1646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1646_, 0, v___x_1645_);
lean_inc(v_mvarId_1599_);
lean_inc(v_tacticName_1598_);
v___x_1647_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1598_, v_mvarId_1599_, v___x_1646_, v___y_1605_, v___y_1606_, v___y_1607_, v___y_1608_);
if (lean_obj_tag(v___x_1647_) == 0)
{
lean_dec_ref(v___x_1647_);
v___y_1625_ = v___y_1605_;
v___y_1626_ = v___y_1606_;
v___y_1627_ = v___y_1607_;
v___y_1628_ = v___y_1608_;
goto v___jp_1624_;
}
else
{
lean_object* v_a_1648_; lean_object* v___x_1650_; uint8_t v_isShared_1651_; uint8_t v_isSharedCheck_1655_; 
lean_dec_ref(v_bs_x27_1614_);
lean_dec(v_v_1612_);
lean_dec_ref(v_majorType_1601_);
lean_dec(v_mvarId_1599_);
lean_dec(v_tacticName_1598_);
v_a_1648_ = lean_ctor_get(v___x_1647_, 0);
v_isSharedCheck_1655_ = !lean_is_exclusive(v___x_1647_);
if (v_isSharedCheck_1655_ == 0)
{
v___x_1650_ = v___x_1647_;
v_isShared_1651_ = v_isSharedCheck_1655_;
goto v_resetjp_1649_;
}
else
{
lean_inc(v_a_1648_);
lean_dec(v___x_1647_);
v___x_1650_ = lean_box(0);
v_isShared_1651_ = v_isSharedCheck_1655_;
goto v_resetjp_1649_;
}
v_resetjp_1649_:
{
lean_object* v___x_1653_; 
if (v_isShared_1651_ == 0)
{
v___x_1653_ = v___x_1650_;
goto v_reusejp_1652_;
}
else
{
lean_object* v_reuseFailAlloc_1654_; 
v_reuseFailAlloc_1654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1654_, 0, v_a_1648_);
v___x_1653_ = v_reuseFailAlloc_1654_;
goto v_reusejp_1652_;
}
v_reusejp_1652_:
{
return v___x_1653_;
}
}
}
}
else
{
v___y_1625_ = v___y_1605_;
v___y_1626_ = v___y_1606_;
v___y_1627_ = v___y_1607_;
v___y_1628_ = v___y_1608_;
goto v___jp_1624_;
}
v___jp_1624_:
{
lean_object* v___x_1629_; 
lean_inc_ref(v_majorType_1601_);
lean_inc(v_mvarId_1599_);
lean_inc(v_tacticName_1598_);
lean_inc(v_idx_1623_);
v___x_1629_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg(v_majorTypeArgs_1597_, v_idx_1623_, v_tacticName_1598_, v_mvarId_1599_, v_v_1612_, v_recursorInfo_1600_, v_majorType_1601_, v___x_1621_, v___x_1621_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_);
lean_dec(v_v_1612_);
if (lean_obj_tag(v___x_1629_) == 0)
{
lean_dec_ref(v___x_1629_);
lean_inc(v_idx_1623_);
v_a_1616_ = v_idx_1623_;
goto v___jp_1615_;
}
else
{
lean_object* v_a_1630_; lean_object* v___x_1632_; uint8_t v_isShared_1633_; uint8_t v_isSharedCheck_1637_; 
lean_dec_ref(v_bs_x27_1614_);
lean_dec_ref(v_majorType_1601_);
lean_dec(v_mvarId_1599_);
lean_dec(v_tacticName_1598_);
v_a_1630_ = lean_ctor_get(v___x_1629_, 0);
v_isSharedCheck_1637_ = !lean_is_exclusive(v___x_1629_);
if (v_isSharedCheck_1637_ == 0)
{
v___x_1632_ = v___x_1629_;
v_isShared_1633_ = v_isSharedCheck_1637_;
goto v_resetjp_1631_;
}
else
{
lean_inc(v_a_1630_);
lean_dec(v___x_1629_);
v___x_1632_ = lean_box(0);
v_isShared_1633_ = v_isSharedCheck_1637_;
goto v_resetjp_1631_;
}
v_resetjp_1631_:
{
lean_object* v___x_1635_; 
if (v_isShared_1633_ == 0)
{
v___x_1635_ = v___x_1632_;
goto v_reusejp_1634_;
}
else
{
lean_object* v_reuseFailAlloc_1636_; 
v_reuseFailAlloc_1636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1636_, 0, v_a_1630_);
v___x_1635_ = v_reuseFailAlloc_1636_;
goto v_reusejp_1634_;
}
v_reusejp_1634_:
{
return v___x_1635_;
}
}
}
}
}
else
{
lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; 
lean_dec(v_v_1612_);
v___x_1656_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__5, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__5);
lean_inc_ref(v_majorType_1601_);
v___x_1657_ = l_Lean_indentExpr(v_majorType_1601_);
v___x_1658_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1658_, 0, v___x_1656_);
lean_ctor_set(v___x_1658_, 1, v___x_1657_);
v___x_1659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1659_, 0, v___x_1658_);
lean_inc(v_mvarId_1599_);
lean_inc(v_tacticName_1598_);
v___x_1660_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1598_, v_mvarId_1599_, v___x_1659_, v___y_1605_, v___y_1606_, v___y_1607_, v___y_1608_);
if (lean_obj_tag(v___x_1660_) == 0)
{
lean_object* v_a_1661_; 
v_a_1661_ = lean_ctor_get(v___x_1660_, 0);
lean_inc(v_a_1661_);
lean_dec_ref(v___x_1660_);
v_a_1616_ = v_a_1661_;
goto v___jp_1615_;
}
else
{
lean_object* v_a_1662_; lean_object* v___x_1664_; uint8_t v_isShared_1665_; uint8_t v_isSharedCheck_1669_; 
lean_dec_ref(v_bs_x27_1614_);
lean_dec_ref(v_majorType_1601_);
lean_dec(v_mvarId_1599_);
lean_dec(v_tacticName_1598_);
v_a_1662_ = lean_ctor_get(v___x_1660_, 0);
v_isSharedCheck_1669_ = !lean_is_exclusive(v___x_1660_);
if (v_isSharedCheck_1669_ == 0)
{
v___x_1664_ = v___x_1660_;
v_isShared_1665_ = v_isSharedCheck_1669_;
goto v_resetjp_1663_;
}
else
{
lean_inc(v_a_1662_);
lean_dec(v___x_1660_);
v___x_1664_ = lean_box(0);
v_isShared_1665_ = v_isSharedCheck_1669_;
goto v_resetjp_1663_;
}
v_resetjp_1663_:
{
lean_object* v___x_1667_; 
if (v_isShared_1665_ == 0)
{
v___x_1667_ = v___x_1664_;
goto v_reusejp_1666_;
}
else
{
lean_object* v_reuseFailAlloc_1668_; 
v_reuseFailAlloc_1668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1668_, 0, v_a_1662_);
v___x_1667_ = v_reuseFailAlloc_1668_;
goto v_reusejp_1666_;
}
v_reusejp_1666_:
{
return v___x_1667_;
}
}
}
}
v___jp_1615_:
{
size_t v___x_1617_; size_t v___x_1618_; lean_object* v___x_1619_; 
v___x_1617_ = ((size_t)1ULL);
v___x_1618_ = lean_usize_add(v_i_1603_, v___x_1617_);
v___x_1619_ = lean_array_uset(v_bs_x27_1614_, v_i_1603_, v_a_1616_);
v_i_1603_ = v___x_1618_;
v_bs_1604_ = v___x_1619_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___boxed(lean_object* v_majorTypeArgs_1670_, lean_object* v_tacticName_1671_, lean_object* v_mvarId_1672_, lean_object* v_recursorInfo_1673_, lean_object* v_majorType_1674_, lean_object* v_sz_1675_, lean_object* v_i_1676_, lean_object* v_bs_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_){
_start:
{
size_t v_sz_boxed_1683_; size_t v_i_boxed_1684_; lean_object* v_res_1685_; 
v_sz_boxed_1683_ = lean_unbox_usize(v_sz_1675_);
lean_dec(v_sz_1675_);
v_i_boxed_1684_ = lean_unbox_usize(v_i_1676_);
lean_dec(v_i_1676_);
v_res_1685_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4(v_majorTypeArgs_1670_, v_tacticName_1671_, v_mvarId_1672_, v_recursorInfo_1673_, v_majorType_1674_, v_sz_boxed_1683_, v_i_boxed_1684_, v_bs_1677_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_);
lean_dec(v___y_1681_);
lean_dec_ref(v___y_1680_);
lean_dec(v___y_1679_);
lean_dec_ref(v___y_1678_);
lean_dec_ref(v_recursorInfo_1673_);
lean_dec_ref(v_majorTypeArgs_1670_);
return v_res_1685_;
}
}
static lean_object* _init_l_Lean_Meta_getMajorTypeIndices___closed__0(void){
_start:
{
lean_object* v___x_1686_; lean_object* v_dummy_1687_; 
v___x_1686_ = lean_box(0);
v_dummy_1687_ = l_Lean_Expr_sort___override(v___x_1686_);
return v_dummy_1687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMajorTypeIndices(lean_object* v_mvarId_1688_, lean_object* v_tacticName_1689_, lean_object* v_recursorInfo_1690_, lean_object* v_majorType_1691_, lean_object* v_a_1692_, lean_object* v_a_1693_, lean_object* v_a_1694_, lean_object* v_a_1695_){
_start:
{
lean_object* v_indicesPos_1697_; lean_object* v_nargs_1698_; lean_object* v_dummy_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v_majorTypeArgs_1703_; lean_object* v___x_1704_; size_t v_sz_1705_; size_t v___x_1706_; lean_object* v___x_1707_; 
v_indicesPos_1697_ = lean_ctor_get(v_recursorInfo_1690_, 6);
v_nargs_1698_ = l_Lean_Expr_getAppNumArgs(v_majorType_1691_);
v_dummy_1699_ = lean_obj_once(&l_Lean_Meta_getMajorTypeIndices___closed__0, &l_Lean_Meta_getMajorTypeIndices___closed__0_once, _init_l_Lean_Meta_getMajorTypeIndices___closed__0);
lean_inc(v_nargs_1698_);
v___x_1700_ = lean_mk_array(v_nargs_1698_, v_dummy_1699_);
v___x_1701_ = lean_unsigned_to_nat(1u);
v___x_1702_ = lean_nat_sub(v_nargs_1698_, v___x_1701_);
lean_dec(v_nargs_1698_);
lean_inc_ref(v_majorType_1691_);
v_majorTypeArgs_1703_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_majorType_1691_, v___x_1700_, v___x_1702_);
lean_inc(v_indicesPos_1697_);
v___x_1704_ = lean_array_mk(v_indicesPos_1697_);
v_sz_1705_ = lean_array_size(v___x_1704_);
v___x_1706_ = ((size_t)0ULL);
v___x_1707_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4(v_majorTypeArgs_1703_, v_tacticName_1689_, v_mvarId_1688_, v_recursorInfo_1690_, v_majorType_1691_, v_sz_1705_, v___x_1706_, v___x_1704_, v_a_1692_, v_a_1693_, v_a_1694_, v_a_1695_);
lean_dec_ref(v_recursorInfo_1690_);
lean_dec_ref(v_majorTypeArgs_1703_);
return v___x_1707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMajorTypeIndices___boxed(lean_object* v_mvarId_1708_, lean_object* v_tacticName_1709_, lean_object* v_recursorInfo_1710_, lean_object* v_majorType_1711_, lean_object* v_a_1712_, lean_object* v_a_1713_, lean_object* v_a_1714_, lean_object* v_a_1715_, lean_object* v_a_1716_){
_start:
{
lean_object* v_res_1717_; 
v_res_1717_ = l_Lean_Meta_getMajorTypeIndices(v_mvarId_1708_, v_tacticName_1709_, v_recursorInfo_1710_, v_majorType_1711_, v_a_1712_, v_a_1713_, v_a_1714_, v_a_1715_);
lean_dec(v_a_1715_);
lean_dec_ref(v_a_1714_);
lean_dec(v_a_1713_);
lean_dec_ref(v_a_1712_);
return v_res_1717_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3(lean_object* v_majorTypeArgs_1718_, lean_object* v_idx_1719_, lean_object* v_tacticName_1720_, lean_object* v_mvarId_1721_, lean_object* v_idxPos_1722_, lean_object* v_recursorInfo_1723_, lean_object* v_majorType_1724_, lean_object* v_n_1725_, lean_object* v_i_1726_, lean_object* v_a_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_){
_start:
{
lean_object* v___x_1733_; 
v___x_1733_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg(v_majorTypeArgs_1718_, v_idx_1719_, v_tacticName_1720_, v_mvarId_1721_, v_idxPos_1722_, v_recursorInfo_1723_, v_majorType_1724_, v_n_1725_, v_i_1726_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_);
return v___x_1733_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___boxed(lean_object* v_majorTypeArgs_1734_, lean_object* v_idx_1735_, lean_object* v_tacticName_1736_, lean_object* v_mvarId_1737_, lean_object* v_idxPos_1738_, lean_object* v_recursorInfo_1739_, lean_object* v_majorType_1740_, lean_object* v_n_1741_, lean_object* v_i_1742_, lean_object* v_a_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_){
_start:
{
lean_object* v_res_1749_; 
v_res_1749_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3(v_majorTypeArgs_1734_, v_idx_1735_, v_tacticName_1736_, v_mvarId_1737_, v_idxPos_1738_, v_recursorInfo_1739_, v_majorType_1740_, v_n_1741_, v_i_1742_, v_a_1743_, v___y_1744_, v___y_1745_, v___y_1746_, v___y_1747_);
lean_dec(v___y_1747_);
lean_dec_ref(v___y_1746_);
lean_dec(v___y_1745_);
lean_dec_ref(v___y_1744_);
lean_dec(v_n_1741_);
lean_dec_ref(v_recursorInfo_1739_);
lean_dec(v_idxPos_1738_);
lean_dec_ref(v_majorTypeArgs_1734_);
return v_res_1749_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1___redArg(lean_object* v_name_1750_, lean_object* v_msg_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_){
_start:
{
lean_object* v_ref_1757_; lean_object* v_msg_1758_; lean_object* v___x_1759_; lean_object* v_a_1760_; lean_object* v___x_1762_; uint8_t v_isShared_1763_; uint8_t v_isSharedCheck_1768_; 
v_ref_1757_ = lean_ctor_get(v___y_1754_, 5);
v_msg_1758_ = l_Lean_MessageData_tagWithErrorName(v_msg_1751_, v_name_1750_);
v___x_1759_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1_spec__2(v_msg_1758_, v___y_1752_, v___y_1753_, v___y_1754_, v___y_1755_);
v_a_1760_ = lean_ctor_get(v___x_1759_, 0);
v_isSharedCheck_1768_ = !lean_is_exclusive(v___x_1759_);
if (v_isSharedCheck_1768_ == 0)
{
v___x_1762_ = v___x_1759_;
v_isShared_1763_ = v_isSharedCheck_1768_;
goto v_resetjp_1761_;
}
else
{
lean_inc(v_a_1760_);
lean_dec(v___x_1759_);
v___x_1762_ = lean_box(0);
v_isShared_1763_ = v_isSharedCheck_1768_;
goto v_resetjp_1761_;
}
v_resetjp_1761_:
{
lean_object* v___x_1764_; lean_object* v___x_1766_; 
lean_inc(v_ref_1757_);
v___x_1764_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1764_, 0, v_ref_1757_);
lean_ctor_set(v___x_1764_, 1, v_a_1760_);
if (v_isShared_1763_ == 0)
{
lean_ctor_set_tag(v___x_1762_, 1);
lean_ctor_set(v___x_1762_, 0, v___x_1764_);
v___x_1766_ = v___x_1762_;
goto v_reusejp_1765_;
}
else
{
lean_object* v_reuseFailAlloc_1767_; 
v_reuseFailAlloc_1767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1767_, 0, v___x_1764_);
v___x_1766_ = v_reuseFailAlloc_1767_;
goto v_reusejp_1765_;
}
v_reusejp_1765_:
{
return v___x_1766_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1___redArg___boxed(lean_object* v_name_1769_, lean_object* v_msg_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_){
_start:
{
lean_object* v_res_1776_; 
v_res_1776_ = l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1___redArg(v_name_1769_, v_msg_1770_, v___y_1771_, v___y_1772_, v___y_1773_, v___y_1774_);
lean_dec(v___y_1774_);
lean_dec_ref(v___y_1773_);
lean_dec(v___y_1772_);
lean_dec_ref(v___y_1771_);
return v_res_1776_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Meta_mkRecursorAppPrefix_spec__0(lean_object* v_a_1777_, lean_object* v___x_1778_, lean_object* v_tacticName_1779_, lean_object* v_mvarId_1780_, lean_object* v_x_1781_, lean_object* v_x_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_){
_start:
{
if (lean_obj_tag(v_x_1782_) == 0)
{
lean_object* v___x_1788_; 
lean_dec(v_mvarId_1780_);
lean_dec(v_tacticName_1779_);
lean_dec(v_a_1777_);
v___x_1788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1788_, 0, v_x_1781_);
return v___x_1788_;
}
else
{
lean_object* v_head_1789_; 
v_head_1789_ = lean_ctor_get(v_x_1782_, 0);
if (lean_obj_tag(v_head_1789_) == 0)
{
lean_object* v_tail_1790_; lean_object* v_fst_1791_; lean_object* v___x_1793_; uint8_t v_isShared_1794_; uint8_t v_isSharedCheck_1802_; 
v_tail_1790_ = lean_ctor_get(v_x_1782_, 1);
v_fst_1791_ = lean_ctor_get(v_x_1781_, 0);
v_isSharedCheck_1802_ = !lean_is_exclusive(v_x_1781_);
if (v_isSharedCheck_1802_ == 0)
{
lean_object* v_unused_1803_; 
v_unused_1803_ = lean_ctor_get(v_x_1781_, 1);
lean_dec(v_unused_1803_);
v___x_1793_ = v_x_1781_;
v_isShared_1794_ = v_isSharedCheck_1802_;
goto v_resetjp_1792_;
}
else
{
lean_inc(v_fst_1791_);
lean_dec(v_x_1781_);
v___x_1793_ = lean_box(0);
v_isShared_1794_ = v_isSharedCheck_1802_;
goto v_resetjp_1792_;
}
v_resetjp_1792_:
{
lean_object* v___x_1795_; uint8_t v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1799_; 
lean_inc(v_a_1777_);
v___x_1795_ = lean_array_push(v_fst_1791_, v_a_1777_);
v___x_1796_ = 1;
v___x_1797_ = lean_box(v___x_1796_);
if (v_isShared_1794_ == 0)
{
lean_ctor_set(v___x_1793_, 1, v___x_1797_);
lean_ctor_set(v___x_1793_, 0, v___x_1795_);
v___x_1799_ = v___x_1793_;
goto v_reusejp_1798_;
}
else
{
lean_object* v_reuseFailAlloc_1801_; 
v_reuseFailAlloc_1801_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1801_, 0, v___x_1795_);
lean_ctor_set(v_reuseFailAlloc_1801_, 1, v___x_1797_);
v___x_1799_ = v_reuseFailAlloc_1801_;
goto v_reusejp_1798_;
}
v_reusejp_1798_:
{
v_x_1781_ = v___x_1799_;
v_x_1782_ = v_tail_1790_;
goto _start;
}
}
}
else
{
lean_object* v_tail_1804_; lean_object* v_fst_1805_; lean_object* v_snd_1806_; lean_object* v___x_1808_; uint8_t v_isShared_1809_; uint8_t v_isSharedCheck_1823_; 
v_tail_1804_ = lean_ctor_get(v_x_1782_, 1);
v_fst_1805_ = lean_ctor_get(v_x_1781_, 0);
v_snd_1806_ = lean_ctor_get(v_x_1781_, 1);
v_isSharedCheck_1823_ = !lean_is_exclusive(v_x_1781_);
if (v_isSharedCheck_1823_ == 0)
{
v___x_1808_ = v_x_1781_;
v_isShared_1809_ = v_isSharedCheck_1823_;
goto v_resetjp_1807_;
}
else
{
lean_inc(v_snd_1806_);
lean_inc(v_fst_1805_);
lean_dec(v_x_1781_);
v___x_1808_ = lean_box(0);
v_isShared_1809_ = v_isSharedCheck_1823_;
goto v_resetjp_1807_;
}
v_resetjp_1807_:
{
lean_object* v_idx_1810_; lean_object* v___x_1811_; uint8_t v___x_1812_; 
v_idx_1810_ = lean_ctor_get(v_head_1789_, 0);
v___x_1811_ = lean_array_get_size(v___x_1778_);
v___x_1812_ = lean_nat_dec_le(v___x_1811_, v_idx_1810_);
if (v___x_1812_ == 0)
{
lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1816_; 
v___x_1813_ = lean_array_fget_borrowed(v___x_1778_, v_idx_1810_);
lean_inc(v___x_1813_);
v___x_1814_ = lean_array_push(v_fst_1805_, v___x_1813_);
if (v_isShared_1809_ == 0)
{
lean_ctor_set(v___x_1808_, 0, v___x_1814_);
v___x_1816_ = v___x_1808_;
goto v_reusejp_1815_;
}
else
{
lean_object* v_reuseFailAlloc_1818_; 
v_reuseFailAlloc_1818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1818_, 0, v___x_1814_);
lean_ctor_set(v_reuseFailAlloc_1818_, 1, v_snd_1806_);
v___x_1816_ = v_reuseFailAlloc_1818_;
goto v_reusejp_1815_;
}
v_reusejp_1815_:
{
v_x_1781_ = v___x_1816_;
v_x_1782_ = v_tail_1804_;
goto _start;
}
}
else
{
lean_object* v___x_1819_; lean_object* v___x_1820_; 
lean_del_object(v___x_1808_);
lean_dec(v_snd_1806_);
lean_dec(v_fst_1805_);
v___x_1819_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9);
lean_inc(v_mvarId_1780_);
lean_inc(v_tacticName_1779_);
v___x_1820_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1779_, v_mvarId_1780_, v___x_1819_, v___y_1783_, v___y_1784_, v___y_1785_, v___y_1786_);
if (lean_obj_tag(v___x_1820_) == 0)
{
lean_object* v_a_1821_; 
v_a_1821_ = lean_ctor_get(v___x_1820_, 0);
lean_inc(v_a_1821_);
lean_dec_ref(v___x_1820_);
v_x_1781_ = v_a_1821_;
v_x_1782_ = v_tail_1804_;
goto _start;
}
else
{
lean_dec(v_mvarId_1780_);
lean_dec(v_tacticName_1779_);
lean_dec(v_a_1777_);
return v___x_1820_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Meta_mkRecursorAppPrefix_spec__0___boxed(lean_object* v_a_1824_, lean_object* v___x_1825_, lean_object* v_tacticName_1826_, lean_object* v_mvarId_1827_, lean_object* v_x_1828_, lean_object* v_x_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_){
_start:
{
lean_object* v_res_1835_; 
v_res_1835_ = l_List_foldlM___at___00Lean_Meta_mkRecursorAppPrefix_spec__0(v_a_1824_, v___x_1825_, v_tacticName_1826_, v_mvarId_1827_, v_x_1828_, v_x_1829_, v___y_1830_, v___y_1831_, v___y_1832_, v___y_1833_);
lean_dec(v___y_1833_);
lean_dec_ref(v___y_1832_);
lean_dec(v___y_1831_);
lean_dec_ref(v___y_1830_);
lean_dec(v_x_1829_);
lean_dec_ref(v___x_1825_);
return v_res_1835_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__8(void){
_start:
{
lean_object* v___x_1851_; lean_object* v___x_1852_; 
v___x_1851_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__7));
v___x_1852_ = l_Lean_stringToMessageData(v___x_1851_);
return v___x_1852_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__10(void){
_start:
{
lean_object* v___x_1854_; lean_object* v___x_1855_; 
v___x_1854_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__9));
v___x_1855_ = l_Lean_stringToMessageData(v___x_1854_);
return v___x_1855_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__13(void){
_start:
{
lean_object* v___x_1859_; lean_object* v___x_1860_; 
v___x_1859_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__12));
v___x_1860_ = l_Lean_MessageData_ofFormat(v___x_1859_);
return v___x_1860_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__14(void){
_start:
{
lean_object* v___x_1861_; lean_object* v___x_1862_; 
v___x_1861_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__13, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__13_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__13);
v___x_1862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1862_, 0, v___x_1861_);
return v___x_1862_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2(lean_object* v_recursorInfo_1863_, lean_object* v_a_1864_, lean_object* v_tacticName_1865_, lean_object* v_mvarId_1866_, lean_object* v_indices_1867_, lean_object* v_a_1868_, lean_object* v_major_1869_, lean_object* v_x_1870_, lean_object* v_x_1871_, lean_object* v_x_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_){
_start:
{
if (lean_obj_tag(v_x_1870_) == 5)
{
lean_object* v_fn_1878_; lean_object* v_arg_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; 
v_fn_1878_ = lean_ctor_get(v_x_1870_, 0);
lean_inc_ref(v_fn_1878_);
v_arg_1879_ = lean_ctor_get(v_x_1870_, 1);
lean_inc_ref(v_arg_1879_);
lean_dec_ref(v_x_1870_);
v___x_1880_ = lean_array_set(v_x_1871_, v_x_1872_, v_arg_1879_);
v___x_1881_ = lean_unsigned_to_nat(1u);
v___x_1882_ = lean_nat_sub(v_x_1872_, v___x_1881_);
lean_dec(v_x_1872_);
v_x_1870_ = v_fn_1878_;
v_x_1871_ = v___x_1880_;
v_x_1872_ = v___x_1882_;
goto _start;
}
else
{
lean_dec(v_x_1872_);
if (lean_obj_tag(v_x_1870_) == 4)
{
lean_object* v_us_1884_; lean_object* v_recursorName_1885_; lean_object* v_univLevelPos_1886_; uint8_t v_depElim_1887_; lean_object* v_paramsPos_1888_; lean_object* v___x_1889_; uint8_t v___x_1890_; lean_object* v___y_1892_; lean_object* v_motive_1893_; lean_object* v___y_1894_; lean_object* v___y_1895_; lean_object* v___y_1896_; lean_object* v___y_1897_; lean_object* v___x_1910_; lean_object* v___x_1911_; 
v_us_1884_ = lean_ctor_get(v_x_1870_, 1);
lean_inc(v_us_1884_);
lean_dec_ref(v_x_1870_);
v_recursorName_1885_ = lean_ctor_get(v_recursorInfo_1863_, 0);
lean_inc(v_recursorName_1885_);
v_univLevelPos_1886_ = lean_ctor_get(v_recursorInfo_1863_, 2);
lean_inc(v_univLevelPos_1886_);
v_depElim_1887_ = lean_ctor_get_uint8(v_recursorInfo_1863_, sizeof(void*)*8);
v_paramsPos_1888_ = lean_ctor_get(v_recursorInfo_1863_, 5);
lean_inc(v_paramsPos_1888_);
lean_dec_ref(v_recursorInfo_1863_);
v___x_1889_ = lean_array_mk(v_us_1884_);
v___x_1890_ = 0;
v___x_1910_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__1));
lean_inc(v_mvarId_1866_);
lean_inc(v_tacticName_1865_);
lean_inc(v_a_1864_);
v___x_1911_ = l_List_foldlM___at___00Lean_Meta_mkRecursorAppPrefix_spec__0(v_a_1864_, v___x_1889_, v_tacticName_1865_, v_mvarId_1866_, v___x_1910_, v_univLevelPos_1886_, v___y_1873_, v___y_1874_, v___y_1875_, v___y_1876_);
lean_dec(v_univLevelPos_1886_);
lean_dec_ref(v___x_1889_);
if (lean_obj_tag(v___x_1911_) == 0)
{
lean_object* v_a_1912_; lean_object* v_fst_1913_; lean_object* v_snd_1914_; lean_object* v___x_1916_; uint8_t v_isShared_1917_; uint8_t v_isSharedCheck_1958_; 
v_a_1912_ = lean_ctor_get(v___x_1911_, 0);
lean_inc(v_a_1912_);
lean_dec_ref(v___x_1911_);
v_fst_1913_ = lean_ctor_get(v_a_1912_, 0);
v_snd_1914_ = lean_ctor_get(v_a_1912_, 1);
v_isSharedCheck_1958_ = !lean_is_exclusive(v_a_1912_);
if (v_isSharedCheck_1958_ == 0)
{
v___x_1916_ = v_a_1912_;
v_isShared_1917_ = v_isSharedCheck_1958_;
goto v_resetjp_1915_;
}
else
{
lean_inc(v_snd_1914_);
lean_inc(v_fst_1913_);
lean_dec(v_a_1912_);
v___x_1916_ = lean_box(0);
v_isShared_1917_ = v_isSharedCheck_1958_;
goto v_resetjp_1915_;
}
v_resetjp_1915_:
{
lean_object* v___y_1919_; lean_object* v___y_1920_; lean_object* v___y_1921_; lean_object* v___y_1922_; uint8_t v___x_1938_; 
v___x_1938_ = lean_unbox(v_snd_1914_);
lean_dec(v_snd_1914_);
if (v___x_1938_ == 0)
{
uint8_t v___x_1939_; 
v___x_1939_ = l_Lean_Level_isZero(v_a_1864_);
lean_dec(v_a_1864_);
if (v___x_1939_ == 0)
{
lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1944_; 
lean_dec(v_fst_1913_);
lean_dec(v_paramsPos_1888_);
lean_dec_ref(v_x_1871_);
lean_dec_ref(v_major_1869_);
lean_dec_ref(v_a_1868_);
v___x_1940_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__6));
v___x_1941_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__8, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__8_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__8);
v___x_1942_ = l_Lean_MessageData_ofName(v_recursorName_1885_);
if (v_isShared_1917_ == 0)
{
lean_ctor_set_tag(v___x_1916_, 7);
lean_ctor_set(v___x_1916_, 1, v___x_1942_);
lean_ctor_set(v___x_1916_, 0, v___x_1941_);
v___x_1944_ = v___x_1916_;
goto v_reusejp_1943_;
}
else
{
lean_object* v_reuseFailAlloc_1957_; 
v_reuseFailAlloc_1957_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1957_, 0, v___x_1941_);
lean_ctor_set(v_reuseFailAlloc_1957_, 1, v___x_1942_);
v___x_1944_ = v_reuseFailAlloc_1957_;
goto v_reusejp_1943_;
}
v_reusejp_1943_:
{
lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v_a_1949_; lean_object* v___x_1951_; uint8_t v_isShared_1952_; uint8_t v_isSharedCheck_1956_; 
v___x_1945_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__10, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__10_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__10);
v___x_1946_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1946_, 0, v___x_1944_);
lean_ctor_set(v___x_1946_, 1, v___x_1945_);
v___x_1947_ = l_Lean_Meta_mkTacticExMsg(v_tacticName_1865_, v_mvarId_1866_, v___x_1946_);
v___x_1948_ = l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1___redArg(v___x_1940_, v___x_1947_, v___y_1873_, v___y_1874_, v___y_1875_, v___y_1876_);
v_a_1949_ = lean_ctor_get(v___x_1948_, 0);
v_isSharedCheck_1956_ = !lean_is_exclusive(v___x_1948_);
if (v_isSharedCheck_1956_ == 0)
{
v___x_1951_ = v___x_1948_;
v_isShared_1952_ = v_isSharedCheck_1956_;
goto v_resetjp_1950_;
}
else
{
lean_inc(v_a_1949_);
lean_dec(v___x_1948_);
v___x_1951_ = lean_box(0);
v_isShared_1952_ = v_isSharedCheck_1956_;
goto v_resetjp_1950_;
}
v_resetjp_1950_:
{
lean_object* v___x_1954_; 
if (v_isShared_1952_ == 0)
{
v___x_1954_ = v___x_1951_;
goto v_reusejp_1953_;
}
else
{
lean_object* v_reuseFailAlloc_1955_; 
v_reuseFailAlloc_1955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1955_, 0, v_a_1949_);
v___x_1954_ = v_reuseFailAlloc_1955_;
goto v_reusejp_1953_;
}
v_reusejp_1953_:
{
return v___x_1954_;
}
}
}
}
else
{
lean_del_object(v___x_1916_);
lean_dec(v_tacticName_1865_);
v___y_1919_ = v___y_1873_;
v___y_1920_ = v___y_1874_;
v___y_1921_ = v___y_1875_;
v___y_1922_ = v___y_1876_;
goto v___jp_1918_;
}
}
else
{
lean_del_object(v___x_1916_);
lean_dec(v_tacticName_1865_);
lean_dec(v_a_1864_);
v___y_1919_ = v___y_1873_;
v___y_1920_ = v___y_1874_;
v___y_1921_ = v___y_1875_;
v___y_1922_ = v___y_1876_;
goto v___jp_1918_;
}
v___jp_1918_:
{
lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; 
v___x_1923_ = lean_array_to_list(v_fst_1913_);
v___x_1924_ = l_Lean_mkConst(v_recursorName_1885_, v___x_1923_);
v___x_1925_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams(v_mvarId_1866_, v_x_1871_, v_paramsPos_1888_, v___x_1924_, v___y_1919_, v___y_1920_, v___y_1921_, v___y_1922_);
lean_dec_ref(v_x_1871_);
if (lean_obj_tag(v___x_1925_) == 0)
{
if (v_depElim_1887_ == 0)
{
lean_object* v_a_1926_; 
lean_dec_ref(v_major_1869_);
v_a_1926_ = lean_ctor_get(v___x_1925_, 0);
lean_inc(v_a_1926_);
lean_dec_ref(v___x_1925_);
v___y_1892_ = v_a_1926_;
v_motive_1893_ = v_a_1868_;
v___y_1894_ = v___y_1919_;
v___y_1895_ = v___y_1920_;
v___y_1896_ = v___y_1921_;
v___y_1897_ = v___y_1922_;
goto v___jp_1891_;
}
else
{
lean_object* v_a_1927_; lean_object* v___x_1928_; 
v_a_1927_ = lean_ctor_get(v___x_1925_, 0);
lean_inc(v_a_1927_);
lean_dec_ref(v___x_1925_);
lean_inc(v___y_1922_);
lean_inc_ref(v___y_1921_);
lean_inc(v___y_1920_);
lean_inc_ref(v___y_1919_);
lean_inc_ref(v_major_1869_);
v___x_1928_ = lean_infer_type(v_major_1869_, v___y_1919_, v___y_1920_, v___y_1921_, v___y_1922_);
if (lean_obj_tag(v___x_1928_) == 0)
{
lean_object* v_a_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; 
v_a_1929_ = lean_ctor_get(v___x_1928_, 0);
lean_inc(v_a_1929_);
lean_dec_ref(v___x_1928_);
v___x_1930_ = lean_unsigned_to_nat(1u);
v___x_1931_ = lean_mk_empty_array_with_capacity(v___x_1930_);
v___x_1932_ = lean_array_push(v___x_1931_, v_major_1869_);
v___x_1933_ = l_Lean_Expr_abstractM(v_a_1868_, v___x_1932_, v___y_1919_, v___y_1920_, v___y_1921_, v___y_1922_);
lean_dec_ref(v___x_1932_);
if (lean_obj_tag(v___x_1933_) == 0)
{
lean_object* v_a_1934_; lean_object* v___x_1935_; uint8_t v___x_1936_; lean_object* v___x_1937_; 
v_a_1934_ = lean_ctor_get(v___x_1933_, 0);
lean_inc(v_a_1934_);
lean_dec_ref(v___x_1933_);
v___x_1935_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__3));
v___x_1936_ = 0;
v___x_1937_ = l_Lean_mkLambda(v___x_1935_, v___x_1936_, v_a_1929_, v_a_1934_);
v___y_1892_ = v_a_1927_;
v_motive_1893_ = v___x_1937_;
v___y_1894_ = v___y_1919_;
v___y_1895_ = v___y_1920_;
v___y_1896_ = v___y_1921_;
v___y_1897_ = v___y_1922_;
goto v___jp_1891_;
}
else
{
lean_dec(v_a_1929_);
lean_dec(v_a_1927_);
return v___x_1933_;
}
}
else
{
lean_dec(v_a_1927_);
lean_dec_ref(v_major_1869_);
lean_dec_ref(v_a_1868_);
return v___x_1928_;
}
}
}
else
{
lean_dec_ref(v_major_1869_);
lean_dec_ref(v_a_1868_);
return v___x_1925_;
}
}
}
}
else
{
lean_object* v_a_1959_; lean_object* v___x_1961_; uint8_t v_isShared_1962_; uint8_t v_isSharedCheck_1966_; 
lean_dec(v_paramsPos_1888_);
lean_dec(v_recursorName_1885_);
lean_dec_ref(v_x_1871_);
lean_dec_ref(v_major_1869_);
lean_dec_ref(v_a_1868_);
lean_dec(v_mvarId_1866_);
lean_dec(v_tacticName_1865_);
lean_dec(v_a_1864_);
v_a_1959_ = lean_ctor_get(v___x_1911_, 0);
v_isSharedCheck_1966_ = !lean_is_exclusive(v___x_1911_);
if (v_isSharedCheck_1966_ == 0)
{
v___x_1961_ = v___x_1911_;
v_isShared_1962_ = v_isSharedCheck_1966_;
goto v_resetjp_1960_;
}
else
{
lean_inc(v_a_1959_);
lean_dec(v___x_1911_);
v___x_1961_ = lean_box(0);
v_isShared_1962_ = v_isSharedCheck_1966_;
goto v_resetjp_1960_;
}
v_resetjp_1960_:
{
lean_object* v___x_1964_; 
if (v_isShared_1962_ == 0)
{
v___x_1964_ = v___x_1961_;
goto v_reusejp_1963_;
}
else
{
lean_object* v_reuseFailAlloc_1965_; 
v_reuseFailAlloc_1965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1965_, 0, v_a_1959_);
v___x_1964_ = v_reuseFailAlloc_1965_;
goto v_reusejp_1963_;
}
v_reusejp_1963_:
{
return v___x_1964_;
}
}
}
v___jp_1891_:
{
uint8_t v___x_1898_; uint8_t v___x_1899_; lean_object* v___x_1900_; 
v___x_1898_ = 1;
v___x_1899_ = 1;
v___x_1900_ = l_Lean_Meta_mkLambdaFVars(v_indices_1867_, v_motive_1893_, v___x_1890_, v___x_1898_, v___x_1890_, v___x_1898_, v___x_1899_, v___y_1894_, v___y_1895_, v___y_1896_, v___y_1897_);
if (lean_obj_tag(v___x_1900_) == 0)
{
lean_object* v_a_1901_; lean_object* v___x_1903_; uint8_t v_isShared_1904_; uint8_t v_isSharedCheck_1909_; 
v_a_1901_ = lean_ctor_get(v___x_1900_, 0);
v_isSharedCheck_1909_ = !lean_is_exclusive(v___x_1900_);
if (v_isSharedCheck_1909_ == 0)
{
v___x_1903_ = v___x_1900_;
v_isShared_1904_ = v_isSharedCheck_1909_;
goto v_resetjp_1902_;
}
else
{
lean_inc(v_a_1901_);
lean_dec(v___x_1900_);
v___x_1903_ = lean_box(0);
v_isShared_1904_ = v_isSharedCheck_1909_;
goto v_resetjp_1902_;
}
v_resetjp_1902_:
{
lean_object* v___x_1905_; lean_object* v___x_1907_; 
v___x_1905_ = l_Lean_Expr_app___override(v___y_1892_, v_a_1901_);
if (v_isShared_1904_ == 0)
{
lean_ctor_set(v___x_1903_, 0, v___x_1905_);
v___x_1907_ = v___x_1903_;
goto v_reusejp_1906_;
}
else
{
lean_object* v_reuseFailAlloc_1908_; 
v_reuseFailAlloc_1908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1908_, 0, v___x_1905_);
v___x_1907_ = v_reuseFailAlloc_1908_;
goto v_reusejp_1906_;
}
v_reusejp_1906_:
{
return v___x_1907_;
}
}
}
else
{
lean_dec_ref(v___y_1892_);
return v___x_1900_;
}
}
}
else
{
lean_object* v___x_1967_; lean_object* v___x_1968_; 
lean_dec_ref(v_x_1871_);
lean_dec_ref(v_x_1870_);
lean_dec_ref(v_major_1869_);
lean_dec_ref(v_a_1868_);
lean_dec(v_a_1864_);
lean_dec_ref(v_recursorInfo_1863_);
v___x_1967_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__14, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__14_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__14);
v___x_1968_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1865_, v_mvarId_1866_, v___x_1967_, v___y_1873_, v___y_1874_, v___y_1875_, v___y_1876_);
return v___x_1968_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___boxed(lean_object* v_recursorInfo_1969_, lean_object* v_a_1970_, lean_object* v_tacticName_1971_, lean_object* v_mvarId_1972_, lean_object* v_indices_1973_, lean_object* v_a_1974_, lean_object* v_major_1975_, lean_object* v_x_1976_, lean_object* v_x_1977_, lean_object* v_x_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_){
_start:
{
lean_object* v_res_1984_; 
v_res_1984_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2(v_recursorInfo_1969_, v_a_1970_, v_tacticName_1971_, v_mvarId_1972_, v_indices_1973_, v_a_1974_, v_major_1975_, v_x_1976_, v_x_1977_, v_x_1978_, v___y_1979_, v___y_1980_, v___y_1981_, v___y_1982_);
lean_dec(v___y_1982_);
lean_dec_ref(v___y_1981_);
lean_dec(v___y_1980_);
lean_dec_ref(v___y_1979_);
lean_dec_ref(v_indices_1973_);
return v_res_1984_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2(lean_object* v_a_1985_, lean_object* v_tacticName_1986_, lean_object* v_mvarId_1987_, lean_object* v_recursorInfo_1988_, lean_object* v_indices_1989_, lean_object* v_a_1990_, lean_object* v_major_1991_, lean_object* v_x_1992_, lean_object* v_x_1993_, lean_object* v_x_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_){
_start:
{
if (lean_obj_tag(v_x_1992_) == 5)
{
lean_object* v_fn_2000_; lean_object* v_arg_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; 
v_fn_2000_ = lean_ctor_get(v_x_1992_, 0);
lean_inc_ref(v_fn_2000_);
v_arg_2001_ = lean_ctor_get(v_x_1992_, 1);
lean_inc_ref(v_arg_2001_);
lean_dec_ref(v_x_1992_);
v___x_2002_ = lean_array_set(v_x_1993_, v_x_1994_, v_arg_2001_);
v___x_2003_ = lean_unsigned_to_nat(1u);
v___x_2004_ = lean_nat_sub(v_x_1994_, v___x_2003_);
v___x_2005_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2(v_recursorInfo_1988_, v_a_1985_, v_tacticName_1986_, v_mvarId_1987_, v_indices_1989_, v_a_1990_, v_major_1991_, v_fn_2000_, v___x_2002_, v___x_2004_, v___y_1995_, v___y_1996_, v___y_1997_, v___y_1998_);
return v___x_2005_;
}
else
{
if (lean_obj_tag(v_x_1992_) == 4)
{
lean_object* v_us_2006_; lean_object* v_recursorName_2007_; lean_object* v_univLevelPos_2008_; uint8_t v_depElim_2009_; lean_object* v_paramsPos_2010_; lean_object* v___x_2011_; uint8_t v___x_2012_; lean_object* v___y_2014_; lean_object* v_motive_2015_; lean_object* v___y_2016_; lean_object* v___y_2017_; lean_object* v___y_2018_; lean_object* v___y_2019_; lean_object* v___x_2032_; lean_object* v___x_2033_; 
v_us_2006_ = lean_ctor_get(v_x_1992_, 1);
lean_inc(v_us_2006_);
lean_dec_ref(v_x_1992_);
v_recursorName_2007_ = lean_ctor_get(v_recursorInfo_1988_, 0);
lean_inc(v_recursorName_2007_);
v_univLevelPos_2008_ = lean_ctor_get(v_recursorInfo_1988_, 2);
lean_inc(v_univLevelPos_2008_);
v_depElim_2009_ = lean_ctor_get_uint8(v_recursorInfo_1988_, sizeof(void*)*8);
v_paramsPos_2010_ = lean_ctor_get(v_recursorInfo_1988_, 5);
lean_inc(v_paramsPos_2010_);
lean_dec_ref(v_recursorInfo_1988_);
v___x_2011_ = lean_array_mk(v_us_2006_);
v___x_2012_ = 0;
v___x_2032_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__1));
lean_inc(v_mvarId_1987_);
lean_inc(v_tacticName_1986_);
lean_inc(v_a_1985_);
v___x_2033_ = l_List_foldlM___at___00Lean_Meta_mkRecursorAppPrefix_spec__0(v_a_1985_, v___x_2011_, v_tacticName_1986_, v_mvarId_1987_, v___x_2032_, v_univLevelPos_2008_, v___y_1995_, v___y_1996_, v___y_1997_, v___y_1998_);
lean_dec(v_univLevelPos_2008_);
lean_dec_ref(v___x_2011_);
if (lean_obj_tag(v___x_2033_) == 0)
{
lean_object* v_a_2034_; lean_object* v_fst_2035_; lean_object* v_snd_2036_; lean_object* v___x_2038_; uint8_t v_isShared_2039_; uint8_t v_isSharedCheck_2080_; 
v_a_2034_ = lean_ctor_get(v___x_2033_, 0);
lean_inc(v_a_2034_);
lean_dec_ref(v___x_2033_);
v_fst_2035_ = lean_ctor_get(v_a_2034_, 0);
v_snd_2036_ = lean_ctor_get(v_a_2034_, 1);
v_isSharedCheck_2080_ = !lean_is_exclusive(v_a_2034_);
if (v_isSharedCheck_2080_ == 0)
{
v___x_2038_ = v_a_2034_;
v_isShared_2039_ = v_isSharedCheck_2080_;
goto v_resetjp_2037_;
}
else
{
lean_inc(v_snd_2036_);
lean_inc(v_fst_2035_);
lean_dec(v_a_2034_);
v___x_2038_ = lean_box(0);
v_isShared_2039_ = v_isSharedCheck_2080_;
goto v_resetjp_2037_;
}
v_resetjp_2037_:
{
lean_object* v___y_2041_; lean_object* v___y_2042_; lean_object* v___y_2043_; lean_object* v___y_2044_; uint8_t v___x_2060_; 
v___x_2060_ = lean_unbox(v_snd_2036_);
lean_dec(v_snd_2036_);
if (v___x_2060_ == 0)
{
uint8_t v___x_2061_; 
v___x_2061_ = l_Lean_Level_isZero(v_a_1985_);
lean_dec(v_a_1985_);
if (v___x_2061_ == 0)
{
lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2066_; 
lean_dec(v_fst_2035_);
lean_dec(v_paramsPos_2010_);
lean_dec_ref(v_x_1993_);
lean_dec_ref(v_major_1991_);
lean_dec_ref(v_a_1990_);
v___x_2062_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__6));
v___x_2063_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__8, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__8_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__8);
v___x_2064_ = l_Lean_MessageData_ofName(v_recursorName_2007_);
if (v_isShared_2039_ == 0)
{
lean_ctor_set_tag(v___x_2038_, 7);
lean_ctor_set(v___x_2038_, 1, v___x_2064_);
lean_ctor_set(v___x_2038_, 0, v___x_2063_);
v___x_2066_ = v___x_2038_;
goto v_reusejp_2065_;
}
else
{
lean_object* v_reuseFailAlloc_2079_; 
v_reuseFailAlloc_2079_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2079_, 0, v___x_2063_);
lean_ctor_set(v_reuseFailAlloc_2079_, 1, v___x_2064_);
v___x_2066_ = v_reuseFailAlloc_2079_;
goto v_reusejp_2065_;
}
v_reusejp_2065_:
{
lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v_a_2071_; lean_object* v___x_2073_; uint8_t v_isShared_2074_; uint8_t v_isSharedCheck_2078_; 
v___x_2067_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__10, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__10_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__10);
v___x_2068_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2068_, 0, v___x_2066_);
lean_ctor_set(v___x_2068_, 1, v___x_2067_);
v___x_2069_ = l_Lean_Meta_mkTacticExMsg(v_tacticName_1986_, v_mvarId_1987_, v___x_2068_);
v___x_2070_ = l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1___redArg(v___x_2062_, v___x_2069_, v___y_1995_, v___y_1996_, v___y_1997_, v___y_1998_);
v_a_2071_ = lean_ctor_get(v___x_2070_, 0);
v_isSharedCheck_2078_ = !lean_is_exclusive(v___x_2070_);
if (v_isSharedCheck_2078_ == 0)
{
v___x_2073_ = v___x_2070_;
v_isShared_2074_ = v_isSharedCheck_2078_;
goto v_resetjp_2072_;
}
else
{
lean_inc(v_a_2071_);
lean_dec(v___x_2070_);
v___x_2073_ = lean_box(0);
v_isShared_2074_ = v_isSharedCheck_2078_;
goto v_resetjp_2072_;
}
v_resetjp_2072_:
{
lean_object* v___x_2076_; 
if (v_isShared_2074_ == 0)
{
v___x_2076_ = v___x_2073_;
goto v_reusejp_2075_;
}
else
{
lean_object* v_reuseFailAlloc_2077_; 
v_reuseFailAlloc_2077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2077_, 0, v_a_2071_);
v___x_2076_ = v_reuseFailAlloc_2077_;
goto v_reusejp_2075_;
}
v_reusejp_2075_:
{
return v___x_2076_;
}
}
}
}
else
{
lean_del_object(v___x_2038_);
lean_dec(v_tacticName_1986_);
v___y_2041_ = v___y_1995_;
v___y_2042_ = v___y_1996_;
v___y_2043_ = v___y_1997_;
v___y_2044_ = v___y_1998_;
goto v___jp_2040_;
}
}
else
{
lean_del_object(v___x_2038_);
lean_dec(v_tacticName_1986_);
lean_dec(v_a_1985_);
v___y_2041_ = v___y_1995_;
v___y_2042_ = v___y_1996_;
v___y_2043_ = v___y_1997_;
v___y_2044_ = v___y_1998_;
goto v___jp_2040_;
}
v___jp_2040_:
{
lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; 
v___x_2045_ = lean_array_to_list(v_fst_2035_);
v___x_2046_ = l_Lean_mkConst(v_recursorName_2007_, v___x_2045_);
v___x_2047_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams(v_mvarId_1987_, v_x_1993_, v_paramsPos_2010_, v___x_2046_, v___y_2041_, v___y_2042_, v___y_2043_, v___y_2044_);
lean_dec_ref(v_x_1993_);
if (lean_obj_tag(v___x_2047_) == 0)
{
if (v_depElim_2009_ == 0)
{
lean_object* v_a_2048_; 
lean_dec_ref(v_major_1991_);
v_a_2048_ = lean_ctor_get(v___x_2047_, 0);
lean_inc(v_a_2048_);
lean_dec_ref(v___x_2047_);
v___y_2014_ = v_a_2048_;
v_motive_2015_ = v_a_1990_;
v___y_2016_ = v___y_2041_;
v___y_2017_ = v___y_2042_;
v___y_2018_ = v___y_2043_;
v___y_2019_ = v___y_2044_;
goto v___jp_2013_;
}
else
{
lean_object* v_a_2049_; lean_object* v___x_2050_; 
v_a_2049_ = lean_ctor_get(v___x_2047_, 0);
lean_inc(v_a_2049_);
lean_dec_ref(v___x_2047_);
lean_inc(v___y_2044_);
lean_inc_ref(v___y_2043_);
lean_inc(v___y_2042_);
lean_inc_ref(v___y_2041_);
lean_inc_ref(v_major_1991_);
v___x_2050_ = lean_infer_type(v_major_1991_, v___y_2041_, v___y_2042_, v___y_2043_, v___y_2044_);
if (lean_obj_tag(v___x_2050_) == 0)
{
lean_object* v_a_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; 
v_a_2051_ = lean_ctor_get(v___x_2050_, 0);
lean_inc(v_a_2051_);
lean_dec_ref(v___x_2050_);
v___x_2052_ = lean_unsigned_to_nat(1u);
v___x_2053_ = lean_mk_empty_array_with_capacity(v___x_2052_);
v___x_2054_ = lean_array_push(v___x_2053_, v_major_1991_);
v___x_2055_ = l_Lean_Expr_abstractM(v_a_1990_, v___x_2054_, v___y_2041_, v___y_2042_, v___y_2043_, v___y_2044_);
lean_dec_ref(v___x_2054_);
if (lean_obj_tag(v___x_2055_) == 0)
{
lean_object* v_a_2056_; lean_object* v___x_2057_; uint8_t v___x_2058_; lean_object* v___x_2059_; 
v_a_2056_ = lean_ctor_get(v___x_2055_, 0);
lean_inc(v_a_2056_);
lean_dec_ref(v___x_2055_);
v___x_2057_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__3));
v___x_2058_ = 0;
v___x_2059_ = l_Lean_mkLambda(v___x_2057_, v___x_2058_, v_a_2051_, v_a_2056_);
v___y_2014_ = v_a_2049_;
v_motive_2015_ = v___x_2059_;
v___y_2016_ = v___y_2041_;
v___y_2017_ = v___y_2042_;
v___y_2018_ = v___y_2043_;
v___y_2019_ = v___y_2044_;
goto v___jp_2013_;
}
else
{
lean_dec(v_a_2051_);
lean_dec(v_a_2049_);
return v___x_2055_;
}
}
else
{
lean_dec(v_a_2049_);
lean_dec_ref(v_major_1991_);
lean_dec_ref(v_a_1990_);
return v___x_2050_;
}
}
}
else
{
lean_dec_ref(v_major_1991_);
lean_dec_ref(v_a_1990_);
return v___x_2047_;
}
}
}
}
else
{
lean_object* v_a_2081_; lean_object* v___x_2083_; uint8_t v_isShared_2084_; uint8_t v_isSharedCheck_2088_; 
lean_dec(v_paramsPos_2010_);
lean_dec(v_recursorName_2007_);
lean_dec_ref(v_x_1993_);
lean_dec_ref(v_major_1991_);
lean_dec_ref(v_a_1990_);
lean_dec(v_mvarId_1987_);
lean_dec(v_tacticName_1986_);
lean_dec(v_a_1985_);
v_a_2081_ = lean_ctor_get(v___x_2033_, 0);
v_isSharedCheck_2088_ = !lean_is_exclusive(v___x_2033_);
if (v_isSharedCheck_2088_ == 0)
{
v___x_2083_ = v___x_2033_;
v_isShared_2084_ = v_isSharedCheck_2088_;
goto v_resetjp_2082_;
}
else
{
lean_inc(v_a_2081_);
lean_dec(v___x_2033_);
v___x_2083_ = lean_box(0);
v_isShared_2084_ = v_isSharedCheck_2088_;
goto v_resetjp_2082_;
}
v_resetjp_2082_:
{
lean_object* v___x_2086_; 
if (v_isShared_2084_ == 0)
{
v___x_2086_ = v___x_2083_;
goto v_reusejp_2085_;
}
else
{
lean_object* v_reuseFailAlloc_2087_; 
v_reuseFailAlloc_2087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2087_, 0, v_a_2081_);
v___x_2086_ = v_reuseFailAlloc_2087_;
goto v_reusejp_2085_;
}
v_reusejp_2085_:
{
return v___x_2086_;
}
}
}
v___jp_2013_:
{
uint8_t v___x_2020_; uint8_t v___x_2021_; lean_object* v___x_2022_; 
v___x_2020_ = 1;
v___x_2021_ = 1;
v___x_2022_ = l_Lean_Meta_mkLambdaFVars(v_indices_1989_, v_motive_2015_, v___x_2012_, v___x_2020_, v___x_2012_, v___x_2020_, v___x_2021_, v___y_2016_, v___y_2017_, v___y_2018_, v___y_2019_);
if (lean_obj_tag(v___x_2022_) == 0)
{
lean_object* v_a_2023_; lean_object* v___x_2025_; uint8_t v_isShared_2026_; uint8_t v_isSharedCheck_2031_; 
v_a_2023_ = lean_ctor_get(v___x_2022_, 0);
v_isSharedCheck_2031_ = !lean_is_exclusive(v___x_2022_);
if (v_isSharedCheck_2031_ == 0)
{
v___x_2025_ = v___x_2022_;
v_isShared_2026_ = v_isSharedCheck_2031_;
goto v_resetjp_2024_;
}
else
{
lean_inc(v_a_2023_);
lean_dec(v___x_2022_);
v___x_2025_ = lean_box(0);
v_isShared_2026_ = v_isSharedCheck_2031_;
goto v_resetjp_2024_;
}
v_resetjp_2024_:
{
lean_object* v___x_2027_; lean_object* v___x_2029_; 
v___x_2027_ = l_Lean_Expr_app___override(v___y_2014_, v_a_2023_);
if (v_isShared_2026_ == 0)
{
lean_ctor_set(v___x_2025_, 0, v___x_2027_);
v___x_2029_ = v___x_2025_;
goto v_reusejp_2028_;
}
else
{
lean_object* v_reuseFailAlloc_2030_; 
v_reuseFailAlloc_2030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2030_, 0, v___x_2027_);
v___x_2029_ = v_reuseFailAlloc_2030_;
goto v_reusejp_2028_;
}
v_reusejp_2028_:
{
return v___x_2029_;
}
}
}
else
{
lean_dec_ref(v___y_2014_);
return v___x_2022_;
}
}
}
else
{
lean_object* v___x_2089_; lean_object* v___x_2090_; 
lean_dec_ref(v_x_1993_);
lean_dec_ref(v_x_1992_);
lean_dec_ref(v_major_1991_);
lean_dec_ref(v_a_1990_);
lean_dec_ref(v_recursorInfo_1988_);
lean_dec(v_a_1985_);
v___x_2089_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__14, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__14_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__14);
v___x_2090_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1986_, v_mvarId_1987_, v___x_2089_, v___y_1995_, v___y_1996_, v___y_1997_, v___y_1998_);
return v___x_2090_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2___boxed(lean_object* v_a_2091_, lean_object* v_tacticName_2092_, lean_object* v_mvarId_2093_, lean_object* v_recursorInfo_2094_, lean_object* v_indices_2095_, lean_object* v_a_2096_, lean_object* v_major_2097_, lean_object* v_x_2098_, lean_object* v_x_2099_, lean_object* v_x_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_){
_start:
{
lean_object* v_res_2106_; 
v_res_2106_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2(v_a_2091_, v_tacticName_2092_, v_mvarId_2093_, v_recursorInfo_2094_, v_indices_2095_, v_a_2096_, v_major_2097_, v_x_2098_, v_x_2099_, v_x_2100_, v___y_2101_, v___y_2102_, v___y_2103_, v___y_2104_);
lean_dec(v___y_2104_);
lean_dec_ref(v___y_2103_);
lean_dec(v___y_2102_);
lean_dec_ref(v___y_2101_);
lean_dec(v_x_2100_);
lean_dec_ref(v_indices_2095_);
return v_res_2106_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkRecursorAppPrefix(lean_object* v_mvarId_2107_, lean_object* v_tacticName_2108_, lean_object* v_majorFVarId_2109_, lean_object* v_recursorInfo_2110_, lean_object* v_indices_2111_, lean_object* v_a_2112_, lean_object* v_a_2113_, lean_object* v_a_2114_, lean_object* v_a_2115_){
_start:
{
lean_object* v___x_2117_; 
lean_inc(v_mvarId_2107_);
v___x_2117_ = l_Lean_MVarId_getType(v_mvarId_2107_, v_a_2112_, v_a_2113_, v_a_2114_, v_a_2115_);
if (lean_obj_tag(v___x_2117_) == 0)
{
lean_object* v_a_2118_; lean_object* v___x_2119_; 
v_a_2118_ = lean_ctor_get(v___x_2117_, 0);
lean_inc_n(v_a_2118_, 2);
lean_dec_ref(v___x_2117_);
v___x_2119_ = l_Lean_Meta_getLevel(v_a_2118_, v_a_2112_, v_a_2113_, v_a_2114_, v_a_2115_);
if (lean_obj_tag(v___x_2119_) == 0)
{
lean_object* v_a_2120_; lean_object* v___x_2121_; 
v_a_2120_ = lean_ctor_get(v___x_2119_, 0);
lean_inc(v_a_2120_);
lean_dec_ref(v___x_2119_);
v___x_2121_ = l_Lean_Meta_normalizeLevel(v_a_2120_, v_a_2112_, v_a_2113_, v_a_2114_, v_a_2115_);
if (lean_obj_tag(v___x_2121_) == 0)
{
lean_object* v_a_2122_; lean_object* v_major_2123_; lean_object* v___x_2124_; 
v_a_2122_ = lean_ctor_get(v___x_2121_, 0);
lean_inc(v_a_2122_);
lean_dec_ref(v___x_2121_);
lean_inc(v_majorFVarId_2109_);
v_major_2123_ = l_Lean_mkFVar(v_majorFVarId_2109_);
v___x_2124_ = l_Lean_FVarId_getDecl___redArg(v_majorFVarId_2109_, v_a_2112_, v_a_2114_, v_a_2115_);
if (lean_obj_tag(v___x_2124_) == 0)
{
lean_object* v_a_2125_; lean_object* v_typeName_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; 
v_a_2125_ = lean_ctor_get(v___x_2124_, 0);
lean_inc(v_a_2125_);
lean_dec_ref(v___x_2124_);
v_typeName_2126_ = lean_ctor_get(v_recursorInfo_2110_, 1);
v___x_2127_ = l_Lean_LocalDecl_type(v_a_2125_);
lean_dec(v_a_2125_);
lean_inc_ref(v___x_2127_);
v___x_2128_ = l_Lean_Meta_whnfUntil(v___x_2127_, v_typeName_2126_, v_a_2112_, v_a_2113_, v_a_2114_, v_a_2115_);
if (lean_obj_tag(v___x_2128_) == 0)
{
lean_object* v_a_2129_; 
v_a_2129_ = lean_ctor_get(v___x_2128_, 0);
lean_inc(v_a_2129_);
lean_dec_ref(v___x_2128_);
if (lean_obj_tag(v_a_2129_) == 1)
{
lean_object* v_val_2130_; lean_object* v_dummy_2131_; lean_object* v_nargs_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; 
lean_dec_ref(v___x_2127_);
v_val_2130_ = lean_ctor_get(v_a_2129_, 0);
lean_inc(v_val_2130_);
lean_dec_ref(v_a_2129_);
v_dummy_2131_ = lean_obj_once(&l_Lean_Meta_getMajorTypeIndices___closed__0, &l_Lean_Meta_getMajorTypeIndices___closed__0_once, _init_l_Lean_Meta_getMajorTypeIndices___closed__0);
v_nargs_2132_ = l_Lean_Expr_getAppNumArgs(v_val_2130_);
lean_inc(v_nargs_2132_);
v___x_2133_ = lean_mk_array(v_nargs_2132_, v_dummy_2131_);
v___x_2134_ = lean_unsigned_to_nat(1u);
v___x_2135_ = lean_nat_sub(v_nargs_2132_, v___x_2134_);
lean_dec(v_nargs_2132_);
v___x_2136_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2(v_a_2122_, v_tacticName_2108_, v_mvarId_2107_, v_recursorInfo_2110_, v_indices_2111_, v_a_2118_, v_major_2123_, v_val_2130_, v___x_2133_, v___x_2135_, v_a_2112_, v_a_2113_, v_a_2114_, v_a_2115_);
lean_dec(v___x_2135_);
return v___x_2136_;
}
else
{
lean_object* v___x_2137_; 
lean_dec(v_a_2129_);
lean_dec_ref(v_major_2123_);
lean_dec(v_a_2122_);
lean_dec(v_a_2118_);
lean_dec_ref(v_recursorInfo_2110_);
v___x_2137_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg(v_tacticName_2108_, v_mvarId_2107_, v___x_2127_, v_a_2112_, v_a_2113_, v_a_2114_, v_a_2115_);
return v___x_2137_;
}
}
else
{
lean_object* v_a_2138_; lean_object* v___x_2140_; uint8_t v_isShared_2141_; uint8_t v_isSharedCheck_2145_; 
lean_dec_ref(v___x_2127_);
lean_dec_ref(v_major_2123_);
lean_dec(v_a_2122_);
lean_dec(v_a_2118_);
lean_dec_ref(v_recursorInfo_2110_);
lean_dec(v_tacticName_2108_);
lean_dec(v_mvarId_2107_);
v_a_2138_ = lean_ctor_get(v___x_2128_, 0);
v_isSharedCheck_2145_ = !lean_is_exclusive(v___x_2128_);
if (v_isSharedCheck_2145_ == 0)
{
v___x_2140_ = v___x_2128_;
v_isShared_2141_ = v_isSharedCheck_2145_;
goto v_resetjp_2139_;
}
else
{
lean_inc(v_a_2138_);
lean_dec(v___x_2128_);
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
lean_dec_ref(v_major_2123_);
lean_dec(v_a_2122_);
lean_dec(v_a_2118_);
lean_dec_ref(v_recursorInfo_2110_);
lean_dec(v_tacticName_2108_);
lean_dec(v_mvarId_2107_);
v_a_2146_ = lean_ctor_get(v___x_2124_, 0);
v_isSharedCheck_2153_ = !lean_is_exclusive(v___x_2124_);
if (v_isSharedCheck_2153_ == 0)
{
v___x_2148_ = v___x_2124_;
v_isShared_2149_ = v_isSharedCheck_2153_;
goto v_resetjp_2147_;
}
else
{
lean_inc(v_a_2146_);
lean_dec(v___x_2124_);
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
lean_dec(v_a_2118_);
lean_dec_ref(v_recursorInfo_2110_);
lean_dec(v_majorFVarId_2109_);
lean_dec(v_tacticName_2108_);
lean_dec(v_mvarId_2107_);
v_a_2154_ = lean_ctor_get(v___x_2121_, 0);
v_isSharedCheck_2161_ = !lean_is_exclusive(v___x_2121_);
if (v_isSharedCheck_2161_ == 0)
{
v___x_2156_ = v___x_2121_;
v_isShared_2157_ = v_isSharedCheck_2161_;
goto v_resetjp_2155_;
}
else
{
lean_inc(v_a_2154_);
lean_dec(v___x_2121_);
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
lean_object* v_a_2162_; lean_object* v___x_2164_; uint8_t v_isShared_2165_; uint8_t v_isSharedCheck_2169_; 
lean_dec(v_a_2118_);
lean_dec_ref(v_recursorInfo_2110_);
lean_dec(v_majorFVarId_2109_);
lean_dec(v_tacticName_2108_);
lean_dec(v_mvarId_2107_);
v_a_2162_ = lean_ctor_get(v___x_2119_, 0);
v_isSharedCheck_2169_ = !lean_is_exclusive(v___x_2119_);
if (v_isSharedCheck_2169_ == 0)
{
v___x_2164_ = v___x_2119_;
v_isShared_2165_ = v_isSharedCheck_2169_;
goto v_resetjp_2163_;
}
else
{
lean_inc(v_a_2162_);
lean_dec(v___x_2119_);
v___x_2164_ = lean_box(0);
v_isShared_2165_ = v_isSharedCheck_2169_;
goto v_resetjp_2163_;
}
v_resetjp_2163_:
{
lean_object* v___x_2167_; 
if (v_isShared_2165_ == 0)
{
v___x_2167_ = v___x_2164_;
goto v_reusejp_2166_;
}
else
{
lean_object* v_reuseFailAlloc_2168_; 
v_reuseFailAlloc_2168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2168_, 0, v_a_2162_);
v___x_2167_ = v_reuseFailAlloc_2168_;
goto v_reusejp_2166_;
}
v_reusejp_2166_:
{
return v___x_2167_;
}
}
}
}
else
{
lean_dec_ref(v_recursorInfo_2110_);
lean_dec(v_majorFVarId_2109_);
lean_dec(v_tacticName_2108_);
lean_dec(v_mvarId_2107_);
return v___x_2117_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkRecursorAppPrefix___boxed(lean_object* v_mvarId_2170_, lean_object* v_tacticName_2171_, lean_object* v_majorFVarId_2172_, lean_object* v_recursorInfo_2173_, lean_object* v_indices_2174_, lean_object* v_a_2175_, lean_object* v_a_2176_, lean_object* v_a_2177_, lean_object* v_a_2178_, lean_object* v_a_2179_){
_start:
{
lean_object* v_res_2180_; 
v_res_2180_ = l_Lean_Meta_mkRecursorAppPrefix(v_mvarId_2170_, v_tacticName_2171_, v_majorFVarId_2172_, v_recursorInfo_2173_, v_indices_2174_, v_a_2175_, v_a_2176_, v_a_2177_, v_a_2178_);
lean_dec(v_a_2178_);
lean_dec_ref(v_a_2177_);
lean_dec(v_a_2176_);
lean_dec_ref(v_a_2175_);
lean_dec_ref(v_indices_2174_);
return v_res_2180_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1(lean_object* v_00_u03b1_2181_, lean_object* v_name_2182_, lean_object* v_msg_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_){
_start:
{
lean_object* v___x_2189_; 
v___x_2189_ = l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1___redArg(v_name_2182_, v_msg_2183_, v___y_2184_, v___y_2185_, v___y_2186_, v___y_2187_);
return v___x_2189_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1___boxed(lean_object* v_00_u03b1_2190_, lean_object* v_name_2191_, lean_object* v_msg_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_){
_start:
{
lean_object* v_res_2198_; 
v_res_2198_ = l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1(v_00_u03b1_2190_, v_name_2191_, v_msg_2192_, v___y_2193_, v___y_2194_, v___y_2195_, v___y_2196_);
lean_dec(v___y_2196_);
lean_dec_ref(v___y_2195_);
lean_dec(v___y_2194_);
lean_dec_ref(v___y_2193_);
return v_res_2198_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___redArg(lean_object* v_mvarId_2199_, lean_object* v_x_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_){
_start:
{
lean_object* v___x_2206_; 
v___x_2206_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_2199_, v_x_2200_, v___y_2201_, v___y_2202_, v___y_2203_, v___y_2204_);
if (lean_obj_tag(v___x_2206_) == 0)
{
lean_object* v_a_2207_; lean_object* v___x_2209_; uint8_t v_isShared_2210_; uint8_t v_isSharedCheck_2214_; 
v_a_2207_ = lean_ctor_get(v___x_2206_, 0);
v_isSharedCheck_2214_ = !lean_is_exclusive(v___x_2206_);
if (v_isSharedCheck_2214_ == 0)
{
v___x_2209_ = v___x_2206_;
v_isShared_2210_ = v_isSharedCheck_2214_;
goto v_resetjp_2208_;
}
else
{
lean_inc(v_a_2207_);
lean_dec(v___x_2206_);
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
v_reuseFailAlloc_2213_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_2215_; lean_object* v___x_2217_; uint8_t v_isShared_2218_; uint8_t v_isSharedCheck_2222_; 
v_a_2215_ = lean_ctor_get(v___x_2206_, 0);
v_isSharedCheck_2222_ = !lean_is_exclusive(v___x_2206_);
if (v_isSharedCheck_2222_ == 0)
{
v___x_2217_ = v___x_2206_;
v_isShared_2218_ = v_isSharedCheck_2222_;
goto v_resetjp_2216_;
}
else
{
lean_inc(v_a_2215_);
lean_dec(v___x_2206_);
v___x_2217_ = lean_box(0);
v_isShared_2218_ = v_isSharedCheck_2222_;
goto v_resetjp_2216_;
}
v_resetjp_2216_:
{
lean_object* v___x_2220_; 
if (v_isShared_2218_ == 0)
{
v___x_2220_ = v___x_2217_;
goto v_reusejp_2219_;
}
else
{
lean_object* v_reuseFailAlloc_2221_; 
v_reuseFailAlloc_2221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2221_, 0, v_a_2215_);
v___x_2220_ = v_reuseFailAlloc_2221_;
goto v_reusejp_2219_;
}
v_reusejp_2219_:
{
return v___x_2220_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___redArg___boxed(lean_object* v_mvarId_2223_, lean_object* v_x_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_){
_start:
{
lean_object* v_res_2230_; 
v_res_2230_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___redArg(v_mvarId_2223_, v_x_2224_, v___y_2225_, v___y_2226_, v___y_2227_, v___y_2228_);
lean_dec(v___y_2228_);
lean_dec_ref(v___y_2227_);
lean_dec(v___y_2226_);
lean_dec_ref(v___y_2225_);
return v_res_2230_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3(lean_object* v_00_u03b1_2231_, lean_object* v_mvarId_2232_, lean_object* v_x_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_){
_start:
{
lean_object* v___x_2239_; 
v___x_2239_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___redArg(v_mvarId_2232_, v_x_2233_, v___y_2234_, v___y_2235_, v___y_2236_, v___y_2237_);
return v___x_2239_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___boxed(lean_object* v_00_u03b1_2240_, lean_object* v_mvarId_2241_, lean_object* v_x_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_){
_start:
{
lean_object* v_res_2248_; 
v_res_2248_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3(v_00_u03b1_2240_, v_mvarId_2241_, v_x_2242_, v___y_2243_, v___y_2244_, v___y_2245_, v___y_2246_);
lean_dec(v___y_2246_);
lean_dec_ref(v___y_2245_);
lean_dec(v___y_2244_);
lean_dec_ref(v___y_2243_);
return v_res_2248_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_induction_spec__2(lean_object* v_fst_2249_, lean_object* v_as_2250_, size_t v_sz_2251_, size_t v_i_2252_, lean_object* v_b_2253_){
_start:
{
uint8_t v___x_2254_; 
v___x_2254_ = lean_usize_dec_lt(v_i_2252_, v_sz_2251_);
if (v___x_2254_ == 0)
{
return v_b_2253_;
}
else
{
lean_object* v_fst_2255_; lean_object* v_snd_2256_; lean_object* v___x_2258_; uint8_t v_isShared_2259_; uint8_t v_isSharedCheck_2274_; 
v_fst_2255_ = lean_ctor_get(v_b_2253_, 0);
v_snd_2256_ = lean_ctor_get(v_b_2253_, 1);
v_isSharedCheck_2274_ = !lean_is_exclusive(v_b_2253_);
if (v_isSharedCheck_2274_ == 0)
{
v___x_2258_ = v_b_2253_;
v_isShared_2259_ = v_isSharedCheck_2274_;
goto v_resetjp_2257_;
}
else
{
lean_inc(v_snd_2256_);
lean_inc(v_fst_2255_);
lean_dec(v_b_2253_);
v___x_2258_ = lean_box(0);
v_isShared_2259_ = v_isSharedCheck_2274_;
goto v_resetjp_2257_;
}
v_resetjp_2257_:
{
lean_object* v___x_2260_; lean_object* v_a_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2269_; 
v___x_2260_ = lean_box(0);
v_a_2261_ = lean_array_uget_borrowed(v_as_2250_, v_i_2252_);
v___x_2262_ = l_Lean_Expr_fvarId_x21(v_a_2261_);
v___x_2263_ = lean_array_get_borrowed(v___x_2260_, v_fst_2249_, v_snd_2256_);
lean_inc(v___x_2263_);
v___x_2264_ = l_Lean_mkFVar(v___x_2263_);
v___x_2265_ = l_Lean_Meta_FVarSubst_insert(v_fst_2255_, v___x_2262_, v___x_2264_);
v___x_2266_ = lean_unsigned_to_nat(1u);
v___x_2267_ = lean_nat_add(v_snd_2256_, v___x_2266_);
lean_dec(v_snd_2256_);
if (v_isShared_2259_ == 0)
{
lean_ctor_set(v___x_2258_, 1, v___x_2267_);
lean_ctor_set(v___x_2258_, 0, v___x_2265_);
v___x_2269_ = v___x_2258_;
goto v_reusejp_2268_;
}
else
{
lean_object* v_reuseFailAlloc_2273_; 
v_reuseFailAlloc_2273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2273_, 0, v___x_2265_);
lean_ctor_set(v_reuseFailAlloc_2273_, 1, v___x_2267_);
v___x_2269_ = v_reuseFailAlloc_2273_;
goto v_reusejp_2268_;
}
v_reusejp_2268_:
{
size_t v___x_2270_; size_t v___x_2271_; 
v___x_2270_ = ((size_t)1ULL);
v___x_2271_ = lean_usize_add(v_i_2252_, v___x_2270_);
v_i_2252_ = v___x_2271_;
v_b_2253_ = v___x_2269_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_induction_spec__2___boxed(lean_object* v_fst_2275_, lean_object* v_as_2276_, lean_object* v_sz_2277_, lean_object* v_i_2278_, lean_object* v_b_2279_){
_start:
{
size_t v_sz_boxed_2280_; size_t v_i_boxed_2281_; lean_object* v_res_2282_; 
v_sz_boxed_2280_ = lean_unbox_usize(v_sz_2277_);
lean_dec(v_sz_2277_);
v_i_boxed_2281_ = lean_unbox_usize(v_i_2278_);
lean_dec(v_i_2278_);
v_res_2282_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_induction_spec__2(v_fst_2275_, v_as_2276_, v_sz_boxed_2280_, v_i_boxed_2281_, v_b_2279_);
lean_dec_ref(v_as_2276_);
lean_dec_ref(v_fst_2275_);
return v_res_2282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4___lam__0(lean_object* v_snd_2283_, lean_object* v___x_2284_, lean_object* v_fst_2285_, lean_object* v_a_2286_, lean_object* v___x_2287_, lean_object* v_givenNames_2288_, lean_object* v_fst_2289_, lean_object* v___x_2290_, lean_object* v_fst_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_){
_start:
{
lean_object* v___x_2297_; 
lean_inc_ref(v_a_2286_);
lean_inc(v_snd_2283_);
v___x_2297_ = l_Lean_Meta_mkRecursorAppPrefix(v_snd_2283_, v___x_2284_, v_fst_2285_, v_a_2286_, v___x_2287_, v___y_2292_, v___y_2293_, v___y_2294_, v___y_2295_);
if (lean_obj_tag(v___x_2297_) == 0)
{
lean_object* v_a_2298_; lean_object* v___x_2299_; 
v_a_2298_ = lean_ctor_get(v___x_2297_, 0);
lean_inc(v_a_2298_);
lean_dec_ref(v___x_2297_);
v___x_2299_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize(v_snd_2283_, v_givenNames_2288_, v_a_2286_, v_fst_2289_, v___x_2290_, v___x_2287_, v_fst_2291_, v_a_2298_, v___y_2292_, v___y_2293_, v___y_2294_, v___y_2295_);
lean_dec_ref(v_a_2286_);
return v___x_2299_;
}
else
{
lean_object* v_a_2300_; lean_object* v___x_2302_; uint8_t v_isShared_2303_; uint8_t v_isSharedCheck_2307_; 
lean_dec(v_fst_2291_);
lean_dec_ref(v___x_2290_);
lean_dec_ref(v_a_2286_);
lean_dec(v_snd_2283_);
v_a_2300_ = lean_ctor_get(v___x_2297_, 0);
v_isSharedCheck_2307_ = !lean_is_exclusive(v___x_2297_);
if (v_isSharedCheck_2307_ == 0)
{
v___x_2302_ = v___x_2297_;
v_isShared_2303_ = v_isSharedCheck_2307_;
goto v_resetjp_2301_;
}
else
{
lean_inc(v_a_2300_);
lean_dec(v___x_2297_);
v___x_2302_ = lean_box(0);
v_isShared_2303_ = v_isSharedCheck_2307_;
goto v_resetjp_2301_;
}
v_resetjp_2301_:
{
lean_object* v___x_2305_; 
if (v_isShared_2303_ == 0)
{
v___x_2305_ = v___x_2302_;
goto v_reusejp_2304_;
}
else
{
lean_object* v_reuseFailAlloc_2306_; 
v_reuseFailAlloc_2306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2306_, 0, v_a_2300_);
v___x_2305_ = v_reuseFailAlloc_2306_;
goto v_reusejp_2304_;
}
v_reusejp_2304_:
{
return v___x_2305_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4___lam__0___boxed(lean_object* v_snd_2308_, lean_object* v___x_2309_, lean_object* v_fst_2310_, lean_object* v_a_2311_, lean_object* v___x_2312_, lean_object* v_givenNames_2313_, lean_object* v_fst_2314_, lean_object* v___x_2315_, lean_object* v_fst_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_){
_start:
{
lean_object* v_res_2322_; 
v_res_2322_ = l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4___lam__0(v_snd_2308_, v___x_2309_, v_fst_2310_, v_a_2311_, v___x_2312_, v_givenNames_2313_, v_fst_2314_, v___x_2315_, v_fst_2316_, v___y_2317_, v___y_2318_, v___y_2319_, v___y_2320_);
lean_dec(v___y_2320_);
lean_dec_ref(v___y_2319_);
lean_dec(v___y_2318_);
lean_dec_ref(v___y_2317_);
lean_dec_ref(v_fst_2314_);
lean_dec_ref(v_givenNames_2313_);
lean_dec_ref(v___x_2312_);
return v_res_2322_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_induction_spec__1(size_t v_sz_2323_, size_t v_i_2324_, lean_object* v_bs_2325_){
_start:
{
uint8_t v___x_2326_; 
v___x_2326_ = lean_usize_dec_lt(v_i_2324_, v_sz_2323_);
if (v___x_2326_ == 0)
{
return v_bs_2325_;
}
else
{
lean_object* v_v_2327_; lean_object* v___x_2328_; lean_object* v_bs_x27_2329_; lean_object* v___x_2330_; size_t v___x_2331_; size_t v___x_2332_; lean_object* v___x_2333_; 
v_v_2327_ = lean_array_uget(v_bs_2325_, v_i_2324_);
v___x_2328_ = lean_unsigned_to_nat(0u);
v_bs_x27_2329_ = lean_array_uset(v_bs_2325_, v_i_2324_, v___x_2328_);
v___x_2330_ = l_Lean_Expr_fvarId_x21(v_v_2327_);
lean_dec(v_v_2327_);
v___x_2331_ = ((size_t)1ULL);
v___x_2332_ = lean_usize_add(v_i_2324_, v___x_2331_);
v___x_2333_ = lean_array_uset(v_bs_x27_2329_, v_i_2324_, v___x_2330_);
v_i_2324_ = v___x_2332_;
v_bs_2325_ = v___x_2333_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_induction_spec__1___boxed(lean_object* v_sz_2335_, lean_object* v_i_2336_, lean_object* v_bs_2337_){
_start:
{
size_t v_sz_boxed_2338_; size_t v_i_boxed_2339_; lean_object* v_res_2340_; 
v_sz_boxed_2338_ = lean_unbox_usize(v_sz_2335_);
lean_dec(v_sz_2335_);
v_i_boxed_2339_ = lean_unbox_usize(v_i_2336_);
lean_dec(v_i_2336_);
v_res_2340_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_induction_spec__1(v_sz_boxed_2338_, v_i_boxed_2339_, v_bs_2337_);
return v_res_2340_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_MVarId_induction_spec__0(lean_object* v_majorTypeArgs_2341_, lean_object* v_val_2342_, lean_object* v_mvarId_2343_, lean_object* v_as_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_){
_start:
{
if (lean_obj_tag(v_as_2344_) == 0)
{
lean_object* v___x_2350_; lean_object* v___x_2351_; 
lean_dec(v_mvarId_2343_);
lean_dec_ref(v_val_2342_);
v___x_2350_ = lean_box(0);
v___x_2351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2351_, 0, v___x_2350_);
return v___x_2351_;
}
else
{
lean_object* v_head_2352_; 
v_head_2352_ = lean_ctor_get(v_as_2344_, 0);
lean_inc(v_head_2352_);
if (lean_obj_tag(v_head_2352_) == 0)
{
lean_object* v_tail_2353_; 
v_tail_2353_ = lean_ctor_get(v_as_2344_, 1);
lean_inc(v_tail_2353_);
lean_dec_ref(v_as_2344_);
v_as_2344_ = v_tail_2353_;
goto _start;
}
else
{
lean_object* v_tail_2355_; lean_object* v___x_2357_; uint8_t v_isShared_2358_; uint8_t v_isSharedCheck_2378_; 
v_tail_2355_ = lean_ctor_get(v_as_2344_, 1);
v_isSharedCheck_2378_ = !lean_is_exclusive(v_as_2344_);
if (v_isSharedCheck_2378_ == 0)
{
lean_object* v_unused_2379_; 
v_unused_2379_ = lean_ctor_get(v_as_2344_, 0);
lean_dec(v_unused_2379_);
v___x_2357_ = v_as_2344_;
v_isShared_2358_ = v_isSharedCheck_2378_;
goto v_resetjp_2356_;
}
else
{
lean_inc(v_tail_2355_);
lean_dec(v_as_2344_);
v___x_2357_ = lean_box(0);
v_isShared_2358_ = v_isSharedCheck_2378_;
goto v_resetjp_2356_;
}
v_resetjp_2356_:
{
lean_object* v_val_2359_; lean_object* v___x_2361_; uint8_t v_isShared_2362_; uint8_t v_isSharedCheck_2377_; 
v_val_2359_ = lean_ctor_get(v_head_2352_, 0);
v_isSharedCheck_2377_ = !lean_is_exclusive(v_head_2352_);
if (v_isSharedCheck_2377_ == 0)
{
v___x_2361_ = v_head_2352_;
v_isShared_2362_ = v_isSharedCheck_2377_;
goto v_resetjp_2360_;
}
else
{
lean_inc(v_val_2359_);
lean_dec(v_head_2352_);
v___x_2361_ = lean_box(0);
v_isShared_2362_ = v_isSharedCheck_2377_;
goto v_resetjp_2360_;
}
v_resetjp_2360_:
{
lean_object* v___x_2363_; uint8_t v___x_2364_; 
v___x_2363_ = lean_array_get_size(v_majorTypeArgs_2341_);
v___x_2364_ = lean_nat_dec_le(v___x_2363_, v_val_2359_);
lean_dec(v_val_2359_);
if (v___x_2364_ == 0)
{
lean_del_object(v___x_2361_);
lean_del_object(v___x_2357_);
v_as_2344_ = v_tail_2355_;
goto _start;
}
else
{
lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2370_; 
v___x_2366_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1));
v___x_2367_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__5, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__5);
lean_inc_ref(v_val_2342_);
v___x_2368_ = l_Lean_indentExpr(v_val_2342_);
if (v_isShared_2358_ == 0)
{
lean_ctor_set_tag(v___x_2357_, 7);
lean_ctor_set(v___x_2357_, 1, v___x_2368_);
lean_ctor_set(v___x_2357_, 0, v___x_2367_);
v___x_2370_ = v___x_2357_;
goto v_reusejp_2369_;
}
else
{
lean_object* v_reuseFailAlloc_2376_; 
v_reuseFailAlloc_2376_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2376_, 0, v___x_2367_);
lean_ctor_set(v_reuseFailAlloc_2376_, 1, v___x_2368_);
v___x_2370_ = v_reuseFailAlloc_2376_;
goto v_reusejp_2369_;
}
v_reusejp_2369_:
{
lean_object* v___x_2372_; 
if (v_isShared_2362_ == 0)
{
lean_ctor_set(v___x_2361_, 0, v___x_2370_);
v___x_2372_ = v___x_2361_;
goto v_reusejp_2371_;
}
else
{
lean_object* v_reuseFailAlloc_2375_; 
v_reuseFailAlloc_2375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2375_, 0, v___x_2370_);
v___x_2372_ = v_reuseFailAlloc_2375_;
goto v_reusejp_2371_;
}
v_reusejp_2371_:
{
lean_object* v___x_2373_; 
lean_inc(v_mvarId_2343_);
v___x_2373_ = l_Lean_Meta_throwTacticEx___redArg(v___x_2366_, v_mvarId_2343_, v___x_2372_, v___y_2345_, v___y_2346_, v___y_2347_, v___y_2348_);
if (lean_obj_tag(v___x_2373_) == 0)
{
lean_dec_ref(v___x_2373_);
v_as_2344_ = v_tail_2355_;
goto _start;
}
else
{
lean_dec(v_tail_2355_);
lean_dec(v_mvarId_2343_);
lean_dec_ref(v_val_2342_);
return v___x_2373_;
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
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_MVarId_induction_spec__0___boxed(lean_object* v_majorTypeArgs_2380_, lean_object* v_val_2381_, lean_object* v_mvarId_2382_, lean_object* v_as_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_){
_start:
{
lean_object* v_res_2389_; 
v_res_2389_ = l_List_forM___at___00Lean_MVarId_induction_spec__0(v_majorTypeArgs_2380_, v_val_2381_, v_mvarId_2382_, v_as_2383_, v___y_2384_, v___y_2385_, v___y_2386_, v___y_2387_);
lean_dec(v___y_2387_);
lean_dec_ref(v___y_2386_);
lean_dec(v___y_2385_);
lean_dec_ref(v___y_2384_);
lean_dec_ref(v_majorTypeArgs_2380_);
return v_res_2389_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__1(void){
_start:
{
lean_object* v___x_2391_; lean_object* v___x_2392_; 
v___x_2391_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__0));
v___x_2392_ = l_Lean_stringToMessageData(v___x_2391_);
return v___x_2392_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__3(void){
_start:
{
lean_object* v___x_2394_; lean_object* v___x_2395_; 
v___x_2394_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__2));
v___x_2395_ = l_Lean_stringToMessageData(v___x_2394_);
return v___x_2395_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__5(void){
_start:
{
lean_object* v___x_2397_; lean_object* v___x_2398_; 
v___x_2397_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__4));
v___x_2398_ = l_Lean_stringToMessageData(v___x_2397_);
return v___x_2398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4(lean_object* v_a_2399_, lean_object* v_val_2400_, lean_object* v_mvarId_2401_, lean_object* v_majorFVarId_2402_, lean_object* v_givenNames_2403_, lean_object* v_recursorName_2404_, lean_object* v_x_2405_, lean_object* v_x_2406_, lean_object* v_x_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_){
_start:
{
if (lean_obj_tag(v_x_2405_) == 5)
{
lean_object* v_fn_2413_; lean_object* v_arg_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; 
v_fn_2413_ = lean_ctor_get(v_x_2405_, 0);
lean_inc_ref(v_fn_2413_);
v_arg_2414_ = lean_ctor_get(v_x_2405_, 1);
lean_inc_ref(v_arg_2414_);
lean_dec_ref(v_x_2405_);
v___x_2415_ = lean_array_set(v_x_2406_, v_x_2407_, v_arg_2414_);
v___x_2416_ = lean_unsigned_to_nat(1u);
v___x_2417_ = lean_nat_sub(v_x_2407_, v___x_2416_);
lean_dec(v_x_2407_);
v_x_2405_ = v_fn_2413_;
v_x_2406_ = v___x_2415_;
v_x_2407_ = v___x_2417_;
goto _start;
}
else
{
uint8_t v_depElim_2419_; lean_object* v_paramsPos_2420_; lean_object* v___x_2421_; 
lean_dec(v_x_2407_);
lean_dec_ref(v_x_2405_);
v_depElim_2419_ = lean_ctor_get_uint8(v_a_2399_, sizeof(void*)*8);
v_paramsPos_2420_ = lean_ctor_get(v_a_2399_, 5);
lean_inc(v_paramsPos_2420_);
lean_inc(v_mvarId_2401_);
lean_inc_ref(v_val_2400_);
v___x_2421_ = l_List_forM___at___00Lean_MVarId_induction_spec__0(v_x_2406_, v_val_2400_, v_mvarId_2401_, v_paramsPos_2420_, v___y_2408_, v___y_2409_, v___y_2410_, v___y_2411_);
lean_dec_ref(v_x_2406_);
if (lean_obj_tag(v___x_2421_) == 0)
{
lean_object* v___x_2422_; lean_object* v___y_2424_; lean_object* v___y_2425_; lean_object* v___y_2426_; lean_object* v___y_2427_; lean_object* v___y_2428_; lean_object* v___y_2429_; lean_object* v___y_2430_; size_t v___y_2431_; lean_object* v___y_2432_; lean_object* v___y_2433_; lean_object* v___y_2434_; lean_object* v___y_2435_; lean_object* v___x_2440_; 
lean_dec_ref(v___x_2421_);
v___x_2422_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1));
lean_inc_ref(v_a_2399_);
lean_inc(v_mvarId_2401_);
v___x_2440_ = l_Lean_Meta_getMajorTypeIndices(v_mvarId_2401_, v___x_2422_, v_a_2399_, v_val_2400_, v___y_2408_, v___y_2409_, v___y_2410_, v___y_2411_);
if (lean_obj_tag(v___x_2440_) == 0)
{
lean_object* v_a_2441_; lean_object* v___x_2442_; 
v_a_2441_ = lean_ctor_get(v___x_2440_, 0);
lean_inc(v_a_2441_);
lean_dec_ref(v___x_2440_);
lean_inc(v_mvarId_2401_);
v___x_2442_ = l_Lean_MVarId_getType(v_mvarId_2401_, v___y_2408_, v___y_2409_, v___y_2410_, v___y_2411_);
if (lean_obj_tag(v___x_2442_) == 0)
{
lean_object* v_a_2443_; lean_object* v_cls_2444_; lean_object* v___y_2446_; lean_object* v___y_2447_; lean_object* v___y_2448_; lean_object* v___y_2449_; 
v_a_2443_ = lean_ctor_get(v___x_2442_, 0);
lean_inc(v_a_2443_);
lean_dec_ref(v___x_2442_);
v_cls_2444_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__2));
if (v_depElim_2419_ == 0)
{
lean_object* v___x_2532_; lean_object* v_a_2533_; lean_object* v___x_2535_; uint8_t v_isShared_2536_; uint8_t v_isSharedCheck_2555_; 
lean_inc(v_majorFVarId_2402_);
v___x_2532_ = l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2___redArg(v_a_2443_, v_majorFVarId_2402_, v___y_2409_);
v_a_2533_ = lean_ctor_get(v___x_2532_, 0);
v_isSharedCheck_2555_ = !lean_is_exclusive(v___x_2532_);
if (v_isSharedCheck_2555_ == 0)
{
v___x_2535_ = v___x_2532_;
v_isShared_2536_ = v_isSharedCheck_2555_;
goto v_resetjp_2534_;
}
else
{
lean_inc(v_a_2533_);
lean_dec(v___x_2532_);
v___x_2535_ = lean_box(0);
v_isShared_2536_ = v_isSharedCheck_2555_;
goto v_resetjp_2534_;
}
v_resetjp_2534_:
{
uint8_t v___x_2537_; 
v___x_2537_ = lean_unbox(v_a_2533_);
lean_dec(v_a_2533_);
if (v___x_2537_ == 0)
{
lean_del_object(v___x_2535_);
lean_dec(v_recursorName_2404_);
v___y_2446_ = v___y_2408_;
v___y_2447_ = v___y_2409_;
v___y_2448_ = v___y_2410_;
v___y_2449_ = v___y_2411_;
goto v___jp_2445_;
}
else
{
lean_object* v___x_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2544_; 
v___x_2538_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__3, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__3);
v___x_2539_ = l_Lean_MessageData_ofName(v_recursorName_2404_);
v___x_2540_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2540_, 0, v___x_2538_);
lean_ctor_set(v___x_2540_, 1, v___x_2539_);
v___x_2541_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__5, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__5_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__5);
v___x_2542_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2542_, 0, v___x_2540_);
lean_ctor_set(v___x_2542_, 1, v___x_2541_);
if (v_isShared_2536_ == 0)
{
lean_ctor_set_tag(v___x_2535_, 1);
lean_ctor_set(v___x_2535_, 0, v___x_2542_);
v___x_2544_ = v___x_2535_;
goto v_reusejp_2543_;
}
else
{
lean_object* v_reuseFailAlloc_2554_; 
v_reuseFailAlloc_2554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2554_, 0, v___x_2542_);
v___x_2544_ = v_reuseFailAlloc_2554_;
goto v_reusejp_2543_;
}
v_reusejp_2543_:
{
lean_object* v___x_2545_; 
lean_inc(v_mvarId_2401_);
v___x_2545_ = l_Lean_Meta_throwTacticEx___redArg(v___x_2422_, v_mvarId_2401_, v___x_2544_, v___y_2408_, v___y_2409_, v___y_2410_, v___y_2411_);
if (lean_obj_tag(v___x_2545_) == 0)
{
lean_dec_ref(v___x_2545_);
v___y_2446_ = v___y_2408_;
v___y_2447_ = v___y_2409_;
v___y_2448_ = v___y_2410_;
v___y_2449_ = v___y_2411_;
goto v___jp_2445_;
}
else
{
lean_object* v_a_2546_; lean_object* v___x_2548_; uint8_t v_isShared_2549_; uint8_t v_isSharedCheck_2553_; 
lean_dec(v_a_2441_);
lean_dec_ref(v_givenNames_2403_);
lean_dec(v_majorFVarId_2402_);
lean_dec(v_mvarId_2401_);
lean_dec_ref(v_a_2399_);
v_a_2546_ = lean_ctor_get(v___x_2545_, 0);
v_isSharedCheck_2553_ = !lean_is_exclusive(v___x_2545_);
if (v_isSharedCheck_2553_ == 0)
{
v___x_2548_ = v___x_2545_;
v_isShared_2549_ = v_isSharedCheck_2553_;
goto v_resetjp_2547_;
}
else
{
lean_inc(v_a_2546_);
lean_dec(v___x_2545_);
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
}
}
}
}
else
{
lean_dec(v_a_2443_);
lean_dec(v_recursorName_2404_);
v___y_2446_ = v___y_2408_;
v___y_2447_ = v___y_2409_;
v___y_2448_ = v___y_2410_;
v___y_2449_ = v___y_2411_;
goto v___jp_2445_;
}
v___jp_2445_:
{
size_t v_sz_2450_; size_t v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; uint8_t v___x_2454_; uint8_t v___x_2455_; lean_object* v___x_2456_; 
v_sz_2450_ = lean_array_size(v_a_2441_);
v___x_2451_ = ((size_t)0ULL);
lean_inc(v_a_2441_);
v___x_2452_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_induction_spec__1(v_sz_2450_, v___x_2451_, v_a_2441_);
lean_inc(v_majorFVarId_2402_);
v___x_2453_ = lean_array_push(v___x_2452_, v_majorFVarId_2402_);
v___x_2454_ = 1;
v___x_2455_ = 0;
v___x_2456_ = l_Lean_MVarId_revert(v_mvarId_2401_, v___x_2453_, v___x_2454_, v___x_2455_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_);
if (lean_obj_tag(v___x_2456_) == 0)
{
lean_object* v_a_2457_; lean_object* v_fst_2458_; lean_object* v_snd_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; 
v_a_2457_ = lean_ctor_get(v___x_2456_, 0);
lean_inc(v_a_2457_);
lean_dec_ref(v___x_2456_);
v_fst_2458_ = lean_ctor_get(v_a_2457_, 0);
lean_inc(v_fst_2458_);
v_snd_2459_ = lean_ctor_get(v_a_2457_, 1);
lean_inc(v_snd_2459_);
lean_dec(v_a_2457_);
v___x_2460_ = lean_array_get_size(v_a_2441_);
v___x_2461_ = lean_box(0);
v___x_2462_ = l_Lean_Meta_introNCore(v_snd_2459_, v___x_2460_, v___x_2461_, v___x_2455_, v___x_2454_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_);
if (lean_obj_tag(v___x_2462_) == 0)
{
lean_object* v_a_2463_; lean_object* v_fst_2464_; lean_object* v_snd_2465_; lean_object* v___x_2466_; 
v_a_2463_ = lean_ctor_get(v___x_2462_, 0);
lean_inc(v_a_2463_);
lean_dec_ref(v___x_2462_);
v_fst_2464_ = lean_ctor_get(v_a_2463_, 0);
lean_inc(v_fst_2464_);
v_snd_2465_ = lean_ctor_get(v_a_2463_, 1);
lean_inc(v_snd_2465_);
lean_dec(v_a_2463_);
v___x_2466_ = l_Lean_Meta_intro1Core(v_snd_2465_, v___x_2454_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_);
if (lean_obj_tag(v___x_2466_) == 0)
{
lean_object* v_a_2467_; lean_object* v_fst_2468_; lean_object* v_snd_2469_; lean_object* v___x_2471_; uint8_t v_isShared_2472_; uint8_t v_isSharedCheck_2507_; 
v_a_2467_ = lean_ctor_get(v___x_2466_, 0);
lean_inc(v_a_2467_);
lean_dec_ref(v___x_2466_);
v_fst_2468_ = lean_ctor_get(v_a_2467_, 0);
v_snd_2469_ = lean_ctor_get(v_a_2467_, 1);
v_isSharedCheck_2507_ = !lean_is_exclusive(v_a_2467_);
if (v_isSharedCheck_2507_ == 0)
{
v___x_2471_ = v_a_2467_;
v_isShared_2472_ = v_isSharedCheck_2507_;
goto v_resetjp_2470_;
}
else
{
lean_inc(v_snd_2469_);
lean_inc(v_fst_2468_);
lean_dec(v_a_2467_);
v___x_2471_ = lean_box(0);
v_isShared_2472_ = v_isSharedCheck_2507_;
goto v_resetjp_2470_;
}
v_resetjp_2470_:
{
lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2478_; 
v___x_2473_ = lean_box(0);
lean_inc(v_fst_2468_);
v___x_2474_ = l_Lean_mkFVar(v_fst_2468_);
lean_inc_ref(v___x_2474_);
v___x_2475_ = l_Lean_Meta_FVarSubst_insert(v___x_2473_, v_majorFVarId_2402_, v___x_2474_);
v___x_2476_ = lean_unsigned_to_nat(0u);
if (v_isShared_2472_ == 0)
{
lean_ctor_set(v___x_2471_, 1, v___x_2476_);
lean_ctor_set(v___x_2471_, 0, v___x_2475_);
v___x_2478_ = v___x_2471_;
goto v_reusejp_2477_;
}
else
{
lean_object* v_reuseFailAlloc_2506_; 
v_reuseFailAlloc_2506_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2506_, 0, v___x_2475_);
lean_ctor_set(v_reuseFailAlloc_2506_, 1, v___x_2476_);
v___x_2478_ = v_reuseFailAlloc_2506_;
goto v_reusejp_2477_;
}
v_reusejp_2477_:
{
lean_object* v___x_2479_; lean_object* v_options_2480_; uint8_t v_hasTrace_2481_; 
v___x_2479_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_induction_spec__2(v_fst_2464_, v_a_2441_, v_sz_2450_, v___x_2451_, v___x_2478_);
lean_dec(v_a_2441_);
v_options_2480_ = lean_ctor_get(v___y_2448_, 2);
v_hasTrace_2481_ = lean_ctor_get_uint8(v_options_2480_, sizeof(void*)*1);
if (v_hasTrace_2481_ == 0)
{
lean_object* v_fst_2482_; 
v_fst_2482_ = lean_ctor_get(v___x_2479_, 0);
lean_inc(v_fst_2482_);
lean_dec_ref(v___x_2479_);
lean_inc(v_snd_2469_);
v___y_2424_ = v_fst_2458_;
v___y_2425_ = v_fst_2468_;
v___y_2426_ = v___x_2474_;
v___y_2427_ = v_snd_2469_;
v___y_2428_ = v_fst_2482_;
v___y_2429_ = v_fst_2464_;
v___y_2430_ = v_snd_2469_;
v___y_2431_ = v___x_2451_;
v___y_2432_ = v___y_2446_;
v___y_2433_ = v___y_2447_;
v___y_2434_ = v___y_2448_;
v___y_2435_ = v___y_2449_;
goto v___jp_2423_;
}
else
{
lean_object* v_fst_2483_; lean_object* v___x_2485_; uint8_t v_isShared_2486_; uint8_t v_isSharedCheck_2504_; 
v_fst_2483_ = lean_ctor_get(v___x_2479_, 0);
v_isSharedCheck_2504_ = !lean_is_exclusive(v___x_2479_);
if (v_isSharedCheck_2504_ == 0)
{
lean_object* v_unused_2505_; 
v_unused_2505_ = lean_ctor_get(v___x_2479_, 1);
lean_dec(v_unused_2505_);
v___x_2485_ = v___x_2479_;
v_isShared_2486_ = v_isSharedCheck_2504_;
goto v_resetjp_2484_;
}
else
{
lean_inc(v_fst_2483_);
lean_dec(v___x_2479_);
v___x_2485_ = lean_box(0);
v_isShared_2486_ = v_isSharedCheck_2504_;
goto v_resetjp_2484_;
}
v_resetjp_2484_:
{
lean_object* v_inheritedTraceOptions_2487_; lean_object* v___x_2488_; uint8_t v___x_2489_; 
v_inheritedTraceOptions_2487_ = lean_ctor_get(v___y_2448_, 13);
v___x_2488_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5);
v___x_2489_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2487_, v_options_2480_, v___x_2488_);
if (v___x_2489_ == 0)
{
lean_del_object(v___x_2485_);
lean_inc(v_snd_2469_);
v___y_2424_ = v_fst_2458_;
v___y_2425_ = v_fst_2468_;
v___y_2426_ = v___x_2474_;
v___y_2427_ = v_snd_2469_;
v___y_2428_ = v_fst_2483_;
v___y_2429_ = v_fst_2464_;
v___y_2430_ = v_snd_2469_;
v___y_2431_ = v___x_2451_;
v___y_2432_ = v___y_2446_;
v___y_2433_ = v___y_2447_;
v___y_2434_ = v___y_2448_;
v___y_2435_ = v___y_2449_;
goto v___jp_2423_;
}
else
{
lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2493_; 
v___x_2490_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__1);
lean_inc(v_snd_2469_);
v___x_2491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2491_, 0, v_snd_2469_);
if (v_isShared_2486_ == 0)
{
lean_ctor_set_tag(v___x_2485_, 7);
lean_ctor_set(v___x_2485_, 1, v___x_2491_);
lean_ctor_set(v___x_2485_, 0, v___x_2490_);
v___x_2493_ = v___x_2485_;
goto v_reusejp_2492_;
}
else
{
lean_object* v_reuseFailAlloc_2503_; 
v_reuseFailAlloc_2503_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2503_, 0, v___x_2490_);
lean_ctor_set(v_reuseFailAlloc_2503_, 1, v___x_2491_);
v___x_2493_ = v_reuseFailAlloc_2503_;
goto v_reusejp_2492_;
}
v_reusejp_2492_:
{
lean_object* v___x_2494_; 
v___x_2494_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1(v_cls_2444_, v___x_2493_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_);
if (lean_obj_tag(v___x_2494_) == 0)
{
lean_dec_ref(v___x_2494_);
lean_inc(v_snd_2469_);
v___y_2424_ = v_fst_2458_;
v___y_2425_ = v_fst_2468_;
v___y_2426_ = v___x_2474_;
v___y_2427_ = v_snd_2469_;
v___y_2428_ = v_fst_2483_;
v___y_2429_ = v_fst_2464_;
v___y_2430_ = v_snd_2469_;
v___y_2431_ = v___x_2451_;
v___y_2432_ = v___y_2446_;
v___y_2433_ = v___y_2447_;
v___y_2434_ = v___y_2448_;
v___y_2435_ = v___y_2449_;
goto v___jp_2423_;
}
else
{
lean_object* v_a_2495_; lean_object* v___x_2497_; uint8_t v_isShared_2498_; uint8_t v_isSharedCheck_2502_; 
lean_dec(v_fst_2483_);
lean_dec_ref(v___x_2474_);
lean_dec(v_snd_2469_);
lean_dec(v_fst_2468_);
lean_dec(v_fst_2464_);
lean_dec(v_fst_2458_);
lean_dec_ref(v_givenNames_2403_);
lean_dec_ref(v_a_2399_);
v_a_2495_ = lean_ctor_get(v___x_2494_, 0);
v_isSharedCheck_2502_ = !lean_is_exclusive(v___x_2494_);
if (v_isSharedCheck_2502_ == 0)
{
v___x_2497_ = v___x_2494_;
v_isShared_2498_ = v_isSharedCheck_2502_;
goto v_resetjp_2496_;
}
else
{
lean_inc(v_a_2495_);
lean_dec(v___x_2494_);
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
}
}
}
}
}
else
{
lean_object* v_a_2508_; lean_object* v___x_2510_; uint8_t v_isShared_2511_; uint8_t v_isSharedCheck_2515_; 
lean_dec(v_fst_2464_);
lean_dec(v_fst_2458_);
lean_dec(v_a_2441_);
lean_dec_ref(v_givenNames_2403_);
lean_dec(v_majorFVarId_2402_);
lean_dec_ref(v_a_2399_);
v_a_2508_ = lean_ctor_get(v___x_2466_, 0);
v_isSharedCheck_2515_ = !lean_is_exclusive(v___x_2466_);
if (v_isSharedCheck_2515_ == 0)
{
v___x_2510_ = v___x_2466_;
v_isShared_2511_ = v_isSharedCheck_2515_;
goto v_resetjp_2509_;
}
else
{
lean_inc(v_a_2508_);
lean_dec(v___x_2466_);
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
lean_dec(v_fst_2458_);
lean_dec(v_a_2441_);
lean_dec_ref(v_givenNames_2403_);
lean_dec(v_majorFVarId_2402_);
lean_dec_ref(v_a_2399_);
v_a_2516_ = lean_ctor_get(v___x_2462_, 0);
v_isSharedCheck_2523_ = !lean_is_exclusive(v___x_2462_);
if (v_isSharedCheck_2523_ == 0)
{
v___x_2518_ = v___x_2462_;
v_isShared_2519_ = v_isSharedCheck_2523_;
goto v_resetjp_2517_;
}
else
{
lean_inc(v_a_2516_);
lean_dec(v___x_2462_);
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
else
{
lean_object* v_a_2524_; lean_object* v___x_2526_; uint8_t v_isShared_2527_; uint8_t v_isSharedCheck_2531_; 
lean_dec(v_a_2441_);
lean_dec_ref(v_givenNames_2403_);
lean_dec(v_majorFVarId_2402_);
lean_dec_ref(v_a_2399_);
v_a_2524_ = lean_ctor_get(v___x_2456_, 0);
v_isSharedCheck_2531_ = !lean_is_exclusive(v___x_2456_);
if (v_isSharedCheck_2531_ == 0)
{
v___x_2526_ = v___x_2456_;
v_isShared_2527_ = v_isSharedCheck_2531_;
goto v_resetjp_2525_;
}
else
{
lean_inc(v_a_2524_);
lean_dec(v___x_2456_);
v___x_2526_ = lean_box(0);
v_isShared_2527_ = v_isSharedCheck_2531_;
goto v_resetjp_2525_;
}
v_resetjp_2525_:
{
lean_object* v___x_2529_; 
if (v_isShared_2527_ == 0)
{
v___x_2529_ = v___x_2526_;
goto v_reusejp_2528_;
}
else
{
lean_object* v_reuseFailAlloc_2530_; 
v_reuseFailAlloc_2530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2530_, 0, v_a_2524_);
v___x_2529_ = v_reuseFailAlloc_2530_;
goto v_reusejp_2528_;
}
v_reusejp_2528_:
{
return v___x_2529_;
}
}
}
}
}
else
{
lean_object* v_a_2556_; lean_object* v___x_2558_; uint8_t v_isShared_2559_; uint8_t v_isSharedCheck_2563_; 
lean_dec(v_a_2441_);
lean_dec(v_recursorName_2404_);
lean_dec_ref(v_givenNames_2403_);
lean_dec(v_majorFVarId_2402_);
lean_dec(v_mvarId_2401_);
lean_dec_ref(v_a_2399_);
v_a_2556_ = lean_ctor_get(v___x_2442_, 0);
v_isSharedCheck_2563_ = !lean_is_exclusive(v___x_2442_);
if (v_isSharedCheck_2563_ == 0)
{
v___x_2558_ = v___x_2442_;
v_isShared_2559_ = v_isSharedCheck_2563_;
goto v_resetjp_2557_;
}
else
{
lean_inc(v_a_2556_);
lean_dec(v___x_2442_);
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
lean_dec(v_recursorName_2404_);
lean_dec_ref(v_givenNames_2403_);
lean_dec(v_majorFVarId_2402_);
lean_dec(v_mvarId_2401_);
lean_dec_ref(v_a_2399_);
v_a_2564_ = lean_ctor_get(v___x_2440_, 0);
v_isSharedCheck_2571_ = !lean_is_exclusive(v___x_2440_);
if (v_isSharedCheck_2571_ == 0)
{
v___x_2566_ = v___x_2440_;
v_isShared_2567_ = v_isSharedCheck_2571_;
goto v_resetjp_2565_;
}
else
{
lean_inc(v_a_2564_);
lean_dec(v___x_2440_);
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
v___jp_2423_:
{
size_t v_sz_2436_; lean_object* v___x_2437_; lean_object* v___f_2438_; lean_object* v___x_2439_; 
v_sz_2436_ = lean_array_size(v___y_2429_);
v___x_2437_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__3(v_sz_2436_, v___y_2431_, v___y_2429_);
v___f_2438_ = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4___lam__0___boxed), 14, 9);
lean_closure_set(v___f_2438_, 0, v___y_2427_);
lean_closure_set(v___f_2438_, 1, v___x_2422_);
lean_closure_set(v___f_2438_, 2, v___y_2425_);
lean_closure_set(v___f_2438_, 3, v_a_2399_);
lean_closure_set(v___f_2438_, 4, v___x_2437_);
lean_closure_set(v___f_2438_, 5, v_givenNames_2403_);
lean_closure_set(v___f_2438_, 6, v___y_2424_);
lean_closure_set(v___f_2438_, 7, v___y_2426_);
lean_closure_set(v___f_2438_, 8, v___y_2428_);
v___x_2439_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___redArg(v___y_2430_, v___f_2438_, v___y_2432_, v___y_2433_, v___y_2434_, v___y_2435_);
return v___x_2439_;
}
}
else
{
lean_object* v_a_2572_; lean_object* v___x_2574_; uint8_t v_isShared_2575_; uint8_t v_isSharedCheck_2579_; 
lean_dec(v_recursorName_2404_);
lean_dec_ref(v_givenNames_2403_);
lean_dec(v_majorFVarId_2402_);
lean_dec(v_mvarId_2401_);
lean_dec_ref(v_val_2400_);
lean_dec_ref(v_a_2399_);
v_a_2572_ = lean_ctor_get(v___x_2421_, 0);
v_isSharedCheck_2579_ = !lean_is_exclusive(v___x_2421_);
if (v_isSharedCheck_2579_ == 0)
{
v___x_2574_ = v___x_2421_;
v_isShared_2575_ = v_isSharedCheck_2579_;
goto v_resetjp_2573_;
}
else
{
lean_inc(v_a_2572_);
lean_dec(v___x_2421_);
v___x_2574_ = lean_box(0);
v_isShared_2575_ = v_isSharedCheck_2579_;
goto v_resetjp_2573_;
}
v_resetjp_2573_:
{
lean_object* v___x_2577_; 
if (v_isShared_2575_ == 0)
{
v___x_2577_ = v___x_2574_;
goto v_reusejp_2576_;
}
else
{
lean_object* v_reuseFailAlloc_2578_; 
v_reuseFailAlloc_2578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2578_, 0, v_a_2572_);
v___x_2577_ = v_reuseFailAlloc_2578_;
goto v_reusejp_2576_;
}
v_reusejp_2576_:
{
return v___x_2577_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___boxed(lean_object* v_a_2580_, lean_object* v_val_2581_, lean_object* v_mvarId_2582_, lean_object* v_majorFVarId_2583_, lean_object* v_givenNames_2584_, lean_object* v_recursorName_2585_, lean_object* v_x_2586_, lean_object* v_x_2587_, lean_object* v_x_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_){
_start:
{
lean_object* v_res_2594_; 
v_res_2594_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4(v_a_2580_, v_val_2581_, v_mvarId_2582_, v_majorFVarId_2583_, v_givenNames_2584_, v_recursorName_2585_, v_x_2586_, v_x_2587_, v_x_2588_, v___y_2589_, v___y_2590_, v___y_2591_, v___y_2592_);
lean_dec(v___y_2592_);
lean_dec_ref(v___y_2591_);
lean_dec(v___y_2590_);
lean_dec_ref(v___y_2589_);
return v_res_2594_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4(lean_object* v_val_2595_, lean_object* v_mvarId_2596_, lean_object* v_a_2597_, lean_object* v_majorFVarId_2598_, lean_object* v_givenNames_2599_, lean_object* v_recursorName_2600_, lean_object* v_x_2601_, lean_object* v_x_2602_, lean_object* v_x_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_){
_start:
{
if (lean_obj_tag(v_x_2601_) == 5)
{
lean_object* v_fn_2609_; lean_object* v_arg_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; 
v_fn_2609_ = lean_ctor_get(v_x_2601_, 0);
lean_inc_ref(v_fn_2609_);
v_arg_2610_ = lean_ctor_get(v_x_2601_, 1);
lean_inc_ref(v_arg_2610_);
lean_dec_ref(v_x_2601_);
v___x_2611_ = lean_array_set(v_x_2602_, v_x_2603_, v_arg_2610_);
v___x_2612_ = lean_unsigned_to_nat(1u);
v___x_2613_ = lean_nat_sub(v_x_2603_, v___x_2612_);
v___x_2614_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4(v_a_2597_, v_val_2595_, v_mvarId_2596_, v_majorFVarId_2598_, v_givenNames_2599_, v_recursorName_2600_, v_fn_2609_, v___x_2611_, v___x_2613_, v___y_2604_, v___y_2605_, v___y_2606_, v___y_2607_);
return v___x_2614_;
}
else
{
uint8_t v_depElim_2615_; lean_object* v_paramsPos_2616_; lean_object* v___x_2617_; 
lean_dec_ref(v_x_2601_);
v_depElim_2615_ = lean_ctor_get_uint8(v_a_2597_, sizeof(void*)*8);
v_paramsPos_2616_ = lean_ctor_get(v_a_2597_, 5);
lean_inc(v_paramsPos_2616_);
lean_inc(v_mvarId_2596_);
lean_inc_ref(v_val_2595_);
v___x_2617_ = l_List_forM___at___00Lean_MVarId_induction_spec__0(v_x_2602_, v_val_2595_, v_mvarId_2596_, v_paramsPos_2616_, v___y_2604_, v___y_2605_, v___y_2606_, v___y_2607_);
lean_dec_ref(v_x_2602_);
if (lean_obj_tag(v___x_2617_) == 0)
{
lean_object* v___x_2618_; lean_object* v___y_2620_; lean_object* v___y_2621_; lean_object* v___y_2622_; lean_object* v___y_2623_; lean_object* v___y_2624_; lean_object* v___y_2625_; size_t v___y_2626_; lean_object* v___y_2627_; lean_object* v___y_2628_; lean_object* v___y_2629_; lean_object* v___y_2630_; lean_object* v___y_2631_; lean_object* v___x_2636_; 
lean_dec_ref(v___x_2617_);
v___x_2618_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1));
lean_inc_ref(v_a_2597_);
lean_inc(v_mvarId_2596_);
v___x_2636_ = l_Lean_Meta_getMajorTypeIndices(v_mvarId_2596_, v___x_2618_, v_a_2597_, v_val_2595_, v___y_2604_, v___y_2605_, v___y_2606_, v___y_2607_);
if (lean_obj_tag(v___x_2636_) == 0)
{
lean_object* v_a_2637_; lean_object* v___x_2638_; 
v_a_2637_ = lean_ctor_get(v___x_2636_, 0);
lean_inc(v_a_2637_);
lean_dec_ref(v___x_2636_);
lean_inc(v_mvarId_2596_);
v___x_2638_ = l_Lean_MVarId_getType(v_mvarId_2596_, v___y_2604_, v___y_2605_, v___y_2606_, v___y_2607_);
if (lean_obj_tag(v___x_2638_) == 0)
{
lean_object* v_a_2639_; lean_object* v_cls_2640_; lean_object* v___y_2642_; lean_object* v___y_2643_; lean_object* v___y_2644_; lean_object* v___y_2645_; 
v_a_2639_ = lean_ctor_get(v___x_2638_, 0);
lean_inc(v_a_2639_);
lean_dec_ref(v___x_2638_);
v_cls_2640_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__2));
if (v_depElim_2615_ == 0)
{
lean_object* v___x_2728_; lean_object* v_a_2729_; lean_object* v___x_2731_; uint8_t v_isShared_2732_; uint8_t v_isSharedCheck_2751_; 
lean_inc(v_majorFVarId_2598_);
v___x_2728_ = l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2___redArg(v_a_2639_, v_majorFVarId_2598_, v___y_2605_);
v_a_2729_ = lean_ctor_get(v___x_2728_, 0);
v_isSharedCheck_2751_ = !lean_is_exclusive(v___x_2728_);
if (v_isSharedCheck_2751_ == 0)
{
v___x_2731_ = v___x_2728_;
v_isShared_2732_ = v_isSharedCheck_2751_;
goto v_resetjp_2730_;
}
else
{
lean_inc(v_a_2729_);
lean_dec(v___x_2728_);
v___x_2731_ = lean_box(0);
v_isShared_2732_ = v_isSharedCheck_2751_;
goto v_resetjp_2730_;
}
v_resetjp_2730_:
{
uint8_t v___x_2733_; 
v___x_2733_ = lean_unbox(v_a_2729_);
lean_dec(v_a_2729_);
if (v___x_2733_ == 0)
{
lean_del_object(v___x_2731_);
lean_dec(v_recursorName_2600_);
v___y_2642_ = v___y_2604_;
v___y_2643_ = v___y_2605_;
v___y_2644_ = v___y_2606_;
v___y_2645_ = v___y_2607_;
goto v___jp_2641_;
}
else
{
lean_object* v___x_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; lean_object* v___x_2740_; 
v___x_2734_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__3, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__3);
v___x_2735_ = l_Lean_MessageData_ofName(v_recursorName_2600_);
v___x_2736_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2736_, 0, v___x_2734_);
lean_ctor_set(v___x_2736_, 1, v___x_2735_);
v___x_2737_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__5, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__5_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__5);
v___x_2738_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2738_, 0, v___x_2736_);
lean_ctor_set(v___x_2738_, 1, v___x_2737_);
if (v_isShared_2732_ == 0)
{
lean_ctor_set_tag(v___x_2731_, 1);
lean_ctor_set(v___x_2731_, 0, v___x_2738_);
v___x_2740_ = v___x_2731_;
goto v_reusejp_2739_;
}
else
{
lean_object* v_reuseFailAlloc_2750_; 
v_reuseFailAlloc_2750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2750_, 0, v___x_2738_);
v___x_2740_ = v_reuseFailAlloc_2750_;
goto v_reusejp_2739_;
}
v_reusejp_2739_:
{
lean_object* v___x_2741_; 
lean_inc(v_mvarId_2596_);
v___x_2741_ = l_Lean_Meta_throwTacticEx___redArg(v___x_2618_, v_mvarId_2596_, v___x_2740_, v___y_2604_, v___y_2605_, v___y_2606_, v___y_2607_);
if (lean_obj_tag(v___x_2741_) == 0)
{
lean_dec_ref(v___x_2741_);
v___y_2642_ = v___y_2604_;
v___y_2643_ = v___y_2605_;
v___y_2644_ = v___y_2606_;
v___y_2645_ = v___y_2607_;
goto v___jp_2641_;
}
else
{
lean_object* v_a_2742_; lean_object* v___x_2744_; uint8_t v_isShared_2745_; uint8_t v_isSharedCheck_2749_; 
lean_dec(v_a_2637_);
lean_dec_ref(v_givenNames_2599_);
lean_dec(v_majorFVarId_2598_);
lean_dec_ref(v_a_2597_);
lean_dec(v_mvarId_2596_);
v_a_2742_ = lean_ctor_get(v___x_2741_, 0);
v_isSharedCheck_2749_ = !lean_is_exclusive(v___x_2741_);
if (v_isSharedCheck_2749_ == 0)
{
v___x_2744_ = v___x_2741_;
v_isShared_2745_ = v_isSharedCheck_2749_;
goto v_resetjp_2743_;
}
else
{
lean_inc(v_a_2742_);
lean_dec(v___x_2741_);
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
}
}
}
}
else
{
lean_dec(v_a_2639_);
lean_dec(v_recursorName_2600_);
v___y_2642_ = v___y_2604_;
v___y_2643_ = v___y_2605_;
v___y_2644_ = v___y_2606_;
v___y_2645_ = v___y_2607_;
goto v___jp_2641_;
}
v___jp_2641_:
{
size_t v_sz_2646_; size_t v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; uint8_t v___x_2650_; uint8_t v___x_2651_; lean_object* v___x_2652_; 
v_sz_2646_ = lean_array_size(v_a_2637_);
v___x_2647_ = ((size_t)0ULL);
lean_inc(v_a_2637_);
v___x_2648_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_induction_spec__1(v_sz_2646_, v___x_2647_, v_a_2637_);
lean_inc(v_majorFVarId_2598_);
v___x_2649_ = lean_array_push(v___x_2648_, v_majorFVarId_2598_);
v___x_2650_ = 1;
v___x_2651_ = 0;
v___x_2652_ = l_Lean_MVarId_revert(v_mvarId_2596_, v___x_2649_, v___x_2650_, v___x_2651_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_);
if (lean_obj_tag(v___x_2652_) == 0)
{
lean_object* v_a_2653_; lean_object* v_fst_2654_; lean_object* v_snd_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; 
v_a_2653_ = lean_ctor_get(v___x_2652_, 0);
lean_inc(v_a_2653_);
lean_dec_ref(v___x_2652_);
v_fst_2654_ = lean_ctor_get(v_a_2653_, 0);
lean_inc(v_fst_2654_);
v_snd_2655_ = lean_ctor_get(v_a_2653_, 1);
lean_inc(v_snd_2655_);
lean_dec(v_a_2653_);
v___x_2656_ = lean_array_get_size(v_a_2637_);
v___x_2657_ = lean_box(0);
v___x_2658_ = l_Lean_Meta_introNCore(v_snd_2655_, v___x_2656_, v___x_2657_, v___x_2651_, v___x_2650_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_);
if (lean_obj_tag(v___x_2658_) == 0)
{
lean_object* v_a_2659_; lean_object* v_fst_2660_; lean_object* v_snd_2661_; lean_object* v___x_2662_; 
v_a_2659_ = lean_ctor_get(v___x_2658_, 0);
lean_inc(v_a_2659_);
lean_dec_ref(v___x_2658_);
v_fst_2660_ = lean_ctor_get(v_a_2659_, 0);
lean_inc(v_fst_2660_);
v_snd_2661_ = lean_ctor_get(v_a_2659_, 1);
lean_inc(v_snd_2661_);
lean_dec(v_a_2659_);
v___x_2662_ = l_Lean_Meta_intro1Core(v_snd_2661_, v___x_2650_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_);
if (lean_obj_tag(v___x_2662_) == 0)
{
lean_object* v_a_2663_; lean_object* v_fst_2664_; lean_object* v_snd_2665_; lean_object* v___x_2667_; uint8_t v_isShared_2668_; uint8_t v_isSharedCheck_2703_; 
v_a_2663_ = lean_ctor_get(v___x_2662_, 0);
lean_inc(v_a_2663_);
lean_dec_ref(v___x_2662_);
v_fst_2664_ = lean_ctor_get(v_a_2663_, 0);
v_snd_2665_ = lean_ctor_get(v_a_2663_, 1);
v_isSharedCheck_2703_ = !lean_is_exclusive(v_a_2663_);
if (v_isSharedCheck_2703_ == 0)
{
v___x_2667_ = v_a_2663_;
v_isShared_2668_ = v_isSharedCheck_2703_;
goto v_resetjp_2666_;
}
else
{
lean_inc(v_snd_2665_);
lean_inc(v_fst_2664_);
lean_dec(v_a_2663_);
v___x_2667_ = lean_box(0);
v_isShared_2668_ = v_isSharedCheck_2703_;
goto v_resetjp_2666_;
}
v_resetjp_2666_:
{
lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2674_; 
v___x_2669_ = lean_box(0);
lean_inc(v_fst_2664_);
v___x_2670_ = l_Lean_mkFVar(v_fst_2664_);
lean_inc_ref(v___x_2670_);
v___x_2671_ = l_Lean_Meta_FVarSubst_insert(v___x_2669_, v_majorFVarId_2598_, v___x_2670_);
v___x_2672_ = lean_unsigned_to_nat(0u);
if (v_isShared_2668_ == 0)
{
lean_ctor_set(v___x_2667_, 1, v___x_2672_);
lean_ctor_set(v___x_2667_, 0, v___x_2671_);
v___x_2674_ = v___x_2667_;
goto v_reusejp_2673_;
}
else
{
lean_object* v_reuseFailAlloc_2702_; 
v_reuseFailAlloc_2702_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2702_, 0, v___x_2671_);
lean_ctor_set(v_reuseFailAlloc_2702_, 1, v___x_2672_);
v___x_2674_ = v_reuseFailAlloc_2702_;
goto v_reusejp_2673_;
}
v_reusejp_2673_:
{
lean_object* v___x_2675_; lean_object* v_options_2676_; uint8_t v_hasTrace_2677_; 
v___x_2675_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_induction_spec__2(v_fst_2660_, v_a_2637_, v_sz_2646_, v___x_2647_, v___x_2674_);
lean_dec(v_a_2637_);
v_options_2676_ = lean_ctor_get(v___y_2644_, 2);
v_hasTrace_2677_ = lean_ctor_get_uint8(v_options_2676_, sizeof(void*)*1);
if (v_hasTrace_2677_ == 0)
{
lean_object* v_fst_2678_; 
v_fst_2678_ = lean_ctor_get(v___x_2675_, 0);
lean_inc(v_fst_2678_);
lean_dec_ref(v___x_2675_);
lean_inc(v_snd_2665_);
v___y_2620_ = v___x_2670_;
v___y_2621_ = v_fst_2664_;
v___y_2622_ = v_fst_2678_;
v___y_2623_ = v_fst_2654_;
v___y_2624_ = v_snd_2665_;
v___y_2625_ = v_fst_2660_;
v___y_2626_ = v___x_2647_;
v___y_2627_ = v_snd_2665_;
v___y_2628_ = v___y_2642_;
v___y_2629_ = v___y_2643_;
v___y_2630_ = v___y_2644_;
v___y_2631_ = v___y_2645_;
goto v___jp_2619_;
}
else
{
lean_object* v_fst_2679_; lean_object* v___x_2681_; uint8_t v_isShared_2682_; uint8_t v_isSharedCheck_2700_; 
v_fst_2679_ = lean_ctor_get(v___x_2675_, 0);
v_isSharedCheck_2700_ = !lean_is_exclusive(v___x_2675_);
if (v_isSharedCheck_2700_ == 0)
{
lean_object* v_unused_2701_; 
v_unused_2701_ = lean_ctor_get(v___x_2675_, 1);
lean_dec(v_unused_2701_);
v___x_2681_ = v___x_2675_;
v_isShared_2682_ = v_isSharedCheck_2700_;
goto v_resetjp_2680_;
}
else
{
lean_inc(v_fst_2679_);
lean_dec(v___x_2675_);
v___x_2681_ = lean_box(0);
v_isShared_2682_ = v_isSharedCheck_2700_;
goto v_resetjp_2680_;
}
v_resetjp_2680_:
{
lean_object* v_inheritedTraceOptions_2683_; lean_object* v___x_2684_; uint8_t v___x_2685_; 
v_inheritedTraceOptions_2683_ = lean_ctor_get(v___y_2644_, 13);
v___x_2684_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5);
v___x_2685_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2683_, v_options_2676_, v___x_2684_);
if (v___x_2685_ == 0)
{
lean_del_object(v___x_2681_);
lean_inc(v_snd_2665_);
v___y_2620_ = v___x_2670_;
v___y_2621_ = v_fst_2664_;
v___y_2622_ = v_fst_2679_;
v___y_2623_ = v_fst_2654_;
v___y_2624_ = v_snd_2665_;
v___y_2625_ = v_fst_2660_;
v___y_2626_ = v___x_2647_;
v___y_2627_ = v_snd_2665_;
v___y_2628_ = v___y_2642_;
v___y_2629_ = v___y_2643_;
v___y_2630_ = v___y_2644_;
v___y_2631_ = v___y_2645_;
goto v___jp_2619_;
}
else
{
lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2689_; 
v___x_2686_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__1);
lean_inc(v_snd_2665_);
v___x_2687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2687_, 0, v_snd_2665_);
if (v_isShared_2682_ == 0)
{
lean_ctor_set_tag(v___x_2681_, 7);
lean_ctor_set(v___x_2681_, 1, v___x_2687_);
lean_ctor_set(v___x_2681_, 0, v___x_2686_);
v___x_2689_ = v___x_2681_;
goto v_reusejp_2688_;
}
else
{
lean_object* v_reuseFailAlloc_2699_; 
v_reuseFailAlloc_2699_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2699_, 0, v___x_2686_);
lean_ctor_set(v_reuseFailAlloc_2699_, 1, v___x_2687_);
v___x_2689_ = v_reuseFailAlloc_2699_;
goto v_reusejp_2688_;
}
v_reusejp_2688_:
{
lean_object* v___x_2690_; 
v___x_2690_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1(v_cls_2640_, v___x_2689_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_);
if (lean_obj_tag(v___x_2690_) == 0)
{
lean_dec_ref(v___x_2690_);
lean_inc(v_snd_2665_);
v___y_2620_ = v___x_2670_;
v___y_2621_ = v_fst_2664_;
v___y_2622_ = v_fst_2679_;
v___y_2623_ = v_fst_2654_;
v___y_2624_ = v_snd_2665_;
v___y_2625_ = v_fst_2660_;
v___y_2626_ = v___x_2647_;
v___y_2627_ = v_snd_2665_;
v___y_2628_ = v___y_2642_;
v___y_2629_ = v___y_2643_;
v___y_2630_ = v___y_2644_;
v___y_2631_ = v___y_2645_;
goto v___jp_2619_;
}
else
{
lean_object* v_a_2691_; lean_object* v___x_2693_; uint8_t v_isShared_2694_; uint8_t v_isSharedCheck_2698_; 
lean_dec(v_fst_2679_);
lean_dec_ref(v___x_2670_);
lean_dec(v_snd_2665_);
lean_dec(v_fst_2664_);
lean_dec(v_fst_2660_);
lean_dec(v_fst_2654_);
lean_dec_ref(v_givenNames_2599_);
lean_dec_ref(v_a_2597_);
v_a_2691_ = lean_ctor_get(v___x_2690_, 0);
v_isSharedCheck_2698_ = !lean_is_exclusive(v___x_2690_);
if (v_isSharedCheck_2698_ == 0)
{
v___x_2693_ = v___x_2690_;
v_isShared_2694_ = v_isSharedCheck_2698_;
goto v_resetjp_2692_;
}
else
{
lean_inc(v_a_2691_);
lean_dec(v___x_2690_);
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
}
}
}
}
}
else
{
lean_object* v_a_2704_; lean_object* v___x_2706_; uint8_t v_isShared_2707_; uint8_t v_isSharedCheck_2711_; 
lean_dec(v_fst_2660_);
lean_dec(v_fst_2654_);
lean_dec(v_a_2637_);
lean_dec_ref(v_givenNames_2599_);
lean_dec(v_majorFVarId_2598_);
lean_dec_ref(v_a_2597_);
v_a_2704_ = lean_ctor_get(v___x_2662_, 0);
v_isSharedCheck_2711_ = !lean_is_exclusive(v___x_2662_);
if (v_isSharedCheck_2711_ == 0)
{
v___x_2706_ = v___x_2662_;
v_isShared_2707_ = v_isSharedCheck_2711_;
goto v_resetjp_2705_;
}
else
{
lean_inc(v_a_2704_);
lean_dec(v___x_2662_);
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
lean_dec(v_fst_2654_);
lean_dec(v_a_2637_);
lean_dec_ref(v_givenNames_2599_);
lean_dec(v_majorFVarId_2598_);
lean_dec_ref(v_a_2597_);
v_a_2712_ = lean_ctor_get(v___x_2658_, 0);
v_isSharedCheck_2719_ = !lean_is_exclusive(v___x_2658_);
if (v_isSharedCheck_2719_ == 0)
{
v___x_2714_ = v___x_2658_;
v_isShared_2715_ = v_isSharedCheck_2719_;
goto v_resetjp_2713_;
}
else
{
lean_inc(v_a_2712_);
lean_dec(v___x_2658_);
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
else
{
lean_object* v_a_2720_; lean_object* v___x_2722_; uint8_t v_isShared_2723_; uint8_t v_isSharedCheck_2727_; 
lean_dec(v_a_2637_);
lean_dec_ref(v_givenNames_2599_);
lean_dec(v_majorFVarId_2598_);
lean_dec_ref(v_a_2597_);
v_a_2720_ = lean_ctor_get(v___x_2652_, 0);
v_isSharedCheck_2727_ = !lean_is_exclusive(v___x_2652_);
if (v_isSharedCheck_2727_ == 0)
{
v___x_2722_ = v___x_2652_;
v_isShared_2723_ = v_isSharedCheck_2727_;
goto v_resetjp_2721_;
}
else
{
lean_inc(v_a_2720_);
lean_dec(v___x_2652_);
v___x_2722_ = lean_box(0);
v_isShared_2723_ = v_isSharedCheck_2727_;
goto v_resetjp_2721_;
}
v_resetjp_2721_:
{
lean_object* v___x_2725_; 
if (v_isShared_2723_ == 0)
{
v___x_2725_ = v___x_2722_;
goto v_reusejp_2724_;
}
else
{
lean_object* v_reuseFailAlloc_2726_; 
v_reuseFailAlloc_2726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2726_, 0, v_a_2720_);
v___x_2725_ = v_reuseFailAlloc_2726_;
goto v_reusejp_2724_;
}
v_reusejp_2724_:
{
return v___x_2725_;
}
}
}
}
}
else
{
lean_object* v_a_2752_; lean_object* v___x_2754_; uint8_t v_isShared_2755_; uint8_t v_isSharedCheck_2759_; 
lean_dec(v_a_2637_);
lean_dec(v_recursorName_2600_);
lean_dec_ref(v_givenNames_2599_);
lean_dec(v_majorFVarId_2598_);
lean_dec_ref(v_a_2597_);
lean_dec(v_mvarId_2596_);
v_a_2752_ = lean_ctor_get(v___x_2638_, 0);
v_isSharedCheck_2759_ = !lean_is_exclusive(v___x_2638_);
if (v_isSharedCheck_2759_ == 0)
{
v___x_2754_ = v___x_2638_;
v_isShared_2755_ = v_isSharedCheck_2759_;
goto v_resetjp_2753_;
}
else
{
lean_inc(v_a_2752_);
lean_dec(v___x_2638_);
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
}
else
{
lean_object* v_a_2760_; lean_object* v___x_2762_; uint8_t v_isShared_2763_; uint8_t v_isSharedCheck_2767_; 
lean_dec(v_recursorName_2600_);
lean_dec_ref(v_givenNames_2599_);
lean_dec(v_majorFVarId_2598_);
lean_dec_ref(v_a_2597_);
lean_dec(v_mvarId_2596_);
v_a_2760_ = lean_ctor_get(v___x_2636_, 0);
v_isSharedCheck_2767_ = !lean_is_exclusive(v___x_2636_);
if (v_isSharedCheck_2767_ == 0)
{
v___x_2762_ = v___x_2636_;
v_isShared_2763_ = v_isSharedCheck_2767_;
goto v_resetjp_2761_;
}
else
{
lean_inc(v_a_2760_);
lean_dec(v___x_2636_);
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
v___jp_2619_:
{
size_t v_sz_2632_; lean_object* v___x_2633_; lean_object* v___f_2634_; lean_object* v___x_2635_; 
v_sz_2632_ = lean_array_size(v___y_2625_);
v___x_2633_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__3(v_sz_2632_, v___y_2626_, v___y_2625_);
v___f_2634_ = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4___lam__0___boxed), 14, 9);
lean_closure_set(v___f_2634_, 0, v___y_2624_);
lean_closure_set(v___f_2634_, 1, v___x_2618_);
lean_closure_set(v___f_2634_, 2, v___y_2621_);
lean_closure_set(v___f_2634_, 3, v_a_2597_);
lean_closure_set(v___f_2634_, 4, v___x_2633_);
lean_closure_set(v___f_2634_, 5, v_givenNames_2599_);
lean_closure_set(v___f_2634_, 6, v___y_2623_);
lean_closure_set(v___f_2634_, 7, v___y_2620_);
lean_closure_set(v___f_2634_, 8, v___y_2622_);
v___x_2635_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___redArg(v___y_2627_, v___f_2634_, v___y_2628_, v___y_2629_, v___y_2630_, v___y_2631_);
return v___x_2635_;
}
}
else
{
lean_object* v_a_2768_; lean_object* v___x_2770_; uint8_t v_isShared_2771_; uint8_t v_isSharedCheck_2775_; 
lean_dec(v_recursorName_2600_);
lean_dec_ref(v_givenNames_2599_);
lean_dec(v_majorFVarId_2598_);
lean_dec_ref(v_a_2597_);
lean_dec(v_mvarId_2596_);
lean_dec_ref(v_val_2595_);
v_a_2768_ = lean_ctor_get(v___x_2617_, 0);
v_isSharedCheck_2775_ = !lean_is_exclusive(v___x_2617_);
if (v_isSharedCheck_2775_ == 0)
{
v___x_2770_ = v___x_2617_;
v_isShared_2771_ = v_isSharedCheck_2775_;
goto v_resetjp_2769_;
}
else
{
lean_inc(v_a_2768_);
lean_dec(v___x_2617_);
v___x_2770_ = lean_box(0);
v_isShared_2771_ = v_isSharedCheck_2775_;
goto v_resetjp_2769_;
}
v_resetjp_2769_:
{
lean_object* v___x_2773_; 
if (v_isShared_2771_ == 0)
{
v___x_2773_ = v___x_2770_;
goto v_reusejp_2772_;
}
else
{
lean_object* v_reuseFailAlloc_2774_; 
v_reuseFailAlloc_2774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2774_, 0, v_a_2768_);
v___x_2773_ = v_reuseFailAlloc_2774_;
goto v_reusejp_2772_;
}
v_reusejp_2772_:
{
return v___x_2773_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4___boxed(lean_object* v_val_2776_, lean_object* v_mvarId_2777_, lean_object* v_a_2778_, lean_object* v_majorFVarId_2779_, lean_object* v_givenNames_2780_, lean_object* v_recursorName_2781_, lean_object* v_x_2782_, lean_object* v_x_2783_, lean_object* v_x_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_, lean_object* v___y_2787_, lean_object* v___y_2788_, lean_object* v___y_2789_){
_start:
{
lean_object* v_res_2790_; 
v_res_2790_ = l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4(v_val_2776_, v_mvarId_2777_, v_a_2778_, v_majorFVarId_2779_, v_givenNames_2780_, v_recursorName_2781_, v_x_2782_, v_x_2783_, v_x_2784_, v___y_2785_, v___y_2786_, v___y_2787_, v___y_2788_);
lean_dec(v___y_2788_);
lean_dec_ref(v___y_2787_);
lean_dec(v___y_2786_);
lean_dec_ref(v___y_2785_);
lean_dec(v_x_2784_);
return v_res_2790_;
}
}
static lean_object* _init_l_Lean_MVarId_induction___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2792_; lean_object* v___x_2793_; 
v___x_2792_ = ((lean_object*)(l_Lean_MVarId_induction___lam__0___closed__0));
v___x_2793_ = l_Lean_stringToMessageData(v___x_2792_);
return v___x_2793_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_induction___lam__0(lean_object* v___x_2794_, lean_object* v_mvarId_2795_, lean_object* v_majorFVarId_2796_, lean_object* v_recursorName_2797_, lean_object* v_givenNames_2798_, lean_object* v_cls_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_, lean_object* v___y_2803_){
_start:
{
lean_object* v___y_2806_; lean_object* v___y_2807_; lean_object* v___y_2808_; lean_object* v___y_2809_; lean_object* v_options_2861_; uint8_t v_hasTrace_2862_; 
v_options_2861_ = lean_ctor_get(v___y_2802_, 2);
v_hasTrace_2862_ = lean_ctor_get_uint8(v_options_2861_, sizeof(void*)*1);
if (v_hasTrace_2862_ == 0)
{
lean_dec(v_cls_2799_);
v___y_2806_ = v___y_2800_;
v___y_2807_ = v___y_2801_;
v___y_2808_ = v___y_2802_;
v___y_2809_ = v___y_2803_;
goto v___jp_2805_;
}
else
{
lean_object* v_inheritedTraceOptions_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; uint8_t v___x_2866_; 
v_inheritedTraceOptions_2863_ = lean_ctor_get(v___y_2802_, 13);
v___x_2864_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__4));
lean_inc(v_cls_2799_);
v___x_2865_ = l_Lean_Name_append(v___x_2864_, v_cls_2799_);
v___x_2866_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2863_, v_options_2861_, v___x_2865_);
lean_dec(v___x_2865_);
if (v___x_2866_ == 0)
{
lean_dec(v_cls_2799_);
v___y_2806_ = v___y_2800_;
v___y_2807_ = v___y_2801_;
v___y_2808_ = v___y_2802_;
v___y_2809_ = v___y_2803_;
goto v___jp_2805_;
}
else
{
lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; 
v___x_2867_ = lean_obj_once(&l_Lean_MVarId_induction___lam__0___closed__1, &l_Lean_MVarId_induction___lam__0___closed__1_once, _init_l_Lean_MVarId_induction___lam__0___closed__1);
lean_inc(v_mvarId_2795_);
v___x_2868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2868_, 0, v_mvarId_2795_);
v___x_2869_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2869_, 0, v___x_2867_);
lean_ctor_set(v___x_2869_, 1, v___x_2868_);
v___x_2870_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1(v_cls_2799_, v___x_2869_, v___y_2800_, v___y_2801_, v___y_2802_, v___y_2803_);
if (lean_obj_tag(v___x_2870_) == 0)
{
lean_dec_ref(v___x_2870_);
v___y_2806_ = v___y_2800_;
v___y_2807_ = v___y_2801_;
v___y_2808_ = v___y_2802_;
v___y_2809_ = v___y_2803_;
goto v___jp_2805_;
}
else
{
lean_object* v_a_2871_; lean_object* v___x_2873_; uint8_t v_isShared_2874_; uint8_t v_isSharedCheck_2878_; 
lean_dec_ref(v_givenNames_2798_);
lean_dec(v_recursorName_2797_);
lean_dec(v_majorFVarId_2796_);
lean_dec(v_mvarId_2795_);
lean_dec_ref(v___x_2794_);
v_a_2871_ = lean_ctor_get(v___x_2870_, 0);
v_isSharedCheck_2878_ = !lean_is_exclusive(v___x_2870_);
if (v_isSharedCheck_2878_ == 0)
{
v___x_2873_ = v___x_2870_;
v_isShared_2874_ = v_isSharedCheck_2878_;
goto v_resetjp_2872_;
}
else
{
lean_inc(v_a_2871_);
lean_dec(v___x_2870_);
v___x_2873_ = lean_box(0);
v_isShared_2874_ = v_isSharedCheck_2878_;
goto v_resetjp_2872_;
}
v_resetjp_2872_:
{
lean_object* v___x_2876_; 
if (v_isShared_2874_ == 0)
{
v___x_2876_ = v___x_2873_;
goto v_reusejp_2875_;
}
else
{
lean_object* v_reuseFailAlloc_2877_; 
v_reuseFailAlloc_2877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2877_, 0, v_a_2871_);
v___x_2876_ = v_reuseFailAlloc_2877_;
goto v_reusejp_2875_;
}
v_reusejp_2875_:
{
return v___x_2876_;
}
}
}
}
}
v___jp_2805_:
{
lean_object* v___x_2810_; lean_object* v___x_2811_; 
v___x_2810_ = l_Lean_Name_mkStr1(v___x_2794_);
lean_inc(v___x_2810_);
lean_inc(v_mvarId_2795_);
v___x_2811_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_2795_, v___x_2810_, v___y_2806_, v___y_2807_, v___y_2808_, v___y_2809_);
if (lean_obj_tag(v___x_2811_) == 0)
{
lean_object* v___x_2812_; 
lean_dec_ref(v___x_2811_);
lean_inc(v_majorFVarId_2796_);
v___x_2812_ = l_Lean_FVarId_getDecl___redArg(v_majorFVarId_2796_, v___y_2806_, v___y_2808_, v___y_2809_);
if (lean_obj_tag(v___x_2812_) == 0)
{
lean_object* v_a_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; 
v_a_2813_ = lean_ctor_get(v___x_2812_, 0);
lean_inc(v_a_2813_);
lean_dec_ref(v___x_2812_);
v___x_2814_ = lean_box(0);
lean_inc(v_recursorName_2797_);
v___x_2815_ = l_Lean_Meta_mkRecursorInfo(v_recursorName_2797_, v___x_2814_, v___y_2806_, v___y_2807_, v___y_2808_, v___y_2809_);
if (lean_obj_tag(v___x_2815_) == 0)
{
lean_object* v_a_2816_; lean_object* v_typeName_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; 
v_a_2816_ = lean_ctor_get(v___x_2815_, 0);
lean_inc(v_a_2816_);
lean_dec_ref(v___x_2815_);
v_typeName_2817_ = lean_ctor_get(v_a_2816_, 1);
v___x_2818_ = l_Lean_LocalDecl_type(v_a_2813_);
lean_dec(v_a_2813_);
lean_inc_ref(v___x_2818_);
v___x_2819_ = l_Lean_Meta_whnfUntil(v___x_2818_, v_typeName_2817_, v___y_2806_, v___y_2807_, v___y_2808_, v___y_2809_);
if (lean_obj_tag(v___x_2819_) == 0)
{
lean_object* v_a_2820_; 
v_a_2820_ = lean_ctor_get(v___x_2819_, 0);
lean_inc(v_a_2820_);
lean_dec_ref(v___x_2819_);
if (lean_obj_tag(v_a_2820_) == 1)
{
lean_object* v_val_2821_; lean_object* v_dummy_2822_; lean_object* v_nargs_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; 
lean_dec_ref(v___x_2818_);
lean_dec(v___x_2810_);
v_val_2821_ = lean_ctor_get(v_a_2820_, 0);
lean_inc_n(v_val_2821_, 2);
lean_dec_ref(v_a_2820_);
v_dummy_2822_ = lean_obj_once(&l_Lean_Meta_getMajorTypeIndices___closed__0, &l_Lean_Meta_getMajorTypeIndices___closed__0_once, _init_l_Lean_Meta_getMajorTypeIndices___closed__0);
v_nargs_2823_ = l_Lean_Expr_getAppNumArgs(v_val_2821_);
lean_inc(v_nargs_2823_);
v___x_2824_ = lean_mk_array(v_nargs_2823_, v_dummy_2822_);
v___x_2825_ = lean_unsigned_to_nat(1u);
v___x_2826_ = lean_nat_sub(v_nargs_2823_, v___x_2825_);
lean_dec(v_nargs_2823_);
v___x_2827_ = l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4(v_val_2821_, v_mvarId_2795_, v_a_2816_, v_majorFVarId_2796_, v_givenNames_2798_, v_recursorName_2797_, v_val_2821_, v___x_2824_, v___x_2826_, v___y_2806_, v___y_2807_, v___y_2808_, v___y_2809_);
lean_dec(v___x_2826_);
return v___x_2827_;
}
else
{
lean_object* v___x_2828_; 
lean_dec(v_a_2820_);
lean_dec(v_a_2816_);
lean_dec_ref(v_givenNames_2798_);
lean_dec(v_recursorName_2797_);
lean_dec(v_majorFVarId_2796_);
v___x_2828_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg(v___x_2810_, v_mvarId_2795_, v___x_2818_, v___y_2806_, v___y_2807_, v___y_2808_, v___y_2809_);
return v___x_2828_;
}
}
else
{
lean_object* v_a_2829_; lean_object* v___x_2831_; uint8_t v_isShared_2832_; uint8_t v_isSharedCheck_2836_; 
lean_dec_ref(v___x_2818_);
lean_dec(v_a_2816_);
lean_dec(v___x_2810_);
lean_dec_ref(v_givenNames_2798_);
lean_dec(v_recursorName_2797_);
lean_dec(v_majorFVarId_2796_);
lean_dec(v_mvarId_2795_);
v_a_2829_ = lean_ctor_get(v___x_2819_, 0);
v_isSharedCheck_2836_ = !lean_is_exclusive(v___x_2819_);
if (v_isSharedCheck_2836_ == 0)
{
v___x_2831_ = v___x_2819_;
v_isShared_2832_ = v_isSharedCheck_2836_;
goto v_resetjp_2830_;
}
else
{
lean_inc(v_a_2829_);
lean_dec(v___x_2819_);
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
lean_dec(v_a_2813_);
lean_dec(v___x_2810_);
lean_dec_ref(v_givenNames_2798_);
lean_dec(v_recursorName_2797_);
lean_dec(v_majorFVarId_2796_);
lean_dec(v_mvarId_2795_);
v_a_2837_ = lean_ctor_get(v___x_2815_, 0);
v_isSharedCheck_2844_ = !lean_is_exclusive(v___x_2815_);
if (v_isSharedCheck_2844_ == 0)
{
v___x_2839_ = v___x_2815_;
v_isShared_2840_ = v_isSharedCheck_2844_;
goto v_resetjp_2838_;
}
else
{
lean_inc(v_a_2837_);
lean_dec(v___x_2815_);
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
lean_dec(v___x_2810_);
lean_dec_ref(v_givenNames_2798_);
lean_dec(v_recursorName_2797_);
lean_dec(v_majorFVarId_2796_);
lean_dec(v_mvarId_2795_);
v_a_2845_ = lean_ctor_get(v___x_2812_, 0);
v_isSharedCheck_2852_ = !lean_is_exclusive(v___x_2812_);
if (v_isSharedCheck_2852_ == 0)
{
v___x_2847_ = v___x_2812_;
v_isShared_2848_ = v_isSharedCheck_2852_;
goto v_resetjp_2846_;
}
else
{
lean_inc(v_a_2845_);
lean_dec(v___x_2812_);
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
else
{
lean_object* v_a_2853_; lean_object* v___x_2855_; uint8_t v_isShared_2856_; uint8_t v_isSharedCheck_2860_; 
lean_dec(v___x_2810_);
lean_dec_ref(v_givenNames_2798_);
lean_dec(v_recursorName_2797_);
lean_dec(v_majorFVarId_2796_);
lean_dec(v_mvarId_2795_);
v_a_2853_ = lean_ctor_get(v___x_2811_, 0);
v_isSharedCheck_2860_ = !lean_is_exclusive(v___x_2811_);
if (v_isSharedCheck_2860_ == 0)
{
v___x_2855_ = v___x_2811_;
v_isShared_2856_ = v_isSharedCheck_2860_;
goto v_resetjp_2854_;
}
else
{
lean_inc(v_a_2853_);
lean_dec(v___x_2811_);
v___x_2855_ = lean_box(0);
v_isShared_2856_ = v_isSharedCheck_2860_;
goto v_resetjp_2854_;
}
v_resetjp_2854_:
{
lean_object* v___x_2858_; 
if (v_isShared_2856_ == 0)
{
v___x_2858_ = v___x_2855_;
goto v_reusejp_2857_;
}
else
{
lean_object* v_reuseFailAlloc_2859_; 
v_reuseFailAlloc_2859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2859_, 0, v_a_2853_);
v___x_2858_ = v_reuseFailAlloc_2859_;
goto v_reusejp_2857_;
}
v_reusejp_2857_:
{
return v___x_2858_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_induction___lam__0___boxed(lean_object* v___x_2879_, lean_object* v_mvarId_2880_, lean_object* v_majorFVarId_2881_, lean_object* v_recursorName_2882_, lean_object* v_givenNames_2883_, lean_object* v_cls_2884_, lean_object* v___y_2885_, lean_object* v___y_2886_, lean_object* v___y_2887_, lean_object* v___y_2888_, lean_object* v___y_2889_){
_start:
{
lean_object* v_res_2890_; 
v_res_2890_ = l_Lean_MVarId_induction___lam__0(v___x_2879_, v_mvarId_2880_, v_majorFVarId_2881_, v_recursorName_2882_, v_givenNames_2883_, v_cls_2884_, v___y_2885_, v___y_2886_, v___y_2887_, v___y_2888_);
lean_dec(v___y_2888_);
lean_dec_ref(v___y_2887_);
lean_dec(v___y_2886_);
lean_dec_ref(v___y_2885_);
return v_res_2890_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_induction(lean_object* v_mvarId_2891_, lean_object* v_majorFVarId_2892_, lean_object* v_recursorName_2893_, lean_object* v_givenNames_2894_, lean_object* v_a_2895_, lean_object* v_a_2896_, lean_object* v_a_2897_, lean_object* v_a_2898_){
_start:
{
lean_object* v___x_2900_; lean_object* v_cls_2901_; lean_object* v___f_2902_; lean_object* v___x_2903_; 
v___x_2900_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__0));
v_cls_2901_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__2));
lean_inc(v_mvarId_2891_);
v___f_2902_ = lean_alloc_closure((void*)(l_Lean_MVarId_induction___lam__0___boxed), 11, 6);
lean_closure_set(v___f_2902_, 0, v___x_2900_);
lean_closure_set(v___f_2902_, 1, v_mvarId_2891_);
lean_closure_set(v___f_2902_, 2, v_majorFVarId_2892_);
lean_closure_set(v___f_2902_, 3, v_recursorName_2893_);
lean_closure_set(v___f_2902_, 4, v_givenNames_2894_);
lean_closure_set(v___f_2902_, 5, v_cls_2901_);
v___x_2903_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___redArg(v_mvarId_2891_, v___f_2902_, v_a_2895_, v_a_2896_, v_a_2897_, v_a_2898_);
return v___x_2903_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_induction___boxed(lean_object* v_mvarId_2904_, lean_object* v_majorFVarId_2905_, lean_object* v_recursorName_2906_, lean_object* v_givenNames_2907_, lean_object* v_a_2908_, lean_object* v_a_2909_, lean_object* v_a_2910_, lean_object* v_a_2911_, lean_object* v_a_2912_){
_start:
{
lean_object* v_res_2913_; 
v_res_2913_ = l_Lean_MVarId_induction(v_mvarId_2904_, v_majorFVarId_2905_, v_recursorName_2906_, v_givenNames_2907_, v_a_2908_, v_a_2909_, v_a_2910_, v_a_2911_);
lean_dec(v_a_2911_);
lean_dec_ref(v_a_2910_);
lean_dec(v_a_2909_);
lean_dec_ref(v_a_2908_);
return v_res_2913_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; 
v___x_2961_ = lean_unsigned_to_nat(2221195325u);
v___x_2962_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_));
v___x_2963_ = l_Lean_Name_num___override(v___x_2962_, v___x_2961_);
return v___x_2963_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; 
v___x_2965_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_));
v___x_2966_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_);
v___x_2967_ = l_Lean_Name_str___override(v___x_2966_, v___x_2965_);
return v___x_2967_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; 
v___x_2969_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_));
v___x_2970_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_);
v___x_2971_ = l_Lean_Name_str___override(v___x_2970_, v___x_2969_);
return v___x_2971_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; 
v___x_2972_ = lean_unsigned_to_nat(2u);
v___x_2973_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_);
v___x_2974_ = l_Lean_Name_num___override(v___x_2973_, v___x_2972_);
return v___x_2974_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2976_; uint8_t v___x_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; 
v___x_2976_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__2));
v___x_2977_ = 0;
v___x_2978_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_);
v___x_2979_ = l_Lean_registerTraceClass(v___x_2976_, v___x_2977_, v___x_2978_);
return v___x_2979_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2____boxed(lean_object* v_a_2980_){
_start:
{
lean_object* v_res_2981_; 
v_res_2981_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_();
return v_res_2981_;
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
l_Lean_Meta_instInhabitedInductionSubgoal_default = _init_l_Lean_Meta_instInhabitedInductionSubgoal_default();
lean_mark_persistent(l_Lean_Meta_instInhabitedInductionSubgoal_default);
l_Lean_Meta_instInhabitedInductionSubgoal = _init_l_Lean_Meta_instInhabitedInductionSubgoal();
lean_mark_persistent(l_Lean_Meta_instInhabitedInductionSubgoal);
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
