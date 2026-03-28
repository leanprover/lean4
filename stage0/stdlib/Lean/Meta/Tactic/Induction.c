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
lean_object* v___f_134_; lean_object* v___x_8857__overap_135_; lean_object* v___x_136_; 
v___f_134_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__4___closed__0));
v___x_8857__overap_135_ = lean_panic_fn_borrowed(v___f_134_, v_msg_128_);
lean_inc(v___y_132_);
lean_inc_ref(v___y_131_);
lean_inc(v___y_130_);
lean_inc_ref(v___y_129_);
v___x_136_ = lean_apply_5(v___x_8857__overap_135_, v___y_129_, v___y_130_, v___y_131_, v___y_132_, lean_box(0));
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
size_t v_x_10128__boxed_369_; size_t v_x_10129__boxed_370_; lean_object* v_res_371_; 
v_x_10128__boxed_369_ = lean_unbox_usize(v_x_365_);
lean_dec(v_x_365_);
v_x_10129__boxed_370_ = lean_unbox_usize(v_x_366_);
lean_dec(v_x_366_);
v_res_371_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2___redArg(v_x_364_, v_x_10128__boxed_369_, v_x_10129__boxed_370_, v_x_367_, v_x_368_);
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
lean_object* v___x_383_; lean_object* v_mctx_384_; lean_object* v_cache_385_; lean_object* v_zetaDeltaFVarIds_386_; lean_object* v_postponed_387_; lean_object* v_diag_388_; lean_object* v___x_390_; uint8_t v_isShared_391_; uint8_t v_isSharedCheck_415_; 
v___x_383_ = lean_st_ref_take(v___y_381_);
v_mctx_384_ = lean_ctor_get(v___x_383_, 0);
v_cache_385_ = lean_ctor_get(v___x_383_, 1);
v_zetaDeltaFVarIds_386_ = lean_ctor_get(v___x_383_, 2);
v_postponed_387_ = lean_ctor_get(v___x_383_, 3);
v_diag_388_ = lean_ctor_get(v___x_383_, 4);
v_isSharedCheck_415_ = !lean_is_exclusive(v___x_383_);
if (v_isSharedCheck_415_ == 0)
{
v___x_390_ = v___x_383_;
v_isShared_391_ = v_isSharedCheck_415_;
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
v_isShared_391_ = v_isSharedCheck_415_;
goto v_resetjp_389_;
}
v_resetjp_389_:
{
lean_object* v_depth_392_; lean_object* v_levelAssignDepth_393_; lean_object* v_mvarCounter_394_; lean_object* v_lDepth_395_; lean_object* v_decls_396_; lean_object* v_userNames_397_; lean_object* v_lAssignment_398_; lean_object* v_eAssignment_399_; lean_object* v_dAssignment_400_; lean_object* v___x_402_; uint8_t v_isShared_403_; uint8_t v_isSharedCheck_414_; 
v_depth_392_ = lean_ctor_get(v_mctx_384_, 0);
v_levelAssignDepth_393_ = lean_ctor_get(v_mctx_384_, 1);
v_mvarCounter_394_ = lean_ctor_get(v_mctx_384_, 2);
v_lDepth_395_ = lean_ctor_get(v_mctx_384_, 3);
v_decls_396_ = lean_ctor_get(v_mctx_384_, 4);
v_userNames_397_ = lean_ctor_get(v_mctx_384_, 5);
v_lAssignment_398_ = lean_ctor_get(v_mctx_384_, 6);
v_eAssignment_399_ = lean_ctor_get(v_mctx_384_, 7);
v_dAssignment_400_ = lean_ctor_get(v_mctx_384_, 8);
v_isSharedCheck_414_ = !lean_is_exclusive(v_mctx_384_);
if (v_isSharedCheck_414_ == 0)
{
v___x_402_ = v_mctx_384_;
v_isShared_403_ = v_isSharedCheck_414_;
goto v_resetjp_401_;
}
else
{
lean_inc(v_dAssignment_400_);
lean_inc(v_eAssignment_399_);
lean_inc(v_lAssignment_398_);
lean_inc(v_userNames_397_);
lean_inc(v_decls_396_);
lean_inc(v_lDepth_395_);
lean_inc(v_mvarCounter_394_);
lean_inc(v_levelAssignDepth_393_);
lean_inc(v_depth_392_);
lean_dec(v_mctx_384_);
v___x_402_ = lean_box(0);
v_isShared_403_ = v_isSharedCheck_414_;
goto v_resetjp_401_;
}
v_resetjp_401_:
{
lean_object* v___x_404_; lean_object* v___x_406_; 
v___x_404_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0___redArg(v_eAssignment_399_, v_mvarId_379_, v_val_380_);
if (v_isShared_403_ == 0)
{
lean_ctor_set(v___x_402_, 7, v___x_404_);
v___x_406_ = v___x_402_;
goto v_reusejp_405_;
}
else
{
lean_object* v_reuseFailAlloc_413_; 
v_reuseFailAlloc_413_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_413_, 0, v_depth_392_);
lean_ctor_set(v_reuseFailAlloc_413_, 1, v_levelAssignDepth_393_);
lean_ctor_set(v_reuseFailAlloc_413_, 2, v_mvarCounter_394_);
lean_ctor_set(v_reuseFailAlloc_413_, 3, v_lDepth_395_);
lean_ctor_set(v_reuseFailAlloc_413_, 4, v_decls_396_);
lean_ctor_set(v_reuseFailAlloc_413_, 5, v_userNames_397_);
lean_ctor_set(v_reuseFailAlloc_413_, 6, v_lAssignment_398_);
lean_ctor_set(v_reuseFailAlloc_413_, 7, v___x_404_);
lean_ctor_set(v_reuseFailAlloc_413_, 8, v_dAssignment_400_);
v___x_406_ = v_reuseFailAlloc_413_;
goto v_reusejp_405_;
}
v_reusejp_405_:
{
lean_object* v___x_408_; 
if (v_isShared_391_ == 0)
{
lean_ctor_set(v___x_390_, 0, v___x_406_);
v___x_408_ = v___x_390_;
goto v_reusejp_407_;
}
else
{
lean_object* v_reuseFailAlloc_412_; 
v_reuseFailAlloc_412_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_412_, 0, v___x_406_);
lean_ctor_set(v_reuseFailAlloc_412_, 1, v_cache_385_);
lean_ctor_set(v_reuseFailAlloc_412_, 2, v_zetaDeltaFVarIds_386_);
lean_ctor_set(v_reuseFailAlloc_412_, 3, v_postponed_387_);
lean_ctor_set(v_reuseFailAlloc_412_, 4, v_diag_388_);
v___x_408_ = v_reuseFailAlloc_412_;
goto v_reusejp_407_;
}
v_reusejp_407_:
{
lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; 
v___x_409_ = lean_st_ref_set(v___y_381_, v___x_408_);
v___x_410_ = lean_box(0);
v___x_411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_411_, 0, v___x_410_);
return v___x_411_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0___redArg___boxed(lean_object* v_mvarId_416_, lean_object* v_val_417_, lean_object* v___y_418_, lean_object* v___y_419_){
_start:
{
lean_object* v_res_420_; 
v_res_420_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0___redArg(v_mvarId_416_, v_val_417_, v___y_418_);
lean_dec(v___y_418_);
return v_res_420_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1_spec__2(lean_object* v_msgData_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_){
_start:
{
lean_object* v___x_427_; lean_object* v_env_428_; lean_object* v___x_429_; lean_object* v_mctx_430_; lean_object* v_lctx_431_; lean_object* v_options_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; 
v___x_427_ = lean_st_ref_get(v___y_425_);
v_env_428_ = lean_ctor_get(v___x_427_, 0);
lean_inc_ref(v_env_428_);
lean_dec(v___x_427_);
v___x_429_ = lean_st_ref_get(v___y_423_);
v_mctx_430_ = lean_ctor_get(v___x_429_, 0);
lean_inc_ref(v_mctx_430_);
lean_dec(v___x_429_);
v_lctx_431_ = lean_ctor_get(v___y_422_, 2);
v_options_432_ = lean_ctor_get(v___y_424_, 2);
lean_inc_ref(v_options_432_);
lean_inc_ref(v_lctx_431_);
v___x_433_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_433_, 0, v_env_428_);
lean_ctor_set(v___x_433_, 1, v_mctx_430_);
lean_ctor_set(v___x_433_, 2, v_lctx_431_);
lean_ctor_set(v___x_433_, 3, v_options_432_);
v___x_434_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_434_, 0, v___x_433_);
lean_ctor_set(v___x_434_, 1, v_msgData_421_);
v___x_435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_435_, 0, v___x_434_);
return v___x_435_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1_spec__2___boxed(lean_object* v_msgData_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_){
_start:
{
lean_object* v_res_442_; 
v_res_442_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1_spec__2(v_msgData_436_, v___y_437_, v___y_438_, v___y_439_, v___y_440_);
lean_dec(v___y_440_);
lean_dec_ref(v___y_439_);
lean_dec(v___y_438_);
lean_dec_ref(v___y_437_);
return v_res_442_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1___closed__0(void){
_start:
{
lean_object* v___x_443_; double v___x_444_; 
v___x_443_ = lean_unsigned_to_nat(0u);
v___x_444_ = lean_float_of_nat(v___x_443_);
return v___x_444_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1(lean_object* v_cls_448_, lean_object* v_msg_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_){
_start:
{
lean_object* v_ref_455_; lean_object* v___x_456_; lean_object* v_a_457_; lean_object* v___x_459_; uint8_t v_isShared_460_; uint8_t v_isSharedCheck_501_; 
v_ref_455_ = lean_ctor_get(v___y_452_, 5);
v___x_456_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1_spec__2(v_msg_449_, v___y_450_, v___y_451_, v___y_452_, v___y_453_);
v_a_457_ = lean_ctor_get(v___x_456_, 0);
v_isSharedCheck_501_ = !lean_is_exclusive(v___x_456_);
if (v_isSharedCheck_501_ == 0)
{
v___x_459_ = v___x_456_;
v_isShared_460_ = v_isSharedCheck_501_;
goto v_resetjp_458_;
}
else
{
lean_inc(v_a_457_);
lean_dec(v___x_456_);
v___x_459_ = lean_box(0);
v_isShared_460_ = v_isSharedCheck_501_;
goto v_resetjp_458_;
}
v_resetjp_458_:
{
lean_object* v___x_461_; lean_object* v_traceState_462_; lean_object* v_env_463_; lean_object* v_nextMacroScope_464_; lean_object* v_ngen_465_; lean_object* v_auxDeclNGen_466_; lean_object* v_cache_467_; lean_object* v_messages_468_; lean_object* v_infoState_469_; lean_object* v_snapshotTasks_470_; lean_object* v___x_472_; uint8_t v_isShared_473_; uint8_t v_isSharedCheck_500_; 
v___x_461_ = lean_st_ref_take(v___y_453_);
v_traceState_462_ = lean_ctor_get(v___x_461_, 4);
v_env_463_ = lean_ctor_get(v___x_461_, 0);
v_nextMacroScope_464_ = lean_ctor_get(v___x_461_, 1);
v_ngen_465_ = lean_ctor_get(v___x_461_, 2);
v_auxDeclNGen_466_ = lean_ctor_get(v___x_461_, 3);
v_cache_467_ = lean_ctor_get(v___x_461_, 5);
v_messages_468_ = lean_ctor_get(v___x_461_, 6);
v_infoState_469_ = lean_ctor_get(v___x_461_, 7);
v_snapshotTasks_470_ = lean_ctor_get(v___x_461_, 8);
v_isSharedCheck_500_ = !lean_is_exclusive(v___x_461_);
if (v_isSharedCheck_500_ == 0)
{
v___x_472_ = v___x_461_;
v_isShared_473_ = v_isSharedCheck_500_;
goto v_resetjp_471_;
}
else
{
lean_inc(v_snapshotTasks_470_);
lean_inc(v_infoState_469_);
lean_inc(v_messages_468_);
lean_inc(v_cache_467_);
lean_inc(v_traceState_462_);
lean_inc(v_auxDeclNGen_466_);
lean_inc(v_ngen_465_);
lean_inc(v_nextMacroScope_464_);
lean_inc(v_env_463_);
lean_dec(v___x_461_);
v___x_472_ = lean_box(0);
v_isShared_473_ = v_isSharedCheck_500_;
goto v_resetjp_471_;
}
v_resetjp_471_:
{
uint64_t v_tid_474_; lean_object* v_traces_475_; lean_object* v___x_477_; uint8_t v_isShared_478_; uint8_t v_isSharedCheck_499_; 
v_tid_474_ = lean_ctor_get_uint64(v_traceState_462_, sizeof(void*)*1);
v_traces_475_ = lean_ctor_get(v_traceState_462_, 0);
v_isSharedCheck_499_ = !lean_is_exclusive(v_traceState_462_);
if (v_isSharedCheck_499_ == 0)
{
v___x_477_ = v_traceState_462_;
v_isShared_478_ = v_isSharedCheck_499_;
goto v_resetjp_476_;
}
else
{
lean_inc(v_traces_475_);
lean_dec(v_traceState_462_);
v___x_477_ = lean_box(0);
v_isShared_478_ = v_isSharedCheck_499_;
goto v_resetjp_476_;
}
v_resetjp_476_:
{
lean_object* v___x_479_; double v___x_480_; uint8_t v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_489_; 
v___x_479_ = lean_box(0);
v___x_480_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1___closed__0);
v___x_481_ = 0;
v___x_482_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1___closed__1));
v___x_483_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_483_, 0, v_cls_448_);
lean_ctor_set(v___x_483_, 1, v___x_479_);
lean_ctor_set(v___x_483_, 2, v___x_482_);
lean_ctor_set_float(v___x_483_, sizeof(void*)*3, v___x_480_);
lean_ctor_set_float(v___x_483_, sizeof(void*)*3 + 8, v___x_480_);
lean_ctor_set_uint8(v___x_483_, sizeof(void*)*3 + 16, v___x_481_);
v___x_484_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1___closed__2));
v___x_485_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_485_, 0, v___x_483_);
lean_ctor_set(v___x_485_, 1, v_a_457_);
lean_ctor_set(v___x_485_, 2, v___x_484_);
lean_inc(v_ref_455_);
v___x_486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_486_, 0, v_ref_455_);
lean_ctor_set(v___x_486_, 1, v___x_485_);
v___x_487_ = l_Lean_PersistentArray_push___redArg(v_traces_475_, v___x_486_);
if (v_isShared_478_ == 0)
{
lean_ctor_set(v___x_477_, 0, v___x_487_);
v___x_489_ = v___x_477_;
goto v_reusejp_488_;
}
else
{
lean_object* v_reuseFailAlloc_498_; 
v_reuseFailAlloc_498_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_498_, 0, v___x_487_);
lean_ctor_set_uint64(v_reuseFailAlloc_498_, sizeof(void*)*1, v_tid_474_);
v___x_489_ = v_reuseFailAlloc_498_;
goto v_reusejp_488_;
}
v_reusejp_488_:
{
lean_object* v___x_491_; 
if (v_isShared_473_ == 0)
{
lean_ctor_set(v___x_472_, 4, v___x_489_);
v___x_491_ = v___x_472_;
goto v_reusejp_490_;
}
else
{
lean_object* v_reuseFailAlloc_497_; 
v_reuseFailAlloc_497_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_497_, 0, v_env_463_);
lean_ctor_set(v_reuseFailAlloc_497_, 1, v_nextMacroScope_464_);
lean_ctor_set(v_reuseFailAlloc_497_, 2, v_ngen_465_);
lean_ctor_set(v_reuseFailAlloc_497_, 3, v_auxDeclNGen_466_);
lean_ctor_set(v_reuseFailAlloc_497_, 4, v___x_489_);
lean_ctor_set(v_reuseFailAlloc_497_, 5, v_cache_467_);
lean_ctor_set(v_reuseFailAlloc_497_, 6, v_messages_468_);
lean_ctor_set(v_reuseFailAlloc_497_, 7, v_infoState_469_);
lean_ctor_set(v_reuseFailAlloc_497_, 8, v_snapshotTasks_470_);
v___x_491_ = v_reuseFailAlloc_497_;
goto v_reusejp_490_;
}
v_reusejp_490_:
{
lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_495_; 
v___x_492_ = lean_st_ref_set(v___y_453_, v___x_491_);
v___x_493_ = lean_box(0);
if (v_isShared_460_ == 0)
{
lean_ctor_set(v___x_459_, 0, v___x_493_);
v___x_495_ = v___x_459_;
goto v_reusejp_494_;
}
else
{
lean_object* v_reuseFailAlloc_496_; 
v_reuseFailAlloc_496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_496_, 0, v___x_493_);
v___x_495_ = v_reuseFailAlloc_496_;
goto v_reusejp_494_;
}
v_reusejp_494_:
{
return v___x_495_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1___boxed(lean_object* v_cls_502_, lean_object* v_msg_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_){
_start:
{
lean_object* v_res_509_; 
v_res_509_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1(v_cls_502_, v_msg_503_, v___y_504_, v___y_505_, v___y_506_, v___y_507_);
lean_dec(v___y_507_);
lean_dec_ref(v___y_506_);
lean_dec(v___y_505_);
lean_dec_ref(v___y_504_);
return v_res_509_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__3(size_t v_sz_510_, size_t v_i_511_, lean_object* v_bs_512_){
_start:
{
uint8_t v___x_513_; 
v___x_513_ = lean_usize_dec_lt(v_i_511_, v_sz_510_);
if (v___x_513_ == 0)
{
return v_bs_512_;
}
else
{
lean_object* v_v_514_; lean_object* v___x_515_; lean_object* v_bs_x27_516_; lean_object* v___x_517_; size_t v___x_518_; size_t v___x_519_; lean_object* v___x_520_; 
v_v_514_ = lean_array_uget(v_bs_512_, v_i_511_);
v___x_515_ = lean_unsigned_to_nat(0u);
v_bs_x27_516_ = lean_array_uset(v_bs_512_, v_i_511_, v___x_515_);
v___x_517_ = l_Lean_mkFVar(v_v_514_);
v___x_518_ = ((size_t)1ULL);
v___x_519_ = lean_usize_add(v_i_511_, v___x_518_);
v___x_520_ = lean_array_uset(v_bs_x27_516_, v_i_511_, v___x_517_);
v_i_511_ = v___x_519_;
v_bs_512_ = v___x_520_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__3___boxed(lean_object* v_sz_522_, lean_object* v_i_523_, lean_object* v_bs_524_){
_start:
{
size_t v_sz_boxed_525_; size_t v_i_boxed_526_; lean_object* v_res_527_; 
v_sz_boxed_525_ = lean_unbox_usize(v_sz_522_);
lean_dec(v_sz_522_);
v_i_boxed_526_ = lean_unbox_usize(v_i_523_);
lean_dec(v_i_523_);
v_res_527_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__3(v_sz_boxed_525_, v_i_boxed_526_, v_bs_524_);
return v_res_527_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5(void){
_start:
{
lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; 
v___x_537_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__2));
v___x_538_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__4));
v___x_539_ = l_Lean_Name_append(v___x_538_, v___x_537_);
return v___x_539_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__7(void){
_start:
{
lean_object* v___x_541_; lean_object* v___x_542_; 
v___x_541_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__6));
v___x_542_ = l_Lean_stringToMessageData(v___x_541_);
return v___x_542_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__9(void){
_start:
{
lean_object* v___x_544_; lean_object* v___x_545_; 
v___x_544_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__8));
v___x_545_ = l_Lean_stringToMessageData(v___x_544_);
return v___x_545_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__11(void){
_start:
{
lean_object* v___x_547_; lean_object* v___x_548_; 
v___x_547_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__10));
v___x_548_ = l_Lean_stringToMessageData(v___x_547_);
return v___x_548_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__16(void){
_start:
{
lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; 
v___x_554_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__15));
v___x_555_ = lean_unsigned_to_nat(15u);
v___x_556_ = lean_unsigned_to_nat(120u);
v___x_557_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__14));
v___x_558_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__13));
v___x_559_ = l_mkPanicMessageWithDecl(v___x_558_, v___x_557_, v___x_556_, v___x_555_, v___x_554_);
return v___x_559_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop(lean_object* v_mvarId_560_, lean_object* v_givenNames_561_, lean_object* v_recursorInfo_562_, lean_object* v_reverted_563_, lean_object* v_major_564_, lean_object* v_indices_565_, lean_object* v_baseSubst_566_, lean_object* v_initialArity_567_, lean_object* v_numMinors_568_, lean_object* v_pos_569_, lean_object* v_minorIdx_570_, lean_object* v_recursor_571_, lean_object* v_recursorType_572_, uint8_t v_consumedMajor_573_, lean_object* v_subgoals_574_, lean_object* v_a_575_, lean_object* v_a_576_, lean_object* v_a_577_, lean_object* v_a_578_){
_start:
{
lean_object* v___y_581_; lean_object* v___y_582_; lean_object* v___y_583_; lean_object* v___y_584_; lean_object* v___y_637_; uint8_t v___y_638_; lean_object* v___y_639_; lean_object* v___y_640_; lean_object* v___y_641_; lean_object* v___y_642_; lean_object* v___y_643_; lean_object* v___y_644_; lean_object* v___y_645_; lean_object* v___y_646_; lean_object* v___y_647_; lean_object* v___y_648_; lean_object* v___y_649_; lean_object* v___y_650_; uint8_t v___y_651_; uint8_t v___y_652_; lean_object* v___y_688_; lean_object* v___y_689_; lean_object* v___y_690_; uint8_t v___y_691_; lean_object* v___y_692_; lean_object* v___y_693_; lean_object* v___y_694_; lean_object* v___y_695_; lean_object* v___y_696_; lean_object* v___y_697_; uint8_t v___y_698_; lean_object* v___y_699_; lean_object* v___y_700_; lean_object* v___y_701_; lean_object* v___y_702_; lean_object* v___y_720_; uint8_t v___y_721_; lean_object* v_fst_722_; lean_object* v_snd_723_; lean_object* v___y_740_; uint8_t v___y_741_; lean_object* v___y_742_; lean_object* v___x_754_; 
v___x_754_ = l_Lean_Meta_whnfForall(v_recursorType_572_, v_a_575_, v_a_576_, v_a_577_, v_a_578_);
if (lean_obj_tag(v___x_754_) == 0)
{
lean_object* v_a_755_; lean_object* v___y_757_; lean_object* v___y_758_; lean_object* v___y_759_; uint8_t v___y_760_; lean_object* v___y_761_; lean_object* v___y_762_; lean_object* v___y_763_; lean_object* v___y_764_; lean_object* v___y_765_; lean_object* v___y_766_; lean_object* v___y_767_; lean_object* v___y_768_; uint8_t v___y_769_; lean_object* v___y_770_; lean_object* v___y_812_; uint8_t v___y_813_; lean_object* v___y_814_; lean_object* v___y_815_; lean_object* v___y_816_; uint8_t v___y_817_; lean_object* v___y_818_; lean_object* v___y_819_; lean_object* v___y_820_; lean_object* v___y_821_; lean_object* v___y_833_; lean_object* v___y_834_; lean_object* v___y_835_; lean_object* v___y_836_; lean_object* v___y_837_; lean_object* v___y_838_; lean_object* v___y_839_; uint8_t v___y_840_; uint8_t v___y_841_; lean_object* v___y_911_; lean_object* v___y_912_; lean_object* v___y_913_; lean_object* v___y_914_; uint8_t v___y_915_; lean_object* v___y_916_; lean_object* v___y_917_; uint8_t v___y_918_; lean_object* v___y_919_; lean_object* v___y_925_; uint8_t v___y_926_; lean_object* v___y_927_; lean_object* v___y_928_; lean_object* v___y_929_; lean_object* v___y_930_; uint8_t v___y_942_; uint8_t v___x_989_; 
v_a_755_ = lean_ctor_get(v___x_754_, 0);
lean_inc(v_a_755_);
lean_dec_ref(v___x_754_);
v___x_989_ = l_Lean_Expr_isForall(v_a_755_);
if (v___x_989_ == 0)
{
v___y_942_ = v___x_989_;
goto v___jp_941_;
}
else
{
lean_object* v_numArgs_990_; uint8_t v___x_991_; 
v_numArgs_990_ = lean_ctor_get(v_recursorInfo_562_, 3);
v___x_991_ = lean_nat_dec_lt(v_pos_569_, v_numArgs_990_);
v___y_942_ = v___x_991_;
goto v___jp_941_;
}
v___jp_756_:
{
lean_object* v___x_771_; 
v___x_771_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___y_757_, v___y_759_, v___y_765_, v___y_762_, v___y_764_, v___y_766_);
if (lean_obj_tag(v___x_771_) == 0)
{
lean_object* v_a_772_; lean_object* v___x_773_; 
v_a_772_ = lean_ctor_get(v___x_771_, 0);
lean_inc(v_a_772_);
lean_dec_ref(v___x_771_);
lean_inc(v_mvarId_560_);
v___x_773_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTypeBody(v_mvarId_560_, v_a_755_, v_a_772_, v___y_765_, v___y_762_, v___y_764_, v___y_766_);
if (lean_obj_tag(v___x_773_) == 0)
{
lean_object* v_options_774_; lean_object* v_a_775_; lean_object* v_inheritedTraceOptions_776_; uint8_t v_hasTrace_777_; lean_object* v___x_778_; 
v_options_774_ = lean_ctor_get(v___y_764_, 2);
v_a_775_ = lean_ctor_get(v___x_773_, 0);
lean_inc(v_a_775_);
lean_dec_ref(v___x_773_);
v_inheritedTraceOptions_776_ = lean_ctor_get(v___y_764_, 13);
v_hasTrace_777_ = lean_ctor_get_uint8(v_options_774_, sizeof(void*)*1);
lean_inc(v_a_772_);
v___x_778_ = l_Lean_Expr_app___override(v_recursor_571_, v_a_772_);
if (v_hasTrace_777_ == 0)
{
v___y_688_ = v_a_772_;
v___y_689_ = v___x_778_;
v___y_690_ = v___y_758_;
v___y_691_ = v___y_760_;
v___y_692_ = v___y_761_;
v___y_693_ = v___y_770_;
v___y_694_ = v___y_767_;
v___y_695_ = v___y_768_;
v___y_696_ = v___y_763_;
v___y_697_ = v_a_775_;
v___y_698_ = v___y_769_;
v___y_699_ = v___y_765_;
v___y_700_ = v___y_762_;
v___y_701_ = v___y_764_;
v___y_702_ = v___y_766_;
goto v___jp_687_;
}
else
{
lean_object* v___x_779_; lean_object* v___x_780_; uint8_t v___x_781_; 
v___x_779_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__2));
v___x_780_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5);
v___x_781_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_776_, v_options_774_, v___x_780_);
if (v___x_781_ == 0)
{
v___y_688_ = v_a_772_;
v___y_689_ = v___x_778_;
v___y_690_ = v___y_758_;
v___y_691_ = v___y_760_;
v___y_692_ = v___y_761_;
v___y_693_ = v___y_770_;
v___y_694_ = v___y_767_;
v___y_695_ = v___y_768_;
v___y_696_ = v___y_763_;
v___y_697_ = v_a_775_;
v___y_698_ = v___y_769_;
v___y_699_ = v___y_765_;
v___y_700_ = v___y_762_;
v___y_701_ = v___y_764_;
v___y_702_ = v___y_766_;
goto v___jp_687_;
}
else
{
lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; 
v___x_782_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__11, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__11_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__11);
v___x_783_ = l_Lean_Expr_fvarId_x21(v_major_564_);
v___x_784_ = l_Lean_MessageData_ofName(v___x_783_);
v___x_785_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_785_, 0, v___x_782_);
lean_ctor_set(v___x_785_, 1, v___x_784_);
v___x_786_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1(v___x_779_, v___x_785_, v___y_765_, v___y_762_, v___y_764_, v___y_766_);
if (lean_obj_tag(v___x_786_) == 0)
{
lean_dec_ref(v___x_786_);
v___y_688_ = v_a_772_;
v___y_689_ = v___x_778_;
v___y_690_ = v___y_758_;
v___y_691_ = v___y_760_;
v___y_692_ = v___y_761_;
v___y_693_ = v___y_770_;
v___y_694_ = v___y_767_;
v___y_695_ = v___y_768_;
v___y_696_ = v___y_763_;
v___y_697_ = v_a_775_;
v___y_698_ = v___y_769_;
v___y_699_ = v___y_765_;
v___y_700_ = v___y_762_;
v___y_701_ = v___y_764_;
v___y_702_ = v___y_766_;
goto v___jp_687_;
}
else
{
lean_object* v_a_787_; lean_object* v___x_789_; uint8_t v_isShared_790_; uint8_t v_isSharedCheck_794_; 
lean_dec_ref(v___x_778_);
lean_dec(v_a_775_);
lean_dec(v_a_772_);
lean_dec_ref(v___y_770_);
lean_dec(v___y_768_);
lean_dec(v___y_763_);
lean_dec(v___y_761_);
lean_dec(v___y_758_);
lean_dec_ref(v_subgoals_574_);
lean_dec(v_minorIdx_570_);
lean_dec(v_pos_569_);
lean_dec(v_baseSubst_566_);
lean_dec_ref(v_major_564_);
lean_dec(v_mvarId_560_);
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
lean_dec(v_a_772_);
lean_dec_ref(v___y_770_);
lean_dec(v___y_768_);
lean_dec(v___y_763_);
lean_dec(v___y_761_);
lean_dec(v___y_758_);
lean_dec_ref(v_subgoals_574_);
lean_dec_ref(v_recursor_571_);
lean_dec(v_minorIdx_570_);
lean_dec(v_pos_569_);
lean_dec(v_baseSubst_566_);
lean_dec_ref(v_major_564_);
lean_dec(v_mvarId_560_);
v_a_795_ = lean_ctor_get(v___x_773_, 0);
v_isSharedCheck_802_ = !lean_is_exclusive(v___x_773_);
if (v_isSharedCheck_802_ == 0)
{
v___x_797_ = v___x_773_;
v_isShared_798_ = v_isSharedCheck_802_;
goto v_resetjp_796_;
}
else
{
lean_inc(v_a_795_);
lean_dec(v___x_773_);
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
lean_dec_ref(v___y_770_);
lean_dec(v___y_768_);
lean_dec(v___y_763_);
lean_dec(v___y_761_);
lean_dec(v___y_758_);
lean_dec(v_a_755_);
lean_dec_ref(v_subgoals_574_);
lean_dec_ref(v_recursor_571_);
lean_dec(v_minorIdx_570_);
lean_dec(v_pos_569_);
lean_dec(v_baseSubst_566_);
lean_dec_ref(v_major_564_);
lean_dec(v_mvarId_560_);
v_a_803_ = lean_ctor_get(v___x_771_, 0);
v_isSharedCheck_810_ = !lean_is_exclusive(v___x_771_);
if (v_isSharedCheck_810_ == 0)
{
v___x_805_ = v___x_771_;
v_isShared_806_ = v_isSharedCheck_810_;
goto v_resetjp_804_;
}
else
{
lean_inc(v_a_803_);
lean_dec(v___x_771_);
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
v___x_822_ = lean_nat_sub(v___y_815_, v_initialArity_567_);
lean_dec(v___y_815_);
v___x_823_ = lean_array_get_size(v_reverted_563_);
v___x_824_ = lean_array_get_size(v_indices_565_);
v___x_825_ = lean_nat_sub(v___x_823_, v___x_824_);
v___x_826_ = lean_nat_sub(v___x_825_, v___y_816_);
lean_dec(v___x_825_);
v___x_827_ = lean_array_get_size(v_givenNames_561_);
v___x_828_ = lean_nat_dec_lt(v_minorIdx_570_, v___x_827_);
if (v___x_828_ == 0)
{
lean_object* v___x_829_; lean_object* v___x_830_; 
v___x_829_ = lean_box(0);
v___x_830_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_830_, 0, v___x_829_);
lean_ctor_set_uint8(v___x_830_, sizeof(void*)*1, v___y_813_);
v___y_757_ = v___y_812_;
v___y_758_ = v___x_826_;
v___y_759_ = v___y_814_;
v___y_760_ = v___y_813_;
v___y_761_ = v___x_824_;
v___y_762_ = v___y_819_;
v___y_763_ = v___x_823_;
v___y_764_ = v___y_820_;
v___y_765_ = v___y_818_;
v___y_766_ = v___y_821_;
v___y_767_ = v___y_816_;
v___y_768_ = v___x_822_;
v___y_769_ = v___y_817_;
v___y_770_ = v___x_830_;
goto v___jp_756_;
}
else
{
lean_object* v___x_831_; 
v___x_831_ = lean_array_fget_borrowed(v_givenNames_561_, v_minorIdx_570_);
lean_inc(v___x_831_);
v___y_757_ = v___y_812_;
v___y_758_ = v___x_826_;
v___y_759_ = v___y_814_;
v___y_760_ = v___y_813_;
v___y_761_ = v___x_824_;
v___y_762_ = v___y_819_;
v___y_763_ = v___x_823_;
v___y_764_ = v___y_820_;
v___y_765_ = v___y_818_;
v___y_766_ = v___y_821_;
v___y_767_ = v___y_816_;
v___y_768_ = v___x_822_;
v___y_769_ = v___y_817_;
v___y_770_ = v___x_831_;
goto v___jp_756_;
}
}
v___jp_832_:
{
if (v___y_841_ == 0)
{
lean_object* v___x_842_; uint8_t v___x_843_; 
lean_inc_ref(v___y_833_);
v___x_842_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTargetArity(v___y_833_);
v___x_843_ = lean_nat_dec_lt(v___x_842_, v_initialArity_567_);
if (v___x_843_ == 0)
{
v___y_812_ = v___y_833_;
v___y_813_ = v___y_841_;
v___y_814_ = v___y_835_;
v___y_815_ = v___x_842_;
v___y_816_ = v___y_838_;
v___y_817_ = v___y_840_;
v___y_818_ = v___y_837_;
v___y_819_ = v___y_839_;
v___y_820_ = v___y_836_;
v___y_821_ = v___y_834_;
goto v___jp_811_;
}
else
{
lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; 
v___x_844_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1));
v___x_845_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9);
lean_inc(v_mvarId_560_);
v___x_846_ = l_Lean_Meta_throwTacticEx___redArg(v___x_844_, v_mvarId_560_, v___x_845_, v___y_837_, v___y_839_, v___y_836_, v___y_834_);
if (lean_obj_tag(v___x_846_) == 0)
{
lean_dec_ref(v___x_846_);
v___y_812_ = v___y_833_;
v___y_813_ = v___y_841_;
v___y_814_ = v___y_835_;
v___y_815_ = v___x_842_;
v___y_816_ = v___y_838_;
v___y_817_ = v___y_840_;
v___y_818_ = v___y_837_;
v___y_819_ = v___y_839_;
v___y_820_ = v___y_836_;
v___y_821_ = v___y_834_;
goto v___jp_811_;
}
else
{
lean_object* v_a_847_; lean_object* v___x_849_; uint8_t v_isShared_850_; uint8_t v_isSharedCheck_854_; 
lean_dec(v___x_842_);
lean_dec(v___y_835_);
lean_dec_ref(v___y_833_);
lean_dec(v_a_755_);
lean_dec_ref(v_subgoals_574_);
lean_dec_ref(v_recursor_571_);
lean_dec(v_minorIdx_570_);
lean_dec(v_pos_569_);
lean_dec(v_baseSubst_566_);
lean_dec_ref(v_major_564_);
lean_dec(v_mvarId_560_);
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
lean_inc_ref(v___y_833_);
v___x_856_ = l_Lean_Meta_synthInstance_x3f(v___y_833_, v___x_855_, v___y_837_, v___y_839_, v___y_836_, v___y_834_);
if (lean_obj_tag(v___x_856_) == 0)
{
lean_object* v_a_857_; 
v_a_857_ = lean_ctor_get(v___x_856_, 0);
lean_inc(v_a_857_);
lean_dec_ref(v___x_856_);
if (lean_obj_tag(v_a_857_) == 0)
{
lean_object* v___x_858_; 
v___x_858_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___y_833_, v___y_835_, v___y_837_, v___y_839_, v___y_836_, v___y_834_);
if (lean_obj_tag(v___x_858_) == 0)
{
lean_object* v_a_859_; lean_object* v___x_860_; 
v_a_859_ = lean_ctor_get(v___x_858_, 0);
lean_inc(v_a_859_);
lean_dec_ref(v___x_858_);
lean_inc(v_mvarId_560_);
v___x_860_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTypeBody(v_mvarId_560_, v_a_755_, v_a_859_, v___y_837_, v___y_839_, v___y_836_, v___y_834_);
if (lean_obj_tag(v___x_860_) == 0)
{
lean_object* v_a_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; 
v_a_861_ = lean_ctor_get(v___x_860_, 0);
lean_inc(v_a_861_);
lean_dec_ref(v___x_860_);
lean_inc(v_a_859_);
v___x_862_ = l_Lean_Expr_app___override(v_recursor_571_, v_a_859_);
v___x_863_ = lean_nat_add(v_pos_569_, v___y_838_);
lean_dec(v_pos_569_);
v___x_864_ = lean_nat_add(v_minorIdx_570_, v___y_838_);
lean_dec(v_minorIdx_570_);
v___x_865_ = l_Lean_Expr_mvarId_x21(v_a_859_);
lean_dec(v_a_859_);
v___x_866_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__12));
v___x_867_ = lean_box(0);
v___x_868_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_868_, 0, v___x_865_);
lean_ctor_set(v___x_868_, 1, v___x_866_);
lean_ctor_set(v___x_868_, 2, v___x_867_);
v___x_869_ = lean_array_push(v_subgoals_574_, v___x_868_);
v_pos_569_ = v___x_863_;
v_minorIdx_570_ = v___x_864_;
v_recursor_571_ = v___x_862_;
v_recursorType_572_ = v_a_861_;
v_subgoals_574_ = v___x_869_;
v_a_575_ = v___y_837_;
v_a_576_ = v___y_839_;
v_a_577_ = v___y_836_;
v_a_578_ = v___y_834_;
goto _start;
}
else
{
lean_object* v_a_871_; lean_object* v___x_873_; uint8_t v_isShared_874_; uint8_t v_isSharedCheck_878_; 
lean_dec(v_a_859_);
lean_dec_ref(v_subgoals_574_);
lean_dec_ref(v_recursor_571_);
lean_dec(v_minorIdx_570_);
lean_dec(v_pos_569_);
lean_dec(v_baseSubst_566_);
lean_dec_ref(v_major_564_);
lean_dec(v_mvarId_560_);
v_a_871_ = lean_ctor_get(v___x_860_, 0);
v_isSharedCheck_878_ = !lean_is_exclusive(v___x_860_);
if (v_isSharedCheck_878_ == 0)
{
v___x_873_ = v___x_860_;
v_isShared_874_ = v_isSharedCheck_878_;
goto v_resetjp_872_;
}
else
{
lean_inc(v_a_871_);
lean_dec(v___x_860_);
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
lean_dec(v_a_755_);
lean_dec_ref(v_subgoals_574_);
lean_dec_ref(v_recursor_571_);
lean_dec(v_minorIdx_570_);
lean_dec(v_pos_569_);
lean_dec(v_baseSubst_566_);
lean_dec_ref(v_major_564_);
lean_dec(v_mvarId_560_);
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
lean_object* v_val_887_; lean_object* v___x_888_; 
lean_dec(v___y_835_);
lean_dec_ref(v___y_833_);
v_val_887_ = lean_ctor_get(v_a_857_, 0);
lean_inc(v_val_887_);
lean_dec_ref(v_a_857_);
lean_inc(v_mvarId_560_);
v___x_888_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTypeBody(v_mvarId_560_, v_a_755_, v_val_887_, v___y_837_, v___y_839_, v___y_836_, v___y_834_);
if (lean_obj_tag(v___x_888_) == 0)
{
lean_object* v_a_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; 
v_a_889_ = lean_ctor_get(v___x_888_, 0);
lean_inc(v_a_889_);
lean_dec_ref(v___x_888_);
v___x_890_ = l_Lean_Expr_app___override(v_recursor_571_, v_val_887_);
v___x_891_ = lean_nat_add(v_pos_569_, v___y_838_);
lean_dec(v_pos_569_);
v___x_892_ = lean_nat_add(v_minorIdx_570_, v___y_838_);
lean_dec(v_minorIdx_570_);
v_pos_569_ = v___x_891_;
v_minorIdx_570_ = v___x_892_;
v_recursor_571_ = v___x_890_;
v_recursorType_572_ = v_a_889_;
v_a_575_ = v___y_837_;
v_a_576_ = v___y_839_;
v_a_577_ = v___y_836_;
v_a_578_ = v___y_834_;
goto _start;
}
else
{
lean_object* v_a_894_; lean_object* v___x_896_; uint8_t v_isShared_897_; uint8_t v_isSharedCheck_901_; 
lean_dec(v_val_887_);
lean_dec_ref(v_subgoals_574_);
lean_dec_ref(v_recursor_571_);
lean_dec(v_minorIdx_570_);
lean_dec(v_pos_569_);
lean_dec(v_baseSubst_566_);
lean_dec_ref(v_major_564_);
lean_dec(v_mvarId_560_);
v_a_894_ = lean_ctor_get(v___x_888_, 0);
v_isSharedCheck_901_ = !lean_is_exclusive(v___x_888_);
if (v_isSharedCheck_901_ == 0)
{
v___x_896_ = v___x_888_;
v_isShared_897_ = v_isSharedCheck_901_;
goto v_resetjp_895_;
}
else
{
lean_inc(v_a_894_);
lean_dec(v___x_888_);
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
lean_dec(v___y_835_);
lean_dec_ref(v___y_833_);
lean_dec(v_a_755_);
lean_dec_ref(v_subgoals_574_);
lean_dec_ref(v_recursor_571_);
lean_dec(v_minorIdx_570_);
lean_dec(v_pos_569_);
lean_dec(v_baseSubst_566_);
lean_dec_ref(v_major_564_);
lean_dec(v_mvarId_560_);
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
v___x_920_ = l_Lean_BinderInfo_isInstImplicit(v___y_915_);
if (v___x_920_ == 0)
{
v___y_833_ = v___y_911_;
v___y_834_ = v___y_912_;
v___y_835_ = v___y_919_;
v___y_836_ = v___y_913_;
v___y_837_ = v___y_914_;
v___y_838_ = v___y_916_;
v___y_839_ = v___y_917_;
v___y_840_ = v___y_918_;
v___y_841_ = v___x_920_;
goto v___jp_832_;
}
else
{
lean_object* v___x_921_; lean_object* v___x_922_; uint8_t v___x_923_; 
v___x_921_ = lean_array_get_size(v_givenNames_561_);
v___x_922_ = lean_unsigned_to_nat(0u);
v___x_923_ = lean_nat_dec_eq(v___x_921_, v___x_922_);
v___y_833_ = v___y_911_;
v___y_834_ = v___y_912_;
v___y_835_ = v___y_919_;
v___y_836_ = v___y_913_;
v___y_837_ = v___y_914_;
v___y_838_ = v___y_916_;
v___y_839_ = v___y_917_;
v___y_840_ = v___y_918_;
v___y_841_ = v___x_923_;
goto v___jp_832_;
}
}
v___jp_924_:
{
if (lean_obj_tag(v_a_755_) == 7)
{
lean_object* v_binderName_931_; lean_object* v_binderType_932_; uint8_t v_binderInfo_933_; lean_object* v___x_934_; lean_object* v___x_935_; uint8_t v___x_936_; 
v_binderName_931_ = lean_ctor_get(v_a_755_, 0);
v_binderType_932_ = lean_ctor_get(v_a_755_, 1);
v_binderInfo_933_ = lean_ctor_get_uint8(v_a_755_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_932_);
v___x_934_ = l_Lean_Expr_headBeta(v_binderType_932_);
v___x_935_ = lean_unsigned_to_nat(1u);
v___x_936_ = lean_nat_dec_eq(v_numMinors_568_, v___x_935_);
if (v___x_936_ == 0)
{
lean_object* v___x_937_; lean_object* v___x_938_; 
lean_inc(v_binderName_931_);
v___x_937_ = lean_erase_macro_scopes(v_binderName_931_);
v___x_938_ = l_Lean_Name_append(v___y_925_, v___x_937_);
v___y_911_ = v___x_934_;
v___y_912_ = v___y_930_;
v___y_913_ = v___y_929_;
v___y_914_ = v___y_927_;
v___y_915_ = v_binderInfo_933_;
v___y_916_ = v___x_935_;
v___y_917_ = v___y_928_;
v___y_918_ = v___y_926_;
v___y_919_ = v___x_938_;
goto v___jp_910_;
}
else
{
v___y_911_ = v___x_934_;
v___y_912_ = v___y_930_;
v___y_913_ = v___y_929_;
v___y_914_ = v___y_927_;
v___y_915_ = v_binderInfo_933_;
v___y_916_ = v___x_935_;
v___y_917_ = v___y_928_;
v___y_918_ = v___y_926_;
v___y_919_ = v___y_925_;
goto v___jp_910_;
}
}
else
{
lean_object* v___x_939_; lean_object* v___x_940_; 
lean_dec(v___y_925_);
lean_dec(v_a_755_);
lean_dec_ref(v_subgoals_574_);
lean_dec_ref(v_recursor_571_);
lean_dec(v_minorIdx_570_);
lean_dec(v_pos_569_);
lean_dec(v_baseSubst_566_);
lean_dec_ref(v_major_564_);
lean_dec(v_mvarId_560_);
v___x_939_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__16, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__16_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__16);
v___x_940_ = l_panic___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__4(v___x_939_, v___y_927_, v___y_928_, v___y_929_, v___y_930_);
return v___x_940_;
}
}
v___jp_941_:
{
if (v___y_942_ == 0)
{
lean_dec(v_a_755_);
lean_dec(v_minorIdx_570_);
lean_dec(v_pos_569_);
lean_dec(v_baseSubst_566_);
lean_dec_ref(v_major_564_);
if (v_consumedMajor_573_ == 0)
{
lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; 
v___x_943_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1));
v___x_944_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9);
lean_inc(v_mvarId_560_);
v___x_945_ = l_Lean_Meta_throwTacticEx___redArg(v___x_943_, v_mvarId_560_, v___x_944_, v_a_575_, v_a_576_, v_a_577_, v_a_578_);
if (lean_obj_tag(v___x_945_) == 0)
{
lean_dec_ref(v___x_945_);
v___y_581_ = v_a_575_;
v___y_582_ = v_a_576_;
v___y_583_ = v_a_577_;
v___y_584_ = v_a_578_;
goto v___jp_580_;
}
else
{
lean_object* v_a_946_; lean_object* v___x_948_; uint8_t v_isShared_949_; uint8_t v_isSharedCheck_953_; 
lean_dec_ref(v_subgoals_574_);
lean_dec_ref(v_recursor_571_);
lean_dec(v_mvarId_560_);
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
v___y_581_ = v_a_575_;
v___y_582_ = v_a_576_;
v___y_583_ = v_a_577_;
v___y_584_ = v_a_578_;
goto v___jp_580_;
}
}
else
{
lean_object* v___x_954_; uint8_t v___x_955_; 
v___x_954_ = l_Lean_Meta_RecursorInfo_firstIndexPos(v_recursorInfo_562_);
v___x_955_ = lean_nat_dec_eq(v_pos_569_, v___x_954_);
lean_dec(v___x_954_);
if (v___x_955_ == 0)
{
lean_object* v___x_956_; 
lean_inc(v_mvarId_560_);
v___x_956_ = l_Lean_MVarId_getTag(v_mvarId_560_, v_a_575_, v_a_576_, v_a_577_, v_a_578_);
if (lean_obj_tag(v___x_956_) == 0)
{
lean_object* v_a_957_; uint8_t v___x_958_; 
v_a_957_ = lean_ctor_get(v___x_956_, 0);
lean_inc(v_a_957_);
lean_dec_ref(v___x_956_);
v___x_958_ = lean_nat_dec_le(v_numMinors_568_, v_minorIdx_570_);
if (v___x_958_ == 0)
{
v___y_925_ = v_a_957_;
v___y_926_ = v___y_942_;
v___y_927_ = v_a_575_;
v___y_928_ = v_a_576_;
v___y_929_ = v_a_577_;
v___y_930_ = v_a_578_;
goto v___jp_924_;
}
else
{
lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; 
v___x_959_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1));
v___x_960_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9);
lean_inc(v_mvarId_560_);
v___x_961_ = l_Lean_Meta_throwTacticEx___redArg(v___x_959_, v_mvarId_560_, v___x_960_, v_a_575_, v_a_576_, v_a_577_, v_a_578_);
if (lean_obj_tag(v___x_961_) == 0)
{
lean_dec_ref(v___x_961_);
v___y_925_ = v_a_957_;
v___y_926_ = v___y_942_;
v___y_927_ = v_a_575_;
v___y_928_ = v_a_576_;
v___y_929_ = v_a_577_;
v___y_930_ = v_a_578_;
goto v___jp_924_;
}
else
{
lean_object* v_a_962_; lean_object* v___x_964_; uint8_t v_isShared_965_; uint8_t v_isSharedCheck_969_; 
lean_dec(v_a_957_);
lean_dec(v_a_755_);
lean_dec_ref(v_subgoals_574_);
lean_dec_ref(v_recursor_571_);
lean_dec(v_minorIdx_570_);
lean_dec(v_pos_569_);
lean_dec(v_baseSubst_566_);
lean_dec_ref(v_major_564_);
lean_dec(v_mvarId_560_);
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
lean_dec(v_a_755_);
lean_dec_ref(v_subgoals_574_);
lean_dec_ref(v_recursor_571_);
lean_dec(v_minorIdx_570_);
lean_dec(v_pos_569_);
lean_dec(v_baseSubst_566_);
lean_dec_ref(v_major_564_);
lean_dec(v_mvarId_560_);
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
v___x_979_ = lean_array_get_size(v_indices_565_);
v___x_980_ = lean_nat_dec_lt(v___x_978_, v___x_979_);
if (v___x_980_ == 0)
{
v___y_720_ = v___x_979_;
v___y_721_ = v___x_955_;
v_fst_722_ = v_recursor_571_;
v_snd_723_ = v_a_755_;
goto v___jp_719_;
}
else
{
lean_object* v___x_981_; uint8_t v___x_982_; 
lean_inc(v_a_755_);
lean_inc_ref(v_recursor_571_);
v___x_981_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_981_, 0, v_recursor_571_);
lean_ctor_set(v___x_981_, 1, v_a_755_);
v___x_982_ = lean_nat_dec_le(v___x_979_, v___x_979_);
if (v___x_982_ == 0)
{
if (v___x_980_ == 0)
{
lean_dec_ref(v___x_981_);
v___y_720_ = v___x_979_;
v___y_721_ = v___x_955_;
v_fst_722_ = v_recursor_571_;
v_snd_723_ = v_a_755_;
goto v___jp_719_;
}
else
{
size_t v___x_983_; size_t v___x_984_; lean_object* v___x_985_; 
lean_dec(v_a_755_);
lean_dec_ref(v_recursor_571_);
v___x_983_ = ((size_t)0ULL);
v___x_984_ = lean_usize_of_nat(v___x_979_);
lean_inc(v_mvarId_560_);
v___x_985_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__5(v_mvarId_560_, v_indices_565_, v___x_983_, v___x_984_, v___x_981_, v_a_575_, v_a_576_, v_a_577_, v_a_578_);
v___y_740_ = v___x_979_;
v___y_741_ = v___x_955_;
v___y_742_ = v___x_985_;
goto v___jp_739_;
}
}
else
{
size_t v___x_986_; size_t v___x_987_; lean_object* v___x_988_; 
lean_dec(v_a_755_);
lean_dec_ref(v_recursor_571_);
v___x_986_ = ((size_t)0ULL);
v___x_987_ = lean_usize_of_nat(v___x_979_);
lean_inc(v_mvarId_560_);
v___x_988_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__5(v_mvarId_560_, v_indices_565_, v___x_986_, v___x_987_, v___x_981_, v_a_575_, v_a_576_, v_a_577_, v_a_578_);
v___y_740_ = v___x_979_;
v___y_741_ = v___x_955_;
v___y_742_ = v___x_988_;
goto v___jp_739_;
}
}
}
}
}
}
else
{
lean_object* v_a_992_; lean_object* v___x_994_; uint8_t v_isShared_995_; uint8_t v_isSharedCheck_999_; 
lean_dec_ref(v_subgoals_574_);
lean_dec_ref(v_recursor_571_);
lean_dec(v_minorIdx_570_);
lean_dec(v_pos_569_);
lean_dec(v_baseSubst_566_);
lean_dec_ref(v_major_564_);
lean_dec(v_mvarId_560_);
v_a_992_ = lean_ctor_get(v___x_754_, 0);
v_isSharedCheck_999_ = !lean_is_exclusive(v___x_754_);
if (v_isSharedCheck_999_ == 0)
{
v___x_994_ = v___x_754_;
v_isShared_995_ = v_isSharedCheck_999_;
goto v_resetjp_993_;
}
else
{
lean_inc(v_a_992_);
lean_dec(v___x_754_);
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
v___jp_580_:
{
lean_object* v___x_585_; 
v___x_585_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0___redArg(v_mvarId_560_, v_recursor_571_, v___y_582_);
if (lean_obj_tag(v___x_585_) == 0)
{
lean_object* v___x_587_; uint8_t v_isShared_588_; uint8_t v_isSharedCheck_626_; 
v_isSharedCheck_626_ = !lean_is_exclusive(v___x_585_);
if (v_isSharedCheck_626_ == 0)
{
lean_object* v_unused_627_; 
v_unused_627_ = lean_ctor_get(v___x_585_, 0);
lean_dec(v_unused_627_);
v___x_587_ = v___x_585_;
v_isShared_588_ = v_isSharedCheck_626_;
goto v_resetjp_586_;
}
else
{
lean_dec(v___x_585_);
v___x_587_ = lean_box(0);
v_isShared_588_ = v_isSharedCheck_626_;
goto v_resetjp_586_;
}
v_resetjp_586_:
{
lean_object* v_options_589_; uint8_t v_hasTrace_590_; 
v_options_589_ = lean_ctor_get(v___y_583_, 2);
v_hasTrace_590_ = lean_ctor_get_uint8(v_options_589_, sizeof(void*)*1);
if (v_hasTrace_590_ == 0)
{
lean_object* v___x_592_; 
if (v_isShared_588_ == 0)
{
lean_ctor_set(v___x_587_, 0, v_subgoals_574_);
v___x_592_ = v___x_587_;
goto v_reusejp_591_;
}
else
{
lean_object* v_reuseFailAlloc_593_; 
v_reuseFailAlloc_593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_593_, 0, v_subgoals_574_);
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
lean_object* v_inheritedTraceOptions_594_; lean_object* v___x_595_; lean_object* v___x_596_; uint8_t v___x_597_; 
v_inheritedTraceOptions_594_ = lean_ctor_get(v___y_583_, 13);
v___x_595_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__2));
v___x_596_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5);
v___x_597_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_594_, v_options_589_, v___x_596_);
if (v___x_597_ == 0)
{
lean_object* v___x_599_; 
if (v_isShared_588_ == 0)
{
lean_ctor_set(v___x_587_, 0, v_subgoals_574_);
v___x_599_ = v___x_587_;
goto v_reusejp_598_;
}
else
{
lean_object* v_reuseFailAlloc_600_; 
v_reuseFailAlloc_600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_600_, 0, v_subgoals_574_);
v___x_599_ = v_reuseFailAlloc_600_;
goto v_reusejp_598_;
}
v_reusejp_598_:
{
return v___x_599_;
}
}
else
{
lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; 
lean_del_object(v___x_587_);
v___x_601_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__7, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__7_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__7);
v___x_602_ = lean_array_get_size(v_subgoals_574_);
v___x_603_ = l_Nat_reprFast(v___x_602_);
v___x_604_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_604_, 0, v___x_603_);
v___x_605_ = l_Lean_MessageData_ofFormat(v___x_604_);
v___x_606_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_606_, 0, v___x_601_);
lean_ctor_set(v___x_606_, 1, v___x_605_);
v___x_607_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__9, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__9_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__9);
v___x_608_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_608_, 0, v___x_606_);
lean_ctor_set(v___x_608_, 1, v___x_607_);
v___x_609_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1(v___x_595_, v___x_608_, v___y_581_, v___y_582_, v___y_583_, v___y_584_);
if (lean_obj_tag(v___x_609_) == 0)
{
lean_object* v___x_611_; uint8_t v_isShared_612_; uint8_t v_isSharedCheck_616_; 
v_isSharedCheck_616_ = !lean_is_exclusive(v___x_609_);
if (v_isSharedCheck_616_ == 0)
{
lean_object* v_unused_617_; 
v_unused_617_ = lean_ctor_get(v___x_609_, 0);
lean_dec(v_unused_617_);
v___x_611_ = v___x_609_;
v_isShared_612_ = v_isSharedCheck_616_;
goto v_resetjp_610_;
}
else
{
lean_dec(v___x_609_);
v___x_611_ = lean_box(0);
v_isShared_612_ = v_isSharedCheck_616_;
goto v_resetjp_610_;
}
v_resetjp_610_:
{
lean_object* v___x_614_; 
if (v_isShared_612_ == 0)
{
lean_ctor_set(v___x_611_, 0, v_subgoals_574_);
v___x_614_ = v___x_611_;
goto v_reusejp_613_;
}
else
{
lean_object* v_reuseFailAlloc_615_; 
v_reuseFailAlloc_615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_615_, 0, v_subgoals_574_);
v___x_614_ = v_reuseFailAlloc_615_;
goto v_reusejp_613_;
}
v_reusejp_613_:
{
return v___x_614_;
}
}
}
else
{
lean_object* v_a_618_; lean_object* v___x_620_; uint8_t v_isShared_621_; uint8_t v_isSharedCheck_625_; 
lean_dec_ref(v_subgoals_574_);
v_a_618_ = lean_ctor_get(v___x_609_, 0);
v_isSharedCheck_625_ = !lean_is_exclusive(v___x_609_);
if (v_isSharedCheck_625_ == 0)
{
v___x_620_ = v___x_609_;
v_isShared_621_ = v_isSharedCheck_625_;
goto v_resetjp_619_;
}
else
{
lean_inc(v_a_618_);
lean_dec(v___x_609_);
v___x_620_ = lean_box(0);
v_isShared_621_ = v_isSharedCheck_625_;
goto v_resetjp_619_;
}
v_resetjp_619_:
{
lean_object* v___x_623_; 
if (v_isShared_621_ == 0)
{
v___x_623_ = v___x_620_;
goto v_reusejp_622_;
}
else
{
lean_object* v_reuseFailAlloc_624_; 
v_reuseFailAlloc_624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_624_, 0, v_a_618_);
v___x_623_ = v_reuseFailAlloc_624_;
goto v_reusejp_622_;
}
v_reusejp_622_:
{
return v___x_623_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_628_; lean_object* v___x_630_; uint8_t v_isShared_631_; uint8_t v_isSharedCheck_635_; 
lean_dec_ref(v_subgoals_574_);
v_a_628_ = lean_ctor_get(v___x_585_, 0);
v_isSharedCheck_635_ = !lean_is_exclusive(v___x_585_);
if (v_isSharedCheck_635_ == 0)
{
v___x_630_ = v___x_585_;
v_isShared_631_ = v_isSharedCheck_635_;
goto v_resetjp_629_;
}
else
{
lean_inc(v_a_628_);
lean_dec(v___x_585_);
v___x_630_ = lean_box(0);
v_isShared_631_ = v_isSharedCheck_635_;
goto v_resetjp_629_;
}
v_resetjp_629_:
{
lean_object* v___x_633_; 
if (v_isShared_631_ == 0)
{
v___x_633_ = v___x_630_;
goto v_reusejp_632_;
}
else
{
lean_object* v_reuseFailAlloc_634_; 
v_reuseFailAlloc_634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_634_, 0, v_a_628_);
v___x_633_ = v_reuseFailAlloc_634_;
goto v_reusejp_632_;
}
v_reusejp_632_:
{
return v___x_633_;
}
}
}
}
v___jp_636_:
{
lean_object* v___x_653_; 
v___x_653_ = l_Lean_Meta_introNCore(v___y_645_, v___y_649_, v___y_640_, v___y_652_, v___y_638_, v___y_641_, v___y_646_, v___y_643_, v___y_647_);
if (lean_obj_tag(v___x_653_) == 0)
{
lean_object* v_a_654_; lean_object* v_fst_655_; lean_object* v_snd_656_; lean_object* v___x_657_; lean_object* v___x_658_; 
v_a_654_ = lean_ctor_get(v___x_653_, 0);
lean_inc(v_a_654_);
lean_dec_ref(v___x_653_);
v_fst_655_ = lean_ctor_get(v_a_654_, 0);
lean_inc(v_fst_655_);
v_snd_656_ = lean_ctor_get(v_a_654_, 1);
lean_inc(v_snd_656_);
lean_dec(v_a_654_);
v___x_657_ = lean_box(0);
v___x_658_ = l_Lean_Meta_introNCore(v_snd_656_, v___y_637_, v___x_657_, v___y_638_, v___y_651_, v___y_641_, v___y_646_, v___y_643_, v___y_647_);
if (lean_obj_tag(v___x_658_) == 0)
{
lean_object* v_a_659_; lean_object* v_fst_660_; lean_object* v_snd_661_; lean_object* v___x_662_; size_t v_sz_663_; size_t v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; 
v_a_659_ = lean_ctor_get(v___x_658_, 0);
lean_inc(v_a_659_);
lean_dec_ref(v___x_658_);
v_fst_660_ = lean_ctor_get(v_a_659_, 0);
lean_inc(v_fst_660_);
v_snd_661_ = lean_ctor_get(v_a_659_, 1);
lean_inc(v_snd_661_);
lean_dec(v_a_659_);
lean_inc(v_baseSubst_566_);
lean_inc(v___y_642_);
v___x_662_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__2___redArg(v___y_639_, v_reverted_563_, v_fst_660_, v___y_642_, v___y_642_, v_baseSubst_566_);
lean_dec(v___y_642_);
lean_dec(v_fst_660_);
lean_dec(v___y_639_);
v_sz_663_ = lean_array_size(v_fst_655_);
v___x_664_ = ((size_t)0ULL);
v___x_665_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__3(v_sz_663_, v___x_664_, v_fst_655_);
v___x_666_ = lean_nat_add(v_pos_569_, v___y_648_);
lean_dec(v_pos_569_);
v___x_667_ = lean_nat_add(v_minorIdx_570_, v___y_648_);
lean_dec(v_minorIdx_570_);
v___x_668_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_668_, 0, v_snd_661_);
lean_ctor_set(v___x_668_, 1, v___x_665_);
lean_ctor_set(v___x_668_, 2, v___x_662_);
v___x_669_ = lean_array_push(v_subgoals_574_, v___x_668_);
v_pos_569_ = v___x_666_;
v_minorIdx_570_ = v___x_667_;
v_recursor_571_ = v___y_644_;
v_recursorType_572_ = v___y_650_;
v_subgoals_574_ = v___x_669_;
v_a_575_ = v___y_641_;
v_a_576_ = v___y_646_;
v_a_577_ = v___y_643_;
v_a_578_ = v___y_647_;
goto _start;
}
else
{
lean_object* v_a_671_; lean_object* v___x_673_; uint8_t v_isShared_674_; uint8_t v_isSharedCheck_678_; 
lean_dec(v_fst_655_);
lean_dec_ref(v___y_650_);
lean_dec_ref(v___y_644_);
lean_dec(v___y_642_);
lean_dec(v___y_639_);
lean_dec_ref(v_subgoals_574_);
lean_dec(v_minorIdx_570_);
lean_dec(v_pos_569_);
lean_dec(v_baseSubst_566_);
lean_dec_ref(v_major_564_);
lean_dec(v_mvarId_560_);
v_a_671_ = lean_ctor_get(v___x_658_, 0);
v_isSharedCheck_678_ = !lean_is_exclusive(v___x_658_);
if (v_isSharedCheck_678_ == 0)
{
v___x_673_ = v___x_658_;
v_isShared_674_ = v_isSharedCheck_678_;
goto v_resetjp_672_;
}
else
{
lean_inc(v_a_671_);
lean_dec(v___x_658_);
v___x_673_ = lean_box(0);
v_isShared_674_ = v_isSharedCheck_678_;
goto v_resetjp_672_;
}
v_resetjp_672_:
{
lean_object* v___x_676_; 
if (v_isShared_674_ == 0)
{
v___x_676_ = v___x_673_;
goto v_reusejp_675_;
}
else
{
lean_object* v_reuseFailAlloc_677_; 
v_reuseFailAlloc_677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_677_, 0, v_a_671_);
v___x_676_ = v_reuseFailAlloc_677_;
goto v_reusejp_675_;
}
v_reusejp_675_:
{
return v___x_676_;
}
}
}
}
else
{
lean_object* v_a_679_; lean_object* v___x_681_; uint8_t v_isShared_682_; uint8_t v_isSharedCheck_686_; 
lean_dec_ref(v___y_650_);
lean_dec_ref(v___y_644_);
lean_dec(v___y_642_);
lean_dec(v___y_639_);
lean_dec(v___y_637_);
lean_dec_ref(v_subgoals_574_);
lean_dec(v_minorIdx_570_);
lean_dec(v_pos_569_);
lean_dec(v_baseSubst_566_);
lean_dec_ref(v_major_564_);
lean_dec(v_mvarId_560_);
v_a_679_ = lean_ctor_get(v___x_653_, 0);
v_isSharedCheck_686_ = !lean_is_exclusive(v___x_653_);
if (v_isSharedCheck_686_ == 0)
{
v___x_681_ = v___x_653_;
v_isShared_682_ = v_isSharedCheck_686_;
goto v_resetjp_680_;
}
else
{
lean_inc(v_a_679_);
lean_dec(v___x_653_);
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
v___jp_687_:
{
lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; 
v___x_703_ = l_Lean_Expr_mvarId_x21(v___y_688_);
lean_dec_ref(v___y_688_);
v___x_704_ = l_Lean_Expr_fvarId_x21(v_major_564_);
v___x_705_ = l_Lean_MVarId_tryClear(v___x_703_, v___x_704_, v___y_699_, v___y_700_, v___y_701_, v___y_702_);
if (lean_obj_tag(v___x_705_) == 0)
{
uint8_t v_explicit_706_; 
v_explicit_706_ = lean_ctor_get_uint8(v___y_693_, sizeof(void*)*1);
if (v_explicit_706_ == 0)
{
lean_object* v_a_707_; lean_object* v_varNames_708_; 
v_a_707_ = lean_ctor_get(v___x_705_, 0);
lean_inc(v_a_707_);
lean_dec_ref(v___x_705_);
v_varNames_708_ = lean_ctor_get(v___y_693_, 0);
lean_inc(v_varNames_708_);
lean_dec_ref(v___y_693_);
v___y_637_ = v___y_690_;
v___y_638_ = v___y_691_;
v___y_639_ = v___y_692_;
v___y_640_ = v_varNames_708_;
v___y_641_ = v___y_699_;
v___y_642_ = v___y_696_;
v___y_643_ = v___y_701_;
v___y_644_ = v___y_689_;
v___y_645_ = v_a_707_;
v___y_646_ = v___y_700_;
v___y_647_ = v___y_702_;
v___y_648_ = v___y_694_;
v___y_649_ = v___y_695_;
v___y_650_ = v___y_697_;
v___y_651_ = v___y_698_;
v___y_652_ = v___y_698_;
goto v___jp_636_;
}
else
{
lean_object* v_a_709_; lean_object* v_varNames_710_; 
v_a_709_ = lean_ctor_get(v___x_705_, 0);
lean_inc(v_a_709_);
lean_dec_ref(v___x_705_);
v_varNames_710_ = lean_ctor_get(v___y_693_, 0);
lean_inc(v_varNames_710_);
lean_dec_ref(v___y_693_);
v___y_637_ = v___y_690_;
v___y_638_ = v___y_691_;
v___y_639_ = v___y_692_;
v___y_640_ = v_varNames_710_;
v___y_641_ = v___y_699_;
v___y_642_ = v___y_696_;
v___y_643_ = v___y_701_;
v___y_644_ = v___y_689_;
v___y_645_ = v_a_709_;
v___y_646_ = v___y_700_;
v___y_647_ = v___y_702_;
v___y_648_ = v___y_694_;
v___y_649_ = v___y_695_;
v___y_650_ = v___y_697_;
v___y_651_ = v___y_698_;
v___y_652_ = v___y_691_;
goto v___jp_636_;
}
}
else
{
lean_object* v_a_711_; lean_object* v___x_713_; uint8_t v_isShared_714_; uint8_t v_isSharedCheck_718_; 
lean_dec_ref(v___y_697_);
lean_dec(v___y_696_);
lean_dec(v___y_695_);
lean_dec_ref(v___y_693_);
lean_dec(v___y_692_);
lean_dec(v___y_690_);
lean_dec_ref(v___y_689_);
lean_dec_ref(v_subgoals_574_);
lean_dec(v_minorIdx_570_);
lean_dec(v_pos_569_);
lean_dec(v_baseSubst_566_);
lean_dec_ref(v_major_564_);
lean_dec(v_mvarId_560_);
v_a_711_ = lean_ctor_get(v___x_705_, 0);
v_isSharedCheck_718_ = !lean_is_exclusive(v___x_705_);
if (v_isSharedCheck_718_ == 0)
{
v___x_713_ = v___x_705_;
v_isShared_714_ = v_isSharedCheck_718_;
goto v_resetjp_712_;
}
else
{
lean_inc(v_a_711_);
lean_dec(v___x_705_);
v___x_713_ = lean_box(0);
v_isShared_714_ = v_isSharedCheck_718_;
goto v_resetjp_712_;
}
v_resetjp_712_:
{
lean_object* v___x_716_; 
if (v_isShared_714_ == 0)
{
v___x_716_ = v___x_713_;
goto v_reusejp_715_;
}
else
{
lean_object* v_reuseFailAlloc_717_; 
v_reuseFailAlloc_717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_717_, 0, v_a_711_);
v___x_716_ = v_reuseFailAlloc_717_;
goto v_reusejp_715_;
}
v_reusejp_715_:
{
return v___x_716_;
}
}
}
}
v___jp_719_:
{
lean_object* v___x_724_; 
lean_inc(v_mvarId_560_);
v___x_724_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTypeBody(v_mvarId_560_, v_snd_723_, v_major_564_, v_a_575_, v_a_576_, v_a_577_, v_a_578_);
if (lean_obj_tag(v___x_724_) == 0)
{
lean_object* v_a_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; 
v_a_725_ = lean_ctor_get(v___x_724_, 0);
lean_inc(v_a_725_);
lean_dec_ref(v___x_724_);
lean_inc_ref(v_major_564_);
v___x_726_ = l_Lean_Expr_app___override(v_fst_722_, v_major_564_);
v___x_727_ = lean_unsigned_to_nat(1u);
v___x_728_ = lean_nat_add(v_pos_569_, v___x_727_);
lean_dec(v_pos_569_);
v___x_729_ = lean_nat_add(v___x_728_, v___y_720_);
lean_dec(v___y_720_);
lean_dec(v___x_728_);
v_pos_569_ = v___x_729_;
v_recursor_571_ = v___x_726_;
v_recursorType_572_ = v_a_725_;
v_consumedMajor_573_ = v___y_721_;
goto _start;
}
else
{
lean_object* v_a_731_; lean_object* v___x_733_; uint8_t v_isShared_734_; uint8_t v_isSharedCheck_738_; 
lean_dec_ref(v_fst_722_);
lean_dec(v___y_720_);
lean_dec_ref(v_subgoals_574_);
lean_dec(v_minorIdx_570_);
lean_dec(v_pos_569_);
lean_dec(v_baseSubst_566_);
lean_dec_ref(v_major_564_);
lean_dec(v_mvarId_560_);
v_a_731_ = lean_ctor_get(v___x_724_, 0);
v_isSharedCheck_738_ = !lean_is_exclusive(v___x_724_);
if (v_isSharedCheck_738_ == 0)
{
v___x_733_ = v___x_724_;
v_isShared_734_ = v_isSharedCheck_738_;
goto v_resetjp_732_;
}
else
{
lean_inc(v_a_731_);
lean_dec(v___x_724_);
v___x_733_ = lean_box(0);
v_isShared_734_ = v_isSharedCheck_738_;
goto v_resetjp_732_;
}
v_resetjp_732_:
{
lean_object* v___x_736_; 
if (v_isShared_734_ == 0)
{
v___x_736_ = v___x_733_;
goto v_reusejp_735_;
}
else
{
lean_object* v_reuseFailAlloc_737_; 
v_reuseFailAlloc_737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_737_, 0, v_a_731_);
v___x_736_ = v_reuseFailAlloc_737_;
goto v_reusejp_735_;
}
v_reusejp_735_:
{
return v___x_736_;
}
}
}
}
v___jp_739_:
{
if (lean_obj_tag(v___y_742_) == 0)
{
lean_object* v_a_743_; lean_object* v_fst_744_; lean_object* v_snd_745_; 
v_a_743_ = lean_ctor_get(v___y_742_, 0);
lean_inc(v_a_743_);
lean_dec_ref(v___y_742_);
v_fst_744_ = lean_ctor_get(v_a_743_, 0);
lean_inc(v_fst_744_);
v_snd_745_ = lean_ctor_get(v_a_743_, 1);
lean_inc(v_snd_745_);
lean_dec(v_a_743_);
v___y_720_ = v___y_740_;
v___y_721_ = v___y_741_;
v_fst_722_ = v_fst_744_;
v_snd_723_ = v_snd_745_;
goto v___jp_719_;
}
else
{
lean_object* v_a_746_; lean_object* v___x_748_; uint8_t v_isShared_749_; uint8_t v_isSharedCheck_753_; 
lean_dec(v___y_740_);
lean_dec_ref(v_subgoals_574_);
lean_dec(v_minorIdx_570_);
lean_dec(v_pos_569_);
lean_dec(v_baseSubst_566_);
lean_dec_ref(v_major_564_);
lean_dec(v_mvarId_560_);
v_a_746_ = lean_ctor_get(v___y_742_, 0);
v_isSharedCheck_753_ = !lean_is_exclusive(v___y_742_);
if (v_isSharedCheck_753_ == 0)
{
v___x_748_ = v___y_742_;
v_isShared_749_ = v_isSharedCheck_753_;
goto v_resetjp_747_;
}
else
{
lean_inc(v_a_746_);
lean_dec(v___y_742_);
v___x_748_ = lean_box(0);
v_isShared_749_ = v_isSharedCheck_753_;
goto v_resetjp_747_;
}
v_resetjp_747_:
{
lean_object* v___x_751_; 
if (v_isShared_749_ == 0)
{
v___x_751_ = v___x_748_;
goto v_reusejp_750_;
}
else
{
lean_object* v_reuseFailAlloc_752_; 
v_reuseFailAlloc_752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_752_, 0, v_a_746_);
v___x_751_ = v_reuseFailAlloc_752_;
goto v_reusejp_750_;
}
v_reusejp_750_:
{
return v___x_751_;
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
size_t v_x_11494__boxed_1072_; size_t v_x_11495__boxed_1073_; lean_object* v_res_1074_; 
v_x_11494__boxed_1072_ = lean_unbox_usize(v_x_1068_);
lean_dec(v_x_1068_);
v_x_11495__boxed_1073_ = lean_unbox_usize(v_x_1069_);
lean_dec(v_x_1069_);
v_res_1074_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2(v_00_u03b2_1066_, v_x_1067_, v_x_11494__boxed_1072_, v_x_11495__boxed_1073_, v_x_1070_, v_x_1071_);
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
lean_object* v_a_1119_; lean_object* v___x_1120_; 
v_a_1119_ = lean_ctor_get(v___x_1118_, 0);
lean_inc(v_a_1119_);
lean_dec_ref(v___x_1118_);
lean_inc(v_a_1116_);
lean_inc_ref(v_a_1115_);
lean_inc(v_a_1114_);
lean_inc_ref(v_a_1113_);
lean_inc_ref(v_recursor_1112_);
v___x_1120_ = lean_infer_type(v_recursor_1112_, v_a_1113_, v_a_1114_, v_a_1115_, v_a_1116_);
if (lean_obj_tag(v___x_1120_) == 0)
{
lean_object* v_a_1121_; lean_object* v_paramsPos_1122_; lean_object* v_produceMotive_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; uint8_t v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; 
v_a_1121_ = lean_ctor_get(v___x_1120_, 0);
lean_inc(v_a_1121_);
lean_dec_ref(v___x_1120_);
v_paramsPos_1122_ = lean_ctor_get(v_recursorInfo_1107_, 5);
v_produceMotive_1123_ = lean_ctor_get(v_recursorInfo_1107_, 7);
v___x_1124_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTargetArity(v_a_1119_);
v___x_1125_ = l_List_lengthTR___redArg(v_produceMotive_1123_);
v___x_1126_ = l_List_lengthTR___redArg(v_paramsPos_1122_);
v___x_1127_ = lean_unsigned_to_nat(1u);
v___x_1128_ = lean_nat_add(v___x_1126_, v___x_1127_);
lean_dec(v___x_1126_);
v___x_1129_ = lean_unsigned_to_nat(0u);
v___x_1130_ = 0;
v___x_1131_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize___closed__0));
v___x_1132_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop(v_mvarId_1105_, v_givenNames_1106_, v_recursorInfo_1107_, v_reverted_1108_, v_major_1109_, v_indices_1110_, v_baseSubst_1111_, v___x_1124_, v___x_1125_, v___x_1128_, v___x_1129_, v_recursor_1112_, v_a_1121_, v___x_1130_, v___x_1131_, v_a_1113_, v_a_1114_, v_a_1115_, v_a_1116_);
lean_dec(v___x_1125_);
lean_dec(v___x_1124_);
return v___x_1132_;
}
else
{
lean_object* v_a_1133_; lean_object* v___x_1135_; uint8_t v_isShared_1136_; uint8_t v_isSharedCheck_1140_; 
lean_dec(v_a_1119_);
lean_dec_ref(v_recursor_1112_);
lean_dec(v_baseSubst_1111_);
lean_dec_ref(v_major_1109_);
lean_dec(v_mvarId_1105_);
v_a_1133_ = lean_ctor_get(v___x_1120_, 0);
v_isSharedCheck_1140_ = !lean_is_exclusive(v___x_1120_);
if (v_isSharedCheck_1140_ == 0)
{
v___x_1135_ = v___x_1120_;
v_isShared_1136_ = v_isSharedCheck_1140_;
goto v_resetjp_1134_;
}
else
{
lean_inc(v_a_1133_);
lean_dec(v___x_1120_);
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
LEAN_EXPORT uint8_t l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___lam__0(lean_object* v_fvarId_1208_, lean_object* v_x_1209_){
_start:
{
uint8_t v___x_1210_; 
v___x_1210_ = l_Lean_instBEqFVarId_beq(v_fvarId_1208_, v_x_1209_);
return v___x_1210_;
}
}
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___lam__0___boxed(lean_object* v_fvarId_1211_, lean_object* v_x_1212_){
_start:
{
uint8_t v_res_1213_; lean_object* v_r_1214_; 
v_res_1213_ = l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___lam__0(v_fvarId_1211_, v_x_1212_);
lean_dec(v_x_1212_);
lean_dec(v_fvarId_1211_);
v_r_1214_ = lean_box(v_res_1213_);
return v_r_1214_;
}
}
LEAN_EXPORT uint8_t l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___lam__1(lean_object* v_x_1215_){
_start:
{
uint8_t v___x_1216_; 
v___x_1216_ = 0;
return v___x_1216_;
}
}
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___lam__1___boxed(lean_object* v_x_1217_){
_start:
{
uint8_t v_res_1218_; lean_object* v_r_1219_; 
v_res_1218_ = l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___lam__1(v_x_1217_);
lean_dec(v_x_1217_);
v_r_1219_ = lean_box(v_res_1218_);
return v_r_1219_;
}
}
static lean_object* _init_l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; 
v___x_1221_ = lean_box(0);
v___x_1222_ = lean_unsigned_to_nat(16u);
v___x_1223_ = lean_mk_array(v___x_1222_, v___x_1221_);
return v___x_1223_;
}
}
static lean_object* _init_l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; 
v___x_1224_ = lean_obj_once(&l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__1, &l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__1_once, _init_l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__1);
v___x_1225_ = lean_unsigned_to_nat(0u);
v___x_1226_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1226_, 0, v___x_1225_);
lean_ctor_set(v___x_1226_, 1, v___x_1224_);
return v___x_1226_;
}
}
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg(lean_object* v_localDecl_1227_, lean_object* v_fvarId_1228_, uint8_t v_generalizeNondepLet_1229_, lean_object* v___y_1230_){
_start:
{
uint8_t v_fst_1233_; lean_object* v_snd_1234_; lean_object* v___y_1253_; lean_object* v___f_1257_; lean_object* v___f_1258_; 
v___f_1257_ = lean_alloc_closure((void*)(l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1257_, 0, v_fvarId_1228_);
v___f_1258_ = ((lean_object*)(l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__0));
if (lean_obj_tag(v_localDecl_1227_) == 0)
{
lean_object* v_type_1259_; lean_object* v___x_1260_; uint8_t v_fst_1262_; lean_object* v_mctx_1263_; lean_object* v___y_1281_; lean_object* v_mctx_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; uint8_t v___x_1289_; 
v_type_1259_ = lean_ctor_get(v_localDecl_1227_, 3);
lean_inc_ref(v_type_1259_);
lean_dec_ref(v_localDecl_1227_);
v___x_1260_ = lean_st_ref_get(v___y_1230_);
v_mctx_1286_ = lean_ctor_get(v___x_1260_, 0);
lean_inc_ref_n(v_mctx_1286_, 2);
lean_dec(v___x_1260_);
v___x_1287_ = lean_obj_once(&l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__2, &l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__2_once, _init_l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__2);
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
lean_dec_ref(v___x_1288_);
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
v___x_1274_ = lean_st_ref_set(v___y_1230_, v___x_1273_);
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
lean_dec_ref(v_localDecl_1227_);
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
v___x_1344_ = lean_obj_once(&l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__2, &l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__2_once, _init_l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__2);
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
lean_dec_ref(v___x_1345_);
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
v___x_1331_ = lean_st_ref_set(v___y_1230_, v___x_1330_);
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
v___x_1311_ = lean_obj_once(&l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__2, &l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__2_once, _init_l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__2);
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
v___x_1246_ = lean_st_ref_set(v___y_1230_, v___x_1245_);
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
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___boxed(lean_object* v_localDecl_1350_, lean_object* v_fvarId_1351_, lean_object* v_generalizeNondepLet_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_){
_start:
{
uint8_t v_generalizeNondepLet_boxed_1355_; lean_object* v_res_1356_; 
v_generalizeNondepLet_boxed_1355_ = lean_unbox(v_generalizeNondepLet_1352_);
v_res_1356_ = l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg(v_localDecl_1350_, v_fvarId_1351_, v_generalizeNondepLet_boxed_1355_, v___y_1353_);
lean_dec(v___y_1353_);
return v_res_1356_;
}
}
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0(lean_object* v_localDecl_1357_, lean_object* v_fvarId_1358_, uint8_t v_generalizeNondepLet_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_){
_start:
{
lean_object* v___x_1365_; 
v___x_1365_ = l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg(v_localDecl_1357_, v_fvarId_1358_, v_generalizeNondepLet_1359_, v___y_1361_);
return v___x_1365_;
}
}
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___boxed(lean_object* v_localDecl_1366_, lean_object* v_fvarId_1367_, lean_object* v_generalizeNondepLet_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_){
_start:
{
uint8_t v_generalizeNondepLet_boxed_1374_; lean_object* v_res_1375_; 
v_generalizeNondepLet_boxed_1374_ = lean_unbox(v_generalizeNondepLet_1368_);
v_res_1375_ = l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0(v_localDecl_1366_, v_fvarId_1367_, v_generalizeNondepLet_boxed_1374_, v___y_1369_, v___y_1370_, v___y_1371_, v___y_1372_);
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
lean_object* v___x_1380_; uint8_t v_fst_1382_; lean_object* v_mctx_1383_; lean_object* v___y_1401_; lean_object* v_mctx_1406_; lean_object* v___f_1407_; lean_object* v___f_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; uint8_t v___x_1411_; 
v___x_1380_ = lean_st_ref_get(v___y_1378_);
v_mctx_1406_ = lean_ctor_get(v___x_1380_, 0);
lean_inc_ref_n(v_mctx_1406_, 2);
lean_dec(v___x_1380_);
v___f_1407_ = ((lean_object*)(l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__0));
v___f_1408_ = lean_alloc_closure((void*)(l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1408_, 0, v_fvarId_1377_);
v___x_1409_ = lean_obj_once(&l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__2, &l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__2_once, _init_l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__2);
v___x_1410_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1410_, 0, v___x_1409_);
lean_ctor_set(v___x_1410_, 1, v_mctx_1406_);
v___x_1411_ = l_Lean_Expr_hasFVar(v_e_1376_);
if (v___x_1411_ == 0)
{
uint8_t v___x_1412_; 
v___x_1412_ = l_Lean_Expr_hasMVar(v_e_1376_);
if (v___x_1412_ == 0)
{
lean_dec_ref(v___x_1410_);
lean_dec_ref(v___f_1408_);
lean_dec_ref(v_e_1376_);
v_fst_1382_ = v___x_1412_;
v_mctx_1383_ = v_mctx_1406_;
goto v___jp_1381_;
}
else
{
lean_object* v___x_1413_; 
lean_dec_ref(v_mctx_1406_);
v___x_1413_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1408_, v___f_1407_, v_e_1376_, v___x_1410_);
v___y_1401_ = v___x_1413_;
goto v___jp_1400_;
}
}
else
{
lean_object* v___x_1414_; 
lean_dec_ref(v_mctx_1406_);
v___x_1414_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1408_, v___f_1407_, v_e_1376_, v___x_1410_);
v___y_1401_ = v___x_1414_;
goto v___jp_1400_;
}
v___jp_1381_:
{
lean_object* v___x_1384_; lean_object* v_cache_1385_; lean_object* v_zetaDeltaFVarIds_1386_; lean_object* v_postponed_1387_; lean_object* v_diag_1388_; lean_object* v___x_1390_; uint8_t v_isShared_1391_; uint8_t v_isSharedCheck_1398_; 
v___x_1384_ = lean_st_ref_take(v___y_1378_);
v_cache_1385_ = lean_ctor_get(v___x_1384_, 1);
v_zetaDeltaFVarIds_1386_ = lean_ctor_get(v___x_1384_, 2);
v_postponed_1387_ = lean_ctor_get(v___x_1384_, 3);
v_diag_1388_ = lean_ctor_get(v___x_1384_, 4);
v_isSharedCheck_1398_ = !lean_is_exclusive(v___x_1384_);
if (v_isSharedCheck_1398_ == 0)
{
lean_object* v_unused_1399_; 
v_unused_1399_ = lean_ctor_get(v___x_1384_, 0);
lean_dec(v_unused_1399_);
v___x_1390_ = v___x_1384_;
v_isShared_1391_ = v_isSharedCheck_1398_;
goto v_resetjp_1389_;
}
else
{
lean_inc(v_diag_1388_);
lean_inc(v_postponed_1387_);
lean_inc(v_zetaDeltaFVarIds_1386_);
lean_inc(v_cache_1385_);
lean_dec(v___x_1384_);
v___x_1390_ = lean_box(0);
v_isShared_1391_ = v_isSharedCheck_1398_;
goto v_resetjp_1389_;
}
v_resetjp_1389_:
{
lean_object* v___x_1393_; 
if (v_isShared_1391_ == 0)
{
lean_ctor_set(v___x_1390_, 0, v_mctx_1383_);
v___x_1393_ = v___x_1390_;
goto v_reusejp_1392_;
}
else
{
lean_object* v_reuseFailAlloc_1397_; 
v_reuseFailAlloc_1397_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1397_, 0, v_mctx_1383_);
lean_ctor_set(v_reuseFailAlloc_1397_, 1, v_cache_1385_);
lean_ctor_set(v_reuseFailAlloc_1397_, 2, v_zetaDeltaFVarIds_1386_);
lean_ctor_set(v_reuseFailAlloc_1397_, 3, v_postponed_1387_);
lean_ctor_set(v_reuseFailAlloc_1397_, 4, v_diag_1388_);
v___x_1393_ = v_reuseFailAlloc_1397_;
goto v_reusejp_1392_;
}
v_reusejp_1392_:
{
lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; 
v___x_1394_ = lean_st_ref_set(v___y_1378_, v___x_1393_);
v___x_1395_ = lean_box(v_fst_1382_);
v___x_1396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1396_, 0, v___x_1395_);
return v___x_1396_;
}
}
}
v___jp_1400_:
{
lean_object* v_snd_1402_; lean_object* v_fst_1403_; lean_object* v_mctx_1404_; uint8_t v___x_1405_; 
v_snd_1402_ = lean_ctor_get(v___y_1401_, 1);
lean_inc(v_snd_1402_);
v_fst_1403_ = lean_ctor_get(v___y_1401_, 0);
lean_inc(v_fst_1403_);
lean_dec_ref(v___y_1401_);
v_mctx_1404_ = lean_ctor_get(v_snd_1402_, 1);
lean_inc_ref(v_mctx_1404_);
lean_dec(v_snd_1402_);
v___x_1405_ = lean_unbox(v_fst_1403_);
lean_dec(v_fst_1403_);
v_fst_1382_ = v___x_1405_;
v_mctx_1383_ = v_mctx_1404_;
goto v___jp_1381_;
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
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_Meta_getMajorTypeIndices_spec__1(lean_object* v_a_1436_, lean_object* v_x_1437_){
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
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_Meta_getMajorTypeIndices_spec__1___boxed(lean_object* v_a_1443_, lean_object* v_x_1444_){
_start:
{
uint8_t v_res_1445_; lean_object* v_r_1446_; 
v_res_1445_ = l_List_elem___at___00Lean_Meta_getMajorTypeIndices_spec__1(v_a_1443_, v_x_1444_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg(lean_object* v_majorTypeArgs_1459_, lean_object* v_idx_1460_, lean_object* v_tacticName_1461_, lean_object* v_mvarId_1462_, lean_object* v_idxPos_1463_, lean_object* v_recursorInfo_1464_, lean_object* v_majorType_1465_, lean_object* v_n_1466_, lean_object* v_i_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_){
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
lean_dec(v_mvarId_1462_);
lean_dec(v_tacticName_1461_);
lean_dec_ref(v_idx_1460_);
v___x_1475_ = lean_box(0);
v___x_1476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1476_, 0, v___x_1475_);
return v___x_1476_;
}
else
{
lean_object* v_one_1477_; lean_object* v_n_1478_; lean_object* v___y_1480_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v_arg_1484_; lean_object* v___y_1486_; lean_object* v___y_1487_; lean_object* v___y_1488_; lean_object* v___y_1489_; uint8_t v___y_1490_; lean_object* v___y_1529_; lean_object* v___y_1530_; lean_object* v___y_1531_; lean_object* v___y_1532_; lean_object* v___y_1537_; lean_object* v___y_1538_; lean_object* v___y_1539_; lean_object* v___y_1540_; uint8_t v___x_1561_; 
v_one_1477_ = lean_unsigned_to_nat(1u);
v_n_1478_ = lean_nat_sub(v_i_1467_, v_one_1477_);
lean_dec(v_i_1467_);
v___x_1482_ = lean_nat_sub(v_n_1466_, v_n_1478_);
v___x_1483_ = lean_nat_sub(v___x_1482_, v_one_1477_);
lean_dec(v___x_1482_);
v_arg_1484_ = lean_array_fget_borrowed(v_majorTypeArgs_1459_, v___x_1483_);
v___x_1561_ = lean_nat_dec_eq(v___x_1483_, v_idxPos_1463_);
if (v___x_1561_ == 0)
{
uint8_t v___x_1562_; 
v___x_1562_ = lean_expr_eqv(v_arg_1484_, v_idx_1460_);
if (v___x_1562_ == 0)
{
v___y_1537_ = v___y_1468_;
v___y_1538_ = v___y_1469_;
v___y_1539_ = v___y_1470_;
v___y_1540_ = v___y_1471_;
goto v___jp_1536_;
}
else
{
lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; 
v___x_1563_ = lean_obj_once(&l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1, &l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1_once, _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1);
lean_inc_ref(v_idx_1460_);
v___x_1564_ = l_Lean_MessageData_ofExpr(v_idx_1460_);
v___x_1565_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1565_, 0, v___x_1563_);
lean_ctor_set(v___x_1565_, 1, v___x_1564_);
v___x_1566_ = lean_obj_once(&l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__7, &l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__7_once, _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__7);
v___x_1567_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1567_, 0, v___x_1565_);
lean_ctor_set(v___x_1567_, 1, v___x_1566_);
lean_inc_ref(v_majorType_1465_);
v___x_1568_ = l_Lean_indentExpr(v_majorType_1465_);
v___x_1569_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1569_, 0, v___x_1567_);
lean_ctor_set(v___x_1569_, 1, v___x_1568_);
v___x_1570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1570_, 0, v___x_1569_);
lean_inc(v_mvarId_1462_);
lean_inc(v_tacticName_1461_);
v___x_1571_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1461_, v_mvarId_1462_, v___x_1570_, v___y_1468_, v___y_1469_, v___y_1470_, v___y_1471_);
if (lean_obj_tag(v___x_1571_) == 0)
{
lean_dec_ref(v___x_1571_);
v___y_1537_ = v___y_1468_;
v___y_1538_ = v___y_1469_;
v___y_1539_ = v___y_1470_;
v___y_1540_ = v___y_1471_;
goto v___jp_1536_;
}
else
{
lean_dec(v___x_1483_);
v___y_1480_ = v___x_1571_;
goto v___jp_1479_;
}
}
}
else
{
v___y_1537_ = v___y_1468_;
v___y_1538_ = v___y_1469_;
v___y_1539_ = v___y_1470_;
v___y_1540_ = v___y_1471_;
goto v___jp_1536_;
}
v___jp_1479_:
{
if (lean_obj_tag(v___y_1480_) == 0)
{
lean_dec_ref(v___y_1480_);
v_i_1467_ = v_n_1478_;
goto _start;
}
else
{
lean_dec(v_n_1478_);
lean_dec_ref(v_majorType_1465_);
lean_dec(v_mvarId_1462_);
lean_dec(v_tacticName_1461_);
lean_dec_ref(v_idx_1460_);
return v___y_1480_;
}
}
v___jp_1485_:
{
if (v___y_1490_ == 0)
{
lean_dec(v___x_1483_);
v_i_1467_ = v_n_1478_;
goto _start;
}
else
{
uint8_t v___x_1492_; 
v___x_1492_ = l_Lean_Expr_isFVar(v_arg_1484_);
if (v___x_1492_ == 0)
{
lean_dec(v___x_1483_);
v_i_1467_ = v_n_1478_;
goto _start;
}
else
{
lean_object* v___x_1494_; lean_object* v___x_1495_; 
v___x_1494_ = l_Lean_Expr_fvarId_x21(v_idx_1460_);
v___x_1495_ = l_Lean_FVarId_getDecl___redArg(v___x_1494_, v___y_1487_, v___y_1486_, v___y_1489_);
if (lean_obj_tag(v___x_1495_) == 0)
{
lean_object* v_a_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v_a_1499_; lean_object* v___x_1501_; uint8_t v_isShared_1502_; uint8_t v_isSharedCheck_1519_; 
v_a_1496_ = lean_ctor_get(v___x_1495_, 0);
lean_inc(v_a_1496_);
lean_dec_ref(v___x_1495_);
v___x_1497_ = l_Lean_Expr_fvarId_x21(v_arg_1484_);
v___x_1498_ = l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg(v_a_1496_, v___x_1497_, v___y_1490_, v___y_1488_);
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
lean_dec(v___x_1483_);
v_i_1467_ = v_n_1478_;
goto _start;
}
else
{
lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1513_; 
v___x_1505_ = lean_obj_once(&l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1, &l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1_once, _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1);
lean_inc_ref(v_idx_1460_);
v___x_1506_ = l_Lean_MessageData_ofExpr(v_idx_1460_);
v___x_1507_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1507_, 0, v___x_1505_);
lean_ctor_set(v___x_1507_, 1, v___x_1506_);
v___x_1508_ = lean_obj_once(&l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__3, &l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__3_once, _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__3);
v___x_1509_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1509_, 0, v___x_1507_);
lean_ctor_set(v___x_1509_, 1, v___x_1508_);
v___x_1510_ = lean_nat_add(v___x_1483_, v_one_1477_);
lean_dec(v___x_1483_);
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
lean_inc(v_mvarId_1462_);
lean_inc(v_tacticName_1461_);
v___x_1517_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1461_, v_mvarId_1462_, v___x_1516_, v___y_1487_, v___y_1488_, v___y_1486_, v___y_1489_);
v___y_1480_ = v___x_1517_;
goto v___jp_1479_;
}
}
}
}
else
{
lean_object* v_a_1520_; lean_object* v___x_1522_; uint8_t v_isShared_1523_; uint8_t v_isSharedCheck_1527_; 
lean_dec(v___x_1483_);
lean_dec(v_n_1478_);
lean_dec_ref(v_majorType_1465_);
lean_dec(v_mvarId_1462_);
lean_dec(v_tacticName_1461_);
lean_dec_ref(v_idx_1460_);
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
v___jp_1528_:
{
uint8_t v___x_1533_; 
v___x_1533_ = lean_nat_dec_lt(v_idxPos_1463_, v___x_1483_);
if (v___x_1533_ == 0)
{
v___y_1486_ = v___y_1531_;
v___y_1487_ = v___y_1529_;
v___y_1488_ = v___y_1530_;
v___y_1489_ = v___y_1532_;
v___y_1490_ = v___x_1533_;
goto v___jp_1485_;
}
else
{
lean_object* v_indicesPos_1534_; uint8_t v___x_1535_; 
v_indicesPos_1534_ = lean_ctor_get(v_recursorInfo_1464_, 6);
v___x_1535_ = l_List_elem___at___00Lean_Meta_getMajorTypeIndices_spec__1(v___x_1483_, v_indicesPos_1534_);
v___y_1486_ = v___y_1531_;
v___y_1487_ = v___y_1529_;
v___y_1488_ = v___y_1530_;
v___y_1489_ = v___y_1532_;
v___y_1490_ = v___x_1535_;
goto v___jp_1485_;
}
}
v___jp_1536_:
{
uint8_t v___x_1541_; 
v___x_1541_ = lean_nat_dec_lt(v___x_1483_, v_idxPos_1463_);
if (v___x_1541_ == 0)
{
v___y_1529_ = v___y_1537_;
v___y_1530_ = v___y_1538_;
v___y_1531_ = v___y_1539_;
v___y_1532_ = v___y_1540_;
goto v___jp_1528_;
}
else
{
lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v_a_1544_; lean_object* v___x_1546_; uint8_t v_isShared_1547_; uint8_t v_isSharedCheck_1560_; 
v___x_1542_ = l_Lean_Expr_fvarId_x21(v_idx_1460_);
lean_inc(v_arg_1484_);
v___x_1543_ = l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2___redArg(v_arg_1484_, v___x_1542_, v___y_1538_);
v_a_1544_ = lean_ctor_get(v___x_1543_, 0);
v_isSharedCheck_1560_ = !lean_is_exclusive(v___x_1543_);
if (v_isSharedCheck_1560_ == 0)
{
v___x_1546_ = v___x_1543_;
v_isShared_1547_ = v_isSharedCheck_1560_;
goto v_resetjp_1545_;
}
else
{
lean_inc(v_a_1544_);
lean_dec(v___x_1543_);
v___x_1546_ = lean_box(0);
v_isShared_1547_ = v_isSharedCheck_1560_;
goto v_resetjp_1545_;
}
v_resetjp_1545_:
{
uint8_t v___x_1548_; 
v___x_1548_ = lean_unbox(v_a_1544_);
lean_dec(v_a_1544_);
if (v___x_1548_ == 0)
{
lean_del_object(v___x_1546_);
v___y_1529_ = v___y_1537_;
v___y_1530_ = v___y_1538_;
v___y_1531_ = v___y_1539_;
v___y_1532_ = v___y_1540_;
goto v___jp_1528_;
}
else
{
lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1557_; 
v___x_1549_ = lean_obj_once(&l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1, &l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1_once, _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1);
lean_inc_ref(v_idx_1460_);
v___x_1550_ = l_Lean_MessageData_ofExpr(v_idx_1460_);
v___x_1551_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1551_, 0, v___x_1549_);
lean_ctor_set(v___x_1551_, 1, v___x_1550_);
v___x_1552_ = lean_obj_once(&l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__5, &l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__5_once, _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__5);
v___x_1553_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1553_, 0, v___x_1551_);
lean_ctor_set(v___x_1553_, 1, v___x_1552_);
lean_inc_ref(v_majorType_1465_);
v___x_1554_ = l_Lean_indentExpr(v_majorType_1465_);
v___x_1555_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1555_, 0, v___x_1553_);
lean_ctor_set(v___x_1555_, 1, v___x_1554_);
if (v_isShared_1547_ == 0)
{
lean_ctor_set_tag(v___x_1546_, 1);
lean_ctor_set(v___x_1546_, 0, v___x_1555_);
v___x_1557_ = v___x_1546_;
goto v_reusejp_1556_;
}
else
{
lean_object* v_reuseFailAlloc_1559_; 
v_reuseFailAlloc_1559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1559_, 0, v___x_1555_);
v___x_1557_ = v_reuseFailAlloc_1559_;
goto v_reusejp_1556_;
}
v_reusejp_1556_:
{
lean_object* v___x_1558_; 
lean_inc(v_mvarId_1462_);
lean_inc(v_tacticName_1461_);
v___x_1558_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1461_, v_mvarId_1462_, v___x_1557_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_);
if (lean_obj_tag(v___x_1558_) == 0)
{
lean_dec_ref(v___x_1558_);
v___y_1529_ = v___y_1537_;
v___y_1530_ = v___y_1538_;
v___y_1531_ = v___y_1539_;
v___y_1532_ = v___y_1540_;
goto v___jp_1528_;
}
else
{
lean_dec(v___x_1483_);
v___y_1480_ = v___x_1558_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___boxed(lean_object* v_majorTypeArgs_1572_, lean_object* v_idx_1573_, lean_object* v_tacticName_1574_, lean_object* v_mvarId_1575_, lean_object* v_idxPos_1576_, lean_object* v_recursorInfo_1577_, lean_object* v_majorType_1578_, lean_object* v_n_1579_, lean_object* v_i_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_){
_start:
{
lean_object* v_res_1586_; 
v_res_1586_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg(v_majorTypeArgs_1572_, v_idx_1573_, v_tacticName_1574_, v_mvarId_1575_, v_idxPos_1576_, v_recursorInfo_1577_, v_majorType_1578_, v_n_1579_, v_i_1580_, v___y_1581_, v___y_1582_, v___y_1583_, v___y_1584_);
lean_dec(v___y_1584_);
lean_dec_ref(v___y_1583_);
lean_dec(v___y_1582_);
lean_dec_ref(v___y_1581_);
lean_dec(v_n_1579_);
lean_dec_ref(v_recursorInfo_1577_);
lean_dec(v_idxPos_1576_);
lean_dec_ref(v_majorTypeArgs_1572_);
return v_res_1586_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__1(void){
_start:
{
lean_object* v___x_1588_; lean_object* v___x_1589_; 
v___x_1588_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__0));
v___x_1589_ = l_Lean_stringToMessageData(v___x_1588_);
return v___x_1589_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__3(void){
_start:
{
lean_object* v___x_1591_; lean_object* v___x_1592_; 
v___x_1591_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__2));
v___x_1592_ = l_Lean_stringToMessageData(v___x_1591_);
return v___x_1592_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__5(void){
_start:
{
lean_object* v___x_1594_; lean_object* v___x_1595_; 
v___x_1594_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__4));
v___x_1595_ = l_Lean_stringToMessageData(v___x_1594_);
return v___x_1595_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4(lean_object* v_majorTypeArgs_1596_, lean_object* v_tacticName_1597_, lean_object* v_mvarId_1598_, lean_object* v_recursorInfo_1599_, lean_object* v_majorType_1600_, size_t v_sz_1601_, size_t v_i_1602_, lean_object* v_bs_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_){
_start:
{
uint8_t v___x_1609_; 
v___x_1609_ = lean_usize_dec_lt(v_i_1602_, v_sz_1601_);
if (v___x_1609_ == 0)
{
lean_object* v___x_1610_; 
lean_dec_ref(v_majorType_1600_);
lean_dec(v_mvarId_1598_);
lean_dec(v_tacticName_1597_);
v___x_1610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1610_, 0, v_bs_1603_);
return v___x_1610_;
}
else
{
lean_object* v_v_1611_; lean_object* v___x_1612_; lean_object* v_bs_x27_1613_; lean_object* v_a_1615_; lean_object* v___x_1620_; uint8_t v___x_1621_; 
v_v_1611_ = lean_array_uget(v_bs_1603_, v_i_1602_);
v___x_1612_ = lean_unsigned_to_nat(0u);
v_bs_x27_1613_ = lean_array_uset(v_bs_1603_, v_i_1602_, v___x_1612_);
v___x_1620_ = lean_array_get_size(v_majorTypeArgs_1596_);
v___x_1621_ = lean_nat_dec_le(v___x_1620_, v_v_1611_);
if (v___x_1621_ == 0)
{
lean_object* v_idx_1622_; lean_object* v___y_1624_; lean_object* v___y_1625_; lean_object* v___y_1626_; lean_object* v___y_1627_; uint8_t v___x_1637_; 
v_idx_1622_ = lean_array_fget_borrowed(v_majorTypeArgs_1596_, v_v_1611_);
v___x_1637_ = l_Lean_Expr_isFVar(v_idx_1622_);
if (v___x_1637_ == 0)
{
lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; 
v___x_1638_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__1);
lean_inc(v_idx_1622_);
v___x_1639_ = l_Lean_MessageData_ofExpr(v_idx_1622_);
v___x_1640_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1640_, 0, v___x_1638_);
lean_ctor_set(v___x_1640_, 1, v___x_1639_);
v___x_1641_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__3);
v___x_1642_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1642_, 0, v___x_1640_);
lean_ctor_set(v___x_1642_, 1, v___x_1641_);
lean_inc_ref(v_majorType_1600_);
v___x_1643_ = l_Lean_indentExpr(v_majorType_1600_);
v___x_1644_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1644_, 0, v___x_1642_);
lean_ctor_set(v___x_1644_, 1, v___x_1643_);
v___x_1645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1645_, 0, v___x_1644_);
lean_inc(v_mvarId_1598_);
lean_inc(v_tacticName_1597_);
v___x_1646_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1597_, v_mvarId_1598_, v___x_1645_, v___y_1604_, v___y_1605_, v___y_1606_, v___y_1607_);
if (lean_obj_tag(v___x_1646_) == 0)
{
lean_dec_ref(v___x_1646_);
v___y_1624_ = v___y_1604_;
v___y_1625_ = v___y_1605_;
v___y_1626_ = v___y_1606_;
v___y_1627_ = v___y_1607_;
goto v___jp_1623_;
}
else
{
lean_object* v_a_1647_; lean_object* v___x_1649_; uint8_t v_isShared_1650_; uint8_t v_isSharedCheck_1654_; 
lean_dec_ref(v_bs_x27_1613_);
lean_dec(v_v_1611_);
lean_dec_ref(v_majorType_1600_);
lean_dec(v_mvarId_1598_);
lean_dec(v_tacticName_1597_);
v_a_1647_ = lean_ctor_get(v___x_1646_, 0);
v_isSharedCheck_1654_ = !lean_is_exclusive(v___x_1646_);
if (v_isSharedCheck_1654_ == 0)
{
v___x_1649_ = v___x_1646_;
v_isShared_1650_ = v_isSharedCheck_1654_;
goto v_resetjp_1648_;
}
else
{
lean_inc(v_a_1647_);
lean_dec(v___x_1646_);
v___x_1649_ = lean_box(0);
v_isShared_1650_ = v_isSharedCheck_1654_;
goto v_resetjp_1648_;
}
v_resetjp_1648_:
{
lean_object* v___x_1652_; 
if (v_isShared_1650_ == 0)
{
v___x_1652_ = v___x_1649_;
goto v_reusejp_1651_;
}
else
{
lean_object* v_reuseFailAlloc_1653_; 
v_reuseFailAlloc_1653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1653_, 0, v_a_1647_);
v___x_1652_ = v_reuseFailAlloc_1653_;
goto v_reusejp_1651_;
}
v_reusejp_1651_:
{
return v___x_1652_;
}
}
}
}
else
{
v___y_1624_ = v___y_1604_;
v___y_1625_ = v___y_1605_;
v___y_1626_ = v___y_1606_;
v___y_1627_ = v___y_1607_;
goto v___jp_1623_;
}
v___jp_1623_:
{
lean_object* v___x_1628_; 
lean_inc_ref(v_majorType_1600_);
lean_inc(v_mvarId_1598_);
lean_inc(v_tacticName_1597_);
lean_inc(v_idx_1622_);
v___x_1628_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg(v_majorTypeArgs_1596_, v_idx_1622_, v_tacticName_1597_, v_mvarId_1598_, v_v_1611_, v_recursorInfo_1599_, v_majorType_1600_, v___x_1620_, v___x_1620_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_);
lean_dec(v_v_1611_);
if (lean_obj_tag(v___x_1628_) == 0)
{
lean_dec_ref(v___x_1628_);
lean_inc(v_idx_1622_);
v_a_1615_ = v_idx_1622_;
goto v___jp_1614_;
}
else
{
lean_object* v_a_1629_; lean_object* v___x_1631_; uint8_t v_isShared_1632_; uint8_t v_isSharedCheck_1636_; 
lean_dec_ref(v_bs_x27_1613_);
lean_dec_ref(v_majorType_1600_);
lean_dec(v_mvarId_1598_);
lean_dec(v_tacticName_1597_);
v_a_1629_ = lean_ctor_get(v___x_1628_, 0);
v_isSharedCheck_1636_ = !lean_is_exclusive(v___x_1628_);
if (v_isSharedCheck_1636_ == 0)
{
v___x_1631_ = v___x_1628_;
v_isShared_1632_ = v_isSharedCheck_1636_;
goto v_resetjp_1630_;
}
else
{
lean_inc(v_a_1629_);
lean_dec(v___x_1628_);
v___x_1631_ = lean_box(0);
v_isShared_1632_ = v_isSharedCheck_1636_;
goto v_resetjp_1630_;
}
v_resetjp_1630_:
{
lean_object* v___x_1634_; 
if (v_isShared_1632_ == 0)
{
v___x_1634_ = v___x_1631_;
goto v_reusejp_1633_;
}
else
{
lean_object* v_reuseFailAlloc_1635_; 
v_reuseFailAlloc_1635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1635_, 0, v_a_1629_);
v___x_1634_ = v_reuseFailAlloc_1635_;
goto v_reusejp_1633_;
}
v_reusejp_1633_:
{
return v___x_1634_;
}
}
}
}
}
else
{
lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; 
lean_dec(v_v_1611_);
v___x_1655_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__5, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__5);
lean_inc_ref(v_majorType_1600_);
v___x_1656_ = l_Lean_indentExpr(v_majorType_1600_);
v___x_1657_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1657_, 0, v___x_1655_);
lean_ctor_set(v___x_1657_, 1, v___x_1656_);
v___x_1658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1658_, 0, v___x_1657_);
lean_inc(v_mvarId_1598_);
lean_inc(v_tacticName_1597_);
v___x_1659_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1597_, v_mvarId_1598_, v___x_1658_, v___y_1604_, v___y_1605_, v___y_1606_, v___y_1607_);
if (lean_obj_tag(v___x_1659_) == 0)
{
lean_object* v_a_1660_; 
v_a_1660_ = lean_ctor_get(v___x_1659_, 0);
lean_inc(v_a_1660_);
lean_dec_ref(v___x_1659_);
v_a_1615_ = v_a_1660_;
goto v___jp_1614_;
}
else
{
lean_object* v_a_1661_; lean_object* v___x_1663_; uint8_t v_isShared_1664_; uint8_t v_isSharedCheck_1668_; 
lean_dec_ref(v_bs_x27_1613_);
lean_dec_ref(v_majorType_1600_);
lean_dec(v_mvarId_1598_);
lean_dec(v_tacticName_1597_);
v_a_1661_ = lean_ctor_get(v___x_1659_, 0);
v_isSharedCheck_1668_ = !lean_is_exclusive(v___x_1659_);
if (v_isSharedCheck_1668_ == 0)
{
v___x_1663_ = v___x_1659_;
v_isShared_1664_ = v_isSharedCheck_1668_;
goto v_resetjp_1662_;
}
else
{
lean_inc(v_a_1661_);
lean_dec(v___x_1659_);
v___x_1663_ = lean_box(0);
v_isShared_1664_ = v_isSharedCheck_1668_;
goto v_resetjp_1662_;
}
v_resetjp_1662_:
{
lean_object* v___x_1666_; 
if (v_isShared_1664_ == 0)
{
v___x_1666_ = v___x_1663_;
goto v_reusejp_1665_;
}
else
{
lean_object* v_reuseFailAlloc_1667_; 
v_reuseFailAlloc_1667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1667_, 0, v_a_1661_);
v___x_1666_ = v_reuseFailAlloc_1667_;
goto v_reusejp_1665_;
}
v_reusejp_1665_:
{
return v___x_1666_;
}
}
}
}
v___jp_1614_:
{
size_t v___x_1616_; size_t v___x_1617_; lean_object* v___x_1618_; 
v___x_1616_ = ((size_t)1ULL);
v___x_1617_ = lean_usize_add(v_i_1602_, v___x_1616_);
v___x_1618_ = lean_array_uset(v_bs_x27_1613_, v_i_1602_, v_a_1615_);
v_i_1602_ = v___x_1617_;
v_bs_1603_ = v___x_1618_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___boxed(lean_object* v_majorTypeArgs_1669_, lean_object* v_tacticName_1670_, lean_object* v_mvarId_1671_, lean_object* v_recursorInfo_1672_, lean_object* v_majorType_1673_, lean_object* v_sz_1674_, lean_object* v_i_1675_, lean_object* v_bs_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_){
_start:
{
size_t v_sz_boxed_1682_; size_t v_i_boxed_1683_; lean_object* v_res_1684_; 
v_sz_boxed_1682_ = lean_unbox_usize(v_sz_1674_);
lean_dec(v_sz_1674_);
v_i_boxed_1683_ = lean_unbox_usize(v_i_1675_);
lean_dec(v_i_1675_);
v_res_1684_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4(v_majorTypeArgs_1669_, v_tacticName_1670_, v_mvarId_1671_, v_recursorInfo_1672_, v_majorType_1673_, v_sz_boxed_1682_, v_i_boxed_1683_, v_bs_1676_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_);
lean_dec(v___y_1680_);
lean_dec_ref(v___y_1679_);
lean_dec(v___y_1678_);
lean_dec_ref(v___y_1677_);
lean_dec_ref(v_recursorInfo_1672_);
lean_dec_ref(v_majorTypeArgs_1669_);
return v_res_1684_;
}
}
static lean_object* _init_l_Lean_Meta_getMajorTypeIndices___closed__0(void){
_start:
{
lean_object* v___x_1685_; lean_object* v_dummy_1686_; 
v___x_1685_ = lean_box(0);
v_dummy_1686_ = l_Lean_Expr_sort___override(v___x_1685_);
return v_dummy_1686_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMajorTypeIndices(lean_object* v_mvarId_1687_, lean_object* v_tacticName_1688_, lean_object* v_recursorInfo_1689_, lean_object* v_majorType_1690_, lean_object* v_a_1691_, lean_object* v_a_1692_, lean_object* v_a_1693_, lean_object* v_a_1694_){
_start:
{
lean_object* v_indicesPos_1696_; lean_object* v_nargs_1697_; lean_object* v_dummy_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v_majorTypeArgs_1702_; lean_object* v___x_1703_; size_t v_sz_1704_; size_t v___x_1705_; lean_object* v___x_1706_; 
v_indicesPos_1696_ = lean_ctor_get(v_recursorInfo_1689_, 6);
v_nargs_1697_ = l_Lean_Expr_getAppNumArgs(v_majorType_1690_);
v_dummy_1698_ = lean_obj_once(&l_Lean_Meta_getMajorTypeIndices___closed__0, &l_Lean_Meta_getMajorTypeIndices___closed__0_once, _init_l_Lean_Meta_getMajorTypeIndices___closed__0);
lean_inc(v_nargs_1697_);
v___x_1699_ = lean_mk_array(v_nargs_1697_, v_dummy_1698_);
v___x_1700_ = lean_unsigned_to_nat(1u);
v___x_1701_ = lean_nat_sub(v_nargs_1697_, v___x_1700_);
lean_dec(v_nargs_1697_);
lean_inc_ref(v_majorType_1690_);
v_majorTypeArgs_1702_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_majorType_1690_, v___x_1699_, v___x_1701_);
lean_inc(v_indicesPos_1696_);
v___x_1703_ = lean_array_mk(v_indicesPos_1696_);
v_sz_1704_ = lean_array_size(v___x_1703_);
v___x_1705_ = ((size_t)0ULL);
v___x_1706_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4(v_majorTypeArgs_1702_, v_tacticName_1688_, v_mvarId_1687_, v_recursorInfo_1689_, v_majorType_1690_, v_sz_1704_, v___x_1705_, v___x_1703_, v_a_1691_, v_a_1692_, v_a_1693_, v_a_1694_);
lean_dec_ref(v_recursorInfo_1689_);
lean_dec_ref(v_majorTypeArgs_1702_);
return v___x_1706_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMajorTypeIndices___boxed(lean_object* v_mvarId_1707_, lean_object* v_tacticName_1708_, lean_object* v_recursorInfo_1709_, lean_object* v_majorType_1710_, lean_object* v_a_1711_, lean_object* v_a_1712_, lean_object* v_a_1713_, lean_object* v_a_1714_, lean_object* v_a_1715_){
_start:
{
lean_object* v_res_1716_; 
v_res_1716_ = l_Lean_Meta_getMajorTypeIndices(v_mvarId_1707_, v_tacticName_1708_, v_recursorInfo_1709_, v_majorType_1710_, v_a_1711_, v_a_1712_, v_a_1713_, v_a_1714_);
lean_dec(v_a_1714_);
lean_dec_ref(v_a_1713_);
lean_dec(v_a_1712_);
lean_dec_ref(v_a_1711_);
return v_res_1716_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3(lean_object* v_majorTypeArgs_1717_, lean_object* v_idx_1718_, lean_object* v_tacticName_1719_, lean_object* v_mvarId_1720_, lean_object* v_idxPos_1721_, lean_object* v_recursorInfo_1722_, lean_object* v_majorType_1723_, lean_object* v_n_1724_, lean_object* v_i_1725_, lean_object* v_a_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_){
_start:
{
lean_object* v___x_1732_; 
v___x_1732_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg(v_majorTypeArgs_1717_, v_idx_1718_, v_tacticName_1719_, v_mvarId_1720_, v_idxPos_1721_, v_recursorInfo_1722_, v_majorType_1723_, v_n_1724_, v_i_1725_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_);
return v___x_1732_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___boxed(lean_object* v_majorTypeArgs_1733_, lean_object* v_idx_1734_, lean_object* v_tacticName_1735_, lean_object* v_mvarId_1736_, lean_object* v_idxPos_1737_, lean_object* v_recursorInfo_1738_, lean_object* v_majorType_1739_, lean_object* v_n_1740_, lean_object* v_i_1741_, lean_object* v_a_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_){
_start:
{
lean_object* v_res_1748_; 
v_res_1748_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3(v_majorTypeArgs_1733_, v_idx_1734_, v_tacticName_1735_, v_mvarId_1736_, v_idxPos_1737_, v_recursorInfo_1738_, v_majorType_1739_, v_n_1740_, v_i_1741_, v_a_1742_, v___y_1743_, v___y_1744_, v___y_1745_, v___y_1746_);
lean_dec(v___y_1746_);
lean_dec_ref(v___y_1745_);
lean_dec(v___y_1744_);
lean_dec_ref(v___y_1743_);
lean_dec(v_n_1740_);
lean_dec_ref(v_recursorInfo_1738_);
lean_dec(v_idxPos_1737_);
lean_dec_ref(v_majorTypeArgs_1733_);
return v_res_1748_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1___redArg(lean_object* v_name_1749_, lean_object* v_msg_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_){
_start:
{
lean_object* v_ref_1756_; lean_object* v_msg_1757_; lean_object* v___x_1758_; lean_object* v_a_1759_; lean_object* v___x_1761_; uint8_t v_isShared_1762_; uint8_t v_isSharedCheck_1767_; 
v_ref_1756_ = lean_ctor_get(v___y_1753_, 5);
v_msg_1757_ = l_Lean_MessageData_tagWithErrorName(v_msg_1750_, v_name_1749_);
v___x_1758_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1_spec__2(v_msg_1757_, v___y_1751_, v___y_1752_, v___y_1753_, v___y_1754_);
v_a_1759_ = lean_ctor_get(v___x_1758_, 0);
v_isSharedCheck_1767_ = !lean_is_exclusive(v___x_1758_);
if (v_isSharedCheck_1767_ == 0)
{
v___x_1761_ = v___x_1758_;
v_isShared_1762_ = v_isSharedCheck_1767_;
goto v_resetjp_1760_;
}
else
{
lean_inc(v_a_1759_);
lean_dec(v___x_1758_);
v___x_1761_ = lean_box(0);
v_isShared_1762_ = v_isSharedCheck_1767_;
goto v_resetjp_1760_;
}
v_resetjp_1760_:
{
lean_object* v___x_1763_; lean_object* v___x_1765_; 
lean_inc(v_ref_1756_);
v___x_1763_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1763_, 0, v_ref_1756_);
lean_ctor_set(v___x_1763_, 1, v_a_1759_);
if (v_isShared_1762_ == 0)
{
lean_ctor_set_tag(v___x_1761_, 1);
lean_ctor_set(v___x_1761_, 0, v___x_1763_);
v___x_1765_ = v___x_1761_;
goto v_reusejp_1764_;
}
else
{
lean_object* v_reuseFailAlloc_1766_; 
v_reuseFailAlloc_1766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1766_, 0, v___x_1763_);
v___x_1765_ = v_reuseFailAlloc_1766_;
goto v_reusejp_1764_;
}
v_reusejp_1764_:
{
return v___x_1765_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1___redArg___boxed(lean_object* v_name_1768_, lean_object* v_msg_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_){
_start:
{
lean_object* v_res_1775_; 
v_res_1775_ = l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1___redArg(v_name_1768_, v_msg_1769_, v___y_1770_, v___y_1771_, v___y_1772_, v___y_1773_);
lean_dec(v___y_1773_);
lean_dec_ref(v___y_1772_);
lean_dec(v___y_1771_);
lean_dec_ref(v___y_1770_);
return v_res_1775_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Meta_mkRecursorAppPrefix_spec__0(lean_object* v_a_1776_, lean_object* v___x_1777_, lean_object* v_tacticName_1778_, lean_object* v_mvarId_1779_, lean_object* v_x_1780_, lean_object* v_x_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_){
_start:
{
if (lean_obj_tag(v_x_1781_) == 0)
{
lean_object* v___x_1787_; 
lean_dec(v_mvarId_1779_);
lean_dec(v_tacticName_1778_);
lean_dec(v_a_1776_);
v___x_1787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1787_, 0, v_x_1780_);
return v___x_1787_;
}
else
{
lean_object* v_head_1788_; 
v_head_1788_ = lean_ctor_get(v_x_1781_, 0);
if (lean_obj_tag(v_head_1788_) == 0)
{
lean_object* v_tail_1789_; lean_object* v_fst_1790_; lean_object* v___x_1792_; uint8_t v_isShared_1793_; uint8_t v_isSharedCheck_1801_; 
v_tail_1789_ = lean_ctor_get(v_x_1781_, 1);
v_fst_1790_ = lean_ctor_get(v_x_1780_, 0);
v_isSharedCheck_1801_ = !lean_is_exclusive(v_x_1780_);
if (v_isSharedCheck_1801_ == 0)
{
lean_object* v_unused_1802_; 
v_unused_1802_ = lean_ctor_get(v_x_1780_, 1);
lean_dec(v_unused_1802_);
v___x_1792_ = v_x_1780_;
v_isShared_1793_ = v_isSharedCheck_1801_;
goto v_resetjp_1791_;
}
else
{
lean_inc(v_fst_1790_);
lean_dec(v_x_1780_);
v___x_1792_ = lean_box(0);
v_isShared_1793_ = v_isSharedCheck_1801_;
goto v_resetjp_1791_;
}
v_resetjp_1791_:
{
lean_object* v___x_1794_; uint8_t v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1798_; 
lean_inc(v_a_1776_);
v___x_1794_ = lean_array_push(v_fst_1790_, v_a_1776_);
v___x_1795_ = 1;
v___x_1796_ = lean_box(v___x_1795_);
if (v_isShared_1793_ == 0)
{
lean_ctor_set(v___x_1792_, 1, v___x_1796_);
lean_ctor_set(v___x_1792_, 0, v___x_1794_);
v___x_1798_ = v___x_1792_;
goto v_reusejp_1797_;
}
else
{
lean_object* v_reuseFailAlloc_1800_; 
v_reuseFailAlloc_1800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1800_, 0, v___x_1794_);
lean_ctor_set(v_reuseFailAlloc_1800_, 1, v___x_1796_);
v___x_1798_ = v_reuseFailAlloc_1800_;
goto v_reusejp_1797_;
}
v_reusejp_1797_:
{
v_x_1780_ = v___x_1798_;
v_x_1781_ = v_tail_1789_;
goto _start;
}
}
}
else
{
lean_object* v_tail_1803_; lean_object* v_fst_1804_; lean_object* v_snd_1805_; lean_object* v___x_1807_; uint8_t v_isShared_1808_; uint8_t v_isSharedCheck_1822_; 
v_tail_1803_ = lean_ctor_get(v_x_1781_, 1);
v_fst_1804_ = lean_ctor_get(v_x_1780_, 0);
v_snd_1805_ = lean_ctor_get(v_x_1780_, 1);
v_isSharedCheck_1822_ = !lean_is_exclusive(v_x_1780_);
if (v_isSharedCheck_1822_ == 0)
{
v___x_1807_ = v_x_1780_;
v_isShared_1808_ = v_isSharedCheck_1822_;
goto v_resetjp_1806_;
}
else
{
lean_inc(v_snd_1805_);
lean_inc(v_fst_1804_);
lean_dec(v_x_1780_);
v___x_1807_ = lean_box(0);
v_isShared_1808_ = v_isSharedCheck_1822_;
goto v_resetjp_1806_;
}
v_resetjp_1806_:
{
lean_object* v_idx_1809_; lean_object* v___x_1810_; uint8_t v___x_1811_; 
v_idx_1809_ = lean_ctor_get(v_head_1788_, 0);
v___x_1810_ = lean_array_get_size(v___x_1777_);
v___x_1811_ = lean_nat_dec_le(v___x_1810_, v_idx_1809_);
if (v___x_1811_ == 0)
{
lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1815_; 
v___x_1812_ = lean_array_fget_borrowed(v___x_1777_, v_idx_1809_);
lean_inc(v___x_1812_);
v___x_1813_ = lean_array_push(v_fst_1804_, v___x_1812_);
if (v_isShared_1808_ == 0)
{
lean_ctor_set(v___x_1807_, 0, v___x_1813_);
v___x_1815_ = v___x_1807_;
goto v_reusejp_1814_;
}
else
{
lean_object* v_reuseFailAlloc_1817_; 
v_reuseFailAlloc_1817_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1817_, 0, v___x_1813_);
lean_ctor_set(v_reuseFailAlloc_1817_, 1, v_snd_1805_);
v___x_1815_ = v_reuseFailAlloc_1817_;
goto v_reusejp_1814_;
}
v_reusejp_1814_:
{
v_x_1780_ = v___x_1815_;
v_x_1781_ = v_tail_1803_;
goto _start;
}
}
else
{
lean_object* v___x_1818_; lean_object* v___x_1819_; 
lean_del_object(v___x_1807_);
lean_dec(v_snd_1805_);
lean_dec(v_fst_1804_);
v___x_1818_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9);
lean_inc(v_mvarId_1779_);
lean_inc(v_tacticName_1778_);
v___x_1819_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1778_, v_mvarId_1779_, v___x_1818_, v___y_1782_, v___y_1783_, v___y_1784_, v___y_1785_);
if (lean_obj_tag(v___x_1819_) == 0)
{
lean_object* v_a_1820_; 
v_a_1820_ = lean_ctor_get(v___x_1819_, 0);
lean_inc(v_a_1820_);
lean_dec_ref(v___x_1819_);
v_x_1780_ = v_a_1820_;
v_x_1781_ = v_tail_1803_;
goto _start;
}
else
{
lean_dec(v_mvarId_1779_);
lean_dec(v_tacticName_1778_);
lean_dec(v_a_1776_);
return v___x_1819_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Meta_mkRecursorAppPrefix_spec__0___boxed(lean_object* v_a_1823_, lean_object* v___x_1824_, lean_object* v_tacticName_1825_, lean_object* v_mvarId_1826_, lean_object* v_x_1827_, lean_object* v_x_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_){
_start:
{
lean_object* v_res_1834_; 
v_res_1834_ = l_List_foldlM___at___00Lean_Meta_mkRecursorAppPrefix_spec__0(v_a_1823_, v___x_1824_, v_tacticName_1825_, v_mvarId_1826_, v_x_1827_, v_x_1828_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_);
lean_dec(v___y_1832_);
lean_dec_ref(v___y_1831_);
lean_dec(v___y_1830_);
lean_dec_ref(v___y_1829_);
lean_dec(v_x_1828_);
lean_dec_ref(v___x_1824_);
return v_res_1834_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__8(void){
_start:
{
lean_object* v___x_1850_; lean_object* v___x_1851_; 
v___x_1850_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__7));
v___x_1851_ = l_Lean_stringToMessageData(v___x_1850_);
return v___x_1851_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__10(void){
_start:
{
lean_object* v___x_1853_; lean_object* v___x_1854_; 
v___x_1853_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__9));
v___x_1854_ = l_Lean_stringToMessageData(v___x_1853_);
return v___x_1854_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__13(void){
_start:
{
lean_object* v___x_1858_; lean_object* v___x_1859_; 
v___x_1858_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__12));
v___x_1859_ = l_Lean_MessageData_ofFormat(v___x_1858_);
return v___x_1859_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__14(void){
_start:
{
lean_object* v___x_1860_; lean_object* v___x_1861_; 
v___x_1860_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__13, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__13_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__13);
v___x_1861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1861_, 0, v___x_1860_);
return v___x_1861_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2(lean_object* v_recursorInfo_1862_, lean_object* v_a_1863_, lean_object* v_tacticName_1864_, lean_object* v_mvarId_1865_, lean_object* v_indices_1866_, lean_object* v_a_1867_, lean_object* v_major_1868_, lean_object* v_x_1869_, lean_object* v_x_1870_, lean_object* v_x_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_){
_start:
{
if (lean_obj_tag(v_x_1869_) == 5)
{
lean_object* v_fn_1877_; lean_object* v_arg_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; 
v_fn_1877_ = lean_ctor_get(v_x_1869_, 0);
lean_inc_ref(v_fn_1877_);
v_arg_1878_ = lean_ctor_get(v_x_1869_, 1);
lean_inc_ref(v_arg_1878_);
lean_dec_ref(v_x_1869_);
v___x_1879_ = lean_array_set(v_x_1870_, v_x_1871_, v_arg_1878_);
v___x_1880_ = lean_unsigned_to_nat(1u);
v___x_1881_ = lean_nat_sub(v_x_1871_, v___x_1880_);
lean_dec(v_x_1871_);
v_x_1869_ = v_fn_1877_;
v_x_1870_ = v___x_1879_;
v_x_1871_ = v___x_1881_;
goto _start;
}
else
{
lean_dec(v_x_1871_);
if (lean_obj_tag(v_x_1869_) == 4)
{
lean_object* v_us_1883_; lean_object* v_recursorName_1884_; lean_object* v_univLevelPos_1885_; uint8_t v_depElim_1886_; lean_object* v_paramsPos_1887_; lean_object* v___x_1888_; uint8_t v___x_1889_; lean_object* v___y_1891_; lean_object* v_motive_1892_; lean_object* v___y_1893_; lean_object* v___y_1894_; lean_object* v___y_1895_; lean_object* v___y_1896_; lean_object* v___x_1909_; lean_object* v___x_1910_; 
v_us_1883_ = lean_ctor_get(v_x_1869_, 1);
lean_inc(v_us_1883_);
lean_dec_ref(v_x_1869_);
v_recursorName_1884_ = lean_ctor_get(v_recursorInfo_1862_, 0);
lean_inc(v_recursorName_1884_);
v_univLevelPos_1885_ = lean_ctor_get(v_recursorInfo_1862_, 2);
lean_inc(v_univLevelPos_1885_);
v_depElim_1886_ = lean_ctor_get_uint8(v_recursorInfo_1862_, sizeof(void*)*8);
v_paramsPos_1887_ = lean_ctor_get(v_recursorInfo_1862_, 5);
lean_inc(v_paramsPos_1887_);
lean_dec_ref(v_recursorInfo_1862_);
v___x_1888_ = lean_array_mk(v_us_1883_);
v___x_1889_ = 0;
v___x_1909_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__1));
lean_inc(v_mvarId_1865_);
lean_inc(v_tacticName_1864_);
lean_inc(v_a_1863_);
v___x_1910_ = l_List_foldlM___at___00Lean_Meta_mkRecursorAppPrefix_spec__0(v_a_1863_, v___x_1888_, v_tacticName_1864_, v_mvarId_1865_, v___x_1909_, v_univLevelPos_1885_, v___y_1872_, v___y_1873_, v___y_1874_, v___y_1875_);
lean_dec(v_univLevelPos_1885_);
lean_dec_ref(v___x_1888_);
if (lean_obj_tag(v___x_1910_) == 0)
{
lean_object* v_a_1911_; lean_object* v_fst_1912_; lean_object* v_snd_1913_; lean_object* v___x_1915_; uint8_t v_isShared_1916_; uint8_t v_isSharedCheck_1957_; 
v_a_1911_ = lean_ctor_get(v___x_1910_, 0);
lean_inc(v_a_1911_);
lean_dec_ref(v___x_1910_);
v_fst_1912_ = lean_ctor_get(v_a_1911_, 0);
v_snd_1913_ = lean_ctor_get(v_a_1911_, 1);
v_isSharedCheck_1957_ = !lean_is_exclusive(v_a_1911_);
if (v_isSharedCheck_1957_ == 0)
{
v___x_1915_ = v_a_1911_;
v_isShared_1916_ = v_isSharedCheck_1957_;
goto v_resetjp_1914_;
}
else
{
lean_inc(v_snd_1913_);
lean_inc(v_fst_1912_);
lean_dec(v_a_1911_);
v___x_1915_ = lean_box(0);
v_isShared_1916_ = v_isSharedCheck_1957_;
goto v_resetjp_1914_;
}
v_resetjp_1914_:
{
lean_object* v___y_1918_; lean_object* v___y_1919_; lean_object* v___y_1920_; lean_object* v___y_1921_; uint8_t v___x_1937_; 
v___x_1937_ = lean_unbox(v_snd_1913_);
lean_dec(v_snd_1913_);
if (v___x_1937_ == 0)
{
uint8_t v___x_1938_; 
v___x_1938_ = l_Lean_Level_isZero(v_a_1863_);
lean_dec(v_a_1863_);
if (v___x_1938_ == 0)
{
lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1943_; 
lean_dec(v_fst_1912_);
lean_dec(v_paramsPos_1887_);
lean_dec_ref(v_x_1870_);
lean_dec_ref(v_major_1868_);
lean_dec_ref(v_a_1867_);
v___x_1939_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__6));
v___x_1940_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__8, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__8_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__8);
v___x_1941_ = l_Lean_MessageData_ofName(v_recursorName_1884_);
if (v_isShared_1916_ == 0)
{
lean_ctor_set_tag(v___x_1915_, 7);
lean_ctor_set(v___x_1915_, 1, v___x_1941_);
lean_ctor_set(v___x_1915_, 0, v___x_1940_);
v___x_1943_ = v___x_1915_;
goto v_reusejp_1942_;
}
else
{
lean_object* v_reuseFailAlloc_1956_; 
v_reuseFailAlloc_1956_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1956_, 0, v___x_1940_);
lean_ctor_set(v_reuseFailAlloc_1956_, 1, v___x_1941_);
v___x_1943_ = v_reuseFailAlloc_1956_;
goto v_reusejp_1942_;
}
v_reusejp_1942_:
{
lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v_a_1948_; lean_object* v___x_1950_; uint8_t v_isShared_1951_; uint8_t v_isSharedCheck_1955_; 
v___x_1944_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__10, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__10_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__10);
v___x_1945_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1945_, 0, v___x_1943_);
lean_ctor_set(v___x_1945_, 1, v___x_1944_);
v___x_1946_ = l_Lean_Meta_mkTacticExMsg(v_tacticName_1864_, v_mvarId_1865_, v___x_1945_);
v___x_1947_ = l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1___redArg(v___x_1939_, v___x_1946_, v___y_1872_, v___y_1873_, v___y_1874_, v___y_1875_);
v_a_1948_ = lean_ctor_get(v___x_1947_, 0);
v_isSharedCheck_1955_ = !lean_is_exclusive(v___x_1947_);
if (v_isSharedCheck_1955_ == 0)
{
v___x_1950_ = v___x_1947_;
v_isShared_1951_ = v_isSharedCheck_1955_;
goto v_resetjp_1949_;
}
else
{
lean_inc(v_a_1948_);
lean_dec(v___x_1947_);
v___x_1950_ = lean_box(0);
v_isShared_1951_ = v_isSharedCheck_1955_;
goto v_resetjp_1949_;
}
v_resetjp_1949_:
{
lean_object* v___x_1953_; 
if (v_isShared_1951_ == 0)
{
v___x_1953_ = v___x_1950_;
goto v_reusejp_1952_;
}
else
{
lean_object* v_reuseFailAlloc_1954_; 
v_reuseFailAlloc_1954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1954_, 0, v_a_1948_);
v___x_1953_ = v_reuseFailAlloc_1954_;
goto v_reusejp_1952_;
}
v_reusejp_1952_:
{
return v___x_1953_;
}
}
}
}
else
{
lean_del_object(v___x_1915_);
lean_dec(v_tacticName_1864_);
v___y_1918_ = v___y_1872_;
v___y_1919_ = v___y_1873_;
v___y_1920_ = v___y_1874_;
v___y_1921_ = v___y_1875_;
goto v___jp_1917_;
}
}
else
{
lean_del_object(v___x_1915_);
lean_dec(v_tacticName_1864_);
lean_dec(v_a_1863_);
v___y_1918_ = v___y_1872_;
v___y_1919_ = v___y_1873_;
v___y_1920_ = v___y_1874_;
v___y_1921_ = v___y_1875_;
goto v___jp_1917_;
}
v___jp_1917_:
{
lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; 
v___x_1922_ = lean_array_to_list(v_fst_1912_);
v___x_1923_ = l_Lean_mkConst(v_recursorName_1884_, v___x_1922_);
v___x_1924_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams(v_mvarId_1865_, v_x_1870_, v_paramsPos_1887_, v___x_1923_, v___y_1918_, v___y_1919_, v___y_1920_, v___y_1921_);
lean_dec_ref(v_x_1870_);
if (lean_obj_tag(v___x_1924_) == 0)
{
if (v_depElim_1886_ == 0)
{
lean_object* v_a_1925_; 
lean_dec_ref(v_major_1868_);
v_a_1925_ = lean_ctor_get(v___x_1924_, 0);
lean_inc(v_a_1925_);
lean_dec_ref(v___x_1924_);
v___y_1891_ = v_a_1925_;
v_motive_1892_ = v_a_1867_;
v___y_1893_ = v___y_1918_;
v___y_1894_ = v___y_1919_;
v___y_1895_ = v___y_1920_;
v___y_1896_ = v___y_1921_;
goto v___jp_1890_;
}
else
{
lean_object* v_a_1926_; lean_object* v___x_1927_; 
v_a_1926_ = lean_ctor_get(v___x_1924_, 0);
lean_inc(v_a_1926_);
lean_dec_ref(v___x_1924_);
lean_inc(v___y_1921_);
lean_inc_ref(v___y_1920_);
lean_inc(v___y_1919_);
lean_inc_ref(v___y_1918_);
lean_inc_ref(v_major_1868_);
v___x_1927_ = lean_infer_type(v_major_1868_, v___y_1918_, v___y_1919_, v___y_1920_, v___y_1921_);
if (lean_obj_tag(v___x_1927_) == 0)
{
lean_object* v_a_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; 
v_a_1928_ = lean_ctor_get(v___x_1927_, 0);
lean_inc(v_a_1928_);
lean_dec_ref(v___x_1927_);
v___x_1929_ = lean_unsigned_to_nat(1u);
v___x_1930_ = lean_mk_empty_array_with_capacity(v___x_1929_);
v___x_1931_ = lean_array_push(v___x_1930_, v_major_1868_);
v___x_1932_ = l_Lean_Expr_abstractM(v_a_1867_, v___x_1931_, v___y_1918_, v___y_1919_, v___y_1920_, v___y_1921_);
lean_dec_ref(v___x_1931_);
if (lean_obj_tag(v___x_1932_) == 0)
{
lean_object* v_a_1933_; lean_object* v___x_1934_; uint8_t v___x_1935_; lean_object* v___x_1936_; 
v_a_1933_ = lean_ctor_get(v___x_1932_, 0);
lean_inc(v_a_1933_);
lean_dec_ref(v___x_1932_);
v___x_1934_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__3));
v___x_1935_ = 0;
v___x_1936_ = l_Lean_mkLambda(v___x_1934_, v___x_1935_, v_a_1928_, v_a_1933_);
v___y_1891_ = v_a_1926_;
v_motive_1892_ = v___x_1936_;
v___y_1893_ = v___y_1918_;
v___y_1894_ = v___y_1919_;
v___y_1895_ = v___y_1920_;
v___y_1896_ = v___y_1921_;
goto v___jp_1890_;
}
else
{
lean_dec(v_a_1928_);
lean_dec(v_a_1926_);
return v___x_1932_;
}
}
else
{
lean_dec(v_a_1926_);
lean_dec_ref(v_major_1868_);
lean_dec_ref(v_a_1867_);
return v___x_1927_;
}
}
}
else
{
lean_dec_ref(v_major_1868_);
lean_dec_ref(v_a_1867_);
return v___x_1924_;
}
}
}
}
else
{
lean_object* v_a_1958_; lean_object* v___x_1960_; uint8_t v_isShared_1961_; uint8_t v_isSharedCheck_1965_; 
lean_dec(v_paramsPos_1887_);
lean_dec(v_recursorName_1884_);
lean_dec_ref(v_x_1870_);
lean_dec_ref(v_major_1868_);
lean_dec_ref(v_a_1867_);
lean_dec(v_mvarId_1865_);
lean_dec(v_tacticName_1864_);
lean_dec(v_a_1863_);
v_a_1958_ = lean_ctor_get(v___x_1910_, 0);
v_isSharedCheck_1965_ = !lean_is_exclusive(v___x_1910_);
if (v_isSharedCheck_1965_ == 0)
{
v___x_1960_ = v___x_1910_;
v_isShared_1961_ = v_isSharedCheck_1965_;
goto v_resetjp_1959_;
}
else
{
lean_inc(v_a_1958_);
lean_dec(v___x_1910_);
v___x_1960_ = lean_box(0);
v_isShared_1961_ = v_isSharedCheck_1965_;
goto v_resetjp_1959_;
}
v_resetjp_1959_:
{
lean_object* v___x_1963_; 
if (v_isShared_1961_ == 0)
{
v___x_1963_ = v___x_1960_;
goto v_reusejp_1962_;
}
else
{
lean_object* v_reuseFailAlloc_1964_; 
v_reuseFailAlloc_1964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1964_, 0, v_a_1958_);
v___x_1963_ = v_reuseFailAlloc_1964_;
goto v_reusejp_1962_;
}
v_reusejp_1962_:
{
return v___x_1963_;
}
}
}
v___jp_1890_:
{
uint8_t v___x_1897_; uint8_t v___x_1898_; lean_object* v___x_1899_; 
v___x_1897_ = 1;
v___x_1898_ = 1;
v___x_1899_ = l_Lean_Meta_mkLambdaFVars(v_indices_1866_, v_motive_1892_, v___x_1889_, v___x_1897_, v___x_1889_, v___x_1897_, v___x_1898_, v___y_1893_, v___y_1894_, v___y_1895_, v___y_1896_);
if (lean_obj_tag(v___x_1899_) == 0)
{
lean_object* v_a_1900_; lean_object* v___x_1902_; uint8_t v_isShared_1903_; uint8_t v_isSharedCheck_1908_; 
v_a_1900_ = lean_ctor_get(v___x_1899_, 0);
v_isSharedCheck_1908_ = !lean_is_exclusive(v___x_1899_);
if (v_isSharedCheck_1908_ == 0)
{
v___x_1902_ = v___x_1899_;
v_isShared_1903_ = v_isSharedCheck_1908_;
goto v_resetjp_1901_;
}
else
{
lean_inc(v_a_1900_);
lean_dec(v___x_1899_);
v___x_1902_ = lean_box(0);
v_isShared_1903_ = v_isSharedCheck_1908_;
goto v_resetjp_1901_;
}
v_resetjp_1901_:
{
lean_object* v___x_1904_; lean_object* v___x_1906_; 
v___x_1904_ = l_Lean_Expr_app___override(v___y_1891_, v_a_1900_);
if (v_isShared_1903_ == 0)
{
lean_ctor_set(v___x_1902_, 0, v___x_1904_);
v___x_1906_ = v___x_1902_;
goto v_reusejp_1905_;
}
else
{
lean_object* v_reuseFailAlloc_1907_; 
v_reuseFailAlloc_1907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1907_, 0, v___x_1904_);
v___x_1906_ = v_reuseFailAlloc_1907_;
goto v_reusejp_1905_;
}
v_reusejp_1905_:
{
return v___x_1906_;
}
}
}
else
{
lean_dec_ref(v___y_1891_);
return v___x_1899_;
}
}
}
else
{
lean_object* v___x_1966_; lean_object* v___x_1967_; 
lean_dec_ref(v_x_1870_);
lean_dec_ref(v_x_1869_);
lean_dec_ref(v_major_1868_);
lean_dec_ref(v_a_1867_);
lean_dec(v_a_1863_);
lean_dec_ref(v_recursorInfo_1862_);
v___x_1966_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__14, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__14_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__14);
v___x_1967_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1864_, v_mvarId_1865_, v___x_1966_, v___y_1872_, v___y_1873_, v___y_1874_, v___y_1875_);
return v___x_1967_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___boxed(lean_object* v_recursorInfo_1968_, lean_object* v_a_1969_, lean_object* v_tacticName_1970_, lean_object* v_mvarId_1971_, lean_object* v_indices_1972_, lean_object* v_a_1973_, lean_object* v_major_1974_, lean_object* v_x_1975_, lean_object* v_x_1976_, lean_object* v_x_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_){
_start:
{
lean_object* v_res_1983_; 
v_res_1983_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2(v_recursorInfo_1968_, v_a_1969_, v_tacticName_1970_, v_mvarId_1971_, v_indices_1972_, v_a_1973_, v_major_1974_, v_x_1975_, v_x_1976_, v_x_1977_, v___y_1978_, v___y_1979_, v___y_1980_, v___y_1981_);
lean_dec(v___y_1981_);
lean_dec_ref(v___y_1980_);
lean_dec(v___y_1979_);
lean_dec_ref(v___y_1978_);
lean_dec_ref(v_indices_1972_);
return v_res_1983_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2(lean_object* v_a_1984_, lean_object* v_tacticName_1985_, lean_object* v_mvarId_1986_, lean_object* v_recursorInfo_1987_, lean_object* v_indices_1988_, lean_object* v_a_1989_, lean_object* v_major_1990_, lean_object* v_x_1991_, lean_object* v_x_1992_, lean_object* v_x_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_){
_start:
{
if (lean_obj_tag(v_x_1991_) == 5)
{
lean_object* v_fn_1999_; lean_object* v_arg_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; 
v_fn_1999_ = lean_ctor_get(v_x_1991_, 0);
lean_inc_ref(v_fn_1999_);
v_arg_2000_ = lean_ctor_get(v_x_1991_, 1);
lean_inc_ref(v_arg_2000_);
lean_dec_ref(v_x_1991_);
v___x_2001_ = lean_array_set(v_x_1992_, v_x_1993_, v_arg_2000_);
v___x_2002_ = lean_unsigned_to_nat(1u);
v___x_2003_ = lean_nat_sub(v_x_1993_, v___x_2002_);
v___x_2004_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2(v_recursorInfo_1987_, v_a_1984_, v_tacticName_1985_, v_mvarId_1986_, v_indices_1988_, v_a_1989_, v_major_1990_, v_fn_1999_, v___x_2001_, v___x_2003_, v___y_1994_, v___y_1995_, v___y_1996_, v___y_1997_);
return v___x_2004_;
}
else
{
if (lean_obj_tag(v_x_1991_) == 4)
{
lean_object* v_us_2005_; lean_object* v_recursorName_2006_; lean_object* v_univLevelPos_2007_; uint8_t v_depElim_2008_; lean_object* v_paramsPos_2009_; lean_object* v___x_2010_; uint8_t v___x_2011_; lean_object* v___y_2013_; lean_object* v_motive_2014_; lean_object* v___y_2015_; lean_object* v___y_2016_; lean_object* v___y_2017_; lean_object* v___y_2018_; lean_object* v___x_2031_; lean_object* v___x_2032_; 
v_us_2005_ = lean_ctor_get(v_x_1991_, 1);
lean_inc(v_us_2005_);
lean_dec_ref(v_x_1991_);
v_recursorName_2006_ = lean_ctor_get(v_recursorInfo_1987_, 0);
lean_inc(v_recursorName_2006_);
v_univLevelPos_2007_ = lean_ctor_get(v_recursorInfo_1987_, 2);
lean_inc(v_univLevelPos_2007_);
v_depElim_2008_ = lean_ctor_get_uint8(v_recursorInfo_1987_, sizeof(void*)*8);
v_paramsPos_2009_ = lean_ctor_get(v_recursorInfo_1987_, 5);
lean_inc(v_paramsPos_2009_);
lean_dec_ref(v_recursorInfo_1987_);
v___x_2010_ = lean_array_mk(v_us_2005_);
v___x_2011_ = 0;
v___x_2031_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__1));
lean_inc(v_mvarId_1986_);
lean_inc(v_tacticName_1985_);
lean_inc(v_a_1984_);
v___x_2032_ = l_List_foldlM___at___00Lean_Meta_mkRecursorAppPrefix_spec__0(v_a_1984_, v___x_2010_, v_tacticName_1985_, v_mvarId_1986_, v___x_2031_, v_univLevelPos_2007_, v___y_1994_, v___y_1995_, v___y_1996_, v___y_1997_);
lean_dec(v_univLevelPos_2007_);
lean_dec_ref(v___x_2010_);
if (lean_obj_tag(v___x_2032_) == 0)
{
lean_object* v_a_2033_; lean_object* v_fst_2034_; lean_object* v_snd_2035_; lean_object* v___x_2037_; uint8_t v_isShared_2038_; uint8_t v_isSharedCheck_2079_; 
v_a_2033_ = lean_ctor_get(v___x_2032_, 0);
lean_inc(v_a_2033_);
lean_dec_ref(v___x_2032_);
v_fst_2034_ = lean_ctor_get(v_a_2033_, 0);
v_snd_2035_ = lean_ctor_get(v_a_2033_, 1);
v_isSharedCheck_2079_ = !lean_is_exclusive(v_a_2033_);
if (v_isSharedCheck_2079_ == 0)
{
v___x_2037_ = v_a_2033_;
v_isShared_2038_ = v_isSharedCheck_2079_;
goto v_resetjp_2036_;
}
else
{
lean_inc(v_snd_2035_);
lean_inc(v_fst_2034_);
lean_dec(v_a_2033_);
v___x_2037_ = lean_box(0);
v_isShared_2038_ = v_isSharedCheck_2079_;
goto v_resetjp_2036_;
}
v_resetjp_2036_:
{
lean_object* v___y_2040_; lean_object* v___y_2041_; lean_object* v___y_2042_; lean_object* v___y_2043_; uint8_t v___x_2059_; 
v___x_2059_ = lean_unbox(v_snd_2035_);
lean_dec(v_snd_2035_);
if (v___x_2059_ == 0)
{
uint8_t v___x_2060_; 
v___x_2060_ = l_Lean_Level_isZero(v_a_1984_);
lean_dec(v_a_1984_);
if (v___x_2060_ == 0)
{
lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2065_; 
lean_dec(v_fst_2034_);
lean_dec(v_paramsPos_2009_);
lean_dec_ref(v_x_1992_);
lean_dec_ref(v_major_1990_);
lean_dec_ref(v_a_1989_);
v___x_2061_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__6));
v___x_2062_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__8, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__8_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__8);
v___x_2063_ = l_Lean_MessageData_ofName(v_recursorName_2006_);
if (v_isShared_2038_ == 0)
{
lean_ctor_set_tag(v___x_2037_, 7);
lean_ctor_set(v___x_2037_, 1, v___x_2063_);
lean_ctor_set(v___x_2037_, 0, v___x_2062_);
v___x_2065_ = v___x_2037_;
goto v_reusejp_2064_;
}
else
{
lean_object* v_reuseFailAlloc_2078_; 
v_reuseFailAlloc_2078_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2078_, 0, v___x_2062_);
lean_ctor_set(v_reuseFailAlloc_2078_, 1, v___x_2063_);
v___x_2065_ = v_reuseFailAlloc_2078_;
goto v_reusejp_2064_;
}
v_reusejp_2064_:
{
lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v_a_2070_; lean_object* v___x_2072_; uint8_t v_isShared_2073_; uint8_t v_isSharedCheck_2077_; 
v___x_2066_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__10, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__10_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__10);
v___x_2067_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2067_, 0, v___x_2065_);
lean_ctor_set(v___x_2067_, 1, v___x_2066_);
v___x_2068_ = l_Lean_Meta_mkTacticExMsg(v_tacticName_1985_, v_mvarId_1986_, v___x_2067_);
v___x_2069_ = l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1___redArg(v___x_2061_, v___x_2068_, v___y_1994_, v___y_1995_, v___y_1996_, v___y_1997_);
v_a_2070_ = lean_ctor_get(v___x_2069_, 0);
v_isSharedCheck_2077_ = !lean_is_exclusive(v___x_2069_);
if (v_isSharedCheck_2077_ == 0)
{
v___x_2072_ = v___x_2069_;
v_isShared_2073_ = v_isSharedCheck_2077_;
goto v_resetjp_2071_;
}
else
{
lean_inc(v_a_2070_);
lean_dec(v___x_2069_);
v___x_2072_ = lean_box(0);
v_isShared_2073_ = v_isSharedCheck_2077_;
goto v_resetjp_2071_;
}
v_resetjp_2071_:
{
lean_object* v___x_2075_; 
if (v_isShared_2073_ == 0)
{
v___x_2075_ = v___x_2072_;
goto v_reusejp_2074_;
}
else
{
lean_object* v_reuseFailAlloc_2076_; 
v_reuseFailAlloc_2076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2076_, 0, v_a_2070_);
v___x_2075_ = v_reuseFailAlloc_2076_;
goto v_reusejp_2074_;
}
v_reusejp_2074_:
{
return v___x_2075_;
}
}
}
}
else
{
lean_del_object(v___x_2037_);
lean_dec(v_tacticName_1985_);
v___y_2040_ = v___y_1994_;
v___y_2041_ = v___y_1995_;
v___y_2042_ = v___y_1996_;
v___y_2043_ = v___y_1997_;
goto v___jp_2039_;
}
}
else
{
lean_del_object(v___x_2037_);
lean_dec(v_tacticName_1985_);
lean_dec(v_a_1984_);
v___y_2040_ = v___y_1994_;
v___y_2041_ = v___y_1995_;
v___y_2042_ = v___y_1996_;
v___y_2043_ = v___y_1997_;
goto v___jp_2039_;
}
v___jp_2039_:
{
lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; 
v___x_2044_ = lean_array_to_list(v_fst_2034_);
v___x_2045_ = l_Lean_mkConst(v_recursorName_2006_, v___x_2044_);
v___x_2046_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams(v_mvarId_1986_, v_x_1992_, v_paramsPos_2009_, v___x_2045_, v___y_2040_, v___y_2041_, v___y_2042_, v___y_2043_);
lean_dec_ref(v_x_1992_);
if (lean_obj_tag(v___x_2046_) == 0)
{
if (v_depElim_2008_ == 0)
{
lean_object* v_a_2047_; 
lean_dec_ref(v_major_1990_);
v_a_2047_ = lean_ctor_get(v___x_2046_, 0);
lean_inc(v_a_2047_);
lean_dec_ref(v___x_2046_);
v___y_2013_ = v_a_2047_;
v_motive_2014_ = v_a_1989_;
v___y_2015_ = v___y_2040_;
v___y_2016_ = v___y_2041_;
v___y_2017_ = v___y_2042_;
v___y_2018_ = v___y_2043_;
goto v___jp_2012_;
}
else
{
lean_object* v_a_2048_; lean_object* v___x_2049_; 
v_a_2048_ = lean_ctor_get(v___x_2046_, 0);
lean_inc(v_a_2048_);
lean_dec_ref(v___x_2046_);
lean_inc(v___y_2043_);
lean_inc_ref(v___y_2042_);
lean_inc(v___y_2041_);
lean_inc_ref(v___y_2040_);
lean_inc_ref(v_major_1990_);
v___x_2049_ = lean_infer_type(v_major_1990_, v___y_2040_, v___y_2041_, v___y_2042_, v___y_2043_);
if (lean_obj_tag(v___x_2049_) == 0)
{
lean_object* v_a_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; 
v_a_2050_ = lean_ctor_get(v___x_2049_, 0);
lean_inc(v_a_2050_);
lean_dec_ref(v___x_2049_);
v___x_2051_ = lean_unsigned_to_nat(1u);
v___x_2052_ = lean_mk_empty_array_with_capacity(v___x_2051_);
v___x_2053_ = lean_array_push(v___x_2052_, v_major_1990_);
v___x_2054_ = l_Lean_Expr_abstractM(v_a_1989_, v___x_2053_, v___y_2040_, v___y_2041_, v___y_2042_, v___y_2043_);
lean_dec_ref(v___x_2053_);
if (lean_obj_tag(v___x_2054_) == 0)
{
lean_object* v_a_2055_; lean_object* v___x_2056_; uint8_t v___x_2057_; lean_object* v___x_2058_; 
v_a_2055_ = lean_ctor_get(v___x_2054_, 0);
lean_inc(v_a_2055_);
lean_dec_ref(v___x_2054_);
v___x_2056_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__3));
v___x_2057_ = 0;
v___x_2058_ = l_Lean_mkLambda(v___x_2056_, v___x_2057_, v_a_2050_, v_a_2055_);
v___y_2013_ = v_a_2048_;
v_motive_2014_ = v___x_2058_;
v___y_2015_ = v___y_2040_;
v___y_2016_ = v___y_2041_;
v___y_2017_ = v___y_2042_;
v___y_2018_ = v___y_2043_;
goto v___jp_2012_;
}
else
{
lean_dec(v_a_2050_);
lean_dec(v_a_2048_);
return v___x_2054_;
}
}
else
{
lean_dec(v_a_2048_);
lean_dec_ref(v_major_1990_);
lean_dec_ref(v_a_1989_);
return v___x_2049_;
}
}
}
else
{
lean_dec_ref(v_major_1990_);
lean_dec_ref(v_a_1989_);
return v___x_2046_;
}
}
}
}
else
{
lean_object* v_a_2080_; lean_object* v___x_2082_; uint8_t v_isShared_2083_; uint8_t v_isSharedCheck_2087_; 
lean_dec(v_paramsPos_2009_);
lean_dec(v_recursorName_2006_);
lean_dec_ref(v_x_1992_);
lean_dec_ref(v_major_1990_);
lean_dec_ref(v_a_1989_);
lean_dec(v_mvarId_1986_);
lean_dec(v_tacticName_1985_);
lean_dec(v_a_1984_);
v_a_2080_ = lean_ctor_get(v___x_2032_, 0);
v_isSharedCheck_2087_ = !lean_is_exclusive(v___x_2032_);
if (v_isSharedCheck_2087_ == 0)
{
v___x_2082_ = v___x_2032_;
v_isShared_2083_ = v_isSharedCheck_2087_;
goto v_resetjp_2081_;
}
else
{
lean_inc(v_a_2080_);
lean_dec(v___x_2032_);
v___x_2082_ = lean_box(0);
v_isShared_2083_ = v_isSharedCheck_2087_;
goto v_resetjp_2081_;
}
v_resetjp_2081_:
{
lean_object* v___x_2085_; 
if (v_isShared_2083_ == 0)
{
v___x_2085_ = v___x_2082_;
goto v_reusejp_2084_;
}
else
{
lean_object* v_reuseFailAlloc_2086_; 
v_reuseFailAlloc_2086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2086_, 0, v_a_2080_);
v___x_2085_ = v_reuseFailAlloc_2086_;
goto v_reusejp_2084_;
}
v_reusejp_2084_:
{
return v___x_2085_;
}
}
}
v___jp_2012_:
{
uint8_t v___x_2019_; uint8_t v___x_2020_; lean_object* v___x_2021_; 
v___x_2019_ = 1;
v___x_2020_ = 1;
v___x_2021_ = l_Lean_Meta_mkLambdaFVars(v_indices_1988_, v_motive_2014_, v___x_2011_, v___x_2019_, v___x_2011_, v___x_2019_, v___x_2020_, v___y_2015_, v___y_2016_, v___y_2017_, v___y_2018_);
if (lean_obj_tag(v___x_2021_) == 0)
{
lean_object* v_a_2022_; lean_object* v___x_2024_; uint8_t v_isShared_2025_; uint8_t v_isSharedCheck_2030_; 
v_a_2022_ = lean_ctor_get(v___x_2021_, 0);
v_isSharedCheck_2030_ = !lean_is_exclusive(v___x_2021_);
if (v_isSharedCheck_2030_ == 0)
{
v___x_2024_ = v___x_2021_;
v_isShared_2025_ = v_isSharedCheck_2030_;
goto v_resetjp_2023_;
}
else
{
lean_inc(v_a_2022_);
lean_dec(v___x_2021_);
v___x_2024_ = lean_box(0);
v_isShared_2025_ = v_isSharedCheck_2030_;
goto v_resetjp_2023_;
}
v_resetjp_2023_:
{
lean_object* v___x_2026_; lean_object* v___x_2028_; 
v___x_2026_ = l_Lean_Expr_app___override(v___y_2013_, v_a_2022_);
if (v_isShared_2025_ == 0)
{
lean_ctor_set(v___x_2024_, 0, v___x_2026_);
v___x_2028_ = v___x_2024_;
goto v_reusejp_2027_;
}
else
{
lean_object* v_reuseFailAlloc_2029_; 
v_reuseFailAlloc_2029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2029_, 0, v___x_2026_);
v___x_2028_ = v_reuseFailAlloc_2029_;
goto v_reusejp_2027_;
}
v_reusejp_2027_:
{
return v___x_2028_;
}
}
}
else
{
lean_dec_ref(v___y_2013_);
return v___x_2021_;
}
}
}
else
{
lean_object* v___x_2088_; lean_object* v___x_2089_; 
lean_dec_ref(v_x_1992_);
lean_dec_ref(v_x_1991_);
lean_dec_ref(v_major_1990_);
lean_dec_ref(v_a_1989_);
lean_dec_ref(v_recursorInfo_1987_);
lean_dec(v_a_1984_);
v___x_2088_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__14, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__14_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__14);
v___x_2089_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1985_, v_mvarId_1986_, v___x_2088_, v___y_1994_, v___y_1995_, v___y_1996_, v___y_1997_);
return v___x_2089_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2___boxed(lean_object* v_a_2090_, lean_object* v_tacticName_2091_, lean_object* v_mvarId_2092_, lean_object* v_recursorInfo_2093_, lean_object* v_indices_2094_, lean_object* v_a_2095_, lean_object* v_major_2096_, lean_object* v_x_2097_, lean_object* v_x_2098_, lean_object* v_x_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_){
_start:
{
lean_object* v_res_2105_; 
v_res_2105_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2(v_a_2090_, v_tacticName_2091_, v_mvarId_2092_, v_recursorInfo_2093_, v_indices_2094_, v_a_2095_, v_major_2096_, v_x_2097_, v_x_2098_, v_x_2099_, v___y_2100_, v___y_2101_, v___y_2102_, v___y_2103_);
lean_dec(v___y_2103_);
lean_dec_ref(v___y_2102_);
lean_dec(v___y_2101_);
lean_dec_ref(v___y_2100_);
lean_dec(v_x_2099_);
lean_dec_ref(v_indices_2094_);
return v_res_2105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkRecursorAppPrefix(lean_object* v_mvarId_2106_, lean_object* v_tacticName_2107_, lean_object* v_majorFVarId_2108_, lean_object* v_recursorInfo_2109_, lean_object* v_indices_2110_, lean_object* v_a_2111_, lean_object* v_a_2112_, lean_object* v_a_2113_, lean_object* v_a_2114_){
_start:
{
lean_object* v___x_2116_; 
lean_inc(v_mvarId_2106_);
v___x_2116_ = l_Lean_MVarId_getType(v_mvarId_2106_, v_a_2111_, v_a_2112_, v_a_2113_, v_a_2114_);
if (lean_obj_tag(v___x_2116_) == 0)
{
lean_object* v_a_2117_; lean_object* v___x_2118_; 
v_a_2117_ = lean_ctor_get(v___x_2116_, 0);
lean_inc_n(v_a_2117_, 2);
lean_dec_ref(v___x_2116_);
v___x_2118_ = l_Lean_Meta_getLevel(v_a_2117_, v_a_2111_, v_a_2112_, v_a_2113_, v_a_2114_);
if (lean_obj_tag(v___x_2118_) == 0)
{
lean_object* v_a_2119_; lean_object* v___x_2120_; 
v_a_2119_ = lean_ctor_get(v___x_2118_, 0);
lean_inc(v_a_2119_);
lean_dec_ref(v___x_2118_);
v___x_2120_ = l_Lean_Meta_normalizeLevel(v_a_2119_, v_a_2111_, v_a_2112_, v_a_2113_, v_a_2114_);
if (lean_obj_tag(v___x_2120_) == 0)
{
lean_object* v_a_2121_; lean_object* v_major_2122_; lean_object* v___x_2123_; 
v_a_2121_ = lean_ctor_get(v___x_2120_, 0);
lean_inc(v_a_2121_);
lean_dec_ref(v___x_2120_);
lean_inc(v_majorFVarId_2108_);
v_major_2122_ = l_Lean_mkFVar(v_majorFVarId_2108_);
v___x_2123_ = l_Lean_FVarId_getDecl___redArg(v_majorFVarId_2108_, v_a_2111_, v_a_2113_, v_a_2114_);
if (lean_obj_tag(v___x_2123_) == 0)
{
lean_object* v_a_2124_; lean_object* v_typeName_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; 
v_a_2124_ = lean_ctor_get(v___x_2123_, 0);
lean_inc(v_a_2124_);
lean_dec_ref(v___x_2123_);
v_typeName_2125_ = lean_ctor_get(v_recursorInfo_2109_, 1);
v___x_2126_ = l_Lean_LocalDecl_type(v_a_2124_);
lean_dec(v_a_2124_);
lean_inc_ref(v___x_2126_);
v___x_2127_ = l_Lean_Meta_whnfUntil(v___x_2126_, v_typeName_2125_, v_a_2111_, v_a_2112_, v_a_2113_, v_a_2114_);
if (lean_obj_tag(v___x_2127_) == 0)
{
lean_object* v_a_2128_; 
v_a_2128_ = lean_ctor_get(v___x_2127_, 0);
lean_inc(v_a_2128_);
lean_dec_ref(v___x_2127_);
if (lean_obj_tag(v_a_2128_) == 1)
{
lean_object* v_val_2129_; lean_object* v_dummy_2130_; lean_object* v_nargs_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; 
lean_dec_ref(v___x_2126_);
v_val_2129_ = lean_ctor_get(v_a_2128_, 0);
lean_inc(v_val_2129_);
lean_dec_ref(v_a_2128_);
v_dummy_2130_ = lean_obj_once(&l_Lean_Meta_getMajorTypeIndices___closed__0, &l_Lean_Meta_getMajorTypeIndices___closed__0_once, _init_l_Lean_Meta_getMajorTypeIndices___closed__0);
v_nargs_2131_ = l_Lean_Expr_getAppNumArgs(v_val_2129_);
lean_inc(v_nargs_2131_);
v___x_2132_ = lean_mk_array(v_nargs_2131_, v_dummy_2130_);
v___x_2133_ = lean_unsigned_to_nat(1u);
v___x_2134_ = lean_nat_sub(v_nargs_2131_, v___x_2133_);
lean_dec(v_nargs_2131_);
v___x_2135_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2(v_a_2121_, v_tacticName_2107_, v_mvarId_2106_, v_recursorInfo_2109_, v_indices_2110_, v_a_2117_, v_major_2122_, v_val_2129_, v___x_2132_, v___x_2134_, v_a_2111_, v_a_2112_, v_a_2113_, v_a_2114_);
lean_dec(v___x_2134_);
return v___x_2135_;
}
else
{
lean_object* v___x_2136_; 
lean_dec(v_a_2128_);
lean_dec_ref(v_major_2122_);
lean_dec(v_a_2121_);
lean_dec(v_a_2117_);
lean_dec_ref(v_recursorInfo_2109_);
v___x_2136_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg(v_tacticName_2107_, v_mvarId_2106_, v___x_2126_, v_a_2111_, v_a_2112_, v_a_2113_, v_a_2114_);
return v___x_2136_;
}
}
else
{
lean_object* v_a_2137_; lean_object* v___x_2139_; uint8_t v_isShared_2140_; uint8_t v_isSharedCheck_2144_; 
lean_dec_ref(v___x_2126_);
lean_dec_ref(v_major_2122_);
lean_dec(v_a_2121_);
lean_dec(v_a_2117_);
lean_dec_ref(v_recursorInfo_2109_);
lean_dec(v_tacticName_2107_);
lean_dec(v_mvarId_2106_);
v_a_2137_ = lean_ctor_get(v___x_2127_, 0);
v_isSharedCheck_2144_ = !lean_is_exclusive(v___x_2127_);
if (v_isSharedCheck_2144_ == 0)
{
v___x_2139_ = v___x_2127_;
v_isShared_2140_ = v_isSharedCheck_2144_;
goto v_resetjp_2138_;
}
else
{
lean_inc(v_a_2137_);
lean_dec(v___x_2127_);
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
lean_dec_ref(v_major_2122_);
lean_dec(v_a_2121_);
lean_dec(v_a_2117_);
lean_dec_ref(v_recursorInfo_2109_);
lean_dec(v_tacticName_2107_);
lean_dec(v_mvarId_2106_);
v_a_2145_ = lean_ctor_get(v___x_2123_, 0);
v_isSharedCheck_2152_ = !lean_is_exclusive(v___x_2123_);
if (v_isSharedCheck_2152_ == 0)
{
v___x_2147_ = v___x_2123_;
v_isShared_2148_ = v_isSharedCheck_2152_;
goto v_resetjp_2146_;
}
else
{
lean_inc(v_a_2145_);
lean_dec(v___x_2123_);
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
lean_dec(v_a_2117_);
lean_dec_ref(v_recursorInfo_2109_);
lean_dec(v_majorFVarId_2108_);
lean_dec(v_tacticName_2107_);
lean_dec(v_mvarId_2106_);
v_a_2153_ = lean_ctor_get(v___x_2120_, 0);
v_isSharedCheck_2160_ = !lean_is_exclusive(v___x_2120_);
if (v_isSharedCheck_2160_ == 0)
{
v___x_2155_ = v___x_2120_;
v_isShared_2156_ = v_isSharedCheck_2160_;
goto v_resetjp_2154_;
}
else
{
lean_inc(v_a_2153_);
lean_dec(v___x_2120_);
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
lean_object* v_a_2161_; lean_object* v___x_2163_; uint8_t v_isShared_2164_; uint8_t v_isSharedCheck_2168_; 
lean_dec(v_a_2117_);
lean_dec_ref(v_recursorInfo_2109_);
lean_dec(v_majorFVarId_2108_);
lean_dec(v_tacticName_2107_);
lean_dec(v_mvarId_2106_);
v_a_2161_ = lean_ctor_get(v___x_2118_, 0);
v_isSharedCheck_2168_ = !lean_is_exclusive(v___x_2118_);
if (v_isSharedCheck_2168_ == 0)
{
v___x_2163_ = v___x_2118_;
v_isShared_2164_ = v_isSharedCheck_2168_;
goto v_resetjp_2162_;
}
else
{
lean_inc(v_a_2161_);
lean_dec(v___x_2118_);
v___x_2163_ = lean_box(0);
v_isShared_2164_ = v_isSharedCheck_2168_;
goto v_resetjp_2162_;
}
v_resetjp_2162_:
{
lean_object* v___x_2166_; 
if (v_isShared_2164_ == 0)
{
v___x_2166_ = v___x_2163_;
goto v_reusejp_2165_;
}
else
{
lean_object* v_reuseFailAlloc_2167_; 
v_reuseFailAlloc_2167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2167_, 0, v_a_2161_);
v___x_2166_ = v_reuseFailAlloc_2167_;
goto v_reusejp_2165_;
}
v_reusejp_2165_:
{
return v___x_2166_;
}
}
}
}
else
{
lean_dec_ref(v_recursorInfo_2109_);
lean_dec(v_majorFVarId_2108_);
lean_dec(v_tacticName_2107_);
lean_dec(v_mvarId_2106_);
return v___x_2116_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkRecursorAppPrefix___boxed(lean_object* v_mvarId_2169_, lean_object* v_tacticName_2170_, lean_object* v_majorFVarId_2171_, lean_object* v_recursorInfo_2172_, lean_object* v_indices_2173_, lean_object* v_a_2174_, lean_object* v_a_2175_, lean_object* v_a_2176_, lean_object* v_a_2177_, lean_object* v_a_2178_){
_start:
{
lean_object* v_res_2179_; 
v_res_2179_ = l_Lean_Meta_mkRecursorAppPrefix(v_mvarId_2169_, v_tacticName_2170_, v_majorFVarId_2171_, v_recursorInfo_2172_, v_indices_2173_, v_a_2174_, v_a_2175_, v_a_2176_, v_a_2177_);
lean_dec(v_a_2177_);
lean_dec_ref(v_a_2176_);
lean_dec(v_a_2175_);
lean_dec_ref(v_a_2174_);
lean_dec_ref(v_indices_2173_);
return v_res_2179_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1(lean_object* v_00_u03b1_2180_, lean_object* v_name_2181_, lean_object* v_msg_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_){
_start:
{
lean_object* v___x_2188_; 
v___x_2188_ = l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1___redArg(v_name_2181_, v_msg_2182_, v___y_2183_, v___y_2184_, v___y_2185_, v___y_2186_);
return v___x_2188_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1___boxed(lean_object* v_00_u03b1_2189_, lean_object* v_name_2190_, lean_object* v_msg_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_){
_start:
{
lean_object* v_res_2197_; 
v_res_2197_ = l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1(v_00_u03b1_2189_, v_name_2190_, v_msg_2191_, v___y_2192_, v___y_2193_, v___y_2194_, v___y_2195_);
lean_dec(v___y_2195_);
lean_dec_ref(v___y_2194_);
lean_dec(v___y_2193_);
lean_dec_ref(v___y_2192_);
return v_res_2197_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___redArg(lean_object* v_mvarId_2198_, lean_object* v_x_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_){
_start:
{
lean_object* v___x_2205_; 
v___x_2205_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_2198_, v_x_2199_, v___y_2200_, v___y_2201_, v___y_2202_, v___y_2203_);
if (lean_obj_tag(v___x_2205_) == 0)
{
lean_object* v_a_2206_; lean_object* v___x_2208_; uint8_t v_isShared_2209_; uint8_t v_isSharedCheck_2213_; 
v_a_2206_ = lean_ctor_get(v___x_2205_, 0);
v_isSharedCheck_2213_ = !lean_is_exclusive(v___x_2205_);
if (v_isSharedCheck_2213_ == 0)
{
v___x_2208_ = v___x_2205_;
v_isShared_2209_ = v_isSharedCheck_2213_;
goto v_resetjp_2207_;
}
else
{
lean_inc(v_a_2206_);
lean_dec(v___x_2205_);
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
v_reuseFailAlloc_2212_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_2214_; lean_object* v___x_2216_; uint8_t v_isShared_2217_; uint8_t v_isSharedCheck_2221_; 
v_a_2214_ = lean_ctor_get(v___x_2205_, 0);
v_isSharedCheck_2221_ = !lean_is_exclusive(v___x_2205_);
if (v_isSharedCheck_2221_ == 0)
{
v___x_2216_ = v___x_2205_;
v_isShared_2217_ = v_isSharedCheck_2221_;
goto v_resetjp_2215_;
}
else
{
lean_inc(v_a_2214_);
lean_dec(v___x_2205_);
v___x_2216_ = lean_box(0);
v_isShared_2217_ = v_isSharedCheck_2221_;
goto v_resetjp_2215_;
}
v_resetjp_2215_:
{
lean_object* v___x_2219_; 
if (v_isShared_2217_ == 0)
{
v___x_2219_ = v___x_2216_;
goto v_reusejp_2218_;
}
else
{
lean_object* v_reuseFailAlloc_2220_; 
v_reuseFailAlloc_2220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2220_, 0, v_a_2214_);
v___x_2219_ = v_reuseFailAlloc_2220_;
goto v_reusejp_2218_;
}
v_reusejp_2218_:
{
return v___x_2219_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___redArg___boxed(lean_object* v_mvarId_2222_, lean_object* v_x_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_){
_start:
{
lean_object* v_res_2229_; 
v_res_2229_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___redArg(v_mvarId_2222_, v_x_2223_, v___y_2224_, v___y_2225_, v___y_2226_, v___y_2227_);
lean_dec(v___y_2227_);
lean_dec_ref(v___y_2226_);
lean_dec(v___y_2225_);
lean_dec_ref(v___y_2224_);
return v_res_2229_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3(lean_object* v_00_u03b1_2230_, lean_object* v_mvarId_2231_, lean_object* v_x_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_){
_start:
{
lean_object* v___x_2238_; 
v___x_2238_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___redArg(v_mvarId_2231_, v_x_2232_, v___y_2233_, v___y_2234_, v___y_2235_, v___y_2236_);
return v___x_2238_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___boxed(lean_object* v_00_u03b1_2239_, lean_object* v_mvarId_2240_, lean_object* v_x_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_){
_start:
{
lean_object* v_res_2247_; 
v_res_2247_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3(v_00_u03b1_2239_, v_mvarId_2240_, v_x_2241_, v___y_2242_, v___y_2243_, v___y_2244_, v___y_2245_);
lean_dec(v___y_2245_);
lean_dec_ref(v___y_2244_);
lean_dec(v___y_2243_);
lean_dec_ref(v___y_2242_);
return v_res_2247_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_induction_spec__2(lean_object* v_fst_2248_, lean_object* v_as_2249_, size_t v_sz_2250_, size_t v_i_2251_, lean_object* v_b_2252_){
_start:
{
uint8_t v___x_2253_; 
v___x_2253_ = lean_usize_dec_lt(v_i_2251_, v_sz_2250_);
if (v___x_2253_ == 0)
{
return v_b_2252_;
}
else
{
lean_object* v_fst_2254_; lean_object* v_snd_2255_; lean_object* v___x_2257_; uint8_t v_isShared_2258_; uint8_t v_isSharedCheck_2273_; 
v_fst_2254_ = lean_ctor_get(v_b_2252_, 0);
v_snd_2255_ = lean_ctor_get(v_b_2252_, 1);
v_isSharedCheck_2273_ = !lean_is_exclusive(v_b_2252_);
if (v_isSharedCheck_2273_ == 0)
{
v___x_2257_ = v_b_2252_;
v_isShared_2258_ = v_isSharedCheck_2273_;
goto v_resetjp_2256_;
}
else
{
lean_inc(v_snd_2255_);
lean_inc(v_fst_2254_);
lean_dec(v_b_2252_);
v___x_2257_ = lean_box(0);
v_isShared_2258_ = v_isSharedCheck_2273_;
goto v_resetjp_2256_;
}
v_resetjp_2256_:
{
lean_object* v___x_2259_; lean_object* v_a_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2268_; 
v___x_2259_ = lean_box(0);
v_a_2260_ = lean_array_uget_borrowed(v_as_2249_, v_i_2251_);
v___x_2261_ = l_Lean_Expr_fvarId_x21(v_a_2260_);
v___x_2262_ = lean_array_get_borrowed(v___x_2259_, v_fst_2248_, v_snd_2255_);
lean_inc(v___x_2262_);
v___x_2263_ = l_Lean_mkFVar(v___x_2262_);
v___x_2264_ = l_Lean_Meta_FVarSubst_insert(v_fst_2254_, v___x_2261_, v___x_2263_);
v___x_2265_ = lean_unsigned_to_nat(1u);
v___x_2266_ = lean_nat_add(v_snd_2255_, v___x_2265_);
lean_dec(v_snd_2255_);
if (v_isShared_2258_ == 0)
{
lean_ctor_set(v___x_2257_, 1, v___x_2266_);
lean_ctor_set(v___x_2257_, 0, v___x_2264_);
v___x_2268_ = v___x_2257_;
goto v_reusejp_2267_;
}
else
{
lean_object* v_reuseFailAlloc_2272_; 
v_reuseFailAlloc_2272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2272_, 0, v___x_2264_);
lean_ctor_set(v_reuseFailAlloc_2272_, 1, v___x_2266_);
v___x_2268_ = v_reuseFailAlloc_2272_;
goto v_reusejp_2267_;
}
v_reusejp_2267_:
{
size_t v___x_2269_; size_t v___x_2270_; 
v___x_2269_ = ((size_t)1ULL);
v___x_2270_ = lean_usize_add(v_i_2251_, v___x_2269_);
v_i_2251_ = v___x_2270_;
v_b_2252_ = v___x_2268_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_induction_spec__2___boxed(lean_object* v_fst_2274_, lean_object* v_as_2275_, lean_object* v_sz_2276_, lean_object* v_i_2277_, lean_object* v_b_2278_){
_start:
{
size_t v_sz_boxed_2279_; size_t v_i_boxed_2280_; lean_object* v_res_2281_; 
v_sz_boxed_2279_ = lean_unbox_usize(v_sz_2276_);
lean_dec(v_sz_2276_);
v_i_boxed_2280_ = lean_unbox_usize(v_i_2277_);
lean_dec(v_i_2277_);
v_res_2281_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_induction_spec__2(v_fst_2274_, v_as_2275_, v_sz_boxed_2279_, v_i_boxed_2280_, v_b_2278_);
lean_dec_ref(v_as_2275_);
lean_dec_ref(v_fst_2274_);
return v_res_2281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4___lam__0(lean_object* v_snd_2282_, lean_object* v___x_2283_, lean_object* v_fst_2284_, lean_object* v_a_2285_, lean_object* v___x_2286_, lean_object* v_givenNames_2287_, lean_object* v_fst_2288_, lean_object* v___x_2289_, lean_object* v_fst_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_){
_start:
{
lean_object* v___x_2296_; 
lean_inc_ref(v_a_2285_);
lean_inc(v_snd_2282_);
v___x_2296_ = l_Lean_Meta_mkRecursorAppPrefix(v_snd_2282_, v___x_2283_, v_fst_2284_, v_a_2285_, v___x_2286_, v___y_2291_, v___y_2292_, v___y_2293_, v___y_2294_);
if (lean_obj_tag(v___x_2296_) == 0)
{
lean_object* v_a_2297_; lean_object* v___x_2298_; 
v_a_2297_ = lean_ctor_get(v___x_2296_, 0);
lean_inc(v_a_2297_);
lean_dec_ref(v___x_2296_);
v___x_2298_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize(v_snd_2282_, v_givenNames_2287_, v_a_2285_, v_fst_2288_, v___x_2289_, v___x_2286_, v_fst_2290_, v_a_2297_, v___y_2291_, v___y_2292_, v___y_2293_, v___y_2294_);
lean_dec_ref(v_a_2285_);
return v___x_2298_;
}
else
{
lean_object* v_a_2299_; lean_object* v___x_2301_; uint8_t v_isShared_2302_; uint8_t v_isSharedCheck_2306_; 
lean_dec(v_fst_2290_);
lean_dec_ref(v___x_2289_);
lean_dec_ref(v_a_2285_);
lean_dec(v_snd_2282_);
v_a_2299_ = lean_ctor_get(v___x_2296_, 0);
v_isSharedCheck_2306_ = !lean_is_exclusive(v___x_2296_);
if (v_isSharedCheck_2306_ == 0)
{
v___x_2301_ = v___x_2296_;
v_isShared_2302_ = v_isSharedCheck_2306_;
goto v_resetjp_2300_;
}
else
{
lean_inc(v_a_2299_);
lean_dec(v___x_2296_);
v___x_2301_ = lean_box(0);
v_isShared_2302_ = v_isSharedCheck_2306_;
goto v_resetjp_2300_;
}
v_resetjp_2300_:
{
lean_object* v___x_2304_; 
if (v_isShared_2302_ == 0)
{
v___x_2304_ = v___x_2301_;
goto v_reusejp_2303_;
}
else
{
lean_object* v_reuseFailAlloc_2305_; 
v_reuseFailAlloc_2305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2305_, 0, v_a_2299_);
v___x_2304_ = v_reuseFailAlloc_2305_;
goto v_reusejp_2303_;
}
v_reusejp_2303_:
{
return v___x_2304_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4___lam__0___boxed(lean_object* v_snd_2307_, lean_object* v___x_2308_, lean_object* v_fst_2309_, lean_object* v_a_2310_, lean_object* v___x_2311_, lean_object* v_givenNames_2312_, lean_object* v_fst_2313_, lean_object* v___x_2314_, lean_object* v_fst_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_){
_start:
{
lean_object* v_res_2321_; 
v_res_2321_ = l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4___lam__0(v_snd_2307_, v___x_2308_, v_fst_2309_, v_a_2310_, v___x_2311_, v_givenNames_2312_, v_fst_2313_, v___x_2314_, v_fst_2315_, v___y_2316_, v___y_2317_, v___y_2318_, v___y_2319_);
lean_dec(v___y_2319_);
lean_dec_ref(v___y_2318_);
lean_dec(v___y_2317_);
lean_dec_ref(v___y_2316_);
lean_dec_ref(v_fst_2313_);
lean_dec_ref(v_givenNames_2312_);
lean_dec_ref(v___x_2311_);
return v_res_2321_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_induction_spec__1(size_t v_sz_2322_, size_t v_i_2323_, lean_object* v_bs_2324_){
_start:
{
uint8_t v___x_2325_; 
v___x_2325_ = lean_usize_dec_lt(v_i_2323_, v_sz_2322_);
if (v___x_2325_ == 0)
{
return v_bs_2324_;
}
else
{
lean_object* v_v_2326_; lean_object* v___x_2327_; lean_object* v_bs_x27_2328_; lean_object* v___x_2329_; size_t v___x_2330_; size_t v___x_2331_; lean_object* v___x_2332_; 
v_v_2326_ = lean_array_uget(v_bs_2324_, v_i_2323_);
v___x_2327_ = lean_unsigned_to_nat(0u);
v_bs_x27_2328_ = lean_array_uset(v_bs_2324_, v_i_2323_, v___x_2327_);
v___x_2329_ = l_Lean_Expr_fvarId_x21(v_v_2326_);
lean_dec(v_v_2326_);
v___x_2330_ = ((size_t)1ULL);
v___x_2331_ = lean_usize_add(v_i_2323_, v___x_2330_);
v___x_2332_ = lean_array_uset(v_bs_x27_2328_, v_i_2323_, v___x_2329_);
v_i_2323_ = v___x_2331_;
v_bs_2324_ = v___x_2332_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_induction_spec__1___boxed(lean_object* v_sz_2334_, lean_object* v_i_2335_, lean_object* v_bs_2336_){
_start:
{
size_t v_sz_boxed_2337_; size_t v_i_boxed_2338_; lean_object* v_res_2339_; 
v_sz_boxed_2337_ = lean_unbox_usize(v_sz_2334_);
lean_dec(v_sz_2334_);
v_i_boxed_2338_ = lean_unbox_usize(v_i_2335_);
lean_dec(v_i_2335_);
v_res_2339_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_induction_spec__1(v_sz_boxed_2337_, v_i_boxed_2338_, v_bs_2336_);
return v_res_2339_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_MVarId_induction_spec__0(lean_object* v_majorTypeArgs_2340_, lean_object* v_val_2341_, lean_object* v_mvarId_2342_, lean_object* v_as_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_){
_start:
{
if (lean_obj_tag(v_as_2343_) == 0)
{
lean_object* v___x_2349_; lean_object* v___x_2350_; 
lean_dec(v_mvarId_2342_);
lean_dec_ref(v_val_2341_);
v___x_2349_ = lean_box(0);
v___x_2350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2350_, 0, v___x_2349_);
return v___x_2350_;
}
else
{
lean_object* v_head_2351_; 
v_head_2351_ = lean_ctor_get(v_as_2343_, 0);
lean_inc(v_head_2351_);
if (lean_obj_tag(v_head_2351_) == 0)
{
lean_object* v_tail_2352_; 
v_tail_2352_ = lean_ctor_get(v_as_2343_, 1);
lean_inc(v_tail_2352_);
lean_dec_ref(v_as_2343_);
v_as_2343_ = v_tail_2352_;
goto _start;
}
else
{
lean_object* v_tail_2354_; lean_object* v___x_2356_; uint8_t v_isShared_2357_; uint8_t v_isSharedCheck_2377_; 
v_tail_2354_ = lean_ctor_get(v_as_2343_, 1);
v_isSharedCheck_2377_ = !lean_is_exclusive(v_as_2343_);
if (v_isSharedCheck_2377_ == 0)
{
lean_object* v_unused_2378_; 
v_unused_2378_ = lean_ctor_get(v_as_2343_, 0);
lean_dec(v_unused_2378_);
v___x_2356_ = v_as_2343_;
v_isShared_2357_ = v_isSharedCheck_2377_;
goto v_resetjp_2355_;
}
else
{
lean_inc(v_tail_2354_);
lean_dec(v_as_2343_);
v___x_2356_ = lean_box(0);
v_isShared_2357_ = v_isSharedCheck_2377_;
goto v_resetjp_2355_;
}
v_resetjp_2355_:
{
lean_object* v_val_2358_; lean_object* v___x_2360_; uint8_t v_isShared_2361_; uint8_t v_isSharedCheck_2376_; 
v_val_2358_ = lean_ctor_get(v_head_2351_, 0);
v_isSharedCheck_2376_ = !lean_is_exclusive(v_head_2351_);
if (v_isSharedCheck_2376_ == 0)
{
v___x_2360_ = v_head_2351_;
v_isShared_2361_ = v_isSharedCheck_2376_;
goto v_resetjp_2359_;
}
else
{
lean_inc(v_val_2358_);
lean_dec(v_head_2351_);
v___x_2360_ = lean_box(0);
v_isShared_2361_ = v_isSharedCheck_2376_;
goto v_resetjp_2359_;
}
v_resetjp_2359_:
{
lean_object* v___x_2362_; uint8_t v___x_2363_; 
v___x_2362_ = lean_array_get_size(v_majorTypeArgs_2340_);
v___x_2363_ = lean_nat_dec_le(v___x_2362_, v_val_2358_);
lean_dec(v_val_2358_);
if (v___x_2363_ == 0)
{
lean_del_object(v___x_2360_);
lean_del_object(v___x_2356_);
v_as_2343_ = v_tail_2354_;
goto _start;
}
else
{
lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2369_; 
v___x_2365_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1));
v___x_2366_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__5, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__5);
lean_inc_ref(v_val_2341_);
v___x_2367_ = l_Lean_indentExpr(v_val_2341_);
if (v_isShared_2357_ == 0)
{
lean_ctor_set_tag(v___x_2356_, 7);
lean_ctor_set(v___x_2356_, 1, v___x_2367_);
lean_ctor_set(v___x_2356_, 0, v___x_2366_);
v___x_2369_ = v___x_2356_;
goto v_reusejp_2368_;
}
else
{
lean_object* v_reuseFailAlloc_2375_; 
v_reuseFailAlloc_2375_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2375_, 0, v___x_2366_);
lean_ctor_set(v_reuseFailAlloc_2375_, 1, v___x_2367_);
v___x_2369_ = v_reuseFailAlloc_2375_;
goto v_reusejp_2368_;
}
v_reusejp_2368_:
{
lean_object* v___x_2371_; 
if (v_isShared_2361_ == 0)
{
lean_ctor_set(v___x_2360_, 0, v___x_2369_);
v___x_2371_ = v___x_2360_;
goto v_reusejp_2370_;
}
else
{
lean_object* v_reuseFailAlloc_2374_; 
v_reuseFailAlloc_2374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2374_, 0, v___x_2369_);
v___x_2371_ = v_reuseFailAlloc_2374_;
goto v_reusejp_2370_;
}
v_reusejp_2370_:
{
lean_object* v___x_2372_; 
lean_inc(v_mvarId_2342_);
v___x_2372_ = l_Lean_Meta_throwTacticEx___redArg(v___x_2365_, v_mvarId_2342_, v___x_2371_, v___y_2344_, v___y_2345_, v___y_2346_, v___y_2347_);
if (lean_obj_tag(v___x_2372_) == 0)
{
lean_dec_ref(v___x_2372_);
v_as_2343_ = v_tail_2354_;
goto _start;
}
else
{
lean_dec(v_tail_2354_);
lean_dec(v_mvarId_2342_);
lean_dec_ref(v_val_2341_);
return v___x_2372_;
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
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_MVarId_induction_spec__0___boxed(lean_object* v_majorTypeArgs_2379_, lean_object* v_val_2380_, lean_object* v_mvarId_2381_, lean_object* v_as_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_){
_start:
{
lean_object* v_res_2388_; 
v_res_2388_ = l_List_forM___at___00Lean_MVarId_induction_spec__0(v_majorTypeArgs_2379_, v_val_2380_, v_mvarId_2381_, v_as_2382_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_);
lean_dec(v___y_2386_);
lean_dec_ref(v___y_2385_);
lean_dec(v___y_2384_);
lean_dec_ref(v___y_2383_);
lean_dec_ref(v_majorTypeArgs_2379_);
return v_res_2388_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__1(void){
_start:
{
lean_object* v___x_2390_; lean_object* v___x_2391_; 
v___x_2390_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__0));
v___x_2391_ = l_Lean_stringToMessageData(v___x_2390_);
return v___x_2391_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__3(void){
_start:
{
lean_object* v___x_2393_; lean_object* v___x_2394_; 
v___x_2393_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__2));
v___x_2394_ = l_Lean_stringToMessageData(v___x_2393_);
return v___x_2394_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__5(void){
_start:
{
lean_object* v___x_2396_; lean_object* v___x_2397_; 
v___x_2396_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__4));
v___x_2397_ = l_Lean_stringToMessageData(v___x_2396_);
return v___x_2397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4(lean_object* v_a_2398_, lean_object* v_val_2399_, lean_object* v_mvarId_2400_, lean_object* v_majorFVarId_2401_, lean_object* v_givenNames_2402_, lean_object* v_recursorName_2403_, lean_object* v_x_2404_, lean_object* v_x_2405_, lean_object* v_x_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_){
_start:
{
if (lean_obj_tag(v_x_2404_) == 5)
{
lean_object* v_fn_2412_; lean_object* v_arg_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; 
v_fn_2412_ = lean_ctor_get(v_x_2404_, 0);
lean_inc_ref(v_fn_2412_);
v_arg_2413_ = lean_ctor_get(v_x_2404_, 1);
lean_inc_ref(v_arg_2413_);
lean_dec_ref(v_x_2404_);
v___x_2414_ = lean_array_set(v_x_2405_, v_x_2406_, v_arg_2413_);
v___x_2415_ = lean_unsigned_to_nat(1u);
v___x_2416_ = lean_nat_sub(v_x_2406_, v___x_2415_);
lean_dec(v_x_2406_);
v_x_2404_ = v_fn_2412_;
v_x_2405_ = v___x_2414_;
v_x_2406_ = v___x_2416_;
goto _start;
}
else
{
uint8_t v_depElim_2418_; lean_object* v_paramsPos_2419_; lean_object* v___x_2420_; 
lean_dec(v_x_2406_);
lean_dec_ref(v_x_2404_);
v_depElim_2418_ = lean_ctor_get_uint8(v_a_2398_, sizeof(void*)*8);
v_paramsPos_2419_ = lean_ctor_get(v_a_2398_, 5);
lean_inc(v_paramsPos_2419_);
lean_inc(v_mvarId_2400_);
lean_inc_ref(v_val_2399_);
v___x_2420_ = l_List_forM___at___00Lean_MVarId_induction_spec__0(v_x_2405_, v_val_2399_, v_mvarId_2400_, v_paramsPos_2419_, v___y_2407_, v___y_2408_, v___y_2409_, v___y_2410_);
lean_dec_ref(v_x_2405_);
if (lean_obj_tag(v___x_2420_) == 0)
{
lean_object* v___x_2421_; lean_object* v___y_2423_; lean_object* v___y_2424_; lean_object* v___y_2425_; lean_object* v___y_2426_; lean_object* v___y_2427_; lean_object* v___y_2428_; lean_object* v___y_2429_; size_t v___y_2430_; lean_object* v___y_2431_; lean_object* v___y_2432_; lean_object* v___y_2433_; lean_object* v___y_2434_; lean_object* v___x_2439_; 
lean_dec_ref(v___x_2420_);
v___x_2421_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1));
lean_inc_ref(v_a_2398_);
lean_inc(v_mvarId_2400_);
v___x_2439_ = l_Lean_Meta_getMajorTypeIndices(v_mvarId_2400_, v___x_2421_, v_a_2398_, v_val_2399_, v___y_2407_, v___y_2408_, v___y_2409_, v___y_2410_);
if (lean_obj_tag(v___x_2439_) == 0)
{
lean_object* v_a_2440_; lean_object* v___x_2441_; 
v_a_2440_ = lean_ctor_get(v___x_2439_, 0);
lean_inc(v_a_2440_);
lean_dec_ref(v___x_2439_);
lean_inc(v_mvarId_2400_);
v___x_2441_ = l_Lean_MVarId_getType(v_mvarId_2400_, v___y_2407_, v___y_2408_, v___y_2409_, v___y_2410_);
if (lean_obj_tag(v___x_2441_) == 0)
{
lean_object* v_a_2442_; lean_object* v_cls_2443_; lean_object* v___y_2445_; lean_object* v___y_2446_; lean_object* v___y_2447_; lean_object* v___y_2448_; 
v_a_2442_ = lean_ctor_get(v___x_2441_, 0);
lean_inc(v_a_2442_);
lean_dec_ref(v___x_2441_);
v_cls_2443_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__2));
if (v_depElim_2418_ == 0)
{
lean_object* v___x_2531_; lean_object* v_a_2532_; lean_object* v___x_2534_; uint8_t v_isShared_2535_; uint8_t v_isSharedCheck_2554_; 
lean_inc(v_majorFVarId_2401_);
v___x_2531_ = l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2___redArg(v_a_2442_, v_majorFVarId_2401_, v___y_2408_);
v_a_2532_ = lean_ctor_get(v___x_2531_, 0);
v_isSharedCheck_2554_ = !lean_is_exclusive(v___x_2531_);
if (v_isSharedCheck_2554_ == 0)
{
v___x_2534_ = v___x_2531_;
v_isShared_2535_ = v_isSharedCheck_2554_;
goto v_resetjp_2533_;
}
else
{
lean_inc(v_a_2532_);
lean_dec(v___x_2531_);
v___x_2534_ = lean_box(0);
v_isShared_2535_ = v_isSharedCheck_2554_;
goto v_resetjp_2533_;
}
v_resetjp_2533_:
{
uint8_t v___x_2536_; 
v___x_2536_ = lean_unbox(v_a_2532_);
lean_dec(v_a_2532_);
if (v___x_2536_ == 0)
{
lean_del_object(v___x_2534_);
lean_dec(v_recursorName_2403_);
v___y_2445_ = v___y_2407_;
v___y_2446_ = v___y_2408_;
v___y_2447_ = v___y_2409_;
v___y_2448_ = v___y_2410_;
goto v___jp_2444_;
}
else
{
lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v___x_2543_; 
v___x_2537_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__3, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__3);
v___x_2538_ = l_Lean_MessageData_ofName(v_recursorName_2403_);
v___x_2539_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2539_, 0, v___x_2537_);
lean_ctor_set(v___x_2539_, 1, v___x_2538_);
v___x_2540_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__5, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__5_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__5);
v___x_2541_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2541_, 0, v___x_2539_);
lean_ctor_set(v___x_2541_, 1, v___x_2540_);
if (v_isShared_2535_ == 0)
{
lean_ctor_set_tag(v___x_2534_, 1);
lean_ctor_set(v___x_2534_, 0, v___x_2541_);
v___x_2543_ = v___x_2534_;
goto v_reusejp_2542_;
}
else
{
lean_object* v_reuseFailAlloc_2553_; 
v_reuseFailAlloc_2553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2553_, 0, v___x_2541_);
v___x_2543_ = v_reuseFailAlloc_2553_;
goto v_reusejp_2542_;
}
v_reusejp_2542_:
{
lean_object* v___x_2544_; 
lean_inc(v_mvarId_2400_);
v___x_2544_ = l_Lean_Meta_throwTacticEx___redArg(v___x_2421_, v_mvarId_2400_, v___x_2543_, v___y_2407_, v___y_2408_, v___y_2409_, v___y_2410_);
if (lean_obj_tag(v___x_2544_) == 0)
{
lean_dec_ref(v___x_2544_);
v___y_2445_ = v___y_2407_;
v___y_2446_ = v___y_2408_;
v___y_2447_ = v___y_2409_;
v___y_2448_ = v___y_2410_;
goto v___jp_2444_;
}
else
{
lean_object* v_a_2545_; lean_object* v___x_2547_; uint8_t v_isShared_2548_; uint8_t v_isSharedCheck_2552_; 
lean_dec(v_a_2440_);
lean_dec_ref(v_givenNames_2402_);
lean_dec(v_majorFVarId_2401_);
lean_dec(v_mvarId_2400_);
lean_dec_ref(v_a_2398_);
v_a_2545_ = lean_ctor_get(v___x_2544_, 0);
v_isSharedCheck_2552_ = !lean_is_exclusive(v___x_2544_);
if (v_isSharedCheck_2552_ == 0)
{
v___x_2547_ = v___x_2544_;
v_isShared_2548_ = v_isSharedCheck_2552_;
goto v_resetjp_2546_;
}
else
{
lean_inc(v_a_2545_);
lean_dec(v___x_2544_);
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
}
}
}
}
else
{
lean_dec(v_a_2442_);
lean_dec(v_recursorName_2403_);
v___y_2445_ = v___y_2407_;
v___y_2446_ = v___y_2408_;
v___y_2447_ = v___y_2409_;
v___y_2448_ = v___y_2410_;
goto v___jp_2444_;
}
v___jp_2444_:
{
size_t v_sz_2449_; size_t v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; uint8_t v___x_2453_; uint8_t v___x_2454_; lean_object* v___x_2455_; 
v_sz_2449_ = lean_array_size(v_a_2440_);
v___x_2450_ = ((size_t)0ULL);
lean_inc(v_a_2440_);
v___x_2451_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_induction_spec__1(v_sz_2449_, v___x_2450_, v_a_2440_);
lean_inc(v_majorFVarId_2401_);
v___x_2452_ = lean_array_push(v___x_2451_, v_majorFVarId_2401_);
v___x_2453_ = 1;
v___x_2454_ = 0;
v___x_2455_ = l_Lean_MVarId_revert(v_mvarId_2400_, v___x_2452_, v___x_2453_, v___x_2454_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_);
if (lean_obj_tag(v___x_2455_) == 0)
{
lean_object* v_a_2456_; lean_object* v_fst_2457_; lean_object* v_snd_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; 
v_a_2456_ = lean_ctor_get(v___x_2455_, 0);
lean_inc(v_a_2456_);
lean_dec_ref(v___x_2455_);
v_fst_2457_ = lean_ctor_get(v_a_2456_, 0);
lean_inc(v_fst_2457_);
v_snd_2458_ = lean_ctor_get(v_a_2456_, 1);
lean_inc(v_snd_2458_);
lean_dec(v_a_2456_);
v___x_2459_ = lean_array_get_size(v_a_2440_);
v___x_2460_ = lean_box(0);
v___x_2461_ = l_Lean_Meta_introNCore(v_snd_2458_, v___x_2459_, v___x_2460_, v___x_2454_, v___x_2453_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_);
if (lean_obj_tag(v___x_2461_) == 0)
{
lean_object* v_a_2462_; lean_object* v_fst_2463_; lean_object* v_snd_2464_; lean_object* v___x_2465_; 
v_a_2462_ = lean_ctor_get(v___x_2461_, 0);
lean_inc(v_a_2462_);
lean_dec_ref(v___x_2461_);
v_fst_2463_ = lean_ctor_get(v_a_2462_, 0);
lean_inc(v_fst_2463_);
v_snd_2464_ = lean_ctor_get(v_a_2462_, 1);
lean_inc(v_snd_2464_);
lean_dec(v_a_2462_);
v___x_2465_ = l_Lean_Meta_intro1Core(v_snd_2464_, v___x_2453_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_);
if (lean_obj_tag(v___x_2465_) == 0)
{
lean_object* v_a_2466_; lean_object* v_fst_2467_; lean_object* v_snd_2468_; lean_object* v___x_2470_; uint8_t v_isShared_2471_; uint8_t v_isSharedCheck_2506_; 
v_a_2466_ = lean_ctor_get(v___x_2465_, 0);
lean_inc(v_a_2466_);
lean_dec_ref(v___x_2465_);
v_fst_2467_ = lean_ctor_get(v_a_2466_, 0);
v_snd_2468_ = lean_ctor_get(v_a_2466_, 1);
v_isSharedCheck_2506_ = !lean_is_exclusive(v_a_2466_);
if (v_isSharedCheck_2506_ == 0)
{
v___x_2470_ = v_a_2466_;
v_isShared_2471_ = v_isSharedCheck_2506_;
goto v_resetjp_2469_;
}
else
{
lean_inc(v_snd_2468_);
lean_inc(v_fst_2467_);
lean_dec(v_a_2466_);
v___x_2470_ = lean_box(0);
v_isShared_2471_ = v_isSharedCheck_2506_;
goto v_resetjp_2469_;
}
v_resetjp_2469_:
{
lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2477_; 
v___x_2472_ = lean_box(0);
lean_inc(v_fst_2467_);
v___x_2473_ = l_Lean_mkFVar(v_fst_2467_);
lean_inc_ref(v___x_2473_);
v___x_2474_ = l_Lean_Meta_FVarSubst_insert(v___x_2472_, v_majorFVarId_2401_, v___x_2473_);
v___x_2475_ = lean_unsigned_to_nat(0u);
if (v_isShared_2471_ == 0)
{
lean_ctor_set(v___x_2470_, 1, v___x_2475_);
lean_ctor_set(v___x_2470_, 0, v___x_2474_);
v___x_2477_ = v___x_2470_;
goto v_reusejp_2476_;
}
else
{
lean_object* v_reuseFailAlloc_2505_; 
v_reuseFailAlloc_2505_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2505_, 0, v___x_2474_);
lean_ctor_set(v_reuseFailAlloc_2505_, 1, v___x_2475_);
v___x_2477_ = v_reuseFailAlloc_2505_;
goto v_reusejp_2476_;
}
v_reusejp_2476_:
{
lean_object* v___x_2478_; lean_object* v_options_2479_; uint8_t v_hasTrace_2480_; 
v___x_2478_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_induction_spec__2(v_fst_2463_, v_a_2440_, v_sz_2449_, v___x_2450_, v___x_2477_);
lean_dec(v_a_2440_);
v_options_2479_ = lean_ctor_get(v___y_2447_, 2);
v_hasTrace_2480_ = lean_ctor_get_uint8(v_options_2479_, sizeof(void*)*1);
if (v_hasTrace_2480_ == 0)
{
lean_object* v_fst_2481_; 
v_fst_2481_ = lean_ctor_get(v___x_2478_, 0);
lean_inc(v_fst_2481_);
lean_dec_ref(v___x_2478_);
lean_inc(v_snd_2468_);
v___y_2423_ = v_fst_2457_;
v___y_2424_ = v_fst_2467_;
v___y_2425_ = v___x_2473_;
v___y_2426_ = v_snd_2468_;
v___y_2427_ = v_fst_2481_;
v___y_2428_ = v_fst_2463_;
v___y_2429_ = v_snd_2468_;
v___y_2430_ = v___x_2450_;
v___y_2431_ = v___y_2445_;
v___y_2432_ = v___y_2446_;
v___y_2433_ = v___y_2447_;
v___y_2434_ = v___y_2448_;
goto v___jp_2422_;
}
else
{
lean_object* v_fst_2482_; lean_object* v___x_2484_; uint8_t v_isShared_2485_; uint8_t v_isSharedCheck_2503_; 
v_fst_2482_ = lean_ctor_get(v___x_2478_, 0);
v_isSharedCheck_2503_ = !lean_is_exclusive(v___x_2478_);
if (v_isSharedCheck_2503_ == 0)
{
lean_object* v_unused_2504_; 
v_unused_2504_ = lean_ctor_get(v___x_2478_, 1);
lean_dec(v_unused_2504_);
v___x_2484_ = v___x_2478_;
v_isShared_2485_ = v_isSharedCheck_2503_;
goto v_resetjp_2483_;
}
else
{
lean_inc(v_fst_2482_);
lean_dec(v___x_2478_);
v___x_2484_ = lean_box(0);
v_isShared_2485_ = v_isSharedCheck_2503_;
goto v_resetjp_2483_;
}
v_resetjp_2483_:
{
lean_object* v_inheritedTraceOptions_2486_; lean_object* v___x_2487_; uint8_t v___x_2488_; 
v_inheritedTraceOptions_2486_ = lean_ctor_get(v___y_2447_, 13);
v___x_2487_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5);
v___x_2488_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2486_, v_options_2479_, v___x_2487_);
if (v___x_2488_ == 0)
{
lean_del_object(v___x_2484_);
lean_inc(v_snd_2468_);
v___y_2423_ = v_fst_2457_;
v___y_2424_ = v_fst_2467_;
v___y_2425_ = v___x_2473_;
v___y_2426_ = v_snd_2468_;
v___y_2427_ = v_fst_2482_;
v___y_2428_ = v_fst_2463_;
v___y_2429_ = v_snd_2468_;
v___y_2430_ = v___x_2450_;
v___y_2431_ = v___y_2445_;
v___y_2432_ = v___y_2446_;
v___y_2433_ = v___y_2447_;
v___y_2434_ = v___y_2448_;
goto v___jp_2422_;
}
else
{
lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2492_; 
v___x_2489_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__1);
lean_inc(v_snd_2468_);
v___x_2490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2490_, 0, v_snd_2468_);
if (v_isShared_2485_ == 0)
{
lean_ctor_set_tag(v___x_2484_, 7);
lean_ctor_set(v___x_2484_, 1, v___x_2490_);
lean_ctor_set(v___x_2484_, 0, v___x_2489_);
v___x_2492_ = v___x_2484_;
goto v_reusejp_2491_;
}
else
{
lean_object* v_reuseFailAlloc_2502_; 
v_reuseFailAlloc_2502_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2502_, 0, v___x_2489_);
lean_ctor_set(v_reuseFailAlloc_2502_, 1, v___x_2490_);
v___x_2492_ = v_reuseFailAlloc_2502_;
goto v_reusejp_2491_;
}
v_reusejp_2491_:
{
lean_object* v___x_2493_; 
v___x_2493_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1(v_cls_2443_, v___x_2492_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_);
if (lean_obj_tag(v___x_2493_) == 0)
{
lean_dec_ref(v___x_2493_);
lean_inc(v_snd_2468_);
v___y_2423_ = v_fst_2457_;
v___y_2424_ = v_fst_2467_;
v___y_2425_ = v___x_2473_;
v___y_2426_ = v_snd_2468_;
v___y_2427_ = v_fst_2482_;
v___y_2428_ = v_fst_2463_;
v___y_2429_ = v_snd_2468_;
v___y_2430_ = v___x_2450_;
v___y_2431_ = v___y_2445_;
v___y_2432_ = v___y_2446_;
v___y_2433_ = v___y_2447_;
v___y_2434_ = v___y_2448_;
goto v___jp_2422_;
}
else
{
lean_object* v_a_2494_; lean_object* v___x_2496_; uint8_t v_isShared_2497_; uint8_t v_isSharedCheck_2501_; 
lean_dec(v_fst_2482_);
lean_dec_ref(v___x_2473_);
lean_dec(v_snd_2468_);
lean_dec(v_fst_2467_);
lean_dec(v_fst_2463_);
lean_dec(v_fst_2457_);
lean_dec_ref(v_givenNames_2402_);
lean_dec_ref(v_a_2398_);
v_a_2494_ = lean_ctor_get(v___x_2493_, 0);
v_isSharedCheck_2501_ = !lean_is_exclusive(v___x_2493_);
if (v_isSharedCheck_2501_ == 0)
{
v___x_2496_ = v___x_2493_;
v_isShared_2497_ = v_isSharedCheck_2501_;
goto v_resetjp_2495_;
}
else
{
lean_inc(v_a_2494_);
lean_dec(v___x_2493_);
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
}
}
}
}
}
else
{
lean_object* v_a_2507_; lean_object* v___x_2509_; uint8_t v_isShared_2510_; uint8_t v_isSharedCheck_2514_; 
lean_dec(v_fst_2463_);
lean_dec(v_fst_2457_);
lean_dec(v_a_2440_);
lean_dec_ref(v_givenNames_2402_);
lean_dec(v_majorFVarId_2401_);
lean_dec_ref(v_a_2398_);
v_a_2507_ = lean_ctor_get(v___x_2465_, 0);
v_isSharedCheck_2514_ = !lean_is_exclusive(v___x_2465_);
if (v_isSharedCheck_2514_ == 0)
{
v___x_2509_ = v___x_2465_;
v_isShared_2510_ = v_isSharedCheck_2514_;
goto v_resetjp_2508_;
}
else
{
lean_inc(v_a_2507_);
lean_dec(v___x_2465_);
v___x_2509_ = lean_box(0);
v_isShared_2510_ = v_isSharedCheck_2514_;
goto v_resetjp_2508_;
}
v_resetjp_2508_:
{
lean_object* v___x_2512_; 
if (v_isShared_2510_ == 0)
{
v___x_2512_ = v___x_2509_;
goto v_reusejp_2511_;
}
else
{
lean_object* v_reuseFailAlloc_2513_; 
v_reuseFailAlloc_2513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2513_, 0, v_a_2507_);
v___x_2512_ = v_reuseFailAlloc_2513_;
goto v_reusejp_2511_;
}
v_reusejp_2511_:
{
return v___x_2512_;
}
}
}
}
else
{
lean_object* v_a_2515_; lean_object* v___x_2517_; uint8_t v_isShared_2518_; uint8_t v_isSharedCheck_2522_; 
lean_dec(v_fst_2457_);
lean_dec(v_a_2440_);
lean_dec_ref(v_givenNames_2402_);
lean_dec(v_majorFVarId_2401_);
lean_dec_ref(v_a_2398_);
v_a_2515_ = lean_ctor_get(v___x_2461_, 0);
v_isSharedCheck_2522_ = !lean_is_exclusive(v___x_2461_);
if (v_isSharedCheck_2522_ == 0)
{
v___x_2517_ = v___x_2461_;
v_isShared_2518_ = v_isSharedCheck_2522_;
goto v_resetjp_2516_;
}
else
{
lean_inc(v_a_2515_);
lean_dec(v___x_2461_);
v___x_2517_ = lean_box(0);
v_isShared_2518_ = v_isSharedCheck_2522_;
goto v_resetjp_2516_;
}
v_resetjp_2516_:
{
lean_object* v___x_2520_; 
if (v_isShared_2518_ == 0)
{
v___x_2520_ = v___x_2517_;
goto v_reusejp_2519_;
}
else
{
lean_object* v_reuseFailAlloc_2521_; 
v_reuseFailAlloc_2521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2521_, 0, v_a_2515_);
v___x_2520_ = v_reuseFailAlloc_2521_;
goto v_reusejp_2519_;
}
v_reusejp_2519_:
{
return v___x_2520_;
}
}
}
}
else
{
lean_object* v_a_2523_; lean_object* v___x_2525_; uint8_t v_isShared_2526_; uint8_t v_isSharedCheck_2530_; 
lean_dec(v_a_2440_);
lean_dec_ref(v_givenNames_2402_);
lean_dec(v_majorFVarId_2401_);
lean_dec_ref(v_a_2398_);
v_a_2523_ = lean_ctor_get(v___x_2455_, 0);
v_isSharedCheck_2530_ = !lean_is_exclusive(v___x_2455_);
if (v_isSharedCheck_2530_ == 0)
{
v___x_2525_ = v___x_2455_;
v_isShared_2526_ = v_isSharedCheck_2530_;
goto v_resetjp_2524_;
}
else
{
lean_inc(v_a_2523_);
lean_dec(v___x_2455_);
v___x_2525_ = lean_box(0);
v_isShared_2526_ = v_isSharedCheck_2530_;
goto v_resetjp_2524_;
}
v_resetjp_2524_:
{
lean_object* v___x_2528_; 
if (v_isShared_2526_ == 0)
{
v___x_2528_ = v___x_2525_;
goto v_reusejp_2527_;
}
else
{
lean_object* v_reuseFailAlloc_2529_; 
v_reuseFailAlloc_2529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2529_, 0, v_a_2523_);
v___x_2528_ = v_reuseFailAlloc_2529_;
goto v_reusejp_2527_;
}
v_reusejp_2527_:
{
return v___x_2528_;
}
}
}
}
}
else
{
lean_object* v_a_2555_; lean_object* v___x_2557_; uint8_t v_isShared_2558_; uint8_t v_isSharedCheck_2562_; 
lean_dec(v_a_2440_);
lean_dec(v_recursorName_2403_);
lean_dec_ref(v_givenNames_2402_);
lean_dec(v_majorFVarId_2401_);
lean_dec(v_mvarId_2400_);
lean_dec_ref(v_a_2398_);
v_a_2555_ = lean_ctor_get(v___x_2441_, 0);
v_isSharedCheck_2562_ = !lean_is_exclusive(v___x_2441_);
if (v_isSharedCheck_2562_ == 0)
{
v___x_2557_ = v___x_2441_;
v_isShared_2558_ = v_isSharedCheck_2562_;
goto v_resetjp_2556_;
}
else
{
lean_inc(v_a_2555_);
lean_dec(v___x_2441_);
v___x_2557_ = lean_box(0);
v_isShared_2558_ = v_isSharedCheck_2562_;
goto v_resetjp_2556_;
}
v_resetjp_2556_:
{
lean_object* v___x_2560_; 
if (v_isShared_2558_ == 0)
{
v___x_2560_ = v___x_2557_;
goto v_reusejp_2559_;
}
else
{
lean_object* v_reuseFailAlloc_2561_; 
v_reuseFailAlloc_2561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2561_, 0, v_a_2555_);
v___x_2560_ = v_reuseFailAlloc_2561_;
goto v_reusejp_2559_;
}
v_reusejp_2559_:
{
return v___x_2560_;
}
}
}
}
else
{
lean_object* v_a_2563_; lean_object* v___x_2565_; uint8_t v_isShared_2566_; uint8_t v_isSharedCheck_2570_; 
lean_dec(v_recursorName_2403_);
lean_dec_ref(v_givenNames_2402_);
lean_dec(v_majorFVarId_2401_);
lean_dec(v_mvarId_2400_);
lean_dec_ref(v_a_2398_);
v_a_2563_ = lean_ctor_get(v___x_2439_, 0);
v_isSharedCheck_2570_ = !lean_is_exclusive(v___x_2439_);
if (v_isSharedCheck_2570_ == 0)
{
v___x_2565_ = v___x_2439_;
v_isShared_2566_ = v_isSharedCheck_2570_;
goto v_resetjp_2564_;
}
else
{
lean_inc(v_a_2563_);
lean_dec(v___x_2439_);
v___x_2565_ = lean_box(0);
v_isShared_2566_ = v_isSharedCheck_2570_;
goto v_resetjp_2564_;
}
v_resetjp_2564_:
{
lean_object* v___x_2568_; 
if (v_isShared_2566_ == 0)
{
v___x_2568_ = v___x_2565_;
goto v_reusejp_2567_;
}
else
{
lean_object* v_reuseFailAlloc_2569_; 
v_reuseFailAlloc_2569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2569_, 0, v_a_2563_);
v___x_2568_ = v_reuseFailAlloc_2569_;
goto v_reusejp_2567_;
}
v_reusejp_2567_:
{
return v___x_2568_;
}
}
}
v___jp_2422_:
{
size_t v_sz_2435_; lean_object* v___x_2436_; lean_object* v___f_2437_; lean_object* v___x_2438_; 
v_sz_2435_ = lean_array_size(v___y_2428_);
v___x_2436_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__3(v_sz_2435_, v___y_2430_, v___y_2428_);
v___f_2437_ = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4___lam__0___boxed), 14, 9);
lean_closure_set(v___f_2437_, 0, v___y_2426_);
lean_closure_set(v___f_2437_, 1, v___x_2421_);
lean_closure_set(v___f_2437_, 2, v___y_2424_);
lean_closure_set(v___f_2437_, 3, v_a_2398_);
lean_closure_set(v___f_2437_, 4, v___x_2436_);
lean_closure_set(v___f_2437_, 5, v_givenNames_2402_);
lean_closure_set(v___f_2437_, 6, v___y_2423_);
lean_closure_set(v___f_2437_, 7, v___y_2425_);
lean_closure_set(v___f_2437_, 8, v___y_2427_);
v___x_2438_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___redArg(v___y_2429_, v___f_2437_, v___y_2431_, v___y_2432_, v___y_2433_, v___y_2434_);
return v___x_2438_;
}
}
else
{
lean_object* v_a_2571_; lean_object* v___x_2573_; uint8_t v_isShared_2574_; uint8_t v_isSharedCheck_2578_; 
lean_dec(v_recursorName_2403_);
lean_dec_ref(v_givenNames_2402_);
lean_dec(v_majorFVarId_2401_);
lean_dec(v_mvarId_2400_);
lean_dec_ref(v_val_2399_);
lean_dec_ref(v_a_2398_);
v_a_2571_ = lean_ctor_get(v___x_2420_, 0);
v_isSharedCheck_2578_ = !lean_is_exclusive(v___x_2420_);
if (v_isSharedCheck_2578_ == 0)
{
v___x_2573_ = v___x_2420_;
v_isShared_2574_ = v_isSharedCheck_2578_;
goto v_resetjp_2572_;
}
else
{
lean_inc(v_a_2571_);
lean_dec(v___x_2420_);
v___x_2573_ = lean_box(0);
v_isShared_2574_ = v_isSharedCheck_2578_;
goto v_resetjp_2572_;
}
v_resetjp_2572_:
{
lean_object* v___x_2576_; 
if (v_isShared_2574_ == 0)
{
v___x_2576_ = v___x_2573_;
goto v_reusejp_2575_;
}
else
{
lean_object* v_reuseFailAlloc_2577_; 
v_reuseFailAlloc_2577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2577_, 0, v_a_2571_);
v___x_2576_ = v_reuseFailAlloc_2577_;
goto v_reusejp_2575_;
}
v_reusejp_2575_:
{
return v___x_2576_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___boxed(lean_object* v_a_2579_, lean_object* v_val_2580_, lean_object* v_mvarId_2581_, lean_object* v_majorFVarId_2582_, lean_object* v_givenNames_2583_, lean_object* v_recursorName_2584_, lean_object* v_x_2585_, lean_object* v_x_2586_, lean_object* v_x_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_){
_start:
{
lean_object* v_res_2593_; 
v_res_2593_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4(v_a_2579_, v_val_2580_, v_mvarId_2581_, v_majorFVarId_2582_, v_givenNames_2583_, v_recursorName_2584_, v_x_2585_, v_x_2586_, v_x_2587_, v___y_2588_, v___y_2589_, v___y_2590_, v___y_2591_);
lean_dec(v___y_2591_);
lean_dec_ref(v___y_2590_);
lean_dec(v___y_2589_);
lean_dec_ref(v___y_2588_);
return v_res_2593_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4(lean_object* v_val_2594_, lean_object* v_mvarId_2595_, lean_object* v_a_2596_, lean_object* v_majorFVarId_2597_, lean_object* v_givenNames_2598_, lean_object* v_recursorName_2599_, lean_object* v_x_2600_, lean_object* v_x_2601_, lean_object* v_x_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_){
_start:
{
if (lean_obj_tag(v_x_2600_) == 5)
{
lean_object* v_fn_2608_; lean_object* v_arg_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; 
v_fn_2608_ = lean_ctor_get(v_x_2600_, 0);
lean_inc_ref(v_fn_2608_);
v_arg_2609_ = lean_ctor_get(v_x_2600_, 1);
lean_inc_ref(v_arg_2609_);
lean_dec_ref(v_x_2600_);
v___x_2610_ = lean_array_set(v_x_2601_, v_x_2602_, v_arg_2609_);
v___x_2611_ = lean_unsigned_to_nat(1u);
v___x_2612_ = lean_nat_sub(v_x_2602_, v___x_2611_);
v___x_2613_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4(v_a_2596_, v_val_2594_, v_mvarId_2595_, v_majorFVarId_2597_, v_givenNames_2598_, v_recursorName_2599_, v_fn_2608_, v___x_2610_, v___x_2612_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_);
return v___x_2613_;
}
else
{
uint8_t v_depElim_2614_; lean_object* v_paramsPos_2615_; lean_object* v___x_2616_; 
lean_dec_ref(v_x_2600_);
v_depElim_2614_ = lean_ctor_get_uint8(v_a_2596_, sizeof(void*)*8);
v_paramsPos_2615_ = lean_ctor_get(v_a_2596_, 5);
lean_inc(v_paramsPos_2615_);
lean_inc(v_mvarId_2595_);
lean_inc_ref(v_val_2594_);
v___x_2616_ = l_List_forM___at___00Lean_MVarId_induction_spec__0(v_x_2601_, v_val_2594_, v_mvarId_2595_, v_paramsPos_2615_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_);
lean_dec_ref(v_x_2601_);
if (lean_obj_tag(v___x_2616_) == 0)
{
lean_object* v___x_2617_; lean_object* v___y_2619_; lean_object* v___y_2620_; lean_object* v___y_2621_; lean_object* v___y_2622_; lean_object* v___y_2623_; lean_object* v___y_2624_; size_t v___y_2625_; lean_object* v___y_2626_; lean_object* v___y_2627_; lean_object* v___y_2628_; lean_object* v___y_2629_; lean_object* v___y_2630_; lean_object* v___x_2635_; 
lean_dec_ref(v___x_2616_);
v___x_2617_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1));
lean_inc_ref(v_a_2596_);
lean_inc(v_mvarId_2595_);
v___x_2635_ = l_Lean_Meta_getMajorTypeIndices(v_mvarId_2595_, v___x_2617_, v_a_2596_, v_val_2594_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_);
if (lean_obj_tag(v___x_2635_) == 0)
{
lean_object* v_a_2636_; lean_object* v___x_2637_; 
v_a_2636_ = lean_ctor_get(v___x_2635_, 0);
lean_inc(v_a_2636_);
lean_dec_ref(v___x_2635_);
lean_inc(v_mvarId_2595_);
v___x_2637_ = l_Lean_MVarId_getType(v_mvarId_2595_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_);
if (lean_obj_tag(v___x_2637_) == 0)
{
lean_object* v_a_2638_; lean_object* v_cls_2639_; lean_object* v___y_2641_; lean_object* v___y_2642_; lean_object* v___y_2643_; lean_object* v___y_2644_; 
v_a_2638_ = lean_ctor_get(v___x_2637_, 0);
lean_inc(v_a_2638_);
lean_dec_ref(v___x_2637_);
v_cls_2639_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__2));
if (v_depElim_2614_ == 0)
{
lean_object* v___x_2727_; lean_object* v_a_2728_; lean_object* v___x_2730_; uint8_t v_isShared_2731_; uint8_t v_isSharedCheck_2750_; 
lean_inc(v_majorFVarId_2597_);
v___x_2727_ = l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2___redArg(v_a_2638_, v_majorFVarId_2597_, v___y_2604_);
v_a_2728_ = lean_ctor_get(v___x_2727_, 0);
v_isSharedCheck_2750_ = !lean_is_exclusive(v___x_2727_);
if (v_isSharedCheck_2750_ == 0)
{
v___x_2730_ = v___x_2727_;
v_isShared_2731_ = v_isSharedCheck_2750_;
goto v_resetjp_2729_;
}
else
{
lean_inc(v_a_2728_);
lean_dec(v___x_2727_);
v___x_2730_ = lean_box(0);
v_isShared_2731_ = v_isSharedCheck_2750_;
goto v_resetjp_2729_;
}
v_resetjp_2729_:
{
uint8_t v___x_2732_; 
v___x_2732_ = lean_unbox(v_a_2728_);
lean_dec(v_a_2728_);
if (v___x_2732_ == 0)
{
lean_del_object(v___x_2730_);
lean_dec(v_recursorName_2599_);
v___y_2641_ = v___y_2603_;
v___y_2642_ = v___y_2604_;
v___y_2643_ = v___y_2605_;
v___y_2644_ = v___y_2606_;
goto v___jp_2640_;
}
else
{
lean_object* v___x_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2739_; 
v___x_2733_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__3, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__3);
v___x_2734_ = l_Lean_MessageData_ofName(v_recursorName_2599_);
v___x_2735_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2735_, 0, v___x_2733_);
lean_ctor_set(v___x_2735_, 1, v___x_2734_);
v___x_2736_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__5, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__5_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__5);
v___x_2737_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2737_, 0, v___x_2735_);
lean_ctor_set(v___x_2737_, 1, v___x_2736_);
if (v_isShared_2731_ == 0)
{
lean_ctor_set_tag(v___x_2730_, 1);
lean_ctor_set(v___x_2730_, 0, v___x_2737_);
v___x_2739_ = v___x_2730_;
goto v_reusejp_2738_;
}
else
{
lean_object* v_reuseFailAlloc_2749_; 
v_reuseFailAlloc_2749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2749_, 0, v___x_2737_);
v___x_2739_ = v_reuseFailAlloc_2749_;
goto v_reusejp_2738_;
}
v_reusejp_2738_:
{
lean_object* v___x_2740_; 
lean_inc(v_mvarId_2595_);
v___x_2740_ = l_Lean_Meta_throwTacticEx___redArg(v___x_2617_, v_mvarId_2595_, v___x_2739_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_);
if (lean_obj_tag(v___x_2740_) == 0)
{
lean_dec_ref(v___x_2740_);
v___y_2641_ = v___y_2603_;
v___y_2642_ = v___y_2604_;
v___y_2643_ = v___y_2605_;
v___y_2644_ = v___y_2606_;
goto v___jp_2640_;
}
else
{
lean_object* v_a_2741_; lean_object* v___x_2743_; uint8_t v_isShared_2744_; uint8_t v_isSharedCheck_2748_; 
lean_dec(v_a_2636_);
lean_dec_ref(v_givenNames_2598_);
lean_dec(v_majorFVarId_2597_);
lean_dec_ref(v_a_2596_);
lean_dec(v_mvarId_2595_);
v_a_2741_ = lean_ctor_get(v___x_2740_, 0);
v_isSharedCheck_2748_ = !lean_is_exclusive(v___x_2740_);
if (v_isSharedCheck_2748_ == 0)
{
v___x_2743_ = v___x_2740_;
v_isShared_2744_ = v_isSharedCheck_2748_;
goto v_resetjp_2742_;
}
else
{
lean_inc(v_a_2741_);
lean_dec(v___x_2740_);
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
}
}
}
}
else
{
lean_dec(v_a_2638_);
lean_dec(v_recursorName_2599_);
v___y_2641_ = v___y_2603_;
v___y_2642_ = v___y_2604_;
v___y_2643_ = v___y_2605_;
v___y_2644_ = v___y_2606_;
goto v___jp_2640_;
}
v___jp_2640_:
{
size_t v_sz_2645_; size_t v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; uint8_t v___x_2649_; uint8_t v___x_2650_; lean_object* v___x_2651_; 
v_sz_2645_ = lean_array_size(v_a_2636_);
v___x_2646_ = ((size_t)0ULL);
lean_inc(v_a_2636_);
v___x_2647_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_induction_spec__1(v_sz_2645_, v___x_2646_, v_a_2636_);
lean_inc(v_majorFVarId_2597_);
v___x_2648_ = lean_array_push(v___x_2647_, v_majorFVarId_2597_);
v___x_2649_ = 1;
v___x_2650_ = 0;
v___x_2651_ = l_Lean_MVarId_revert(v_mvarId_2595_, v___x_2648_, v___x_2649_, v___x_2650_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_);
if (lean_obj_tag(v___x_2651_) == 0)
{
lean_object* v_a_2652_; lean_object* v_fst_2653_; lean_object* v_snd_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; 
v_a_2652_ = lean_ctor_get(v___x_2651_, 0);
lean_inc(v_a_2652_);
lean_dec_ref(v___x_2651_);
v_fst_2653_ = lean_ctor_get(v_a_2652_, 0);
lean_inc(v_fst_2653_);
v_snd_2654_ = lean_ctor_get(v_a_2652_, 1);
lean_inc(v_snd_2654_);
lean_dec(v_a_2652_);
v___x_2655_ = lean_array_get_size(v_a_2636_);
v___x_2656_ = lean_box(0);
v___x_2657_ = l_Lean_Meta_introNCore(v_snd_2654_, v___x_2655_, v___x_2656_, v___x_2650_, v___x_2649_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_);
if (lean_obj_tag(v___x_2657_) == 0)
{
lean_object* v_a_2658_; lean_object* v_fst_2659_; lean_object* v_snd_2660_; lean_object* v___x_2661_; 
v_a_2658_ = lean_ctor_get(v___x_2657_, 0);
lean_inc(v_a_2658_);
lean_dec_ref(v___x_2657_);
v_fst_2659_ = lean_ctor_get(v_a_2658_, 0);
lean_inc(v_fst_2659_);
v_snd_2660_ = lean_ctor_get(v_a_2658_, 1);
lean_inc(v_snd_2660_);
lean_dec(v_a_2658_);
v___x_2661_ = l_Lean_Meta_intro1Core(v_snd_2660_, v___x_2649_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_);
if (lean_obj_tag(v___x_2661_) == 0)
{
lean_object* v_a_2662_; lean_object* v_fst_2663_; lean_object* v_snd_2664_; lean_object* v___x_2666_; uint8_t v_isShared_2667_; uint8_t v_isSharedCheck_2702_; 
v_a_2662_ = lean_ctor_get(v___x_2661_, 0);
lean_inc(v_a_2662_);
lean_dec_ref(v___x_2661_);
v_fst_2663_ = lean_ctor_get(v_a_2662_, 0);
v_snd_2664_ = lean_ctor_get(v_a_2662_, 1);
v_isSharedCheck_2702_ = !lean_is_exclusive(v_a_2662_);
if (v_isSharedCheck_2702_ == 0)
{
v___x_2666_ = v_a_2662_;
v_isShared_2667_ = v_isSharedCheck_2702_;
goto v_resetjp_2665_;
}
else
{
lean_inc(v_snd_2664_);
lean_inc(v_fst_2663_);
lean_dec(v_a_2662_);
v___x_2666_ = lean_box(0);
v_isShared_2667_ = v_isSharedCheck_2702_;
goto v_resetjp_2665_;
}
v_resetjp_2665_:
{
lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2673_; 
v___x_2668_ = lean_box(0);
lean_inc(v_fst_2663_);
v___x_2669_ = l_Lean_mkFVar(v_fst_2663_);
lean_inc_ref(v___x_2669_);
v___x_2670_ = l_Lean_Meta_FVarSubst_insert(v___x_2668_, v_majorFVarId_2597_, v___x_2669_);
v___x_2671_ = lean_unsigned_to_nat(0u);
if (v_isShared_2667_ == 0)
{
lean_ctor_set(v___x_2666_, 1, v___x_2671_);
lean_ctor_set(v___x_2666_, 0, v___x_2670_);
v___x_2673_ = v___x_2666_;
goto v_reusejp_2672_;
}
else
{
lean_object* v_reuseFailAlloc_2701_; 
v_reuseFailAlloc_2701_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2701_, 0, v___x_2670_);
lean_ctor_set(v_reuseFailAlloc_2701_, 1, v___x_2671_);
v___x_2673_ = v_reuseFailAlloc_2701_;
goto v_reusejp_2672_;
}
v_reusejp_2672_:
{
lean_object* v___x_2674_; lean_object* v_options_2675_; uint8_t v_hasTrace_2676_; 
v___x_2674_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_induction_spec__2(v_fst_2659_, v_a_2636_, v_sz_2645_, v___x_2646_, v___x_2673_);
lean_dec(v_a_2636_);
v_options_2675_ = lean_ctor_get(v___y_2643_, 2);
v_hasTrace_2676_ = lean_ctor_get_uint8(v_options_2675_, sizeof(void*)*1);
if (v_hasTrace_2676_ == 0)
{
lean_object* v_fst_2677_; 
v_fst_2677_ = lean_ctor_get(v___x_2674_, 0);
lean_inc(v_fst_2677_);
lean_dec_ref(v___x_2674_);
lean_inc(v_snd_2664_);
v___y_2619_ = v___x_2669_;
v___y_2620_ = v_fst_2663_;
v___y_2621_ = v_fst_2677_;
v___y_2622_ = v_fst_2653_;
v___y_2623_ = v_snd_2664_;
v___y_2624_ = v_fst_2659_;
v___y_2625_ = v___x_2646_;
v___y_2626_ = v_snd_2664_;
v___y_2627_ = v___y_2641_;
v___y_2628_ = v___y_2642_;
v___y_2629_ = v___y_2643_;
v___y_2630_ = v___y_2644_;
goto v___jp_2618_;
}
else
{
lean_object* v_fst_2678_; lean_object* v___x_2680_; uint8_t v_isShared_2681_; uint8_t v_isSharedCheck_2699_; 
v_fst_2678_ = lean_ctor_get(v___x_2674_, 0);
v_isSharedCheck_2699_ = !lean_is_exclusive(v___x_2674_);
if (v_isSharedCheck_2699_ == 0)
{
lean_object* v_unused_2700_; 
v_unused_2700_ = lean_ctor_get(v___x_2674_, 1);
lean_dec(v_unused_2700_);
v___x_2680_ = v___x_2674_;
v_isShared_2681_ = v_isSharedCheck_2699_;
goto v_resetjp_2679_;
}
else
{
lean_inc(v_fst_2678_);
lean_dec(v___x_2674_);
v___x_2680_ = lean_box(0);
v_isShared_2681_ = v_isSharedCheck_2699_;
goto v_resetjp_2679_;
}
v_resetjp_2679_:
{
lean_object* v_inheritedTraceOptions_2682_; lean_object* v___x_2683_; uint8_t v___x_2684_; 
v_inheritedTraceOptions_2682_ = lean_ctor_get(v___y_2643_, 13);
v___x_2683_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5);
v___x_2684_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2682_, v_options_2675_, v___x_2683_);
if (v___x_2684_ == 0)
{
lean_del_object(v___x_2680_);
lean_inc(v_snd_2664_);
v___y_2619_ = v___x_2669_;
v___y_2620_ = v_fst_2663_;
v___y_2621_ = v_fst_2678_;
v___y_2622_ = v_fst_2653_;
v___y_2623_ = v_snd_2664_;
v___y_2624_ = v_fst_2659_;
v___y_2625_ = v___x_2646_;
v___y_2626_ = v_snd_2664_;
v___y_2627_ = v___y_2641_;
v___y_2628_ = v___y_2642_;
v___y_2629_ = v___y_2643_;
v___y_2630_ = v___y_2644_;
goto v___jp_2618_;
}
else
{
lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2688_; 
v___x_2685_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__1);
lean_inc(v_snd_2664_);
v___x_2686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2686_, 0, v_snd_2664_);
if (v_isShared_2681_ == 0)
{
lean_ctor_set_tag(v___x_2680_, 7);
lean_ctor_set(v___x_2680_, 1, v___x_2686_);
lean_ctor_set(v___x_2680_, 0, v___x_2685_);
v___x_2688_ = v___x_2680_;
goto v_reusejp_2687_;
}
else
{
lean_object* v_reuseFailAlloc_2698_; 
v_reuseFailAlloc_2698_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2698_, 0, v___x_2685_);
lean_ctor_set(v_reuseFailAlloc_2698_, 1, v___x_2686_);
v___x_2688_ = v_reuseFailAlloc_2698_;
goto v_reusejp_2687_;
}
v_reusejp_2687_:
{
lean_object* v___x_2689_; 
v___x_2689_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1(v_cls_2639_, v___x_2688_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_);
if (lean_obj_tag(v___x_2689_) == 0)
{
lean_dec_ref(v___x_2689_);
lean_inc(v_snd_2664_);
v___y_2619_ = v___x_2669_;
v___y_2620_ = v_fst_2663_;
v___y_2621_ = v_fst_2678_;
v___y_2622_ = v_fst_2653_;
v___y_2623_ = v_snd_2664_;
v___y_2624_ = v_fst_2659_;
v___y_2625_ = v___x_2646_;
v___y_2626_ = v_snd_2664_;
v___y_2627_ = v___y_2641_;
v___y_2628_ = v___y_2642_;
v___y_2629_ = v___y_2643_;
v___y_2630_ = v___y_2644_;
goto v___jp_2618_;
}
else
{
lean_object* v_a_2690_; lean_object* v___x_2692_; uint8_t v_isShared_2693_; uint8_t v_isSharedCheck_2697_; 
lean_dec(v_fst_2678_);
lean_dec_ref(v___x_2669_);
lean_dec(v_snd_2664_);
lean_dec(v_fst_2663_);
lean_dec(v_fst_2659_);
lean_dec(v_fst_2653_);
lean_dec_ref(v_givenNames_2598_);
lean_dec_ref(v_a_2596_);
v_a_2690_ = lean_ctor_get(v___x_2689_, 0);
v_isSharedCheck_2697_ = !lean_is_exclusive(v___x_2689_);
if (v_isSharedCheck_2697_ == 0)
{
v___x_2692_ = v___x_2689_;
v_isShared_2693_ = v_isSharedCheck_2697_;
goto v_resetjp_2691_;
}
else
{
lean_inc(v_a_2690_);
lean_dec(v___x_2689_);
v___x_2692_ = lean_box(0);
v_isShared_2693_ = v_isSharedCheck_2697_;
goto v_resetjp_2691_;
}
v_resetjp_2691_:
{
lean_object* v___x_2695_; 
if (v_isShared_2693_ == 0)
{
v___x_2695_ = v___x_2692_;
goto v_reusejp_2694_;
}
else
{
lean_object* v_reuseFailAlloc_2696_; 
v_reuseFailAlloc_2696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2696_, 0, v_a_2690_);
v___x_2695_ = v_reuseFailAlloc_2696_;
goto v_reusejp_2694_;
}
v_reusejp_2694_:
{
return v___x_2695_;
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
lean_object* v_a_2703_; lean_object* v___x_2705_; uint8_t v_isShared_2706_; uint8_t v_isSharedCheck_2710_; 
lean_dec(v_fst_2659_);
lean_dec(v_fst_2653_);
lean_dec(v_a_2636_);
lean_dec_ref(v_givenNames_2598_);
lean_dec(v_majorFVarId_2597_);
lean_dec_ref(v_a_2596_);
v_a_2703_ = lean_ctor_get(v___x_2661_, 0);
v_isSharedCheck_2710_ = !lean_is_exclusive(v___x_2661_);
if (v_isSharedCheck_2710_ == 0)
{
v___x_2705_ = v___x_2661_;
v_isShared_2706_ = v_isSharedCheck_2710_;
goto v_resetjp_2704_;
}
else
{
lean_inc(v_a_2703_);
lean_dec(v___x_2661_);
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
lean_dec(v_fst_2653_);
lean_dec(v_a_2636_);
lean_dec_ref(v_givenNames_2598_);
lean_dec(v_majorFVarId_2597_);
lean_dec_ref(v_a_2596_);
v_a_2711_ = lean_ctor_get(v___x_2657_, 0);
v_isSharedCheck_2718_ = !lean_is_exclusive(v___x_2657_);
if (v_isSharedCheck_2718_ == 0)
{
v___x_2713_ = v___x_2657_;
v_isShared_2714_ = v_isSharedCheck_2718_;
goto v_resetjp_2712_;
}
else
{
lean_inc(v_a_2711_);
lean_dec(v___x_2657_);
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
else
{
lean_object* v_a_2719_; lean_object* v___x_2721_; uint8_t v_isShared_2722_; uint8_t v_isSharedCheck_2726_; 
lean_dec(v_a_2636_);
lean_dec_ref(v_givenNames_2598_);
lean_dec(v_majorFVarId_2597_);
lean_dec_ref(v_a_2596_);
v_a_2719_ = lean_ctor_get(v___x_2651_, 0);
v_isSharedCheck_2726_ = !lean_is_exclusive(v___x_2651_);
if (v_isSharedCheck_2726_ == 0)
{
v___x_2721_ = v___x_2651_;
v_isShared_2722_ = v_isSharedCheck_2726_;
goto v_resetjp_2720_;
}
else
{
lean_inc(v_a_2719_);
lean_dec(v___x_2651_);
v___x_2721_ = lean_box(0);
v_isShared_2722_ = v_isSharedCheck_2726_;
goto v_resetjp_2720_;
}
v_resetjp_2720_:
{
lean_object* v___x_2724_; 
if (v_isShared_2722_ == 0)
{
v___x_2724_ = v___x_2721_;
goto v_reusejp_2723_;
}
else
{
lean_object* v_reuseFailAlloc_2725_; 
v_reuseFailAlloc_2725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2725_, 0, v_a_2719_);
v___x_2724_ = v_reuseFailAlloc_2725_;
goto v_reusejp_2723_;
}
v_reusejp_2723_:
{
return v___x_2724_;
}
}
}
}
}
else
{
lean_object* v_a_2751_; lean_object* v___x_2753_; uint8_t v_isShared_2754_; uint8_t v_isSharedCheck_2758_; 
lean_dec(v_a_2636_);
lean_dec(v_recursorName_2599_);
lean_dec_ref(v_givenNames_2598_);
lean_dec(v_majorFVarId_2597_);
lean_dec_ref(v_a_2596_);
lean_dec(v_mvarId_2595_);
v_a_2751_ = lean_ctor_get(v___x_2637_, 0);
v_isSharedCheck_2758_ = !lean_is_exclusive(v___x_2637_);
if (v_isSharedCheck_2758_ == 0)
{
v___x_2753_ = v___x_2637_;
v_isShared_2754_ = v_isSharedCheck_2758_;
goto v_resetjp_2752_;
}
else
{
lean_inc(v_a_2751_);
lean_dec(v___x_2637_);
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
}
else
{
lean_object* v_a_2759_; lean_object* v___x_2761_; uint8_t v_isShared_2762_; uint8_t v_isSharedCheck_2766_; 
lean_dec(v_recursorName_2599_);
lean_dec_ref(v_givenNames_2598_);
lean_dec(v_majorFVarId_2597_);
lean_dec_ref(v_a_2596_);
lean_dec(v_mvarId_2595_);
v_a_2759_ = lean_ctor_get(v___x_2635_, 0);
v_isSharedCheck_2766_ = !lean_is_exclusive(v___x_2635_);
if (v_isSharedCheck_2766_ == 0)
{
v___x_2761_ = v___x_2635_;
v_isShared_2762_ = v_isSharedCheck_2766_;
goto v_resetjp_2760_;
}
else
{
lean_inc(v_a_2759_);
lean_dec(v___x_2635_);
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
v___jp_2618_:
{
size_t v_sz_2631_; lean_object* v___x_2632_; lean_object* v___f_2633_; lean_object* v___x_2634_; 
v_sz_2631_ = lean_array_size(v___y_2624_);
v___x_2632_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__3(v_sz_2631_, v___y_2625_, v___y_2624_);
v___f_2633_ = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4___lam__0___boxed), 14, 9);
lean_closure_set(v___f_2633_, 0, v___y_2623_);
lean_closure_set(v___f_2633_, 1, v___x_2617_);
lean_closure_set(v___f_2633_, 2, v___y_2620_);
lean_closure_set(v___f_2633_, 3, v_a_2596_);
lean_closure_set(v___f_2633_, 4, v___x_2632_);
lean_closure_set(v___f_2633_, 5, v_givenNames_2598_);
lean_closure_set(v___f_2633_, 6, v___y_2622_);
lean_closure_set(v___f_2633_, 7, v___y_2619_);
lean_closure_set(v___f_2633_, 8, v___y_2621_);
v___x_2634_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___redArg(v___y_2626_, v___f_2633_, v___y_2627_, v___y_2628_, v___y_2629_, v___y_2630_);
return v___x_2634_;
}
}
else
{
lean_object* v_a_2767_; lean_object* v___x_2769_; uint8_t v_isShared_2770_; uint8_t v_isSharedCheck_2774_; 
lean_dec(v_recursorName_2599_);
lean_dec_ref(v_givenNames_2598_);
lean_dec(v_majorFVarId_2597_);
lean_dec_ref(v_a_2596_);
lean_dec(v_mvarId_2595_);
lean_dec_ref(v_val_2594_);
v_a_2767_ = lean_ctor_get(v___x_2616_, 0);
v_isSharedCheck_2774_ = !lean_is_exclusive(v___x_2616_);
if (v_isSharedCheck_2774_ == 0)
{
v___x_2769_ = v___x_2616_;
v_isShared_2770_ = v_isSharedCheck_2774_;
goto v_resetjp_2768_;
}
else
{
lean_inc(v_a_2767_);
lean_dec(v___x_2616_);
v___x_2769_ = lean_box(0);
v_isShared_2770_ = v_isSharedCheck_2774_;
goto v_resetjp_2768_;
}
v_resetjp_2768_:
{
lean_object* v___x_2772_; 
if (v_isShared_2770_ == 0)
{
v___x_2772_ = v___x_2769_;
goto v_reusejp_2771_;
}
else
{
lean_object* v_reuseFailAlloc_2773_; 
v_reuseFailAlloc_2773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2773_, 0, v_a_2767_);
v___x_2772_ = v_reuseFailAlloc_2773_;
goto v_reusejp_2771_;
}
v_reusejp_2771_:
{
return v___x_2772_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4___boxed(lean_object* v_val_2775_, lean_object* v_mvarId_2776_, lean_object* v_a_2777_, lean_object* v_majorFVarId_2778_, lean_object* v_givenNames_2779_, lean_object* v_recursorName_2780_, lean_object* v_x_2781_, lean_object* v_x_2782_, lean_object* v_x_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_, lean_object* v___y_2787_, lean_object* v___y_2788_){
_start:
{
lean_object* v_res_2789_; 
v_res_2789_ = l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4(v_val_2775_, v_mvarId_2776_, v_a_2777_, v_majorFVarId_2778_, v_givenNames_2779_, v_recursorName_2780_, v_x_2781_, v_x_2782_, v_x_2783_, v___y_2784_, v___y_2785_, v___y_2786_, v___y_2787_);
lean_dec(v___y_2787_);
lean_dec_ref(v___y_2786_);
lean_dec(v___y_2785_);
lean_dec_ref(v___y_2784_);
lean_dec(v_x_2783_);
return v_res_2789_;
}
}
static lean_object* _init_l_Lean_MVarId_induction___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2791_; lean_object* v___x_2792_; 
v___x_2791_ = ((lean_object*)(l_Lean_MVarId_induction___lam__0___closed__0));
v___x_2792_ = l_Lean_stringToMessageData(v___x_2791_);
return v___x_2792_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_induction___lam__0(lean_object* v___x_2793_, lean_object* v_mvarId_2794_, lean_object* v_majorFVarId_2795_, lean_object* v_recursorName_2796_, lean_object* v_givenNames_2797_, lean_object* v_cls_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_){
_start:
{
lean_object* v___y_2805_; lean_object* v___y_2806_; lean_object* v___y_2807_; lean_object* v___y_2808_; lean_object* v_options_2860_; uint8_t v_hasTrace_2861_; 
v_options_2860_ = lean_ctor_get(v___y_2801_, 2);
v_hasTrace_2861_ = lean_ctor_get_uint8(v_options_2860_, sizeof(void*)*1);
if (v_hasTrace_2861_ == 0)
{
lean_dec(v_cls_2798_);
v___y_2805_ = v___y_2799_;
v___y_2806_ = v___y_2800_;
v___y_2807_ = v___y_2801_;
v___y_2808_ = v___y_2802_;
goto v___jp_2804_;
}
else
{
lean_object* v_inheritedTraceOptions_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; uint8_t v___x_2865_; 
v_inheritedTraceOptions_2862_ = lean_ctor_get(v___y_2801_, 13);
v___x_2863_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__4));
lean_inc(v_cls_2798_);
v___x_2864_ = l_Lean_Name_append(v___x_2863_, v_cls_2798_);
v___x_2865_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2862_, v_options_2860_, v___x_2864_);
lean_dec(v___x_2864_);
if (v___x_2865_ == 0)
{
lean_dec(v_cls_2798_);
v___y_2805_ = v___y_2799_;
v___y_2806_ = v___y_2800_;
v___y_2807_ = v___y_2801_;
v___y_2808_ = v___y_2802_;
goto v___jp_2804_;
}
else
{
lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; 
v___x_2866_ = lean_obj_once(&l_Lean_MVarId_induction___lam__0___closed__1, &l_Lean_MVarId_induction___lam__0___closed__1_once, _init_l_Lean_MVarId_induction___lam__0___closed__1);
lean_inc(v_mvarId_2794_);
v___x_2867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2867_, 0, v_mvarId_2794_);
v___x_2868_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2868_, 0, v___x_2866_);
lean_ctor_set(v___x_2868_, 1, v___x_2867_);
v___x_2869_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1(v_cls_2798_, v___x_2868_, v___y_2799_, v___y_2800_, v___y_2801_, v___y_2802_);
if (lean_obj_tag(v___x_2869_) == 0)
{
lean_dec_ref(v___x_2869_);
v___y_2805_ = v___y_2799_;
v___y_2806_ = v___y_2800_;
v___y_2807_ = v___y_2801_;
v___y_2808_ = v___y_2802_;
goto v___jp_2804_;
}
else
{
lean_object* v_a_2870_; lean_object* v___x_2872_; uint8_t v_isShared_2873_; uint8_t v_isSharedCheck_2877_; 
lean_dec_ref(v_givenNames_2797_);
lean_dec(v_recursorName_2796_);
lean_dec(v_majorFVarId_2795_);
lean_dec(v_mvarId_2794_);
lean_dec_ref(v___x_2793_);
v_a_2870_ = lean_ctor_get(v___x_2869_, 0);
v_isSharedCheck_2877_ = !lean_is_exclusive(v___x_2869_);
if (v_isSharedCheck_2877_ == 0)
{
v___x_2872_ = v___x_2869_;
v_isShared_2873_ = v_isSharedCheck_2877_;
goto v_resetjp_2871_;
}
else
{
lean_inc(v_a_2870_);
lean_dec(v___x_2869_);
v___x_2872_ = lean_box(0);
v_isShared_2873_ = v_isSharedCheck_2877_;
goto v_resetjp_2871_;
}
v_resetjp_2871_:
{
lean_object* v___x_2875_; 
if (v_isShared_2873_ == 0)
{
v___x_2875_ = v___x_2872_;
goto v_reusejp_2874_;
}
else
{
lean_object* v_reuseFailAlloc_2876_; 
v_reuseFailAlloc_2876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2876_, 0, v_a_2870_);
v___x_2875_ = v_reuseFailAlloc_2876_;
goto v_reusejp_2874_;
}
v_reusejp_2874_:
{
return v___x_2875_;
}
}
}
}
}
v___jp_2804_:
{
lean_object* v___x_2809_; lean_object* v___x_2810_; 
v___x_2809_ = l_Lean_Name_mkStr1(v___x_2793_);
lean_inc(v___x_2809_);
lean_inc(v_mvarId_2794_);
v___x_2810_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_2794_, v___x_2809_, v___y_2805_, v___y_2806_, v___y_2807_, v___y_2808_);
if (lean_obj_tag(v___x_2810_) == 0)
{
lean_object* v___x_2811_; 
lean_dec_ref(v___x_2810_);
lean_inc(v_majorFVarId_2795_);
v___x_2811_ = l_Lean_FVarId_getDecl___redArg(v_majorFVarId_2795_, v___y_2805_, v___y_2807_, v___y_2808_);
if (lean_obj_tag(v___x_2811_) == 0)
{
lean_object* v_a_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; 
v_a_2812_ = lean_ctor_get(v___x_2811_, 0);
lean_inc(v_a_2812_);
lean_dec_ref(v___x_2811_);
v___x_2813_ = lean_box(0);
lean_inc(v_recursorName_2796_);
v___x_2814_ = l_Lean_Meta_mkRecursorInfo(v_recursorName_2796_, v___x_2813_, v___y_2805_, v___y_2806_, v___y_2807_, v___y_2808_);
if (lean_obj_tag(v___x_2814_) == 0)
{
lean_object* v_a_2815_; lean_object* v_typeName_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; 
v_a_2815_ = lean_ctor_get(v___x_2814_, 0);
lean_inc(v_a_2815_);
lean_dec_ref(v___x_2814_);
v_typeName_2816_ = lean_ctor_get(v_a_2815_, 1);
v___x_2817_ = l_Lean_LocalDecl_type(v_a_2812_);
lean_dec(v_a_2812_);
lean_inc_ref(v___x_2817_);
v___x_2818_ = l_Lean_Meta_whnfUntil(v___x_2817_, v_typeName_2816_, v___y_2805_, v___y_2806_, v___y_2807_, v___y_2808_);
if (lean_obj_tag(v___x_2818_) == 0)
{
lean_object* v_a_2819_; 
v_a_2819_ = lean_ctor_get(v___x_2818_, 0);
lean_inc(v_a_2819_);
lean_dec_ref(v___x_2818_);
if (lean_obj_tag(v_a_2819_) == 1)
{
lean_object* v_val_2820_; lean_object* v_dummy_2821_; lean_object* v_nargs_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; 
lean_dec_ref(v___x_2817_);
lean_dec(v___x_2809_);
v_val_2820_ = lean_ctor_get(v_a_2819_, 0);
lean_inc_n(v_val_2820_, 2);
lean_dec_ref(v_a_2819_);
v_dummy_2821_ = lean_obj_once(&l_Lean_Meta_getMajorTypeIndices___closed__0, &l_Lean_Meta_getMajorTypeIndices___closed__0_once, _init_l_Lean_Meta_getMajorTypeIndices___closed__0);
v_nargs_2822_ = l_Lean_Expr_getAppNumArgs(v_val_2820_);
lean_inc(v_nargs_2822_);
v___x_2823_ = lean_mk_array(v_nargs_2822_, v_dummy_2821_);
v___x_2824_ = lean_unsigned_to_nat(1u);
v___x_2825_ = lean_nat_sub(v_nargs_2822_, v___x_2824_);
lean_dec(v_nargs_2822_);
v___x_2826_ = l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4(v_val_2820_, v_mvarId_2794_, v_a_2815_, v_majorFVarId_2795_, v_givenNames_2797_, v_recursorName_2796_, v_val_2820_, v___x_2823_, v___x_2825_, v___y_2805_, v___y_2806_, v___y_2807_, v___y_2808_);
lean_dec(v___x_2825_);
return v___x_2826_;
}
else
{
lean_object* v___x_2827_; 
lean_dec(v_a_2819_);
lean_dec(v_a_2815_);
lean_dec_ref(v_givenNames_2797_);
lean_dec(v_recursorName_2796_);
lean_dec(v_majorFVarId_2795_);
v___x_2827_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg(v___x_2809_, v_mvarId_2794_, v___x_2817_, v___y_2805_, v___y_2806_, v___y_2807_, v___y_2808_);
return v___x_2827_;
}
}
else
{
lean_object* v_a_2828_; lean_object* v___x_2830_; uint8_t v_isShared_2831_; uint8_t v_isSharedCheck_2835_; 
lean_dec_ref(v___x_2817_);
lean_dec(v_a_2815_);
lean_dec(v___x_2809_);
lean_dec_ref(v_givenNames_2797_);
lean_dec(v_recursorName_2796_);
lean_dec(v_majorFVarId_2795_);
lean_dec(v_mvarId_2794_);
v_a_2828_ = lean_ctor_get(v___x_2818_, 0);
v_isSharedCheck_2835_ = !lean_is_exclusive(v___x_2818_);
if (v_isSharedCheck_2835_ == 0)
{
v___x_2830_ = v___x_2818_;
v_isShared_2831_ = v_isSharedCheck_2835_;
goto v_resetjp_2829_;
}
else
{
lean_inc(v_a_2828_);
lean_dec(v___x_2818_);
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
lean_dec(v_a_2812_);
lean_dec(v___x_2809_);
lean_dec_ref(v_givenNames_2797_);
lean_dec(v_recursorName_2796_);
lean_dec(v_majorFVarId_2795_);
lean_dec(v_mvarId_2794_);
v_a_2836_ = lean_ctor_get(v___x_2814_, 0);
v_isSharedCheck_2843_ = !lean_is_exclusive(v___x_2814_);
if (v_isSharedCheck_2843_ == 0)
{
v___x_2838_ = v___x_2814_;
v_isShared_2839_ = v_isSharedCheck_2843_;
goto v_resetjp_2837_;
}
else
{
lean_inc(v_a_2836_);
lean_dec(v___x_2814_);
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
lean_dec(v___x_2809_);
lean_dec_ref(v_givenNames_2797_);
lean_dec(v_recursorName_2796_);
lean_dec(v_majorFVarId_2795_);
lean_dec(v_mvarId_2794_);
v_a_2844_ = lean_ctor_get(v___x_2811_, 0);
v_isSharedCheck_2851_ = !lean_is_exclusive(v___x_2811_);
if (v_isSharedCheck_2851_ == 0)
{
v___x_2846_ = v___x_2811_;
v_isShared_2847_ = v_isSharedCheck_2851_;
goto v_resetjp_2845_;
}
else
{
lean_inc(v_a_2844_);
lean_dec(v___x_2811_);
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
else
{
lean_object* v_a_2852_; lean_object* v___x_2854_; uint8_t v_isShared_2855_; uint8_t v_isSharedCheck_2859_; 
lean_dec(v___x_2809_);
lean_dec_ref(v_givenNames_2797_);
lean_dec(v_recursorName_2796_);
lean_dec(v_majorFVarId_2795_);
lean_dec(v_mvarId_2794_);
v_a_2852_ = lean_ctor_get(v___x_2810_, 0);
v_isSharedCheck_2859_ = !lean_is_exclusive(v___x_2810_);
if (v_isSharedCheck_2859_ == 0)
{
v___x_2854_ = v___x_2810_;
v_isShared_2855_ = v_isSharedCheck_2859_;
goto v_resetjp_2853_;
}
else
{
lean_inc(v_a_2852_);
lean_dec(v___x_2810_);
v___x_2854_ = lean_box(0);
v_isShared_2855_ = v_isSharedCheck_2859_;
goto v_resetjp_2853_;
}
v_resetjp_2853_:
{
lean_object* v___x_2857_; 
if (v_isShared_2855_ == 0)
{
v___x_2857_ = v___x_2854_;
goto v_reusejp_2856_;
}
else
{
lean_object* v_reuseFailAlloc_2858_; 
v_reuseFailAlloc_2858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2858_, 0, v_a_2852_);
v___x_2857_ = v_reuseFailAlloc_2858_;
goto v_reusejp_2856_;
}
v_reusejp_2856_:
{
return v___x_2857_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_induction___lam__0___boxed(lean_object* v___x_2878_, lean_object* v_mvarId_2879_, lean_object* v_majorFVarId_2880_, lean_object* v_recursorName_2881_, lean_object* v_givenNames_2882_, lean_object* v_cls_2883_, lean_object* v___y_2884_, lean_object* v___y_2885_, lean_object* v___y_2886_, lean_object* v___y_2887_, lean_object* v___y_2888_){
_start:
{
lean_object* v_res_2889_; 
v_res_2889_ = l_Lean_MVarId_induction___lam__0(v___x_2878_, v_mvarId_2879_, v_majorFVarId_2880_, v_recursorName_2881_, v_givenNames_2882_, v_cls_2883_, v___y_2884_, v___y_2885_, v___y_2886_, v___y_2887_);
lean_dec(v___y_2887_);
lean_dec_ref(v___y_2886_);
lean_dec(v___y_2885_);
lean_dec_ref(v___y_2884_);
return v_res_2889_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_induction(lean_object* v_mvarId_2890_, lean_object* v_majorFVarId_2891_, lean_object* v_recursorName_2892_, lean_object* v_givenNames_2893_, lean_object* v_a_2894_, lean_object* v_a_2895_, lean_object* v_a_2896_, lean_object* v_a_2897_){
_start:
{
lean_object* v___x_2899_; lean_object* v_cls_2900_; lean_object* v___f_2901_; lean_object* v___x_2902_; 
v___x_2899_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__0));
v_cls_2900_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__2));
lean_inc(v_mvarId_2890_);
v___f_2901_ = lean_alloc_closure((void*)(l_Lean_MVarId_induction___lam__0___boxed), 11, 6);
lean_closure_set(v___f_2901_, 0, v___x_2899_);
lean_closure_set(v___f_2901_, 1, v_mvarId_2890_);
lean_closure_set(v___f_2901_, 2, v_majorFVarId_2891_);
lean_closure_set(v___f_2901_, 3, v_recursorName_2892_);
lean_closure_set(v___f_2901_, 4, v_givenNames_2893_);
lean_closure_set(v___f_2901_, 5, v_cls_2900_);
v___x_2902_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___redArg(v_mvarId_2890_, v___f_2901_, v_a_2894_, v_a_2895_, v_a_2896_, v_a_2897_);
return v___x_2902_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_induction___boxed(lean_object* v_mvarId_2903_, lean_object* v_majorFVarId_2904_, lean_object* v_recursorName_2905_, lean_object* v_givenNames_2906_, lean_object* v_a_2907_, lean_object* v_a_2908_, lean_object* v_a_2909_, lean_object* v_a_2910_, lean_object* v_a_2911_){
_start:
{
lean_object* v_res_2912_; 
v_res_2912_ = l_Lean_MVarId_induction(v_mvarId_2903_, v_majorFVarId_2904_, v_recursorName_2905_, v_givenNames_2906_, v_a_2907_, v_a_2908_, v_a_2909_, v_a_2910_);
lean_dec(v_a_2910_);
lean_dec_ref(v_a_2909_);
lean_dec(v_a_2908_);
lean_dec_ref(v_a_2907_);
return v_res_2912_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; 
v___x_2960_ = lean_unsigned_to_nat(2221195325u);
v___x_2961_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_));
v___x_2962_ = l_Lean_Name_num___override(v___x_2961_, v___x_2960_);
return v___x_2962_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; 
v___x_2964_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_));
v___x_2965_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_);
v___x_2966_ = l_Lean_Name_str___override(v___x_2965_, v___x_2964_);
return v___x_2966_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; 
v___x_2968_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_));
v___x_2969_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_);
v___x_2970_ = l_Lean_Name_str___override(v___x_2969_, v___x_2968_);
return v___x_2970_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; 
v___x_2971_ = lean_unsigned_to_nat(2u);
v___x_2972_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_);
v___x_2973_ = l_Lean_Name_num___override(v___x_2972_, v___x_2971_);
return v___x_2973_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2975_; uint8_t v___x_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; 
v___x_2975_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__2));
v___x_2976_ = 0;
v___x_2977_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_);
v___x_2978_ = l_Lean_registerTraceClass(v___x_2975_, v___x_2976_, v___x_2977_);
return v___x_2978_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2____boxed(lean_object* v_a_2979_){
_start:
{
lean_object* v_res_2980_; 
v_res_2980_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_();
return v_res_2980_;
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
