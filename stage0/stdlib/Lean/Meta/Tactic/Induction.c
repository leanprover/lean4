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
lean_object* v___f_134_; lean_object* v___x_8870__overap_135_; lean_object* v___x_136_; 
v___f_134_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__4___closed__0));
v___x_8870__overap_135_ = lean_panic_fn_borrowed(v___f_134_, v_msg_128_);
lean_inc(v___y_132_);
lean_inc_ref(v___y_131_);
lean_inc(v___y_130_);
lean_inc_ref(v___y_129_);
v___x_136_ = lean_apply_5(v___x_8870__overap_135_, v___y_129_, v___y_130_, v___y_131_, v___y_132_, lean_box(0));
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
size_t v_x_10127__boxed_363_; size_t v_x_10128__boxed_364_; lean_object* v_res_365_; 
v_x_10127__boxed_363_ = lean_unbox_usize(v_x_359_);
lean_dec(v_x_359_);
v_x_10128__boxed_364_ = lean_unbox_usize(v_x_360_);
lean_dec(v_x_360_);
v_res_365_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2___redArg(v_x_358_, v_x_10127__boxed_363_, v_x_10128__boxed_364_, v_x_361_, v_x_362_);
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
lean_object* v___x_377_; lean_object* v_mctx_378_; lean_object* v_cache_379_; lean_object* v_zetaDeltaFVarIds_380_; lean_object* v_postponed_381_; lean_object* v_diag_382_; lean_object* v___x_384_; uint8_t v_isShared_385_; uint8_t v_isSharedCheck_411_; 
v___x_377_ = lean_st_ref_take(v___y_375_);
v_mctx_378_ = lean_ctor_get(v___x_377_, 0);
v_cache_379_ = lean_ctor_get(v___x_377_, 1);
v_zetaDeltaFVarIds_380_ = lean_ctor_get(v___x_377_, 2);
v_postponed_381_ = lean_ctor_get(v___x_377_, 3);
v_diag_382_ = lean_ctor_get(v___x_377_, 4);
v_isSharedCheck_411_ = !lean_is_exclusive(v___x_377_);
if (v_isSharedCheck_411_ == 0)
{
v___x_384_ = v___x_377_;
v_isShared_385_ = v_isSharedCheck_411_;
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
v_isShared_385_ = v_isSharedCheck_411_;
goto v_resetjp_383_;
}
v_resetjp_383_:
{
lean_object* v_depth_386_; lean_object* v_levelAssignDepth_387_; lean_object* v_lmvarCounter_388_; lean_object* v_mvarCounter_389_; lean_object* v_lDecls_390_; lean_object* v_decls_391_; lean_object* v_userNames_392_; lean_object* v_lAssignment_393_; lean_object* v_eAssignment_394_; lean_object* v_dAssignment_395_; lean_object* v_instanceTypedMVars_396_; lean_object* v___x_398_; uint8_t v_isShared_399_; uint8_t v_isSharedCheck_410_; 
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
v_instanceTypedMVars_396_ = lean_ctor_get(v_mctx_378_, 10);
v_isSharedCheck_410_ = !lean_is_exclusive(v_mctx_378_);
if (v_isSharedCheck_410_ == 0)
{
v___x_398_ = v_mctx_378_;
v_isShared_399_ = v_isSharedCheck_410_;
goto v_resetjp_397_;
}
else
{
lean_inc(v_instanceTypedMVars_396_);
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
v___x_398_ = lean_box(0);
v_isShared_399_ = v_isSharedCheck_410_;
goto v_resetjp_397_;
}
v_resetjp_397_:
{
lean_object* v___x_400_; lean_object* v___x_402_; 
v___x_400_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0___redArg(v_eAssignment_394_, v_mvarId_373_, v_val_374_);
if (v_isShared_399_ == 0)
{
lean_ctor_set(v___x_398_, 8, v___x_400_);
v___x_402_ = v___x_398_;
goto v_reusejp_401_;
}
else
{
lean_object* v_reuseFailAlloc_409_; 
v_reuseFailAlloc_409_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_409_, 0, v_depth_386_);
lean_ctor_set(v_reuseFailAlloc_409_, 1, v_levelAssignDepth_387_);
lean_ctor_set(v_reuseFailAlloc_409_, 2, v_lmvarCounter_388_);
lean_ctor_set(v_reuseFailAlloc_409_, 3, v_mvarCounter_389_);
lean_ctor_set(v_reuseFailAlloc_409_, 4, v_lDecls_390_);
lean_ctor_set(v_reuseFailAlloc_409_, 5, v_decls_391_);
lean_ctor_set(v_reuseFailAlloc_409_, 6, v_userNames_392_);
lean_ctor_set(v_reuseFailAlloc_409_, 7, v_lAssignment_393_);
lean_ctor_set(v_reuseFailAlloc_409_, 8, v___x_400_);
lean_ctor_set(v_reuseFailAlloc_409_, 9, v_dAssignment_395_);
lean_ctor_set(v_reuseFailAlloc_409_, 10, v_instanceTypedMVars_396_);
v___x_402_ = v_reuseFailAlloc_409_;
goto v_reusejp_401_;
}
v_reusejp_401_:
{
lean_object* v___x_404_; 
if (v_isShared_385_ == 0)
{
lean_ctor_set(v___x_384_, 0, v___x_402_);
v___x_404_ = v___x_384_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_408_; 
v_reuseFailAlloc_408_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_408_, 0, v___x_402_);
lean_ctor_set(v_reuseFailAlloc_408_, 1, v_cache_379_);
lean_ctor_set(v_reuseFailAlloc_408_, 2, v_zetaDeltaFVarIds_380_);
lean_ctor_set(v_reuseFailAlloc_408_, 3, v_postponed_381_);
lean_ctor_set(v_reuseFailAlloc_408_, 4, v_diag_382_);
v___x_404_ = v_reuseFailAlloc_408_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; 
v___x_405_ = lean_st_ref_put(v___y_375_, v___x_404_);
v___x_406_ = lean_box(0);
v___x_407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_407_, 0, v___x_406_);
return v___x_407_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0___redArg___boxed(lean_object* v_mvarId_412_, lean_object* v_val_413_, lean_object* v___y_414_, lean_object* v___y_415_){
_start:
{
lean_object* v_res_416_; 
v_res_416_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0___redArg(v_mvarId_412_, v_val_413_, v___y_414_);
lean_dec(v___y_414_);
return v_res_416_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1_spec__2(lean_object* v_msgData_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_){
_start:
{
lean_object* v___x_423_; lean_object* v_env_424_; lean_object* v___x_425_; lean_object* v_mctx_426_; lean_object* v_lctx_427_; lean_object* v_options_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; 
v___x_423_ = lean_st_ref_get(v___y_421_);
v_env_424_ = lean_ctor_get(v___x_423_, 0);
lean_inc_ref(v_env_424_);
lean_dec(v___x_423_);
v___x_425_ = lean_st_ref_get(v___y_419_);
v_mctx_426_ = lean_ctor_get(v___x_425_, 0);
lean_inc_ref(v_mctx_426_);
lean_dec(v___x_425_);
v_lctx_427_ = lean_ctor_get(v___y_418_, 2);
v_options_428_ = lean_ctor_get(v___y_420_, 2);
lean_inc_ref(v_options_428_);
lean_inc_ref(v_lctx_427_);
v___x_429_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_429_, 0, v_env_424_);
lean_ctor_set(v___x_429_, 1, v_mctx_426_);
lean_ctor_set(v___x_429_, 2, v_lctx_427_);
lean_ctor_set(v___x_429_, 3, v_options_428_);
v___x_430_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_430_, 0, v___x_429_);
lean_ctor_set(v___x_430_, 1, v_msgData_417_);
v___x_431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_431_, 0, v___x_430_);
return v___x_431_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1_spec__2___boxed(lean_object* v_msgData_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_){
_start:
{
lean_object* v_res_438_; 
v_res_438_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1_spec__2(v_msgData_432_, v___y_433_, v___y_434_, v___y_435_, v___y_436_);
lean_dec(v___y_436_);
lean_dec_ref(v___y_435_);
lean_dec(v___y_434_);
lean_dec_ref(v___y_433_);
return v_res_438_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1___closed__0(void){
_start:
{
lean_object* v___x_439_; double v___x_440_; 
v___x_439_ = lean_unsigned_to_nat(0u);
v___x_440_ = lean_float_of_nat(v___x_439_);
return v___x_440_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1(lean_object* v_cls_444_, lean_object* v_msg_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_){
_start:
{
lean_object* v_ref_451_; lean_object* v___x_452_; lean_object* v_a_453_; lean_object* v___x_455_; uint8_t v_isShared_456_; uint8_t v_isSharedCheck_497_; 
v_ref_451_ = lean_ctor_get(v___y_448_, 5);
v___x_452_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1_spec__2(v_msg_445_, v___y_446_, v___y_447_, v___y_448_, v___y_449_);
v_a_453_ = lean_ctor_get(v___x_452_, 0);
v_isSharedCheck_497_ = !lean_is_exclusive(v___x_452_);
if (v_isSharedCheck_497_ == 0)
{
v___x_455_ = v___x_452_;
v_isShared_456_ = v_isSharedCheck_497_;
goto v_resetjp_454_;
}
else
{
lean_inc(v_a_453_);
lean_dec(v___x_452_);
v___x_455_ = lean_box(0);
v_isShared_456_ = v_isSharedCheck_497_;
goto v_resetjp_454_;
}
v_resetjp_454_:
{
lean_object* v___x_457_; lean_object* v_traceState_458_; lean_object* v_env_459_; lean_object* v_nextMacroScope_460_; lean_object* v_ngen_461_; lean_object* v_auxDeclNGen_462_; lean_object* v_cache_463_; lean_object* v_messages_464_; lean_object* v_infoState_465_; lean_object* v_snapshotTasks_466_; lean_object* v___x_468_; uint8_t v_isShared_469_; uint8_t v_isSharedCheck_496_; 
v___x_457_ = lean_st_ref_take(v___y_449_);
v_traceState_458_ = lean_ctor_get(v___x_457_, 4);
v_env_459_ = lean_ctor_get(v___x_457_, 0);
v_nextMacroScope_460_ = lean_ctor_get(v___x_457_, 1);
v_ngen_461_ = lean_ctor_get(v___x_457_, 2);
v_auxDeclNGen_462_ = lean_ctor_get(v___x_457_, 3);
v_cache_463_ = lean_ctor_get(v___x_457_, 5);
v_messages_464_ = lean_ctor_get(v___x_457_, 6);
v_infoState_465_ = lean_ctor_get(v___x_457_, 7);
v_snapshotTasks_466_ = lean_ctor_get(v___x_457_, 8);
v_isSharedCheck_496_ = !lean_is_exclusive(v___x_457_);
if (v_isSharedCheck_496_ == 0)
{
v___x_468_ = v___x_457_;
v_isShared_469_ = v_isSharedCheck_496_;
goto v_resetjp_467_;
}
else
{
lean_inc(v_snapshotTasks_466_);
lean_inc(v_infoState_465_);
lean_inc(v_messages_464_);
lean_inc(v_cache_463_);
lean_inc(v_traceState_458_);
lean_inc(v_auxDeclNGen_462_);
lean_inc(v_ngen_461_);
lean_inc(v_nextMacroScope_460_);
lean_inc(v_env_459_);
lean_dec(v___x_457_);
v___x_468_ = lean_box(0);
v_isShared_469_ = v_isSharedCheck_496_;
goto v_resetjp_467_;
}
v_resetjp_467_:
{
uint64_t v_tid_470_; lean_object* v_traces_471_; lean_object* v___x_473_; uint8_t v_isShared_474_; uint8_t v_isSharedCheck_495_; 
v_tid_470_ = lean_ctor_get_uint64(v_traceState_458_, sizeof(void*)*1);
v_traces_471_ = lean_ctor_get(v_traceState_458_, 0);
v_isSharedCheck_495_ = !lean_is_exclusive(v_traceState_458_);
if (v_isSharedCheck_495_ == 0)
{
v___x_473_ = v_traceState_458_;
v_isShared_474_ = v_isSharedCheck_495_;
goto v_resetjp_472_;
}
else
{
lean_inc(v_traces_471_);
lean_dec(v_traceState_458_);
v___x_473_ = lean_box(0);
v_isShared_474_ = v_isSharedCheck_495_;
goto v_resetjp_472_;
}
v_resetjp_472_:
{
lean_object* v___x_475_; double v___x_476_; uint8_t v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_485_; 
v___x_475_ = lean_box(0);
v___x_476_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1___closed__0);
v___x_477_ = 0;
v___x_478_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1___closed__1));
v___x_479_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_479_, 0, v_cls_444_);
lean_ctor_set(v___x_479_, 1, v___x_475_);
lean_ctor_set(v___x_479_, 2, v___x_478_);
lean_ctor_set_float(v___x_479_, sizeof(void*)*3, v___x_476_);
lean_ctor_set_float(v___x_479_, sizeof(void*)*3 + 8, v___x_476_);
lean_ctor_set_uint8(v___x_479_, sizeof(void*)*3 + 16, v___x_477_);
v___x_480_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1___closed__2));
v___x_481_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_481_, 0, v___x_479_);
lean_ctor_set(v___x_481_, 1, v_a_453_);
lean_ctor_set(v___x_481_, 2, v___x_480_);
lean_inc(v_ref_451_);
v___x_482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_482_, 0, v_ref_451_);
lean_ctor_set(v___x_482_, 1, v___x_481_);
v___x_483_ = l_Lean_PersistentArray_push___redArg(v_traces_471_, v___x_482_);
if (v_isShared_474_ == 0)
{
lean_ctor_set(v___x_473_, 0, v___x_483_);
v___x_485_ = v___x_473_;
goto v_reusejp_484_;
}
else
{
lean_object* v_reuseFailAlloc_494_; 
v_reuseFailAlloc_494_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_494_, 0, v___x_483_);
lean_ctor_set_uint64(v_reuseFailAlloc_494_, sizeof(void*)*1, v_tid_470_);
v___x_485_ = v_reuseFailAlloc_494_;
goto v_reusejp_484_;
}
v_reusejp_484_:
{
lean_object* v___x_487_; 
if (v_isShared_469_ == 0)
{
lean_ctor_set(v___x_468_, 4, v___x_485_);
v___x_487_ = v___x_468_;
goto v_reusejp_486_;
}
else
{
lean_object* v_reuseFailAlloc_493_; 
v_reuseFailAlloc_493_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_493_, 0, v_env_459_);
lean_ctor_set(v_reuseFailAlloc_493_, 1, v_nextMacroScope_460_);
lean_ctor_set(v_reuseFailAlloc_493_, 2, v_ngen_461_);
lean_ctor_set(v_reuseFailAlloc_493_, 3, v_auxDeclNGen_462_);
lean_ctor_set(v_reuseFailAlloc_493_, 4, v___x_485_);
lean_ctor_set(v_reuseFailAlloc_493_, 5, v_cache_463_);
lean_ctor_set(v_reuseFailAlloc_493_, 6, v_messages_464_);
lean_ctor_set(v_reuseFailAlloc_493_, 7, v_infoState_465_);
lean_ctor_set(v_reuseFailAlloc_493_, 8, v_snapshotTasks_466_);
v___x_487_ = v_reuseFailAlloc_493_;
goto v_reusejp_486_;
}
v_reusejp_486_:
{
lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_491_; 
v___x_488_ = lean_st_ref_put(v___y_449_, v___x_487_);
v___x_489_ = lean_box(0);
if (v_isShared_456_ == 0)
{
lean_ctor_set(v___x_455_, 0, v___x_489_);
v___x_491_ = v___x_455_;
goto v_reusejp_490_;
}
else
{
lean_object* v_reuseFailAlloc_492_; 
v_reuseFailAlloc_492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_492_, 0, v___x_489_);
v___x_491_ = v_reuseFailAlloc_492_;
goto v_reusejp_490_;
}
v_reusejp_490_:
{
return v___x_491_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1___boxed(lean_object* v_cls_498_, lean_object* v_msg_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_){
_start:
{
lean_object* v_res_505_; 
v_res_505_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1(v_cls_498_, v_msg_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_);
lean_dec(v___y_503_);
lean_dec_ref(v___y_502_);
lean_dec(v___y_501_);
lean_dec_ref(v___y_500_);
return v_res_505_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__3(size_t v_sz_506_, size_t v_i_507_, lean_object* v_bs_508_){
_start:
{
uint8_t v___x_509_; 
v___x_509_ = lean_usize_dec_lt(v_i_507_, v_sz_506_);
if (v___x_509_ == 0)
{
return v_bs_508_;
}
else
{
lean_object* v_v_510_; lean_object* v___x_511_; lean_object* v_bs_x27_512_; lean_object* v___x_513_; size_t v___x_514_; size_t v___x_515_; lean_object* v___x_516_; 
v_v_510_ = lean_array_uget(v_bs_508_, v_i_507_);
v___x_511_ = lean_unsigned_to_nat(0u);
v_bs_x27_512_ = lean_array_uset(v_bs_508_, v_i_507_, v___x_511_);
v___x_513_ = l_Lean_mkFVar(v_v_510_);
v___x_514_ = ((size_t)1ULL);
v___x_515_ = lean_usize_add(v_i_507_, v___x_514_);
v___x_516_ = lean_array_uset(v_bs_x27_512_, v_i_507_, v___x_513_);
v_i_507_ = v___x_515_;
v_bs_508_ = v___x_516_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__3___boxed(lean_object* v_sz_518_, lean_object* v_i_519_, lean_object* v_bs_520_){
_start:
{
size_t v_sz_boxed_521_; size_t v_i_boxed_522_; lean_object* v_res_523_; 
v_sz_boxed_521_ = lean_unbox_usize(v_sz_518_);
lean_dec(v_sz_518_);
v_i_boxed_522_ = lean_unbox_usize(v_i_519_);
lean_dec(v_i_519_);
v_res_523_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__3(v_sz_boxed_521_, v_i_boxed_522_, v_bs_520_);
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
lean_object* v___y_575_; lean_object* v___y_576_; lean_object* v___y_577_; lean_object* v___y_578_; lean_object* v___y_631_; lean_object* v___y_632_; lean_object* v___y_633_; lean_object* v___y_634_; lean_object* v___y_635_; lean_object* v___y_636_; lean_object* v___y_637_; uint8_t v___y_638_; uint8_t v___y_639_; lean_object* v___y_640_; lean_object* v___y_641_; lean_object* v___y_642_; lean_object* v___y_643_; lean_object* v___y_644_; lean_object* v___y_645_; uint8_t v___y_646_; lean_object* v___y_682_; uint8_t v___y_683_; lean_object* v___y_684_; lean_object* v___y_685_; uint8_t v___y_686_; lean_object* v___y_687_; lean_object* v___y_688_; lean_object* v___y_689_; lean_object* v___y_690_; lean_object* v___y_691_; lean_object* v___y_692_; lean_object* v___y_693_; lean_object* v___y_694_; lean_object* v___y_695_; lean_object* v___y_696_; uint8_t v___y_714_; lean_object* v___y_715_; lean_object* v_fst_716_; lean_object* v_snd_717_; lean_object* v___y_734_; uint8_t v___y_735_; lean_object* v___y_736_; lean_object* v___x_748_; 
v___x_748_ = l_Lean_Meta_whnfForall(v_recursorType_566_, v_a_569_, v_a_570_, v_a_571_, v_a_572_);
if (lean_obj_tag(v___x_748_) == 0)
{
lean_object* v_a_749_; lean_object* v___y_751_; lean_object* v___y_752_; lean_object* v___y_753_; lean_object* v___y_754_; lean_object* v___y_755_; lean_object* v___y_756_; uint8_t v___y_757_; lean_object* v___y_758_; lean_object* v___y_759_; uint8_t v___y_760_; lean_object* v___y_761_; lean_object* v___y_762_; lean_object* v___y_763_; lean_object* v___y_764_; lean_object* v___y_806_; uint8_t v___y_807_; uint8_t v___y_808_; lean_object* v___y_809_; lean_object* v___y_810_; lean_object* v___y_811_; lean_object* v___y_812_; lean_object* v___y_813_; lean_object* v___y_814_; lean_object* v___y_815_; lean_object* v___y_827_; lean_object* v___y_828_; uint8_t v___y_829_; lean_object* v___y_830_; lean_object* v___y_831_; lean_object* v___y_832_; lean_object* v___y_833_; lean_object* v___y_834_; uint8_t v___y_835_; lean_object* v___y_905_; lean_object* v___y_906_; uint8_t v___y_907_; lean_object* v___y_908_; lean_object* v___y_909_; uint8_t v___y_910_; lean_object* v___y_911_; lean_object* v___y_912_; lean_object* v___y_913_; uint8_t v___y_919_; lean_object* v___y_920_; lean_object* v___y_921_; lean_object* v___y_922_; lean_object* v___y_923_; lean_object* v___y_924_; uint8_t v___y_936_; uint8_t v___x_983_; 
v_a_749_ = lean_ctor_get(v___x_748_, 0);
lean_inc(v_a_749_);
lean_dec_ref_known(v___x_748_, 1);
v___x_983_ = l_Lean_Expr_isForall(v_a_749_);
if (v___x_983_ == 0)
{
v___y_936_ = v___x_983_;
goto v___jp_935_;
}
else
{
lean_object* v_numArgs_984_; uint8_t v___x_985_; 
v_numArgs_984_ = lean_ctor_get(v_recursorInfo_556_, 3);
v___x_985_ = lean_nat_dec_lt(v_pos_563_, v_numArgs_984_);
v___y_936_ = v___x_985_;
goto v___jp_935_;
}
v___jp_750_:
{
lean_object* v___x_765_; 
v___x_765_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___y_751_, v___y_753_, v___y_763_, v___y_755_, v___y_754_, v___y_758_);
if (lean_obj_tag(v___x_765_) == 0)
{
lean_object* v_a_766_; lean_object* v___x_767_; 
v_a_766_ = lean_ctor_get(v___x_765_, 0);
lean_inc(v_a_766_);
lean_dec_ref_known(v___x_765_, 1);
lean_inc(v_mvarId_554_);
v___x_767_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTypeBody(v_mvarId_554_, v_a_749_, v_a_766_, v___y_763_, v___y_755_, v___y_754_, v___y_758_);
if (lean_obj_tag(v___x_767_) == 0)
{
lean_object* v_options_768_; lean_object* v_a_769_; lean_object* v_inheritedTraceOptions_770_; uint8_t v_hasTrace_771_; lean_object* v___x_772_; 
v_options_768_ = lean_ctor_get(v___y_754_, 2);
v_a_769_ = lean_ctor_get(v___x_767_, 0);
lean_inc(v_a_769_);
lean_dec_ref_known(v___x_767_, 1);
v_inheritedTraceOptions_770_ = lean_ctor_get(v___y_754_, 13);
v_hasTrace_771_ = lean_ctor_get_uint8(v_options_768_, sizeof(void*)*1);
lean_inc(v_a_766_);
v___x_772_ = l_Lean_Expr_app___override(v_recursor_565_, v_a_766_);
if (v_hasTrace_771_ == 0)
{
v___y_682_ = v___x_772_;
v___y_683_ = v___y_757_;
v___y_684_ = v___y_752_;
v___y_685_ = v___y_759_;
v___y_686_ = v___y_760_;
v___y_687_ = v_a_766_;
v___y_688_ = v___y_764_;
v___y_689_ = v___y_761_;
v___y_690_ = v___y_762_;
v___y_691_ = v_a_769_;
v___y_692_ = v___y_756_;
v___y_693_ = v___y_763_;
v___y_694_ = v___y_755_;
v___y_695_ = v___y_754_;
v___y_696_ = v___y_758_;
goto v___jp_681_;
}
else
{
lean_object* v___x_773_; lean_object* v___x_774_; uint8_t v___x_775_; 
v___x_773_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__2));
v___x_774_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5);
v___x_775_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_770_, v_options_768_, v___x_774_);
if (v___x_775_ == 0)
{
v___y_682_ = v___x_772_;
v___y_683_ = v___y_757_;
v___y_684_ = v___y_752_;
v___y_685_ = v___y_759_;
v___y_686_ = v___y_760_;
v___y_687_ = v_a_766_;
v___y_688_ = v___y_764_;
v___y_689_ = v___y_761_;
v___y_690_ = v___y_762_;
v___y_691_ = v_a_769_;
v___y_692_ = v___y_756_;
v___y_693_ = v___y_763_;
v___y_694_ = v___y_755_;
v___y_695_ = v___y_754_;
v___y_696_ = v___y_758_;
goto v___jp_681_;
}
else
{
lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; 
v___x_776_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__11, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__11_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__11);
v___x_777_ = l_Lean_Expr_fvarId_x21(v_major_558_);
v___x_778_ = l_Lean_MessageData_ofName(v___x_777_);
v___x_779_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_779_, 0, v___x_776_);
lean_ctor_set(v___x_779_, 1, v___x_778_);
v___x_780_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1(v___x_773_, v___x_779_, v___y_763_, v___y_755_, v___y_754_, v___y_758_);
if (lean_obj_tag(v___x_780_) == 0)
{
lean_dec_ref_known(v___x_780_, 1);
v___y_682_ = v___x_772_;
v___y_683_ = v___y_757_;
v___y_684_ = v___y_752_;
v___y_685_ = v___y_759_;
v___y_686_ = v___y_760_;
v___y_687_ = v_a_766_;
v___y_688_ = v___y_764_;
v___y_689_ = v___y_761_;
v___y_690_ = v___y_762_;
v___y_691_ = v_a_769_;
v___y_692_ = v___y_756_;
v___y_693_ = v___y_763_;
v___y_694_ = v___y_755_;
v___y_695_ = v___y_754_;
v___y_696_ = v___y_758_;
goto v___jp_681_;
}
else
{
lean_object* v_a_781_; lean_object* v___x_783_; uint8_t v_isShared_784_; uint8_t v_isSharedCheck_788_; 
lean_dec_ref(v___x_772_);
lean_dec(v_a_769_);
lean_dec(v_a_766_);
lean_dec_ref(v___y_764_);
lean_dec(v___y_762_);
lean_dec(v___y_761_);
lean_dec(v___y_759_);
lean_dec(v___y_752_);
lean_dec_ref(v_subgoals_568_);
lean_dec(v_minorIdx_564_);
lean_dec(v_pos_563_);
lean_dec(v_baseSubst_560_);
lean_dec_ref(v_major_558_);
lean_dec(v_mvarId_554_);
v_a_781_ = lean_ctor_get(v___x_780_, 0);
v_isSharedCheck_788_ = !lean_is_exclusive(v___x_780_);
if (v_isSharedCheck_788_ == 0)
{
v___x_783_ = v___x_780_;
v_isShared_784_ = v_isSharedCheck_788_;
goto v_resetjp_782_;
}
else
{
lean_inc(v_a_781_);
lean_dec(v___x_780_);
v___x_783_ = lean_box(0);
v_isShared_784_ = v_isSharedCheck_788_;
goto v_resetjp_782_;
}
v_resetjp_782_:
{
lean_object* v___x_786_; 
if (v_isShared_784_ == 0)
{
v___x_786_ = v___x_783_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_787_; 
v_reuseFailAlloc_787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_787_, 0, v_a_781_);
v___x_786_ = v_reuseFailAlloc_787_;
goto v_reusejp_785_;
}
v_reusejp_785_:
{
return v___x_786_;
}
}
}
}
}
}
else
{
lean_object* v_a_789_; lean_object* v___x_791_; uint8_t v_isShared_792_; uint8_t v_isSharedCheck_796_; 
lean_dec(v_a_766_);
lean_dec_ref(v___y_764_);
lean_dec(v___y_762_);
lean_dec(v___y_761_);
lean_dec(v___y_759_);
lean_dec(v___y_752_);
lean_dec_ref(v_subgoals_568_);
lean_dec_ref(v_recursor_565_);
lean_dec(v_minorIdx_564_);
lean_dec(v_pos_563_);
lean_dec(v_baseSubst_560_);
lean_dec_ref(v_major_558_);
lean_dec(v_mvarId_554_);
v_a_789_ = lean_ctor_get(v___x_767_, 0);
v_isSharedCheck_796_ = !lean_is_exclusive(v___x_767_);
if (v_isSharedCheck_796_ == 0)
{
v___x_791_ = v___x_767_;
v_isShared_792_ = v_isSharedCheck_796_;
goto v_resetjp_790_;
}
else
{
lean_inc(v_a_789_);
lean_dec(v___x_767_);
v___x_791_ = lean_box(0);
v_isShared_792_ = v_isSharedCheck_796_;
goto v_resetjp_790_;
}
v_resetjp_790_:
{
lean_object* v___x_794_; 
if (v_isShared_792_ == 0)
{
v___x_794_ = v___x_791_;
goto v_reusejp_793_;
}
else
{
lean_object* v_reuseFailAlloc_795_; 
v_reuseFailAlloc_795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_795_, 0, v_a_789_);
v___x_794_ = v_reuseFailAlloc_795_;
goto v_reusejp_793_;
}
v_reusejp_793_:
{
return v___x_794_;
}
}
}
}
else
{
lean_object* v_a_797_; lean_object* v___x_799_; uint8_t v_isShared_800_; uint8_t v_isSharedCheck_804_; 
lean_dec_ref(v___y_764_);
lean_dec(v___y_762_);
lean_dec(v___y_761_);
lean_dec(v___y_759_);
lean_dec(v___y_752_);
lean_dec(v_a_749_);
lean_dec_ref(v_subgoals_568_);
lean_dec_ref(v_recursor_565_);
lean_dec(v_minorIdx_564_);
lean_dec(v_pos_563_);
lean_dec(v_baseSubst_560_);
lean_dec_ref(v_major_558_);
lean_dec(v_mvarId_554_);
v_a_797_ = lean_ctor_get(v___x_765_, 0);
v_isSharedCheck_804_ = !lean_is_exclusive(v___x_765_);
if (v_isSharedCheck_804_ == 0)
{
v___x_799_ = v___x_765_;
v_isShared_800_ = v_isSharedCheck_804_;
goto v_resetjp_798_;
}
else
{
lean_inc(v_a_797_);
lean_dec(v___x_765_);
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
v___jp_805_:
{
lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; uint8_t v___x_822_; 
v___x_816_ = lean_nat_sub(v___y_810_, v_initialArity_561_);
lean_dec(v___y_810_);
v___x_817_ = lean_array_get_size(v_reverted_557_);
v___x_818_ = lean_array_get_size(v_indices_559_);
v___x_819_ = lean_nat_sub(v___x_817_, v___x_818_);
v___x_820_ = lean_nat_sub(v___x_819_, v___y_811_);
lean_dec(v___x_819_);
v___x_821_ = lean_array_get_size(v_givenNames_555_);
v___x_822_ = lean_nat_dec_lt(v_minorIdx_564_, v___x_821_);
if (v___x_822_ == 0)
{
lean_object* v___x_823_; lean_object* v___x_824_; 
v___x_823_ = lean_box(0);
v___x_824_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_824_, 0, v___x_823_);
lean_ctor_set_uint8(v___x_824_, sizeof(void*)*1, v___y_808_);
v___y_751_ = v___y_806_;
v___y_752_ = v___x_820_;
v___y_753_ = v___y_809_;
v___y_754_ = v___y_814_;
v___y_755_ = v___y_813_;
v___y_756_ = v___y_811_;
v___y_757_ = v___y_807_;
v___y_758_ = v___y_815_;
v___y_759_ = v___x_817_;
v___y_760_ = v___y_808_;
v___y_761_ = v___x_816_;
v___y_762_ = v___x_818_;
v___y_763_ = v___y_812_;
v___y_764_ = v___x_824_;
goto v___jp_750_;
}
else
{
lean_object* v___x_825_; 
v___x_825_ = lean_array_fget_borrowed(v_givenNames_555_, v_minorIdx_564_);
lean_inc(v___x_825_);
v___y_751_ = v___y_806_;
v___y_752_ = v___x_820_;
v___y_753_ = v___y_809_;
v___y_754_ = v___y_814_;
v___y_755_ = v___y_813_;
v___y_756_ = v___y_811_;
v___y_757_ = v___y_807_;
v___y_758_ = v___y_815_;
v___y_759_ = v___x_817_;
v___y_760_ = v___y_808_;
v___y_761_ = v___x_816_;
v___y_762_ = v___x_818_;
v___y_763_ = v___y_812_;
v___y_764_ = v___x_825_;
goto v___jp_750_;
}
}
v___jp_826_:
{
if (v___y_835_ == 0)
{
lean_object* v___x_836_; uint8_t v___x_837_; 
lean_inc_ref(v___y_828_);
v___x_836_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTargetArity(v___y_828_);
v___x_837_ = lean_nat_dec_lt(v___x_836_, v_initialArity_561_);
if (v___x_837_ == 0)
{
v___y_806_ = v___y_828_;
v___y_807_ = v___y_829_;
v___y_808_ = v___y_835_;
v___y_809_ = v___y_831_;
v___y_810_ = v___x_836_;
v___y_811_ = v___y_833_;
v___y_812_ = v___y_827_;
v___y_813_ = v___y_830_;
v___y_814_ = v___y_832_;
v___y_815_ = v___y_834_;
goto v___jp_805_;
}
else
{
lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; 
v___x_838_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1));
v___x_839_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9);
lean_inc(v_mvarId_554_);
v___x_840_ = l_Lean_Meta_throwTacticEx___redArg(v___x_838_, v_mvarId_554_, v___x_839_, v___y_827_, v___y_830_, v___y_832_, v___y_834_);
if (lean_obj_tag(v___x_840_) == 0)
{
lean_dec_ref_known(v___x_840_, 1);
v___y_806_ = v___y_828_;
v___y_807_ = v___y_829_;
v___y_808_ = v___y_835_;
v___y_809_ = v___y_831_;
v___y_810_ = v___x_836_;
v___y_811_ = v___y_833_;
v___y_812_ = v___y_827_;
v___y_813_ = v___y_830_;
v___y_814_ = v___y_832_;
v___y_815_ = v___y_834_;
goto v___jp_805_;
}
else
{
lean_object* v_a_841_; lean_object* v___x_843_; uint8_t v_isShared_844_; uint8_t v_isSharedCheck_848_; 
lean_dec(v___x_836_);
lean_dec(v___y_831_);
lean_dec_ref(v___y_828_);
lean_dec(v_a_749_);
lean_dec_ref(v_subgoals_568_);
lean_dec_ref(v_recursor_565_);
lean_dec(v_minorIdx_564_);
lean_dec(v_pos_563_);
lean_dec(v_baseSubst_560_);
lean_dec_ref(v_major_558_);
lean_dec(v_mvarId_554_);
v_a_841_ = lean_ctor_get(v___x_840_, 0);
v_isSharedCheck_848_ = !lean_is_exclusive(v___x_840_);
if (v_isSharedCheck_848_ == 0)
{
v___x_843_ = v___x_840_;
v_isShared_844_ = v_isSharedCheck_848_;
goto v_resetjp_842_;
}
else
{
lean_inc(v_a_841_);
lean_dec(v___x_840_);
v___x_843_ = lean_box(0);
v_isShared_844_ = v_isSharedCheck_848_;
goto v_resetjp_842_;
}
v_resetjp_842_:
{
lean_object* v___x_846_; 
if (v_isShared_844_ == 0)
{
v___x_846_ = v___x_843_;
goto v_reusejp_845_;
}
else
{
lean_object* v_reuseFailAlloc_847_; 
v_reuseFailAlloc_847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_847_, 0, v_a_841_);
v___x_846_ = v_reuseFailAlloc_847_;
goto v_reusejp_845_;
}
v_reusejp_845_:
{
return v___x_846_;
}
}
}
}
}
else
{
lean_object* v___x_849_; lean_object* v___x_850_; 
v___x_849_ = lean_box(0);
lean_inc_ref(v___y_828_);
v___x_850_ = l_Lean_Meta_synthInstance_x3f(v___y_828_, v___x_849_, v___y_827_, v___y_830_, v___y_832_, v___y_834_);
if (lean_obj_tag(v___x_850_) == 0)
{
lean_object* v_a_851_; 
v_a_851_ = lean_ctor_get(v___x_850_, 0);
lean_inc(v_a_851_);
lean_dec_ref_known(v___x_850_, 1);
if (lean_obj_tag(v_a_851_) == 0)
{
lean_object* v___x_852_; 
v___x_852_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___y_828_, v___y_831_, v___y_827_, v___y_830_, v___y_832_, v___y_834_);
if (lean_obj_tag(v___x_852_) == 0)
{
lean_object* v_a_853_; lean_object* v___x_854_; 
v_a_853_ = lean_ctor_get(v___x_852_, 0);
lean_inc(v_a_853_);
lean_dec_ref_known(v___x_852_, 1);
lean_inc(v_mvarId_554_);
v___x_854_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTypeBody(v_mvarId_554_, v_a_749_, v_a_853_, v___y_827_, v___y_830_, v___y_832_, v___y_834_);
if (lean_obj_tag(v___x_854_) == 0)
{
lean_object* v_a_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; 
v_a_855_ = lean_ctor_get(v___x_854_, 0);
lean_inc(v_a_855_);
lean_dec_ref_known(v___x_854_, 1);
lean_inc(v_a_853_);
v___x_856_ = l_Lean_Expr_app___override(v_recursor_565_, v_a_853_);
v___x_857_ = lean_nat_add(v_pos_563_, v___y_833_);
lean_dec(v_pos_563_);
v___x_858_ = lean_nat_add(v_minorIdx_564_, v___y_833_);
lean_dec(v_minorIdx_564_);
v___x_859_ = l_Lean_Expr_mvarId_x21(v_a_853_);
lean_dec(v_a_853_);
v___x_860_ = ((lean_object*)(l_Lean_Meta_instInhabitedInductionSubgoal_default___closed__0));
v___x_861_ = lean_box(0);
v___x_862_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_862_, 0, v___x_859_);
lean_ctor_set(v___x_862_, 1, v___x_860_);
lean_ctor_set(v___x_862_, 2, v___x_861_);
v___x_863_ = lean_array_push(v_subgoals_568_, v___x_862_);
v_pos_563_ = v___x_857_;
v_minorIdx_564_ = v___x_858_;
v_recursor_565_ = v___x_856_;
v_recursorType_566_ = v_a_855_;
v_subgoals_568_ = v___x_863_;
v_a_569_ = v___y_827_;
v_a_570_ = v___y_830_;
v_a_571_ = v___y_832_;
v_a_572_ = v___y_834_;
goto _start;
}
else
{
lean_object* v_a_865_; lean_object* v___x_867_; uint8_t v_isShared_868_; uint8_t v_isSharedCheck_872_; 
lean_dec(v_a_853_);
lean_dec_ref(v_subgoals_568_);
lean_dec_ref(v_recursor_565_);
lean_dec(v_minorIdx_564_);
lean_dec(v_pos_563_);
lean_dec(v_baseSubst_560_);
lean_dec_ref(v_major_558_);
lean_dec(v_mvarId_554_);
v_a_865_ = lean_ctor_get(v___x_854_, 0);
v_isSharedCheck_872_ = !lean_is_exclusive(v___x_854_);
if (v_isSharedCheck_872_ == 0)
{
v___x_867_ = v___x_854_;
v_isShared_868_ = v_isSharedCheck_872_;
goto v_resetjp_866_;
}
else
{
lean_inc(v_a_865_);
lean_dec(v___x_854_);
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
lean_object* v_a_873_; lean_object* v___x_875_; uint8_t v_isShared_876_; uint8_t v_isSharedCheck_880_; 
lean_dec(v_a_749_);
lean_dec_ref(v_subgoals_568_);
lean_dec_ref(v_recursor_565_);
lean_dec(v_minorIdx_564_);
lean_dec(v_pos_563_);
lean_dec(v_baseSubst_560_);
lean_dec_ref(v_major_558_);
lean_dec(v_mvarId_554_);
v_a_873_ = lean_ctor_get(v___x_852_, 0);
v_isSharedCheck_880_ = !lean_is_exclusive(v___x_852_);
if (v_isSharedCheck_880_ == 0)
{
v___x_875_ = v___x_852_;
v_isShared_876_ = v_isSharedCheck_880_;
goto v_resetjp_874_;
}
else
{
lean_inc(v_a_873_);
lean_dec(v___x_852_);
v___x_875_ = lean_box(0);
v_isShared_876_ = v_isSharedCheck_880_;
goto v_resetjp_874_;
}
v_resetjp_874_:
{
lean_object* v___x_878_; 
if (v_isShared_876_ == 0)
{
v___x_878_ = v___x_875_;
goto v_reusejp_877_;
}
else
{
lean_object* v_reuseFailAlloc_879_; 
v_reuseFailAlloc_879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_879_, 0, v_a_873_);
v___x_878_ = v_reuseFailAlloc_879_;
goto v_reusejp_877_;
}
v_reusejp_877_:
{
return v___x_878_;
}
}
}
}
else
{
lean_object* v_val_881_; lean_object* v___x_882_; 
lean_dec(v___y_831_);
lean_dec_ref(v___y_828_);
v_val_881_ = lean_ctor_get(v_a_851_, 0);
lean_inc(v_val_881_);
lean_dec_ref_known(v_a_851_, 1);
lean_inc(v_mvarId_554_);
v___x_882_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTypeBody(v_mvarId_554_, v_a_749_, v_val_881_, v___y_827_, v___y_830_, v___y_832_, v___y_834_);
if (lean_obj_tag(v___x_882_) == 0)
{
lean_object* v_a_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; 
v_a_883_ = lean_ctor_get(v___x_882_, 0);
lean_inc(v_a_883_);
lean_dec_ref_known(v___x_882_, 1);
v___x_884_ = l_Lean_Expr_app___override(v_recursor_565_, v_val_881_);
v___x_885_ = lean_nat_add(v_pos_563_, v___y_833_);
lean_dec(v_pos_563_);
v___x_886_ = lean_nat_add(v_minorIdx_564_, v___y_833_);
lean_dec(v_minorIdx_564_);
v_pos_563_ = v___x_885_;
v_minorIdx_564_ = v___x_886_;
v_recursor_565_ = v___x_884_;
v_recursorType_566_ = v_a_883_;
v_a_569_ = v___y_827_;
v_a_570_ = v___y_830_;
v_a_571_ = v___y_832_;
v_a_572_ = v___y_834_;
goto _start;
}
else
{
lean_object* v_a_888_; lean_object* v___x_890_; uint8_t v_isShared_891_; uint8_t v_isSharedCheck_895_; 
lean_dec(v_val_881_);
lean_dec_ref(v_subgoals_568_);
lean_dec_ref(v_recursor_565_);
lean_dec(v_minorIdx_564_);
lean_dec(v_pos_563_);
lean_dec(v_baseSubst_560_);
lean_dec_ref(v_major_558_);
lean_dec(v_mvarId_554_);
v_a_888_ = lean_ctor_get(v___x_882_, 0);
v_isSharedCheck_895_ = !lean_is_exclusive(v___x_882_);
if (v_isSharedCheck_895_ == 0)
{
v___x_890_ = v___x_882_;
v_isShared_891_ = v_isSharedCheck_895_;
goto v_resetjp_889_;
}
else
{
lean_inc(v_a_888_);
lean_dec(v___x_882_);
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
else
{
lean_object* v_a_896_; lean_object* v___x_898_; uint8_t v_isShared_899_; uint8_t v_isSharedCheck_903_; 
lean_dec(v___y_831_);
lean_dec_ref(v___y_828_);
lean_dec(v_a_749_);
lean_dec_ref(v_subgoals_568_);
lean_dec_ref(v_recursor_565_);
lean_dec(v_minorIdx_564_);
lean_dec(v_pos_563_);
lean_dec(v_baseSubst_560_);
lean_dec_ref(v_major_558_);
lean_dec(v_mvarId_554_);
v_a_896_ = lean_ctor_get(v___x_850_, 0);
v_isSharedCheck_903_ = !lean_is_exclusive(v___x_850_);
if (v_isSharedCheck_903_ == 0)
{
v___x_898_ = v___x_850_;
v_isShared_899_ = v_isSharedCheck_903_;
goto v_resetjp_897_;
}
else
{
lean_inc(v_a_896_);
lean_dec(v___x_850_);
v___x_898_ = lean_box(0);
v_isShared_899_ = v_isSharedCheck_903_;
goto v_resetjp_897_;
}
v_resetjp_897_:
{
lean_object* v___x_901_; 
if (v_isShared_899_ == 0)
{
v___x_901_ = v___x_898_;
goto v_reusejp_900_;
}
else
{
lean_object* v_reuseFailAlloc_902_; 
v_reuseFailAlloc_902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_902_, 0, v_a_896_);
v___x_901_ = v_reuseFailAlloc_902_;
goto v_reusejp_900_;
}
v_reusejp_900_:
{
return v___x_901_;
}
}
}
}
}
v___jp_904_:
{
uint8_t v___x_914_; 
v___x_914_ = l_Lean_BinderInfo_isInstImplicit(v___y_910_);
if (v___x_914_ == 0)
{
v___y_827_ = v___y_905_;
v___y_828_ = v___y_906_;
v___y_829_ = v___y_907_;
v___y_830_ = v___y_908_;
v___y_831_ = v___y_913_;
v___y_832_ = v___y_909_;
v___y_833_ = v___y_911_;
v___y_834_ = v___y_912_;
v___y_835_ = v___x_914_;
goto v___jp_826_;
}
else
{
lean_object* v___x_915_; lean_object* v___x_916_; uint8_t v___x_917_; 
v___x_915_ = lean_array_get_size(v_givenNames_555_);
v___x_916_ = lean_unsigned_to_nat(0u);
v___x_917_ = lean_nat_dec_eq(v___x_915_, v___x_916_);
v___y_827_ = v___y_905_;
v___y_828_ = v___y_906_;
v___y_829_ = v___y_907_;
v___y_830_ = v___y_908_;
v___y_831_ = v___y_913_;
v___y_832_ = v___y_909_;
v___y_833_ = v___y_911_;
v___y_834_ = v___y_912_;
v___y_835_ = v___x_917_;
goto v___jp_826_;
}
}
v___jp_918_:
{
if (lean_obj_tag(v_a_749_) == 7)
{
lean_object* v_binderName_925_; lean_object* v_binderType_926_; uint8_t v_binderInfo_927_; lean_object* v___x_928_; lean_object* v___x_929_; uint8_t v___x_930_; 
v_binderName_925_ = lean_ctor_get(v_a_749_, 0);
v_binderType_926_ = lean_ctor_get(v_a_749_, 1);
v_binderInfo_927_ = lean_ctor_get_uint8(v_a_749_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_926_);
v___x_928_ = l_Lean_Expr_headBeta(v_binderType_926_);
v___x_929_ = lean_unsigned_to_nat(1u);
v___x_930_ = lean_nat_dec_eq(v_numMinors_562_, v___x_929_);
if (v___x_930_ == 0)
{
lean_object* v___x_931_; lean_object* v___x_932_; 
v___x_931_ = l_Lean_Name_eraseMacroScopes(v_binderName_925_);
v___x_932_ = l_Lean_Name_append(v___y_920_, v___x_931_);
v___y_905_ = v___y_921_;
v___y_906_ = v___x_928_;
v___y_907_ = v___y_919_;
v___y_908_ = v___y_922_;
v___y_909_ = v___y_923_;
v___y_910_ = v_binderInfo_927_;
v___y_911_ = v___x_929_;
v___y_912_ = v___y_924_;
v___y_913_ = v___x_932_;
goto v___jp_904_;
}
else
{
v___y_905_ = v___y_921_;
v___y_906_ = v___x_928_;
v___y_907_ = v___y_919_;
v___y_908_ = v___y_922_;
v___y_909_ = v___y_923_;
v___y_910_ = v_binderInfo_927_;
v___y_911_ = v___x_929_;
v___y_912_ = v___y_924_;
v___y_913_ = v___y_920_;
goto v___jp_904_;
}
}
else
{
lean_object* v___x_933_; lean_object* v___x_934_; 
lean_dec(v___y_920_);
lean_dec(v_a_749_);
lean_dec_ref(v_subgoals_568_);
lean_dec_ref(v_recursor_565_);
lean_dec(v_minorIdx_564_);
lean_dec(v_pos_563_);
lean_dec(v_baseSubst_560_);
lean_dec_ref(v_major_558_);
lean_dec(v_mvarId_554_);
v___x_933_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__15, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__15_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__15);
v___x_934_ = l_panic___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__4(v___x_933_, v___y_921_, v___y_922_, v___y_923_, v___y_924_);
return v___x_934_;
}
}
v___jp_935_:
{
if (v___y_936_ == 0)
{
lean_dec(v_a_749_);
lean_dec(v_minorIdx_564_);
lean_dec(v_pos_563_);
lean_dec(v_baseSubst_560_);
lean_dec_ref(v_major_558_);
if (v_consumedMajor_567_ == 0)
{
lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; 
v___x_937_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1));
v___x_938_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9);
lean_inc(v_mvarId_554_);
v___x_939_ = l_Lean_Meta_throwTacticEx___redArg(v___x_937_, v_mvarId_554_, v___x_938_, v_a_569_, v_a_570_, v_a_571_, v_a_572_);
if (lean_obj_tag(v___x_939_) == 0)
{
lean_dec_ref_known(v___x_939_, 1);
v___y_575_ = v_a_569_;
v___y_576_ = v_a_570_;
v___y_577_ = v_a_571_;
v___y_578_ = v_a_572_;
goto v___jp_574_;
}
else
{
lean_object* v_a_940_; lean_object* v___x_942_; uint8_t v_isShared_943_; uint8_t v_isSharedCheck_947_; 
lean_dec_ref(v_subgoals_568_);
lean_dec_ref(v_recursor_565_);
lean_dec(v_mvarId_554_);
v_a_940_ = lean_ctor_get(v___x_939_, 0);
v_isSharedCheck_947_ = !lean_is_exclusive(v___x_939_);
if (v_isSharedCheck_947_ == 0)
{
v___x_942_ = v___x_939_;
v_isShared_943_ = v_isSharedCheck_947_;
goto v_resetjp_941_;
}
else
{
lean_inc(v_a_940_);
lean_dec(v___x_939_);
v___x_942_ = lean_box(0);
v_isShared_943_ = v_isSharedCheck_947_;
goto v_resetjp_941_;
}
v_resetjp_941_:
{
lean_object* v___x_945_; 
if (v_isShared_943_ == 0)
{
v___x_945_ = v___x_942_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v_a_940_);
v___x_945_ = v_reuseFailAlloc_946_;
goto v_reusejp_944_;
}
v_reusejp_944_:
{
return v___x_945_;
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
else
{
lean_object* v___x_948_; uint8_t v___x_949_; 
v___x_948_ = l_Lean_Meta_RecursorInfo_firstIndexPos(v_recursorInfo_556_);
v___x_949_ = lean_nat_dec_eq(v_pos_563_, v___x_948_);
lean_dec(v___x_948_);
if (v___x_949_ == 0)
{
lean_object* v___x_950_; 
lean_inc(v_mvarId_554_);
v___x_950_ = l_Lean_MVarId_getTag(v_mvarId_554_, v_a_569_, v_a_570_, v_a_571_, v_a_572_);
if (lean_obj_tag(v___x_950_) == 0)
{
lean_object* v_a_951_; uint8_t v___x_952_; 
v_a_951_ = lean_ctor_get(v___x_950_, 0);
lean_inc(v_a_951_);
lean_dec_ref_known(v___x_950_, 1);
v___x_952_ = lean_nat_dec_le(v_numMinors_562_, v_minorIdx_564_);
if (v___x_952_ == 0)
{
v___y_919_ = v___y_936_;
v___y_920_ = v_a_951_;
v___y_921_ = v_a_569_;
v___y_922_ = v_a_570_;
v___y_923_ = v_a_571_;
v___y_924_ = v_a_572_;
goto v___jp_918_;
}
else
{
lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; 
v___x_953_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1));
v___x_954_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9);
lean_inc(v_mvarId_554_);
v___x_955_ = l_Lean_Meta_throwTacticEx___redArg(v___x_953_, v_mvarId_554_, v___x_954_, v_a_569_, v_a_570_, v_a_571_, v_a_572_);
if (lean_obj_tag(v___x_955_) == 0)
{
lean_dec_ref_known(v___x_955_, 1);
v___y_919_ = v___y_936_;
v___y_920_ = v_a_951_;
v___y_921_ = v_a_569_;
v___y_922_ = v_a_570_;
v___y_923_ = v_a_571_;
v___y_924_ = v_a_572_;
goto v___jp_918_;
}
else
{
lean_object* v_a_956_; lean_object* v___x_958_; uint8_t v_isShared_959_; uint8_t v_isSharedCheck_963_; 
lean_dec(v_a_951_);
lean_dec(v_a_749_);
lean_dec_ref(v_subgoals_568_);
lean_dec_ref(v_recursor_565_);
lean_dec(v_minorIdx_564_);
lean_dec(v_pos_563_);
lean_dec(v_baseSubst_560_);
lean_dec_ref(v_major_558_);
lean_dec(v_mvarId_554_);
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
}
else
{
lean_object* v_a_964_; lean_object* v___x_966_; uint8_t v_isShared_967_; uint8_t v_isSharedCheck_971_; 
lean_dec(v_a_749_);
lean_dec_ref(v_subgoals_568_);
lean_dec_ref(v_recursor_565_);
lean_dec(v_minorIdx_564_);
lean_dec(v_pos_563_);
lean_dec(v_baseSubst_560_);
lean_dec_ref(v_major_558_);
lean_dec(v_mvarId_554_);
v_a_964_ = lean_ctor_get(v___x_950_, 0);
v_isSharedCheck_971_ = !lean_is_exclusive(v___x_950_);
if (v_isSharedCheck_971_ == 0)
{
v___x_966_ = v___x_950_;
v_isShared_967_ = v_isSharedCheck_971_;
goto v_resetjp_965_;
}
else
{
lean_inc(v_a_964_);
lean_dec(v___x_950_);
v___x_966_ = lean_box(0);
v_isShared_967_ = v_isSharedCheck_971_;
goto v_resetjp_965_;
}
v_resetjp_965_:
{
lean_object* v___x_969_; 
if (v_isShared_967_ == 0)
{
v___x_969_ = v___x_966_;
goto v_reusejp_968_;
}
else
{
lean_object* v_reuseFailAlloc_970_; 
v_reuseFailAlloc_970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_970_, 0, v_a_964_);
v___x_969_ = v_reuseFailAlloc_970_;
goto v_reusejp_968_;
}
v_reusejp_968_:
{
return v___x_969_;
}
}
}
}
else
{
lean_object* v___x_972_; lean_object* v___x_973_; uint8_t v___x_974_; 
v___x_972_ = lean_unsigned_to_nat(0u);
v___x_973_ = lean_array_get_size(v_indices_559_);
v___x_974_ = lean_nat_dec_lt(v___x_972_, v___x_973_);
if (v___x_974_ == 0)
{
v___y_714_ = v___x_949_;
v___y_715_ = v___x_973_;
v_fst_716_ = v_recursor_565_;
v_snd_717_ = v_a_749_;
goto v___jp_713_;
}
else
{
lean_object* v___x_975_; uint8_t v___x_976_; 
lean_inc(v_a_749_);
lean_inc_ref(v_recursor_565_);
v___x_975_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_975_, 0, v_recursor_565_);
lean_ctor_set(v___x_975_, 1, v_a_749_);
v___x_976_ = lean_nat_dec_le(v___x_973_, v___x_973_);
if (v___x_976_ == 0)
{
if (v___x_974_ == 0)
{
lean_dec_ref_known(v___x_975_, 2);
v___y_714_ = v___x_949_;
v___y_715_ = v___x_973_;
v_fst_716_ = v_recursor_565_;
v_snd_717_ = v_a_749_;
goto v___jp_713_;
}
else
{
size_t v___x_977_; size_t v___x_978_; lean_object* v___x_979_; 
lean_dec(v_a_749_);
lean_dec_ref(v_recursor_565_);
v___x_977_ = ((size_t)0ULL);
v___x_978_ = lean_usize_of_nat(v___x_973_);
lean_inc(v_mvarId_554_);
v___x_979_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__5(v_mvarId_554_, v_indices_559_, v___x_977_, v___x_978_, v___x_975_, v_a_569_, v_a_570_, v_a_571_, v_a_572_);
v___y_734_ = v___x_973_;
v___y_735_ = v___x_949_;
v___y_736_ = v___x_979_;
goto v___jp_733_;
}
}
else
{
size_t v___x_980_; size_t v___x_981_; lean_object* v___x_982_; 
lean_dec(v_a_749_);
lean_dec_ref(v_recursor_565_);
v___x_980_ = ((size_t)0ULL);
v___x_981_ = lean_usize_of_nat(v___x_973_);
lean_inc(v_mvarId_554_);
v___x_982_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__5(v_mvarId_554_, v_indices_559_, v___x_980_, v___x_981_, v___x_975_, v_a_569_, v_a_570_, v_a_571_, v_a_572_);
v___y_734_ = v___x_973_;
v___y_735_ = v___x_949_;
v___y_736_ = v___x_982_;
goto v___jp_733_;
}
}
}
}
}
}
else
{
lean_object* v_a_986_; lean_object* v___x_988_; uint8_t v_isShared_989_; uint8_t v_isSharedCheck_993_; 
lean_dec_ref(v_subgoals_568_);
lean_dec_ref(v_recursor_565_);
lean_dec(v_minorIdx_564_);
lean_dec(v_pos_563_);
lean_dec(v_baseSubst_560_);
lean_dec_ref(v_major_558_);
lean_dec(v_mvarId_554_);
v_a_986_ = lean_ctor_get(v___x_748_, 0);
v_isSharedCheck_993_ = !lean_is_exclusive(v___x_748_);
if (v_isSharedCheck_993_ == 0)
{
v___x_988_ = v___x_748_;
v_isShared_989_ = v_isSharedCheck_993_;
goto v_resetjp_987_;
}
else
{
lean_inc(v_a_986_);
lean_dec(v___x_748_);
v___x_988_ = lean_box(0);
v_isShared_989_ = v_isSharedCheck_993_;
goto v_resetjp_987_;
}
v_resetjp_987_:
{
lean_object* v___x_991_; 
if (v_isShared_989_ == 0)
{
v___x_991_ = v___x_988_;
goto v_reusejp_990_;
}
else
{
lean_object* v_reuseFailAlloc_992_; 
v_reuseFailAlloc_992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_992_, 0, v_a_986_);
v___x_991_ = v_reuseFailAlloc_992_;
goto v_reusejp_990_;
}
v_reusejp_990_:
{
return v___x_991_;
}
}
}
v___jp_574_:
{
lean_object* v___x_579_; 
v___x_579_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0___redArg(v_mvarId_554_, v_recursor_565_, v___y_576_);
if (lean_obj_tag(v___x_579_) == 0)
{
lean_object* v___x_581_; uint8_t v_isShared_582_; uint8_t v_isSharedCheck_620_; 
v_isSharedCheck_620_ = !lean_is_exclusive(v___x_579_);
if (v_isSharedCheck_620_ == 0)
{
lean_object* v_unused_621_; 
v_unused_621_ = lean_ctor_get(v___x_579_, 0);
lean_dec(v_unused_621_);
v___x_581_ = v___x_579_;
v_isShared_582_ = v_isSharedCheck_620_;
goto v_resetjp_580_;
}
else
{
lean_dec(v___x_579_);
v___x_581_ = lean_box(0);
v_isShared_582_ = v_isSharedCheck_620_;
goto v_resetjp_580_;
}
v_resetjp_580_:
{
lean_object* v_options_583_; uint8_t v_hasTrace_584_; 
v_options_583_ = lean_ctor_get(v___y_577_, 2);
v_hasTrace_584_ = lean_ctor_get_uint8(v_options_583_, sizeof(void*)*1);
if (v_hasTrace_584_ == 0)
{
lean_object* v___x_586_; 
if (v_isShared_582_ == 0)
{
lean_ctor_set(v___x_581_, 0, v_subgoals_568_);
v___x_586_ = v___x_581_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_587_; 
v_reuseFailAlloc_587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_587_, 0, v_subgoals_568_);
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
v_inheritedTraceOptions_588_ = lean_ctor_get(v___y_577_, 13);
v___x_589_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__2));
v___x_590_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5);
v___x_591_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_588_, v_options_583_, v___x_590_);
if (v___x_591_ == 0)
{
lean_object* v___x_593_; 
if (v_isShared_582_ == 0)
{
lean_ctor_set(v___x_581_, 0, v_subgoals_568_);
v___x_593_ = v___x_581_;
goto v_reusejp_592_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v_subgoals_568_);
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
lean_del_object(v___x_581_);
v___x_595_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__7, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__7_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__7);
v___x_596_ = lean_array_get_size(v_subgoals_568_);
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
v___x_603_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1(v___x_589_, v___x_602_, v___y_575_, v___y_576_, v___y_577_, v___y_578_);
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
lean_ctor_set(v___x_605_, 0, v_subgoals_568_);
v___x_608_ = v___x_605_;
goto v_reusejp_607_;
}
else
{
lean_object* v_reuseFailAlloc_609_; 
v_reuseFailAlloc_609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v_subgoals_568_);
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
lean_dec_ref(v_subgoals_568_);
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
lean_dec_ref(v_subgoals_568_);
v_a_622_ = lean_ctor_get(v___x_579_, 0);
v_isSharedCheck_629_ = !lean_is_exclusive(v___x_579_);
if (v_isSharedCheck_629_ == 0)
{
v___x_624_ = v___x_579_;
v_isShared_625_ = v_isSharedCheck_629_;
goto v_resetjp_623_;
}
else
{
lean_inc(v_a_622_);
lean_dec(v___x_579_);
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
v___x_647_ = l_Lean_Meta_introNCore(v___y_642_, v___y_643_, v___y_633_, v___y_646_, v___y_639_, v___y_637_, v___y_641_, v___y_631_, v___y_645_);
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
v___x_652_ = l_Lean_Meta_introNCore(v_snd_650_, v___y_632_, v___x_651_, v___y_639_, v___y_638_, v___y_637_, v___y_641_, v___y_631_, v___y_645_);
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
lean_inc(v_baseSubst_560_);
lean_inc(v___y_640_);
v___x_656_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__2___redArg(v___y_644_, v_reverted_557_, v_fst_654_, v___y_640_, v___y_640_, v_baseSubst_560_);
lean_dec(v___y_640_);
lean_dec(v_fst_654_);
lean_dec(v___y_644_);
v_sz_657_ = lean_array_size(v_fst_649_);
v___x_658_ = ((size_t)0ULL);
v___x_659_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__3(v_sz_657_, v___x_658_, v_fst_649_);
v___x_660_ = lean_nat_add(v_pos_563_, v___y_635_);
lean_dec(v_pos_563_);
v___x_661_ = lean_nat_add(v_minorIdx_564_, v___y_635_);
lean_dec(v_minorIdx_564_);
v___x_662_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_662_, 0, v_snd_655_);
lean_ctor_set(v___x_662_, 1, v___x_659_);
lean_ctor_set(v___x_662_, 2, v___x_656_);
v___x_663_ = lean_array_push(v_subgoals_568_, v___x_662_);
v_pos_563_ = v___x_660_;
v_minorIdx_564_ = v___x_661_;
v_recursor_565_ = v___y_636_;
v_recursorType_566_ = v___y_634_;
v_subgoals_568_ = v___x_663_;
v_a_569_ = v___y_637_;
v_a_570_ = v___y_641_;
v_a_571_ = v___y_631_;
v_a_572_ = v___y_645_;
goto _start;
}
else
{
lean_object* v_a_665_; lean_object* v___x_667_; uint8_t v_isShared_668_; uint8_t v_isSharedCheck_672_; 
lean_dec(v_fst_649_);
lean_dec(v___y_644_);
lean_dec(v___y_640_);
lean_dec_ref(v___y_636_);
lean_dec_ref(v___y_634_);
lean_dec_ref(v_subgoals_568_);
lean_dec(v_minorIdx_564_);
lean_dec(v_pos_563_);
lean_dec(v_baseSubst_560_);
lean_dec_ref(v_major_558_);
lean_dec(v_mvarId_554_);
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
lean_dec(v___y_644_);
lean_dec(v___y_640_);
lean_dec_ref(v___y_636_);
lean_dec_ref(v___y_634_);
lean_dec(v___y_632_);
lean_dec_ref(v_subgoals_568_);
lean_dec(v_minorIdx_564_);
lean_dec(v_pos_563_);
lean_dec(v_baseSubst_560_);
lean_dec_ref(v_major_558_);
lean_dec(v_mvarId_554_);
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
v___x_698_ = l_Lean_Expr_fvarId_x21(v_major_558_);
v___x_699_ = l_Lean_MVarId_tryClear(v___x_697_, v___x_698_, v___y_693_, v___y_694_, v___y_695_, v___y_696_);
if (lean_obj_tag(v___x_699_) == 0)
{
uint8_t v_explicit_700_; 
v_explicit_700_ = lean_ctor_get_uint8(v___y_688_, sizeof(void*)*1);
if (v_explicit_700_ == 0)
{
lean_object* v_a_701_; lean_object* v_varNames_702_; 
v_a_701_ = lean_ctor_get(v___x_699_, 0);
lean_inc(v_a_701_);
lean_dec_ref_known(v___x_699_, 1);
v_varNames_702_ = lean_ctor_get(v___y_688_, 0);
lean_inc(v_varNames_702_);
lean_dec_ref(v___y_688_);
v___y_631_ = v___y_695_;
v___y_632_ = v___y_684_;
v___y_633_ = v_varNames_702_;
v___y_634_ = v___y_691_;
v___y_635_ = v___y_692_;
v___y_636_ = v___y_682_;
v___y_637_ = v___y_693_;
v___y_638_ = v___y_683_;
v___y_639_ = v___y_686_;
v___y_640_ = v___y_685_;
v___y_641_ = v___y_694_;
v___y_642_ = v_a_701_;
v___y_643_ = v___y_689_;
v___y_644_ = v___y_690_;
v___y_645_ = v___y_696_;
v___y_646_ = v___y_683_;
goto v___jp_630_;
}
else
{
lean_object* v_a_703_; lean_object* v_varNames_704_; 
v_a_703_ = lean_ctor_get(v___x_699_, 0);
lean_inc(v_a_703_);
lean_dec_ref_known(v___x_699_, 1);
v_varNames_704_ = lean_ctor_get(v___y_688_, 0);
lean_inc(v_varNames_704_);
lean_dec_ref(v___y_688_);
v___y_631_ = v___y_695_;
v___y_632_ = v___y_684_;
v___y_633_ = v_varNames_704_;
v___y_634_ = v___y_691_;
v___y_635_ = v___y_692_;
v___y_636_ = v___y_682_;
v___y_637_ = v___y_693_;
v___y_638_ = v___y_683_;
v___y_639_ = v___y_686_;
v___y_640_ = v___y_685_;
v___y_641_ = v___y_694_;
v___y_642_ = v_a_703_;
v___y_643_ = v___y_689_;
v___y_644_ = v___y_690_;
v___y_645_ = v___y_696_;
v___y_646_ = v___y_686_;
goto v___jp_630_;
}
}
else
{
lean_object* v_a_705_; lean_object* v___x_707_; uint8_t v_isShared_708_; uint8_t v_isSharedCheck_712_; 
lean_dec_ref(v___y_691_);
lean_dec(v___y_690_);
lean_dec(v___y_689_);
lean_dec_ref(v___y_688_);
lean_dec(v___y_685_);
lean_dec(v___y_684_);
lean_dec_ref(v___y_682_);
lean_dec_ref(v_subgoals_568_);
lean_dec(v_minorIdx_564_);
lean_dec(v_pos_563_);
lean_dec(v_baseSubst_560_);
lean_dec_ref(v_major_558_);
lean_dec(v_mvarId_554_);
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
lean_object* v___x_718_; 
lean_inc(v_mvarId_554_);
v___x_718_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTypeBody(v_mvarId_554_, v_snd_717_, v_major_558_, v_a_569_, v_a_570_, v_a_571_, v_a_572_);
if (lean_obj_tag(v___x_718_) == 0)
{
lean_object* v_a_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; 
v_a_719_ = lean_ctor_get(v___x_718_, 0);
lean_inc(v_a_719_);
lean_dec_ref_known(v___x_718_, 1);
lean_inc_ref(v_major_558_);
v___x_720_ = l_Lean_Expr_app___override(v_fst_716_, v_major_558_);
v___x_721_ = lean_unsigned_to_nat(1u);
v___x_722_ = lean_nat_add(v_pos_563_, v___x_721_);
lean_dec(v_pos_563_);
v___x_723_ = lean_nat_add(v___x_722_, v___y_715_);
lean_dec(v___y_715_);
lean_dec(v___x_722_);
v_pos_563_ = v___x_723_;
v_recursor_565_ = v___x_720_;
v_recursorType_566_ = v_a_719_;
v_consumedMajor_567_ = v___y_714_;
goto _start;
}
else
{
lean_object* v_a_725_; lean_object* v___x_727_; uint8_t v_isShared_728_; uint8_t v_isSharedCheck_732_; 
lean_dec_ref(v_fst_716_);
lean_dec(v___y_715_);
lean_dec_ref(v_subgoals_568_);
lean_dec(v_minorIdx_564_);
lean_dec(v_pos_563_);
lean_dec(v_baseSubst_560_);
lean_dec_ref(v_major_558_);
lean_dec(v_mvarId_554_);
v_a_725_ = lean_ctor_get(v___x_718_, 0);
v_isSharedCheck_732_ = !lean_is_exclusive(v___x_718_);
if (v_isSharedCheck_732_ == 0)
{
v___x_727_ = v___x_718_;
v_isShared_728_ = v_isSharedCheck_732_;
goto v_resetjp_726_;
}
else
{
lean_inc(v_a_725_);
lean_dec(v___x_718_);
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
lean_dec_ref(v_subgoals_568_);
lean_dec(v_minorIdx_564_);
lean_dec(v_pos_563_);
lean_dec(v_baseSubst_560_);
lean_dec_ref(v_major_558_);
lean_dec(v_mvarId_554_);
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
lean_object* v_mvarId_994_ = _args[0];
lean_object* v_givenNames_995_ = _args[1];
lean_object* v_recursorInfo_996_ = _args[2];
lean_object* v_reverted_997_ = _args[3];
lean_object* v_major_998_ = _args[4];
lean_object* v_indices_999_ = _args[5];
lean_object* v_baseSubst_1000_ = _args[6];
lean_object* v_initialArity_1001_ = _args[7];
lean_object* v_numMinors_1002_ = _args[8];
lean_object* v_pos_1003_ = _args[9];
lean_object* v_minorIdx_1004_ = _args[10];
lean_object* v_recursor_1005_ = _args[11];
lean_object* v_recursorType_1006_ = _args[12];
lean_object* v_consumedMajor_1007_ = _args[13];
lean_object* v_subgoals_1008_ = _args[14];
lean_object* v_a_1009_ = _args[15];
lean_object* v_a_1010_ = _args[16];
lean_object* v_a_1011_ = _args[17];
lean_object* v_a_1012_ = _args[18];
lean_object* v_a_1013_ = _args[19];
_start:
{
uint8_t v_consumedMajor_boxed_1014_; lean_object* v_res_1015_; 
v_consumedMajor_boxed_1014_ = lean_unbox(v_consumedMajor_1007_);
v_res_1015_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop(v_mvarId_994_, v_givenNames_995_, v_recursorInfo_996_, v_reverted_997_, v_major_998_, v_indices_999_, v_baseSubst_1000_, v_initialArity_1001_, v_numMinors_1002_, v_pos_1003_, v_minorIdx_1004_, v_recursor_1005_, v_recursorType_1006_, v_consumedMajor_boxed_1014_, v_subgoals_1008_, v_a_1009_, v_a_1010_, v_a_1011_, v_a_1012_);
lean_dec(v_a_1012_);
lean_dec_ref(v_a_1011_);
lean_dec(v_a_1010_);
lean_dec_ref(v_a_1009_);
lean_dec(v_numMinors_1002_);
lean_dec(v_initialArity_1001_);
lean_dec_ref(v_indices_999_);
lean_dec_ref(v_reverted_997_);
lean_dec_ref(v_recursorInfo_996_);
lean_dec_ref(v_givenNames_995_);
return v_res_1015_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0(lean_object* v_mvarId_1016_, lean_object* v_val_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_){
_start:
{
lean_object* v___x_1023_; 
v___x_1023_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0___redArg(v_mvarId_1016_, v_val_1017_, v___y_1019_);
return v___x_1023_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0___boxed(lean_object* v_mvarId_1024_, lean_object* v_val_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_){
_start:
{
lean_object* v_res_1031_; 
v_res_1031_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0(v_mvarId_1024_, v_val_1025_, v___y_1026_, v___y_1027_, v___y_1028_, v___y_1029_);
lean_dec(v___y_1029_);
lean_dec_ref(v___y_1028_);
lean_dec(v___y_1027_);
lean_dec_ref(v___y_1026_);
return v_res_1031_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__2(lean_object* v___x_1032_, lean_object* v_reverted_1033_, lean_object* v_fst_1034_, lean_object* v_n_1035_, lean_object* v_j_1036_, lean_object* v_a_1037_, lean_object* v_a_1038_){
_start:
{
lean_object* v___x_1039_; 
v___x_1039_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__2___redArg(v___x_1032_, v_reverted_1033_, v_fst_1034_, v_n_1035_, v_j_1036_, v_a_1038_);
return v___x_1039_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__2___boxed(lean_object* v___x_1040_, lean_object* v_reverted_1041_, lean_object* v_fst_1042_, lean_object* v_n_1043_, lean_object* v_j_1044_, lean_object* v_a_1045_, lean_object* v_a_1046_){
_start:
{
lean_object* v_res_1047_; 
v_res_1047_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__2(v___x_1040_, v_reverted_1041_, v_fst_1042_, v_n_1043_, v_j_1044_, v_a_1045_, v_a_1046_);
lean_dec(v_n_1043_);
lean_dec_ref(v_fst_1042_);
lean_dec_ref(v_reverted_1041_);
lean_dec(v___x_1040_);
return v_res_1047_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0(lean_object* v_00_u03b2_1048_, lean_object* v_x_1049_, lean_object* v_x_1050_, lean_object* v_x_1051_){
_start:
{
lean_object* v___x_1052_; 
v___x_1052_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0___redArg(v_x_1049_, v_x_1050_, v_x_1051_);
return v___x_1052_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1053_, lean_object* v_x_1054_, size_t v_x_1055_, size_t v_x_1056_, lean_object* v_x_1057_, lean_object* v_x_1058_){
_start:
{
lean_object* v___x_1059_; 
v___x_1059_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2___redArg(v_x_1054_, v_x_1055_, v_x_1056_, v_x_1057_, v_x_1058_);
return v___x_1059_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1060_, lean_object* v_x_1061_, lean_object* v_x_1062_, lean_object* v_x_1063_, lean_object* v_x_1064_, lean_object* v_x_1065_){
_start:
{
size_t v_x_11483__boxed_1066_; size_t v_x_11484__boxed_1067_; lean_object* v_res_1068_; 
v_x_11483__boxed_1066_ = lean_unbox_usize(v_x_1062_);
lean_dec(v_x_1062_);
v_x_11484__boxed_1067_ = lean_unbox_usize(v_x_1063_);
lean_dec(v_x_1063_);
v_res_1068_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2(v_00_u03b2_1060_, v_x_1061_, v_x_11483__boxed_1066_, v_x_11484__boxed_1067_, v_x_1064_, v_x_1065_);
return v_res_1068_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__8(lean_object* v_00_u03b2_1069_, lean_object* v_n_1070_, lean_object* v_k_1071_, lean_object* v_v_1072_){
_start:
{
lean_object* v___x_1073_; 
v___x_1073_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__8___redArg(v_n_1070_, v_k_1071_, v_v_1072_);
return v___x_1073_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__9(lean_object* v_00_u03b2_1074_, size_t v_depth_1075_, lean_object* v_keys_1076_, lean_object* v_vals_1077_, lean_object* v_heq_1078_, lean_object* v_i_1079_, lean_object* v_entries_1080_){
_start:
{
lean_object* v___x_1081_; 
v___x_1081_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__9___redArg(v_depth_1075_, v_keys_1076_, v_vals_1077_, v_i_1079_, v_entries_1080_);
return v___x_1081_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__9___boxed(lean_object* v_00_u03b2_1082_, lean_object* v_depth_1083_, lean_object* v_keys_1084_, lean_object* v_vals_1085_, lean_object* v_heq_1086_, lean_object* v_i_1087_, lean_object* v_entries_1088_){
_start:
{
size_t v_depth_boxed_1089_; lean_object* v_res_1090_; 
v_depth_boxed_1089_ = lean_unbox_usize(v_depth_1083_);
lean_dec(v_depth_1083_);
v_res_1090_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__9(v_00_u03b2_1082_, v_depth_boxed_1089_, v_keys_1084_, v_vals_1085_, v_heq_1086_, v_i_1087_, v_entries_1088_);
lean_dec_ref(v_vals_1085_);
lean_dec_ref(v_keys_1084_);
return v_res_1090_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__8_spec__9(lean_object* v_00_u03b2_1091_, lean_object* v_x_1092_, lean_object* v_x_1093_, lean_object* v_x_1094_, lean_object* v_x_1095_){
_start:
{
lean_object* v___x_1096_; 
v___x_1096_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__8_spec__9___redArg(v_x_1092_, v_x_1093_, v_x_1094_, v_x_1095_);
return v___x_1096_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize(lean_object* v_mvarId_1099_, lean_object* v_givenNames_1100_, lean_object* v_recursorInfo_1101_, lean_object* v_reverted_1102_, lean_object* v_major_1103_, lean_object* v_indices_1104_, lean_object* v_baseSubst_1105_, lean_object* v_recursor_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_){
_start:
{
lean_object* v___x_1112_; 
lean_inc(v_mvarId_1099_);
v___x_1112_ = l_Lean_MVarId_getType(v_mvarId_1099_, v_a_1107_, v_a_1108_, v_a_1109_, v_a_1110_);
if (lean_obj_tag(v___x_1112_) == 0)
{
lean_object* v_a_1113_; lean_object* v___x_1114_; 
v_a_1113_ = lean_ctor_get(v___x_1112_, 0);
lean_inc(v_a_1113_);
lean_dec_ref_known(v___x_1112_, 1);
lean_inc(v_a_1110_);
lean_inc_ref(v_a_1109_);
lean_inc(v_a_1108_);
lean_inc_ref(v_a_1107_);
lean_inc_ref(v_recursor_1106_);
v___x_1114_ = lean_infer_type(v_recursor_1106_, v_a_1107_, v_a_1108_, v_a_1109_, v_a_1110_);
if (lean_obj_tag(v___x_1114_) == 0)
{
lean_object* v_a_1115_; lean_object* v_paramsPos_1116_; lean_object* v_produceMotive_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; uint8_t v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; 
v_a_1115_ = lean_ctor_get(v___x_1114_, 0);
lean_inc(v_a_1115_);
lean_dec_ref_known(v___x_1114_, 1);
v_paramsPos_1116_ = lean_ctor_get(v_recursorInfo_1101_, 5);
v_produceMotive_1117_ = lean_ctor_get(v_recursorInfo_1101_, 7);
v___x_1118_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTargetArity(v_a_1113_);
v___x_1119_ = l_List_lengthTR___redArg(v_produceMotive_1117_);
v___x_1120_ = l_List_lengthTR___redArg(v_paramsPos_1116_);
v___x_1121_ = lean_unsigned_to_nat(1u);
v___x_1122_ = lean_nat_add(v___x_1120_, v___x_1121_);
lean_dec(v___x_1120_);
v___x_1123_ = lean_unsigned_to_nat(0u);
v___x_1124_ = 0;
v___x_1125_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize___closed__0));
v___x_1126_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop(v_mvarId_1099_, v_givenNames_1100_, v_recursorInfo_1101_, v_reverted_1102_, v_major_1103_, v_indices_1104_, v_baseSubst_1105_, v___x_1118_, v___x_1119_, v___x_1122_, v___x_1123_, v_recursor_1106_, v_a_1115_, v___x_1124_, v___x_1125_, v_a_1107_, v_a_1108_, v_a_1109_, v_a_1110_);
lean_dec(v___x_1119_);
lean_dec(v___x_1118_);
return v___x_1126_;
}
else
{
lean_object* v_a_1127_; lean_object* v___x_1129_; uint8_t v_isShared_1130_; uint8_t v_isSharedCheck_1134_; 
lean_dec(v_a_1113_);
lean_dec_ref(v_recursor_1106_);
lean_dec(v_baseSubst_1105_);
lean_dec_ref(v_major_1103_);
lean_dec(v_mvarId_1099_);
v_a_1127_ = lean_ctor_get(v___x_1114_, 0);
v_isSharedCheck_1134_ = !lean_is_exclusive(v___x_1114_);
if (v_isSharedCheck_1134_ == 0)
{
v___x_1129_ = v___x_1114_;
v_isShared_1130_ = v_isSharedCheck_1134_;
goto v_resetjp_1128_;
}
else
{
lean_inc(v_a_1127_);
lean_dec(v___x_1114_);
v___x_1129_ = lean_box(0);
v_isShared_1130_ = v_isSharedCheck_1134_;
goto v_resetjp_1128_;
}
v_resetjp_1128_:
{
lean_object* v___x_1132_; 
if (v_isShared_1130_ == 0)
{
v___x_1132_ = v___x_1129_;
goto v_reusejp_1131_;
}
else
{
lean_object* v_reuseFailAlloc_1133_; 
v_reuseFailAlloc_1133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1133_, 0, v_a_1127_);
v___x_1132_ = v_reuseFailAlloc_1133_;
goto v_reusejp_1131_;
}
v_reusejp_1131_:
{
return v___x_1132_;
}
}
}
}
else
{
lean_object* v_a_1135_; lean_object* v___x_1137_; uint8_t v_isShared_1138_; uint8_t v_isSharedCheck_1142_; 
lean_dec_ref(v_recursor_1106_);
lean_dec(v_baseSubst_1105_);
lean_dec_ref(v_major_1103_);
lean_dec(v_mvarId_1099_);
v_a_1135_ = lean_ctor_get(v___x_1112_, 0);
v_isSharedCheck_1142_ = !lean_is_exclusive(v___x_1112_);
if (v_isSharedCheck_1142_ == 0)
{
v___x_1137_ = v___x_1112_;
v_isShared_1138_ = v_isSharedCheck_1142_;
goto v_resetjp_1136_;
}
else
{
lean_inc(v_a_1135_);
lean_dec(v___x_1112_);
v___x_1137_ = lean_box(0);
v_isShared_1138_ = v_isSharedCheck_1142_;
goto v_resetjp_1136_;
}
v_resetjp_1136_:
{
lean_object* v___x_1140_; 
if (v_isShared_1138_ == 0)
{
v___x_1140_ = v___x_1137_;
goto v_reusejp_1139_;
}
else
{
lean_object* v_reuseFailAlloc_1141_; 
v_reuseFailAlloc_1141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1141_, 0, v_a_1135_);
v___x_1140_ = v_reuseFailAlloc_1141_;
goto v_reusejp_1139_;
}
v_reusejp_1139_:
{
return v___x_1140_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize___boxed(lean_object* v_mvarId_1143_, lean_object* v_givenNames_1144_, lean_object* v_recursorInfo_1145_, lean_object* v_reverted_1146_, lean_object* v_major_1147_, lean_object* v_indices_1148_, lean_object* v_baseSubst_1149_, lean_object* v_recursor_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_){
_start:
{
lean_object* v_res_1156_; 
v_res_1156_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize(v_mvarId_1143_, v_givenNames_1144_, v_recursorInfo_1145_, v_reverted_1146_, v_major_1147_, v_indices_1148_, v_baseSubst_1149_, v_recursor_1150_, v_a_1151_, v_a_1152_, v_a_1153_, v_a_1154_);
lean_dec(v_a_1154_);
lean_dec_ref(v_a_1153_);
lean_dec(v_a_1152_);
lean_dec_ref(v_a_1151_);
lean_dec_ref(v_indices_1148_);
lean_dec_ref(v_reverted_1146_);
lean_dec_ref(v_recursorInfo_1145_);
lean_dec_ref(v_givenNames_1144_);
return v_res_1156_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg___closed__1(void){
_start:
{
lean_object* v___x_1158_; lean_object* v___x_1159_; 
v___x_1158_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg___closed__0));
v___x_1159_ = l_Lean_stringToMessageData(v___x_1158_);
return v___x_1159_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg(lean_object* v_tacticName_1160_, lean_object* v_mvarId_1161_, lean_object* v_majorType_1162_, lean_object* v_a_1163_, lean_object* v_a_1164_, lean_object* v_a_1165_, lean_object* v_a_1166_){
_start:
{
lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; 
v___x_1168_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg___closed__1, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg___closed__1);
v___x_1169_ = l_Lean_indentExpr(v_majorType_1162_);
v___x_1170_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1170_, 0, v___x_1168_);
lean_ctor_set(v___x_1170_, 1, v___x_1169_);
v___x_1171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1171_, 0, v___x_1170_);
v___x_1172_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1160_, v_mvarId_1161_, v___x_1171_, v_a_1163_, v_a_1164_, v_a_1165_, v_a_1166_);
return v___x_1172_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg___boxed(lean_object* v_tacticName_1173_, lean_object* v_mvarId_1174_, lean_object* v_majorType_1175_, lean_object* v_a_1176_, lean_object* v_a_1177_, lean_object* v_a_1178_, lean_object* v_a_1179_, lean_object* v_a_1180_){
_start:
{
lean_object* v_res_1181_; 
v_res_1181_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg(v_tacticName_1173_, v_mvarId_1174_, v_majorType_1175_, v_a_1176_, v_a_1177_, v_a_1178_, v_a_1179_);
lean_dec(v_a_1179_);
lean_dec_ref(v_a_1178_);
lean_dec(v_a_1177_);
lean_dec_ref(v_a_1176_);
return v_res_1181_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType(lean_object* v_00_u03b1_1182_, lean_object* v_tacticName_1183_, lean_object* v_mvarId_1184_, lean_object* v_majorType_1185_, lean_object* v_a_1186_, lean_object* v_a_1187_, lean_object* v_a_1188_, lean_object* v_a_1189_){
_start:
{
lean_object* v___x_1191_; 
v___x_1191_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg(v_tacticName_1183_, v_mvarId_1184_, v_majorType_1185_, v_a_1186_, v_a_1187_, v_a_1188_, v_a_1189_);
return v___x_1191_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___boxed(lean_object* v_00_u03b1_1192_, lean_object* v_tacticName_1193_, lean_object* v_mvarId_1194_, lean_object* v_majorType_1195_, lean_object* v_a_1196_, lean_object* v_a_1197_, lean_object* v_a_1198_, lean_object* v_a_1199_, lean_object* v_a_1200_){
_start:
{
lean_object* v_res_1201_; 
v_res_1201_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType(v_00_u03b1_1192_, v_tacticName_1193_, v_mvarId_1194_, v_majorType_1195_, v_a_1196_, v_a_1197_, v_a_1198_, v_a_1199_);
lean_dec(v_a_1199_);
lean_dec_ref(v_a_1198_);
lean_dec(v_a_1197_);
lean_dec_ref(v_a_1196_);
return v_res_1201_;
}
}
LEAN_EXPORT uint8_t l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___lam__0(lean_object* v_fvarId_1202_, lean_object* v_x_1203_){
_start:
{
uint8_t v___x_1204_; 
v___x_1204_ = l_Lean_instBEqFVarId_beq(v_fvarId_1202_, v_x_1203_);
return v___x_1204_;
}
}
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___lam__0___boxed(lean_object* v_fvarId_1205_, lean_object* v_x_1206_){
_start:
{
uint8_t v_res_1207_; lean_object* v_r_1208_; 
v_res_1207_ = l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___lam__0(v_fvarId_1205_, v_x_1206_);
lean_dec(v_x_1206_);
lean_dec(v_fvarId_1205_);
v_r_1208_ = lean_box(v_res_1207_);
return v_r_1208_;
}
}
LEAN_EXPORT uint8_t l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___lam__1(lean_object* v_x_1209_){
_start:
{
uint8_t v___x_1210_; 
v___x_1210_ = 0;
return v___x_1210_;
}
}
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___lam__1___boxed(lean_object* v_x_1211_){
_start:
{
uint8_t v_res_1212_; lean_object* v_r_1213_; 
v_res_1212_ = l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___lam__1(v_x_1211_);
lean_dec(v_x_1211_);
v_r_1213_ = lean_box(v_res_1212_);
return v_r_1213_;
}
}
static lean_object* _init_l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; 
v___x_1215_ = lean_box(0);
v___x_1216_ = lean_unsigned_to_nat(16u);
v___x_1217_ = lean_mk_array(v___x_1216_, v___x_1215_);
return v___x_1217_;
}
}
static lean_object* _init_l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; 
v___x_1218_ = lean_obj_once(&l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__1, &l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__1_once, _init_l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__1);
v___x_1219_ = lean_unsigned_to_nat(0u);
v___x_1220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1220_, 0, v___x_1219_);
lean_ctor_set(v___x_1220_, 1, v___x_1218_);
return v___x_1220_;
}
}
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg(lean_object* v_localDecl_1221_, lean_object* v_fvarId_1222_, uint8_t v_generalizeNondepLet_1223_, lean_object* v___y_1224_){
_start:
{
uint8_t v_fst_1227_; lean_object* v_snd_1228_; lean_object* v___y_1247_; lean_object* v___f_1251_; lean_object* v___f_1252_; 
v___f_1251_ = lean_alloc_closure((void*)(l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1251_, 0, v_fvarId_1222_);
v___f_1252_ = ((lean_object*)(l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__0));
if (lean_obj_tag(v_localDecl_1221_) == 0)
{
lean_object* v_type_1253_; lean_object* v___x_1254_; uint8_t v_fst_1256_; lean_object* v_mctx_1257_; lean_object* v___y_1275_; lean_object* v_mctx_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; uint8_t v___x_1283_; 
v_type_1253_ = lean_ctor_get(v_localDecl_1221_, 3);
lean_inc_ref(v_type_1253_);
lean_dec_ref_known(v_localDecl_1221_, 4);
v___x_1254_ = lean_st_ref_get(v___y_1224_);
v_mctx_1280_ = lean_ctor_get(v___x_1254_, 0);
lean_inc_ref_n(v_mctx_1280_, 2);
lean_dec(v___x_1254_);
v___x_1281_ = lean_obj_once(&l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__2, &l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__2_once, _init_l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__2);
v___x_1282_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1282_, 0, v___x_1281_);
lean_ctor_set(v___x_1282_, 1, v_mctx_1280_);
v___x_1283_ = l_Lean_Expr_hasFVar(v_type_1253_);
if (v___x_1283_ == 0)
{
uint8_t v___x_1284_; 
v___x_1284_ = l_Lean_Expr_hasMVar(v_type_1253_);
if (v___x_1284_ == 0)
{
lean_dec_ref_known(v___x_1282_, 2);
lean_dec_ref(v_type_1253_);
lean_dec_ref(v___f_1251_);
v_fst_1256_ = v___x_1284_;
v_mctx_1257_ = v_mctx_1280_;
goto v___jp_1255_;
}
else
{
lean_object* v___x_1285_; 
lean_dec_ref(v_mctx_1280_);
v___x_1285_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1251_, v___f_1252_, v_type_1253_, v___x_1282_);
v___y_1275_ = v___x_1285_;
goto v___jp_1274_;
}
}
else
{
lean_object* v___x_1286_; 
lean_dec_ref(v_mctx_1280_);
v___x_1286_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1251_, v___f_1252_, v_type_1253_, v___x_1282_);
v___y_1275_ = v___x_1286_;
goto v___jp_1274_;
}
v___jp_1255_:
{
lean_object* v___x_1258_; lean_object* v_cache_1259_; lean_object* v_zetaDeltaFVarIds_1260_; lean_object* v_postponed_1261_; lean_object* v_diag_1262_; lean_object* v___x_1264_; uint8_t v_isShared_1265_; uint8_t v_isSharedCheck_1272_; 
v___x_1258_ = lean_st_ref_take(v___y_1224_);
v_cache_1259_ = lean_ctor_get(v___x_1258_, 1);
v_zetaDeltaFVarIds_1260_ = lean_ctor_get(v___x_1258_, 2);
v_postponed_1261_ = lean_ctor_get(v___x_1258_, 3);
v_diag_1262_ = lean_ctor_get(v___x_1258_, 4);
v_isSharedCheck_1272_ = !lean_is_exclusive(v___x_1258_);
if (v_isSharedCheck_1272_ == 0)
{
lean_object* v_unused_1273_; 
v_unused_1273_ = lean_ctor_get(v___x_1258_, 0);
lean_dec(v_unused_1273_);
v___x_1264_ = v___x_1258_;
v_isShared_1265_ = v_isSharedCheck_1272_;
goto v_resetjp_1263_;
}
else
{
lean_inc(v_diag_1262_);
lean_inc(v_postponed_1261_);
lean_inc(v_zetaDeltaFVarIds_1260_);
lean_inc(v_cache_1259_);
lean_dec(v___x_1258_);
v___x_1264_ = lean_box(0);
v_isShared_1265_ = v_isSharedCheck_1272_;
goto v_resetjp_1263_;
}
v_resetjp_1263_:
{
lean_object* v___x_1267_; 
if (v_isShared_1265_ == 0)
{
lean_ctor_set(v___x_1264_, 0, v_mctx_1257_);
v___x_1267_ = v___x_1264_;
goto v_reusejp_1266_;
}
else
{
lean_object* v_reuseFailAlloc_1271_; 
v_reuseFailAlloc_1271_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1271_, 0, v_mctx_1257_);
lean_ctor_set(v_reuseFailAlloc_1271_, 1, v_cache_1259_);
lean_ctor_set(v_reuseFailAlloc_1271_, 2, v_zetaDeltaFVarIds_1260_);
lean_ctor_set(v_reuseFailAlloc_1271_, 3, v_postponed_1261_);
lean_ctor_set(v_reuseFailAlloc_1271_, 4, v_diag_1262_);
v___x_1267_ = v_reuseFailAlloc_1271_;
goto v_reusejp_1266_;
}
v_reusejp_1266_:
{
lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; 
v___x_1268_ = lean_st_ref_put(v___y_1224_, v___x_1267_);
v___x_1269_ = lean_box(v_fst_1256_);
v___x_1270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1270_, 0, v___x_1269_);
return v___x_1270_;
}
}
}
v___jp_1274_:
{
lean_object* v_snd_1276_; lean_object* v_fst_1277_; lean_object* v_mctx_1278_; uint8_t v___x_1279_; 
v_snd_1276_ = lean_ctor_get(v___y_1275_, 1);
lean_inc(v_snd_1276_);
v_fst_1277_ = lean_ctor_get(v___y_1275_, 0);
lean_inc(v_fst_1277_);
lean_dec_ref(v___y_1275_);
v_mctx_1278_ = lean_ctor_get(v_snd_1276_, 1);
lean_inc_ref(v_mctx_1278_);
lean_dec(v_snd_1276_);
v___x_1279_ = lean_unbox(v_fst_1277_);
lean_dec(v_fst_1277_);
v_fst_1256_ = v___x_1279_;
v_mctx_1257_ = v_mctx_1278_;
goto v___jp_1255_;
}
}
else
{
lean_object* v_type_1287_; lean_object* v_value_1288_; uint8_t v_nondep_1289_; uint8_t v_fst_1291_; lean_object* v_snd_1292_; lean_object* v___y_1298_; 
v_type_1287_ = lean_ctor_get(v_localDecl_1221_, 3);
lean_inc_ref(v_type_1287_);
v_value_1288_ = lean_ctor_get(v_localDecl_1221_, 4);
lean_inc_ref(v_value_1288_);
v_nondep_1289_ = lean_ctor_get_uint8(v_localDecl_1221_, sizeof(void*)*5);
lean_dec_ref_known(v_localDecl_1221_, 5);
if (v_generalizeNondepLet_1223_ == 0)
{
goto v___jp_1302_;
}
else
{
if (v_nondep_1289_ == 0)
{
goto v___jp_1302_;
}
else
{
lean_object* v___x_1311_; uint8_t v_fst_1313_; lean_object* v_mctx_1314_; lean_object* v___y_1332_; lean_object* v_mctx_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; uint8_t v___x_1340_; 
lean_dec_ref(v_value_1288_);
v___x_1311_ = lean_st_ref_get(v___y_1224_);
v_mctx_1337_ = lean_ctor_get(v___x_1311_, 0);
lean_inc_ref_n(v_mctx_1337_, 2);
lean_dec(v___x_1311_);
v___x_1338_ = lean_obj_once(&l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__2, &l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__2_once, _init_l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__2);
v___x_1339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1339_, 0, v___x_1338_);
lean_ctor_set(v___x_1339_, 1, v_mctx_1337_);
v___x_1340_ = l_Lean_Expr_hasFVar(v_type_1287_);
if (v___x_1340_ == 0)
{
uint8_t v___x_1341_; 
v___x_1341_ = l_Lean_Expr_hasMVar(v_type_1287_);
if (v___x_1341_ == 0)
{
lean_dec_ref_known(v___x_1339_, 2);
lean_dec_ref(v_type_1287_);
lean_dec_ref(v___f_1251_);
v_fst_1313_ = v___x_1341_;
v_mctx_1314_ = v_mctx_1337_;
goto v___jp_1312_;
}
else
{
lean_object* v___x_1342_; 
lean_dec_ref(v_mctx_1337_);
v___x_1342_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1251_, v___f_1252_, v_type_1287_, v___x_1339_);
v___y_1332_ = v___x_1342_;
goto v___jp_1331_;
}
}
else
{
lean_object* v___x_1343_; 
lean_dec_ref(v_mctx_1337_);
v___x_1343_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1251_, v___f_1252_, v_type_1287_, v___x_1339_);
v___y_1332_ = v___x_1343_;
goto v___jp_1331_;
}
v___jp_1312_:
{
lean_object* v___x_1315_; lean_object* v_cache_1316_; lean_object* v_zetaDeltaFVarIds_1317_; lean_object* v_postponed_1318_; lean_object* v_diag_1319_; lean_object* v___x_1321_; uint8_t v_isShared_1322_; uint8_t v_isSharedCheck_1329_; 
v___x_1315_ = lean_st_ref_take(v___y_1224_);
v_cache_1316_ = lean_ctor_get(v___x_1315_, 1);
v_zetaDeltaFVarIds_1317_ = lean_ctor_get(v___x_1315_, 2);
v_postponed_1318_ = lean_ctor_get(v___x_1315_, 3);
v_diag_1319_ = lean_ctor_get(v___x_1315_, 4);
v_isSharedCheck_1329_ = !lean_is_exclusive(v___x_1315_);
if (v_isSharedCheck_1329_ == 0)
{
lean_object* v_unused_1330_; 
v_unused_1330_ = lean_ctor_get(v___x_1315_, 0);
lean_dec(v_unused_1330_);
v___x_1321_ = v___x_1315_;
v_isShared_1322_ = v_isSharedCheck_1329_;
goto v_resetjp_1320_;
}
else
{
lean_inc(v_diag_1319_);
lean_inc(v_postponed_1318_);
lean_inc(v_zetaDeltaFVarIds_1317_);
lean_inc(v_cache_1316_);
lean_dec(v___x_1315_);
v___x_1321_ = lean_box(0);
v_isShared_1322_ = v_isSharedCheck_1329_;
goto v_resetjp_1320_;
}
v_resetjp_1320_:
{
lean_object* v___x_1324_; 
if (v_isShared_1322_ == 0)
{
lean_ctor_set(v___x_1321_, 0, v_mctx_1314_);
v___x_1324_ = v___x_1321_;
goto v_reusejp_1323_;
}
else
{
lean_object* v_reuseFailAlloc_1328_; 
v_reuseFailAlloc_1328_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1328_, 0, v_mctx_1314_);
lean_ctor_set(v_reuseFailAlloc_1328_, 1, v_cache_1316_);
lean_ctor_set(v_reuseFailAlloc_1328_, 2, v_zetaDeltaFVarIds_1317_);
lean_ctor_set(v_reuseFailAlloc_1328_, 3, v_postponed_1318_);
lean_ctor_set(v_reuseFailAlloc_1328_, 4, v_diag_1319_);
v___x_1324_ = v_reuseFailAlloc_1328_;
goto v_reusejp_1323_;
}
v_reusejp_1323_:
{
lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; 
v___x_1325_ = lean_st_ref_put(v___y_1224_, v___x_1324_);
v___x_1326_ = lean_box(v_fst_1313_);
v___x_1327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1327_, 0, v___x_1326_);
return v___x_1327_;
}
}
}
v___jp_1331_:
{
lean_object* v_snd_1333_; lean_object* v_fst_1334_; lean_object* v_mctx_1335_; uint8_t v___x_1336_; 
v_snd_1333_ = lean_ctor_get(v___y_1332_, 1);
lean_inc(v_snd_1333_);
v_fst_1334_ = lean_ctor_get(v___y_1332_, 0);
lean_inc(v_fst_1334_);
lean_dec_ref(v___y_1332_);
v_mctx_1335_ = lean_ctor_get(v_snd_1333_, 1);
lean_inc_ref(v_mctx_1335_);
lean_dec(v_snd_1333_);
v___x_1336_ = lean_unbox(v_fst_1334_);
lean_dec(v_fst_1334_);
v_fst_1313_ = v___x_1336_;
v_mctx_1314_ = v_mctx_1335_;
goto v___jp_1312_;
}
}
}
v___jp_1290_:
{
if (v_fst_1291_ == 0)
{
uint8_t v___x_1293_; 
v___x_1293_ = l_Lean_Expr_hasFVar(v_value_1288_);
if (v___x_1293_ == 0)
{
uint8_t v___x_1294_; 
v___x_1294_ = l_Lean_Expr_hasMVar(v_value_1288_);
if (v___x_1294_ == 0)
{
lean_dec_ref(v_value_1288_);
lean_dec_ref(v___f_1251_);
v_fst_1227_ = v___x_1294_;
v_snd_1228_ = v_snd_1292_;
goto v___jp_1226_;
}
else
{
lean_object* v___x_1295_; 
v___x_1295_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1251_, v___f_1252_, v_value_1288_, v_snd_1292_);
v___y_1247_ = v___x_1295_;
goto v___jp_1246_;
}
}
else
{
lean_object* v___x_1296_; 
v___x_1296_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1251_, v___f_1252_, v_value_1288_, v_snd_1292_);
v___y_1247_ = v___x_1296_;
goto v___jp_1246_;
}
}
else
{
lean_dec_ref(v_value_1288_);
lean_dec_ref(v___f_1251_);
v_fst_1227_ = v_fst_1291_;
v_snd_1228_ = v_snd_1292_;
goto v___jp_1226_;
}
}
v___jp_1297_:
{
lean_object* v_fst_1299_; lean_object* v_snd_1300_; uint8_t v___x_1301_; 
v_fst_1299_ = lean_ctor_get(v___y_1298_, 0);
lean_inc(v_fst_1299_);
v_snd_1300_ = lean_ctor_get(v___y_1298_, 1);
lean_inc(v_snd_1300_);
lean_dec_ref(v___y_1298_);
v___x_1301_ = lean_unbox(v_fst_1299_);
lean_dec(v_fst_1299_);
v_fst_1291_ = v___x_1301_;
v_snd_1292_ = v_snd_1300_;
goto v___jp_1290_;
}
v___jp_1302_:
{
lean_object* v___x_1303_; lean_object* v_mctx_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; uint8_t v___x_1307_; 
v___x_1303_ = lean_st_ref_get(v___y_1224_);
v_mctx_1304_ = lean_ctor_get(v___x_1303_, 0);
lean_inc_ref(v_mctx_1304_);
lean_dec(v___x_1303_);
v___x_1305_ = lean_obj_once(&l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__2, &l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__2_once, _init_l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__2);
v___x_1306_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1306_, 0, v___x_1305_);
lean_ctor_set(v___x_1306_, 1, v_mctx_1304_);
v___x_1307_ = l_Lean_Expr_hasFVar(v_type_1287_);
if (v___x_1307_ == 0)
{
uint8_t v___x_1308_; 
v___x_1308_ = l_Lean_Expr_hasMVar(v_type_1287_);
if (v___x_1308_ == 0)
{
lean_dec_ref(v_type_1287_);
v_fst_1291_ = v___x_1308_;
v_snd_1292_ = v___x_1306_;
goto v___jp_1290_;
}
else
{
lean_object* v___x_1309_; 
lean_inc_ref(v___f_1251_);
v___x_1309_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1251_, v___f_1252_, v_type_1287_, v___x_1306_);
v___y_1298_ = v___x_1309_;
goto v___jp_1297_;
}
}
else
{
lean_object* v___x_1310_; 
lean_inc_ref(v___f_1251_);
v___x_1310_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1251_, v___f_1252_, v_type_1287_, v___x_1306_);
v___y_1298_ = v___x_1310_;
goto v___jp_1297_;
}
}
}
v___jp_1226_:
{
lean_object* v_mctx_1229_; lean_object* v___x_1230_; lean_object* v_cache_1231_; lean_object* v_zetaDeltaFVarIds_1232_; lean_object* v_postponed_1233_; lean_object* v_diag_1234_; lean_object* v___x_1236_; uint8_t v_isShared_1237_; uint8_t v_isSharedCheck_1244_; 
v_mctx_1229_ = lean_ctor_get(v_snd_1228_, 1);
lean_inc_ref(v_mctx_1229_);
lean_dec_ref(v_snd_1228_);
v___x_1230_ = lean_st_ref_take(v___y_1224_);
v_cache_1231_ = lean_ctor_get(v___x_1230_, 1);
v_zetaDeltaFVarIds_1232_ = lean_ctor_get(v___x_1230_, 2);
v_postponed_1233_ = lean_ctor_get(v___x_1230_, 3);
v_diag_1234_ = lean_ctor_get(v___x_1230_, 4);
v_isSharedCheck_1244_ = !lean_is_exclusive(v___x_1230_);
if (v_isSharedCheck_1244_ == 0)
{
lean_object* v_unused_1245_; 
v_unused_1245_ = lean_ctor_get(v___x_1230_, 0);
lean_dec(v_unused_1245_);
v___x_1236_ = v___x_1230_;
v_isShared_1237_ = v_isSharedCheck_1244_;
goto v_resetjp_1235_;
}
else
{
lean_inc(v_diag_1234_);
lean_inc(v_postponed_1233_);
lean_inc(v_zetaDeltaFVarIds_1232_);
lean_inc(v_cache_1231_);
lean_dec(v___x_1230_);
v___x_1236_ = lean_box(0);
v_isShared_1237_ = v_isSharedCheck_1244_;
goto v_resetjp_1235_;
}
v_resetjp_1235_:
{
lean_object* v___x_1239_; 
if (v_isShared_1237_ == 0)
{
lean_ctor_set(v___x_1236_, 0, v_mctx_1229_);
v___x_1239_ = v___x_1236_;
goto v_reusejp_1238_;
}
else
{
lean_object* v_reuseFailAlloc_1243_; 
v_reuseFailAlloc_1243_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1243_, 0, v_mctx_1229_);
lean_ctor_set(v_reuseFailAlloc_1243_, 1, v_cache_1231_);
lean_ctor_set(v_reuseFailAlloc_1243_, 2, v_zetaDeltaFVarIds_1232_);
lean_ctor_set(v_reuseFailAlloc_1243_, 3, v_postponed_1233_);
lean_ctor_set(v_reuseFailAlloc_1243_, 4, v_diag_1234_);
v___x_1239_ = v_reuseFailAlloc_1243_;
goto v_reusejp_1238_;
}
v_reusejp_1238_:
{
lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; 
v___x_1240_ = lean_st_ref_put(v___y_1224_, v___x_1239_);
v___x_1241_ = lean_box(v_fst_1227_);
v___x_1242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1242_, 0, v___x_1241_);
return v___x_1242_;
}
}
}
v___jp_1246_:
{
lean_object* v_fst_1248_; lean_object* v_snd_1249_; uint8_t v___x_1250_; 
v_fst_1248_ = lean_ctor_get(v___y_1247_, 0);
lean_inc(v_fst_1248_);
v_snd_1249_ = lean_ctor_get(v___y_1247_, 1);
lean_inc(v_snd_1249_);
lean_dec_ref(v___y_1247_);
v___x_1250_ = lean_unbox(v_fst_1248_);
lean_dec(v_fst_1248_);
v_fst_1227_ = v___x_1250_;
v_snd_1228_ = v_snd_1249_;
goto v___jp_1226_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___boxed(lean_object* v_localDecl_1344_, lean_object* v_fvarId_1345_, lean_object* v_generalizeNondepLet_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_){
_start:
{
uint8_t v_generalizeNondepLet_boxed_1349_; lean_object* v_res_1350_; 
v_generalizeNondepLet_boxed_1349_ = lean_unbox(v_generalizeNondepLet_1346_);
v_res_1350_ = l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg(v_localDecl_1344_, v_fvarId_1345_, v_generalizeNondepLet_boxed_1349_, v___y_1347_);
lean_dec(v___y_1347_);
return v_res_1350_;
}
}
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0(lean_object* v_localDecl_1351_, lean_object* v_fvarId_1352_, uint8_t v_generalizeNondepLet_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_){
_start:
{
lean_object* v___x_1359_; 
v___x_1359_ = l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg(v_localDecl_1351_, v_fvarId_1352_, v_generalizeNondepLet_1353_, v___y_1355_);
return v___x_1359_;
}
}
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___boxed(lean_object* v_localDecl_1360_, lean_object* v_fvarId_1361_, lean_object* v_generalizeNondepLet_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_){
_start:
{
uint8_t v_generalizeNondepLet_boxed_1368_; lean_object* v_res_1369_; 
v_generalizeNondepLet_boxed_1368_ = lean_unbox(v_generalizeNondepLet_1362_);
v_res_1369_ = l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0(v_localDecl_1360_, v_fvarId_1361_, v_generalizeNondepLet_boxed_1368_, v___y_1363_, v___y_1364_, v___y_1365_, v___y_1366_);
lean_dec(v___y_1366_);
lean_dec_ref(v___y_1365_);
lean_dec(v___y_1364_);
lean_dec_ref(v___y_1363_);
return v_res_1369_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2___redArg(lean_object* v_e_1370_, lean_object* v_fvarId_1371_, lean_object* v___y_1372_){
_start:
{
lean_object* v___x_1374_; uint8_t v_fst_1376_; lean_object* v_mctx_1377_; lean_object* v___y_1395_; lean_object* v_mctx_1400_; lean_object* v___f_1401_; lean_object* v___f_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; uint8_t v___x_1405_; 
v___x_1374_ = lean_st_ref_get(v___y_1372_);
v_mctx_1400_ = lean_ctor_get(v___x_1374_, 0);
lean_inc_ref_n(v_mctx_1400_, 2);
lean_dec(v___x_1374_);
v___f_1401_ = ((lean_object*)(l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__0));
v___f_1402_ = lean_alloc_closure((void*)(l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1402_, 0, v_fvarId_1371_);
v___x_1403_ = lean_obj_once(&l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__2, &l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__2_once, _init_l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__2);
v___x_1404_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1404_, 0, v___x_1403_);
lean_ctor_set(v___x_1404_, 1, v_mctx_1400_);
v___x_1405_ = l_Lean_Expr_hasFVar(v_e_1370_);
if (v___x_1405_ == 0)
{
uint8_t v___x_1406_; 
v___x_1406_ = l_Lean_Expr_hasMVar(v_e_1370_);
if (v___x_1406_ == 0)
{
lean_dec_ref_known(v___x_1404_, 2);
lean_dec_ref(v___f_1402_);
lean_dec_ref(v_e_1370_);
v_fst_1376_ = v___x_1406_;
v_mctx_1377_ = v_mctx_1400_;
goto v___jp_1375_;
}
else
{
lean_object* v___x_1407_; 
lean_dec_ref(v_mctx_1400_);
v___x_1407_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1402_, v___f_1401_, v_e_1370_, v___x_1404_);
v___y_1395_ = v___x_1407_;
goto v___jp_1394_;
}
}
else
{
lean_object* v___x_1408_; 
lean_dec_ref(v_mctx_1400_);
v___x_1408_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1402_, v___f_1401_, v_e_1370_, v___x_1404_);
v___y_1395_ = v___x_1408_;
goto v___jp_1394_;
}
v___jp_1375_:
{
lean_object* v___x_1378_; lean_object* v_cache_1379_; lean_object* v_zetaDeltaFVarIds_1380_; lean_object* v_postponed_1381_; lean_object* v_diag_1382_; lean_object* v___x_1384_; uint8_t v_isShared_1385_; uint8_t v_isSharedCheck_1392_; 
v___x_1378_ = lean_st_ref_take(v___y_1372_);
v_cache_1379_ = lean_ctor_get(v___x_1378_, 1);
v_zetaDeltaFVarIds_1380_ = lean_ctor_get(v___x_1378_, 2);
v_postponed_1381_ = lean_ctor_get(v___x_1378_, 3);
v_diag_1382_ = lean_ctor_get(v___x_1378_, 4);
v_isSharedCheck_1392_ = !lean_is_exclusive(v___x_1378_);
if (v_isSharedCheck_1392_ == 0)
{
lean_object* v_unused_1393_; 
v_unused_1393_ = lean_ctor_get(v___x_1378_, 0);
lean_dec(v_unused_1393_);
v___x_1384_ = v___x_1378_;
v_isShared_1385_ = v_isSharedCheck_1392_;
goto v_resetjp_1383_;
}
else
{
lean_inc(v_diag_1382_);
lean_inc(v_postponed_1381_);
lean_inc(v_zetaDeltaFVarIds_1380_);
lean_inc(v_cache_1379_);
lean_dec(v___x_1378_);
v___x_1384_ = lean_box(0);
v_isShared_1385_ = v_isSharedCheck_1392_;
goto v_resetjp_1383_;
}
v_resetjp_1383_:
{
lean_object* v___x_1387_; 
if (v_isShared_1385_ == 0)
{
lean_ctor_set(v___x_1384_, 0, v_mctx_1377_);
v___x_1387_ = v___x_1384_;
goto v_reusejp_1386_;
}
else
{
lean_object* v_reuseFailAlloc_1391_; 
v_reuseFailAlloc_1391_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1391_, 0, v_mctx_1377_);
lean_ctor_set(v_reuseFailAlloc_1391_, 1, v_cache_1379_);
lean_ctor_set(v_reuseFailAlloc_1391_, 2, v_zetaDeltaFVarIds_1380_);
lean_ctor_set(v_reuseFailAlloc_1391_, 3, v_postponed_1381_);
lean_ctor_set(v_reuseFailAlloc_1391_, 4, v_diag_1382_);
v___x_1387_ = v_reuseFailAlloc_1391_;
goto v_reusejp_1386_;
}
v_reusejp_1386_:
{
lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; 
v___x_1388_ = lean_st_ref_put(v___y_1372_, v___x_1387_);
v___x_1389_ = lean_box(v_fst_1376_);
v___x_1390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1390_, 0, v___x_1389_);
return v___x_1390_;
}
}
}
v___jp_1394_:
{
lean_object* v_snd_1396_; lean_object* v_fst_1397_; lean_object* v_mctx_1398_; uint8_t v___x_1399_; 
v_snd_1396_ = lean_ctor_get(v___y_1395_, 1);
lean_inc(v_snd_1396_);
v_fst_1397_ = lean_ctor_get(v___y_1395_, 0);
lean_inc(v_fst_1397_);
lean_dec_ref(v___y_1395_);
v_mctx_1398_ = lean_ctor_get(v_snd_1396_, 1);
lean_inc_ref(v_mctx_1398_);
lean_dec(v_snd_1396_);
v___x_1399_ = lean_unbox(v_fst_1397_);
lean_dec(v_fst_1397_);
v_fst_1376_ = v___x_1399_;
v_mctx_1377_ = v_mctx_1398_;
goto v___jp_1375_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2___redArg___boxed(lean_object* v_e_1409_, lean_object* v_fvarId_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_){
_start:
{
lean_object* v_res_1413_; 
v_res_1413_ = l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2___redArg(v_e_1409_, v_fvarId_1410_, v___y_1411_);
lean_dec(v___y_1411_);
return v_res_1413_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2(lean_object* v_e_1414_, lean_object* v_fvarId_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_){
_start:
{
lean_object* v___x_1421_; 
v___x_1421_ = l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2___redArg(v_e_1414_, v_fvarId_1415_, v___y_1417_);
return v___x_1421_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2___boxed(lean_object* v_e_1422_, lean_object* v_fvarId_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_){
_start:
{
lean_object* v_res_1429_; 
v_res_1429_ = l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2(v_e_1422_, v_fvarId_1423_, v___y_1424_, v___y_1425_, v___y_1426_, v___y_1427_);
lean_dec(v___y_1427_);
lean_dec_ref(v___y_1426_);
lean_dec(v___y_1425_);
lean_dec_ref(v___y_1424_);
return v_res_1429_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_Meta_getMajorTypeIndices_spec__1(lean_object* v_a_1430_, lean_object* v_x_1431_){
_start:
{
if (lean_obj_tag(v_x_1431_) == 0)
{
uint8_t v___x_1432_; 
v___x_1432_ = 0;
return v___x_1432_;
}
else
{
lean_object* v_head_1433_; lean_object* v_tail_1434_; uint8_t v___x_1435_; 
v_head_1433_ = lean_ctor_get(v_x_1431_, 0);
v_tail_1434_ = lean_ctor_get(v_x_1431_, 1);
v___x_1435_ = lean_nat_dec_eq(v_a_1430_, v_head_1433_);
if (v___x_1435_ == 0)
{
v_x_1431_ = v_tail_1434_;
goto _start;
}
else
{
return v___x_1435_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_Meta_getMajorTypeIndices_spec__1___boxed(lean_object* v_a_1437_, lean_object* v_x_1438_){
_start:
{
uint8_t v_res_1439_; lean_object* v_r_1440_; 
v_res_1439_ = l_List_elem___at___00Lean_Meta_getMajorTypeIndices_spec__1(v_a_1437_, v_x_1438_);
lean_dec(v_x_1438_);
lean_dec(v_a_1437_);
v_r_1440_ = lean_box(v_res_1439_);
return v_r_1440_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_1442_; lean_object* v___x_1443_; 
v___x_1442_ = ((lean_object*)(l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__0));
v___x_1443_ = l_Lean_stringToMessageData(v___x_1442_);
return v___x_1443_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_1445_; lean_object* v___x_1446_; 
v___x_1445_ = ((lean_object*)(l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__2));
v___x_1446_ = l_Lean_stringToMessageData(v___x_1445_);
return v___x_1446_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__5(void){
_start:
{
lean_object* v___x_1448_; lean_object* v___x_1449_; 
v___x_1448_ = ((lean_object*)(l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__4));
v___x_1449_ = l_Lean_stringToMessageData(v___x_1448_);
return v___x_1449_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__7(void){
_start:
{
lean_object* v___x_1451_; lean_object* v___x_1452_; 
v___x_1451_ = ((lean_object*)(l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__6));
v___x_1452_ = l_Lean_stringToMessageData(v___x_1451_);
return v___x_1452_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg(lean_object* v_majorTypeArgs_1453_, lean_object* v_idx_1454_, lean_object* v_tacticName_1455_, lean_object* v_mvarId_1456_, lean_object* v_idxPos_1457_, lean_object* v_recursorInfo_1458_, lean_object* v_majorType_1459_, lean_object* v_n_1460_, lean_object* v_i_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_){
_start:
{
lean_object* v_zero_1467_; uint8_t v_isZero_1468_; 
v_zero_1467_ = lean_unsigned_to_nat(0u);
v_isZero_1468_ = lean_nat_dec_eq(v_i_1461_, v_zero_1467_);
if (v_isZero_1468_ == 1)
{
lean_object* v___x_1469_; lean_object* v___x_1470_; 
lean_dec(v_i_1461_);
lean_dec_ref(v_majorType_1459_);
lean_dec(v_mvarId_1456_);
lean_dec(v_tacticName_1455_);
lean_dec_ref(v_idx_1454_);
v___x_1469_ = lean_box(0);
v___x_1470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1470_, 0, v___x_1469_);
return v___x_1470_;
}
else
{
lean_object* v_one_1471_; lean_object* v_n_1472_; lean_object* v___y_1474_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v_arg_1478_; lean_object* v___y_1480_; lean_object* v___y_1481_; lean_object* v___y_1482_; lean_object* v___y_1483_; uint8_t v___y_1484_; lean_object* v___y_1523_; lean_object* v___y_1524_; lean_object* v___y_1525_; lean_object* v___y_1526_; lean_object* v___y_1531_; lean_object* v___y_1532_; lean_object* v___y_1533_; lean_object* v___y_1534_; uint8_t v___x_1555_; 
v_one_1471_ = lean_unsigned_to_nat(1u);
v_n_1472_ = lean_nat_sub(v_i_1461_, v_one_1471_);
lean_dec(v_i_1461_);
v___x_1476_ = lean_nat_sub(v_n_1460_, v_n_1472_);
v___x_1477_ = lean_nat_sub(v___x_1476_, v_one_1471_);
lean_dec(v___x_1476_);
v_arg_1478_ = lean_array_fget_borrowed(v_majorTypeArgs_1453_, v___x_1477_);
v___x_1555_ = lean_nat_dec_eq(v___x_1477_, v_idxPos_1457_);
if (v___x_1555_ == 0)
{
uint8_t v___x_1556_; 
v___x_1556_ = lean_expr_eqv(v_arg_1478_, v_idx_1454_);
if (v___x_1556_ == 0)
{
v___y_1531_ = v___y_1462_;
v___y_1532_ = v___y_1463_;
v___y_1533_ = v___y_1464_;
v___y_1534_ = v___y_1465_;
goto v___jp_1530_;
}
else
{
lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; 
v___x_1557_ = lean_obj_once(&l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1, &l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1_once, _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1);
lean_inc_ref(v_idx_1454_);
v___x_1558_ = l_Lean_MessageData_ofExpr(v_idx_1454_);
v___x_1559_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1559_, 0, v___x_1557_);
lean_ctor_set(v___x_1559_, 1, v___x_1558_);
v___x_1560_ = lean_obj_once(&l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__7, &l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__7_once, _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__7);
v___x_1561_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1561_, 0, v___x_1559_);
lean_ctor_set(v___x_1561_, 1, v___x_1560_);
lean_inc_ref(v_majorType_1459_);
v___x_1562_ = l_Lean_indentExpr(v_majorType_1459_);
v___x_1563_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1563_, 0, v___x_1561_);
lean_ctor_set(v___x_1563_, 1, v___x_1562_);
v___x_1564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1564_, 0, v___x_1563_);
lean_inc(v_mvarId_1456_);
lean_inc(v_tacticName_1455_);
v___x_1565_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1455_, v_mvarId_1456_, v___x_1564_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_);
if (lean_obj_tag(v___x_1565_) == 0)
{
lean_dec_ref_known(v___x_1565_, 1);
v___y_1531_ = v___y_1462_;
v___y_1532_ = v___y_1463_;
v___y_1533_ = v___y_1464_;
v___y_1534_ = v___y_1465_;
goto v___jp_1530_;
}
else
{
lean_dec(v___x_1477_);
v___y_1474_ = v___x_1565_;
goto v___jp_1473_;
}
}
}
else
{
v___y_1531_ = v___y_1462_;
v___y_1532_ = v___y_1463_;
v___y_1533_ = v___y_1464_;
v___y_1534_ = v___y_1465_;
goto v___jp_1530_;
}
v___jp_1473_:
{
if (lean_obj_tag(v___y_1474_) == 0)
{
lean_dec_ref_known(v___y_1474_, 1);
v_i_1461_ = v_n_1472_;
goto _start;
}
else
{
lean_dec(v_n_1472_);
lean_dec_ref(v_majorType_1459_);
lean_dec(v_mvarId_1456_);
lean_dec(v_tacticName_1455_);
lean_dec_ref(v_idx_1454_);
return v___y_1474_;
}
}
v___jp_1479_:
{
if (v___y_1484_ == 0)
{
lean_dec(v___x_1477_);
v_i_1461_ = v_n_1472_;
goto _start;
}
else
{
uint8_t v___x_1486_; 
v___x_1486_ = l_Lean_Expr_isFVar(v_arg_1478_);
if (v___x_1486_ == 0)
{
lean_dec(v___x_1477_);
v_i_1461_ = v_n_1472_;
goto _start;
}
else
{
lean_object* v___x_1488_; lean_object* v___x_1489_; 
v___x_1488_ = l_Lean_Expr_fvarId_x21(v_idx_1454_);
v___x_1489_ = l_Lean_FVarId_getDecl___redArg(v___x_1488_, v___y_1483_, v___y_1480_, v___y_1482_);
if (lean_obj_tag(v___x_1489_) == 0)
{
lean_object* v_a_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v_a_1493_; lean_object* v___x_1495_; uint8_t v_isShared_1496_; uint8_t v_isSharedCheck_1513_; 
v_a_1490_ = lean_ctor_get(v___x_1489_, 0);
lean_inc(v_a_1490_);
lean_dec_ref_known(v___x_1489_, 1);
v___x_1491_ = l_Lean_Expr_fvarId_x21(v_arg_1478_);
v___x_1492_ = l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg(v_a_1490_, v___x_1491_, v___y_1484_, v___y_1481_);
v_a_1493_ = lean_ctor_get(v___x_1492_, 0);
v_isSharedCheck_1513_ = !lean_is_exclusive(v___x_1492_);
if (v_isSharedCheck_1513_ == 0)
{
v___x_1495_ = v___x_1492_;
v_isShared_1496_ = v_isSharedCheck_1513_;
goto v_resetjp_1494_;
}
else
{
lean_inc(v_a_1493_);
lean_dec(v___x_1492_);
v___x_1495_ = lean_box(0);
v_isShared_1496_ = v_isSharedCheck_1513_;
goto v_resetjp_1494_;
}
v_resetjp_1494_:
{
uint8_t v___x_1497_; 
v___x_1497_ = lean_unbox(v_a_1493_);
lean_dec(v_a_1493_);
if (v___x_1497_ == 0)
{
lean_del_object(v___x_1495_);
lean_dec(v___x_1477_);
v_i_1461_ = v_n_1472_;
goto _start;
}
else
{
lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1507_; 
v___x_1499_ = lean_obj_once(&l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1, &l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1_once, _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1);
lean_inc_ref(v_idx_1454_);
v___x_1500_ = l_Lean_MessageData_ofExpr(v_idx_1454_);
v___x_1501_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1501_, 0, v___x_1499_);
lean_ctor_set(v___x_1501_, 1, v___x_1500_);
v___x_1502_ = lean_obj_once(&l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__3, &l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__3_once, _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__3);
v___x_1503_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1503_, 0, v___x_1501_);
lean_ctor_set(v___x_1503_, 1, v___x_1502_);
v___x_1504_ = lean_nat_add(v___x_1477_, v_one_1471_);
lean_dec(v___x_1477_);
v___x_1505_ = l_Nat_reprFast(v___x_1504_);
if (v_isShared_1496_ == 0)
{
lean_ctor_set_tag(v___x_1495_, 3);
lean_ctor_set(v___x_1495_, 0, v___x_1505_);
v___x_1507_ = v___x_1495_;
goto v_reusejp_1506_;
}
else
{
lean_object* v_reuseFailAlloc_1512_; 
v_reuseFailAlloc_1512_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1512_, 0, v___x_1505_);
v___x_1507_ = v_reuseFailAlloc_1512_;
goto v_reusejp_1506_;
}
v_reusejp_1506_:
{
lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; 
v___x_1508_ = l_Lean_MessageData_ofFormat(v___x_1507_);
v___x_1509_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1509_, 0, v___x_1503_);
lean_ctor_set(v___x_1509_, 1, v___x_1508_);
v___x_1510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1510_, 0, v___x_1509_);
lean_inc(v_mvarId_1456_);
lean_inc(v_tacticName_1455_);
v___x_1511_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1455_, v_mvarId_1456_, v___x_1510_, v___y_1483_, v___y_1481_, v___y_1480_, v___y_1482_);
v___y_1474_ = v___x_1511_;
goto v___jp_1473_;
}
}
}
}
else
{
lean_object* v_a_1514_; lean_object* v___x_1516_; uint8_t v_isShared_1517_; uint8_t v_isSharedCheck_1521_; 
lean_dec(v___x_1477_);
lean_dec(v_n_1472_);
lean_dec_ref(v_majorType_1459_);
lean_dec(v_mvarId_1456_);
lean_dec(v_tacticName_1455_);
lean_dec_ref(v_idx_1454_);
v_a_1514_ = lean_ctor_get(v___x_1489_, 0);
v_isSharedCheck_1521_ = !lean_is_exclusive(v___x_1489_);
if (v_isSharedCheck_1521_ == 0)
{
v___x_1516_ = v___x_1489_;
v_isShared_1517_ = v_isSharedCheck_1521_;
goto v_resetjp_1515_;
}
else
{
lean_inc(v_a_1514_);
lean_dec(v___x_1489_);
v___x_1516_ = lean_box(0);
v_isShared_1517_ = v_isSharedCheck_1521_;
goto v_resetjp_1515_;
}
v_resetjp_1515_:
{
lean_object* v___x_1519_; 
if (v_isShared_1517_ == 0)
{
v___x_1519_ = v___x_1516_;
goto v_reusejp_1518_;
}
else
{
lean_object* v_reuseFailAlloc_1520_; 
v_reuseFailAlloc_1520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1520_, 0, v_a_1514_);
v___x_1519_ = v_reuseFailAlloc_1520_;
goto v_reusejp_1518_;
}
v_reusejp_1518_:
{
return v___x_1519_;
}
}
}
}
}
}
v___jp_1522_:
{
uint8_t v___x_1527_; 
v___x_1527_ = lean_nat_dec_lt(v_idxPos_1457_, v___x_1477_);
if (v___x_1527_ == 0)
{
v___y_1480_ = v___y_1525_;
v___y_1481_ = v___y_1524_;
v___y_1482_ = v___y_1526_;
v___y_1483_ = v___y_1523_;
v___y_1484_ = v___x_1527_;
goto v___jp_1479_;
}
else
{
lean_object* v_indicesPos_1528_; uint8_t v___x_1529_; 
v_indicesPos_1528_ = lean_ctor_get(v_recursorInfo_1458_, 6);
v___x_1529_ = l_List_elem___at___00Lean_Meta_getMajorTypeIndices_spec__1(v___x_1477_, v_indicesPos_1528_);
v___y_1480_ = v___y_1525_;
v___y_1481_ = v___y_1524_;
v___y_1482_ = v___y_1526_;
v___y_1483_ = v___y_1523_;
v___y_1484_ = v___x_1529_;
goto v___jp_1479_;
}
}
v___jp_1530_:
{
uint8_t v___x_1535_; 
v___x_1535_ = lean_nat_dec_lt(v___x_1477_, v_idxPos_1457_);
if (v___x_1535_ == 0)
{
v___y_1523_ = v___y_1531_;
v___y_1524_ = v___y_1532_;
v___y_1525_ = v___y_1533_;
v___y_1526_ = v___y_1534_;
goto v___jp_1522_;
}
else
{
lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v_a_1538_; lean_object* v___x_1540_; uint8_t v_isShared_1541_; uint8_t v_isSharedCheck_1554_; 
v___x_1536_ = l_Lean_Expr_fvarId_x21(v_idx_1454_);
lean_inc(v_arg_1478_);
v___x_1537_ = l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2___redArg(v_arg_1478_, v___x_1536_, v___y_1532_);
v_a_1538_ = lean_ctor_get(v___x_1537_, 0);
v_isSharedCheck_1554_ = !lean_is_exclusive(v___x_1537_);
if (v_isSharedCheck_1554_ == 0)
{
v___x_1540_ = v___x_1537_;
v_isShared_1541_ = v_isSharedCheck_1554_;
goto v_resetjp_1539_;
}
else
{
lean_inc(v_a_1538_);
lean_dec(v___x_1537_);
v___x_1540_ = lean_box(0);
v_isShared_1541_ = v_isSharedCheck_1554_;
goto v_resetjp_1539_;
}
v_resetjp_1539_:
{
uint8_t v___x_1542_; 
v___x_1542_ = lean_unbox(v_a_1538_);
lean_dec(v_a_1538_);
if (v___x_1542_ == 0)
{
lean_del_object(v___x_1540_);
v___y_1523_ = v___y_1531_;
v___y_1524_ = v___y_1532_;
v___y_1525_ = v___y_1533_;
v___y_1526_ = v___y_1534_;
goto v___jp_1522_;
}
else
{
lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1551_; 
v___x_1543_ = lean_obj_once(&l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1, &l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1_once, _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1);
lean_inc_ref(v_idx_1454_);
v___x_1544_ = l_Lean_MessageData_ofExpr(v_idx_1454_);
v___x_1545_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1545_, 0, v___x_1543_);
lean_ctor_set(v___x_1545_, 1, v___x_1544_);
v___x_1546_ = lean_obj_once(&l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__5, &l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__5_once, _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__5);
v___x_1547_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1547_, 0, v___x_1545_);
lean_ctor_set(v___x_1547_, 1, v___x_1546_);
lean_inc_ref(v_majorType_1459_);
v___x_1548_ = l_Lean_indentExpr(v_majorType_1459_);
v___x_1549_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1549_, 0, v___x_1547_);
lean_ctor_set(v___x_1549_, 1, v___x_1548_);
if (v_isShared_1541_ == 0)
{
lean_ctor_set_tag(v___x_1540_, 1);
lean_ctor_set(v___x_1540_, 0, v___x_1549_);
v___x_1551_ = v___x_1540_;
goto v_reusejp_1550_;
}
else
{
lean_object* v_reuseFailAlloc_1553_; 
v_reuseFailAlloc_1553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1553_, 0, v___x_1549_);
v___x_1551_ = v_reuseFailAlloc_1553_;
goto v_reusejp_1550_;
}
v_reusejp_1550_:
{
lean_object* v___x_1552_; 
lean_inc(v_mvarId_1456_);
lean_inc(v_tacticName_1455_);
v___x_1552_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1455_, v_mvarId_1456_, v___x_1551_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_);
if (lean_obj_tag(v___x_1552_) == 0)
{
lean_dec_ref_known(v___x_1552_, 1);
v___y_1523_ = v___y_1531_;
v___y_1524_ = v___y_1532_;
v___y_1525_ = v___y_1533_;
v___y_1526_ = v___y_1534_;
goto v___jp_1522_;
}
else
{
lean_dec(v___x_1477_);
v___y_1474_ = v___x_1552_;
goto v___jp_1473_;
}
}
}
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
lean_object* v_a_1905_; lean_object* v_fst_1906_; lean_object* v_snd_1907_; lean_object* v___x_1909_; uint8_t v_isShared_1910_; uint8_t v_isSharedCheck_1951_; 
v_a_1905_ = lean_ctor_get(v___x_1904_, 0);
lean_inc(v_a_1905_);
lean_dec_ref_known(v___x_1904_, 1);
v_fst_1906_ = lean_ctor_get(v_a_1905_, 0);
v_snd_1907_ = lean_ctor_get(v_a_1905_, 1);
v_isSharedCheck_1951_ = !lean_is_exclusive(v_a_1905_);
if (v_isSharedCheck_1951_ == 0)
{
v___x_1909_ = v_a_1905_;
v_isShared_1910_ = v_isSharedCheck_1951_;
goto v_resetjp_1908_;
}
else
{
lean_inc(v_snd_1907_);
lean_inc(v_fst_1906_);
lean_dec(v_a_1905_);
v___x_1909_ = lean_box(0);
v_isShared_1910_ = v_isSharedCheck_1951_;
goto v_resetjp_1908_;
}
v_resetjp_1908_:
{
lean_object* v___y_1912_; lean_object* v___y_1913_; lean_object* v___y_1914_; lean_object* v___y_1915_; uint8_t v___x_1931_; 
v___x_1931_ = lean_unbox(v_snd_1907_);
lean_dec(v_snd_1907_);
if (v___x_1931_ == 0)
{
uint8_t v___x_1932_; 
v___x_1932_ = l_Lean_Level_isZero(v_a_1857_);
lean_dec(v_a_1857_);
if (v___x_1932_ == 0)
{
lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1937_; 
lean_dec(v_fst_1906_);
lean_dec(v_paramsPos_1881_);
lean_dec_ref(v_x_1864_);
lean_dec_ref(v_major_1862_);
lean_dec_ref(v_a_1861_);
v___x_1933_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__6));
v___x_1934_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__8, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__8_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__8);
v___x_1935_ = l_Lean_MessageData_ofName(v_recursorName_1878_);
if (v_isShared_1910_ == 0)
{
lean_ctor_set_tag(v___x_1909_, 7);
lean_ctor_set(v___x_1909_, 1, v___x_1935_);
lean_ctor_set(v___x_1909_, 0, v___x_1934_);
v___x_1937_ = v___x_1909_;
goto v_reusejp_1936_;
}
else
{
lean_object* v_reuseFailAlloc_1950_; 
v_reuseFailAlloc_1950_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1950_, 0, v___x_1934_);
lean_ctor_set(v_reuseFailAlloc_1950_, 1, v___x_1935_);
v___x_1937_ = v_reuseFailAlloc_1950_;
goto v_reusejp_1936_;
}
v_reusejp_1936_:
{
lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v_a_1942_; lean_object* v___x_1944_; uint8_t v_isShared_1945_; uint8_t v_isSharedCheck_1949_; 
v___x_1938_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__10, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__10_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__10);
v___x_1939_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1939_, 0, v___x_1937_);
lean_ctor_set(v___x_1939_, 1, v___x_1938_);
v___x_1940_ = l_Lean_Meta_mkTacticExMsg(v_tacticName_1858_, v_mvarId_1859_, v___x_1939_);
v___x_1941_ = l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1___redArg(v___x_1933_, v___x_1940_, v___y_1866_, v___y_1867_, v___y_1868_, v___y_1869_);
v_a_1942_ = lean_ctor_get(v___x_1941_, 0);
v_isSharedCheck_1949_ = !lean_is_exclusive(v___x_1941_);
if (v_isSharedCheck_1949_ == 0)
{
v___x_1944_ = v___x_1941_;
v_isShared_1945_ = v_isSharedCheck_1949_;
goto v_resetjp_1943_;
}
else
{
lean_inc(v_a_1942_);
lean_dec(v___x_1941_);
v___x_1944_ = lean_box(0);
v_isShared_1945_ = v_isSharedCheck_1949_;
goto v_resetjp_1943_;
}
v_resetjp_1943_:
{
lean_object* v___x_1947_; 
if (v_isShared_1945_ == 0)
{
v___x_1947_ = v___x_1944_;
goto v_reusejp_1946_;
}
else
{
lean_object* v_reuseFailAlloc_1948_; 
v_reuseFailAlloc_1948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1948_, 0, v_a_1942_);
v___x_1947_ = v_reuseFailAlloc_1948_;
goto v_reusejp_1946_;
}
v_reusejp_1946_:
{
return v___x_1947_;
}
}
}
}
else
{
lean_del_object(v___x_1909_);
lean_dec(v_tacticName_1858_);
v___y_1912_ = v___y_1866_;
v___y_1913_ = v___y_1867_;
v___y_1914_ = v___y_1868_;
v___y_1915_ = v___y_1869_;
goto v___jp_1911_;
}
}
else
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
lean_object* v_a_1952_; lean_object* v___x_1954_; uint8_t v_isShared_1955_; uint8_t v_isSharedCheck_1959_; 
lean_dec(v_paramsPos_1881_);
lean_dec(v_recursorName_1878_);
lean_dec_ref(v_x_1864_);
lean_dec_ref(v_major_1862_);
lean_dec_ref(v_a_1861_);
lean_dec(v_mvarId_1859_);
lean_dec(v_tacticName_1858_);
lean_dec(v_a_1857_);
v_a_1952_ = lean_ctor_get(v___x_1904_, 0);
v_isSharedCheck_1959_ = !lean_is_exclusive(v___x_1904_);
if (v_isSharedCheck_1959_ == 0)
{
v___x_1954_ = v___x_1904_;
v_isShared_1955_ = v_isSharedCheck_1959_;
goto v_resetjp_1953_;
}
else
{
lean_inc(v_a_1952_);
lean_dec(v___x_1904_);
v___x_1954_ = lean_box(0);
v_isShared_1955_ = v_isSharedCheck_1959_;
goto v_resetjp_1953_;
}
v_resetjp_1953_:
{
lean_object* v___x_1957_; 
if (v_isShared_1955_ == 0)
{
v___x_1957_ = v___x_1954_;
goto v_reusejp_1956_;
}
else
{
lean_object* v_reuseFailAlloc_1958_; 
v_reuseFailAlloc_1958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1958_, 0, v_a_1952_);
v___x_1957_ = v_reuseFailAlloc_1958_;
goto v_reusejp_1956_;
}
v_reusejp_1956_:
{
return v___x_1957_;
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
lean_object* v___x_1960_; lean_object* v___x_1961_; 
lean_dec_ref(v_x_1864_);
lean_dec_ref(v_x_1863_);
lean_dec_ref(v_major_1862_);
lean_dec_ref(v_a_1861_);
lean_dec(v_a_1857_);
lean_dec_ref(v_recursorInfo_1856_);
v___x_1960_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__14, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__14_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__14);
v___x_1961_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1858_, v_mvarId_1859_, v___x_1960_, v___y_1866_, v___y_1867_, v___y_1868_, v___y_1869_);
return v___x_1961_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___boxed(lean_object* v_recursorInfo_1962_, lean_object* v_a_1963_, lean_object* v_tacticName_1964_, lean_object* v_mvarId_1965_, lean_object* v_indices_1966_, lean_object* v_a_1967_, lean_object* v_major_1968_, lean_object* v_x_1969_, lean_object* v_x_1970_, lean_object* v_x_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_){
_start:
{
lean_object* v_res_1977_; 
v_res_1977_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2(v_recursorInfo_1962_, v_a_1963_, v_tacticName_1964_, v_mvarId_1965_, v_indices_1966_, v_a_1967_, v_major_1968_, v_x_1969_, v_x_1970_, v_x_1971_, v___y_1972_, v___y_1973_, v___y_1974_, v___y_1975_);
lean_dec(v___y_1975_);
lean_dec_ref(v___y_1974_);
lean_dec(v___y_1973_);
lean_dec_ref(v___y_1972_);
lean_dec_ref(v_indices_1966_);
return v_res_1977_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2(lean_object* v_a_1978_, lean_object* v_tacticName_1979_, lean_object* v_mvarId_1980_, lean_object* v_recursorInfo_1981_, lean_object* v_indices_1982_, lean_object* v_a_1983_, lean_object* v_major_1984_, lean_object* v_x_1985_, lean_object* v_x_1986_, lean_object* v_x_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_){
_start:
{
if (lean_obj_tag(v_x_1985_) == 5)
{
lean_object* v_fn_1993_; lean_object* v_arg_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; 
v_fn_1993_ = lean_ctor_get(v_x_1985_, 0);
lean_inc_ref(v_fn_1993_);
v_arg_1994_ = lean_ctor_get(v_x_1985_, 1);
lean_inc_ref(v_arg_1994_);
lean_dec_ref_known(v_x_1985_, 2);
v___x_1995_ = lean_array_set(v_x_1986_, v_x_1987_, v_arg_1994_);
v___x_1996_ = lean_unsigned_to_nat(1u);
v___x_1997_ = lean_nat_sub(v_x_1987_, v___x_1996_);
v___x_1998_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2(v_recursorInfo_1981_, v_a_1978_, v_tacticName_1979_, v_mvarId_1980_, v_indices_1982_, v_a_1983_, v_major_1984_, v_fn_1993_, v___x_1995_, v___x_1997_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_);
return v___x_1998_;
}
else
{
if (lean_obj_tag(v_x_1985_) == 4)
{
lean_object* v_us_1999_; lean_object* v_recursorName_2000_; lean_object* v_univLevelPos_2001_; uint8_t v_depElim_2002_; lean_object* v_paramsPos_2003_; lean_object* v___x_2004_; uint8_t v___x_2005_; lean_object* v___y_2007_; lean_object* v_motive_2008_; lean_object* v___y_2009_; lean_object* v___y_2010_; lean_object* v___y_2011_; lean_object* v___y_2012_; lean_object* v___x_2025_; lean_object* v___x_2026_; 
v_us_1999_ = lean_ctor_get(v_x_1985_, 1);
lean_inc(v_us_1999_);
lean_dec_ref_known(v_x_1985_, 2);
v_recursorName_2000_ = lean_ctor_get(v_recursorInfo_1981_, 0);
lean_inc(v_recursorName_2000_);
v_univLevelPos_2001_ = lean_ctor_get(v_recursorInfo_1981_, 2);
lean_inc(v_univLevelPos_2001_);
v_depElim_2002_ = lean_ctor_get_uint8(v_recursorInfo_1981_, sizeof(void*)*8);
v_paramsPos_2003_ = lean_ctor_get(v_recursorInfo_1981_, 5);
lean_inc(v_paramsPos_2003_);
lean_dec_ref(v_recursorInfo_1981_);
v___x_2004_ = lean_array_mk(v_us_1999_);
v___x_2005_ = 0;
v___x_2025_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__1));
lean_inc(v_mvarId_1980_);
lean_inc(v_tacticName_1979_);
lean_inc(v_a_1978_);
v___x_2026_ = l_List_foldlM___at___00Lean_Meta_mkRecursorAppPrefix_spec__0(v_a_1978_, v___x_2004_, v_tacticName_1979_, v_mvarId_1980_, v___x_2025_, v_univLevelPos_2001_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_);
lean_dec(v_univLevelPos_2001_);
lean_dec_ref(v___x_2004_);
if (lean_obj_tag(v___x_2026_) == 0)
{
lean_object* v_a_2027_; lean_object* v_fst_2028_; lean_object* v_snd_2029_; lean_object* v___x_2031_; uint8_t v_isShared_2032_; uint8_t v_isSharedCheck_2073_; 
v_a_2027_ = lean_ctor_get(v___x_2026_, 0);
lean_inc(v_a_2027_);
lean_dec_ref_known(v___x_2026_, 1);
v_fst_2028_ = lean_ctor_get(v_a_2027_, 0);
v_snd_2029_ = lean_ctor_get(v_a_2027_, 1);
v_isSharedCheck_2073_ = !lean_is_exclusive(v_a_2027_);
if (v_isSharedCheck_2073_ == 0)
{
v___x_2031_ = v_a_2027_;
v_isShared_2032_ = v_isSharedCheck_2073_;
goto v_resetjp_2030_;
}
else
{
lean_inc(v_snd_2029_);
lean_inc(v_fst_2028_);
lean_dec(v_a_2027_);
v___x_2031_ = lean_box(0);
v_isShared_2032_ = v_isSharedCheck_2073_;
goto v_resetjp_2030_;
}
v_resetjp_2030_:
{
lean_object* v___y_2034_; lean_object* v___y_2035_; lean_object* v___y_2036_; lean_object* v___y_2037_; uint8_t v___x_2053_; 
v___x_2053_ = lean_unbox(v_snd_2029_);
lean_dec(v_snd_2029_);
if (v___x_2053_ == 0)
{
uint8_t v___x_2054_; 
v___x_2054_ = l_Lean_Level_isZero(v_a_1978_);
lean_dec(v_a_1978_);
if (v___x_2054_ == 0)
{
lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2059_; 
lean_dec(v_fst_2028_);
lean_dec(v_paramsPos_2003_);
lean_dec_ref(v_x_1986_);
lean_dec_ref(v_major_1984_);
lean_dec_ref(v_a_1983_);
v___x_2055_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__6));
v___x_2056_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__8, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__8_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__8);
v___x_2057_ = l_Lean_MessageData_ofName(v_recursorName_2000_);
if (v_isShared_2032_ == 0)
{
lean_ctor_set_tag(v___x_2031_, 7);
lean_ctor_set(v___x_2031_, 1, v___x_2057_);
lean_ctor_set(v___x_2031_, 0, v___x_2056_);
v___x_2059_ = v___x_2031_;
goto v_reusejp_2058_;
}
else
{
lean_object* v_reuseFailAlloc_2072_; 
v_reuseFailAlloc_2072_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2072_, 0, v___x_2056_);
lean_ctor_set(v_reuseFailAlloc_2072_, 1, v___x_2057_);
v___x_2059_ = v_reuseFailAlloc_2072_;
goto v_reusejp_2058_;
}
v_reusejp_2058_:
{
lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v_a_2064_; lean_object* v___x_2066_; uint8_t v_isShared_2067_; uint8_t v_isSharedCheck_2071_; 
v___x_2060_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__10, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__10_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__10);
v___x_2061_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2061_, 0, v___x_2059_);
lean_ctor_set(v___x_2061_, 1, v___x_2060_);
v___x_2062_ = l_Lean_Meta_mkTacticExMsg(v_tacticName_1979_, v_mvarId_1980_, v___x_2061_);
v___x_2063_ = l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1___redArg(v___x_2055_, v___x_2062_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_);
v_a_2064_ = lean_ctor_get(v___x_2063_, 0);
v_isSharedCheck_2071_ = !lean_is_exclusive(v___x_2063_);
if (v_isSharedCheck_2071_ == 0)
{
v___x_2066_ = v___x_2063_;
v_isShared_2067_ = v_isSharedCheck_2071_;
goto v_resetjp_2065_;
}
else
{
lean_inc(v_a_2064_);
lean_dec(v___x_2063_);
v___x_2066_ = lean_box(0);
v_isShared_2067_ = v_isSharedCheck_2071_;
goto v_resetjp_2065_;
}
v_resetjp_2065_:
{
lean_object* v___x_2069_; 
if (v_isShared_2067_ == 0)
{
v___x_2069_ = v___x_2066_;
goto v_reusejp_2068_;
}
else
{
lean_object* v_reuseFailAlloc_2070_; 
v_reuseFailAlloc_2070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2070_, 0, v_a_2064_);
v___x_2069_ = v_reuseFailAlloc_2070_;
goto v_reusejp_2068_;
}
v_reusejp_2068_:
{
return v___x_2069_;
}
}
}
}
else
{
lean_del_object(v___x_2031_);
lean_dec(v_tacticName_1979_);
v___y_2034_ = v___y_1988_;
v___y_2035_ = v___y_1989_;
v___y_2036_ = v___y_1990_;
v___y_2037_ = v___y_1991_;
goto v___jp_2033_;
}
}
else
{
lean_del_object(v___x_2031_);
lean_dec(v_tacticName_1979_);
lean_dec(v_a_1978_);
v___y_2034_ = v___y_1988_;
v___y_2035_ = v___y_1989_;
v___y_2036_ = v___y_1990_;
v___y_2037_ = v___y_1991_;
goto v___jp_2033_;
}
v___jp_2033_:
{
lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; 
v___x_2038_ = lean_array_to_list(v_fst_2028_);
v___x_2039_ = l_Lean_mkConst(v_recursorName_2000_, v___x_2038_);
v___x_2040_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams(v_mvarId_1980_, v_x_1986_, v_paramsPos_2003_, v___x_2039_, v___y_2034_, v___y_2035_, v___y_2036_, v___y_2037_);
lean_dec_ref(v_x_1986_);
if (lean_obj_tag(v___x_2040_) == 0)
{
if (v_depElim_2002_ == 0)
{
lean_object* v_a_2041_; 
lean_dec_ref(v_major_1984_);
v_a_2041_ = lean_ctor_get(v___x_2040_, 0);
lean_inc(v_a_2041_);
lean_dec_ref_known(v___x_2040_, 1);
v___y_2007_ = v_a_2041_;
v_motive_2008_ = v_a_1983_;
v___y_2009_ = v___y_2034_;
v___y_2010_ = v___y_2035_;
v___y_2011_ = v___y_2036_;
v___y_2012_ = v___y_2037_;
goto v___jp_2006_;
}
else
{
lean_object* v_a_2042_; lean_object* v___x_2043_; 
v_a_2042_ = lean_ctor_get(v___x_2040_, 0);
lean_inc(v_a_2042_);
lean_dec_ref_known(v___x_2040_, 1);
lean_inc(v___y_2037_);
lean_inc_ref(v___y_2036_);
lean_inc(v___y_2035_);
lean_inc_ref(v___y_2034_);
lean_inc_ref(v_major_1984_);
v___x_2043_ = lean_infer_type(v_major_1984_, v___y_2034_, v___y_2035_, v___y_2036_, v___y_2037_);
if (lean_obj_tag(v___x_2043_) == 0)
{
lean_object* v_a_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; 
v_a_2044_ = lean_ctor_get(v___x_2043_, 0);
lean_inc(v_a_2044_);
lean_dec_ref_known(v___x_2043_, 1);
v___x_2045_ = lean_unsigned_to_nat(1u);
v___x_2046_ = lean_mk_empty_array_with_capacity(v___x_2045_);
v___x_2047_ = lean_array_push(v___x_2046_, v_major_1984_);
v___x_2048_ = l_Lean_Expr_abstractM(v_a_1983_, v___x_2047_, v___y_2034_, v___y_2035_, v___y_2036_, v___y_2037_);
lean_dec_ref(v___x_2047_);
if (lean_obj_tag(v___x_2048_) == 0)
{
lean_object* v_a_2049_; lean_object* v___x_2050_; uint8_t v___x_2051_; lean_object* v___x_2052_; 
v_a_2049_ = lean_ctor_get(v___x_2048_, 0);
lean_inc(v_a_2049_);
lean_dec_ref_known(v___x_2048_, 1);
v___x_2050_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__3));
v___x_2051_ = 0;
v___x_2052_ = l_Lean_mkLambda(v___x_2050_, v___x_2051_, v_a_2044_, v_a_2049_);
v___y_2007_ = v_a_2042_;
v_motive_2008_ = v___x_2052_;
v___y_2009_ = v___y_2034_;
v___y_2010_ = v___y_2035_;
v___y_2011_ = v___y_2036_;
v___y_2012_ = v___y_2037_;
goto v___jp_2006_;
}
else
{
lean_dec(v_a_2044_);
lean_dec(v_a_2042_);
return v___x_2048_;
}
}
else
{
lean_dec(v_a_2042_);
lean_dec_ref(v_major_1984_);
lean_dec_ref(v_a_1983_);
return v___x_2043_;
}
}
}
else
{
lean_dec_ref(v_major_1984_);
lean_dec_ref(v_a_1983_);
return v___x_2040_;
}
}
}
}
else
{
lean_object* v_a_2074_; lean_object* v___x_2076_; uint8_t v_isShared_2077_; uint8_t v_isSharedCheck_2081_; 
lean_dec(v_paramsPos_2003_);
lean_dec(v_recursorName_2000_);
lean_dec_ref(v_x_1986_);
lean_dec_ref(v_major_1984_);
lean_dec_ref(v_a_1983_);
lean_dec(v_mvarId_1980_);
lean_dec(v_tacticName_1979_);
lean_dec(v_a_1978_);
v_a_2074_ = lean_ctor_get(v___x_2026_, 0);
v_isSharedCheck_2081_ = !lean_is_exclusive(v___x_2026_);
if (v_isSharedCheck_2081_ == 0)
{
v___x_2076_ = v___x_2026_;
v_isShared_2077_ = v_isSharedCheck_2081_;
goto v_resetjp_2075_;
}
else
{
lean_inc(v_a_2074_);
lean_dec(v___x_2026_);
v___x_2076_ = lean_box(0);
v_isShared_2077_ = v_isSharedCheck_2081_;
goto v_resetjp_2075_;
}
v_resetjp_2075_:
{
lean_object* v___x_2079_; 
if (v_isShared_2077_ == 0)
{
v___x_2079_ = v___x_2076_;
goto v_reusejp_2078_;
}
else
{
lean_object* v_reuseFailAlloc_2080_; 
v_reuseFailAlloc_2080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2080_, 0, v_a_2074_);
v___x_2079_ = v_reuseFailAlloc_2080_;
goto v_reusejp_2078_;
}
v_reusejp_2078_:
{
return v___x_2079_;
}
}
}
v___jp_2006_:
{
uint8_t v___x_2013_; uint8_t v___x_2014_; lean_object* v___x_2015_; 
v___x_2013_ = 1;
v___x_2014_ = 1;
v___x_2015_ = l_Lean_Meta_mkLambdaFVars(v_indices_1982_, v_motive_2008_, v___x_2005_, v___x_2013_, v___x_2005_, v___x_2013_, v___x_2014_, v___y_2009_, v___y_2010_, v___y_2011_, v___y_2012_);
if (lean_obj_tag(v___x_2015_) == 0)
{
lean_object* v_a_2016_; lean_object* v___x_2018_; uint8_t v_isShared_2019_; uint8_t v_isSharedCheck_2024_; 
v_a_2016_ = lean_ctor_get(v___x_2015_, 0);
v_isSharedCheck_2024_ = !lean_is_exclusive(v___x_2015_);
if (v_isSharedCheck_2024_ == 0)
{
v___x_2018_ = v___x_2015_;
v_isShared_2019_ = v_isSharedCheck_2024_;
goto v_resetjp_2017_;
}
else
{
lean_inc(v_a_2016_);
lean_dec(v___x_2015_);
v___x_2018_ = lean_box(0);
v_isShared_2019_ = v_isSharedCheck_2024_;
goto v_resetjp_2017_;
}
v_resetjp_2017_:
{
lean_object* v___x_2020_; lean_object* v___x_2022_; 
v___x_2020_ = l_Lean_Expr_app___override(v___y_2007_, v_a_2016_);
if (v_isShared_2019_ == 0)
{
lean_ctor_set(v___x_2018_, 0, v___x_2020_);
v___x_2022_ = v___x_2018_;
goto v_reusejp_2021_;
}
else
{
lean_object* v_reuseFailAlloc_2023_; 
v_reuseFailAlloc_2023_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2023_, 0, v___x_2020_);
v___x_2022_ = v_reuseFailAlloc_2023_;
goto v_reusejp_2021_;
}
v_reusejp_2021_:
{
return v___x_2022_;
}
}
}
else
{
lean_dec_ref(v___y_2007_);
return v___x_2015_;
}
}
}
else
{
lean_object* v___x_2082_; lean_object* v___x_2083_; 
lean_dec_ref(v_x_1986_);
lean_dec_ref(v_x_1985_);
lean_dec_ref(v_major_1984_);
lean_dec_ref(v_a_1983_);
lean_dec_ref(v_recursorInfo_1981_);
lean_dec(v_a_1978_);
v___x_2082_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__14, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__14_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__14);
v___x_2083_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1979_, v_mvarId_1980_, v___x_2082_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_);
return v___x_2083_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2___boxed(lean_object* v_a_2084_, lean_object* v_tacticName_2085_, lean_object* v_mvarId_2086_, lean_object* v_recursorInfo_2087_, lean_object* v_indices_2088_, lean_object* v_a_2089_, lean_object* v_major_2090_, lean_object* v_x_2091_, lean_object* v_x_2092_, lean_object* v_x_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_){
_start:
{
lean_object* v_res_2099_; 
v_res_2099_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2(v_a_2084_, v_tacticName_2085_, v_mvarId_2086_, v_recursorInfo_2087_, v_indices_2088_, v_a_2089_, v_major_2090_, v_x_2091_, v_x_2092_, v_x_2093_, v___y_2094_, v___y_2095_, v___y_2096_, v___y_2097_);
lean_dec(v___y_2097_);
lean_dec_ref(v___y_2096_);
lean_dec(v___y_2095_);
lean_dec_ref(v___y_2094_);
lean_dec(v_x_2093_);
lean_dec_ref(v_indices_2088_);
return v_res_2099_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkRecursorAppPrefix(lean_object* v_mvarId_2100_, lean_object* v_tacticName_2101_, lean_object* v_majorFVarId_2102_, lean_object* v_recursorInfo_2103_, lean_object* v_indices_2104_, lean_object* v_a_2105_, lean_object* v_a_2106_, lean_object* v_a_2107_, lean_object* v_a_2108_){
_start:
{
lean_object* v___x_2110_; 
lean_inc(v_mvarId_2100_);
v___x_2110_ = l_Lean_MVarId_getType(v_mvarId_2100_, v_a_2105_, v_a_2106_, v_a_2107_, v_a_2108_);
if (lean_obj_tag(v___x_2110_) == 0)
{
lean_object* v_a_2111_; lean_object* v___x_2112_; 
v_a_2111_ = lean_ctor_get(v___x_2110_, 0);
lean_inc_n(v_a_2111_, 2);
lean_dec_ref_known(v___x_2110_, 1);
v___x_2112_ = l_Lean_Meta_getLevel(v_a_2111_, v_a_2105_, v_a_2106_, v_a_2107_, v_a_2108_);
if (lean_obj_tag(v___x_2112_) == 0)
{
lean_object* v_a_2113_; lean_object* v___x_2114_; 
v_a_2113_ = lean_ctor_get(v___x_2112_, 0);
lean_inc(v_a_2113_);
lean_dec_ref_known(v___x_2112_, 1);
v___x_2114_ = l_Lean_Meta_normalizeLevel(v_a_2113_, v_a_2105_, v_a_2106_, v_a_2107_, v_a_2108_);
if (lean_obj_tag(v___x_2114_) == 0)
{
lean_object* v_a_2115_; lean_object* v_major_2116_; lean_object* v___x_2117_; 
v_a_2115_ = lean_ctor_get(v___x_2114_, 0);
lean_inc(v_a_2115_);
lean_dec_ref_known(v___x_2114_, 1);
lean_inc(v_majorFVarId_2102_);
v_major_2116_ = l_Lean_mkFVar(v_majorFVarId_2102_);
v___x_2117_ = l_Lean_FVarId_getDecl___redArg(v_majorFVarId_2102_, v_a_2105_, v_a_2107_, v_a_2108_);
if (lean_obj_tag(v___x_2117_) == 0)
{
lean_object* v_a_2118_; lean_object* v_typeName_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; 
v_a_2118_ = lean_ctor_get(v___x_2117_, 0);
lean_inc(v_a_2118_);
lean_dec_ref_known(v___x_2117_, 1);
v_typeName_2119_ = lean_ctor_get(v_recursorInfo_2103_, 1);
v___x_2120_ = l_Lean_LocalDecl_type(v_a_2118_);
lean_dec(v_a_2118_);
lean_inc_ref(v___x_2120_);
v___x_2121_ = l_Lean_Meta_whnfUntil(v___x_2120_, v_typeName_2119_, v_a_2105_, v_a_2106_, v_a_2107_, v_a_2108_);
if (lean_obj_tag(v___x_2121_) == 0)
{
lean_object* v_a_2122_; 
v_a_2122_ = lean_ctor_get(v___x_2121_, 0);
lean_inc(v_a_2122_);
lean_dec_ref_known(v___x_2121_, 1);
if (lean_obj_tag(v_a_2122_) == 1)
{
lean_object* v_val_2123_; lean_object* v_dummy_2124_; lean_object* v_nargs_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; 
lean_dec_ref(v___x_2120_);
v_val_2123_ = lean_ctor_get(v_a_2122_, 0);
lean_inc(v_val_2123_);
lean_dec_ref_known(v_a_2122_, 1);
v_dummy_2124_ = lean_obj_once(&l_Lean_Meta_getMajorTypeIndices___closed__0, &l_Lean_Meta_getMajorTypeIndices___closed__0_once, _init_l_Lean_Meta_getMajorTypeIndices___closed__0);
v_nargs_2125_ = l_Lean_Expr_getAppNumArgs(v_val_2123_);
lean_inc(v_nargs_2125_);
v___x_2126_ = lean_mk_array(v_nargs_2125_, v_dummy_2124_);
v___x_2127_ = lean_unsigned_to_nat(1u);
v___x_2128_ = lean_nat_sub(v_nargs_2125_, v___x_2127_);
lean_dec(v_nargs_2125_);
v___x_2129_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2(v_a_2115_, v_tacticName_2101_, v_mvarId_2100_, v_recursorInfo_2103_, v_indices_2104_, v_a_2111_, v_major_2116_, v_val_2123_, v___x_2126_, v___x_2128_, v_a_2105_, v_a_2106_, v_a_2107_, v_a_2108_);
lean_dec(v___x_2128_);
return v___x_2129_;
}
else
{
lean_object* v___x_2130_; 
lean_dec(v_a_2122_);
lean_dec_ref(v_major_2116_);
lean_dec(v_a_2115_);
lean_dec(v_a_2111_);
lean_dec_ref(v_recursorInfo_2103_);
v___x_2130_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg(v_tacticName_2101_, v_mvarId_2100_, v___x_2120_, v_a_2105_, v_a_2106_, v_a_2107_, v_a_2108_);
return v___x_2130_;
}
}
else
{
lean_object* v_a_2131_; lean_object* v___x_2133_; uint8_t v_isShared_2134_; uint8_t v_isSharedCheck_2138_; 
lean_dec_ref(v___x_2120_);
lean_dec_ref(v_major_2116_);
lean_dec(v_a_2115_);
lean_dec(v_a_2111_);
lean_dec_ref(v_recursorInfo_2103_);
lean_dec(v_tacticName_2101_);
lean_dec(v_mvarId_2100_);
v_a_2131_ = lean_ctor_get(v___x_2121_, 0);
v_isSharedCheck_2138_ = !lean_is_exclusive(v___x_2121_);
if (v_isSharedCheck_2138_ == 0)
{
v___x_2133_ = v___x_2121_;
v_isShared_2134_ = v_isSharedCheck_2138_;
goto v_resetjp_2132_;
}
else
{
lean_inc(v_a_2131_);
lean_dec(v___x_2121_);
v___x_2133_ = lean_box(0);
v_isShared_2134_ = v_isSharedCheck_2138_;
goto v_resetjp_2132_;
}
v_resetjp_2132_:
{
lean_object* v___x_2136_; 
if (v_isShared_2134_ == 0)
{
v___x_2136_ = v___x_2133_;
goto v_reusejp_2135_;
}
else
{
lean_object* v_reuseFailAlloc_2137_; 
v_reuseFailAlloc_2137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2137_, 0, v_a_2131_);
v___x_2136_ = v_reuseFailAlloc_2137_;
goto v_reusejp_2135_;
}
v_reusejp_2135_:
{
return v___x_2136_;
}
}
}
}
else
{
lean_object* v_a_2139_; lean_object* v___x_2141_; uint8_t v_isShared_2142_; uint8_t v_isSharedCheck_2146_; 
lean_dec_ref(v_major_2116_);
lean_dec(v_a_2115_);
lean_dec(v_a_2111_);
lean_dec_ref(v_recursorInfo_2103_);
lean_dec(v_tacticName_2101_);
lean_dec(v_mvarId_2100_);
v_a_2139_ = lean_ctor_get(v___x_2117_, 0);
v_isSharedCheck_2146_ = !lean_is_exclusive(v___x_2117_);
if (v_isSharedCheck_2146_ == 0)
{
v___x_2141_ = v___x_2117_;
v_isShared_2142_ = v_isSharedCheck_2146_;
goto v_resetjp_2140_;
}
else
{
lean_inc(v_a_2139_);
lean_dec(v___x_2117_);
v___x_2141_ = lean_box(0);
v_isShared_2142_ = v_isSharedCheck_2146_;
goto v_resetjp_2140_;
}
v_resetjp_2140_:
{
lean_object* v___x_2144_; 
if (v_isShared_2142_ == 0)
{
v___x_2144_ = v___x_2141_;
goto v_reusejp_2143_;
}
else
{
lean_object* v_reuseFailAlloc_2145_; 
v_reuseFailAlloc_2145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2145_, 0, v_a_2139_);
v___x_2144_ = v_reuseFailAlloc_2145_;
goto v_reusejp_2143_;
}
v_reusejp_2143_:
{
return v___x_2144_;
}
}
}
}
else
{
lean_object* v_a_2147_; lean_object* v___x_2149_; uint8_t v_isShared_2150_; uint8_t v_isSharedCheck_2154_; 
lean_dec(v_a_2111_);
lean_dec_ref(v_recursorInfo_2103_);
lean_dec(v_majorFVarId_2102_);
lean_dec(v_tacticName_2101_);
lean_dec(v_mvarId_2100_);
v_a_2147_ = lean_ctor_get(v___x_2114_, 0);
v_isSharedCheck_2154_ = !lean_is_exclusive(v___x_2114_);
if (v_isSharedCheck_2154_ == 0)
{
v___x_2149_ = v___x_2114_;
v_isShared_2150_ = v_isSharedCheck_2154_;
goto v_resetjp_2148_;
}
else
{
lean_inc(v_a_2147_);
lean_dec(v___x_2114_);
v___x_2149_ = lean_box(0);
v_isShared_2150_ = v_isSharedCheck_2154_;
goto v_resetjp_2148_;
}
v_resetjp_2148_:
{
lean_object* v___x_2152_; 
if (v_isShared_2150_ == 0)
{
v___x_2152_ = v___x_2149_;
goto v_reusejp_2151_;
}
else
{
lean_object* v_reuseFailAlloc_2153_; 
v_reuseFailAlloc_2153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2153_, 0, v_a_2147_);
v___x_2152_ = v_reuseFailAlloc_2153_;
goto v_reusejp_2151_;
}
v_reusejp_2151_:
{
return v___x_2152_;
}
}
}
}
else
{
lean_object* v_a_2155_; lean_object* v___x_2157_; uint8_t v_isShared_2158_; uint8_t v_isSharedCheck_2162_; 
lean_dec(v_a_2111_);
lean_dec_ref(v_recursorInfo_2103_);
lean_dec(v_majorFVarId_2102_);
lean_dec(v_tacticName_2101_);
lean_dec(v_mvarId_2100_);
v_a_2155_ = lean_ctor_get(v___x_2112_, 0);
v_isSharedCheck_2162_ = !lean_is_exclusive(v___x_2112_);
if (v_isSharedCheck_2162_ == 0)
{
v___x_2157_ = v___x_2112_;
v_isShared_2158_ = v_isSharedCheck_2162_;
goto v_resetjp_2156_;
}
else
{
lean_inc(v_a_2155_);
lean_dec(v___x_2112_);
v___x_2157_ = lean_box(0);
v_isShared_2158_ = v_isSharedCheck_2162_;
goto v_resetjp_2156_;
}
v_resetjp_2156_:
{
lean_object* v___x_2160_; 
if (v_isShared_2158_ == 0)
{
v___x_2160_ = v___x_2157_;
goto v_reusejp_2159_;
}
else
{
lean_object* v_reuseFailAlloc_2161_; 
v_reuseFailAlloc_2161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2161_, 0, v_a_2155_);
v___x_2160_ = v_reuseFailAlloc_2161_;
goto v_reusejp_2159_;
}
v_reusejp_2159_:
{
return v___x_2160_;
}
}
}
}
else
{
lean_dec_ref(v_recursorInfo_2103_);
lean_dec(v_majorFVarId_2102_);
lean_dec(v_tacticName_2101_);
lean_dec(v_mvarId_2100_);
return v___x_2110_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkRecursorAppPrefix___boxed(lean_object* v_mvarId_2163_, lean_object* v_tacticName_2164_, lean_object* v_majorFVarId_2165_, lean_object* v_recursorInfo_2166_, lean_object* v_indices_2167_, lean_object* v_a_2168_, lean_object* v_a_2169_, lean_object* v_a_2170_, lean_object* v_a_2171_, lean_object* v_a_2172_){
_start:
{
lean_object* v_res_2173_; 
v_res_2173_ = l_Lean_Meta_mkRecursorAppPrefix(v_mvarId_2163_, v_tacticName_2164_, v_majorFVarId_2165_, v_recursorInfo_2166_, v_indices_2167_, v_a_2168_, v_a_2169_, v_a_2170_, v_a_2171_);
lean_dec(v_a_2171_);
lean_dec_ref(v_a_2170_);
lean_dec(v_a_2169_);
lean_dec_ref(v_a_2168_);
lean_dec_ref(v_indices_2167_);
return v_res_2173_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1(lean_object* v_00_u03b1_2174_, lean_object* v_name_2175_, lean_object* v_msg_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_){
_start:
{
lean_object* v___x_2182_; 
v___x_2182_ = l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1___redArg(v_name_2175_, v_msg_2176_, v___y_2177_, v___y_2178_, v___y_2179_, v___y_2180_);
return v___x_2182_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1___boxed(lean_object* v_00_u03b1_2183_, lean_object* v_name_2184_, lean_object* v_msg_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_){
_start:
{
lean_object* v_res_2191_; 
v_res_2191_ = l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1(v_00_u03b1_2183_, v_name_2184_, v_msg_2185_, v___y_2186_, v___y_2187_, v___y_2188_, v___y_2189_);
lean_dec(v___y_2189_);
lean_dec_ref(v___y_2188_);
lean_dec(v___y_2187_);
lean_dec_ref(v___y_2186_);
return v_res_2191_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___redArg(lean_object* v_mvarId_2192_, lean_object* v_x_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_){
_start:
{
lean_object* v___x_2199_; 
v___x_2199_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_2192_, v_x_2193_, v___y_2194_, v___y_2195_, v___y_2196_, v___y_2197_);
if (lean_obj_tag(v___x_2199_) == 0)
{
lean_object* v_a_2200_; lean_object* v___x_2202_; uint8_t v_isShared_2203_; uint8_t v_isSharedCheck_2207_; 
v_a_2200_ = lean_ctor_get(v___x_2199_, 0);
v_isSharedCheck_2207_ = !lean_is_exclusive(v___x_2199_);
if (v_isSharedCheck_2207_ == 0)
{
v___x_2202_ = v___x_2199_;
v_isShared_2203_ = v_isSharedCheck_2207_;
goto v_resetjp_2201_;
}
else
{
lean_inc(v_a_2200_);
lean_dec(v___x_2199_);
v___x_2202_ = lean_box(0);
v_isShared_2203_ = v_isSharedCheck_2207_;
goto v_resetjp_2201_;
}
v_resetjp_2201_:
{
lean_object* v___x_2205_; 
if (v_isShared_2203_ == 0)
{
v___x_2205_ = v___x_2202_;
goto v_reusejp_2204_;
}
else
{
lean_object* v_reuseFailAlloc_2206_; 
v_reuseFailAlloc_2206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2206_, 0, v_a_2200_);
v___x_2205_ = v_reuseFailAlloc_2206_;
goto v_reusejp_2204_;
}
v_reusejp_2204_:
{
return v___x_2205_;
}
}
}
else
{
lean_object* v_a_2208_; lean_object* v___x_2210_; uint8_t v_isShared_2211_; uint8_t v_isSharedCheck_2215_; 
v_a_2208_ = lean_ctor_get(v___x_2199_, 0);
v_isSharedCheck_2215_ = !lean_is_exclusive(v___x_2199_);
if (v_isSharedCheck_2215_ == 0)
{
v___x_2210_ = v___x_2199_;
v_isShared_2211_ = v_isSharedCheck_2215_;
goto v_resetjp_2209_;
}
else
{
lean_inc(v_a_2208_);
lean_dec(v___x_2199_);
v___x_2210_ = lean_box(0);
v_isShared_2211_ = v_isSharedCheck_2215_;
goto v_resetjp_2209_;
}
v_resetjp_2209_:
{
lean_object* v___x_2213_; 
if (v_isShared_2211_ == 0)
{
v___x_2213_ = v___x_2210_;
goto v_reusejp_2212_;
}
else
{
lean_object* v_reuseFailAlloc_2214_; 
v_reuseFailAlloc_2214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2214_, 0, v_a_2208_);
v___x_2213_ = v_reuseFailAlloc_2214_;
goto v_reusejp_2212_;
}
v_reusejp_2212_:
{
return v___x_2213_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___redArg___boxed(lean_object* v_mvarId_2216_, lean_object* v_x_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_){
_start:
{
lean_object* v_res_2223_; 
v_res_2223_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___redArg(v_mvarId_2216_, v_x_2217_, v___y_2218_, v___y_2219_, v___y_2220_, v___y_2221_);
lean_dec(v___y_2221_);
lean_dec_ref(v___y_2220_);
lean_dec(v___y_2219_);
lean_dec_ref(v___y_2218_);
return v_res_2223_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3(lean_object* v_00_u03b1_2224_, lean_object* v_mvarId_2225_, lean_object* v_x_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_){
_start:
{
lean_object* v___x_2232_; 
v___x_2232_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___redArg(v_mvarId_2225_, v_x_2226_, v___y_2227_, v___y_2228_, v___y_2229_, v___y_2230_);
return v___x_2232_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___boxed(lean_object* v_00_u03b1_2233_, lean_object* v_mvarId_2234_, lean_object* v_x_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_){
_start:
{
lean_object* v_res_2241_; 
v_res_2241_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3(v_00_u03b1_2233_, v_mvarId_2234_, v_x_2235_, v___y_2236_, v___y_2237_, v___y_2238_, v___y_2239_);
lean_dec(v___y_2239_);
lean_dec_ref(v___y_2238_);
lean_dec(v___y_2237_);
lean_dec_ref(v___y_2236_);
return v_res_2241_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_induction_spec__2(lean_object* v_fst_2242_, lean_object* v_as_2243_, size_t v_sz_2244_, size_t v_i_2245_, lean_object* v_b_2246_){
_start:
{
uint8_t v___x_2247_; 
v___x_2247_ = lean_usize_dec_lt(v_i_2245_, v_sz_2244_);
if (v___x_2247_ == 0)
{
return v_b_2246_;
}
else
{
lean_object* v_fst_2248_; lean_object* v_snd_2249_; lean_object* v___x_2251_; uint8_t v_isShared_2252_; uint8_t v_isSharedCheck_2267_; 
v_fst_2248_ = lean_ctor_get(v_b_2246_, 0);
v_snd_2249_ = lean_ctor_get(v_b_2246_, 1);
v_isSharedCheck_2267_ = !lean_is_exclusive(v_b_2246_);
if (v_isSharedCheck_2267_ == 0)
{
v___x_2251_ = v_b_2246_;
v_isShared_2252_ = v_isSharedCheck_2267_;
goto v_resetjp_2250_;
}
else
{
lean_inc(v_snd_2249_);
lean_inc(v_fst_2248_);
lean_dec(v_b_2246_);
v___x_2251_ = lean_box(0);
v_isShared_2252_ = v_isSharedCheck_2267_;
goto v_resetjp_2250_;
}
v_resetjp_2250_:
{
lean_object* v___x_2253_; lean_object* v_a_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2262_; 
v___x_2253_ = lean_box(0);
v_a_2254_ = lean_array_uget_borrowed(v_as_2243_, v_i_2245_);
v___x_2255_ = l_Lean_Expr_fvarId_x21(v_a_2254_);
v___x_2256_ = lean_array_get_borrowed(v___x_2253_, v_fst_2242_, v_snd_2249_);
lean_inc(v___x_2256_);
v___x_2257_ = l_Lean_mkFVar(v___x_2256_);
v___x_2258_ = l_Lean_Meta_FVarSubst_insert(v_fst_2248_, v___x_2255_, v___x_2257_);
v___x_2259_ = lean_unsigned_to_nat(1u);
v___x_2260_ = lean_nat_add(v_snd_2249_, v___x_2259_);
lean_dec(v_snd_2249_);
if (v_isShared_2252_ == 0)
{
lean_ctor_set(v___x_2251_, 1, v___x_2260_);
lean_ctor_set(v___x_2251_, 0, v___x_2258_);
v___x_2262_ = v___x_2251_;
goto v_reusejp_2261_;
}
else
{
lean_object* v_reuseFailAlloc_2266_; 
v_reuseFailAlloc_2266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2266_, 0, v___x_2258_);
lean_ctor_set(v_reuseFailAlloc_2266_, 1, v___x_2260_);
v___x_2262_ = v_reuseFailAlloc_2266_;
goto v_reusejp_2261_;
}
v_reusejp_2261_:
{
size_t v___x_2263_; size_t v___x_2264_; 
v___x_2263_ = ((size_t)1ULL);
v___x_2264_ = lean_usize_add(v_i_2245_, v___x_2263_);
v_i_2245_ = v___x_2264_;
v_b_2246_ = v___x_2262_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_induction_spec__2___boxed(lean_object* v_fst_2268_, lean_object* v_as_2269_, lean_object* v_sz_2270_, lean_object* v_i_2271_, lean_object* v_b_2272_){
_start:
{
size_t v_sz_boxed_2273_; size_t v_i_boxed_2274_; lean_object* v_res_2275_; 
v_sz_boxed_2273_ = lean_unbox_usize(v_sz_2270_);
lean_dec(v_sz_2270_);
v_i_boxed_2274_ = lean_unbox_usize(v_i_2271_);
lean_dec(v_i_2271_);
v_res_2275_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_induction_spec__2(v_fst_2268_, v_as_2269_, v_sz_boxed_2273_, v_i_boxed_2274_, v_b_2272_);
lean_dec_ref(v_as_2269_);
lean_dec_ref(v_fst_2268_);
return v_res_2275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4___lam__0(lean_object* v_snd_2276_, lean_object* v___x_2277_, lean_object* v_fst_2278_, lean_object* v_a_2279_, lean_object* v___x_2280_, lean_object* v_givenNames_2281_, lean_object* v_fst_2282_, lean_object* v___x_2283_, lean_object* v_fst_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_){
_start:
{
lean_object* v___x_2290_; 
lean_inc_ref(v_a_2279_);
lean_inc(v_snd_2276_);
v___x_2290_ = l_Lean_Meta_mkRecursorAppPrefix(v_snd_2276_, v___x_2277_, v_fst_2278_, v_a_2279_, v___x_2280_, v___y_2285_, v___y_2286_, v___y_2287_, v___y_2288_);
if (lean_obj_tag(v___x_2290_) == 0)
{
lean_object* v_a_2291_; lean_object* v___x_2292_; 
v_a_2291_ = lean_ctor_get(v___x_2290_, 0);
lean_inc(v_a_2291_);
lean_dec_ref_known(v___x_2290_, 1);
v___x_2292_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize(v_snd_2276_, v_givenNames_2281_, v_a_2279_, v_fst_2282_, v___x_2283_, v___x_2280_, v_fst_2284_, v_a_2291_, v___y_2285_, v___y_2286_, v___y_2287_, v___y_2288_);
lean_dec_ref(v_a_2279_);
return v___x_2292_;
}
else
{
lean_object* v_a_2293_; lean_object* v___x_2295_; uint8_t v_isShared_2296_; uint8_t v_isSharedCheck_2300_; 
lean_dec(v_fst_2284_);
lean_dec_ref(v___x_2283_);
lean_dec_ref(v_a_2279_);
lean_dec(v_snd_2276_);
v_a_2293_ = lean_ctor_get(v___x_2290_, 0);
v_isSharedCheck_2300_ = !lean_is_exclusive(v___x_2290_);
if (v_isSharedCheck_2300_ == 0)
{
v___x_2295_ = v___x_2290_;
v_isShared_2296_ = v_isSharedCheck_2300_;
goto v_resetjp_2294_;
}
else
{
lean_inc(v_a_2293_);
lean_dec(v___x_2290_);
v___x_2295_ = lean_box(0);
v_isShared_2296_ = v_isSharedCheck_2300_;
goto v_resetjp_2294_;
}
v_resetjp_2294_:
{
lean_object* v___x_2298_; 
if (v_isShared_2296_ == 0)
{
v___x_2298_ = v___x_2295_;
goto v_reusejp_2297_;
}
else
{
lean_object* v_reuseFailAlloc_2299_; 
v_reuseFailAlloc_2299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2299_, 0, v_a_2293_);
v___x_2298_ = v_reuseFailAlloc_2299_;
goto v_reusejp_2297_;
}
v_reusejp_2297_:
{
return v___x_2298_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4___lam__0___boxed(lean_object* v_snd_2301_, lean_object* v___x_2302_, lean_object* v_fst_2303_, lean_object* v_a_2304_, lean_object* v___x_2305_, lean_object* v_givenNames_2306_, lean_object* v_fst_2307_, lean_object* v___x_2308_, lean_object* v_fst_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_){
_start:
{
lean_object* v_res_2315_; 
v_res_2315_ = l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4___lam__0(v_snd_2301_, v___x_2302_, v_fst_2303_, v_a_2304_, v___x_2305_, v_givenNames_2306_, v_fst_2307_, v___x_2308_, v_fst_2309_, v___y_2310_, v___y_2311_, v___y_2312_, v___y_2313_);
lean_dec(v___y_2313_);
lean_dec_ref(v___y_2312_);
lean_dec(v___y_2311_);
lean_dec_ref(v___y_2310_);
lean_dec_ref(v_fst_2307_);
lean_dec_ref(v_givenNames_2306_);
lean_dec_ref(v___x_2305_);
return v_res_2315_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_induction_spec__1(size_t v_sz_2316_, size_t v_i_2317_, lean_object* v_bs_2318_){
_start:
{
uint8_t v___x_2319_; 
v___x_2319_ = lean_usize_dec_lt(v_i_2317_, v_sz_2316_);
if (v___x_2319_ == 0)
{
return v_bs_2318_;
}
else
{
lean_object* v_v_2320_; lean_object* v___x_2321_; lean_object* v_bs_x27_2322_; lean_object* v___x_2323_; size_t v___x_2324_; size_t v___x_2325_; lean_object* v___x_2326_; 
v_v_2320_ = lean_array_uget(v_bs_2318_, v_i_2317_);
v___x_2321_ = lean_unsigned_to_nat(0u);
v_bs_x27_2322_ = lean_array_uset(v_bs_2318_, v_i_2317_, v___x_2321_);
v___x_2323_ = l_Lean_Expr_fvarId_x21(v_v_2320_);
lean_dec(v_v_2320_);
v___x_2324_ = ((size_t)1ULL);
v___x_2325_ = lean_usize_add(v_i_2317_, v___x_2324_);
v___x_2326_ = lean_array_uset(v_bs_x27_2322_, v_i_2317_, v___x_2323_);
v_i_2317_ = v___x_2325_;
v_bs_2318_ = v___x_2326_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_induction_spec__1___boxed(lean_object* v_sz_2328_, lean_object* v_i_2329_, lean_object* v_bs_2330_){
_start:
{
size_t v_sz_boxed_2331_; size_t v_i_boxed_2332_; lean_object* v_res_2333_; 
v_sz_boxed_2331_ = lean_unbox_usize(v_sz_2328_);
lean_dec(v_sz_2328_);
v_i_boxed_2332_ = lean_unbox_usize(v_i_2329_);
lean_dec(v_i_2329_);
v_res_2333_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_induction_spec__1(v_sz_boxed_2331_, v_i_boxed_2332_, v_bs_2330_);
return v_res_2333_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_MVarId_induction_spec__0(lean_object* v_majorTypeArgs_2334_, lean_object* v_val_2335_, lean_object* v_mvarId_2336_, lean_object* v_as_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_){
_start:
{
if (lean_obj_tag(v_as_2337_) == 0)
{
lean_object* v___x_2343_; lean_object* v___x_2344_; 
lean_dec(v_mvarId_2336_);
lean_dec_ref(v_val_2335_);
v___x_2343_ = lean_box(0);
v___x_2344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2344_, 0, v___x_2343_);
return v___x_2344_;
}
else
{
lean_object* v_head_2345_; 
v_head_2345_ = lean_ctor_get(v_as_2337_, 0);
lean_inc(v_head_2345_);
if (lean_obj_tag(v_head_2345_) == 0)
{
lean_object* v_tail_2346_; 
v_tail_2346_ = lean_ctor_get(v_as_2337_, 1);
lean_inc(v_tail_2346_);
lean_dec_ref_known(v_as_2337_, 2);
v_as_2337_ = v_tail_2346_;
goto _start;
}
else
{
lean_object* v_tail_2348_; lean_object* v___x_2350_; uint8_t v_isShared_2351_; uint8_t v_isSharedCheck_2371_; 
v_tail_2348_ = lean_ctor_get(v_as_2337_, 1);
v_isSharedCheck_2371_ = !lean_is_exclusive(v_as_2337_);
if (v_isSharedCheck_2371_ == 0)
{
lean_object* v_unused_2372_; 
v_unused_2372_ = lean_ctor_get(v_as_2337_, 0);
lean_dec(v_unused_2372_);
v___x_2350_ = v_as_2337_;
v_isShared_2351_ = v_isSharedCheck_2371_;
goto v_resetjp_2349_;
}
else
{
lean_inc(v_tail_2348_);
lean_dec(v_as_2337_);
v___x_2350_ = lean_box(0);
v_isShared_2351_ = v_isSharedCheck_2371_;
goto v_resetjp_2349_;
}
v_resetjp_2349_:
{
lean_object* v_val_2352_; lean_object* v___x_2354_; uint8_t v_isShared_2355_; uint8_t v_isSharedCheck_2370_; 
v_val_2352_ = lean_ctor_get(v_head_2345_, 0);
v_isSharedCheck_2370_ = !lean_is_exclusive(v_head_2345_);
if (v_isSharedCheck_2370_ == 0)
{
v___x_2354_ = v_head_2345_;
v_isShared_2355_ = v_isSharedCheck_2370_;
goto v_resetjp_2353_;
}
else
{
lean_inc(v_val_2352_);
lean_dec(v_head_2345_);
v___x_2354_ = lean_box(0);
v_isShared_2355_ = v_isSharedCheck_2370_;
goto v_resetjp_2353_;
}
v_resetjp_2353_:
{
lean_object* v___x_2356_; uint8_t v___x_2357_; 
v___x_2356_ = lean_array_get_size(v_majorTypeArgs_2334_);
v___x_2357_ = lean_nat_dec_le(v___x_2356_, v_val_2352_);
lean_dec(v_val_2352_);
if (v___x_2357_ == 0)
{
lean_del_object(v___x_2354_);
lean_del_object(v___x_2350_);
v_as_2337_ = v_tail_2348_;
goto _start;
}
else
{
lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2363_; 
v___x_2359_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1));
v___x_2360_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__5, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__5);
lean_inc_ref(v_val_2335_);
v___x_2361_ = l_Lean_indentExpr(v_val_2335_);
if (v_isShared_2351_ == 0)
{
lean_ctor_set_tag(v___x_2350_, 7);
lean_ctor_set(v___x_2350_, 1, v___x_2361_);
lean_ctor_set(v___x_2350_, 0, v___x_2360_);
v___x_2363_ = v___x_2350_;
goto v_reusejp_2362_;
}
else
{
lean_object* v_reuseFailAlloc_2369_; 
v_reuseFailAlloc_2369_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2369_, 0, v___x_2360_);
lean_ctor_set(v_reuseFailAlloc_2369_, 1, v___x_2361_);
v___x_2363_ = v_reuseFailAlloc_2369_;
goto v_reusejp_2362_;
}
v_reusejp_2362_:
{
lean_object* v___x_2365_; 
if (v_isShared_2355_ == 0)
{
lean_ctor_set(v___x_2354_, 0, v___x_2363_);
v___x_2365_ = v___x_2354_;
goto v_reusejp_2364_;
}
else
{
lean_object* v_reuseFailAlloc_2368_; 
v_reuseFailAlloc_2368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2368_, 0, v___x_2363_);
v___x_2365_ = v_reuseFailAlloc_2368_;
goto v_reusejp_2364_;
}
v_reusejp_2364_:
{
lean_object* v___x_2366_; 
lean_inc(v_mvarId_2336_);
v___x_2366_ = l_Lean_Meta_throwTacticEx___redArg(v___x_2359_, v_mvarId_2336_, v___x_2365_, v___y_2338_, v___y_2339_, v___y_2340_, v___y_2341_);
if (lean_obj_tag(v___x_2366_) == 0)
{
lean_dec_ref_known(v___x_2366_, 1);
v_as_2337_ = v_tail_2348_;
goto _start;
}
else
{
lean_dec(v_tail_2348_);
lean_dec(v_mvarId_2336_);
lean_dec_ref(v_val_2335_);
return v___x_2366_;
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
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_MVarId_induction_spec__0___boxed(lean_object* v_majorTypeArgs_2373_, lean_object* v_val_2374_, lean_object* v_mvarId_2375_, lean_object* v_as_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_){
_start:
{
lean_object* v_res_2382_; 
v_res_2382_ = l_List_forM___at___00Lean_MVarId_induction_spec__0(v_majorTypeArgs_2373_, v_val_2374_, v_mvarId_2375_, v_as_2376_, v___y_2377_, v___y_2378_, v___y_2379_, v___y_2380_);
lean_dec(v___y_2380_);
lean_dec_ref(v___y_2379_);
lean_dec(v___y_2378_);
lean_dec_ref(v___y_2377_);
lean_dec_ref(v_majorTypeArgs_2373_);
return v_res_2382_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__1(void){
_start:
{
lean_object* v___x_2384_; lean_object* v___x_2385_; 
v___x_2384_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__0));
v___x_2385_ = l_Lean_stringToMessageData(v___x_2384_);
return v___x_2385_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__3(void){
_start:
{
lean_object* v___x_2387_; lean_object* v___x_2388_; 
v___x_2387_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__2));
v___x_2388_ = l_Lean_stringToMessageData(v___x_2387_);
return v___x_2388_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__5(void){
_start:
{
lean_object* v___x_2390_; lean_object* v___x_2391_; 
v___x_2390_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__4));
v___x_2391_ = l_Lean_stringToMessageData(v___x_2390_);
return v___x_2391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4(lean_object* v_a_2392_, lean_object* v_val_2393_, lean_object* v_mvarId_2394_, lean_object* v_majorFVarId_2395_, lean_object* v_givenNames_2396_, lean_object* v_recursorName_2397_, lean_object* v_x_2398_, lean_object* v_x_2399_, lean_object* v_x_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_){
_start:
{
if (lean_obj_tag(v_x_2398_) == 5)
{
lean_object* v_fn_2406_; lean_object* v_arg_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; 
v_fn_2406_ = lean_ctor_get(v_x_2398_, 0);
lean_inc_ref(v_fn_2406_);
v_arg_2407_ = lean_ctor_get(v_x_2398_, 1);
lean_inc_ref(v_arg_2407_);
lean_dec_ref_known(v_x_2398_, 2);
v___x_2408_ = lean_array_set(v_x_2399_, v_x_2400_, v_arg_2407_);
v___x_2409_ = lean_unsigned_to_nat(1u);
v___x_2410_ = lean_nat_sub(v_x_2400_, v___x_2409_);
lean_dec(v_x_2400_);
v_x_2398_ = v_fn_2406_;
v_x_2399_ = v___x_2408_;
v_x_2400_ = v___x_2410_;
goto _start;
}
else
{
uint8_t v_depElim_2412_; lean_object* v_paramsPos_2413_; lean_object* v___x_2414_; 
lean_dec(v_x_2400_);
lean_dec_ref(v_x_2398_);
v_depElim_2412_ = lean_ctor_get_uint8(v_a_2392_, sizeof(void*)*8);
v_paramsPos_2413_ = lean_ctor_get(v_a_2392_, 5);
lean_inc(v_paramsPos_2413_);
lean_inc(v_mvarId_2394_);
lean_inc_ref(v_val_2393_);
v___x_2414_ = l_List_forM___at___00Lean_MVarId_induction_spec__0(v_x_2399_, v_val_2393_, v_mvarId_2394_, v_paramsPos_2413_, v___y_2401_, v___y_2402_, v___y_2403_, v___y_2404_);
lean_dec_ref(v_x_2399_);
if (lean_obj_tag(v___x_2414_) == 0)
{
lean_object* v___x_2415_; lean_object* v___y_2417_; lean_object* v___y_2418_; lean_object* v___y_2419_; lean_object* v___y_2420_; lean_object* v___y_2421_; lean_object* v___y_2422_; lean_object* v___y_2423_; size_t v___y_2424_; lean_object* v___y_2425_; lean_object* v___y_2426_; lean_object* v___y_2427_; lean_object* v___y_2428_; lean_object* v___x_2433_; 
lean_dec_ref_known(v___x_2414_, 1);
v___x_2415_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1));
lean_inc_ref(v_a_2392_);
lean_inc(v_mvarId_2394_);
v___x_2433_ = l_Lean_Meta_getMajorTypeIndices(v_mvarId_2394_, v___x_2415_, v_a_2392_, v_val_2393_, v___y_2401_, v___y_2402_, v___y_2403_, v___y_2404_);
if (lean_obj_tag(v___x_2433_) == 0)
{
lean_object* v_a_2434_; lean_object* v___x_2435_; 
v_a_2434_ = lean_ctor_get(v___x_2433_, 0);
lean_inc(v_a_2434_);
lean_dec_ref_known(v___x_2433_, 1);
lean_inc(v_mvarId_2394_);
v___x_2435_ = l_Lean_MVarId_getType(v_mvarId_2394_, v___y_2401_, v___y_2402_, v___y_2403_, v___y_2404_);
if (lean_obj_tag(v___x_2435_) == 0)
{
lean_object* v_a_2436_; lean_object* v_cls_2437_; lean_object* v___y_2439_; lean_object* v___y_2440_; lean_object* v___y_2441_; lean_object* v___y_2442_; 
v_a_2436_ = lean_ctor_get(v___x_2435_, 0);
lean_inc(v_a_2436_);
lean_dec_ref_known(v___x_2435_, 1);
v_cls_2437_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__2));
if (v_depElim_2412_ == 0)
{
lean_object* v___x_2525_; lean_object* v_a_2526_; lean_object* v___x_2528_; uint8_t v_isShared_2529_; uint8_t v_isSharedCheck_2548_; 
lean_inc(v_majorFVarId_2395_);
v___x_2525_ = l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2___redArg(v_a_2436_, v_majorFVarId_2395_, v___y_2402_);
v_a_2526_ = lean_ctor_get(v___x_2525_, 0);
v_isSharedCheck_2548_ = !lean_is_exclusive(v___x_2525_);
if (v_isSharedCheck_2548_ == 0)
{
v___x_2528_ = v___x_2525_;
v_isShared_2529_ = v_isSharedCheck_2548_;
goto v_resetjp_2527_;
}
else
{
lean_inc(v_a_2526_);
lean_dec(v___x_2525_);
v___x_2528_ = lean_box(0);
v_isShared_2529_ = v_isSharedCheck_2548_;
goto v_resetjp_2527_;
}
v_resetjp_2527_:
{
uint8_t v___x_2530_; 
v___x_2530_ = lean_unbox(v_a_2526_);
lean_dec(v_a_2526_);
if (v___x_2530_ == 0)
{
lean_del_object(v___x_2528_);
lean_dec(v_recursorName_2397_);
v___y_2439_ = v___y_2401_;
v___y_2440_ = v___y_2402_;
v___y_2441_ = v___y_2403_;
v___y_2442_ = v___y_2404_;
goto v___jp_2438_;
}
else
{
lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2537_; 
v___x_2531_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__3, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__3);
v___x_2532_ = l_Lean_MessageData_ofName(v_recursorName_2397_);
v___x_2533_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2533_, 0, v___x_2531_);
lean_ctor_set(v___x_2533_, 1, v___x_2532_);
v___x_2534_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__5, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__5_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__5);
v___x_2535_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2535_, 0, v___x_2533_);
lean_ctor_set(v___x_2535_, 1, v___x_2534_);
if (v_isShared_2529_ == 0)
{
lean_ctor_set_tag(v___x_2528_, 1);
lean_ctor_set(v___x_2528_, 0, v___x_2535_);
v___x_2537_ = v___x_2528_;
goto v_reusejp_2536_;
}
else
{
lean_object* v_reuseFailAlloc_2547_; 
v_reuseFailAlloc_2547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2547_, 0, v___x_2535_);
v___x_2537_ = v_reuseFailAlloc_2547_;
goto v_reusejp_2536_;
}
v_reusejp_2536_:
{
lean_object* v___x_2538_; 
lean_inc(v_mvarId_2394_);
v___x_2538_ = l_Lean_Meta_throwTacticEx___redArg(v___x_2415_, v_mvarId_2394_, v___x_2537_, v___y_2401_, v___y_2402_, v___y_2403_, v___y_2404_);
if (lean_obj_tag(v___x_2538_) == 0)
{
lean_dec_ref_known(v___x_2538_, 1);
v___y_2439_ = v___y_2401_;
v___y_2440_ = v___y_2402_;
v___y_2441_ = v___y_2403_;
v___y_2442_ = v___y_2404_;
goto v___jp_2438_;
}
else
{
lean_object* v_a_2539_; lean_object* v___x_2541_; uint8_t v_isShared_2542_; uint8_t v_isSharedCheck_2546_; 
lean_dec(v_a_2434_);
lean_dec_ref(v_givenNames_2396_);
lean_dec(v_majorFVarId_2395_);
lean_dec(v_mvarId_2394_);
lean_dec_ref(v_a_2392_);
v_a_2539_ = lean_ctor_get(v___x_2538_, 0);
v_isSharedCheck_2546_ = !lean_is_exclusive(v___x_2538_);
if (v_isSharedCheck_2546_ == 0)
{
v___x_2541_ = v___x_2538_;
v_isShared_2542_ = v_isSharedCheck_2546_;
goto v_resetjp_2540_;
}
else
{
lean_inc(v_a_2539_);
lean_dec(v___x_2538_);
v___x_2541_ = lean_box(0);
v_isShared_2542_ = v_isSharedCheck_2546_;
goto v_resetjp_2540_;
}
v_resetjp_2540_:
{
lean_object* v___x_2544_; 
if (v_isShared_2542_ == 0)
{
v___x_2544_ = v___x_2541_;
goto v_reusejp_2543_;
}
else
{
lean_object* v_reuseFailAlloc_2545_; 
v_reuseFailAlloc_2545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2545_, 0, v_a_2539_);
v___x_2544_ = v_reuseFailAlloc_2545_;
goto v_reusejp_2543_;
}
v_reusejp_2543_:
{
return v___x_2544_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_2436_);
lean_dec(v_recursorName_2397_);
v___y_2439_ = v___y_2401_;
v___y_2440_ = v___y_2402_;
v___y_2441_ = v___y_2403_;
v___y_2442_ = v___y_2404_;
goto v___jp_2438_;
}
v___jp_2438_:
{
size_t v_sz_2443_; size_t v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; uint8_t v___x_2447_; uint8_t v___x_2448_; lean_object* v___x_2449_; 
v_sz_2443_ = lean_array_size(v_a_2434_);
v___x_2444_ = ((size_t)0ULL);
lean_inc(v_a_2434_);
v___x_2445_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_induction_spec__1(v_sz_2443_, v___x_2444_, v_a_2434_);
lean_inc(v_majorFVarId_2395_);
v___x_2446_ = lean_array_push(v___x_2445_, v_majorFVarId_2395_);
v___x_2447_ = 1;
v___x_2448_ = 0;
v___x_2449_ = l_Lean_MVarId_revert(v_mvarId_2394_, v___x_2446_, v___x_2447_, v___x_2448_, v___y_2439_, v___y_2440_, v___y_2441_, v___y_2442_);
if (lean_obj_tag(v___x_2449_) == 0)
{
lean_object* v_a_2450_; lean_object* v_fst_2451_; lean_object* v_snd_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; 
v_a_2450_ = lean_ctor_get(v___x_2449_, 0);
lean_inc(v_a_2450_);
lean_dec_ref_known(v___x_2449_, 1);
v_fst_2451_ = lean_ctor_get(v_a_2450_, 0);
lean_inc(v_fst_2451_);
v_snd_2452_ = lean_ctor_get(v_a_2450_, 1);
lean_inc(v_snd_2452_);
lean_dec(v_a_2450_);
v___x_2453_ = lean_array_get_size(v_a_2434_);
v___x_2454_ = lean_box(0);
v___x_2455_ = l_Lean_Meta_introNCore(v_snd_2452_, v___x_2453_, v___x_2454_, v___x_2448_, v___x_2447_, v___y_2439_, v___y_2440_, v___y_2441_, v___y_2442_);
if (lean_obj_tag(v___x_2455_) == 0)
{
lean_object* v_a_2456_; lean_object* v_fst_2457_; lean_object* v_snd_2458_; lean_object* v___x_2459_; 
v_a_2456_ = lean_ctor_get(v___x_2455_, 0);
lean_inc(v_a_2456_);
lean_dec_ref_known(v___x_2455_, 1);
v_fst_2457_ = lean_ctor_get(v_a_2456_, 0);
lean_inc(v_fst_2457_);
v_snd_2458_ = lean_ctor_get(v_a_2456_, 1);
lean_inc(v_snd_2458_);
lean_dec(v_a_2456_);
v___x_2459_ = l_Lean_Meta_intro1Core(v_snd_2458_, v___x_2447_, v___y_2439_, v___y_2440_, v___y_2441_, v___y_2442_);
if (lean_obj_tag(v___x_2459_) == 0)
{
lean_object* v_a_2460_; lean_object* v_fst_2461_; lean_object* v_snd_2462_; lean_object* v___x_2464_; uint8_t v_isShared_2465_; uint8_t v_isSharedCheck_2500_; 
v_a_2460_ = lean_ctor_get(v___x_2459_, 0);
lean_inc(v_a_2460_);
lean_dec_ref_known(v___x_2459_, 1);
v_fst_2461_ = lean_ctor_get(v_a_2460_, 0);
v_snd_2462_ = lean_ctor_get(v_a_2460_, 1);
v_isSharedCheck_2500_ = !lean_is_exclusive(v_a_2460_);
if (v_isSharedCheck_2500_ == 0)
{
v___x_2464_ = v_a_2460_;
v_isShared_2465_ = v_isSharedCheck_2500_;
goto v_resetjp_2463_;
}
else
{
lean_inc(v_snd_2462_);
lean_inc(v_fst_2461_);
lean_dec(v_a_2460_);
v___x_2464_ = lean_box(0);
v_isShared_2465_ = v_isSharedCheck_2500_;
goto v_resetjp_2463_;
}
v_resetjp_2463_:
{
lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2471_; 
v___x_2466_ = lean_box(0);
lean_inc(v_fst_2461_);
v___x_2467_ = l_Lean_mkFVar(v_fst_2461_);
lean_inc_ref(v___x_2467_);
v___x_2468_ = l_Lean_Meta_FVarSubst_insert(v___x_2466_, v_majorFVarId_2395_, v___x_2467_);
v___x_2469_ = lean_unsigned_to_nat(0u);
if (v_isShared_2465_ == 0)
{
lean_ctor_set(v___x_2464_, 1, v___x_2469_);
lean_ctor_set(v___x_2464_, 0, v___x_2468_);
v___x_2471_ = v___x_2464_;
goto v_reusejp_2470_;
}
else
{
lean_object* v_reuseFailAlloc_2499_; 
v_reuseFailAlloc_2499_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2499_, 0, v___x_2468_);
lean_ctor_set(v_reuseFailAlloc_2499_, 1, v___x_2469_);
v___x_2471_ = v_reuseFailAlloc_2499_;
goto v_reusejp_2470_;
}
v_reusejp_2470_:
{
lean_object* v___x_2472_; lean_object* v_options_2473_; uint8_t v_hasTrace_2474_; 
v___x_2472_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_induction_spec__2(v_fst_2457_, v_a_2434_, v_sz_2443_, v___x_2444_, v___x_2471_);
lean_dec(v_a_2434_);
v_options_2473_ = lean_ctor_get(v___y_2441_, 2);
v_hasTrace_2474_ = lean_ctor_get_uint8(v_options_2473_, sizeof(void*)*1);
if (v_hasTrace_2474_ == 0)
{
lean_object* v_fst_2475_; 
v_fst_2475_ = lean_ctor_get(v___x_2472_, 0);
lean_inc(v_fst_2475_);
lean_dec_ref(v___x_2472_);
lean_inc(v_snd_2462_);
v___y_2417_ = v_snd_2462_;
v___y_2418_ = v_fst_2475_;
v___y_2419_ = v_fst_2461_;
v___y_2420_ = v___x_2467_;
v___y_2421_ = v_fst_2451_;
v___y_2422_ = v_snd_2462_;
v___y_2423_ = v_fst_2457_;
v___y_2424_ = v___x_2444_;
v___y_2425_ = v___y_2439_;
v___y_2426_ = v___y_2440_;
v___y_2427_ = v___y_2441_;
v___y_2428_ = v___y_2442_;
goto v___jp_2416_;
}
else
{
lean_object* v_fst_2476_; lean_object* v___x_2478_; uint8_t v_isShared_2479_; uint8_t v_isSharedCheck_2497_; 
v_fst_2476_ = lean_ctor_get(v___x_2472_, 0);
v_isSharedCheck_2497_ = !lean_is_exclusive(v___x_2472_);
if (v_isSharedCheck_2497_ == 0)
{
lean_object* v_unused_2498_; 
v_unused_2498_ = lean_ctor_get(v___x_2472_, 1);
lean_dec(v_unused_2498_);
v___x_2478_ = v___x_2472_;
v_isShared_2479_ = v_isSharedCheck_2497_;
goto v_resetjp_2477_;
}
else
{
lean_inc(v_fst_2476_);
lean_dec(v___x_2472_);
v___x_2478_ = lean_box(0);
v_isShared_2479_ = v_isSharedCheck_2497_;
goto v_resetjp_2477_;
}
v_resetjp_2477_:
{
lean_object* v_inheritedTraceOptions_2480_; lean_object* v___x_2481_; uint8_t v___x_2482_; 
v_inheritedTraceOptions_2480_ = lean_ctor_get(v___y_2441_, 13);
v___x_2481_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5);
v___x_2482_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2480_, v_options_2473_, v___x_2481_);
if (v___x_2482_ == 0)
{
lean_del_object(v___x_2478_);
lean_inc(v_snd_2462_);
v___y_2417_ = v_snd_2462_;
v___y_2418_ = v_fst_2476_;
v___y_2419_ = v_fst_2461_;
v___y_2420_ = v___x_2467_;
v___y_2421_ = v_fst_2451_;
v___y_2422_ = v_snd_2462_;
v___y_2423_ = v_fst_2457_;
v___y_2424_ = v___x_2444_;
v___y_2425_ = v___y_2439_;
v___y_2426_ = v___y_2440_;
v___y_2427_ = v___y_2441_;
v___y_2428_ = v___y_2442_;
goto v___jp_2416_;
}
else
{
lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2486_; 
v___x_2483_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__1);
lean_inc(v_snd_2462_);
v___x_2484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2484_, 0, v_snd_2462_);
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
v___x_2487_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1(v_cls_2437_, v___x_2486_, v___y_2439_, v___y_2440_, v___y_2441_, v___y_2442_);
if (lean_obj_tag(v___x_2487_) == 0)
{
lean_dec_ref_known(v___x_2487_, 1);
lean_inc(v_snd_2462_);
v___y_2417_ = v_snd_2462_;
v___y_2418_ = v_fst_2476_;
v___y_2419_ = v_fst_2461_;
v___y_2420_ = v___x_2467_;
v___y_2421_ = v_fst_2451_;
v___y_2422_ = v_snd_2462_;
v___y_2423_ = v_fst_2457_;
v___y_2424_ = v___x_2444_;
v___y_2425_ = v___y_2439_;
v___y_2426_ = v___y_2440_;
v___y_2427_ = v___y_2441_;
v___y_2428_ = v___y_2442_;
goto v___jp_2416_;
}
else
{
lean_object* v_a_2488_; lean_object* v___x_2490_; uint8_t v_isShared_2491_; uint8_t v_isSharedCheck_2495_; 
lean_dec(v_fst_2476_);
lean_dec_ref(v___x_2467_);
lean_dec(v_snd_2462_);
lean_dec(v_fst_2461_);
lean_dec(v_fst_2457_);
lean_dec(v_fst_2451_);
lean_dec_ref(v_givenNames_2396_);
lean_dec_ref(v_a_2392_);
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
lean_dec(v_fst_2457_);
lean_dec(v_fst_2451_);
lean_dec(v_a_2434_);
lean_dec_ref(v_givenNames_2396_);
lean_dec(v_majorFVarId_2395_);
lean_dec_ref(v_a_2392_);
v_a_2501_ = lean_ctor_get(v___x_2459_, 0);
v_isSharedCheck_2508_ = !lean_is_exclusive(v___x_2459_);
if (v_isSharedCheck_2508_ == 0)
{
v___x_2503_ = v___x_2459_;
v_isShared_2504_ = v_isSharedCheck_2508_;
goto v_resetjp_2502_;
}
else
{
lean_inc(v_a_2501_);
lean_dec(v___x_2459_);
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
lean_dec(v_fst_2451_);
lean_dec(v_a_2434_);
lean_dec_ref(v_givenNames_2396_);
lean_dec(v_majorFVarId_2395_);
lean_dec_ref(v_a_2392_);
v_a_2509_ = lean_ctor_get(v___x_2455_, 0);
v_isSharedCheck_2516_ = !lean_is_exclusive(v___x_2455_);
if (v_isSharedCheck_2516_ == 0)
{
v___x_2511_ = v___x_2455_;
v_isShared_2512_ = v_isSharedCheck_2516_;
goto v_resetjp_2510_;
}
else
{
lean_inc(v_a_2509_);
lean_dec(v___x_2455_);
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
lean_dec(v_a_2434_);
lean_dec_ref(v_givenNames_2396_);
lean_dec(v_majorFVarId_2395_);
lean_dec_ref(v_a_2392_);
v_a_2517_ = lean_ctor_get(v___x_2449_, 0);
v_isSharedCheck_2524_ = !lean_is_exclusive(v___x_2449_);
if (v_isSharedCheck_2524_ == 0)
{
v___x_2519_ = v___x_2449_;
v_isShared_2520_ = v_isSharedCheck_2524_;
goto v_resetjp_2518_;
}
else
{
lean_inc(v_a_2517_);
lean_dec(v___x_2449_);
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
lean_object* v_a_2549_; lean_object* v___x_2551_; uint8_t v_isShared_2552_; uint8_t v_isSharedCheck_2556_; 
lean_dec(v_a_2434_);
lean_dec(v_recursorName_2397_);
lean_dec_ref(v_givenNames_2396_);
lean_dec(v_majorFVarId_2395_);
lean_dec(v_mvarId_2394_);
lean_dec_ref(v_a_2392_);
v_a_2549_ = lean_ctor_get(v___x_2435_, 0);
v_isSharedCheck_2556_ = !lean_is_exclusive(v___x_2435_);
if (v_isSharedCheck_2556_ == 0)
{
v___x_2551_ = v___x_2435_;
v_isShared_2552_ = v_isSharedCheck_2556_;
goto v_resetjp_2550_;
}
else
{
lean_inc(v_a_2549_);
lean_dec(v___x_2435_);
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
lean_dec(v_recursorName_2397_);
lean_dec_ref(v_givenNames_2396_);
lean_dec(v_majorFVarId_2395_);
lean_dec(v_mvarId_2394_);
lean_dec_ref(v_a_2392_);
v_a_2557_ = lean_ctor_get(v___x_2433_, 0);
v_isSharedCheck_2564_ = !lean_is_exclusive(v___x_2433_);
if (v_isSharedCheck_2564_ == 0)
{
v___x_2559_ = v___x_2433_;
v_isShared_2560_ = v_isSharedCheck_2564_;
goto v_resetjp_2558_;
}
else
{
lean_inc(v_a_2557_);
lean_dec(v___x_2433_);
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
v___jp_2416_:
{
size_t v_sz_2429_; lean_object* v___x_2430_; lean_object* v___f_2431_; lean_object* v___x_2432_; 
v_sz_2429_ = lean_array_size(v___y_2423_);
v___x_2430_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__3(v_sz_2429_, v___y_2424_, v___y_2423_);
v___f_2431_ = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4___lam__0___boxed), 14, 9);
lean_closure_set(v___f_2431_, 0, v___y_2417_);
lean_closure_set(v___f_2431_, 1, v___x_2415_);
lean_closure_set(v___f_2431_, 2, v___y_2419_);
lean_closure_set(v___f_2431_, 3, v_a_2392_);
lean_closure_set(v___f_2431_, 4, v___x_2430_);
lean_closure_set(v___f_2431_, 5, v_givenNames_2396_);
lean_closure_set(v___f_2431_, 6, v___y_2421_);
lean_closure_set(v___f_2431_, 7, v___y_2420_);
lean_closure_set(v___f_2431_, 8, v___y_2418_);
v___x_2432_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___redArg(v___y_2422_, v___f_2431_, v___y_2425_, v___y_2426_, v___y_2427_, v___y_2428_);
return v___x_2432_;
}
}
else
{
lean_object* v_a_2565_; lean_object* v___x_2567_; uint8_t v_isShared_2568_; uint8_t v_isSharedCheck_2572_; 
lean_dec(v_recursorName_2397_);
lean_dec_ref(v_givenNames_2396_);
lean_dec(v_majorFVarId_2395_);
lean_dec(v_mvarId_2394_);
lean_dec_ref(v_val_2393_);
lean_dec_ref(v_a_2392_);
v_a_2565_ = lean_ctor_get(v___x_2414_, 0);
v_isSharedCheck_2572_ = !lean_is_exclusive(v___x_2414_);
if (v_isSharedCheck_2572_ == 0)
{
v___x_2567_ = v___x_2414_;
v_isShared_2568_ = v_isSharedCheck_2572_;
goto v_resetjp_2566_;
}
else
{
lean_inc(v_a_2565_);
lean_dec(v___x_2414_);
v___x_2567_ = lean_box(0);
v_isShared_2568_ = v_isSharedCheck_2572_;
goto v_resetjp_2566_;
}
v_resetjp_2566_:
{
lean_object* v___x_2570_; 
if (v_isShared_2568_ == 0)
{
v___x_2570_ = v___x_2567_;
goto v_reusejp_2569_;
}
else
{
lean_object* v_reuseFailAlloc_2571_; 
v_reuseFailAlloc_2571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2571_, 0, v_a_2565_);
v___x_2570_ = v_reuseFailAlloc_2571_;
goto v_reusejp_2569_;
}
v_reusejp_2569_:
{
return v___x_2570_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___boxed(lean_object* v_a_2573_, lean_object* v_val_2574_, lean_object* v_mvarId_2575_, lean_object* v_majorFVarId_2576_, lean_object* v_givenNames_2577_, lean_object* v_recursorName_2578_, lean_object* v_x_2579_, lean_object* v_x_2580_, lean_object* v_x_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_){
_start:
{
lean_object* v_res_2587_; 
v_res_2587_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4(v_a_2573_, v_val_2574_, v_mvarId_2575_, v_majorFVarId_2576_, v_givenNames_2577_, v_recursorName_2578_, v_x_2579_, v_x_2580_, v_x_2581_, v___y_2582_, v___y_2583_, v___y_2584_, v___y_2585_);
lean_dec(v___y_2585_);
lean_dec_ref(v___y_2584_);
lean_dec(v___y_2583_);
lean_dec_ref(v___y_2582_);
return v_res_2587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4(lean_object* v_val_2588_, lean_object* v_mvarId_2589_, lean_object* v_a_2590_, lean_object* v_majorFVarId_2591_, lean_object* v_givenNames_2592_, lean_object* v_recursorName_2593_, lean_object* v_x_2594_, lean_object* v_x_2595_, lean_object* v_x_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_){
_start:
{
if (lean_obj_tag(v_x_2594_) == 5)
{
lean_object* v_fn_2602_; lean_object* v_arg_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; 
v_fn_2602_ = lean_ctor_get(v_x_2594_, 0);
lean_inc_ref(v_fn_2602_);
v_arg_2603_ = lean_ctor_get(v_x_2594_, 1);
lean_inc_ref(v_arg_2603_);
lean_dec_ref_known(v_x_2594_, 2);
v___x_2604_ = lean_array_set(v_x_2595_, v_x_2596_, v_arg_2603_);
v___x_2605_ = lean_unsigned_to_nat(1u);
v___x_2606_ = lean_nat_sub(v_x_2596_, v___x_2605_);
v___x_2607_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4(v_a_2590_, v_val_2588_, v_mvarId_2589_, v_majorFVarId_2591_, v_givenNames_2592_, v_recursorName_2593_, v_fn_2602_, v___x_2604_, v___x_2606_, v___y_2597_, v___y_2598_, v___y_2599_, v___y_2600_);
return v___x_2607_;
}
else
{
uint8_t v_depElim_2608_; lean_object* v_paramsPos_2609_; lean_object* v___x_2610_; 
lean_dec_ref(v_x_2594_);
v_depElim_2608_ = lean_ctor_get_uint8(v_a_2590_, sizeof(void*)*8);
v_paramsPos_2609_ = lean_ctor_get(v_a_2590_, 5);
lean_inc(v_paramsPos_2609_);
lean_inc(v_mvarId_2589_);
lean_inc_ref(v_val_2588_);
v___x_2610_ = l_List_forM___at___00Lean_MVarId_induction_spec__0(v_x_2595_, v_val_2588_, v_mvarId_2589_, v_paramsPos_2609_, v___y_2597_, v___y_2598_, v___y_2599_, v___y_2600_);
lean_dec_ref(v_x_2595_);
if (lean_obj_tag(v___x_2610_) == 0)
{
lean_object* v___x_2611_; lean_object* v___y_2613_; lean_object* v___y_2614_; lean_object* v___y_2615_; lean_object* v___y_2616_; lean_object* v___y_2617_; size_t v___y_2618_; lean_object* v___y_2619_; lean_object* v___y_2620_; lean_object* v___y_2621_; lean_object* v___y_2622_; lean_object* v___y_2623_; lean_object* v___y_2624_; lean_object* v___x_2629_; 
lean_dec_ref_known(v___x_2610_, 1);
v___x_2611_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1));
lean_inc_ref(v_a_2590_);
lean_inc(v_mvarId_2589_);
v___x_2629_ = l_Lean_Meta_getMajorTypeIndices(v_mvarId_2589_, v___x_2611_, v_a_2590_, v_val_2588_, v___y_2597_, v___y_2598_, v___y_2599_, v___y_2600_);
if (lean_obj_tag(v___x_2629_) == 0)
{
lean_object* v_a_2630_; lean_object* v___x_2631_; 
v_a_2630_ = lean_ctor_get(v___x_2629_, 0);
lean_inc(v_a_2630_);
lean_dec_ref_known(v___x_2629_, 1);
lean_inc(v_mvarId_2589_);
v___x_2631_ = l_Lean_MVarId_getType(v_mvarId_2589_, v___y_2597_, v___y_2598_, v___y_2599_, v___y_2600_);
if (lean_obj_tag(v___x_2631_) == 0)
{
lean_object* v_a_2632_; lean_object* v_cls_2633_; lean_object* v___y_2635_; lean_object* v___y_2636_; lean_object* v___y_2637_; lean_object* v___y_2638_; 
v_a_2632_ = lean_ctor_get(v___x_2631_, 0);
lean_inc(v_a_2632_);
lean_dec_ref_known(v___x_2631_, 1);
v_cls_2633_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__2));
if (v_depElim_2608_ == 0)
{
lean_object* v___x_2721_; lean_object* v_a_2722_; lean_object* v___x_2724_; uint8_t v_isShared_2725_; uint8_t v_isSharedCheck_2744_; 
lean_inc(v_majorFVarId_2591_);
v___x_2721_ = l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2___redArg(v_a_2632_, v_majorFVarId_2591_, v___y_2598_);
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
lean_dec(v_recursorName_2593_);
v___y_2635_ = v___y_2597_;
v___y_2636_ = v___y_2598_;
v___y_2637_ = v___y_2599_;
v___y_2638_ = v___y_2600_;
goto v___jp_2634_;
}
else
{
lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v___x_2733_; 
v___x_2727_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__3, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__3);
v___x_2728_ = l_Lean_MessageData_ofName(v_recursorName_2593_);
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
lean_inc(v_mvarId_2589_);
v___x_2734_ = l_Lean_Meta_throwTacticEx___redArg(v___x_2611_, v_mvarId_2589_, v___x_2733_, v___y_2597_, v___y_2598_, v___y_2599_, v___y_2600_);
if (lean_obj_tag(v___x_2734_) == 0)
{
lean_dec_ref_known(v___x_2734_, 1);
v___y_2635_ = v___y_2597_;
v___y_2636_ = v___y_2598_;
v___y_2637_ = v___y_2599_;
v___y_2638_ = v___y_2600_;
goto v___jp_2634_;
}
else
{
lean_object* v_a_2735_; lean_object* v___x_2737_; uint8_t v_isShared_2738_; uint8_t v_isSharedCheck_2742_; 
lean_dec(v_a_2630_);
lean_dec_ref(v_givenNames_2592_);
lean_dec(v_majorFVarId_2591_);
lean_dec_ref(v_a_2590_);
lean_dec(v_mvarId_2589_);
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
lean_dec(v_a_2632_);
lean_dec(v_recursorName_2593_);
v___y_2635_ = v___y_2597_;
v___y_2636_ = v___y_2598_;
v___y_2637_ = v___y_2599_;
v___y_2638_ = v___y_2600_;
goto v___jp_2634_;
}
v___jp_2634_:
{
size_t v_sz_2639_; size_t v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; uint8_t v___x_2643_; uint8_t v___x_2644_; lean_object* v___x_2645_; 
v_sz_2639_ = lean_array_size(v_a_2630_);
v___x_2640_ = ((size_t)0ULL);
lean_inc(v_a_2630_);
v___x_2641_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_induction_spec__1(v_sz_2639_, v___x_2640_, v_a_2630_);
lean_inc(v_majorFVarId_2591_);
v___x_2642_ = lean_array_push(v___x_2641_, v_majorFVarId_2591_);
v___x_2643_ = 1;
v___x_2644_ = 0;
v___x_2645_ = l_Lean_MVarId_revert(v_mvarId_2589_, v___x_2642_, v___x_2643_, v___x_2644_, v___y_2635_, v___y_2636_, v___y_2637_, v___y_2638_);
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
v___x_2649_ = lean_array_get_size(v_a_2630_);
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
lean_object* v_a_2656_; lean_object* v_fst_2657_; lean_object* v_snd_2658_; lean_object* v___x_2660_; uint8_t v_isShared_2661_; uint8_t v_isSharedCheck_2696_; 
v_a_2656_ = lean_ctor_get(v___x_2655_, 0);
lean_inc(v_a_2656_);
lean_dec_ref_known(v___x_2655_, 1);
v_fst_2657_ = lean_ctor_get(v_a_2656_, 0);
v_snd_2658_ = lean_ctor_get(v_a_2656_, 1);
v_isSharedCheck_2696_ = !lean_is_exclusive(v_a_2656_);
if (v_isSharedCheck_2696_ == 0)
{
v___x_2660_ = v_a_2656_;
v_isShared_2661_ = v_isSharedCheck_2696_;
goto v_resetjp_2659_;
}
else
{
lean_inc(v_snd_2658_);
lean_inc(v_fst_2657_);
lean_dec(v_a_2656_);
v___x_2660_ = lean_box(0);
v_isShared_2661_ = v_isSharedCheck_2696_;
goto v_resetjp_2659_;
}
v_resetjp_2659_:
{
lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2667_; 
v___x_2662_ = lean_box(0);
lean_inc(v_fst_2657_);
v___x_2663_ = l_Lean_mkFVar(v_fst_2657_);
lean_inc_ref(v___x_2663_);
v___x_2664_ = l_Lean_Meta_FVarSubst_insert(v___x_2662_, v_majorFVarId_2591_, v___x_2663_);
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
lean_object* v_reuseFailAlloc_2695_; 
v_reuseFailAlloc_2695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2695_, 0, v___x_2664_);
lean_ctor_set(v_reuseFailAlloc_2695_, 1, v___x_2665_);
v___x_2667_ = v_reuseFailAlloc_2695_;
goto v_reusejp_2666_;
}
v_reusejp_2666_:
{
lean_object* v___x_2668_; lean_object* v_options_2669_; uint8_t v_hasTrace_2670_; 
v___x_2668_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_induction_spec__2(v_fst_2653_, v_a_2630_, v_sz_2639_, v___x_2640_, v___x_2667_);
lean_dec(v_a_2630_);
v_options_2669_ = lean_ctor_get(v___y_2637_, 2);
v_hasTrace_2670_ = lean_ctor_get_uint8(v_options_2669_, sizeof(void*)*1);
if (v_hasTrace_2670_ == 0)
{
lean_object* v_fst_2671_; 
v_fst_2671_ = lean_ctor_get(v___x_2668_, 0);
lean_inc(v_fst_2671_);
lean_dec_ref(v___x_2668_);
lean_inc(v_snd_2658_);
v___y_2613_ = v_fst_2671_;
v___y_2614_ = v_fst_2647_;
v___y_2615_ = v_snd_2658_;
v___y_2616_ = v_fst_2657_;
v___y_2617_ = v___x_2663_;
v___y_2618_ = v___x_2640_;
v___y_2619_ = v_snd_2658_;
v___y_2620_ = v_fst_2653_;
v___y_2621_ = v___y_2635_;
v___y_2622_ = v___y_2636_;
v___y_2623_ = v___y_2637_;
v___y_2624_ = v___y_2638_;
goto v___jp_2612_;
}
else
{
lean_object* v_fst_2672_; lean_object* v___x_2674_; uint8_t v_isShared_2675_; uint8_t v_isSharedCheck_2693_; 
v_fst_2672_ = lean_ctor_get(v___x_2668_, 0);
v_isSharedCheck_2693_ = !lean_is_exclusive(v___x_2668_);
if (v_isSharedCheck_2693_ == 0)
{
lean_object* v_unused_2694_; 
v_unused_2694_ = lean_ctor_get(v___x_2668_, 1);
lean_dec(v_unused_2694_);
v___x_2674_ = v___x_2668_;
v_isShared_2675_ = v_isSharedCheck_2693_;
goto v_resetjp_2673_;
}
else
{
lean_inc(v_fst_2672_);
lean_dec(v___x_2668_);
v___x_2674_ = lean_box(0);
v_isShared_2675_ = v_isSharedCheck_2693_;
goto v_resetjp_2673_;
}
v_resetjp_2673_:
{
lean_object* v_inheritedTraceOptions_2676_; lean_object* v___x_2677_; uint8_t v___x_2678_; 
v_inheritedTraceOptions_2676_ = lean_ctor_get(v___y_2637_, 13);
v___x_2677_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5);
v___x_2678_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2676_, v_options_2669_, v___x_2677_);
if (v___x_2678_ == 0)
{
lean_del_object(v___x_2674_);
lean_inc(v_snd_2658_);
v___y_2613_ = v_fst_2672_;
v___y_2614_ = v_fst_2647_;
v___y_2615_ = v_snd_2658_;
v___y_2616_ = v_fst_2657_;
v___y_2617_ = v___x_2663_;
v___y_2618_ = v___x_2640_;
v___y_2619_ = v_snd_2658_;
v___y_2620_ = v_fst_2653_;
v___y_2621_ = v___y_2635_;
v___y_2622_ = v___y_2636_;
v___y_2623_ = v___y_2637_;
v___y_2624_ = v___y_2638_;
goto v___jp_2612_;
}
else
{
lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2682_; 
v___x_2679_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__1);
lean_inc(v_snd_2658_);
v___x_2680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2680_, 0, v_snd_2658_);
if (v_isShared_2675_ == 0)
{
lean_ctor_set_tag(v___x_2674_, 7);
lean_ctor_set(v___x_2674_, 1, v___x_2680_);
lean_ctor_set(v___x_2674_, 0, v___x_2679_);
v___x_2682_ = v___x_2674_;
goto v_reusejp_2681_;
}
else
{
lean_object* v_reuseFailAlloc_2692_; 
v_reuseFailAlloc_2692_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2692_, 0, v___x_2679_);
lean_ctor_set(v_reuseFailAlloc_2692_, 1, v___x_2680_);
v___x_2682_ = v_reuseFailAlloc_2692_;
goto v_reusejp_2681_;
}
v_reusejp_2681_:
{
lean_object* v___x_2683_; 
v___x_2683_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1(v_cls_2633_, v___x_2682_, v___y_2635_, v___y_2636_, v___y_2637_, v___y_2638_);
if (lean_obj_tag(v___x_2683_) == 0)
{
lean_dec_ref_known(v___x_2683_, 1);
lean_inc(v_snd_2658_);
v___y_2613_ = v_fst_2672_;
v___y_2614_ = v_fst_2647_;
v___y_2615_ = v_snd_2658_;
v___y_2616_ = v_fst_2657_;
v___y_2617_ = v___x_2663_;
v___y_2618_ = v___x_2640_;
v___y_2619_ = v_snd_2658_;
v___y_2620_ = v_fst_2653_;
v___y_2621_ = v___y_2635_;
v___y_2622_ = v___y_2636_;
v___y_2623_ = v___y_2637_;
v___y_2624_ = v___y_2638_;
goto v___jp_2612_;
}
else
{
lean_object* v_a_2684_; lean_object* v___x_2686_; uint8_t v_isShared_2687_; uint8_t v_isSharedCheck_2691_; 
lean_dec(v_fst_2672_);
lean_dec_ref(v___x_2663_);
lean_dec(v_snd_2658_);
lean_dec(v_fst_2657_);
lean_dec(v_fst_2653_);
lean_dec(v_fst_2647_);
lean_dec_ref(v_givenNames_2592_);
lean_dec_ref(v_a_2590_);
v_a_2684_ = lean_ctor_get(v___x_2683_, 0);
v_isSharedCheck_2691_ = !lean_is_exclusive(v___x_2683_);
if (v_isSharedCheck_2691_ == 0)
{
v___x_2686_ = v___x_2683_;
v_isShared_2687_ = v_isSharedCheck_2691_;
goto v_resetjp_2685_;
}
else
{
lean_inc(v_a_2684_);
lean_dec(v___x_2683_);
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
}
}
}
}
}
}
else
{
lean_object* v_a_2697_; lean_object* v___x_2699_; uint8_t v_isShared_2700_; uint8_t v_isSharedCheck_2704_; 
lean_dec(v_fst_2653_);
lean_dec(v_fst_2647_);
lean_dec(v_a_2630_);
lean_dec_ref(v_givenNames_2592_);
lean_dec(v_majorFVarId_2591_);
lean_dec_ref(v_a_2590_);
v_a_2697_ = lean_ctor_get(v___x_2655_, 0);
v_isSharedCheck_2704_ = !lean_is_exclusive(v___x_2655_);
if (v_isSharedCheck_2704_ == 0)
{
v___x_2699_ = v___x_2655_;
v_isShared_2700_ = v_isSharedCheck_2704_;
goto v_resetjp_2698_;
}
else
{
lean_inc(v_a_2697_);
lean_dec(v___x_2655_);
v___x_2699_ = lean_box(0);
v_isShared_2700_ = v_isSharedCheck_2704_;
goto v_resetjp_2698_;
}
v_resetjp_2698_:
{
lean_object* v___x_2702_; 
if (v_isShared_2700_ == 0)
{
v___x_2702_ = v___x_2699_;
goto v_reusejp_2701_;
}
else
{
lean_object* v_reuseFailAlloc_2703_; 
v_reuseFailAlloc_2703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2703_, 0, v_a_2697_);
v___x_2702_ = v_reuseFailAlloc_2703_;
goto v_reusejp_2701_;
}
v_reusejp_2701_:
{
return v___x_2702_;
}
}
}
}
else
{
lean_object* v_a_2705_; lean_object* v___x_2707_; uint8_t v_isShared_2708_; uint8_t v_isSharedCheck_2712_; 
lean_dec(v_fst_2647_);
lean_dec(v_a_2630_);
lean_dec_ref(v_givenNames_2592_);
lean_dec(v_majorFVarId_2591_);
lean_dec_ref(v_a_2590_);
v_a_2705_ = lean_ctor_get(v___x_2651_, 0);
v_isSharedCheck_2712_ = !lean_is_exclusive(v___x_2651_);
if (v_isSharedCheck_2712_ == 0)
{
v___x_2707_ = v___x_2651_;
v_isShared_2708_ = v_isSharedCheck_2712_;
goto v_resetjp_2706_;
}
else
{
lean_inc(v_a_2705_);
lean_dec(v___x_2651_);
v___x_2707_ = lean_box(0);
v_isShared_2708_ = v_isSharedCheck_2712_;
goto v_resetjp_2706_;
}
v_resetjp_2706_:
{
lean_object* v___x_2710_; 
if (v_isShared_2708_ == 0)
{
v___x_2710_ = v___x_2707_;
goto v_reusejp_2709_;
}
else
{
lean_object* v_reuseFailAlloc_2711_; 
v_reuseFailAlloc_2711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2711_, 0, v_a_2705_);
v___x_2710_ = v_reuseFailAlloc_2711_;
goto v_reusejp_2709_;
}
v_reusejp_2709_:
{
return v___x_2710_;
}
}
}
}
else
{
lean_object* v_a_2713_; lean_object* v___x_2715_; uint8_t v_isShared_2716_; uint8_t v_isSharedCheck_2720_; 
lean_dec(v_a_2630_);
lean_dec_ref(v_givenNames_2592_);
lean_dec(v_majorFVarId_2591_);
lean_dec_ref(v_a_2590_);
v_a_2713_ = lean_ctor_get(v___x_2645_, 0);
v_isSharedCheck_2720_ = !lean_is_exclusive(v___x_2645_);
if (v_isSharedCheck_2720_ == 0)
{
v___x_2715_ = v___x_2645_;
v_isShared_2716_ = v_isSharedCheck_2720_;
goto v_resetjp_2714_;
}
else
{
lean_inc(v_a_2713_);
lean_dec(v___x_2645_);
v___x_2715_ = lean_box(0);
v_isShared_2716_ = v_isSharedCheck_2720_;
goto v_resetjp_2714_;
}
v_resetjp_2714_:
{
lean_object* v___x_2718_; 
if (v_isShared_2716_ == 0)
{
v___x_2718_ = v___x_2715_;
goto v_reusejp_2717_;
}
else
{
lean_object* v_reuseFailAlloc_2719_; 
v_reuseFailAlloc_2719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2719_, 0, v_a_2713_);
v___x_2718_ = v_reuseFailAlloc_2719_;
goto v_reusejp_2717_;
}
v_reusejp_2717_:
{
return v___x_2718_;
}
}
}
}
}
else
{
lean_object* v_a_2745_; lean_object* v___x_2747_; uint8_t v_isShared_2748_; uint8_t v_isSharedCheck_2752_; 
lean_dec(v_a_2630_);
lean_dec(v_recursorName_2593_);
lean_dec_ref(v_givenNames_2592_);
lean_dec(v_majorFVarId_2591_);
lean_dec_ref(v_a_2590_);
lean_dec(v_mvarId_2589_);
v_a_2745_ = lean_ctor_get(v___x_2631_, 0);
v_isSharedCheck_2752_ = !lean_is_exclusive(v___x_2631_);
if (v_isSharedCheck_2752_ == 0)
{
v___x_2747_ = v___x_2631_;
v_isShared_2748_ = v_isSharedCheck_2752_;
goto v_resetjp_2746_;
}
else
{
lean_inc(v_a_2745_);
lean_dec(v___x_2631_);
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
}
else
{
lean_object* v_a_2753_; lean_object* v___x_2755_; uint8_t v_isShared_2756_; uint8_t v_isSharedCheck_2760_; 
lean_dec(v_recursorName_2593_);
lean_dec_ref(v_givenNames_2592_);
lean_dec(v_majorFVarId_2591_);
lean_dec_ref(v_a_2590_);
lean_dec(v_mvarId_2589_);
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
v___jp_2612_:
{
size_t v_sz_2625_; lean_object* v___x_2626_; lean_object* v___f_2627_; lean_object* v___x_2628_; 
v_sz_2625_ = lean_array_size(v___y_2620_);
v___x_2626_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__3(v_sz_2625_, v___y_2618_, v___y_2620_);
v___f_2627_ = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4___lam__0___boxed), 14, 9);
lean_closure_set(v___f_2627_, 0, v___y_2615_);
lean_closure_set(v___f_2627_, 1, v___x_2611_);
lean_closure_set(v___f_2627_, 2, v___y_2616_);
lean_closure_set(v___f_2627_, 3, v_a_2590_);
lean_closure_set(v___f_2627_, 4, v___x_2626_);
lean_closure_set(v___f_2627_, 5, v_givenNames_2592_);
lean_closure_set(v___f_2627_, 6, v___y_2614_);
lean_closure_set(v___f_2627_, 7, v___y_2617_);
lean_closure_set(v___f_2627_, 8, v___y_2613_);
v___x_2628_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___redArg(v___y_2619_, v___f_2627_, v___y_2621_, v___y_2622_, v___y_2623_, v___y_2624_);
return v___x_2628_;
}
}
else
{
lean_object* v_a_2761_; lean_object* v___x_2763_; uint8_t v_isShared_2764_; uint8_t v_isSharedCheck_2768_; 
lean_dec(v_recursorName_2593_);
lean_dec_ref(v_givenNames_2592_);
lean_dec(v_majorFVarId_2591_);
lean_dec_ref(v_a_2590_);
lean_dec(v_mvarId_2589_);
lean_dec_ref(v_val_2588_);
v_a_2761_ = lean_ctor_get(v___x_2610_, 0);
v_isSharedCheck_2768_ = !lean_is_exclusive(v___x_2610_);
if (v_isSharedCheck_2768_ == 0)
{
v___x_2763_ = v___x_2610_;
v_isShared_2764_ = v_isSharedCheck_2768_;
goto v_resetjp_2762_;
}
else
{
lean_inc(v_a_2761_);
lean_dec(v___x_2610_);
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
lean_object* v___y_2799_; lean_object* v___y_2800_; lean_object* v___y_2801_; lean_object* v___y_2802_; lean_object* v_options_2854_; uint8_t v_hasTrace_2855_; 
v_options_2854_ = lean_ctor_get(v___y_2795_, 2);
v_hasTrace_2855_ = lean_ctor_get_uint8(v_options_2854_, sizeof(void*)*1);
if (v_hasTrace_2855_ == 0)
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
lean_object* v_inheritedTraceOptions_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; uint8_t v___x_2859_; 
v_inheritedTraceOptions_2856_ = lean_ctor_get(v___y_2795_, 13);
v___x_2857_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__4));
lean_inc(v_cls_2792_);
v___x_2858_ = l_Lean_Name_append(v___x_2857_, v_cls_2792_);
v___x_2859_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2856_, v_options_2854_, v___x_2858_);
lean_dec(v___x_2858_);
if (v___x_2859_ == 0)
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
lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; 
v___x_2860_ = lean_obj_once(&l_Lean_MVarId_induction___lam__0___closed__1, &l_Lean_MVarId_induction___lam__0___closed__1_once, _init_l_Lean_MVarId_induction___lam__0___closed__1);
lean_inc(v_mvarId_2788_);
v___x_2861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2861_, 0, v_mvarId_2788_);
v___x_2862_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2862_, 0, v___x_2860_);
lean_ctor_set(v___x_2862_, 1, v___x_2861_);
v___x_2863_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1(v_cls_2792_, v___x_2862_, v___y_2793_, v___y_2794_, v___y_2795_, v___y_2796_);
if (lean_obj_tag(v___x_2863_) == 0)
{
lean_dec_ref_known(v___x_2863_, 1);
v___y_2799_ = v___y_2793_;
v___y_2800_ = v___y_2794_;
v___y_2801_ = v___y_2795_;
v___y_2802_ = v___y_2796_;
goto v___jp_2798_;
}
else
{
lean_object* v_a_2864_; lean_object* v___x_2866_; uint8_t v_isShared_2867_; uint8_t v_isSharedCheck_2871_; 
lean_dec_ref(v_givenNames_2791_);
lean_dec(v_recursorName_2790_);
lean_dec(v_majorFVarId_2789_);
lean_dec(v_mvarId_2788_);
lean_dec_ref(v___x_2787_);
v_a_2864_ = lean_ctor_get(v___x_2863_, 0);
v_isSharedCheck_2871_ = !lean_is_exclusive(v___x_2863_);
if (v_isSharedCheck_2871_ == 0)
{
v___x_2866_ = v___x_2863_;
v_isShared_2867_ = v_isSharedCheck_2871_;
goto v_resetjp_2865_;
}
else
{
lean_inc(v_a_2864_);
lean_dec(v___x_2863_);
v___x_2866_ = lean_box(0);
v_isShared_2867_ = v_isSharedCheck_2871_;
goto v_resetjp_2865_;
}
v_resetjp_2865_:
{
lean_object* v___x_2869_; 
if (v_isShared_2867_ == 0)
{
v___x_2869_ = v___x_2866_;
goto v_reusejp_2868_;
}
else
{
lean_object* v_reuseFailAlloc_2870_; 
v_reuseFailAlloc_2870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2870_, 0, v_a_2864_);
v___x_2869_ = v_reuseFailAlloc_2870_;
goto v_reusejp_2868_;
}
v_reusejp_2868_:
{
return v___x_2869_;
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
LEAN_EXPORT lean_object* l_Lean_MVarId_induction___lam__0___boxed(lean_object* v___x_2872_, lean_object* v_mvarId_2873_, lean_object* v_majorFVarId_2874_, lean_object* v_recursorName_2875_, lean_object* v_givenNames_2876_, lean_object* v_cls_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_){
_start:
{
lean_object* v_res_2883_; 
v_res_2883_ = l_Lean_MVarId_induction___lam__0(v___x_2872_, v_mvarId_2873_, v_majorFVarId_2874_, v_recursorName_2875_, v_givenNames_2876_, v_cls_2877_, v___y_2878_, v___y_2879_, v___y_2880_, v___y_2881_);
lean_dec(v___y_2881_);
lean_dec_ref(v___y_2880_);
lean_dec(v___y_2879_);
lean_dec_ref(v___y_2878_);
return v_res_2883_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_induction(lean_object* v_mvarId_2884_, lean_object* v_majorFVarId_2885_, lean_object* v_recursorName_2886_, lean_object* v_givenNames_2887_, lean_object* v_a_2888_, lean_object* v_a_2889_, lean_object* v_a_2890_, lean_object* v_a_2891_){
_start:
{
lean_object* v___x_2893_; lean_object* v_cls_2894_; lean_object* v___f_2895_; lean_object* v___x_2896_; 
v___x_2893_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__0));
v_cls_2894_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__2));
lean_inc(v_mvarId_2884_);
v___f_2895_ = lean_alloc_closure((void*)(l_Lean_MVarId_induction___lam__0___boxed), 11, 6);
lean_closure_set(v___f_2895_, 0, v___x_2893_);
lean_closure_set(v___f_2895_, 1, v_mvarId_2884_);
lean_closure_set(v___f_2895_, 2, v_majorFVarId_2885_);
lean_closure_set(v___f_2895_, 3, v_recursorName_2886_);
lean_closure_set(v___f_2895_, 4, v_givenNames_2887_);
lean_closure_set(v___f_2895_, 5, v_cls_2894_);
v___x_2896_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___redArg(v_mvarId_2884_, v___f_2895_, v_a_2888_, v_a_2889_, v_a_2890_, v_a_2891_);
return v___x_2896_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_induction___boxed(lean_object* v_mvarId_2897_, lean_object* v_majorFVarId_2898_, lean_object* v_recursorName_2899_, lean_object* v_givenNames_2900_, lean_object* v_a_2901_, lean_object* v_a_2902_, lean_object* v_a_2903_, lean_object* v_a_2904_, lean_object* v_a_2905_){
_start:
{
lean_object* v_res_2906_; 
v_res_2906_ = l_Lean_MVarId_induction(v_mvarId_2897_, v_majorFVarId_2898_, v_recursorName_2899_, v_givenNames_2900_, v_a_2901_, v_a_2902_, v_a_2903_, v_a_2904_);
lean_dec(v_a_2904_);
lean_dec_ref(v_a_2903_);
lean_dec(v_a_2902_);
lean_dec_ref(v_a_2901_);
return v_res_2906_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; 
v___x_2954_ = lean_unsigned_to_nat(2221195325u);
v___x_2955_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_));
v___x_2956_ = l_Lean_Name_num___override(v___x_2955_, v___x_2954_);
return v___x_2956_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; 
v___x_2958_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_));
v___x_2959_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_);
v___x_2960_ = l_Lean_Name_str___override(v___x_2959_, v___x_2958_);
return v___x_2960_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; 
v___x_2962_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_));
v___x_2963_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_);
v___x_2964_ = l_Lean_Name_str___override(v___x_2963_, v___x_2962_);
return v___x_2964_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; 
v___x_2965_ = lean_unsigned_to_nat(2u);
v___x_2966_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_);
v___x_2967_ = l_Lean_Name_num___override(v___x_2966_, v___x_2965_);
return v___x_2967_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2969_; uint8_t v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; 
v___x_2969_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__2));
v___x_2970_ = 0;
v___x_2971_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_);
v___x_2972_ = l_Lean_registerTraceClass(v___x_2969_, v___x_2970_, v___x_2971_);
return v___x_2972_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2____boxed(lean_object* v_a_2973_){
_start:
{
lean_object* v_res_2974_; 
v_res_2974_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_();
return v_res_2974_;
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
