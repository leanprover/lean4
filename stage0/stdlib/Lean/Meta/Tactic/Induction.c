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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
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
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l_Lean_Meta_introNCore(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_FVarSubst_insert(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_MVarId_tryClear(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
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
lean_object* v___f_134_; lean_object* v___x_6294__overap_135_; lean_object* v___x_136_; 
v___f_134_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__4___closed__0));
v___x_6294__overap_135_ = lean_panic_fn_borrowed(v___f_134_, v_msg_128_);
lean_inc(v___y_132_);
lean_inc_ref(v___y_131_);
lean_inc(v___y_130_);
lean_inc_ref(v___y_129_);
v___x_136_ = lean_apply_5(v___x_6294__overap_135_, v___y_129_, v___y_130_, v___y_131_, v___y_132_, lean_box(0));
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
size_t v_x_7574__boxed_361_; size_t v_x_7575__boxed_362_; lean_object* v_res_363_; 
v_x_7574__boxed_361_ = lean_unbox_usize(v_x_357_);
lean_dec(v_x_357_);
v_x_7575__boxed_362_ = lean_unbox_usize(v_x_358_);
lean_dec(v_x_358_);
v_res_363_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2___redArg(v_x_356_, v_x_7574__boxed_361_, v_x_7575__boxed_362_, v_x_359_, v_x_360_);
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
lean_object* v___x_398_; lean_object* v___x_400_; 
v___x_398_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0___redArg(v_eAssignment_392_, v_mvarId_371_, v_val_372_);
if (v_isShared_397_ == 0)
{
lean_ctor_set(v___x_396_, 8, v___x_398_);
v___x_400_ = v___x_396_;
goto v_reusejp_399_;
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
lean_ctor_set(v_reuseFailAlloc_407_, 8, v___x_398_);
lean_ctor_set(v_reuseFailAlloc_407_, 9, v_dAssignment_393_);
lean_ctor_set(v_reuseFailAlloc_407_, 10, v_instanceTypedMVars_394_);
v___x_400_ = v_reuseFailAlloc_407_;
goto v_reusejp_399_;
}
v_reusejp_399_:
{
lean_object* v___x_402_; 
if (v_isShared_383_ == 0)
{
lean_ctor_set(v___x_382_, 0, v___x_400_);
v___x_402_ = v___x_382_;
goto v_reusejp_401_;
}
else
{
lean_object* v_reuseFailAlloc_406_; 
v_reuseFailAlloc_406_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_406_, 0, v___x_400_);
lean_ctor_set(v_reuseFailAlloc_406_, 1, v_cache_377_);
lean_ctor_set(v_reuseFailAlloc_406_, 2, v_zetaDeltaFVarIds_378_);
lean_ctor_set(v_reuseFailAlloc_406_, 3, v_postponed_379_);
lean_ctor_set(v_reuseFailAlloc_406_, 4, v_diag_380_);
v___x_402_ = v_reuseFailAlloc_406_;
goto v_reusejp_401_;
}
v_reusejp_401_:
{
lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; 
v___x_403_ = lean_st_ref_put(v___y_373_, v___x_402_);
v___x_404_ = lean_box(0);
v___x_405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_405_, 0, v___x_404_);
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
lean_object* v___x_421_; lean_object* v_env_422_; lean_object* v___x_423_; lean_object* v_mctx_424_; lean_object* v_lctx_425_; lean_object* v_options_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; 
v___x_421_ = lean_st_ref_get(v___y_419_);
v_env_422_ = lean_ctor_get(v___x_421_, 0);
lean_inc_ref(v_env_422_);
lean_dec(v___x_421_);
v___x_423_ = lean_st_ref_get(v___y_417_);
v_mctx_424_ = lean_ctor_get(v___x_423_, 0);
lean_inc_ref(v_mctx_424_);
lean_dec(v___x_423_);
v_lctx_425_ = lean_ctor_get(v___y_416_, 2);
v_options_426_ = lean_ctor_get(v___y_418_, 2);
lean_inc_ref(v_options_426_);
lean_inc_ref(v_lctx_425_);
v___x_427_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_427_, 0, v_env_422_);
lean_ctor_set(v___x_427_, 1, v_mctx_424_);
lean_ctor_set(v___x_427_, 2, v_lctx_425_);
lean_ctor_set(v___x_427_, 3, v_options_426_);
v___x_428_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_428_, 0, v___x_427_);
lean_ctor_set(v___x_428_, 1, v_msgData_415_);
v___x_429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_429_, 0, v___x_428_);
return v___x_429_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1_spec__2___boxed(lean_object* v_msgData_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_){
_start:
{
lean_object* v_res_436_; 
v_res_436_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1_spec__2(v_msgData_430_, v___y_431_, v___y_432_, v___y_433_, v___y_434_);
lean_dec(v___y_434_);
lean_dec_ref(v___y_433_);
lean_dec(v___y_432_);
lean_dec_ref(v___y_431_);
return v_res_436_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1___closed__0(void){
_start:
{
lean_object* v___x_437_; double v___x_438_; 
v___x_437_ = lean_unsigned_to_nat(0u);
v___x_438_ = lean_float_of_nat(v___x_437_);
return v___x_438_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1(lean_object* v_cls_442_, lean_object* v_msg_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_){
_start:
{
lean_object* v_ref_449_; lean_object* v___x_450_; lean_object* v_a_451_; lean_object* v___x_453_; uint8_t v_isShared_454_; uint8_t v_isSharedCheck_495_; 
v_ref_449_ = lean_ctor_get(v___y_446_, 5);
v___x_450_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1_spec__2(v_msg_443_, v___y_444_, v___y_445_, v___y_446_, v___y_447_);
v_a_451_ = lean_ctor_get(v___x_450_, 0);
v_isSharedCheck_495_ = !lean_is_exclusive(v___x_450_);
if (v_isSharedCheck_495_ == 0)
{
v___x_453_ = v___x_450_;
v_isShared_454_ = v_isSharedCheck_495_;
goto v_resetjp_452_;
}
else
{
lean_inc(v_a_451_);
lean_dec(v___x_450_);
v___x_453_ = lean_box(0);
v_isShared_454_ = v_isSharedCheck_495_;
goto v_resetjp_452_;
}
v_resetjp_452_:
{
lean_object* v___x_455_; lean_object* v_traceState_456_; lean_object* v_env_457_; lean_object* v_nextMacroScope_458_; lean_object* v_ngen_459_; lean_object* v_auxDeclNGen_460_; lean_object* v_cache_461_; lean_object* v_messages_462_; lean_object* v_infoState_463_; lean_object* v_snapshotTasks_464_; lean_object* v___x_466_; uint8_t v_isShared_467_; uint8_t v_isSharedCheck_494_; 
v___x_455_ = lean_st_ref_take(v___y_447_);
v_traceState_456_ = lean_ctor_get(v___x_455_, 4);
v_env_457_ = lean_ctor_get(v___x_455_, 0);
v_nextMacroScope_458_ = lean_ctor_get(v___x_455_, 1);
v_ngen_459_ = lean_ctor_get(v___x_455_, 2);
v_auxDeclNGen_460_ = lean_ctor_get(v___x_455_, 3);
v_cache_461_ = lean_ctor_get(v___x_455_, 5);
v_messages_462_ = lean_ctor_get(v___x_455_, 6);
v_infoState_463_ = lean_ctor_get(v___x_455_, 7);
v_snapshotTasks_464_ = lean_ctor_get(v___x_455_, 8);
v_isSharedCheck_494_ = !lean_is_exclusive(v___x_455_);
if (v_isSharedCheck_494_ == 0)
{
v___x_466_ = v___x_455_;
v_isShared_467_ = v_isSharedCheck_494_;
goto v_resetjp_465_;
}
else
{
lean_inc(v_snapshotTasks_464_);
lean_inc(v_infoState_463_);
lean_inc(v_messages_462_);
lean_inc(v_cache_461_);
lean_inc(v_traceState_456_);
lean_inc(v_auxDeclNGen_460_);
lean_inc(v_ngen_459_);
lean_inc(v_nextMacroScope_458_);
lean_inc(v_env_457_);
lean_dec(v___x_455_);
v___x_466_ = lean_box(0);
v_isShared_467_ = v_isSharedCheck_494_;
goto v_resetjp_465_;
}
v_resetjp_465_:
{
uint64_t v_tid_468_; lean_object* v_traces_469_; lean_object* v___x_471_; uint8_t v_isShared_472_; uint8_t v_isSharedCheck_493_; 
v_tid_468_ = lean_ctor_get_uint64(v_traceState_456_, sizeof(void*)*1);
v_traces_469_ = lean_ctor_get(v_traceState_456_, 0);
v_isSharedCheck_493_ = !lean_is_exclusive(v_traceState_456_);
if (v_isSharedCheck_493_ == 0)
{
v___x_471_ = v_traceState_456_;
v_isShared_472_ = v_isSharedCheck_493_;
goto v_resetjp_470_;
}
else
{
lean_inc(v_traces_469_);
lean_dec(v_traceState_456_);
v___x_471_ = lean_box(0);
v_isShared_472_ = v_isSharedCheck_493_;
goto v_resetjp_470_;
}
v_resetjp_470_:
{
lean_object* v___x_473_; double v___x_474_; uint8_t v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_483_; 
v___x_473_ = lean_box(0);
v___x_474_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1___closed__0);
v___x_475_ = 0;
v___x_476_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1___closed__1));
v___x_477_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_477_, 0, v_cls_442_);
lean_ctor_set(v___x_477_, 1, v___x_473_);
lean_ctor_set(v___x_477_, 2, v___x_476_);
lean_ctor_set_float(v___x_477_, sizeof(void*)*3, v___x_474_);
lean_ctor_set_float(v___x_477_, sizeof(void*)*3 + 8, v___x_474_);
lean_ctor_set_uint8(v___x_477_, sizeof(void*)*3 + 16, v___x_475_);
v___x_478_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1___closed__2));
v___x_479_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_479_, 0, v___x_477_);
lean_ctor_set(v___x_479_, 1, v_a_451_);
lean_ctor_set(v___x_479_, 2, v___x_478_);
lean_inc(v_ref_449_);
v___x_480_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_480_, 0, v_ref_449_);
lean_ctor_set(v___x_480_, 1, v___x_479_);
v___x_481_ = l_Lean_PersistentArray_push___redArg(v_traces_469_, v___x_480_);
if (v_isShared_472_ == 0)
{
lean_ctor_set(v___x_471_, 0, v___x_481_);
v___x_483_ = v___x_471_;
goto v_reusejp_482_;
}
else
{
lean_object* v_reuseFailAlloc_492_; 
v_reuseFailAlloc_492_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_492_, 0, v___x_481_);
lean_ctor_set_uint64(v_reuseFailAlloc_492_, sizeof(void*)*1, v_tid_468_);
v___x_483_ = v_reuseFailAlloc_492_;
goto v_reusejp_482_;
}
v_reusejp_482_:
{
lean_object* v___x_485_; 
if (v_isShared_467_ == 0)
{
lean_ctor_set(v___x_466_, 4, v___x_483_);
v___x_485_ = v___x_466_;
goto v_reusejp_484_;
}
else
{
lean_object* v_reuseFailAlloc_491_; 
v_reuseFailAlloc_491_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_491_, 0, v_env_457_);
lean_ctor_set(v_reuseFailAlloc_491_, 1, v_nextMacroScope_458_);
lean_ctor_set(v_reuseFailAlloc_491_, 2, v_ngen_459_);
lean_ctor_set(v_reuseFailAlloc_491_, 3, v_auxDeclNGen_460_);
lean_ctor_set(v_reuseFailAlloc_491_, 4, v___x_483_);
lean_ctor_set(v_reuseFailAlloc_491_, 5, v_cache_461_);
lean_ctor_set(v_reuseFailAlloc_491_, 6, v_messages_462_);
lean_ctor_set(v_reuseFailAlloc_491_, 7, v_infoState_463_);
lean_ctor_set(v_reuseFailAlloc_491_, 8, v_snapshotTasks_464_);
v___x_485_ = v_reuseFailAlloc_491_;
goto v_reusejp_484_;
}
v_reusejp_484_:
{
lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_489_; 
v___x_486_ = lean_st_ref_put(v___y_447_, v___x_485_);
v___x_487_ = lean_box(0);
if (v_isShared_454_ == 0)
{
lean_ctor_set(v___x_453_, 0, v___x_487_);
v___x_489_ = v___x_453_;
goto v_reusejp_488_;
}
else
{
lean_object* v_reuseFailAlloc_490_; 
v_reuseFailAlloc_490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_490_, 0, v___x_487_);
v___x_489_ = v_reuseFailAlloc_490_;
goto v_reusejp_488_;
}
v_reusejp_488_:
{
return v___x_489_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1___boxed(lean_object* v_cls_496_, lean_object* v_msg_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_){
_start:
{
lean_object* v_res_503_; 
v_res_503_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1(v_cls_496_, v_msg_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_);
lean_dec(v___y_501_);
lean_dec_ref(v___y_500_);
lean_dec(v___y_499_);
lean_dec_ref(v___y_498_);
return v_res_503_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__3(size_t v_sz_504_, size_t v_i_505_, lean_object* v_bs_506_){
_start:
{
uint8_t v___x_507_; 
v___x_507_ = lean_usize_dec_lt(v_i_505_, v_sz_504_);
if (v___x_507_ == 0)
{
return v_bs_506_;
}
else
{
lean_object* v_v_508_; lean_object* v___x_509_; lean_object* v_bs_x27_510_; lean_object* v___x_511_; size_t v___x_512_; size_t v___x_513_; lean_object* v___x_514_; 
v_v_508_ = lean_array_uget(v_bs_506_, v_i_505_);
v___x_509_ = lean_unsigned_to_nat(0u);
v_bs_x27_510_ = lean_array_uset(v_bs_506_, v_i_505_, v___x_509_);
v___x_511_ = l_Lean_mkFVar(v_v_508_);
v___x_512_ = ((size_t)1ULL);
v___x_513_ = lean_usize_add(v_i_505_, v___x_512_);
v___x_514_ = lean_array_uset(v_bs_x27_510_, v_i_505_, v___x_511_);
v_i_505_ = v___x_513_;
v_bs_506_ = v___x_514_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__3___boxed(lean_object* v_sz_516_, lean_object* v_i_517_, lean_object* v_bs_518_){
_start:
{
size_t v_sz_boxed_519_; size_t v_i_boxed_520_; lean_object* v_res_521_; 
v_sz_boxed_519_ = lean_unbox_usize(v_sz_516_);
lean_dec(v_sz_516_);
v_i_boxed_520_ = lean_unbox_usize(v_i_517_);
lean_dec(v_i_517_);
v_res_521_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__3(v_sz_boxed_519_, v_i_boxed_520_, v_bs_518_);
return v_res_521_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5(void){
_start:
{
lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; 
v___x_531_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__2));
v___x_532_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__4));
v___x_533_ = l_Lean_Name_append(v___x_532_, v___x_531_);
return v___x_533_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__7(void){
_start:
{
lean_object* v___x_535_; lean_object* v___x_536_; 
v___x_535_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__6));
v___x_536_ = l_Lean_stringToMessageData(v___x_535_);
return v___x_536_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__9(void){
_start:
{
lean_object* v___x_538_; lean_object* v___x_539_; 
v___x_538_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__8));
v___x_539_ = l_Lean_stringToMessageData(v___x_538_);
return v___x_539_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__11(void){
_start:
{
lean_object* v___x_541_; lean_object* v___x_542_; 
v___x_541_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__10));
v___x_542_ = l_Lean_stringToMessageData(v___x_541_);
return v___x_542_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__15(void){
_start:
{
lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; 
v___x_546_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__14));
v___x_547_ = lean_unsigned_to_nat(15u);
v___x_548_ = lean_unsigned_to_nat(120u);
v___x_549_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__13));
v___x_550_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__12));
v___x_551_ = l_mkPanicMessageWithDecl(v___x_550_, v___x_549_, v___x_548_, v___x_547_, v___x_546_);
return v___x_551_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop(lean_object* v_mvarId_552_, lean_object* v_givenNames_553_, lean_object* v_recursorInfo_554_, lean_object* v_reverted_555_, lean_object* v_major_556_, lean_object* v_indices_557_, lean_object* v_baseSubst_558_, lean_object* v_initialArity_559_, lean_object* v_numMinors_560_, lean_object* v_pos_561_, lean_object* v_minorIdx_562_, lean_object* v_recursor_563_, lean_object* v_recursorType_564_, uint8_t v_consumedMajor_565_, lean_object* v_subgoals_566_, lean_object* v_a_567_, lean_object* v_a_568_, lean_object* v_a_569_, lean_object* v_a_570_){
_start:
{
lean_object* v___y_573_; uint8_t v___y_574_; lean_object* v_fst_575_; lean_object* v_snd_576_; lean_object* v___y_593_; uint8_t v___y_594_; lean_object* v___y_595_; lean_object* v___y_608_; lean_object* v___y_609_; uint8_t v___y_610_; lean_object* v___y_611_; lean_object* v___y_612_; lean_object* v___y_613_; lean_object* v___y_614_; lean_object* v___y_615_; lean_object* v___y_616_; lean_object* v___y_617_; lean_object* v___y_618_; lean_object* v___y_619_; lean_object* v___y_620_; uint8_t v___y_621_; lean_object* v___y_622_; uint8_t v___y_623_; lean_object* v___y_659_; lean_object* v___y_660_; lean_object* v___y_661_; uint8_t v___y_662_; lean_object* v___y_663_; lean_object* v___y_664_; lean_object* v___y_665_; lean_object* v___y_666_; uint8_t v___y_667_; lean_object* v___y_668_; lean_object* v___y_669_; lean_object* v___y_670_; lean_object* v___y_671_; lean_object* v___y_672_; lean_object* v___y_673_; lean_object* v___y_691_; lean_object* v___y_692_; lean_object* v___y_693_; lean_object* v___y_694_; lean_object* v___x_746_; 
v___x_746_ = l_Lean_Meta_whnfForall(v_recursorType_564_, v_a_567_, v_a_568_, v_a_569_, v_a_570_);
if (lean_obj_tag(v___x_746_) == 0)
{
lean_object* v_a_747_; lean_object* v___y_749_; lean_object* v___y_750_; uint8_t v___y_751_; lean_object* v___y_752_; lean_object* v___y_753_; lean_object* v___y_754_; lean_object* v___y_755_; lean_object* v___y_756_; lean_object* v___y_757_; lean_object* v___y_758_; lean_object* v___y_759_; lean_object* v___y_760_; uint8_t v___y_761_; lean_object* v___y_762_; lean_object* v___y_804_; lean_object* v___y_805_; uint8_t v___y_806_; lean_object* v___y_807_; lean_object* v___y_808_; uint8_t v___y_809_; lean_object* v___y_810_; lean_object* v___y_811_; lean_object* v___y_812_; lean_object* v___y_813_; lean_object* v___y_825_; lean_object* v___y_826_; lean_object* v___y_827_; lean_object* v___y_828_; lean_object* v___y_829_; lean_object* v___y_830_; uint8_t v___y_831_; lean_object* v___y_832_; uint8_t v___y_833_; lean_object* v___y_903_; lean_object* v___y_904_; uint8_t v___y_905_; lean_object* v___y_906_; lean_object* v___y_907_; lean_object* v___y_908_; uint8_t v___y_909_; lean_object* v___y_910_; lean_object* v___y_911_; lean_object* v___y_917_; uint8_t v___y_918_; lean_object* v___y_919_; lean_object* v___y_920_; lean_object* v___y_921_; lean_object* v___y_922_; uint8_t v___x_933_; uint8_t v___y_935_; uint8_t v___x_982_; 
v_a_747_ = lean_ctor_get(v___x_746_, 0);
lean_inc(v_a_747_);
lean_dec_ref_known(v___x_746_, 1);
v___x_933_ = lean_nat_dec_le(v_numMinors_560_, v_minorIdx_562_);
v___x_982_ = l_Lean_Expr_isForall(v_a_747_);
if (v___x_982_ == 0)
{
v___y_935_ = v___x_982_;
goto v___jp_934_;
}
else
{
lean_object* v_numArgs_983_; uint8_t v___x_984_; 
v_numArgs_983_ = lean_ctor_get(v_recursorInfo_554_, 3);
v___x_984_ = lean_nat_dec_lt(v_pos_561_, v_numArgs_983_);
v___y_935_ = v___x_984_;
goto v___jp_934_;
}
v___jp_748_:
{
lean_object* v___x_763_; 
v___x_763_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___y_749_, v___y_753_, v___y_754_, v___y_755_, v___y_759_, v___y_760_);
if (lean_obj_tag(v___x_763_) == 0)
{
lean_object* v_a_764_; lean_object* v___x_765_; 
v_a_764_ = lean_ctor_get(v___x_763_, 0);
lean_inc(v_a_764_);
lean_dec_ref_known(v___x_763_, 1);
lean_inc(v_mvarId_552_);
v___x_765_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTypeBody(v_mvarId_552_, v_a_747_, v_a_764_, v___y_754_, v___y_755_, v___y_759_, v___y_760_);
if (lean_obj_tag(v___x_765_) == 0)
{
lean_object* v_options_766_; lean_object* v_a_767_; lean_object* v_inheritedTraceOptions_768_; uint8_t v_hasTrace_769_; lean_object* v___x_770_; 
v_options_766_ = lean_ctor_get(v___y_759_, 2);
v_a_767_ = lean_ctor_get(v___x_765_, 0);
lean_inc(v_a_767_);
lean_dec_ref_known(v___x_765_, 1);
v_inheritedTraceOptions_768_ = lean_ctor_get(v___y_759_, 13);
v_hasTrace_769_ = lean_ctor_get_uint8(v_options_766_, sizeof(void*)*1);
lean_inc(v_a_764_);
v___x_770_ = l_Lean_Expr_app___override(v_recursor_563_, v_a_764_);
if (v_hasTrace_769_ == 0)
{
v___y_659_ = v___y_757_;
v___y_660_ = v___y_750_;
v___y_661_ = v_a_767_;
v___y_662_ = v___y_751_;
v___y_663_ = v___y_762_;
v___y_664_ = v___y_758_;
v___y_665_ = v___x_770_;
v___y_666_ = v___y_752_;
v___y_667_ = v___y_761_;
v___y_668_ = v___y_756_;
v___y_669_ = v_a_764_;
v___y_670_ = v___y_754_;
v___y_671_ = v___y_755_;
v___y_672_ = v___y_759_;
v___y_673_ = v___y_760_;
goto v___jp_658_;
}
else
{
lean_object* v___x_771_; lean_object* v___x_772_; uint8_t v___x_773_; 
v___x_771_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__2));
v___x_772_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5);
v___x_773_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_768_, v_options_766_, v___x_772_);
if (v___x_773_ == 0)
{
v___y_659_ = v___y_757_;
v___y_660_ = v___y_750_;
v___y_661_ = v_a_767_;
v___y_662_ = v___y_751_;
v___y_663_ = v___y_762_;
v___y_664_ = v___y_758_;
v___y_665_ = v___x_770_;
v___y_666_ = v___y_752_;
v___y_667_ = v___y_761_;
v___y_668_ = v___y_756_;
v___y_669_ = v_a_764_;
v___y_670_ = v___y_754_;
v___y_671_ = v___y_755_;
v___y_672_ = v___y_759_;
v___y_673_ = v___y_760_;
goto v___jp_658_;
}
else
{
lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; 
v___x_774_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__11, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__11_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__11);
v___x_775_ = l_Lean_Expr_fvarId_x21(v_major_556_);
v___x_776_ = l_Lean_MessageData_ofName(v___x_775_);
v___x_777_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_777_, 0, v___x_774_);
lean_ctor_set(v___x_777_, 1, v___x_776_);
v___x_778_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1(v___x_771_, v___x_777_, v___y_754_, v___y_755_, v___y_759_, v___y_760_);
if (lean_obj_tag(v___x_778_) == 0)
{
lean_dec_ref_known(v___x_778_, 1);
v___y_659_ = v___y_757_;
v___y_660_ = v___y_750_;
v___y_661_ = v_a_767_;
v___y_662_ = v___y_751_;
v___y_663_ = v___y_762_;
v___y_664_ = v___y_758_;
v___y_665_ = v___x_770_;
v___y_666_ = v___y_752_;
v___y_667_ = v___y_761_;
v___y_668_ = v___y_756_;
v___y_669_ = v_a_764_;
v___y_670_ = v___y_754_;
v___y_671_ = v___y_755_;
v___y_672_ = v___y_759_;
v___y_673_ = v___y_760_;
goto v___jp_658_;
}
else
{
lean_object* v_a_779_; lean_object* v___x_781_; uint8_t v_isShared_782_; uint8_t v_isSharedCheck_786_; 
lean_dec_ref(v___x_770_);
lean_dec(v_a_767_);
lean_dec(v_a_764_);
lean_dec_ref(v___y_762_);
lean_dec(v___y_757_);
lean_dec(v___y_756_);
lean_dec(v___y_752_);
lean_dec(v___y_750_);
lean_dec_ref(v_subgoals_566_);
lean_dec(v_minorIdx_562_);
lean_dec(v_pos_561_);
lean_dec(v_baseSubst_558_);
lean_dec_ref(v_major_556_);
lean_dec(v_mvarId_552_);
v_a_779_ = lean_ctor_get(v___x_778_, 0);
v_isSharedCheck_786_ = !lean_is_exclusive(v___x_778_);
if (v_isSharedCheck_786_ == 0)
{
v___x_781_ = v___x_778_;
v_isShared_782_ = v_isSharedCheck_786_;
goto v_resetjp_780_;
}
else
{
lean_inc(v_a_779_);
lean_dec(v___x_778_);
v___x_781_ = lean_box(0);
v_isShared_782_ = v_isSharedCheck_786_;
goto v_resetjp_780_;
}
v_resetjp_780_:
{
lean_object* v___x_784_; 
if (v_isShared_782_ == 0)
{
v___x_784_ = v___x_781_;
goto v_reusejp_783_;
}
else
{
lean_object* v_reuseFailAlloc_785_; 
v_reuseFailAlloc_785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_785_, 0, v_a_779_);
v___x_784_ = v_reuseFailAlloc_785_;
goto v_reusejp_783_;
}
v_reusejp_783_:
{
return v___x_784_;
}
}
}
}
}
}
else
{
lean_object* v_a_787_; lean_object* v___x_789_; uint8_t v_isShared_790_; uint8_t v_isSharedCheck_794_; 
lean_dec(v_a_764_);
lean_dec_ref(v___y_762_);
lean_dec(v___y_757_);
lean_dec(v___y_756_);
lean_dec(v___y_752_);
lean_dec(v___y_750_);
lean_dec_ref(v_subgoals_566_);
lean_dec_ref(v_recursor_563_);
lean_dec(v_minorIdx_562_);
lean_dec(v_pos_561_);
lean_dec(v_baseSubst_558_);
lean_dec_ref(v_major_556_);
lean_dec(v_mvarId_552_);
v_a_787_ = lean_ctor_get(v___x_765_, 0);
v_isSharedCheck_794_ = !lean_is_exclusive(v___x_765_);
if (v_isSharedCheck_794_ == 0)
{
v___x_789_ = v___x_765_;
v_isShared_790_ = v_isSharedCheck_794_;
goto v_resetjp_788_;
}
else
{
lean_inc(v_a_787_);
lean_dec(v___x_765_);
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
else
{
lean_object* v_a_795_; lean_object* v___x_797_; uint8_t v_isShared_798_; uint8_t v_isSharedCheck_802_; 
lean_dec_ref(v___y_762_);
lean_dec(v___y_757_);
lean_dec(v___y_756_);
lean_dec(v___y_752_);
lean_dec(v___y_750_);
lean_dec(v_a_747_);
lean_dec_ref(v_subgoals_566_);
lean_dec_ref(v_recursor_563_);
lean_dec(v_minorIdx_562_);
lean_dec(v_pos_561_);
lean_dec(v_baseSubst_558_);
lean_dec_ref(v_major_556_);
lean_dec(v_mvarId_552_);
v_a_795_ = lean_ctor_get(v___x_763_, 0);
v_isSharedCheck_802_ = !lean_is_exclusive(v___x_763_);
if (v_isSharedCheck_802_ == 0)
{
v___x_797_ = v___x_763_;
v_isShared_798_ = v_isSharedCheck_802_;
goto v_resetjp_796_;
}
else
{
lean_inc(v_a_795_);
lean_dec(v___x_763_);
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
v___jp_803_:
{
lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; uint8_t v___x_820_; 
v___x_814_ = lean_nat_sub(v___y_805_, v_initialArity_559_);
lean_dec(v___y_805_);
v___x_815_ = lean_array_get_size(v_reverted_555_);
v___x_816_ = lean_array_get_size(v_indices_557_);
v___x_817_ = lean_nat_sub(v___x_815_, v___x_816_);
v___x_818_ = lean_nat_sub(v___x_817_, v___y_807_);
lean_dec(v___x_817_);
v___x_819_ = lean_array_get_size(v_givenNames_553_);
v___x_820_ = lean_nat_dec_lt(v_minorIdx_562_, v___x_819_);
if (v___x_820_ == 0)
{
lean_object* v___x_821_; lean_object* v___x_822_; 
v___x_821_ = lean_box(0);
v___x_822_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_822_, 0, v___x_821_);
lean_ctor_set_uint8(v___x_822_, sizeof(void*)*1, v___x_820_);
v___y_749_ = v___y_804_;
v___y_750_ = v___x_815_;
v___y_751_ = v___y_806_;
v___y_752_ = v___x_814_;
v___y_753_ = v___y_808_;
v___y_754_ = v___y_810_;
v___y_755_ = v___y_811_;
v___y_756_ = v___x_818_;
v___y_757_ = v___x_816_;
v___y_758_ = v___y_807_;
v___y_759_ = v___y_812_;
v___y_760_ = v___y_813_;
v___y_761_ = v___y_809_;
v___y_762_ = v___x_822_;
goto v___jp_748_;
}
else
{
lean_object* v___x_823_; 
v___x_823_ = lean_array_fget_borrowed(v_givenNames_553_, v_minorIdx_562_);
lean_inc(v___x_823_);
v___y_749_ = v___y_804_;
v___y_750_ = v___x_815_;
v___y_751_ = v___y_806_;
v___y_752_ = v___x_814_;
v___y_753_ = v___y_808_;
v___y_754_ = v___y_810_;
v___y_755_ = v___y_811_;
v___y_756_ = v___x_818_;
v___y_757_ = v___x_816_;
v___y_758_ = v___y_807_;
v___y_759_ = v___y_812_;
v___y_760_ = v___y_813_;
v___y_761_ = v___y_809_;
v___y_762_ = v___x_823_;
goto v___jp_748_;
}
}
v___jp_824_:
{
if (v___y_833_ == 0)
{
lean_object* v___x_834_; uint8_t v___x_835_; 
lean_inc_ref(v___y_825_);
v___x_834_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTargetArity(v___y_825_);
v___x_835_ = lean_nat_dec_lt(v___x_834_, v_initialArity_559_);
if (v___x_835_ == 0)
{
v___y_804_ = v___y_825_;
v___y_805_ = v___x_834_;
v___y_806_ = v___y_833_;
v___y_807_ = v___y_829_;
v___y_808_ = v___y_830_;
v___y_809_ = v___y_831_;
v___y_810_ = v___y_832_;
v___y_811_ = v___y_826_;
v___y_812_ = v___y_828_;
v___y_813_ = v___y_827_;
goto v___jp_803_;
}
else
{
lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; 
v___x_836_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1));
v___x_837_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9);
lean_inc(v_mvarId_552_);
v___x_838_ = l_Lean_Meta_throwTacticEx___redArg(v___x_836_, v_mvarId_552_, v___x_837_, v___y_832_, v___y_826_, v___y_828_, v___y_827_);
if (lean_obj_tag(v___x_838_) == 0)
{
lean_dec_ref_known(v___x_838_, 1);
v___y_804_ = v___y_825_;
v___y_805_ = v___x_834_;
v___y_806_ = v___y_833_;
v___y_807_ = v___y_829_;
v___y_808_ = v___y_830_;
v___y_809_ = v___y_831_;
v___y_810_ = v___y_832_;
v___y_811_ = v___y_826_;
v___y_812_ = v___y_828_;
v___y_813_ = v___y_827_;
goto v___jp_803_;
}
else
{
lean_object* v_a_839_; lean_object* v___x_841_; uint8_t v_isShared_842_; uint8_t v_isSharedCheck_846_; 
lean_dec(v___x_834_);
lean_dec(v___y_830_);
lean_dec_ref(v___y_825_);
lean_dec(v_a_747_);
lean_dec_ref(v_subgoals_566_);
lean_dec_ref(v_recursor_563_);
lean_dec(v_minorIdx_562_);
lean_dec(v_pos_561_);
lean_dec(v_baseSubst_558_);
lean_dec_ref(v_major_556_);
lean_dec(v_mvarId_552_);
v_a_839_ = lean_ctor_get(v___x_838_, 0);
v_isSharedCheck_846_ = !lean_is_exclusive(v___x_838_);
if (v_isSharedCheck_846_ == 0)
{
v___x_841_ = v___x_838_;
v_isShared_842_ = v_isSharedCheck_846_;
goto v_resetjp_840_;
}
else
{
lean_inc(v_a_839_);
lean_dec(v___x_838_);
v___x_841_ = lean_box(0);
v_isShared_842_ = v_isSharedCheck_846_;
goto v_resetjp_840_;
}
v_resetjp_840_:
{
lean_object* v___x_844_; 
if (v_isShared_842_ == 0)
{
v___x_844_ = v___x_841_;
goto v_reusejp_843_;
}
else
{
lean_object* v_reuseFailAlloc_845_; 
v_reuseFailAlloc_845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_845_, 0, v_a_839_);
v___x_844_ = v_reuseFailAlloc_845_;
goto v_reusejp_843_;
}
v_reusejp_843_:
{
return v___x_844_;
}
}
}
}
}
else
{
lean_object* v___x_847_; lean_object* v___x_848_; 
v___x_847_ = lean_box(0);
lean_inc_ref(v___y_825_);
v___x_848_ = l_Lean_Meta_synthInstance_x3f(v___y_825_, v___x_847_, v___y_832_, v___y_826_, v___y_828_, v___y_827_);
if (lean_obj_tag(v___x_848_) == 0)
{
lean_object* v_a_849_; 
v_a_849_ = lean_ctor_get(v___x_848_, 0);
lean_inc(v_a_849_);
lean_dec_ref_known(v___x_848_, 1);
if (lean_obj_tag(v_a_849_) == 0)
{
lean_object* v___x_850_; 
v___x_850_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___y_825_, v___y_830_, v___y_832_, v___y_826_, v___y_828_, v___y_827_);
if (lean_obj_tag(v___x_850_) == 0)
{
lean_object* v_a_851_; lean_object* v___x_852_; 
v_a_851_ = lean_ctor_get(v___x_850_, 0);
lean_inc(v_a_851_);
lean_dec_ref_known(v___x_850_, 1);
lean_inc(v_mvarId_552_);
v___x_852_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTypeBody(v_mvarId_552_, v_a_747_, v_a_851_, v___y_832_, v___y_826_, v___y_828_, v___y_827_);
if (lean_obj_tag(v___x_852_) == 0)
{
lean_object* v_a_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; 
v_a_853_ = lean_ctor_get(v___x_852_, 0);
lean_inc(v_a_853_);
lean_dec_ref_known(v___x_852_, 1);
lean_inc(v_a_851_);
v___x_854_ = l_Lean_Expr_app___override(v_recursor_563_, v_a_851_);
v___x_855_ = lean_nat_add(v_pos_561_, v___y_829_);
lean_dec(v_pos_561_);
v___x_856_ = lean_nat_add(v_minorIdx_562_, v___y_829_);
lean_dec(v_minorIdx_562_);
v___x_857_ = l_Lean_Expr_mvarId_x21(v_a_851_);
lean_dec(v_a_851_);
v___x_858_ = ((lean_object*)(l_Lean_Meta_instInhabitedInductionSubgoal_default___closed__0));
v___x_859_ = lean_box(0);
v___x_860_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_860_, 0, v___x_857_);
lean_ctor_set(v___x_860_, 1, v___x_858_);
lean_ctor_set(v___x_860_, 2, v___x_859_);
v___x_861_ = lean_array_push(v_subgoals_566_, v___x_860_);
v_pos_561_ = v___x_855_;
v_minorIdx_562_ = v___x_856_;
v_recursor_563_ = v___x_854_;
v_recursorType_564_ = v_a_853_;
v_subgoals_566_ = v___x_861_;
v_a_567_ = v___y_832_;
v_a_568_ = v___y_826_;
v_a_569_ = v___y_828_;
v_a_570_ = v___y_827_;
goto _start;
}
else
{
lean_object* v_a_863_; lean_object* v___x_865_; uint8_t v_isShared_866_; uint8_t v_isSharedCheck_870_; 
lean_dec(v_a_851_);
lean_dec_ref(v_subgoals_566_);
lean_dec_ref(v_recursor_563_);
lean_dec(v_minorIdx_562_);
lean_dec(v_pos_561_);
lean_dec(v_baseSubst_558_);
lean_dec_ref(v_major_556_);
lean_dec(v_mvarId_552_);
v_a_863_ = lean_ctor_get(v___x_852_, 0);
v_isSharedCheck_870_ = !lean_is_exclusive(v___x_852_);
if (v_isSharedCheck_870_ == 0)
{
v___x_865_ = v___x_852_;
v_isShared_866_ = v_isSharedCheck_870_;
goto v_resetjp_864_;
}
else
{
lean_inc(v_a_863_);
lean_dec(v___x_852_);
v___x_865_ = lean_box(0);
v_isShared_866_ = v_isSharedCheck_870_;
goto v_resetjp_864_;
}
v_resetjp_864_:
{
lean_object* v___x_868_; 
if (v_isShared_866_ == 0)
{
v___x_868_ = v___x_865_;
goto v_reusejp_867_;
}
else
{
lean_object* v_reuseFailAlloc_869_; 
v_reuseFailAlloc_869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_869_, 0, v_a_863_);
v___x_868_ = v_reuseFailAlloc_869_;
goto v_reusejp_867_;
}
v_reusejp_867_:
{
return v___x_868_;
}
}
}
}
else
{
lean_object* v_a_871_; lean_object* v___x_873_; uint8_t v_isShared_874_; uint8_t v_isSharedCheck_878_; 
lean_dec(v_a_747_);
lean_dec_ref(v_subgoals_566_);
lean_dec_ref(v_recursor_563_);
lean_dec(v_minorIdx_562_);
lean_dec(v_pos_561_);
lean_dec(v_baseSubst_558_);
lean_dec_ref(v_major_556_);
lean_dec(v_mvarId_552_);
v_a_871_ = lean_ctor_get(v___x_850_, 0);
v_isSharedCheck_878_ = !lean_is_exclusive(v___x_850_);
if (v_isSharedCheck_878_ == 0)
{
v___x_873_ = v___x_850_;
v_isShared_874_ = v_isSharedCheck_878_;
goto v_resetjp_872_;
}
else
{
lean_inc(v_a_871_);
lean_dec(v___x_850_);
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
lean_object* v_val_879_; lean_object* v___x_880_; 
lean_dec(v___y_830_);
lean_dec_ref(v___y_825_);
v_val_879_ = lean_ctor_get(v_a_849_, 0);
lean_inc(v_val_879_);
lean_dec_ref_known(v_a_849_, 1);
lean_inc(v_mvarId_552_);
v___x_880_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTypeBody(v_mvarId_552_, v_a_747_, v_val_879_, v___y_832_, v___y_826_, v___y_828_, v___y_827_);
if (lean_obj_tag(v___x_880_) == 0)
{
lean_object* v_a_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; 
v_a_881_ = lean_ctor_get(v___x_880_, 0);
lean_inc(v_a_881_);
lean_dec_ref_known(v___x_880_, 1);
v___x_882_ = l_Lean_Expr_app___override(v_recursor_563_, v_val_879_);
v___x_883_ = lean_nat_add(v_pos_561_, v___y_829_);
lean_dec(v_pos_561_);
v___x_884_ = lean_nat_add(v_minorIdx_562_, v___y_829_);
lean_dec(v_minorIdx_562_);
v_pos_561_ = v___x_883_;
v_minorIdx_562_ = v___x_884_;
v_recursor_563_ = v___x_882_;
v_recursorType_564_ = v_a_881_;
v_a_567_ = v___y_832_;
v_a_568_ = v___y_826_;
v_a_569_ = v___y_828_;
v_a_570_ = v___y_827_;
goto _start;
}
else
{
lean_object* v_a_886_; lean_object* v___x_888_; uint8_t v_isShared_889_; uint8_t v_isSharedCheck_893_; 
lean_dec(v_val_879_);
lean_dec_ref(v_subgoals_566_);
lean_dec_ref(v_recursor_563_);
lean_dec(v_minorIdx_562_);
lean_dec(v_pos_561_);
lean_dec(v_baseSubst_558_);
lean_dec_ref(v_major_556_);
lean_dec(v_mvarId_552_);
v_a_886_ = lean_ctor_get(v___x_880_, 0);
v_isSharedCheck_893_ = !lean_is_exclusive(v___x_880_);
if (v_isSharedCheck_893_ == 0)
{
v___x_888_ = v___x_880_;
v_isShared_889_ = v_isSharedCheck_893_;
goto v_resetjp_887_;
}
else
{
lean_inc(v_a_886_);
lean_dec(v___x_880_);
v___x_888_ = lean_box(0);
v_isShared_889_ = v_isSharedCheck_893_;
goto v_resetjp_887_;
}
v_resetjp_887_:
{
lean_object* v___x_891_; 
if (v_isShared_889_ == 0)
{
v___x_891_ = v___x_888_;
goto v_reusejp_890_;
}
else
{
lean_object* v_reuseFailAlloc_892_; 
v_reuseFailAlloc_892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_892_, 0, v_a_886_);
v___x_891_ = v_reuseFailAlloc_892_;
goto v_reusejp_890_;
}
v_reusejp_890_:
{
return v___x_891_;
}
}
}
}
}
else
{
lean_object* v_a_894_; lean_object* v___x_896_; uint8_t v_isShared_897_; uint8_t v_isSharedCheck_901_; 
lean_dec(v___y_830_);
lean_dec_ref(v___y_825_);
lean_dec(v_a_747_);
lean_dec_ref(v_subgoals_566_);
lean_dec_ref(v_recursor_563_);
lean_dec(v_minorIdx_562_);
lean_dec(v_pos_561_);
lean_dec(v_baseSubst_558_);
lean_dec_ref(v_major_556_);
lean_dec(v_mvarId_552_);
v_a_894_ = lean_ctor_get(v___x_848_, 0);
v_isSharedCheck_901_ = !lean_is_exclusive(v___x_848_);
if (v_isSharedCheck_901_ == 0)
{
v___x_896_ = v___x_848_;
v_isShared_897_ = v_isSharedCheck_901_;
goto v_resetjp_895_;
}
else
{
lean_inc(v_a_894_);
lean_dec(v___x_848_);
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
v___jp_902_:
{
uint8_t v___x_912_; 
v___x_912_ = l_Lean_BinderInfo_isInstImplicit(v___y_905_);
if (v___x_912_ == 0)
{
v___y_825_ = v___y_903_;
v___y_826_ = v___y_904_;
v___y_827_ = v___y_908_;
v___y_828_ = v___y_907_;
v___y_829_ = v___y_906_;
v___y_830_ = v___y_911_;
v___y_831_ = v___y_909_;
v___y_832_ = v___y_910_;
v___y_833_ = v___x_912_;
goto v___jp_824_;
}
else
{
lean_object* v___x_913_; lean_object* v___x_914_; uint8_t v___x_915_; 
v___x_913_ = lean_array_get_size(v_givenNames_553_);
v___x_914_ = lean_unsigned_to_nat(0u);
v___x_915_ = lean_nat_dec_eq(v___x_913_, v___x_914_);
v___y_825_ = v___y_903_;
v___y_826_ = v___y_904_;
v___y_827_ = v___y_908_;
v___y_828_ = v___y_907_;
v___y_829_ = v___y_906_;
v___y_830_ = v___y_911_;
v___y_831_ = v___y_909_;
v___y_832_ = v___y_910_;
v___y_833_ = v___x_915_;
goto v___jp_824_;
}
}
v___jp_916_:
{
if (lean_obj_tag(v_a_747_) == 7)
{
lean_object* v_binderName_923_; lean_object* v_binderType_924_; uint8_t v_binderInfo_925_; lean_object* v___x_926_; lean_object* v___x_927_; uint8_t v___x_928_; 
v_binderName_923_ = lean_ctor_get(v_a_747_, 0);
v_binderType_924_ = lean_ctor_get(v_a_747_, 1);
v_binderInfo_925_ = lean_ctor_get_uint8(v_a_747_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_924_);
v___x_926_ = l_Lean_Expr_headBeta(v_binderType_924_);
v___x_927_ = lean_unsigned_to_nat(1u);
v___x_928_ = lean_nat_dec_eq(v_numMinors_560_, v___x_927_);
if (v___x_928_ == 0)
{
lean_object* v___x_929_; lean_object* v___x_930_; 
v___x_929_ = l_Lean_Name_eraseMacroScopes(v_binderName_923_);
v___x_930_ = l_Lean_Name_append(v___y_917_, v___x_929_);
v___y_903_ = v___x_926_;
v___y_904_ = v___y_920_;
v___y_905_ = v_binderInfo_925_;
v___y_906_ = v___x_927_;
v___y_907_ = v___y_921_;
v___y_908_ = v___y_922_;
v___y_909_ = v___y_918_;
v___y_910_ = v___y_919_;
v___y_911_ = v___x_930_;
goto v___jp_902_;
}
else
{
v___y_903_ = v___x_926_;
v___y_904_ = v___y_920_;
v___y_905_ = v_binderInfo_925_;
v___y_906_ = v___x_927_;
v___y_907_ = v___y_921_;
v___y_908_ = v___y_922_;
v___y_909_ = v___y_918_;
v___y_910_ = v___y_919_;
v___y_911_ = v___y_917_;
goto v___jp_902_;
}
}
else
{
lean_object* v___x_931_; lean_object* v___x_932_; 
lean_dec(v___y_917_);
lean_dec(v_a_747_);
lean_dec_ref(v_subgoals_566_);
lean_dec_ref(v_recursor_563_);
lean_dec(v_minorIdx_562_);
lean_dec(v_pos_561_);
lean_dec(v_baseSubst_558_);
lean_dec_ref(v_major_556_);
lean_dec(v_mvarId_552_);
v___x_931_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__15, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__15_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__15);
v___x_932_ = l_panic___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__4(v___x_931_, v___y_919_, v___y_920_, v___y_921_, v___y_922_);
return v___x_932_;
}
}
v___jp_934_:
{
if (v___y_935_ == 0)
{
lean_dec(v_a_747_);
lean_dec(v_minorIdx_562_);
lean_dec(v_pos_561_);
lean_dec(v_baseSubst_558_);
lean_dec_ref(v_major_556_);
if (v_consumedMajor_565_ == 0)
{
lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; 
v___x_936_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1));
v___x_937_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9);
lean_inc(v_mvarId_552_);
v___x_938_ = l_Lean_Meta_throwTacticEx___redArg(v___x_936_, v_mvarId_552_, v___x_937_, v_a_567_, v_a_568_, v_a_569_, v_a_570_);
if (lean_obj_tag(v___x_938_) == 0)
{
lean_dec_ref_known(v___x_938_, 1);
v___y_691_ = v_a_567_;
v___y_692_ = v_a_568_;
v___y_693_ = v_a_569_;
v___y_694_ = v_a_570_;
goto v___jp_690_;
}
else
{
lean_object* v_a_939_; lean_object* v___x_941_; uint8_t v_isShared_942_; uint8_t v_isSharedCheck_946_; 
lean_dec_ref(v_subgoals_566_);
lean_dec_ref(v_recursor_563_);
lean_dec(v_mvarId_552_);
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
v___y_691_ = v_a_567_;
v___y_692_ = v_a_568_;
v___y_693_ = v_a_569_;
v___y_694_ = v_a_570_;
goto v___jp_690_;
}
}
else
{
lean_object* v___x_947_; uint8_t v___x_948_; 
v___x_947_ = l_Lean_Meta_RecursorInfo_firstIndexPos(v_recursorInfo_554_);
v___x_948_ = lean_nat_dec_eq(v_pos_561_, v___x_947_);
lean_dec(v___x_947_);
if (v___x_948_ == 0)
{
lean_object* v___x_949_; 
lean_inc(v_mvarId_552_);
v___x_949_ = l_Lean_MVarId_getTag(v_mvarId_552_, v_a_567_, v_a_568_, v_a_569_, v_a_570_);
if (lean_obj_tag(v___x_949_) == 0)
{
if (v___x_933_ == 0)
{
lean_object* v_a_950_; 
v_a_950_ = lean_ctor_get(v___x_949_, 0);
lean_inc(v_a_950_);
lean_dec_ref_known(v___x_949_, 1);
v___y_917_ = v_a_950_;
v___y_918_ = v___y_935_;
v___y_919_ = v_a_567_;
v___y_920_ = v_a_568_;
v___y_921_ = v_a_569_;
v___y_922_ = v_a_570_;
goto v___jp_916_;
}
else
{
lean_object* v_a_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; 
v_a_951_ = lean_ctor_get(v___x_949_, 0);
lean_inc(v_a_951_);
lean_dec_ref_known(v___x_949_, 1);
v___x_952_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1));
v___x_953_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9);
lean_inc(v_mvarId_552_);
v___x_954_ = l_Lean_Meta_throwTacticEx___redArg(v___x_952_, v_mvarId_552_, v___x_953_, v_a_567_, v_a_568_, v_a_569_, v_a_570_);
if (lean_obj_tag(v___x_954_) == 0)
{
lean_dec_ref_known(v___x_954_, 1);
v___y_917_ = v_a_951_;
v___y_918_ = v___y_935_;
v___y_919_ = v_a_567_;
v___y_920_ = v_a_568_;
v___y_921_ = v_a_569_;
v___y_922_ = v_a_570_;
goto v___jp_916_;
}
else
{
lean_object* v_a_955_; lean_object* v___x_957_; uint8_t v_isShared_958_; uint8_t v_isSharedCheck_962_; 
lean_dec(v_a_951_);
lean_dec(v_a_747_);
lean_dec_ref(v_subgoals_566_);
lean_dec_ref(v_recursor_563_);
lean_dec(v_minorIdx_562_);
lean_dec(v_pos_561_);
lean_dec(v_baseSubst_558_);
lean_dec_ref(v_major_556_);
lean_dec(v_mvarId_552_);
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
lean_dec(v_a_747_);
lean_dec_ref(v_subgoals_566_);
lean_dec_ref(v_recursor_563_);
lean_dec(v_minorIdx_562_);
lean_dec(v_pos_561_);
lean_dec(v_baseSubst_558_);
lean_dec_ref(v_major_556_);
lean_dec(v_mvarId_552_);
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
v___x_972_ = lean_array_get_size(v_indices_557_);
v___x_973_ = lean_nat_dec_lt(v___x_971_, v___x_972_);
if (v___x_973_ == 0)
{
v___y_573_ = v___x_972_;
v___y_574_ = v___x_948_;
v_fst_575_ = v_recursor_563_;
v_snd_576_ = v_a_747_;
goto v___jp_572_;
}
else
{
lean_object* v___x_974_; uint8_t v___x_975_; 
lean_inc(v_a_747_);
lean_inc_ref(v_recursor_563_);
v___x_974_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_974_, 0, v_recursor_563_);
lean_ctor_set(v___x_974_, 1, v_a_747_);
v___x_975_ = lean_nat_dec_le(v___x_972_, v___x_972_);
if (v___x_975_ == 0)
{
if (v___x_973_ == 0)
{
lean_dec_ref_known(v___x_974_, 2);
v___y_573_ = v___x_972_;
v___y_574_ = v___x_948_;
v_fst_575_ = v_recursor_563_;
v_snd_576_ = v_a_747_;
goto v___jp_572_;
}
else
{
size_t v___x_976_; size_t v___x_977_; lean_object* v___x_978_; 
lean_dec(v_a_747_);
lean_dec_ref(v_recursor_563_);
v___x_976_ = ((size_t)0ULL);
v___x_977_ = lean_usize_of_nat(v___x_972_);
lean_inc(v_mvarId_552_);
v___x_978_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__5(v_mvarId_552_, v_indices_557_, v___x_976_, v___x_977_, v___x_974_, v_a_567_, v_a_568_, v_a_569_, v_a_570_);
v___y_593_ = v___x_972_;
v___y_594_ = v___x_948_;
v___y_595_ = v___x_978_;
goto v___jp_592_;
}
}
else
{
size_t v___x_979_; size_t v___x_980_; lean_object* v___x_981_; 
lean_dec(v_a_747_);
lean_dec_ref(v_recursor_563_);
v___x_979_ = ((size_t)0ULL);
v___x_980_ = lean_usize_of_nat(v___x_972_);
lean_inc(v_mvarId_552_);
v___x_981_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__5(v_mvarId_552_, v_indices_557_, v___x_979_, v___x_980_, v___x_974_, v_a_567_, v_a_568_, v_a_569_, v_a_570_);
v___y_593_ = v___x_972_;
v___y_594_ = v___x_948_;
v___y_595_ = v___x_981_;
goto v___jp_592_;
}
}
}
}
}
}
else
{
lean_object* v_a_985_; lean_object* v___x_987_; uint8_t v_isShared_988_; uint8_t v_isSharedCheck_992_; 
lean_dec_ref(v_subgoals_566_);
lean_dec_ref(v_recursor_563_);
lean_dec(v_minorIdx_562_);
lean_dec(v_pos_561_);
lean_dec(v_baseSubst_558_);
lean_dec_ref(v_major_556_);
lean_dec(v_mvarId_552_);
v_a_985_ = lean_ctor_get(v___x_746_, 0);
v_isSharedCheck_992_ = !lean_is_exclusive(v___x_746_);
if (v_isSharedCheck_992_ == 0)
{
v___x_987_ = v___x_746_;
v_isShared_988_ = v_isSharedCheck_992_;
goto v_resetjp_986_;
}
else
{
lean_inc(v_a_985_);
lean_dec(v___x_746_);
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
v___jp_572_:
{
lean_object* v___x_577_; 
lean_inc(v_mvarId_552_);
v___x_577_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTypeBody(v_mvarId_552_, v_snd_576_, v_major_556_, v_a_567_, v_a_568_, v_a_569_, v_a_570_);
if (lean_obj_tag(v___x_577_) == 0)
{
lean_object* v_a_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; 
v_a_578_ = lean_ctor_get(v___x_577_, 0);
lean_inc(v_a_578_);
lean_dec_ref_known(v___x_577_, 1);
lean_inc_ref(v_major_556_);
v___x_579_ = l_Lean_Expr_app___override(v_fst_575_, v_major_556_);
v___x_580_ = lean_unsigned_to_nat(1u);
v___x_581_ = lean_nat_add(v_pos_561_, v___x_580_);
lean_dec(v_pos_561_);
v___x_582_ = lean_nat_add(v___x_581_, v___y_573_);
lean_dec(v___y_573_);
lean_dec(v___x_581_);
v_pos_561_ = v___x_582_;
v_recursor_563_ = v___x_579_;
v_recursorType_564_ = v_a_578_;
v_consumedMajor_565_ = v___y_574_;
goto _start;
}
else
{
lean_object* v_a_584_; lean_object* v___x_586_; uint8_t v_isShared_587_; uint8_t v_isSharedCheck_591_; 
lean_dec_ref(v_fst_575_);
lean_dec(v___y_573_);
lean_dec_ref(v_subgoals_566_);
lean_dec(v_minorIdx_562_);
lean_dec(v_pos_561_);
lean_dec(v_baseSubst_558_);
lean_dec_ref(v_major_556_);
lean_dec(v_mvarId_552_);
v_a_584_ = lean_ctor_get(v___x_577_, 0);
v_isSharedCheck_591_ = !lean_is_exclusive(v___x_577_);
if (v_isSharedCheck_591_ == 0)
{
v___x_586_ = v___x_577_;
v_isShared_587_ = v_isSharedCheck_591_;
goto v_resetjp_585_;
}
else
{
lean_inc(v_a_584_);
lean_dec(v___x_577_);
v___x_586_ = lean_box(0);
v_isShared_587_ = v_isSharedCheck_591_;
goto v_resetjp_585_;
}
v_resetjp_585_:
{
lean_object* v___x_589_; 
if (v_isShared_587_ == 0)
{
v___x_589_ = v___x_586_;
goto v_reusejp_588_;
}
else
{
lean_object* v_reuseFailAlloc_590_; 
v_reuseFailAlloc_590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_590_, 0, v_a_584_);
v___x_589_ = v_reuseFailAlloc_590_;
goto v_reusejp_588_;
}
v_reusejp_588_:
{
return v___x_589_;
}
}
}
}
v___jp_592_:
{
if (lean_obj_tag(v___y_595_) == 0)
{
lean_object* v_a_596_; lean_object* v_fst_597_; lean_object* v_snd_598_; 
v_a_596_ = lean_ctor_get(v___y_595_, 0);
lean_inc(v_a_596_);
lean_dec_ref_known(v___y_595_, 1);
v_fst_597_ = lean_ctor_get(v_a_596_, 0);
lean_inc(v_fst_597_);
v_snd_598_ = lean_ctor_get(v_a_596_, 1);
lean_inc(v_snd_598_);
lean_dec(v_a_596_);
v___y_573_ = v___y_593_;
v___y_574_ = v___y_594_;
v_fst_575_ = v_fst_597_;
v_snd_576_ = v_snd_598_;
goto v___jp_572_;
}
else
{
lean_object* v_a_599_; lean_object* v___x_601_; uint8_t v_isShared_602_; uint8_t v_isSharedCheck_606_; 
lean_dec(v___y_593_);
lean_dec_ref(v_subgoals_566_);
lean_dec(v_minorIdx_562_);
lean_dec(v_pos_561_);
lean_dec(v_baseSubst_558_);
lean_dec_ref(v_major_556_);
lean_dec(v_mvarId_552_);
v_a_599_ = lean_ctor_get(v___y_595_, 0);
v_isSharedCheck_606_ = !lean_is_exclusive(v___y_595_);
if (v_isSharedCheck_606_ == 0)
{
v___x_601_ = v___y_595_;
v_isShared_602_ = v_isSharedCheck_606_;
goto v_resetjp_600_;
}
else
{
lean_inc(v_a_599_);
lean_dec(v___y_595_);
v___x_601_ = lean_box(0);
v_isShared_602_ = v_isSharedCheck_606_;
goto v_resetjp_600_;
}
v_resetjp_600_:
{
lean_object* v___x_604_; 
if (v_isShared_602_ == 0)
{
v___x_604_ = v___x_601_;
goto v_reusejp_603_;
}
else
{
lean_object* v_reuseFailAlloc_605_; 
v_reuseFailAlloc_605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_605_, 0, v_a_599_);
v___x_604_ = v_reuseFailAlloc_605_;
goto v_reusejp_603_;
}
v_reusejp_603_:
{
return v___x_604_;
}
}
}
}
v___jp_607_:
{
lean_object* v___x_624_; 
v___x_624_ = l_Lean_Meta_introNCore(v___y_620_, v___y_612_, v___y_613_, v___y_623_, v___y_610_, v___y_619_, v___y_608_, v___y_611_, v___y_622_);
if (lean_obj_tag(v___x_624_) == 0)
{
lean_object* v_a_625_; lean_object* v_fst_626_; lean_object* v_snd_627_; lean_object* v___x_628_; lean_object* v___x_629_; 
v_a_625_ = lean_ctor_get(v___x_624_, 0);
lean_inc(v_a_625_);
lean_dec_ref_known(v___x_624_, 1);
v_fst_626_ = lean_ctor_get(v_a_625_, 0);
lean_inc(v_fst_626_);
v_snd_627_ = lean_ctor_get(v_a_625_, 1);
lean_inc(v_snd_627_);
lean_dec(v_a_625_);
v___x_628_ = lean_box(0);
v___x_629_ = l_Lean_Meta_introNCore(v_snd_627_, v___y_614_, v___x_628_, v___y_610_, v___y_621_, v___y_619_, v___y_608_, v___y_611_, v___y_622_);
if (lean_obj_tag(v___x_629_) == 0)
{
lean_object* v_a_630_; lean_object* v_fst_631_; lean_object* v_snd_632_; lean_object* v___x_633_; size_t v_sz_634_; size_t v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; 
v_a_630_ = lean_ctor_get(v___x_629_, 0);
lean_inc(v_a_630_);
lean_dec_ref_known(v___x_629_, 1);
v_fst_631_ = lean_ctor_get(v_a_630_, 0);
lean_inc(v_fst_631_);
v_snd_632_ = lean_ctor_get(v_a_630_, 1);
lean_inc(v_snd_632_);
lean_dec(v_a_630_);
lean_inc(v_baseSubst_558_);
lean_inc(v___y_609_);
v___x_633_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__2___redArg(v___y_615_, v_reverted_555_, v_fst_631_, v___y_609_, v___y_609_, v_baseSubst_558_);
lean_dec(v___y_609_);
lean_dec(v_fst_631_);
lean_dec(v___y_615_);
v_sz_634_ = lean_array_size(v_fst_626_);
v___x_635_ = ((size_t)0ULL);
v___x_636_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__3(v_sz_634_, v___x_635_, v_fst_626_);
v___x_637_ = lean_nat_add(v_pos_561_, v___y_617_);
lean_dec(v_pos_561_);
v___x_638_ = lean_nat_add(v_minorIdx_562_, v___y_617_);
lean_dec(v_minorIdx_562_);
v___x_639_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_639_, 0, v_snd_632_);
lean_ctor_set(v___x_639_, 1, v___x_636_);
lean_ctor_set(v___x_639_, 2, v___x_633_);
v___x_640_ = lean_array_push(v_subgoals_566_, v___x_639_);
v_pos_561_ = v___x_637_;
v_minorIdx_562_ = v___x_638_;
v_recursor_563_ = v___y_618_;
v_recursorType_564_ = v___y_616_;
v_subgoals_566_ = v___x_640_;
v_a_567_ = v___y_619_;
v_a_568_ = v___y_608_;
v_a_569_ = v___y_611_;
v_a_570_ = v___y_622_;
goto _start;
}
else
{
lean_object* v_a_642_; lean_object* v___x_644_; uint8_t v_isShared_645_; uint8_t v_isSharedCheck_649_; 
lean_dec(v_fst_626_);
lean_dec_ref(v___y_618_);
lean_dec_ref(v___y_616_);
lean_dec(v___y_615_);
lean_dec(v___y_609_);
lean_dec_ref(v_subgoals_566_);
lean_dec(v_minorIdx_562_);
lean_dec(v_pos_561_);
lean_dec(v_baseSubst_558_);
lean_dec_ref(v_major_556_);
lean_dec(v_mvarId_552_);
v_a_642_ = lean_ctor_get(v___x_629_, 0);
v_isSharedCheck_649_ = !lean_is_exclusive(v___x_629_);
if (v_isSharedCheck_649_ == 0)
{
v___x_644_ = v___x_629_;
v_isShared_645_ = v_isSharedCheck_649_;
goto v_resetjp_643_;
}
else
{
lean_inc(v_a_642_);
lean_dec(v___x_629_);
v___x_644_ = lean_box(0);
v_isShared_645_ = v_isSharedCheck_649_;
goto v_resetjp_643_;
}
v_resetjp_643_:
{
lean_object* v___x_647_; 
if (v_isShared_645_ == 0)
{
v___x_647_ = v___x_644_;
goto v_reusejp_646_;
}
else
{
lean_object* v_reuseFailAlloc_648_; 
v_reuseFailAlloc_648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_648_, 0, v_a_642_);
v___x_647_ = v_reuseFailAlloc_648_;
goto v_reusejp_646_;
}
v_reusejp_646_:
{
return v___x_647_;
}
}
}
}
else
{
lean_object* v_a_650_; lean_object* v___x_652_; uint8_t v_isShared_653_; uint8_t v_isSharedCheck_657_; 
lean_dec_ref(v___y_618_);
lean_dec_ref(v___y_616_);
lean_dec(v___y_615_);
lean_dec(v___y_614_);
lean_dec(v___y_609_);
lean_dec_ref(v_subgoals_566_);
lean_dec(v_minorIdx_562_);
lean_dec(v_pos_561_);
lean_dec(v_baseSubst_558_);
lean_dec_ref(v_major_556_);
lean_dec(v_mvarId_552_);
v_a_650_ = lean_ctor_get(v___x_624_, 0);
v_isSharedCheck_657_ = !lean_is_exclusive(v___x_624_);
if (v_isSharedCheck_657_ == 0)
{
v___x_652_ = v___x_624_;
v_isShared_653_ = v_isSharedCheck_657_;
goto v_resetjp_651_;
}
else
{
lean_inc(v_a_650_);
lean_dec(v___x_624_);
v___x_652_ = lean_box(0);
v_isShared_653_ = v_isSharedCheck_657_;
goto v_resetjp_651_;
}
v_resetjp_651_:
{
lean_object* v___x_655_; 
if (v_isShared_653_ == 0)
{
v___x_655_ = v___x_652_;
goto v_reusejp_654_;
}
else
{
lean_object* v_reuseFailAlloc_656_; 
v_reuseFailAlloc_656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_656_, 0, v_a_650_);
v___x_655_ = v_reuseFailAlloc_656_;
goto v_reusejp_654_;
}
v_reusejp_654_:
{
return v___x_655_;
}
}
}
}
v___jp_658_:
{
lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; 
v___x_674_ = l_Lean_Expr_mvarId_x21(v___y_669_);
lean_dec_ref(v___y_669_);
v___x_675_ = l_Lean_Expr_fvarId_x21(v_major_556_);
v___x_676_ = l_Lean_MVarId_tryClear(v___x_674_, v___x_675_, v___y_670_, v___y_671_, v___y_672_, v___y_673_);
if (lean_obj_tag(v___x_676_) == 0)
{
uint8_t v_explicit_677_; 
v_explicit_677_ = lean_ctor_get_uint8(v___y_663_, sizeof(void*)*1);
if (v_explicit_677_ == 0)
{
lean_object* v_a_678_; lean_object* v_varNames_679_; 
v_a_678_ = lean_ctor_get(v___x_676_, 0);
lean_inc(v_a_678_);
lean_dec_ref_known(v___x_676_, 1);
v_varNames_679_ = lean_ctor_get(v___y_663_, 0);
lean_inc(v_varNames_679_);
lean_dec_ref(v___y_663_);
v___y_608_ = v___y_671_;
v___y_609_ = v___y_660_;
v___y_610_ = v___y_662_;
v___y_611_ = v___y_672_;
v___y_612_ = v___y_666_;
v___y_613_ = v_varNames_679_;
v___y_614_ = v___y_668_;
v___y_615_ = v___y_659_;
v___y_616_ = v___y_661_;
v___y_617_ = v___y_664_;
v___y_618_ = v___y_665_;
v___y_619_ = v___y_670_;
v___y_620_ = v_a_678_;
v___y_621_ = v___y_667_;
v___y_622_ = v___y_673_;
v___y_623_ = v___y_667_;
goto v___jp_607_;
}
else
{
lean_object* v_a_680_; lean_object* v_varNames_681_; 
v_a_680_ = lean_ctor_get(v___x_676_, 0);
lean_inc(v_a_680_);
lean_dec_ref_known(v___x_676_, 1);
v_varNames_681_ = lean_ctor_get(v___y_663_, 0);
lean_inc(v_varNames_681_);
lean_dec_ref(v___y_663_);
v___y_608_ = v___y_671_;
v___y_609_ = v___y_660_;
v___y_610_ = v___y_662_;
v___y_611_ = v___y_672_;
v___y_612_ = v___y_666_;
v___y_613_ = v_varNames_681_;
v___y_614_ = v___y_668_;
v___y_615_ = v___y_659_;
v___y_616_ = v___y_661_;
v___y_617_ = v___y_664_;
v___y_618_ = v___y_665_;
v___y_619_ = v___y_670_;
v___y_620_ = v_a_680_;
v___y_621_ = v___y_667_;
v___y_622_ = v___y_673_;
v___y_623_ = v___y_662_;
goto v___jp_607_;
}
}
else
{
lean_object* v_a_682_; lean_object* v___x_684_; uint8_t v_isShared_685_; uint8_t v_isSharedCheck_689_; 
lean_dec(v___y_668_);
lean_dec(v___y_666_);
lean_dec_ref(v___y_665_);
lean_dec_ref(v___y_663_);
lean_dec_ref(v___y_661_);
lean_dec(v___y_660_);
lean_dec(v___y_659_);
lean_dec_ref(v_subgoals_566_);
lean_dec(v_minorIdx_562_);
lean_dec(v_pos_561_);
lean_dec(v_baseSubst_558_);
lean_dec_ref(v_major_556_);
lean_dec(v_mvarId_552_);
v_a_682_ = lean_ctor_get(v___x_676_, 0);
v_isSharedCheck_689_ = !lean_is_exclusive(v___x_676_);
if (v_isSharedCheck_689_ == 0)
{
v___x_684_ = v___x_676_;
v_isShared_685_ = v_isSharedCheck_689_;
goto v_resetjp_683_;
}
else
{
lean_inc(v_a_682_);
lean_dec(v___x_676_);
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
v___jp_690_:
{
lean_object* v___x_695_; 
v___x_695_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0___redArg(v_mvarId_552_, v_recursor_563_, v___y_692_);
if (lean_obj_tag(v___x_695_) == 0)
{
lean_object* v___x_697_; uint8_t v_isShared_698_; uint8_t v_isSharedCheck_736_; 
v_isSharedCheck_736_ = !lean_is_exclusive(v___x_695_);
if (v_isSharedCheck_736_ == 0)
{
lean_object* v_unused_737_; 
v_unused_737_ = lean_ctor_get(v___x_695_, 0);
lean_dec(v_unused_737_);
v___x_697_ = v___x_695_;
v_isShared_698_ = v_isSharedCheck_736_;
goto v_resetjp_696_;
}
else
{
lean_dec(v___x_695_);
v___x_697_ = lean_box(0);
v_isShared_698_ = v_isSharedCheck_736_;
goto v_resetjp_696_;
}
v_resetjp_696_:
{
lean_object* v_options_699_; uint8_t v_hasTrace_700_; 
v_options_699_ = lean_ctor_get(v___y_693_, 2);
v_hasTrace_700_ = lean_ctor_get_uint8(v_options_699_, sizeof(void*)*1);
if (v_hasTrace_700_ == 0)
{
lean_object* v___x_702_; 
if (v_isShared_698_ == 0)
{
lean_ctor_set(v___x_697_, 0, v_subgoals_566_);
v___x_702_ = v___x_697_;
goto v_reusejp_701_;
}
else
{
lean_object* v_reuseFailAlloc_703_; 
v_reuseFailAlloc_703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_703_, 0, v_subgoals_566_);
v___x_702_ = v_reuseFailAlloc_703_;
goto v_reusejp_701_;
}
v_reusejp_701_:
{
return v___x_702_;
}
}
else
{
lean_object* v_inheritedTraceOptions_704_; lean_object* v___x_705_; lean_object* v___x_706_; uint8_t v___x_707_; 
v_inheritedTraceOptions_704_ = lean_ctor_get(v___y_693_, 13);
v___x_705_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__2));
v___x_706_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5);
v___x_707_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_704_, v_options_699_, v___x_706_);
if (v___x_707_ == 0)
{
lean_object* v___x_709_; 
if (v_isShared_698_ == 0)
{
lean_ctor_set(v___x_697_, 0, v_subgoals_566_);
v___x_709_ = v___x_697_;
goto v_reusejp_708_;
}
else
{
lean_object* v_reuseFailAlloc_710_; 
v_reuseFailAlloc_710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_710_, 0, v_subgoals_566_);
v___x_709_ = v_reuseFailAlloc_710_;
goto v_reusejp_708_;
}
v_reusejp_708_:
{
return v___x_709_;
}
}
else
{
lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; 
lean_del_object(v___x_697_);
v___x_711_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__7, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__7_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__7);
v___x_712_ = lean_array_get_size(v_subgoals_566_);
v___x_713_ = l_Nat_reprFast(v___x_712_);
v___x_714_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_714_, 0, v___x_713_);
v___x_715_ = l_Lean_MessageData_ofFormat(v___x_714_);
v___x_716_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_716_, 0, v___x_711_);
lean_ctor_set(v___x_716_, 1, v___x_715_);
v___x_717_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__9, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__9_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__9);
v___x_718_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_718_, 0, v___x_716_);
lean_ctor_set(v___x_718_, 1, v___x_717_);
v___x_719_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1(v___x_705_, v___x_718_, v___y_691_, v___y_692_, v___y_693_, v___y_694_);
if (lean_obj_tag(v___x_719_) == 0)
{
lean_object* v___x_721_; uint8_t v_isShared_722_; uint8_t v_isSharedCheck_726_; 
v_isSharedCheck_726_ = !lean_is_exclusive(v___x_719_);
if (v_isSharedCheck_726_ == 0)
{
lean_object* v_unused_727_; 
v_unused_727_ = lean_ctor_get(v___x_719_, 0);
lean_dec(v_unused_727_);
v___x_721_ = v___x_719_;
v_isShared_722_ = v_isSharedCheck_726_;
goto v_resetjp_720_;
}
else
{
lean_dec(v___x_719_);
v___x_721_ = lean_box(0);
v_isShared_722_ = v_isSharedCheck_726_;
goto v_resetjp_720_;
}
v_resetjp_720_:
{
lean_object* v___x_724_; 
if (v_isShared_722_ == 0)
{
lean_ctor_set(v___x_721_, 0, v_subgoals_566_);
v___x_724_ = v___x_721_;
goto v_reusejp_723_;
}
else
{
lean_object* v_reuseFailAlloc_725_; 
v_reuseFailAlloc_725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_725_, 0, v_subgoals_566_);
v___x_724_ = v_reuseFailAlloc_725_;
goto v_reusejp_723_;
}
v_reusejp_723_:
{
return v___x_724_;
}
}
}
else
{
lean_object* v_a_728_; lean_object* v___x_730_; uint8_t v_isShared_731_; uint8_t v_isSharedCheck_735_; 
lean_dec_ref(v_subgoals_566_);
v_a_728_ = lean_ctor_get(v___x_719_, 0);
v_isSharedCheck_735_ = !lean_is_exclusive(v___x_719_);
if (v_isSharedCheck_735_ == 0)
{
v___x_730_ = v___x_719_;
v_isShared_731_ = v_isSharedCheck_735_;
goto v_resetjp_729_;
}
else
{
lean_inc(v_a_728_);
lean_dec(v___x_719_);
v___x_730_ = lean_box(0);
v_isShared_731_ = v_isSharedCheck_735_;
goto v_resetjp_729_;
}
v_resetjp_729_:
{
lean_object* v___x_733_; 
if (v_isShared_731_ == 0)
{
v___x_733_ = v___x_730_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_734_; 
v_reuseFailAlloc_734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_734_, 0, v_a_728_);
v___x_733_ = v_reuseFailAlloc_734_;
goto v_reusejp_732_;
}
v_reusejp_732_:
{
return v___x_733_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_738_; lean_object* v___x_740_; uint8_t v_isShared_741_; uint8_t v_isSharedCheck_745_; 
lean_dec_ref(v_subgoals_566_);
v_a_738_ = lean_ctor_get(v___x_695_, 0);
v_isSharedCheck_745_ = !lean_is_exclusive(v___x_695_);
if (v_isSharedCheck_745_ == 0)
{
v___x_740_ = v___x_695_;
v_isShared_741_ = v_isSharedCheck_745_;
goto v_resetjp_739_;
}
else
{
lean_inc(v_a_738_);
lean_dec(v___x_695_);
v___x_740_ = lean_box(0);
v_isShared_741_ = v_isSharedCheck_745_;
goto v_resetjp_739_;
}
v_resetjp_739_:
{
lean_object* v___x_743_; 
if (v_isShared_741_ == 0)
{
v___x_743_ = v___x_740_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v_a_738_);
v___x_743_ = v_reuseFailAlloc_744_;
goto v_reusejp_742_;
}
v_reusejp_742_:
{
return v___x_743_;
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
size_t v_x_8928__boxed_1065_; size_t v_x_8929__boxed_1066_; lean_object* v_res_1067_; 
v_x_8928__boxed_1065_ = lean_unbox_usize(v_x_1061_);
lean_dec(v_x_1061_);
v_x_8929__boxed_1066_ = lean_unbox_usize(v_x_1062_);
lean_dec(v_x_1062_);
v_res_1067_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2(v_00_u03b2_1059_, v_x_1060_, v_x_8928__boxed_1065_, v_x_8929__boxed_1066_, v_x_1063_, v_x_1064_);
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
LEAN_EXPORT uint8_t l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___lam__0(lean_object* v_fvarId_1201_, lean_object* v_x_1202_){
_start:
{
uint8_t v___x_1203_; 
v___x_1203_ = l_Lean_instBEqFVarId_beq(v_fvarId_1201_, v_x_1202_);
return v___x_1203_;
}
}
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___lam__0___boxed(lean_object* v_fvarId_1204_, lean_object* v_x_1205_){
_start:
{
uint8_t v_res_1206_; lean_object* v_r_1207_; 
v_res_1206_ = l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___lam__0(v_fvarId_1204_, v_x_1205_);
lean_dec(v_x_1205_);
lean_dec(v_fvarId_1204_);
v_r_1207_ = lean_box(v_res_1206_);
return v_r_1207_;
}
}
LEAN_EXPORT uint8_t l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___lam__1(lean_object* v_x_1208_){
_start:
{
uint8_t v___x_1209_; 
v___x_1209_ = 0;
return v___x_1209_;
}
}
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___lam__1___boxed(lean_object* v_x_1210_){
_start:
{
uint8_t v_res_1211_; lean_object* v_r_1212_; 
v_res_1211_ = l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___lam__1(v_x_1210_);
lean_dec(v_x_1210_);
v_r_1212_ = lean_box(v_res_1211_);
return v_r_1212_;
}
}
static lean_object* _init_l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; 
v___x_1214_ = lean_box(0);
v___x_1215_ = lean_unsigned_to_nat(16u);
v___x_1216_ = lean_mk_array(v___x_1215_, v___x_1214_);
return v___x_1216_;
}
}
static lean_object* _init_l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; 
v___x_1217_ = lean_obj_once(&l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__1, &l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__1_once, _init_l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__1);
v___x_1218_ = lean_unsigned_to_nat(0u);
v___x_1219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1219_, 0, v___x_1218_);
lean_ctor_set(v___x_1219_, 1, v___x_1217_);
return v___x_1219_;
}
}
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg(lean_object* v_localDecl_1220_, lean_object* v_fvarId_1221_, uint8_t v_generalizeNondepLet_1222_, lean_object* v___y_1223_){
_start:
{
uint8_t v_fst_1226_; lean_object* v_snd_1227_; lean_object* v___y_1246_; lean_object* v___f_1250_; lean_object* v___f_1251_; 
v___f_1250_ = lean_alloc_closure((void*)(l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1250_, 0, v_fvarId_1221_);
v___f_1251_ = ((lean_object*)(l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__0));
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
v___x_1280_ = lean_obj_once(&l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__2, &l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__2_once, _init_l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__2);
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
v___x_1267_ = lean_st_ref_put(v___y_1223_, v___x_1266_);
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
v___x_1337_ = lean_obj_once(&l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__2, &l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__2_once, _init_l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__2);
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
v___x_1324_ = lean_st_ref_put(v___y_1223_, v___x_1323_);
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
v___x_1304_ = lean_obj_once(&l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__2, &l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__2_once, _init_l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__2);
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
v___x_1239_ = lean_st_ref_put(v___y_1223_, v___x_1238_);
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
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___boxed(lean_object* v_localDecl_1343_, lean_object* v_fvarId_1344_, lean_object* v_generalizeNondepLet_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_){
_start:
{
uint8_t v_generalizeNondepLet_boxed_1348_; lean_object* v_res_1349_; 
v_generalizeNondepLet_boxed_1348_ = lean_unbox(v_generalizeNondepLet_1345_);
v_res_1349_ = l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg(v_localDecl_1343_, v_fvarId_1344_, v_generalizeNondepLet_boxed_1348_, v___y_1346_);
lean_dec(v___y_1346_);
return v_res_1349_;
}
}
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1(lean_object* v_localDecl_1350_, lean_object* v_fvarId_1351_, uint8_t v_generalizeNondepLet_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_){
_start:
{
lean_object* v___x_1358_; 
v___x_1358_ = l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg(v_localDecl_1350_, v_fvarId_1351_, v_generalizeNondepLet_1352_, v___y_1354_);
return v___x_1358_;
}
}
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___boxed(lean_object* v_localDecl_1359_, lean_object* v_fvarId_1360_, lean_object* v_generalizeNondepLet_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_){
_start:
{
uint8_t v_generalizeNondepLet_boxed_1367_; lean_object* v_res_1368_; 
v_generalizeNondepLet_boxed_1367_ = lean_unbox(v_generalizeNondepLet_1361_);
v_res_1368_ = l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1(v_localDecl_1359_, v_fvarId_1360_, v_generalizeNondepLet_boxed_1367_, v___y_1362_, v___y_1363_, v___y_1364_, v___y_1365_);
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
v___f_1400_ = ((lean_object*)(l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__0));
v___f_1401_ = lean_alloc_closure((void*)(l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1401_, 0, v_fvarId_1370_);
v___x_1402_ = lean_obj_once(&l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__2, &l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__2_once, _init_l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg___closed__2);
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
v___x_1387_ = lean_st_ref_put(v___y_1371_, v___x_1386_);
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
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_Meta_getMajorTypeIndices_spec__0(lean_object* v_a_1429_, lean_object* v_x_1430_){
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
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_Meta_getMajorTypeIndices_spec__0___boxed(lean_object* v_a_1436_, lean_object* v_x_1437_){
_start:
{
uint8_t v_res_1438_; lean_object* v_r_1439_; 
v_res_1438_ = l_List_elem___at___00Lean_Meta_getMajorTypeIndices_spec__0(v_a_1436_, v_x_1437_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg(lean_object* v_majorTypeArgs_1452_, lean_object* v_idxPos_1453_, lean_object* v_recursorInfo_1454_, lean_object* v_idx_1455_, lean_object* v_tacticName_1456_, lean_object* v_mvarId_1457_, lean_object* v_majorType_1458_, lean_object* v_n_1459_, lean_object* v_i_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_){
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
lean_dec(v_mvarId_1457_);
lean_dec(v_tacticName_1456_);
lean_dec_ref(v_idx_1455_);
v___x_1468_ = lean_box(0);
v___x_1469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1469_, 0, v___x_1468_);
return v___x_1469_;
}
else
{
lean_object* v_one_1470_; lean_object* v_n_1471_; lean_object* v___y_1473_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v_arg_1477_; uint8_t v___x_1478_; lean_object* v___y_1480_; lean_object* v___y_1481_; lean_object* v___y_1482_; lean_object* v___y_1483_; uint8_t v___x_1524_; lean_object* v___y_1526_; lean_object* v___y_1527_; lean_object* v___y_1528_; lean_object* v___y_1529_; uint8_t v___x_1549_; 
v_one_1470_ = lean_unsigned_to_nat(1u);
v_n_1471_ = lean_nat_sub(v_i_1460_, v_one_1470_);
lean_dec(v_i_1460_);
v___x_1475_ = lean_nat_sub(v_n_1459_, v_n_1471_);
v___x_1476_ = lean_nat_sub(v___x_1475_, v_one_1470_);
lean_dec(v___x_1475_);
v_arg_1477_ = lean_array_fget_borrowed(v_majorTypeArgs_1452_, v___x_1476_);
v___x_1478_ = lean_nat_dec_lt(v_idxPos_1453_, v___x_1476_);
v___x_1524_ = lean_nat_dec_lt(v___x_1476_, v_idxPos_1453_);
v___x_1549_ = lean_nat_dec_eq(v___x_1476_, v_idxPos_1453_);
if (v___x_1549_ == 0)
{
uint8_t v___x_1550_; 
v___x_1550_ = lean_expr_eqv(v_arg_1477_, v_idx_1455_);
if (v___x_1550_ == 0)
{
v___y_1526_ = v___y_1461_;
v___y_1527_ = v___y_1462_;
v___y_1528_ = v___y_1463_;
v___y_1529_ = v___y_1464_;
goto v___jp_1525_;
}
else
{
lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; 
v___x_1551_ = lean_obj_once(&l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1, &l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1_once, _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1);
lean_inc_ref(v_idx_1455_);
v___x_1552_ = l_Lean_MessageData_ofExpr(v_idx_1455_);
v___x_1553_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1553_, 0, v___x_1551_);
lean_ctor_set(v___x_1553_, 1, v___x_1552_);
v___x_1554_ = lean_obj_once(&l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__7, &l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__7_once, _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__7);
v___x_1555_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1555_, 0, v___x_1553_);
lean_ctor_set(v___x_1555_, 1, v___x_1554_);
lean_inc_ref(v_majorType_1458_);
v___x_1556_ = l_Lean_indentExpr(v_majorType_1458_);
v___x_1557_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1557_, 0, v___x_1555_);
lean_ctor_set(v___x_1557_, 1, v___x_1556_);
v___x_1558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1558_, 0, v___x_1557_);
lean_inc(v_mvarId_1457_);
lean_inc(v_tacticName_1456_);
v___x_1559_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1456_, v_mvarId_1457_, v___x_1558_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_);
if (lean_obj_tag(v___x_1559_) == 0)
{
lean_dec_ref_known(v___x_1559_, 1);
v___y_1526_ = v___y_1461_;
v___y_1527_ = v___y_1462_;
v___y_1528_ = v___y_1463_;
v___y_1529_ = v___y_1464_;
goto v___jp_1525_;
}
else
{
lean_dec(v___x_1476_);
v___y_1473_ = v___x_1559_;
goto v___jp_1472_;
}
}
}
else
{
v___y_1526_ = v___y_1461_;
v___y_1527_ = v___y_1462_;
v___y_1528_ = v___y_1463_;
v___y_1529_ = v___y_1464_;
goto v___jp_1525_;
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
lean_dec(v_mvarId_1457_);
lean_dec(v_tacticName_1456_);
lean_dec_ref(v_idx_1455_);
return v___y_1473_;
}
}
v___jp_1479_:
{
if (v___x_1478_ == 0)
{
lean_dec(v___x_1476_);
v_i_1460_ = v_n_1471_;
goto _start;
}
else
{
lean_object* v_indicesPos_1485_; uint8_t v___x_1486_; 
v_indicesPos_1485_ = lean_ctor_get(v_recursorInfo_1454_, 6);
v___x_1486_ = l_List_elem___at___00Lean_Meta_getMajorTypeIndices_spec__0(v___x_1476_, v_indicesPos_1485_);
if (v___x_1486_ == 0)
{
lean_dec(v___x_1476_);
v_i_1460_ = v_n_1471_;
goto _start;
}
else
{
uint8_t v___x_1488_; 
v___x_1488_ = l_Lean_Expr_isFVar(v_arg_1477_);
if (v___x_1488_ == 0)
{
lean_dec(v___x_1476_);
v_i_1460_ = v_n_1471_;
goto _start;
}
else
{
lean_object* v___x_1490_; lean_object* v___x_1491_; 
v___x_1490_ = l_Lean_Expr_fvarId_x21(v_idx_1455_);
v___x_1491_ = l_Lean_FVarId_getDecl___redArg(v___x_1490_, v___y_1480_, v___y_1482_, v___y_1483_);
if (lean_obj_tag(v___x_1491_) == 0)
{
lean_object* v_a_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v_a_1495_; lean_object* v___x_1497_; uint8_t v_isShared_1498_; uint8_t v_isSharedCheck_1515_; 
v_a_1492_ = lean_ctor_get(v___x_1491_, 0);
lean_inc(v_a_1492_);
lean_dec_ref_known(v___x_1491_, 1);
v___x_1493_ = l_Lean_Expr_fvarId_x21(v_arg_1477_);
v___x_1494_ = l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__1___redArg(v_a_1492_, v___x_1493_, v___x_1486_, v___y_1481_);
v_a_1495_ = lean_ctor_get(v___x_1494_, 0);
v_isSharedCheck_1515_ = !lean_is_exclusive(v___x_1494_);
if (v_isSharedCheck_1515_ == 0)
{
v___x_1497_ = v___x_1494_;
v_isShared_1498_ = v_isSharedCheck_1515_;
goto v_resetjp_1496_;
}
else
{
lean_inc(v_a_1495_);
lean_dec(v___x_1494_);
v___x_1497_ = lean_box(0);
v_isShared_1498_ = v_isSharedCheck_1515_;
goto v_resetjp_1496_;
}
v_resetjp_1496_:
{
uint8_t v___x_1499_; 
v___x_1499_ = lean_unbox(v_a_1495_);
lean_dec(v_a_1495_);
if (v___x_1499_ == 0)
{
lean_del_object(v___x_1497_);
lean_dec(v___x_1476_);
v_i_1460_ = v_n_1471_;
goto _start;
}
else
{
lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1509_; 
v___x_1501_ = lean_obj_once(&l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1, &l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1_once, _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1);
lean_inc_ref(v_idx_1455_);
v___x_1502_ = l_Lean_MessageData_ofExpr(v_idx_1455_);
v___x_1503_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1503_, 0, v___x_1501_);
lean_ctor_set(v___x_1503_, 1, v___x_1502_);
v___x_1504_ = lean_obj_once(&l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__3, &l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__3_once, _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__3);
v___x_1505_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1505_, 0, v___x_1503_);
lean_ctor_set(v___x_1505_, 1, v___x_1504_);
v___x_1506_ = lean_nat_add(v___x_1476_, v_one_1470_);
lean_dec(v___x_1476_);
v___x_1507_ = l_Nat_reprFast(v___x_1506_);
if (v_isShared_1498_ == 0)
{
lean_ctor_set_tag(v___x_1497_, 3);
lean_ctor_set(v___x_1497_, 0, v___x_1507_);
v___x_1509_ = v___x_1497_;
goto v_reusejp_1508_;
}
else
{
lean_object* v_reuseFailAlloc_1514_; 
v_reuseFailAlloc_1514_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1514_, 0, v___x_1507_);
v___x_1509_ = v_reuseFailAlloc_1514_;
goto v_reusejp_1508_;
}
v_reusejp_1508_:
{
lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; 
v___x_1510_ = l_Lean_MessageData_ofFormat(v___x_1509_);
v___x_1511_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1511_, 0, v___x_1505_);
lean_ctor_set(v___x_1511_, 1, v___x_1510_);
v___x_1512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1512_, 0, v___x_1511_);
lean_inc(v_mvarId_1457_);
lean_inc(v_tacticName_1456_);
v___x_1513_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1456_, v_mvarId_1457_, v___x_1512_, v___y_1480_, v___y_1481_, v___y_1482_, v___y_1483_);
v___y_1473_ = v___x_1513_;
goto v___jp_1472_;
}
}
}
}
else
{
lean_object* v_a_1516_; lean_object* v___x_1518_; uint8_t v_isShared_1519_; uint8_t v_isSharedCheck_1523_; 
lean_dec(v___x_1476_);
lean_dec(v_n_1471_);
lean_dec_ref(v_majorType_1458_);
lean_dec(v_mvarId_1457_);
lean_dec(v_tacticName_1456_);
lean_dec_ref(v_idx_1455_);
v_a_1516_ = lean_ctor_get(v___x_1491_, 0);
v_isSharedCheck_1523_ = !lean_is_exclusive(v___x_1491_);
if (v_isSharedCheck_1523_ == 0)
{
v___x_1518_ = v___x_1491_;
v_isShared_1519_ = v_isSharedCheck_1523_;
goto v_resetjp_1517_;
}
else
{
lean_inc(v_a_1516_);
lean_dec(v___x_1491_);
v___x_1518_ = lean_box(0);
v_isShared_1519_ = v_isSharedCheck_1523_;
goto v_resetjp_1517_;
}
v_resetjp_1517_:
{
lean_object* v___x_1521_; 
if (v_isShared_1519_ == 0)
{
v___x_1521_ = v___x_1518_;
goto v_reusejp_1520_;
}
else
{
lean_object* v_reuseFailAlloc_1522_; 
v_reuseFailAlloc_1522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1522_, 0, v_a_1516_);
v___x_1521_ = v_reuseFailAlloc_1522_;
goto v_reusejp_1520_;
}
v_reusejp_1520_:
{
return v___x_1521_;
}
}
}
}
}
}
}
v___jp_1525_:
{
if (v___x_1524_ == 0)
{
v___y_1480_ = v___y_1526_;
v___y_1481_ = v___y_1527_;
v___y_1482_ = v___y_1528_;
v___y_1483_ = v___y_1529_;
goto v___jp_1479_;
}
else
{
lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v_a_1532_; lean_object* v___x_1534_; uint8_t v_isShared_1535_; uint8_t v_isSharedCheck_1548_; 
v___x_1530_ = l_Lean_Expr_fvarId_x21(v_idx_1455_);
lean_inc(v_arg_1477_);
v___x_1531_ = l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2___redArg(v_arg_1477_, v___x_1530_, v___y_1527_);
v_a_1532_ = lean_ctor_get(v___x_1531_, 0);
v_isSharedCheck_1548_ = !lean_is_exclusive(v___x_1531_);
if (v_isSharedCheck_1548_ == 0)
{
v___x_1534_ = v___x_1531_;
v_isShared_1535_ = v_isSharedCheck_1548_;
goto v_resetjp_1533_;
}
else
{
lean_inc(v_a_1532_);
lean_dec(v___x_1531_);
v___x_1534_ = lean_box(0);
v_isShared_1535_ = v_isSharedCheck_1548_;
goto v_resetjp_1533_;
}
v_resetjp_1533_:
{
uint8_t v___x_1536_; 
v___x_1536_ = lean_unbox(v_a_1532_);
lean_dec(v_a_1532_);
if (v___x_1536_ == 0)
{
lean_del_object(v___x_1534_);
v___y_1480_ = v___y_1526_;
v___y_1481_ = v___y_1527_;
v___y_1482_ = v___y_1528_;
v___y_1483_ = v___y_1529_;
goto v___jp_1479_;
}
else
{
lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1545_; 
v___x_1537_ = lean_obj_once(&l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1, &l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1_once, _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1);
lean_inc_ref(v_idx_1455_);
v___x_1538_ = l_Lean_MessageData_ofExpr(v_idx_1455_);
v___x_1539_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1539_, 0, v___x_1537_);
lean_ctor_set(v___x_1539_, 1, v___x_1538_);
v___x_1540_ = lean_obj_once(&l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__5, &l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__5_once, _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__5);
v___x_1541_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1541_, 0, v___x_1539_);
lean_ctor_set(v___x_1541_, 1, v___x_1540_);
lean_inc_ref(v_majorType_1458_);
v___x_1542_ = l_Lean_indentExpr(v_majorType_1458_);
v___x_1543_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1543_, 0, v___x_1541_);
lean_ctor_set(v___x_1543_, 1, v___x_1542_);
if (v_isShared_1535_ == 0)
{
lean_ctor_set_tag(v___x_1534_, 1);
lean_ctor_set(v___x_1534_, 0, v___x_1543_);
v___x_1545_ = v___x_1534_;
goto v_reusejp_1544_;
}
else
{
lean_object* v_reuseFailAlloc_1547_; 
v_reuseFailAlloc_1547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1547_, 0, v___x_1543_);
v___x_1545_ = v_reuseFailAlloc_1547_;
goto v_reusejp_1544_;
}
v_reusejp_1544_:
{
lean_object* v___x_1546_; 
lean_inc(v_mvarId_1457_);
lean_inc(v_tacticName_1456_);
v___x_1546_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1456_, v_mvarId_1457_, v___x_1545_, v___y_1526_, v___y_1527_, v___y_1528_, v___y_1529_);
if (lean_obj_tag(v___x_1546_) == 0)
{
lean_dec_ref_known(v___x_1546_, 1);
v___y_1480_ = v___y_1526_;
v___y_1481_ = v___y_1527_;
v___y_1482_ = v___y_1528_;
v___y_1483_ = v___y_1529_;
goto v___jp_1479_;
}
else
{
lean_dec(v___x_1476_);
v___y_1473_ = v___x_1546_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___boxed(lean_object* v_majorTypeArgs_1560_, lean_object* v_idxPos_1561_, lean_object* v_recursorInfo_1562_, lean_object* v_idx_1563_, lean_object* v_tacticName_1564_, lean_object* v_mvarId_1565_, lean_object* v_majorType_1566_, lean_object* v_n_1567_, lean_object* v_i_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_){
_start:
{
lean_object* v_res_1574_; 
v_res_1574_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg(v_majorTypeArgs_1560_, v_idxPos_1561_, v_recursorInfo_1562_, v_idx_1563_, v_tacticName_1564_, v_mvarId_1565_, v_majorType_1566_, v_n_1567_, v_i_1568_, v___y_1569_, v___y_1570_, v___y_1571_, v___y_1572_);
lean_dec(v___y_1572_);
lean_dec_ref(v___y_1571_);
lean_dec(v___y_1570_);
lean_dec_ref(v___y_1569_);
lean_dec(v_n_1567_);
lean_dec_ref(v_recursorInfo_1562_);
lean_dec(v_idxPos_1561_);
lean_dec_ref(v_majorTypeArgs_1560_);
return v_res_1574_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__1(void){
_start:
{
lean_object* v___x_1576_; lean_object* v___x_1577_; 
v___x_1576_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__0));
v___x_1577_ = l_Lean_stringToMessageData(v___x_1576_);
return v___x_1577_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__3(void){
_start:
{
lean_object* v___x_1579_; lean_object* v___x_1580_; 
v___x_1579_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__2));
v___x_1580_ = l_Lean_stringToMessageData(v___x_1579_);
return v___x_1580_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__5(void){
_start:
{
lean_object* v___x_1582_; lean_object* v___x_1583_; 
v___x_1582_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__4));
v___x_1583_ = l_Lean_stringToMessageData(v___x_1582_);
return v___x_1583_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4(lean_object* v_majorTypeArgs_1584_, lean_object* v_recursorInfo_1585_, lean_object* v_tacticName_1586_, lean_object* v_mvarId_1587_, lean_object* v_majorType_1588_, size_t v_sz_1589_, size_t v_i_1590_, lean_object* v_bs_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_){
_start:
{
uint8_t v___x_1597_; 
v___x_1597_ = lean_usize_dec_lt(v_i_1590_, v_sz_1589_);
if (v___x_1597_ == 0)
{
lean_object* v___x_1598_; 
lean_dec_ref(v_majorType_1588_);
lean_dec(v_mvarId_1587_);
lean_dec(v_tacticName_1586_);
v___x_1598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1598_, 0, v_bs_1591_);
return v___x_1598_;
}
else
{
lean_object* v_v_1599_; lean_object* v___x_1600_; lean_object* v_bs_x27_1601_; lean_object* v_a_1603_; lean_object* v___x_1608_; uint8_t v___x_1609_; 
v_v_1599_ = lean_array_uget(v_bs_1591_, v_i_1590_);
v___x_1600_ = lean_unsigned_to_nat(0u);
v_bs_x27_1601_ = lean_array_uset(v_bs_1591_, v_i_1590_, v___x_1600_);
v___x_1608_ = lean_array_get_size(v_majorTypeArgs_1584_);
v___x_1609_ = lean_nat_dec_le(v___x_1608_, v_v_1599_);
if (v___x_1609_ == 0)
{
lean_object* v_idx_1610_; lean_object* v___y_1612_; lean_object* v___y_1613_; lean_object* v___y_1614_; lean_object* v___y_1615_; uint8_t v___x_1625_; 
v_idx_1610_ = lean_array_fget_borrowed(v_majorTypeArgs_1584_, v_v_1599_);
v___x_1625_ = l_Lean_Expr_isFVar(v_idx_1610_);
if (v___x_1625_ == 0)
{
lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; 
v___x_1626_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__1);
lean_inc(v_idx_1610_);
v___x_1627_ = l_Lean_MessageData_ofExpr(v_idx_1610_);
v___x_1628_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1628_, 0, v___x_1626_);
lean_ctor_set(v___x_1628_, 1, v___x_1627_);
v___x_1629_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__3);
v___x_1630_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1630_, 0, v___x_1628_);
lean_ctor_set(v___x_1630_, 1, v___x_1629_);
lean_inc_ref(v_majorType_1588_);
v___x_1631_ = l_Lean_indentExpr(v_majorType_1588_);
v___x_1632_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1632_, 0, v___x_1630_);
lean_ctor_set(v___x_1632_, 1, v___x_1631_);
v___x_1633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1633_, 0, v___x_1632_);
lean_inc(v_mvarId_1587_);
lean_inc(v_tacticName_1586_);
v___x_1634_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1586_, v_mvarId_1587_, v___x_1633_, v___y_1592_, v___y_1593_, v___y_1594_, v___y_1595_);
if (lean_obj_tag(v___x_1634_) == 0)
{
lean_dec_ref_known(v___x_1634_, 1);
v___y_1612_ = v___y_1592_;
v___y_1613_ = v___y_1593_;
v___y_1614_ = v___y_1594_;
v___y_1615_ = v___y_1595_;
goto v___jp_1611_;
}
else
{
lean_object* v_a_1635_; lean_object* v___x_1637_; uint8_t v_isShared_1638_; uint8_t v_isSharedCheck_1642_; 
lean_dec_ref(v_bs_x27_1601_);
lean_dec(v_v_1599_);
lean_dec_ref(v_majorType_1588_);
lean_dec(v_mvarId_1587_);
lean_dec(v_tacticName_1586_);
v_a_1635_ = lean_ctor_get(v___x_1634_, 0);
v_isSharedCheck_1642_ = !lean_is_exclusive(v___x_1634_);
if (v_isSharedCheck_1642_ == 0)
{
v___x_1637_ = v___x_1634_;
v_isShared_1638_ = v_isSharedCheck_1642_;
goto v_resetjp_1636_;
}
else
{
lean_inc(v_a_1635_);
lean_dec(v___x_1634_);
v___x_1637_ = lean_box(0);
v_isShared_1638_ = v_isSharedCheck_1642_;
goto v_resetjp_1636_;
}
v_resetjp_1636_:
{
lean_object* v___x_1640_; 
if (v_isShared_1638_ == 0)
{
v___x_1640_ = v___x_1637_;
goto v_reusejp_1639_;
}
else
{
lean_object* v_reuseFailAlloc_1641_; 
v_reuseFailAlloc_1641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1641_, 0, v_a_1635_);
v___x_1640_ = v_reuseFailAlloc_1641_;
goto v_reusejp_1639_;
}
v_reusejp_1639_:
{
return v___x_1640_;
}
}
}
}
else
{
v___y_1612_ = v___y_1592_;
v___y_1613_ = v___y_1593_;
v___y_1614_ = v___y_1594_;
v___y_1615_ = v___y_1595_;
goto v___jp_1611_;
}
v___jp_1611_:
{
lean_object* v___x_1616_; 
lean_inc_ref(v_majorType_1588_);
lean_inc(v_mvarId_1587_);
lean_inc(v_tacticName_1586_);
lean_inc(v_idx_1610_);
v___x_1616_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg(v_majorTypeArgs_1584_, v_v_1599_, v_recursorInfo_1585_, v_idx_1610_, v_tacticName_1586_, v_mvarId_1587_, v_majorType_1588_, v___x_1608_, v___x_1608_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_);
lean_dec(v_v_1599_);
if (lean_obj_tag(v___x_1616_) == 0)
{
lean_dec_ref_known(v___x_1616_, 1);
lean_inc(v_idx_1610_);
v_a_1603_ = v_idx_1610_;
goto v___jp_1602_;
}
else
{
lean_object* v_a_1617_; lean_object* v___x_1619_; uint8_t v_isShared_1620_; uint8_t v_isSharedCheck_1624_; 
lean_dec_ref(v_bs_x27_1601_);
lean_dec_ref(v_majorType_1588_);
lean_dec(v_mvarId_1587_);
lean_dec(v_tacticName_1586_);
v_a_1617_ = lean_ctor_get(v___x_1616_, 0);
v_isSharedCheck_1624_ = !lean_is_exclusive(v___x_1616_);
if (v_isSharedCheck_1624_ == 0)
{
v___x_1619_ = v___x_1616_;
v_isShared_1620_ = v_isSharedCheck_1624_;
goto v_resetjp_1618_;
}
else
{
lean_inc(v_a_1617_);
lean_dec(v___x_1616_);
v___x_1619_ = lean_box(0);
v_isShared_1620_ = v_isSharedCheck_1624_;
goto v_resetjp_1618_;
}
v_resetjp_1618_:
{
lean_object* v___x_1622_; 
if (v_isShared_1620_ == 0)
{
v___x_1622_ = v___x_1619_;
goto v_reusejp_1621_;
}
else
{
lean_object* v_reuseFailAlloc_1623_; 
v_reuseFailAlloc_1623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1623_, 0, v_a_1617_);
v___x_1622_ = v_reuseFailAlloc_1623_;
goto v_reusejp_1621_;
}
v_reusejp_1621_:
{
return v___x_1622_;
}
}
}
}
}
else
{
lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; 
lean_dec(v_v_1599_);
v___x_1643_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__5, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__5);
lean_inc_ref(v_majorType_1588_);
v___x_1644_ = l_Lean_indentExpr(v_majorType_1588_);
v___x_1645_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1645_, 0, v___x_1643_);
lean_ctor_set(v___x_1645_, 1, v___x_1644_);
v___x_1646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1646_, 0, v___x_1645_);
lean_inc(v_mvarId_1587_);
lean_inc(v_tacticName_1586_);
v___x_1647_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1586_, v_mvarId_1587_, v___x_1646_, v___y_1592_, v___y_1593_, v___y_1594_, v___y_1595_);
if (lean_obj_tag(v___x_1647_) == 0)
{
lean_object* v_a_1648_; 
v_a_1648_ = lean_ctor_get(v___x_1647_, 0);
lean_inc(v_a_1648_);
lean_dec_ref_known(v___x_1647_, 1);
v_a_1603_ = v_a_1648_;
goto v___jp_1602_;
}
else
{
lean_object* v_a_1649_; lean_object* v___x_1651_; uint8_t v_isShared_1652_; uint8_t v_isSharedCheck_1656_; 
lean_dec_ref(v_bs_x27_1601_);
lean_dec_ref(v_majorType_1588_);
lean_dec(v_mvarId_1587_);
lean_dec(v_tacticName_1586_);
v_a_1649_ = lean_ctor_get(v___x_1647_, 0);
v_isSharedCheck_1656_ = !lean_is_exclusive(v___x_1647_);
if (v_isSharedCheck_1656_ == 0)
{
v___x_1651_ = v___x_1647_;
v_isShared_1652_ = v_isSharedCheck_1656_;
goto v_resetjp_1650_;
}
else
{
lean_inc(v_a_1649_);
lean_dec(v___x_1647_);
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
v___jp_1602_:
{
size_t v___x_1604_; size_t v___x_1605_; lean_object* v___x_1606_; 
v___x_1604_ = ((size_t)1ULL);
v___x_1605_ = lean_usize_add(v_i_1590_, v___x_1604_);
v___x_1606_ = lean_array_uset(v_bs_x27_1601_, v_i_1590_, v_a_1603_);
v_i_1590_ = v___x_1605_;
v_bs_1591_ = v___x_1606_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___boxed(lean_object* v_majorTypeArgs_1657_, lean_object* v_recursorInfo_1658_, lean_object* v_tacticName_1659_, lean_object* v_mvarId_1660_, lean_object* v_majorType_1661_, lean_object* v_sz_1662_, lean_object* v_i_1663_, lean_object* v_bs_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_){
_start:
{
size_t v_sz_boxed_1670_; size_t v_i_boxed_1671_; lean_object* v_res_1672_; 
v_sz_boxed_1670_ = lean_unbox_usize(v_sz_1662_);
lean_dec(v_sz_1662_);
v_i_boxed_1671_ = lean_unbox_usize(v_i_1663_);
lean_dec(v_i_1663_);
v_res_1672_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4(v_majorTypeArgs_1657_, v_recursorInfo_1658_, v_tacticName_1659_, v_mvarId_1660_, v_majorType_1661_, v_sz_boxed_1670_, v_i_boxed_1671_, v_bs_1664_, v___y_1665_, v___y_1666_, v___y_1667_, v___y_1668_);
lean_dec(v___y_1668_);
lean_dec_ref(v___y_1667_);
lean_dec(v___y_1666_);
lean_dec_ref(v___y_1665_);
lean_dec_ref(v_recursorInfo_1658_);
lean_dec_ref(v_majorTypeArgs_1657_);
return v_res_1672_;
}
}
static lean_object* _init_l_Lean_Meta_getMajorTypeIndices___closed__0(void){
_start:
{
lean_object* v___x_1673_; lean_object* v_dummy_1674_; 
v___x_1673_ = lean_box(0);
v_dummy_1674_ = l_Lean_Expr_sort___override(v___x_1673_);
return v_dummy_1674_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMajorTypeIndices(lean_object* v_mvarId_1675_, lean_object* v_tacticName_1676_, lean_object* v_recursorInfo_1677_, lean_object* v_majorType_1678_, lean_object* v_a_1679_, lean_object* v_a_1680_, lean_object* v_a_1681_, lean_object* v_a_1682_){
_start:
{
lean_object* v_indicesPos_1684_; lean_object* v_nargs_1685_; lean_object* v_dummy_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v_majorTypeArgs_1690_; lean_object* v___x_1691_; size_t v_sz_1692_; size_t v___x_1693_; lean_object* v___x_1694_; 
v_indicesPos_1684_ = lean_ctor_get(v_recursorInfo_1677_, 6);
v_nargs_1685_ = l_Lean_Expr_getAppNumArgs(v_majorType_1678_);
v_dummy_1686_ = lean_obj_once(&l_Lean_Meta_getMajorTypeIndices___closed__0, &l_Lean_Meta_getMajorTypeIndices___closed__0_once, _init_l_Lean_Meta_getMajorTypeIndices___closed__0);
lean_inc(v_nargs_1685_);
v___x_1687_ = lean_mk_array(v_nargs_1685_, v_dummy_1686_);
v___x_1688_ = lean_unsigned_to_nat(1u);
v___x_1689_ = lean_nat_sub(v_nargs_1685_, v___x_1688_);
lean_dec(v_nargs_1685_);
lean_inc_ref(v_majorType_1678_);
v_majorTypeArgs_1690_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_majorType_1678_, v___x_1687_, v___x_1689_);
lean_inc(v_indicesPos_1684_);
v___x_1691_ = lean_array_mk(v_indicesPos_1684_);
v_sz_1692_ = lean_array_size(v___x_1691_);
v___x_1693_ = ((size_t)0ULL);
v___x_1694_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4(v_majorTypeArgs_1690_, v_recursorInfo_1677_, v_tacticName_1676_, v_mvarId_1675_, v_majorType_1678_, v_sz_1692_, v___x_1693_, v___x_1691_, v_a_1679_, v_a_1680_, v_a_1681_, v_a_1682_);
lean_dec_ref(v_recursorInfo_1677_);
lean_dec_ref(v_majorTypeArgs_1690_);
return v___x_1694_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMajorTypeIndices___boxed(lean_object* v_mvarId_1695_, lean_object* v_tacticName_1696_, lean_object* v_recursorInfo_1697_, lean_object* v_majorType_1698_, lean_object* v_a_1699_, lean_object* v_a_1700_, lean_object* v_a_1701_, lean_object* v_a_1702_, lean_object* v_a_1703_){
_start:
{
lean_object* v_res_1704_; 
v_res_1704_ = l_Lean_Meta_getMajorTypeIndices(v_mvarId_1695_, v_tacticName_1696_, v_recursorInfo_1697_, v_majorType_1698_, v_a_1699_, v_a_1700_, v_a_1701_, v_a_1702_);
lean_dec(v_a_1702_);
lean_dec_ref(v_a_1701_);
lean_dec(v_a_1700_);
lean_dec_ref(v_a_1699_);
return v_res_1704_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3(lean_object* v_majorTypeArgs_1705_, lean_object* v_idxPos_1706_, lean_object* v_recursorInfo_1707_, lean_object* v_idx_1708_, lean_object* v_tacticName_1709_, lean_object* v_mvarId_1710_, lean_object* v_majorType_1711_, lean_object* v_n_1712_, lean_object* v_i_1713_, lean_object* v_a_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_){
_start:
{
lean_object* v___x_1720_; 
v___x_1720_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg(v_majorTypeArgs_1705_, v_idxPos_1706_, v_recursorInfo_1707_, v_idx_1708_, v_tacticName_1709_, v_mvarId_1710_, v_majorType_1711_, v_n_1712_, v_i_1713_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_);
return v___x_1720_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___boxed(lean_object* v_majorTypeArgs_1721_, lean_object* v_idxPos_1722_, lean_object* v_recursorInfo_1723_, lean_object* v_idx_1724_, lean_object* v_tacticName_1725_, lean_object* v_mvarId_1726_, lean_object* v_majorType_1727_, lean_object* v_n_1728_, lean_object* v_i_1729_, lean_object* v_a_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_){
_start:
{
lean_object* v_res_1736_; 
v_res_1736_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3(v_majorTypeArgs_1721_, v_idxPos_1722_, v_recursorInfo_1723_, v_idx_1724_, v_tacticName_1725_, v_mvarId_1726_, v_majorType_1727_, v_n_1728_, v_i_1729_, v_a_1730_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_);
lean_dec(v___y_1734_);
lean_dec_ref(v___y_1733_);
lean_dec(v___y_1732_);
lean_dec_ref(v___y_1731_);
lean_dec(v_n_1728_);
lean_dec_ref(v_recursorInfo_1723_);
lean_dec(v_idxPos_1722_);
lean_dec_ref(v_majorTypeArgs_1721_);
return v_res_1736_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1___redArg(lean_object* v_name_1737_, lean_object* v_msg_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_){
_start:
{
lean_object* v_ref_1744_; lean_object* v_msg_1745_; lean_object* v___x_1746_; lean_object* v_a_1747_; lean_object* v___x_1749_; uint8_t v_isShared_1750_; uint8_t v_isSharedCheck_1755_; 
v_ref_1744_ = lean_ctor_get(v___y_1741_, 5);
v_msg_1745_ = l_Lean_MessageData_tagWithErrorName(v_msg_1738_, v_name_1737_);
v___x_1746_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1_spec__2(v_msg_1745_, v___y_1739_, v___y_1740_, v___y_1741_, v___y_1742_);
v_a_1747_ = lean_ctor_get(v___x_1746_, 0);
v_isSharedCheck_1755_ = !lean_is_exclusive(v___x_1746_);
if (v_isSharedCheck_1755_ == 0)
{
v___x_1749_ = v___x_1746_;
v_isShared_1750_ = v_isSharedCheck_1755_;
goto v_resetjp_1748_;
}
else
{
lean_inc(v_a_1747_);
lean_dec(v___x_1746_);
v___x_1749_ = lean_box(0);
v_isShared_1750_ = v_isSharedCheck_1755_;
goto v_resetjp_1748_;
}
v_resetjp_1748_:
{
lean_object* v___x_1751_; lean_object* v___x_1753_; 
lean_inc(v_ref_1744_);
v___x_1751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1751_, 0, v_ref_1744_);
lean_ctor_set(v___x_1751_, 1, v_a_1747_);
if (v_isShared_1750_ == 0)
{
lean_ctor_set_tag(v___x_1749_, 1);
lean_ctor_set(v___x_1749_, 0, v___x_1751_);
v___x_1753_ = v___x_1749_;
goto v_reusejp_1752_;
}
else
{
lean_object* v_reuseFailAlloc_1754_; 
v_reuseFailAlloc_1754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1754_, 0, v___x_1751_);
v___x_1753_ = v_reuseFailAlloc_1754_;
goto v_reusejp_1752_;
}
v_reusejp_1752_:
{
return v___x_1753_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1___redArg___boxed(lean_object* v_name_1756_, lean_object* v_msg_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_){
_start:
{
lean_object* v_res_1763_; 
v_res_1763_ = l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1___redArg(v_name_1756_, v_msg_1757_, v___y_1758_, v___y_1759_, v___y_1760_, v___y_1761_);
lean_dec(v___y_1761_);
lean_dec_ref(v___y_1760_);
lean_dec(v___y_1759_);
lean_dec_ref(v___y_1758_);
return v_res_1763_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Meta_mkRecursorAppPrefix_spec__0(lean_object* v_a_1764_, lean_object* v___x_1765_, lean_object* v_tacticName_1766_, lean_object* v_mvarId_1767_, lean_object* v_x_1768_, lean_object* v_x_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_){
_start:
{
if (lean_obj_tag(v_x_1769_) == 0)
{
lean_object* v___x_1775_; 
lean_dec(v_mvarId_1767_);
lean_dec(v_tacticName_1766_);
lean_dec(v_a_1764_);
v___x_1775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1775_, 0, v_x_1768_);
return v___x_1775_;
}
else
{
lean_object* v_head_1776_; 
v_head_1776_ = lean_ctor_get(v_x_1769_, 0);
if (lean_obj_tag(v_head_1776_) == 0)
{
lean_object* v_tail_1777_; lean_object* v_fst_1778_; lean_object* v___x_1780_; uint8_t v_isShared_1781_; uint8_t v_isSharedCheck_1789_; 
v_tail_1777_ = lean_ctor_get(v_x_1769_, 1);
v_fst_1778_ = lean_ctor_get(v_x_1768_, 0);
v_isSharedCheck_1789_ = !lean_is_exclusive(v_x_1768_);
if (v_isSharedCheck_1789_ == 0)
{
lean_object* v_unused_1790_; 
v_unused_1790_ = lean_ctor_get(v_x_1768_, 1);
lean_dec(v_unused_1790_);
v___x_1780_ = v_x_1768_;
v_isShared_1781_ = v_isSharedCheck_1789_;
goto v_resetjp_1779_;
}
else
{
lean_inc(v_fst_1778_);
lean_dec(v_x_1768_);
v___x_1780_ = lean_box(0);
v_isShared_1781_ = v_isSharedCheck_1789_;
goto v_resetjp_1779_;
}
v_resetjp_1779_:
{
lean_object* v___x_1782_; uint8_t v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1786_; 
lean_inc(v_a_1764_);
v___x_1782_ = lean_array_push(v_fst_1778_, v_a_1764_);
v___x_1783_ = 1;
v___x_1784_ = lean_box(v___x_1783_);
if (v_isShared_1781_ == 0)
{
lean_ctor_set(v___x_1780_, 1, v___x_1784_);
lean_ctor_set(v___x_1780_, 0, v___x_1782_);
v___x_1786_ = v___x_1780_;
goto v_reusejp_1785_;
}
else
{
lean_object* v_reuseFailAlloc_1788_; 
v_reuseFailAlloc_1788_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1788_, 0, v___x_1782_);
lean_ctor_set(v_reuseFailAlloc_1788_, 1, v___x_1784_);
v___x_1786_ = v_reuseFailAlloc_1788_;
goto v_reusejp_1785_;
}
v_reusejp_1785_:
{
v_x_1768_ = v___x_1786_;
v_x_1769_ = v_tail_1777_;
goto _start;
}
}
}
else
{
lean_object* v_tail_1791_; lean_object* v_fst_1792_; lean_object* v_snd_1793_; lean_object* v___x_1795_; uint8_t v_isShared_1796_; uint8_t v_isSharedCheck_1810_; 
v_tail_1791_ = lean_ctor_get(v_x_1769_, 1);
v_fst_1792_ = lean_ctor_get(v_x_1768_, 0);
v_snd_1793_ = lean_ctor_get(v_x_1768_, 1);
v_isSharedCheck_1810_ = !lean_is_exclusive(v_x_1768_);
if (v_isSharedCheck_1810_ == 0)
{
v___x_1795_ = v_x_1768_;
v_isShared_1796_ = v_isSharedCheck_1810_;
goto v_resetjp_1794_;
}
else
{
lean_inc(v_snd_1793_);
lean_inc(v_fst_1792_);
lean_dec(v_x_1768_);
v___x_1795_ = lean_box(0);
v_isShared_1796_ = v_isSharedCheck_1810_;
goto v_resetjp_1794_;
}
v_resetjp_1794_:
{
lean_object* v_idx_1797_; lean_object* v___x_1798_; uint8_t v___x_1799_; 
v_idx_1797_ = lean_ctor_get(v_head_1776_, 0);
v___x_1798_ = lean_array_get_size(v___x_1765_);
v___x_1799_ = lean_nat_dec_le(v___x_1798_, v_idx_1797_);
if (v___x_1799_ == 0)
{
lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1803_; 
v___x_1800_ = lean_array_fget_borrowed(v___x_1765_, v_idx_1797_);
lean_inc(v___x_1800_);
v___x_1801_ = lean_array_push(v_fst_1792_, v___x_1800_);
if (v_isShared_1796_ == 0)
{
lean_ctor_set(v___x_1795_, 0, v___x_1801_);
v___x_1803_ = v___x_1795_;
goto v_reusejp_1802_;
}
else
{
lean_object* v_reuseFailAlloc_1805_; 
v_reuseFailAlloc_1805_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1805_, 0, v___x_1801_);
lean_ctor_set(v_reuseFailAlloc_1805_, 1, v_snd_1793_);
v___x_1803_ = v_reuseFailAlloc_1805_;
goto v_reusejp_1802_;
}
v_reusejp_1802_:
{
v_x_1768_ = v___x_1803_;
v_x_1769_ = v_tail_1791_;
goto _start;
}
}
else
{
lean_object* v___x_1806_; lean_object* v___x_1807_; 
lean_del_object(v___x_1795_);
lean_dec(v_snd_1793_);
lean_dec(v_fst_1792_);
v___x_1806_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9);
lean_inc(v_mvarId_1767_);
lean_inc(v_tacticName_1766_);
v___x_1807_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1766_, v_mvarId_1767_, v___x_1806_, v___y_1770_, v___y_1771_, v___y_1772_, v___y_1773_);
if (lean_obj_tag(v___x_1807_) == 0)
{
lean_object* v_a_1808_; 
v_a_1808_ = lean_ctor_get(v___x_1807_, 0);
lean_inc(v_a_1808_);
lean_dec_ref_known(v___x_1807_, 1);
v_x_1768_ = v_a_1808_;
v_x_1769_ = v_tail_1791_;
goto _start;
}
else
{
lean_dec(v_mvarId_1767_);
lean_dec(v_tacticName_1766_);
lean_dec(v_a_1764_);
return v___x_1807_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Meta_mkRecursorAppPrefix_spec__0___boxed(lean_object* v_a_1811_, lean_object* v___x_1812_, lean_object* v_tacticName_1813_, lean_object* v_mvarId_1814_, lean_object* v_x_1815_, lean_object* v_x_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_){
_start:
{
lean_object* v_res_1822_; 
v_res_1822_ = l_List_foldlM___at___00Lean_Meta_mkRecursorAppPrefix_spec__0(v_a_1811_, v___x_1812_, v_tacticName_1813_, v_mvarId_1814_, v_x_1815_, v_x_1816_, v___y_1817_, v___y_1818_, v___y_1819_, v___y_1820_);
lean_dec(v___y_1820_);
lean_dec_ref(v___y_1819_);
lean_dec(v___y_1818_);
lean_dec_ref(v___y_1817_);
lean_dec(v_x_1816_);
lean_dec_ref(v___x_1812_);
return v_res_1822_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__8(void){
_start:
{
lean_object* v___x_1838_; lean_object* v___x_1839_; 
v___x_1838_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__7));
v___x_1839_ = l_Lean_stringToMessageData(v___x_1838_);
return v___x_1839_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__10(void){
_start:
{
lean_object* v___x_1841_; lean_object* v___x_1842_; 
v___x_1841_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__9));
v___x_1842_ = l_Lean_stringToMessageData(v___x_1841_);
return v___x_1842_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__13(void){
_start:
{
lean_object* v___x_1846_; lean_object* v___x_1847_; 
v___x_1846_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__12));
v___x_1847_ = l_Lean_MessageData_ofFormat(v___x_1846_);
return v___x_1847_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__14(void){
_start:
{
lean_object* v___x_1848_; lean_object* v___x_1849_; 
v___x_1848_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__13, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__13_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__13);
v___x_1849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1849_, 0, v___x_1848_);
return v___x_1849_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2(lean_object* v_recursorInfo_1850_, lean_object* v_a_1851_, lean_object* v_tacticName_1852_, lean_object* v_mvarId_1853_, lean_object* v_indices_1854_, lean_object* v_a_1855_, lean_object* v_major_1856_, lean_object* v_x_1857_, lean_object* v_x_1858_, lean_object* v_x_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_){
_start:
{
if (lean_obj_tag(v_x_1857_) == 5)
{
lean_object* v_fn_1865_; lean_object* v_arg_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; 
v_fn_1865_ = lean_ctor_get(v_x_1857_, 0);
lean_inc_ref(v_fn_1865_);
v_arg_1866_ = lean_ctor_get(v_x_1857_, 1);
lean_inc_ref(v_arg_1866_);
lean_dec_ref_known(v_x_1857_, 2);
v___x_1867_ = lean_array_set(v_x_1858_, v_x_1859_, v_arg_1866_);
v___x_1868_ = lean_unsigned_to_nat(1u);
v___x_1869_ = lean_nat_sub(v_x_1859_, v___x_1868_);
lean_dec(v_x_1859_);
v_x_1857_ = v_fn_1865_;
v_x_1858_ = v___x_1867_;
v_x_1859_ = v___x_1869_;
goto _start;
}
else
{
lean_dec(v_x_1859_);
if (lean_obj_tag(v_x_1857_) == 4)
{
lean_object* v_us_1871_; lean_object* v_recursorName_1872_; lean_object* v_univLevelPos_1873_; uint8_t v_depElim_1874_; lean_object* v_paramsPos_1875_; lean_object* v___x_1876_; uint8_t v___x_1877_; lean_object* v___y_1879_; lean_object* v_motive_1880_; lean_object* v___y_1881_; lean_object* v___y_1882_; lean_object* v___y_1883_; lean_object* v___y_1884_; lean_object* v___x_1897_; lean_object* v___x_1898_; 
v_us_1871_ = lean_ctor_get(v_x_1857_, 1);
lean_inc(v_us_1871_);
lean_dec_ref_known(v_x_1857_, 2);
v_recursorName_1872_ = lean_ctor_get(v_recursorInfo_1850_, 0);
lean_inc(v_recursorName_1872_);
v_univLevelPos_1873_ = lean_ctor_get(v_recursorInfo_1850_, 2);
lean_inc(v_univLevelPos_1873_);
v_depElim_1874_ = lean_ctor_get_uint8(v_recursorInfo_1850_, sizeof(void*)*8);
v_paramsPos_1875_ = lean_ctor_get(v_recursorInfo_1850_, 5);
lean_inc(v_paramsPos_1875_);
lean_dec_ref(v_recursorInfo_1850_);
v___x_1876_ = lean_array_mk(v_us_1871_);
v___x_1877_ = 0;
v___x_1897_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__1));
lean_inc(v_mvarId_1853_);
lean_inc(v_tacticName_1852_);
lean_inc(v_a_1851_);
v___x_1898_ = l_List_foldlM___at___00Lean_Meta_mkRecursorAppPrefix_spec__0(v_a_1851_, v___x_1876_, v_tacticName_1852_, v_mvarId_1853_, v___x_1897_, v_univLevelPos_1873_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_);
lean_dec(v_univLevelPos_1873_);
lean_dec_ref(v___x_1876_);
if (lean_obj_tag(v___x_1898_) == 0)
{
lean_object* v_a_1899_; lean_object* v_fst_1900_; lean_object* v_snd_1901_; lean_object* v___x_1903_; uint8_t v_isShared_1904_; uint8_t v_isSharedCheck_1945_; 
v_a_1899_ = lean_ctor_get(v___x_1898_, 0);
lean_inc(v_a_1899_);
lean_dec_ref_known(v___x_1898_, 1);
v_fst_1900_ = lean_ctor_get(v_a_1899_, 0);
v_snd_1901_ = lean_ctor_get(v_a_1899_, 1);
v_isSharedCheck_1945_ = !lean_is_exclusive(v_a_1899_);
if (v_isSharedCheck_1945_ == 0)
{
v___x_1903_ = v_a_1899_;
v_isShared_1904_ = v_isSharedCheck_1945_;
goto v_resetjp_1902_;
}
else
{
lean_inc(v_snd_1901_);
lean_inc(v_fst_1900_);
lean_dec(v_a_1899_);
v___x_1903_ = lean_box(0);
v_isShared_1904_ = v_isSharedCheck_1945_;
goto v_resetjp_1902_;
}
v_resetjp_1902_:
{
lean_object* v___y_1906_; lean_object* v___y_1907_; lean_object* v___y_1908_; lean_object* v___y_1909_; uint8_t v___x_1925_; 
v___x_1925_ = lean_unbox(v_snd_1901_);
lean_dec(v_snd_1901_);
if (v___x_1925_ == 0)
{
uint8_t v___x_1926_; 
v___x_1926_ = l_Lean_Level_isZero(v_a_1851_);
lean_dec(v_a_1851_);
if (v___x_1926_ == 0)
{
lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1931_; 
lean_dec(v_fst_1900_);
lean_dec(v_paramsPos_1875_);
lean_dec_ref(v_x_1858_);
lean_dec_ref(v_major_1856_);
lean_dec_ref(v_a_1855_);
v___x_1927_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__6));
v___x_1928_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__8, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__8_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__8);
v___x_1929_ = l_Lean_MessageData_ofName(v_recursorName_1872_);
if (v_isShared_1904_ == 0)
{
lean_ctor_set_tag(v___x_1903_, 7);
lean_ctor_set(v___x_1903_, 1, v___x_1929_);
lean_ctor_set(v___x_1903_, 0, v___x_1928_);
v___x_1931_ = v___x_1903_;
goto v_reusejp_1930_;
}
else
{
lean_object* v_reuseFailAlloc_1944_; 
v_reuseFailAlloc_1944_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1944_, 0, v___x_1928_);
lean_ctor_set(v_reuseFailAlloc_1944_, 1, v___x_1929_);
v___x_1931_ = v_reuseFailAlloc_1944_;
goto v_reusejp_1930_;
}
v_reusejp_1930_:
{
lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v_a_1936_; lean_object* v___x_1938_; uint8_t v_isShared_1939_; uint8_t v_isSharedCheck_1943_; 
v___x_1932_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__10, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__10_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__10);
v___x_1933_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1933_, 0, v___x_1931_);
lean_ctor_set(v___x_1933_, 1, v___x_1932_);
v___x_1934_ = l_Lean_Meta_mkTacticExMsg(v_tacticName_1852_, v_mvarId_1853_, v___x_1933_);
v___x_1935_ = l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1___redArg(v___x_1927_, v___x_1934_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_);
v_a_1936_ = lean_ctor_get(v___x_1935_, 0);
v_isSharedCheck_1943_ = !lean_is_exclusive(v___x_1935_);
if (v_isSharedCheck_1943_ == 0)
{
v___x_1938_ = v___x_1935_;
v_isShared_1939_ = v_isSharedCheck_1943_;
goto v_resetjp_1937_;
}
else
{
lean_inc(v_a_1936_);
lean_dec(v___x_1935_);
v___x_1938_ = lean_box(0);
v_isShared_1939_ = v_isSharedCheck_1943_;
goto v_resetjp_1937_;
}
v_resetjp_1937_:
{
lean_object* v___x_1941_; 
if (v_isShared_1939_ == 0)
{
v___x_1941_ = v___x_1938_;
goto v_reusejp_1940_;
}
else
{
lean_object* v_reuseFailAlloc_1942_; 
v_reuseFailAlloc_1942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1942_, 0, v_a_1936_);
v___x_1941_ = v_reuseFailAlloc_1942_;
goto v_reusejp_1940_;
}
v_reusejp_1940_:
{
return v___x_1941_;
}
}
}
}
else
{
lean_del_object(v___x_1903_);
lean_dec(v_tacticName_1852_);
v___y_1906_ = v___y_1860_;
v___y_1907_ = v___y_1861_;
v___y_1908_ = v___y_1862_;
v___y_1909_ = v___y_1863_;
goto v___jp_1905_;
}
}
else
{
lean_del_object(v___x_1903_);
lean_dec(v_tacticName_1852_);
lean_dec(v_a_1851_);
v___y_1906_ = v___y_1860_;
v___y_1907_ = v___y_1861_;
v___y_1908_ = v___y_1862_;
v___y_1909_ = v___y_1863_;
goto v___jp_1905_;
}
v___jp_1905_:
{
lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; 
v___x_1910_ = lean_array_to_list(v_fst_1900_);
v___x_1911_ = l_Lean_mkConst(v_recursorName_1872_, v___x_1910_);
v___x_1912_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams(v_mvarId_1853_, v_x_1858_, v_paramsPos_1875_, v___x_1911_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_);
lean_dec_ref(v_x_1858_);
if (lean_obj_tag(v___x_1912_) == 0)
{
if (v_depElim_1874_ == 0)
{
lean_object* v_a_1913_; 
lean_dec_ref(v_major_1856_);
v_a_1913_ = lean_ctor_get(v___x_1912_, 0);
lean_inc(v_a_1913_);
lean_dec_ref_known(v___x_1912_, 1);
v___y_1879_ = v_a_1913_;
v_motive_1880_ = v_a_1855_;
v___y_1881_ = v___y_1906_;
v___y_1882_ = v___y_1907_;
v___y_1883_ = v___y_1908_;
v___y_1884_ = v___y_1909_;
goto v___jp_1878_;
}
else
{
lean_object* v_a_1914_; lean_object* v___x_1915_; 
v_a_1914_ = lean_ctor_get(v___x_1912_, 0);
lean_inc(v_a_1914_);
lean_dec_ref_known(v___x_1912_, 1);
lean_inc(v___y_1909_);
lean_inc_ref(v___y_1908_);
lean_inc(v___y_1907_);
lean_inc_ref(v___y_1906_);
lean_inc_ref(v_major_1856_);
v___x_1915_ = lean_infer_type(v_major_1856_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_);
if (lean_obj_tag(v___x_1915_) == 0)
{
lean_object* v_a_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; 
v_a_1916_ = lean_ctor_get(v___x_1915_, 0);
lean_inc(v_a_1916_);
lean_dec_ref_known(v___x_1915_, 1);
v___x_1917_ = lean_unsigned_to_nat(1u);
v___x_1918_ = lean_mk_empty_array_with_capacity(v___x_1917_);
v___x_1919_ = lean_array_push(v___x_1918_, v_major_1856_);
v___x_1920_ = l_Lean_Expr_abstractM(v_a_1855_, v___x_1919_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_);
lean_dec_ref(v___x_1919_);
if (lean_obj_tag(v___x_1920_) == 0)
{
lean_object* v_a_1921_; lean_object* v___x_1922_; uint8_t v___x_1923_; lean_object* v___x_1924_; 
v_a_1921_ = lean_ctor_get(v___x_1920_, 0);
lean_inc(v_a_1921_);
lean_dec_ref_known(v___x_1920_, 1);
v___x_1922_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__3));
v___x_1923_ = 0;
v___x_1924_ = l_Lean_mkLambda(v___x_1922_, v___x_1923_, v_a_1916_, v_a_1921_);
v___y_1879_ = v_a_1914_;
v_motive_1880_ = v___x_1924_;
v___y_1881_ = v___y_1906_;
v___y_1882_ = v___y_1907_;
v___y_1883_ = v___y_1908_;
v___y_1884_ = v___y_1909_;
goto v___jp_1878_;
}
else
{
lean_dec(v_a_1916_);
lean_dec(v_a_1914_);
return v___x_1920_;
}
}
else
{
lean_dec(v_a_1914_);
lean_dec_ref(v_major_1856_);
lean_dec_ref(v_a_1855_);
return v___x_1915_;
}
}
}
else
{
lean_dec_ref(v_major_1856_);
lean_dec_ref(v_a_1855_);
return v___x_1912_;
}
}
}
}
else
{
lean_object* v_a_1946_; lean_object* v___x_1948_; uint8_t v_isShared_1949_; uint8_t v_isSharedCheck_1953_; 
lean_dec(v_paramsPos_1875_);
lean_dec(v_recursorName_1872_);
lean_dec_ref(v_x_1858_);
lean_dec_ref(v_major_1856_);
lean_dec_ref(v_a_1855_);
lean_dec(v_mvarId_1853_);
lean_dec(v_tacticName_1852_);
lean_dec(v_a_1851_);
v_a_1946_ = lean_ctor_get(v___x_1898_, 0);
v_isSharedCheck_1953_ = !lean_is_exclusive(v___x_1898_);
if (v_isSharedCheck_1953_ == 0)
{
v___x_1948_ = v___x_1898_;
v_isShared_1949_ = v_isSharedCheck_1953_;
goto v_resetjp_1947_;
}
else
{
lean_inc(v_a_1946_);
lean_dec(v___x_1898_);
v___x_1948_ = lean_box(0);
v_isShared_1949_ = v_isSharedCheck_1953_;
goto v_resetjp_1947_;
}
v_resetjp_1947_:
{
lean_object* v___x_1951_; 
if (v_isShared_1949_ == 0)
{
v___x_1951_ = v___x_1948_;
goto v_reusejp_1950_;
}
else
{
lean_object* v_reuseFailAlloc_1952_; 
v_reuseFailAlloc_1952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1952_, 0, v_a_1946_);
v___x_1951_ = v_reuseFailAlloc_1952_;
goto v_reusejp_1950_;
}
v_reusejp_1950_:
{
return v___x_1951_;
}
}
}
v___jp_1878_:
{
uint8_t v___x_1885_; uint8_t v___x_1886_; lean_object* v___x_1887_; 
v___x_1885_ = 1;
v___x_1886_ = 1;
v___x_1887_ = l_Lean_Meta_mkLambdaFVars(v_indices_1854_, v_motive_1880_, v___x_1877_, v___x_1885_, v___x_1877_, v___x_1885_, v___x_1886_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_);
if (lean_obj_tag(v___x_1887_) == 0)
{
lean_object* v_a_1888_; lean_object* v___x_1890_; uint8_t v_isShared_1891_; uint8_t v_isSharedCheck_1896_; 
v_a_1888_ = lean_ctor_get(v___x_1887_, 0);
v_isSharedCheck_1896_ = !lean_is_exclusive(v___x_1887_);
if (v_isSharedCheck_1896_ == 0)
{
v___x_1890_ = v___x_1887_;
v_isShared_1891_ = v_isSharedCheck_1896_;
goto v_resetjp_1889_;
}
else
{
lean_inc(v_a_1888_);
lean_dec(v___x_1887_);
v___x_1890_ = lean_box(0);
v_isShared_1891_ = v_isSharedCheck_1896_;
goto v_resetjp_1889_;
}
v_resetjp_1889_:
{
lean_object* v___x_1892_; lean_object* v___x_1894_; 
v___x_1892_ = l_Lean_Expr_app___override(v___y_1879_, v_a_1888_);
if (v_isShared_1891_ == 0)
{
lean_ctor_set(v___x_1890_, 0, v___x_1892_);
v___x_1894_ = v___x_1890_;
goto v_reusejp_1893_;
}
else
{
lean_object* v_reuseFailAlloc_1895_; 
v_reuseFailAlloc_1895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1895_, 0, v___x_1892_);
v___x_1894_ = v_reuseFailAlloc_1895_;
goto v_reusejp_1893_;
}
v_reusejp_1893_:
{
return v___x_1894_;
}
}
}
else
{
lean_dec_ref(v___y_1879_);
return v___x_1887_;
}
}
}
else
{
lean_object* v___x_1954_; lean_object* v___x_1955_; 
lean_dec_ref(v_x_1858_);
lean_dec_ref(v_x_1857_);
lean_dec_ref(v_major_1856_);
lean_dec_ref(v_a_1855_);
lean_dec(v_a_1851_);
lean_dec_ref(v_recursorInfo_1850_);
v___x_1954_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__14, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__14_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__14);
v___x_1955_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1852_, v_mvarId_1853_, v___x_1954_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_);
return v___x_1955_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___boxed(lean_object* v_recursorInfo_1956_, lean_object* v_a_1957_, lean_object* v_tacticName_1958_, lean_object* v_mvarId_1959_, lean_object* v_indices_1960_, lean_object* v_a_1961_, lean_object* v_major_1962_, lean_object* v_x_1963_, lean_object* v_x_1964_, lean_object* v_x_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_){
_start:
{
lean_object* v_res_1971_; 
v_res_1971_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2(v_recursorInfo_1956_, v_a_1957_, v_tacticName_1958_, v_mvarId_1959_, v_indices_1960_, v_a_1961_, v_major_1962_, v_x_1963_, v_x_1964_, v_x_1965_, v___y_1966_, v___y_1967_, v___y_1968_, v___y_1969_);
lean_dec(v___y_1969_);
lean_dec_ref(v___y_1968_);
lean_dec(v___y_1967_);
lean_dec_ref(v___y_1966_);
lean_dec_ref(v_indices_1960_);
return v_res_1971_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2(lean_object* v_a_1972_, lean_object* v_tacticName_1973_, lean_object* v_mvarId_1974_, lean_object* v_recursorInfo_1975_, lean_object* v_indices_1976_, lean_object* v_a_1977_, lean_object* v_major_1978_, lean_object* v_x_1979_, lean_object* v_x_1980_, lean_object* v_x_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_){
_start:
{
if (lean_obj_tag(v_x_1979_) == 5)
{
lean_object* v_fn_1987_; lean_object* v_arg_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; 
v_fn_1987_ = lean_ctor_get(v_x_1979_, 0);
lean_inc_ref(v_fn_1987_);
v_arg_1988_ = lean_ctor_get(v_x_1979_, 1);
lean_inc_ref(v_arg_1988_);
lean_dec_ref_known(v_x_1979_, 2);
v___x_1989_ = lean_array_set(v_x_1980_, v_x_1981_, v_arg_1988_);
v___x_1990_ = lean_unsigned_to_nat(1u);
v___x_1991_ = lean_nat_sub(v_x_1981_, v___x_1990_);
v___x_1992_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2(v_recursorInfo_1975_, v_a_1972_, v_tacticName_1973_, v_mvarId_1974_, v_indices_1976_, v_a_1977_, v_major_1978_, v_fn_1987_, v___x_1989_, v___x_1991_, v___y_1982_, v___y_1983_, v___y_1984_, v___y_1985_);
return v___x_1992_;
}
else
{
if (lean_obj_tag(v_x_1979_) == 4)
{
lean_object* v_us_1993_; lean_object* v_recursorName_1994_; lean_object* v_univLevelPos_1995_; uint8_t v_depElim_1996_; lean_object* v_paramsPos_1997_; lean_object* v___x_1998_; uint8_t v___x_1999_; lean_object* v___y_2001_; lean_object* v_motive_2002_; lean_object* v___y_2003_; lean_object* v___y_2004_; lean_object* v___y_2005_; lean_object* v___y_2006_; lean_object* v___x_2019_; lean_object* v___x_2020_; 
v_us_1993_ = lean_ctor_get(v_x_1979_, 1);
lean_inc(v_us_1993_);
lean_dec_ref_known(v_x_1979_, 2);
v_recursorName_1994_ = lean_ctor_get(v_recursorInfo_1975_, 0);
lean_inc(v_recursorName_1994_);
v_univLevelPos_1995_ = lean_ctor_get(v_recursorInfo_1975_, 2);
lean_inc(v_univLevelPos_1995_);
v_depElim_1996_ = lean_ctor_get_uint8(v_recursorInfo_1975_, sizeof(void*)*8);
v_paramsPos_1997_ = lean_ctor_get(v_recursorInfo_1975_, 5);
lean_inc(v_paramsPos_1997_);
lean_dec_ref(v_recursorInfo_1975_);
v___x_1998_ = lean_array_mk(v_us_1993_);
v___x_1999_ = 0;
v___x_2019_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__1));
lean_inc(v_mvarId_1974_);
lean_inc(v_tacticName_1973_);
lean_inc(v_a_1972_);
v___x_2020_ = l_List_foldlM___at___00Lean_Meta_mkRecursorAppPrefix_spec__0(v_a_1972_, v___x_1998_, v_tacticName_1973_, v_mvarId_1974_, v___x_2019_, v_univLevelPos_1995_, v___y_1982_, v___y_1983_, v___y_1984_, v___y_1985_);
lean_dec(v_univLevelPos_1995_);
lean_dec_ref(v___x_1998_);
if (lean_obj_tag(v___x_2020_) == 0)
{
lean_object* v_a_2021_; lean_object* v_fst_2022_; lean_object* v_snd_2023_; lean_object* v___x_2025_; uint8_t v_isShared_2026_; uint8_t v_isSharedCheck_2067_; 
v_a_2021_ = lean_ctor_get(v___x_2020_, 0);
lean_inc(v_a_2021_);
lean_dec_ref_known(v___x_2020_, 1);
v_fst_2022_ = lean_ctor_get(v_a_2021_, 0);
v_snd_2023_ = lean_ctor_get(v_a_2021_, 1);
v_isSharedCheck_2067_ = !lean_is_exclusive(v_a_2021_);
if (v_isSharedCheck_2067_ == 0)
{
v___x_2025_ = v_a_2021_;
v_isShared_2026_ = v_isSharedCheck_2067_;
goto v_resetjp_2024_;
}
else
{
lean_inc(v_snd_2023_);
lean_inc(v_fst_2022_);
lean_dec(v_a_2021_);
v___x_2025_ = lean_box(0);
v_isShared_2026_ = v_isSharedCheck_2067_;
goto v_resetjp_2024_;
}
v_resetjp_2024_:
{
lean_object* v___y_2028_; lean_object* v___y_2029_; lean_object* v___y_2030_; lean_object* v___y_2031_; uint8_t v___x_2047_; 
v___x_2047_ = lean_unbox(v_snd_2023_);
lean_dec(v_snd_2023_);
if (v___x_2047_ == 0)
{
uint8_t v___x_2048_; 
v___x_2048_ = l_Lean_Level_isZero(v_a_1972_);
lean_dec(v_a_1972_);
if (v___x_2048_ == 0)
{
lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2053_; 
lean_dec(v_fst_2022_);
lean_dec(v_paramsPos_1997_);
lean_dec_ref(v_x_1980_);
lean_dec_ref(v_major_1978_);
lean_dec_ref(v_a_1977_);
v___x_2049_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__6));
v___x_2050_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__8, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__8_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__8);
v___x_2051_ = l_Lean_MessageData_ofName(v_recursorName_1994_);
if (v_isShared_2026_ == 0)
{
lean_ctor_set_tag(v___x_2025_, 7);
lean_ctor_set(v___x_2025_, 1, v___x_2051_);
lean_ctor_set(v___x_2025_, 0, v___x_2050_);
v___x_2053_ = v___x_2025_;
goto v_reusejp_2052_;
}
else
{
lean_object* v_reuseFailAlloc_2066_; 
v_reuseFailAlloc_2066_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2066_, 0, v___x_2050_);
lean_ctor_set(v_reuseFailAlloc_2066_, 1, v___x_2051_);
v___x_2053_ = v_reuseFailAlloc_2066_;
goto v_reusejp_2052_;
}
v_reusejp_2052_:
{
lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v_a_2058_; lean_object* v___x_2060_; uint8_t v_isShared_2061_; uint8_t v_isSharedCheck_2065_; 
v___x_2054_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__10, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__10_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__10);
v___x_2055_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2055_, 0, v___x_2053_);
lean_ctor_set(v___x_2055_, 1, v___x_2054_);
v___x_2056_ = l_Lean_Meta_mkTacticExMsg(v_tacticName_1973_, v_mvarId_1974_, v___x_2055_);
v___x_2057_ = l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1___redArg(v___x_2049_, v___x_2056_, v___y_1982_, v___y_1983_, v___y_1984_, v___y_1985_);
v_a_2058_ = lean_ctor_get(v___x_2057_, 0);
v_isSharedCheck_2065_ = !lean_is_exclusive(v___x_2057_);
if (v_isSharedCheck_2065_ == 0)
{
v___x_2060_ = v___x_2057_;
v_isShared_2061_ = v_isSharedCheck_2065_;
goto v_resetjp_2059_;
}
else
{
lean_inc(v_a_2058_);
lean_dec(v___x_2057_);
v___x_2060_ = lean_box(0);
v_isShared_2061_ = v_isSharedCheck_2065_;
goto v_resetjp_2059_;
}
v_resetjp_2059_:
{
lean_object* v___x_2063_; 
if (v_isShared_2061_ == 0)
{
v___x_2063_ = v___x_2060_;
goto v_reusejp_2062_;
}
else
{
lean_object* v_reuseFailAlloc_2064_; 
v_reuseFailAlloc_2064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2064_, 0, v_a_2058_);
v___x_2063_ = v_reuseFailAlloc_2064_;
goto v_reusejp_2062_;
}
v_reusejp_2062_:
{
return v___x_2063_;
}
}
}
}
else
{
lean_del_object(v___x_2025_);
lean_dec(v_tacticName_1973_);
v___y_2028_ = v___y_1982_;
v___y_2029_ = v___y_1983_;
v___y_2030_ = v___y_1984_;
v___y_2031_ = v___y_1985_;
goto v___jp_2027_;
}
}
else
{
lean_del_object(v___x_2025_);
lean_dec(v_tacticName_1973_);
lean_dec(v_a_1972_);
v___y_2028_ = v___y_1982_;
v___y_2029_ = v___y_1983_;
v___y_2030_ = v___y_1984_;
v___y_2031_ = v___y_1985_;
goto v___jp_2027_;
}
v___jp_2027_:
{
lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; 
v___x_2032_ = lean_array_to_list(v_fst_2022_);
v___x_2033_ = l_Lean_mkConst(v_recursorName_1994_, v___x_2032_);
v___x_2034_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams(v_mvarId_1974_, v_x_1980_, v_paramsPos_1997_, v___x_2033_, v___y_2028_, v___y_2029_, v___y_2030_, v___y_2031_);
lean_dec_ref(v_x_1980_);
if (lean_obj_tag(v___x_2034_) == 0)
{
if (v_depElim_1996_ == 0)
{
lean_object* v_a_2035_; 
lean_dec_ref(v_major_1978_);
v_a_2035_ = lean_ctor_get(v___x_2034_, 0);
lean_inc(v_a_2035_);
lean_dec_ref_known(v___x_2034_, 1);
v___y_2001_ = v_a_2035_;
v_motive_2002_ = v_a_1977_;
v___y_2003_ = v___y_2028_;
v___y_2004_ = v___y_2029_;
v___y_2005_ = v___y_2030_;
v___y_2006_ = v___y_2031_;
goto v___jp_2000_;
}
else
{
lean_object* v_a_2036_; lean_object* v___x_2037_; 
v_a_2036_ = lean_ctor_get(v___x_2034_, 0);
lean_inc(v_a_2036_);
lean_dec_ref_known(v___x_2034_, 1);
lean_inc(v___y_2031_);
lean_inc_ref(v___y_2030_);
lean_inc(v___y_2029_);
lean_inc_ref(v___y_2028_);
lean_inc_ref(v_major_1978_);
v___x_2037_ = lean_infer_type(v_major_1978_, v___y_2028_, v___y_2029_, v___y_2030_, v___y_2031_);
if (lean_obj_tag(v___x_2037_) == 0)
{
lean_object* v_a_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; 
v_a_2038_ = lean_ctor_get(v___x_2037_, 0);
lean_inc(v_a_2038_);
lean_dec_ref_known(v___x_2037_, 1);
v___x_2039_ = lean_unsigned_to_nat(1u);
v___x_2040_ = lean_mk_empty_array_with_capacity(v___x_2039_);
v___x_2041_ = lean_array_push(v___x_2040_, v_major_1978_);
v___x_2042_ = l_Lean_Expr_abstractM(v_a_1977_, v___x_2041_, v___y_2028_, v___y_2029_, v___y_2030_, v___y_2031_);
lean_dec_ref(v___x_2041_);
if (lean_obj_tag(v___x_2042_) == 0)
{
lean_object* v_a_2043_; lean_object* v___x_2044_; uint8_t v___x_2045_; lean_object* v___x_2046_; 
v_a_2043_ = lean_ctor_get(v___x_2042_, 0);
lean_inc(v_a_2043_);
lean_dec_ref_known(v___x_2042_, 1);
v___x_2044_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__3));
v___x_2045_ = 0;
v___x_2046_ = l_Lean_mkLambda(v___x_2044_, v___x_2045_, v_a_2038_, v_a_2043_);
v___y_2001_ = v_a_2036_;
v_motive_2002_ = v___x_2046_;
v___y_2003_ = v___y_2028_;
v___y_2004_ = v___y_2029_;
v___y_2005_ = v___y_2030_;
v___y_2006_ = v___y_2031_;
goto v___jp_2000_;
}
else
{
lean_dec(v_a_2038_);
lean_dec(v_a_2036_);
return v___x_2042_;
}
}
else
{
lean_dec(v_a_2036_);
lean_dec_ref(v_major_1978_);
lean_dec_ref(v_a_1977_);
return v___x_2037_;
}
}
}
else
{
lean_dec_ref(v_major_1978_);
lean_dec_ref(v_a_1977_);
return v___x_2034_;
}
}
}
}
else
{
lean_object* v_a_2068_; lean_object* v___x_2070_; uint8_t v_isShared_2071_; uint8_t v_isSharedCheck_2075_; 
lean_dec(v_paramsPos_1997_);
lean_dec(v_recursorName_1994_);
lean_dec_ref(v_x_1980_);
lean_dec_ref(v_major_1978_);
lean_dec_ref(v_a_1977_);
lean_dec(v_mvarId_1974_);
lean_dec(v_tacticName_1973_);
lean_dec(v_a_1972_);
v_a_2068_ = lean_ctor_get(v___x_2020_, 0);
v_isSharedCheck_2075_ = !lean_is_exclusive(v___x_2020_);
if (v_isSharedCheck_2075_ == 0)
{
v___x_2070_ = v___x_2020_;
v_isShared_2071_ = v_isSharedCheck_2075_;
goto v_resetjp_2069_;
}
else
{
lean_inc(v_a_2068_);
lean_dec(v___x_2020_);
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
v___jp_2000_:
{
uint8_t v___x_2007_; uint8_t v___x_2008_; lean_object* v___x_2009_; 
v___x_2007_ = 1;
v___x_2008_ = 1;
v___x_2009_ = l_Lean_Meta_mkLambdaFVars(v_indices_1976_, v_motive_2002_, v___x_1999_, v___x_2007_, v___x_1999_, v___x_2007_, v___x_2008_, v___y_2003_, v___y_2004_, v___y_2005_, v___y_2006_);
if (lean_obj_tag(v___x_2009_) == 0)
{
lean_object* v_a_2010_; lean_object* v___x_2012_; uint8_t v_isShared_2013_; uint8_t v_isSharedCheck_2018_; 
v_a_2010_ = lean_ctor_get(v___x_2009_, 0);
v_isSharedCheck_2018_ = !lean_is_exclusive(v___x_2009_);
if (v_isSharedCheck_2018_ == 0)
{
v___x_2012_ = v___x_2009_;
v_isShared_2013_ = v_isSharedCheck_2018_;
goto v_resetjp_2011_;
}
else
{
lean_inc(v_a_2010_);
lean_dec(v___x_2009_);
v___x_2012_ = lean_box(0);
v_isShared_2013_ = v_isSharedCheck_2018_;
goto v_resetjp_2011_;
}
v_resetjp_2011_:
{
lean_object* v___x_2014_; lean_object* v___x_2016_; 
v___x_2014_ = l_Lean_Expr_app___override(v___y_2001_, v_a_2010_);
if (v_isShared_2013_ == 0)
{
lean_ctor_set(v___x_2012_, 0, v___x_2014_);
v___x_2016_ = v___x_2012_;
goto v_reusejp_2015_;
}
else
{
lean_object* v_reuseFailAlloc_2017_; 
v_reuseFailAlloc_2017_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2017_, 0, v___x_2014_);
v___x_2016_ = v_reuseFailAlloc_2017_;
goto v_reusejp_2015_;
}
v_reusejp_2015_:
{
return v___x_2016_;
}
}
}
else
{
lean_dec_ref(v___y_2001_);
return v___x_2009_;
}
}
}
else
{
lean_object* v___x_2076_; lean_object* v___x_2077_; 
lean_dec_ref(v_x_1980_);
lean_dec_ref(v_x_1979_);
lean_dec_ref(v_major_1978_);
lean_dec_ref(v_a_1977_);
lean_dec_ref(v_recursorInfo_1975_);
lean_dec(v_a_1972_);
v___x_2076_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__14, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__14_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__14);
v___x_2077_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_1973_, v_mvarId_1974_, v___x_2076_, v___y_1982_, v___y_1983_, v___y_1984_, v___y_1985_);
return v___x_2077_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2___boxed(lean_object* v_a_2078_, lean_object* v_tacticName_2079_, lean_object* v_mvarId_2080_, lean_object* v_recursorInfo_2081_, lean_object* v_indices_2082_, lean_object* v_a_2083_, lean_object* v_major_2084_, lean_object* v_x_2085_, lean_object* v_x_2086_, lean_object* v_x_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_){
_start:
{
lean_object* v_res_2093_; 
v_res_2093_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2(v_a_2078_, v_tacticName_2079_, v_mvarId_2080_, v_recursorInfo_2081_, v_indices_2082_, v_a_2083_, v_major_2084_, v_x_2085_, v_x_2086_, v_x_2087_, v___y_2088_, v___y_2089_, v___y_2090_, v___y_2091_);
lean_dec(v___y_2091_);
lean_dec_ref(v___y_2090_);
lean_dec(v___y_2089_);
lean_dec_ref(v___y_2088_);
lean_dec(v_x_2087_);
lean_dec_ref(v_indices_2082_);
return v_res_2093_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkRecursorAppPrefix(lean_object* v_mvarId_2094_, lean_object* v_tacticName_2095_, lean_object* v_majorFVarId_2096_, lean_object* v_recursorInfo_2097_, lean_object* v_indices_2098_, lean_object* v_a_2099_, lean_object* v_a_2100_, lean_object* v_a_2101_, lean_object* v_a_2102_){
_start:
{
lean_object* v___x_2104_; 
lean_inc(v_mvarId_2094_);
v___x_2104_ = l_Lean_MVarId_getType(v_mvarId_2094_, v_a_2099_, v_a_2100_, v_a_2101_, v_a_2102_);
if (lean_obj_tag(v___x_2104_) == 0)
{
lean_object* v_a_2105_; lean_object* v___x_2106_; 
v_a_2105_ = lean_ctor_get(v___x_2104_, 0);
lean_inc_n(v_a_2105_, 2);
lean_dec_ref_known(v___x_2104_, 1);
v___x_2106_ = l_Lean_Meta_getLevel(v_a_2105_, v_a_2099_, v_a_2100_, v_a_2101_, v_a_2102_);
if (lean_obj_tag(v___x_2106_) == 0)
{
lean_object* v_a_2107_; lean_object* v___x_2108_; 
v_a_2107_ = lean_ctor_get(v___x_2106_, 0);
lean_inc(v_a_2107_);
lean_dec_ref_known(v___x_2106_, 1);
v___x_2108_ = l_Lean_Meta_normalizeLevel(v_a_2107_, v_a_2099_, v_a_2100_, v_a_2101_, v_a_2102_);
if (lean_obj_tag(v___x_2108_) == 0)
{
lean_object* v_a_2109_; lean_object* v_major_2110_; lean_object* v___x_2111_; 
v_a_2109_ = lean_ctor_get(v___x_2108_, 0);
lean_inc(v_a_2109_);
lean_dec_ref_known(v___x_2108_, 1);
lean_inc(v_majorFVarId_2096_);
v_major_2110_ = l_Lean_mkFVar(v_majorFVarId_2096_);
v___x_2111_ = l_Lean_FVarId_getDecl___redArg(v_majorFVarId_2096_, v_a_2099_, v_a_2101_, v_a_2102_);
if (lean_obj_tag(v___x_2111_) == 0)
{
lean_object* v_a_2112_; lean_object* v_typeName_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; 
v_a_2112_ = lean_ctor_get(v___x_2111_, 0);
lean_inc(v_a_2112_);
lean_dec_ref_known(v___x_2111_, 1);
v_typeName_2113_ = lean_ctor_get(v_recursorInfo_2097_, 1);
v___x_2114_ = l_Lean_LocalDecl_type(v_a_2112_);
lean_dec(v_a_2112_);
lean_inc_ref(v___x_2114_);
v___x_2115_ = l_Lean_Meta_whnfUntil(v___x_2114_, v_typeName_2113_, v_a_2099_, v_a_2100_, v_a_2101_, v_a_2102_);
if (lean_obj_tag(v___x_2115_) == 0)
{
lean_object* v_a_2116_; 
v_a_2116_ = lean_ctor_get(v___x_2115_, 0);
lean_inc(v_a_2116_);
lean_dec_ref_known(v___x_2115_, 1);
if (lean_obj_tag(v_a_2116_) == 1)
{
lean_object* v_val_2117_; lean_object* v_dummy_2118_; lean_object* v_nargs_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; 
lean_dec_ref(v___x_2114_);
v_val_2117_ = lean_ctor_get(v_a_2116_, 0);
lean_inc(v_val_2117_);
lean_dec_ref_known(v_a_2116_, 1);
v_dummy_2118_ = lean_obj_once(&l_Lean_Meta_getMajorTypeIndices___closed__0, &l_Lean_Meta_getMajorTypeIndices___closed__0_once, _init_l_Lean_Meta_getMajorTypeIndices___closed__0);
v_nargs_2119_ = l_Lean_Expr_getAppNumArgs(v_val_2117_);
lean_inc(v_nargs_2119_);
v___x_2120_ = lean_mk_array(v_nargs_2119_, v_dummy_2118_);
v___x_2121_ = lean_unsigned_to_nat(1u);
v___x_2122_ = lean_nat_sub(v_nargs_2119_, v___x_2121_);
lean_dec(v_nargs_2119_);
v___x_2123_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2(v_a_2109_, v_tacticName_2095_, v_mvarId_2094_, v_recursorInfo_2097_, v_indices_2098_, v_a_2105_, v_major_2110_, v_val_2117_, v___x_2120_, v___x_2122_, v_a_2099_, v_a_2100_, v_a_2101_, v_a_2102_);
lean_dec(v___x_2122_);
return v___x_2123_;
}
else
{
lean_object* v___x_2124_; 
lean_dec(v_a_2116_);
lean_dec_ref(v_major_2110_);
lean_dec(v_a_2109_);
lean_dec(v_a_2105_);
lean_dec_ref(v_recursorInfo_2097_);
v___x_2124_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg(v_tacticName_2095_, v_mvarId_2094_, v___x_2114_, v_a_2099_, v_a_2100_, v_a_2101_, v_a_2102_);
return v___x_2124_;
}
}
else
{
lean_object* v_a_2125_; lean_object* v___x_2127_; uint8_t v_isShared_2128_; uint8_t v_isSharedCheck_2132_; 
lean_dec_ref(v___x_2114_);
lean_dec_ref(v_major_2110_);
lean_dec(v_a_2109_);
lean_dec(v_a_2105_);
lean_dec_ref(v_recursorInfo_2097_);
lean_dec(v_tacticName_2095_);
lean_dec(v_mvarId_2094_);
v_a_2125_ = lean_ctor_get(v___x_2115_, 0);
v_isSharedCheck_2132_ = !lean_is_exclusive(v___x_2115_);
if (v_isSharedCheck_2132_ == 0)
{
v___x_2127_ = v___x_2115_;
v_isShared_2128_ = v_isSharedCheck_2132_;
goto v_resetjp_2126_;
}
else
{
lean_inc(v_a_2125_);
lean_dec(v___x_2115_);
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
lean_dec_ref(v_major_2110_);
lean_dec(v_a_2109_);
lean_dec(v_a_2105_);
lean_dec_ref(v_recursorInfo_2097_);
lean_dec(v_tacticName_2095_);
lean_dec(v_mvarId_2094_);
v_a_2133_ = lean_ctor_get(v___x_2111_, 0);
v_isSharedCheck_2140_ = !lean_is_exclusive(v___x_2111_);
if (v_isSharedCheck_2140_ == 0)
{
v___x_2135_ = v___x_2111_;
v_isShared_2136_ = v_isSharedCheck_2140_;
goto v_resetjp_2134_;
}
else
{
lean_inc(v_a_2133_);
lean_dec(v___x_2111_);
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
lean_object* v_a_2141_; lean_object* v___x_2143_; uint8_t v_isShared_2144_; uint8_t v_isSharedCheck_2148_; 
lean_dec(v_a_2105_);
lean_dec_ref(v_recursorInfo_2097_);
lean_dec(v_majorFVarId_2096_);
lean_dec(v_tacticName_2095_);
lean_dec(v_mvarId_2094_);
v_a_2141_ = lean_ctor_get(v___x_2108_, 0);
v_isSharedCheck_2148_ = !lean_is_exclusive(v___x_2108_);
if (v_isSharedCheck_2148_ == 0)
{
v___x_2143_ = v___x_2108_;
v_isShared_2144_ = v_isSharedCheck_2148_;
goto v_resetjp_2142_;
}
else
{
lean_inc(v_a_2141_);
lean_dec(v___x_2108_);
v___x_2143_ = lean_box(0);
v_isShared_2144_ = v_isSharedCheck_2148_;
goto v_resetjp_2142_;
}
v_resetjp_2142_:
{
lean_object* v___x_2146_; 
if (v_isShared_2144_ == 0)
{
v___x_2146_ = v___x_2143_;
goto v_reusejp_2145_;
}
else
{
lean_object* v_reuseFailAlloc_2147_; 
v_reuseFailAlloc_2147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2147_, 0, v_a_2141_);
v___x_2146_ = v_reuseFailAlloc_2147_;
goto v_reusejp_2145_;
}
v_reusejp_2145_:
{
return v___x_2146_;
}
}
}
}
else
{
lean_object* v_a_2149_; lean_object* v___x_2151_; uint8_t v_isShared_2152_; uint8_t v_isSharedCheck_2156_; 
lean_dec(v_a_2105_);
lean_dec_ref(v_recursorInfo_2097_);
lean_dec(v_majorFVarId_2096_);
lean_dec(v_tacticName_2095_);
lean_dec(v_mvarId_2094_);
v_a_2149_ = lean_ctor_get(v___x_2106_, 0);
v_isSharedCheck_2156_ = !lean_is_exclusive(v___x_2106_);
if (v_isSharedCheck_2156_ == 0)
{
v___x_2151_ = v___x_2106_;
v_isShared_2152_ = v_isSharedCheck_2156_;
goto v_resetjp_2150_;
}
else
{
lean_inc(v_a_2149_);
lean_dec(v___x_2106_);
v___x_2151_ = lean_box(0);
v_isShared_2152_ = v_isSharedCheck_2156_;
goto v_resetjp_2150_;
}
v_resetjp_2150_:
{
lean_object* v___x_2154_; 
if (v_isShared_2152_ == 0)
{
v___x_2154_ = v___x_2151_;
goto v_reusejp_2153_;
}
else
{
lean_object* v_reuseFailAlloc_2155_; 
v_reuseFailAlloc_2155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2155_, 0, v_a_2149_);
v___x_2154_ = v_reuseFailAlloc_2155_;
goto v_reusejp_2153_;
}
v_reusejp_2153_:
{
return v___x_2154_;
}
}
}
}
else
{
lean_dec_ref(v_recursorInfo_2097_);
lean_dec(v_majorFVarId_2096_);
lean_dec(v_tacticName_2095_);
lean_dec(v_mvarId_2094_);
return v___x_2104_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkRecursorAppPrefix___boxed(lean_object* v_mvarId_2157_, lean_object* v_tacticName_2158_, lean_object* v_majorFVarId_2159_, lean_object* v_recursorInfo_2160_, lean_object* v_indices_2161_, lean_object* v_a_2162_, lean_object* v_a_2163_, lean_object* v_a_2164_, lean_object* v_a_2165_, lean_object* v_a_2166_){
_start:
{
lean_object* v_res_2167_; 
v_res_2167_ = l_Lean_Meta_mkRecursorAppPrefix(v_mvarId_2157_, v_tacticName_2158_, v_majorFVarId_2159_, v_recursorInfo_2160_, v_indices_2161_, v_a_2162_, v_a_2163_, v_a_2164_, v_a_2165_);
lean_dec(v_a_2165_);
lean_dec_ref(v_a_2164_);
lean_dec(v_a_2163_);
lean_dec_ref(v_a_2162_);
lean_dec_ref(v_indices_2161_);
return v_res_2167_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1(lean_object* v_00_u03b1_2168_, lean_object* v_name_2169_, lean_object* v_msg_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_){
_start:
{
lean_object* v___x_2176_; 
v___x_2176_ = l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1___redArg(v_name_2169_, v_msg_2170_, v___y_2171_, v___y_2172_, v___y_2173_, v___y_2174_);
return v___x_2176_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1___boxed(lean_object* v_00_u03b1_2177_, lean_object* v_name_2178_, lean_object* v_msg_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_){
_start:
{
lean_object* v_res_2185_; 
v_res_2185_ = l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1(v_00_u03b1_2177_, v_name_2178_, v_msg_2179_, v___y_2180_, v___y_2181_, v___y_2182_, v___y_2183_);
lean_dec(v___y_2183_);
lean_dec_ref(v___y_2182_);
lean_dec(v___y_2181_);
lean_dec_ref(v___y_2180_);
return v_res_2185_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___redArg(lean_object* v_mvarId_2186_, lean_object* v_x_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_){
_start:
{
lean_object* v___x_2193_; 
v___x_2193_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_2186_, v_x_2187_, v___y_2188_, v___y_2189_, v___y_2190_, v___y_2191_);
if (lean_obj_tag(v___x_2193_) == 0)
{
lean_object* v_a_2194_; lean_object* v___x_2196_; uint8_t v_isShared_2197_; uint8_t v_isSharedCheck_2201_; 
v_a_2194_ = lean_ctor_get(v___x_2193_, 0);
v_isSharedCheck_2201_ = !lean_is_exclusive(v___x_2193_);
if (v_isSharedCheck_2201_ == 0)
{
v___x_2196_ = v___x_2193_;
v_isShared_2197_ = v_isSharedCheck_2201_;
goto v_resetjp_2195_;
}
else
{
lean_inc(v_a_2194_);
lean_dec(v___x_2193_);
v___x_2196_ = lean_box(0);
v_isShared_2197_ = v_isSharedCheck_2201_;
goto v_resetjp_2195_;
}
v_resetjp_2195_:
{
lean_object* v___x_2199_; 
if (v_isShared_2197_ == 0)
{
v___x_2199_ = v___x_2196_;
goto v_reusejp_2198_;
}
else
{
lean_object* v_reuseFailAlloc_2200_; 
v_reuseFailAlloc_2200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2200_, 0, v_a_2194_);
v___x_2199_ = v_reuseFailAlloc_2200_;
goto v_reusejp_2198_;
}
v_reusejp_2198_:
{
return v___x_2199_;
}
}
}
else
{
lean_object* v_a_2202_; lean_object* v___x_2204_; uint8_t v_isShared_2205_; uint8_t v_isSharedCheck_2209_; 
v_a_2202_ = lean_ctor_get(v___x_2193_, 0);
v_isSharedCheck_2209_ = !lean_is_exclusive(v___x_2193_);
if (v_isSharedCheck_2209_ == 0)
{
v___x_2204_ = v___x_2193_;
v_isShared_2205_ = v_isSharedCheck_2209_;
goto v_resetjp_2203_;
}
else
{
lean_inc(v_a_2202_);
lean_dec(v___x_2193_);
v___x_2204_ = lean_box(0);
v_isShared_2205_ = v_isSharedCheck_2209_;
goto v_resetjp_2203_;
}
v_resetjp_2203_:
{
lean_object* v___x_2207_; 
if (v_isShared_2205_ == 0)
{
v___x_2207_ = v___x_2204_;
goto v_reusejp_2206_;
}
else
{
lean_object* v_reuseFailAlloc_2208_; 
v_reuseFailAlloc_2208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2208_, 0, v_a_2202_);
v___x_2207_ = v_reuseFailAlloc_2208_;
goto v_reusejp_2206_;
}
v_reusejp_2206_:
{
return v___x_2207_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___redArg___boxed(lean_object* v_mvarId_2210_, lean_object* v_x_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_){
_start:
{
lean_object* v_res_2217_; 
v_res_2217_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___redArg(v_mvarId_2210_, v_x_2211_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_);
lean_dec(v___y_2215_);
lean_dec_ref(v___y_2214_);
lean_dec(v___y_2213_);
lean_dec_ref(v___y_2212_);
return v_res_2217_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3(lean_object* v_00_u03b1_2218_, lean_object* v_mvarId_2219_, lean_object* v_x_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_){
_start:
{
lean_object* v___x_2226_; 
v___x_2226_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___redArg(v_mvarId_2219_, v_x_2220_, v___y_2221_, v___y_2222_, v___y_2223_, v___y_2224_);
return v___x_2226_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___boxed(lean_object* v_00_u03b1_2227_, lean_object* v_mvarId_2228_, lean_object* v_x_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_){
_start:
{
lean_object* v_res_2235_; 
v_res_2235_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3(v_00_u03b1_2227_, v_mvarId_2228_, v_x_2229_, v___y_2230_, v___y_2231_, v___y_2232_, v___y_2233_);
lean_dec(v___y_2233_);
lean_dec_ref(v___y_2232_);
lean_dec(v___y_2231_);
lean_dec_ref(v___y_2230_);
return v_res_2235_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_induction_spec__2(lean_object* v_fst_2236_, lean_object* v_as_2237_, size_t v_sz_2238_, size_t v_i_2239_, lean_object* v_b_2240_){
_start:
{
uint8_t v___x_2241_; 
v___x_2241_ = lean_usize_dec_lt(v_i_2239_, v_sz_2238_);
if (v___x_2241_ == 0)
{
return v_b_2240_;
}
else
{
lean_object* v_fst_2242_; lean_object* v_snd_2243_; lean_object* v___x_2245_; uint8_t v_isShared_2246_; uint8_t v_isSharedCheck_2261_; 
v_fst_2242_ = lean_ctor_get(v_b_2240_, 0);
v_snd_2243_ = lean_ctor_get(v_b_2240_, 1);
v_isSharedCheck_2261_ = !lean_is_exclusive(v_b_2240_);
if (v_isSharedCheck_2261_ == 0)
{
v___x_2245_ = v_b_2240_;
v_isShared_2246_ = v_isSharedCheck_2261_;
goto v_resetjp_2244_;
}
else
{
lean_inc(v_snd_2243_);
lean_inc(v_fst_2242_);
lean_dec(v_b_2240_);
v___x_2245_ = lean_box(0);
v_isShared_2246_ = v_isSharedCheck_2261_;
goto v_resetjp_2244_;
}
v_resetjp_2244_:
{
lean_object* v___x_2247_; lean_object* v_a_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2256_; 
v___x_2247_ = lean_box(0);
v_a_2248_ = lean_array_uget_borrowed(v_as_2237_, v_i_2239_);
v___x_2249_ = l_Lean_Expr_fvarId_x21(v_a_2248_);
v___x_2250_ = lean_array_get_borrowed(v___x_2247_, v_fst_2236_, v_snd_2243_);
lean_inc(v___x_2250_);
v___x_2251_ = l_Lean_mkFVar(v___x_2250_);
v___x_2252_ = l_Lean_Meta_FVarSubst_insert(v_fst_2242_, v___x_2249_, v___x_2251_);
v___x_2253_ = lean_unsigned_to_nat(1u);
v___x_2254_ = lean_nat_add(v_snd_2243_, v___x_2253_);
lean_dec(v_snd_2243_);
if (v_isShared_2246_ == 0)
{
lean_ctor_set(v___x_2245_, 1, v___x_2254_);
lean_ctor_set(v___x_2245_, 0, v___x_2252_);
v___x_2256_ = v___x_2245_;
goto v_reusejp_2255_;
}
else
{
lean_object* v_reuseFailAlloc_2260_; 
v_reuseFailAlloc_2260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2260_, 0, v___x_2252_);
lean_ctor_set(v_reuseFailAlloc_2260_, 1, v___x_2254_);
v___x_2256_ = v_reuseFailAlloc_2260_;
goto v_reusejp_2255_;
}
v_reusejp_2255_:
{
size_t v___x_2257_; size_t v___x_2258_; 
v___x_2257_ = ((size_t)1ULL);
v___x_2258_ = lean_usize_add(v_i_2239_, v___x_2257_);
v_i_2239_ = v___x_2258_;
v_b_2240_ = v___x_2256_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_induction_spec__2___boxed(lean_object* v_fst_2262_, lean_object* v_as_2263_, lean_object* v_sz_2264_, lean_object* v_i_2265_, lean_object* v_b_2266_){
_start:
{
size_t v_sz_boxed_2267_; size_t v_i_boxed_2268_; lean_object* v_res_2269_; 
v_sz_boxed_2267_ = lean_unbox_usize(v_sz_2264_);
lean_dec(v_sz_2264_);
v_i_boxed_2268_ = lean_unbox_usize(v_i_2265_);
lean_dec(v_i_2265_);
v_res_2269_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_induction_spec__2(v_fst_2262_, v_as_2263_, v_sz_boxed_2267_, v_i_boxed_2268_, v_b_2266_);
lean_dec_ref(v_as_2263_);
lean_dec_ref(v_fst_2262_);
return v_res_2269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4___lam__0(lean_object* v_snd_2270_, lean_object* v___x_2271_, lean_object* v_fst_2272_, lean_object* v_a_2273_, lean_object* v___x_2274_, lean_object* v_givenNames_2275_, lean_object* v_fst_2276_, lean_object* v___x_2277_, lean_object* v_fst_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_){
_start:
{
lean_object* v___x_2284_; 
lean_inc_ref(v_a_2273_);
lean_inc(v_snd_2270_);
v___x_2284_ = l_Lean_Meta_mkRecursorAppPrefix(v_snd_2270_, v___x_2271_, v_fst_2272_, v_a_2273_, v___x_2274_, v___y_2279_, v___y_2280_, v___y_2281_, v___y_2282_);
if (lean_obj_tag(v___x_2284_) == 0)
{
lean_object* v_a_2285_; lean_object* v___x_2286_; 
v_a_2285_ = lean_ctor_get(v___x_2284_, 0);
lean_inc(v_a_2285_);
lean_dec_ref_known(v___x_2284_, 1);
v___x_2286_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize(v_snd_2270_, v_givenNames_2275_, v_a_2273_, v_fst_2276_, v___x_2277_, v___x_2274_, v_fst_2278_, v_a_2285_, v___y_2279_, v___y_2280_, v___y_2281_, v___y_2282_);
lean_dec_ref(v_a_2273_);
return v___x_2286_;
}
else
{
lean_object* v_a_2287_; lean_object* v___x_2289_; uint8_t v_isShared_2290_; uint8_t v_isSharedCheck_2294_; 
lean_dec(v_fst_2278_);
lean_dec_ref(v___x_2277_);
lean_dec_ref(v_a_2273_);
lean_dec(v_snd_2270_);
v_a_2287_ = lean_ctor_get(v___x_2284_, 0);
v_isSharedCheck_2294_ = !lean_is_exclusive(v___x_2284_);
if (v_isSharedCheck_2294_ == 0)
{
v___x_2289_ = v___x_2284_;
v_isShared_2290_ = v_isSharedCheck_2294_;
goto v_resetjp_2288_;
}
else
{
lean_inc(v_a_2287_);
lean_dec(v___x_2284_);
v___x_2289_ = lean_box(0);
v_isShared_2290_ = v_isSharedCheck_2294_;
goto v_resetjp_2288_;
}
v_resetjp_2288_:
{
lean_object* v___x_2292_; 
if (v_isShared_2290_ == 0)
{
v___x_2292_ = v___x_2289_;
goto v_reusejp_2291_;
}
else
{
lean_object* v_reuseFailAlloc_2293_; 
v_reuseFailAlloc_2293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2293_, 0, v_a_2287_);
v___x_2292_ = v_reuseFailAlloc_2293_;
goto v_reusejp_2291_;
}
v_reusejp_2291_:
{
return v___x_2292_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4___lam__0___boxed(lean_object* v_snd_2295_, lean_object* v___x_2296_, lean_object* v_fst_2297_, lean_object* v_a_2298_, lean_object* v___x_2299_, lean_object* v_givenNames_2300_, lean_object* v_fst_2301_, lean_object* v___x_2302_, lean_object* v_fst_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_){
_start:
{
lean_object* v_res_2309_; 
v_res_2309_ = l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4___lam__0(v_snd_2295_, v___x_2296_, v_fst_2297_, v_a_2298_, v___x_2299_, v_givenNames_2300_, v_fst_2301_, v___x_2302_, v_fst_2303_, v___y_2304_, v___y_2305_, v___y_2306_, v___y_2307_);
lean_dec(v___y_2307_);
lean_dec_ref(v___y_2306_);
lean_dec(v___y_2305_);
lean_dec_ref(v___y_2304_);
lean_dec_ref(v_fst_2301_);
lean_dec_ref(v_givenNames_2300_);
lean_dec_ref(v___x_2299_);
return v_res_2309_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_induction_spec__1(size_t v_sz_2310_, size_t v_i_2311_, lean_object* v_bs_2312_){
_start:
{
uint8_t v___x_2313_; 
v___x_2313_ = lean_usize_dec_lt(v_i_2311_, v_sz_2310_);
if (v___x_2313_ == 0)
{
return v_bs_2312_;
}
else
{
lean_object* v_v_2314_; lean_object* v___x_2315_; lean_object* v_bs_x27_2316_; lean_object* v___x_2317_; size_t v___x_2318_; size_t v___x_2319_; lean_object* v___x_2320_; 
v_v_2314_ = lean_array_uget(v_bs_2312_, v_i_2311_);
v___x_2315_ = lean_unsigned_to_nat(0u);
v_bs_x27_2316_ = lean_array_uset(v_bs_2312_, v_i_2311_, v___x_2315_);
v___x_2317_ = l_Lean_Expr_fvarId_x21(v_v_2314_);
lean_dec(v_v_2314_);
v___x_2318_ = ((size_t)1ULL);
v___x_2319_ = lean_usize_add(v_i_2311_, v___x_2318_);
v___x_2320_ = lean_array_uset(v_bs_x27_2316_, v_i_2311_, v___x_2317_);
v_i_2311_ = v___x_2319_;
v_bs_2312_ = v___x_2320_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_induction_spec__1___boxed(lean_object* v_sz_2322_, lean_object* v_i_2323_, lean_object* v_bs_2324_){
_start:
{
size_t v_sz_boxed_2325_; size_t v_i_boxed_2326_; lean_object* v_res_2327_; 
v_sz_boxed_2325_ = lean_unbox_usize(v_sz_2322_);
lean_dec(v_sz_2322_);
v_i_boxed_2326_ = lean_unbox_usize(v_i_2323_);
lean_dec(v_i_2323_);
v_res_2327_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_induction_spec__1(v_sz_boxed_2325_, v_i_boxed_2326_, v_bs_2324_);
return v_res_2327_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_MVarId_induction_spec__0(lean_object* v_majorTypeArgs_2328_, lean_object* v_val_2329_, lean_object* v_mvarId_2330_, lean_object* v_as_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_){
_start:
{
if (lean_obj_tag(v_as_2331_) == 0)
{
lean_object* v___x_2337_; lean_object* v___x_2338_; 
lean_dec(v_mvarId_2330_);
lean_dec_ref(v_val_2329_);
v___x_2337_ = lean_box(0);
v___x_2338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2338_, 0, v___x_2337_);
return v___x_2338_;
}
else
{
lean_object* v_head_2339_; 
v_head_2339_ = lean_ctor_get(v_as_2331_, 0);
lean_inc(v_head_2339_);
if (lean_obj_tag(v_head_2339_) == 0)
{
lean_object* v_tail_2340_; 
v_tail_2340_ = lean_ctor_get(v_as_2331_, 1);
lean_inc(v_tail_2340_);
lean_dec_ref_known(v_as_2331_, 2);
v_as_2331_ = v_tail_2340_;
goto _start;
}
else
{
lean_object* v_tail_2342_; lean_object* v___x_2344_; uint8_t v_isShared_2345_; uint8_t v_isSharedCheck_2365_; 
v_tail_2342_ = lean_ctor_get(v_as_2331_, 1);
v_isSharedCheck_2365_ = !lean_is_exclusive(v_as_2331_);
if (v_isSharedCheck_2365_ == 0)
{
lean_object* v_unused_2366_; 
v_unused_2366_ = lean_ctor_get(v_as_2331_, 0);
lean_dec(v_unused_2366_);
v___x_2344_ = v_as_2331_;
v_isShared_2345_ = v_isSharedCheck_2365_;
goto v_resetjp_2343_;
}
else
{
lean_inc(v_tail_2342_);
lean_dec(v_as_2331_);
v___x_2344_ = lean_box(0);
v_isShared_2345_ = v_isSharedCheck_2365_;
goto v_resetjp_2343_;
}
v_resetjp_2343_:
{
lean_object* v_val_2346_; lean_object* v___x_2348_; uint8_t v_isShared_2349_; uint8_t v_isSharedCheck_2364_; 
v_val_2346_ = lean_ctor_get(v_head_2339_, 0);
v_isSharedCheck_2364_ = !lean_is_exclusive(v_head_2339_);
if (v_isSharedCheck_2364_ == 0)
{
v___x_2348_ = v_head_2339_;
v_isShared_2349_ = v_isSharedCheck_2364_;
goto v_resetjp_2347_;
}
else
{
lean_inc(v_val_2346_);
lean_dec(v_head_2339_);
v___x_2348_ = lean_box(0);
v_isShared_2349_ = v_isSharedCheck_2364_;
goto v_resetjp_2347_;
}
v_resetjp_2347_:
{
lean_object* v___x_2350_; uint8_t v___x_2351_; 
v___x_2350_ = lean_array_get_size(v_majorTypeArgs_2328_);
v___x_2351_ = lean_nat_dec_le(v___x_2350_, v_val_2346_);
lean_dec(v_val_2346_);
if (v___x_2351_ == 0)
{
lean_del_object(v___x_2348_);
lean_del_object(v___x_2344_);
v_as_2331_ = v_tail_2342_;
goto _start;
}
else
{
lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2357_; 
v___x_2353_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1));
v___x_2354_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__5, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__5);
lean_inc_ref(v_val_2329_);
v___x_2355_ = l_Lean_indentExpr(v_val_2329_);
if (v_isShared_2345_ == 0)
{
lean_ctor_set_tag(v___x_2344_, 7);
lean_ctor_set(v___x_2344_, 1, v___x_2355_);
lean_ctor_set(v___x_2344_, 0, v___x_2354_);
v___x_2357_ = v___x_2344_;
goto v_reusejp_2356_;
}
else
{
lean_object* v_reuseFailAlloc_2363_; 
v_reuseFailAlloc_2363_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2363_, 0, v___x_2354_);
lean_ctor_set(v_reuseFailAlloc_2363_, 1, v___x_2355_);
v___x_2357_ = v_reuseFailAlloc_2363_;
goto v_reusejp_2356_;
}
v_reusejp_2356_:
{
lean_object* v___x_2359_; 
if (v_isShared_2349_ == 0)
{
lean_ctor_set(v___x_2348_, 0, v___x_2357_);
v___x_2359_ = v___x_2348_;
goto v_reusejp_2358_;
}
else
{
lean_object* v_reuseFailAlloc_2362_; 
v_reuseFailAlloc_2362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2362_, 0, v___x_2357_);
v___x_2359_ = v_reuseFailAlloc_2362_;
goto v_reusejp_2358_;
}
v_reusejp_2358_:
{
lean_object* v___x_2360_; 
lean_inc(v_mvarId_2330_);
v___x_2360_ = l_Lean_Meta_throwTacticEx___redArg(v___x_2353_, v_mvarId_2330_, v___x_2359_, v___y_2332_, v___y_2333_, v___y_2334_, v___y_2335_);
if (lean_obj_tag(v___x_2360_) == 0)
{
lean_dec_ref_known(v___x_2360_, 1);
v_as_2331_ = v_tail_2342_;
goto _start;
}
else
{
lean_dec(v_tail_2342_);
lean_dec(v_mvarId_2330_);
lean_dec_ref(v_val_2329_);
return v___x_2360_;
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
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_MVarId_induction_spec__0___boxed(lean_object* v_majorTypeArgs_2367_, lean_object* v_val_2368_, lean_object* v_mvarId_2369_, lean_object* v_as_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_){
_start:
{
lean_object* v_res_2376_; 
v_res_2376_ = l_List_forM___at___00Lean_MVarId_induction_spec__0(v_majorTypeArgs_2367_, v_val_2368_, v_mvarId_2369_, v_as_2370_, v___y_2371_, v___y_2372_, v___y_2373_, v___y_2374_);
lean_dec(v___y_2374_);
lean_dec_ref(v___y_2373_);
lean_dec(v___y_2372_);
lean_dec_ref(v___y_2371_);
lean_dec_ref(v_majorTypeArgs_2367_);
return v_res_2376_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__1(void){
_start:
{
lean_object* v___x_2378_; lean_object* v___x_2379_; 
v___x_2378_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__0));
v___x_2379_ = l_Lean_stringToMessageData(v___x_2378_);
return v___x_2379_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__3(void){
_start:
{
lean_object* v___x_2381_; lean_object* v___x_2382_; 
v___x_2381_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__2));
v___x_2382_ = l_Lean_stringToMessageData(v___x_2381_);
return v___x_2382_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__5(void){
_start:
{
lean_object* v___x_2384_; lean_object* v___x_2385_; 
v___x_2384_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__4));
v___x_2385_ = l_Lean_stringToMessageData(v___x_2384_);
return v___x_2385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4(lean_object* v_a_2386_, lean_object* v_val_2387_, lean_object* v_mvarId_2388_, lean_object* v_majorFVarId_2389_, lean_object* v_givenNames_2390_, lean_object* v_recursorName_2391_, lean_object* v_x_2392_, lean_object* v_x_2393_, lean_object* v_x_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_){
_start:
{
if (lean_obj_tag(v_x_2392_) == 5)
{
lean_object* v_fn_2400_; lean_object* v_arg_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; 
v_fn_2400_ = lean_ctor_get(v_x_2392_, 0);
lean_inc_ref(v_fn_2400_);
v_arg_2401_ = lean_ctor_get(v_x_2392_, 1);
lean_inc_ref(v_arg_2401_);
lean_dec_ref_known(v_x_2392_, 2);
v___x_2402_ = lean_array_set(v_x_2393_, v_x_2394_, v_arg_2401_);
v___x_2403_ = lean_unsigned_to_nat(1u);
v___x_2404_ = lean_nat_sub(v_x_2394_, v___x_2403_);
lean_dec(v_x_2394_);
v_x_2392_ = v_fn_2400_;
v_x_2393_ = v___x_2402_;
v_x_2394_ = v___x_2404_;
goto _start;
}
else
{
uint8_t v_depElim_2406_; lean_object* v_paramsPos_2407_; lean_object* v___x_2408_; 
lean_dec(v_x_2394_);
lean_dec_ref(v_x_2392_);
v_depElim_2406_ = lean_ctor_get_uint8(v_a_2386_, sizeof(void*)*8);
v_paramsPos_2407_ = lean_ctor_get(v_a_2386_, 5);
lean_inc(v_paramsPos_2407_);
lean_inc(v_mvarId_2388_);
lean_inc_ref(v_val_2387_);
v___x_2408_ = l_List_forM___at___00Lean_MVarId_induction_spec__0(v_x_2393_, v_val_2387_, v_mvarId_2388_, v_paramsPos_2407_, v___y_2395_, v___y_2396_, v___y_2397_, v___y_2398_);
lean_dec_ref(v_x_2393_);
if (lean_obj_tag(v___x_2408_) == 0)
{
lean_object* v___x_2409_; lean_object* v___y_2411_; lean_object* v___y_2412_; lean_object* v___y_2413_; lean_object* v___y_2414_; lean_object* v___y_2415_; size_t v___y_2416_; lean_object* v___y_2417_; lean_object* v___y_2418_; lean_object* v___y_2419_; lean_object* v___y_2420_; lean_object* v___y_2421_; lean_object* v___y_2422_; lean_object* v___x_2427_; 
lean_dec_ref_known(v___x_2408_, 1);
v___x_2409_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1));
lean_inc_ref(v_a_2386_);
lean_inc(v_mvarId_2388_);
v___x_2427_ = l_Lean_Meta_getMajorTypeIndices(v_mvarId_2388_, v___x_2409_, v_a_2386_, v_val_2387_, v___y_2395_, v___y_2396_, v___y_2397_, v___y_2398_);
if (lean_obj_tag(v___x_2427_) == 0)
{
lean_object* v_a_2428_; lean_object* v___x_2429_; 
v_a_2428_ = lean_ctor_get(v___x_2427_, 0);
lean_inc(v_a_2428_);
lean_dec_ref_known(v___x_2427_, 1);
lean_inc(v_mvarId_2388_);
v___x_2429_ = l_Lean_MVarId_getType(v_mvarId_2388_, v___y_2395_, v___y_2396_, v___y_2397_, v___y_2398_);
if (lean_obj_tag(v___x_2429_) == 0)
{
lean_object* v_a_2430_; lean_object* v_cls_2431_; lean_object* v___y_2433_; lean_object* v___y_2434_; lean_object* v___y_2435_; lean_object* v___y_2436_; 
v_a_2430_ = lean_ctor_get(v___x_2429_, 0);
lean_inc(v_a_2430_);
lean_dec_ref_known(v___x_2429_, 1);
v_cls_2431_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__2));
if (v_depElim_2406_ == 0)
{
lean_object* v___x_2519_; lean_object* v_a_2520_; lean_object* v___x_2522_; uint8_t v_isShared_2523_; uint8_t v_isSharedCheck_2542_; 
lean_inc(v_majorFVarId_2389_);
v___x_2519_ = l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2___redArg(v_a_2430_, v_majorFVarId_2389_, v___y_2396_);
v_a_2520_ = lean_ctor_get(v___x_2519_, 0);
v_isSharedCheck_2542_ = !lean_is_exclusive(v___x_2519_);
if (v_isSharedCheck_2542_ == 0)
{
v___x_2522_ = v___x_2519_;
v_isShared_2523_ = v_isSharedCheck_2542_;
goto v_resetjp_2521_;
}
else
{
lean_inc(v_a_2520_);
lean_dec(v___x_2519_);
v___x_2522_ = lean_box(0);
v_isShared_2523_ = v_isSharedCheck_2542_;
goto v_resetjp_2521_;
}
v_resetjp_2521_:
{
uint8_t v___x_2524_; 
v___x_2524_ = lean_unbox(v_a_2520_);
lean_dec(v_a_2520_);
if (v___x_2524_ == 0)
{
lean_del_object(v___x_2522_);
lean_dec(v_recursorName_2391_);
v___y_2433_ = v___y_2395_;
v___y_2434_ = v___y_2396_;
v___y_2435_ = v___y_2397_;
v___y_2436_ = v___y_2398_;
goto v___jp_2432_;
}
else
{
lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2531_; 
v___x_2525_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__3, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__3);
v___x_2526_ = l_Lean_MessageData_ofName(v_recursorName_2391_);
v___x_2527_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2527_, 0, v___x_2525_);
lean_ctor_set(v___x_2527_, 1, v___x_2526_);
v___x_2528_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__5, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__5_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__5);
v___x_2529_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2529_, 0, v___x_2527_);
lean_ctor_set(v___x_2529_, 1, v___x_2528_);
if (v_isShared_2523_ == 0)
{
lean_ctor_set_tag(v___x_2522_, 1);
lean_ctor_set(v___x_2522_, 0, v___x_2529_);
v___x_2531_ = v___x_2522_;
goto v_reusejp_2530_;
}
else
{
lean_object* v_reuseFailAlloc_2541_; 
v_reuseFailAlloc_2541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2541_, 0, v___x_2529_);
v___x_2531_ = v_reuseFailAlloc_2541_;
goto v_reusejp_2530_;
}
v_reusejp_2530_:
{
lean_object* v___x_2532_; 
lean_inc(v_mvarId_2388_);
v___x_2532_ = l_Lean_Meta_throwTacticEx___redArg(v___x_2409_, v_mvarId_2388_, v___x_2531_, v___y_2395_, v___y_2396_, v___y_2397_, v___y_2398_);
if (lean_obj_tag(v___x_2532_) == 0)
{
lean_dec_ref_known(v___x_2532_, 1);
v___y_2433_ = v___y_2395_;
v___y_2434_ = v___y_2396_;
v___y_2435_ = v___y_2397_;
v___y_2436_ = v___y_2398_;
goto v___jp_2432_;
}
else
{
lean_object* v_a_2533_; lean_object* v___x_2535_; uint8_t v_isShared_2536_; uint8_t v_isSharedCheck_2540_; 
lean_dec(v_a_2428_);
lean_dec_ref(v_givenNames_2390_);
lean_dec(v_majorFVarId_2389_);
lean_dec(v_mvarId_2388_);
lean_dec_ref(v_a_2386_);
v_a_2533_ = lean_ctor_get(v___x_2532_, 0);
v_isSharedCheck_2540_ = !lean_is_exclusive(v___x_2532_);
if (v_isSharedCheck_2540_ == 0)
{
v___x_2535_ = v___x_2532_;
v_isShared_2536_ = v_isSharedCheck_2540_;
goto v_resetjp_2534_;
}
else
{
lean_inc(v_a_2533_);
lean_dec(v___x_2532_);
v___x_2535_ = lean_box(0);
v_isShared_2536_ = v_isSharedCheck_2540_;
goto v_resetjp_2534_;
}
v_resetjp_2534_:
{
lean_object* v___x_2538_; 
if (v_isShared_2536_ == 0)
{
v___x_2538_ = v___x_2535_;
goto v_reusejp_2537_;
}
else
{
lean_object* v_reuseFailAlloc_2539_; 
v_reuseFailAlloc_2539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2539_, 0, v_a_2533_);
v___x_2538_ = v_reuseFailAlloc_2539_;
goto v_reusejp_2537_;
}
v_reusejp_2537_:
{
return v___x_2538_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_2430_);
lean_dec(v_recursorName_2391_);
v___y_2433_ = v___y_2395_;
v___y_2434_ = v___y_2396_;
v___y_2435_ = v___y_2397_;
v___y_2436_ = v___y_2398_;
goto v___jp_2432_;
}
v___jp_2432_:
{
size_t v_sz_2437_; size_t v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; uint8_t v___x_2441_; uint8_t v___x_2442_; lean_object* v___x_2443_; 
v_sz_2437_ = lean_array_size(v_a_2428_);
v___x_2438_ = ((size_t)0ULL);
lean_inc(v_a_2428_);
v___x_2439_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_induction_spec__1(v_sz_2437_, v___x_2438_, v_a_2428_);
lean_inc(v_majorFVarId_2389_);
v___x_2440_ = lean_array_push(v___x_2439_, v_majorFVarId_2389_);
v___x_2441_ = 1;
v___x_2442_ = 0;
v___x_2443_ = l_Lean_MVarId_revert(v_mvarId_2388_, v___x_2440_, v___x_2441_, v___x_2442_, v___y_2433_, v___y_2434_, v___y_2435_, v___y_2436_);
if (lean_obj_tag(v___x_2443_) == 0)
{
lean_object* v_a_2444_; lean_object* v_fst_2445_; lean_object* v_snd_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; 
v_a_2444_ = lean_ctor_get(v___x_2443_, 0);
lean_inc(v_a_2444_);
lean_dec_ref_known(v___x_2443_, 1);
v_fst_2445_ = lean_ctor_get(v_a_2444_, 0);
lean_inc(v_fst_2445_);
v_snd_2446_ = lean_ctor_get(v_a_2444_, 1);
lean_inc(v_snd_2446_);
lean_dec(v_a_2444_);
v___x_2447_ = lean_array_get_size(v_a_2428_);
v___x_2448_ = lean_box(0);
v___x_2449_ = l_Lean_Meta_introNCore(v_snd_2446_, v___x_2447_, v___x_2448_, v___x_2442_, v___x_2441_, v___y_2433_, v___y_2434_, v___y_2435_, v___y_2436_);
if (lean_obj_tag(v___x_2449_) == 0)
{
lean_object* v_a_2450_; lean_object* v_fst_2451_; lean_object* v_snd_2452_; lean_object* v___x_2453_; 
v_a_2450_ = lean_ctor_get(v___x_2449_, 0);
lean_inc(v_a_2450_);
lean_dec_ref_known(v___x_2449_, 1);
v_fst_2451_ = lean_ctor_get(v_a_2450_, 0);
lean_inc(v_fst_2451_);
v_snd_2452_ = lean_ctor_get(v_a_2450_, 1);
lean_inc(v_snd_2452_);
lean_dec(v_a_2450_);
v___x_2453_ = l_Lean_Meta_intro1Core(v_snd_2452_, v___x_2441_, v___y_2433_, v___y_2434_, v___y_2435_, v___y_2436_);
if (lean_obj_tag(v___x_2453_) == 0)
{
lean_object* v_a_2454_; lean_object* v_fst_2455_; lean_object* v_snd_2456_; lean_object* v___x_2458_; uint8_t v_isShared_2459_; uint8_t v_isSharedCheck_2494_; 
v_a_2454_ = lean_ctor_get(v___x_2453_, 0);
lean_inc(v_a_2454_);
lean_dec_ref_known(v___x_2453_, 1);
v_fst_2455_ = lean_ctor_get(v_a_2454_, 0);
v_snd_2456_ = lean_ctor_get(v_a_2454_, 1);
v_isSharedCheck_2494_ = !lean_is_exclusive(v_a_2454_);
if (v_isSharedCheck_2494_ == 0)
{
v___x_2458_ = v_a_2454_;
v_isShared_2459_ = v_isSharedCheck_2494_;
goto v_resetjp_2457_;
}
else
{
lean_inc(v_snd_2456_);
lean_inc(v_fst_2455_);
lean_dec(v_a_2454_);
v___x_2458_ = lean_box(0);
v_isShared_2459_ = v_isSharedCheck_2494_;
goto v_resetjp_2457_;
}
v_resetjp_2457_:
{
lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2465_; 
v___x_2460_ = lean_box(0);
lean_inc(v_fst_2455_);
v___x_2461_ = l_Lean_mkFVar(v_fst_2455_);
lean_inc_ref(v___x_2461_);
v___x_2462_ = l_Lean_Meta_FVarSubst_insert(v___x_2460_, v_majorFVarId_2389_, v___x_2461_);
v___x_2463_ = lean_unsigned_to_nat(0u);
if (v_isShared_2459_ == 0)
{
lean_ctor_set(v___x_2458_, 1, v___x_2463_);
lean_ctor_set(v___x_2458_, 0, v___x_2462_);
v___x_2465_ = v___x_2458_;
goto v_reusejp_2464_;
}
else
{
lean_object* v_reuseFailAlloc_2493_; 
v_reuseFailAlloc_2493_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2493_, 0, v___x_2462_);
lean_ctor_set(v_reuseFailAlloc_2493_, 1, v___x_2463_);
v___x_2465_ = v_reuseFailAlloc_2493_;
goto v_reusejp_2464_;
}
v_reusejp_2464_:
{
lean_object* v___x_2466_; lean_object* v_options_2467_; uint8_t v_hasTrace_2468_; 
v___x_2466_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_induction_spec__2(v_fst_2451_, v_a_2428_, v_sz_2437_, v___x_2438_, v___x_2465_);
lean_dec(v_a_2428_);
v_options_2467_ = lean_ctor_get(v___y_2435_, 2);
v_hasTrace_2468_ = lean_ctor_get_uint8(v_options_2467_, sizeof(void*)*1);
if (v_hasTrace_2468_ == 0)
{
lean_object* v_fst_2469_; 
v_fst_2469_ = lean_ctor_get(v___x_2466_, 0);
lean_inc(v_fst_2469_);
lean_dec_ref(v___x_2466_);
lean_inc(v_snd_2456_);
v___y_2411_ = v_fst_2469_;
v___y_2412_ = v_fst_2455_;
v___y_2413_ = v___x_2461_;
v___y_2414_ = v_fst_2445_;
v___y_2415_ = v_snd_2456_;
v___y_2416_ = v___x_2438_;
v___y_2417_ = v_fst_2451_;
v___y_2418_ = v_snd_2456_;
v___y_2419_ = v___y_2433_;
v___y_2420_ = v___y_2434_;
v___y_2421_ = v___y_2435_;
v___y_2422_ = v___y_2436_;
goto v___jp_2410_;
}
else
{
lean_object* v_fst_2470_; lean_object* v___x_2472_; uint8_t v_isShared_2473_; uint8_t v_isSharedCheck_2491_; 
v_fst_2470_ = lean_ctor_get(v___x_2466_, 0);
v_isSharedCheck_2491_ = !lean_is_exclusive(v___x_2466_);
if (v_isSharedCheck_2491_ == 0)
{
lean_object* v_unused_2492_; 
v_unused_2492_ = lean_ctor_get(v___x_2466_, 1);
lean_dec(v_unused_2492_);
v___x_2472_ = v___x_2466_;
v_isShared_2473_ = v_isSharedCheck_2491_;
goto v_resetjp_2471_;
}
else
{
lean_inc(v_fst_2470_);
lean_dec(v___x_2466_);
v___x_2472_ = lean_box(0);
v_isShared_2473_ = v_isSharedCheck_2491_;
goto v_resetjp_2471_;
}
v_resetjp_2471_:
{
lean_object* v_inheritedTraceOptions_2474_; lean_object* v___x_2475_; uint8_t v___x_2476_; 
v_inheritedTraceOptions_2474_ = lean_ctor_get(v___y_2435_, 13);
v___x_2475_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5);
v___x_2476_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2474_, v_options_2467_, v___x_2475_);
if (v___x_2476_ == 0)
{
lean_del_object(v___x_2472_);
lean_inc(v_snd_2456_);
v___y_2411_ = v_fst_2470_;
v___y_2412_ = v_fst_2455_;
v___y_2413_ = v___x_2461_;
v___y_2414_ = v_fst_2445_;
v___y_2415_ = v_snd_2456_;
v___y_2416_ = v___x_2438_;
v___y_2417_ = v_fst_2451_;
v___y_2418_ = v_snd_2456_;
v___y_2419_ = v___y_2433_;
v___y_2420_ = v___y_2434_;
v___y_2421_ = v___y_2435_;
v___y_2422_ = v___y_2436_;
goto v___jp_2410_;
}
else
{
lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2480_; 
v___x_2477_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__1);
lean_inc(v_snd_2456_);
v___x_2478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2478_, 0, v_snd_2456_);
if (v_isShared_2473_ == 0)
{
lean_ctor_set_tag(v___x_2472_, 7);
lean_ctor_set(v___x_2472_, 1, v___x_2478_);
lean_ctor_set(v___x_2472_, 0, v___x_2477_);
v___x_2480_ = v___x_2472_;
goto v_reusejp_2479_;
}
else
{
lean_object* v_reuseFailAlloc_2490_; 
v_reuseFailAlloc_2490_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2490_, 0, v___x_2477_);
lean_ctor_set(v_reuseFailAlloc_2490_, 1, v___x_2478_);
v___x_2480_ = v_reuseFailAlloc_2490_;
goto v_reusejp_2479_;
}
v_reusejp_2479_:
{
lean_object* v___x_2481_; 
v___x_2481_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1(v_cls_2431_, v___x_2480_, v___y_2433_, v___y_2434_, v___y_2435_, v___y_2436_);
if (lean_obj_tag(v___x_2481_) == 0)
{
lean_dec_ref_known(v___x_2481_, 1);
lean_inc(v_snd_2456_);
v___y_2411_ = v_fst_2470_;
v___y_2412_ = v_fst_2455_;
v___y_2413_ = v___x_2461_;
v___y_2414_ = v_fst_2445_;
v___y_2415_ = v_snd_2456_;
v___y_2416_ = v___x_2438_;
v___y_2417_ = v_fst_2451_;
v___y_2418_ = v_snd_2456_;
v___y_2419_ = v___y_2433_;
v___y_2420_ = v___y_2434_;
v___y_2421_ = v___y_2435_;
v___y_2422_ = v___y_2436_;
goto v___jp_2410_;
}
else
{
lean_object* v_a_2482_; lean_object* v___x_2484_; uint8_t v_isShared_2485_; uint8_t v_isSharedCheck_2489_; 
lean_dec(v_fst_2470_);
lean_dec_ref(v___x_2461_);
lean_dec(v_snd_2456_);
lean_dec(v_fst_2455_);
lean_dec(v_fst_2451_);
lean_dec(v_fst_2445_);
lean_dec_ref(v_givenNames_2390_);
lean_dec_ref(v_a_2386_);
v_a_2482_ = lean_ctor_get(v___x_2481_, 0);
v_isSharedCheck_2489_ = !lean_is_exclusive(v___x_2481_);
if (v_isSharedCheck_2489_ == 0)
{
v___x_2484_ = v___x_2481_;
v_isShared_2485_ = v_isSharedCheck_2489_;
goto v_resetjp_2483_;
}
else
{
lean_inc(v_a_2482_);
lean_dec(v___x_2481_);
v___x_2484_ = lean_box(0);
v_isShared_2485_ = v_isSharedCheck_2489_;
goto v_resetjp_2483_;
}
v_resetjp_2483_:
{
lean_object* v___x_2487_; 
if (v_isShared_2485_ == 0)
{
v___x_2487_ = v___x_2484_;
goto v_reusejp_2486_;
}
else
{
lean_object* v_reuseFailAlloc_2488_; 
v_reuseFailAlloc_2488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2488_, 0, v_a_2482_);
v___x_2487_ = v_reuseFailAlloc_2488_;
goto v_reusejp_2486_;
}
v_reusejp_2486_:
{
return v___x_2487_;
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
lean_object* v_a_2495_; lean_object* v___x_2497_; uint8_t v_isShared_2498_; uint8_t v_isSharedCheck_2502_; 
lean_dec(v_fst_2451_);
lean_dec(v_fst_2445_);
lean_dec(v_a_2428_);
lean_dec_ref(v_givenNames_2390_);
lean_dec(v_majorFVarId_2389_);
lean_dec_ref(v_a_2386_);
v_a_2495_ = lean_ctor_get(v___x_2453_, 0);
v_isSharedCheck_2502_ = !lean_is_exclusive(v___x_2453_);
if (v_isSharedCheck_2502_ == 0)
{
v___x_2497_ = v___x_2453_;
v_isShared_2498_ = v_isSharedCheck_2502_;
goto v_resetjp_2496_;
}
else
{
lean_inc(v_a_2495_);
lean_dec(v___x_2453_);
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
else
{
lean_object* v_a_2503_; lean_object* v___x_2505_; uint8_t v_isShared_2506_; uint8_t v_isSharedCheck_2510_; 
lean_dec(v_fst_2445_);
lean_dec(v_a_2428_);
lean_dec_ref(v_givenNames_2390_);
lean_dec(v_majorFVarId_2389_);
lean_dec_ref(v_a_2386_);
v_a_2503_ = lean_ctor_get(v___x_2449_, 0);
v_isSharedCheck_2510_ = !lean_is_exclusive(v___x_2449_);
if (v_isSharedCheck_2510_ == 0)
{
v___x_2505_ = v___x_2449_;
v_isShared_2506_ = v_isSharedCheck_2510_;
goto v_resetjp_2504_;
}
else
{
lean_inc(v_a_2503_);
lean_dec(v___x_2449_);
v___x_2505_ = lean_box(0);
v_isShared_2506_ = v_isSharedCheck_2510_;
goto v_resetjp_2504_;
}
v_resetjp_2504_:
{
lean_object* v___x_2508_; 
if (v_isShared_2506_ == 0)
{
v___x_2508_ = v___x_2505_;
goto v_reusejp_2507_;
}
else
{
lean_object* v_reuseFailAlloc_2509_; 
v_reuseFailAlloc_2509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2509_, 0, v_a_2503_);
v___x_2508_ = v_reuseFailAlloc_2509_;
goto v_reusejp_2507_;
}
v_reusejp_2507_:
{
return v___x_2508_;
}
}
}
}
else
{
lean_object* v_a_2511_; lean_object* v___x_2513_; uint8_t v_isShared_2514_; uint8_t v_isSharedCheck_2518_; 
lean_dec(v_a_2428_);
lean_dec_ref(v_givenNames_2390_);
lean_dec(v_majorFVarId_2389_);
lean_dec_ref(v_a_2386_);
v_a_2511_ = lean_ctor_get(v___x_2443_, 0);
v_isSharedCheck_2518_ = !lean_is_exclusive(v___x_2443_);
if (v_isSharedCheck_2518_ == 0)
{
v___x_2513_ = v___x_2443_;
v_isShared_2514_ = v_isSharedCheck_2518_;
goto v_resetjp_2512_;
}
else
{
lean_inc(v_a_2511_);
lean_dec(v___x_2443_);
v___x_2513_ = lean_box(0);
v_isShared_2514_ = v_isSharedCheck_2518_;
goto v_resetjp_2512_;
}
v_resetjp_2512_:
{
lean_object* v___x_2516_; 
if (v_isShared_2514_ == 0)
{
v___x_2516_ = v___x_2513_;
goto v_reusejp_2515_;
}
else
{
lean_object* v_reuseFailAlloc_2517_; 
v_reuseFailAlloc_2517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2517_, 0, v_a_2511_);
v___x_2516_ = v_reuseFailAlloc_2517_;
goto v_reusejp_2515_;
}
v_reusejp_2515_:
{
return v___x_2516_;
}
}
}
}
}
else
{
lean_object* v_a_2543_; lean_object* v___x_2545_; uint8_t v_isShared_2546_; uint8_t v_isSharedCheck_2550_; 
lean_dec(v_a_2428_);
lean_dec(v_recursorName_2391_);
lean_dec_ref(v_givenNames_2390_);
lean_dec(v_majorFVarId_2389_);
lean_dec(v_mvarId_2388_);
lean_dec_ref(v_a_2386_);
v_a_2543_ = lean_ctor_get(v___x_2429_, 0);
v_isSharedCheck_2550_ = !lean_is_exclusive(v___x_2429_);
if (v_isSharedCheck_2550_ == 0)
{
v___x_2545_ = v___x_2429_;
v_isShared_2546_ = v_isSharedCheck_2550_;
goto v_resetjp_2544_;
}
else
{
lean_inc(v_a_2543_);
lean_dec(v___x_2429_);
v___x_2545_ = lean_box(0);
v_isShared_2546_ = v_isSharedCheck_2550_;
goto v_resetjp_2544_;
}
v_resetjp_2544_:
{
lean_object* v___x_2548_; 
if (v_isShared_2546_ == 0)
{
v___x_2548_ = v___x_2545_;
goto v_reusejp_2547_;
}
else
{
lean_object* v_reuseFailAlloc_2549_; 
v_reuseFailAlloc_2549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2549_, 0, v_a_2543_);
v___x_2548_ = v_reuseFailAlloc_2549_;
goto v_reusejp_2547_;
}
v_reusejp_2547_:
{
return v___x_2548_;
}
}
}
}
else
{
lean_object* v_a_2551_; lean_object* v___x_2553_; uint8_t v_isShared_2554_; uint8_t v_isSharedCheck_2558_; 
lean_dec(v_recursorName_2391_);
lean_dec_ref(v_givenNames_2390_);
lean_dec(v_majorFVarId_2389_);
lean_dec(v_mvarId_2388_);
lean_dec_ref(v_a_2386_);
v_a_2551_ = lean_ctor_get(v___x_2427_, 0);
v_isSharedCheck_2558_ = !lean_is_exclusive(v___x_2427_);
if (v_isSharedCheck_2558_ == 0)
{
v___x_2553_ = v___x_2427_;
v_isShared_2554_ = v_isSharedCheck_2558_;
goto v_resetjp_2552_;
}
else
{
lean_inc(v_a_2551_);
lean_dec(v___x_2427_);
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
v___jp_2410_:
{
size_t v_sz_2423_; lean_object* v___x_2424_; lean_object* v___f_2425_; lean_object* v___x_2426_; 
v_sz_2423_ = lean_array_size(v___y_2417_);
v___x_2424_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__3(v_sz_2423_, v___y_2416_, v___y_2417_);
v___f_2425_ = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4___lam__0___boxed), 14, 9);
lean_closure_set(v___f_2425_, 0, v___y_2415_);
lean_closure_set(v___f_2425_, 1, v___x_2409_);
lean_closure_set(v___f_2425_, 2, v___y_2412_);
lean_closure_set(v___f_2425_, 3, v_a_2386_);
lean_closure_set(v___f_2425_, 4, v___x_2424_);
lean_closure_set(v___f_2425_, 5, v_givenNames_2390_);
lean_closure_set(v___f_2425_, 6, v___y_2414_);
lean_closure_set(v___f_2425_, 7, v___y_2413_);
lean_closure_set(v___f_2425_, 8, v___y_2411_);
v___x_2426_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___redArg(v___y_2418_, v___f_2425_, v___y_2419_, v___y_2420_, v___y_2421_, v___y_2422_);
return v___x_2426_;
}
}
else
{
lean_object* v_a_2559_; lean_object* v___x_2561_; uint8_t v_isShared_2562_; uint8_t v_isSharedCheck_2566_; 
lean_dec(v_recursorName_2391_);
lean_dec_ref(v_givenNames_2390_);
lean_dec(v_majorFVarId_2389_);
lean_dec(v_mvarId_2388_);
lean_dec_ref(v_val_2387_);
lean_dec_ref(v_a_2386_);
v_a_2559_ = lean_ctor_get(v___x_2408_, 0);
v_isSharedCheck_2566_ = !lean_is_exclusive(v___x_2408_);
if (v_isSharedCheck_2566_ == 0)
{
v___x_2561_ = v___x_2408_;
v_isShared_2562_ = v_isSharedCheck_2566_;
goto v_resetjp_2560_;
}
else
{
lean_inc(v_a_2559_);
lean_dec(v___x_2408_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___boxed(lean_object* v_a_2567_, lean_object* v_val_2568_, lean_object* v_mvarId_2569_, lean_object* v_majorFVarId_2570_, lean_object* v_givenNames_2571_, lean_object* v_recursorName_2572_, lean_object* v_x_2573_, lean_object* v_x_2574_, lean_object* v_x_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_){
_start:
{
lean_object* v_res_2581_; 
v_res_2581_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4(v_a_2567_, v_val_2568_, v_mvarId_2569_, v_majorFVarId_2570_, v_givenNames_2571_, v_recursorName_2572_, v_x_2573_, v_x_2574_, v_x_2575_, v___y_2576_, v___y_2577_, v___y_2578_, v___y_2579_);
lean_dec(v___y_2579_);
lean_dec_ref(v___y_2578_);
lean_dec(v___y_2577_);
lean_dec_ref(v___y_2576_);
return v_res_2581_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4(lean_object* v_val_2582_, lean_object* v_mvarId_2583_, lean_object* v_a_2584_, lean_object* v_majorFVarId_2585_, lean_object* v_givenNames_2586_, lean_object* v_recursorName_2587_, lean_object* v_x_2588_, lean_object* v_x_2589_, lean_object* v_x_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_){
_start:
{
if (lean_obj_tag(v_x_2588_) == 5)
{
lean_object* v_fn_2596_; lean_object* v_arg_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; 
v_fn_2596_ = lean_ctor_get(v_x_2588_, 0);
lean_inc_ref(v_fn_2596_);
v_arg_2597_ = lean_ctor_get(v_x_2588_, 1);
lean_inc_ref(v_arg_2597_);
lean_dec_ref_known(v_x_2588_, 2);
v___x_2598_ = lean_array_set(v_x_2589_, v_x_2590_, v_arg_2597_);
v___x_2599_ = lean_unsigned_to_nat(1u);
v___x_2600_ = lean_nat_sub(v_x_2590_, v___x_2599_);
v___x_2601_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4(v_a_2584_, v_val_2582_, v_mvarId_2583_, v_majorFVarId_2585_, v_givenNames_2586_, v_recursorName_2587_, v_fn_2596_, v___x_2598_, v___x_2600_, v___y_2591_, v___y_2592_, v___y_2593_, v___y_2594_);
return v___x_2601_;
}
else
{
uint8_t v_depElim_2602_; lean_object* v_paramsPos_2603_; lean_object* v___x_2604_; 
lean_dec_ref(v_x_2588_);
v_depElim_2602_ = lean_ctor_get_uint8(v_a_2584_, sizeof(void*)*8);
v_paramsPos_2603_ = lean_ctor_get(v_a_2584_, 5);
lean_inc(v_paramsPos_2603_);
lean_inc(v_mvarId_2583_);
lean_inc_ref(v_val_2582_);
v___x_2604_ = l_List_forM___at___00Lean_MVarId_induction_spec__0(v_x_2589_, v_val_2582_, v_mvarId_2583_, v_paramsPos_2603_, v___y_2591_, v___y_2592_, v___y_2593_, v___y_2594_);
lean_dec_ref(v_x_2589_);
if (lean_obj_tag(v___x_2604_) == 0)
{
lean_object* v___x_2605_; lean_object* v___y_2607_; lean_object* v___y_2608_; lean_object* v___y_2609_; lean_object* v___y_2610_; lean_object* v___y_2611_; lean_object* v___y_2612_; size_t v___y_2613_; lean_object* v___y_2614_; lean_object* v___y_2615_; lean_object* v___y_2616_; lean_object* v___y_2617_; lean_object* v___y_2618_; lean_object* v___x_2623_; 
lean_dec_ref_known(v___x_2604_, 1);
v___x_2605_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1));
lean_inc_ref(v_a_2584_);
lean_inc(v_mvarId_2583_);
v___x_2623_ = l_Lean_Meta_getMajorTypeIndices(v_mvarId_2583_, v___x_2605_, v_a_2584_, v_val_2582_, v___y_2591_, v___y_2592_, v___y_2593_, v___y_2594_);
if (lean_obj_tag(v___x_2623_) == 0)
{
lean_object* v_a_2624_; lean_object* v___x_2625_; 
v_a_2624_ = lean_ctor_get(v___x_2623_, 0);
lean_inc(v_a_2624_);
lean_dec_ref_known(v___x_2623_, 1);
lean_inc(v_mvarId_2583_);
v___x_2625_ = l_Lean_MVarId_getType(v_mvarId_2583_, v___y_2591_, v___y_2592_, v___y_2593_, v___y_2594_);
if (lean_obj_tag(v___x_2625_) == 0)
{
lean_object* v_a_2626_; lean_object* v_cls_2627_; lean_object* v___y_2629_; lean_object* v___y_2630_; lean_object* v___y_2631_; lean_object* v___y_2632_; 
v_a_2626_ = lean_ctor_get(v___x_2625_, 0);
lean_inc(v_a_2626_);
lean_dec_ref_known(v___x_2625_, 1);
v_cls_2627_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__2));
if (v_depElim_2602_ == 0)
{
lean_object* v___x_2715_; lean_object* v_a_2716_; lean_object* v___x_2718_; uint8_t v_isShared_2719_; uint8_t v_isSharedCheck_2738_; 
lean_inc(v_majorFVarId_2585_);
v___x_2715_ = l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2___redArg(v_a_2626_, v_majorFVarId_2585_, v___y_2592_);
v_a_2716_ = lean_ctor_get(v___x_2715_, 0);
v_isSharedCheck_2738_ = !lean_is_exclusive(v___x_2715_);
if (v_isSharedCheck_2738_ == 0)
{
v___x_2718_ = v___x_2715_;
v_isShared_2719_ = v_isSharedCheck_2738_;
goto v_resetjp_2717_;
}
else
{
lean_inc(v_a_2716_);
lean_dec(v___x_2715_);
v___x_2718_ = lean_box(0);
v_isShared_2719_ = v_isSharedCheck_2738_;
goto v_resetjp_2717_;
}
v_resetjp_2717_:
{
uint8_t v___x_2720_; 
v___x_2720_ = lean_unbox(v_a_2716_);
lean_dec(v_a_2716_);
if (v___x_2720_ == 0)
{
lean_del_object(v___x_2718_);
lean_dec(v_recursorName_2587_);
v___y_2629_ = v___y_2591_;
v___y_2630_ = v___y_2592_;
v___y_2631_ = v___y_2593_;
v___y_2632_ = v___y_2594_;
goto v___jp_2628_;
}
else
{
lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2727_; 
v___x_2721_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__3, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__3);
v___x_2722_ = l_Lean_MessageData_ofName(v_recursorName_2587_);
v___x_2723_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2723_, 0, v___x_2721_);
lean_ctor_set(v___x_2723_, 1, v___x_2722_);
v___x_2724_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__5, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__5_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__5);
v___x_2725_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2725_, 0, v___x_2723_);
lean_ctor_set(v___x_2725_, 1, v___x_2724_);
if (v_isShared_2719_ == 0)
{
lean_ctor_set_tag(v___x_2718_, 1);
lean_ctor_set(v___x_2718_, 0, v___x_2725_);
v___x_2727_ = v___x_2718_;
goto v_reusejp_2726_;
}
else
{
lean_object* v_reuseFailAlloc_2737_; 
v_reuseFailAlloc_2737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2737_, 0, v___x_2725_);
v___x_2727_ = v_reuseFailAlloc_2737_;
goto v_reusejp_2726_;
}
v_reusejp_2726_:
{
lean_object* v___x_2728_; 
lean_inc(v_mvarId_2583_);
v___x_2728_ = l_Lean_Meta_throwTacticEx___redArg(v___x_2605_, v_mvarId_2583_, v___x_2727_, v___y_2591_, v___y_2592_, v___y_2593_, v___y_2594_);
if (lean_obj_tag(v___x_2728_) == 0)
{
lean_dec_ref_known(v___x_2728_, 1);
v___y_2629_ = v___y_2591_;
v___y_2630_ = v___y_2592_;
v___y_2631_ = v___y_2593_;
v___y_2632_ = v___y_2594_;
goto v___jp_2628_;
}
else
{
lean_object* v_a_2729_; lean_object* v___x_2731_; uint8_t v_isShared_2732_; uint8_t v_isSharedCheck_2736_; 
lean_dec(v_a_2624_);
lean_dec_ref(v_givenNames_2586_);
lean_dec(v_majorFVarId_2585_);
lean_dec_ref(v_a_2584_);
lean_dec(v_mvarId_2583_);
v_a_2729_ = lean_ctor_get(v___x_2728_, 0);
v_isSharedCheck_2736_ = !lean_is_exclusive(v___x_2728_);
if (v_isSharedCheck_2736_ == 0)
{
v___x_2731_ = v___x_2728_;
v_isShared_2732_ = v_isSharedCheck_2736_;
goto v_resetjp_2730_;
}
else
{
lean_inc(v_a_2729_);
lean_dec(v___x_2728_);
v___x_2731_ = lean_box(0);
v_isShared_2732_ = v_isSharedCheck_2736_;
goto v_resetjp_2730_;
}
v_resetjp_2730_:
{
lean_object* v___x_2734_; 
if (v_isShared_2732_ == 0)
{
v___x_2734_ = v___x_2731_;
goto v_reusejp_2733_;
}
else
{
lean_object* v_reuseFailAlloc_2735_; 
v_reuseFailAlloc_2735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2735_, 0, v_a_2729_);
v___x_2734_ = v_reuseFailAlloc_2735_;
goto v_reusejp_2733_;
}
v_reusejp_2733_:
{
return v___x_2734_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_2626_);
lean_dec(v_recursorName_2587_);
v___y_2629_ = v___y_2591_;
v___y_2630_ = v___y_2592_;
v___y_2631_ = v___y_2593_;
v___y_2632_ = v___y_2594_;
goto v___jp_2628_;
}
v___jp_2628_:
{
size_t v_sz_2633_; size_t v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; uint8_t v___x_2637_; uint8_t v___x_2638_; lean_object* v___x_2639_; 
v_sz_2633_ = lean_array_size(v_a_2624_);
v___x_2634_ = ((size_t)0ULL);
lean_inc(v_a_2624_);
v___x_2635_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_induction_spec__1(v_sz_2633_, v___x_2634_, v_a_2624_);
lean_inc(v_majorFVarId_2585_);
v___x_2636_ = lean_array_push(v___x_2635_, v_majorFVarId_2585_);
v___x_2637_ = 1;
v___x_2638_ = 0;
v___x_2639_ = l_Lean_MVarId_revert(v_mvarId_2583_, v___x_2636_, v___x_2637_, v___x_2638_, v___y_2629_, v___y_2630_, v___y_2631_, v___y_2632_);
if (lean_obj_tag(v___x_2639_) == 0)
{
lean_object* v_a_2640_; lean_object* v_fst_2641_; lean_object* v_snd_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; 
v_a_2640_ = lean_ctor_get(v___x_2639_, 0);
lean_inc(v_a_2640_);
lean_dec_ref_known(v___x_2639_, 1);
v_fst_2641_ = lean_ctor_get(v_a_2640_, 0);
lean_inc(v_fst_2641_);
v_snd_2642_ = lean_ctor_get(v_a_2640_, 1);
lean_inc(v_snd_2642_);
lean_dec(v_a_2640_);
v___x_2643_ = lean_array_get_size(v_a_2624_);
v___x_2644_ = lean_box(0);
v___x_2645_ = l_Lean_Meta_introNCore(v_snd_2642_, v___x_2643_, v___x_2644_, v___x_2638_, v___x_2637_, v___y_2629_, v___y_2630_, v___y_2631_, v___y_2632_);
if (lean_obj_tag(v___x_2645_) == 0)
{
lean_object* v_a_2646_; lean_object* v_fst_2647_; lean_object* v_snd_2648_; lean_object* v___x_2649_; 
v_a_2646_ = lean_ctor_get(v___x_2645_, 0);
lean_inc(v_a_2646_);
lean_dec_ref_known(v___x_2645_, 1);
v_fst_2647_ = lean_ctor_get(v_a_2646_, 0);
lean_inc(v_fst_2647_);
v_snd_2648_ = lean_ctor_get(v_a_2646_, 1);
lean_inc(v_snd_2648_);
lean_dec(v_a_2646_);
v___x_2649_ = l_Lean_Meta_intro1Core(v_snd_2648_, v___x_2637_, v___y_2629_, v___y_2630_, v___y_2631_, v___y_2632_);
if (lean_obj_tag(v___x_2649_) == 0)
{
lean_object* v_a_2650_; lean_object* v_fst_2651_; lean_object* v_snd_2652_; lean_object* v___x_2654_; uint8_t v_isShared_2655_; uint8_t v_isSharedCheck_2690_; 
v_a_2650_ = lean_ctor_get(v___x_2649_, 0);
lean_inc(v_a_2650_);
lean_dec_ref_known(v___x_2649_, 1);
v_fst_2651_ = lean_ctor_get(v_a_2650_, 0);
v_snd_2652_ = lean_ctor_get(v_a_2650_, 1);
v_isSharedCheck_2690_ = !lean_is_exclusive(v_a_2650_);
if (v_isSharedCheck_2690_ == 0)
{
v___x_2654_ = v_a_2650_;
v_isShared_2655_ = v_isSharedCheck_2690_;
goto v_resetjp_2653_;
}
else
{
lean_inc(v_snd_2652_);
lean_inc(v_fst_2651_);
lean_dec(v_a_2650_);
v___x_2654_ = lean_box(0);
v_isShared_2655_ = v_isSharedCheck_2690_;
goto v_resetjp_2653_;
}
v_resetjp_2653_:
{
lean_object* v___x_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_2661_; 
v___x_2656_ = lean_box(0);
lean_inc(v_fst_2651_);
v___x_2657_ = l_Lean_mkFVar(v_fst_2651_);
lean_inc_ref(v___x_2657_);
v___x_2658_ = l_Lean_Meta_FVarSubst_insert(v___x_2656_, v_majorFVarId_2585_, v___x_2657_);
v___x_2659_ = lean_unsigned_to_nat(0u);
if (v_isShared_2655_ == 0)
{
lean_ctor_set(v___x_2654_, 1, v___x_2659_);
lean_ctor_set(v___x_2654_, 0, v___x_2658_);
v___x_2661_ = v___x_2654_;
goto v_reusejp_2660_;
}
else
{
lean_object* v_reuseFailAlloc_2689_; 
v_reuseFailAlloc_2689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2689_, 0, v___x_2658_);
lean_ctor_set(v_reuseFailAlloc_2689_, 1, v___x_2659_);
v___x_2661_ = v_reuseFailAlloc_2689_;
goto v_reusejp_2660_;
}
v_reusejp_2660_:
{
lean_object* v___x_2662_; lean_object* v_options_2663_; uint8_t v_hasTrace_2664_; 
v___x_2662_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_induction_spec__2(v_fst_2647_, v_a_2624_, v_sz_2633_, v___x_2634_, v___x_2661_);
lean_dec(v_a_2624_);
v_options_2663_ = lean_ctor_get(v___y_2631_, 2);
v_hasTrace_2664_ = lean_ctor_get_uint8(v_options_2663_, sizeof(void*)*1);
if (v_hasTrace_2664_ == 0)
{
lean_object* v_fst_2665_; 
v_fst_2665_ = lean_ctor_get(v___x_2662_, 0);
lean_inc(v_fst_2665_);
lean_dec_ref(v___x_2662_);
lean_inc(v_snd_2652_);
v___y_2607_ = v_fst_2665_;
v___y_2608_ = v_fst_2651_;
v___y_2609_ = v___x_2657_;
v___y_2610_ = v_fst_2641_;
v___y_2611_ = v_snd_2652_;
v___y_2612_ = v_fst_2647_;
v___y_2613_ = v___x_2634_;
v___y_2614_ = v_snd_2652_;
v___y_2615_ = v___y_2629_;
v___y_2616_ = v___y_2630_;
v___y_2617_ = v___y_2631_;
v___y_2618_ = v___y_2632_;
goto v___jp_2606_;
}
else
{
lean_object* v_fst_2666_; lean_object* v___x_2668_; uint8_t v_isShared_2669_; uint8_t v_isSharedCheck_2687_; 
v_fst_2666_ = lean_ctor_get(v___x_2662_, 0);
v_isSharedCheck_2687_ = !lean_is_exclusive(v___x_2662_);
if (v_isSharedCheck_2687_ == 0)
{
lean_object* v_unused_2688_; 
v_unused_2688_ = lean_ctor_get(v___x_2662_, 1);
lean_dec(v_unused_2688_);
v___x_2668_ = v___x_2662_;
v_isShared_2669_ = v_isSharedCheck_2687_;
goto v_resetjp_2667_;
}
else
{
lean_inc(v_fst_2666_);
lean_dec(v___x_2662_);
v___x_2668_ = lean_box(0);
v_isShared_2669_ = v_isSharedCheck_2687_;
goto v_resetjp_2667_;
}
v_resetjp_2667_:
{
lean_object* v_inheritedTraceOptions_2670_; lean_object* v___x_2671_; uint8_t v___x_2672_; 
v_inheritedTraceOptions_2670_ = lean_ctor_get(v___y_2631_, 13);
v___x_2671_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5_once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5);
v___x_2672_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2670_, v_options_2663_, v___x_2671_);
if (v___x_2672_ == 0)
{
lean_del_object(v___x_2668_);
lean_inc(v_snd_2652_);
v___y_2607_ = v_fst_2666_;
v___y_2608_ = v_fst_2651_;
v___y_2609_ = v___x_2657_;
v___y_2610_ = v_fst_2641_;
v___y_2611_ = v_snd_2652_;
v___y_2612_ = v_fst_2647_;
v___y_2613_ = v___x_2634_;
v___y_2614_ = v_snd_2652_;
v___y_2615_ = v___y_2629_;
v___y_2616_ = v___y_2630_;
v___y_2617_ = v___y_2631_;
v___y_2618_ = v___y_2632_;
goto v___jp_2606_;
}
else
{
lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2676_; 
v___x_2673_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__1);
lean_inc(v_snd_2652_);
v___x_2674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2674_, 0, v_snd_2652_);
if (v_isShared_2669_ == 0)
{
lean_ctor_set_tag(v___x_2668_, 7);
lean_ctor_set(v___x_2668_, 1, v___x_2674_);
lean_ctor_set(v___x_2668_, 0, v___x_2673_);
v___x_2676_ = v___x_2668_;
goto v_reusejp_2675_;
}
else
{
lean_object* v_reuseFailAlloc_2686_; 
v_reuseFailAlloc_2686_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2686_, 0, v___x_2673_);
lean_ctor_set(v_reuseFailAlloc_2686_, 1, v___x_2674_);
v___x_2676_ = v_reuseFailAlloc_2686_;
goto v_reusejp_2675_;
}
v_reusejp_2675_:
{
lean_object* v___x_2677_; 
v___x_2677_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1(v_cls_2627_, v___x_2676_, v___y_2629_, v___y_2630_, v___y_2631_, v___y_2632_);
if (lean_obj_tag(v___x_2677_) == 0)
{
lean_dec_ref_known(v___x_2677_, 1);
lean_inc(v_snd_2652_);
v___y_2607_ = v_fst_2666_;
v___y_2608_ = v_fst_2651_;
v___y_2609_ = v___x_2657_;
v___y_2610_ = v_fst_2641_;
v___y_2611_ = v_snd_2652_;
v___y_2612_ = v_fst_2647_;
v___y_2613_ = v___x_2634_;
v___y_2614_ = v_snd_2652_;
v___y_2615_ = v___y_2629_;
v___y_2616_ = v___y_2630_;
v___y_2617_ = v___y_2631_;
v___y_2618_ = v___y_2632_;
goto v___jp_2606_;
}
else
{
lean_object* v_a_2678_; lean_object* v___x_2680_; uint8_t v_isShared_2681_; uint8_t v_isSharedCheck_2685_; 
lean_dec(v_fst_2666_);
lean_dec_ref(v___x_2657_);
lean_dec(v_snd_2652_);
lean_dec(v_fst_2651_);
lean_dec(v_fst_2647_);
lean_dec(v_fst_2641_);
lean_dec_ref(v_givenNames_2586_);
lean_dec_ref(v_a_2584_);
v_a_2678_ = lean_ctor_get(v___x_2677_, 0);
v_isSharedCheck_2685_ = !lean_is_exclusive(v___x_2677_);
if (v_isSharedCheck_2685_ == 0)
{
v___x_2680_ = v___x_2677_;
v_isShared_2681_ = v_isSharedCheck_2685_;
goto v_resetjp_2679_;
}
else
{
lean_inc(v_a_2678_);
lean_dec(v___x_2677_);
v___x_2680_ = lean_box(0);
v_isShared_2681_ = v_isSharedCheck_2685_;
goto v_resetjp_2679_;
}
v_resetjp_2679_:
{
lean_object* v___x_2683_; 
if (v_isShared_2681_ == 0)
{
v___x_2683_ = v___x_2680_;
goto v_reusejp_2682_;
}
else
{
lean_object* v_reuseFailAlloc_2684_; 
v_reuseFailAlloc_2684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2684_, 0, v_a_2678_);
v___x_2683_ = v_reuseFailAlloc_2684_;
goto v_reusejp_2682_;
}
v_reusejp_2682_:
{
return v___x_2683_;
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
lean_object* v_a_2691_; lean_object* v___x_2693_; uint8_t v_isShared_2694_; uint8_t v_isSharedCheck_2698_; 
lean_dec(v_fst_2647_);
lean_dec(v_fst_2641_);
lean_dec(v_a_2624_);
lean_dec_ref(v_givenNames_2586_);
lean_dec(v_majorFVarId_2585_);
lean_dec_ref(v_a_2584_);
v_a_2691_ = lean_ctor_get(v___x_2649_, 0);
v_isSharedCheck_2698_ = !lean_is_exclusive(v___x_2649_);
if (v_isSharedCheck_2698_ == 0)
{
v___x_2693_ = v___x_2649_;
v_isShared_2694_ = v_isSharedCheck_2698_;
goto v_resetjp_2692_;
}
else
{
lean_inc(v_a_2691_);
lean_dec(v___x_2649_);
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
else
{
lean_object* v_a_2699_; lean_object* v___x_2701_; uint8_t v_isShared_2702_; uint8_t v_isSharedCheck_2706_; 
lean_dec(v_fst_2641_);
lean_dec(v_a_2624_);
lean_dec_ref(v_givenNames_2586_);
lean_dec(v_majorFVarId_2585_);
lean_dec_ref(v_a_2584_);
v_a_2699_ = lean_ctor_get(v___x_2645_, 0);
v_isSharedCheck_2706_ = !lean_is_exclusive(v___x_2645_);
if (v_isSharedCheck_2706_ == 0)
{
v___x_2701_ = v___x_2645_;
v_isShared_2702_ = v_isSharedCheck_2706_;
goto v_resetjp_2700_;
}
else
{
lean_inc(v_a_2699_);
lean_dec(v___x_2645_);
v___x_2701_ = lean_box(0);
v_isShared_2702_ = v_isSharedCheck_2706_;
goto v_resetjp_2700_;
}
v_resetjp_2700_:
{
lean_object* v___x_2704_; 
if (v_isShared_2702_ == 0)
{
v___x_2704_ = v___x_2701_;
goto v_reusejp_2703_;
}
else
{
lean_object* v_reuseFailAlloc_2705_; 
v_reuseFailAlloc_2705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2705_, 0, v_a_2699_);
v___x_2704_ = v_reuseFailAlloc_2705_;
goto v_reusejp_2703_;
}
v_reusejp_2703_:
{
return v___x_2704_;
}
}
}
}
else
{
lean_object* v_a_2707_; lean_object* v___x_2709_; uint8_t v_isShared_2710_; uint8_t v_isSharedCheck_2714_; 
lean_dec(v_a_2624_);
lean_dec_ref(v_givenNames_2586_);
lean_dec(v_majorFVarId_2585_);
lean_dec_ref(v_a_2584_);
v_a_2707_ = lean_ctor_get(v___x_2639_, 0);
v_isSharedCheck_2714_ = !lean_is_exclusive(v___x_2639_);
if (v_isSharedCheck_2714_ == 0)
{
v___x_2709_ = v___x_2639_;
v_isShared_2710_ = v_isSharedCheck_2714_;
goto v_resetjp_2708_;
}
else
{
lean_inc(v_a_2707_);
lean_dec(v___x_2639_);
v___x_2709_ = lean_box(0);
v_isShared_2710_ = v_isSharedCheck_2714_;
goto v_resetjp_2708_;
}
v_resetjp_2708_:
{
lean_object* v___x_2712_; 
if (v_isShared_2710_ == 0)
{
v___x_2712_ = v___x_2709_;
goto v_reusejp_2711_;
}
else
{
lean_object* v_reuseFailAlloc_2713_; 
v_reuseFailAlloc_2713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2713_, 0, v_a_2707_);
v___x_2712_ = v_reuseFailAlloc_2713_;
goto v_reusejp_2711_;
}
v_reusejp_2711_:
{
return v___x_2712_;
}
}
}
}
}
else
{
lean_object* v_a_2739_; lean_object* v___x_2741_; uint8_t v_isShared_2742_; uint8_t v_isSharedCheck_2746_; 
lean_dec(v_a_2624_);
lean_dec(v_recursorName_2587_);
lean_dec_ref(v_givenNames_2586_);
lean_dec(v_majorFVarId_2585_);
lean_dec_ref(v_a_2584_);
lean_dec(v_mvarId_2583_);
v_a_2739_ = lean_ctor_get(v___x_2625_, 0);
v_isSharedCheck_2746_ = !lean_is_exclusive(v___x_2625_);
if (v_isSharedCheck_2746_ == 0)
{
v___x_2741_ = v___x_2625_;
v_isShared_2742_ = v_isSharedCheck_2746_;
goto v_resetjp_2740_;
}
else
{
lean_inc(v_a_2739_);
lean_dec(v___x_2625_);
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
lean_dec(v_recursorName_2587_);
lean_dec_ref(v_givenNames_2586_);
lean_dec(v_majorFVarId_2585_);
lean_dec_ref(v_a_2584_);
lean_dec(v_mvarId_2583_);
v_a_2747_ = lean_ctor_get(v___x_2623_, 0);
v_isSharedCheck_2754_ = !lean_is_exclusive(v___x_2623_);
if (v_isSharedCheck_2754_ == 0)
{
v___x_2749_ = v___x_2623_;
v_isShared_2750_ = v_isSharedCheck_2754_;
goto v_resetjp_2748_;
}
else
{
lean_inc(v_a_2747_);
lean_dec(v___x_2623_);
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
v___jp_2606_:
{
size_t v_sz_2619_; lean_object* v___x_2620_; lean_object* v___f_2621_; lean_object* v___x_2622_; 
v_sz_2619_ = lean_array_size(v___y_2612_);
v___x_2620_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__3(v_sz_2619_, v___y_2613_, v___y_2612_);
v___f_2621_ = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4___lam__0___boxed), 14, 9);
lean_closure_set(v___f_2621_, 0, v___y_2611_);
lean_closure_set(v___f_2621_, 1, v___x_2605_);
lean_closure_set(v___f_2621_, 2, v___y_2608_);
lean_closure_set(v___f_2621_, 3, v_a_2584_);
lean_closure_set(v___f_2621_, 4, v___x_2620_);
lean_closure_set(v___f_2621_, 5, v_givenNames_2586_);
lean_closure_set(v___f_2621_, 6, v___y_2610_);
lean_closure_set(v___f_2621_, 7, v___y_2609_);
lean_closure_set(v___f_2621_, 8, v___y_2607_);
v___x_2622_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___redArg(v___y_2614_, v___f_2621_, v___y_2615_, v___y_2616_, v___y_2617_, v___y_2618_);
return v___x_2622_;
}
}
else
{
lean_object* v_a_2755_; lean_object* v___x_2757_; uint8_t v_isShared_2758_; uint8_t v_isSharedCheck_2762_; 
lean_dec(v_recursorName_2587_);
lean_dec_ref(v_givenNames_2586_);
lean_dec(v_majorFVarId_2585_);
lean_dec_ref(v_a_2584_);
lean_dec(v_mvarId_2583_);
lean_dec_ref(v_val_2582_);
v_a_2755_ = lean_ctor_get(v___x_2604_, 0);
v_isSharedCheck_2762_ = !lean_is_exclusive(v___x_2604_);
if (v_isSharedCheck_2762_ == 0)
{
v___x_2757_ = v___x_2604_;
v_isShared_2758_ = v_isSharedCheck_2762_;
goto v_resetjp_2756_;
}
else
{
lean_inc(v_a_2755_);
lean_dec(v___x_2604_);
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
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4___boxed(lean_object* v_val_2763_, lean_object* v_mvarId_2764_, lean_object* v_a_2765_, lean_object* v_majorFVarId_2766_, lean_object* v_givenNames_2767_, lean_object* v_recursorName_2768_, lean_object* v_x_2769_, lean_object* v_x_2770_, lean_object* v_x_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_){
_start:
{
lean_object* v_res_2777_; 
v_res_2777_ = l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4(v_val_2763_, v_mvarId_2764_, v_a_2765_, v_majorFVarId_2766_, v_givenNames_2767_, v_recursorName_2768_, v_x_2769_, v_x_2770_, v_x_2771_, v___y_2772_, v___y_2773_, v___y_2774_, v___y_2775_);
lean_dec(v___y_2775_);
lean_dec_ref(v___y_2774_);
lean_dec(v___y_2773_);
lean_dec_ref(v___y_2772_);
lean_dec(v_x_2771_);
return v_res_2777_;
}
}
static lean_object* _init_l_Lean_MVarId_induction___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2779_; lean_object* v___x_2780_; 
v___x_2779_ = ((lean_object*)(l_Lean_MVarId_induction___lam__0___closed__0));
v___x_2780_ = l_Lean_stringToMessageData(v___x_2779_);
return v___x_2780_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_induction___lam__0(lean_object* v___x_2781_, lean_object* v_mvarId_2782_, lean_object* v_majorFVarId_2783_, lean_object* v_recursorName_2784_, lean_object* v_givenNames_2785_, lean_object* v_cls_2786_, lean_object* v___y_2787_, lean_object* v___y_2788_, lean_object* v___y_2789_, lean_object* v___y_2790_){
_start:
{
lean_object* v___y_2793_; lean_object* v___y_2794_; lean_object* v___y_2795_; lean_object* v___y_2796_; lean_object* v_options_2848_; uint8_t v_hasTrace_2849_; 
v_options_2848_ = lean_ctor_get(v___y_2789_, 2);
v_hasTrace_2849_ = lean_ctor_get_uint8(v_options_2848_, sizeof(void*)*1);
if (v_hasTrace_2849_ == 0)
{
lean_dec(v_cls_2786_);
v___y_2793_ = v___y_2787_;
v___y_2794_ = v___y_2788_;
v___y_2795_ = v___y_2789_;
v___y_2796_ = v___y_2790_;
goto v___jp_2792_;
}
else
{
lean_object* v_inheritedTraceOptions_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; uint8_t v___x_2853_; 
v_inheritedTraceOptions_2850_ = lean_ctor_get(v___y_2789_, 13);
v___x_2851_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__4));
lean_inc(v_cls_2786_);
v___x_2852_ = l_Lean_Name_append(v___x_2851_, v_cls_2786_);
v___x_2853_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2850_, v_options_2848_, v___x_2852_);
lean_dec(v___x_2852_);
if (v___x_2853_ == 0)
{
lean_dec(v_cls_2786_);
v___y_2793_ = v___y_2787_;
v___y_2794_ = v___y_2788_;
v___y_2795_ = v___y_2789_;
v___y_2796_ = v___y_2790_;
goto v___jp_2792_;
}
else
{
lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; 
v___x_2854_ = lean_obj_once(&l_Lean_MVarId_induction___lam__0___closed__1, &l_Lean_MVarId_induction___lam__0___closed__1_once, _init_l_Lean_MVarId_induction___lam__0___closed__1);
lean_inc(v_mvarId_2782_);
v___x_2855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2855_, 0, v_mvarId_2782_);
v___x_2856_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2856_, 0, v___x_2854_);
lean_ctor_set(v___x_2856_, 1, v___x_2855_);
v___x_2857_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1(v_cls_2786_, v___x_2856_, v___y_2787_, v___y_2788_, v___y_2789_, v___y_2790_);
if (lean_obj_tag(v___x_2857_) == 0)
{
lean_dec_ref_known(v___x_2857_, 1);
v___y_2793_ = v___y_2787_;
v___y_2794_ = v___y_2788_;
v___y_2795_ = v___y_2789_;
v___y_2796_ = v___y_2790_;
goto v___jp_2792_;
}
else
{
lean_object* v_a_2858_; lean_object* v___x_2860_; uint8_t v_isShared_2861_; uint8_t v_isSharedCheck_2865_; 
lean_dec_ref(v_givenNames_2785_);
lean_dec(v_recursorName_2784_);
lean_dec(v_majorFVarId_2783_);
lean_dec(v_mvarId_2782_);
lean_dec_ref(v___x_2781_);
v_a_2858_ = lean_ctor_get(v___x_2857_, 0);
v_isSharedCheck_2865_ = !lean_is_exclusive(v___x_2857_);
if (v_isSharedCheck_2865_ == 0)
{
v___x_2860_ = v___x_2857_;
v_isShared_2861_ = v_isSharedCheck_2865_;
goto v_resetjp_2859_;
}
else
{
lean_inc(v_a_2858_);
lean_dec(v___x_2857_);
v___x_2860_ = lean_box(0);
v_isShared_2861_ = v_isSharedCheck_2865_;
goto v_resetjp_2859_;
}
v_resetjp_2859_:
{
lean_object* v___x_2863_; 
if (v_isShared_2861_ == 0)
{
v___x_2863_ = v___x_2860_;
goto v_reusejp_2862_;
}
else
{
lean_object* v_reuseFailAlloc_2864_; 
v_reuseFailAlloc_2864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2864_, 0, v_a_2858_);
v___x_2863_ = v_reuseFailAlloc_2864_;
goto v_reusejp_2862_;
}
v_reusejp_2862_:
{
return v___x_2863_;
}
}
}
}
}
v___jp_2792_:
{
lean_object* v___x_2797_; lean_object* v___x_2798_; 
v___x_2797_ = l_Lean_Name_mkStr1(v___x_2781_);
lean_inc(v___x_2797_);
lean_inc(v_mvarId_2782_);
v___x_2798_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_2782_, v___x_2797_, v___y_2793_, v___y_2794_, v___y_2795_, v___y_2796_);
if (lean_obj_tag(v___x_2798_) == 0)
{
lean_object* v___x_2799_; 
lean_dec_ref_known(v___x_2798_, 1);
lean_inc(v_majorFVarId_2783_);
v___x_2799_ = l_Lean_FVarId_getDecl___redArg(v_majorFVarId_2783_, v___y_2793_, v___y_2795_, v___y_2796_);
if (lean_obj_tag(v___x_2799_) == 0)
{
lean_object* v_a_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; 
v_a_2800_ = lean_ctor_get(v___x_2799_, 0);
lean_inc(v_a_2800_);
lean_dec_ref_known(v___x_2799_, 1);
v___x_2801_ = lean_box(0);
lean_inc(v_recursorName_2784_);
v___x_2802_ = l_Lean_Meta_mkRecursorInfo(v_recursorName_2784_, v___x_2801_, v___y_2793_, v___y_2794_, v___y_2795_, v___y_2796_);
if (lean_obj_tag(v___x_2802_) == 0)
{
lean_object* v_a_2803_; lean_object* v_typeName_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; 
v_a_2803_ = lean_ctor_get(v___x_2802_, 0);
lean_inc(v_a_2803_);
lean_dec_ref_known(v___x_2802_, 1);
v_typeName_2804_ = lean_ctor_get(v_a_2803_, 1);
v___x_2805_ = l_Lean_LocalDecl_type(v_a_2800_);
lean_dec(v_a_2800_);
lean_inc_ref(v___x_2805_);
v___x_2806_ = l_Lean_Meta_whnfUntil(v___x_2805_, v_typeName_2804_, v___y_2793_, v___y_2794_, v___y_2795_, v___y_2796_);
if (lean_obj_tag(v___x_2806_) == 0)
{
lean_object* v_a_2807_; 
v_a_2807_ = lean_ctor_get(v___x_2806_, 0);
lean_inc(v_a_2807_);
lean_dec_ref_known(v___x_2806_, 1);
if (lean_obj_tag(v_a_2807_) == 1)
{
lean_object* v_val_2808_; lean_object* v_dummy_2809_; lean_object* v_nargs_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; 
lean_dec_ref(v___x_2805_);
lean_dec(v___x_2797_);
v_val_2808_ = lean_ctor_get(v_a_2807_, 0);
lean_inc_n(v_val_2808_, 2);
lean_dec_ref_known(v_a_2807_, 1);
v_dummy_2809_ = lean_obj_once(&l_Lean_Meta_getMajorTypeIndices___closed__0, &l_Lean_Meta_getMajorTypeIndices___closed__0_once, _init_l_Lean_Meta_getMajorTypeIndices___closed__0);
v_nargs_2810_ = l_Lean_Expr_getAppNumArgs(v_val_2808_);
lean_inc(v_nargs_2810_);
v___x_2811_ = lean_mk_array(v_nargs_2810_, v_dummy_2809_);
v___x_2812_ = lean_unsigned_to_nat(1u);
v___x_2813_ = lean_nat_sub(v_nargs_2810_, v___x_2812_);
lean_dec(v_nargs_2810_);
v___x_2814_ = l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4(v_val_2808_, v_mvarId_2782_, v_a_2803_, v_majorFVarId_2783_, v_givenNames_2785_, v_recursorName_2784_, v_val_2808_, v___x_2811_, v___x_2813_, v___y_2793_, v___y_2794_, v___y_2795_, v___y_2796_);
lean_dec(v___x_2813_);
return v___x_2814_;
}
else
{
lean_object* v___x_2815_; 
lean_dec(v_a_2807_);
lean_dec(v_a_2803_);
lean_dec_ref(v_givenNames_2785_);
lean_dec(v_recursorName_2784_);
lean_dec(v_majorFVarId_2783_);
v___x_2815_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg(v___x_2797_, v_mvarId_2782_, v___x_2805_, v___y_2793_, v___y_2794_, v___y_2795_, v___y_2796_);
return v___x_2815_;
}
}
else
{
lean_object* v_a_2816_; lean_object* v___x_2818_; uint8_t v_isShared_2819_; uint8_t v_isSharedCheck_2823_; 
lean_dec_ref(v___x_2805_);
lean_dec(v_a_2803_);
lean_dec(v___x_2797_);
lean_dec_ref(v_givenNames_2785_);
lean_dec(v_recursorName_2784_);
lean_dec(v_majorFVarId_2783_);
lean_dec(v_mvarId_2782_);
v_a_2816_ = lean_ctor_get(v___x_2806_, 0);
v_isSharedCheck_2823_ = !lean_is_exclusive(v___x_2806_);
if (v_isSharedCheck_2823_ == 0)
{
v___x_2818_ = v___x_2806_;
v_isShared_2819_ = v_isSharedCheck_2823_;
goto v_resetjp_2817_;
}
else
{
lean_inc(v_a_2816_);
lean_dec(v___x_2806_);
v___x_2818_ = lean_box(0);
v_isShared_2819_ = v_isSharedCheck_2823_;
goto v_resetjp_2817_;
}
v_resetjp_2817_:
{
lean_object* v___x_2821_; 
if (v_isShared_2819_ == 0)
{
v___x_2821_ = v___x_2818_;
goto v_reusejp_2820_;
}
else
{
lean_object* v_reuseFailAlloc_2822_; 
v_reuseFailAlloc_2822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2822_, 0, v_a_2816_);
v___x_2821_ = v_reuseFailAlloc_2822_;
goto v_reusejp_2820_;
}
v_reusejp_2820_:
{
return v___x_2821_;
}
}
}
}
else
{
lean_object* v_a_2824_; lean_object* v___x_2826_; uint8_t v_isShared_2827_; uint8_t v_isSharedCheck_2831_; 
lean_dec(v_a_2800_);
lean_dec(v___x_2797_);
lean_dec_ref(v_givenNames_2785_);
lean_dec(v_recursorName_2784_);
lean_dec(v_majorFVarId_2783_);
lean_dec(v_mvarId_2782_);
v_a_2824_ = lean_ctor_get(v___x_2802_, 0);
v_isSharedCheck_2831_ = !lean_is_exclusive(v___x_2802_);
if (v_isSharedCheck_2831_ == 0)
{
v___x_2826_ = v___x_2802_;
v_isShared_2827_ = v_isSharedCheck_2831_;
goto v_resetjp_2825_;
}
else
{
lean_inc(v_a_2824_);
lean_dec(v___x_2802_);
v___x_2826_ = lean_box(0);
v_isShared_2827_ = v_isSharedCheck_2831_;
goto v_resetjp_2825_;
}
v_resetjp_2825_:
{
lean_object* v___x_2829_; 
if (v_isShared_2827_ == 0)
{
v___x_2829_ = v___x_2826_;
goto v_reusejp_2828_;
}
else
{
lean_object* v_reuseFailAlloc_2830_; 
v_reuseFailAlloc_2830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2830_, 0, v_a_2824_);
v___x_2829_ = v_reuseFailAlloc_2830_;
goto v_reusejp_2828_;
}
v_reusejp_2828_:
{
return v___x_2829_;
}
}
}
}
else
{
lean_object* v_a_2832_; lean_object* v___x_2834_; uint8_t v_isShared_2835_; uint8_t v_isSharedCheck_2839_; 
lean_dec(v___x_2797_);
lean_dec_ref(v_givenNames_2785_);
lean_dec(v_recursorName_2784_);
lean_dec(v_majorFVarId_2783_);
lean_dec(v_mvarId_2782_);
v_a_2832_ = lean_ctor_get(v___x_2799_, 0);
v_isSharedCheck_2839_ = !lean_is_exclusive(v___x_2799_);
if (v_isSharedCheck_2839_ == 0)
{
v___x_2834_ = v___x_2799_;
v_isShared_2835_ = v_isSharedCheck_2839_;
goto v_resetjp_2833_;
}
else
{
lean_inc(v_a_2832_);
lean_dec(v___x_2799_);
v___x_2834_ = lean_box(0);
v_isShared_2835_ = v_isSharedCheck_2839_;
goto v_resetjp_2833_;
}
v_resetjp_2833_:
{
lean_object* v___x_2837_; 
if (v_isShared_2835_ == 0)
{
v___x_2837_ = v___x_2834_;
goto v_reusejp_2836_;
}
else
{
lean_object* v_reuseFailAlloc_2838_; 
v_reuseFailAlloc_2838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2838_, 0, v_a_2832_);
v___x_2837_ = v_reuseFailAlloc_2838_;
goto v_reusejp_2836_;
}
v_reusejp_2836_:
{
return v___x_2837_;
}
}
}
}
else
{
lean_object* v_a_2840_; lean_object* v___x_2842_; uint8_t v_isShared_2843_; uint8_t v_isSharedCheck_2847_; 
lean_dec(v___x_2797_);
lean_dec_ref(v_givenNames_2785_);
lean_dec(v_recursorName_2784_);
lean_dec(v_majorFVarId_2783_);
lean_dec(v_mvarId_2782_);
v_a_2840_ = lean_ctor_get(v___x_2798_, 0);
v_isSharedCheck_2847_ = !lean_is_exclusive(v___x_2798_);
if (v_isSharedCheck_2847_ == 0)
{
v___x_2842_ = v___x_2798_;
v_isShared_2843_ = v_isSharedCheck_2847_;
goto v_resetjp_2841_;
}
else
{
lean_inc(v_a_2840_);
lean_dec(v___x_2798_);
v___x_2842_ = lean_box(0);
v_isShared_2843_ = v_isSharedCheck_2847_;
goto v_resetjp_2841_;
}
v_resetjp_2841_:
{
lean_object* v___x_2845_; 
if (v_isShared_2843_ == 0)
{
v___x_2845_ = v___x_2842_;
goto v_reusejp_2844_;
}
else
{
lean_object* v_reuseFailAlloc_2846_; 
v_reuseFailAlloc_2846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2846_, 0, v_a_2840_);
v___x_2845_ = v_reuseFailAlloc_2846_;
goto v_reusejp_2844_;
}
v_reusejp_2844_:
{
return v___x_2845_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_induction___lam__0___boxed(lean_object* v___x_2866_, lean_object* v_mvarId_2867_, lean_object* v_majorFVarId_2868_, lean_object* v_recursorName_2869_, lean_object* v_givenNames_2870_, lean_object* v_cls_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_){
_start:
{
lean_object* v_res_2877_; 
v_res_2877_ = l_Lean_MVarId_induction___lam__0(v___x_2866_, v_mvarId_2867_, v_majorFVarId_2868_, v_recursorName_2869_, v_givenNames_2870_, v_cls_2871_, v___y_2872_, v___y_2873_, v___y_2874_, v___y_2875_);
lean_dec(v___y_2875_);
lean_dec_ref(v___y_2874_);
lean_dec(v___y_2873_);
lean_dec_ref(v___y_2872_);
return v_res_2877_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_induction(lean_object* v_mvarId_2878_, lean_object* v_majorFVarId_2879_, lean_object* v_recursorName_2880_, lean_object* v_givenNames_2881_, lean_object* v_a_2882_, lean_object* v_a_2883_, lean_object* v_a_2884_, lean_object* v_a_2885_){
_start:
{
lean_object* v___x_2887_; lean_object* v_cls_2888_; lean_object* v___f_2889_; lean_object* v___x_2890_; 
v___x_2887_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__0));
v_cls_2888_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__2));
lean_inc(v_mvarId_2878_);
v___f_2889_ = lean_alloc_closure((void*)(l_Lean_MVarId_induction___lam__0___boxed), 11, 6);
lean_closure_set(v___f_2889_, 0, v___x_2887_);
lean_closure_set(v___f_2889_, 1, v_mvarId_2878_);
lean_closure_set(v___f_2889_, 2, v_majorFVarId_2879_);
lean_closure_set(v___f_2889_, 3, v_recursorName_2880_);
lean_closure_set(v___f_2889_, 4, v_givenNames_2881_);
lean_closure_set(v___f_2889_, 5, v_cls_2888_);
v___x_2890_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___redArg(v_mvarId_2878_, v___f_2889_, v_a_2882_, v_a_2883_, v_a_2884_, v_a_2885_);
return v___x_2890_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_induction___boxed(lean_object* v_mvarId_2891_, lean_object* v_majorFVarId_2892_, lean_object* v_recursorName_2893_, lean_object* v_givenNames_2894_, lean_object* v_a_2895_, lean_object* v_a_2896_, lean_object* v_a_2897_, lean_object* v_a_2898_, lean_object* v_a_2899_){
_start:
{
lean_object* v_res_2900_; 
v_res_2900_ = l_Lean_MVarId_induction(v_mvarId_2891_, v_majorFVarId_2892_, v_recursorName_2893_, v_givenNames_2894_, v_a_2895_, v_a_2896_, v_a_2897_, v_a_2898_);
lean_dec(v_a_2898_);
lean_dec_ref(v_a_2897_);
lean_dec(v_a_2896_);
lean_dec_ref(v_a_2895_);
return v_res_2900_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; 
v___x_2948_ = lean_unsigned_to_nat(2221195325u);
v___x_2949_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_));
v___x_2950_ = l_Lean_Name_num___override(v___x_2949_, v___x_2948_);
return v___x_2950_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; 
v___x_2952_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_));
v___x_2953_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_);
v___x_2954_ = l_Lean_Name_str___override(v___x_2953_, v___x_2952_);
return v___x_2954_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; 
v___x_2956_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_));
v___x_2957_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_);
v___x_2958_ = l_Lean_Name_str___override(v___x_2957_, v___x_2956_);
return v___x_2958_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; 
v___x_2959_ = lean_unsigned_to_nat(2u);
v___x_2960_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_);
v___x_2961_ = l_Lean_Name_num___override(v___x_2960_, v___x_2959_);
return v___x_2961_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2963_; uint8_t v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; 
v___x_2963_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__2));
v___x_2964_ = 0;
v___x_2965_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_);
v___x_2966_ = l_Lean_registerTraceClass(v___x_2963_, v___x_2964_, v___x_2965_);
return v___x_2966_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2____boxed(lean_object* v_a_2967_){
_start:
{
lean_object* v_res_2968_; 
v_res_2968_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_();
return v_res_2968_;
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
